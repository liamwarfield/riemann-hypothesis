module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicLatticeSpec
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PhiPositiveDefiniteCholeskyFormula
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IwasawaInt
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.H1MapSubgroup
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselOpNormPowerIntegralLtTopClosedSubgroup
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsLatMeasurableConst
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProdAbsNormDivsDvd

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PsiComplexifiedKEquivariance
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PsiComplexifiedKEquivariance
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder

noncomputable section
namespace GlobalTheory.Dec.Equivar
variable {n : ℕ}

lemma diag_KC (ε : Fin n → Bool) {d : Fin n → ℂ} (hd : ∀ a, d a ≠ 0) : Matrix.diagonal d ∈ KC ε := by
  refine ⟨?_, ?_⟩
  · rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_diagonal]
    exact IsUnit.mk0 _ (Finset.prod_ne_zero_iff.2 fun a _ => hd a)
  · unfold Jm
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1; funext a; ring

lemma KC_mul {ε : Fin n → Bool} {a b : Matrix (Fin n) (Fin n) ℂ} (ha : a ∈ KC ε) (hb : b ∈ KC ε) :
    a * b ∈ KC ε := by
  refine ⟨ha.1.mul hb.1, ?_⟩
  rw [Matrix.mul_assoc, hb.2, ← Matrix.mul_assoc, ha.2, Matrix.mul_assoc]

lemma KC_inv {ε : Fin n → Bool} {a : Matrix (Fin n) (Fin n) ℂ} (ha : a ∈ KC ε) : a⁻¹ ∈ KC ε := by
  have hd := (Matrix.isUnit_iff_isUnit_det a).1 ha.1
  refine ⟨Matrix.isUnit_nonsing_inv_iff.2 ha.1, ?_⟩
  calc a⁻¹ * Jm ε = a⁻¹ * (Jm ε * a) * a⁻¹ := by
        rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_right _ _ hd]
    _ = Jm ε * a⁻¹ := by rw [← ha.2, Matrix.nonsing_inv_mul_cancel_left _ _ hd]

lemma KC_conjT {ε : Fin n → Bool} {a : Matrix (Fin n) (Fin n) ℂ} (ha : a ∈ KC ε) : aᴴ ∈ KC ε := by
  refine ⟨by simpa [Matrix.star_eq_conjTranspose] using ha.1.star, ?_⟩
  have h := congrArg Matrix.conjTranspose ha.2
  simp only [Matrix.conjTranspose_mul, Jm_conjTranspose] at h
  exact h.symm

variable {ε : Fin n → Bool} {abelian₂ : Fin n → ℝ} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  {τ : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)} {w : W}

lemma tau_diag (hτ : IsTau ε abelian₂ τ w) (r : Fin n → ℝ) :
    τ (Matrix.diagonal fun a => Complex.exp (r a)) w = Complex.exp (-((∑ a, abelian₂ a * r a : ℝ) : ℂ)) • w := by
  refine ext_inner_left ℂ fun u => ?_
  set c : ℂ := -((∑ a, abelian₂ a * r a : ℝ) : ℂ) with hc
  let f : ℂ → ℂ := fun s => ⟪u, τ (Matrix.diagonal fun a => Complex.exp (r a * s)) w⟫_ℂ
  let g : ℂ → ℂ := fun s => Complex.exp (c * s) * ⟪u, w⟫_ℂ
  have hf : Differentiable ℂ f := by
    have h1 : Differentiable ℂ (fun s : ℂ => fun i j : Fin n =>
        (Matrix.diagonal fun a => Complex.exp (r a * s)) i j) := by
      refine differentiable_pi.2 fun i => differentiable_pi.2 fun j => ?_
      by_cases h : i = j
      · subst h; simp only [Matrix.diagonal_apply_eq]; fun_prop
      · simp only [Matrix.diagonal_apply_ne _ h]; fun_prop
    have := (hτ.2.2.1 u w).comp (s := Set.univ) h1.differentiableOn
      (fun s _ => diag_KC ε fun a => Complex.exp_ne_zero _)
    exact differentiableOn_univ.1 this
  have hg : Differentiable ℂ g := by fun_prop
  have hfg : ∀ t : ℝ, f (t * Complex.I) = g (t * Complex.I) := by
    intro t
    have hmem : Matrix.diagonal (fun a => Complex.exp (((r a * t : ℝ) : ℂ) * Complex.I)) ∈ Kset ε := by
      refine ⟨?_, (diag_KC ε fun a => Complex.exp_ne_zero _).2⟩
      rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
        Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext a
      rw [Pi.star_apply, Complex.star_def, Complex.mul_conj', Complex.norm_exp_ofReal_mul_I]
      simp
    have h := hτ.2.2.2.2.2.2.1 (fun a => r a * t) hmem
    simp only [f, g]
    have e : (fun a => Complex.exp (r a * (t * Complex.I))) =
        (fun a => Complex.exp (((r a * t : ℝ) : ℂ) * Complex.I)) := by
      funext a; push_cast; rw [mul_assoc]
    rw [e, h, inner_smul_right, hc]
    congr 2
    simp only [Pi.neg_apply, ← mul_assoc, ← Finset.sum_mul, neg_mul, Finset.sum_neg_distrib]
    push_cast; ring
  have hfreq : ∃ᶠ z in nhdsWithin (0 : ℂ) {0}ᶜ, f z = g z := by
    have ht : Filter.Tendsto (fun t : ℝ => (t : ℂ) * Complex.I) (nhdsWithin 0 {0}ᶜ) (nhdsWithin 0 {0}ᶜ) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have : Continuous fun t : ℝ => (t : ℂ) * Complex.I := by fun_prop
        simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with t ht
        simpa using ht
    exact ht.frequently (Filter.Frequently.of_forall hfg)
  have := AnalyticOnNhd.eq_of_frequently_eq (hf.differentiableOn.analyticOnNhd isOpen_univ)
    (hg.differentiableOn.analyticOnNhd isOpen_univ) hfreq
  have := congrFun this 1
  simpa [f, g, inner_smul_right] using this

lemma tau_lo (hτ : IsTau ε abelian₂ τ w) {b : Matrix (Fin n) (Fin n) ℂ} (hb : b ∈ KC ε) (hlo : IsLo b)
    (hpos : ∀ l, 0 < b l l) : τ b w = ((∏ l, ‖b l l‖ ^ (-(abelian₂ l)) : ℝ) : ℂ) • w := by
  have hne : ∀ l, b l l ≠ 0 := fun l => (hpos l).ne'
  have hn : ∀ l, 0 < ‖b l l‖ := fun l => norm_pos_iff.2 (hne l)
  have hexp : ∀ l, Complex.exp (Real.log ‖b l l‖ : ℝ) = b l l := fun l => by
    rw [← Complex.ofReal_exp, Real.exp_log (hn l)]
    exact Complex.norm_of_nonneg' (hpos l).le
  have hu : Matrix.diagonal (fun a => (b a a)⁻¹) * b ∈ KC ε :=
    KC_mul (diag_KC ε fun a => inv_ne_zero (hne a)) hb
  have hu1 : IsLoUni (Matrix.diagonal (fun a => (b a a)⁻¹) * b) := by
    intro i j
    refine ⟨fun h => by simp [Matrix.diagonal_mul, hlo i j h], fun h => ?_⟩
    subst h
    simp [Matrix.diagonal_mul, hne]
  have e : b = (Matrix.diagonal fun a => Complex.exp (Real.log ‖b a a‖ : ℝ)) *
      (Matrix.diagonal (fun a => (b a a)⁻¹) * b) := by
    simp only [hexp]
    ext i j
    simp [Matrix.diagonal_mul, hne]
  have h1 := hτ.2.1.2 _ (diag_KC ε (d := fun a => Complex.exp (Real.log ‖b a a‖ : ℝ))
    fun a => Complex.exp_ne_zero _) _ hu
  rw [← e] at h1
  rw [h1, ContinuousLinearMap.comp_apply, hτ.2.2.2.2.2.2.2 _ hu hu1, tau_diag hτ]
  congr 1
  rw [← Complex.ofReal_neg, ← Complex.ofReal_exp, ← Finset.sum_neg_distrib, Real.exp_sum]
  congr 1
  refine Finset.prod_congr rfl fun l _ => ?_
  rw [Real.rpow_def_of_pos (hn l)]
  congr 1; ring

lemma tau_cont (hτ : IsTau ε abelian₂ τ w) (v : W) : ContinuousOn (fun k => τ k v) (Kset ε) := by
  have := hτ.1
  have e : (fun k => τ k v) = fun k => ∑ i, ⟪stdOrthonormalBasis ℂ W i, τ k v⟫_ℂ • stdOrthonormalBasis ℂ W i := by
    funext k
    rw [(stdOrthonormalBasis ℂ W).sum_repr']
  rw [e]
  refine continuousOn_finsetSum _ fun i _ => ContinuousOn.smul ?_ continuousOn_const
  exact (hτ.2.2.1 _ v).continuousOn.mono fun k hk => FormF.K_KC hk

lemma muInt_cast {lam : Fin n → ℝ} (hlam : IsHCParam lam) (ε : Fin n → Bool) (l : Fin n) :
    (muInt lam l : ℝ) = lowK ε lam l + 2 * rhoC ε l := by
  obtain ⟨m, hm⟩ := hlam.2 l
  have h1 := half_sum_roots_standard n ε l
  have h2 : lam l + Formalism.QuantumDeterminants.rhoStd n l = ((m + n - 1 - (l : ℕ) : ℤ) : ℝ) := by
    simp only [Formalism.QuantumDeterminants.rhoStd]; push_cast; linarith
  have h3 : (muInt lam l : ℝ) = lam l + Formalism.QuantumDeterminants.rhoStd n l := by
    rw [muInt, h2, Int.floor_intCast]
  rw [h3]
  simp only [lowK, Formalism.QuantumDeterminants.rhoStd, Pi.add_apply, Pi.sub_apply]
  linarith

lemma scalar_eq {lam : Fin n → ℝ} (hlam : IsHCParam lam) (ε : Fin n → Bool) {d : Fin n → ℂ} (hd : ∀ l, d l ≠ 0) :
    (∏ l, (d l * star (d l)) ^ (-(muInt lam l))) * ((∏ l, ‖d l‖ ^ (4 * rhoC ε l) : ℝ) : ℂ) =
      ((∏ l, ‖d l‖ ^ (-(lowK ε lam l)) : ℝ) : ℂ) * ((∏ l, ‖d l‖ ^ (-(lowK ε lam l)) : ℝ) : ℂ) := by
  simp only [Complex.star_def, Complex.mul_conj', ← Complex.ofReal_pow, ← Complex.ofReal_zpow,
    ← Complex.ofReal_prod, ← Complex.ofReal_mul, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun l _ => ?_
  have hn : 0 < ‖d l‖ := norm_pos_iff.2 (hd l)
  rw [← Real.rpow_intCast, ← Real.rpow_natCast, ← Real.rpow_mul hn.le, ← Real.rpow_add hn, ← Real.rpow_add hn]
  congr 1
  push_cast
  rw [muInt_cast hlam ε]
  ring

theorem psEquiv_of (hT : PhiTri) (hP : PhiPos) (hI : IwasawaKC) (hH : IwasawaInt) : PsEquiv := by
  intro n ε lam W _ _ τ w hlam hτ x y hx hy
  have hyd := (Matrix.isUnit_iff_isUnit_det y).1 hy.1
  have hx' : (y * x * yᴴ).PosDef := hx.mul_mul_conjTranspose_same (Matrix.vecMul_injective_of_isUnit hy.1)
  obtain ⟨κ, β, hκ, -⟩ := hI n ε
  have hmem : ∀ k : KG ε, y⁻¹ * toMK k ∈ KC ε := fun k => KC_mul (KC_inv hy) (FormF.K_KC k.2)
  ext u
  refine ext_inner_left ℂ fun v => ?_
  have hadj : ∀ a : W, ⟪v, τ y a⟫_ℂ = ⟪τ yᴴ v, a⟫_ℂ := fun a => by
    rw [hτ.2.2.2.1 _ (KC_conjT hy), Matrix.conjTranspose_conjTranspose]
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hadj,
    FormF.psEntry hP n ε lam W τ w hτ.1 (tau_cont hτ) _ hx', FormF.psEntry hP n ε lam W τ w hτ.1 (tau_cont hτ) _ hx]
  congr 1
  have hF : ContinuousOn (fun k : Matrix (Fin n) (Fin n) ℂ =>
      Phi lam (k⁻¹ * x * k) * (⟪τ yᴴ v, τ k w⟫_ℂ * ⟪τ k w, τ yᴴ u⟫_ℂ)) (Kset ε) := by
    refine ContinuousOn.mul ?_ ((ContinuousOn.inner (𝕜 := ℂ) continuousOn_const (tau_cont hτ w)).mul
      (ContinuousOn.inner (𝕜 := ℂ) (tau_cont hτ w) continuousOn_const))
    refine ContinuousOn.congr (f := fun k => Phi lam (kᴴ * x * k)) ?_ fun k hk => by simp only [FormF.K_inv hk]
    unfold Phi
    refine continuousOn_finsetProd _ fun i _ => ContinuousOn.zpow₀ ?_ _ fun k hk => Or.inl ?_
    · unfold leadMinor
      exact (((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul
        continuous_id).matrix_submatrix _ _).matrix_det.continuousOn
    · exact (hP n lam _ (hx.conjTranspose_mul_mul_same
        (Matrix.mulVec_injective_of_isUnit (FormF.K_KC hk).1))).1 i
  rw [← hH n ε y⁻¹ (fun k => κ (y⁻¹ * toMK k)) (fun k => β (y⁻¹ * toMK k)) (KC_inv hy)
    (fun k => hκ _ (hmem k)) _ hF]
  congr 1
  funext k
  obtain ⟨h1, h2, h3, h4, h5⟩ := hκ _ (hmem k)
  have hk : toMK k ∈ Kset ε := k.2
  generalize κ (y⁻¹ * toMK k) = c at *
  generalize β (y⁻¹ * toMK k) = b at *
  generalize toMK k = g at *
  have hg : g = y * (c * b) := by rw [← h5, Matrix.mul_nonsing_inv_cancel_left _ _ hyd]
  have hgg : gᴴ * g = 1 := Unitary.star_mul_self_of_mem hk.1
  have hc : cᴴ = b * gᴴ * y := by
    rw [← FormF.K_inv h1]
    apply Matrix.inv_eq_left_inv
    have : gᴴ * y * c * b = 1 := by
      rw [Matrix.mul_assoc, Matrix.mul_assoc, ← hg, hgg]
    have := mul_eq_one_comm.1 this
    simpa only [Matrix.mul_assoc] using this
  have hz : c⁻¹ * x * c = b * (g⁻¹ * (y * x * yᴴ) * g) * bᴴ := by
    have : c = yᴴ * g * bᴴ := by
      rw [← Matrix.conjTranspose_conjTranspose c, hc]
      simp [Matrix.mul_assoc]
    rw [FormF.K_inv h1, FormF.K_inv hk, hc]
    conv_lhs => rw [this]
    simp only [Matrix.mul_assoc]
  have hne : ∀ l, b l l ≠ 0 := fun l => (h4 l).ne'
  have hΩ : g⁻¹ * (y * x * yᴴ) * g ∈ Omega n := by
    rw [FormF.K_inv hk]
    exact (hP n lam _ (hx'.conjTranspose_mul_mul_same
        (Matrix.mulVec_injective_of_isUnit (FormF.K_KC hk).1))).1
  have hΦ := (hT n lam b _ bᴴ h3 (fun i j h => by simp [h3 j i h]) (fun l => ⟨hne l, by simp [hne l]⟩) hΩ).2
  have hw : τ g w = ((∏ l, ‖b l l‖ ^ (-(lowK ε lam l)) : ℝ) : ℂ) • τ y (τ c w) := by
    conv_lhs => rw [hg]
    rw [hτ.2.1.2 _ hy _ (KC_mul (FormF.K_KC h1) h2), hτ.2.1.2 _ (FormF.K_KC h1) _ h2]
    simp only [ContinuousLinearMap.comp_apply]
    rw [tau_lo hτ h2 h3 h4, map_smul, map_smul]
  have hs := scalar_eq hlam ε (d := fun l => b l l) hne
  rw [hz, hΦ, hw, inner_smul_right, inner_smul_left, Complex.conj_ofReal, hadj, hτ.2.2.2.1 _ hy]
  simp only [Matrix.conjTranspose_apply]
  linear_combination (-(Phi lam (g⁻¹ * (y * x * yᴴ) * g) * (⟪τ yᴴ v, τ c w⟫_ℂ * ⟪τ c w, τ yᴴ u⟫_ℂ))) * hs

theorem psEquiv : PsEquiv := psEquiv_of GlobalTheory.PhiTriangular.phiTri GlobalTheory.Dec.phiPos GlobalTheory.Dec.iwasawaKC GlobalTheory.IwaInt.iwasawaInt

end GlobalTheory.Dec.Equivar
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PsiComplexifiedKEquivarianceStatement
open GlobalTheory.Dec
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.psi_complexifiedK_equivariance : PsEquiv := by
  first | exact @GlobalTheory.Dec.Equivar.psEquiv | exact GlobalTheory.Dec.Equivar.psEquiv | (intros; apply GlobalTheory.Dec.Equivar.psEquiv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NeZeroOfMemRoots
open Polynomial GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys

noncomputable section

namespace GlobalTheory.SerSys.LabLoc

open scoped Classical

variable {g : ℕ} [Fact g.Prime]

theorem eq_of_roots_eq {f h : (ZMod g)[X]} (hf : f.Monic) (hh : h.Monic)
    (e : Formalism.CyclotomicNorms.rootsBar f = Formalism.CyclotomicNorms.rootsBar h) : f = h := by
  apply Polynomial.map_injective (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g)) (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g)).injective
  rw [(IsAlgClosed.splits (f.map _)).eq_prod_roots_of_monic (hf.map _),
    (IsAlgClosed.splits (h.map _)).eq_prod_roots_of_monic (hh.map _)]
  exact congrArg (fun m : Multiset (Formalism.CyclotomicNorms.Fbar g) => (m.map fun a => X - C a).prod) e

theorem ne_zero_of_mem_roots {f : (ZMod g)[X]} (h0 : f.coeff 0 ≠ 0) {x : Formalism.CyclotomicNorms.Fbar g}
    (hx : x ∈ Formalism.CyclotomicNorms.rootsBar f) : x ≠ 0 := by
  rintro rfl
  have hf : f.map (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g)) ≠ 0 := (mem_roots'.1 hx).1
  have := (mem_roots'.1 hx).2
  rw [IsRoot, eval_map, eval₂_at_zero] at this
  exact h0 ((algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g)).injective (by simpa using this))

theorem map_eq_map {τ : Formalism.CyclotomicNorms.Fbar g →* ℂ} (hτ : Set.InjOn τ {x | x ≠ 0}) {A B : Multiset (Formalism.CyclotomicNorms.Fbar g)}
    (hA : ∀ x ∈ A, x ≠ 0) (hB : ∀ x ∈ B, x ≠ 0) (e : A.map τ = B.map τ) : A = B := by
  rw [Multiset.ext]
  intro x
  by_cases hx : x = 0
  · subst hx
    rw [Multiset.count_eq_zero.2 (fun h => hA 0 h rfl), Multiset.count_eq_zero.2 (fun h => hB 0 h rfl)]
  have key : ∀ C : Multiset (Formalism.CyclotomicNorms.Fbar g), (∀ y ∈ C, y ≠ 0) → C.count x = (C.map τ).count (τ x) := by
    intro C hC
    rw [Multiset.count_map, Multiset.count_eq_card_filter_eq]
    congr 1
    refine Multiset.filter_congr fun y hy => ⟨fun h => h ▸ rfl, fun h => hτ hx (hC y hy) h⟩
  rw [key A hA, key B hB, e]

theorem actK_finset_sum {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GL (Fin n) ℚ_[g]) V) {ι : Type} (T : Finset ι) (a : ι → MonoidAlgebra ℂ (Gn g n)) :
    actK ρ (∑ i ∈ T, a i) = ∑ i ∈ T, actK ρ (a i) := by
  classical
  induction T using Finset.induction_on with
  | empty => simp [actK]
  | insert i T hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, ← ih]
    simp [actK, add_smul, Finset.sum_add_distrib]

theorem actK_one_of_mem {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GL (Fin n) ℚ_[g]) V) {v : V} (hv : v ∈ fixK1 ρ) : actK ρ 1 v = v := by
  have hs : actK ρ 1 = ρ (lift g n 1) := by
    unfold actK
    rw [MonoidAlgebra.one_def, Finset.sum_eq_single 1]
    · simp
    · intro y _ hy
      simp [Finsupp.single_eq_of_ne hy]
    · simp
  have hk : red g n (Function.invFun (red g n) 1) = 1 := Function.invFun_eq ⟨1, map_one _⟩
  rw [hs, lift]
  have := (Submodule.mem_iInf _).1 hv ⟨_, hk⟩
  rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at this
  simpa using this

end GlobalTheory.SerSys.LabLoc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselFormCoeffProductFubiniIntegrable
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselFormCoeffProductFubiniIntegrable
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.SgInf

theorem integrable_opn_rpow_neg {k r : ℕ} (μ : Measure (Mt k r)) (A : ℝ)
    (hc : Continuous fun x : Mat k r => opn x) (h : normInt μ A < ⊤) :
    Integrable (fun x : Mt k r => opn (Matrix.of x) ^ (-A)) μ := by
  have hm : Measurable fun x : Mt k r => opn (Matrix.of x) ^ (-A) :=
    (show Continuous fun x : Mt k r => opn (Matrix.of x) from hc).measurable.pow_const _
  refine ⟨hm.aestronglyMeasurable, ?_⟩
  exact (hasFiniteIntegral_iff_ofReal
    (Filter.Eventually.of_forall fun x => Real.rpow_nonneg (opn_nonneg _) _)).2 h

theorem rpow_fubini_ineq {x y t a : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y) (ht : 0 < t) (hyt : t / x ≤ y)
    (ha : 0 ≤ a) : x ^ (-a) * y ^ (-a) ≤ x ^ (-(a / 2)) * t ^ (-(a / 2)) := by
  have hx0 : 0 < x := lt_of_lt_of_le one_pos hx
  have h1 : y ^ (-a) ≤ y ^ (-(a / 2)) := Real.rpow_le_rpow_of_exponent_le hy (by linarith)
  have h2 : y ^ (-(a / 2)) ≤ (t / x) ^ (-(a / 2)) :=
    Real.rpow_le_rpow_of_nonpos (div_pos ht hx0) hyt (by linarith)
  have h3 : (t / x) ^ (-(a / 2)) = t ^ (-(a / 2)) / x ^ (-(a / 2)) := Real.div_rpow ht.le hx0.le _
  have h4 : x ^ (-a) = x ^ (-(a / 2)) * x ^ (-(a / 2)) := by
    rw [← Real.rpow_add hx0]; ring_nf
  have hxp : 0 < x ^ (-(a / 2)) := Real.rpow_pos_of_pos hx0 _
  calc x ^ (-a) * y ^ (-a) ≤ x ^ (-a) * ((t / x) ^ (-(a / 2))) :=
        mul_le_mul_of_nonneg_left (h1.trans h2) (Real.rpow_nonneg hx0.le _)
    _ = x ^ (-(a / 2)) * t ^ (-(a / 2)) := by
        rw [h3, h4]; field_simp

theorem fubini_bound : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)) , Std σ w a μG d → Side z π μS → ∀ u ∈ DD σ w, ∀ u₁ ∈ DD σ w, ∀ v ∈ DD σ w, ∀ v₁ ∈ DD σ w, Integrable (fun p : Mt k r × Mt k r => coef σ u v (Matrix.of p.1) * star (coef σ u₁ v₁ (Matrix.of p.2 * Matrix.of p.1))) (μG.prod μS) := by
  intro k r H _ _ _ Wp _ _ _ _ σ w a μG d z c π μS hStd hSide u hu u₁ hu₁ v hv v₁ hv₁
  obtain ⟨hk, hrep, -, -, hHG, -, ha, hdec, -⟩ := hStd
  obtain ⟨hz, hT, -, hHS, -⟩ := hSide
  obtain ⟨hGc, -, -, hSc, -⟩ := GlobalTheory.SgInf.closedSub_groups k r z hz hT
  obtain ⟨hN1, -, hNc, -, -, -, hN7, -⟩ := GlobalTheory.T.besselModelUnitaryGroup_opNorm_properties k r
  have hA := (GlobalTheory.T.bessel_constant_bounds_of_ge_two_n_pow_five k r a hk ha).1
  have hIG := GlobalTheory.T.besselOpNormPowerIntegral_lt_top_closedSubgroup k r (GG k r) μG (a / 2) hGc hHG hA
  have hIS := GlobalTheory.T.besselOpNormPowerIntegral_lt_top_closedSubgroup k r (Sset k r z) μS (a / 2) hSc hHS hA
  obtain ⟨C, hC⟩ := hdec u hu v hv
  obtain ⟨C₁, hC₁⟩ := hdec u₁ hu₁ v₁ hv₁
  haveI := hHG.1
  haveI := hHS.1
  have ha0 : 0 ≤ a := le_trans (by positivity) ha
  set T : Set (Mt k r × Mt k r) := {p | Matrix.of p.1 ∈ GG k r ∧ Matrix.of p.2 ∈ Sset k r z} with hTdef
  have hTm : MeasurableSet T := by
    have h1 : IsClosed {p : Mt k r × Mt k r | Matrix.of p.1 ∈ GG k r} :=
      hGc.2.1.preimage continuous_fst
    have h2 : IsClosed {p : Mt k r × Mt k r | Matrix.of p.2 ∈ Sset k r z} :=
      hSc.2.1.preimage continuous_snd
    exact (h1.inter h2).measurableSet
  have hTae : ∀ᵐ p ∂(μG.prod μS), p ∈ T := by
    rw [ae_iff]
    refine measure_mono_null (t := ({x : Mt k r | Matrix.of x ∉ GG k r} ×ˢ Set.univ) ∪
      (Set.univ ×ˢ {x : Mt k r | Matrix.of x ∉ Sset k r z})) ?_ ?_
    · intro p hp
      simp only [Set.mem_setOf_eq, hTdef, not_and_or] at hp
      rcases hp with hp | hp
      · exact Or.inl ⟨hp, trivial⟩
      · exact Or.inr ⟨trivial, hp⟩
    · refine measure_union_null ?_ ?_
      · rw [Measure.prod_prod, hHG.2.2.1, zero_mul]
      · rw [Measure.prod_prod, hHS.2.2.1, mul_zero]
  have hg : Integrable (fun p : Mt k r × Mt k r => (|C| * |C₁|) *
      (opn (Matrix.of p.1) ^ (-(a / 2)) * opn (Matrix.of p.2) ^ (-(a / 2)))) (μG.prod μS) :=
    ((integrable_opn_rpow_neg μG _ hNc hIG).mul_prod (integrable_opn_rpow_neg μS _ hNc hIS)).const_mul _
  have hcont : ContinuousOn (fun p : Mt k r × Mt k r =>
      coef σ u v (Matrix.of p.1) * star (coef σ u₁ v₁ (Matrix.of p.2 * Matrix.of p.1))) T := by
    have c1 : ContinuousOn (fun p : Mt k r × Mt k r => σ (Matrix.of p.1) u) T :=
      (hrep.2.2 u).comp (continuous_fst.continuousOn) (fun p hp => hp.1)
    have hmul : Continuous fun p : Mt k r × Mt k r => (Matrix.of p.2 * Matrix.of p.1 : Mat k r) :=
      (continuous_snd (X := Mat k r) (Y := Mat k r)).matrix_mul continuous_fst
    have c2 : ContinuousOn (fun p : Mt k r × Mt k r => σ (Matrix.of p.2 * Matrix.of p.1) u₁) T :=
      (hrep.2.2 u₁).comp hmul.continuousOn
        (fun p hp => hGc.2.2.2.1 _ (hSc.1 hp.2) _ hp.1)
    exact (continuousOn_const.inner c1).mul (continuous_star.comp_continuousOn (continuousOn_const.inner c2))
  refine hg.mono' ?_ ?_
  · have := hcont.aestronglyMeasurable (μ := μG.prod μS) hTm
    rwa [Measure.restrict_eq_self_of_ae_mem hTae] at this
  · filter_upwards [hTae] with p hp
    obtain ⟨hpG, hpS⟩ := hp
    have hSG : Matrix.of p.2 ∈ GG k r := hSc.1 hpS
    have hyG : (Matrix.of p.2 * Matrix.of p.1 : Mat k r) ∈ GG k r := hGc.2.2.2.1 _ hSG _ hpG
    have hx1 := (hN1 _ hpG).2
    have ht1 := (hN1 _ hSG).2
    have hy1 := (hN1 _ hyG).2
    have hyt : opn (Matrix.of p.2 : Mat k r) / opn (Matrix.of p.1 : Mat k r) ≤
        opn (Matrix.of p.2 * Matrix.of p.1 : Mat k r) := (hN7 _ hSG _ hpG).1
    have e1 : ‖coef σ u v (Matrix.of p.1)‖ ≤ |C| * opn (Matrix.of p.1 : Mat k r) ^ (-a) :=
      (hC _ hpG).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_nonneg (opn_nonneg _) _))
    have e2 : ‖coef σ u₁ v₁ (Matrix.of p.2 * Matrix.of p.1)‖ ≤
        |C₁| * opn (Matrix.of p.2 * Matrix.of p.1 : Mat k r) ^ (-a) :=
      (hC₁ _ hyG).trans (mul_le_mul_of_nonneg_right (le_abs_self C₁) (Real.rpow_nonneg (opn_nonneg _) _))
    have key := rpow_fubini_ineq hx1 hy1 (lt_of_lt_of_le one_pos ht1) hyt ha0
    rw [norm_mul, norm_star]
    calc ‖coef σ u v (Matrix.of p.1)‖ * ‖coef σ u₁ v₁ (Matrix.of p.2 * Matrix.of p.1)‖
        ≤ (|C| * opn (Matrix.of p.1 : Mat k r) ^ (-a)) *
            (|C₁| * opn (Matrix.of p.2 * Matrix.of p.1 : Mat k r) ^ (-a)) :=
          mul_le_mul e1 e2 (norm_nonneg _) (mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (opn_nonneg _) _))
      _ = (|C| * |C₁|) * (opn (Matrix.of p.1 : Mat k r) ^ (-a) *
            opn (Matrix.of p.2 * Matrix.of p.1 : Mat k r) ^ (-a)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left key (mul_nonneg (abs_nonneg _) (abs_nonneg _))

end GlobalTheory.SgInf
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselFormCoeffProductFubiniIntegrableStatement
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselForm_coeff_product_fubini_integrable : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)) , Std σ w a μG d → Side z π μS → ∀ u ∈ DD σ w, ∀ u₁ ∈ DD σ w, ∀ v ∈ DD σ w, ∀ v₁ ∈ DD σ w, Integrable (fun p : Mt k r × Mt k r => coef σ u v (Matrix.of p.1) * star (coef σ u₁ v₁ (Matrix.of p.2 * Matrix.of p.1))) (μG.prod μS) := by
  first | exact @GlobalTheory.SgInf.fubini_bound | exact GlobalTheory.SgInf.fubini_bound | (intros; apply GlobalTheory.SgInf.fubini_bound <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsSaturatedIsotropicFlagOfAdaptedBasis
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsSaturatedIsotropicFlagOfAdaptedBasis
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase

noncomputable section

namespace GlobalTheory.FlagBase.AdSat

theorem hform_eq {E : Type} [Field E] [StarRing E] {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) :
    Formalism.UG.hform (starRingEnd E) J x y = star x ⬝ᵥ (J *ᵥ y) := by
  simp [Formalism.UG.hform, dotProduct, mulVec, Finset.mul_sum, mul_assoc, starRingEnd_apply]

theorem isSatFlag_of_isAdapted (I I₀ : AutInst) (e : I₀.E ≃+* I.E) (xf : I.Gf) (a : ℕ) (j : Fin a → ℕ)
    (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)) (Λ : ∀ i, Submodule (𝓞 I.E) (Fin (j i) → I.E))
    (x₀ : I₀.Gf) (T T' : ∀ i, Matrix (Fin I.n) (Fin (j i)) I.E) (T₀ : Matrix (Fin I.n) (Fin I₀.n) I.E)
    (_hj : ∀ i, 1 ≤ j i) (h : IsAdapted I I₀ e xf j S Λ x₀ T T' T₀) :
    IsSatFlag I (lamX I (1, xf)) j S := by
  classical
  obtain ⟨-, -, hΛ, h1, h2, -, hL, hS⟩ := h
  have hJ : I.Jᴴ = I.J := I.J_herm
  let p : ∀ i, (Fin I.n → I.E) →ₗ[I.E] (Fin (j i) → I.E) := fun i => ((T' i)ᴴ * I.J).mulVecLin
  have hsw : ∀ i k, (T' i)ᴴ * I.J * T k = ((T k)ᴴ * I.J * T' i)ᴴ := fun i k => by
    simp [Matrix.conjTranspose_mul, hJ, Matrix.mul_assoc]
  have pT : ∀ i x, p i (T i *ᵥ x) = x := fun i x => by
    simp only [p, mulVecLin_apply, mulVec_mulVec]
    rw [hsw, (h2 i).1]; simp
  have pT' : ∀ i k x, k ≠ i → p i (T k *ᵥ x) = 0 := fun i k x hk => by
    simp only [p, mulVecLin_apply, mulVec_mulVec]
    rw [hsw, (h1 k i).2.2 hk]; simp
  have pS : ∀ i (u : ∀ i, Fin (j i) → I.E), p i (∑ k, T k *ᵥ u k) = u i := fun i u => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.sum_eq_single i (fun k _ hk => pT' i k _ hk) (by simp), pT]
  have hsp : ∀ k z, z ∈ Submodule.span I.E (S k : Set (Fin I.n → I.E)) →
      z = ∑ i, T i *ᵥ p i z ∧ ∀ i : Fin a, ¬ i.castSucc < k → p i z = 0 := fun k z hz => by
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨u, -, hu, rfl⟩ := (hS k z).1 hz
      simp only [pS]
      exact ⟨trivial, hu⟩
    | zero => simp
    | add x y _ _ hx hy =>
      refine ⟨?_, fun i hi => by rw [map_add (f := _), hx.2 i hi, hy.2 i hi, add_zero]⟩
      simp only [map_add (f := _), mulVec_add, Finset.sum_add_distrib]
      rw [← hx.1, ← hy.1]
    | smul c x _ hx =>
      refine ⟨?_, fun i hi => by rw [map_smul, hx.2 i hi, smul_zero]⟩
      simp only [map_smul, mulVec_smul, ← Finset.smul_sum]
      rw [← hx.1]
  have hmono : Monotone S := fun k l hkl z hz => by
    obtain ⟨u, hu, hu0, rfl⟩ := (hS k z).1 hz
    exact (hS l _).2 ⟨u, hu, fun i hi => hu0 i fun h => hi (h.trans_le hkl), rfl⟩
  refine ⟨?_, hmono, fun i => ?_, fun k y => ⟨fun hy => ⟨?_, Submodule.subset_span hy⟩, ?_⟩, ?_⟩
  · refine eq_bot_iff.2 fun z hz => ?_
    obtain ⟨u, -, hu0, rfl⟩ := (hS 0 z).1 hz
    have : ∀ i, u i = 0 := fun i => hu0 i (by simp)
    simp [this]
  · have hsup : Submodule.span I.E (S i.succ : Set (Fin I.n → I.E)) =
        Submodule.span I.E (S i.castSucc : Set (Fin I.n → I.E)) ⊔ LinearMap.range (T i).mulVecLin := by
      apply le_antisymm
      · refine Submodule.span_le.2 fun z hz => ?_
        obtain ⟨u, hu, hu0, rfl⟩ := (hS _ z).1 hz
        have e1 : ∑ k, T k *ᵥ u k = ∑ k, T k *ᵥ Function.update u i 0 k + T i *ᵥ u i := by
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i),
            ← Finset.add_sum_erase _ (fun k => T k *ᵥ Function.update u i 0 k) (Finset.mem_univ i)]
          rw [Finset.sum_congr rfl (s₁ := univ.erase i) (f := fun k => T k *ᵥ Function.update u i 0 k)
            (g := fun k => T k *ᵥ u k)
            (fun k hk => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)])]
          simp [add_comm]
        rw [e1]
        refine Submodule.add_mem_sup (Submodule.subset_span ((hS _ _).2 ⟨_, fun k => ?_, fun k hk => ?_, rfl⟩))
          ⟨u i, rfl⟩
        · by_cases hki : k = i
          · subst hki; simp
          · rw [Function.update_of_ne hki]; exact hu k
        · by_cases hki : k = i
          · subst hki; simp
          · rw [Function.update_of_ne hki]
            refine hu0 k fun h => hk ?_
            rw [Fin.castSucc_lt_succ_iff] at h
            exact Fin.castSucc_lt_castSucc_iff.2 (lt_of_le_of_ne h hki)
      · refine sup_le (Submodule.span_mono (hmono (Fin.castSucc_lt_succ).le)) ?_
        letI : Submodule.IsFullLattice I.E (Λ i) := hΛ i
        rw [LinearMap.range_eq_map, ← Submodule.IsFullLattice.span_eq_top (A := I.E) (M := Λ i), Submodule.map_span]
        refine Submodule.span_mono ?_
        rintro _ ⟨x, hx, rfl⟩
        refine (hS _ _).2 ⟨Pi.single i x, fun k => ?_, fun k hk => ?_, ?_⟩
        · by_cases hki : k = i
          · subst hki; simpa using hx
          · rw [Pi.single_eq_of_ne hki]; exact zero_mem _
        · refine Pi.single_eq_of_ne ?_ _
          rintro rfl
          exact hk Fin.castSucc_lt_succ
        · rw [Finset.sum_eq_single i (fun k _ hk => by rw [Pi.single_eq_of_ne hk, mulVec_zero]) (by simp)]
          simp
    have hinf : Submodule.span I.E (S i.castSucc : Set (Fin I.n → I.E)) ⊓ LinearMap.range (T i).mulVecLin = ⊥ := by
      refine eq_bot_iff.2 ?_
      rintro _ ⟨hz, x, rfl⟩
      have : x = 0 := (pT i x).symm.trans ((hsp _ _ hz).2 i (lt_irrefl _))
      simp [this]
    have hinj : Function.Injective (T i).mulVecLin := fun x y hxy => by
      rw [← pT i x, ← pT i y]; exact congrArg (p i) hxy
    have := Submodule.finrank_sup_add_finrank_inf_eq (Submodule.span I.E (S i.castSucc : Set (Fin I.n → I.E)))
      (LinearMap.range (T i).mulVecLin)
    rw [hinf, ← hsup, LinearMap.finrank_range_of_inj hinj] at this
    simpa [Formalism.HN.rkK] using this
  · obtain ⟨u, hu, -, rfl⟩ := (hS k y).1 hy
    refine (hL _).2 ⟨u, 0, 0, hu, fun i t _ => by simp, zero_mem _, ?_⟩
    have : (fun l => e ((0 : Fin I₀.n → I₀.E) l)) = 0 := by ext; simp
    rw [this]
    simp
  · rintro ⟨hy, hy'⟩
    obtain ⟨u, u', y₀, hu, -, -, hz⟩ := (hL y).1 hy
    have hp : ∀ i, p i y = u i := fun i => by
      have a1 : ∀ k, p i (T' k *ᵥ u' k) = 0 := fun k => by
        simp only [p, mulVecLin_apply, mulVec_mulVec]
        rw [(h1 i k).2.1]; simp
      have a2 : ∀ x, p i (T₀ *ᵥ x) = 0 := fun x => by
        simp only [p, mulVecLin_apply, mulVec_mulVec]
        rw [(h2 i).2.2]; simp
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hz, map_add (f := _), map_add (f := _), pS, a2, map_sum]
      simp [a1]
    obtain ⟨b1, b2⟩ := hsp k y hy'
    exact (hS k y).2 ⟨fun i => p i y, fun i => by simpa only [hp] using hu i, b2, b1⟩
  · intro x hx y hy
    obtain ⟨u, -, -, rfl⟩ := (hS _ x).1 hx
    obtain ⟨v, -, -, rfl⟩ := (hS _ y).1 hy
    rw [hform_eq, star_sum, sum_dotProduct]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [mulVec_sum, dotProduct_sum]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, (h1 i k).1]
    simp

end GlobalTheory.FlagBase.AdSat
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsSaturatedIsotropicFlagOfAdaptedBasisStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSaturatedIsotropicFlag_of_adaptedBasis : ∀ (I I₀ : AutInst) (e : I₀.E ≃+* I.E) (xf : I.Gf) (a : ℕ) (j : Fin a → ℕ) (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)) (Λ : ∀ i, Submodule (𝓞 I.E) (Fin (j i) → I.E)) (x₀ : I₀.Gf) (T T' : ∀ i, Matrix (Fin I.n) (Fin (j i)) I.E) (T₀ : Matrix (Fin I.n) (Fin I₀.n) I.E), (∀ i, 1 ≤ j i) → IsAdapted I I₀ e xf j S Λ x₀ T T' T₀ → IsSatFlag I (lamX I (1, xf)) j S := by
  first | exact @GlobalTheory.FlagBase.AdSat.isSatFlag_of_isAdapted | exact GlobalTheory.FlagBase.AdSat.isSatFlag_of_isAdapted | (intros; apply GlobalTheory.FlagBase.AdSat.isSatFlag_of_isAdapted <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardIsometriesFixingSubspaceDefiniteLatticesLe
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardIsometriesFixingSubspaceDefiniteLatticesLe
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.IsoCount

section
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]

theorem isTraceDef_of_pd (H : Formalism.HermitianLatticeCounting.S6.HermSpace K V) (hp : GlobalTheory.Mass.PD H.B.flip) : IsTraceDef H := by
  intro x hx
  have h1 := trace_eq_sum_embeddings ℂ (K := ℚ) (L := K) (x := H.B x x)
  have h2 : (0 : ℝ) < (algebraMap ℚ ℂ (Algebra.trace ℚ K (H.B x x))).re := by
    have : Nonempty (K →ₐ[ℚ] ℂ) := ⟨IsAlgClosed.lift⟩
    rw [h1, Complex.re_sum]
    exact Finset.sum_pos (fun σ _ => hp σ.toRingHom x hx) Finset.univ_nonempty
  have h3 : (algebraMap ℚ ℂ (Algebra.trace ℚ K (H.B x x))).re = ((Algebra.trace ℚ K (H.B x x) : ℚ) : ℝ) := by
    simp
  rw [h3] at h2
  exact_mod_cast h2

variable [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

def fixAut (H : Formalism.HermitianLatticeCounting.S6.HermSpace K V) (U : Submodule K V) (L : Submodule (𝓞 K) V) : Subgroup (V ≃ₗ[K] V) where
  carrier := {η | η ∈ isomGrp H ∧ imLat η L = L ∧ ∀ y ∈ U, η y = y}
  one_mem' := ⟨(isomGrp H).one_mem, Formalism.HermitianLatticesTheory.genusBasic_gmap_one L, fun _ _ => rfl⟩
  mul_mem' := by
    rintro a b ⟨ha, haL, haU⟩ ⟨hb, hbL, hbU⟩
    refine ⟨mul_mem ha hb, ?_, fun y hy => ?_⟩
    · unfold imLat at *
      rw [Formalism.HermitianLatticesTheory.genusBasic_gmap_mul, hbL, haL]
    · show a (b y) = y
      rw [hbU y hy, haU y hy]
  inv_mem' := by
    rintro a ⟨ha, haL, haU⟩
    refine ⟨inv_mem ha, ?_, fun y hy => ?_⟩
    · unfold imLat at *
      have := Formalism.HermitianLatticesTheory.genusBasic_gmap_inv a L
      rwa [haL] at this
    · show a.symm y = y
      rw [LinearEquiv.symm_apply_eq, haU y hy]


omit [NumberField K] [StarRing K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem map_eq_of_fix {U : Submodule K V} {g : V ≃ₗ[K] V} (h : ∀ y ∈ U, g y = y) :
    U.map (g : V →ₗ[K] V) = U := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have : (g : V →ₗ[K] V) x = x := h x hx
    rw [this]; exact hx
  · intro hy
    exact ⟨y, hy, h y hy⟩

def toQuot (H : Formalism.HermitianLatticeCounting.S6.HermSpace K V) (U : Submodule K V) (L : Submodule (𝓞 K) V) :
    fixAut H U L →* ((V ⧸ U) ≃ₗ[K] (V ⧸ U)) :=
  MonoidHom.mk' (fun g => Submodule.Quotient.equiv U U g.1 (map_eq_of_fix g.2.2.2)) (by
    intro a b
    ext x
    induction x using Submodule.Quotient.induction_on
    rfl)

theorem toQuot_mk (H : Formalism.HermitianLatticeCounting.S6.HermSpace K V) (U : Submodule K V) (L : Submodule (𝓞 K) V) (g : fixAut H U L)
    (x : V) : toQuot H U L g (Submodule.Quotient.mk x) = Submodule.Quotient.mk (g.1 x) := rfl

theorem toQuot_injective {H : Formalism.HermitianLatticeCounting.S6.HermSpace K V} (hH : IsTraceDef H) (U : Submodule K V)
    (L : Submodule (𝓞 K) V) : Function.Injective (toQuot H U L) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  apply Subtype.ext
  ext x
  have h1 : Submodule.Quotient.mk (p := U) (g.1 x) = Submodule.Quotient.mk x := by
    rw [← toQuot_mk, hg]; rfl
  have hu : g.1 x - x ∈ U := (Submodule.Quotient.eq U).1 h1
  have h2 := (mem_isomGrp H g.1).1 g.2.1 x (g.1 x - x)
  rw [g.2.2.2 _ hu] at h2
  have h3 : H.B (g.1 x - x) (g.1 x - x) = 0 := by
    rw [map_sub H.B, LinearMap.sub_apply, h2, sub_self]
  by_contra hne
  have h4 := hH (g.1 x - x) (sub_ne_zero.2 hne)
  rw [h3, map_zero] at h4
  exact lt_irrefl _ h4

variable [FiniteDimensional K V]

theorem fixAut_finite {H : Formalism.HermitianLatticeCounting.S6.HermSpace K V} (hH : IsTraceDef H) (U : Submodule K V)
    {L : Submodule (𝓞 K) V} (hL : Submodule.IsFullLattice K L) : (fixAut H U L : Set (V ≃ₗ[K] V)).Finite :=
  (autCard_eq_natCard hH hL).1.subset fun _ hg => ⟨hg.1, hg.2.1⟩

theorem card_fixAut_dvd (hM : MinkowskiBound) {H : Formalism.HermitianLatticeCounting.S6.HermSpace K V} (hH : IsTraceDef H) (U : Submodule K V)
    {L : Submodule (𝓞 K) V} (hL : Submodule.IsFullLattice K L) :
    Nat.card (fixAut H U L) ∣ minkowskiM (Module.finrank ℚ K * Module.finrank K (V ⧸ U)) := by
  have hfin : Finite (fixAut H U L) := (fixAut_finite hH U hL).to_subtype
  have e := MonoidHom.ofInjective (toQuot_injective hH U L)
  rw [Nat.card_congr e.toEquiv]
  refine GlobalTheory.AutLattice.card_dvd_minkM hM K (V ⧸ U) (L.map (U.mkQ.restrictScalars (𝓞 K)))
    (hL.toIsLattice.fg.map _) ?_ _ (Finite.of_equiv _ e.toEquiv) ?_
  · have : ((L.map (U.mkQ.restrictScalars (𝓞 K)) : Submodule (𝓞 K) (V ⧸ U)) : Set (V ⧸ U))
        = U.mkQ '' (L : Set V) := rfl
    rw [this, Submodule.span_image, hL.span_eq_top, Submodule.map_top, Submodule.range_mkQ]
  · rintro _ ⟨g, rfl⟩ _ ⟨x, hx, rfl⟩
    refine ⟨g.1 x, ?_, rfl⟩
    have h := g.2.2.1
    have h' : g.1 x ∈ imLat g.1 L := ⟨x, hx, rfl⟩
    rwa [h] at h'

end

theorem isoCnt : MinkowskiBound → ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : Formalism.HermitianLatticeCounting.S6.HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → GlobalTheory.Mass.PD H.B.flip → ∀ (U : Submodule K V) (L L' : Submodule (𝓞 K) V), Submodule.IsFullLattice K L → Submodule.IsFullLattice K L' → ((({η : V ≃ₗ[K] V | η ∈ isomGrp H ∧ imLat η L = L' ∧ ∀ y ∈ U, η y = y}).encard : ℕ∞) : ℝ≥0∞) ≤ ((4 * ((Module.finrank K V) - Module.finrank K U) * (Formalism.HermitianLatticesTheory.fDeg K) : ℕ) : ℝ≥0∞) ^ (4 * ((Module.finrank K V) - Module.finrank K U) * (Formalism.HermitianLatticesTheory.fDeg K)) := by
  intro hM K V _ _ _ _ _ _ _ _ H hK hp U L L' hL _
  have hH := isTraceDef_of_pd H hp
  set S := {η : V ≃ₗ[K] V | η ∈ isomGrp H ∧ imLat η L = L' ∧ ∀ y ∈ U, η y = y} with hS
  rcases S.eq_empty_or_nonempty with h0 | ⟨η, hη, hηL, hηU⟩
  · rw [h0]; simp
  have h1 : S.encard ≤ (fixAut H U L : Set (V ≃ₗ[K] V)).encard := by
    refine Set.encard_le_encard_of_injOn (f := fun a => η⁻¹ * a) ?_ ?_
    · rintro a ⟨ha, haL, haU⟩
      refine ⟨mul_mem (inv_mem hη) ha, ?_, fun y hy => ?_⟩
      · unfold imLat at *
        rw [Formalism.HermitianLatticesTheory.genusBasic_gmap_mul, haL, ← hηL, Formalism.HermitianLatticesTheory.genusBasic_gmap_inv]
      · show η.symm (a y) = y
        rw [LinearEquiv.symm_apply_eq, haU y hy, hηU y hy]
    · intro a _ b _ hab
      simpa using hab
  have hn : Module.finrank ℚ K = 2 * Formalism.HermitianLatticesTheory.fDeg K := by
    have := hK.1
    have h2 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces K
    rw [IsTotallyComplex.nrRealPlaces_eq_zero, zero_add] at h2
    rw [Formalism.HermitianLatticesTheory.fDeg, h2, IsTotallyComplex.finrank]
  have hq : Module.finrank K (V ⧸ U) = Module.finrank K V - Module.finrank K U := by
    have := U.finrank_quotient_add_finrank
    omega
  have h2 := (card_fixAut_dvd hM hH U hL).trans (Formalism.HermitianLatticeCounting.P.minkowski_number_dvd_factorial _)
  have h3 := (Nat.le_of_dvd (Nat.factorial_pos _) h2).trans (Nat.factorial_le_pow _)
  have e : 2 * (Module.finrank ℚ K * Module.finrank K (V ⧸ U))
      = 4 * (Module.finrank K V - Module.finrank K U) * Formalism.HermitianLatticesTheory.fDeg K := by
    rw [hn, hq]; ring
  rw [e] at h3
  have h4 : (fixAut H U L : Set (V ≃ₗ[K] V)).encard = (Nat.card (fixAut H U L) : ℕ∞) := by
    rw [← (fixAut_finite hH U hL).cast_ncard_eq, ← Nat.card_coe_set_eq]
    rfl
  rw [h4] at h1
  refine (ENat.toENNReal_le.2 h1).trans ?_
  rw [ENat.toENNReal_coe]
  exact_mod_cast h3

end GlobalTheory.IsoCount
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardIsometriesFixingSubspaceDefiniteLatticesLeStatement
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_isometries_fixing_subspace_definite_lattices_le : MinkowskiBound → ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : Formalism.HermitianLatticeCounting.S6.HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → GlobalTheory.Mass.PD H.B.flip → ∀ (U : Submodule K V) (L L' : Submodule (𝓞 K) V), Submodule.IsFullLattice K L → Submodule.IsFullLattice K L' → ((({η : V ≃ₗ[K] V | η ∈ isomGrp H ∧ imLat η L = L' ∧ ∀ y ∈ U, η y = y}).encard : ℕ∞) : ℝ≥0∞) ≤ ((4 * ((Module.finrank K V) - Module.finrank K U) * (Formalism.HermitianLatticesTheory.fDeg K) : ℕ) : ℝ≥0∞) ^ (4 * ((Module.finrank K V) - Module.finrank K U) * (Formalism.HermitianLatticesTheory.fDeg K)) := by
  first | exact @GlobalTheory.IsoCount.isoCnt | exact GlobalTheory.IsoCount.isoCnt | (intros; apply GlobalTheory.IsoCount.isoCnt <;> first | assumption | exact (by assumption : Submodule.IsFullLattice _ _).toIsLattice)
end
end
