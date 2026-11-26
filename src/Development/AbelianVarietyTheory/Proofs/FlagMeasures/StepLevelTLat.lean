module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SelfDualAt
public import Formalism.LocalToGlobal.HermitianForms.TiedStep
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SelfDualLoc
public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.CenteredPerpendicularSets
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormPosOfIsUnit
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarBallGrowthUnitaryJ
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HasFDerivAtOfContinuousPartials

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.StepLevelTLat
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

namespace GlobalTheory.St.G

theorem _root_.GlobalTheory.St.G.stepLevel_tLat : ∀ (F E : Type) [Field F] [NumberField F]
    [Field E] [NumberField E] [Algebra F E] (n : ℕ) (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E)
    (T f : ℕ) (bad : Set (HeightOneSpectrum (𝓞 F))) (S : _root_.Formalism.L2.Forms.StepLevel F E σ J T f bad),
    _root_.GlobalTheory.St.G.TLat σ J T f S.Lb := by
  intro F E _ _ _ _ _ n σ J T f bad S
  refine ⟨⟨S.Lb_fin, S.Lb_span⟩, S.Lb_int, S.Lb_dual, S.Lb_index, fun v hv => ?_⟩
  obtain ⟨x, hx⟩ := DFunLike.ne_iff.mp (S.fT_ne v hv)
  exact ⟨x, x.2, fun hmem => hx (S.fT_L v hv x hmem)⟩

end GlobalTheory.St.G
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsLocallySelfDualOfHermitianLatticeOfLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsLocallySelfDualOfHermitianLatticeOfLevel
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

namespace GlobalTheory.St.G

theorem selfDualAt_of_tLat :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHerm (cm.sig : E →+* E) J → J.det ≠ 0 → ∀ (T f : ℕ) (L : Submodule (𝓞 E) (Fin n → E)), TLat cm.sig J T f L → ∀ (v : HeightOneSpectrum (𝓞 F)), (T : 𝓞 F) ∉ v.asIdeal → SelfDualAt cm.sig J v L := by
  intro F E _ _ _ _ _ _ cm n J _ _ T f L hL v hv
  obtain ⟨⟨hfin, _⟩, hint, hT, _, _⟩ := hL
  exact self_dual_local F E n cm.sig J v L T hfin (fun x hx y hy => hint y hy x hx)
    (fun y hy => hT y hy) hv

end GlobalTheory.St.G
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsLocallySelfDualOfHermitianLatticeOfLevelStatement
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLocallySelfDual_of_hermitianLatticeOfLevel : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHerm (cm.sig : E →+* E) J → J.det ≠ 0 → ∀ (T f : ℕ) (L : Submodule (𝓞 E) (Fin n → E)), TLat cm.sig J T f L → ∀ (v : HeightOneSpectrum (𝓞 F)), (T : 𝓞 F) ∉ v.asIdeal → SelfDualAt cm.sig J v L := by
  first | exact @GlobalTheory.St.G.selfDualAt_of_tLat | exact GlobalTheory.St.G.selfDualAt_of_tLat | (intros; apply GlobalTheory.St.G.selfDualAt_of_tLat <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdelicUnitaryOfFiniteSupport
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdelicUnitaryOfFiniteSupport
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

namespace GlobalTheory.St.G

theorem exists_adelic_of_finset {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] {n : ℕ} (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E)
    (h : ∀ v : HeightOneSpectrum (𝓞 F), GL (Fin n) (E ⊗[F] v.adicCompletion F))
    (hh : ∀ v, h v ∈ UPts σ J (v.adicCompletion F)) (S : Finset (HeightOneSpectrum (𝓞 F))) :
    ∃ x ∈ UPts σ J (Ad F), (∀ v ∈ S, bc (prV (E := E) v) x = h v) ∧
      ∀ v ∉ S, bc (prV (E := E) v) x = 1 := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, one_mem _, by simp, fun v _ => map_one _⟩
  | insert w S hw ih =>
    obtain ⟨x, hx, h1, h2⟩ := ih
    have hne : ∀ v, v ≠ w →
        bc (prV (E := E) v) (Formalism.UG.P.afsplitU w (h w) x) = bc (prV (E := E) v) x := fun v hv =>
      Units.ext (Formalism.UG.P.afsplitC_prV_ne w v hv _ _)
    refine ⟨Formalism.UG.P.afsplitU w (h w) x, Formalism.UG.P.afsplitU_mem w σ J _ _ (hh w) hx, ?_, ?_⟩
    · intro v hv
      by_cases e : v = w
      · subst e
        exact Units.ext (Formalism.UG.P.afsplitC_prV v _ _)
      · rw [hne v e]
        exact h1 v ((Finset.mem_insert.1 hv).resolve_left e)
    · intro v hv
      rw [Finset.mem_insert, not_or] at hv
      rw [hne v hv.1]
      exact h2 v hv.2

theorem exists_adelic_of_finite_support : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (h : ∀ v : HeightOneSpectrum (𝓞 F), GL (Fin n) (E ⊗[F] v.adicCompletion F)), (∀ v, h v ∈ UPts σ J (v.adicCompletion F)) → {v | h v ≠ 1}.Finite → ∃ x ∈ UPts σ J (Ad F), ∀ v, bc (prV (E := E) v) x = h v := by
  intro F E _ _ _ _ _ n σ J h hh hf
  obtain ⟨x, hx, h1, h2⟩ := exists_adelic_of_finset σ J h hh hf.toFinset
  refine ⟨x, hx, fun v => ?_⟩
  by_cases hv : v ∈ hf.toFinset
  · exact h1 v hv
  · rw [h2 v hv]
    by_contra e
    exact hv (hf.mem_toFinset.2 fun e' => e e'.symm)

end GlobalTheory.St.G
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdelicUnitaryOfFiniteSupportStatement
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adelic_unitary_of_finite_support : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (h : ∀ v : HeightOneSpectrum (𝓞 F), GL (Fin n) (E ⊗[F] v.adicCompletion F)), (∀ v, h v ∈ UPts σ J (v.adicCompletion F)) → {v | h v ≠ 1}.Finite → ∃ x ∈ UPts σ J (Ad F), ∀ v, bc (prV (E := E) v) x = h v := by
  first | exact @GlobalTheory.St.G.exists_adelic_of_finite_support | exact GlobalTheory.St.G.exists_adelic_of_finite_support | (intros; apply GlobalTheory.St.G.exists_adelic_of_finite_support <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CoveringRadiiIff
open NumberField Matrix Finset

noncomputable section

namespace GlobalTheory.CoverRadiiEq

open Formalism.MainNotions.S GlobalTheory.Count

section Lie

variable {A : Type} [CommRing A] {n : ℕ}

theorem hform_eq_dot (s : A →+* A) (M : Matrix (Fin n) (Fin n) A) (u u' : Fin n → A) :
    Formalism.UG.hform s M u u' = (fun i => s (u i)) ⬝ᵥ (M *ᵥ u') := by
  unfold Formalism.UG.hform
  simp only [dotProduct, mulVec, Finset.mul_sum, mul_assoc]

theorem hform_skew (s : A →+* A) (J Y : Matrix (Fin n) (Fin n) A) (u u' : Fin n → A) :
    Formalism.UG.hform s J (Y *ᵥ u) u' + Formalism.UG.hform s J u (Y *ᵥ u') =
      Formalism.UG.hform s (Formalism.UG.cT s Y * J + J * Y) u u' := by
  rw [hform_eq_dot, hform_eq_dot, hform_eq_dot]
  have h1 : (fun i => s ((Y *ᵥ u) i)) = (Y.map s) *ᵥ (fun i => s (u i)) := by
    funext i
    set_option synthInstance.maxHeartbeats 100000 in
      simp [mulVec, dotProduct, map_sum, map_mul]
  have h2 : ((Y.map s) *ᵥ (fun i => s (u i))) ⬝ᵥ (J *ᵥ u') =
      (fun i => s (u i)) ⬝ᵥ (((Y.map s)ᵀ * J) *ᵥ u') := by
    rw [← mulVec_mulVec, dotProduct_mulVec (fun i => s (u i)) (Y.map s)ᵀ, vecMul_transpose]
  rw [h1, h2, mulVec_mulVec, ← dotProduct_add, ← add_mulVec]
  rfl

private lemma hform_single_single' (s : A →+* A) (M : Matrix (Fin n) (Fin n) A) (i j : Fin n) :
    Formalism.UG.hform s M (Pi.single i 1) (Pi.single j 1) = M i j := by
  rw [hform_eq_dot]
  have e : (fun a => s ((Pi.single i (1 : A) : Fin n → A) a)) = (Pi.single i 1 : Fin n → A) := by
    funext a
    by_cases h : a = i
    · subst h; simp
    · simp [Pi.single_apply, h]
  rw [e]
  simp

theorem skew_iff (s : A →+* A) (J Y : Matrix (Fin n) (Fin n) A) :
    Formalism.UG.cT s Y * J + J * Y = 0 ↔ GlobalTheory.IndefiniteRowSideFullHecke.CenteredPerpendicularSets.IsSkew s J Y := by
  constructor
  · intro h u u'
    rw [hform_skew, h, hform_eq_dot, zero_mulVec, dotProduct_zero]
  · intro h
    ext i j
    rw [Matrix.zero_apply, ← hform_single_single' s (Formalism.UG.cT s Y * J + J * Y) i j, ← hform_skew]
    exact h _ _

end Lie

variable (I : AutInst)

end GlobalTheory.CoverRadiiEq
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GgOneAndIsClass
open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

namespace GlobalTheory.GLq.GGDeg

variable {g : ℕ} [Fact g.Prime]

theorem isUnit_of_isUniUp {n : ℕ} {M : Mt g n} (h : IsUniUp M) : IsUnit M := by
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_of_upperTriangular (fun a b hab => (h a b).1 hab),
    Finset.prod_eq_one fun a _ => (h a a).2 rfl]
  exact isUnit_one

theorem card_uniUp_mat (n : ℕ) :
    (Finset.univ.filter fun M : Mt g n => IsUniUp M).card = ∏ i : Fin n, g ^ (i : ℕ) := by
  have h : (Finset.univ.filter fun M : Mt g n => IsUniUp M) =
      (Fintype.piFinset fun a : Fin n => Fintype.piFinset fun b : Fin n =>
        (if a < b then Finset.univ else if a = b then {1} else {0} : Finset (ZMod g)) :
          Finset (Fin n → Fin n → ZMod g)) := by
    ext M
    rw [Finset.mem_filter, and_iff_right (Finset.mem_univ _)]
    refine Iff.trans ?_ Fintype.mem_piFinset.symm
    refine forall_congr' fun a => Iff.trans (forall_congr' fun b => ?_) Fintype.mem_piFinset.symm
    rcases lt_trichotomy a b with hab | hab | hab
    · simp [hab, hab.ne, hab.not_gt]
    · subst hab; simp
    · simp [hab, hab.ne', hab.not_gt]
  rw [h]
  erw [Fintype.card_piFinset]
  simp only [Fintype.card_piFinset]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun b _ => ?_
  have h2 : ∀ a : Fin n, (if a < b then Finset.univ else if a = b then {1} else {0} : Finset (ZMod g)).card =
      if a < b then g else 1 := by
    intro a
    split_ifs <;> simp [ZMod.card]
  simp only [h2]
  rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
  congr 1
  rw [show (Finset.univ.filter fun a : Fin n => a < b) = Finset.Iio b by ext; simp]
  simp

theorem card_uniUp (n : ℕ) :
    (Finset.univ.filter fun u : Gn g n => IsUniUp (u : Mt g n)).card = ∏ i : Fin n, g ^ (i : ℕ) := by
  rw [← card_uniUp_mat]
  refine Finset.card_bij (fun u _ => (u : Mt g n)) ?_ ?_ ?_
  · intro u hu
    simpa using hu
  · intro u _ v _ h
    exact Units.ext h
  · intro M hM
    have hM' : IsUniUp M := by simpa using hM
    exact ⟨(isUnit_of_isUniUp hM').unit, by simpa using hM', rfl⟩

theorem card_Gn (n : ℕ) : (Fintype.card (Gn g n) : ℂ) =
    (∏ i : Fin n, (g : ℂ) ^ (i : ℕ)) * ∏ i ∈ Finset.Icc 1 n, ((g : ℂ) ^ i - 1) := by
  have hg : 0 < g := (Fact.out : g.Prime).pos
  rw [← Nat.card_eq_fintype_card, Matrix.card_GL_field, ZMod.card, Nat.cast_prod]
  have h1 : ∏ i ∈ Finset.Icc 1 n, ((g : ℂ) ^ i - 1) = ∏ i : Fin n, ((g : ℂ) ^ (n - i) - 1) := by
    rw [Fin.prod_univ_eq_prod_range (fun i => ((g : ℂ) ^ (n - i) - 1)) n]
    refine Finset.prod_bij' (fun i _ => n - i) (fun i _ => n - i) ?_ ?_ ?_ ?_ ?_ <;>
      simp only [Finset.mem_Icc, Finset.mem_range] <;> intro i hi
    · omega
    · omega
    · omega
    · omega
    · rw [show n - (n - i) = i by omega]
  rw [h1, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Nat.cast_sub (Nat.pow_le_pow_right hg i.2.le), mul_sub, ← pow_add,
    show (i : ℕ) + (n - i) = n by have := i.2; omega]
  push_cast
  ring

theorem gg_one_and_isClass : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ) (n : ℕ),
    gg ψ n 1 = ∏ i ∈ Finset.Icc 1 n, ((g : ℂ) ^ i - 1) ∧ IsClass (gg ψ n) := by
  intro g _ ψ n
  have hg : (g : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : g.Prime).ne_zero
  constructor
  · have h1 : IsUniUp (1 : Mt g n) := fun a b =>
      ⟨fun h => Matrix.one_apply_ne h.ne', fun h => h ▸ Matrix.one_apply_eq a⟩
    have h2 : ∀ i, entN (1 : Mt g n) i (i + 1) = 0 := by
      intro i
      unfold entN
      split_ifs with h
      · exact Matrix.one_apply_ne (by simp)
      · rfl
    unfold gg
    simp only [mul_one, inv_mul_cancel, Units.val_one, h1, if_true, h2, Finset.sum_const_zero,
      AddChar.map_zero_eq_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [card_uniUp, card_Gn]
    push_cast
    rw [inv_mul_cancel_left₀ (Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ hg)]
  · intro x z
    unfold gg
    congr 1
    refine (Fintype.sum_equiv (Equiv.mulLeft z) _ _ fun y => ?_).symm
    have : (Equiv.mulLeft z y)⁻¹ * (z * x * z⁻¹) * (Equiv.mulLeft z y) = y⁻¹ * x * y := by
      simp [mul_assoc]
    rw [this]

end GlobalTheory.GLq.GGDeg
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MajorantIntegrable
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count
open scoped InnerProductSpace

namespace GlobalTheory.Count.Majorant

theorem decE_le_exp (q : ℕ) (hq : 1 ≤ q) (h d : ℝ) (hh : 0 ≤ h) (hd : 0 ≤ d) :
    decE q h d ≤ Real.exp (h / 8) * Real.exp (-(h / (8 * Real.sqrt q) * d)) := by
  have hs : (1 : ℝ) ≤ Real.sqrt q := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hq)
  have hm : d / Real.sqrt q - 1 ≤ min (2 * d ^ 2) (d / Real.sqrt q) := by
    have h1 : d / Real.sqrt q ≤ d := div_le_self hd hs
    exact le_min (by nlinarith [sq_nonneg (d - 1 / 4)]) (by linarith)
  have key : h / (8 * Real.sqrt q) * d = h / 8 * (d / Real.sqrt q) := by
    rw [div_mul_eq_mul_div, div_mul_div_comm]
  have hmul := mul_le_mul_of_nonneg_left hm (by linarith : (0 : ℝ) ≤ h / 8)
  unfold GlobalTheory.Count.decE
  rw [← Real.exp_add, Real.exp_le_exp, key]
  nlinarith [hmul]

theorem dOp_eq_zero {n : ℕ} (ε : Fin n → Bool) (h0 : rkR ε = 0) (g : UJ ε) : dOp (uMat g) = 0 := by
  have hall : (∀ a, ε a = false) ∨ (∀ a, ε a = true) := by
    unfold GlobalTheory.Count.rkR at h0
    rcases Nat.min_eq_zero_iff.mp h0 with h1 | h1
    · left
      intro a
      have ha : a ∉ univ.filter (fun a => ε a = true) := by
        rw [Finset.card_eq_zero.mp h1]; simp
      simpa using ha
    · right
      intro a
      have ha : a ∉ univ.filter (fun a => ε a = false) := by
        rw [Finset.card_eq_zero.mp h1]; simp
      simpa using ha
  have hJ : Jm ε = 1 ∨ Jm ε = -1 := by
    rcases hall with hf | ht
    · right
      ext i j
      by_cases hij : i = j <;> simp [Jm, Matrix.diagonal_apply, Matrix.one_apply, hf, hij]
    · left
      ext i j
      by_cases hij : i = j <;> simp [Jm, Matrix.diagonal_apply, Matrix.one_apply, ht, hij]
  have hg : inUJ ε (uMat g) := g.2
  have hu : uMat g ∈ Matrix.unitaryGroup (Fin n) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
    unfold inUJ at hg
    rcases hJ with hJ | hJ <;> rw [hJ] at hg <;> simpa using hg
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    unfold GlobalTheory.Count.dOp
    have hle : ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (uMat g))‖ ≤ 0 :=
      ContinuousLinearMap.opNorm_le_bound _ le_rfl fun x => by simp [EuclideanSpace.norm_eq]
    rw [le_antisymm hle (norm_nonneg _), Real.log_zero]
  · have hP0 : inP ε (0 : Matrix (Fin n) (Fin n) ℂ) := by simp [inP, inG]
    obtain ⟨hb0, hb1, -⟩ := GlobalTheory.Count.Cartan.dOp_bounds hn hu hP0
    rw [NormedSpace.exp_zero, mul_one] at hb0 hb1
    have hs0 : hs (0 : Matrix (Fin n) (Fin n) ℂ) = 0 := by simp [hs]
    rw [hs0, Real.sqrt_zero] at hb1
    nlinarith [Real.sqrt_pos.mpr (two_pos : (0 : ℝ) < 2)]

theorem majorant_integrable : ∀ (n : ℕ) (ε : Fin n → Bool) (h s : ℝ), 0 ≤ h → (rkR ε = 0 ∨ 8 * Real.sqrt (rkR ε) * (s + 4 * n * rkR ε) < h) → Integrable (fun g : UJ ε => decE (rkR ε) h (dOp (uMat g)) * Real.exp (s * dOp (uMat g))) (muG ε) := by
  intro n ε h s hh hcase
  obtain ⟨C, -, hC⟩ := GlobalTheory.T.haar_ball_growth_unitaryJ n ε
  have hcont : Continuous (fun g : UJ ε => dOp (uMat g)) :=
    (GlobalTheory.Count.Cartan.cartan_distances n ε).2.2.2.2
  have hmeas : Measurable (fun g : UJ ε => dOp (uMat g)) := hcont.measurable
  have hdec : Continuous (decE (rkR ε) h) := by
    unfold GlobalTheory.Count.decE
    fun_prop
  have hint_meas : AEStronglyMeasurable
      (fun g : UJ ε => decE (rkR ε) h (dOp (uMat g)) * Real.exp (s * dOp (uMat g))) (muG ε) :=
    ((hdec.comp hcont).mul (Real.continuous_exp.comp (continuous_const.mul hcont))).aestronglyMeasurable
  by_cases hq : rkR ε = 0
  · have hz : ∀ g : UJ ε, dOp (uMat g) = 0 := fun g => dOp_eq_zero ε hq g
    have hI := GlobalTheory.T.integrable_exp_neg_mul_of_sublevel_le_exp (UJ ε) (muG ε) (fun g => dOp (uMat g)) (4 * n * rkR ε)
      (4 * n * rkR ε + 1) C hmeas (fun g => by simp [hz g]) hC (by linarith)
    refine hI.congr (ae_of_all _ fun g => ?_)
    simp [hz g, GlobalTheory.Count.decE]
  · have hq1 : 1 ≤ rkR ε := Nat.one_le_iff_ne_zero.mpr hq
    have hlt : 8 * Real.sqrt (rkR ε) * (s + 4 * n * rkR ε) < h := hcase.resolve_left hq
    have hrk : rkR ε ≤ n := by
      unfold GlobalTheory.Count.rkR
      exact (min_le_left _ _).trans ((Finset.card_le_univ _).trans (Fintype.card_fin n).le)
    have hn : 1 ≤ n := hq1.trans hrk
    have hpos : ∀ g : UJ ε, 0 ≤ dOp (uMat g) := fun g =>
      ((GlobalTheory.Count.Cartan.cartan_distances n ε).2.1 g g hn).1
    have hsq : 0 < Real.sqrt (rkR ε) := Real.sqrt_pos.mpr (by exact_mod_cast Nat.pos_of_ne_zero hq)
    have hab : (4 * n * rkR ε : ℝ) < h / (8 * Real.sqrt (rkR ε)) - s := by
      have : s + 4 * n * rkR ε < h / (8 * Real.sqrt (rkR ε)) :=
        (lt_div_iff₀ (by linarith : (0 : ℝ) < 8 * Real.sqrt (rkR ε))).mpr (by linarith)
      linarith
    have hI := (GlobalTheory.T.integrable_exp_neg_mul_of_sublevel_le_exp (UJ ε) (muG ε) (fun g => dOp (uMat g)) (4 * n * rkR ε)
      (h / (8 * Real.sqrt (rkR ε)) - s) C hmeas hpos hC hab).const_mul (Real.exp (h / 8))
    refine hI.mono' hint_meas (ae_of_all _ fun g => ?_)
    have hd := hpos g
    have hE := decE_le_exp (rkR ε) hq1 h (dOp (uMat g)) hh hd
    have hnn : 0 ≤ decE (rkR ε) h (dOp (uMat g)) * Real.exp (s * dOp (uMat g)) := by
      unfold GlobalTheory.Count.decE
      positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    calc decE (rkR ε) h (dOp (uMat g)) * Real.exp (s * dOp (uMat g))
        ≤ Real.exp (h / 8) * Real.exp (-(h / (8 * Real.sqrt (rkR ε)) * dOp (uMat g))) *
            Real.exp (s * dOp (uMat g)) := mul_le_mul_of_nonneg_right hE (Real.exp_pos _).le
      _ = Real.exp (h / 8) * Real.exp (-((h / (8 * Real.sqrt (rkR ε)) - s) * dOp (uMat g))) := by
          rw [mul_assoc, ← Real.exp_add]
          congr 2
          ring

end GlobalTheory.Count.Majorant
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardDoubleCosetMulCardInter
open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

namespace GlobalTheory.GLm

theorem card_doubleCoset_mul_card_inter {G : Type} [Group G] [Fintype G] (H K : Subgroup G) (w : G) :
    (Finset.univ.filter fun y : G => ∃ h ∈ H, ∃ k ∈ K, y = h * w * k).card *
      (Finset.univ.filter fun x : G => x ∈ H ∧ w⁻¹ * x * w ∈ K).card = Nat.card H * Nat.card K := by
  have hmaps : ∀ p ∈ (Finset.univ : Finset (H × K)),
      (p.1 : G) * w * p.2 ∈ Finset.univ.filter fun y : G => ∃ h ∈ H, ∃ k ∈ K, y = h * w * k := by
    intro p _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨p.1, p.1.2, p.2, p.2.2, rfl⟩
  have hcard := Finset.card_eq_sum_card_fiberwise
    (f := fun p : H × K => (p.1 : G) * w * p.2) (s := Finset.univ) hmaps
  have hfib : ∀ y ∈ (Finset.univ.filter fun y : G => ∃ h ∈ H, ∃ k ∈ K, y = h * w * k),
      ((Finset.univ : Finset (H × K)).filter fun p => (p.1 : G) * w * p.2 = y).card =
        (Finset.univ.filter fun x : G => x ∈ H ∧ w⁻¹ * x * w ∈ K).card := by
    intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    obtain ⟨h0, hh0, k0, hk0, rfl⟩ := hy
    symm
    refine Finset.card_bij'
      (fun t ht => ((⟨h0 * t, H.mul_mem hh0 (Finset.mem_filter.1 ht).2.1⟩ : H),
        (⟨w⁻¹ * t⁻¹ * w * k0, by
          have hinv := K.inv_mem (Finset.mem_filter.1 ht).2.2
          rw [show (w⁻¹ * t * w)⁻¹ = w⁻¹ * t⁻¹ * w by group] at hinv
          exact K.mul_mem hinv hk0⟩ : K)))
      (fun p _ => h0⁻¹ * (p.1 : G)) ?_ ?_ ?_ ?_
    · intro t _
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      group
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
      have e : (p.1 : G) = h0 * w * k0 * (p.2 : G)⁻¹ * w⁻¹ := by
        rw [← hp]; group
      refine ⟨H.mul_mem (H.inv_mem hh0) p.1.2, ?_⟩
      rw [e, show w⁻¹ * (h0⁻¹ * (h0 * w * k0 * (p.2 : G)⁻¹ * w⁻¹)) * w = k0 * (p.2 : G)⁻¹ by group]
      exact K.mul_mem hk0 (K.inv_mem p.2.2)
    · intro t _
      group
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
      have e : (p.2 : G) = w⁻¹ * (p.1 : G)⁻¹ * (h0 * w * k0) := by
        rw [← hp]; group
      ext
      · simp
      · simp only
        rw [e]
        group
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul] at hcard
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ← Fintype.card_prod, ← Finset.card_univ,
    hcard]

private theorem sum_conj_double_coset_eq_of_invariant {G : Type} [Group G] [Fintype G] (H K : Subgroup G) (w h k : G)
    (hh : h ∈ H) (hk : k ∈ K) (lam φ : G → ℂ)
    (hlam : ∀ h ∈ H, ∀ x ∈ H, lam (h * x * h⁻¹) = lam x)
    (hφ : ∀ k ∈ K, ∀ x ∈ K, φ (k * x * k⁻¹) = φ x) :
    (∑ x : G, if x ∈ H ∧ (h * w * k)⁻¹ * x * (h * w * k) ∈ K then
        lam x * φ ((h * w * k)⁻¹ * x * (h * w * k)) else 0) =
      ∑ x : G, if x ∈ H ∧ w⁻¹ * x * w ∈ K then lam x * φ (w⁻¹ * x * w) else 0 := by
  refine (Fintype.sum_equiv (MulAut.conj h).toEquiv _ _ fun x => ?_).symm
  simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply]
  have e1 : (h * w * k)⁻¹ * (h * x * h⁻¹) * (h * w * k) = k⁻¹ * (w⁻¹ * x * w) * k := by group
  simp only [e1]
  have eH : h * x * h⁻¹ ∈ H ↔ x ∈ H := by
    rw [H.mul_mem_cancel_right (H.inv_mem hh), H.mul_mem_cancel_left hh]
  have eK : k⁻¹ * (w⁻¹ * x * w) * k ∈ K ↔ w⁻¹ * x * w ∈ K := by
    rw [K.mul_mem_cancel_right hk, K.mul_mem_cancel_left (K.inv_mem hk)]
  by_cases hx : x ∈ H ∧ w⁻¹ * x * w ∈ K
  · have hc := hφ k⁻¹ (K.inv_mem hk) _ hx.2
    rw [inv_inv] at hc
    rw [if_pos hx, if_pos ⟨eH.2 hx.1, eK.2 hx.2⟩, hlam h hh x hx.1, hc]
  · rw [if_neg hx, if_neg]
    rintro ⟨h1, h2⟩
    exact hx ⟨eH.1 h1, eK.1 h2⟩

theorem mackey_doubleCoset_pairing : ∀ (G : Type) [Group G] [Fintype G] (H K : Subgroup G) (ι : Type) (R : Finset ι) (w : ι → G), (∀ x : G, ∃! i, i ∈ R ∧ ∃ h ∈ H, ∃ k ∈ K, x = h * w i * k) → ∀ (lam φ : G → ℂ), (∀ h ∈ H, ∀ x ∈ H, lam (h * x * h⁻¹) = lam x) → (∀ k ∈ K, ∀ x ∈ K, φ (k * x * k⁻¹) = φ x) → (Nat.card H : ℂ)⁻¹ * ∑ x : G, (if x ∈ H then lam x * ((Nat.card K : ℂ)⁻¹ * ∑ y : G, if y⁻¹ * x * y ∈ K then φ (y⁻¹ * x * y) else 0) else 0) = ∑ i ∈ R, ((Finset.univ.filter fun x : G => x ∈ H ∧ (w i)⁻¹ * x * w i ∈ K).card : ℂ)⁻¹ * ∑ x : G, if x ∈ H ∧ (w i)⁻¹ * x * w i ∈ K then lam x * φ ((w i)⁻¹ * x * w i) else 0 := by
  intro G _ _ H K ι R w hR lam φ hlam hφ
  have hHpos : (Nat.card H : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  have hKpos : (Nat.card K : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  have h1 : ∀ x : G, (if x ∈ H then lam x * ((Nat.card K : ℂ)⁻¹ *
        ∑ y : G, if y⁻¹ * x * y ∈ K then φ (y⁻¹ * x * y) else 0) else 0) =
      (Nat.card K : ℂ)⁻¹ * ∑ y : G,
        (if x ∈ H ∧ y⁻¹ * x * y ∈ K then lam x * φ (y⁻¹ * x * y) else 0) := by
    intro x
    by_cases hx : x ∈ H
    · rw [if_pos hx]
      simp only [Finset.mul_sum]
      refine Finset.sum_congr rfl fun y _ => ?_
      by_cases hy : y⁻¹ * x * y ∈ K
      · rw [if_pos hy, if_pos ⟨hx, hy⟩]; ring
      · rw [if_neg hy, if_neg (fun hc => hy hc.2)]; ring
    · simp [hx]
  rw [Finset.sum_congr rfl (fun x _ => h1 x), ← Finset.mul_sum, Finset.sum_comm]
  have h2 : ∀ y : G, (∑ x : G,
        (if x ∈ H ∧ y⁻¹ * x * y ∈ K then lam x * φ (y⁻¹ * x * y) else 0)) =
      ∑ i ∈ R, if (∃ h ∈ H, ∃ k ∈ K, y = h * w i * k) then
        (∑ x : G, if x ∈ H ∧ (w i)⁻¹ * x * w i ∈ K then lam x * φ ((w i)⁻¹ * x * w i) else 0)
        else 0 := by
    intro y
    obtain ⟨i, ⟨hi, h, hhH, k, hkK, rfl⟩, huniq⟩ := hR y
    rw [Finset.sum_eq_single_of_mem i hi]
    · rw [if_pos ⟨h, hhH, k, hkK, rfl⟩]
      exact sum_conj_double_coset_eq_of_invariant H K (w i) h k hhH hkK lam φ hlam hφ
    · intro j hj hji
      rw [if_neg]
      intro hP
      exact hji (huniq j ⟨hj, hP⟩)
  rw [Finset.sum_congr rfl (fun y _ => h2 y), Finset.sum_comm]
  have h3 : ∀ i ∈ R, (∑ y : G, if (∃ h ∈ H, ∃ k ∈ K, y = h * w i * k) then
        (∑ x : G, if x ∈ H ∧ (w i)⁻¹ * x * w i ∈ K then lam x * φ ((w i)⁻¹ * x * w i) else 0)
        else 0) =
      ((Nat.card H : ℂ) * Nat.card K) *
        ((Finset.univ.filter fun x : G => x ∈ H ∧ (w i)⁻¹ * x * w i ∈ K).card : ℂ)⁻¹ *
        (∑ x : G, if x ∈ H ∧ (w i)⁻¹ * x * w i ∈ K then lam x * φ ((w i)⁻¹ * x * w i) else 0) := by
    intro i _
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have hc : ((Finset.univ.filter fun y : G => ∃ h ∈ H, ∃ k ∈ K, y = h * w i * k).card : ℂ) *
        ((Finset.univ.filter fun x : G => x ∈ H ∧ (w i)⁻¹ * x * w i ∈ K).card : ℂ) =
          (Nat.card H : ℂ) * Nat.card K := by
      exact_mod_cast card_doubleCoset_mul_card_inter H K (w i)
    have hI : ((Finset.univ.filter fun x : G => x ∈ H ∧ (w i)⁻¹ * x * w i ∈ K).card : ℂ) ≠ 0 := by
      have hmem : (1 : G) ∈ Finset.univ.filter fun x : G => x ∈ H ∧ (w i)⁻¹ * x * w i ∈ K := by
        simp [H.one_mem, K.one_mem]
      exact_mod_cast (Finset.card_pos.2 ⟨1, hmem⟩).ne'
    rw [← hc, mul_inv_cancel_right₀ hI]
  rw [Finset.sum_congr rfl h3, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have e1 : (Nat.card H : ℂ)⁻¹ * Nat.card H = 1 := inv_mul_cancel₀ hHpos
  have e2 : (Nat.card K : ℂ)⁻¹ * Nat.card K = 1 := inv_mul_cancel₀ hKpos
  linear_combination
    ((Nat.card K : ℂ)⁻¹ * Nat.card K *
      ((Finset.univ.filter fun x : G => x ∈ H ∧ (w i)⁻¹ * x * w i ∈ K).card : ℂ)⁻¹ *
      (∑ x : G, if x ∈ H ∧ (w i)⁻¹ * x * w i ∈ K then lam x * φ ((w i)⁻¹ * x * w i) else 0)) * e1 +
    (((Finset.univ.filter fun x : G => x ∈ H ∧ (w i)⁻¹ * x * w i ∈ K).card : ℂ)⁻¹ *
      (∑ x : G, if x ∈ H ∧ (w i)⁻¹ * x * w i ∈ K then lam x * φ ((w i)⁻¹ * x * w i) else 0)) * e2

end GlobalTheory.GLm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BernsteinZelevinskyDerivativeGLnEqTwistedSum
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BernsteinZelevinskyDerivativeGLnEqTwistedSum
open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

namespace GlobalTheory.GLm.DerFormula

variable {g : ℕ} [Fact g.Prime]

theorem isUnit_of_isUniUp {N : ℕ} {M : Mt g N} (hM : IsUniUp M) : IsUnit M := by
  have htri : M.BlockTriangular id := fun i j hij => (hM i j).1 hij
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_of_isUpperTriangular htri]
  simp [(hM _ _).2 rfl]

theorem card_lt_pairs (N : ℕ) : Fintype.card {p : Fin N × Fin N // p.1 < p.2} = N * (N - 1) / 2 := by
  rw [Fintype.card_subtype, Finset.card_filter, Fintype.sum_prod_type, Finset.sum_comm]
  have hb : ∀ b : Fin N, (∑ a : Fin N, if a < b then 1 else 0) = (b : ℕ) := by
    intro b
    rw [← Finset.card_filter, ← Fin.card_Iio b]
    congr 1
    ext a
    simp
  simp only [hb]
  rw [Fin.sum_univ_eq_sum_range (fun i => i) N, Finset.sum_range_id]

def ofUpper {N : ℕ} (f : {p : Fin N × Fin N // p.1 < p.2} → ZMod g) : Mt g N :=
  fun a b => if h : a < b then f ⟨(a, b), h⟩ else if a = b then 1 else 0

theorem isUniUp_ofUpper {N : ℕ} (f : {p : Fin N × Fin N // p.1 < p.2} → ZMod g) : IsUniUp (ofUpper f) := by
  intro a b
  refine ⟨fun hba => ?_, fun hab => ?_⟩
  · simp only [ofUpper, dif_neg (not_lt.mpr hba.le), if_neg hba.ne']
  · subst hab
    simp [ofUpper]

theorem card_uniUp (N : ℕ) :
    (Finset.univ.filter fun u : Gn g N => IsUniUp (u : Mt g N)).card = g ^ (N * (N - 1) / 2) := by
  rw [← Fintype.card_subtype]
  have e : {u : Gn g N // IsUniUp (u : Mt g N)} ≃ ({p : Fin N × Fin N // p.1 < p.2} → ZMod g) :=
    { toFun := fun u p => (u.1 : Mt g N) p.1.1 p.1.2
      invFun := fun f => ⟨(isUnit_of_isUniUp (isUniUp_ofUpper f)).unit, isUniUp_ofUpper f⟩
      left_inv := by
        rintro ⟨u, hu⟩
        apply Subtype.ext
        apply Units.ext
        dsimp only
        rw [IsUnit.unit_spec]
        funext a b
        show ofUpper _ a b = (u : Mt g N) a b
        rcases lt_trichotomy a b with hab | rfl | hab
        · simp only [ofUpper, dif_pos hab]
        · simp only [ofUpper, dif_neg (lt_irrefl a)]
          exact ((hu a a).2 rfl).symm
        · simp only [ofUpper, dif_neg (not_lt.mpr hab.le), if_neg hab.ne']
          exact ((hu a b).1 hab).symm
      right_inv := by
        intro f
        funext p
        dsimp only
        rw [IsUnit.unit_spec]
        show ofUpper f p.1.1 p.1.2 = f p
        simp only [ofUpper, dif_pos p.2] }
  rw [Fintype.card_congr e, Fintype.card_fun, ZMod.card, card_lt_pairs]

theorem eU_coeff (ψ : AddChar (ZMod g) ℂ) (N : ℕ) (u : Gn g N) :
    (eU g N ψ).coeff u = if IsUniUp (u : Mt g N) then
      ((g : ℂ) ^ (N * (N - 1) / 2))⁻¹ * (ψ (∑ i ∈ Finset.range (N - 1), entN (u : Mt g N) i (i + 1)))⁻¹ else 0 := by
  unfold eU eDat
  rw [MonoidAlgebra.coeff_smul_apply, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  simp only [MonoidAlgebra.coeff_single, Finsupp.single_apply, Finset.sum_ite_eq', Finset.mem_filter,
    Finset.mem_univ, true_and, card_uniUp, Nat.cast_pow, smul_eq_mul]
  split_ifs <;> simp

theorem sum_br (i n : ℕ) (M : Mt g n) :
    ∑ j ∈ Finset.range (n - i - 1), entN (br i (n - i) M) j (j + 1) = supFrom i M := by
  unfold supFrom
  rw [Finset.sum_Ico_eq_sum_range, show n - 1 - i = n - i - 1 by omega]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_range] at hj
  have h1 : j < n - i := by omega
  have h2 : j + 1 < n - i := by omega
  have hbr : entN (br i (n - i) M) j (j + 1) = entN M (i + j) (i + (j + 1)) := by
    conv_lhs => unfold entN
    rw [dif_pos ⟨h1, h2⟩]
    rfl
  rw [hbr, add_assoc]

end GlobalTheory.GLm.DerFormula

namespace GlobalTheory.GLm

open DerFormula

theorem der_eq_sum : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ) (i n : ℕ) (F : Gn g n → ℂ) (h : Gn g i), i ≤ n → der ψ i F h = ((g : ℂ) ^ (i * (n - i) + (n - i) * (n - i - 1) / 2))⁻¹ * ∑ x : Gn g n, if InR i (x : Mt g n) ∧ tl i (x : Mt g n) = (h : Mt g i) then F x * (ψ (supFrom i (x : Mt g n)))⁻¹ else 0 := by
  intro g _ ψ i n F h _
  have key : ∀ x : Gn g n, (∑ v : Gn g (n - i),
      (if IsUniUp (v : Mt g (n - i)) then
        (ψ (∑ j ∈ Finset.range (n - i - 1), entN (v : Mt g (n - i)) j (j + 1)))⁻¹ else 0) *
      (if InPar i (x : Mt g n) ∧ tl i (x : Mt g n) = (h : Mt g i) ∧
          br i (n - i) (x : Mt g n) = (v : Mt g (n - i)) then F x else 0)) =
      if InR i (x : Mt g n) ∧ tl i (x : Mt g n) = (h : Mt g i) then
        F x * (ψ (supFrom i (x : Mt g n)))⁻¹ else 0 := by
    intro x
    unfold InR
    by_cases hx : (InPar i (x : Mt g n) ∧ IsUniUp (br i (n - i) (x : Mt g n))) ∧
        tl i (x : Mt g n) = (h : Mt g i)
    · obtain ⟨⟨hP, hU⟩, ht⟩ := hx
      have hv0 : ((isUnit_of_isUniUp hU).unit : Mt g (n - i)) = br i (n - i) (x : Mt g n) :=
        IsUnit.unit_spec _
      rw [Finset.sum_eq_single (isUnit_of_isUniUp hU).unit]
      · rw [if_pos (by rw [hv0]; exact hU), if_pos ⟨hP, ht, hv0.symm⟩, if_pos ⟨⟨hP, hU⟩, ht⟩, hv0, sum_br,
          mul_comm]
      · intro v _ hv
        refine mul_eq_zero_of_right _ (if_neg ?_)
        rintro ⟨-, -, hb⟩
        exact hv (Units.ext (hb.symm.trans hv0.symm))
      · intro hv
        exact absurd (Finset.mem_univ _) hv
    · rw [if_neg hx]
      refine Finset.sum_eq_zero fun v _ => ?_
      by_cases hv : IsUniUp (v : Mt g (n - i))
      · refine mul_eq_zero_of_right _ (if_neg ?_)
        rintro ⟨hP, ht, hb⟩
        exact hx ⟨⟨hP, by rw [hb]; exact hv⟩, ht⟩
      · rw [if_neg hv, zero_mul]
  simp only [der, wh, tr, res, eU_coeff]
  calc _ = ∑ v : Gn g (n - i), ((g : ℂ) ^ (i * (n - i)))⁻¹ * ((g : ℂ) ^ ((n - i) * (n - i - 1) / 2))⁻¹ *
        ∑ x : Gn g n, (if IsUniUp (v : Mt g (n - i)) then
          (ψ (∑ j ∈ Finset.range (n - i - 1), entN (v : Mt g (n - i)) j (j + 1)))⁻¹ else 0) *
          (if InPar i (x : Mt g n) ∧ tl i (x : Mt g n) = (h : Mt g i) ∧
            br i (n - i) (x : Mt g n) = (v : Mt g (n - i)) then F x else 0) := by
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [← Finset.mul_sum]
        split_ifs <;> ring
    _ = _ := by
        rw [← Finset.mul_sum, Finset.sum_comm]
        simp only [key]
        rw [pow_add, mul_inv]

end GlobalTheory.GLm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BernsteinZelevinskyDerivativeGLnEqTwistedSumStatement
open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bernsteinZelevinskyDerivativeGLn_eq_twisted_sum : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ) (i n : ℕ) (F : Gn g n → ℂ) (h : Gn g i), i ≤ n → der ψ i F h = ((g : ℂ) ^ (i * (n - i) + (n - i) * (n - i - 1) / 2))⁻¹ * ∑ x : Gn g n, if InR i (x : Mt g n) ∧ tl i (x : Mt g n) = (h : Mt g i) then F x * (ψ (supFrom i (x : Mt g n)))⁻¹ else 0 := by
  first | exact @GlobalTheory.GLm.der_eq_sum | exact GlobalTheory.GLm.der_eq_sum | (intros; apply GlobalTheory.GLm.der_eq_sum <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsMirabolicConjInvariantTwistedTailMeanFun
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsMirabolicConjInvariantTwistedTailMeanFun
noncomputable section

namespace GlobalTheory.GLm.TailClass

open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

variable {g : ℕ} [Fact g.Prime] {m k : ℕ}

def dM (k : ℕ) (A : Mt g m) : Mt g (m + k) :=
  (Matrix.fromBlocks A 0 0 (1 : Mt g k)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm

theorem dM_mul (A B : Mt g m) : dM k A * dM k B = dM k (A * B) := by
  simp [dM, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]

theorem dM_one : dM k (1 : Mt g m) = 1 := by
  simp [dM, Matrix.fromBlocks_one]

def dG (k : ℕ) (p : Gn g m) : Gn g (m + k) :=
  ⟨dM k p.val, dM k p.inv, by rw [dM_mul, p.val_inv, dM_one], by rw [dM_mul, p.inv_val, dM_one]⟩

theorem conj_val (p : Gn g m) (x : Gn g (m + k)) :
    ((dG k p * x * (dG k p)⁻¹ : Gn g (m + k)) : Mt g (m + k)) =
      dM k (p : Mt g m) * (x : Mt g (m + k)) * dM k ((p⁻¹ : Gn g m) : Mt g m) := rfl

theorem tl_apply (X : Mt g (m + k)) (i j : Fin m) : tl m X i j = X (Fin.castAdd k i) (Fin.castAdd k j) := by
  have h : (i : ℕ) < m + k ∧ (j : ℕ) < m + k := ⟨by omega, by omega⟩
  rw [tl, entN, dif_pos h]; rfl

theorem upperLeftBlock_blockDiagExtendByIdentity_conj (A B : Mt g m) (X : Mt g (m + k)) : tl m (dM k A * X * dM k B) = A * tl m X * B := by
  ext i j
  simp [tl_apply, dM, Matrix.mul_apply, Fin.sum_univ_add]

theorem blockDiagExtendByIdentity_conj_upperRight_apply (A B : Mt g m) (X : Mt g (m + k)) (i : Fin m) (j : Fin k) :
    (dM k A * X * dM k B) (Fin.castAdd k i) (Fin.natAdd m j) =
      ∑ l, A i l * X (Fin.castAdd k l) (Fin.natAdd m j) := by
  simp [dM, Matrix.mul_apply, Fin.sum_univ_add, Matrix.one_apply]

theorem blockDiagExtendByIdentity_conj_lowerLeft_apply (A B : Mt g m) (X : Mt g (m + k)) (i : Fin k) (j : Fin m) :
    (dM k A * X * dM k B) (Fin.natAdd m i) (Fin.castAdd k j) =
      ∑ l, X (Fin.natAdd m i) (Fin.castAdd k l) * B l j := by
  simp [dM, Matrix.mul_apply, Fin.sum_univ_add, Matrix.one_apply]

theorem blockDiagExtendByIdentity_conj_lowerRight_apply (A B : Mt g m) (X : Mt g (m + k)) (i j : Fin k) :
    (dM k A * X * dM k B) (Fin.natAdd m i) (Fin.natAdd m j) = X (Fin.natAdd m i) (Fin.natAdd m j) := by
  simp [dM, Matrix.mul_apply, Fin.sum_univ_add, Matrix.one_apply]

theorem entN_blockDiagExtendByIdentity_conj_lowerRight (A B : Mt g m) (X : Mt g (m + k)) (i j : ℕ) (hi : m ≤ i) (hj : m ≤ j) :
    entN (dM k A * X * dM k B) i j = entN X i j := by
  unfold entN
  split_ifs with h
  · have e1 : (⟨i, h.1⟩ : Fin (m + k)) = Fin.natAdd m ⟨i - m, by omega⟩ := by ext; simp; omega
    have e2 : (⟨j, h.2⟩ : Fin (m + k)) = Fin.natAdd m ⟨j - m, by omega⟩ := by ext; simp; omega
    rw [e1, e2, blockDiagExtendByIdentity_conj_lowerRight_apply]
  · rfl

theorem inR_conj (A B : Mt g m) (X : Mt g (m + k)) (h : InR m X) : InR m (dM k A * X * dM k B) := by
  refine ⟨fun i j hj hi => ?_, ?_⟩
  · have e1 : i = Fin.natAdd m ⟨i - m, by omega⟩ := by ext; simp; omega
    have e2 : j = Fin.castAdd k ⟨j, hj⟩ := by ext; simp
    rw [e1, e2, blockDiagExtendByIdentity_conj_lowerLeft_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [h.1 _ _ (by simp) (by simp), zero_mul]
  · have : br m (m + k - m) (dM k A * X * dM k B) = br m (m + k - m) X := by
      ext i j
      exact entN_blockDiagExtendByIdentity_conj_lowerRight A B X _ _ (by omega) (by omega)
    rw [this]; exact h.2

theorem supFrom_conj (hm : 1 ≤ m) (A B : Mt g m) (hA : InMir A) (X : Mt g (m + k)) :
    supFrom (m - 1) (dM k A * X * dM k B) = supFrom (m - 1) X := by
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_Ico] at hj
  by_cases h : m ≤ j
  · exact entN_blockDiagExtendByIdentity_conj_lowerRight A B X _ _ h (by omega)
  · have h' : j < m + k ∧ j + 1 < m + k := ⟨by omega, by omega⟩
    have e1 : (⟨j, h'.1⟩ : Fin (m + k)) = Fin.castAdd k ⟨j, by omega⟩ := by ext; simp
    have e2 : (⟨j + 1, h'.2⟩ : Fin (m + k)) = Fin.natAdd m ⟨0, by omega⟩ := by ext; simp; omega
    rw [entN, entN, dif_pos h', dif_pos h', e1, e2, blockDiagExtendByIdentity_conj_upperRight_apply]
    have : ∀ l, A ⟨j, by omega⟩ l = (1 : Mt g m) ⟨j, by omega⟩ l := fun l => hA _ _ (by simp; omega)
    simp [this, Matrix.one_apply]

theorem inMir_of (X : Mt g (m + k)) (h : InR m X) (h0 : InMir (tl m X)) : InMir X := by
  intro i j hi
  by_cases him : (i : ℕ) < m
  · have hj : (j : ℕ) < m := by omega
    have e1 : i = Fin.castAdd k ⟨i, him⟩ := by ext; simp
    have e2 : j = Fin.castAdd k ⟨j, hj⟩ := by ext; simp
    have := h0 ⟨i, him⟩ ⟨j, hj⟩ (by simp; omega)
    rw [tl_apply, ← e1, ← e2] at this
    rw [this]
    simp [Matrix.one_apply, Fin.ext_iff]
  · by_cases hj : (j : ℕ) < m
    · rw [h.1 i j hj (by omega), Matrix.one_apply_ne]
      intro e; subst e; omega
    · have h2 := h.2 ⟨i - m, by omega⟩ ⟨j - m, by omega⟩
      have h' : m + (i - m) < m + k ∧ m + (j - m) < m + k := ⟨by omega, by omega⟩
      have e1 : (⟨m + (i - m), h'.1⟩ : Fin (m + k)) = i := by ext; simp; omega
      have e2 : (⟨m + (j - m), h'.2⟩ : Fin (m + k)) = j := by ext; simp; omega
      simp only [br, entN, dif_pos h', e1, e2] at h2
      by_cases e : i = j
      · subst e
        rw [h2.2 rfl, Matrix.one_apply_eq]
      · rw [Matrix.one_apply_ne e]
        refine h2.1 ?_
        have : (i : ℕ) ≠ j := fun h => e (Fin.ext h)
        rw [Fin.lt_def]
        simp only
        omega

theorem inMir_dM (A : Mt g m) (hA : InMir A) : InMir (dM k A) := by
  have e : dM k A = dM k A * 1 * dM k 1 := by rw [dM_one, mul_one, mul_one]
  have h1 : InR m (1 : Mt g (m + k)) := by
    refine ⟨fun i j hj hi => Matrix.one_apply_ne (by intro e; subst e; omega), fun a b => ?_⟩
    have h' : m + a < m + k ∧ m + b < m + k := ⟨by omega, by omega⟩
    simp only [br, entN, dif_pos h', Matrix.one_apply, Fin.ext_iff, Fin.lt_def]
    constructor
    · intro h; rw [if_neg (by omega)]
    · intro h; rw [if_pos (by omega)]
  have h2 : tl m (1 : Mt g (m + k)) = 1 := by
    ext i j
    simp [tl_apply, Matrix.one_apply, Fin.ext_iff]
  refine inMir_of _ (e ▸ inR_conj _ _ _ h1) ?_
  rw [e, upperLeftBlock_blockDiagExtendByIdentity_conj, h2, mul_one, mul_one]
  exact hA

theorem isMirClass_tail (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ) (m n : ℕ) (F : Gn g n → ℂ)
    (hm : 1 ≤ m) (hmn : m ≤ n) (hF : IsMirClass F) : IsMirClass (tail ψ m F) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  intro p x₀ hp hx₀
  unfold tail
  congr 1
  symm
  refine Fintype.sum_equiv (MulAut.conj (dG k p)).toEquiv _ _ fun x => ?_
  have e : (MulAut.conj (dG k p)).toEquiv x = dG k p * x * (dG k p)⁻¹ := rfl
  rw [e]
  have hiff : (InR m (x : Mt g (m + k)) ∧ tl m (x : Mt g (m + k)) = (x₀ : Mt g m)) ↔
      (InR m ((dG k p * x * (dG k p)⁻¹ : Gn g (m + k)) : Mt g (m + k)) ∧
        tl m ((dG k p * x * (dG k p)⁻¹ : Gn g (m + k)) : Mt g (m + k)) = ((p * x₀ * p⁻¹ : Gn g m) : Mt g m)) := by
    rw [conj_val, upperLeftBlock_blockDiagExtendByIdentity_conj, Units.val_mul, Units.val_mul, Units.mul_left_inj, Units.mul_right_inj]
    refine and_congr_left fun _ => ⟨inR_conj _ _ _, fun h => ?_⟩
    have := inR_conj ((p⁻¹ : Gn g m) : Mt g m) (p : Mt g m) _ h
    rwa [← mul_assoc, ← mul_assoc, mul_assoc _ (dM k _) (dM k _), dM_mul, Units.inv_mul, dM_one,
      one_mul, mul_one] at this
  by_cases h : InR m (x : Mt g (m + k)) ∧ tl m (x : Mt g (m + k)) = (x₀ : Mt g m)
  · rw [if_pos h, if_pos (hiff.1 h), hF _ _ (inMir_dM _ hp) (inMir_of _ h.1 (h.2 ▸ hx₀)), conj_val,
      supFrom_conj hm _ _ hp]
  · rw [if_neg h, if_neg (fun h' => h (hiff.2 h'))]

end GlobalTheory.GLm.TailClass
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsMirabolicConjInvariantTwistedTailMeanFunStatement
open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isMirabolicConjInvariant_twistedTailMeanFun : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ) (m n : ℕ) (F : Gn g n → ℂ), 1 ≤ m → m ≤ n → IsMirClass F → IsMirClass (tail ψ m F) := by
  first | exact @GlobalTheory.GLm.TailClass.isMirClass_tail | exact GlobalTheory.GLm.TailClass.isMirClass_tail | (intros; apply GlobalTheory.GLm.TailClass.isMirClass_tail <;> assumption)
end
end
