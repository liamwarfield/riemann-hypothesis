module

public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspRapidDecaySiegelGL
public import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsTamagawaMeasureNormalization
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvariantHermitianFormCuspidalRep

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EvFinSSOneNot
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open IsDedekindDomain NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.SPartTensor

section Generic

variable {F E A R : Type} [Field F] [Field E] [Algebra F E] [CommRing A] [Algebra F A] [CommRing R] [Algebra F R]

def tP (p : A →ₐ[F] R) : A ⊗[F] E →+* R ⊗[F] E := (Algebra.TensorProduct.map p (AlgHom.id F E)).toRingHom

def tQ (s : R →ₗ[F] A) : R ⊗[F] E →+ A ⊗[F] E := (LinearMap.rTensor E s).toAddMonoidHom

@[simp] theorem rTensor_tmul₂ (p : A →ₐ[F] R) (a : A) (x : E) : tP p (a ⊗ₜ[F] x) = p a ⊗ₜ[F] x := rfl

@[simp] theorem tQ_tmul (s : R →ₗ[F] A) (r : R) (x : E) : tQ s (r ⊗ₜ[F] x) = s r ⊗ₜ[F] x := rfl

theorem rTensor_includeRight (p : A →ₐ[F] R) (x : E) : tP p (inclR (F := F) A x) = inclR (F := F) R x := by
  change tP p ((1 : A) ⊗ₜ[F] x) = (1 : R) ⊗ₜ[F] x
  rw [rTensor_tmul₂, map_one]

theorem rTensor_lTensor_comm₂ (p : A →ₐ[F] R) (σ : E →ₐ[F] E) (x : A ⊗[F] E) :
    tP p (sigR A σ x) = sigR R σ (tP p x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a y => rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem tQ_sigR (s : R →ₗ[F] A) (σ : E →ₐ[F] E) (y : R ⊗[F] E) :
    tQ s (sigR R σ y) = sigR A σ (tQ s y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a y => rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem rTensor_rTensor_of_rightInverse (p : A →ₐ[F] R) (s : R →ₗ[F] A) (h : ∀ r, p (s r) = r) (y : R ⊗[F] E) :
    tP p (tQ s y) = y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a y => rw [tQ_tmul, rTensor_tmul₂, h]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem tQ_tP (p : A →ₐ[F] R) (s : R →ₗ[F] A) (b : A) (h : ∀ a, s (p a) = b * a) (x : A ⊗[F] E) :
    tQ s (tP p x) = (b ⊗ₜ[F] (1 : E)) * x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a y => rw [rTensor_tmul₂, tQ_tmul, h, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | add x y hx hy => simp only [map_add (f := _), hx, hy, mul_add]

theorem tQ_mul (s : R →ₗ[F] A) (h : ∀ r r', s (r * r') = s r * s r') (y y' : R ⊗[F] E) :
    tQ s (y * y') = tQ s y * tQ s y' := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy, add_mul]
  | tmul a z =>
    induction y' using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add (f := _), hx, hy, mul_add]
    | tmul b w =>
      rw [Algebra.TensorProduct.tmul_mul_tmul, tQ_tmul, tQ_tmul, tQ_tmul, h,
        Algebra.TensorProduct.tmul_mul_tmul]

end Generic

section Adelic

variable {F : Type} [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F)))

abbrev RS : Type := Ainf F × (∀ v : S, Fv F v.1)

def finOf (c : ∀ v : S, Fv F v.1) : Af F := ∑ v : S, singleFin v.1 (c v)

variable {S}

theorem evalV_finOf (c : ∀ v : S, Fv F v.1) (u : HeightOneSpectrum (𝓞 F)) (h : u ∈ S) :
    evalV F u (finOf S c) = c ⟨u, h⟩ := by
  unfold finOf
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.sum_eq_single (⟨u, h⟩ : S)
    (fun b _ hb => evalV_singleFin_ne (fun e => hb (Subtype.ext e.symm)) _) (by simp)]
  exact evalV_singleFin_self u _

theorem evalV_finOf_not (c : ∀ v : S, Fv F v.1) (u : HeightOneSpectrum (𝓞 F)) (h : u ∉ S) :
    evalV F u (finOf S c) = 0 := by
  unfold finOf
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  exact Finset.sum_eq_zero fun b _ => evalV_singleFin_ne (fun e => h (by rw [e]; exact b.2)) _

theorem af_ext {x y : Af F} (h : ∀ u, evalV F u x = evalV F u y) : x = y :=
  by first | exact RestrictedProduct.ext _ _ h | exact Subtype.ext (funext h)

variable (S)

def pS : AF F →ₐ[F] RS S :=
  (fstA F).prod (Pi.algHom F _ fun v : S => (evalV F v.1).comp (sndA F))

def sS : RS S →ₗ[F] AF F where
  toFun r := (r.1, finOf S r.2)
  map_add' r r' := by
    refine Prod.ext rfl ?_
    change finOf S (r.2 + r'.2) = finOf S r.2 + finOf S r'.2
    simp [finOf, Finset.sum_add_distrib]
  map_smul' a r := by
    refine Prod.ext rfl ?_
    change finOf S (a • r.2) = a • finOf S r.2
    simp [finOf, Finset.smul_sum]

variable {S}

theorem pS_sS (r : RS S) : pS S (sS S r) = r := by
  refine Prod.ext rfl (funext fun v => ?_)
  exact evalV_finOf r.2 v.1 v.2

theorem sS_mul (r r' : RS S) : sS S (r * r') = sS S r * sS S r' := by
  refine Prod.ext rfl (af_ext fun u => ?_)
  change evalV F u (finOf S (r.2 * r'.2)) = evalV F u (finOf S r.2 * finOf S r'.2)
  rw [map_mul]
  by_cases h : u ∈ S
  · rw [evalV_finOf _ u h, evalV_finOf _ u h, evalV_finOf _ u h]; rfl
  · rw [evalV_finOf_not _ u h, evalV_finOf_not _ u h, zero_mul]

theorem sS_pS (a : AF F) : sS S (pS S a) = sS S 1 * a := by
  refine Prod.ext (one_mul _).symm (af_ext fun u => ?_)
  change evalV F u (finOf S fun v : S => evalV F v.1 a.2) = evalV F u (finOf S 1 * a.2)
  rw [map_mul]
  by_cases h : u ∈ S
  · rw [evalV_finOf _ u h, evalV_finOf _ u h]; simp
  · rw [evalV_finOf_not _ u h, evalV_finOf_not _ u h, zero_mul]

theorem evInf_sS_one (w : InfinitePlace F) : evInf F w (sS S 1) = 1 := by
  change (GlobalTheory.AutFunCompare.evW w) (1 : Ainf F) = 1
  exact map_one _

theorem evFin_sS_one_mem {v : HeightOneSpectrum (𝓞 F)} (h : v ∈ S) : evFin F v (sS S 1) = 1 :=
  evalV_finOf _ v h

theorem evFin_sS_one_not {v : HeightOneSpectrum (𝓞 F)} (h : v ∉ S) : evFin F v (sS S 1) = 0 :=
  evalV_finOf_not _ v h

end Adelic

theorem sPartOf {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)
    (S : Finset (HeightOneSpectrum (𝓞 F))) (e : AF F ⊗[F] E)
    (hinj : ∀ a : AF F ⊗[F] E, (∀ w, compInf F E w a = 0) → (∀ v, compFin F E v a = 0) → a = 0)
    (h1 : ∀ w, compInf F E w e = 1) (h2 : ∀ v ∈ S, compFin F E v e = 1) (h3 : ∀ v, v ∉ S → compFin F E v e = 0) :
    ∃ (R : Type) (_ : CommRing R) (_ : Algebra F R) (_ : IsArtinianRing R) (_ : IsReduced R)
      (P : AF F ⊗[F] E →+* R ⊗[F] E) (Q : R ⊗[F] E →+ AF F ⊗[F] E),
      (∀ x, P (inclR (F := F) (AF F) x) = inclR R x) ∧ (∀ x, P (sigR (AF F) σ x) = sigR R σ (P x)) ∧
      (∀ y, Q (sigR R σ y) = sigR (AF F) σ (Q y)) ∧ (∀ y, P (Q y) = y) ∧ (∀ x, Q (P x) = e * x) ∧
      ∀ y y', Q (y * y') = Q y * Q y' := by
  have hE : e = (sS S 1 : AF F) ⊗ₜ[F] (1 : E) := by
    rw [← sub_eq_zero]
    refine hinj _ (fun w => ?_) (fun v => ?_)
    · rw [RingHom.map_sub, h1 w, sub_eq_zero]
      change (1 : _) = evInf F w (sS S 1) ⊗ₜ[F] (1 : E)
      rw [evInf_sS_one]; rfl
    · rw [RingHom.map_sub, sub_eq_zero]
      change _ = evFin F v (sS S 1) ⊗ₜ[F] (1 : E)
      by_cases h : v ∈ S
      · rw [h2 v h, evFin_sS_one_mem h]; rfl
      · rw [h3 v h, evFin_sS_one_not h, TensorProduct.zero_tmul]
  haveI : IsArtinianRing (Ainf F) := inferInstanceAs (IsArtinianRing (∀ v : InfinitePlace F, v.Completion))
  haveI : IsReduced (Ainf F) := inferInstanceAs (IsReduced (∀ v : InfinitePlace F, v.Completion))
  refine ⟨RS S, inferInstance, inferInstance, inferInstance, inferInstance, tP (pS S), tQ (sS S),
    rTensor_includeRight _, rTensor_lTensor_comm₂ _ _, tQ_sigR _ _, rTensor_rTensor_of_rightInverse _ _ pS_sS, fun x => ?_, tQ_mul _ sS_mul⟩
  rw [hE]
  exact tQ_tP _ _ _ sS_pS x

theorem sPart : (∀ (D : D7) (a : AE D), (∀ w, compInf D.host.F D.host.E w a = 0) → (∀ v, cv D v a = 0) → a = 0) →
    ∀ (D : D7) (S : Finset (Pl D)) (e : AE D), IsIdem S e →
    ∃ (R : Type) (_ : CommRing R) (_ : Algebra D.host.F R) (_ : IsArtinianRing R) (_ : IsReduced R)
      (P : AE D →+* R ⊗[D.host.F] D.host.E) (Q : R ⊗[D.host.F] D.host.E →+ AE D),
      (∀ x, P (incA D x) = inclR R x) ∧ (∀ x, P (cA D x) = sigR R D.sp.cm.sig (P x)) ∧
      (∀ y, Q (sigR R D.sp.cm.sig y) = cA D (Q y)) ∧ (∀ y, P (Q y) = y) ∧ (∀ x, Q (P x) = e * x) ∧
      ∀ y y', Q (y * y') = Q y * Q y' := by
  intro hinj D S e he
  exact sPartOf D.sp.cm.sig S e (hinj D) he.1 (fun v h => (he.2 v).trans (if_pos h))
    (fun v h => (he.2 v).trans (if_neg h))

end GlobalTheory.CompanionTheory.SPartTensor
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzTensorDensity
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzTensorDensity
noncomputable section

open GlobalTheory.CompanionTheory.ThTot

namespace GlobalTheory.CompanionTheory.ThTot.SchwT

section Analysis

variable {E E₁ E₂ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]

theorem norm_iter_comp_le (A : E →L[ℝ] E₁) (hA : ‖A‖ ≤ 1) (f : SchwartzMap E₁ ℂ) (n : ℕ) (z : E) :
    ‖iteratedFDeriv ℝ n (fun w => f (A w)) z‖ ≤ ‖iteratedFDeriv ℝ n f (A z)‖ := by
  have h : iteratedFDeriv ℝ n (fun w => f (A w)) z =
      (iteratedFDeriv ℝ n f (A z)).compContinuousLinearMap fun _ => A :=
    A.iteratedFDeriv_comp_right (f := f) (f.smooth n) z le_rfl
  rw [h]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have : ∏ _i : Fin n, ‖A‖ ≤ 1 := Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun _ _ => hA
  exact mul_le_of_le_one_right (norm_nonneg _) this

def tens (A : E →L[ℝ] E₁) (B : E →L[ℝ] E₂) (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1)
    (hAB : ∀ z, ‖z‖ ≤ max ‖A z‖ ‖B z‖) (f : SchwartzMap E₁ ℂ) (g : SchwartzMap E₂ ℂ) : SchwartzMap E ℂ where
  toFun z := f (A z) * g (B z)
  smooth' := ((f.smooth ⊤).comp A.contDiff).mul ((g.smooth ⊤).comp B.contDiff)
  decay' := by
    intro k n
    choose Cf hCf using fun (a : ℕ × ℕ) => f.decay' a.1 a.2
    choose Cg hCg using fun (a : ℕ × ℕ) => g.decay' a.1 a.2
    refine ⟨∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
      (Cf (k, i) * Cg (0, n - i) + Cf (0, i) * Cg (k, n - i)), fun z => ?_⟩
    have hf1 : ContDiff ℝ n (fun w => f (A w)) := (f.smooth n).comp A.contDiff
    have hg1 : ContDiff ℝ n (fun w => g (B w)) := (g.smooth n).comp B.contDiff
    have hL := norm_iteratedFDeriv_mul_le (𝕜 := ℝ) (n := n) (N := n) hf1 hg1 z le_rfl
    have hz : ‖z‖ ^ k ≤ ‖A z‖ ^ k + ‖B z‖ ^ k := by
      rcases le_total ‖A z‖ ‖B z‖ with h | h
      · have : ‖z‖ ≤ ‖B z‖ := (hAB z).trans (max_le h le_rfl)
        exact (pow_le_pow_left₀ (norm_nonneg _) this k).trans (le_add_of_nonneg_left (by positivity))
      · have : ‖z‖ ≤ ‖A z‖ := (hAB z).trans (max_le le_rfl h)
        exact (pow_le_pow_left₀ (norm_nonneg _) this k).trans (le_add_of_nonneg_right (by positivity))
    calc ‖z‖ ^ k * ‖iteratedFDeriv ℝ n (fun z => f (A z) * g (B z)) z‖
        ≤ ‖z‖ ^ k * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
            ‖iteratedFDeriv ℝ i (fun w => f (A w)) z‖ * ‖iteratedFDeriv ℝ (n - i) (fun w => g (B w)) z‖ :=
          mul_le_mul_of_nonneg_left hL (by positivity)
      _ = ∑ i ∈ Finset.range (n + 1), ‖z‖ ^ k * ((n.choose i : ℝ) *
            ‖iteratedFDeriv ℝ i (fun w => f (A w)) z‖ * ‖iteratedFDeriv ℝ (n - i) (fun w => g (B w)) z‖) :=
          Finset.mul_sum _ _ _
      _ ≤ _ := by
          refine Finset.sum_le_sum fun i _ => ?_
          set a := ‖iteratedFDeriv ℝ i f (A z)‖
          set b := ‖iteratedFDeriv ℝ (n - i) g (B z)‖
          have ha0 : 0 ≤ a := norm_nonneg _
          have hb0 : 0 ≤ b := norm_nonneg _
          have h1 : ‖A z‖ ^ k * a ≤ Cf (k, i) := hCf (k, i) (A z)
          have h2 : b ≤ Cg (0, n - i) := by
            have := hCg (0, n - i) (B z)
            simp only [pow_zero, one_mul] at this
            exact this
          have h3 : a ≤ Cf (0, i) := by
            have := hCf (0, i) (A z)
            simp only [pow_zero, one_mul] at this
            exact this
          have h4 : ‖B z‖ ^ k * b ≤ Cg (k, n - i) := hCg (k, n - i) (B z)
          have hn0 : (0 : ℝ) ≤ n.choose i := by positivity
          have hA' := norm_iter_comp_le A hA f i z
          have hB' := norm_iter_comp_le B hB g (n - i) z
          have hAk : 0 ≤ ‖A z‖ ^ k := by positivity
          have hBk : 0 ≤ ‖B z‖ ^ k := by positivity
          have e1 : ‖A z‖ ^ k * a * b ≤ Cf (k, i) * Cg (0, n - i) :=
            mul_le_mul h1 h2 hb0 ((mul_nonneg hAk ha0).trans h1)
          have e2 : a * (‖B z‖ ^ k * b) ≤ Cf (0, i) * Cg (k, n - i) :=
            mul_le_mul h3 h4 (mul_nonneg hBk hb0) (ha0.trans h3)
          calc ‖z‖ ^ k * ((n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun w => f (A w)) z‖ *
                ‖iteratedFDeriv ℝ (n - i) (fun w => g (B w)) z‖)
              ≤ (‖A z‖ ^ k + ‖B z‖ ^ k) * ((n.choose i : ℝ) * a * b) := by
                refine mul_le_mul hz ?_ (by positivity) (by positivity)
                exact mul_le_mul (mul_le_mul_of_nonneg_left hA' hn0) hB' (norm_nonneg _) (by positivity)
            _ = (n.choose i : ℝ) * (‖A z‖ ^ k * a * b + a * (‖B z‖ ^ k * b)) := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add e1 e2) hn0

@[simp] theorem tens_apply (A : E →L[ℝ] E₁) (B : E →L[ℝ] E₂) (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1)
    (hAB : ∀ z, ‖z‖ ≤ max ‖A z‖ ‖B z‖) (f : SchwartzMap E₁ ℂ) (g : SchwartzMap E₂ ℂ) (z : E) :
    tens A B hA hB hAB f g z = f (A z) * g (B z) := rfl

end Analysis

section Coord

variable {T : Type*} [Fintype T] {r s p : ℕ}

def topL (T : Type*) [Fintype T] (r s p : ℕ) : (T → Fin (r + s) → Fin p → ℂ) →L[ℝ] (T → Fin r → Fin p → ℂ) where
  toFun t := fun τ i j => t τ (Fin.castAdd s i) j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := by fun_prop

def botL (T : Type*) [Fintype T] (r s p : ℕ) : (T → Fin (r + s) → Fin p → ℂ) →L[ℝ] (T → Fin s → Fin p → ℂ) where
  toFun t := fun τ i j => t τ (Fin.natAdd r i) j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := by fun_prop

theorem norm_coord_le (t : T → Fin r → Fin p → ℂ) (τ : T) (i : Fin r) (j : Fin p) : ‖t τ i j‖ ≤ ‖t‖ :=
  (norm_le_pi_norm (t τ i) j).trans ((norm_le_pi_norm (t τ) i).trans (norm_le_pi_norm t τ))

theorem norm_le_of_coord {t : T → Fin r → Fin p → ℂ} {C : ℝ} (hC : 0 ≤ C) (h : ∀ τ i j, ‖t τ i j‖ ≤ C) : ‖t‖ ≤ C :=
  (pi_norm_le_iff_of_nonneg hC).2 fun τ => (pi_norm_le_iff_of_nonneg hC).2 fun i =>
    (pi_norm_le_iff_of_nonneg hC).2 fun j => h τ i j

theorem norm_topL_le : ‖topL T r s p‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun t => by
    rw [one_mul]
    exact norm_le_of_coord (norm_nonneg _) fun τ i j => norm_coord_le t τ _ j

theorem norm_botL_le : ‖botL T r s p‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun t => by
    rw [one_mul]
    exact norm_le_of_coord (norm_nonneg _) fun τ i j => norm_coord_le t τ _ j

theorem norm_le_max (t : T → Fin (r + s) → Fin p → ℂ) : ‖t‖ ≤ max ‖topL T r s p t‖ ‖botL T r s p t‖ := by
  refine norm_le_of_coord (le_max_of_le_left (norm_nonneg _)) fun τ i j => ?_
  induction i using Fin.addCases with
  | left a => exact le_max_of_le_left (norm_coord_le (topL T r s p t) τ a j)
  | right b => exact le_max_of_le_right (norm_coord_le (botL T r s p t) τ b j)

end Coord

section Finite

variable {R : Type} {tR : TopologicalSpace R} {r s p : ℕ}

def joinR (a : Fin r → Fin p → R) (b : Fin s → Fin p → R) : Fin (r + s) → Fin p → R :=
  fun i j => Fin.addCases (motive := fun _ => R) (fun u => a u j) (fun v => b v j) i

theorem continuous_joinR :
    Continuous fun q : (Fin r → Fin p → R) × (Fin s → Fin p → R) => joinR q.1 q.2 := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  induction i using Fin.addCases with
  | left a => simp only [joinR, Fin.addCases_left]; fun_prop
  | right b => simp only [joinR, Fin.addCases_right]; fun_prop

theorem sb_tensor {g : (Fin r → Fin p → R) → ℂ} {g' : (Fin s → Fin p → R) → ℂ}
    (hg : g ∈ GlobalTheory.WeilM.SB (Fin r → Fin p → R)) (hg' : g' ∈ GlobalTheory.WeilM.SB (Fin s → Fin p → R)) :
    (fun u : Fin (r + s) → Fin p → R =>
      g (fun i j => u (Fin.castAdd s i) j) * g' (fun i j => u (Fin.natAdd r i) j)) ∈
      GlobalTheory.WeilM.SB (Fin (r + s) → Fin p → R) := by
  obtain ⟨hl, hc⟩ := hg
  obtain ⟨hl', hc'⟩ := hg'
  have hT : Continuous fun u : Fin (r + s) → Fin p → R => fun (i : Fin r) (j : Fin p) => u (Fin.castAdd s i) j := by
    fun_prop
  have hB : Continuous fun u : Fin (r + s) → Fin p → R => fun (i : Fin s) (j : Fin p) => u (Fin.natAdd r i) j := by
    fun_prop
  have hlc := (hl.comp_continuous hT).mul (hl'.comp_continuous hB)
  refine ⟨hlc, ?_⟩
  set G : (Fin (r + s) → Fin p → R) → ℂ := fun u =>
    g (fun i j => u (Fin.castAdd s i) j) * g' (fun i j => u (Fin.natAdd r i) j) with hG
  have hlG : IsLocallyConstant G := hlc
  have hclosed : IsClosed (Function.support G) := by
    have : Function.support G = (G ⁻¹' {0})ᶜ := by ext u; simp [Function.mem_support]
    rw [this]
    exact (hlG.isOpen_fiber 0).isClosed_compl
  have hK : IsCompact ((fun q : (Fin r → Fin p → R) × (Fin s → Fin p → R) => joinR q.1 q.2) ''
      (tsupport g ×ˢ tsupport g')) := (IsCompact.prod hc hc').image continuous_joinR
  have hsub : Function.support G ⊆ (fun q : (Fin r → Fin p → R) × (Fin s → Fin p → R) => joinR q.1 q.2) ''
      (tsupport g ×ˢ tsupport g') := by
    intro u hu
    have hu' : G u ≠ 0 := hu
    refine ⟨(fun i j => u (Fin.castAdd s i) j, fun i j => u (Fin.natAdd r i) j), ⟨?_, ?_⟩, ?_⟩
    · exact subset_tsupport _ (left_ne_zero_of_mul hu')
    · exact subset_tsupport _ (right_ne_zero_of_mul hu')
    · funext i j
      induction i using Fin.addCases with
      | left a => simp [joinR]
      | right b => simp [joinR]
  have : HasCompactSupport G := by
    unfold HasCompactSupport tsupport
    rw [hclosed.closure_eq]
    exact hK.of_isClosed_subset hclosed hsub
  exact this

end Finite

theorem schwTensor : SchwTensor := by
  intro D θ _ r s p φ hφ φ' hφ'
  induction hφ using Submodule.span_induction with
  | zero =>
    convert (GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz.schwartzA θ (r + s) p).zero_mem using 1
    funext y; simp
  | add a b _ _ ha hb =>
    have := (GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz.schwartzA θ (r + s) p).add_mem ha hb
    convert this using 1
    funext y; simp [add_mul]
  | smul c a _ ha =>
    have := (GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz.schwartzA θ (r + s) p).smul_mem c ha
    convert this using 1
    funext y; simp [mul_assoc]
  | mem a ha =>
    obtain ⟨f, g, hg, rfl⟩ := ha
    induction hφ' using Submodule.span_induction with
    | zero =>
    convert (GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz.schwartzA θ (r + s) p).zero_mem using 1
    funext y; simp
    | add a b _ _ ha hb =>
      have := (GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz.schwartzA θ (r + s) p).add_mem ha hb
      convert this using 1
      funext y; simp [mul_add]
    | smul c a _ ha =>
      have := (GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz.schwartzA θ (r + s) p).smul_mem c ha
      convert this using 1
      funext y; simp only [Pi.smul_apply, smul_eq_mul]; ring
    | mem b hb =>
      obtain ⟨f', g', hg', rfl⟩ := hb
      refine Submodule.subset_span ⟨tens (topL _ r s p) (botL _ r s p) norm_topL_le norm_botL_le norm_le_max f f',
        _, sb_tensor hg hg', ?_⟩
      funext y
      simp only [tens_apply]
      exact mul_mul_mul_comm _ _ _ _

end GlobalTheory.CompanionTheory.ThTot.SchwT

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzTensorDensityStatement
open GlobalTheory.CompanionTheory.ThTot
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_tensor_density : SchwTensor := by
  first | exact @GlobalTheory.CompanionTheory.ThTot.SchwT.schwTensor | exact GlobalTheory.CompanionTheory.ThTot.SchwT.schwTensor | (intros; apply GlobalTheory.CompanionTheory.ThTot.SchwT.schwTensor <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PhaseContinuousUnitary
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PhaseContinuousUnitary
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField
open GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl GlobalTheory.CompanionTheory.SW.Core

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl

theorem psiFin_continuous_unit (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ)
    (hψ : IsCharAF F ψ) : Continuous (psiFin F ψ) ∧ ∀ y, ‖psiFin F ψ y‖ = 1 := by
  refine ⟨?_, fun y => hψ.2.1 _⟩
  have : Continuous fun y : Af F => pairA F 0 y := continuous_const.prodMk continuous_id
  exact hψ.1.comp this


set_option maxHeartbeats 1000000 in
theorem phaseB_pairB_props : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E)
    (n : ℕ) (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ (b : HermR (Af F) σ n),
    Continuous (phaseB σ J (psiFin F ψ) b) ∧ (∀ X, ‖phaseB σ J (psiFin F ψ) b X‖ = 1) ∧
    ∀ X, Continuous (pairB σ J (psiFin F ψ) b X) := by
  intro F E _ _ _ _ _ σ hσ M J n ψ hψ b
  obtain ⟨a1, a2, a3, -, -, -, -, -, -, -⟩ := GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F
  haveI : LocallyCompactSpace (Af F) := a1
  haveI : SecondCountableTopology (Af F) := a2
  haveI : T2Space (Af F) := a3
  obtain ⟨t1, -, -, -, hs, htr, -, -, -, hG⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ (Af F)
  haveI : IsTopologicalRing (Af F ⊗[F] E) := t1
  obtain ⟨hc, hn⟩ := psiFin_continuous_unit F ψ hψ
  refine ⟨?_, fun X => hn _, fun X => ?_⟩
  · refine hc.comp (continuous_const.mul (htr.comp (Continuous.matrix_trace
      (Continuous.matrix_mul continuous_const (hG n M J)))))
  · refine hc.comp (htr.comp (Continuous.matrix_trace
      (Continuous.matrix_mul continuous_const ?_)))
    refine continuous_matrix fun a c => ?_
    simp only [gram2, hR, Formalism.UG.hform]
    refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
    exact continuous_const.mul ((continuous_apply j).comp (continuous_apply c))

end GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PhaseContinuousUnitaryStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField
open GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl GlobalTheory.CompanionTheory.SW.Core

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.phase_continuous_unitary : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E)
    (n : ℕ) (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ (b : HermR (Af F) σ n),
    Continuous (phaseB σ J (psiFin F ψ) b) ∧ (∀ X, ‖phaseB σ J (psiFin F ψ) b X‖ = 1) ∧
    ∀ X, Continuous (pairB σ J (psiFin F ψ) b X) := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.phaseB_pairB_props | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.phaseB_pairB_props | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.phaseB_pairB_props <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DensityBoundByRecursion
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DensityBoundByRecursion
open scoped Matrix NNReal ENNReal TensorProduct
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.WhitFree GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.AvgFree MeasureTheory

namespace GlobalTheory.CompanionTheory.DensityIter

theorem bounded_density_of_iterated
    (H ι : Type) [MeasurableSpace H] (ν : Measure H) (D : Set H → ℝ≥0∞) (Dtot : ℝ≥0∞)
    (hDtot : Dtot ≠ ⊤) (hD : ∀ Y, MeasurableSet Y → D Y ≤ Dtot)
    (I : Finset ι) (α β : ι → ℝ≥0) (C₀ : ℝ≥0)
    (hit : ∀ Y, MeasurableSet Y → ∃ Z : ι → Set H,
      (∀ i ∈ I, MeasurableSet (Z i) ∧ ν (Z i) = β i * ν Y) ∧
        D Y ≤ C₀ * ν Y + ∑ i ∈ I, α i * D (Z i))
    (hρ : ∑ i ∈ I, α i * β i < 1) (hr : ∑ i ∈ I, α i < 1) :
    ∃ C : ℝ≥0, ∀ Y, MeasurableSet Y → D Y ≤ C * ν Y := by
  set ρ : ℝ≥0 := ∑ i ∈ I, α i * β i with hρdef
  set r : ℝ≥0 := ∑ i ∈ I, α i with hrdef
  set K : ℝ≥0 := C₀ / (1 - ρ) with hK
  have hKeq : C₀ + K * ρ = K := by
    have h1 : K * (1 - ρ) = C₀ := div_mul_cancel₀ C₀ (tsub_pos_of_lt hρ).ne'
    calc C₀ + K * ρ = K * (1 - ρ) + K * ρ := by rw [h1]
      _ = K * (1 - ρ + ρ) := by rw [mul_add]
      _ = K := by rw [tsub_add_cancel_of_le hρ.le, mul_one]
  have hKeq' : (C₀ : ℝ≥0∞) + K * ρ = K := by exact_mod_cast hKeq
  have hρc : (ρ : ℝ≥0∞) = ∑ i ∈ I, (α i : ℝ≥0∞) * β i := by
    simp only [hρdef, ENNReal.ofNNReal_finsetSum, ENNReal.coe_mul]
  have hrc : (r : ℝ≥0∞) = ∑ i ∈ I, (α i : ℝ≥0∞) := by
    simp only [hrdef, ENNReal.ofNNReal_finsetSum]
  have key : ∀ n : ℕ, ∀ Y, MeasurableSet Y → D Y ≤ K * ν Y + (r : ℝ≥0∞) ^ n * Dtot := by
    intro n
    induction n with
    | zero =>
      intro Y hY
      rw [pow_zero, one_mul]
      exact le_add_left (hD Y hY)
    | succ n ih =>
      intro Y hY
      obtain ⟨Z, hZ, hDY⟩ := hit Y hY
      have e1 : ∑ i ∈ I, (α i : ℝ≥0∞) * (K * ((β i : ℝ≥0∞) * ν Y)) = K * ρ * ν Y := by
        rw [hρc, Finset.mul_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => by ring
      have e2 : ∑ i ∈ I, (α i : ℝ≥0∞) * ((r : ℝ≥0∞) ^ n * Dtot) = (r : ℝ≥0∞) ^ (n + 1) * Dtot := by
        rw [← Finset.sum_mul, ← hrc]
        ring
      calc D Y ≤ C₀ * ν Y + ∑ i ∈ I, α i * D (Z i) := hDY
        _ ≤ C₀ * ν Y + ∑ i ∈ I, (α i : ℝ≥0∞) * (K * ((β i : ℝ≥0∞) * ν Y) + (r : ℝ≥0∞) ^ n * Dtot) := by
          gcongr with i hi
          rw [← (hZ i hi).2]
          exact ih _ (hZ i hi).1
        _ = C₀ * ν Y + (K * ρ * ν Y + (r : ℝ≥0∞) ^ (n + 1) * Dtot) := by
          simp only [mul_add, Finset.sum_add_distrib, e1, e2]
        _ = K * ν Y + (r : ℝ≥0∞) ^ (n + 1) * Dtot := by
          rw [← add_assoc, ← add_mul, hKeq']
  refine ⟨K, fun Y hY => ?_⟩
  have hr1 : (r : ℝ≥0∞) < 1 := by exact_mod_cast hr
  have ht : Filter.Tendsto (fun n : ℕ => (K : ℝ≥0∞) * ν Y + (r : ℝ≥0∞) ^ n * Dtot) Filter.atTop
      (nhds ((K : ℝ≥0∞) * ν Y + 0 * Dtot)) :=
    tendsto_const_nhds.add
      (ENNReal.Tendsto.mul_const (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hr1) (Or.inr hDtot))
  rw [zero_mul, add_zero] at ht
  exact ge_of_tendsto' ht fun n => key n Y hY

end GlobalTheory.CompanionTheory.DensityIter
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DensityBoundByRecursionStatement
open scoped Matrix NNReal ENNReal TensorProduct
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.WhitFree GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.AvgFree MeasureTheory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.density_bound_by_recursion : ∀ (H ι : Type) [MeasurableSpace H] (ν : Measure H) (D : Set H → ℝ≥0∞) (Dtot : ℝ≥0∞), Dtot ≠ ⊤ → (∀ Y, MeasurableSet Y → D Y ≤ Dtot) → ∀ (I : Finset ι) (α β : ι → ℝ≥0) (C₀ : ℝ≥0), (∀ Y, MeasurableSet Y → ∃ Z : ι → Set H, (∀ i ∈ I, MeasurableSet (Z i) ∧ ν (Z i) = β i * ν Y) ∧ D Y ≤ C₀ * ν Y + ∑ i ∈ I, α i * D (Z i)) → ∑ i ∈ I, α i * β i < 1 → ∑ i ∈ I, α i < 1 → ∃ C : ℝ≥0, ∀ Y, MeasurableSet Y → D Y ≤ C * ν Y := by
  first | exact @GlobalTheory.CompanionTheory.DensityIter.bounded_density_of_iterated | exact GlobalTheory.CompanionTheory.DensityIter.bounded_density_of_iterated | (intros; apply GlobalTheory.CompanionTheory.DensityIter.bounded_density_of_iterated <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanMatrixPreservesForm
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeisenbergCoords
open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.HeisCoords

open Matrix

section Cplx

variable {n : ℕ} (J : Matrix (Fin n) (Fin n) ℂ)

variable {J}

end Cplx

section Coords

variable {n : ℕ} {J : Matrix (Fin n) (Fin n) ℂ}

end Coords

section Transfer

open Formalism.UG (cT bc UJ)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {J : Matrix (Fin n) (Fin n) E} {ν : InfinitePlace F}

theorem archMat_unitary (hcm : IsCMExt F E σ) (τ : EmbOver E ν) (g : HA ν.Completion σ J) :
    (GlobalTheory.Orb.archMat σ J τ g)ᴴ * J.map τ.1 * GlobalTheory.Orb.archMat σ J τ g = J.map τ.1 :=
  (archEquiv J hcm τ g).2

end Transfer

open Formalism.UG (cT bc UJ)

end GlobalTheory.HeisCoords

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanMatrixPreservesForm
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.CFin
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.CompanionTheory.CFin

theorem archMat_projArch_unitary : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (g : GAd σ J) (w : InfinitePlace F) (τ : EmbOver E w), cT (starRingEnd ℂ) (archMat σ J τ (projArch σ J w g)) * J.map τ.1 * archMat σ J τ (projArch σ J w g) = J.map τ.1 := by
  intro F E _ _ _ _ _ σ hcm n J g w τ
  have h := GlobalTheory.HeisCoords.archMat_unitary hcm τ (projArch σ J w g)
  have e : cT (starRingEnd ℂ) (archMat σ J τ (projArch σ J w g)) = (archMat σ J τ (projArch σ J w g))ᴴ := by
    ext i j
    simp [cT, Matrix.conjTranspose_apply]
  rw [e]
  exact h

end GlobalTheory.CompanionTheory.CFin
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanMatrixPreservesFormStatement
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.CFin
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_matrix_preserves_form : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (g : GAd σ J) (w : InfinitePlace F) (τ : EmbOver E w), cT (starRingEnd ℂ) (archMat σ J τ (projArch σ J w g)) * J.map τ.1 * archMat σ J τ (projArch σ J w g) = J.map τ.1 := by
  first | exact @GlobalTheory.CompanionTheory.CFin.archMat_projArch_unitary | exact GlobalTheory.CompanionTheory.CFin.archMat_projArch_unitary | (intros; apply GlobalTheory.CompanionTheory.CFin.archMat_projArch_unitary <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUnitForm
noncomputable section

open NumberField IsDedekindDomain Matrix Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.LFun PositivityTheory.JacquetShalikaLocal

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.JSUnit

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem norm_central (π : CuspSub E a) (H : π.V →ₗ⋆[ℂ] π.V →ₗ[ℂ] ℂ) (hp : ∀ φ, φ ≠ 0 → 0 < (H φ φ).re)
    (hi : ∀ k φ ψ, H (π.op (.fin k) φ) (π.op (.fin k) ψ) = H φ ψ) {ω : HChar E} (hω : π.HasCentChar ω) (z) :
    ‖((ω.1 (finId E z) : ℂˣ) : ℂ)‖ = 1 := by
  have := Submodule.nontrivial_iff_ne_bot.2 π.ne_bot
  obtain ⟨x, hx⟩ := exists_ne (0 : π.V)
  have h1 : π.op (.fin (GeneralLinearGroup.scalar (Fin a) z)) x = ((ω.1 (finId E z) : ℂˣ) : ℂ) • x := hω z x
  have h2 := hi (GeneralLinearGroup.scalar (Fin a) z) x x
  rw [h1] at h2
  generalize ((ω.1 (finId E z) : ℂˣ) : ℂ) = c at h2 ⊢
  simp only [map_smulₛₗ, map_smul, LinearMap.smul_apply, smul_eq_mul] at h2
  have hne : H x x ≠ 0 := fun e => by
    have h := hp x hx
    simp [e] at h
  have h3 : starRingEnd ℂ c * c = 1 := mul_right_cancel₀ hne (by linear_combination h2)
  rw [Complex.conj_mul'] at h3
  have h4 : ‖c‖ ^ 2 = 1 := by exact_mod_cast h3
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h4

theorem norm_loc (π : CuspSub E a) (H : π.V →ₗ⋆[ℂ] π.V →ₗ[ℂ] ℂ) (hp : ∀ φ, φ ≠ 0 → 0 < (H φ φ).re)
    (hi : ∀ k φ ψ, H (π.op (.fin k) φ) (π.op (.fin k) ψ) = H φ ψ) (χ : HChar E) {ω : HChar E} (hu : ω.IsUnitary)
    (hω : (π.twist χ).HasCentChar ω) (ha : a ≠ 0) (w : HeightOneSpectrum (𝓞 E)) (g : GL (Fin a) (w.adicCompletion E)) :
    ‖((χ.loc w (GeneralLinearGroup.det g) : ℂˣ) : ℂ)‖ = 1 := by
  have e : (π.twist χ).twist χ⁻¹ = π := by
    rw [← CuspSub.twist_mul, mul_inv_cancel, CuspSub.twist_one]
  have h2 := hω.twist χ⁻¹
  rw [e] at h2
  have h3 := norm_central π H hp hi h2 (GeneralLinearGroup.det (locGL E a w g))
  rw [finId_det_locGL] at h3
  generalize GeneralLinearGroup.det g = u at h3 ⊢
  have h4 : ‖((ω.loc w u : ℂˣ) : ℂ)‖ = 1 := hu _
  have h5 : (ω * χ⁻¹ ^ a).loc w u = ω.loc w u * (χ.loc w u)⁻¹ ^ a := rfl
  change ‖(((ω * χ⁻¹ ^ a).loc w u : ℂˣ) : ℂ)‖ = 1 at h3
  rw [h5] at h3
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, norm_mul, norm_pow, norm_inv, h4,
    one_mul] at h3
  have h6 := (pow_eq_one_iff_of_nonneg (by positivity) ha).1 h3
  exact inv_eq_one.1 h6

theorem exists_unit_form : G1 := by
  intro E _ _ _ a π hu w
  obtain ⟨ω, hωu, hω⟩ := hu
  rw [CG.hasCentChar_mk] at hω
  obtain ⟨π₀, χ, hn, rfl⟩ := GlobalTheory.CompanionTheory.TwistNorm.exists_twist_normalised π
  obtain ⟨H, h1, h2, h3, -, -⟩ := GlobalTheory.GelfandKazhdanHerm.exists_invariant_hermitian
    GlobalTheory.CompanionTheory.CuspFinGL.cuspFormsBoundedGL E a π₀ hn
  let T := π₀.toTwist χ
  have hT : ∀ g x, (π₀.twist χ).locRep w g (T x) =
      ((χ.loc w (GeneralLinearGroup.det g) : ℂˣ) : ℂ) • T (π₀.locRep w g x) := fun g x => by
    rw [CuspSub.locRep_eq, CuspSub.op_toTwist, opAdd, zero_smul, add_zero, map_smul, opMul, CuspSub.chiDet_locGL]
    rfl
  have hn1 : ∀ g : GL (Fin a) (w.adicCompletion E), ‖((χ.loc w (GeneralLinearGroup.det g) : ℂˣ) : ℂ)‖ = 1 := fun g => by
    rcases eq_or_ne a 0 with rfl | ha
    · rw [show GeneralLinearGroup.det g = 1 from Units.ext (by simp [Matrix.det_isEmpty]), map_one]
      simp
    · exact norm_loc π₀ H h2 h3 χ hωu hω ha w g
  refine ⟨(H.comp T.symm.toLinearMap).compl₂ T.symm.toLinearMap, ?_⟩
  refine And.intro (fun u v => ?_) (And.intro (fun u hu => ?_) fun g u v => ?_)
  · simpa using h1 (T.symm u) (T.symm v)
  · exact h2 _ (T.symm.map_ne_zero_iff.2 hu)
  · obtain ⟨u, rfl⟩ := T.surjective u
    obtain ⟨v, rfl⟩ := T.surjective v
    rw [hT, hT]
    generalize hc : ((χ.loc w (GeneralLinearGroup.det g) : ℂˣ) : ℂ) = c
    have hcc : starRingEnd ℂ c * c = 1 := by
      rw [Complex.conj_mul', ← hc, hn1 g]
      simp
    simp only [LinearMap.compl₂_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, map_smulₛₗ, map_smul, LinearMap.smul_apply,
      LinearEquiv.symm_apply_apply, smul_eq_mul]
    rw [CuspSub.locRep_eq, h3, ← mul_assoc, RingHom.id_apply, mul_comm c, hcc, one_mul]

end GlobalTheory.CompanionTheory.JSUnit

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaussSumFiniteAverageBound
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaussSumFiniteAverageBound
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField
open GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl GlobalTheory.CompanionTheory.SW.Core

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.CosetBound

theorem twisted_integral_finite_coset_combination_bound :
    ∀ (X : Type) [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    [SecondCountableTopology X] [T2Space X] [MeasurableSpace X] [BorelSpace X] (m : Measure X) [m.IsAddHaarMeasure]
    (L : AddSubgroup X), IsCompact (L : Set X) → IsOpen (L : Set X) →
    ∀ (q : X → ℂ), Continuous q → (∀ x, ‖q x‖ = 1) → ∀ K : ℝ,
    (∀ x₀ : X, ‖∫ x in {y | y - x₀ ∈ L}, q x ∂m‖ ^ 2 ≤ K) →
    ∀ (Q : X → ℂ) (s : Finset X),
    (∀ x, Q x = ∑ a ∈ s, Q a * Set.indicator {y | y - a ∈ L} (fun _ => (1 : ℂ)) x) →
    ‖∫ x, Q x * q x ∂m‖ ≤ (∑ a ∈ s, ‖Q a‖) * √K := by
  intro X _ _ _ _ _ _ _ m _ L hc ho q hq hn K hK Q s hQ
  have hopen : ∀ a : X, IsOpen {y : X | y - a ∈ L} := fun a =>
    ho.preimage (continuous_id.sub continuous_const)
  have hmeas : ∀ a : X, MeasurableSet {y : X | y - a ∈ L} := fun a => (hopen a).measurableSet
  have hcomp : ∀ a : X, IsCompact {y : X | y - a ∈ L} := by
    intro a
    have himg : {y : X | y - a ∈ L} = (fun x => x + a) '' (L : Set X) := by
      ext y
      constructor
      · intro hy
        exact ⟨y - a, hy, by simp⟩
      · rintro ⟨x, hx, rfl⟩
        simpa using hx
    rw [himg]
    exact hc.image (continuous_id.add continuous_const)
  have hion : ∀ a : X, IntegrableOn q {y : X | y - a ∈ L} m := fun a =>
    hq.continuousOn.integrableOn_compact (hcomp a)
  have hterm : ∀ a : X, (fun x => Set.indicator {y : X | y - a ∈ L} (fun _ => (1 : ℂ)) x * q x)
      = Set.indicator {y : X | y - a ∈ L} q := by
    intro a
    funext x
    by_cases hx : x ∈ {y : X | y - a ∈ L}
    · simp only [Set.indicator_of_mem hx, one_mul]
    · simp only [Set.indicator_of_notMem hx, zero_mul]
  have hint : ∀ a : X, Integrable (Set.indicator {y : X | y - a ∈ L} q) m := fun a =>
    (integrable_indicator_iff (hmeas a)).2 (hion a)
  have hfun : (fun x => Q x * q x)
      = fun x => ∑ a ∈ s, Q a * Set.indicator {y : X | y - a ∈ L} q x := by
    funext x
    conv_lhs => rw [hQ x]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [mul_assoc, congrFun (hterm a) x]
  have hsum : ∫ x, Q x * q x ∂m = ∑ a ∈ s, Q a * ∫ x in {y : X | y - a ∈ L}, q x ∂m := by
    rw [hfun, integral_finsetSum s (fun a _ => (hint a).const_mul (Q a))]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [integral_const_mul, integral_indicator (hmeas a)]
  have hone : ∀ a : X, ‖∫ x in {y : X | y - a ∈ L}, q x ∂m‖ ≤ √K := by
    intro a
    have h := Real.abs_le_sqrt (hK a)
    rwa [abs_of_nonneg (norm_nonneg _)] at h
  rw [hsum, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hone a) (norm_nonneg _)

end GlobalTheory.CompanionTheory.SiegelND.Integ.CosetBound
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaussSumFiniteAverageBoundStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField
open GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl GlobalTheory.CompanionTheory.SW.Core

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gauss_sum_finite_average_bound : ∀ (X : Type) [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    [SecondCountableTopology X] [T2Space X] [MeasurableSpace X] [BorelSpace X] (m : Measure X) [m.IsAddHaarMeasure]
    (L : AddSubgroup X), IsCompact (L : Set X) → IsOpen (L : Set X) →
    ∀ (q : X → ℂ), Continuous q → (∀ x, ‖q x‖ = 1) → ∀ K : ℝ,
    (∀ x₀ : X, ‖∫ x in {y | y - x₀ ∈ L}, q x ∂m‖ ^ 2 ≤ K) →
    ∀ (Q : X → ℂ) (s : Finset X),
    (∀ x, Q x = ∑ a ∈ s, Q a * Set.indicator {y | y - a ∈ L} (fun _ => (1 : ℂ)) x) →
    ‖∫ x, Q x * q x ∂m‖ ≤ (∑ a ∈ s, ‖Q a‖) * √K := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.CosetBound.twisted_integral_finite_coset_combination_bound | exact GlobalTheory.CompanionTheory.SiegelND.Integ.CosetBound.twisted_integral_finite_coset_combination_bound | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.CosetBound.twisted_integral_finite_coset_combination_bound <;> assumption)
end
end
