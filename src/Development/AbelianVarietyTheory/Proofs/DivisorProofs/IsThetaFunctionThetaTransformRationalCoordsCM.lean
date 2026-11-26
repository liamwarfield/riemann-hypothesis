module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegIdxOfIsStd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasDerivAtHeisenbergOperatorThetaTransformRealLi

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairAMulEqZeroIffSnd
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

noncomputable section

namespace GlobalTheory.ThetaTransformF

open Formalism.IndefR.DatumF GlobalTheory.ThetaTransform GlobalTheory.SWQ

section Ad

variable (F : Type) [Field F] [NumberField F]

theorem fstA_pairA' (x : Ainf F) (y : Af F) : fstA F (pairA F x y) = x := rfl

theorem sndA_pairA' (x : Ainf F) (y : Af F) : sndA F (pairA F x y) = y := rfl

variable {F} in
theorem af_ext' {a b : AF F} (h1 : fstA F a = fstA F b) (h2 : sndA F a = sndA F b) : a = b :=
  Prod.ext (α := Ainf F) (β := Af F) h1 h2

theorem pairA_mul_eq_zero_iff_snd' (a : AF F) : pairA F 0 1 * a = 0 ↔ sndA F a = 0 := by
  constructor
  · intro h
    have := congrArg (sndA F) h
    rwa [map_mul, map_zero, sndA_pairA', one_mul] at this
  · intro h
    refine af_ext' ?_ ?_
    · rw [map_mul, map_zero, fstA_pairA', zero_mul]
    · rw [map_mul, map_zero, sndA_pairA', h, mul_zero]

theorem pairA_mul_eq_zero_iff_fst' (a : AF F) : pairA F 1 0 * a = 0 ↔ fstA F a = 0 := by
  constructor
  · intro h
    have := congrArg (fstA F) h
    rwa [map_mul, map_zero, fstA_pairA', one_mul] at this
  · intro h
    refine af_ext' ?_ ?_
    · rw [map_mul, map_zero, fstA_pairA', h, mul_zero]
    · rw [map_mul, map_zero, sndA_pairA', zero_mul]

def incFin : Af F →ₗ[F] AF F where
  toFun y := pairA F 0 y
  map_add' y y' := af_ext' (by rw [map_add (f := _), fstA_pairA', fstA_pairA', fstA_pairA', add_zero])
    (by rw [map_add (f := _), sndA_pairA', sndA_pairA', sndA_pairA'])
  map_smul' c y := af_ext' (by rw [map_smul, fstA_pairA', fstA_pairA', RingHom.id_apply, smul_zero])
    (by rw [map_smul, sndA_pairA', sndA_pairA', RingHom.id_apply])

def incInf : Ainf F →ₗ[F] AF F where
  toFun y := pairA F y 0
  map_add' y y' := af_ext' (by rw [map_add (f := _), fstA_pairA', fstA_pairA', fstA_pairA'])
    (by rw [map_add (f := _), sndA_pairA', sndA_pairA', sndA_pairA', add_zero])
  map_smul' c y := af_ext' (by rw [map_smul, fstA_pairA', fstA_pairA', RingHom.id_apply])
    (by rw [map_smul, sndA_pairA', sndA_pairA', RingHom.id_apply, smul_zero])

theorem incFin_sndA (a : AF F) : incFin F (sndA F a) = pairA F 0 1 * a :=
  af_ext' (by rw [map_mul, fstA_pairA', zero_mul]; rfl) (by rw [map_mul, sndA_pairA', one_mul]; rfl)

theorem incInf_fstA (a : AF F) : incInf F (fstA F a) = pairA F 1 0 * a :=
  af_ext' (by rw [map_mul, fstA_pairA', one_mul]; rfl) (by rw [map_mul, sndA_pairA', zero_mul]; rfl)

end Ad

section Coord

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def secFin : Af F ⊗[F] E →ₗ[F] AF F ⊗[F] E := TensorProduct.map (incFin F) LinearMap.id

def secInf : Ainf F ⊗[F] E →ₗ[F] AF F ⊗[F] E := TensorProduct.map (incInf F) LinearMap.id

variable {F E}

theorem secFin_finPartF (z : AF F ⊗[F] E) : secFin F E (finPartF F E z) = pairA F 0 1 • z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [(finPartF F E).map_zero, (secFin F E).map_zero, smul_zero]
  | tmul a b =>
    have h1 : finPartF F E (a ⊗ₜ b) = sndA F a ⊗ₜ b := rfl
    rw [h1, secFin, TensorProduct.map_tmul, LinearMap.id_apply, incFin_sndA, TensorProduct.smul_tmul', smul_eq_mul]
  | add x y hx hy => rw [(finPartF F E).map_add, (secFin F E).map_add, hx, hy, smul_add]

theorem secInf_infPartF (z : AF F ⊗[F] E) : secInf F E (infPartF F E z) = pairA F 1 0 • z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [(infPartF F E).map_zero, (secInf F E).map_zero, smul_zero]
  | tmul a b =>
    have h1 : infPartF F E (a ⊗ₜ b) = fstA F a ⊗ₜ b := rfl
    rw [h1, secInf, TensorProduct.map_tmul, LinearMap.id_apply, incInf_fstA, TensorProduct.smul_tmul', smul_eq_mul]
  | add x y hx hy => rw [(infPartF F E).map_add, (secInf F E).map_add, hx, hy, smul_add]

theorem finPartF_smul (z : AF F ⊗[F] E) : finPartF F E (pairA F 0 1 • z) = finPartF F E z := by
  rw [Algebra.smul_def, (finPartF F E).map_mul]
  have : finPartF F E (algebraMap (AF F) (AF F ⊗[F] E) (pairA F 0 1)) = 1 := by
    rw [Algebra.TensorProduct.algebraMap_apply]
    show sndA F (algebraMap (AF F) (AF F) (pairA F 0 1)) ⊗ₜ[F] (1 : E) = 1
    rw [Algebra.algebraMap_self, RingHom.id_apply, sndA_pairA']
    rfl
  rw [this, one_mul]

theorem infPartF_smul (z : AF F ⊗[F] E) : infPartF F E (pairA F 1 0 • z) = infPartF F E z := by
  rw [Algebra.smul_def, (infPartF F E).map_mul]
  have : infPartF F E (algebraMap (AF F) (AF F ⊗[F] E) (pairA F 1 0)) = 1 := by
    rw [Algebra.TensorProduct.algebraMap_apply]
    show fstA F (algebraMap (AF F) (AF F) (pairA F 1 0)) ⊗ₜ[F] (1 : E) = 1
    rw [Algebra.algebraMap_self, RingHom.id_apply, fstA_pairA']
    rfl
  rw [this, one_mul]

theorem finPartF_eq_zero_iff (z : AF F ⊗[F] E) : finPartF F E z = 0 ↔ pairA F 0 1 • z = 0 := by
  constructor
  · intro h; rw [← secFin_finPartF, h, (secFin F E).map_zero]
  · intro h; rw [← finPartF_smul, h, (finPartF F E).map_zero]

theorem infPartF_eq_zero_iff (z : AF F ⊗[F] E) : infPartF F E z = 0 ↔ pairA F 1 0 • z = 0 := by
  constructor
  · intro h; rw [← secInf_infPartF, h, (secInf F E).map_zero]
  · intro h; rw [← infPartF_smul, h, (infPartF F E).map_zero]

omit [Field E] [NumberField E] [Algebra F E] in
theorem smul_vec_fin' {N : ℕ} (u : Fin N → AF F) : pairA F 0 1 • u = 0 ↔ fin u = 0 := by
  rw [funext_iff, funext_iff]
  exact forall_congr' fun l => pairA_mul_eq_zero_iff_snd' F (u l)

omit [Field E] [NumberField E] [Algebra F E] in
theorem smul_vec_inf' {N : ℕ} (u : Fin N → AF F) : pairA F 1 0 • u = 0 ↔ inf u = 0 := by
  rw [funext_iff, funext_iff]
  exact forall_congr' fun l => pairA_mul_eq_zero_iff_fst' F (u l)

theorem coordF (m n N : ℕ) (e : Matrix (Fin m) (Fin n) (AF F ⊗[F] E) ≃ₗ[AF F] VA F N) :
    Continuous e ∧ Continuous e.symm ∧
      (∀ x, x.map (finPartF F E) = 0 ↔ fin (e x).1 = 0 ∧ fin (e x).2 = 0) ∧
      (∀ x, x.map (infPartF F E) = 0 ↔ inf (e x).1 = 0 ∧ inf (e x).2 = 0) := by
  haveI h0 : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousAdd (AF F ⊗[F] E) := IsModuleTopology.toContinuousAdd (AF F) (AF F ⊗[F] E)
  haveI h1 : IsModuleTopology (AF F) (Fin n → AF F ⊗[F] E) := IsModuleTopology.instPi
  haveI h2 : IsModuleTopology (AF F) (Matrix (Fin m) (Fin n) (AF F ⊗[F] E)) := IsModuleTopology.instPi
  refine ⟨IsModuleTopology.continuous_of_linearMap e.toLinearMap,
    IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap, fun x => ?_, fun x => ?_⟩
  · have key : x.map (finPartF F E) = 0 ↔ pairA F 0 1 • x = 0 := by
      rw [← Matrix.ext_iff, ← Matrix.ext_iff]
      simp only [Matrix.map_apply, Matrix.zero_apply, Matrix.smul_apply]
      exact forall_congr' fun i => forall_congr' fun j => finPartF_eq_zero_iff (x i j)
    rw [key, ← smul_vec_fin', ← smul_vec_fin', ← LinearEquiv.map_eq_zero_iff e, LinearEquiv.map_smul]
    exact Prod.ext_iff
  · have key : x.map (infPartF F E) = 0 ↔ pairA F 1 0 • x = 0 := by
      rw [← Matrix.ext_iff, ← Matrix.ext_iff]
      simp only [Matrix.map_apply, Matrix.zero_apply, Matrix.smul_apply]
      exact forall_congr' fun i => forall_congr' fun j => infPartF_eq_zero_iff (x i j)
    rw [key, ← smul_vec_inf', ← smul_vec_inf', ← LinearEquiv.map_eq_zero_iff e, LinearEquiv.map_smul]
    exact Prod.ext_iff

end Coord

end GlobalTheory.ThetaTransformF

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BicharDerivContDiff
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BicharDerivContDiff
open scoped ContDiff

namespace GlobalTheory

open intervalIntegral Filter Topology

theorem bichar_deriv_contDiff (k : ℕ) (Q : (Fin k → ℝ) → ℝ → ℂ)
    (hQ : Continuous (Function.uncurry Q))
    (hs : ∀ t s s', Q t (s + s') = Q t s * Q t s')
    (ht : ∀ t t' s, Q (t + t') s = Q t s * Q t' s)
    (h0 : ∀ t, Q t 0 = 1) :
    ContDiff ℝ ∞ (fun t => deriv (Q t) 0) := by
  have hQt : ∀ t, Continuous (Q t) := fun t =>
    hQ.comp (continuous_const.prodMk continuous_id : Continuous fun s : ℝ => (t, s))
  set g : (Fin k → ℝ) → ℝ → ℂ := fun t δ => ∫ r in (0:ℝ)..δ, Q t r with hgdef
  have hg : ∀ t x, HasDerivAt (g t) (Q t x) x := fun t x =>
    ((hQt t).integral_hasStrictDerivAt 0 x).hasDerivAt
  have hid : ∀ t s δ, Q t s * g t δ = g t (s + δ) - g t s := by
    intro t s δ
    have hint : ∀ a b : ℝ, IntervalIntegrable (Q t) MeasureTheory.volume a b :=
      fun a b => (hQt t).intervalIntegrable a b
    simp only [hgdef]
    rw [integral_interval_sub_left (hint _ _) (hint _ _)]
    have h1 : ∫ x in (0:ℝ)..δ, Q t (x + s) = ∫ x in s..s + δ, Q t x := by
      rw [intervalIntegral.integral_comp_add_right (fun x => Q t x) s]
      simp [add_comm]
    rw [← h1]
    simp_rw [hs, intervalIntegral.integral_mul_const]
    ring
  have hder : ∀ t δ, g t δ ≠ 0 → ∀ s,
      HasDerivAt (Q t) ((Q t (s + δ) - Q t s) / g t δ) s := by
    intro t δ hδ s
    have heq : Q t = fun u => (g t (u + δ) - g t u) / g t δ := by
      funext u; rw [← hid t u δ, mul_div_cancel_right₀ _ hδ]
    have ha : HasDerivAt (fun u => g t (u + δ)) (Q t (s + δ)) s :=
      HasDerivAt.comp_add_const s δ (hg t (s + δ))
    have h1 : HasDerivAt (fun u => (g t (u + δ) - g t u) / g t δ)
        ((Q t (s + δ) - Q t s) / g t δ) s := (ha.sub (hg t s)).div_const _
    rwa [← heq] at h1
  have hex : ∀ t, ∃ δ, g t δ ≠ 0 := by
    intro t
    have h := (hg t 0).eventually_ne (c := 0) (by rw [h0]; exact one_ne_zero)
    obtain ⟨z, hz⟩ := h.exists
    refine ⟨z, ?_⟩
    simpa [hgdef] using hz
  have hd : ∀ t, HasDerivAt (Q t) (deriv (Q t) 0) 0 := by
    intro t
    obtain ⟨δ, hδ⟩ := hex t
    exact (hder t δ hδ 0).differentiableAt.hasDerivAt
  have hadd : ∀ t t', deriv (Q (t + t')) 0 = deriv (Q t) 0 + deriv (Q t') 0 := by
    intro t t'
    have e : Q (t + t') = Q t * Q t' := funext fun s => by rw [Pi.mul_apply, ht]
    have hm := (hd t).mul (hd t')
    rw [← e] at hm
    rw [hm.deriv, h0, h0]; ring
  let c : (Fin k → ℝ) →+ ℂ := AddMonoidHom.mk' (fun t => deriv (Q t) 0) hadd
  have hQ0 : ∀ s, Q 0 s = 1 := by
    intro s
    have h1 : Q 0 s = Q 0 s * Q 0 s := by simpa using ht 0 0 s
    have h2 : Q 0 s * Q 0 (-s) = 1 := by rw [← hs, add_neg_cancel, h0]
    have hne : Q 0 s ≠ 0 := left_ne_zero_of_mul_eq_one h2
    have := mul_left_cancel₀ hne (h1.symm.trans (mul_one _).symm)
    exact this
  have hgc : Continuous fun t => g t 1 :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hQ 0 1
  have hg01 : g 0 1 = 1 := by simp [hgdef, hQ0]
  have hne : ∀ᶠ t in 𝓝 (0 : Fin k → ℝ), g t 1 ≠ 0 :=
    hgc.continuousAt.eventually_ne (by rw [hg01]; exact one_ne_zero)
  have hc0 : ContinuousAt c 0 := by
    have hQ1 : Continuous fun t => Q t 1 :=
      hQ.comp (continuous_id.prodMk continuous_const : Continuous fun t => (t, (1:ℝ)))
    have hf : ContinuousAt (fun t => (Q t 1 - 1) / g t 1) 0 :=
      ((hQ1.sub continuous_const).continuousAt).div hgc.continuousAt (by rw [hg01]; exact one_ne_zero)
    refine hf.congr ?_
    filter_upwards [hne] with t htne
    have := (hder t 1 htne 0).deriv
    simp only [zero_add, h0] at this
    simp [c, this]
  have hcc : Continuous c := continuous_of_continuousAt_zero c hc0
  have : (fun t => deriv (Q t) 0) = ⇑(c.toRealLinearMap hcc) := by
    funext t; simp [c]
  rw [this]
  exact (c.toRealLinearMap hcc).contDiff

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BicharDerivContDiffStatement
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contDiff_deriv_zero_of_continuous_bicharacter : ∀ (k : ℕ) (Q : (Fin k → ℝ) → ℝ → ℂ), Continuous (Function.uncurry Q) → (∀ t s s', Q t (s + s') = Q t s * Q t s') → (∀ t t' s, Q (t + t') s = Q t s * Q t' s) → (∀ t, Q t 0 = 1) → ContDiff ℝ ∞ (fun t => deriv (Q t) 0) := by
  first | exact @GlobalTheory.bichar_deriv_contDiff | exact GlobalTheory.bichar_deriv_contDiff | (intros; apply GlobalTheory.bichar_deriv_contDiff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThetaFunctionThetaTransformRationalCoordsCM
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.ThetaTransformF

open Formalism.IndefR.DatumF GlobalTheory.ThetaTransform GlobalTheory.SWQ
open scoped ContDiff

theorem charR_hasDerivAt : ∀ (χ : ℝ → ℂ), Continuous χ → (∀ s t, χ (s + t) = χ s * χ t) → χ 0 = 1 →
    ∀ s, HasDerivAt χ (deriv χ 0 * χ s) s := GlobalTheory.T.hasDerivAt_of_continuous_real_to_complex_exponential

theorem biChar_contDiff : ∀ (k : ℕ) (Q : (Fin k → ℝ) → ℝ → ℂ), Continuous (Function.uncurry Q) →
    (∀ t s s', Q t (s + s') = Q t s * Q t s') → (∀ t t' s, Q (t + t') s = Q t s * Q t' s) → (∀ t, Q t 0 = 1) →
    ContDiff ℝ ∞ (fun t => deriv (Q t) 0) := GlobalTheory.T.contDiff_deriv_zero_of_continuous_bicharacter

section Phase

variable {F : Type} [Field F] [NumberField F] {N : ℕ} [Invertible (2 : AF F)] {ψ : AddChar (AF F) ℂ}

def phase (ψ : AddChar (AF F) ℂ) (M : ℝ →+ VA F N) (w : VA F N) (s : ℝ) : ℂ := ψ (⅟(2 : AF F) * symV w (M s))

theorem symV_add_left (w w' u : VA F N) : symV (w + w') u = symV w u + symV w' u := by
  simp only [symV, Prod.fst_add, Prod.snd_add, add_dotProduct, dotProduct_add]; ring

theorem symV_add_right (w u u' : VA F N) : symV w (u + u') = symV w u + symV w u' := by
  simp only [symV, Prod.fst_add, Prod.snd_add, add_dotProduct, dotProduct_add]; ring

theorem symV_zero_right (w : VA F N) : symV w 0 = 0 := by simp [symV]

theorem continuous_symV : Continuous fun p : VA F N × VA F N => symV p.1 p.2 := by
  unfold symV dotProduct
  fun_prop

theorem phase_add (M : ℝ →+ VA F N) (w : VA F N) (s s' : ℝ) :
    phase ψ M w (s + s') = phase ψ M w s * phase ψ M w s' := by
  simp only [phase, map_add (f := _), symV_add_right, mul_add, AddChar.map_add_eq_mul]

theorem phase_add_left (M : ℝ →+ VA F N) (w w' : VA F N) (s : ℝ) :
    phase ψ M (w + w') s = phase ψ M w s * phase ψ M w' s := by
  simp only [phase, symV_add_left, mul_add, AddChar.map_add_eq_mul]

theorem phase_zero (M : ℝ →+ VA F N) (w : VA F N) : phase ψ M w 0 = 1 := by
  simp [phase, symV_zero_right]

theorem continuous_phase (hψ : Continuous ψ) {M : ℝ →+ VA F N} (hM : Continuous M) :
    Continuous fun p : VA F N × ℝ => phase ψ M p.1 p.2 := by
  have h1 : Continuous fun p : VA F N × ℝ => (p.1, M p.2) := by fun_prop
  have h2 : Continuous fun p : VA F N × ℝ => symV p.1 (M p.2) :=
    Continuous.comp (g := fun q : VA F N × VA F N => symV q.1 q.2) (f := fun p : VA F N × ℝ => (p.1, M p.2)) continuous_symV h1
  have h3 : Continuous fun p : VA F N × ℝ => ⅟(2 : AF F) * symV p.1 (M p.2) := continuous_const.mul h2
  exact hψ.comp h3

end Phase

end GlobalTheory.ThetaTransformF

end

noncomputable section

namespace GlobalTheory.ThetaTransformF

open Formalism.IndefR.DatumF GlobalTheory.ThetaTransform GlobalTheory.SWQ
open scoped ContDiff

section Crit

variable {F : Type} [Field F] [NumberField F] {N : ℕ} [Invertible (2 : AF F)] {ψ : AddChar (AF F) ℂ}

theorem continuous_phase_right (hψ : Continuous ψ) {M : ℝ →+ VA F N} (hM : Continuous M) (w : VA F N) :
    Continuous (phase ψ M w) := by
  have h : Continuous fun s : ℝ => ((w, s) : VA F N × ℝ) := by fun_prop
  exact Continuous.comp (g := fun p : VA F N × ℝ => phase ψ M p.1 p.2) (f := fun s : ℝ => ((w, s) : VA F N × ℝ))
    (continuous_phase hψ hM) h

theorem phase_hasDerivAt (hψ : Continuous ψ) {M : ℝ →+ VA F N} (hM : Continuous M) (w : VA F N) (s : ℝ) :
    HasDerivAt (phase ψ M w) (deriv (phase ψ M w) 0 * phase ψ M w s) s :=
  charR_hasDerivAt _ (continuous_phase_right hψ hM w) (phase_add M w) (phase_zero M w) s

theorem contDiff_phase_deriv (hψ : Continuous ψ) {M : ℝ →+ VA F N} (hM : Continuous M) {k : ℕ}
    {L : (Fin k → ℝ) →+ VA F N} (hL : Continuous L) (u : VA F N) :
    ContDiff ℝ ∞ fun t => deriv (phase ψ M (u + L t)) 0 := by
  have e : (fun t => deriv (phase ψ M (u + L t)) 0) =
      fun t => deriv (phase ψ M u) 0 + deriv (phase ψ M (L t)) 0 := by
    funext t
    have hf : phase ψ M (u + L t) = fun s => phase ψ M u s * phase ψ M (L t) s := funext (phase_add_left M u (L t))
    have hd := ((phase_hasDerivAt hψ hM u 0).mul (phase_hasDerivAt hψ hM (L t) 0)).deriv
    simp only [phase_zero, mul_one, one_mul] at hd
    rw [hf]
    exact hd
  rw [e]
  have hQ : Continuous (Function.uncurry fun t s => phase ψ M (L t) s) := by
    have h : Continuous fun p : (Fin k → ℝ) × ℝ => ((L p.1, p.2) : VA F N × ℝ) := by fun_prop
    exact Continuous.comp (g := fun p : VA F N × ℝ => phase ψ M p.1 p.2)
      (f := fun p : (Fin k → ℝ) × ℝ => ((L p.1, p.2) : VA F N × ℝ)) (continuous_phase hψ hM) h
  exact contDiff_const.add (biChar_contDiff k (fun t s => phase ψ M (L t) s) hQ
    (fun t s s' => phase_add M (L t) s s') (fun t t' s => by simp only [map_add (f := _)]; exact phase_add_left M _ _ s)
    (fun t => phase_zero M (L t)))

theorem hasDerivAt_lineV (hψ : Continuous ψ) {M : ℝ →+ VA F N} (hM : Continuous M) {f : VA F N → ℂ}
    {w : VA F N} {c : ℂ} (hd : HasDerivAt (fun s : ℝ => heisV ψ (M s) f w) c 0) :
    HasDerivAt (fun s : ℝ => f (w + M s)) (c + -deriv (phase ψ M w) 0 * f w) 0 := by
  have hp := phase_hasDerivAt hψ hM w 0
  have hne : ∀ s, phase ψ M w s ≠ 0 := fun s h0 => by
    have := AddChar.map_add_eq_mul ψ (⅟(2 : AF F) * symV w (M s)) (-(⅟(2 : AF F) * symV w (M s)))
    rw [add_neg_cancel, AddChar.map_zero_eq_one] at this
    have h0' : ψ (⅟(2 : AF F) * symV w (M s)) = 0 := h0
    rw [h0', zero_mul] at this
    exact one_ne_zero this
  have e : (fun s : ℝ => f (w + M s)) = fun s => heisV ψ (M s) f w / phase ψ M w s := by
    funext s
    rw [heisV]
    exact (mul_div_cancel_left₀ _ (hne s)).symm
  rw [e]
  refine (hd.div hp (hne 0)).congr_deriv ?_
  have h1 : heisV ψ (M 0) f w = f w := by
    rw [heisV, map_zero, symV_zero_right, mul_zero, AddChar.map_zero_eq_one, one_mul, add_zero]
  rw [h1, phase_zero, mul_one]
  field_simp
  ring

theorem contDiff_of_heisV_closed (ψ : AddChar (AF F) ℂ) (hψ : Continuous ψ) (V : Set (VA F N → ℂ))
    (hc : ∀ f ∈ V, Continuous f)
    (hd : ∀ f ∈ V, ∀ M : ℝ →+ VA F N, IsRealLine M → ∃ f' ∈ V, ∀ w,
      HasDerivAt (fun t : ℝ => heisV ψ (M t) f w) (f' w) 0) :
    ∀ f ∈ V, ∀ (k : ℕ) (L : (Fin k → ℝ) →+ VA F N), Continuous L → (∀ t, fin (L t).1 = 0 ∧ fin (L t).2 = 0) →
      ∀ w, ContDiff ℝ ∞ fun t => f (w + L t) := by
  intro f hf k L hL hLf u
  let P : ((Fin k → ℝ) → ℂ) → Prop := fun G => ∃ f ∈ V, G = fun t => f (u + L t)
  refine GlobalTheory.Unf.MatCoef.contDiff_of_partials P ?_ ?_ _ ⟨f, hf, rfl⟩
  · rintro _ ⟨f, hf, rfl⟩
    have h : Continuous fun t => u + L t := by fun_prop
    exact (hc f hf).comp h
  · rintro _ ⟨f, hf, rfl⟩ i
    let E : ℝ →ₗ[ℝ] (Fin k → ℝ) := LinearMap.toSpanSingleton ℝ (Fin k → ℝ) (Pi.single i 1)
    let M : ℝ →+ VA F N := L.comp E.toAddMonoidHom
    have hM : Continuous M := hL.comp E.continuous_of_finiteDimensional
    obtain ⟨f', hf', hD⟩ := hd f hf M ⟨hM, fun s => hLf _⟩
    refine ⟨2, ![fun _ => 1, fun t => -deriv (phase ψ M (u + L t)) 0],
      ![fun t => f' (u + L t), fun t => f (u + L t)], fun j => ?_, fun j => ?_, fun t => ?_⟩
    · fin_cases j
      · exact contDiff_const
      · exact (contDiff_phase_deriv hψ hM hL u).neg
    · fin_cases j
      · exact ⟨f', hf', rfl⟩
      · exact ⟨f, hf, rfl⟩
    · have e : (fun s : ℝ => f (u + L (t + s • Pi.single i 1))) = fun s => f ((u + L t) + M s) := by
        funext s
        have : E s = s • Pi.single i 1 := rfl
        rw [map_add (f := _), add_assoc, ← this]
        rfl
      rw [e]
      convert hasDerivAt_lineV hψ hM (hD (u + L t)) using 1
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, one_mul]

end Crit

end GlobalTheory.ThetaTransformF

end

noncomputable section

namespace GlobalTheory.ThetaTransformF

open Formalism.IndefR.DatumF GlobalTheory.ThetaTransform GlobalTheory.SWQ
open scoped ContDiff

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [Invertible (2 : AF F)]
  {σ : E →ₐ[F] E} {nS nT N : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E} {ξ₀ : E}
  {ψ : AddChar (AF F) ℂ} {e : WOF F E nS nT ≃ₗ[AF F] VA F N}

theorem symplOHF_eq (he : ∀ w w', symplOF σ JS JT ξ₀ w w' = symV (e w) (e w')) (w w' : WOF F E nS nT) :
    symplOHF σ JS JT ξ₀ w w' = ⅟(2 : AF F) * symV (e w) (e w') := by
  rw [symplOHF, he, invOf_two_eq]

theorem heisOF_comp (he : ∀ w w', symplOF σ JS JT ξ₀ w w' = symV (e w) (e w')) (u : WOF F E nS nT)
    (f : VA F N → ℂ) : heisOF σ JS JT ξ₀ ψ u (f ∘ e) = heisV ψ (e u) f ∘ e := by
  funext w
  simp only [heisOF, heisV, Function.comp_apply, symplOHF_eq he, map_add (f := _)]

end Main


open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels in
theorem isThetaFunOF_thV : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      Formalism.IndefR.DatumF.IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
      ∀ (N : ℕ) (e : Formalism.IndefR.DatumF.WOF F E nS nT ≃ₗ[AF F] GlobalTheory.ThetaTransform.VA F N),
        (∀ w w', Formalism.IndefR.DatumF.symplOF σ JS JT ξ₀ w w' = GlobalTheory.ThetaTransform.symV (e w) (e w')) →
        (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : Fin N → F,
          e (Formalism.IndefR.DatumF.ratWF x) = (GlobalTheory.SWQ.rat y, GlobalTheory.SWQ.rat z)) →
        ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin N),
          Formalism.IndefR.DatumF.IsThetaFunOF σ JS JT ξ₀ B.ψ (GlobalTheory.ThetaTransform.thV B.ψ Φ ∘ e) := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT _ _ ξ₀ _ _ hstd N e he hrat Φ hΦ
  have hR : IsTotallyReal F := hB.cm.1
  have hψ : IsCharAF F B.ψ := hstd.1
  obtain ⟨hc, -, hfin, hinf⟩ := coordF nT nS N e
  have hcont : ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin N), Continuous (thV B.ψ Φ) := fun Φ hΦ =>
    GlobalTheory.T.continuous_adelicThetaTransformSymplectic_of_decay F N B.ψ hR hψ Φ (GlobalTheory.T.adelicRapidDecay_of_mem_adelicSchwartzSpace F N Φ hΦ)
  refine ⟨fun γ w => ?_, ?_, (hcont Φ hΦ).comp hc, ?_⟩
  · obtain ⟨y, z, h⟩ := hrat γ
    simp only [Function.comp_apply, map_add (f := _), symplOHF_eq he, h]
    exact quasiV_thV B.ψ hψ.2.2.1 Φ y z (e w)
  · obtain ⟨U, hUo, hU⟩ := GlobalTheory.T.adelicSchwartz_fixed_by_schroedinger_open_finite_subgroup F N B.ψ hR hψ Φ hΦ
    refine ⟨U.comap e.toLinearMap.toAddMonoidHom, hUo.preimage hc, fun u hu h0 => ?_⟩
    rw [heisOF_comp he, ← thV_schr, hU (e u) hu ((hinf u).1 h0).1 ((hinf u).1 h0).2]
  · intro k L hL hL0 w
    have h := contDiff_of_heisV_closed B.ψ hψ.1 {g | ∃ Φ ∈ GlobalTheory.WeilM.schA F (Fin N), g = thV B.ψ Φ}
      (by rintro _ ⟨Φ, hΦ, rfl⟩; exact hcont Φ hΦ)
      (by
        rintro _ ⟨Φ, hΦ, rfl⟩ M hM
        obtain ⟨Φ', hΦ', hd⟩ := GlobalTheory.T.hasDerivAt_heisenbergOperator_thetaTransform_realLine F N B.ψ hR hψ Φ hΦ M hM
        exact ⟨_, ⟨Φ', hΦ', rfl⟩, hd⟩)
      _ ⟨Φ, hΦ, rfl⟩ k (e.toLinearMap.toAddMonoidHom.comp L) (hc.comp hL) (fun t => (hfin _).1 (hL0 t)) (e w)
    simpa [Function.comp_def] using h

end GlobalTheory.ThetaTransformF

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThetaFunctionThetaTransformRationalCoordsCMStatement
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isThetaFunction_thetaTransform_rational_coords_CM : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      Formalism.IndefR.DatumF.IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
      ∀ (N : ℕ) (e : Formalism.IndefR.DatumF.WOF F E nS nT ≃ₗ[AF F] GlobalTheory.ThetaTransform.VA F N),
        (∀ w w', Formalism.IndefR.DatumF.symplOF σ JS JT ξ₀ w w' = GlobalTheory.ThetaTransform.symV (e w) (e w')) →
        (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : Fin N → F,
          e (Formalism.IndefR.DatumF.ratWF x) = (GlobalTheory.SWQ.rat y, GlobalTheory.SWQ.rat z)) →
        ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin N),
          Formalism.IndefR.DatumF.IsThetaFunOF σ JS JT ξ₀ B.ψ (GlobalTheory.ThetaTransform.thV B.ψ Φ ∘ e) := by
  first | exact @GlobalTheory.ThetaTransformF.isThetaFunOF_thV | exact GlobalTheory.ThetaTransformF.isThetaFunOF_thV | (intros; apply GlobalTheory.ThetaTransformF.isThetaFunOF_thV <;> assumption)
end
