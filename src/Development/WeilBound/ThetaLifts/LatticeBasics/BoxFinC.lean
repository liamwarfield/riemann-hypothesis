module

public import Development.WeilBound.ThetaLifts.LatticeBasics.RealInv
public import Development.WeilBound.ThetaLifts.LatticeBasics.ThetaBox

@[expose] public section

section -- merged from Development.WeilBound.ThetaLifts.LatticeBasics.BoxFinV
section -- merged from Development.WeilBound.ThetaLifts.LatticeBasics.BoxFinB
section -- merged from Development.WeilBound.ThetaLifts.LatticeBasics.BoxFinA
noncomputable section

namespace GlobalTheory.ThK.Dbl.Box

open scoped SchwartzMap
open GlobalTheory.ThK.Dbl.Dense Complex

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

structure Gau (f : 𝓢(V, ℂ)) (m : V →ₗ[ℝ] V →ₗ[ℝ] ℂ) : Prop where
  ne : ∀ y, f y ≠ 0
  der : ∀ a y, fderiv ℝ f y a = m a y * f y
  symm : ∀ a y, m a y = m y a
  neg : ∀ a, a ≠ 0 → (m a a).re < 0

theorem gau_of {f : 𝓢(V, ℂ)} (hf : f ≠ 0) {m : V →ₗ[ℝ] V →ₗ[ℝ] ℂ} (hm : ∀ a y, fderiv ℝ f y a = m a y * f y) : Gau f m := by
  obtain ⟨c, Q, Q', hc, pos, e⟩ := GlobalTheory.CompanionTheory.Twist.schwartz_logDeriv_linear_gaussian f hf m hm
  have ne : ∀ y, f y ≠ 0 := fun y => by rw [e]; exact mul_ne_zero hc (exp_ne_zero _)
  have key : ∀ a y, m a y = -((Q a y + Q y a : ℝ) : ℂ) - I * ((Q' a y + Q' y a : ℝ) : ℂ) := fun a y => by
    have l : HasDerivAt (fun t : ℝ => y + t • a) a 0 := by simpa using ((hasDerivAt_id (0 : ℝ)).smul_const a).const_add y
    have h1 : HasDerivAt (fun t : ℝ => f (y + t • a)) (fderiv ℝ f y a) 0 :=
      HasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) (f.differentiableAt (x := y)).hasFDerivAt l (by simp)
    have q : ∀ P : V →ₗ[ℝ] V →ₗ[ℝ] ℝ, HasDerivAt (fun t : ℝ => ((P (y + t • a) (y + t • a) : ℝ) : ℂ)) ((P a y + P y a : ℝ) : ℂ) 0 :=
      fun P => by
        have e1 : (fun t : ℝ => P (y + t • a) (y + t • a)) = fun t => P y y + t * (P a y + P y a) + t ^ 2 * P a a := by
          funext t; simp only [map_add (f := _), map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]; ring
        have : HasDerivAt (fun t : ℝ => P (y + t • a) (y + t • a)) (P a y + P y a) 0 := by
          rw [e1]
          exact ((((hasDerivAt_id (0 : ℝ)).mul_const (P a y + P y a)).const_add (P y y)).fun_add
            ((hasDerivAt_pow 2 (0 : ℝ)).mul_const (P a a))).congr_deriv (by simp)
        exact this.ofReal_comp
    have h2 := (((q Q).neg.sub ((q Q').const_mul I)).cexp).const_mul c
    have h3 : (fun t : ℝ => f (y + t • a)) = _ := funext fun t => e _
    rw [h3] at h1
    have h4 := h1.unique h2
    rw [hm] at h4
    refine mul_right_cancel₀ (ne y) (h4.trans ?_)
    rw [e]; simp; ring
  refine ⟨ne, hm, fun a y => by rw [key, key, add_comm (Q a y), add_comm (Q' a y)], fun a ha => ?_⟩
  have := pos a ha
  rw [key]; simp; linarith

theorem opp {f g : 𝓢(V, ℂ)} {m n : V →ₗ[ℝ] V →ₗ[ℝ] ℂ} (hf : Gau f m) (hg : Gau g n) {a b : V} {L L' : V →L[ℝ] ℝ}
    (h1 : dop b L' f = I • dop a L f) (h2 : dop (-b) (-L') g = I • dop a L g) : a = 0 ∧ L = 0 := by
  have e1 : ∀ y, m b y - 2 * Real.pi * I * L' y = I * (m a y - 2 * Real.pi * I * L y) := fun y => by
    have := congrArg (fun h : 𝓢(V, ℂ) => h y) h1
    simp only [SchwartzMap.smul_apply, dop_apply, hf.der, smul_eq_mul] at this
    exact mul_right_cancel₀ (hf.ne y) (by linear_combination this)
  have e2 : ∀ y, -n b y + 2 * Real.pi * I * L' y = I * (n a y - 2 * Real.pi * I * L y) := fun y => by
    have := congrArg (fun h : 𝓢(V, ℂ) => h y) h2
    simp only [SchwartzMap.smul_apply, dop_apply, hg.der, smul_eq_mul, map_neg, LinearMap.neg_apply,
      ContinuousLinearMap.neg_apply, ofReal_neg] at this
    exact mul_right_cancel₀ (hg.ne y) (by linear_combination this)
  have r1 := fun y => congrArg re (e1 y)
  have i1 := fun y => congrArg im (e1 y)
  have r2 := fun y => congrArg re (e2 y)
  have i2 := fun y => congrArg im (e2 y)
  simp at r1 i1 r2 i2
  have s1 := congrArg im (hf.symm a b)
  have s2 := congrArg im (hg.symm a b)
  have le : ∀ {h : 𝓢(V, ℂ)} {k} (_ : Gau h k) x, (k x x).re ≤ 0 := fun H x => by
    by_cases hx : x = 0
    · simp [hx]
    · exact (H.neg x hx).le
  have ha : a = 0 := by
    by_contra ha
    linarith [hf.neg a ha, hg.neg a ha, le hf b, le hg b, r1 b, r2 b, i1 a, i2 a]
  have hb : b = 0 := by
    by_contra hb
    linarith [hf.neg b hb, hg.neg b hb, le hf a, le hg a, r1 b, r2 b, i1 a, i2 a]
  refine ⟨ha, ContinuousLinearMap.ext fun y => ?_⟩
  have := r1 y
  simpa [ha, hb, Real.pi_ne_zero] using this

end GlobalTheory.ThK.Dbl.Box

end
end

noncomputable section

namespace GlobalTheory.ThK.Dbl.Box

open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl.Dense

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] {ψ : AddChar (AF F) ℂ}

def nf (z : κ → AF F) : κ → mixedEmbedding.mixedSpace F := fun i => evI F (z i)

def fn (z : κ → AF F) : κ → Af F := fun i => (z i).2

omit [Fintype κ] in
theorem pt_self (z : κ → AF F) : pt (nf z) (fn z) = z :=
  funext fun i => Prod.ext ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm_apply_apply _) rfl

theorem nf_pt (x : κ → mixedEmbedding.mixedSpace F) (y : κ → Af F) : nf (pt x y) = x := evI_pt x y

omit [Fintype κ] in
theorem nf_add (z z' : κ → AF F) : nf (z + z') = nf z + nf z' := funext fun _ => evI_add _ _

def DP (a : κ → mixedEmbedding.mixedSpace F) (L : (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ) (Φ : (κ → AF F) → ℂ) :
    (κ → AF F) → ℂ :=
  fun z => fderiv ℝ (fun x => Φ (pt x (fn z))) (nf z) a + (-(2 * Real.pi * Complex.I) * (L (nf z) : ℂ)) * Φ z

def D (w : (κ → AF F) × (κ → AF F)) : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ := DP (nf w.1) (Dense.linForm (nf w.2))

theorem linForm_add (b b' : κ → mixedEmbedding.mixedSpace F) : Dense.linForm (b + b') = Dense.linForm b + Dense.linForm b' := by
  ext y
  simp only [add_apply, linForm_apply, Pi.add_apply, mul_add, Finset.sum_add_distrib, map_add (f := _)]

theorem DP_add_left (a a' L L') (Φ : (κ → AF F) → ℂ) : DP (a + a') (L + L') Φ = DP a L Φ + DP a' L' Φ := by
  funext z
  simp only [DP, map_add (f := _), add_apply, Pi.add_apply]
  push_cast
  ring

theorem DP_smul_left (t : ℝ) (a L) (Φ : (κ → AF F) → ℂ) : DP (t • a) (t • L) Φ = (t : ℂ) • DP a L Φ := by
  funext z
  simp only [DP, map_smul, smul_apply, Pi.smul_apply, smul_eq_mul, Complex.real_smul]
  push_cast
  ring

theorem D_add_left (w w') (Φ : (κ → AF F) → ℂ) : D (w + w') Φ = D w Φ + D w' Φ := by
  rw [D, Prod.fst_add, Prod.snd_add, nf_add, nf_add, linForm_add, DP_add_left]; rfl

theorem slice {Φ : (κ → AF F) → ℂ} (h : Φ ∈ schA F κ) (y : κ → Af F) : ∃ f : SInf F κ, ∀ x, Φ (pt x y) = f x := by
  induction h using Submodule.span_induction with
  | mem Φ h => obtain ⟨f, g, -, rfl⟩ := h; exact ⟨g y • f, fun x => by rw [pureA_pt, mul_comm]; rfl⟩
  | zero => exact ⟨0, fun _ => rfl⟩
  | add _ _ _ _ h h' => obtain ⟨f, e⟩ := h; obtain ⟨f', e'⟩ := h'; exact ⟨f + f', fun x => by rw [Pi.add_apply, e, e']; rfl⟩
  | smul c _ _ h => obtain ⟨f, e⟩ := h; exact ⟨c • f, fun x => by rw [Pi.smul_apply, e]; rfl⟩

theorem DP_pt {Φ : (κ → AF F) → ℂ} {y : κ → Af F} {f : SInf F κ} (e : ∀ x, Φ (pt x y) = f x) (a L x) :
    DP a L Φ (pt x y) = dop a L f x := by
  rw [dop_apply, DP, nf_pt, e]
  exact congrArg (fun g => fderiv ℝ g x a + _) (funext e)

theorem DP_add {Φ Ψ : (κ → AF F) → ℂ} (h : Φ ∈ schA F κ) (h' : Ψ ∈ schA F κ) (a L) : DP a L (Φ + Ψ) = DP a L Φ + DP a L Ψ := by
  funext z
  obtain ⟨f, e⟩ := slice h (fn z)
  obtain ⟨g, e'⟩ := slice h' (fn z)
  rw [← pt_self z, Pi.add_apply, DP_pt e, DP_pt e', DP_pt (f := f + g) fun x => by rw [Pi.add_apply, e, e']; rfl]
  exact congrArg (fun k : SInf F κ => k (nf z)) ((dopL a L).map_add f g)

theorem DP_smul {Φ : (κ → AF F) → ℂ} (h : Φ ∈ schA F κ) (c : ℂ) (a L) : DP a L (c • Φ) = c • DP a L Φ := by
  funext z
  obtain ⟨f, e⟩ := slice h (fn z)
  rw [← pt_self z, Pi.smul_apply, DP_pt e, DP_pt (f := c • f) fun x => by rw [Pi.smul_apply, e]; rfl]
  exact congrArg (fun k : SInf F κ => k (nf z)) ((dopL a L).map_smul c f)

theorem DP_zero (a L) : DP a L (0 : (κ → AF F) → ℂ) = 0 := funext fun z => by simp [DP]

theorem DP_pure (f : SInf F κ) (g : (κ → Af F) → ℂ) (a L) : DP a L (pureA F f g) = pureA F (dop a L f) g := by
  funext z
  rw [← pt_self z, DP_pt (f := g (fn z) • f) fun x => by rw [pureA_pt, mul_comm]; rfl, pureA_pt, mul_comm]
  exact congrArg (fun k : SInf F κ => k (nf z)) ((dopL a L).map_smul _ f)

theorem DP_mem {Φ : (κ → AF F) → ℂ} (h : Φ ∈ schA F κ) (a L) : DP a L Φ ∈ schA F κ := by
  induction h using Submodule.span_induction with
  | mem Φ h => obtain ⟨f, g, hg, rfl⟩ := h; rw [DP_pure]; exact Submodule.subset_span ⟨_, g, hg, rfl⟩
  | zero => rw [DP_zero]; exact zero_mem _
  | add _ _ h1 h2 h h' => rw [DP_add h1 h2]; exact add_mem h h'
  | smul c _ h1 h => rw [DP_smul h1]; exact Submodule.smul_mem _ _ h

theorem schr_pt (hψ : IsStd ψ) {w : (κ → AF F) × (κ → AF F)} (hw : At (evI F) w) (Ψ : (κ → AF F) → ℂ) (t : ℝ) (x y) :
    schr ψ (realAd F t • w) Ψ (pt x y) = hl (nf w.1) (Dense.linForm (nf w.2)) t (fun x => Ψ (pt x y)) x := by
  have ha : At (evI F) w.1 := fun s hs => congrArg Prod.fst (hw s hs)
  have hb : At (evI F) w.2 := fun s hs => congrArg Prod.snd (hw s hs)
  have e : pt x y + realAd F t • w.1 = pt (x + t • nf w.1) y := by
    rw [← pt_self (pt x y + realAd F t • w.1)]
    congr 1
    · rw [nf_add, nf_pt]; congr 1; funext i; simp [nf, evI_mul, evI_realAd, Algebra.smul_def]
    · funext i
      show y i + (realAd F t).2 * (w.1 i).2 = y i
      rw [snd_eq_zero ha, mul_zero, add_zero]
  show ψ (pt x y ⬝ᵥ (realAd F t • w.2) + ⅟(2 : AF F) * ((realAd F t • w.1) ⬝ᵥ (realAd F t • w.2))) * Ψ (pt x y + realAd F t • w.1) = _
  rw [phase_line ψ hψ _ _ _ hb t, e, evI_half_trace, evI_pt]
  simp only [hl, linForm_apply]
  rfl

theorem hasD (hψ : IsStd ψ) {w : (κ → AF F) × (κ → AF F)} (hw : At (evI F) w) {Φ : (κ → AF F) → ℂ} (h : Φ ∈ schA F κ) (z) :
    HasDerivAt (fun t : ℝ => schr ψ (realAd F t • w) Φ z) (D w Φ z) 0 := by
  obtain ⟨f, e⟩ := slice h (fn z)
  rw [← pt_self z, D, DP_pt e]
  simp only [schr_pt hψ hw, e]
  exact hasDerivAt_hl _ _ f _

theorem eval_adm (z : κ → AF F) : (LinearMap.proj z : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) ∈ (adeleClass F).adm κ := fun g _ =>
  ⟨g (fn z) • (BoundedContinuousFunction.evalCLM ℂ (nf z) ∘L SchwartzMap.toBoundedContinuousFunctionCLM ℂ _ ℂ),
    fun _ => mul_comm _ _⟩

structure Imp (ψ : AddChar (AF F) ℂ) (T : Module.End ℂ ((κ → AF F) → ℂ)) (g : (κ → AF F) × (κ → AF F) → (κ → AF F) × (κ → AF F)) :
    Prop where
  pres : ∀ φ ∈ schA F κ, T φ ∈ schA F κ
  adm : ∀ l ∈ (adeleClass F).adm κ, l ∘ₗ T ∈ (adeleClass F).adm κ
  add : ∀ w w', g (w + w') = g w + g w'
  smul : ∀ (c : AF F) w, g (c • w) = c • g w
  impl : ∀ w, ∀ φ ∈ schA F κ, T (schr ψ w φ) = schr ψ (g w) (T φ)

variable {T : Module.End ℂ ((κ → AF F) → ℂ)} {g : (κ → AF F) × (κ → AF F) → (κ → AF F) × (κ → AF F)}

theorem Imp.at (h : Imp ψ T g) {w} (hw : At (evI F) w) : At (evI F) (g w) := fun s hs => by
  rw [← h.smul, hw s hs, ← zero_smul (AF F) (0 : (κ → AF F) × (κ → AF F)), h.smul, zero_smul, zero_smul]

theorem Imp.of_ne (hψ : IsStd ψ) (h : Imp ψ T g) {w} (hw : At (evI F) w) (ha : nf w.1 ≠ 0) {Φ} (hΦ : Φ ∈ schA F κ) :
    T (D w Φ) = D (g w) (T Φ) := by
  induction hΦ using Submodule.span_induction with
  | mem Φ hm =>
    have hs : Φ ∈ schA F κ := Submodule.subset_span hm
    obtain ⟨f, φ, hφ, rfl⟩ := hm
    obtain ⟨G, hG, hD⟩ := hl_line_deriv (nf w.1) (Dense.linForm (nf w.2)) f
    funext z
    obtain ⟨S, hS⟩ := h.adm _ (eval_adm z) φ hφ
    have h1 := hD ha S
    have e : (fun t => S (G t)) = fun t : ℝ => schr ψ (realAd F t • g w) (T (pureA F f φ)) z := funext fun t => by
      rw [← hS, ← h.smul, ← h.impl _ _ hs]
      refine congrArg (fun Ψ => T Ψ z) (funext fun z' => ?_)
      rw [← pt_self z', schr_pt hψ hw, pureA_pt, hG]
      simp only [pureA_pt, hl, mul_assoc]
    rw [e, ← hS] at h1
    rw [D, DP_pure]
    exact h1.unique (hasD hψ (h.at hw) (h.pres _ hs) z)
  | zero => simp only [D, DP_zero, map_zero]
  | add _ _ h1 h2 i1 i2 => simp only [D] at *; rw [DP_add h1 h2, map_add (f := _), map_add (f := _), DP_add (h.pres _ h1) (h.pres _ h2), i1, i2]
  | smul c _ h1 i1 => simp only [D] at *; rw [DP_smul h1, map_smul, map_smul, DP_smul (h.pres _ h1), i1]

theorem at_pt (x : κ → mixedEmbedding.mixedSpace F) : At (evI F) (pt x (0 : κ → Af F)) := fun s hs => by
  have h1 : s.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).map_eq_zero_iff.1 hs
  funext i
  refine Prod.ext ?_ ?_
  · show s.1 * _ = 0
    rw [h1, zero_mul]
  · show s.2 * 0 = 0
    rw [mul_zero]

theorem Imp.inter (hψ : IsStd ψ) (h : Imp ψ T g) {w} (hw : At (evI F) w) {Φ} (hΦ : Φ ∈ schA F κ) : T (D w Φ) = D (g w) (T Φ) := by
  by_cases ha : nf w.1 = 0
  · rcases subsingleton_or_nontrivial (κ → mixedEmbedding.mixedSpace F) with hV | hV
    · have z : ∀ a L (Ψ : (κ → AF F) → ℂ), DP a L Ψ = 0 := fun a L Ψ => funext fun z => by
        simp [DP, Subsingleton.elim a 0, Subsingleton.elim (nf z) 0]
      simp only [D, z, map_zero]
    · obtain ⟨ξ, hξ⟩ := exists_ne (0 : κ → mixedEmbedding.mixedSpace F)
      have hv : At (evI F) ((pt ξ 0, 0) : (κ → AF F) × (κ → AF F)) := fun s hs => Prod.ext (at_pt ξ s hs) (smul_zero _)
      have h1 := h.of_ne hψ (w := w + (pt ξ 0, 0)) (fun s hs => by rw [smul_add, hw s hs, hv s hs, add_zero])
        (by rwa [Prod.fst_add, nf_add, ha, zero_add, nf_pt]) hΦ
      have h2 := h.of_ne hψ hv (by rwa [nf_pt]) hΦ
      rw [D_add_left, map_add (f := _), h.add, D_add_left, h2] at h1
      exact add_right_cancel h1
  · exact h.of_ne hψ hw ha hΦ

theorem exists_D_fin (N : Submodule ℂ ((κ → AF F) → ℂ)) [FiniteDimensional ℂ N] (hN : N ≤ schA F κ) :
    ∃ N' : Submodule ℂ ((κ → AF F) → ℂ), FiniteDimensional ℂ N' ∧ ∀ a L, ∀ Φ ∈ N, DP a L Φ ∈ N' := by
  let b := Module.finBasis ℝ ((κ → mixedEmbedding.mixedSpace F) × ((κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ))
  let l : _ → N →ₗ[ℂ] ((κ → AF F) → ℂ) := fun i =>
    ⟨⟨fun Φ => DP (b i).1 (b i).2 Φ.1, fun Φ Ψ => DP_add (hN Φ.2) (hN Ψ.2) _ _⟩, fun c Φ => DP_smul (hN Φ.2) c _ _⟩
  refine ⟨⨆ i, LinearMap.range (l i), inferInstance, fun a L Φ hΦ => ?_⟩
  have : ∀ q ∈ Submodule.span ℝ (Set.range b), DP q.1 q.2 Φ ∈ ⨆ i, LinearMap.range (l i) := fun q hq => by
    induction hq using Submodule.span_induction with
    | mem q h => obtain ⟨i, rfl⟩ := h; exact Submodule.mem_iSup_of_mem i ⟨⟨Φ, hΦ⟩, rfl⟩
    | zero => convert Submodule.zero_mem _; funext z; simp [DP]
    | add x y _ _ hx hy => rw [Prod.fst_add, Prod.snd_add, DP_add_left]; exact add_mem hx hy
    | smul t q _ h => rw [Prod.smul_fst, Prod.smul_snd, DP_smul_left]; exact Submodule.smul_mem _ _ h
  exact this (a, L) (b.span_eq ▸ trivial)

end GlobalTheory.ThK.Dbl.Box

end
end

noncomputable section

namespace GlobalTheory.ThK.Dbl.Box

open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.ThK.Dbl.Dense
open GlobalTheory.AdelicU (EmbOver)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (AE At SInf evI piInf realAd)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {κ β : Type} [Fintype κ] [Fintype β] {m n : ℕ}

theorem at_entry' {α β : Type} {u : Matrix α β (AE F E)} (hu : At (evI F) u) (i : α) (j : β) :
    At (evI F) (u i j) := fun c hc => by
  simpa using congrFun (congrFun (hu c hc) i) j

theorem exists_real_structure' (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (emb : ∀ w : InfinitePlace F, EmbOver E w)
    {α β : Type} {κ : Type} [Fintype κ]
    (e : Matrix α β (AE F E) ≃ₗ[AF F] (κ → AF F) × (κ → AF F))
    (C : InfinitePlace F → Matrix α β ℂ →ₗ[ℝ] Matrix α β ℂ) :
    ∃ (s : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F) →
          Matrix α β (AE F E))
      (Jm : ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) →ₗ[ℝ]
        ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F))),
      (∀ p, At (evI F) (s p)) ∧
      (∀ p, (fun i => evI F ((e (s p)).1 i)) = p.1 ∧ (fun i => evI F ((e (s p)).2 i)) = p.2) ∧
      ∀ p w, (s (Jm p)).map (piInf (emb w)) = C w ((s p).map (piInf (emb w))) := by
  let s : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F) →
      Matrix α β (AE F E) :=
    fun p => e.symm (fun i => lift (p.1 i), fun i => lift (p.2 i))
  have es : ∀ p, e (s p) = (fun i => lift (p.1 i), fun i => lift (p.2 i)) := fun p => e.apply_symm_apply _
  have sAdd : ∀ p q, s (p + q) = s p + s q := fun p q => by
    show e.symm _ = e.symm _ + e.symm _
    rw [← map_add (f := _)]
    congr 1
    refine Prod.ext (funext fun i => lift_add _ _) (funext fun i => lift_add _ _)
  have sSmul : ∀ (t : ℝ) p, s (t • p) = realAd F t • s p := fun t p => by
    show e.symm _ = realAd F t • e.symm _
    rw [← map_smul]
    congr 1
    refine Prod.ext (funext fun i => lift_smul _ _) (funext fun i => lift_smul _ _)
  have sAt : ∀ p, At (evI F) (s p) := fun p c hc => by
    show c • e.symm _ = 0
    rw [← map_smul]
    have : c • ((fun i => lift (p.1 i), fun i => lift (p.2 i)) : (κ → AF F) × (κ → AF F)) = 0 :=
      Prod.ext (funext fun i => at_lift _ c hc) (funext fun i => at_lift _ c hc)
    rw [this, map_zero]
  let Ψ : ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) →ₗ[ℝ]
      (InfinitePlace F → Matrix α β ℂ) :=
    { toFun := fun p w => (s p).map (piInf (emb w))
      map_add' := fun p q => by
        funext w
        rw [sAdd]
        ext i j
        simp
      map_smul' := fun t p => by
        funext w
        rw [sSmul]
        ext i j
        simp [GlobalTheory.CompanionTheory.RealAdeleComponent.piInf_realAd_smul] }
  have hΨ : ∀ p w, Ψ p w = (s p).map (piInf (emb w)) := fun _ _ => rfl
  have inj : Function.Injective Ψ := by
    refine (injective_iff_map_eq_zero Ψ).2 fun p hp => ?_
    have s0 : s p = 0 := by
      ext i j
      refine GlobalTheory.CompanionTheory.CMAdele.eq_zero_of_piInf σ h emb _ (at_entry' (sAt p) i j) fun w => ?_
      have := congrFun (congrFun (congrFun hp w) i) j
      simpa [hΨ] using this
    have e0 := es p
    rw [s0, map_zero] at e0
    refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
    · have := congrFun (congrArg Prod.fst e0) i
      have := congrArg (evI F) this
      rw [evI_lift] at this
      simpa [evI_zero] using this.symm
    · have := congrFun (congrArg Prod.snd e0) i
      have := congrArg (evI F) this
      rw [evI_lift] at this
      simpa [evI_zero] using this.symm
  have surj : Function.Surjective Ψ := fun Z => by
    choose x hxA hxZ using fun (ij : α × β) => GlobalTheory.CompanionTheory.RealPlaceAdele.exists_adele_piInf σ h emb (fun w => Z w ij.1 ij.2)
    let u : Matrix α β (AE F E) := Matrix.of fun i j => x (i, j)
    have uAt : At (evI F) u := fun c hc => by
      ext i j
      exact hxA (i, j) c hc
    have hAt2 : ∀ c : AF F, evI F c = 0 → c • e u = 0 := fun c hc => by
      rw [← map_smul, uAt c hc, map_zero]
    refine ⟨(fun i => evI F ((e u).1 i), fun i => evI F ((e u).2 i)), ?_⟩
    have su : s (fun i => evI F ((e u).1 i), fun i => evI F ((e u).2 i)) = u := by
      show e.symm _ = u
      rw [LinearEquiv.symm_apply_eq]
      refine Prod.ext (funext fun i => lift_evI fun c hc => ?_) (funext fun i => lift_evI fun c hc => ?_)
      · exact congrFun (congrArg Prod.fst (hAt2 c hc)) i
      · exact congrFun (congrArg Prod.snd (hAt2 c hc)) i
    funext w
    rw [hΨ, su]
    ext i j
    exact hxZ (i, j) w
  let Ψe := LinearEquiv.ofBijective Ψ ⟨inj, surj⟩
  let Cp : (InfinitePlace F → Matrix α β ℂ) →ₗ[ℝ] (InfinitePlace F → Matrix α β ℂ) :=
    LinearMap.pi fun w => C w ∘ₗ LinearMap.proj w
  refine ⟨s, Ψe.symm.toLinearMap ∘ₗ Cp ∘ₗ Ψ, sAt, fun p => ?_, fun p w => ?_⟩
  · rw [es]
    exact ⟨funext fun i => evI_lift _, funext fun i => evI_lift _⟩
  · have : Ψ ((Ψe.symm.toLinearMap ∘ₗ Cp ∘ₗ Ψ) p) = Cp (Ψ p) := Ψe.apply_symm_apply _
    exact congrFun this w

def Rel (τ : ∀ w : InfinitePlace F, EmbOver E w) (ε : InfinitePlace F → ℤˣ) (θ : InfinitePlace F → Matrix (Fin m) (Fin m) ℂ)
    (θ' : InfinitePlace F → Matrix β β ℂ) (u u' : Matrix (Fin m) β (AE F E)) : Prop :=
  ∀ w, u'.map (piInf (τ w)) = (((ε w : ℤ) : ℂ) * Complex.I) • (θ w * u.map (piInf (τ w)) * (θ' w)ᵀ)

def dd0 (p : (κ → AF F) × (κ → AF F)) (f : SInf F κ) : SInf F κ := dop (nf p.1) (Dense.linForm (nf p.2)) f

def Gs (e : Matrix (Fin m) β (AE F E) ≃ₗ[AF F] (κ → AF F) × (κ → AF F)) (τ : ∀ w : InfinitePlace F, EmbOver E w)
    (ε : InfinitePlace F → ℤˣ) (θ : InfinitePlace F → Matrix (Fin m) (Fin m) ℂ) (θ' : InfinitePlace F → Matrix β β ℂ)
    (f : SInf F κ) : Prop :=
  ∀ u u', At (evI F) u → At (evI F) u' → Rel τ ε θ θ' u u' → dd0 (e u') f = Complex.I • dd0 (e u) f

variable {e : Matrix (Fin m) β (AE F E) ≃ₗ[AF F] (κ → AF F) × (κ → AF F)} {τ : ∀ w : InfinitePlace F, EmbOver E w}
  {ε ε' : InfinitePlace F → ℤˣ} {θ : InfinitePlace F → Matrix (Fin m) (Fin m) ℂ} {θ' : InfinitePlace F → Matrix β β ℂ}
  {f f' : SInf F κ}

theorem Gs.gau (h : IsCMExt F E σ) (hf : Gs e τ ε θ θ' f) (h0 : f ≠ 0) : ∃ k, Gau f k := by
  let C : InfinitePlace F → Matrix (Fin m) β ℂ →ₗ[ℝ] Matrix (Fin m) β ℂ := fun w =>
    { toFun := fun x => (((ε w : ℤ) : ℂ) * Complex.I) • (θ w * x * (θ' w)ᵀ)
      map_add' := fun x y => by rw [Matrix.mul_add, Matrix.add_mul, smul_add]
      map_smul' := fun t x => by
        simp only [Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply]
        rw [smul_comm] }
  obtain ⟨S, J, sAt, sev, sJ⟩ := exists_real_structure' σ h τ e C
  let T : (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] ℝ :=
    LinearMap.mk₂ ℝ (fun y b => Dense.linForm b y) (fun y y' b => map_add _ y y') (fun t y b => map_smul _ t y)
      (fun y b b' => by simp only [linForm_apply, Pi.add_apply, mul_add, Finset.sum_add_distrib, map_add (f := _)])
      (fun t y b => by simp only [linForm_apply, Pi.smul_apply, mul_smul_comm, ← Finset.smul_sum, map_smul])
  obtain ⟨k, hk⟩ := GlobalTheory.CompanionTheory.Twist.FockLogDeriv.main T (fun b hb => funext fun i => trace_mul_eq_zero _ fun y => by
      have : Dense.linForm b (Pi.single i y) = 0 := hb _
      rw [linForm_apply, Finset.sum_eq_single i (fun j _ hj => by simp [hj]) (by simp), Pi.single_eq_same, mul_comm] at this
      exact this) J f h0 fun p y => by
    have := congrArg (fun g : SInf F κ => g y) (hf (S p) (S (J p)) (sAt _) (sAt _) fun w => sJ p w)
    have e1 : ∀ q, nf (e (S q)).1 = q.1 := fun q => (sev q).1
    have e2 : ∀ q, nf (e (S q)).2 = q.2 := fun q => (sev q).2
    simp only [dd0, SchwartzMap.smul_apply, smul_eq_mul, dop_apply, e1, e2] at this
    exact this
  exact ⟨k, gau_of h0 hk⟩

theorem exists_rel (h : IsCMExt F E σ) (ε : InfinitePlace F → ℤˣ) (u : Matrix (Fin m) β (AE F E)) :
    ∃ u', At (evI F) u' ∧ Rel τ ε θ θ' u u' := by
  choose x hx hz using fun i j => GlobalTheory.CompanionTheory.RealPlaceAdele.exists_adele_piInf σ h τ fun w =>
    ((((ε w : ℤ) : ℂ) * Complex.I) • (θ w * u.map (piInf (τ w)) * (θ' w)ᵀ)) i j
  exact ⟨Matrix.of x, fun c hc => Matrix.ext fun i j => hx i j c hc, fun w => Matrix.ext fun i j => hz i j w⟩

theorem Gs.same (h : IsCMExt F E σ) (hf : Gs e τ ε θ θ' f) (hf' : Gs e τ ε' θ θ' f') (h0 : f ≠ 0) (h0' : f' ≠ 0) :
    Gs e τ ε θ θ' f' := by
  intro u u' hu hu' hr
  obtain ⟨k, g⟩ := hf.gau h h0
  obtain ⟨k', g'⟩ := hf'.gau h h0'
  obtain ⟨u'', hu'', hr'⟩ := exists_rel (τ := τ) (θ := θ) (θ' := θ') h ε' u
  have hv : At (evI F) (u' - u'') := fun c hc => by rw [smul_sub, hu' c hc, hu'' c hc, sub_zero]
  obtain ⟨v', hv', hs⟩ := exists_rel (τ := τ) (θ := θ) (θ' := θ') h ε (u' - u'')
  have hs' : Rel τ ε' θ θ' (u' - u'') (-v') := fun w => by
    rw [Matrix.map_neg _ (map_neg _), hs w, Matrix.map_sub _ (map_sub _), hr w, hr' w, ← sub_smul]
    simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, ← neg_smul]
    congr 1
    rcases Int.units_eq_one_or (ε w) with a | a <;> rcases Int.units_eq_one_or (ε' w) with b | b <;> simp [a, b]
  have h2 := hf' _ _ hv (fun c hc => by rw [smul_neg, hv' c hc, neg_zero]) hs'
  have en : ∀ z : κ → AF F, nf (-z) = -nf z := fun z => funext fun i =>
    map_neg (InfiniteAdeleRing.ringEquiv_mixedSpace F) (z i).1
  have el : ∀ b : κ → mixedEmbedding.mixedSpace F, Dense.linForm (-b) = -Dense.linForm b := fun b => by
    exact ContinuousLinearMap.ext fun y => by
      simp only [linForm_apply, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib, map_neg, ContinuousLinearMap.neg_apply]
  rw [map_neg, dd0, Prod.fst_neg, Prod.snd_neg, en, en, el] at h2
  obtain ⟨a0, l0⟩ := opp g g' (hf _ _ hv hv' hs) h2
  rw [← hf' u u'' hu hu'' hr', ← sub_add_cancel u' u'', map_add (f := _), dd0, Prod.fst_add, Prod.snd_add, nf_add, nf_add,
    linForm_add, a0, l0, zero_add, zero_add, dd0]

end GlobalTheory.ThK.Dbl.Box

end
end

noncomputable section

namespace GlobalTheory.ThK.Dbl.Box

open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl.Dense

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {κ β : Type} [Fintype κ] [Fintype β] {m n : ℕ}

variable {A : Spc F E m} {Y : Spc F E n} {B : Base F E}
  {d' : Darboux (symp (R := AF F) (cA σ) (-1) (incM F A.J) (incM F Y.J)) κ}
  {dd : Darboux (symp (R := AF F) (cA σ) (-1) (incM F A.J) (dbl (incM F Y.J))) (κ ⊕ κ)}
  {om : G2 σ Y →* Module.End ℂ ((κ ⊕ κ → AF F) → ℂ)} {K : Subgroup (G2 σ Y)}

theorem at_e {W : Type} [AddCommGroup W] [Module (AF F) W] {ι : Type} (e : W ≃ₗ[AF F] (ι → AF F) × (ι → AF F)) {u : W}
    (hu : At (evI F) u) : At (evI F) (e u) := fun s hs => by rw [← map_smul, hu s hs, map_zero]

theorem imp (hs : IsSplitting (adeleClass F) B.ψ dd (actB (cA σ)) om) (k : G2 σ Y) :
    Imp B.ψ (om k) fun w => dd.e (actB (cA σ) k (dd.e.symm w)) :=
  ⟨hs.pres k, hs.adm k, fun w w' => by simp only [actB, map_add (f := _), Matrix.add_mul],
    fun c w => by simp only [actB, map_smul, Matrix.smul_mul], fun w φ hφ => by
      have := hs.impl k (dd.e.symm w) φ hφ
      rwa [Darboux.rho, LinearEquiv.apply_symm_apply] at this⟩

theorem om_D (hψ : IsStd B.ψ) (hs : IsSplitting (adeleClass F) B.ψ dd (actB (cA σ)) om) (k : G2 σ Y) {u} (hu : At (evI F) u) {Φ}
    (hΦ : Φ ∈ schA F (κ ⊕ κ)) : om k (D (dd.e u) Φ) = D (dd.e (actB (cA σ) k u)) (om k Φ) := by
  have := (imp hs k).inter hψ (at_e dd.e hu) hΦ
  rwa [LinearEquiv.symm_apply_apply] at this

theorem at_actB (k : G2 σ Y) {u : Matrix (Fin m) (Fin n ⊕ Fin n) (AE F E)} (hu : At (evI F) u) : At (evI F) (actB (cA σ) k u) :=
  fun s hs => by rw [actB, ← Matrix.smul_mul, hu s hs, Matrix.zero_mul]

theorem actB_inv (k : G2 σ Y) (u : Matrix (Fin m) (Fin n ⊕ Fin n) (AE F E)) : actB (cA σ) k (actB (cA σ) k⁻¹ u) = u := by
  rw [actB, actB, Matrix.mul_assoc, ← Matrix.transpose_mul, ← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel]
  simp


variable (om K) in
def kfin : Submodule ℂ ((κ ⊕ κ → AF F) → ℂ) where
  carrier := {Φ | ∃ N : Submodule ℂ ((κ ⊕ κ → AF F) → ℂ), FiniteDimensional ℂ N ∧ N ≤ schA F _ ∧ Φ ∈ N ∧ ∀ k ∈ K, ∀ Ψ ∈ N, om k Ψ ∈ N}
  zero_mem' := ⟨⊥, inferInstance, bot_le, zero_mem _, fun k _ g hg => by rw [(Submodule.mem_bot ℂ).1 hg, map_zero]; exact zero_mem _⟩
  add_mem' := by
    rintro f g ⟨N, _, h0, h1, h2⟩ ⟨N', _, h0', h1', h2'⟩
    refine ⟨N ⊔ N', inferInstance, sup_le h0 h0', Submodule.add_mem_sup h1 h1', fun k hk g hg => ?_⟩
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 hg
    rw [map_add (f := _)]
    exact Submodule.add_mem_sup (h2 k hk x hx) (h2' k hk y hy)
  smul_mem' := fun c _ ⟨N, h, h0, h1, h2⟩ => ⟨N, h, h0, N.smul_mem c h1, h2⟩

theorem D_kfin (hψ : IsStd B.ψ) (hs : IsSplitting (adeleClass F) B.ψ dd (actB (cA σ)) om) {u} (hu : At (evI F) u) {Φ}
    (h : Φ ∈ kfin om K) : D (dd.e u) Φ ∈ kfin om K := by
  obtain ⟨N, _, h0, h1, h2⟩ := h
  obtain ⟨N', _, h4⟩ := exists_D_fin N h0
  refine ⟨Submodule.span ℂ {z | ∃ v, At (evI F) v ∧ ∃ x ∈ N, z = D (dd.e v) x},
    Submodule.finiteDimensional_of_le (S₂ := N') (Submodule.span_le.2 ?_), Submodule.span_le.2 ?_,
    Submodule.subset_span ⟨u, hu, Φ, h1, rfl⟩, fun k hk z hz => ?_⟩
  · rintro _ ⟨v, -, x, hx, rfl⟩
    exact h4 _ _ x hx
  · rintro _ ⟨v, -, x, hx, rfl⟩
    exact DP_mem (h0 hx) _ _
  · induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨v, hv, x, hx, rfl⟩ := hz
      exact Submodule.subset_span ⟨_, at_actB k hv, _, h2 k hk x hx, om_D hψ hs k hv (h0 hx)⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add _ _ _ _ i j => rw [map_add (f := _)]; exact add_mem i j
    | smul c _ _ i => rw [map_smul]; exact Submodule.smul_mem _ _ i

abbrev th2 (Y : Spc F E n) (w : InfinitePlace F) := Matrix.fromBlocks (Y.θ w) 0 0 (-Y.θ w)

theorem vac_kfin (hL : FinLevel) (hB : B.IsGood σ) (hK : IsStab2 B K) (hc : IsCompact (K : Set (G2 σ Y)))
    (hs : IsSplitting (adeleClass F) B.ψ dd (actB (cA σ)) om) {ε} {Φ} (hΦ : Φ ∈ schA F (κ ⊕ κ))
    (hv : ∀ u u', At (evI F) u → At (evI F) u' → Rel B.emb ε A.θ (th2 Y) u u' → D (dd.e u') Φ = Complex.I • D (dd.e u) Φ) :
    Φ ∈ kfin om K := by
  obtain ⟨Λ, l1, l2, s, s1, s2⟩ := hL F E σ B m n A Y hB _ dd K hc Φ hΦ
  have radd : ∀ u (x y : (κ ⊕ κ → AF F) → ℂ), dd.rho B.ψ u (x + y) = dd.rho B.ψ u x + dd.rho B.ψ u y := fun u x y =>
    funext fun _ => mul_add _ _ _
  have rsmul : ∀ u (c : ℂ) (x : (κ ⊕ κ → AF F) → ℂ), dd.rho B.ψ u (c • x) = c • dd.rho B.ψ u x := fun u c x =>
    funext fun _ => mul_left_comm _ _ _
  let N : Submodule ℂ ((κ ⊕ κ → AF F) → ℂ) :=
    { carrier := {Ψ | Ψ ∈ schA F _ ∧ (∀ u ∈ Λ, dd.rho B.ψ u Ψ = Ψ) ∧ ∀ u u', At (evI F) u → At (evI F) u' →
        Rel B.emb ε A.θ (th2 Y) u u' → D (dd.e u') Ψ = Complex.I • D (dd.e u) Ψ}
      zero_mem' := ⟨zero_mem _, fun u _ => funext fun _ => mul_zero _, fun _ _ _ _ _ => by simp only [D, DP_zero, smul_zero]⟩
      add_mem' := fun h h' => ⟨add_mem h.1 h'.1, fun u hu => by rw [radd, h.2.1 u hu, h'.2.1 u hu], fun u u' a b c => by
        have e1 := h.2.2 u u' a b c
        have e2 := h'.2.2 u u' a b c
        simp only [D] at e1 e2 ⊢
        rw [DP_add h.1 h'.1, DP_add h.1 h'.1, e1, e2, smul_add]⟩
      smul_mem' := fun t _ h => ⟨Submodule.smul_mem _ _ h.1, fun u hu => by rw [rsmul, h.2.1 u hu], fun u u' a b c => by
        have e1 := h.2.2 u u' a b c
        simp only [D] at e1 ⊢
        rw [DP_smul h.1, DP_smul h.1, e1, smul_comm]⟩ }
  refine ⟨N, ?_, fun _ h => h.1, ⟨hΦ, l2, hv⟩, fun k hk Ψ h => ⟨hs.pres k _ h.1, fun u hu => ?_, fun u u' a b c => ?_⟩⟩
  · refine FiniteDimensional.of_injective ((LinearMap.pi fun y : s => LinearMap.proj y.1) ∘ₗ N.subtype)
      ((injective_iff_map_eq_zero _).2 fun Ψ h0 => Subtype.ext (funext fun z => ?_))
    have sp : ∀ x (y : κ ⊕ κ → AF F), (∀ i, evI F (y i) = 0) → pt x 0 + y = pt x (fn y) := fun x y hy => by
      rw [← pt_self (pt x 0 + y), nf_add, nf_pt, show nf y = 0 from funext hy, add_zero]
      exact congrArg (pt x) (funext fun i => zero_add _)
    have z0 : ∀ i, evI F (pt 0 (fn z) i) = 0 := fun i => congrFun (evI_pt 0 (fn z)) i
    have := s2 Ψ.1 Ψ.2.2.1 (pt (nf z) 0) (at_pt _) (fun y hy => ?_) _ z0
    · rwa [sp _ _ z0, show fn (pt 0 (fn z)) = fn z from rfl, pt_self] at this
    obtain ⟨f, e⟩ := slice Ψ.2.1 (fn y)
    have g : Gs dd.e B.emb ε A.θ (th2 Y) f := fun u u' a b c => SchwartzMap.ext fun x => by
      have := congrFun (Ψ.2.2.2 u u' a b c) (pt x (fn y))
      rwa [Pi.smul_apply, D, D, DP_pt e, DP_pt e] at this
    rw [sp _ _ (s1 y hy), e]
    by_cases hf : f = 0
    · rw [hf]; rfl
    obtain ⟨_, hg⟩ := g.gau hB.cm hf
    refine (hg.ne 0 ?_).elim
    rw [← e, ← show nf y = 0 from funext (s1 y hy), pt_self]
    exact congrFun h0 ⟨y, hy⟩
  · rw [← actB_inv k u, ← hs.impl k _ _ h.1, h.2.1 _ ((l1 u hu).2.2 _ (inv_mem hk))]
  · rw [← actB_inv k u, ← actB_inv k u', ← om_D hB.std hs k (at_actB _ a) h.1, ← om_D hB.std hs k (at_actB _ b) h.1, ← map_smul]
    refine congrArg (om k) (h.2.2 _ _ (at_actB _ a) (at_actB _ b) fun w => ?_)
    have cm := (((hK k⁻¹).1 (inv_mem hk)).1 w).eq
    simp only [actB, Matrix.map_mul, Matrix.transpose_map, c w, Matrix.smul_mul, Matrix.mul_assoc, ← Matrix.transpose_mul]
    exact congrArg (fun x => _ • (_ * (_ * xᵀ))) cm

theorem D_box (hψ : IsStd B.ψ) (hd : IsDblCoord (cA σ) (-1) (incM F A.J) (incM F Y.J) d' dd) {u₁ u₂} (h1 : At (evI F) u₁)
    (h2 : At (evI F) u₂) (f₁ f₂ : SInf F κ) {g₁ g₂} (s1 : g₁ ∈ SB (κ → Af F)) (s2 : g₂ ∈ SB (κ → Af F)) :
    D (dd.e (Matrix.fromCols u₁ u₂)) (boxFun (pureA F f₁ g₁) (star (pureA F f₂ g₂))) =
      boxFun (pureA F (dd0 (d'.e u₁) f₁) g₁) (star (pureA F f₂ g₂)) + boxFun (pureA F f₁ g₁) (star (pureA F (dd0 (d'.e u₂) f₂) g₂)) := by
  have m1 : pureA F f₁ g₁ ∈ schA F κ := Submodule.subset_span ⟨f₁, g₁, s1, rfl⟩
  have m2 : pureA F f₂ g₂ ∈ schA F κ := Submodule.subset_span ⟨f₂, g₂, s2, rfl⟩
  have h12 : At (evI F) (Matrix.fromCols u₁ u₂) := fun s hs => by
    ext i (j | j)
    exacts [congrFun₂ (h1 s hs) i j, congrFun₂ (h2 s hs) i j]
  funext z
  have a := hasD hψ (at_e dd.e h12) (box_mem m1 m2) z
  have a1 := hasD hψ (at_e d'.e h1) m1 (z ∘ Sum.inl)
  have a2 := (hasD hψ (at_e d'.e h2) m2 (z ∘ Sum.inr)).star
  have b := a1.mul a2
  have sc0 : ∀ {w}, At (evI F) w → ∀ (Ψ : (κ → AF F) → ℂ) x, schr B.ψ (realAd F 0 • w) Ψ x = Ψ x := fun hw Ψ x => by
    rw [← pt_self x, schr_pt hψ hw]; simp [hl]
  simp only [sc0 (at_e d'.e h1), sc0 (at_e d'.e h2), D, DP_pure] at b
  refine a.unique (b.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_))
  have hb := fun s hs => congrArg Prod.snd (at_e d'.e h2 s hs)
  have cj := phase_line B.ψ hψ (d'.e u₂).1 (d'.e u₂).2 (z ∘ Sum.inr) hb t
  have cj' : B.ψ (-((z ∘ Sum.inr) ⬝ᵥ (realAd F t • (d'.e u₂).2) + ⅟(2 : AF F) * ((realAd F t • (d'.e u₂).1) ⬝ᵥ (realAd F t • (d'.e u₂).2)))) =
      star (B.ψ ((z ∘ Sum.inr) ⬝ᵥ (realAd F t • (d'.e u₂).2) + ⅟(2 : AF F) * ((realAd F t • (d'.e u₂).1) ⬝ᵥ (realAd F t • (d'.e u₂).2)))) := by
    rw [AddChar.map_neg_eq_inv, cj, ← Complex.exp_neg, Complex.star_def, ← Complex.exp_conj]
    congr 1
    simp only [map_mul, map_neg, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
    ring
  simp only [hd u₁ u₂, schr, boxFun, Pi.mul_apply, Pi.star_apply, star_mul', Prod.smul_fst, Prod.smul_snd, Prod.smul_mk]
  rw [mul_mul_mul_comm, ← cj', ← AddChar.map_add_eq_mul]
  congr 2
  simp only [dotProduct, Fintype.sum_sum_type, Pi.smul_apply, Sum.elim_inl, Sum.elim_inr, Pi.neg_apply, Function.comp_apply,
    smul_neg, mul_neg, Finset.sum_neg_distrib]
  ring

theorem box_kfin (hL : FinLevel) (hB : B.IsGood σ) (hK : IsStab2 B K) (hc : IsCompact (K : Set (G2 σ Y)))
    (hs : IsSplitting (adeleClass F) B.ψ dd (actB (cA σ)) om) (hd : IsDblCoord (cA σ) (-1) (incM F A.J) (incM F Y.J) d' dd)
    {P : Submodule ℂ (SInf F κ)} (hP : ∀ N : Submodule ℂ (SInf F κ), (∀ ε f, Gs d'.e B.emb ε A.θ Y.θ f → f ∈ N) →
      (∀ u, At (evI F) u → ∀ f ∈ N, dd0 (d'.e u) f ∈ N) → P ≤ N) {g₁ g₂} (s1 : g₁ ∈ SB (κ → Af F)) (s2 : g₂ ∈ SB (κ → Af F))
    {f₁ f₂} (h1 : f₁ ∈ P) (h2 : f₂ ∈ P) : boxFun (pureA F f₁ g₁) (star (pureA F f₂ g₂)) ∈ kfin om K := by
  let bx : SInf F κ → SInf F κ → (κ ⊕ κ → AF F) → ℂ := fun f f' => boxFun (pureA F f g₁) (star (pureA F f' g₂))
  have z1 : ∀ f', bx 0 f' = 0 := fun f' => funext fun z => by simp [bx, boxFun, pureA]
  have z2 : ∀ f, bx f 0 = 0 := fun f => funext fun z => by simp [bx, boxFun, pureA]
  have a1 : ∀ f g f', bx (f + g) f' = bx f f' + bx g f' := fun f g f' => funext fun z => by simp [bx, boxFun, pureA, add_mul]
  have a2 : ∀ f f' g, bx f (f' + g) = bx f f' + bx f g := fun f g f' => funext fun z => by simp [bx, boxFun, pureA, add_mul, mul_add]
  have c1 : ∀ (c : ℂ) f f', bx (c • f) f' = c • bx f f' := fun c f f' => funext fun z => by simp [bx, boxFun, pureA, mul_assoc]
  have c2 : ∀ (c : ℂ) f f', bx f (c • f') = star c • bx f f' := fun c f f' => funext fun z => by
    simp [bx, boxFun, pureA]; ring
  have at0 : At (evI F) (0 : Matrix (Fin m) (Fin n) (AE F E)) := fun _ _ => smul_zero _
  have d0 : ∀ f : SInf F κ, dd0 (d'.e 0) f = 0 := fun f => SchwartzMap.ext fun x => by
    simp [dd0, dop_apply, show nf (0 : κ → AF F) = 0 from funext fun _ => evI_zero, linForm_apply]
  have atc : ∀ {u₁ u₂ : Matrix (Fin m) (Fin n) (AE F E)}, At (evI F) u₁ → At (evI F) u₂ → At (evI F) (Matrix.fromCols u₁ u₂) :=
    fun h1 h2 s hs => by
      ext i (j | j)
      exacts [congrFun₂ (h1 s hs) i j, congrFun₂ (h2 s hs) i j]
  have base : ∀ ε f, Gs d'.e B.emb ε A.θ Y.θ f → ∀ ε' f', Gs d'.e B.emb ε' A.θ Y.θ f' → bx f f' ∈ kfin om K := by
    intro ε f hf ε' f' hf'
    by_cases e : f = 0
    · rw [e, z1]; exact zero_mem _
    by_cases e' : f' = 0
    · rw [e', z2]; exact zero_mem _
    have hf'' := hf.same hB.cm hf' e e'
    refine vac_kfin (ε := ε) hL hB hK hc hs (box_mem (Submodule.subset_span ⟨f, g₁, s1, rfl⟩) (Submodule.subset_span ⟨f', g₂, s2, rfl⟩))
      fun u u' a b c => ?_
    have al : ∀ {v : Matrix (Fin m) (Fin n ⊕ Fin n) (AE F E)}, At (evI F) v → At (evI F) v.toCols₁ ∧ At (evI F) v.toCols₂ := fun h =>
      ⟨fun s hs => Matrix.ext fun i j => congrFun₂ (h s hs) i (.inl j), fun s hs => Matrix.ext fun i j => congrFun₂ (h s hs) i (.inr j)⟩
    have r1 : Rel B.emb ε A.θ Y.θ u.toCols₁ u'.toCols₁ := fun w => Matrix.ext fun i j => by
      have := congrFun₂ (c w) i (.inl j)
      simpa [Matrix.mul_apply, Fintype.sum_sum_type] using this
    have r2 : Rel B.emb ε A.θ Y.θ (-u.toCols₂) u'.toCols₂ := fun w => Matrix.ext fun i j => by
      have := congrFun₂ (c w) i (.inr j)
      simpa [Matrix.mul_apply, Fintype.sum_sum_type] using this
    have n2 : dd0 (d'.e (-u.toCols₂)) f' = -dd0 (d'.e u.toCols₂) f' := SchwartzMap.ext fun x => by
      have ng : ∀ y : κ → AF F, nf (-y) = -nf y := fun y => funext fun i => map_neg (InfiniteAdeleRing.ringEquiv_mixedSpace F) _
      simp only [dd0, map_neg, Prod.fst_neg, Prod.snd_neg, ng, dop_apply, SchwartzMap.neg_apply, linForm_apply, Pi.neg_apply, mul_neg,
        Finset.sum_neg_distrib]
      push_cast
      ring
    rw [← u.fromCols_toCols, ← u'.fromCols_toCols, D_box hB.std hd (al a).1 (al a).2 f f' s1 s2,
      D_box hB.std hd (al b).1 (al b).2 f f' s1 s2, hf _ _ (al a).1 (al b).1 r1,
      hf'' _ _ (fun s hs => by rw [smul_neg, (al a).2 s hs, neg_zero]) (al b).2 r2, n2, smul_neg, ← neg_smul]
    change bx _ _ + bx _ _ = _ • (bx _ _ + bx _ _)
    rw [c1, c2, smul_add]
    simp
  refine hP ⟨⟨⟨{f' | ∀ f ∈ P, bx f f' ∈ kfin om K}, fun h h' f hf => a2 f _ _ ▸ add_mem (h f hf) (h' f hf)⟩,
    fun f _ => z2 f ▸ zero_mem _⟩, fun c _ h f hf => c2 c f _ ▸ Submodule.smul_mem _ _ (h f hf)⟩ (fun ε' f' hf' => ?_)
    (fun u hu f' h f hf => ?_) h2 f₁ h1
  · refine hP ⟨⟨⟨{f | bx f f' ∈ kfin om K}, fun h h' => by
      rw [Set.mem_setOf_eq, a1]; exact add_mem h h'⟩, by rw [Set.mem_setOf_eq, z1]; exact zero_mem _⟩,
      fun c _ h => by rw [Set.mem_setOf_eq, c1]; exact Submodule.smul_mem _ _ h⟩ (fun ε f hf => base ε f hf ε' f' hf') fun u hu f h => ?_
    have := D_kfin hB.std hs (atc hu at0) h
    rw [D_box hB.std hd hu at0 f f' s1 s2, d0] at this
    change bx _ _ + bx _ _ ∈ _ at this
    rw [z2, add_zero] at this
    exact this
  · have := D_kfin hB.std hs (atc at0 hu) (h f hf)
    rw [D_box hB.std hd at0 hu f f' s1 s2, d0] at this
    change bx _ _ + bx _ _ ∈ _ at this
    rwa [z1, zero_add] at this

end GlobalTheory.ThK.Dbl.Box

end
