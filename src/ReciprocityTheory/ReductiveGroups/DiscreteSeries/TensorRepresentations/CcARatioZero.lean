module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.TraceFormula

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.PoleMatch
section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.PoleMatchA
noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

open MeasureTheory

section Generic

variable {W : Type*} [AddCommGroup W] [Module ℂ W]

theorem pm_pow_eig (A : Module.End ℂ W) {z : ℂ} {f : W} (h : A f = z • f) (k : ℕ) :
    (A ^ k) f = z ^ k • f := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', mul_apply_eq_comp, ih, map_smul, h, smul_smul, pow_succ]

theorem pm_proj_decomp (A Q : Module.End ℂ W) (T : Submodule ℂ W) (B : Finset ℝ) (z : ℂ)
    (hQ1 : ∀ f ∈ T, A f = z • f → Q f = f) (hQ0 : ∀ f ∈ T, ∀ z' : ℂ, z' ≠ z → A f = z' • f → Q f = 0)
    (fb : ℝ → W) (hfb : ∀ b, fb b ∈ T ∧ A (fb b) = ((b : ℝ) : ℂ) • fb b) :
    Q (∑ b ∈ B, fb b) = ∑ b ∈ B, if ((b : ℝ) : ℂ) = z then fb b else 0 := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  split_ifs with h
  · exact hQ1 _ (hfb b).1 (by rw [← h]; exact (hfb b).2)
  · exact hQ0 _ (hfb b).1 _ h (hfb b).2

theorem pm_agree (A : Module.End ℂ W) (T : Submodule ℂ W) (B : Finset ℝ)
    (hdec : ∀ f ∈ T, ∃ fb : ℝ → W, (∀ b, fb b ∈ T ∧ A (fb b) = ((b : ℝ) : ℂ) • fb b) ∧ f = ∑ b ∈ B, fb b)
    (P : ℝ → Module.End ℂ W)
    (hP1 : ∀ b, ∀ f ∈ T, A f = ((b : ℝ) : ℂ) • f → P b f = f)
    (hP0 : ∀ b, ∀ f ∈ T, ∀ z' : ℂ, z' ≠ ((b : ℝ) : ℂ) → A f = z' • f → P b f = 0) :
    (∀ f ∈ T, ∀ k : ℕ, (A ^ k) f = ∑ b ∈ B, ((b : ℝ) : ℂ) ^ k • P b f) ∧
      ∀ (Q : Module.End ℂ W) (z : ℂ), (∀ f ∈ T, A f = z • f → Q f = f) →
        (∀ f ∈ T, ∀ z' : ℂ, z' ≠ z → A f = z' • f → Q f = 0) →
        ∀ f ∈ T, Q f = ∑ b ∈ B, if ((b : ℝ) : ℂ) = z then P b f else 0 := by
  have hPb : ∀ fb : ℝ → W, (∀ b, fb b ∈ T ∧ A (fb b) = ((b : ℝ) : ℂ) • fb b) →
      ∀ b ∈ B, P b (∑ b' ∈ B, fb b') = fb b := by
    intro fb hfb b hb
    rw [pm_proj_decomp A (P b) T B _ (hP1 b) (hP0 b) fb hfb]
    simp [Complex.ofReal_inj, hb]
  refine ⟨fun f hf k => ?_, fun Q z hQ1 hQ0 f hf => ?_⟩
  · obtain ⟨fb, hfb, rfl⟩ := hdec f hf
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun b hb => ?_
    rw [hPb fb hfb b hb, pm_pow_eig A (hfb b).2]
  · obtain ⟨fb, hfb, rfl⟩ := hdec f hf
    rw [pm_proj_decomp A Q T B z hQ1 hQ0 fb hfb]
    refine Finset.sum_congr rfl fun b hb => ?_
    rw [hPb fb hfb b hb]

end Generic

theorem pm_single_mem {M : Type*} [AddCommGroup M] [Module ℂ M] (S : Submodule ℂ M) {x : M} (hx : x ∈ S)
    (c : Fin n) : Pi.single c x ∈ tensSub (n := n) S := by
  refine tset_mem.2 fun i => ?_
  by_cases h : i = c <;> simp [h, hx]

theorem pm_ptr {M : Type*} [AddCommGroup M] [Module ℂ M] (S : Submodule ℂ M)
    (Q : Module.End ℂ (Fin n → M)) (R : ℝ → Module.End ℂ (Fin n → M)) (B : Finset ℝ) (g : ℝ → ℂ)
    (hQ : ∀ f ∈ tensSub S, Q f = ∑ b ∈ B, g b • R b f) {x : M} (hx : x ∈ S) :
    ptr Q x = ∑ b ∈ B, g b • ptr (R b) x := by
  simp only [ptr_apply, hQ _ (pm_single_mem S hx _), Finset.sum_apply, Pi.smul_apply, Finset.smul_sum]
  exact Finset.sum_comm

theorem pm_resid (dual : Bool) (lam : Fin n → ℝ) (s : Fin n) :
    resid (poleF dual lam) s = ((ratioF dual lam s : ℝ) : ℂ) := by
  cases dual
  · exact resid_poleV lam s
  · exact resid_poleVd lam s

theorem pm_pole_inj (dual : Bool) {lam : Fin n → ℝ} (hl : StrictAnti lam) : Function.Injective (poleF dual lam) := by
  cases dual
  · exact poleV_injective hl.injective
  · exact poleVd_injective hl.injective

theorem pm_char (dual : Bool) {M : Type*} [AddCommGroup M] [Module ℂ M] {E : Fin n → Fin n → Module.End ℂ M}
    {lam : Fin n → ℝ} {S : Submodule ℂ M} (hS : HasGelfandChar E lam S) (k : ℕ) (x : M) (hx : x ∈ S) :
    ptr (eeF dual E ^ k) x = PowerSeries.coeff (k + 1) (resSeries (poleF dual lam)) • x := by
  cases dual
  · exact ptr_eeV_pow_char hS k x hx
  · exact ptr_eeVd_pow_char hS k x hx

theorem pm_core (dual : Bool) {lam : Fin n → ℝ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {ε : Fin n → Bool}
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}
    (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) (hsm : ∀ v : D, IsSmoothVecU ε σ v)
    {V : Submodule ℂ D} (hgap : StdGap ε lam) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) (hW : ∀ v ∈ genSub E V, ∀ w ∈ genSub E V, MemLp (fun g : Formalism.REAL.UJ ε =>
      ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) * inner ℂ ((w : D) : H) (σ (Formalism.MainNotions.S.umat g) ((v : D) : H)))
      2 (Formalism.REAL.muG ε)) (hG : HasGelfandChar E lam (genSub E V)) :
    ∃ B : Finset ℝ, ∃ c : ℝ → ℂ, ∃ P : ℝ → Module.End ℂ (Fin n → D),
      (∀ z : ℂ, ∀ f ∈ tensSub (genSub E V), f ≠ 0 → eeF dual E f = z • f → ∃ b ∈ B, z = ((b : ℝ) : ℂ)) ∧
      (∀ b, ∀ f ∈ tensSub (genSub E V), P b f ∈ tensSub (genSub E V)) ∧
      (∀ b, ∀ f ∈ tensSub (genSub E V), eeF dual E (P b f) = ((b : ℝ) : ℂ) • P b f) ∧
      (∀ b, ∀ f ∈ tensSub (genSub E V), eeF dual E f = ((b : ℝ) : ℂ) • f → P b f = f) ∧
      (∀ b, ∀ x ∈ genSub E V, ptr (P b) x = c b • x) ∧
      (∀ b, c b = 0 → ∀ f ∈ tensSub (genSub E V), P b f = 0) ∧
      (∀ (Q : Module.End ℂ (Fin n → D)) (z : ℂ), (∀ f ∈ tensSub (genSub E V), eeF dual E f = z • f → Q f = f) →
        (∀ f ∈ tensSub (genSub E V), ∀ z' : ℂ, z' ≠ z → eeF dual E f = z' • f → Q f = 0) →
        ∀ x ∈ genSub E V, ptr Q x = (∑ b ∈ B, if ((b : ℝ) : ℂ) = z then c b else 0) • x) ∧
      (∀ p : ℂ, (∑ b ∈ B, if ((b : ℝ) : ℂ) = p then c b else 0) =
        ∑ s ∈ univ.filter (fun s => poleF dual lam s = p), ((ratioF dual lam s : ℝ) : ℂ)) ∧
      ∃ x₀ ∈ genSub E V, x₀ ≠ 0 := by
  obtain ⟨B, hdec, hev⟩ := ee_decomp dual hσ hD hgap hV hc hVK hW
  have hPex := fun b : ℝ => eigenProj_exists dual hσ hD hgap hV hc hVK hW ((b : ℝ) : ℂ)
  choose P hPG hPP hPz hP1 hP0 using hPex
  have hsc := fun b => ptr_scalar dual hσ hD hgap hV hc hVK (hPG b)
  choose c hcb using hsc
  have hPB := fun b => eigenProj_formB dual hσ hD hgap hV hc hVK hW _ (hPG b).1 (hPz b) (hP1 b) (hP0 b)
  have htr := fun b => trace_nonneg dual hσ hD hsm hgap hV hc hVK hW (hPG b) (hPP b) (hPB b) (hPz b) (hcb b)
  obtain ⟨hpow, hagr⟩ := pm_agree (eeF dual E) (tensSub (genSub E V)) B hdec P hP1 hP0
  have hQ : ∀ (Q : Module.End ℂ (Fin n → D)) (z : ℂ),
      (∀ f ∈ tensSub (genSub E V), eeF dual E f = z • f → Q f = f) →
      (∀ f ∈ tensSub (genSub E V), ∀ z' : ℂ, z' ≠ z → eeF dual E f = z' • f → Q f = 0) →
      ∀ x ∈ genSub E V, ptr Q x = (∑ b ∈ B, if ((b : ℝ) : ℂ) = z then c b else 0) • x := by
    intro Q z hQ1 hQ0 x hx
    rw [pm_ptr (genSub E V) Q P B (fun b => if ((b : ℝ) : ℂ) = z then 1 else 0)
      (fun f hf => by
        rw [hagr Q z hQ1 hQ0 f hf]
        exact sum_congr rfl fun b _ => by split_ifs <;> simp) hx, Finset.sum_smul]
    refine sum_congr rfl fun b _ => ?_
    rw [hcb b x hx]
    split_ifs <;> simp
  have hVle : V ≤ genSub E V := by
    unfold genSub
    exact le_sInf fun T hT => hT.1
  obtain ⟨x₀, hx₀V, hx₀0, -⟩ := hV.2.2.2
  have hx₀ : x₀ ∈ genSub E V := hVle hx₀V
  have hmom : ∀ k : ℕ, ∑ i : B, c i * ((i : ℝ) : ℂ) ^ k =
      ∑ s, resid (poleF dual lam) s * poleF dual lam s ^ k := by
    intro k
    rw [Finset.sum_coe_sort B (fun b => c b * ((b : ℝ) : ℂ) ^ k), ← resSeries_coeff_succ (pm_pole_inj dual hgap.1) k]
    apply smul_left_injective ℂ hx₀0
    beta_reduce
    rw [← pm_char dual hG k x₀ hx₀, pm_ptr (genSub E V) _ P B (fun b => ((b : ℝ) : ℂ) ^ k)
      (fun f hf => hpow f hf k) hx₀, Finset.sum_smul]
    refine sum_congr rfl fun b _ => ?_
    rw [hcb b x₀ hx₀, smul_smul, mul_comm (c b)]
  refine ⟨B, c, P, hev, fun b => (hPG b).1, hPz, hP1, hcb, fun b h0 => (htr b).2.2 h0, hQ, fun p => ?_,
    x₀, hx₀, hx₀0⟩
  have hf := moment_fibre (fun i : B => ((i : ℝ) : ℂ)) (fun i => c i) (poleF dual lam) (resid (poleF dual lam)) hmom p
  rw [Finset.sum_filter, Finset.sum_coe_sort B (fun b => if ((b : ℝ) : ℂ) = p then c b else 0)] at hf
  rw [hf]
  exact sum_congr rfl fun s _ => pm_resid dual lam s

theorem pm_filter_pole (dual : Bool) {lam : Fin n → ℝ} (hl : StrictAnti lam) (s : Fin n) :
    univ.filter (fun s' => poleF dual lam s' = poleF dual lam s) = {s} := by
  ext t
  simp [(pm_pole_inj dual hl).eq_iff]

theorem pm_sum_single {B : Finset ℝ} {b : ℝ} (hb : b ∈ B) (c : ℝ → ℂ) :
    (∑ b' ∈ B, if ((b' : ℝ) : ℂ) = ((b : ℝ) : ℂ) then c b' else 0) = c b := by
  simp [Complex.ofReal_inj, hb]

end ReciprocityTheory.ChartRestriction.DS
end
end

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

open MeasureTheory

theorem pole_match (dual : Bool) {lam : Fin n → ℝ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {ε : Fin n → Bool}
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}
    (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) (hsm : ∀ v : D, IsSmoothVecU ε σ v)
    {V : Submodule ℂ D} (hgap : StdGap ε lam) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) (hW : ∀ v ∈ genSub E V, ∀ w ∈ genSub E V, MemLp (fun g : Formalism.REAL.UJ ε =>
      ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) * inner ℂ ((w : D) : H) (σ (Formalism.MainNotions.S.umat g) ((v : D) : H)))
      2 (Formalism.REAL.muG ε)) (hG : HasGelfandChar E lam (genSub E V)) :
    (∀ z : ℂ, ∀ f ∈ tensSub (genSub E V), f ≠ 0 → eeF dual E f = z • f → ∃ s, z = poleF dual lam s) ∧
      ∀ (s : Fin n) (P : Module.End ℂ (Fin n → D)), IsGKEndo dual ε σ E (genSub E V) P →
        (∀ f ∈ tensSub (genSub E V), P (P f) = P f) →
        (∀ f ∈ tensSub (genSub E V), ∀ g ∈ tensSub (genSub E V), formB ε (P f) g = formB ε f (P g)) →
        (∀ f ∈ tensSub (genSub E V), eeF dual E (P f) = poleF dual lam s • P f) →
        (∀ f ∈ tensSub (genSub E V), eeF dual E f = poleF dual lam s • f → P f = f) →
        (∀ f ∈ tensSub (genSub E V), ∀ z' : ℂ, z' ≠ poleF dual lam s → eeF dual E f = z' • f → P f = 0) →
        ∀ x ∈ genSub E V, ptr P x = ((ratioF dual lam s : ℝ) : ℂ) • x := by
  obtain ⟨B, c, P, hev, -, -, hP1, -, hc0, hQ, hfib, -⟩ := pm_core dual hσ hD hsm hgap hV hc hVK hW hG
  refine ⟨fun z f hf hf0 hz => ?_, fun s Q _ _ _ _ hQ1 hQ0 x hx => ?_⟩
  · obtain ⟨b, hb, rfl⟩ := hev z f hf hf0 hz
    have hcne : c b ≠ 0 := fun h0 => hf0 (by rw [← hP1 b f hf hz]; exact hc0 b h0 f hf)
    have h1 := hfib ((b : ℝ) : ℂ)
    rw [pm_sum_single hb] at h1
    by_contra hne
    simp only [not_exists] at hne
    rw [Finset.filter_eq_empty_iff.2 (fun s _ h => hne s h.symm), Finset.sum_empty] at h1
    exact hcne h1
  · rw [hQ Q _ hQ1 hQ0 x hx, hfib, pm_filter_pole dual hgap.1 s, Finset.sum_singleton]

theorem pole_zero (dual : Bool) {lam : Fin n → ℝ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {ε : Fin n → Bool}
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}
    (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) (hsm : ∀ v : D, IsSmoothVecU ε σ v)
    {V : Submodule ℂ D} (hgap : StdGap ε lam) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) (hW : ∀ v ∈ genSub E V, ∀ w ∈ genSub E V, MemLp (fun g : Formalism.REAL.UJ ε =>
      ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) * inner ℂ ((w : D) : H) (σ (Formalism.MainNotions.S.umat g) ((v : D) : H)))
      2 (Formalism.REAL.muG ε)) (hG : HasGelfandChar E lam (genSub E V)) (s : Fin n) :
    ratioF dual lam s = 0 ↔ ∀ f ∈ tensSub (genSub E V), eeF dual E f = poleF dual lam s • f → f = 0 := by
  obtain ⟨B, c, P, hev, hPM, hPz, hP1, hcb, hc0, -, hfib, x₀, hx₀, hx₀0⟩ :=
    pm_core dual hσ hD hsm hgap hV hc hVK hW hG
  have h1 := hfib (poleF dual lam s)
  rw [pm_filter_pole dual hgap.1 s, Finset.sum_singleton] at h1
  constructor
  · intro h0 f hf hz
    by_contra hf0
    obtain ⟨b, hb, hzb⟩ := hev _ f hf hf0 hz
    have hcne : c b ≠ 0 := fun h => hf0 (by rw [← hP1 b f hf (hzb ▸ hz)]; exact hc0 b h f hf)
    rw [hzb, pm_sum_single hb, h0, Complex.ofReal_zero] at h1
    exact hcne h1
  · intro hno
    have hsum : (∑ b ∈ B, if ((b : ℝ) : ℂ) = poleF dual lam s then c b else 0) = 0 := by
      refine sum_eq_zero fun b _ => ?_
      split_ifs with h
      · have hz : ∀ f ∈ tensSub (genSub E V), P b f = 0 := fun f hf =>
          hno _ (hPM b f hf) (by rw [hPz b f hf, h])
        have h2 : c b • x₀ = 0 := by
          rw [← hcb b x₀ hx₀, ptr_apply]
          exact sum_eq_zero fun i _ => congrFun (hz _ (pm_single_mem _ hx₀ i)) i
        exact (smul_eq_zero.1 h2).resolve_right hx₀0
      · rfl
    rw [hsum] at h1
    simpa only [Complex.ofReal_re, Complex.zero_re] using congrArg Complex.re h1.symm

end ReciprocityTheory.ChartRestriction.DS
end
end

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

open MeasureTheory

section SlopeTestRemainingChoices

variable {ε : Fin n → Bool} {lam : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)}
  {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} {v₀ : T.V}

theorem ccA_sqInt (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0) :
    Formalism.MainNotions.S.IsSqIntOn ε (closRep (rreg ε) (closGen (smE ε (rreg ε)) (datumV ε Ψ v₀))) :=
  (isDS_sigLam hgap hP hv₀).2.2.2.2.1

theorem ccA_fdeg_eq (w : Hlam ε Ψ v₀) : Formalism.MainNotions.S.fdegOf (Formalism.REAL.muG ε) (sigLam ε Ψ v₀) w =
    Formalism.MainNotions.S.fdegOf (Formalism.REAL.muG ε) (closRep (rreg ε) (closGen (smE ε (rreg ε)) (datumV ε Ψ v₀))) w := rfl

theorem ccA_fdeg_pos (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0) {w : Hlam ε Ψ v₀} (hw : w ≠ 0) :
    0 < Formalism.MainNotions.S.fdegOf (Formalism.REAL.muG ε) (sigLam ε Ψ v₀) w := by
  obtain ⟨d, hd⟩ := Formalism.MainNotions.BridgeCSchur.fdeg_of_DS lam (sigLam ε Ψ v₀) (isDS_sigLam hgap hP hv₀)
  rw [fdegOf_of_isFdeg' hd hw]
  exact hd.1

end SlopeTestRemainingChoices

theorem ccA_arith {a b r r₂ : ℝ} (ha : 0 < a) (hb : 0 < b) (h1 : a / b ≤ r) (h2 : b / a ≤ r₂)
    (hm : r * r₂ = 1) : a / b = r := by
  have hr : 0 < r := lt_of_lt_of_le (div_pos ha hb) h1
  refine le_antisymm h1 ?_
  rw [div_le_iff₀ ha] at h2
  rw [le_div_iff₀ hb]
  nlinarith

theorem ccA_ratio_mul (dual : Bool) {ε : Fin n → Bool} {lam lam' : Fin n → ℝ} (hgap : StdGap ε lam)
    (hgap' : StdGap ε lam') (s : Fin n) (hlam' : lam' = shiftF dual lam s) :
    ratioF dual lam s * ratioF (!dual) lam' s = 1 := by
  cases dual
  · subst hlam'
    change ratioV lam s * ratioVd (lam + Pi.single s 1) s = 1
    rw [mul_comm]
    exact ratioVd_add_single_mul s hgap.1.injective hgap'.1.injective
  · subst hlam'
    change ratioVd lam s * ratioV (lam - Pi.single s 1) s = 1
    have h := ratioVd_add_single_mul (μ := lam - Pi.single s 1) s hgap'.1.injective
      (by rw [sub_add_cancel]; exact hgap.1.injective)
    rw [sub_add_cancel] at h
    exact h

theorem ccA_shift_back (dual : Bool) {lam lam' : Fin n → ℝ} (s : Fin n) (hlam' : lam' = shiftF dual lam s) :
    lam = shiftF (!dual) lam' s := by
  cases dual <;> subst hlam' <;> delta shiftF <;> simp

theorem ccA_ratio_zero (dual : Bool) {ε : Fin n → Bool} {lam : Fin n → ℝ} (hgap : StdGap ε lam) (s : Fin n)
    (hsing : ¬ Function.Injective (shiftF dual lam s)) : ratioF dual lam s = 0 := by
  cases dual
  · obtain ⟨s', hs', heq⟩ := (not_injective_shift_iff hgap.1.injective s 1
      (ν := shiftF false lam s) (by delta shiftF; simp)
      (fun x hx => by delta shiftF; simp [Pi.single_eq_of_ne hx])).1 hsing
    change ratioV lam s = 0
    delta ratioV
    exact prod_eq_zero hs' (by rw [heq, sub_self, zero_div])
  · obtain ⟨s', hs', heq⟩ := (not_injective_shift_iff hgap.1.injective s (-1)
      (ν := shiftF true lam s) (by delta shiftF; simp [sub_eq_add_neg])
      (fun x hx => by delta shiftF; simp [Pi.single_eq_of_ne hx])).1 hsing
    change ratioVd lam s = 0
    delta ratioVd
    exact prod_eq_zero hs' (by rw [sub_eq_add_neg (lam s), heq, sub_self, zero_div])

theorem cc_gk (dual : Bool) {ε : Fin n → Bool} {lam lam' : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)}
    {T' : S7.KType ε (lowK ε lam')} {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)}
    {Ψ' : Matrix (Fin n) (Fin n) ℂ → (T'.V →L[ℂ] T'.V)} {v₀ : T.V} {v₀' : T'.V}
    (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0)
    (hgap' : StdGap ε lam') (hP' : IsPsiFor ε lam' T' Ψ') (hv₀' : v₀' ≠ 0)
    {h h' : ℝ} (hh : GapAtLeast ε lam h) (hth : thrStar ε < h) (hh' : GapAtLeast ε lam' h') (hth' : thrStar ε < h')
    (hpos : ∀ X, inP ε X → (Ψ (NormedSpace.exp X)).IsPositive)
    (hpos' : ∀ X, inP ε X → (Ψ' (NormedSpace.exp X)).IsPositive)
    (hW : (∀ v ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀), ∀ w ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀),
      MemLp (fun g : Formalism.REAL.UJ ε => ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) *
        inner ℂ ((w : smD ε (rreg ε)) : L2 ε) (rreg ε (Formalism.MainNotions.S.umat g) ((v : smD ε (rreg ε)) : L2 ε))) 2 (Formalism.REAL.muG ε))) (hW' : (∀ v ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ' v₀'), ∀ w ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ' v₀'),
      MemLp (fun g : Formalism.REAL.UJ ε => ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) *
        inner ℂ ((w : smD ε (rreg ε)) : L2 ε) (rreg ε (Formalism.MainNotions.S.umat g) ((v : smD ε (rreg ε)) : L2 ε))) 2 (Formalism.REAL.muG ε)))
    (hG : HasGelfandChar (smE ε (rreg ε)) lam (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)))
    (hG' : HasGelfandChar (smE ε (rreg ε)) lam' (genSub (smE ε (rreg ε)) (datumV ε Ψ' v₀')))
    (s : Fin n) (hlam' : lam' = shiftF dual lam s) {w : Hlam ε Ψ v₀} (hw : w ≠ 0) {w' : Hlam ε Ψ' v₀'} (hw' : w' ≠ 0) :
    (∃ ι : smD ε (rreg ε) →ₗ[ℂ] (Fin n → smD ε (rreg ε)),
      IsGKEmb dual ε (rreg ε) (smE ε (rreg ε)) (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)) (genSub (smE ε (rreg ε)) (datumV ε Ψ' v₀')) ι ∧
      (∀ x ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ' v₀'), eeF dual (smE ε (rreg ε)) (ι x) = poleF dual lam s • ι x) ∧
      ∀ f ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)), eeF dual (smE ε (rreg ε)) f = poleF dual lam s • f →
        ∃ x ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ' v₀'), f = ι x) ∧
    Formalism.MainNotions.S.fdegOf (Formalism.REAL.muG ε) (sigLam ε Ψ' v₀') w' / Formalism.MainNotions.S.fdegOf (Formalism.REAL.muG ε) (sigLam ε Ψ v₀) w =
      ratioF dual lam s := by
  have hσ := rreg_isURepOn ε
  have hD : IsDerivedOn ε (rreg ε) (smD ε (rreg ε)) (smE ε (rreg ε)) := isDerivedOn_smE hσ
  have hsm : ∀ v : smD ε (rreg ε), IsSmoothVecU ε (rreg ε) (v : _) := fun v => (mem_smD_iff ε (rreg ε) _).1 v.2
  have hV := datumV_isKIrrHW hP hv₀
  have hV' := datumV_isKIrrHW hP' hv₀'
  have hc := datumV_casimir hP v₀
  have hc' := datumV_casimir hP' v₀'
  have hVK := datumV_kStable hP v₀
  have hVK' := datumV_kStable hP' v₀'
  have hSq := ccA_sqInt hgap hP hv₀
  have hSq' := ccA_sqInt hgap' hP' hv₀'

  obtain ⟨ι, hι, hιe⟩ := occ_exists dual hgap hP hv₀ hgap' hP' hv₀' hh hth hh' hth' hpos hpos' hW s hlam'
  obtain ⟨P, hPG, hPP, hPz, hP1, hP0⟩ := eigenProj_exists dual hσ hD hgap hV hc hVK hW (poleF dual lam s)
  have hPB := eigenProj_formB dual hσ hD hgap hV hc hVK hW (poleF dual lam s) hPG.1 hPz hP1 hP0
  have hptr := (pole_match dual hσ hD hsm hgap hV hc hVK hW hG).2 s P hPG hPP hPB hPz hP1 hP0
  have hιP : ∀ x ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ' v₀'), P (ι x) = ι x :=
    fun x hx => hP1 _ (hι.1 x hx) (hιe x hx)
  obtain ⟨hle, heq⟩ := trace_ge dual hσ hD hsm hgap hV hc hVK hW hgap' hV' hc' hVK' hSq hSq' hPG hPP hPB hPz hptr hι hιP hw hw'

  have hlam := ccA_shift_back dual s hlam'
  obtain ⟨ι₂, hι₂, hιe₂⟩ := occ_exists (!dual) hgap' hP' hv₀' hgap hP hv₀ hh' hth' hh hth hpos' hpos hW' s hlam
  obtain ⟨P₂, hPG₂, hPP₂, hPz₂, hP1₂, hP0₂⟩ :=
    eigenProj_exists (!dual) hσ hD hgap' hV' hc' hVK' hW' (poleF (!dual) lam' s)
  have hPB₂ := eigenProj_formB (!dual) hσ hD hgap' hV' hc' hVK' hW' (poleF (!dual) lam' s) hPG₂.1 hPz₂ hP1₂ hP0₂
  have hptr₂ := (pole_match (!dual) hσ hD hsm hgap' hV' hc' hVK' hW' hG').2 s P₂ hPG₂ hPP₂ hPB₂ hPz₂ hP1₂ hP0₂
  have hιP₂ : ∀ x ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀), P₂ (ι₂ x) = ι₂ x :=
    fun x hx => hP1₂ _ (hι₂.1 x hx) (hιe₂ x hx)
  obtain ⟨hle₂, -⟩ := trace_ge (!dual) hσ hD hsm hgap' hV' hc' hVK' hW' hgap hV hc hVK hSq' hSq hPG₂ hPP₂ hPB₂ hPz₂ hptr₂
    hι₂ hιP₂ hw' hw
  simp only [Complex.ofReal_re] at hle hle₂ heq
  rw [← ccA_fdeg_eq, ← ccA_fdeg_eq] at hle hle₂ heq
  have hEq := ccA_arith (ccA_fdeg_pos hgap' hP' hv₀' hw') (ccA_fdeg_pos hgap hP hv₀ hw) hle hle₂
    (ccA_ratio_mul dual hgap hgap' s hlam')
  refine ⟨⟨ι, hι, hιe, fun f hf hfe => ?_⟩, hEq⟩
  obtain ⟨x, hx, hPx⟩ := heq hEq.symm f hf
  exact ⟨x, hx, by rw [← hPx, hP1 f hf hfe]⟩

theorem cc_gk_singular (dual : Bool) {lam : Fin n → ℝ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {ε : Fin n → Bool}
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}
    (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) (hsm : ∀ v : D, IsSmoothVecU ε σ v)
    {V : Submodule ℂ D} (hgap : StdGap ε lam) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) (hW : ∀ v ∈ genSub E V, ∀ w ∈ genSub E V, MemLp (fun g : Formalism.REAL.UJ ε =>
      ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) * inner ℂ ((w : D) : H) (σ (Formalism.MainNotions.S.umat g) ((v : D) : H)))
      2 (Formalism.REAL.muG ε)) (hG : HasGelfandChar E lam (genSub E V)) (s : Fin n)
    (hsing : ¬ Function.Injective (shiftF dual lam s)) :
    ∀ f ∈ tensSub (genSub E V), eeF dual E f = poleF dual lam s • f → f = 0 := by
  exact (pole_zero dual hσ hD hsm hgap hV hc hVK hW hG s).1 (ccA_ratio_zero dual hgap s hsing)

end ReciprocityTheory.ChartRestriction.DS
