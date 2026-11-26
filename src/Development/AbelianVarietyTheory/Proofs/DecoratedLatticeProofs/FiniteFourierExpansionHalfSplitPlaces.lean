module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastGroupEmbeddingRealComponentsBlockForm
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DescentDataStepExponents
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergFixesLatticeVacuumPeriodLattice

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExpTraceEqBrk
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TraceBrk

theorem exp_trace_eq_brk : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ M Y : Matrix (Fin T.rank) (Fin S.rank) D.host.E, Complex.exp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ D.host.E (D.host.xi0 * GlobalTheory.LatVac.hRat S T M Y) : ℚ) : ℂ)) = brk (HV sc) (embH (tauE D) δ (Matrix.toLin' Y)) (embH (tauE D) δ (Matrix.toLin' M)) := by
  intro D ψ θ S T δ sc h M Y
  have hz : ∀ (γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) τ i j,
      embH (tauE D) δ (Matrix.toLin' γ) τ i j = δ * tauE D τ (γ i j) := by
    intro γ τ i j
    simp [embH, Matrix.toLin'_apply, Matrix.mulVec_single_one]
  have hδ : δ * starRingEnd ℂ δ = ((‖δ‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hHV : HV sc (embH (tauE D) δ (Matrix.toLin' M)) (embH (tauE D) δ (Matrix.toLin' Y)) =
      ((sc * ‖δ‖ ^ 2 : ℝ) : ℂ) * ∑ τ, tauE D τ (GlobalTheory.LatVac.hRat S T M Y) := by
    rw [GlobalTheory.LatSign.hRat_one S T h.gS h.gT]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [HV, LinearMap.mk₂'ₛₗ_apply, hz, map_sum, map_mul, GlobalTheory.LatSign.tauE_star']
    rw [Complex.ofReal_mul, ← hδ, mul_assoc]
    congr 1
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => ?_
    ring
  rw [brk, Formalism.L2.Th1.H.altE, hHV, h.scale, ← GlobalTheory.LatSign.sum_two_re_eq_trace, Complex.im_ofReal_mul,
    Complex.im_sum, ← Complex.ofReal_sum]
  have hs : ∑ τ, 2 * (tauE D τ (D.host.xi0 * GlobalTheory.LatVac.hRat S T M Y)).re =
      -(2 * (Real.sqrt D.host.d)⁻¹ * ∑ τ, (tauE D τ (GlobalTheory.LatVac.hRat S T M Y)).im) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [map_mul, h.xi, mul_assoc, Complex.I_mul_re, Complex.im_ofReal_mul]
    ring
  rw [hs, Complex.ofReal_neg]
  congr 1
  ring

end GlobalTheory.TraceBrk
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BrkSumRepsOrth
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem brk_sum_reps_orth : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (H : Formalism.L2.Th1.H.Sesq V) (α : V → ℂ) (A B Λ : AddSubgroup V), SplitHyp H α A B Λ → ∀ SB : Finset V, Formalism.L2.Th1.H.IsReps Λ B SB → ∀ w ∈ Λ ⊓ A, ∑ y ∈ SB, brk H y w = if w ∈ B then (SB.card : ℂ) else 0 := by
  intro V _ _ H α A B Λ hyp SB hSB w hw
  obtain ⟨hH, -, hB, -, sdB, hΛ, -, -, -, -⟩ := hyp
  have hBint := (Formalism.L2.Th1.H.semicharacterBasic V H hH B α hB).2.2
  have hΛint := (Formalism.L2.Th1.H.semicharacterBasic V H hH Λ α hΛ).2.2
  have hwΛ : w ∈ Λ := (AddSubgroup.mem_inf.1 hw).1
  by_cases hwB : w ∈ B
  · rw [if_pos hwB, Finset.sum_congr rfl fun y hy => brk_one_of_int H (hBint hwB y (hSB.1 y hy))]
    simp
  · rw [if_neg hwB]
    have hnd : w ∉ Formalism.L2.Th1.H.dualLat H B := by rw [sdB]; exact hwB
    have hex : ∃ y₀ ∈ B, ¬ ∃ m : ℤ, Formalism.L2.Th1.H.altE H w y₀ = (m : ℝ) := by
      by_contra hcon
      push_neg at hcon
      exact hnd (fun y hy => hcon y hy)
    obtain ⟨y₀, hy₀B, hy₀⟩ := hex
    exact char_sum_zero hSB (fun y => brk H y w) (fun u v => brk_add_left H u v w)
      (fun m _ hmΛ => brk_one_of_int H (hΛint hwΛ m hmΛ)) (x₀ := y₀) hy₀B
      (fun h => hy₀ (int_of_brk_one H h))

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NoConjOfIdemSum
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CocRZeroLeft
open NumberField IsDedekindDomain Formalism.L2.Ker

noncomputable section

namespace GlobalTheory.SemiTwist

variable {E : Type} [Field E] [NumberField E] [StarRing E] {ι : Type} [Fintype ι] {a b : ℕ}
  (emb : ι → E →+* ℂ) (δ : ℂ) (d : ℕ) (sc : ℝ)

def cocR (x y : Formalism.L2.Col.HomE E a b) : ℝ :=
  (Real.sqrt d * (HV (ι := ι) sc (embH emb δ x) (embH emb δ y)).re +
    Formalism.L2.Th1.H.altE (HV sc) (embH emb δ x) (embH emb δ y)) / 2

theorem cocR_add_left (x y z : Formalism.L2.Col.HomE E a b) :
    cocR emb δ d sc (x + y) z = cocR (ι := ι) emb δ d sc x z + cocR emb δ d sc y z := by
  simp only [cocR, Formalism.L2.Th1.H.altE, map_add (f := _), LinearMap.add_apply, Complex.add_re, Complex.add_im]; ring

theorem cocR_zero_left (z : Formalism.L2.Col.HomE E a b) : cocR (ι := ι) emb δ d sc 0 z = 0 := by
  simp [cocR, Formalism.L2.Th1.H.altE]

theorem hv_embH_smul (hconj : ∀ τ x, emb τ (star x) = starRingEnd ℂ (emb τ x)) (r : E) (x y : Formalism.L2.Col.HomE E a b) :
    HV (ι := ι) sc (embH emb δ (r • x)) (embH emb δ y) = HV sc (embH emb δ x) (embH emb δ (star r • y)) := by
  simp only [HV, LinearMap.mk₂'ₛₗ_apply, embH, AddMonoidHom.coe_mk, ZeroHom.coe_mk, LinearMap.smul_apply, Pi.smul_apply,
    smul_eq_mul, map_mul, hconj, Complex.conj_conj]
  congr 1
  refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem cocR_smul (hconj : ∀ τ x, emb τ (star x) = starRingEnd ℂ (emb τ x)) (r : E) (x y : Formalism.L2.Col.HomE E a b) :
    cocR (ι := ι) emb δ d sc (r • x) y = cocR emb δ d sc x (star r • y) := by
  simp only [cocR, Formalism.L2.Th1.H.altE, hv_embH_smul emb δ sc hconj]

theorem semiChar_twO : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (ι : Type) [Fintype ι] [Nonempty ι] (a b : ℕ) (emb : ι → E →+* ℂ) (δ : ℂ) (d : ℕ) (sc : ℝ) (M : Submodule (𝓞 E) (Formalism.L2.Col.HomE E a b)) (c : ℕ) (e : HeightOneSpectrum (𝓞 E) → ℤ), δ ≠ 0 → (∀ (τ : ι) (x : E), emb τ (star x) = starRingEnd ℂ (emb τ x)) → 0 < c → (∀ Q, e (Formalism.L2.Col.conjPrime₂ Q) = -e Q) → (∀ Q, e Q = 1 ∨ e Q = 0 ∨ e Q = -1) → Formalism.L2.Th1.H.IsSelfDual (HV sc) (laV emb δ M) → Formalism.L2.Th1.H.IsSemiChar (HV sc) (laV emb δ M) (alV d sc) → Formalism.L2.Th1.H.IsSemiChar (HV sc) (laV emb δ (twist₂ M c e)) (alV d sc) := by
  intro E _ _ _ ι _ _ a b emb δ d sc M c e _ hconj hc he _ _ hM
  have hH : Formalism.L2.Th1.H.IsHerm (HV (ι := ι) (a := a) (b := b) sc) := fun x y => by
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Formalism.L2.Ker.HV, map_sum, mul_comm]
  have h0 : ∀ x ∈ M, ∀ y ∈ M, ∃ n : ℤ, cocR emb δ d sc x y = n := fun x hx y hy =>
    (GlobalTheory.KerLaw.semi_iff hH (Real.sqrt d) _).1 hM (embH emb δ x) ⟨x, hx, rfl⟩ (embH emb δ y) ⟨y, hy, rfl⟩
  refine (GlobalTheory.KerLaw.semi_iff hH (Real.sqrt d) _).2 ?_
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  change ∃ n : ℤ, cocR emb δ d sc x y = n
  let I : Ideal (𝓞 E) :=
    { carrier := {r | ∀ s : 𝓞 E, ∃ n : ℤ, cocR emb δ d sc ((s * r) • x) y = n}
      zero_mem' := fun s => ⟨0, by simp [cocR_zero_left]⟩
      add_mem' := fun {r r'} hr hr' s => by
        obtain ⟨n, hn⟩ := hr s
        obtain ⟨m, hm⟩ := hr' s
        exact ⟨n + m, by rw [mul_add, add_smul, cocR_add_left, hn, hm, Int.cast_add]⟩
      smul_mem' := fun t r hr s => by
        rw [smul_eq_mul, ← mul_assoc]
        exact hr _ }
  have hI : I = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    let Q : HeightOneSpectrum (𝓞 E) :=
      ⟨m, hm.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hm (RingOfIntegers.not_isField E)⟩
    obtain ⟨u, hu, hx⟩ := (Formalism.L2.Col.mem_locP _ _ _).1 ((GlobalTheory.KerLaw.mem_tw _ _ _ _).1 hx Q)
    obtain ⟨v, hv, hy⟩ := (Formalism.L2.Col.mem_locP _ _ _).1 ((GlobalTheory.KerLaw.mem_tw _ _ _ _).1 hy (Formalism.L2.Col.conjPrime₂ Q))
    rw [he, zpow_neg, inv_inv] at hy
    have hmem : u * Formalism.L2.Col.cO E v ∈ I := by
      intro s
      obtain ⟨n, hn⟩ := h0 _ (Submodule.smul_mem _ s hx) _ hy
      refine ⟨n, ?_⟩
      rw [← hn]
      have e1 : (s * (u * Formalism.L2.Col.cO E v)) • x =
          (star (algebraMap (𝓞 E) E v) * (c : E) ^ e Q) • (s • u • ((c : E) ^ e Q)⁻¹ • x) := by
        rw [← algebraMap_smul E s, ← algebraMap_smul E u, ← algebraMap_smul E (s * _), smul_smul, smul_smul, smul_smul,
          map_mul, map_mul, Formalism.L2.Col.algebraMap_cO]
        congr 1
        have hk : (c : E) ^ e Q ≠ 0 := zpow_ne_zero _ (Nat.cast_ne_zero.2 hc.ne')
        field_simp
      rw [e1, cocR_smul emb δ d sc hconj, star_mul', star_star, star_zpow₀, star_natCast, mul_smul, algebraMap_smul]
    rcases hm.isPrime.mem_or_mem (hle hmem) with h' | h'
    · exact hu h'
    · exact hv h'
  have : (1 : 𝓞 E) ∈ I := hI ▸ Submodule.mem_top
  simpa using this 1

end GlobalTheory.SemiTwist
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AltENsmulLeft
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HermitianCocycleIntegralOfLocal
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HermitianCocycleIntegralOfLocal
open NumberField IsDedekindDomain Formalism.L2.Ker

open Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.L2.Th1.H

noncomputable section

namespace GlobalTheory.CocIntLoc

variable {E : Type} [Field E] [NumberField E] [StarRing E] {ι : Type} [Fintype ι] {a b : ℕ}

theorem hv_apply (sc : ℝ) (z w : VV ι a b) :
    HV sc z w = (sc : ℂ) * ∑ τ, ∑ i, ∑ j, z τ i j * (starRingEnd ℂ) (w τ i j) := rfl

theorem hv_swap (sc : ℝ) (z w : VV ι a b) :
    HV sc w z = (starRingEnd ℂ) (HV sc z w) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hv_apply, map_mul, map_sum, Complex.conj_ofReal, Complex.conj_conj]
  congr 1
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => mul_comm _ _

theorem embH_apply (emb : ι → E →+* ℂ) (δ : ℂ) (x : HomE E a b) (τ : ι) (i : Fin b) (j : Fin a) :
    embH emb δ x τ i j = δ * emb τ (x (Pi.single j 1) i) := rfl

theorem hv_smul (emb : ι → E →+* ℂ) (δ : ℂ) (sc : ℝ) (hs : ∀ (τ : ι) (x : E), emb τ (star x) = starRingEnd ℂ (emb τ x))
    (r : E) (x y : HomE E a b) :
    HV sc (embH emb δ (r • x)) (embH emb δ y) = HV sc (embH emb δ x) (embH emb δ (star r • y)) := by
  rw [hv_apply, hv_apply]
  congr 1
  refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [embH_apply, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, map_mul, hs, Complex.conj_conj]
  ring

theorem int_of_local (M : Submodule (𝓞 E) (HomE E a b)) (f : HomE E a b → HomE E a b → ℝ)
    (hadd : ∀ x x' y, f (x + x') y = f x y + f x' y) (hsm : ∀ (r : E) x y, f (r • x) y = f x (star r • y))
    (hM : ∀ x ∈ M, ∀ y ∈ M, ∃ n : ℤ, f x y = n) (x y : HomE E a b)
    (h : ∀ Q : HeightOneSpectrum (𝓞 E), ∃ k : E, k ≠ 0 ∧ k⁻¹ • x ∈ localization₂ Q.asIdeal M ∧
      star k • y ∈ localization₂ (conjPrime₂ Q).asIdeal M) : ∃ n : ℤ, f x y = n := by
  have hzero : ∀ z, f 0 z = 0 := fun z => by
    have := hadd 0 0 z
    rw [add_zero] at this
    linarith
  let I : Ideal (𝓞 E) :=
    { carrier := {r | ∀ s : 𝓞 E, ∃ n : ℤ, f ((s * r) • x) y = n}
      zero_mem' := fun s => ⟨0, by simp [hzero]⟩
      add_mem' := fun {r r'} hr hr' s => by
        obtain ⟨n, hn⟩ := hr s
        obtain ⟨m, hm⟩ := hr' s
        exact ⟨n + m, by rw [mul_add, add_smul, hadd, hn, hm, Int.cast_add]⟩
      smul_mem' := fun c r hr s => by
        show ∃ n : ℤ, f ((s * (c * r)) • x) y = n
        rw [← mul_assoc]
        exact hr _ }
  have hI : I = ⊤ := by
    by_contra hne
    obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hne
    let Q : HeightOneSpectrum (𝓞 E) :=
      ⟨P, hP.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField E)⟩
    obtain ⟨k, hk, hx, hy⟩ := h Q
    obtain ⟨u, hu, hx⟩ := hx
    obtain ⟨v, hv, hy⟩ := hy
    have hmem : u * cO E v ∈ I := by
      intro s
      obtain ⟨n, hn⟩ := hM _ (Submodule.smul_mem _ s hx) _ hy
      refine ⟨n, ?_⟩
      rw [← hn]
      have e1 : (s * (u * cO E v)) • x = (star (algebraMap (𝓞 E) E v) * k) • (s • u • k⁻¹ • x) := by
        rw [← algebraMap_smul E s, ← algebraMap_smul E u, ← algebraMap_smul E (s * _), smul_smul, smul_smul, smul_smul,
          map_mul, map_mul, algebraMap_cO]
        congr 1
        field_simp
      rw [e1, hsm, star_mul', star_star, mul_smul, algebraMap_smul]
    rcases hP.isPrime.mem_or_mem (hle hmem) with h' | h'
    · exact hu h'
    · exact hv ((mem_conjP Q v).2 h')
  have : (1 : 𝓞 E) ∈ I := hI ▸ Submodule.mem_top
  simpa using this 1

theorem integral_of_local : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (ι : Type) [Fintype ι] [Nonempty ι] (a b : ℕ) (emb : ι → E →+* ℂ) (δ : ℂ) (d : ℕ) (sc : ℝ) (M : Submodule (𝓞 E) (Formalism.L2.Col.HomE E a b)), δ ≠ 0 → (∀ (τ : ι) (x : E), emb τ (star x) = starRingEnd ℂ (emb τ x)) → Formalism.L2.Th1.H.IsSelfDual (HV sc) (laV emb δ M) → Formalism.L2.Th1.H.IsSemiChar (HV sc) (laV emb δ M) (alV d sc) → ∀ x y : Formalism.L2.Col.HomE E a b, (∀ Q : HeightOneSpectrum (𝓞 E), ∃ k : E, k ≠ 0 ∧ k⁻¹ • x ∈ Formalism.HermitianLatticesTheory.localization₂ Q.asIdeal M ∧ star k • y ∈ Formalism.HermitianLatticesTheory.localization₂ (Formalism.L2.Col.conjPrime₂ Q).asIdeal M) → (∃ n : ℤ, Formalism.L2.Th1.H.altE (HV sc) (embH emb δ x) (embH emb δ y) = n) ∧ ∃ n : ℤ, (Real.sqrt d * (HV sc (embH emb δ x) (embH emb δ y)).re + Formalism.L2.Th1.H.altE (HV sc) (embH emb δ x) (embH emb δ y)) / 2 = n := by
  intro E _ _ _ ι _ _ a b emb δ d sc M _ hs hsd hsc x y h
  have hmemL : ∀ {z : HomE E a b}, z ∈ M → embH emb δ z ∈ laV emb δ M := fun {z} hz => ⟨z, hz, rfl⟩
  have hsmA : ∀ (r : E) (x y : HomE E a b), altE (HV sc) (embH emb δ (r • x)) (embH emb δ y) =
      altE (HV sc) (embH emb δ x) (embH emb δ (star r • y)) := by
    intro r x y; simp only [altE, hv_smul emb δ sc hs]
  have hintA : ∀ x ∈ M, ∀ y ∈ M, ∃ n : ℤ, altE (HV sc) (embH emb δ x) (embH emb δ y) = n := by
    intro x hx y hy
    have h1 := hmemL hx
    rw [← hsd] at h1
    exact h1 _ (hmemL hy)
  refine ⟨int_of_local M (fun x y => altE (HV sc) (embH emb δ x) (embH emb δ y)) ?_ hsmA hintA x y h,
    int_of_local M (fun x y => (Real.sqrt d * (HV sc (embH emb δ x) (embH emb δ y)).re +
      altE (HV sc) (embH emb δ x) (embH emb δ y)) / 2) ?_ ?_ ?_ x y h⟩
  · intro x x' y
    simp only [altE, map_add (f := _), LinearMap.add_apply, Complex.add_im]
  · intro x x' y
    simp only [altE, map_add (f := _), LinearMap.add_apply, Complex.add_im, Complex.add_re]
    ring
  · intro r x y
    simp only [altE, hv_smul emb δ sc hs]
  · intro x hx y hy
    obtain ⟨m, hm⟩ := hintA x hx y hy
    have h := hsc.2 _ (hmemL hx) _ (hmemL hy)
    simp only [alV, alphaQ, Formalism.L2.Th1.H.qOf] at h
    rw [← Complex.exp_add, ← Complex.exp_add, Complex.exp_eq_exp_iff_exists_int] at h
    obtain ⟨n, hn⟩ := h
    refine ⟨n + m, ?_⟩
    have h2 := congrArg Complex.im hn
    have h3 : (HV sc (embH emb δ y) (embH emb δ x)).re = (HV sc (embH emb δ x) (embH emb δ y)).re := by
      rw [hv_swap]; simp
    simp only [altE] at hm
    simp only [map_add (f := _), LinearMap.add_apply, Complex.add_re, h3, altE, hm] at h2
    simp at h2
    simp only [altE, hm]
    push_cast
    apply mul_left_cancel₀ Real.pi_ne_zero
    linarith

end GlobalTheory.CocIntLoc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HermitianCocycleIntegralOfLocalStatement
open NumberField IsDedekindDomain Formalism.L2.Ker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_cocycle_integral_of_local : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (ι : Type) [Fintype ι] [Nonempty ι] (a b : ℕ) (emb : ι → E →+* ℂ) (δ : ℂ) (d : ℕ) (sc : ℝ) (M : Submodule (𝓞 E) (Formalism.L2.Col.HomE E a b)), δ ≠ 0 → (∀ (τ : ι) (x : E), emb τ (star x) = starRingEnd ℂ (emb τ x)) → Formalism.L2.Th1.H.IsSelfDual (HV sc) (laV emb δ M) → Formalism.L2.Th1.H.IsSemiChar (HV sc) (laV emb δ M) (alV d sc) → ∀ x y : Formalism.L2.Col.HomE E a b, (∀ Q : HeightOneSpectrum (𝓞 E), ∃ k : E, k ≠ 0 ∧ k⁻¹ • x ∈ Formalism.HermitianLatticesTheory.localization₂ Q.asIdeal M ∧ star k • y ∈ Formalism.HermitianLatticesTheory.localization₂ (Formalism.L2.Col.conjPrime₂ Q).asIdeal M) → (∃ n : ℤ, Formalism.L2.Th1.H.altE (HV sc) (embH emb δ x) (embH emb δ y) = n) ∧ ∃ n : ℤ, (Real.sqrt d * (HV sc (embH emb δ x) (embH emb δ y)).re + Formalism.L2.Th1.H.altE (HV sc) (embH emb δ x) (embH emb δ y)) / 2 = n := by
  first | exact @GlobalTheory.CocIntLoc.integral_of_local | exact GlobalTheory.CocIntLoc.integral_of_local | (intros; apply GlobalTheory.CocIntLoc.integral_of_local <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNotMemDvdLocallyAway
open NumberField IsDedekindDomain Formalism.L2.Ker

namespace GlobalTheory

theorem exists_not_mem_dvd_locally_away (E : Type) [Field E] [NumberField E]
    (Q : HeightOneSpectrum (𝓞 E)) (r : 𝓞 E) (hr : r ≠ 0) :
    ∃ t : 𝓞 E, t ∉ Q.asIdeal ∧ ∀ Q' : HeightOneSpectrum (𝓞 E), Q' ≠ Q →
      ∃ w : 𝓞 E, w ∉ Q'.asIdeal ∧ ∃ z : 𝓞 E, w * t = r * z := by
  have hI : Ideal.span {r} ≠ ⊥ := by
    rwa [Ne, Ideal.span_singleton_eq_bot]
  have hnu : ¬ IsUnit Q.asIdeal := fun h => Q.isPrime.ne_top (Ideal.isUnit_iff.1 h)
  obtain ⟨J, hJ, hnd⟩ := (FiniteMultiplicity.of_not_isUnit hnu hI).exists_eq_pow_mul_and_not_dvd
  set m := multiplicity Q.asIdeal (Ideal.span {r})
  have hJle : ¬ J ≤ Q.asIdeal := fun h => hnd (Ideal.dvd_iff_le.2 h)
  obtain ⟨t, htJ, htQ⟩ := Set.not_subset.1 hJle
  refine ⟨t, htQ, fun Q' hQ' => ?_⟩
  have hnle : ¬ Q.asIdeal ^ m ≤ Q'.asIdeal := by
    intro h
    have h1 : Q.asIdeal ≤ Q'.asIdeal := Q'.isPrime.le_of_pow_le h
    have h2 : Q.asIdeal = Q'.asIdeal := Q.isMaximal.eq_of_le Q'.isPrime.ne_top h1
    exact hQ' (HeightOneSpectrum.ext h2.symm)
  obtain ⟨w, hwm, hwQ'⟩ := Set.not_subset.1 hnle
  refine ⟨w, hwQ', ?_⟩
  have hmem : w * t ∈ Ideal.span {r} := by
    rw [hJ]; exact Ideal.mul_mem_mul hwm htJ
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 hmem
  exact ⟨z, by rw [← hz, mul_comm]⟩

end GlobalTheory
end

open NumberField IsDedekindDomain Formalism.L2.Ker

noncomputable section

namespace GlobalTheory.TwPerSelfDual

open _root_.Formalism.L2.Col Formalism.HermitianLatticesTheory _root_.Formalism.L2.Th1.H

variable {E : Type} [Field E] [NumberField E] [StarRing E] {ι : Type} [Fintype ι] {a b : ℕ}

theorem hv_apply' (sc : ℝ) (z w : VV ι a b) :
    HV sc z w = (sc : ℂ) * ∑ τ, ∑ i, ∑ j, z τ i j * (starRingEnd ℂ) (w τ i j) := rfl

theorem embH_apply' (emb : ι → E →+* ℂ) (δ : ℂ) (x : HomE E a b) (τ : ι) (i : Fin b) (j : Fin a) :
    embH emb δ x τ i j = δ * emb τ (x (Pi.single j 1) i) := rfl

theorem hv_smul_emb (emb : ι → E →+* ℂ) (δ : ℂ) (sc : ℝ)
    (hst : ∀ (τ : ι) (x : E), emb τ (star x) = starRingEnd ℂ (emb τ x)) (r : E) (x y : HomE E a b) :
    HV sc (embH emb δ (r • x)) (embH emb δ y) = HV sc (embH emb δ x) (embH emb δ (star r • y)) := by
  rw [hv_apply', hv_apply']
  congr 1
  refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [embH_apply', LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, map_mul, hst, Complex.conj_conj]
  ring

theorem embH_injective' [Nonempty ι] (emb : ι → E →+* ℂ) {δ : ℂ} (hδ : δ ≠ 0) :
    Function.Injective (embH emb δ : HomE E a b → VV ι a b) := by
  intro x y h
  obtain ⟨τ⟩ := ‹Nonempty ι›
  refine LinearMap.pi_ext' fun j => LinearMap.ext_ring ?_
  funext i
  have := congrFun (congrFun (congrFun h τ) i) j
  rw [embH_apply', embH_apply'] at this
  simpa using (emb τ).injective (mul_left_cancel₀ hδ this)

theorem altE_nsmul_left {V : Type} [AddCommGroup V] [Module ℂ V] (H : Sesq V) (n : ℕ) (v w : V) :
    altE H (n • v) w = altE H v (n • w) := by
  simp only [altE, map_nsmul, LinearMap.smul_apply]

section Mod

variable {W : Type} [AddCommGroup W] [Module E W] [Module (𝓞 E) W] [IsScalarTower (𝓞 E) E W]

theorem npow_smul_mem (L : Submodule (𝓞 E) W) (c n : ℕ) {y : W} (hy : y ∈ L) : ((c : E) ^ n) • y ∈ L := by
  induction n with
  | zero => simpa using hy
  | succ n ih => rw [pow_succ', mul_smul]; exact nat_smul_mem L c ih

theorem zpow_smul_mem (L : Submodule (𝓞 E) W) (c : ℕ) {k : ℤ} (hk : 0 ≤ k) {y : W} (hy : y ∈ L) :
    ((c : E) ^ k) • y ∈ L := by
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hk
  rw [zpow_natCast]; exact npow_smul_mem L c n hy

end Mod

theorem twO_selfDual : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (ι : Type) [Fintype ι] [Nonempty ι] (a b : ℕ) (emb : ι → E →+* ℂ) (δ : ℂ) (d : ℕ) (sc : ℝ) (M : Submodule (𝓞 E) (Formalism.L2.Col.HomE E a b)) (c : ℕ) (e : HeightOneSpectrum (𝓞 E) → ℤ), δ ≠ 0 → (∀ (τ : ι) (x : E), emb τ (star x) = starRingEnd ℂ (emb τ x)) → 0 < c → (∀ Q, e (Formalism.L2.Col.conjPrime₂ Q) = -e Q) → (∀ Q, e Q = 1 ∨ e Q = 0 ∨ e Q = -1) → Formalism.L2.Th1.H.IsSelfDual (HV sc) (laV emb δ M) → Formalism.L2.Th1.H.IsSemiChar (HV sc) (laV emb δ M) (alV d sc) → Formalism.L2.Th1.H.IsSelfDual (HV sc) (laV emb δ (twist₂ M c e)) := by
  intro E _ _ _ ι _ _ a b emb δ d sc M c e hδ hst hc he her hSD hSC
  have hcE : (c : E) ≠ 0 := by exact_mod_cast hc.ne'
  have hstk : ∀ k : ℤ, star ((c : E) ^ k) = (c : E) ^ k := fun k => by rw [star_zpow₀, star_natCast]
  have hSD' : dualLat (HV sc) (laV emb δ M) = laV emb δ M := hSD
  have hdualM : ∀ z : HomE E a b, (∀ y ∈ M, ∃ m : ℤ, altE (HV sc) (embH emb δ z) (embH emb δ y) = m) → z ∈ M := by
    intro z hz
    have h1 : embH emb δ z ∈ dualLat (HV sc) (laV emb δ M) := by
      rintro _ ⟨y, hy, rfl⟩
      exact hz y hy
    rw [hSD'] at h1
    obtain ⟨z', hz', e'⟩ := h1
    rwa [← embH_injective' emb hδ e']
  have hcM : ∀ y ∈ M, (c : E) • y ∈ twist₂ M c e := by
    intro y hy
    rw [mem_twO]
    intro Q
    apply le_locP'
    rw [smul_smul, ← zpow_neg, ← zpow_add_one₀ hcE]
    apply zpow_smul_mem M c _ hy
    rcases her Q with h | h | h <;> rw [h] <;> norm_num
  show dualLat (HV sc) (laV emb δ (twist₂ M c e)) = laV emb δ (twist₂ M c e)
  apply le_antisymm
  · intro v hv
    have hcv : c • v ∈ dualLat (HV sc) (laV emb δ M) := by
      rintro _ ⟨y, hy, rfl⟩
      rw [altE_nsmul_left, ← map_nsmul]
      apply hv
      refine ⟨c • y, ?_, rfl⟩
      show c • y ∈ twist₂ M c e
      rw [← Nat.cast_smul_eq_nsmul E]
      exact hcM y hy
    rw [hSD'] at hcv
    obtain ⟨m, hm, hmv⟩ := hcv
    set x : HomE E a b := ((c : E)⁻¹) • m with hxdef
    have hxm : (c : E) • x = m := by rw [hxdef, smul_smul, mul_inv_cancel₀ hcE, one_smul]
    have hxv : embH emb δ x = v := by
      have h1 : c • embH emb δ x = c • v := by
        rw [← map_nsmul, ← Nat.cast_smul_eq_nsmul E, hxm]; exact hmv
      have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
      rw [← Nat.cast_smul_eq_nsmul ℂ, ← Nat.cast_smul_eq_nsmul ℂ] at h1
      exact smul_right_injective _ hcC h1
    refine ⟨x, ?_, hxv⟩
    show x ∈ twist₂ M c e
    rw [mem_twO]
    intro Q
    have hc2 : ((c : 𝓞 E) ^ 2) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hc.ne')
    obtain ⟨t, ht, hwt⟩ := GlobalTheory.exists_not_mem_dvd_locally_away E (conjPrime₂ Q) _ hc2
    have hT : ∀ y ∈ M, (algebraMap (𝓞 E) E t * ((c : E) ^ e Q)⁻¹) • y ∈ twist₂ M c e := by
      intro y hy
      rw [mem_twO]
      intro Q'
      rw [smul_smul]
      by_cases hQ' : Q' = conjPrime₂ Q
      · subst hQ'
        rw [he Q, zpow_neg, inv_inv]
        have h1 : (c : E) ^ e Q * (algebraMap (𝓞 E) E t * ((c : E) ^ e Q)⁻¹) = algebraMap (𝓞 E) E t := by
          have : (c : E) ^ e Q ≠ 0 := zpow_ne_zero _ hcE
          field_simp
        rw [h1, IsScalarTower.algebraMap_smul]
        exact le_locP' M _ (M.smul_mem t hy)
      · obtain ⟨w, hw, z, hz⟩ := hwt Q' hQ'
        have hz' : algebraMap (𝓞 E) E w * algebraMap (𝓞 E) E t = (c : E) ^ 2 * algebraMap (𝓞 E) E z := by
          have := congrArg (algebraMap (𝓞 E) E) hz
          simpa using this
        have hn : (((2 - e Q' - e Q).toNat : ℕ) : ℤ) = 2 - e Q' - e Q :=
          Int.toNat_of_nonneg (by rcases her Q with h | h | h <;> rcases her Q' with h' | h' | h' <;> omega)
        refine loc_of_scal M Q' hw (ρ := (c : 𝓞 E) ^ (2 - e Q' - e Q).toNat * z) ?_ hy
        rw [map_mul, map_pow, map_natCast, ← zpow_natCast, hn, zpow_sub₀ hcE, zpow_sub₀ hcE, zpow_ofNat]
        linear_combination (((c : E) ^ e Q')⁻¹ * ((c : E) ^ e Q)⁻¹) * hz'
    refine ⟨cO E t, fun h => ht ((mem_conjP Q t).2 h), ?_⟩
    rw [← IsScalarTower.algebraMap_smul E (cO E t), smul_smul]
    apply hdualM
    intro y hy
    unfold altE
    rw [hv_smul_emb emb δ sc hst, star_mul', algebraMap_cO, star_star, star_inv₀, hstk, hxv]
    exact hv _ ⟨_, hT y hy, rfl⟩
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    refine (GlobalTheory.T.hermitian_cocycle_integral_of_local E ι a b emb δ d sc M hδ hst hSD hSC x y fun Q =>
      ⟨(c : E) ^ e Q, zpow_ne_zero _ hcE, (mem_twO _ _ _ _).1 hx Q, ?_⟩).1
    rw [hstk]
    have := (mem_twO _ _ _ _).1 hy (conjPrime₂ Q)
    rwa [he Q, zpow_neg, inv_inv] at this

end GlobalTheory.TwPerSelfDual
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HalfSplit

theorem noConj_of_idemSum : ∀ (D : D7) (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → ∀ P ∈ SS, Formalism.L2.Col.conjPrime₂ P ∉ SS := by
  intro D e SS hI P hP hP'
  obtain ⟨⟨es, hes, he⟩, hc⟩ := hI
  have h1 : ∀ i ∈ SS, es i * es i = es i := fun i hi => (hes i hi).1.1
  have hcross : ∀ i ∈ SS, ∀ j ∈ SS, es i * cA D (es j) = 0 := by
    subst he
    exact GlobalTheory.PlaceDatum.cross_eq_zero (R := AE D) GlobalTheory.PlaceDatum.isUnit_natCast (cA D) es SS h1 hc
  have hcj : Lev.IsConjPl (D := D) (Formalism.L2.Col.conjPrime₂ P) P := by
    intro c hc'
    exact ⟨Formalism.L2.Col.cO D.host.E c, (Formalism.L2.Col.mem_conjP P c).1 hc', rfl⟩
  have heq : es P = cA D (es (Formalism.L2.Col.conjPrime₂ P)) :=
    Formalism.IndefR.Fin.conj_idem_eq (hes _ hP') (hes P hP) hcj
  apply Formalism.IndefR.Fin.idemAt_ne_zero (hes P hP)
  have := hcross P hP _ hP'
  rw [← heq, h1 P hP] at this
  exact this

theorem splitHyp_halves : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → ∀ (N : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (c : ℕ), 0 < c → Odd c → (∀ Q ∈ SS, ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal) → LaFacts (tauE D) δ D.host.d sc (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N' → IsSelfDualC S N → IsSelfDualC T N' → SplitHyp (HV sc) (alV D.host.d sc) (AC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) SS N N' c) (BC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) SS N N' c) (LamC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') := by
  intro D ψ θ S T δ sc hP e SS hI N N' c hc hcS h2 hL hN hN'
  have hSS : ∀ P ∈ SS, Formalism.L2.Col.conjPrime₂ P ∉ SS := noConj_of_idemSum D e SS hI
  have hT : Nonempty D.what₂.Tau := ⟨D.eTau.symm (Classical.arbitrary _)⟩
  have hconj : ∀ τ (x : D.host.E), tauE D τ (star x) = starRingEnd ℂ (tauE D τ x) := fun τ x =>
    GlobalTheory.FockCompare.tauE_star τ x
  have he1 : ∀ Q, expS SS Q = 1 ∨ expS SS Q = 0 ∨ expS SS Q = -1 := by
    intro Q; unfold expS; split_ifs <;> simp
  have hc1 : ∀ Q, expS SS (Formalism.L2.Col.conjPrime₂ Q) = -expS SS Q := exponent_set_conjugate D.host.E SS hSS
  have hfg : N.FG := hN.1.fg
  have tw : ∀ f : HeightOneSpectrum (𝓞 D.host.E) → ℤ, (∀ Q, f (Formalism.L2.Col.conjPrime₂ Q) = -f Q) →
      (∀ Q, f Q = 1 ∨ f Q = 0 ∨ f Q = -1) →
      LaFacts (tauE D) δ D.host.d sc (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N (twist₂ N' c f) := by
    intro f hf1 hf2
    unfold LaFacts LamC
    rw [← twist_homomorphism D.host.E _ _ _ N N' c f hfg hc]
    exact ⟨GlobalTheory.TwPerSelfDual.twO_selfDual D.host.E D.what₂.Tau _ _ (tauE D) δ D.host.d sc _ c f hP.ne hconj hc hf1 hf2 hL.1 hL.2,
      GlobalTheory.SemiTwist.semiChar_twO D.host.E D.what₂.Tau _ _ (tauE D) δ D.host.d sc _ c f hP.ne hconj hc hf1 hf2 hL.1 hL.2⟩
  exact half_periods_of_lattice D.host.E D.what₂.Tau _ _ (tauE D) δ D.host.d sc _ SS N N' c hP.ne hc hSS hfg hL
    (tw _ hc1 he1) (tw (fun Q => -expS SS Q) (fun Q => by simp [hc1])
      (fun Q => by rcases he1 Q with h | h | h <;> simp [h]))

end GlobalTheory.HalfSplit
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CardRepsEq
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RepsCard

theorem card_reps_eq : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (H : Formalism.L2.Th1.H.Sesq V) (α : V → ℂ) (A B Λ : AddSubgroup V), SplitHyp H α A B Λ → ∀ SA SB : Finset V, Formalism.L2.Th1.H.IsReps B (Λ ⊓ A) SA → Formalism.L2.Th1.H.IsReps Λ B SB → SA.card = SB.card := by
  intro V _ _ H α A B Λ hyp SA SB hSA hSB
  obtain ⟨hH, -, hB, -, sdB, hΛ, -, -, -, h5⟩ := hyp
  have hBint := (Formalism.L2.Th1.H.semicharacterBasic V H hH B α hB).2.2
  have hΛint := (Formalism.L2.Th1.H.semicharacterBasic V H hH Λ α hΛ).2.2
  have hone : ∀ {Λ₁ Λ₂ : AddSubgroup V} {S : Finset V} (c : ℂ), Formalism.L2.Th1.H.IsReps Λ₁ Λ₂ S →
      ∑ x ∈ S, (if x ∈ Λ₁ then c else 0) = c := by
    intro Λ₁ Λ₂ S c hS
    obtain ⟨x₀, hx₀, hd⟩ := hS.2.2 0 Λ₂.zero_mem
    have hx₀Λ : x₀ ∈ Λ₁ := by simpa using Λ₁.neg_mem hd
    rw [Finset.sum_eq_single x₀]
    · simp [hx₀Λ]
    · intro x hx hne
      rw [if_neg]
      intro hxΛ
      exact hne (hS.2.1 x hx x₀ hx₀ (Λ₁.sub_mem hxΛ hx₀Λ))
    · intro h; exact absurd hx₀ h
  have hcol : ∀ s ∈ SA, ∑ y ∈ SB, brk H y s = if s ∈ B then (SB.card : ℂ) else 0 := by
    intro s hs
    have hsΛ : s ∈ Λ := (hSA.1 s hs).1
    split_ifs with hsB
    · have hsd : s ∈ Formalism.L2.Th1.H.dualLat H B := by rw [sdB]; exact hsB
      rw [Finset.sum_congr rfl fun y hy => brk_one_of_int H (hsd y (hSB.1 y hy))]
      simp
    · by_contra hne
      apply hsB
      have hsd : s ∈ Formalism.L2.Th1.H.dualLat H B := by
        intro y hyB
        by_contra hno
        refine hne (char_sum_zero hSB (fun y => brk H y s) (fun u v => brk_add_left H u v s) ?_ (x₀ := y) hyB ?_)
        · intro m _ hmΛ; exact brk_one_of_int H (hΛint hsΛ m hmΛ)
        · intro h1; exact hno (int_of_brk_one H h1)
      rwa [sdB] at hsd
  have hrow : ∀ y ∈ SB, ∑ s ∈ SA, brk H y s = if y ∈ Λ then (SA.card : ℂ) else 0 := by
    intro y hy
    have hyB : y ∈ B := hSB.1 y hy
    split_ifs with hyΛ
    · rw [Finset.sum_congr rfl fun s hs => brk_one_of_int H (hΛint (hSA.1 s hs).1 y hyΛ)]
      simp
    · by_contra hne
      apply hyΛ
      apply h5 y hyB
      intro a haA haΛ
      by_contra hno
      refine hne (char_sum_zero hSA (fun s => brk H y s) (fun u v => brk_add_right H y u v) ?_ (x₀ := a) ⟨haΛ, haA⟩ ?_)
      · intro m _ hmB; exact brk_one_of_int H (hBint hmB y hyB)
      · intro h1; exact hno (int_of_brk_one H h1)
  have key : ∑ s ∈ SA, ∑ y ∈ SB, brk H y s = ∑ y ∈ SB, ∑ s ∈ SA, brk H y s := Finset.sum_comm
  rw [Finset.sum_congr rfl hcol, Finset.sum_congr rfl hrow, hone _ hSA, hone _ hSB] at key
  exact_mod_cast key.symm

end GlobalTheory.RepsCard
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteFourierExpansionHalfSplitPlaces
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdForm.DatumFour

theorem nsmul_mem_perO_of_halfB {E : Type} [Field E] [NumberField E] [StarRing E] {a b : ℕ}
    {SS : Finset (HeightOneSpectrum (𝓞 E))} {M : Submodule (𝓞 E) (Formalism.L2.Col.HomE E a b)} {c : ℕ} (hc : 0 < c)
    {y : Formalism.L2.Col.HomE E a b} (hy : y ∈ halfBO SS M c) : c • y ∈ M := by
  have h := Formalism.L2.Ker.mem_of_forall_locP M fun Q => GlobalTheory.AdForm.HalfPairing.smul_mem_locP hc hy Q
  rwa [Nat.cast_smul_eq_nsmul] at h

theorem xi_add_halfB {E : Type} [Field E] [NumberField E] [StarRing E] {a b : ℕ}
    {SS : Finset (HeightOneSpectrum (𝓞 E))} {N : Submodule (𝓞 E) (Formalism.L2.Col.Sp E a)} {N' : Submodule (𝓞 E) (Formalism.L2.Col.Sp E b)}
    {M : Submodule (𝓞 E) (Formalism.L2.Col.HomE E a b)} {c : ℕ} (hc : 0 < c) (Ξ : Formalism.L2.Col.HomE E a b → ℂ)
    (hΞ2 : ∀ x, ∀ y ∈ Formalism.L2.Col.homAt SS N N', Ξ (x + (c : E) • y) = Ξ x)
    (hH : ∀ z, (∀ P ∈ SS, z ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal M) → z ∈ Formalism.L2.Col.homAt SS N N')
    {β : Formalism.L2.Col.HomE E a b} (hβ : β ∈ halfBO SS M c) (x : Formalism.L2.Col.HomE E a b) : Ξ (x + β) = Ξ x := by
  have hcE : (c : E) ≠ 0 := Nat.cast_ne_zero.2 hc.ne'
  have h1 : (c : E)⁻¹ • β ∈ Formalism.L2.Col.homAt SS N N' := by
    refine hH _ fun P hP => ?_
    have h2 := (Formalism.L2.Ker.mem_twO M c _ β).1 hβ P
    have h3 : expS SS P = 1 := by unfold expS; rw [if_pos hP]
    rwa [h3, zpow_one] at h2
  have h4 := hΞ2 x _ h1
  rwa [smul_smul, mul_inv_cancel₀ hcE, one_smul] at h4

noncomputable def eXm {D : D7} (S T : HSp D) (e : AE D) (x : Formalism.L2.Col.HomE D.host.E S.rank T.rank) : WO S T :=
  (LinearMap.toMatrix' x).map fun r => e * incA D r

theorem nsmul_toMatrix_mem_latRat {D : D7} {S T : HSp D} (hcc : D.host.ccK = ⊤) {N : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {N' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} (dS : IsSelfDualC S N) (k c : ℕ) {y : Formalism.L2.Col.HomE D.host.E S.rank T.rank}
    (hy : c • y ∈ perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') :
    (k * c) • LinearMap.toMatrix' y ∈ GlobalTheory.LatVac.latRat S T (N : Set (Fin S.rank → D.host.E)) (N' : Set (Fin T.rank → D.host.E)) := by
  have h1 := GlobalTheory.AdForm.HalfPairing.toMatrix_mem_latRat hcc dS hy
  rw [map_nsmul] at h1
  rw [mul_smul]
  exact nsmul_mem h1 k

theorem char_brk {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} {δ : ℂ} {sc : ℝ} (hP : StdPair θ S T δ sc ψ)
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    (dS : IsSelfDualC S ΛS) (dT : IsSelfDualC T ΛT) {e : AE D} (he0 : infPart D e = 0) {k : ℕ} {t u : WO S T}
    (ht : IsHalf e t) (hu : u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True)
    {M : Matrix (Fin T.rank) (Fin S.rank) D.host.E} (htM : t = GlobalTheory.LatVac.finTens 1 M + k • u)
    (y' : Formalism.L2.Col.HomE D.host.E S.rank T.rank)
    (hY : k • LinearMap.toMatrix' y' ∈ GlobalTheory.LatVac.latRat S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E))) :
    ψ (symplO S T t (eXm S T (cA D e) y')) = brk (HV sc) (embH (tauE D) δ y') (embH (tauE D) δ (Matrix.toLin' M)) := by
  have hht : IsHalf (cA D (cA D e)) t := by rw [GlobalTheory.LatVac.cA_cA]; exact ht
  have h4 := GlobalTheory.DatumFourier.char_eq hP.std dS dT (GlobalTheory.PlaceVec.infPart_cA he0) hht hu htM hY
  have h6 := GlobalTheory.TraceBrk.exp_trace_eq_brk D ψ θ S T δ sc hP M (LinearMap.toMatrix' y')
  rw [Matrix.toLin'_toMatrix'] at h6
  exact h4.trans h6

theorem fin_sum {V : Type} [AddCommGroup V] [Module ℂ V] (H : Formalism.L2.Th1.H.Sesq V) {A B Λ : AddSubgroup V} {SA SB : Finset V}
    (f g : V → ℂ) {v : V} (hv : v ∈ Λ ⊓ A) (hRA : Formalism.L2.Th1.H.IsReps B (Λ ⊓ A) SA)
    (horth : ∀ w ∈ Λ ⊓ A, ∑ y ∈ SB, brk H y w = if w ∈ B then (SB.card : ℂ) else 0)
    (hcard : SA.card = SB.card) (hne : SB.card ≠ 0) (hg : ∀ y ∈ SB, g y = brk H y v) :
    ∃ s0 ∈ SA, v - s0 ∈ B ∧
      ∑ y ∈ SB, (((SA.card : ℂ))⁻¹ * ∑ s ∈ SA, f s * (brk H y s)⁻¹) * g y = f s0 := by
  obtain ⟨s0, hs0, hvs0⟩ := hRA.2.2 v hv
  refine ⟨s0, hs0, hvs0, ?_⟩
  have h1 : ∑ y ∈ SB, (((SA.card : ℂ))⁻¹ * ∑ s ∈ SA, f s * (brk H y s)⁻¹) * g y
      = ((SA.card : ℂ))⁻¹ * ∑ s ∈ SA, f s * ∑ y ∈ SB, brk H y (v - s) := by
    rw [Finset.sum_congr rfl fun y hy => by rw [hg y hy]]
    simp only [Formalism.L2.Ker.brk_sub_right, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun y _ => by ring
  rw [h1, Finset.sum_congr rfl fun s hs => by rw [horth (v - s) (sub_mem hv (hRA.1 s hs))]]
  rw [Finset.sum_eq_single s0 (fun s hs hne' => by
      rw [if_neg (fun h => hne' (hRA.2.1 s hs s0 hs0 (by
        have h2 : s - s0 = (v - s0) - (v - s) := by abel
        rw [h2]; exact sub_mem hvs0 h))), mul_zero]) (fun h => absurd hs0 h), if_pos hvs0, hcard]
  have : (SB.card : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hne
  field_simp

theorem onV_embH {E : Type} [Field E] [NumberField E] [StarRing E] {ι : Type} [Fintype ι] [Nonempty ι] {a b : ℕ}
    (emb : ι → E →+* ℂ) {δ : ℂ} (hδ : δ ≠ 0) (Ξ : Formalism.L2.Col.HomE E a b → ℂ) (z : Formalism.L2.Col.HomE E a b) :
    onV emb δ Ξ (embH emb δ z) = Ξ z := by
  have h : ∃ x, embH emb δ x = embH emb δ z := ⟨z, rfl⟩
  unfold onV
  rw [dite_eq_left h]
  exact congrArg Ξ (Formalism.L2.Ker.embH_inj emb hδ h.choose_spec)

theorem mem_BC {E : Type} [Field E] [NumberField E] [StarRing E] {ι : Type} [Fintype ι] {a b : ℕ}
    {emb : ι → E →+* ℂ} {δ : ℂ} {AA0 : Submodule (𝓞 E) E} {SS : Finset (HeightOneSpectrum (𝓞 E))}
    {N : Submodule (𝓞 E) (Formalism.L2.Col.Sp E a)} {N' : Submodule (𝓞 E) (Formalism.L2.Col.Sp E b)} {c : ℕ} {w : VV ι a b}
    (h : w ∈ BC emb δ AA0 SS N N' c) : ∃ β ∈ halfBO SS (perO AA0 N N') c, embH emb δ β = w :=
  AddSubgroup.mem_map.1 h

theorem embH_sub_eq {E : Type} [Field E] [NumberField E] {ι : Type} {a b : ℕ} (emb : ι → E →+* ℂ) (δ : ℂ)
    (m p β : Formalism.L2.Col.HomE E a b) (x0 s0 : VV ι a b) (hp : embH emb δ p = x0)
    (hβ : embH emb δ β = embH emb δ m - s0) : s0 - x0 = embH emb δ (m - p - β) := by
  rw [map_sub, map_sub, hp, hβ]; abel

theorem xi_sub_halfB {E : Type} [Field E] [NumberField E] [StarRing E] {a b : ℕ}
    {SS : Finset (HeightOneSpectrum (𝓞 E))} {N : Submodule (𝓞 E) (Formalism.L2.Col.Sp E a)} {N' : Submodule (𝓞 E) (Formalism.L2.Col.Sp E b)}
    {M : Submodule (𝓞 E) (Formalism.L2.Col.HomE E a b)} {c : ℕ} (hc : 0 < c) (Ξ : Formalism.L2.Col.HomE E a b → ℂ)
    (hΞ2 : ∀ x, ∀ y ∈ Formalism.L2.Col.homAt SS N N', Ξ (x + (c : E) • y) = Ξ x)
    (hH : ∀ z, (∀ P ∈ SS, z ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal M) → z ∈ Formalism.L2.Col.homAt SS N N')
    {β : Formalism.L2.Col.HomE E a b} (hβ : β ∈ halfBO SS M c) (x : Formalism.L2.Col.HomE E a b) : Ξ (x - β) = Ξ x := by
  have h1 := xi_add_halfB hc Ξ hΞ2 hH hβ (x - β)
  rw [sub_add_cancel] at h1
  exact h1.symm


set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 200000 in
theorem four_expand : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (a b : ℕ) (hS : S.rank = a) (hT : T.rank = b) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → ∀ (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)) (c : ℕ), 0 < c → Odd c → (∀ Q ∈ SS, ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal) → LaFacts (tauE D) δ D.host.d sc (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N' → (∃ ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E), IsSelfDualC S ΛS ∧ (ΛS : Set (Fin S.rank → D.host.E)) = latFr S hS N) → (∃ ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E), IsSelfDualC T ΛT ∧ (ΛT : Set (Fin T.rank → D.host.E)) = latFr T hT N') → ∀ (Φ : WO S T → ℂ) (Ξ : Formalism.L2.Col.HomE D.host.E a b → ℂ), IsSBHalf e (latO S T (latFr S hS N) (latFr T hT N') fun _ => True) Φ → (∀ γ, Φ (γ.map fun r => e * incA D r) = Ξ (toHom S T hS hT γ)) → (∀ x, Ξ x ≠ 0 → (c : D.host.E) • x ∈ Formalism.L2.Col.homAt SS N N') → (∀ x, ∀ y ∈ Formalism.L2.Col.homAt SS N N', Ξ (x + (c : D.host.E) • y) = Ξ x) → ∀ (SX SA SB : Finset (VV D.what₂.Tau a b)), Formalism.L2.Th1.H.IsReps (LamC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') (AC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) SS N N' c) SX → Formalism.L2.Th1.H.IsReps (BC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) SS N N' c) ((LamC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') ⊓ (AC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) SS N N' c)) SA → Formalism.L2.Th1.H.IsReps (LamC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') (BC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) SS N N' c) SB → ∀ (px py : VV D.what₂.Tau a b → Formalism.L2.Col.HomE D.host.E a b), (∀ x ∈ SX, px x ∈ halfAO SS (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') c ∧ embH (tauE D) δ (px x) = x) → (∀ y ∈ SB, py y ∈ halfBO SS (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') c ∧ embH (tauE D) δ (py y) = y) → ∀ t, Φ t = ∑ x ∈ SX, ∑ y ∈ SB, (((SA.card : ℂ))⁻¹ * ∑ s ∈ SA, onV (tauE D) δ Ξ (s - x) * (brk (HV sc) y s)⁻¹) * (ψ (symplO S T (t + ((LinearMap.toMatrix' (px x)).reindex (finCongr hT.symm) (finCongr hS.symm)).map fun r => e * incA D r) (((LinearMap.toMatrix' (py y)).reindex (finCongr hT.symm) (finCongr hS.symm)).map fun r => cA D e * incA D r)) * halfInd e (latO S T (latFr S hS N) (latFr T hT N') fun _ => True) (t + ((LinearMap.toMatrix' (px x)).reindex (finCongr hT.symm) (finCongr hS.symm)).map fun r => e * incA D r)) := by
  intro D ψ θ S T a b hS hT δ sc hP e SS hE N N' c hc hcP h2 hLa ⟨ΛS, dS, eS⟩ ⟨ΛT, dT, eT⟩ Φ Ξ hSB hΦ hΞ1 hΞ2 SX SA SB hRX hRA hRB px py hpx hpy
  subst hS hT
  obtain rfl : ΛS = N := SetLike.coe_injective eS
  obtain rfl : ΛT = N' := SetLike.coe_injective eT
  rw [← eS, ← eT] at hSB
  rw [← eS, ← eT]
  haveI : Nonempty D.what₂.Tau := ⟨D.eTau.symm 1⟩
  set Λ := latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True with hΛ
  have hee : e * e = e := GlobalTheory.PlaceDatum.idemSum_mul_self hE
  have he0 : infPart D e = 0 := GlobalTheory.PlaceVec.idemSum_infPart hE
  have hecA : e * cA D e = 0 := hE.2
  have heI : finPart D e ∈ intAE D := GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← map_mul, hee])
  have hcAcA : cA D e * cA D e = cA D e := by rw [← map_mul, hee]
  have hcI : finPart D (cA D e) ∈ intAE D := GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← map_mul, hcAcA])
  have hΛe : ∀ w ∈ Λ, e • w ∈ Λ := GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ e heI
  have hΛc : ∀ w ∈ Λ, cA D e • w ∈ Λ := GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ (cA D e) hcI
  have hhe : ∀ w : WO S T, IsHalf e (e • w) := fun w i j => by
    rw [Matrix.smul_apply, smul_eq_mul, ← mul_assoc, hee]
  have heX : ∀ x, IsHalf e (eXm S T e x) := fun x i j => by
    simp only [eXm, Matrix.map_apply, ← mul_assoc, hee]
  have heX_add : ∀ x y, eXm S T e (x + y) = eXm S T e x + eXm S T e y := fun x y => by
    ext i j; simp only [eXm, map_add (f := _), Matrix.map_apply, Matrix.add_apply, RingHom.map_add (f := _), mul_add]
  have heX_sub : ∀ x y, eXm S T e (x - y) = eXm S T e x - eXm S T e y := fun x y => by
    ext i j; simp only [eXm, map_sub, Matrix.map_apply, Matrix.sub_apply, RingHom.map_sub, mul_sub]
  have heF : ∀ M : Matrix (Fin T.rank) (Fin S.rank) D.host.E, e • GlobalTheory.LatVac.finTens 1 M = eXm S T e (Matrix.toLin' M) := fun M => by
    ext i j
    simp only [eXm, LinearMap.toMatrix'_toLin', Matrix.smul_apply, smul_eq_mul, Matrix.map_apply]
    refine GlobalTheory.SplitScalar.adele_ext (by simp only [RingHom.map_mul, he0, zero_mul]) ?_
    have h6 : finPart D (GlobalTheory.LatVac.finTens 1 M i j) = finPart D (incA D (M i j)) := rfl
    rw [RingHom.map_mul, RingHom.map_mul, h6]
  have hkeX : ∀ K : ℕ, ∀ M : Matrix (Fin T.rank) (Fin S.rank) D.host.E, K • eXm S T e (Matrix.toLin' ((K : D.host.E)⁻¹ • M)) = (if K = 0 then 0 else eXm S T e (Matrix.toLin' M)) := by
    intro K M
    split_ifs with hK
    · rw [hK, zero_smul]
    ext i j
    simp only [eXm, LinearMap.toMatrix'_toLin', Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, nsmul_eq_mul]
    rw [← mul_assoc, mul_comm (K : AE D) e, mul_assoc, show (K : AE D) = incA D (K : D.host.E) by simp, ← map_mul,
      ← mul_assoc, mul_inv_cancel₀ (Nat.cast_ne_zero.2 hK), one_mul]
  have hKinj : ∀ K : ℕ, 0 < K → ∀ w₁ w₂ : WO S T, K • w₁ = K • w₂ → w₁ = w₂ := by
    intro K hK w₁ w₂ h
    have hu : IsUnit (K : AE D) := by
      have h1 : (K : AE D) = incA D (K : D.host.E) := by simp
      rw [h1]
      exact (IsUnit.mk0 _ (Nat.cast_ne_zero.2 hK.ne')).map _
    ext i j
    have h3 := congrFun (congrFun h i) j
    simp only [Matrix.smul_apply, nsmul_eq_mul] at h3
    exact hu.mul_left_cancel h3
  have hΦ' : ∀ x, Φ (eXm S T e x) = Ξ x := fun x => by
    rw [eXm, hΦ]
    congr 1
    unfold toHom
    rw [show ((LinearMap.toMatrix' x).reindex (finCongr rfl) (finCongr rfl)) = LinearMap.toMatrix' x from by
      ext i j; simp [Matrix.reindex_apply], Matrix.toLin'_toMatrix']
  obtain ⟨hsup, k, hk, hinv, hsupp⟩ := hSB
  have hSplit := GlobalTheory.HalfSplit.splitHyp_halves D ψ θ S T δ sc hP e SS hE ΛS ΛT c hc hcP h2 hLa dS dT
  intro t
  show Φ t = ∑ x ∈ SX, ∑ y ∈ SB, (((SA.card : ℂ))⁻¹ * ∑ s ∈ SA, onV (tauE D) δ Ξ (s - x) * (brk (HV sc) y s)⁻¹) *
    (ψ (symplO S T (t + eXm S T e (px x)) (eXm S T (cA D e) (py y))) * halfInd e Λ (t + eXm S T e (px x)))
  have hRHS0 : ∀ x ∈ SX, t + eXm S T e (px x) ∉ Λ ∨ ¬ IsHalf e (t + eXm S T e (px x)) → ∑ y ∈ SB, (((SA.card : ℂ))⁻¹ * ∑ s ∈ SA, onV (tauE D) δ Ξ (s - x) * (brk (HV sc) y s)⁻¹) *
      (ψ (symplO S T (t + eXm S T e (px x)) (eXm S T (cA D e) (py y))) * halfInd e Λ (t + eXm S T e (px x))) = 0 := by
    intro x _ h
    have h0 : halfInd e Λ (t + eXm S T e (px x)) = 0 := by
      unfold halfInd
      rw [if_neg]
      rintro ⟨h1, h3⟩
      rcases h with h | h
      exacts [h h1, h h3]
    simp [h0]
  by_cases ht : IsHalf e t
  swap
  ·
    have hΦ0 : Φ t = 0 := by
      by_contra h0
      exact ht (hsup t h0)
    rw [hΦ0]
    refine (Finset.sum_eq_zero fun x hx => hRHS0 x hx (Or.inr fun h3 => ht fun i j => ?_)).symm
    have h4 := h3 i j
    have h5 := heX (px x) i j
    simp only [Matrix.add_apply, mul_add] at h4
    rw [h5] at h4
    exact add_right_cancel h4
  have hsn : ∀ (a : AE D) (n : ℕ) (w : WO S T), a • (n • w) = n • (a • w) := fun a n w => by
    ext i j; simp only [Matrix.smul_apply, smul_eq_mul, nsmul_eq_mul]; ring
  have hns3 : ∀ (p q r : ℕ) (w : WO S T), (p * q * r) • w = p • (q • (r • w)) := fun p q r w => by
    ext i j; simp only [Matrix.smul_apply, nsmul_eq_mul]; push_cast; ring
  have hns2 : ∀ (p q : ℕ) (w : WO S T), (p * q) • w = p • (q • w) := fun p q w => by
    ext i j; simp only [Matrix.smul_apply, nsmul_eq_mul]; push_cast; ring
  have hhs : ∀ (n : ℕ) (w : WO S T), IsHalf e w → IsHalf e (n • w) := fun n w hw i j => by
    rw [Matrix.smul_apply, nsmul_eq_mul, mul_left_comm, hw i j]
  have hEX : Φ t ≠ 0 → ∃ x0 ∈ SX, t + eXm S T e (px x0) ∈ Λ := by
    intro h0
    obtain ⟨M, hM, u, hu, htM⟩ := GlobalTheory.DatumFourier.approx_mod (Nat.mul_pos (Nat.mul_pos hk hk) hc) (hsupp t h0)
    have hteq : t = eXm S T e (Matrix.toLin' ((k : D.host.E)⁻¹ • M)) + k • (c • (e • u)) := by
      apply hKinj k hk
      have h1 : k • t = e • (k • t) := by
        ext i j
        rw [Matrix.smul_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, nsmul_eq_mul, mul_left_comm, ht i j]
      rw [h1, htM, smul_add, heF, smul_add, hkeX k M, if_neg hk.ne', hsn, hns3]
    have hΦg : Φ t = Ξ (Matrix.toLin' ((k : D.host.E)⁻¹ • M)) := by
      rw [hteq, hinv _ (nsmul_mem (hΛe u hu) c) (hhs c _ (hhe u)), hΦ']
    have hg1 := hΞ1 _ (hΦg ▸ h0)
    have hg2 := (GlobalTheory.HomAtPer.homAt_iff_locP_perO D S T SS h2 ΛS ΛT dS dT _).1 hg1
    obtain ⟨x0, hx0, hloc⟩ := GlobalTheory.PerLift.exists_rep_add_mem D ψ θ S T δ sc hP e SS hE ΛS ΛT dS dT c hc SX hRX px hpx _ hg2
    refine ⟨x0, hx0, ?_⟩
    have h3 := (GlobalTheory.AdForm.HalfLat.half_mem_latO_iff D S T hP.cc e SS hE ΛS ΛT dS dT _).2 hloc
    have h4 : t + eXm S T e (px x0) = eXm S T e (Matrix.toLin' ((k : D.host.E)⁻¹ • M) + px x0) + k • (c • (e • u)) := by
      conv_lhs => rw [hteq]
      rw [heX_add]; abel
    rw [h4]
    exact add_mem h3 (nsmul_mem (nsmul_mem (hΛe u hu) c) k)
  have hUQ : ∀ x ∈ SX, ∀ x0 ∈ SX, t + eXm S T e (px x) ∈ Λ → t + eXm S T e (px x0) ∈ Λ → x = x0 := by
    intro x hx x0 hx0 h1 h3
    have h4 : eXm S T e (px x - px x0) ∈ Λ := by
      have h5 : eXm S T e (px x - px x0) = (t + eXm S T e (px x)) - (t + eXm S T e (px x0)) := by rw [heX_sub]; abel
      rw [h5]; exact sub_mem h1 h3
    have hloc := (GlobalTheory.AdForm.HalfLat.half_mem_latO_iff D S T hP.cc e SS hE ΛS ΛT dS dT _).1 h4
    have hA : px x - px x0 ∈ halfAO SS (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) ΛS ΛT) c :=
      sub_mem (hpx x hx).1 (hpx x0 hx0).1
    have hmem : px x - px x0 ∈ perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) ΛS ΛT := by
      apply Formalism.L2.Ker.mem_of_forall_locP
      intro Q
      by_cases hQ : Q ∈ SS
      · exact hloc Q hQ
      · have h6 := (Formalism.L2.Ker.mem_twO _ c _ _).1 hA Q
        unfold expS at h6
        rw [if_neg hQ] at h6
        split_ifs at h6 with hQ'
        · have hcE : (c : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hc.ne'
          have h7 := Formalism.L2.Ker.nat_smul_mem _ c h6
          rwa [neg_neg, zpow_one, smul_smul, mul_inv_cancel₀ hcE, one_smul] at h7
        · simpa using h6
    have h8 : x - x0 ∈ LamC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) ΛS ΛT :=
      ⟨px x - px x0, hmem, by rw [map_sub, (hpx x hx).2, (hpx x0 hx0).2]⟩
    exact hRX.2.1 x hx x0 hx0 h8
  by_cases hex : ∃ x0 ∈ SX, t + eXm S T e (px x0) ∈ Λ
  swap
  · have hΦ0 : Φ t = 0 := by
      by_contra h0
      exact hex (hEX h0)
    rw [hΦ0]
    exact (Finset.sum_eq_zero fun x hx => hRHS0 x hx (Or.inl fun h => hex ⟨x, hx, h⟩)).symm
  obtain ⟨x0, hx0, hu0⟩ := hex
  rw [Finset.sum_eq_single x0 (fun x hx hne => hRHS0 x hx (Or.inl fun h => hne (hUQ x hx x0 hx0 h hu0)))
    (fun h => absurd hx0 h)]
  have huh : IsHalf e (t + eXm S T e (px x0)) := fun i j => by
    rw [Matrix.add_apply, mul_add, ht i j, heX _ i j]
  have hI : halfInd e Λ (t + eXm S T e (px x0)) = 1 := by
    unfold halfInd
    rw [if_pos ⟨hu0, huh⟩]
  simp only [hI, mul_one]
  obtain ⟨M, hM, u', hu', huM⟩ := GlobalTheory.DatumFourier.approx_mod (Nat.mul_pos hk hc) hu0
  have hueq : t + eXm S T e (px x0) = eXm S T e (Matrix.toLin' M) + k • (c • (e • u')) := by
    have h1 : t + eXm S T e (px x0) = e • (t + eXm S T e (px x0)) := by
      ext i j
      rw [Matrix.smul_apply, smul_eq_mul, huh i j]
    rw [h1, huM, smul_add, heF, hsn, hns2]
  have hΦt : Φ t = Ξ (Matrix.toLin' M - px x0) := by
    have h1 : t = eXm S T e (Matrix.toLin' M - px x0) + k • (c • (e • u')) := by
      rw [heX_sub, sub_add_eq_add_sub, ← hueq]; abel
    rw [h1, hinv _ (nsmul_mem (hΛe u' hu') c) (hhs c _ (hhe u')), hΦ']
  have hcAu : cA D e • (t + eXm S T e (px x0)) = 0 := by
    ext i j
    rw [Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply, ← huh i j, ← mul_assoc, mul_comm (cA D e) e, hecA, zero_mul]
  have hmA := GlobalTheory.HalfAConj.mem_perO_inf_halfAO D S T hP.cc e SS hE ΛS ΛT dS dT c hc M hM ⟨-(k • (cA D e • u')), neg_mem (nsmul_mem (hΛc u' hu') k), by
      have h1 := congrArg (fun w => cA D e • w) huM
      simp only [hcAu, smul_add] at h1
      rw [eq_neg_of_add_eq_zero_left h1.symm, hsn, mul_comm k c, hns2, smul_neg]⟩
  have hv : embH (tauE D) δ (Matrix.toLin' M) ∈ LamC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) ΛS ΛT ⊓
      AC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) SS ΛS ΛT c :=
    ⟨⟨_, hmA.1, rfl⟩, ⟨_, hmA.2, rfl⟩⟩
  have hY : ∀ y ∈ SB, ψ (symplO S T (t + eXm S T e (px x0)) (eXm S T (cA D e) (py y))) = brk (HV sc) y (embH (tauE D) δ (Matrix.toLin' M)) := by
    intro y hy
    have hcy : c • py y ∈ perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) ΛS ΛT :=
      nsmul_mem_perO_of_halfB hc (hpy y hy).1
    have hKY : (k * c) • LinearMap.toMatrix' (py y) ∈
        GlobalTheory.LatVac.latRat S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) := by
      exact nsmul_toMatrix_mem_latRat hP.cc dS k c hcy
    exact (char_brk hP dS dT he0 huh hu' huM (py y) hKY).trans (by rw [(hpy y hy).2])
  have hcard := GlobalTheory.RepsCard.card_reps_eq _ _ _ _ _ _ hSplit SA SB hRA hRB
  obtain ⟨y0, hy0, -⟩ := hRB.2.2 0 (zero_mem _)
  have hSBne : SB.card ≠ 0 := (Finset.card_pos.2 ⟨y0, hy0⟩).ne'
  obtain ⟨s0, hs0, hvs0, hsum⟩ := fin_sum (HV sc) (fun s => onV (tauE D) δ Ξ (s - x0))
    (fun y => ψ (symplO S T (t + eXm S T e (px x0)) (eXm S T (cA D e) (py y)))) hv hRA
    (fun w hw => GlobalTheory.brk_sum_reps_orth _ _ _ _ _ _ hSplit SB hRB w hw) hcard hSBne hY
  refine hΦt.trans (Eq.trans ?_ hsum.symm)
  beta_reduce
  refine (mem_BC hvs0).elim fun β hβ => ?_
  have hβ' := hβ.1
  have hβe := hβ.2
  have hs0e := embH_sub_eq (tauE D) δ (Matrix.toLin' M) (px x0) β x0 s0 (hpx x0 hx0).2 hβe
  have hXi := xi_sub_halfB hc Ξ hΞ2 (fun z hz => (GlobalTheory.HomAtPer.homAt_iff_locP_perO D S T SS h2 ΛS ΛT dS dT z).2 hz) hβ' (Matrix.toLin' M - px x0)
  rw [hs0e, onV_embH (tauE D) hP.ne, hXi]

end GlobalTheory.AdForm.DatumFour
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteFourierExpansionHalfSplitPlacesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_fourier_expansion_half_split_places : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (a b : ℕ) (hS : S.rank = a) (hT : T.rank = b) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → ∀ (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)) (c : ℕ), 0 < c → Odd c → (∀ Q ∈ SS, ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal) → LaFacts (tauE D) δ D.host.d sc (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N' → (∃ ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E), IsSelfDualC S ΛS ∧ (ΛS : Set (Fin S.rank → D.host.E)) = latFr S hS N) → (∃ ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E), IsSelfDualC T ΛT ∧ (ΛT : Set (Fin T.rank → D.host.E)) = latFr T hT N') → ∀ (Φ : WO S T → ℂ) (Ξ : Formalism.L2.Col.HomE D.host.E a b → ℂ), IsSBHalf e (latO S T (latFr S hS N) (latFr T hT N') fun _ => True) Φ → (∀ γ, Φ (γ.map fun r => e * incA D r) = Ξ (toHom S T hS hT γ)) → (∀ x, Ξ x ≠ 0 → (c : D.host.E) • x ∈ Formalism.L2.Col.homAt SS N N') → (∀ x, ∀ y ∈ Formalism.L2.Col.homAt SS N N', Ξ (x + (c : D.host.E) • y) = Ξ x) → ∀ (SX SA SB : Finset (VV D.what₂.Tau a b)), Formalism.L2.Th1.H.IsReps (LamC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') (AC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) SS N N' c) SX → Formalism.L2.Th1.H.IsReps (BC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) SS N N' c) ((LamC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') ⊓ (AC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) SS N N' c)) SA → Formalism.L2.Th1.H.IsReps (LamC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') (BC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) SS N N' c) SB → ∀ (px py : VV D.what₂.Tau a b → Formalism.L2.Col.HomE D.host.E a b), (∀ x ∈ SX, px x ∈ halfAO SS (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') c ∧ embH (tauE D) δ (px x) = x) → (∀ y ∈ SB, py y ∈ halfBO SS (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') c ∧ embH (tauE D) δ (py y) = y) → ∀ t, Φ t = ∑ x ∈ SX, ∑ y ∈ SB, (((SA.card : ℂ))⁻¹ * ∑ s ∈ SA, onV (tauE D) δ Ξ (s - x) * (brk (HV sc) y s)⁻¹) * (ψ (symplO S T (t + ((LinearMap.toMatrix' (px x)).reindex (finCongr hT.symm) (finCongr hS.symm)).map fun r => e * incA D r) (((LinearMap.toMatrix' (py y)).reindex (finCongr hT.symm) (finCongr hS.symm)).map fun r => cA D e * incA D r)) * halfInd e (latO S T (latFr S hS N) (latFr T hT N') fun _ => True) (t + ((LinearMap.toMatrix' (px x)).reindex (finCongr hT.symm) (finCongr hS.symm)).map fun r => e * incA D r)) := by
  first | exact @GlobalTheory.AdForm.DatumFour.four_expand | exact GlobalTheory.AdForm.DatumFour.four_expand | (intros; apply GlobalTheory.AdForm.DatumFour.four_expand <;> assumption)
end
