module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.RelIndexSmulSub
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.LatBasOHolds

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.HermitianBasisBelowSecond
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.OEvBasis
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.IdxPiWStd
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.PairHermSmulRight
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.BHRSmulRight
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.SdVolHOfPi
noncomputable section

namespace PI.OmLocU

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.LocVol NumberField IsDedekindDomain

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

theorem sdVolW_of (a : ℕ) (hC : CondV σ J ψ v) (hD : DualW σ J ψ v Λ a) (hI : IdxW v Λ a)
    (hFull : ∃ L : Submodule (𝓞 E) (Fin n → E),
      Submodule.IsFullLattice E L ∧ (L : Set (Fin n → E)) = Λ) :
    SdVolW σ J ψ v Λ a :=
  sdVolW_of_top σ J ψ v Λ a hC (topW_holds v Λ a hFull) hD hI

theorem sdVolH_of (a : ℕ) (hC : CondV σ J ψ v) (hD : DualH σ J ψ v a) (hI : IdxHO σ v a) :
    SdVolH σ J ψ v a :=
  sdVolH_of_top σ J ψ v a hC (topH_holds v σ a) hD hI

theorem sdVolW_of_pi (a : ℕ) (hC : CondV σ J ψ v) (hD : DualW σ J ψ v Λ a) (hI : IdxPiW v Λ a)
    (hFull : ∃ L : Submodule (𝓞 E) (Fin n → E),
      Submodule.IsFullLattice E L ∧ (L : Set (Fin n → E)) = Λ) :
    SdVolW σ J ψ v Λ a :=
  sdVolW_of σ J ψ v Λ a hC hD (idxW_of v Λ a hI) hFull

theorem sdVolH_of_pi (a : ℕ) (hC : CondV σ J ψ v) (hD : DualH σ J ψ v a) (hI : IdxPiH σ v a) :
    SdVolH σ J ψ v a :=
  sdVolH_of σ J ψ v a hC hD (idxHO_of σ v a hI)

end PI.OmLocU
end
end

noncomputable section

namespace PI.OmLocU.SdB

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain PI.OmLocU PI.VolStabSW
open scoped TensorProduct

section Int

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))

theorem b_fg : (Submodule.span (v.adicCompletionIntegers F)
    ((fun x : 𝓞 E => inclR (F := F) (Fv F v) (x : E)) '' Set.univ)).FG := by
  let b := RingOfIntegers.basis E
  have h : Submodule.span (v.adicCompletionIntegers F)
      ((fun x : 𝓞 E => inclR (F := F) (Fv F v) (x : E)) '' Set.univ) =
      Submodule.span (v.adicCompletionIntegers F)
        (Set.range fun i => inclR (F := F) (Fv F v) ((b i : 𝓞 E) : E)) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨x, -, rfl⟩
      have hx : ((x : 𝓞 E) : E) = ∑ i, (b.repr x i) • ((b i : 𝓞 E) : E) := by
        have := congrArg (fun y : 𝓞 E => (y : E)) (b.sum_repr x)
        simpa using this.symm
      simp only
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hx, map_sum]
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [map_zsmul]
      exact zsmul_mem (Submodule.subset_span (Set.mem_range_self i)) _
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact Submodule.subset_span ⟨_, Set.mem_univ _, rfl⟩
  rw [h]
  exact Submodule.fg_span (Set.finite_range _)

def bAlg : Subalgebra (v.adicCompletionIntegers F) (Fv F v ⊗[F] E) :=
  Submodule.toSubalgebra (Submodule.span (v.adicCompletionIntegers F)
    ((fun x : 𝓞 E => inclR (F := F) (Fv F v) (x : E)) '' Set.univ)) (b_one_mem (E := E) v)
    (fun _ _ hx hy => b_mul_mem v hx hy)

theorem b_int_of_sc {a : Fv F v} (ha : sc (E := E) v a ∈ OEv (E := E) v) : a ∈ v.adicCompletionIntegers F := by
  have hfg : (Subalgebra.toSubmodule (bAlg (E := E) v)).FG := b_fg v
  have hi : IsIntegral (v.adicCompletionIntegers F) (sc (E := E) v a) :=
    IsIntegral.of_mem_of_fg (bAlg (E := E) v) hfg _ ha
  let f : Fv F v →ₐ[v.adicCompletionIntegers F] Fv F v ⊗[F] E :=
    (Algebra.ofId (Fv F v) (Fv F v ⊗[F] E)).restrictScalars (v.adicCompletionIntegers F)
  have hfa : f a = sc (E := E) v a := by rw [b_sc_eq]; rfl
  rw [← hfa] at hi
  have hi' := (isIntegral_algHom_iff f (algebraMap (Fv F v) (Fv F v ⊗[F] E)).injective).1 hi
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hi'
  rw [← hy]
  exact y.2

theorem b_sigR_mem (σ : E →ₐ[F] E) {z : Fv F v ⊗[F] E} (hz : z ∈ OEv (E := E) v) :
    sigR (Fv F v) σ z ∈ OEv (E := E) v := by
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, -, rfl⟩ := hx
    have hb : IsIntegral ℤ (σ (b : E)) := by
      simpa using (b.isIntegral_coe).map (σ.toRingHom.toIntAlgHom)
    have e : sigR (Fv F v) σ (inclR (F := F) (Fv F v) (b : E)) =
        inclR (F := F) (Fv F v) ((⟨σ (b : E), hb⟩ : 𝓞 E) : E) := by
      simp [sigR, inclR]
    rw [e]
    exact b_inclR_mem (F := F) (E := E) v ⟨σ (b : E), hb⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx =>
    have h1 : r • x = algebraMap (Fv F v) (Fv F v ⊗[F] E) (r : Fv F v) * x := by
      rw [← Algebra.smul_def]; rfl
    have h2 : algebraMap (Fv F v) (Fv F v ⊗[F] E) (r : Fv F v) * sigR (Fv F v) σ x =
        r • sigR (Fv F v) σ x := by
      rw [← Algebra.smul_def]; rfl
    have h3 : sigR (Fv F v) σ (algebraMap (Fv F v) (Fv F v ⊗[F] E) (r : Fv F v)) =
        algebraMap (Fv F v) (Fv F v ⊗[F] E) (r : Fv F v) := by
      simp [sigR, Algebra.TensorProduct.algebraMap_apply]
    rw [h1, map_mul, h3, h2]
    exact Submodule.smul_mem _ r hx

theorem b_tr_sc (s : Fv F v) (w : Fv F v ⊗[F] E) :
    Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (sc (E := E) v s * w) =
      s * Algebra.trace (Fv F v) (Fv F v ⊗[F] E) w := by
  rw [b_sc_eq, ← Algebra.smul_def, map_smul, smul_eq_mul]

end Int

section DualW

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

theorem b_hR_smul_right (x y : Fin n → Fv F v ⊗[F] E) (c : Fv F v ⊗[F] E) :
    hR (Fv F v) σ J x (c • y) = c * hR (Fv F v) σ J x y := by
  simp only [hR, Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem b_hR_smul_left (c : Fv F v ⊗[F] E) (x y : Fin n → Fv F v ⊗[F] E) :
    hR (Fv F v) σ J (c • x) y = sigR (Fv F v) σ c * hR (Fv F v) σ J x y := by
  simp only [hR, Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem b_hR_zero_left (y : Fin n → Fv F v ⊗[F] E) : hR (Fv F v) σ J 0 y = 0 := by
  simp [hR, Formalism.UG.hform]

theorem b_smulF (s : Fv F v) (y : Fin n → Fv F v ⊗[F] E) : s • y = sc (E := E) v s • y := by
  funext i
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [Algebra.smul_def]
  rfl

theorem b_BR_smul_right {a : ℕ} (s : Fv F v) (X Y : TupV (E := E) v n a) :
    BR (Fv F v) σ J X (s • Y) = s * BR (Fv F v) σ J X Y := by
  simp only [BR, Pi.smul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [b_smulF v s (Y i), b_hR_smul_right, b_tr_sc]

theorem b_BR_single {a : ℕ} (i : Fin a) (u : Fin n → Fv F v ⊗[F] E) (Y : TupV (E := E) v n a) :
    BR (Fv F v) σ J (Pi.single i u) Y =
      Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (hR (Fv F v) σ J u (Y i)) := by
  classical
  rw [BR, Finset.sum_eq_single i]
  · rw [Pi.single_eq_same]
  · intro j _ hj
    rw [Pi.single_eq_of_ne hj, b_hR_zero_left, map_zero]
  · intro h; exact absurd (Finset.mem_univ i) h
theorem dualW_of_perf (a : ℕ) (hP : TrPerf σ J ψ v) : DualW σ J ψ v Λ a := by
  classical
  rintro hS ⟨L, hLat, rfl⟩ hSD hU
  have hd0 := dV_ne_zero v
  have hinv : ∀ y, σ (σ y) = y := b_sig_sig σ hS.1
  ext Y
  simp only [Set.mem_ofPred_eq, SetLike.mem_coe, mem_smulSub]
  constructor
  · intro h
    refine ⟨dV v • Y, fun i => ?_, by rw [smul_smul, inv_mul_cancel₀ hd0, one_smul]⟩
    refine (hSD _).2 fun x hx => hP hS hU _ fun c hc => ?_
    have hcx : Pi.single i (sigR (Fv F v) σ c • x) ∈ LamT v (L : Set (Fin n → E)) a := by
      intro j
      by_cases hj : j = i
      · subst hj
        rw [Pi.single_eq_same]
        exact b_lat_smul v L (b_sigR_mem v σ hc) hx
      · rw [Pi.single_eq_of_ne hj]
        exact Submodule.zero_mem _
    have h1 := h _ hcx
    rw [b_BR_single, b_hR_smul_left, sigR_sigR v σ hinv] at h1
    rw [Pi.smul_apply, b_smulF v, b_hR_smul_right, mul_left_comm, b_tr_sc]
    exact h1
  · rintro ⟨X', hX', rfl⟩ X hX
    rw [b_BR_smul_right, ← mul_assoc, mul_inv_cancel₀ hd0, one_mul]
    exact sum_mem fun i _ => b_trace_mem v ((hSD _).1 (hX' i) _ (hX i))

end DualW

end PI.OmLocU.SdB
end
end

noncomputable section

namespace PI.OmLocU.SdB

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain PI.OmLocU PI.VolStabSW
open scoped TensorProduct

section DualH

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F))

theorem b_tr_sig (hcm : IsCMExt F E σ) (w : Fv F v ⊗[F] E) :
    Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (sigR (Fv F v) σ w) = Algebra.trace (Fv F v) (Fv F v ⊗[F] E) w := by
  have hinv := b_sig_sig σ hcm
  have hnt := b_sig_nt σ hcm
  have hfin : Module.finrank F E = 2 := hcm.2.2.1
  apply (algebraMap (Fv F v) (Fv F v ⊗[F] E)).injective
  rw [trace_v v σ hinv hnt hfin, trace_v v σ hinv hnt hfin, sigR_sigR v σ hinv, add_comm]

def hm {a : ℕ} (hinv : ∀ y, σ (σ y) = y) (i j : Fin a) (c : Fv F v ⊗[F] E) : HermR (Fv F v) σ a :=
  ⟨Matrix.single i j c + Matrix.single j i (sigR (Fv F v) σ c), fun p q => by
    simp only [Matrix.add_apply, Matrix.single_apply]
    rw [map_add (f := _), apply_ite (sigR (Fv F v) σ), apply_ite (sigR (Fv F v) σ), map_zero, sigR_sigR v σ hinv, add_comm]
    congr 1 <;> exact if_congr and_comm rfl rfl⟩

theorem coe_hm {a : ℕ} (hinv : ∀ y, σ (σ y) = y) (i j : Fin a) (c : Fv F v ⊗[F] E) :
    (hm σ v hinv i j c : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) =
      Matrix.single i j c + Matrix.single j i (sigR (Fv F v) σ c) := rfl

theorem hm_mem {a : ℕ} (hinv : ∀ y, σ (σ y) = y) (i j : Fin a) {c : Fv F v ⊗[F] E}
    (hc : c ∈ OEv (E := E) v) : hm σ v hinv i j c ∈ HO σ v a := by
  intro p q
  rw [coe_hm, Matrix.add_apply, Matrix.single_apply, Matrix.single_apply]
  refine Submodule.add_mem _ ?_ ?_
  · split_ifs
    · exact hc
    · exact Submodule.zero_mem _
  · split_ifs
    · exact b_sigR_mem v σ hc
    · exact Submodule.zero_mem _

theorem sum_eq_trace {a : ℕ} (M N : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) :
    ∑ p, ∑ q, M p q * N q p = (M * N).trace := by
  rfl

theorem half_two : algebraMap F (Fv F v) (1 / 2) * 2 = 1 := by
  rw [← map_ofNat (algebraMap F (Fv F v)) 2, ← map_mul, one_div, inv_mul_cancel₀ two_ne_zero, map_one]

theorem half_mul (t : Fv F v) : algebraMap F (Fv F v) (1 / 2) * (t + t) = t := by
  rw [← two_mul, ← mul_assoc, half_two, one_mul]

theorem pair_hm (hcm : IsCMExt F E σ) {a : ℕ} (i j : Fin a) (c : Fv F v ⊗[F] E) (T : HermR (Fv F v) σ a) :
    pairHerm (Fv F v) σ a (hm σ v (b_sig_sig σ hcm) i j c) T =
      Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (c * (T : Matrix (Fin a) (Fin a) _) j i) := by
  unfold pairHerm
  rw [sum_eq_trace, coe_hm, add_mul, Matrix.trace_add, Matrix.trace_single_mul, Matrix.trace_single_mul,
    smul_eq_mul, smul_eq_mul, ← T.2 i j, ← map_mul (sigR (Fv F v) σ), map_add, b_tr_sig σ v hcm, half_mul]

theorem pairHerm_smul_right' {a : ℕ} (s : Fv F v) (S T : HermR (Fv F v) σ a) :
    pairHerm (Fv F v) σ a S (s • T) = s * pairHerm (Fv F v) σ a S T := by
  simp only [pairHerm, coe_hermSMul, Matrix.smul_apply, mul_smul_comm, ← Finset.smul_sum, map_smul,
    smul_eq_mul]
  ring

theorem pair_int (hcm : IsCMExt F E σ) {a : ℕ} {S T : HermR (Fv F v) σ a} (hS : S ∈ HO σ v a) (hT : T ∈ HO σ v a) :
    pairHerm (Fv F v) σ a S T ∈ v.adicCompletionIntegers F := by
  have hinv := b_sig_sig σ hcm
  have hnt := b_sig_nt σ hcm
  have hfin : Module.finrank F E = 2 := hcm.2.2.1
  set u := ∑ p, ∑ q, (S : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) p q * (T : Matrix (Fin a) (Fin a) _) q p
    with hudef
  have hu : u ∈ OEv (E := E) v :=
    sum_mem fun p _ => sum_mem fun q _ => b_mul_mem v (hS p q) (hT q p)
  have hfix : sigR (Fv F v) σ u = u := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hudef, map_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    rw [← S.2 p q, ← T.2 q p]
  have hsc : sc (E := E) v (pairHerm (Fv F v) σ a S T) = u := by
    have htr : sc (E := E) v (Algebra.trace (Fv F v) (Fv F v ⊗[F] E) u) = u + u := by
      rw [b_sc_eq, trace_v v σ hinv hnt hfin, hfix]
    have h2 : sc (E := E) v (algebraMap F (Fv F v) (1 / 2)) * 2 = 1 := by
      have e2 : (2 : Fv F v ⊗[F] E) = sc (E := E) v 2 := by rw [b_sc_eq, map_ofNat]
      rw [e2, b_sc_eq, b_sc_eq, ← map_mul, half_two, map_one]
    have hm2 : ∀ x y : Fv F v, sc (E := E) v (x * y) = sc (E := E) v x * sc (E := E) v y := fun x y => by
      simp only [b_sc_eq, map_mul]
    unfold pairHerm
    rw [← hudef, hm2, htr, ← two_mul, ← mul_assoc, h2, one_mul]
  exact b_int_of_sc v (hsc ▸ hu)

theorem dualH_of_perf (a : ℕ) (hP : TrPerf σ J ψ v) : DualH σ J ψ v a := by
  intro hS hU
  have hcm := hS.1
  have hd0 := dV_ne_zero v
  ext T
  simp only [Set.mem_ofPred_eq, SetLike.mem_coe, mem_smulSub]
  constructor
  · intro h
    refine ⟨dV v • T, fun i j => ?_, by rw [smul_smul, inv_mul_cancel₀ hd0, one_smul]⟩
    rw [coe_hermSMul, Matrix.smul_apply, Algebra.smul_def]
    refine hP hS hU _ fun c hc => ?_
    have h1 := h _ (hm_mem σ v (b_sig_sig σ hcm) j i hc)
    rw [pair_hm σ v hcm] at h1
    rw [mul_left_comm, ← b_sc_eq, b_tr_sc]
    exact h1
  · rintro ⟨T', hT', rfl⟩ S hS'
    rw [pairHerm_smul_right', ← mul_assoc, mul_inv_cancel₀ hd0, one_mul]
    exact pair_int σ v hcm hS' hT'

end DualH

end PI.OmLocU.SdB
end
end

noncomputable section

namespace PI.OmLocU.SdB

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain PI.OmLocU PI.VolStabSW
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

theorem latIdx (b : Fin (2 * n) → Fin n → Fv F v ⊗[F] E) (hb : LinearIndependent (Fv F v) b)
    (hmem : ∀ x, x ∈ latLoc (E := E) v Λ ↔
      ∃ c : Fin (2 * n) → v.adicCompletionIntegers F, x = ∑ i, (c i : Fv F v) • b i)
    (hR : ResIdx v) (ϖ : Fv F v) (hϖ : IsUnif v ϖ) :
    (lattice₂ v Λ ϖ).relIndex (latA v Λ) = (Ideal.absNorm v.asIdeal) ^ (2 * n) := by
  let φ : (Fin (2 * n) → v.adicCompletionIntegers F) →+ latA v Λ :=
    { toFun := fun c => ⟨∑ i, (c i : Fv F v) • b i, (hmem _).2 ⟨c, rfl⟩⟩
      map_zero' := by ext1; simp
      map_add' := fun c d => by
        ext1
        simp [add_smul, Finset.sum_add_distrib] }
  have hφs : Function.Surjective φ := by
    rintro ⟨x, hx⟩
    obtain ⟨c, rfl⟩ := (hmem x).1 hx
    exact ⟨c, rfl⟩
  have key : ((lattice₂ v Λ ϖ).addSubgroupOf (latA v Λ)).comap φ =
      AddSubgroup.pi Set.univ (fun _ => unifO v ϖ) := by
    ext c
    rw [AddSubgroup.mem_comap, AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_pi]
    constructor
    · rintro ⟨z, hz, hze⟩ i _
      obtain ⟨d, rfl⟩ := (hmem z).1 hz
      refine ⟨d i, ?_⟩
      have e : ∑ i, (c i : Fv F v) • b i = ∑ i, (ϖ * d i) • b i := by
        have : (DistribSMul.toAddMonoidHom (Fin n → Fv F v ⊗[F] E) (sc (E := E) v ϖ))
            (∑ i, (d i : Fv F v) • b i) = ∑ i, (ϖ * d i) • b i := by
          show sc (E := E) v ϖ • ∑ i, (d i : Fv F v) • b i = _
          rw [Finset.smul_sum]
          exact Finset.sum_congr rfl fun i _ => sc_smul_smul v ϖ _ _
        rw [← this, hze]
        rfl
      have h0 := Fintype.linearIndependent_iff.1 hb (fun i => (c i : Fv F v) - ϖ * d i)
        (by simp only [sub_smul, Finset.sum_sub_distrib, e, sub_self])
      exact sub_eq_zero.1 (h0 i)
    · intro h
      choose d hd using fun i => h i (Set.mem_univ i)
      refine ⟨∑ i, (d i : Fv F v) • b i, (hmem _).2 ⟨d, rfl⟩, ?_⟩
      show sc (E := E) v ϖ • ∑ i, (d i : Fv F v) • b i = ∑ i, (c i : Fv F v) • b i
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [sc_smul_smul, hd i]
  rw [AddSubgroup.relIndex, ← AddSubgroup.index_comap_of_surjective _ hφs, key, AddSubgroup.index_pi]
  simp only [hR ϖ hϖ, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem lamIdx (a : ℕ) (b : Fin (2 * n) → Fin n → Fv F v ⊗[F] E) (hb : LinearIndependent (Fv F v) b)
    (hmem : ∀ x, x ∈ latLoc (E := E) v Λ ↔
      ∃ c : Fin (2 * n) → v.adicCompletionIntegers F, x = ∑ i, (c i : Fv F v) • b i)
    (hR : ResIdx v) (ϖ : Fv F v) (hϖ : IsUnif v ϖ) :
    (lamP v Λ a ϖ).relIndex (lamA v Λ a) = (Ideal.absNorm v.asIdeal) ^ (2 * n * a) := by
  have hV := latIdx v Λ b hb hmem hR ϖ hϖ
  rw [AddSubgroup.relIndex, ← redT_ker, AddSubgroup.index_ker,
    AddMonoidHom.range_eq_top.2 (redT_surj v Λ a ϖ), AddSubgroup.card_top, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin a),
    Fintype.card_fin]
  have hq : Nat.card (latA v Λ ⧸ (lattice₂ v Λ ϖ).addSubgroupOf (latA v Λ)) =
      (Ideal.absNorm v.asIdeal) ^ (2 * n) := by
    rw [← hV, AddSubgroup.relIndex, AddSubgroup.index]
  rw [hq, ← pow_mul]

theorem basis_of (hCM : IsCMExt F E σ) (L : Submodule (𝓞 E) (Fin n → E)) (hLat : Submodule.IsFullLattice E L) :
    ∃ b : Fin (2 * n) → (Fin n → Fv F v ⊗[F] E), LinearIndependent (Fv F v) b ∧
      ∀ x, x ∈ latLoc (E := E) v (L : Set (Fin n → E)) ↔
        ∃ c : Fin (2 * n) → v.adicCompletionIntegers F, x = ∑ i, (c i : Fv F v) • b i := by
  classical
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have h2 : Module.finrank F E = 2 := hCM.2.2.1
  obtain ⟨m, b, hli, hmem, hsp⟩ := exists_basO v L hLat
  have hm : m = 2 * n := by
    have h1 := Module.finrank_eq_card_basis (Module.Basis.mk hli hsp)
    rw [Fintype.card_fin] at h1
    rw [← h1, Module.finrank_pi_fintype]
    simp only [Module.finrank_baseChange, h2, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    ring
  subst hm
  exact ⟨b, hli, hmem⟩

theorem smul_tup {a : ℕ} (ϖ : Fv F v) (p : TupV (E := E) v n a) : ϖ • p = sc (E := E) v ϖ • p := by
  funext i j
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [Algebra.smul_def]
  rfl

theorem idxPiW_std (a : ℕ) (hS : StdHyp σ J ψ)
    (hFull : ∃ L : Submodule (𝓞 E) (Fin n → E),
      Submodule.IsFullLattice E L ∧ (L : Set (Fin n → E)) = Λ) : IdxPiW v Λ a := by
  obtain ⟨L, hLat, rfl⟩ := hFull
  rintro _ _ ϖ hϖ
  obtain ⟨b, hb, hmem⟩ := basis_of σ v hS.1 L hLat
  have e : smulSub ϖ (LW v (L : Set (Fin n → E)) a) = lamP v (L : Set (Fin n → E)) a ϖ := by
    ext X
    rw [mem_smulSub, lamP, AddSubgroup.mem_map]
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨p, hp, by rw [DistribSMul.toAddMonoidHom_apply, smul_tup]⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨p, hp, by rw [DistribSMul.toAddMonoidHom_apply, smul_tup]⟩
  have e2 : LW v (L : Set (Fin n → E)) a = lamA v (L : Set (Fin n → E)) a := AddSubgroup.ext fun _ => Iff.rfl
  rw [e, e2, lamIdx v _ a b hb hmem (resIdx_holds v) ϖ hϖ, qv]
  push_cast
  ring

end PI.OmLocU.SdB
end
end

noncomputable section

namespace PI.OmLocU.SdB

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain PI.OmLocU PI.VolStabSW
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))

theorem genIdx {W : Type} [AddCommGroup W] [Module (Fv F v) W] {ι : Type} [Fintype ι] (M : AddSubgroup W)
    (b : ι → W) (hb : LinearIndependent (Fv F v) b)
    (hmem : ∀ x, x ∈ M ↔ ∃ c : ι → v.adicCompletionIntegers F, x = ∑ i, (c i : Fv F v) • b i)
    (ϖ : Fv F v) (hϖ : IsUnif v ϖ) :
    (smulSub ϖ M).relIndex M = (Ideal.absNorm v.asIdeal) ^ (Fintype.card ι) := by
  classical
  let φ : (ι → v.adicCompletionIntegers F) →+ M :=
    { toFun := fun c => ⟨∑ i, (c i : Fv F v) • b i, (hmem _).2 ⟨c, rfl⟩⟩
      map_zero' := by ext1; simp
      map_add' := fun c d => by
        ext1
        simp [add_smul, Finset.sum_add_distrib] }
  have hφs : Function.Surjective φ := by
    rintro ⟨x, hx⟩
    obtain ⟨c, rfl⟩ := (hmem x).1 hx
    exact ⟨c, rfl⟩
  have hsm : ∀ d : ι → v.adicCompletionIntegers F,
      ϖ • ∑ i, (d i : Fv F v) • b i = ∑ i, (ϖ * d i) • b i := by
    intro d
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => smul_smul _ _ _
  have key : ((smulSub ϖ M).addSubgroupOf M).comap φ =
      AddSubgroup.pi Set.univ (fun _ => unifO v ϖ) := by
    ext c
    rw [AddSubgroup.mem_comap, AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_pi]
    constructor
    · intro hc i _
      obtain ⟨z, hz, hze⟩ := (mem_smulSub ϖ M _).1 hc
      obtain ⟨d, rfl⟩ := (hmem z).1 hz
      refine ⟨d i, ?_⟩
      have e : ∑ i, (c i : Fv F v) • b i = ∑ i, (ϖ * d i) • b i := by
        rw [← hsm, hze]
        rfl
      have h0 := Fintype.linearIndependent_iff.1 hb (fun i => (c i : Fv F v) - ϖ * d i)
        (by simp only [sub_smul, Finset.sum_sub_distrib, e, sub_self])
      exact sub_eq_zero.1 (h0 i)
    · intro h
      choose d hd using fun i => h i (Set.mem_univ i)
      refine (mem_smulSub ϖ M _).2 ⟨∑ i, (d i : Fv F v) • b i, (hmem _).2 ⟨d, rfl⟩, ?_⟩
      rw [hsm]
      show ∑ i, (ϖ * d i) • b i = ∑ i, (c i : Fv F v) • b i
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hd i]
  rw [AddSubgroup.relIndex, ← AddSubgroup.index_comap_of_surjective _ hφs, key, AddSubgroup.index_pi]
  simp only [resIdx_holds v ϖ hϖ, Finset.prod_const, Finset.card_univ]

theorem oEv_basis : ∃ β : Fin (Module.finrank F E) → Fv F v ⊗[F] E, LinearIndependent (Fv F v) β ∧
    ∀ x, x ∈ OEv (E := E) v ↔ ∃ c : Fin (Module.finrank F E) → v.adicCompletionIntegers F,
      x = ∑ i, (c i : Fv F v) • β i := by
  classical
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  set M := Submodule.span (v.adicCompletionIntegers F)
    ((fun x : 𝓞 E => inclR (F := F) (Fv F v) (x : E)) '' Set.univ) with hM
  have : Module.Finite (v.adicCompletionIntegers F) M := Module.Finite.iff_fg.2 (b_fg v)
  have : Module.IsTorsionFree (v.adicCompletionIntegers F) (Fv F v ⊗[F] E) :=
    Module.IsTorsionFree.of_smul_eq_zero fun r x h => by
      have h' : (r : Fv F v) • x = 0 := h
      rcases smul_eq_zero.1 h' with h0 | h0
      · exact Or.inl (Subtype.ext h0)
      · exact Or.inr h0
  have : Module.Free (v.adicCompletionIntegers F) M := Module.free_of_finite_type_torsion_free'
  let bM := Module.finBasis (v.adicCompletionIntegers F) M
  let b0 : Fin (Module.finrank (v.adicCompletionIntegers F) M) → Fv F v ⊗[F] E := fun i => (bM i : _)
  have hli0 : LinearIndependent (v.adicCompletionIntegers F) b0 :=
    bM.linearIndependent.map' M.subtype (Submodule.ker_subtype M)
  have hli : LinearIndependent (Fv F v) b0 :=
    (LinearIndependent.iff_fractionRing (v.adicCompletionIntegers F) (Fv F v)).1 hli0
  have hmem : ∀ x, x ∈ M ↔ ∃ c : Fin (Module.finrank (v.adicCompletionIntegers F) M) → v.adicCompletionIntegers F,
      x = ∑ i, (c i : Fv F v) • b0 i := by
    intro x
    constructor
    · intro hx
      refine ⟨fun i => bM.repr ⟨x, hx⟩ i, ?_⟩
      have h := congrArg Subtype.val (bM.sum_repr ⟨x, hx⟩)
      rw [Submodule.coe_sum] at h
      exact h.symm.trans (Finset.sum_congr rfl fun i _ => rfl)
    · rintro ⟨c, rfl⟩
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem M (c i) (bM i).2
  have hsp : ⊤ ≤ Submodule.span (Fv F v) (Set.range b0) := by
    have hM0 : ∀ x ∈ M, x ∈ Submodule.span (Fv F v) (Set.range b0) := by
      intro x hx
      obtain ⟨c, rfl⟩ := (hmem x).1 hx
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    intro x _
    induction x using TensorProduct.induction_on with
    | zero => exact Submodule.zero_mem _
    | tmul c e =>
      have hal : IsAlgebraic ℤ e := IsFractionRing.isAlgebraic_iff ℤ ℚ E |>.mpr (.of_finite ℚ e)
      obtain ⟨m, hm0, hI⟩ := hal.exists_integral_multiple
      have hmF : (m : Fv F v) ≠ 0 := by
        rw [← map_intCast (algebraMap F (Fv F v))]
        exact (map_ne_zero _).2 (Int.cast_ne_zero.2 hm0)
      have e2 : inclR (F := F) (Fv F v) (m • e) = (m : Fv F v) • inclR (F := F) (Fv F v) e := by
        rw [map_zsmul, Int.cast_smul_eq_zsmul]
      have e3 : c ⊗ₜ[F] e = c • inclR (F := F) (Fv F v) e := by
        simp [inclR, TensorProduct.smul_tmul']
      have e1 : c ⊗ₜ[F] e = (c * (m : Fv F v)⁻¹) • inclR (F := F) (Fv F v) ((⟨m • e, hI⟩ : 𝓞 E) : E) := by
        show _ = (c * (m : Fv F v)⁻¹) • inclR (F := F) (Fv F v) (m • e)
        rw [e2, smul_smul, mul_assoc, inv_mul_cancel₀ hmF, mul_one, e3]
      rw [e1]
      exact Submodule.smul_mem _ _ (hM0 _ (b_inclR_mem (F := F) (E := E) v ⟨m • e, hI⟩))
    | add x y hx hy => exact Submodule.add_mem _ (hx trivial) (hy trivial)
  have hrk : Module.finrank (v.adicCompletionIntegers F) M = Module.finrank F E := by
    have h1 := Module.finrank_eq_card_basis (Module.Basis.mk hli hsp)
    rw [Fintype.card_fin] at h1
    rw [← h1, Module.finrank_baseChange]
  refine ⟨fun i => b0 (Fin.cast hrk.symm i), ?_, fun x => ?_⟩
  · exact hli.comp _ (Fin.cast_injective _)
  · rw [show x ∈ OEv (E := E) v ↔ x ∈ M from Iff.rfl, hmem]
    constructor
    · rintro ⟨c, rfl⟩
      refine ⟨fun i => c (Fin.cast hrk.symm i), ?_⟩
      exact (Fintype.sum_equiv (finCongr hrk) _ _ (fun i => rfl))
    · rintro ⟨c, rfl⟩
      refine ⟨fun i => c (Fin.cast hrk i), ?_⟩
      exact Fintype.sum_equiv (finCongr hrk.symm) _ _ (fun i => by simp)

end PI.OmLocU.SdB
end
end

noncomputable section

namespace PI.OmLocU.SdB

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain PI.OmLocU PI.VolStabSW
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F))

def hd {a : ℕ} (i : Fin a) : HermR (Fv F v) σ a :=
  ⟨Matrix.single i i 1, fun p q => by
    rw [Matrix.single_apply, Matrix.single_apply, apply_ite (sigR (Fv F v) σ), map_one, map_zero]
    exact if_congr and_comm rfl rfl⟩

theorem hm_apply_ne {a : ℕ} (hinv : ∀ y, σ (σ y) = y) {k l i j : Fin a} (c : Fv F v ⊗[F] E)
    (h1 : ¬(k = i ∧ l = j)) (h2 : ¬(l = i ∧ k = j)) :
    (hm σ v hinv k l c : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j = 0 := by
  show (Matrix.single k l c + Matrix.single l k (sigR (Fv F v) σ c)) i j = 0
  rw [Matrix.add_apply, Matrix.single_apply, Matrix.single_apply, if_neg h1, if_neg h2, add_zero]

theorem hd_apply_ne {a : ℕ} {k i j : Fin a} (h : ¬(k = i ∧ k = j)) :
    (hd σ v k : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j = 0 := by
  show Matrix.single k k (1 : Fv F v ⊗[F] E) i j = 0
  rw [Matrix.single_apply, if_neg h]

def hb {a : ℕ} (hinv : ∀ y, σ (σ y) = y) (β : Fin 2 → Fv F v ⊗[F] E) (p : Fin a × Fin a) : HermR (Fv F v) σ a :=
  if p.1 < p.2 then hm σ v hinv p.1 p.2 (β 0) else if p.2 < p.1 then hm σ v hinv p.2 p.1 (β 1) else hd σ v p.1

theorem hb_zero {a : ℕ} (hinv : ∀ y, σ (σ y) = y) (β : Fin 2 → Fv F v ⊗[F] E) {p : Fin a × Fin a} {i j : Fin a}
    (hp1 : p ≠ (i, j)) (hp2 : p ≠ (j, i)) : (hb σ v hinv β p : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j = 0 := by
  obtain ⟨k, l⟩ := p
  unfold hb
  dsimp only
  split_ifs with hkl hlk
  · exact hm_apply_ne σ v hinv _ (fun e => hp1 (Prod.ext e.1 e.2)) (fun e => hp2 (Prod.ext e.2 e.1))
  · exact hm_apply_ne σ v hinv _ (fun e => hp2 (Prod.ext e.2 e.1)) (fun e => hp1 (Prod.ext e.1 e.2))
  · have hkl' : k = l := le_antisymm (not_lt.1 hlk) (not_lt.1 hkl)
    subst hkl'
    exact hd_apply_ne σ v (fun e => hp1 (Prod.ext e.1 e.2))

theorem hermitian_basis_above_first {a : ℕ} (hinv : ∀ y, σ (σ y) = y) (β : Fin 2 → Fv F v ⊗[F] E) {i j : Fin a} (h : i < j) :
    (hb σ v hinv β (i, j) : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j = β 0 := by
  unfold hb
  rw [if_pos h]
  show (Matrix.single i j (β 0) + Matrix.single j i (sigR (Fv F v) σ (β 0))) i j = β 0
  rw [Matrix.add_apply, Matrix.single_apply, Matrix.single_apply, if_pos ⟨rfl, rfl⟩,
    if_neg (fun e => h.ne e.2), add_zero]

theorem hermitian_basis_above_second {a : ℕ} (hinv : ∀ y, σ (σ y) = y) (β : Fin 2 → Fv F v ⊗[F] E) {i j : Fin a} (h : i < j) :
    (hb σ v hinv β (j, i) : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j = β 1 := by
  unfold hb
  rw [if_neg (not_lt.2 h.le), if_pos h]
  show (Matrix.single i j (β 1) + Matrix.single j i (sigR (Fv F v) σ (β 1))) i j = β 1
  rw [Matrix.add_apply, Matrix.single_apply, Matrix.single_apply, if_pos ⟨rfl, rfl⟩,
    if_neg (fun e => h.ne e.2), add_zero]

theorem hermitian_basis_below_first {a : ℕ} (hinv : ∀ y, σ (σ y) = y) (β : Fin 2 → Fv F v ⊗[F] E) {i j : Fin a} (h : j < i) :
    (hb σ v hinv β (i, j) : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j = sigR (Fv F v) σ (β 1) := by
  unfold hb
  rw [if_neg (not_lt.2 h.le), if_pos h]
  show (Matrix.single j i (β 1) + Matrix.single i j (sigR (Fv F v) σ (β 1))) i j = sigR (Fv F v) σ (β 1)
  rw [Matrix.add_apply, Matrix.single_apply, Matrix.single_apply, if_neg (fun e => h.ne e.1),
    if_pos ⟨rfl, rfl⟩, zero_add]

theorem hermitian_basis_below_second {a : ℕ} (hinv : ∀ y, σ (σ y) = y) (β : Fin 2 → Fv F v ⊗[F] E) {i j : Fin a} (h : j < i) :
    (hb σ v hinv β (j, i) : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j = sigR (Fv F v) σ (β 0) := by
  unfold hb
  rw [if_pos h]
  show (Matrix.single j i (β 0) + Matrix.single i j (sigR (Fv F v) σ (β 0))) i j = sigR (Fv F v) σ (β 0)
  rw [Matrix.add_apply, Matrix.single_apply, Matrix.single_apply, if_neg (fun e => h.ne e.1),
    if_pos ⟨rfl, rfl⟩, zero_add]

theorem hb_eq {a : ℕ} (hinv : ∀ y, σ (σ y) = y) (β : Fin 2 → Fv F v ⊗[F] E) (i : Fin a) :
    (hb σ v hinv β (i, i) : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i i = 1 := by
  unfold hb
  rw [if_neg (lt_irrefl i), if_neg (lt_irrefl i)]
  show Matrix.single i i (1 : Fv F v ⊗[F] E) i i = 1
  rw [Matrix.single_apply, if_pos ⟨rfl, rfl⟩]

theorem coe_sum_hb {a : ℕ} (hinv : ∀ y, σ (σ y) = y) (β : Fin 2 → Fv F v ⊗[F] E) (c : Fin a × Fin a → Fv F v)
    (i j : Fin a) :
    ((∑ p, c p • hb σ v hinv β p : HermR (Fv F v) σ a) : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j =
      ∑ p, c p • (hb σ v hinv β p : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j := by
  rw [AddSubmonoidClass.coe_finsetSum, Matrix.sum_apply]
  rfl

theorem sum_lt {a : ℕ} (hinv : ∀ y, σ (σ y) = y) (β : Fin 2 → Fv F v ⊗[F] E) (c : Fin a × Fin a → Fv F v)
    {i j : Fin a} (h : i < j) :
    ((∑ p, c p • hb σ v hinv β p : HermR (Fv F v) σ a) : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j =
      c (i, j) • β 0 + c (j, i) • β 1 := by
  have hne : ((i, j) : Fin a × Fin a) ≠ (j, i) := fun e => h.ne (Prod.ext_iff.1 e).1
  rw [coe_sum_hb, Fintype.sum_eq_add (i, j) (j, i) hne
    (fun p hp => by rw [hb_zero σ v hinv β hp.1 hp.2, smul_zero]), hermitian_basis_above_first σ v hinv β h, hermitian_basis_above_second σ v hinv β h]

theorem sum_gt {a : ℕ} (hinv : ∀ y, σ (σ y) = y) (β : Fin 2 → Fv F v ⊗[F] E) (c : Fin a × Fin a → Fv F v)
    {i j : Fin a} (h : j < i) :
    ((∑ p, c p • hb σ v hinv β p : HermR (Fv F v) σ a) : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j =
      c (i, j) • sigR (Fv F v) σ (β 1) + c (j, i) • sigR (Fv F v) σ (β 0) := by
  have hne : ((i, j) : Fin a × Fin a) ≠ (j, i) := fun e => h.ne' (Prod.ext_iff.1 e).1
  rw [coe_sum_hb, Fintype.sum_eq_add (i, j) (j, i) hne
    (fun p hp => by rw [hb_zero σ v hinv β hp.1 hp.2, smul_zero]), hermitian_basis_below_first σ v hinv β h, hermitian_basis_below_second σ v hinv β h]

theorem sum_diag {a : ℕ} (hinv : ∀ y, σ (σ y) = y) (β : Fin 2 → Fv F v ⊗[F] E) (c : Fin a × Fin a → Fv F v)
    (i : Fin a) :
    ((∑ p, c p • hb σ v hinv β p : HermR (Fv F v) σ a) : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i i =
      sc (E := E) v (c (i, i)) := by
  rw [coe_sum_hb, Fintype.sum_eq_single (i, i) (fun p hp => by rw [hb_zero σ v hinv β hp hp, smul_zero]),
    hb_eq, sc, Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

end PI.OmLocU.SdB
end
end

noncomputable section

namespace PI.OmLocU.SdB

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain PI.OmLocU PI.VolStabSW
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F))

theorem oEv_basis2 (hfin : Module.finrank F E = 2) : ∃ β : Fin 2 → Fv F v ⊗[F] E, LinearIndependent (Fv F v) β ∧
    ∀ x, x ∈ OEv (E := E) v ↔ ∃ c : Fin 2 → v.adicCompletionIntegers F, x = ∑ i, (c i : Fv F v) • β i := by
  have h := oEv_basis (E := E) v
  rw [hfin] at h
  exact h

theorem sigR_smulF (c : Fv F v) (x : Fv F v ⊗[F] E) : sigR (Fv F v) σ (c • x) = c • sigR (Fv F v) σ x := by
  induction x using TensorProduct.induction_on with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | tmul a b => simp [sigR, TensorProduct.smul_tmul']
  | add x y hx hy => rw [smul_add, map_add (f := _), map_add (f := _), hx, hy, smul_add]

theorem hb_li {a : ℕ} (hinv : ∀ y, σ (σ y) = y) (β : Fin 2 → Fv F v ⊗[F] E) (hβ : LinearIndependent (Fv F v) β) :
    LinearIndependent (Fv F v) (hb σ v hinv β (a := a)) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc p
  have hent : ∀ i j, ((∑ p, c p • hb σ v hinv β p : HermR (Fv F v) σ a) :
      Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j = 0 := by
    intro i j
    rw [hc]
    rfl
  have hβ2 := Fintype.linearIndependent_iff.1 hβ
  obtain ⟨i, j⟩ := p
  rcases lt_trichotomy i j with h | rfl | h
  · have h1 := hent i j
    rw [sum_lt σ v hinv β c h] at h1
    have h0 := hβ2 ![c (i, j), c (j, i)] (by simpa [Fin.sum_univ_two] using h1)
    simpa using h0 0
  · have h1 := hent i i
    rw [sum_diag σ v hinv β c i, b_sc_eq] at h1
    exact (map_eq_zero_iff _ (algebraMap (Fv F v) (Fv F v ⊗[F] E)).injective).1 h1
  · have h1 := hent j i
    rw [sum_lt σ v hinv β c h] at h1
    have h0 := hβ2 ![c (j, i), c (i, j)] (by simpa [Fin.sum_univ_two] using h1)
    simpa using h0 1

theorem fix_int' (hcm : IsCMExt F E σ) {t : Fv F v ⊗[F] E} (ht : t ∈ OEv (E := E) v)
    (hf : sigR (Fv F v) σ t = t) : ∃ r ∈ v.adicCompletionIntegers F, t = sc (E := E) v r := by
  have hinv := b_sig_sig σ hcm
  have hnt := b_sig_nt σ hcm
  have hfin := hcm.2.2.1
  set r : Fv F v := algebraMap F (Fv F v) (1 / 2) * Algebra.trace (Fv F v) (Fv F v ⊗[F] E) t with hr
  have hsc : sc (E := E) v r = t := by
    calc sc (E := E) v r
        = algebraMap (Fv F v) (Fv F v ⊗[F] E) (algebraMap F (Fv F v) (1 / 2)) * (t + t) := by
          rw [b_sc_eq, hr, map_mul, trace_v v σ hinv hnt hfin, hf]
      _ = algebraMap (Fv F v) (Fv F v ⊗[F] E) (algebraMap F (Fv F v) (1 / 2) * 2) * t := by
          rw [map_mul, map_ofNat, mul_assoc, two_mul]
      _ = t := by rw [half_two, map_one, one_mul]
  refine ⟨r, b_int_of_sc v (hsc ▸ ht), hsc.symm⟩

theorem hb_mem {a : ℕ} (hcm : IsCMExt F E σ) (β : Fin 2 → Fv F v ⊗[F] E)
    (hβ : ∀ x, x ∈ OEv (E := E) v ↔ ∃ c : Fin 2 → v.adicCompletionIntegers F, x = ∑ i, (c i : Fv F v) • β i)
    (T : HermR (Fv F v) σ a) :
    T ∈ HO σ v a ↔ ∃ c : Fin a × Fin a → v.adicCompletionIntegers F,
      T = ∑ p, (c p : Fv F v) • hb σ v (b_sig_sig σ hcm) β p := by
  have hinv := b_sig_sig σ hcm
  constructor
  · intro hT
    have hT' : ∀ i j, (T : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j ∈ OEv (E := E) v := hT
    have hH : ∀ i j, sigR (Fv F v) σ ((T : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) j i) =
        (T : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j := fun i j => T.2 i j
    choose d hd using fun i j => (hβ _).1 (hT' i j)
    choose r hr hrT using fun i => fix_int' σ v hcm (hT' i i) (hH i i)
    refine ⟨fun p => if p.1 < p.2 then d p.1 p.2 0 else if p.2 < p.1 then d p.2 p.1 1 else ⟨r p.1, hr p.1⟩, ?_⟩
    apply Subtype.ext
    ext i j
    rcases lt_trichotomy i j with h | rfl | h
    · rw [sum_lt σ v hinv β _ h, hd i j, Fin.sum_univ_two]
      simp [h, not_lt.2 h.le]
    · rw [sum_diag σ v hinv β _ i, hrT i]
      simp
    · rw [sum_gt σ v hinv β _ h, ← hH i j, hd j i, Fin.sum_univ_two, map_add (f := _), sigR_smulF, sigR_smulF, add_comm]
      simp [h, not_lt.2 h.le]
  · rintro ⟨c, rfl⟩
    intro i j
    rcases lt_trichotomy i j with h | rfl | h
    · rw [sum_lt σ v hinv β _ h]
      exact (hβ _).2 ⟨![c (i, j), c (j, i)], by simp [Fin.sum_univ_two]⟩
    · rw [sum_diag σ v hinv β _ i]
      exact b_sc_mem v (c (i, i)).2
    · rw [sum_gt σ v hinv β _ h]
      have hm := b_sigR_mem v σ ((hβ ((c (j, i) : Fv F v) • β 0 + (c (i, j) : Fv F v) • β 1)).2
        ⟨![c (j, i), c (i, j)], by simp [Fin.sum_univ_two]⟩)
      rwa [map_add, sigR_smulF, sigR_smulF, add_comm] at hm

theorem idxPiH_std (a : ℕ) (hS : StdHyp σ J ψ) : IdxPiH σ v a := by
  intro _ ϖ hϖ
  have hcm := hS.1
  obtain ⟨β, hli, hβ⟩ := oEv_basis2 v hcm.2.2.1
  rw [genIdx v (HO σ v a) (hb σ v (b_sig_sig σ hcm) β) (hb_li σ v (b_sig_sig σ hcm) β hli)
    (hb_mem σ v hcm β hβ) ϖ hϖ, qv, Fintype.card_prod, Fintype.card_fin]
  push_cast
  ring

end PI.OmLocU.SdB
