module

public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CmBaseThetaTensorPowerTranslatesIntegral
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.IntWAPlaces
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.IntEasy
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.IntPull

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TranslateNormalizedVectorIntegralCombTensorPower
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TranslateNormalizedVectorIntegralCombTensorPower
noncomputable section

namespace GlobalTheory.MomN

open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity Formalism.L2.KerInert Formalism.L2.KerInert.ISd

theorem transl_normVec_int : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → ∀ χ : IdE D → ℂ, IsChi D χ → ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), admitted D N N' L L' → EqAt D p (StandardLatticesGL3.stdL D N) L → EqAt D p (StandardLatticesGL3.stdL D N') L' → ∀ t : VC D N N', TorsPrime D p (La D B.tor L L') t → ∃ (m : ℕ) (c : Fin m → ℂ) (s : Fin m → VC D N N'), (∀ k, c k ∈ Qbar ∧ IsIntP (lamC lam (c k))) ∧ (∀ k, TorsPrime D p (La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N')) (s k)) ∧ U D B.tor t (B.eNat χ N N' L L') = fun z => ∑ k, c k * U D B.tor (s k) (B.thZero N N') z := by
  intro D cc δ B hcc hδ χ hχ p _ lam N N' M M' hAdm hM hM' t ht
  obtain ⟨s, hs, hsM, hMs⟩ := hM
  obtain ⟨s', hs', hsM', hMs'⟩ := hM'
  have hp : p.Prime := Fact.out
  have spos : 0 < s := Nat.pos_of_ne_zero (by rintro rfl; exact hp.one_lt.ne' (Nat.coprime_zero_left p |>.mp hs))
  have spos' : 0 < s' := Nat.pos_of_ne_zero (by rintro rfl; exact hp.one_lt.ne' (Nat.coprime_zero_left p |>.mp hs'))
  set La0 := La D (tor0 D cc δ) (Formalism.MainNotions.StandardLatticesGL3.stdL D N) (Formalism.MainNotions.StandardLatticesGL3.stdL D N') with hLa0
  set La1 := La D (tor0 D cc δ) M (Formalism.MainNotions.StandardLatticesGL3.stdL D N') with hLa1
  set La2 := La D (tor0 D cc δ) M M' with hLa2
  have one_std : ∀ y ∈ Formalism.MainNotions.StandardLatticesGL3.stdL D N', ((1 : ℕ) : D.host.E) • y ∈ Formalism.MainNotions.StandardLatticesGL3.stdL D N' := by
    intro y hy; simpa using hy
  have one_M : ∀ y ∈ M, ((1 : ℕ) : D.host.E) • y ∈ M := by
    intro y hy; simpa using hy
  have k10 : ∀ z ∈ La1, (s * 1) • z ∈ La0 := fun z hz => La_smul cc δ s 1 hsM one_std hz
  have k21 : ∀ z ∈ La2, (1 * s') • z ∈ La1 := fun z hz => La_smul cc δ 1 s' one_M hMs' hz
  have k20 : ∀ z ∈ La2, (s * s') • z ∈ La0 := fun z hz => La_smul cc δ s s' hsM hMs' hz
  have k12 : ∀ z ∈ La1, (1 * s') • z ∈ La2 := fun z hz => La_smul cc δ 1 s' one_M hsM' hz
  have hδ0 : δ ≠ 0 := delta_nonzero_link D cc hcc δ hδ
  have hI : IO.HfInt (tor0 D cc δ) La2 := hermitian_form_integral_values D cc hcc δ hδ hδ0 N N' M M' hAdm

  let Q2 : VC D N N' → Prop := fun y => ∃ n : ℕ, 0 < n ∧ n • y ∈ La2
  have q2_add : ∀ x y, Q2 x → Q2 y → Q2 (x + y) := by
    rintro x y ⟨n, hn, hx⟩ ⟨m, hm, hy⟩
    refine ⟨n * m, Nat.mul_pos hn hm, ?_⟩
    have e : (n * m) • (x + y) = m • (n • x) + n • (m • y) := by
      rw [smul_add, smul_smul, smul_smul, mul_comm m n]
    rw [e]
    exact add_mem (AddSubgroup.nsmul_mem _ hx m) (AddSubgroup.nsmul_mem _ hy n)
  have q2_2 : ∀ x ∈ La2, Q2 x := fun x hx => ⟨1, one_pos, by simpa using hx⟩
  have q2_1 : ∀ x ∈ La1, Q2 x := fun x hx => ⟨1 * s', by omega, k12 x hx⟩
  have cf_good : ∀ x y, Q2 x → Q2 y → Good lam (IO.cf (tor0 D cc δ) x y) := by
    rintro x y ⟨n, hn, hx⟩ ⟨m, hm, hy⟩
    obtain ⟨q, hq⟩ := im_rat (tor0 D cc δ) hI hn hm hx hy
    exact good_cf lam _ x y q hq

  have R1 : Rep lam B.tor (fun y => y ∈ La1) (B.thHalf N N' M) (B.thZero N N') := by
    show Rep lam B.tor (fun y => y ∈ La1) (Iop D B.tor La0 La1 (B.thZero N N')) (B.thZero N N')
    refine rep_Iop (Pt := fun y => y = 0) (rep_self rfl) ?_ ?_
    · rintro x hx y rfl
      exact ⟨cf_good x 0 (q2_1 x hx) (q2_2 0 (zero_mem _)), by simpa using hx⟩
    · exact idx_coprime La0 La1 (s * 1) (by simpa using hs) k10

  have R2 : Rep lam B.tor (fun y => ∃ a ∈ La2, ∃ b ∈ La1, y = a + b) (B.thMoved N N' M M') (B.thZero N N') := by
    show Rep lam B.tor _ (Iop D B.tor La1 La2 (B.thHalf N N' M)) (B.thZero N N')
    refine rep_Iop R1 ?_ ?_
    · intro x hx y hy
      exact ⟨cf_good x y (q2_2 x hx) (q2_1 y hy), x, hx, y, hy, rfl⟩
    · exact idx_coprime La1 La2 (1 * s') (by simpa using hs') k21

  obtain ⟨n, hn, hnp, hnt⟩ := ht
  have R3 : Rep lam B.tor (TorsPrime D p La0) (U D B.tor t (B.thMoved N N' M M')) (B.thZero N N') := by
    refine rep_U t R2 ?_
    rintro y ⟨a, ha, b, hb, rfl⟩
    refine ⟨cf_good t _ ⟨n, hn, hnt⟩ (q2_add a b (q2_2 a ha) (q2_1 b hb)), ?_⟩
    refine ⟨n * (s * s'), Nat.mul_pos hn (Nat.mul_pos spos spos'), Nat.Coprime.mul_left hnp (Nat.Coprime.mul_left hs hs'), ?_⟩
    have e : (n * (s * s')) • (t + (a + b)) = (s * s') • (n • t) + (n • ((s * s') • a) + (n * s') • ((s * 1) • b)) := by
      simp only [smul_add, smul_smul]
      congr 1
      · rw [mul_comm]
      · congr 1
        rw [mul_one, mul_assoc, mul_comm s' s]
    rw [e]
    exact add_mem (k20 _ hnt) (add_mem (AddSubgroup.nsmul_mem _ (k20 a ha) n)
      (AddSubgroup.nsmul_mem _ (k10 b hb) (n * s')))

  have hchi := RestC.chiFacUnit (D := D) χ hχ p lam N N' M M' hAdm ⟨s, hs, hsM, hMs⟩ ⟨s', hs', hsM', hMs'⟩
  have hgood : Good lam (Base.chiFac χ N N' M M') := ⟨hchi.1, le_of_eq hchi.2⟩
  have R4 := rep_smul hgood R3
  have e : U D B.tor t (B.eNat χ N N' M M') = fun z => Base.chiFac χ N N' M M' * U D B.tor t (B.thMoved N N' M M') z := by
    funext z
    exact IO.U_smul _ t _ _ z
  rw [e]
  obtain ⟨m, c, s₀, hc, hs₀, hF⟩ := R4
  exact ⟨m, c, s₀, hc, hs₀, hF⟩

end GlobalTheory.MomN
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TranslateNormalizedVectorIntegralCombTensorPowerStatement
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.translate_normalized_vector_integral_comb_tensor_power : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → ∀ χ : IdE D → ℂ, IsChi D χ → ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), admitted D N N' L L' → EqAt D p (StandardLatticesGL3.stdL D N) L → EqAt D p (StandardLatticesGL3.stdL D N') L' → ∀ t : VC D N N', TorsPrime D p (La D B.tor L L') t → ∃ (m : ℕ) (c : Fin m → ℂ) (s : Fin m → VC D N N'), (∀ k, c k ∈ Qbar ∧ IsIntP (lamC lam (c k))) ∧ (∀ k, TorsPrime D p (La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N')) (s k)) ∧ U D B.tor t (B.eNat χ N N' L L') = fun z => ∑ k, c k * U D B.tor (s k) (B.thZero N N') z := by
  first | exact @GlobalTheory.MomN.transl_normVec_int | exact GlobalTheory.MomN.transl_normVec_int | (intros; apply GlobalTheory.MomN.transl_normVec_int <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WeakApproximationUnitaryLatticesSplitPrime
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WeakApproximationUnitaryLatticesSplitPrime
noncomputable section

namespace GlobalTheory.MomN

open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN

theorem weakApprox_split : ∀ (D : D7) (p : ℕ) [Fact p.Prime], p ≠ 2 → jacobiSym (-(D.host.d : ℤ)) p = 1 → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), admitted D N N' L L' → letI := D.host.cmStar; ∃ (γ : Matrix.unitaryGroup (Fin N) D.host.E) (γ' : Matrix.unitaryGroup (Fin N') D.host.E) (M : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (M' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), admitted D N N' M M' ∧ EqAt D p (StandardLatticesGL3.stdL D N) M ∧ EqAt D p (StandardLatticesGL3.stdL D N') M' ∧ L = SDLat.smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) M ∧ L' = SDLat.smulLat (γ' : Matrix (Fin N') (Fin N') D.host.E) M' := by
  intro D p _ _ _ N N' L L' hAdm
  let _ := D.host.cmStar
  obtain ⟨hN, hN', hL, hL'⟩ := hAdm
  have hCM : PI.UG.IsCMUnram D.host.E := D.sp.cm.cmUnram
  have hp : p.Prime := Fact.out
  obtain ⟨γ, M, hM, hEq, hLM⟩ := Formalism.L2.KerInert.wa_main Formalism.L2.KerInert.weak_approximation_places hCM p hp N L hL
  obtain ⟨γ', M', hM', hEq', hLM'⟩ := Formalism.L2.KerInert.wa_main Formalism.L2.KerInert.weak_approximation_places hCM p hp N' L' hL'
  exact ⟨γ, γ', M, M', ⟨hN, hN', hM, hM'⟩, hEq, hEq', hLM, hLM'⟩

end GlobalTheory.MomN
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WeakApproximationUnitaryLatticesSplitPrimeStatement
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weakApproximation_unitaryLattices_splitPrime : ∀ (D : D7) (p : ℕ) [Fact p.Prime], p ≠ 2 → jacobiSym (-(D.host.d : ℤ)) p = 1 → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), admitted D N N' L L' → letI := D.host.cmStar; ∃ (γ : Matrix.unitaryGroup (Fin N) D.host.E) (γ' : Matrix.unitaryGroup (Fin N') D.host.E) (M : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (M' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), admitted D N N' M M' ∧ EqAt D p (StandardLatticesGL3.stdL D N) M ∧ EqAt D p (StandardLatticesGL3.stdL D N') M' ∧ L = SDLat.smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) M ∧ L' = SDLat.smulLat (γ' : Matrix (Fin N') (Fin N') D.host.E) M' := by
  first | exact @GlobalTheory.MomN.weakApprox_split | exact GlobalTheory.MomN.weakApprox_split | (intros; apply GlobalTheory.MomN.weakApprox_split <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnitaryPairPullbackLatticesTranslates
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnitaryPairPullbackLatticesTranslates
noncomputable section

open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN

namespace GlobalTheory.MomPull

variable {D : D7} {N N' : ℕ}

def tPullL (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (γ : Matrix (Fin N) (Fin N) D.host.E)
    (γ' : Matrix (Fin N') (Fin N') D.host.E) : VC D N N' →ₗ[ℂ] VC D N N' where
  toFun := Formalism.L2.KerInert.tPull D (tor0 D cc δ) γ γ'
  map_add' := Formalism.L2.KerInert.ie_tPull_add cc δ γ γ'
  map_smul' := Formalism.L2.KerInert.ie_tPull_smul cc δ γ γ'

theorem hf_tPull (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (γ : Matrix (Fin N) (Fin N) D.host.E)
    (γ' : Matrix (Fin N') (Fin N') D.host.E) (hγ : (letI := D.host.cmStar; γ * star γ) = 1)
    (hγ' : (letI := D.host.cmStar; γ' * star γ') = 1) (z w : VC D N N') :
    Hf D (tor0 D cc δ) (Formalism.L2.KerInert.tPull D (tor0 D cc δ) γ γ' z)
      (Formalism.L2.KerInert.tPull D (tor0 D cc δ) γ γ' w) = Hf D (tor0 D cc δ) z w := by
  letI := D.host.cmStar
  unfold Hf
  congr 1
  refine Finset.sum_congr rfl fun τ _ => ?_
  have h1 := Formalism.L2.KerInert.PullbackComparison.map_mul_star D (embT D τ) γ hγ
  have h2 := Formalism.L2.KerInert.PullbackComparison.map_mul_star D (embT D τ) γ' hγ'
  rw [Matrix.star_eq_conjTranspose] at h1 h2
  exact Formalism.L2.KerInert.PullbackComparison.sum_mul_star_conj (γ.map (embT D τ)) (γ'.map (embT D τ)) h1 h2
    (Matrix.of (z τ)) (Matrix.of (w τ))

end GlobalTheory.MomPull


open GlobalTheory.MomPull in
theorem GlobalTheory.MomPull.pull_unitary : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (N N' : ℕ), letI := D.host.cmStar; ∀ (γ : Matrix.unitaryGroup (Fin N) D.host.E) (γ' : Matrix.unitaryGroup (Fin N') D.host.E) (M : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (M' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), ∃ g : VC D N N' →L[ℂ] VC D N N', (∀ x ∈ La D (tor0 D cc δ) (SDLat.smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) M) (SDLat.smulLat (γ' : Matrix (Fin N') (Fin N') D.host.E) M'), g x ∈ La D (tor0 D cc δ) M M') ∧ ∀ (t : VC D N N') (G : VC D N N' → ℂ), U D (tor0 D cc δ) t (pull D (tor0 D cc δ) (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E) G) = fun z => U D (tor0 D cc δ) (g t) G (g z) := by
  intro D cc δ N N'
  letI := D.host.cmStar
  intro γ γ' M M'
  have h1' : star (γ' : Matrix (Fin N') (Fin N') D.host.E) * γ' = 1 := Matrix.mem_unitaryGroup_iff'.mp γ'.2
  have hγ : (γ : Matrix (Fin N) (Fin N) D.host.E) * star (γ : Matrix (Fin N) (Fin N) D.host.E) = 1 :=
    Matrix.mem_unitaryGroup_iff.mp γ.2
  have hγ' : (γ' : Matrix (Fin N') (Fin N') D.host.E) * star (γ' : Matrix (Fin N') (Fin N') D.host.E) = 1 :=
    Matrix.mem_unitaryGroup_iff.mp γ'.2
  refine ⟨LinearMap.toContinuousLinearMap (tPullL cc δ (γ : Matrix (Fin N) (Fin N) D.host.E)
    (γ' : Matrix (Fin N') (Fin N') D.host.E)), fun x hx => ?_, fun t G => ?_⟩
  · have h := Formalism.L2.KerInert.ie_La_pull cc δ _ _ h1' M M' hx
    exact h
  · funext z
    show G (Formalism.L2.KerInert.tPull D (tor0 D cc δ) (γ : Matrix (Fin N) (Fin N) D.host.E)
        (γ' : Matrix (Fin N') (Fin N') D.host.E) (z + t)) * _ =
      G (Formalism.L2.KerInert.tPull D (tor0 D cc δ) (γ : Matrix (Fin N) (Fin N) D.host.E)
        (γ' : Matrix (Fin N') (Fin N') D.host.E) z + Formalism.L2.KerInert.tPull D (tor0 D cc δ)
        (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E) t) * _
    have e : ∀ y, (LinearMap.toContinuousLinearMap (tPullL cc δ (γ : Matrix (Fin N) (Fin N) D.host.E)
        (γ' : Matrix (Fin N') (Fin N') D.host.E))) y = Formalism.L2.KerInert.tPull D (tor0 D cc δ)
        (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E) y := fun _ => rfl
    simp only [e]
    rw [hf_tPull cc δ _ _ hγ hγ', hf_tPull cc δ _ _ hγ hγ', Formalism.L2.KerInert.ie_tPull_add]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnitaryPairPullbackLatticesTranslatesStatement
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryPairPullback_lattices_translates : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (N N' : ℕ), letI := D.host.cmStar; ∀ (γ : Matrix.unitaryGroup (Fin N) D.host.E) (γ' : Matrix.unitaryGroup (Fin N') D.host.E) (M : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (M' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), ∃ g : VC D N N' →L[ℂ] VC D N N', (∀ x ∈ La D (tor0 D cc δ) (SDLat.smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) M) (SDLat.smulLat (γ' : Matrix (Fin N') (Fin N') D.host.E) M'), g x ∈ La D (tor0 D cc δ) M M') ∧ ∀ (t : VC D N N') (G : VC D N N' → ℂ), U D (tor0 D cc δ) t (pull D (tor0 D cc δ) (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E) G) = fun z => U D (tor0 D cc δ) (g t) G (g z) := by
  first | exact @GlobalTheory.MomPull.pull_unitary | exact GlobalTheory.MomPull.pull_unitary | (intros; apply GlobalTheory.MomPull.pull_unitary <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormalizedVectorTranslatesPrimeOrderIntegral
noncomputable section

open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN

namespace GlobalTheory.MomN

theorem contDiff_U {D : D7} {N N' : ℕ} (T : Tor D) (t : VC D N N') {G : VC D N N' → ℂ} (hG : ContDiff ℂ ⊤ G) :
    ContDiff ℂ ⊤ (U D T t G) := by
  have hH : ContDiff ℂ ⊤ fun z : VC D N N' => Hf D T z t := by
    unfold Hf
    refine ContDiff.div_const ?_ _
    refine ContDiff.sum fun τ _ => ContDiff.sum fun i _ => ContDiff.sum fun j _ => ?_
    refine ContDiff.mul ?_ contDiff_const
    fun_prop
  unfold U
  refine ContDiff.mul (hG.comp (contDiff_id.add contDiff_const)) ?_
  exact ContDiff.cexp ((contDiff_const.mul hH).sub contDiff_const)

theorem transPrime_int : (∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : IdE D → ℂ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → IsChi D χ → B.EqP χ) → ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → ∀ (q : ℕ) [Fact q.Prime], q ≠ 2 → jacobiSym (-(D.host.d : ℤ)) q = 1 → Nat.Coprime (Ideal.absNorm cc) q → ∀ (ι : ℂ ≃+* ℂ_[q]) (δ₀ : ℂ) (θ : ℂ → ℂ) (Ω : ℂ_[q]), Per D.host.d ι δ₀ θ Ω → ∀ χ : IdE D → ℂ, IsChi D χ → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), admitted D N N' L L' → ∀ t : VC D N N', TorsPrime D q (La D B.tor L L') t → LatInt ι (Ω / ι δ₀) (La D B.tor L L') (U D B.tor t (B.eNat χ N N' L L')) := by
  intro hEq D cc δ B hcc hδ q _ hq2 hsplit hcop ι δ₀ θ Ω hPer χ hχ N N' L L' hA t ht
  letI := D.host.cmStar
  obtain ⟨γ, γ', M, M', hAM, hE, hE', rfl, rfl⟩ := GlobalTheory.T.weakApproximation_unitaryLattices_splitPrime D q hq2 hsplit N N' L L' hA
  obtain ⟨hN, hN', hSM, hSM'⟩ := id hAM
  have hcov : pull D B.tor (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E)
      (B.eNat χ N N' M M') =
      B.eNat χ N N' (SDLat.smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) M)
        (SDLat.smulLat (γ' : Matrix (Fin N') (Fin N') D.host.E) M') :=
    (hEq D cc δ B χ hcc hδ hχ).1 N N' ⟨M, hSM⟩ ⟨M', hSM'⟩ hN hN' γ γ'
  obtain ⟨g, hg, hU⟩ := GlobalTheory.T.unitaryPairPullback_lattices_translates D cc δ N N' γ γ' M M'
  have ht' : TorsPrime D q (La D B.tor M M') (g t) := by
    obtain ⟨n, hn, hc, hm⟩ := ht
    refine ⟨n, hn, hc, ?_⟩
    have := hg _ hm
    rwa [map_nsmul] at this
  let lam : Qbar →+* ℂ_[q] := (ι : ℂ →+* ℂ_[q]).comp (algebraMap Qbar ℂ)
  obtain ⟨m, c, s, hc, hs, heq⟩ :=
    GlobalTheory.T.translate_normalized_vector_integral_comb_tensor_power D cc δ B hcc hδ χ hχ q lam N N' M M' hAM hE hE' (g t) ht'
  have hzero : ∀ k, LatInt ι (Ω / ι δ₀) (La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N'))
      (U D B.tor (s k) (B.thZero N N')) := fun k =>
    GlobalTheory.T.cm_base_theta_tensor_power_translates_integral D cc δ B hcc hδ q hq2 hsplit hcop ι δ₀ θ Ω hPer N N' (s k) (hs k)
  have hd : ContDiff ℂ ⊤ (B.thZero N N') :=
    AnalyticOnNhd.contDiff (B.thZeroMem (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.stdOK B hcc hδ) N N').1
  have hsm : ∀ k, ContDiff ℂ ⊤ (U D B.tor (s k) (B.thZero N N')) := fun k => contDiff_U _ _ hd
  have hcn : ∀ k, ‖ι (c k)‖ ≤ 1 := by
    intro k
    obtain ⟨h1, h2⟩ := hc k
    have e : lamC lam (c k) = ι (c k) := by
      unfold lamC
      rw [dite_eq_left h1]
      rfl
    rw [← e]
    exact h2
  have hsum := (GlobalTheory.T.latticeJetsAreBoundedMoments_prod_and_sum q ι (VC D N N') (Ω / ι δ₀) (La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N'))).2
    (Fin m) Finset.univ c (fun k => U D B.tor (s k) (B.thZero N N')) (fun k _ => hsm k) (fun k _ => hcn k)
    (fun k _ => hzero k)
  have hGs : ContDiff ℂ ⊤ fun z => ∑ k, c k * U D B.tor (s k) (B.thZero N N') z :=
    ContDiff.sum fun k _ => contDiff_const.mul (hsm k)
  obtain ⟨a, ha, hsM, hMs⟩ := hE
  obtain ⟨b, hb, hsM', hMs'⟩ := hE'
  have hpull := GlobalTheory.T.latticeJetsAreBoundedMoments_pullback q ι (VC D N N') (VC D N N') (Ω / ι δ₀)
    (La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N'))
    (La D B.tor (SDLat.smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) M)
      (SDLat.smulLat (γ' : Matrix (Fin N') (Fin N') D.host.E) M')) g _ hGs
    (fun x hx => ⟨a * b, Nat.Coprime.mul_left ha hb,
      Formalism.L2.KerInert.ISd.La_smul cc δ a b hsM hMs' (hg x hx)⟩) hsum
  rw [← hcov, show U D B.tor t (pull D B.tor (γ : Matrix (Fin N) (Fin N) D.host.E)
      (γ' : Matrix (Fin N') (Fin N') D.host.E) (B.eNat χ N N' M M')) =
      fun z => U D B.tor (g t) (B.eNat χ N N' M M') (g z) from hU t _, heq]
  exact hpull

end GlobalTheory.MomN
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormalizedVectorTranslatesPrimeOrderIntegralStatement
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalizedVector_translates_prime_order_integral : (∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : IdE D → ℂ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → IsChi D χ → B.EqP χ) → ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → ∀ (q : ℕ) [Fact q.Prime], q ≠ 2 → jacobiSym (-(D.host.d : ℤ)) q = 1 → Nat.Coprime (Ideal.absNorm cc) q → ∀ (ι : ℂ ≃+* ℂ_[q]) (δ₀ : ℂ) (θ : ℂ → ℂ) (Ω : ℂ_[q]), Per D.host.d ι δ₀ θ Ω → ∀ χ : IdE D → ℂ, IsChi D χ → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), admitted D N N' L L' → ∀ t : VC D N N', TorsPrime D q (La D B.tor L L') t → LatInt ι (Ω / ι δ₀) (La D B.tor L L') (U D B.tor t (B.eNat χ N N' L L')) := by
  first | exact @GlobalTheory.MomN.transPrime_int | exact GlobalTheory.MomN.transPrime_int | (intros; apply GlobalTheory.MomN.transPrime_int <;> assumption)
end
