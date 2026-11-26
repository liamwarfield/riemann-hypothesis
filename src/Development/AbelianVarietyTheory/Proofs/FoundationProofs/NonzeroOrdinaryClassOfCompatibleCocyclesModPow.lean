module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsCuspFunctionalValueModPrimePowDiamondIndepende

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemCoefRingInvertPrimeInvOfMemNeZero
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemCoefRingInvertPrimeInvOfMemNeZero
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

noncomputable section

namespace GlobalTheory.Ord2

theorem memE_inv_of_mem : ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (d : Qbar l), d ∈ c.O → d ≠ 0 → MemE c d⁻¹ := by
  intro l _ c d hd hd0
  set x : c.O := ⟨d, hd⟩ with hxdef
  have hx0 : x ≠ 0 := fun h => hd0 (congrArg Subtype.val h)
  set L : c.O := ((l : ℕ) : c.O) with hLdef
  have hLval : (L : Qbar l) = ((l : ℕ) : Qbar l) := by simp [hLdef]
  have hL0 : L ≠ 0 := by
    intro h
    have : ((l : ℕ) : Qbar l) = 0 := by rw [← hLval, h]; rfl
    have h1 := (norm_natCast_l (l := l))
    rw [this, norm_zero] at h1
    have : (0:ℝ) < (l:ℝ)⁻¹ := inv_pos.2 (by exact_mod_cast (Fact.out : l.Prime).pos)
    linarith
  have hLnu : ¬ IsUnit L := by
    rintro ⟨u, hu⟩
    have h1 : ((u : c.O) : Qbar l) * ((u⁻¹ : c.Oˣ) : c.O) = 1 := by
      rw [← Subalgebra.coe_mul, Units.mul_inv]; rfl
    have hn2 : ‖(((u⁻¹ : c.Oˣ) : c.O) : Qbar l)‖ ≤ 1 := norm_le_one_of_mem_coef c (SetLike.coe_mem _)
    have hu' : ((u : c.O) : Qbar l) = ((l : ℕ) : Qbar l) := by rw [hu, hLval]
    rw [hu'] at h1
    have h2 := congrArg norm h1
    rw [norm_mul, norm_one] at h2
    have h3 := norm_natCast_l_lt_one (l := l)
    have h4 : ‖((l : ℕ) : Qbar l)‖ * ‖(((u⁻¹ : c.Oˣ) : c.O) : Qbar l)‖ < 1 :=
      lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) hn2) h3
    linarith
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible c.O
  obtain ⟨v, u, hxu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0 hϖ
  obtain ⟨m, u', hLu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hL0 hϖ
  have hm : m ≠ 0 := by
    rintro rfl
    apply hLnu
    rw [hLu, pow_zero, mul_one]; exact u'.isUnit
  have hϖL : ϖ ∣ L := by
    rw [hLu]
    exact Dvd.dvd.mul_left (dvd_pow_self ϖ hm) _
  have hdiv : x ∣ L ^ v := by
    rw [hxu]
    exact (Units.mul_left_dvd).2 (pow_dvd_pow_of_dvd hϖL v)
  obtain ⟨q, hq⟩ := hdiv
  refine ⟨v, ?_⟩
  have hq' : ((l : ℕ) : Qbar l) ^ v = d * (q : Qbar l) := by
    have := congrArg (fun y : c.O => (y : Qbar l)) hq
    simpa [hLval, hxdef] using this
  rw [hq', mul_comm d, mul_assoc, mul_inv_cancel₀ hd0, mul_one]
  exact q.2

end GlobalTheory.Ord2

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemCoefRingInvertPrimeInvOfMemNeZeroStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.memCoefRingInvertPrime_inv_of_mem_ne_zero : ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (d : Qbar l), d ∈ c.O → d ≠ 0 → MemE c d⁻¹ := by
  first | exact @GlobalTheory.Ord2.memE_inv_of_mem | exact GlobalTheory.Ord2.memE_inv_of_mem | (intros; apply GlobalTheory.Ord2.memE_inv_of_mem <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LimitOfApproximateCocycles
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LimitOfApproximateCocycles
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2

theorem qbarLVectorCongruent_integralMatrix_mulVec {l : ℕ} [Fact l.Prime] (c : Coef l) (M : Matrix (Fin 2) (Fin 2) (Qbar l))
    (hM : ∀ i j, M i j ∈ c.O) {n : ℕ} {v w : Fin 2 → Qbar l} (h : Cv n v w) :
    Cv n (M *ᵥ v) (M *ᵥ w) := by
  intro i
  unfold Cg
  have e : (M *ᵥ v) i - (M *ᵥ w) i = M i 0 * (v 0 - w 0) + M i 1 * (v 1 - w 1) := by
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]; ring
  rw [e]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (norm_le_one_of_mem_coef c (hM i 0))).trans (h 0)
  · rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (norm_le_one_of_mem_coef c (hM i 1))).trans (h 1)

theorem limit_cocycle_mem_cocycles : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : R2 Ω l) (c : Coef l), (∀ s i j, mat W s i j ∈ c.O) → ∀ (a : ℕ → G ℚ Ω → Fin 2 → Qbar l) (z : G ℚ Ω → Fin 2 → Qbar l), (∀ n s t, Cv n (a n (s * t)) (a n s + mat W s *ᵥ a n t)) → (∀ n s, ∀ᶠ t in nhds s, Cv n (a n t) (a n s)) → (∀ n s, Cv n (z s) (a n s)) → z ∈ Z1 (Loc.colRep W) := by
  intro l _ Ω _ _ W c hW a z hco hloc hz
  rw [mem_Z1_iff_cocycle]
  refine ⟨?_, ?_⟩
  · refine continuous_pi fun i => ?_
    refine continuous_iff_continuousAt.2 fun s => ?_
    have key : Filter.Tendsto (fun t => z t i) (nhds s) (@nhds (Qbar l) UniformSpace.toTopologicalSpace (z s i)) := by
      rw [Metric.tendsto_nhds]
      intro ε hε
      obtain ⟨n, hn⟩ := (tendsto_norm_l_pow (l := l)).eventually (gt_mem_nhds hε) |>.exists
      filter_upwards [hloc n s] with t ht
      have h1 : Cg n (z t i) (z s i) :=
        cg_trans (hz n t i) (cg_trans (ht i) (cg_symm (hz n s i)))
      rw [dist_eq_norm]
      exact lt_of_le_of_lt h1 hn
    exact key
  · intro s t
    have hcol : ∀ v, (Loc.colRep W s) v = mat W s *ᵥ v := by
      intro v; simp [Loc.colRep, Matrix.toLin'_apply]
    rw [hcol]
    funext i
    refine eq_of_forall_cg fun n => ?_
    have hA : Cv n (z (s * t)) (a n (s * t)) := hz n (s * t)
    have hB := hco n s t
    have hC : Cv n (a n s + mat W s *ᵥ a n t) (z s + mat W s *ᵥ z t) := by
      intro j
      have h2 := qbarLVectorCongruent_integralMatrix_mulVec c (mat W s) (hW s) (cv_symm (hz n t)) j
      have h3 := cg_symm (hz n s j)
      unfold Cg at h2 h3 ⊢
      have e : (a n s + mat W s *ᵥ a n t) j - (z s + mat W s *ᵥ z t) j
          = (a n s j - z s j) + ((mat W s *ᵥ a n t) j - (mat W s *ᵥ z t) j) := by
        simp only [Pi.add_apply]; ring
      rw [e]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h3 h2)
    exact (cv_trans hA (cv_trans hB hC)) i

end GlobalTheory.Ord2
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LimitOfApproximateCocyclesStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.limit_of_approximate_cocycles : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : R2 Ω l) (c : Coef l), (∀ s i j, mat W s i j ∈ c.O) → ∀ (a : ℕ → G ℚ Ω → Fin 2 → Qbar l) (z : G ℚ Ω → Fin 2 → Qbar l), (∀ n s t, Cv n (a n (s * t)) (a n s + mat W s *ᵥ a n t)) → (∀ n s, ∀ᶠ t in nhds s, Cv n (a n t) (a n s)) → (∀ n s, Cv n (z s) (a n s)) → z ∈ Z1 (Loc.colRep W) := by
  first | exact @GlobalTheory.Ord2.limit_cocycle_mem_cocycles | exact GlobalTheory.Ord2.limit_cocycle_mem_cocycles | (intros; apply GlobalTheory.Ord2.limit_cocycle_mem_cocycles <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDotProductEqOfPrimePowApproxQbarL
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDotProductEqOfPrimePowApproxQbarL
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory

theorem exists_dotProduct_eq_of_approx_pow {K : Type*} [NormedField K] (r : ℝ) (hr0 : 0 ≤ r)
    (hr1 : r < 1) (X : Type*) (m : ℕ) (M : X → Fin m → K) (z : X → K)
    (h : ∀ n : ℕ, ∃ y : Fin m → K, ∀ x, ‖z x - M x ⬝ᵥ y‖ ≤ r ^ n) :
    ∃ y : Fin m → K, ∀ x, z x = M x ⬝ᵥ y := by
  classical
  let T : (X →₀ K) →ₗ[K] (Fin m → K) := Finsupp.linearCombination K M
  let φ : Module.Dual K (X →₀ K) := Finsupp.linearCombination K z
  have hker : φ ∈ (LinearMap.ker T).dualAnnihilator := by
    rw [Submodule.mem_dualAnnihilator]
    intro c hc
    have hc' : ∑ x ∈ c.support, c x • M x = 0 := by
      simpa [T, Finsupp.linearCombination_apply, Finsupp.sum] using hc
    have hφ : φ c = ∑ x ∈ c.support, c x * z x := by
      simp [φ, Finsupp.linearCombination_apply, Finsupp.sum]
    have hb : ∀ n : ℕ, ‖φ c‖ ≤ (∑ x ∈ c.support, ‖c x‖) * r ^ n := by
      intro n
      obtain ⟨y, hy⟩ := h n
      have h0 : ∑ x ∈ c.support, c x * (M x ⬝ᵥ y) = 0 := by
        have := congrArg (· ⬝ᵥ y) hc'
        simpa [sum_dotProduct, smul_dotProduct] using this
      have : φ c = ∑ x ∈ c.support, c x * (z x - M x ⬝ᵥ y) := by
        simp only [mul_sub, Finset.sum_sub_distrib, h0, sub_zero, hφ]
      rw [this, Finset.sum_mul]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => ?_)
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hy x) (norm_nonneg _)
    have hlim : Filter.Tendsto (fun n : ℕ => (∑ x ∈ c.support, ‖c x‖) * r ^ n) Filter.atTop
        (nhds 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).const_mul
        (∑ x ∈ c.support, ‖c x‖)
    exact norm_le_zero_iff.mp (ge_of_tendsto' hlim hb)
  rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker] at hker
  obtain ⟨g, hg⟩ := hker
  refine ⟨fun i => g (fun j => if i = j then 1 else 0), fun x => ?_⟩
  have h1 := congrArg (fun f : Module.Dual K (X →₀ K) => f (Finsupp.single x 1)) hg
  simp only [LinearMap.dualMap_apply, T, φ, Finsupp.linearCombination_single, one_smul,
    smul_eq_mul, one_mul] at h1
  rw [← h1, LinearMap.pi_apply_eq_sum_univ g (M x)]
  simp [dotProduct]

theorem exists_dotProduct_eq_of_approx_prime_pow :
    ∀ (l : ℕ) [Fact l.Prime] (X : Type) (m : ℕ) (M : X → Fin m → Qbar l) (z : X → Qbar l), (∀ n : ℕ, ∃ y : Fin m → Qbar l, ∀ x, ‖z x - M x ⬝ᵥ y‖ ≤ ‖((l : ℕ) : Qbar l) ^ n‖) → ∃ y : Fin m → Qbar l, ∀ x, z x = M x ⬝ᵥ y := by
  intro l _ X m M z h
  have hl : ‖((l : ℕ) : Qbar l)‖ < 1 := by
    have e : ((l : ℕ) : Qbar l) = algebraMap ℚ_[l] (Qbar l) (l : ℚ_[l]) := by simp
    rw [e, norm_algebraMap']
    exact Padic.norm_p_lt_one
  refine exists_dotProduct_eq_of_approx_pow _ (norm_nonneg _) hl X m M z fun n => ?_
  simpa only [norm_pow] using h n

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDotProductEqOfPrimePowApproxQbarLStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dotProduct_eq_of_primePow_approx_qbarL : ∀ (l : ℕ) [Fact l.Prime] (X : Type) (m : ℕ) (M : X → Fin m → Qbar l) (z : X → Qbar l), (∀ n : ℕ, ∃ y : Fin m → Qbar l, ∀ x, ‖z x - M x ⬝ᵥ y‖ ≤ ‖((l : ℕ) : Qbar l) ^ n‖) → ∃ y : Fin m → Qbar l, ∀ x, z x = M x ⬝ᵥ y := by
  first | exact @GlobalTheory.exists_dotProduct_eq_of_approx_prime_pow | exact GlobalTheory.exists_dotProduct_eq_of_approx_prime_pow | (intros; apply GlobalTheory.exists_dotProduct_eq_of_approx_prime_pow <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NonzeroOrdinaryClassOfCompatibleCocyclesModPow
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2

theorem limit_nonzero_ordinary_class : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l) (c : Coef l), Continuous W → (∀ s i j, mat W s i j ∈ c.O) → (∃ g, (mat W g - 1).det ≠ 0) → ∀ (a : ℕ → G ℚ Ω → Fin 2 → Qbar l) (N : ℕ), (∀ n s i, a n s i ∈ c.O) → (∀ n s t, Cv n (a n (s * t)) (a n s + mat W s *ᵥ a n t)) → (∀ n s, ∀ᶠ t in nhds s, Cv n (a n t) (a n s)) → (∀ n s, Cv n (a (n + 1) s) (a n s)) → (∀ n, ∀ b ∈ (toGS Ω (S : Set Pl)).ker, Cv n (a n b) 0) → (∀ n, ∀ q ∈ S, ((l : ℕ) : 𝓞 ℚ) ∉ q.asIdeal → ∀ B : ValuationSubring Ω, IsPlaceOver B q → ∃ y : Fin 2 → Qbar l, VecE c y ∧ ∀ s ∈ Ine (F := ℚ) B, Cv n (a n s) (mat W s *ᵥ y - y)) → (∀ n, ∃ y : Qbar l, MemE c y ∧ ∀ s ∈ Dec (F := ℚ) A, Cg n (a n s 1) (mat W s 1 1 * y - y)) → (¬ ∃ y : Fin 2 → Qbar l, VecE c y ∧ ∀ s, Cv N (a N s) (mat W s *ᵥ y - y)) → ¬ GrZero W A := by
  intro l _ Ω _ _ _ S A W c hWc hWint hg a N ha hcoc hloc hstep hker hine hdec hN hGZ
  obtain ⟨z0, hz0O, hz0⟩ := GlobalTheory.T.exists_integral_limit_compatible_modPrimePow l c (G ℚ Ω × Fin 2) (fun n p => a n p.1 p.2) (fun n p => ha n p.1 p.2)
    (fun n p => hstep n p.1 p.2)
  let z : G ℚ Ω → Fin 2 → Qbar l := fun s i => z0 (s, i)
  have hzO : ∀ s i, z s i ∈ c.O := fun s i => hz0O (s, i)
  have hza : ∀ n s, Cv n (z s) (a n s) := fun n s i => hz0 n (s, i)
  have hZ : z ∈ Z1 (Loc.colRep W) := GlobalTheory.T.limit_of_approximate_cocycles l Ω W c hWint a z hcoc hloc hza
  have hcol : ∀ s (v : Fin 2 → Qbar l), Loc.colRep W s v = mat W s *ᵥ v := fun s v => by
    simp [Loc.colRep, Matrix.toLin'_apply]
  have hrow : ∀ s (y : Fin 2 → Qbar l) i, (fun j => (mat W s - 1) i j) ⬝ᵥ y = (mat W s *ᵥ y - y) i := by
    intro s y i
    show ((mat W s - 1) *ᵥ y) i = _
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
  have hzker : ∀ b ∈ (toGS Ω (S : Set Pl)).ker, z b = 0 := by
    intro b hb
    funext i
    refine eq_zero_of_forall_norm_le _ fun n => ?_
    have h := cg_trans (hza n b i) (hker n b hb i)
    simp only [Cg, Pi.zero_apply, sub_zero] at h
    exact h
  have hexact : ∀ H : Subgroup (G ℚ Ω), (∀ n, ∃ y : Fin 2 → Qbar l, ∀ s ∈ H, Cv n (a n s) (mat W s *ᵥ y - y)) →
      ∃ x : Fin 2 → Qbar l, ∀ s ∈ H, z s = mat W s *ᵥ x - x := by
    intro H hH
    obtain ⟨x, hx⟩ := GlobalTheory.T.exists_dotProduct_eq_of_primePow_approx_qbarL l (↥H × Fin 2) 2 (fun p j => (mat W p.1 - 1) p.2 j) (fun p => z p.1 p.2) (fun n => by
      obtain ⟨y, hy⟩ := hH n
      refine ⟨y, fun p => ?_⟩
      have h := cg_trans (hza n p.1 p.2) (hy p.1 p.1.2 p.2)
      rw [← hrow] at h
      exact h)
    exact ⟨x, fun s hs => funext fun i => by rw [← hrow]; exact hx (⟨s, hs⟩, i)⟩
  have hUnr : Unr W z := by
    intro w hw
    refine ⟨placeOf Ω w, isPlaceOver_placeOf Ω w, ?_⟩
    by_cases hwS : w ∈ S
    · exact hexact (Ine (F := ℚ) (placeOf Ω w)) fun n => by
        obtain ⟨y, -, hy⟩ := hine n w hwS hw _ (isPlaceOver_placeOf Ω w)
        exact ⟨y, hy⟩
    · refine ⟨0, fun s hs => ?_⟩
      have hsN : s ∈ (toGS Ω (S : Set Pl)).ker := by
        show s ∈ (QuotientGroup.mk' (NS Ω (S : Set Pl))).ker
        rw [QuotientGroup.ker_mk']
        apply Subgroup.le_topologicalClosure
        apply Subgroup.subset_normalClosure
        simp only [Set.mem_iUnion]
        exact ⟨w, by simpa using hwS, placeOf Ω w, isPlaceOver_placeOf Ω w, hs⟩
      rw [hzker s hsN]
      simp
  have hGr : Gr W A z := by
    obtain ⟨y, hy⟩ := GlobalTheory.T.exists_dotProduct_eq_of_primePow_approx_qbarL l (↥(Dec (F := ℚ) A)) 1 (fun s _ => mat W s 1 1 - 1) (fun s => z s 1) (fun n => by
      obtain ⟨y, -, hy⟩ := hdec n
      refine ⟨fun _ => y, fun s => ?_⟩
      have h := cg_trans (hza n s 1) (hy s s.2)
      have e : (fun _ : Fin 1 => mat W s 1 1 - 1) ⬝ᵥ (fun _ => y) = mat W s 1 1 * y - y := by
        simp [dotProduct]; ring
      rw [e]; exact h)
    refine ⟨y 0, fun s hs => ?_⟩
    have h := hy ⟨s, hs⟩
    rw [h]
    simp [dotProduct]
    ring
  obtain ⟨x, hx⟩ := (mem_coboundaries1 _ _).1 (hGZ z hZ hUnr hGr)
  obtain ⟨g, hdg⟩ := hg
  have hMO : ∀ i j, (mat W g - 1) i j ∈ c.O := by
    intro i j
    rw [Matrix.sub_apply, Matrix.one_apply]
    split_ifs
    · exact c.O.sub_mem (hWint g i j) c.O.one_mem
    · exact c.O.sub_mem (hWint g i j) c.O.zero_mem
  have hdO : (mat W g - 1).det ∈ c.O := by
    rw [Matrix.det_fin_two]
    exact c.O.sub_mem (c.O.mul_mem (hMO 0 0) (hMO 1 1)) (c.O.mul_mem (hMO 0 1) (hMO 1 0))
  have hadjO : ∀ i j, (mat W g - 1).adjugate i j ∈ c.O := by
    intro i j
    rw [Matrix.adjugate_fin_two]
    fin_cases i <;> fin_cases j
    · exact hMO 1 1
    · exact c.O.neg_mem (hMO 0 1)
    · exact c.O.neg_mem (hMO 1 0)
    · exact hMO 0 0
  have hMx : (mat W g - 1) *ᵥ x = z g := by rw [hx g, hcol, Matrix.sub_mulVec, Matrix.one_mulVec]
  have hdx : (mat W g - 1).det • x = (mat W g - 1).adjugate *ᵥ z g := by
    rw [← hMx, Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
  obtain ⟨k, hk⟩ := GlobalTheory.T.memCoefRingInvertPrime_inv_of_mem_ne_zero l c _ hdO hdg
  have hxE : VecE c x := ⟨k, fun i => by
    have e : x i = ((mat W g - 1).det)⁻¹ * ((mat W g - 1).adjugate *ᵥ z g) i := by
      rw [← hdx, Pi.smul_apply, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hdg, one_mul]
    rw [e, ← mul_assoc]
    refine c.O.mul_mem hk ?_
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    exact c.O.add_mem (c.O.mul_mem (hadjO i 0) (hzO g 0)) (c.O.mul_mem (hadjO i 1) (hzO g 1))⟩
  refine hN ⟨x, hxE, fun s => ?_⟩
  have h := hza N s
  rw [hx s, hcol] at h
  exact cv_symm h

end GlobalTheory.Ord2

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NonzeroOrdinaryClassOfCompatibleCocyclesModPowStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonzero_ordinary_class_of_compatible_cocycles_mod_pow : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l) (c : Coef l), Continuous W → (∀ s i j, mat W s i j ∈ c.O) → (∃ g, (mat W g - 1).det ≠ 0) → ∀ (a : ℕ → G ℚ Ω → Fin 2 → Qbar l) (N : ℕ), (∀ n s i, a n s i ∈ c.O) → (∀ n s t, Cv n (a n (s * t)) (a n s + mat W s *ᵥ a n t)) → (∀ n s, ∀ᶠ t in nhds s, Cv n (a n t) (a n s)) → (∀ n s, Cv n (a (n + 1) s) (a n s)) → (∀ n, ∀ b ∈ (toGS Ω (S : Set Pl)).ker, Cv n (a n b) 0) → (∀ n, ∀ q ∈ S, ((l : ℕ) : 𝓞 ℚ) ∉ q.asIdeal → ∀ B : ValuationSubring Ω, IsPlaceOver B q → ∃ y : Fin 2 → Qbar l, VecE c y ∧ ∀ s ∈ Ine (F := ℚ) B, Cv n (a n s) (mat W s *ᵥ y - y)) → (∀ n, ∃ y : Qbar l, MemE c y ∧ ∀ s ∈ Dec (F := ℚ) A, Cg n (a n s 1) (mat W s 1 1 * y - y)) → (¬ ∃ y : Fin 2 → Qbar l, VecE c y ∧ ∀ s, Cv N (a N s) (mat W s *ᵥ y - y)) → ¬ GrZero W A := by
  first | exact @GlobalTheory.Ord2.limit_nonzero_ordinary_class | exact GlobalTheory.Ord2.limit_nonzero_ordinary_class | (intros; apply GlobalTheory.Ord2.limit_nonzero_ordinary_class <;> assumption)
end
