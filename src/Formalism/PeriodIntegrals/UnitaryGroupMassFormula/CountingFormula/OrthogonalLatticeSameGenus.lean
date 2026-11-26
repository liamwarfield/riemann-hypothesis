module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.DifferentIdealPowers

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.OrthogonalLatticeSameGenus
open NumberField Module
open Classical

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.RowsMassW

open Formalism.HermitianLattices.Ext.L3

section Glue

variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {V1 : Type} [AddCommGroup V1] [Module K V1] [Module (𝓞 K) V1] [IsScalarTower (𝓞 K) K V1]

def wPerp (h1 : V1 →ₗ⋆[K] V1 →ₗ[K] K) (z : V1) : Submodule K V1 := LinearMap.ker (h1 z)

def hPerp (h1 : V1 →ₗ⋆[K] V1 →ₗ[K] K) (z : V1) : wPerp h1 z →ₗ⋆[K] wPerp h1 z →ₗ[K] K :=
  (h1.compl₂ (wPerp h1 z).subtype).comp (wPerp h1 z).subtype

def l0 (h1 : V1 →ₗ⋆[K] V1 →ₗ[K] K) (z : V1) (M : Submodule (𝓞 K) V1) : Submodule (𝓞 K) (wPerp h1 z) :=
  M.comap ((wPerp h1 z).subtype.restrictScalars (𝓞 K))

def IsGlueLat (h1 : V1 →ₗ⋆[K] V1 →ₗ[K] K) (z : V1) (M : Submodule (𝓞 K) V1) : Prop :=
  Submodule.IsLattice K M ∧ Formalism.HermitianLatticesTheory.IsUnimodular h1 M ∧ z ∈ M ∧
    ∀ c : K, c • z ∈ M → ∃ o : 𝓞 K, (o : K) = c

def hz (h1 : V1 →ₗ⋆[K] V1 →ₗ[K] K) (z : V1) : Set (V1 ≃ₗ[K] V1) :=
  {σ | σ ∈ Formalism.HermitianLatticesTheory.isom h1 ∧ σ z = z}

def stabZ (h1 : V1 →ₗ⋆[K] V1 →ₗ[K] K) (z : V1) (M : Submodule (𝓞 K) V1) : Set (V1 ≃ₗ[K] V1) :=
  {σ | σ ∈ hz h1 z ∧ Formalism.HermitianLatticesTheory.gmap σ M = M}

def IsHzReps (h1 : V1 →ₗ⋆[K] V1 →ₗ[K] K) (z : V1) (s : Finset (Submodule (𝓞 K) V1)) : Prop :=
  (∀ M ∈ s, IsGlueLat h1 z M) ∧
    ∀ M, IsGlueLat h1 z M → ∃! M', M' ∈ s ∧ ∃ σ ∈ hz h1 z, Formalism.HermitianLatticesTheory.gmap σ M' = M

end Glue

def GlueHyp (K F : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    {V1 : Type} [AddCommGroup V1] [Module K V1] [Module (𝓞 K) V1] [IsScalarTower (𝓞 K) K V1]
    (h1 : V1 →ₗ⋆[K] V1 →ₗ[K] K) (z : V1) (t : ℕ) : Prop :=
  Formalism.HermitianLatticesTheory.IsCMUnram K ∧ IsFixF K F ∧ h1.IsSymm ∧ h1 z z = -((t : ℕ) : K) ∧ 0 < t ∧
    IsTotPosDef (hPerp h1 z)

end PI.UnitaryGroupMassFormula.CntFormula.RowsMassW
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.JordanExists
open NumberField Module IsDedekindDomain Formalism.L2.SG.Pf.Cnt
open Classical

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.R6

open Formalism.HermitianLattices.Ext.L3

def JordanExists : Prop :=
  ∀ (K F V ι : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι]
    [DecidableEq ι]
    (h : V →ₗ⋆[K] V →ₗ[K] K) (X : Submodule K V) (x : ι → V)
    (𝔞 : ι → FractionalIdeal (nonZeroDivisors (𝓞 K)) K),
    Formalism.HermitianLatticesTheory.IsCMUnram K → IsFixF K F → Module.finrank F K = 2 → h.IsSymm →
    (∀ i, ∀ a ∈ (𝔞 i : Submodule (𝓞 K) K), star a ∈ (𝔞 i : Submodule (𝓞 K) K)) → (∀ i, 𝔞 i ≠ 0) →
    LinearIndependent K x → Submodule.span K (Set.range x) = X → (gram h x).det ≠ 0 →
    Formalism.HermitianLatticesTheory.IsIntegralLat h (pbLat x 𝔞) →
    ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → ∃ b a, IsJordanIn h X (pbLat x 𝔞) 𝔭 b a

def DetLocal : Prop :=
  ∀ (K F V ι : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]
    (h : V →ₗ⋆[K] V →ₗ[K] K) (X : Submodule K V) (x : ι → V)
    (𝔞 : ι → FractionalIdeal (nonZeroDivisors (𝓞 K)) K), IsFixF K F →
    (∀ i, ∀ a ∈ (𝔞 i : Submodule (𝓞 K) K), star a ∈ (𝔞 i : Submodule (𝓞 K) K)) → (∀ i, 𝔞 i ≠ 0) →
    LinearIndependent K x → Submodule.span K (Set.range x) = X → (gram h x).det ≠ 0 →
    ∀ (𝔭 : Ideal (𝓞 F)) (b : Fin (finrank K X) → V) (a : Fin (finrank K X) → 𝓞 F), 𝔭.IsMaximal →
      IsJordanIn h X (pbLat x 𝔞) 𝔭 b a →
      ∀ P : HeightOneSpectrum (𝓞 K), P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 K)) = 𝔭 →
        FractionalIdeal.count K P ((∏ i, 𝔞 i ^ 2) *
            FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (gram h x).det) =
          FractionalIdeal.count K P
            (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (algebraMap F K (∏ j, ((a j : 𝓞 F) : F))))

def CountExt : Prop :=
  ∀ (K F : Type) [Field K] [NumberField K] [Field F] [NumberField F] [Algebra F K] (n : ℕ)
    (𝔭 : Ideal (𝓞 F)) (P : HeightOneSpectrum (𝓞 K)) (α : Fin n → 𝓞 F), 𝔭.IsMaximal →
    P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 K)) = 𝔭 → (∀ j, α j ≠ 0) →
    FractionalIdeal.count K P
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (algebraMap F K (∏ j, ((α j : 𝓞 F) : F)))) =
      ((P.asIdeal.ramificationIdx (𝓞 F) * ∑ j, vF 𝔭 (α j) : ℕ) : ℤ)

def NormAssembly : Prop :=
  ∀ (K F : Type) [Field K] [NumberField K] [Field F] [NumberField F] [Algebra F K],
    Module.finrank F K = 2 →
    ∀ (J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) (w : Ideal (𝓞 F) → ℕ), J ≠ 0 →
    (∀ (𝔭 : Ideal (𝓞 F)) (P : HeightOneSpectrum (𝓞 K)), 𝔭.IsMaximal →
      P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 K)) = 𝔭 →
        FractionalIdeal.count K P J = ((P.asIdeal.ramificationIdx (𝓞 F) * w 𝔭 : ℕ) : ℤ)) →
    (∏' 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, (Ideal.absNorm 𝔭.1 : ℝ) ^ w 𝔭.1) ^ 2 =
      (FractionalIdeal.absNorm J : ℝ)

end PI.UnitaryGroupMassFormula.CntFormula.R6
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.AbsNormSpanNatCast
open NumberField Module
open Classical

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.RowsMassW

open Formalism.HermitianLattices.Ext.L3

section Arith

variable {F : Type} [Field F] [NumberField F]

def nfT (F : Type) [Field F] [NumberField F] (T : ℕ) : Multiset (Ideal (𝓞 F)) :=
  UniqueFactorizationMonoid.normalizedFactors (Ideal.span {((T : ℕ) : 𝓞 F)})

def supT (F : Type) [Field F] [NumberField F] (T : ℕ) : Finset {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} :=
  (nfT F T).toFinset.subtype (fun 𝔭 => 𝔭.IsMaximal)

theorem span_natCast_ne_bot {T : ℕ} (hT : 0 < T) : Ideal.span {((T : ℕ) : 𝓞 F)} ≠ ⊥ := by
  rw [Ne, Ideal.span_singleton_eq_bot]
  exact_mod_cast hT.ne'

theorem mem_nfT_iff {T : ℕ} (hT : 0 < T) (P : Ideal (𝓞 F)) :
    P ∈ nfT F T ↔ P.IsPrime ∧ ((T : ℕ) : 𝓞 F) ∈ P := by
  unfold nfT
  rw [Ideal.mem_normalizedFactors_iff (span_natCast_ne_bot hT), Ideal.span_singleton_le_iff_mem]

theorem isMaximal_of_mem_nfT {T : ℕ} (hT : 0 < T) {P : Ideal (𝓞 F)} (h : P ∈ nfT F T) :
    P.IsMaximal := by
  obtain ⟨hP, hm⟩ := (mem_nfT_iff hT P).1 h
  refine hP.isMaximal ?_
  rintro rfl
  rw [Ideal.mem_bot] at hm
  exact (Nat.cast_ne_zero.2 hT.ne') hm

theorem mem_supT {T : ℕ} (hT : 0 < T) (𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}) :
    𝔭 ∈ supT F T ↔ ((T : ℕ) : 𝓞 F) ∈ 𝔭.1 := by
  unfold supT
  rw [Finset.mem_subtype, Multiset.mem_toFinset, mem_nfT_iff hT]
  exact ⟨fun h => h.2, fun h => ⟨𝔭.2.isPrime, h⟩⟩

theorem tprod_supT {T : ℕ} (hT : 0 < T) (g : Ideal (𝓞 F) → ℝ) :
    (∏' 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, (if ((T : ℕ) : 𝓞 F) ∈ 𝔭.1 then g 𝔭.1 else 1)) =
      ∏ P ∈ (nfT F T).toFinset, g P := by
  rw [tprod_eq_prod (s := supT F T)]
  · unfold supT
    rw [Finset.prod_subtype_eq_prod_filter (f := fun P => if ((T : ℕ) : 𝓞 F) ∈ P then g P else 1)]
    rw [Finset.filter_true_of_mem (fun P hP => isMaximal_of_mem_nfT hT (Multiset.mem_toFinset.1 hP))]
    refine Finset.prod_congr rfl fun P hP => ?_
    rw [if_pos ((mem_nfT_iff hT P).1 (Multiset.mem_toFinset.1 hP)).2]
  · intro 𝔭 h𝔭
    rw [if_neg (fun h => h𝔭 ((mem_supT hT 𝔭).2 h))]

theorem absNorm_span_natCast (T : ℕ) :
    Ideal.absNorm (Ideal.span {((T : ℕ) : 𝓞 F)}) = T ^ finrank ℚ F := by
  rw [Ideal.absNorm_span_singleton]
  have e : ((T : ℕ) : 𝓞 F) = algebraMap ℤ (𝓞 F) (T : ℤ) := by simp
  rw [e, Algebra.norm_algebraMap, RingOfIntegers.rank]
  simp [Int.natAbs_pow]

theorem prod_absNorm_pow {T : ℕ} (hT : 0 < T) :
    ∏ P ∈ (nfT F T).toFinset, (Ideal.absNorm P : ℝ) ^ (vT F T P) = (T : ℝ) ^ finrank ℚ F := by
  have h1 : ∏ P ∈ (nfT F T).toFinset, (Ideal.absNorm P) ^ (Multiset.count P (nfT F T)) =
      ((nfT F T).map Ideal.absNorm).prod := (Finset.prod_multiset_map_count _ _).symm
  have h2 : ((nfT F T).map Ideal.absNorm).prod = Ideal.absNorm (nfT F T).prod :=
    (map_multiset_prod Ideal.absNorm _).symm
  have h3 : (nfT F T).prod = Ideal.span {((T : ℕ) : 𝓞 F)} :=
    Ideal.prod_normalizedFactors_eq_self (span_natCast_ne_bot hT)
  have h4 : ∏ P ∈ (nfT F T).toFinset, (Ideal.absNorm P) ^ (vT F T P) = T ^ finrank ℚ F := by
    have : ∀ P, vT F T P = Multiset.count P (nfT F T) := fun P => rfl
    simp only [this]
    rw [h1, h2, h3, absNorm_span_natCast]
  exact_mod_cast h4

end Arith

end PI.UnitaryGroupMassFormula.CntFormula.RowsMassW
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.DifferentIdealPowersNeZero
open NumberField Module Formalism.MainNotions.S

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.R6

def SStable {K : Type} [Field K] [NumberField K] [StarRing K]
    (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Prop :=
  ∀ a ∈ (I : Submodule (𝓞 K) K), star a ∈ (I : Submodule (𝓞 K) K)

section Generic

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem sStable_one : SStable (1 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) := by
  intro a ha
  rw [FractionalIdeal.mem_coe, FractionalIdeal.mem_one_iff] at ha ⊢
  obtain ⟨x, rfl⟩ := ha
  exact ⟨NumberField.RingOfIntegers.mapRingHom (starRingEnd K) x, rfl⟩

theorem sStable_mul {I J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K} (hI : SStable I) (hJ : SStable J) :
    SStable (I * J) := by
  intro a ha
  rw [FractionalIdeal.coe_mul] at ha ⊢
  refine Submodule.mul_induction_on (C := fun a => star a ∈ (I : Submodule (𝓞 K) K) * J) ha ?_ ?_
  · intro x hx y hy
    rw [star_mul, mul_comm (star y)]
    exact Submodule.mul_mem_mul (hI x hx) (hJ y hy)
  · intro x y hx hy
    rw [star_add]
    exact add_mem hx hy

theorem sStable_pow {I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K} (hI : SStable I) (n : ℕ) :
    SStable (I ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact sStable_one
  | succ n ih => rw [pow_succ]; exact sStable_mul ih hI

theorem sStable_inv {I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K} (hI : SStable I) : SStable I⁻¹ := by
  by_cases h0 : I = 0
  · subst h0
    intro a ha
    rw [FractionalIdeal.inv_zero', FractionalIdeal.coe_zero, Submodule.mem_bot] at ha ⊢
    rw [ha, star_zero]
  · intro a ha
    rw [FractionalIdeal.mem_coe, FractionalIdeal.mem_inv_iff h0] at ha ⊢
    intro y hy
    have h1 : a * star y ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) :=
      ha _ (FractionalIdeal.mem_coe.mp (hI y (FractionalIdeal.mem_coe.mpr hy)))
    have h2 := sStable_one (K := K) _ (FractionalIdeal.mem_coe.mpr h1)
    rw [star_mul, star_star, mul_comm] at h2
    exact FractionalIdeal.mem_coe.mp h2

theorem sStable_zpow {I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K} (hI : SStable I) (n : ℤ) :
    SStable (I ^ n) := by
  cases n with
  | ofNat n => rw [Int.ofNat_eq_coe, zpow_natCast]; exact sStable_pow hI n
  | negSucc n => rw [zpow_negSucc]; exact sStable_inv (sStable_pow hI _)

end Generic

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem sStable_ddS (D : Formalism.BasicNotions.D7) : SStable (ddS D) := by
  intro a ha
  rw [FractionalIdeal.mem_coe] at ha ⊢
  unfold ddS at ha ⊢
  rw [FractionalIdeal.mem_coeIdeal] at ha ⊢
  obtain ⟨y, hy, rfl⟩ := ha

  have hc : (NumberField.RingOfIntegers.mapRingHom (starRingEnd D.host.E)).comp
      (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = algebraMap (𝓞 D.host.F) (𝓞 D.host.E) := by
    ext x
    exact (D.sp.cm.fixed _).2 ⟨(x : D.host.F), rfl⟩
  refine ⟨NumberField.RingOfIntegers.mapRingHom (starRingEnd D.host.E) y, ?_, rfl⟩
  rw [← hc, ← Ideal.map_map]
  exact Ideal.mem_map_of_mem _ hy

theorem ddS_ne_zero' (D : Formalism.BasicNotions.D7) : ddS D ≠ 0 := by
  unfold ddS
  rw [ne_eq, FractionalIdeal.coeIdeal_eq_zero]
  exact Ideal.map_ne_bot_of_ne_bot (differentIdeal_ne_bot)

theorem stable_differentIdealPowers (D : Formalism.BasicNotions.D7) (i : Fin (D.R.rS + 1)) : SStable (differentIdealPowers D i) := by
  induction i using Fin.lastCases with
  | last => unfold differentIdealPowers; rw [Fin.snoc_last]; exact sStable_one
  | cast a => unfold differentIdealPowers; rw [Fin.snoc_castSucc]; exact sStable_zpow (sStable_ddS D) _

theorem differentIdealPowers_ne_zero (D : Formalism.BasicNotions.D7) (i : Fin (D.R.rS + 1)) : differentIdealPowers D i ≠ 0 := by
  induction i using Fin.lastCases with
  | last => unfold differentIdealPowers; rw [Fin.snoc_last]; exact one_ne_zero
  | cast a => unfold differentIdealPowers; rw [Fin.snoc_castSucc]; exact zpow_ne_zero _ (ddS_ne_zero' D)

end PI.UnitaryGroupMassFormula.CntFormula.R6
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.LinearIndependentOfDetGram
open NumberField Module Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal Formalism.L2.SG.Pf.Cnt
open Classical

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.R6

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem gram_comb {K V ι κ : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] [Fintype ι]
    (h : V →ₗ⋆[K] V →ₗ[K] K) (v : ι → V) (A : Matrix ι κ K) (x : κ → V)
    (hx : ∀ j, x j = ∑ i, A i j • v i) : gram h x = A.conjTranspose * gram h v * A := by
  ext i j
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [gram, Matrix.of_apply, hx, Matrix.mul_apply, Matrix.conjTranspose_apply, map_sum,
    LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, map_smul, smul_eq_mul,
    starRingEnd_apply, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

theorem linearIndependent_of_det_gram {K V ι : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
    [Fintype ι] [DecidableEq ι] (h : V →ₗ⋆[K] V →ₗ[K] K) (x : ι → V) (hd : (gram h x).det ≠ 0) :
    LinearIndependent K x := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hv : Matrix.mulVec (gram h x) c = 0 := by
    funext j
    have hj := congrArg (h (x j)) hc
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, smul_eq_mul, map_zero] at hj
    simp only [Matrix.mulVec, dotProduct, gram, Matrix.of_apply, Pi.zero_apply]
    rw [← hj]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have h0 := Matrix.eq_zero_of_mulVec_eq_zero hd hv
  intro i
  exact congrFun h0 i

variable {D : Formalism.BasicNotions.D7}

theorem flag_gram {T : D.host.E} (F : FlagG (VS D) D.R.rS T) (a b : Fin (D.R.rS + 1)) :
    (VS D).hT (F.fvec a) (F.fvec b) = if a = Fin.last D.R.rS ∧ b = Fin.last D.R.rS then -T else 0 := by
  have hs : ∀ x y, (VS D).hT y x = star ((VS D).hT x y) := fun x y => ((VS D).herm.eq x y).symm
  rcases Fin.eq_castSucc_or_eq_last a with ⟨i, rfl⟩ | rfl <;>
    rcases Fin.eq_castSucc_or_eq_last b with ⟨j, rfl⟩ | rfl
  · simp [FlagG.fvec, F.e_iso, Fin.castSucc_ne_last]
  · simp [FlagG.fvec, F.z_orth, Fin.castSucc_ne_last]
  · simp [FlagG.fvec, Fin.castSucc_ne_last]
    rw [hs (F.e j) F.z, F.z_orth j, star_zero]
  · simp [FlagG.fvec, F.z_norm]

theorem gram_pair {T T' : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (F' : LFlag (D.sp.Y 0) D.R.rS T')
    (Z : MatZ D) (hZ : ZhatL (lf D F0) F' = Z) :
    gram (VS D).hT (Sum.elim F0.fvec F'.fl.fvec) = Ga T T' Z := by
  have hs : ∀ x y, (VS D).hT y x = star ((VS D).hT x y) := fun x y => ((VS D).herm.eq x y).symm
  subst hZ
  ext (a | a) (b | b)
  · simp [gram, Ga, flag_gram]
  · simp [gram, Ga, ZhatL, Zhat, brS]
  · simp [gram, Ga, ZhatL, Zhat, brS, Matrix.conjTranspose_apply, hs (F'.fl.fvec a)]
  · simp [gram, Ga, flag_gram]

def flagDifferenceMatrix (D : Formalism.BasicNotions.D7) :
    Matrix (Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) (Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) D.host.E :=
  Matrix.fromBlocks 1 (-(((gS D : D.host.E))⁻¹ • (1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E))) 0
    (((gS D : D.host.E))⁻¹ • (1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E))

theorem flagDifference_comb {T T' : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (F' : LFlag (D.sp.Y 0) D.R.rS T') :
    ∀ j, flagDifferenceVectors D F0 F' j = ∑ i, flagDifferenceMatrix D i j • Sum.elim F0.fvec F'.fl.fvec i := by
  intro j
  rcases j with b | b
  · simp [flagDifferenceVectors, flagDifferenceMatrix, Fintype.sum_sum_type, Matrix.one_apply]
  · simp [flagDifferenceVectors, flagDifferenceMatrix, Fintype.sum_sum_type, Matrix.one_apply, sub_eq_add_neg, add_comm]

theorem det_flagDifference_matrix (D : Formalism.BasicNotions.D7) : (flagDifferenceMatrix D).det = ((gS D : D.host.E))⁻¹ ^ (D.R.rS + 1) := by
  rw [flagDifferenceMatrix, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul, Matrix.det_smul, Matrix.det_one,
    mul_one, Fintype.card_fin]

theorem star_gS (D : Formalism.BasicNotions.D7) : star ((gS D : D.host.E))⁻¹ = ((gS D : D.host.E))⁻¹ := by
  rw [star_inv₀, star_natCast]

theorem det_gram_flagDifference {T T' : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (F' : LFlag (D.sp.Y 0) D.R.rS T')
    (Z : MatZ D) (hZ : ZhatL (lf D F0) F' = Z) :
    (gram (VS D).hT (flagDifferenceVectors D F0 F')).det = ((gS D : D.host.E))⁻¹ ^ (2 * (D.R.rS + 1)) * (Ga T T' Z).det := by
  rw [gram_comb (VS D).hT _ (flagDifferenceMatrix D) _ (flagDifference_comb F0 F'), gram_pair F0 F' Z hZ, Matrix.det_mul,
    Matrix.det_mul, Matrix.det_conjTranspose, det_flagDifference_matrix, star_pow, star_gS]
  ring

theorem span_flagDifferenceBasis {T T' : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (F' : LFlag (D.sp.Y 0) D.R.rS T') :
    Submodule.span D.host.E (Set.range (flagDifferenceVectors D F0 F')) = UPair D F0 F' := by
  have hg : ((gS D : D.host.E)) ≠ 0 := by
    have h0 := (D.host.g_prime 0).ne_zero
    have h1 := (D.host.g_prime 1).ne_zero
    rw [gS]
    exact_mod_cast mul_ne_zero h0 h1
  unfold UPair
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    rcases j with b | b
    · exact Submodule.subset_span (Or.inl ⟨b, rfl⟩)
    · simp only [flagDifferenceVectors, Sum.elim_inr]
      exact Submodule.smul_mem _ _ (Submodule.sub_mem _
        (Submodule.subset_span (Or.inr ⟨b, rfl⟩)) (Submodule.subset_span (Or.inl ⟨b, rfl⟩)))
  · rw [Submodule.span_le]
    rintro _ (⟨b, rfl⟩ | ⟨b, rfl⟩)
    · exact Submodule.subset_span ⟨Sum.inl b, rfl⟩
    · have h1 : F'.fl.fvec b = (gS D : D.host.E) • flagDifferenceVectors D F0 F' (Sum.inr b) +
          flagDifferenceVectors D F0 F' (Sum.inl b) := by
        simp only [flagDifferenceVectors, Sum.elim_inr, Sum.elim_inl, smul_smul, mul_inv_cancel₀ hg, one_smul,
          sub_add_cancel]
      rw [h1]
      exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩))
        (Submodule.subset_span ⟨_, rfl⟩)

end PI.UnitaryGroupMassFormula.CntFormula.R6
end
end
