module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGenNear
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ExistsMPrimeFiltration
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.CechHcSubsingletonOfBij

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPullSectionIntegral
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

namespace PullSectionIntegral

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem aeval_scale_of_isMultiHomog (y : (Σ k, ι k) → Ω) (t : K → Ω) {f : MRing ι} {e : K → ℕ}
    (hf : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f e) :
    aeval (fun p => t p.1 * y p) f = (∏ k, t k ^ e k) * aeval y f := by
  simp only [aeval_def, eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hpow : ∏ p : Σ k, ι k, t p.1 ^ d p = ∏ k, t k ^ e k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ i, t k ^ d ⟨k, i⟩ = t k ^ e k
    rw [Finset.prod_pow_eq_pow_sum, hf d hd k]
  have hsplit : ∏ p, (t p.1 * y p) ^ d p = (∏ p : Σ k, ι k, t p.1 ^ d p) * ∏ p, y p ^ d p := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun p _ => mul_pow _ _ _
  rw [hsplit, hpow]
  ring


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem eval_mConeMap (y : (Σ k, ι k) → Ω) (t : K → Ω) (f : MRing ι) :
    eval t (mConeMap y f) = aeval (fun p => t p.1 * y p) f := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [mConeMap]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p i hp =>
    rw [map_mul, map_mul, hp]
    simp [mConeMap, mul_comm]

theorem aeval_scale_eq_zero {y : (Σ k, ι k) → Ω} (t : K → Ω) {f : MRing ι} (hf : f ∈ mCoordIdeal y) :
    aeval (fun p => t p.1 * y p) f = 0 := by
  rw [← eval_mConeMap, show mConeMap y f = 0 from hf, map_zero]

theorem exists_sum_eq_one [CharZero Ω] (P : Ideal (MRing ι)) (y' : (Σ k, ι k) → Ω) (c : ∀ k, ι k)
    (hc : ∀ k, y' ⟨k, c k⟩ = 1) (hP : ∀ f ∈ P, aeval y' f = 0) {n : ℕ} (L : Fin n → MRing ι)
    (hL : ∀ z ∈ mcPts P, ∃ j, eval z (map (Int.castRingHom ℂ) (L j)) ≠ 0) :
    ∃ b : Fin n → MvPolynomial (Σ k, ι k) ℚ, ∑ i, aeval y' (b i) * aeval y' (L i) = 1 := by
  classical
  set φ : MvPolynomial (Σ k, ι k) ℚ →ₐ[ℚ] Ω := aeval y'
  let Lq : Fin n → MvPolynomial (Σ k, ι k) ℚ := fun i => map (algebraMap ℤ ℚ) (L i)
  have hLq : ∀ i, φ (Lq i) = aeval y' (L i) := fun i => aeval_map_algebraMap ℚ y' (L i)
  let J : Ideal (MvPolynomial (Σ k, ι k) ℚ) := RingHom.ker φ ⊔ Ideal.span (Set.range Lq)
  by_cases hJ : J = ⊤
  · have h1 : (1 : MvPolynomial (Σ k, ι k) ℚ) ∈ J := hJ ▸ Submodule.mem_top
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp h1
    obtain ⟨β, rfl⟩ := (Ideal.mem_span_range_iff_exists_fun).mp hb
    refine ⟨β, ?_⟩
    have := congrArg φ hab
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_add (f := _), show φ a = 0 from ha, zero_add, map_sum, map_one] at this
    rw [← this]
    exact Finset.sum_congr rfl fun i _ => by rw [map_mul, hLq]
  · exfalso
    obtain ⟨m, hm, hJm⟩ := Ideal.exists_le_maximal J hJ
    let := Ideal.Quotient.field m
    have : Algebra.FiniteType ℚ (MvPolynomial (Σ k, ι k) ℚ ⧸ m) :=
      Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℚ m)
        (Ideal.Quotient.mkₐ_surjective ℚ m)
    have := finite_of_finite_type_of_isJacobsonRing ℚ (MvPolynomial (Σ k, ι k) ℚ ⧸ m)
    let ψ : (MvPolynomial (Σ k, ι k) ℚ ⧸ m) →ₐ[ℚ] ℂ := (by
      refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
      solve_by_elim* (maxDepth := 2) only [*,
        @_root_.DivisionSemiring.to_moduleIsTorsionFree,
        @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
    let z : (Σ k, ι k) → ℂ := fun p => ψ (Ideal.Quotient.mk m (X p))
    have hz : ∀ g : MvPolynomial (Σ k, ι k) ℚ, ψ (Ideal.Quotient.mk m g) = aeval z g := by
      intro g
      have : (ψ.comp (Ideal.Quotient.mkₐ ℚ m)) = aeval z := by
        ext p; simp [z]
      exact congrArg (fun F => F g) this
    have hzZ : ∀ f : MRing ι, eval z (map (Int.castRingHom ℂ) f) =
        ψ (Ideal.Quotient.mk m (map (algebraMap ℤ ℚ) f)) := by
      intro f
      rw [hz, aeval_map_algebraMap, eval_map, aeval_def, algebraMap_int_eq]
    have hker : ∀ g ∈ RingHom.ker φ, Ideal.Quotient.mk m g = 0 := fun g hg =>
      Ideal.Quotient.eq_zero_iff_mem.mpr (hJm (Ideal.mem_sup_left hg))
    have hzP : z ∈ mcPts P := by
      refine ⟨fun k => ⟨c k, ?_⟩, fun f hf => ?_⟩
      · have hX : (X ⟨k, c k⟩ - 1 : MvPolynomial (Σ k, ι k) ℚ) ∈ RingHom.ker φ := by
          simp [RingHom.mem_ker, φ, hc k]
        have := hker _ hX
        rw [map_sub, map_one, sub_eq_zero] at this
        simp [z, this]
      · have hφf : φ (map (algebraMap ℤ ℚ) f) = 0 := by
          rw [show φ (map (algebraMap ℤ ℚ) f) = aeval y' f from aeval_map_algebraMap ℚ y' f]
          exact hP f hf
        rw [hzZ, hker _ (RingHom.mem_ker.mpr hφf), map_zero]
    obtain ⟨j, hj⟩ := hL z hzP
    apply hj
    rw [hzZ, Ideal.Quotient.eq_zero_iff_mem.mpr (hJm (Ideal.mem_sup_right
      (Ideal.subset_span ⟨j, rfl⟩))), map_zero]


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem aeval_mem_of_forall [CharZero Ω] (V : Subring Ω) (hQ : ∀ r : ℚ, algebraMap ℚ Ω r ∈ V)
    (y' : (Σ k, ι k) → Ω) (hy : ∀ p, y' p ∈ V) (b : MvPolynomial (Σ k, ι k) ℚ) : aeval y' b ∈ V := by
  induction b using MvPolynomial.induction_on with
  | C a => simpa using hQ a
  | add p q hp hq => rw [map_add (f := _)]; exact V.add_mem hp hq
  | mul_X p i hp => rw [map_mul, aeval_X]; exact V.mul_mem hp (hy i)

theorem proof : PullSectionIntegral.Statement := by
  intro K _ ι _ Ω _ _ y D e L q hV _ he hL hzero τ s hs j hj
  classical
  set A := Algebra.adjoin ℚ (Set.range fun i => aeval y (L i) / aeval y (L j))
  set R := (integralClosure A Ω).toSubring
  have : IsIntegrallyClosedIn R Ω := inferInstanceAs (IsIntegrallyClosedIn (integralClosure A Ω) Ω)
  show s / aeval y (L j) ^ (q * τ) ∈ R
  by_contra hnot
  obtain ⟨V, hRV, htV⟩ := Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn hnot
  have hAV : ∀ x ∈ A, x ∈ V := fun x hx =>
    hRV (isIntegral_algebraMap (R := A) (A := Ω) (x := ⟨x, hx⟩))
  have hQ : ∀ r : ℚ, algebraMap ℚ Ω r ∈ V.toSubring := fun r => hAV _ (A.algebraMap_mem r)

  have hrel : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0 := by
    intro k
    obtain ⟨i, hi⟩ := hV.2.1.2.2 k
    refine ⟨i, fun h0 => hi ?_⟩
    show mConeMap y (X ⟨k, i⟩) = 0
    simp [mConeMap, h0]
  have hmax : ∀ k, ∃ c : ι k, ∀ i, V.valuation (y ⟨k, i⟩) ≤ V.valuation (y ⟨k, c⟩) := by
    intro k
    obtain ⟨i0, -⟩ := hrel k
    obtain ⟨c, -, hc⟩ := Finset.exists_max_image Finset.univ (fun i => V.valuation (y ⟨k, i⟩))
      ⟨i0, Finset.mem_univ _⟩
    exact ⟨c, fun i => hc i (Finset.mem_univ _)⟩
  choose c hc using hmax
  have hc0 : ∀ k, y ⟨k, c k⟩ ≠ 0 := by
    intro k h0
    obtain ⟨i0, hi0⟩ := hrel k
    have := hc k i0
    rw [h0, map_zero, le_zero_iff, map_eq_zero] at this
    exact hi0 this
  have hratio : ∀ p : Σ k, ι k, y p / y ⟨p.1, c p.1⟩ ∈ V := by
    intro p
    rw [← V.valuation_le_one_iff, map_div₀]
    exact div_le_one_of_le₀ (hc p.1 p.2) zero_le

  set M : Ω := ∏ k, y ⟨k, c k⟩ ^ e k
  have hM0 : M ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc0 k)
  have hchart : (chartRingZ y c : Set Ω) ⊆ V := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx => obtain ⟨p, rfl⟩ := hx; exact hratio p
    | algebraMap r => simp
    | add a b _ _ ha hb => exact add_mem ha hb
    | mul a b _ _ ha hb => exact mul_mem ha hb
  have : IsIntegrallyClosedIn V.toSubring Ω := inferInstanceAs (IsIntegrallyClosedIn V Ω)
  have hxV : s * ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * ((q * e k : ℕ) : ℤ))) ∈ V.toSubring :=
    (Subring.integralClosure_le_iff (R := chartRingZ y c) (T := V.toSubring)).mpr
      (fun r => hchart r.2) (hs c hc0)
  have hprod : ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * ((q * e k : ℕ) : ℤ))) = (M ^ (q * τ))⁻¹ := by
    rw [← Finset.prod_pow, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [show -((τ : ℤ) * ((q * e k : ℕ) : ℤ)) = -((e k * (q * τ) : ℕ) : ℤ) by push_cast; ring,
      zpow_neg, zpow_natCast, pow_mul]
  rw [hprod] at hxV

  set t : K → Ω := fun k => (y ⟨k, c k⟩)⁻¹
  have hP' : ∀ f ∈ mCoordIdeal y, aeval (fun p => t p.1 * y p) f = 0 := fun f hf =>
    aeval_scale_eq_zero t hf
  obtain ⟨b, hb⟩ := exists_sum_eq_one (mCoordIdeal y) (fun p => t p.1 * y p) c
    (fun k => inv_mul_cancel₀ (hc0 k)) hP' L hzero
  have hLt : ∀ i, aeval (fun p => t p.1 * y p) (L i) = M⁻¹ * aeval y (L i) := by
    intro i
    rw [aeval_scale_of_isMultiHomog y t (hL i)]
    simp [t, M, Finset.prod_inv_distrib, inv_pow]
  have hratio' : ∀ p : Σ k, ι k, t p.1 * y p ∈ V := fun p => by
    simpa [t, div_eq_inv_mul] using hratio p
  have hMV : M / aeval y (L j) ∈ V := by
    have hsum : M / aeval y (L j) =
        ∑ i, aeval (fun p => t p.1 * y p) (b i) * (aeval y (L i) / aeval y (L j)) := by
      have := congrArg (fun w => w * (M / aeval y (L j))) hb
      simp only [one_mul, Finset.sum_mul, hLt] at this
      rw [← this]
      refine Finset.sum_congr rfl fun i _ => ?_
      field_simp
    rw [hsum]
    refine sum_mem fun i _ => mul_mem ?_ ?_
    · exact aeval_mem_of_forall V.toSubring hQ _ (fun p => hratio' p) (b i)
    · exact hAV _ (Algebra.subset_adjoin ⟨i, rfl⟩)
  apply htV
  have hMn : M ^ (q * τ) ≠ 0 := pow_ne_zero _ hM0
  have : s / aeval y (L j) ^ (q * τ) = s * (M ^ (q * τ))⁻¹ * (M / aeval y (L j)) ^ (q * τ) := by
    rw [div_pow, mul_assoc, ← mul_div_assoc, inv_mul_cancel₀ hMn, mul_one_div]
  rw [this]
  exact mul_mem hxV (pow_mem hMV _)

end PullSectionIntegral

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGenNearCover
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def GenNearCover.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type)
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
    (V : Ideal (MRingOver S ι)) (M : Type) [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M] [IsScalarTower S (MRingOver S ι) M]
    (𝓜 : (K → ℤ) → Submodule S M) (deg : ℕ → K → ℤ),
    IsNoetherianRing S → KH.IsMGraded S ι 𝓜 → V ≤ Module.annihilator (MRingOver S ι) M →
    (∀ P : Ideal (MRingOver S ι), IsClosedMultiPt P → V ≤ P →
      ∃ (f : MRingOver S ι) (δ : K → ℕ) (c₀ : ℕ), ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f δ ∧ f ∉ P ∧
        ∀ c : ℕ, c₀ ≤ c → GenNear S ι 𝓜 (deg c) f δ) →
    ∃ c₁ : ℕ, ∀ c : ℕ, c₁ ≤ c → GeneratedMod S ι 𝓜 (deg c)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsChartNakayamaGen
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def ChartNakayamaGen.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type)
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
    (M : Type) [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M] [IsScalarTower S (MRingOver S ι) M]
    (𝓜 : (K → ℤ) → Submodule S M) (P : Ideal (MRingOver S ι)) (d : K → ℤ),
    IsNoetherianRing S → Module.Finite (MRingOver S ι) M → KH.IsMGraded S ι 𝓜 → P.IsPrime → IsMultiHomogIdeal P →
    ∀ I : KH.Cell K ι 0, (∀ k, ∀ i ∈ I.1 k, (X ⟨k, i⟩ : MRingOver S ι) ∉ P) →
    (∀ x ∈ KH.locPart ι 𝓜 (KH.cellMon S I.1) d, ∃ z ∈ KH.cechZc ι 𝓜 d 0,
      x - z I ∈ locIdealPart 𝓜 (KH.cellMon S I.1) P d) →
    ∃ (f : MRingOver S ι) (δ : K → ℕ), ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f δ ∧ f ∉ P ∧ GenNear S ι 𝓜 d f δ

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsClosedPtFibreLift
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def ClosedPtFibreLift.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type)
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
    (M : Type) [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M] [IsScalarTower S (MRingOver S ι) M]
    (𝓜 : (K → ℤ) → Submodule S M) (P : Ideal (MRingOver S ι)) (d : K → ℤ),
    IsNoetherianRing S → Module.Finite (MRingOver S ι) M → KH.IsMGraded S ι 𝓜 → IsClosedMultiPt P →
    Subsingleton (KH.cechHc ι (subGrading 𝓜 (P • ⊤ : Submodule (MRingOver S ι) M)) d 1) →
    ∀ I : KH.Cell K ι 0, (∀ k, ∀ i ∈ I.1 k, (X ⟨k, i⟩ : MRingOver S ι) ∉ P) →
    ∀ x ∈ KH.locPart ι 𝓜 (KH.cellMon S I.1) d, ∃ z ∈ KH.cechZc ι 𝓜 d 0,
      x - z I ∈ locIdealPart 𝓜 (KH.cellMon S I.1) P d

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsLocIdealKer
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def LocIdealKer.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (M : Type) [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M] [IsScalarTower S (MRingOver S ι) M]
    (𝓜 : (K → ℤ) → Submodule S M) (P : Ideal (MRingOver S ι)) (T : Submonoid (MRingOver S ι)) (d : K → ℤ),
    KH.IsMGraded S ι 𝓜 → IsMultiHomogIdeal P → (∀ t ∈ T, ∃ a : K → ℕ, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog t a) →
    ∀ w ∈ KH.locPart ι 𝓜 T d,
      (w ∈ locIdealPart 𝓜 T P d ↔
        IsLocalizedModule.map T (LocalizedModule.mkLinearMap T M)
          (LocalizedModule.mkLinearMap T (M ⧸ (P • ⊤ : Submodule (MRingOver S ι) M)))
          (P • ⊤ : Submodule (MRingOver S ι) M).mkQ w = 0)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsModulePieceHilbert
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def ModulePieceHilbert.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (J₁ J₂ : Ideal (MRing ι)) (N d : ℕ),
    IsMultiHomogIdeal J₁ → IsMultiHomogIdeal J₂ → J₂ ≤ J₁ → 0 < N →
    (∀ f ∈ J₁, (N : MRing ι) * f ∈ J₂) →
    (∀ W : Ideal (MRing ι), W.IsPrime → J₂ ≤ W → ReciprocityTheory.ChartRestriction.G.Geo.IsRelevant W →
      ringKrullDim (MRing ι ⧸ W) ≤ ((d + Fintype.card K : ℕ) : WithBot ℕ∞)) →
    ∀ s : K → ℕ, ∃ (a₀ : ℕ) (C : ℝ), ∀ a : K → ℕ, (∀ k, a₀ ≤ a k) →
      |Real.log (modPieceCard J₁ J₂ (a + s)) -
          (∑ᶠ W ∈ topComps J₂ d, ((multAt J₂ W : ℝ) - multAt J₁ W) * Real.log (charOf W) *
            (geoNum d W (fun _ k => (a k : ℤ)) : ℝ)) / (d.factorial : ℝ)| ≤
        C * ((∑ k, a k : ℕ) + 1 : ℝ) ^ d / ((∑ k, a k : ℕ) + 1 : ℝ)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsFibreNormPrimeBound
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

def FibreNormPrimeBound.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (e : K → ℕ) (L : Fin (D + 1) → MRing ι) (q : ℕ),
    IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    (∀ k, 1 ≤ e k) → (∀ j, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (L j) e) →
    (∀ z ∈ mcPts (mCoordIdeal y), ∃ j, eval z (map (Int.castRingHom ℂ) (L j)) ≠ 0) →
    ∀ p : ℕ, p.Prime → ∃ C : ℕ,
      ∀ τ : ℕ, ∀ s ∈ chartLatNm y (fun k => ((q * e k : ℕ) : ℤ)) τ, ∀ (j : Fin (D + 1))
        (c : ℕ → MvPolynomial (Fin (D + 1)) ℚ), IsDehomNormForms y L j (q * τ) s c →
          ∀ m : Fin (D + 1) →₀ ℕ,
            -((C * τ : ℕ) : ℤ) ≤ padicValRat p ((c (Module.finrank (pullField y L) Ω)).coeff m)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsDehomNormPIntegral
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial

noncomputable section

def DehomNormPIntegral.Statement : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] (D : ℕ) (l : Fin (D + 1) → Ω) (P : IntermediateField ℚ Ω)
    [FiniteDimensional P Ω],
    P = IntermediateField.adjoin ℚ {x | ∃ i k, l k ≠ 0 ∧ x = l i / l k} →
    (∀ (d : ℕ) (F : MvPolynomial (Fin (D + 1)) ℚ), F.IsHomogeneous d → aeval l F = 0 → F = 0) →
    ∀ (p : ℕ), p.Prime → ∀ M : ℕ, ¬ p ∣ M → ∀ (j : Fin (D + 1)) (m : ℕ) (u : Ω),
      u ∈ integralClosure (Algebra.adjoin ℤ (insert ((M : Ω)⁻¹) (Set.range fun i => l i / l j))) Ω →
      ∀ c : ℕ → MvPolynomial (Fin (D + 1)) ℚ,
        (c (Module.finrank P Ω)).IsHomogeneous (Module.finrank P Ω * m) →
        (LinearMap.charpoly (Algebra.lmul P Ω u)).map (algebraMap P Ω) =
          ∑ i ∈ Finset.range (Module.finrank P Ω + 1),
            Polynomial.C (aeval (fun i' => l i' / l j) (c i)) * Polynomial.X ^ (Module.finrank P Ω - i) →
        ∀ μ : Fin (D + 1) →₀ ℕ, 0 ≤ padicValRat p ((c (Module.finrank P Ω)).coeff μ)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsNormFormGaussBound
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial

noncomputable section

def NormFormGaussBound.Statement : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] (D : ℕ) (l : Fin (D + 1) → Ω) (P : IntermediateField ℚ Ω)
    [FiniteDimensional P Ω],
    P = IntermediateField.adjoin ℚ {x | ∃ i k, l k ≠ 0 ∧ x = l i / l k} →
    (∀ (d : ℕ) (F : MvPolynomial (Fin (D + 1)) ℚ), F.IsHomogeneous d → aeval l F = 0 → F = 0) →
    ∀ p : ℕ, p.Prime → ∀ (j : Fin (D + 1)) (K d : ℕ) (x : Ω) (c : ℕ → MvPolynomial (Fin (D + 1)) ℚ),
      (c (Module.finrank P Ω)).IsHomogeneous d →
      (LinearMap.charpoly (Algebra.lmul P Ω x)).map (algebraMap P Ω) =
        ∑ i ∈ Finset.range (Module.finrank P Ω + 1),
          Polynomial.C (aeval (fun i' => l i' / l j) (c i)) * Polynomial.X ^ (Module.finrank P Ω - i) →
      (p : Ω) ^ K * x ∈ integralClosure
        (Subring.closure ({z | ∃ i k, z = l i / l k} ∪ {z | ∃ r : ℕ, ¬ p ∣ r ∧ z = (r : Ω)⁻¹})) Ω →
      ∀ μ : Fin (D + 1) →₀ ℕ,
        -((Module.finrank P Ω * K : ℕ) : ℤ) ≤ padicValRat p ((c (Module.finrank P Ω)).coeff μ)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsClosedPtGenUniform
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def ClosedPtGenUniform.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type)
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
    (V : Ideal (MRingOver S ι)) (N : K → ℤ),
    IsNoetherianRing S →
    (∀ (M : Type) [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M] [IsScalarTower S (MRingOver S ι) M]
      (𝓜 : (K → ℤ) → Submodule S M),
      Module.Finite (MRingOver S ι) M → KH.IsMGraded S ι 𝓜 → V ≤ Module.annihilator (MRingOver S ι) M →
      ∀ e : K → ℤ, ∃ c₁ : ℕ, ∀ c : ℕ, c₁ ≤ c → Subsingleton (KH.cechHc ι 𝓜 (e + c • N) 1)) →
    ∀ (M : Type) [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M] [IsScalarTower S (MRingOver S ι) M]
    (𝓜 : (K → ℤ) → Submodule S M),
      Module.Finite (MRingOver S ι) M → KH.IsMGraded S ι 𝓜 → V ≤ Module.annihilator (MRingOver S ι) M →
      ∀ (e : K → ℤ) (P : Ideal (MRingOver S ι)), IsClosedMultiPt P →
        ∃ (f : MRingOver S ι) (δ : K → ℕ) (c₀ : ℕ), ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f δ ∧ f ∉ P ∧
          ∀ c : ℕ, c₀ ≤ c → GenNear S ι 𝓜 (e + c • N) f δ

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsFibreNormDehomRoots
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

def FibreNormDehomRoots.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (e : K → ℕ) (L : Fin (D + 1) → MRing ι) (q : ℕ),
    IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    (∀ k, 1 ≤ e k) → (∀ j, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (L j) e) →
    (∀ z ∈ mcPts (mCoordIdeal y), ∃ j, eval z (map (Int.castRingHom ℂ) (L j)) ≠ 0) →
    ∀ τ : ℕ, ∀ s ∈ chartLatNm y (fun k => ((q * e k : ℕ) : ℤ)) τ, ∀ (j : Fin (D + 1))
      (c : ℕ → MvPolynomial (Fin (D + 1)) ℚ), IsDehomNormForms y L j (q * τ) s c →
        ∀ ζ : Fin (D + 1) → ℂ, ζ ≠ 0 → ∀ w : ℂ,
          ∑ i ∈ Finset.range (Module.finrank (pullField y L) Ω + 1),
            eval ζ (map (algebraMap ℚ ℂ) (c i)) * w ^ (Module.finrank (pullField y L) Ω - i) = 0 →
          ∃ z ∈ mcPts (mCoordIdeal y), ∃ t : ℂ, t ≠ 0 ∧
            (∀ j, eval z (map (Int.castRingHom ℂ) (L j)) = t * ζ j) ∧
            ∀ (dg dh : K → ℕ) (g h : MRing ι), ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g dg → ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog h dh →
              (∀ k, dg k = dh k + τ * (q * e k)) → aeval y g = s * aeval y h →
              eval z (map (Int.castRingHom ℂ) h) ≠ 0 →
              eval z (map (Int.castRingHom ℂ) g) = w * t ^ (q * τ) * eval z (map (Int.castRingHom ℂ) h)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsCharpolyRootLift
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial

noncomputable section

def CharpolyRootLift.Statement : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] (D : ℕ) (l : Fin (D + 1) → Ω) (P : IntermediateField ℚ Ω)
    [FiniteDimensional P Ω],
    P = IntermediateField.adjoin ℚ {x | ∃ i k, l k ≠ 0 ∧ x = l i / l k} →
    (∀ (d : ℕ) (F : MvPolynomial (Fin (D + 1)) ℚ), F.IsHomogeneous d → aeval l F = 0 → F = 0) →
    ∀ (j : Fin (D + 1)) (m : ℕ) (u : Ω) (c : ℕ → MvPolynomial (Fin (D + 1)) ℚ),
      l j ≠ 0 → c 0 = 1 → (∀ i ≤ Module.finrank P Ω, (c i).IsHomogeneous (i * m)) →
      (LinearMap.charpoly (Algebra.lmul P Ω (u / l j ^ m))).map (algebraMap P Ω) =
        ∑ i ∈ Finset.range (Module.finrank P Ω + 1),
          Polynomial.C (aeval (fun i' => l i' / l j) (c i)) * Polynomial.X ^ (Module.finrank P Ω - i) →
      ∀ (a : Fin (D + 1)) (hu : u / l a ^ m ∈
          integralClosure (Algebra.adjoin ℚ (Set.range fun k => l k / l a)) Ω)
        (ζ : Fin (D + 1) → ℂ), ζ a ≠ 0 → ∀ w : ℂ,
        ∑ i ∈ Finset.range (Module.finrank P Ω + 1),
          eval ζ (map (algebraMap ℚ ℂ) (c i)) * w ^ (Module.finrank P Ω - i) = 0 →
        ∃ ψ : integralClosure (Algebra.adjoin ℚ (Set.range fun k => l k / l a)) Ω →+* ℂ,
          (∀ (k : Fin (D + 1)) (hk : l k / l a ∈
              integralClosure (Algebra.adjoin ℚ (Set.range fun k => l k / l a)) Ω),
            ψ ⟨l k / l a, hk⟩ = ζ k / ζ a) ∧
          ψ ⟨u / l a ^ m, hu⟩ = w / ζ a ^ m

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSecCochReduce
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

theorem SecCochReduce.map_map_int {K : Type} {ι : K → Type} (p : ℕ) (f : MRing ι) :
    MvPolynomial.map (Int.castRingHom (ZMod p)) (MvPolynomial.map (Int.castRingHom ℤ) f) =
      MvPolynomial.map (Int.castRingHom (ZMod p)) f := by
  rw [MvPolynomial.map_map]
  congr 1

theorem SecCochReduce.proof : SecCochReduce.Statement := by
  intro K _ _ ι _ _ Ω _ y p a s hs
  funext J
  rw [FibreReduction.redCoch_apply]
  by_cases hz : ∃ k, y ⟨k, GenOnFibres.cellChart J k⟩ = 0
  · obtain ⟨k, h0⟩ := hz
    have := GenOnFibres.subsingleton_loc (S := ZMod p) (GenOnFibres.cellChart_mem J k) h0
    exact Subsingleton.elim _ _
  · push Not at hz
    obtain ⟨e, F, hF, _, heq⟩ := GenOnFibres.secCoch_spec (S := ℤ) hs J hz
    have hrep : GenOnFibres.IsRep y (ZMod p) (KH.cellMon (ZMod p) J.1)
        (FibreReduction.redLoc y p J.1 (GenOnFibres.secCoch y ℤ s a J)) (GenOnFibres.cellChart J) s a := by
      refine ⟨e, F, hF, GenOnFibres.cmon_mem (ZMod p) (GenOnFibres.cellChart_mem J) e, ?_⟩
      rw [heq, FibreReduction.redLoc_mk, FibreReduction.redRing_mk, SecCochReduce.map_map_int]
      congr 1
      exact Subtype.ext (SecCochReduce.map_map_int p _)
    exact hrep.unique (GenOnFibres.secCoch_spec hs J hz)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGeneratedNefGeneric
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1

noncomputable section

theorem GeneratedNefGeneric.eq_natCast_of_add_one_eq (d : ℕ) (x : WithBot ℕ∞)
    (hform : x + 1 = ((d : ℕ) : WithBot ℕ∞) + 1) : x = d := by
  induction x using WithBot.recBotCoe with
  | bot => exact absurd hform (by simp; rw [← Nat.cast_succ]; exact (WithBot.natCast_ne_bot _).symm)
  | coe y =>
    induction y using ENat.recTopCoe with
    | top =>
      exfalso
      have h1 : (((⊤ : ℕ∞) + 1 : ℕ∞) : WithBot ℕ∞) = (((d + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := by
        rw [WithBot.coe_add]; exact_mod_cast hform
      have h2 : ((⊤ : ℕ∞) + 1 : ℕ∞) = ((d + 1 : ℕ) : ℕ∞) := WithBot.coe_injective h1
      rw [top_add] at h2
      exact ENat.top_ne_natCast _ h2
    | coe y =>
      have h1 : ((y + 1 : ℕ) : WithBot ℕ∞) = ((d + 1 : ℕ) : WithBot ℕ∞) := by exact_mod_cast hform
      have : y = d := by exact_mod_cast (by exact_mod_cast h1 : y + 1 = d + 1) |> Nat.succ_injective
      subst this; rfl

theorem GeneratedNefGeneric.isProjVarF_map {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {W : Ideal (MRing ι)} {d : ℕ} (hW : IsArithVar W (d + 1)) :
    IsProjVarF (W.map (MvPolynomial.map (Int.castRingHom ℚ))) d := by
  obtain ⟨-, ⟨hWp, ⟨S, hS, hWS⟩, hrel⟩, hhor, hdim⟩ := hW
  have : W.IsPrime := hWp
  have hchar : ∀ m : ℤ, (C m : MvPolynomial (Σ k, ι k) ℤ) ∈ W → m = 0 := by
    intro m hm
    have h1 : m ∈ W.comap (C : ℤ →+* MRing ι) := hm
    rw [show W.comap (C : ℤ →+* MRing ι) = ⊥ from hhor, Ideal.mem_bot] at h1
    exact h1
  obtain ⟨hqp, hcomap, hform⟩ := ReciprocityTheory.AnForm.R.extQ_spec W hchar
  have hq : ReciprocityTheory.AnForm.R.extQ W = W.map (MvPolynomial.map (Int.castRingHom ℚ)) := rfl
  rw [← hq]
  refine ⟨⟨hqp, ?_, ?_⟩, ?_⟩
  · refine ⟨MvPolynomial.map (Int.castRingHom ℚ) '' S, ?_, ?_⟩
    · rintro _ ⟨f, hf, rfl⟩
      obtain ⟨b, hb⟩ := hS f hf
      exact ⟨b, fun m hm k => hb m (MvPolynomial.support_map_subset _ _ hm) k⟩
    · show W.map (MvPolynomial.map (Int.castRingHom ℚ)) = _
      rw [hWS, Ideal.map_span]
  · intro k
    obtain ⟨i, hi⟩ := hrel k
    refine ⟨i, fun hX => hi ?_⟩
    rw [← hcomap, Ideal.mem_comap, map_X]
    exact hX
  · refine GeneratedNefGeneric.eq_natCast_of_add_one_eq (d + Fintype.card K) _ ?_
    rw [hform, hdim, show d + 1 + Fintype.card K = (d + Fintype.card K) + 1 by omega]
    push_cast
    rfl

theorem GeneratedNefGeneric.proof (hG : GenOnFibres.Statement) (hR : GeneratedRestrict.Statement)
    (hN : GeneratedProductNonneg.Statement) : GeneratedNefGeneric.Statement := by
  intro K _ ι _ Ω _ _ y D a q w _ hw hgen W hW hPW
  classical
  let _ : LinearOrder K := LinearOrder.lift' (Fintype.equivFin K) (Fintype.equivFin K).injective
  let _ : ∀ k, LinearOrder (ι k) := fun k =>
    LinearOrder.lift' (Fintype.equivFin (ι k)) (Fintype.equivFin (ι k)).injective
  have hQ : KH.GeneratedV ℚ (KH.genIdeal y) a := (hG K ι Ω y a q w hw hgen).1
  have hWQ : KH.GeneratedV ℚ (W.map (MvPolynomial.map (Int.castRingHom ℚ))) a :=
    hR ℚ K ι _ _ a (Ideal.map_mono hPW) hQ
  have hV : IsProjVarF (W.map (MvPolynomial.map (Int.castRingHom ℚ))) 1 :=
    GeneratedNefGeneric.isProjVarF_map (d := 1) hW
  have h := hN ℚ K ι (fun V _ L => NumbersDVR.intNum ℚ V L) _ 1 (fun _ => a)
    (NumbersDVR.IntNumIsFieldIntersection.full ℚ K ι) hV (fun _ => hWQ)
  unfold genDeg
  convert h

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenKoszulStep
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry KoszulCech

noncomputable section

namespace GenKoszulStep

variable {S : Type} [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type} [∀ k, Fintype (ι k)]
  [∀ k, LinearOrder (ι k)]

theorem subsingleton_cechHc_iff {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M]
    [IsScalarTower S (MRingOver S ι) M] (𝓜 : (K → ℤ) → Submodule S M) (c : K → ℤ) (n : ℕ) :
    Subsingleton (KH.cechHc ι 𝓜 c (n + 1)) ↔
      ∀ x ∈ KH.cechCc ι 𝓜 c (n + 1), KH.cechD S ι M (n + 1) x = 0 →
        ∃ y ∈ KH.cechCc ι 𝓜 c n, KH.cechD S ι M n y = x := by
  rw [KH.cechHc, Submodule.Quotient.subsingleton_iff, eq_top_iff]
  constructor
  · intro h x hx hdx
    have hZ : x ∈ KH.cechZc ι 𝓜 c (n + 1) := ⟨hx, hdx⟩
    obtain ⟨y, hy, hyx⟩ := h (Submodule.mem_top (x := ⟨x, hZ⟩))
    exact ⟨y, hy, hyx⟩
  · rintro h ⟨x, hx, hdx⟩ -
    obtain ⟨y, hy, hyx⟩ := h x hx hdx
    exact ⟨y, hy, hyx⟩

theorem gather {V : Ideal (MRingOver S ι)} {α : K → ℤ} (h : KH.GeneratedV S V α) :
    ∃ (R : ℕ) (z : Fin R → KH.CechC S ι (MRingOver S ι ⧸ V) 0),
      (∀ j, z j ∈ KH.cechZc ι (KH.quotPart S V) α 0) ∧
      ∀ I : KH.Cell K ι 0, ∃ u : Fin R → LocalizedModule (KH.cellMon S I.1) (MRingOver S ι ⧸ V),
        (∀ j, u j ∈ KH.locPart ι (KH.quotPart S V) (KH.cellMon S I.1) (-α)) ∧ ∑ j, u j * z j I = 1 := by
  classical
  choose r zz uu hz hu hs using h
  have : Finite (KH.Cell K ι 0) := by unfold KH.Cell; infer_instance
  let _ : Fintype (KH.Cell K ι 0) := Fintype.ofFinite _
  set e := Fintype.equivFin (Σ I : KH.Cell K ι 0, Fin (r I))
  let v : ∀ I : KH.Cell K ι 0, (Σ I' : KH.Cell K ι 0, Fin (r I')) →
      LocalizedModule (KH.cellMon S I.1) (MRingOver S ι ⧸ V) :=
    fun I σ => if h : σ.1 = I then h ▸ uu σ.1 σ.2 else 0
  refine ⟨Fintype.card (Σ I : KH.Cell K ι 0, Fin (r I)), fun j => zz (e.symm j).1 (e.symm j).2,
    fun j => hz _ _, fun I => ⟨fun j => v I (e.symm j), fun j => ?_, ?_⟩⟩
  · have hv : ∀ σ, v I σ ∈ KH.locPart ι (KH.quotPart S V) (KH.cellMon S I.1) (-α) := by
      rintro ⟨I', i⟩
      simp only [v]
      split_ifs with hI
      · subst hI
        exact hu _ i
      · exact Submodule.zero_mem _
    exact hv (e.symm j)
  · rw [Equiv.sum_comp e.symm (fun σ => v I σ * zz σ.1 σ.2 I), Fintype.sum_sigma,
      Finset.sum_eq_single I]
    · simp only [v, dif_pos rfl]
      exact hs I
    · intro I' _ hI'
      refine Finset.sum_eq_zero fun i _ => ?_
      simp only [v, dif_neg hI']
      exact zero_mul (zz I' i I)
    · simp

end GenKoszulStep

open GenKoszulStep

theorem GenKoszulStep.proof (hB : KoszulCechComplex.Statement) (hC : KoszulCechExact.Statement)
    (hD : DoubleComplexVanish.Statement) (hSq : KH.CechDSqStatement) (hDeg : KH.CechDDegStatement) :
    GenKoszulStep.Statement := by
  intro S _ K _ _ ι _ _ V α _ hα
  obtain ⟨R, z, hz, hu⟩ := gather hα
  refine ⟨R, fun c hc => ?_⟩
  have hB' := hB S K ι V α R z hz c
  have hC' := hC S K ι V α R z hu c
  have key := hD (fun p n => KosC S ι V R p n) (fun p n => kosPart S ι V R α c p n)
    (fun p n => kosCech S ι V R p n) (fun p n => kosD z p n) R
    (fun p n x hx J _ => hDeg S K ι _ _ _ n (x J) (hx J trivial))
    (fun p n x hx => (hB' p n).1 x hx)
    (fun p n x _ => funext fun J => LinearMap.congr_fun (hSq S K ι (MRingOver S ι ⧸ V) n) (x J))
    (fun p n x _ => (hB' p n).2.1 x)
    (fun p n x _ => (hB' p n).2.2 x)
    (fun n x hx => (hC' n).1 x hx)
    (fun p n x hx h0 => (hC' n).2 p x hx h0)
    (fun p n hp x _ => funext fun J => absurd ((J.2.symm.trans_le (J.1.card_le_univ)).trans_eq
      (Fintype.card_fin R)) (by omega))
    (fun p hp1 hpR n x hx h0 => by
      have hJ := fun J => (subsingleton_cechHc_iff _ _ n).mp (hc p hp1 hpR (n + 1) (by omega))
        (x J) (hx J trivial) (congrFun h0 J)
      choose y hy hdy using hJ
      exact ⟨y, fun J _ => hy J, funext hdy⟩)
  intro i hi
  obtain ⟨n, rfl⟩ : ∃ n, i = n + 1 := ⟨i - 1, by omega⟩
  rw [subsingleton_cechHc_iff]
  intro x hx hdx
  obtain ⟨y, hy, hdy⟩ := key n (fun _ => x) (fun J _ => by simpa using hx) (funext fun _ => hdx)
  exact ⟨y ⟨∅, Finset.card_empty⟩, by simpa using hy _ trivial, congrFun hdy _⟩

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockResolutionFormsIndependent
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry SupBoundCount

noncomputable section

theorem BlockResolutionFormsIndependent.proof (hND : NonvanishingDense.Statement) :
    BlockResolutionFormsIndependent.Statement := by
  intro D K _ _ ι _ Ω _ _ d n r b hb a ha
  choose f hf hbf using hb.1
  obtain ⟨g, hgJ, hgP⟩ := SetLike.not_le_iff_exists.1 d.R.nondeg

  set F : ((Σ k, ι k) → ℂ) → ℂ := fun z => ∑ k, a k * eval z (map (Int.castRingHom ℂ) (f k)) with hF
  have ha' : ∀ x : d.R.X, F (blockPt d x) = 0 := by
    intro x
    have := ha x
    simp only [hbf, eval_map_int_rat] at this
    exact this
  have hli : LinearIndependent ℤ fun k => aeval d.y (f k) := by
    have := hb.2.1
    simp only [hbf, ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.aeval_map_int] at this
    exact this
  have hFc : Continuous F :=
    continuous_finsetSum _ fun k _ => continuous_const.mul (continuous_eval _)

  have hev : ∀ (s : MRing ι) (e : K → ℕ), ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s e → ∀ (c : K → ℂ) (z : (Σ k, ι k) → ℂ),
      eval (fun p => c p.1 * z p) (map (Int.castRingHom ℂ) s) =
        (∏ k, c k ^ e k) * eval z (map (Int.castRingHom ℂ) s) := by
    intro s e hs c z
    rw [eval_map, eval_map, eval₂_eq', eval₂_eq', Finset.mul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hc : (∏ i : (Σ k, ι k), c i.1 ^ m i) = ∏ k, c k ^ e k := by
      rw [Fintype.prod_sigma]
      refine Finset.prod_congr rfl fun k _ => ?_
      show ∏ i, c k ^ m ⟨k, i⟩ = _
      rw [Finset.prod_pow_eq_pow_sum, hs m hm k]
    simp only [mul_pow, Finset.prod_mul_distrib, hc]
    ring

  have hsmul : ∀ (c : K → ℂ) (z : (Σ k, ι k) → ℂ),
      F (fun p => c p.1 * z p) = (∏ k, c k ^ blockDeg d.k₀ n k) * F z := by
    intro c z
    simp only [hF, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hev (f k) _ (hf k) c z]
    ring

  have hoff : ∀ z, z ∈ mcPts (mCoordIdeal d.y) →
      eval z (map (Int.castRingHom ℂ) g) ≠ 0 → F z = 0 := by
    intro z hz hgz
    obtain ⟨x, c, hc, hxz⟩ := d.R.surj z hz (fun hJ => hgz (hJ.2 g hgJ))
    have h1 := ha' x
    rw [show blockPt d x = d.R.lift x x from rfl, hxz, hsmul] at h1
    exact (mul_eq_zero.1 h1).resolve_left
      (Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc k))

  have hpts : ∀ z ∈ mcPts (mCoordIdeal d.y), F z = 0 := by
    intro z hz
    have hcl := hND K ι (mCoordIdeal d.y) (D + 1) g d.arith hgP hz
    have hsub : {z | z ∈ mcPts (mCoordIdeal d.y) ∧
        eval z (map (Int.castRingHom ℂ) g) ≠ 0} ⊆ {z | F z = 0} := by
      intro z' hz'
      exact hoff z' hz'.1 hz'.2
    exact (isClosed_eq hFc continuous_const).closure_subset_iff.2 hsub hcl
  exact coeff_eq_zero hli (mcPts_nonempty d) hpts

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
