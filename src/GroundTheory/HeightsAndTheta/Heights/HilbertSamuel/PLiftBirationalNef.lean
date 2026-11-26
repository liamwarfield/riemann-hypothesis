module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsKodairaGeneric
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.AssemblyBridgeFull
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.ModelSt
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsResVolume
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PGenericFibreDim
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.MemConePtsIffChartIdeal
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsFibreNormBound
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsRatNoetherFrame

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PLiftBirationalNef
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1

noncomputable section

set_option linter.unusedSectionVars false

namespace LiftBirationalNef

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [CharZero Ω]

theorem exists_int_of_rat (f : MRingOver ℚ ι) :
    ∃ (m : ℕ) (F : MRing ι), 0 < m ∧ MvPolynomial.map (Int.castRingHom ℚ) F = C (m : ℚ) * f := by
  induction f using MvPolynomial.induction_on' with
  | monomial u a =>
    refine ⟨a.den, monomial u a.num, a.den_pos, ?_⟩
    rw [map_monomial, C_mul_monomial]
    congr 1
    rw [eq_intCast, mul_comm, Rat.mul_den_eq_num]
  | add p q hp hq =>
    obtain ⟨m1, F1, hm1, h1⟩ := hp
    obtain ⟨m2, F2, hm2, h2⟩ := hq
    refine ⟨m1 * m2, C (m2 : ℤ) * F1 + C (m1 : ℤ) * F2, Nat.mul_pos hm1 hm2, ?_⟩
    rw [map_add (f := _), map_mul, map_mul, map_C, map_C, h1, h2]
    simp only [eq_intCast, Int.cast_natCast, Nat.cast_mul, C_mul]
    ring

theorem mConeMapOver_map (y : (Σ k, ι k) → Ω) (F : MRing ι) :
    KH.mConeMapOver ℚ y (MvPolynomial.map (Int.castRingHom ℚ) F) = mConeMap y F := by
  rw [← algebraMap_int_eq]
  exact MvPolynomial.aeval_map_algebraMap ℚ _ F

theorem genIdeal_eq (y : (Σ k, ι k) → Ω) : KH.genIdeal y = KH.mIdealOver ℚ y := by
  apply le_antisymm
  · rw [KH.genIdeal, Ideal.map_le_iff_le_comap]
    intro F hF
    rw [Ideal.mem_comap, KH.mIdealOver, RingHom.mem_ker, mConeMapOver_map]
    exact hF
  · intro f hf
    obtain ⟨m, F, hm, hF⟩ := exists_int_of_rat f
    rw [KH.mIdealOver, RingHom.mem_ker] at hf
    have hF0 : F ∈ mCoordIdeal y := by
      rw [mCoordIdeal, RingHom.mem_ker, ← mConeMapOver_map, hF, map_mul, hf, mul_zero]
    have hmap : MvPolynomial.map (Int.castRingHom ℚ) F ∈ KH.genIdeal y := Ideal.mem_map_of_mem _ hF0
    have hm0 : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
    have hf' : f = C ((m : ℚ)⁻¹) * MvPolynomial.map (Int.castRingHom ℚ) F := by
      rw [hF, ← mul_assoc, ← C_mul, inv_mul_cancel₀ hm0, C_1, one_mul]
    rw [hf']
    exact Ideal.mul_mem_left _ _ hmap

theorem coord_ne_zero_of_not_mem {y : (Σ k, ι k) → Ω} {p : Σ k, ι k}
    (h : (X p : MRing ι) ∉ mCoordIdeal y) : y p ≠ 0 := by
  intro h0
  apply h
  rw [mCoordIdeal, RingHom.mem_ker, mConeMap, aeval_X, h0, C_0, zero_mul]

theorem aeval_scale {y : (Σ k, ι k) → Ω} (lam : K → Ω) {G : MRing ι} {d : K → ℕ} (hG : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog G d) :
    aeval (fun p => lam p.1 * y p) G = (∏ k, lam k ^ d k) * aeval y G := by
  classical
  conv_lhs => rw [G.as_sum]
  conv_rhs => rw [G.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [aeval_monomial, aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp_rw [mul_pow, Finset.prod_mul_distrib]
  have hl : ∏ p : Σ k, ι k, lam p.1 ^ m p = ∏ k, lam k ^ d k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ i, lam k ^ m ⟨k, i⟩ = lam k ^ d k
    rw [Finset.prod_pow_eq_pow_sum, hG m hm k]
  rw [hl]
  ring

end LiftBirationalNef


end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PShiftDegreePolynomial
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

namespace ShiftDegreePolynomial

def toMultilinear {K : Type} {n : ℕ} (f : (Fin n → K → ℤ) → ℤ)
    (hadd : ∀ (bs : Fin n → K → ℤ) (j : Fin n) (x y : K → ℤ),
      f (Function.update bs j (x + y)) = f (Function.update bs j x) + f (Function.update bs j y)) :
    MultilinearMap (RingHom.id ℤ) (fun _ : Fin n => K → ℤ) ℤ where
  toFun := f
  map_update_add' := by
    intro inst m i x y
    obtain rfl : inst = instDecidableEqFin n := Subsingleton.elim _ _
    exact hadd m i x y
  map_update_smul' := by
    intro inst m i c x
    obtain rfl : inst = instDecidableEqFin n := Subsingleton.elim _ _
    exact (AddMonoidHom.mk' (fun x => f (Function.update m i x)) (hadd m i)).map_zsmul c x

theorem expand {K : Type} {n : ℕ} (f : (Fin n → K → ℤ) → ℤ)
    (hadd : ∀ (bs : Fin n → K → ℤ) (j : Fin n) (x y : K → ℤ),
      f (Function.update bs j (x + y)) = f (Function.update bs j x) + f (Function.update bs j y))
    (q : ℤ) (a b : K → ℤ) :
    f (fun _ => q • a + b) =
      ∑ s : Finset (Fin n), q ^ s.card * f (s.piecewise (fun _ => a) (fun _ => b)) := by
  have h1 := (toMultilinear f hadd).map_add_univ (fun _ => q • a) (fun _ => b)
  refine h1.trans (Finset.sum_congr rfl fun s _ => ?_)
  have h2 := (toMultilinear f hadd).map_piecewise_smul (fun _ => q)
    (s.piecewise (fun _ => a) (fun _ => b)) s
  have h3 : s.piecewise (fun i => q • s.piecewise (fun _ => a) (fun _ => b) i)
      (s.piecewise (fun _ => a) (fun _ => b)) = s.piecewise (fun _ => q • a) (fun _ => b) := by
    funext i
    by_cases hi : i ∈ s <;> simp [Finset.piecewise, hi]
  rw [h3, Finset.prod_const, RingHom.id_apply, smul_eq_mul] at h2
  exact h2

theorem genericFibre {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {P : Ideal (MRing ι)} {D : ℕ} (hP : IsArithVar P (D + 1)) :
    GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiProjPrime (P.map (MvPolynomial.map (Int.castRingHom ℚ))) ∧
      ringKrullDim (MvPolynomial (Σ k, ι k) ℚ ⧸ P.map (MvPolynomial.map (Int.castRingHom ℚ))) =
        ((D + Fintype.card K : ℕ) : WithBot ℕ∞) := by
  obtain ⟨-, ⟨hPp, ⟨S, hS, hPS⟩, hrel⟩, hhor, hdim⟩ := hP
  have : P.IsPrime := hPp
  have hchar : ∀ m : ℤ, (C m : MvPolynomial (Σ k, ι k) ℤ) ∈ P → m = 0 := by
    intro m hm
    have h1 : m ∈ P.comap (C : ℤ →+* MRing ι) := hm
    rw [show P.comap (C : ℤ →+* MRing ι) = ⊥ from hhor, Ideal.mem_bot] at h1
    exact h1
  obtain ⟨hqp, hcomap, hform⟩ := ReciprocityTheory.AnForm.R.extQ_spec P hchar
  have hq : ReciprocityTheory.AnForm.R.extQ P = P.map (MvPolynomial.map (Int.castRingHom ℚ)) := rfl
  rw [← hq]
  refine ⟨⟨hqp, ?_, ?_⟩, ?_⟩
  · rw [GroundTheory.Heights₂.Heights.Bridge.isMultiHomogIdeal_iff]
    refine ⟨MvPolynomial.map (Int.castRingHom ℚ) '' S, ?_, ?_⟩
    · rintro _ ⟨f, hf, rfl⟩
      obtain ⟨b, hb⟩ := hS f hf
      exact ⟨b, fun m hm k => hb m (MvPolynomial.support_map_subset _ _ hm) k⟩
    · rw [hq, hPS, Ideal.map_span]
  · intro k
    obtain ⟨i, hi⟩ := hrel k
    refine ⟨i, fun hX => hi ?_⟩
    rw [← hcomap, Ideal.mem_comap, map_X]
    exact hX
  · rw [hdim] at hform
    refine GroundTheory.Heights₂.Heights.ObjectsChow.GenericFibreDim.eq_natCast_of_add_one_eq _ _ ?_
    rw [hform]
    push_cast
    ring

theorem proof (h : MixedNumberPolynomial.Statement.{0}) : ShiftDegreePolynomial.Statement := by
  classical
  intro K _ ι _ P D a b hP
  obtain ⟨hprime, hdimq⟩ := genericFibre hP
  set Q := P.map (MvPolynomial.map (Int.castRingHom ℚ)) with hQ
  have hadd := (h ℚ K ι Q D hprime hdimq).2
  let f : (Fin D → K → ℤ) → ℤ := fun bs => GroundTheory.Heights₂.Heights.NumbersDVR.intNum ℚ Q bs
  let c : Finset (Fin D) → ℤ := fun s => f (s.piecewise (fun _ => a) (fun _ => b))
  refine ⟨∑ s : Finset (Fin D), Polynomial.C (c s : ℝ) * Polynomial.X ^ s.card, ?_, ?_, ?_⟩
  · refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun s _ => ?_
    refine (Polynomial.natDegree_C_mul_X_pow_le _ _).trans ?_
    simpa using Finset.card_le_univ s
  · rw [Polynomial.finsetSum_coeff]
    simp_rw [Polynomial.coeff_C_mul_X_pow]
    rw [Finset.sum_eq_single Finset.univ]
    · simp [c, f, genDeg, hQ]
    · intro s _ hs
      rw [if_neg]
      intro hD
      apply hs
      rw [← Finset.card_eq_iff_eq_univ, Fintype.card_fin]
      exact hD.symm
    · intro hu
      exact absurd (Finset.mem_univ _) hu
  · intro q
    have hexp := expand f hadd (q : ℤ) a b
    have hg : genDeg P D ((q : ℤ) • a + b) = f (fun _ => (q : ℤ) • a + b) := rfl
    rw [hg, hexp, Polynomial.eval_finsetSum]
    push_cast
    refine Finset.sum_congr rfl fun s _ => ?_
    simp [c, mul_comm]

end ShiftDegreePolynomial

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsChartImageNull
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def ChartDimLt.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (J : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (e : ℕ)
    (p : (k : K) → ι k),
    IsMultiHomogIdeal J →
    ringKrullDim (MvPolynomial (Σ k, ι k) ℂ ⧸ J) < ((e + Fintype.card K : ℕ) : WithBot ℕ∞) →
      ringKrullDim (MvPolynomial (Σ k, ι k) ℂ ⧸ ReciprocityTheory.AnForm.R.chartIdeal J p) < (e : WithBot ℕ∞)

def ChartRatioImageNull.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (J : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (e : ℕ)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)),
    ringKrullDim (MvPolynomial (Σ k, ι k) ℂ ⧸ J) < (e : WithBot ℕ∞) →
      volume {y : Fin e → ℂ | ∃ z ∈ zeroLocus ℂ J, Ψ (segre z) 0 ≠ 0 ∧
        (Fin.cons 1 y : Fin (e + 1) → ℂ) = (Ψ (segre z) 0)⁻¹ • Ψ (segre z)} = 0

section Inhabitants

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGradedSubquot
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def subGrading {S : Type*} [CommRing S] {K : Type*} {ι : K → Type*} {M : Type*} [AddCommGroup M]
    [Module (MRingOver S ι) M] [Module S M] [IsScalarTower S (MRingOver S ι) M]
    (𝓜 : (K → ℤ) → Submodule S M) (N : Submodule (MRingOver S ι) M) (c : K → ℤ) : Submodule S N :=
  (𝓜 c).comap (N.subtype.restrictScalars S)

def quotGrading {S : Type*} [CommRing S] {K : Type*} {ι : K → Type*} {N : Type*} [AddCommGroup N]
    [Module (MRingOver S ι) N] [Module S N] [IsScalarTower S (MRingOver S ι) N]
    (𝓝 : (K → ℤ) → Submodule S N) (L : Submodule (MRingOver S ι) N) (c : K → ℤ) : Submodule S (N ⧸ L) :=
  (𝓝 c).map (L.mkQ.restrictScalars S)

def GradedSubquot.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (M : Type) [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M] [IsScalarTower S (MRingOver S ι) M]
    (𝓜 : (K → ℤ) → Submodule S M) (G H : Set M),
    KH.IsMGraded S ι 𝓜 → (∀ x ∈ G, ∃ c, x ∈ 𝓜 c) → (∀ x ∈ H, ∃ c, x ∈ 𝓜 c) →
    Submodule.span (MRingOver S ι) G ≤ Submodule.span (MRingOver S ι) H →
    KH.IsMGraded S ι (subGrading 𝓜 (Submodule.span (MRingOver S ι) H)) ∧
      KH.IsMGraded S ι (quotGrading (subGrading 𝓜 (Submodule.span (MRingOver S ι) H))
        ((Submodule.span (MRingOver S ι) G).comap (Submodule.span (MRingOver S ι) H).subtype))

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenDegTwist
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1

noncomputable section

def intNumMultilinear {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
    (I : Ideal (MRingOver ℚ ι)) (n : ℕ) (hI : NumbersDVR.IsMultiHomogIdeal I)
    (hr : NumbersDVR.IsRelevant I) (hd : FieldNumbers.relDim I = n) :
    MultilinearMap (RingHom.id ℤ) (fun _ : Fin n => K → ℤ) ℤ where
  toFun bs := NumbersDVR.intNum ℚ I bs
  map_update_add' := by
    intro inst bs i x y
    obtain rfl : inst = instDecidableEqFin n := Subsingleton.elim _ _
    exact FieldNumbers.IntNumAdd.full ℚ K ι I hI hr n hd bs i x y
  map_update_smul' := by
    intro inst bs i c x
    obtain rfl : inst = instDecidableEqFin n := Subsingleton.elim _ _
    let g : (K → ℤ) →+ ℤ := AddMonoidHom.mk' (fun x => NumbersDVR.intNum ℚ I (Function.update bs i x))
      fun x y => FieldNumbers.IntNumAdd.full ℚ K ι I hI hr n hd bs i x y
    exact map_zsmul g c x

theorem intNumMultilinear_apply {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
    (I : Ideal (MRingOver ℚ ι)) (n : ℕ) (hI : NumbersDVR.IsMultiHomogIdeal I)
    (hr : NumbersDVR.IsRelevant I) (hd : FieldNumbers.relDim I = n) (bs : Fin n → K → ℤ) :
    intNumMultilinear I n hI hr hd bs = NumbersDVR.intNum ℚ I bs :=
  rfl

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsMixedKleimanLow
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo

def MixedKleiman.AtDim (d : ℕ) : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P P0 : Ideal (MRing ι))
    (M A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (a : K → ℕ) (II : IntersectionSystem),
    IsIntersectionSystem II → 1 ≤ d → IsArithVar P d → P0 ≤ P →
    IsSemipositiveRel P0 P M → NefOnFibres P M.a → IsConjInvariantH M →
    (∀ W, IsArithVar W 1 → P ≤ W → 0 ≤ II K ι W 1 ![M]) →
    (A.a = fun k => (a k : ℤ)) → IsSemipositiveRel P0 P A → MonomialsBounded P A a → IsConjInvariantH A →
    ∀ j ≤ d, 0 ≤ II K ι P d (fun i : Fin d => if (i : ℕ) < j then M else A)

def MixedKleiman.LowAt (d : ℕ) : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P P0 : Ideal (MRing ι))
    (M A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (a : K → ℕ) (II : IntersectionSystem),
    IsIntersectionSystem II → 1 ≤ d → IsArithVar P d → P0 ≤ P →
    IsSemipositiveRel P0 P M → NefOnFibres P M.a → IsConjInvariantH M →
    (∀ W, IsArithVar W 1 → P ≤ W → 0 ≤ II K ι W 1 ![M]) →
    (A.a = fun k => (a k : ℤ)) → IsSemipositiveRel P0 P A → MonomialsBounded P A a → IsConjInvariantH A →
    ∀ j < d, 0 ≤ II K ι P d (fun i : Fin d => if (i : ℕ) < j then M else A)

def MixedKleiman.TopAt (d : ℕ) : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P P0 : Ideal (MRing ι))
    (M : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (II : IntersectionSystem),
    IsIntersectionSystem II → 1 ≤ d → IsArithVar P d → P0 ≤ P →
    IsSemipositiveRel P0 P M → NefOnFibres P M.a → IsConjInvariantH M →
    (∀ W, IsArithVar W 1 → P ≤ W → 0 ≤ II K ι W 1 ![M]) →
    0 ≤ II K ι P d (fun _ => M)

theorem MixedKleiman.atDim_zero : MixedKleiman.AtDim 0 := by
  intro K _ ι _ P P0 M A a II _ h1
  exact absurd h1 (by norm_num)

def MixedKleimanLow.Statement : Prop :=
  ∀ d : ℕ, MixedKleiman.AtDim (d - 1) → MixedKleiman.LowAt d

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenericFibreVar
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1

noncomputable section

theorem GenericFibreVar.proof : GenericFibreVar.Statement := by
  intro K _ ι _ Ω _ y D hP
  obtain ⟨-, ⟨hPp, ⟨S, hS, hPS⟩, hrel⟩, hhor, hdim⟩ := hP
  have : (mCoordIdeal y).IsPrime := hPp
  have hchar : ∀ m : ℤ, (C m : MvPolynomial (Σ k, ι k) ℤ) ∈ mCoordIdeal y → m = 0 := by
    intro m hm
    have h1 : m ∈ (mCoordIdeal y).comap (C : ℤ →+* MRing ι) := hm
    rw [show (mCoordIdeal y).comap (C : ℤ →+* MRing ι) = ⊥ from hhor, Ideal.mem_bot] at h1
    exact h1
  obtain ⟨hqp, hcomap, hform⟩ := ReciprocityTheory.AnForm.R.extQ_spec (mCoordIdeal y) hchar
  have hq : ReciprocityTheory.AnForm.R.extQ (mCoordIdeal y) = KH.genIdeal y := rfl
  rw [← hq]
  refine ⟨⟨hqp, ?_, ?_⟩, ?_⟩
  · refine ⟨MvPolynomial.map (Int.castRingHom ℚ) '' S, ?_, ?_⟩
    · rintro _ ⟨f, hf, rfl⟩
      obtain ⟨b, hb⟩ := hS f hf
      exact ⟨b, fun m hm k => hb m (MvPolynomial.support_map_subset _ _ hm) k⟩
    · show (mCoordIdeal y).map (MvPolynomial.map (Int.castRingHom ℚ)) = _
      rw [hPS, Ideal.map_span]
  · intro k
    obtain ⟨i, hi⟩ := hrel k
    refine ⟨i, fun hX => hi ?_⟩
    rw [← hcomap, Ideal.mem_comap, map_X]
    exact hX
  · refine GroundTheory.Heights₂.Heights.ObjectsChow.GenericFibreDim.eq_natCast_of_add_one_eq
      (D + Fintype.card K) _ ?_
    rw [hform, hdim, show D + 1 + Fintype.card K = (D + Fintype.card K) + 1 by omega]
    push_cast
    rfl

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PFibreNormBound
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

theorem FibreNormBound.proof (h₁ : ProjAvoidingForm.Statement) (h₂ : FibreRepresentatives.Statement)
    (h₃ : FibreNormMax.Statement) (h₄ : MetricMaxComparison.Statement) : FibreNormBound.Statement := by
  intro K _ ι _ Ω _ y D A df f hV hB hA hf hfP
  obtain ⟨e, L, G, he, hL, hL0, hG, hGf⟩ := h₁ K ι Ω y D df f hV hf hfP
  obtain ⟨n, c, B, hn, hB1, hF⟩ := h₃ K ι Ω y D A.a e L hV hB he hL hL0
  obtain ⟨C, hC, hAC⟩ := h₄ K ι A hA
  choose S hS₁ hS₂ using h₂ K ι Ω y D e L he hL hL0
  refine ⟨n, c, B * C ^ n, G, S, hn, one_le_mul_of_one_le_of_one_le hB1 (one_le_pow₀ hC), hG, ?_, ?_⟩
  · intro ζ _ hGζ z hz
    obtain ⟨hzP, t, ht⟩ := hS₁ ζ z hz
    exact ⟨hzP, hGf ζ hGζ z hzP ⟨t, ht⟩⟩
  · intro τ u hu hu0
    obtain ⟨F, hF0, hFdeg, hFb⟩ := hF τ u hu hu0
    refine ⟨F, hF0, hFdeg, fun ζ hζ _ M hM hrep => ?_⟩
    have hC0 : (0 : ℝ) ≤ C := zero_le_one.trans hC
    have key := hFb ζ hζ (S ζ) (hS₂ ζ) (M * C ^ τ) (by positivity) (fun z hz => by
      obtain ⟨dg, dh, g, h, hg, hh, hd, hgh, hz0, hle⟩ := hrep z hz
      refine ⟨dg, dh, g, h, hg, hh, hd, hgh, hz0, ?_⟩
      have hzb := (hS₁ ζ z hz).1.1
      have h0 : 0 ≤ A.h z := (A.pos z hzb).le
      calc ‖eval z (map (Int.castRingHom ℂ) g)‖
          ≤ M * A.h z ^ τ * ‖eval z (map (Int.castRingHom ℂ) h)‖ := hle
        _ ≤ M * (C * (ReciprocityTheory.ChartRestriction.G.Geo.HermLine.ofMetrics (fun k => maxMetric (C := ℂ) (ι := ι k)) A.a).h z) ^ τ *
              ‖eval z (map (Int.castRingHom ℂ) h)‖ := by
            gcongr
            exact hAC z hzb
        _ = M * C ^ τ * (ReciprocityTheory.ChartRestriction.G.Geo.HermLine.ofMetrics (fun k => maxMetric (C := ℂ) (ι := ι k)) A.a).h z ^ τ *
              ‖eval z (map (Int.castRingHom ℂ) h)‖ := by ring)
    have hB0 : (0 : ℝ) ≤ B := zero_le_one.trans hB1
    have hpow : C ^ (τ * n) ≤ C ^ (n * (τ + 1)) :=
      pow_le_pow_right₀ hC (by rw [Nat.mul_comm n]; exact Nat.mul_le_mul_right n (Nat.le_succ τ))
    calc ‖eval ζ (map (Int.castRingHom ℂ) F)‖ ≤ B ^ (τ + 1) * (M * C ^ τ) ^ n := key
      _ = B ^ (τ + 1) * M ^ n * C ^ (τ * n) := by rw [mul_pow, ← pow_mul]; ring
      _ ≤ B ^ (τ + 1) * M ^ n * C ^ (n * (τ + 1)) := by gcongr
      _ = (B * C ^ n) ^ (τ + 1) * M ^ n := by rw [mul_pow, ← pow_mul]; ring

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ZcombIsConjInvariantH
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

set_option linter.unusedSectionVars false

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem HermLine.zcomb_isConjInvariantH {A B : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} (hA : IsConjInvariantH A) (hB : IsConjInvariantH B)
    (p q : ℤ) : IsConjInvariantH (HermLine.zcomb A B p q) := fun z => by
  show A.h _ ^ p * B.h _ ^ q = A.h z ^ p * B.h z ^ q
  rw [hA z, hB z]

theorem fsH_isConjInvariantH (ι : K → Type) [∀ k, Fintype (ι k)] : IsConjInvariantH (fsH ι) := fun z => by
  show ∏ k, (fsMetric (ι := ι k)).ρ (fun i => (starRingEnd ℂ) (z ⟨k, i⟩)) ^ (1 : K → ℤ) k =
    ∏ k, (fsMetric (ι := ι k)).ρ (fun i => z ⟨k, i⟩) ^ (1 : K → ℤ) k
  exact Finset.prod_congr rfl fun k _ => by rw [ProjLine.isConjInvariant_fs (fun i => z ⟨k, i⟩)]

theorem zcomb_metric_identity {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (q k p n : ℕ) :
    a ^ (q * n) = (a ^ ((q : ℤ) - k * p) * b ^ (p : ℤ)) ^ n * (a ^ (k : ℤ) * b ^ (-1 : ℤ)) ^ (p * n) := by
  rw [← zpow_natCast a, ← zpow_natCast (_ * _) n, ← zpow_natCast (_ * _) (p * n), mul_zpow, mul_zpow,
    ← zpow_mul, ← zpow_mul, ← zpow_mul, ← zpow_mul, mul_mul_mul_comm, ← zpow_add₀ ha, ← zpow_add₀ hb]
  have e1 : ((q : ℤ) - k * p) * (n : ℤ) + (k : ℤ) * ((p * n : ℕ) : ℤ) = ((q * n : ℕ) : ℤ) := by push_cast; ring
  have e2 : (p : ℤ) * (n : ℤ) + (-1 : ℤ) * ((p * n : ℕ) : ℤ) = 0 := by push_cast; ring
  rw [e1, e2, zpow_zero, mul_one]

theorem G2.proof (hK : KodairaSection.Statement) (hS : SectionProduct.Statement)
    (hP : PerturbSemipos.Statement) (hG : NefAmpleGeneric.Statement) (hF : NefAmpleFibre.Statement)
    (hL : ZCombLimit.Statement) : G2.Statement := by
  intro K _ _ ι _ _ Ω _ _ y D M P0 II hD hII har hb hM
  obtain ⟨k, e, C, hk, hC, he0, he, heb⟩ := hK K ι Ω y D M P0 hD har hb hM
  have hHs : IsSmoothHerm (fsH ι) := by
    have h := (hP K ι P0 (mCoordIdeal y) M 0 1 hM.semipos le_rfl zero_le_one).1
    have h' : (HermLine.zcomb M (fsH ι) 0 1).h = (fsH ι).h := by
      funext z
      simp [HermLine.zcomb]
    unfold IsSmoothHerm at h ⊢
    rwa [h'] at h
  refine ⟨k, e, C, hk, hC, he0, he, heb, fun p q hp hpq => ?_,
    hL K ι Ω y D M (fsH ι) II k hII har hM.semipos.1 hHs⟩
  have hkq : k * p ≤ q := hpq.le
  have ha : (HermLine.zcomb M (fsH ι) ((q : ℤ) - k * p) p).a =
      ((q - k * p : ℕ) : ℤ) • M.a + fun _ => ((p : ℕ) : ℤ) := by
    funext i
    simp [HermLine.zcomb, fsH, ReciprocityTheory.ChartRestriction.G.Geo.HermLine.ofMetrics, Nat.cast_sub hkq]
  have hb0 : (0 : ℤ) ≤ (q : ℤ) - k * p := by
    have : ((k * p : ℕ) : ℤ) ≤ q := by exact_mod_cast hkq
    push_cast at this
    linarith
  refine ⟨hP K ι P0 (mCoordIdeal y) M _ _ hM.semipos hb0 (Nat.cast_nonneg p),
    HermLine.zcomb_isConjInvariantH hM.conjInv (fsH_isConjInvariantH ι) _ _, ?_, fun ℓ hℓ => ?_, ?_⟩
  · rw [ha]
    exact hG K ι Ω y D M P0 (q - k * p) p har hM.normalForm_baseLattice_le_dualSpan_sup_line hM.semipos (by omega) hp
  · rw [ha]
    exact hF K ι Ω y D M.a (q - k * p) p ℓ har hM.nef (by omega) hp hℓ
  intro n s hs
  have hB : e ∈ chartLat y (HermLine.zcomb M (fsH ι) k (-1)).a 1 := by
    have h' : (HermLine.zcomb M (fsH ι) k (-1)).a = (k : ℤ) • M.a - 1 := by
      funext i
      simp [HermLine.zcomb, fsH, ReciprocityTheory.ChartRestriction.G.Geo.HermLine.ofMetrics]
      ring
    rw [h']
    exact he
  have hdeg : ((q * n : ℕ) : ℤ) • M.a = (n : ℤ) • (HermLine.zcomb M (fsH ι) ((q : ℤ) - k * p) p).a +
      ((p * n : ℕ) : ℤ) • (HermLine.zcomb M (fsH ι) k (-1)).a := by
    funext i
    simp [HermLine.zcomb, fsH, ReciprocityTheory.ChartRestriction.G.Geo.HermLine.ofMetrics]
    ring
  have hmet : ∀ z ∈ mcPts (mCoordIdeal y), M.h z ^ (q * n) =
      (HermLine.zcomb M (fsH ι) ((q : ℤ) - k * p) p).h z ^ n *
        (HermLine.zcomb M (fsH ι) k (-1)).h z ^ (p * n) := fun z hz =>
    zcomb_metric_identity (M.pos z hz.1).ne' ((fsH ι).pos z hz.1).ne' q k p n
  obtain ⟨hmem, hbd⟩ := hS K ι Ω y (HermLine.zcomb M (fsH ι) ((q : ℤ) - k * p) p)
    (HermLine.zcomb M (fsH ι) k (-1)) M n (p * n) (q * n) s e hdeg hmet hs hB
  refine ⟨hmem, fun c hc => ?_⟩
  have h := hbd c (Real.exp C) hc heb
  rwa [← Real.exp_nat_mul] at h

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGridSeparation
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

namespace GridSeparation

theorem norm_eval_le_of_torus {e : ℕ} (G : MvPolynomial (Fin e) ℤ) (ζ : Fin e → ℂ) (hζ : ∀ i, ‖ζ i‖ = 1) :
    ‖eval ζ (map (Int.castRingHom ℂ) G)‖ ≤ ∑ d ∈ G.support, ((|G.coeff d| : ℤ) : ℝ) := by
  rw [eval_map, eval₂_eq]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun d _ => ?_)
  rw [norm_mul, norm_prod]
  simp [hζ]

theorem grid_finite (e m : ℕ) (hm : 0 < m) : {ζ : Fin e → ℂ | ∀ i, ζ i ^ m = 1}.Finite := by
  have h1 : {x : ℂ | x ^ m = 1}.Finite :=
    (Polynomial.nthRoots m (1 : ℂ)).toFinset.finite_toSet.subset fun x hx => by
      simpa [Polynomial.mem_nthRoots hm] using hx
  convert Set.Finite.pi (t := fun _ : Fin e => {x : ℂ | x ^ m = 1}) fun _ => h1 using 1
  ext ζ
  simp [Set.mem_pi]

theorem norm_of_pow_eq_one {m : ℕ} (hm : 0 < m) {x : ℂ} (hx : x ^ m = 1) : ‖x‖ = 1 :=
  (pow_eq_one_iff_of_nonneg (norm_nonneg x) hm.ne').mp (by rw [← norm_pow, hx, norm_one])

theorem proof (hNL : NormalLocusRep.Statement) (hFN : FibreNormBound.Statement)
    (hRG : RootGridLower.Statement) : GridSeparation.Statement := by
  classical
  intro K _ ι _ Ω _ y D A hV hBir hA
  obtain ⟨df, f, hf, hfP, hrep⟩ := hNL K ι Ω y D hV hBir
  obtain ⟨n, c, B, G, Fib, hn, hB1, hG0, hFib, hnorm⟩ := hFN K ι Ω y D A df f hV hBir hA hf hfP
  set SG : ℝ := ∑ d ∈ G.support, ((|G.coeff d| : ℤ) : ℝ) + 1 with hSG
  have hSG1 : 1 ≤ SG := by
    have : 0 ≤ ∑ d ∈ G.support, ((|G.coeff d| : ℤ) : ℝ) := Finset.sum_nonneg fun d _ => by positivity
    linarith
  have hX : 1 ≤ 2 * B * SG := by nlinarith
  refine ⟨Real.log (2 * B * SG), Real.log_nonneg hX, fun τ => ?_⟩
  set m := G.totalDegree + c * (τ + 1) + 1 with hm
  have hm0 : 0 < m := by omega
  set Z := ((grid_finite (D + 1) m hm0).toFinset.filter
    fun ζ => eval ζ (map (Int.castRingHom ℂ) G) ≠ 0).biUnion Fib with hZ
  have hmem : ∀ ζ : Fin (D + 1) → ℂ, (∀ i, ζ i ^ m = 1) → eval ζ (map (Int.castRingHom ℂ) G) ≠ 0 →
      ∀ z ∈ Fib ζ, z ∈ Z := fun ζ hζ hG z hz =>
    Finset.mem_biUnion.mpr ⟨ζ, Finset.mem_filter.mpr ⟨(Set.Finite.mem_toFinset _).mpr hζ, hG⟩, hz⟩
  have hZpt : ∀ z ∈ Z, z ∈ mcPts (mCoordIdeal y) ∧ eval z (map (Int.castRingHom ℂ) f) ≠ 0 := by
    intro z hz
    obtain ⟨ζ, hζ, hzζ⟩ := Finset.mem_biUnion.mp hz
    obtain ⟨hζg, hGζ⟩ := Finset.mem_filter.mp hζ
    have hζg' : ∀ i, ζ i ^ m = 1 := (Set.Finite.mem_toFinset _).mp hζg
    exact hFib ζ (fun i => norm_of_pow_eq_one hm0 (hζg' i)) hGζ z hzζ
  refine ⟨Z, fun z hz => (hZpt z hz).1, fun s hs z hz => hrep A.a τ s hs z (hZpt z hz).1 (hZpt z hz).2, ?_⟩
  intro u hu hu0
  obtain ⟨F, hF0, hFdeg, hFb⟩ := hnorm τ u hu hu0
  by_contra hcon
  obtain ⟨ζ, hζm, hζ1⟩ := hRG (D + 1) m (G * F) (mul_ne_zero hG0 hF0) fun i => by
    have h1 := degreeOf_mul_le i G F
    have h2 := degreeOf_le_totalDegree G i
    have h3 := hFdeg i
    omega
  have hζn : ∀ i, ‖ζ i‖ = 1 := fun i => norm_of_pow_eq_one hm0 (hζm i)
  rw [map_mul, eval_mul, norm_mul] at hζ1
  have hGζ : eval ζ (map (Int.castRingHom ℂ) G) ≠ 0 := by
    intro h
    rw [h, norm_zero, zero_mul] at hζ1
    linarith
  set E := Real.exp (-(Real.log (2 * B * SG) * ((τ : ℝ) + 1))) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have hFle := hFb ζ hζn hGζ E hE0.le fun z hz => by
    obtain ⟨dg, dh, g, h, hg, hh, hd, hy, hz0⟩ :=
      hrep A.a τ u hu z (hFib ζ hζn hGζ z hz).1 (hFib ζ hζn hGζ z hz).2
    refine ⟨dg, dh, g, h, hg, hh, hd, hy, hz0, ?_⟩
    by_contra hlt
    exact hcon ⟨z, hmem ζ hζm hGζ z hz, dg, dh, g, h, hg, hh, hd, hy, hz0, (not_le.mp hlt).le⟩
  have hEX : E * (2 * B * SG) ^ (τ + 1) = 1 := by
    have : -(Real.log (2 * B * SG) * ((τ : ℝ) + 1)) = ((τ + 1 : ℕ) : ℝ) * (-Real.log (2 * B * SG)) := by
      push_cast
      ring
    rw [hE, this, Real.exp_nat_mul, Real.exp_neg, Real.exp_log (by linarith), ← mul_pow,
      inv_mul_cancel₀ (by linarith), one_pow]
  have hE1 : E ≤ 1 := by
    have : 1 ≤ (2 * B * SG) ^ (τ + 1) := one_le_pow₀ hX
    nlinarith
  have hEn : E ^ n ≤ E := pow_le_of_le_one hE0.le hE1 (by omega)
  have hGle : ‖eval ζ (map (Int.castRingHom ℂ) G)‖ ≤ SG := by
    have := norm_eval_le_of_torus G ζ hζn
    linarith
  have hpow : 2 * SG * B ^ (τ + 1) ≤ (2 * B * SG) ^ (τ + 1) := by
    rw [show 2 * B * SG = (2 * SG) * B by ring, mul_pow]
    have hB0 : 0 ≤ B ^ (τ + 1) := pow_nonneg (by linarith) _
    have : 2 * SG ≤ (2 * SG) ^ (τ + 1) := le_self_pow₀ (by linarith) (by omega)
    nlinarith
  have hBp : 0 ≤ B ^ (τ + 1) := pow_nonneg (by linarith) _
  have hFn : ‖eval ζ (map (Int.castRingHom ℂ) F)‖ ≤ B ^ (τ + 1) * E := by
    calc _ ≤ B ^ (τ + 1) * E ^ n := hFle
      _ ≤ B ^ (τ + 1) * E := mul_le_mul_of_nonneg_left hEn hBp
  have key : 2 * (SG * (B ^ (τ + 1) * E)) ≤ 1 := by
    calc 2 * (SG * (B ^ (τ + 1) * E)) = (2 * SG * B ^ (τ + 1)) * E := by ring
      _ ≤ (2 * B * SG) ^ (τ + 1) * E := mul_le_mul_of_nonneg_right hpow hE0.le
      _ = 1 := by rw [mul_comm, hEX]
  have hFnn : 0 ≤ ‖eval ζ (map (Int.castRingHom ℂ) F)‖ := norm_nonneg _
  have : ‖eval ζ (map (Int.castRingHom ℂ) G)‖ * ‖eval ζ (map (Int.castRingHom ℂ) F)‖ ≤
      SG * (B ^ (τ + 1) * E) :=
    mul_le_mul hGle hFn hFnn (by linarith)
  linarith

end GridSeparation

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.IsSemipositiveRelConstShift
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

noncomputable section

section Shift

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]


omit [∀ k, Fintype (ι k)] in
theorem constShift_a (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (η : ℝ) : (HermLine.constShift A η).a = A.a := by
  simp [HermLine.constShift, ReciprocityTheory.ChartRestriction.G.Geo.HermLine.tensor, ReciprocityTheory.ChartRestriction.G.Geo.HermLine.ofWeight]

omit [∀ k, Fintype (ι k)] in
theorem constShift_h (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (η : ℝ) (z : (Σ k, ι k) → ℂ) :
    (HermLine.constShift A η).h z = A.h z * Real.exp (-η) := rfl

theorem isSmoothHerm_constShift {A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} (hA : IsSmoothHerm A) (η : ℝ) :
    IsSmoothHerm (HermLine.constShift A η) := by
  have : (HermLine.constShift A η).h = fun z => A.h z * Real.exp (-η) := rfl
  unfold IsSmoothHerm at hA ⊢
  rw [this]
  exact hA.mul contDiffOn_const

omit [∀ k, Fintype (ι k)] in
theorem isConjInvariantH_constShift {A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} (hA : IsConjInvariantH A) (η : ℝ) :
    IsConjInvariantH (HermLine.constShift A η) := by
  intro z
  rw [constShift_h, constShift_h, hA z]

theorem leviForm_constShift (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (η : ℝ) {z : (Σ k, ι k) → ℂ}
    (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) (w : (Σ k, ι k) → ℂ) :
    leviForm (fun x => Real.log ((HermLine.constShift A η).h x)) z w =
      leviForm (fun x => Real.log (A.h x)) z w := by
  have hU : IsOpen {x : (Σ k, ι k) → ℂ | ∀ k, ∃ i, x ⟨k, i⟩ ≠ 0} := by
    have : {x : (Σ k, ι k) → ℂ | ∀ k, ∃ i, x ⟨k, i⟩ ≠ 0} = ⋂ k, ⋃ i, {x | x ⟨k, i⟩ ≠ 0} := by
      ext x
      simp
    rw [this]
    exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i =>
      isOpen_ne_fun (continuous_apply _) continuous_const
  have h1 : (fun x => Real.log ((HermLine.constShift A η).h x)) =ᶠ[𝓝 z]
      fun x => Real.log (A.h x) + (-η) := by
    filter_upwards [hU.mem_nhds hz] with x hx
    rw [constShift_h, Real.log_mul (A.pos x hx).ne' (Real.exp_pos _).ne', Real.log_exp]
  have h2 : fderiv ℝ (fun x => Real.log ((HermLine.constShift A η).h x)) =ᶠ[𝓝 z]
      fderiv ℝ (fun x => Real.log (A.h x)) := by
    filter_upwards [h1.eventuallyEq_nhds] with x hx
    rw [hx.fderiv_eq, fderiv_add_const]
  unfold leviForm
  rw [h2.fderiv_eq]

theorem isSemipositiveRel_constShift {P0 P : Ideal (MRing ι)} {A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι}
    (hA : IsSemipositiveRel P0 P A) (η : ℝ) : IsSemipositiveRel P0 P (HermLine.constShift A η) := by
  refine ⟨isSmoothHerm_constShift hA.1 η, fun z hz w hw => ?_⟩
  rw [leviForm_constShift A η hz.1 w]
  exact hA.2 z hz w hw

end Shift

theorem exists_small_section_of_arithmeticVolume_pos {Ω : Type} [Field Ω] {Pr : ℕ → Ω → Prop} {La : ℕ → AddSubgroup Ω}
    {D : ℕ} (h : 0 < arVolP Pr La 1 D) : ∃ n, 1 ≤ n ∧ ∃ s ∈ La n, s ≠ 0 ∧ Pr n s := by
  by_contra hne
  push Not at hne
  have hzero : ∀ k, 1 ≤ k → smallSectionCount Pr La k = 0 := by
    intro k hk
    have hsub : Subsingleton {s : La k // Pr k (s : Ω)} := by
      constructor
      rintro ⟨a, ha⟩ ⟨b, hb⟩
      have ha0 : (a : Ω) = 0 := by
        by_contra h0
        exact hne k hk a a.2 h0 ha
      have hb0 : (b : Ω) = 0 := by
        by_contra h0
        exact hne k hk b b.2 h0 hb
      exact Subtype.ext (Subtype.ext (ha0.trans hb0.symm))
    have := hsub
    have hc : Nat.card {s : La k // Pr k (s : Ω)} ≤ 1 := Finite.card_le_one_iff_subsingleton.mpr hsub
    unfold smallSectionCount
    interval_cases Nat.card {s : La k // Pr k (s : Ω)} <;> simp
  have : arVolP Pr La 1 D = 0 := by
    unfold arVolP
    refine (limsup_congr ?_).trans (limsup_const 0)
    filter_upwards [eventually_ge_atTop 1] with k hk
    rw [one_mul, hzero k hk, zero_div]
  linarith

theorem G4.proof (hG6 : ArithmeticVolumeBig.Statement) (hCS : ConstantShift.Statement) : G4.Statement := by
  intro K _ ι _ Ω _ _ y D M P0 II hD hII har hb hM hpos
  obtain ⟨η, hη0, hηlt⟩ : ∃ η : ℝ, 0 < η ∧ ((D : ℝ) + 1) * η * geomDeg (mCoordIdeal y) M D <
      II K ι (mCoordIdeal y) (D + 1) (fun _ => M) := by
    set T := II K ι (mCoordIdeal y) (D + 1) (fun _ => M)
    set g := geomDeg (mCoordIdeal y) M D
    have hden : 0 < 2 * (((D : ℝ) + 1) * |g| + 1) := by positivity
    refine ⟨T / (2 * (((D : ℝ) + 1) * |g| + 1)), div_pos hpos hden, ?_⟩
    set η := T / (2 * (((D : ℝ) + 1) * |g| + 1))
    have hη0 : 0 < η := div_pos hpos hden
    have he : η * (2 * (((D : ℝ) + 1) * |g| + 1)) = T := div_mul_cancel₀ T hden.ne'
    have h1 : ((D : ℝ) + 1) * η * g ≤ ((D : ℝ) + 1) * η * |g| :=
      mul_le_mul_of_nonneg_left (le_abs_self g) (by positivity)
    have h3 : 0 ≤ ((D : ℝ) + 1) * η * |g| := by positivity
    nlinarith
  have hshift := hCS K ι (II K ι) (mCoordIdeal y) D M η (hII K ι) har hM.semipos.1
  have hpos' : 0 < II K ι (mCoordIdeal y) (D + 1) (fun _ => HermLine.constShift M η) := by
    rw [hshift]
    linarith
  have hvol := hG6 K ι Ω y D (HermLine.constShift M η) P0 II hD hII har hb hM.normalForm_baseLattice_le_dualSpan_sup_line
    (isSemipositiveRel_constShift hM.semipos η) (by rw [constShift_a]; exact hM.nef)
    (isConjInvariantH_constShift hM.conjInv η)
  obtain ⟨n, hn, s, hs, hs0, hsmall⟩ := exists_small_section_of_arithmeticVolume_pos (hpos'.trans_le hvol)
  have hn' : (0 : ℝ) < n * η := mul_pos (by exact_mod_cast hn) hη0
  refine ⟨n, s, hn, by rwa [constShift_a] at hs, hs0, Real.exp (-(n * η)), ?_, ?_⟩
  · rw [Real.exp_lt_one_iff]
    linarith
  · intro dg dh g h z hg hh hdeg heq hz
    have hle := hsmall dg dh g h z hg hh (by rw [constShift_a]; exact hdeg) heq hz
    have e : Real.exp (-(n * η)) = Real.exp (-η) ^ n := by
      rw [← Real.exp_nat_mul]
      ring_nf
    refine hle.trans (le_of_eq ?_)
    rw [constShift_h, mul_pow, e]
    ring

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBergmanDensIntegrable
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MeasureTheory Set ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.CP

noncomputable section

def BergmanDensIntegrable.Statement : Prop :=
  ∀ {D : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X]
    [BorelSpace X] (A : FinHolAtlas D X) (L : HolLineBundle A) (W : Weight L)
    (dV : SmoothVolume A), Integrable (bergmanDens W dV) dV.μ

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBergmanIntegrable
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MeasureTheory Set ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.CP

noncomputable section

def BergmanIntegrable.Statement : Prop :=
  ∀ {D : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X]
    [BorelSpace X] (A : FinHolAtlas D X) (L : HolLineBundle A) (W : Weight L)
    (dV : SmoothVolume A) (n : ℕ) (V : Submodule ℂ (Fin A.n → X → ℂ)) [FiniteDimensional ℂ V],
    V ≤ L.sections n → Integrable (bergman W dV V n) dV.μ

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBlockImageGenDeg
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter Asymptotics

noncomputable section

def BlockImageGenDeg.Statement : Prop :=
  ∀ (D : ℕ) (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (κ : Type) [Fintype κ] (y : (Σ k, ι k) → Ω) (k₀ : K) (M : Matrix (Ix κ) (ι k₀) ℤ)
    (N : Matrix (ι k₀) (Ix κ) ℤ) (x : Ix κ → Ω),
    IsArithVar (mCoordIdeal y) (D + 1) → BlockBirational y k₀ → IsBlockImage y k₀ M N x →
    genDeg (ι := GlobalTheory κ) (coordIdeal ℤ x) D 1 = genDeg (mCoordIdeal y) D (unitDeg k₀)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
