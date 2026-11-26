module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.RiemannLatticeEigenProjection
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ArithIntersectionMultilinearAll
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.IsChainFirst

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.LogIntegralMultilinear
section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.IntersectionSystemDegree
section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.IntersectionSystemDegree
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem degreeStatement_of_intersectionSystem :
    ∀ II : IntersectionSystem, IsIntersectionSystem II → ReciprocityTheory.ChartRestriction.G.Geo.DegreeStatement :=
  fun II h => GlobalTheory.CompanionTheory.Ar.Giv.degree_of_isIntersectionSystem II h

end GlobalTheory.CompanionTheory.Ar.Top
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.IntersectionSystemDegreeStatement
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intersection_system_degree : ∀ II : IntersectionSystem, IsIntersectionSystem II → ReciprocityTheory.ChartRestriction.G.Geo.DegreeStatement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.degreeStatement_of_intersectionSystem | exact GlobalTheory.CompanionTheory.Ar.Top.degreeStatement_of_intersectionSystem | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.degreeStatement_of_intersectionSystem <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ArithIntersectionConstantMetric
section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ArithIntersectionConstantMetric
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem intersection_snoc_constWeight : ∀ II : IntersectionSystem, IsIntersectionSystem II → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ) (L : Fin e → HermLine ι) (c : ℝ), IsArithVar P (e + 1) → (∀ j, IsSmoothHerm (L j)) → II K ι P (e + 1) (Fin.snoc L (HermLine.ofWeight (fun _ => c) (fun _ _ _ => rfl))) = -c * ptsIntegral P (fun j z => Real.log ((L j).h z)) (fun _ => 1) :=
  RootFieldNumerics.intersection_constant_metric_line

end GlobalTheory.CompanionTheory.Ar.Top
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ArithIntersectionConstantMetricStatement
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arith_intersection_constant_metric : ∀ II : IntersectionSystem, IsIntersectionSystem II → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ) (L : Fin e → HermLine ι) (c : ℝ), IsArithVar P (e + 1) → (∀ j, IsSmoothHerm (L j)) → II K ι P (e + 1) (Fin.snoc L (HermLine.ofWeight (fun _ => c) (fun _ _ _ => rfl))) = -c * ptsIntegral P (fun j z => Real.log ((L j).h z)) (fun _ => 1) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.intersection_snoc_constWeight | exact GlobalTheory.CompanionTheory.Ar.Top.intersection_snoc_constWeight | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.intersection_snoc_constWeight <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.LogIntegralMultilinear
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Top.GeoMix

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem line_ext {A B : HermLine ι} (ha : A.a = B.a) (hh : A.h = B.h) : A = B := by
  cases A
  cases B
  cases ha
  cases hh
  rfl

def oneLine (ι : K → Type) [∀ k, Fintype (ι k)] : HermLine ι :=
  HermLine.ofWeight (fun _ => (-1 : ℝ)) (fun _ _ _ => rfl)

theorem smooth_oneLine : IsSmoothHerm (oneLine ι) := by
  show ContDiffOn ℝ _ (fun _ => Real.exp (-(-1 : ℝ))) _
  exact contDiffOn_const

theorem smooth_comb {J : Type} [Fintype J] {ℓ : J → HermLine ι} (hℓ : ∀ j, IsSmoothHerm (ℓ j))
    (n : J → ℤ) : IsSmoothHerm (combLine ℓ n) := by
  refine contDiffOn_prod fun a _ => ?_
  intro z hz
  have h0 : (ℓ a).h z ≠ 0 := ((ℓ a).pos z hz).ne'
  have hf := hℓ a z hz
  have key : ∀ m : ℤ, ContDiffWithinAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => (ℓ a).h z ^ m)
      {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} z := by
    intro m
    cases m with
    | ofNat k => simpa only [Int.ofNat_eq_natCast, zpow_natCast] using hf.pow k
    | negSucc k =>
      simp only [zpow_negSucc]
      exact (hf.pow (k + 1)).inv (pow_ne_zero _ h0)
  exact key _

def extLine {J : Type} (ℓ : J → HermLine ι) : Option J → HermLine ι
  | none => oneLine ι
  | some j => ℓ j

def extExp {J : Type} (m : J → ℤ) : Option J → ℤ
  | none => 0
  | some j => m j

def lastExp {J : Type} : Option J → ℤ
  | none => 1
  | some _ => 0

theorem comb_extExp {J : Type} [Fintype J] (ℓ : J → HermLine ι) (m : J → ℤ) :
    combLine (extLine ℓ) (extExp m) = combLine ℓ m := by
  apply line_ext
  · simp [combLine, Fintype.sum_option, extLine, extExp]
  · funext z
    simp [combLine, Fintype.prod_option, extLine, extExp]

theorem comb_lastExp {J : Type} [Fintype J] (ℓ : J → HermLine ι) :
    combLine (extLine ℓ) lastExp = oneLine ι := by
  apply line_ext
  · simp [combLine, Fintype.sum_option, extLine, lastExp]
  · funext z
    simp [combLine, Fintype.prod_option, extLine, lastExp]

theorem pts_eq_II (II : IntersectionSystem) (hII : IsFullIntersectionSystem II) (P : Ideal (MRing ι))
    {e : ℕ} (L : Fin e → HermLine ι) (hP : IsArithVar P (e + 1)) (hL : ∀ j, IsSmoothHerm (L j)) :
    ptsIntegral P (fun k z => Real.log ((L k).h z)) (fun _ => 1) =
      II K ι P (e + 1) (Fin.snoc L (oneLine ι)) := by
  have h := GlobalTheory.T.arith_intersection_constant_metric II hII.1 K ι P e L (-1) hP hL
  have h' : II K ι P (e + 1) (Fin.snoc L (oneLine ι)) =
      - -1 * ptsIntegral P (fun j z => Real.log ((L j).h z)) (fun _ => 1) := h
  rw [h']
  ring

theorem pts_comb (II : IntersectionSystem) (hII : IsFullIntersectionSystem II) (P : Ideal (MRing ι))
    {e : ℕ} {J : Type} [Fintype J] [DecidableEq J] (ℓ : J → HermLine ι) (n : Fin e → J → ℤ)
    (hP : IsArithVar P (e + 1)) (hℓ : ∀ j, IsSmoothHerm (ℓ j)) :
    ptsIntegral P (fun k z => Real.log ((combLine ℓ (n k)).h z)) (fun _ => 1) =
      ∑ w : Fin e → J, (∏ k, (n k (w k) : ℝ)) *
        ptsIntegral P (fun k z => Real.log ((ℓ (w k)).h z)) (fun _ => 1) := by
  have hext : ∀ o, IsSmoothHerm (extLine ℓ o) := by
    intro o
    cases o with
    | none => exact smooth_oneLine
    | some j => exact hℓ j
  let n' : Fin (e + 1) → Option J → ℤ :=
    Fin.snoc (α := fun _ => Option J → ℤ) (fun k => extExp (n k)) lastExp
  have hn'c : ∀ k : Fin e, n' k.castSucc = extExp (n k) := fun k => by simp [n']
  have hn'l : n' (Fin.last e) = lastExp := by simp [n']
  have hcomb : (Fin.snoc (fun k => combLine ℓ (n k)) (oneLine ι) : Fin (e + 1) → HermLine ι) =
      fun k => combLine (extLine ℓ) (n' k) := by
    funext k
    refine Fin.lastCases ?_ (fun k => ?_) k
    · simp [hn'l, comb_lastExp]
    · simp [hn'c, comb_extExp]
  rw [pts_eq_II II hII P _ hP (fun k => smooth_comb hℓ _), hcomb,
    GlobalTheory.T.arith_intersection_multilinear_all II hII K ι P (e + 1) (Option J) (extLine ℓ) n' hP hext]
  symm
  let E : (Fin e → J) → (Fin (e + 1) → Option J) := fun w =>
    Fin.snoc (α := fun _ => Option J) (fun k => some (w k)) none
  have hEc : ∀ (w : Fin e → J) (k : Fin e), E w k.castSucc = some (w k) := fun w k => by simp [E]
  have hEl : ∀ w : Fin e → J, E w (Fin.last e) = none := fun w => by simp [E]
  refine Finset.sum_of_injOn E ?_ ?_ ?_ ?_
  · intro w _ w' _ h
    funext k
    have := congrFun h k.castSucc
    rw [hEc, hEc] at this
    exact Option.some.inj this
  · intro w _
    exact Finset.mem_coe.2 (Finset.mem_univ _)
  · intro v _ hv
    have hzero : ∏ k, (n' k (v k) : ℝ) = 0 := by
      by_cases hl : v (Fin.last e) = none
      · by_cases hs : ∀ k : Fin e, (v k.castSucc).isSome
        · exfalso
          apply hv
          refine ⟨fun k => (v k.castSucc).get (hs k), Finset.mem_coe.2 (Finset.mem_univ _), ?_⟩
          funext k
          refine Fin.lastCases ?_ (fun k => ?_) k
          · rw [hEl, hl]
          · rw [hEc]
            simp
        · push_neg at hs
          obtain ⟨k, hk⟩ := hs
          have hk' : v k.castSucc = none := by simpa using hk
          refine Finset.prod_eq_zero (Finset.mem_univ k.castSucc) ?_
          rw [hk', hn'c]
          simp [extExp]
      · obtain ⟨j, hj⟩ := Option.ne_none_iff_exists'.1 hl
        refine Finset.prod_eq_zero (Finset.mem_univ (Fin.last e)) ?_
        rw [hj, hn'l]
        simp [lastExp]
    rw [hzero, zero_mul]
  · intro w _
    have hlines : (fun k => extLine ℓ (E w k)) =
        (Fin.snoc (fun k => ℓ (w k)) (oneLine ι) : Fin (e + 1) → HermLine ι) := by
      funext k
      refine Fin.lastCases ?_ (fun k => ?_) k
      · simp [hEl, extLine]
      · simp [hEc, extLine]
    rw [hlines, ← pts_eq_II II hII P _ hP (fun k => hℓ _), Fin.prod_univ_castSucc]
    simp [hn'c, hn'l, hEc, hEl, extExp, lastExp]

theorem pts_perm (II : IntersectionSystem) (hII : IsFullIntersectionSystem II) (P : Ideal (MRing ι))
    {e : ℕ} (L : Fin e → HermLine ι) (σ : Equiv.Perm (Fin e)) (hP : IsArithVar P (e + 1))
    (hL : ∀ j, IsSmoothHerm (L j)) :
    ptsIntegral P (fun k z => Real.log ((L (σ k)).h z)) (fun _ => 1) =
      ptsIntegral P (fun k z => Real.log ((L k).h z)) (fun _ => 1) := by
  let τ : Equiv.Perm (Fin (e + 1)) :=
    (finSuccEquivLast.trans (Equiv.optionCongr σ)).trans finSuccEquivLast.symm
  have hτc : ∀ k : Fin e, τ k.castSucc = (σ k).castSucc := fun k => by simp [τ]
  have hτl : τ (Fin.last e) = Fin.last e := by simp [τ]
  have hcomp : (Fin.snoc (fun k => L (σ k)) (oneLine ι) : Fin (e + 1) → HermLine ι) =
      (Fin.snoc L (oneLine ι) : Fin (e + 1) → HermLine ι) ∘ τ := by
    funext k
    refine Fin.lastCases ?_ (fun k => ?_) k
    · simp [hτl]
    · simp [hτc]
  have hsm : ∀ j, IsSmoothHerm ((Fin.snoc L (oneLine ι) : Fin (e + 1) → HermLine ι) j) := by
    intro j
    refine Fin.lastCases ?_ (fun k => ?_) j
    · simpa using smooth_oneLine
    · simpa using hL k
  rw [pts_eq_II II hII P _ hP (fun k => hL _), pts_eq_II II hII P _ hP hL, hcomp]
  exact (hII.1 K ι).1 P (e + 1) _ τ hP hsm

theorem pts_deg (II : IntersectionSystem) (hII : IsFullIntersectionSystem II) (P : Ideal (MRing ι))
    {e : ℕ} (L L' : Fin e → HermLine ι) (hP : IsArithVar P (e + 1)) (hL : ∀ j, IsSmoothHerm (L j))
    (hL' : ∀ j, IsSmoothHerm (L' j)) (ha : ∀ k, (L' k).a = (L k).a) :
    ptsIntegral P (fun k z => Real.log ((L' k).h z)) (fun _ => 1) =
      ptsIntegral P (fun k z => Real.log ((L k).h z)) (fun _ => 1) := by
  have hD := GlobalTheory.T.intersection_system_degree II hII.1
  have h1 : ptsIntegral P (fun k z => Real.log ((L k).h z)) (fun _ => 1) = _ :=
    hD K ι P e L 2 hP hL Nat.prime_two
  have h2 : ptsIntegral P (fun k z => Real.log ((L' k).h z)) (fun _ => 1) = _ :=
    hD K ι P e L' 2 hP hL' Nat.prime_two
  have hdeg : (fun j => (L' j).a) = fun j => (L j).a := funext ha
  rw [h1, h2, hdeg]

end GlobalTheory.CompanionTheory.Ar.Top.GeoMix

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem geo_multilin : ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ) (J : Type) [Fintype J] [DecidableEq J] (ℓ : J → HermLine ι) (n : Fin e → J → ℤ), IsArithVar P (e + 1) → (∀ j, IsSmoothHerm (ℓ j)) → (ptsIntegral P (fun k z => Real.log ((combLine ℓ (n k)).h z)) (fun _ => 1) = ∑ w : Fin e → J, (∏ k, (n k (w k) : ℝ)) * ptsIntegral P (fun k z => Real.log ((ℓ (w k)).h z)) (fun _ => 1)) ∧ (∀ (L L' : Fin e → HermLine ι) (σ : Equiv.Perm (Fin e)), (∀ k, IsSmoothHerm (L k)) → (∀ k, IsSmoothHerm (L' k)) → (∀ k, (L' k).a = (L (σ k)).a) → ptsIntegral P (fun k z => Real.log ((L' k).h z)) (fun _ => 1) = ptsIntegral P (fun k z => Real.log ((L k).h z)) (fun _ => 1)) := by
  intro II hII K _ ι _ P e J _ _ ℓ n hP hℓ
  refine ⟨GeoMix.pts_comb II hII P ℓ n hP hℓ, ?_⟩
  intro L L' σ hL hL' ha
  rw [GeoMix.pts_deg II hII P (fun k => L (σ k)) L' hP (fun k => hL _) hL' ha]
  exact GeoMix.pts_perm II hII P L σ hP hL

end GlobalTheory.CompanionTheory.Ar.Top
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.LogIntegralMultilinearStatement
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_integral_multilinear : ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ) (J : Type) [Fintype J] [DecidableEq J] (ℓ : J → HermLine ι) (n : Fin e → J → ℤ), IsArithVar P (e + 1) → (∀ j, IsSmoothHerm (ℓ j)) → (ptsIntegral P (fun k z => Real.log ((combLine ℓ (n k)).h z)) (fun _ => 1) = ∑ w : Fin e → J, (∏ k, (n k (w k) : ℝ)) * ptsIntegral P (fun k z => Real.log ((ℓ (w k)).h z)) (fun _ => 1)) ∧ (∀ (L L' : Fin e → HermLine ι) (σ : Equiv.Perm (Fin e)), (∀ k, IsSmoothHerm (L k)) → (∀ k, IsSmoothHerm (L' k)) → (∀ k, (L' k).a = (L (σ k)).a) → ptsIntegral P (fun k z => Real.log ((L' k).h z)) (fun _ => 1) = ptsIntegral P (fun k z => Real.log ((L k).h z)) (fun _ => 1)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.geo_multilin | exact GlobalTheory.CompanionTheory.Ar.Top.geo_multilin | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.geo_multilin <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.IsBlockMapDrop
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Top.FlDeg

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GroundTheory.Heights₂.Heights.LowerBoundFree

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ} {K : Type}

theorem isBlockMap_drop (j : K → FlBlock Ψ N) (k₀ : K) :
    IsBlockMap (Subtype.val : {k // k ≠ k₀} → K) (dropV j k₀) := by
  refine ⟨Subtype.val_injective, ?_, fun _ => rfl, ?_⟩
  · rintro ⟨⟨a, ha⟩, x⟩ ⟨⟨b, hb⟩, y⟩ h
    have h' : (⟨a, x⟩ : Σ k, PIdx j k) = ⟨b, y⟩ := h
    cases h'
    rfl
  · rintro ⟨k, x⟩ ⟨⟨k', hk⟩, rfl⟩
    exact ⟨⟨⟨k', hk⟩, x⟩, rfl⟩

theorem imageZ_drop [Fintype K] [DecidableEq K] (j : K → FlBlock Ψ N) (k₀ : K) :
    imageZ (dropV j k₀) (PPart j) = PPart (dropJ j k₀) := by
  have key : ∀ f : MRing (PIdx (dropJ j k₀)), mConeMap (yPart j) (rename (dropV j k₀) f) =
      rename Subtype.val (mConeMap (yPart (dropJ j k₀)) f) := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C a => simp [mConeMap]
    | add p q hp hq => simp [hp, hq]
    | mul_X p n hp =>
      simp only [map_mul, hp, rename_X]
      congr 1
      simp [mConeMap, yPart, dropV, dropJ]
  ext f
  simp only [imageZ, PPart, mCoordIdeal, Ideal.mem_comap, RingHom.mem_ker]
  show mConeMap (yPart j) (rename (dropV j k₀) f) = 0 ↔ _
  rw [key]
  constructor
  · intro h
    exact rename_injective _ Subtype.val_injective (by rw [h, map_zero])
  · intro h
    have h' : mConeMap (yPart (dropJ j k₀)) f = 0 := h
    rw [h', map_zero]

end GlobalTheory.CompanionTheory.Ar.Top.FlDeg
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.IsometricFamilyIntersectionEq
section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.IsometricFamilyIntersectionEq
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)

namespace GlobalTheory.CompanionTheory.Ar.Num.TopLink

section Cyc

variable {K : Type} [DecidableEq K] {ι : K → Type}

theorem intNumL_perm (F : Type) [Field F] (V : Ideal (MRing ι F)) {l l' : List (K → ℤ)} (h : l.Perm l') :
    intNumL F V l = intNumL F V l' := by
  haveI : LeftCommutative (diffStep : (K → ℤ) → ((K → ℤ) → ℤ) → (K → ℤ) → ℤ) := ⟨fun a b g => by
    funext m
    simp only [diffStep]
    rw [sub_right_comm m a b]
    ring⟩
  unfold intNumL intNum mixedDiff
  rw [List.ofFn_get, List.ofFn_get, h.foldr_eq]

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem cycList_perm (Z : Ideal (MRing ι O) → ℤ) {l l' : List (K → ℤ)} (h : l.Perm l') :
    cycList Z l = cycList Z l' := by
  unfold cycList
  congr 1
  funext W
  exact intNumL_perm (IsLocalRing.ResidueField O) (specialIdeal W) h


omit [DecidableEq K] in
theorem divCycle_mul_finite {R : Type} [CommRing R] [IsNoetherianRing (MRing ι R)] (P : Ideal (MRing ι R))
    (f : MRing ι R) (n : Ideal (MRing ι R) → ℤ) :
    (Function.support fun W => divCycle P f W * n W).Finite := by
  refine (Ideal.finite_minimalPrimes_of_isNoetherianRing _ (P ⊔ Ideal.span {f})).subset ?_
  intro W hW
  by_contra h
  apply hW
  simp only [divCycle]
  rw [dite_eq_right (fun h' => h h'.1), zero_mul]

theorem cycList_ratDiv [Fintype K] [∀ k, Fintype (ι k)] (P : Ideal (MRing ι O)) (f g : MRing ι O)
    (l : List (K → ℤ)) :
    cycList (ratDiv P f g) l = cycList (divCycle P f) l - cycList (divCycle P g) l := by
  unfold cycList cycEval ratDiv
  simp only [sub_mul]
  exact finsum_sub_distrib (divCycle_mul_finite P f _) (divCycle_mul_finite P g _)

end Cyc

theorem link_monomial {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {P : Ideal (MRing ι ℤ)} {D : ℕ} (hP : IsArithVar P (D + 1))
    {I : Ideal (MRing ι ℤ) → (n : ℕ) → (Fin n → HermLine ι) → ℝ} (hI : IsIntersectionFamily I)
    {σ : Type} {S : Finset Nat.Primes} {T : LocPair ι ℤ σ} (hT : T.IsVertOff P S)
    {A A' : σ → HermLine ι} (hA : ∀ i, IsSmoothHerm (A i)) (hA' : ∀ i, IsSmoothHerm (A' i))
    (hiso : T.IsIsometric P A A') (i : σ) (μ : σ ⊕ σ →₀ ℕ) (hμ : μ.toMultiset.card = D) :
    arList I P (((μ + Finsupp.single (Sum.inl i) 1).toMultiset.map (Sum.elim A A')).toList) -
      arList I P (((μ + Finsupp.single (Sum.inr i) 1).toMultiset.map (Sum.elim A A')).toList) =
    ∑ p ∈ S, Real.log (p : ℕ) *
      (cycList (ratDiv (extTo (ZP p) P) (MvPolynomial.map (Int.castRingHom (ZP p)) (T.f i))
        (MvPolynomial.map (Int.castRingHom (ZP p)) (T.g i))) (classList (Sum.elim T.x T.x') μ ++ []) : ℝ) := by
  classical
  set m := μ.toMultiset.toList with hm
  have hlen : m.length = D := by rw [hm, Multiset.length_toList, hμ]
  subst hlen
  let L : Fin m.length → HermLine ι := fun j => Sum.elim A A' (m.get j)
  have hB : ∀ s, IsSmoothHerm (Sum.elim A A' s) := by
    rintro (s | s)
    · exact hA s
    · exact hA' s
  have hL : ∀ j, IsSmoothHerm (L j) := fun j => hB _
  have hofL : List.ofFn L = m.map (Sum.elim A A') := by
    conv_rhs => rw [← List.ofFn_get m]
    rw [List.map_ofFn]
    rfl
  have key : ∀ s, arList I P (((μ + Finsupp.single s 1).toMultiset.map (Sum.elim A A')).toList) =
      I P (m.length + 1) (Fin.snoc L (Sum.elim A A' s)) := by
    intro s
    apply arList_eq_of_perm hP hI
    · intro j
      refine Fin.lastCases ?_ (fun j => ?_) j
      · rw [Fin.snoc_last]; exact hB s
      · rw [Fin.snoc_castSucc]; exact hL j
    · rw [List.ofFn_succ']
      simp only [Fin.snoc_castSucc, Fin.snoc_last]
      rw [show (List.ofFn fun j => L j) = m.map (Sum.elim A A') from hofL, ← Multiset.coe_eq_coe,
        Multiset.coe_toList, List.concat_eq_append, ← Multiset.coe_add, ← Multiset.map_coe, hm,
        Multiset.coe_toList, map_add, Finsupp.toMultiset_single, Multiset.map_add]
      simp
  have hdeg : (List.ofFn fun j => (L j).a).Perm (classList (Sum.elim T.x T.x') μ ++ []) := by
    have h1 : (List.ofFn fun j => (L j).a) = m.map (Sum.elim T.x T.x') := by
      conv_rhs => rw [← List.ofFn_get m]
      rw [List.map_ofFn]
      congr 1
      funext j
      change (Sum.elim A A' (m.get j)).a = Sum.elim T.x T.x' (m.get j)
      cases h : m.get j with
      | inl s => exact (hiso s).1
      | inr s => exact (hiso s).2.1
    rw [h1, List.append_nil, classList, ← Multiset.coe_eq_coe, Multiset.coe_toList, ← Multiset.map_coe, hm,
      Multiset.coe_toList]
  rw [key, key]
  have step := GlobalTheory.T.isometric_vertical_intersection_eq K ι P m.length hP I hI S (T.comp fun _ : Unit => i) (fun _ => hT i)
    (A i) (A' i) (hA i) (hA' i) (fun _ => hiso i) L hL
  refine step.trans (Finset.sum_congr rfl fun p _ => ?_)
  obtain ⟨⟨bf, bg, hf, hg, -⟩, hfP, hgP, -⟩ := hT i
  have e1 := GlobalTheory.T.vertical_number_local_cycle K ι P m.length hP p bf (T.f i) hf hfP (List.ofFn fun j => (L j).a) (by simp)
  have e2 := GlobalTheory.T.vertical_number_local_cycle K ι P m.length hP p bg (T.g i) hg hgP (List.ofFn fun j => (L j).a) (by simp)
  rw [← cycList_perm _ hdeg, cycList_ratDiv, ← e1, ← e2]
  push_cast
  rfl

theorem arNum_eq_sum_log_val : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι ℤ)) (D : ℕ), IsArithVar P (D + 1) → ∀ (I : Ideal (MRing ι ℤ) → (n : ℕ) → (Fin n → HermLine ι) → ℝ), IsIntersectionFamily I → ∀ (σ : Type) [Fintype σ] (S : Finset Nat.Primes) (T : LocPair ι ℤ σ), T.IsVertOff P S → ∀ A A' : σ → HermLine ι, (∀ i, IsSmoothHerm (A i)) → (∀ i, IsSmoothHerm (A' i)) → T.IsIsometric P A A' → ∀ (V : MvPolynomial (σ ⊕ σ) ℝ) (Gs : σ → MvPolynomial (σ ⊕ σ) ℝ), IsMixExpansion D V Gs → arNum I P (Sum.elim A A') V = ∑ p ∈ S, Real.log (p : ℕ) * (T.map (Int.castRingHom (ZP p))).val (extTo (ZP p) P) Gs := by
  intro K _ _ ι _ P D hP I hI σ _ S T hT A A' hA hA' hiso V Gs hV
  classical
  obtain ⟨rfl, hG⟩ := hV
  rw [arNum_sum']
  simp only [LocPair.val, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [cycNum, Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_lhs => rw [(Gs i).as_sum, Finset.mul_sum, arNum_sum']
  refine Finset.sum_congr rfl fun μ hμ => ?_
  have hcard : μ.toMultiset.card = D := by
    have h := hG i (MvPolynomial.mem_support_iff.1 hμ)
    rw [Finsupp.card_toMultiset, ← h, Finsupp.weight_apply]
    simp only [Pi.one_apply, smul_eq_mul, mul_one]
    rfl
  have hpoly : (X (Sum.inl i) - X (Sum.inr i)) * monomial μ (AddMonoidAlgebra.coeff (Gs i) μ) =
      monomial (μ + Finsupp.single (Sum.inl i) 1) (AddMonoidAlgebra.coeff (Gs i) μ) +
        monomial (μ + Finsupp.single (Sum.inr i) 1) (-AddMonoidAlgebra.coeff (Gs i) μ) := by
    rw [monomial_add_single, monomial_add_single, map_neg]
    ring
  have hmono := link_monomial hP hI hT hA hA' hiso i μ hcard
  rw [hpoly, arNum_add', arNum_monomial', arNum_monomial', neg_mul, ← sub_eq_add_neg, ← mul_sub, hmono,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [LocPair.map]
  ring

end GlobalTheory.CompanionTheory.Ar.Num.TopLink
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.IsometricFamilyIntersectionEqStatement
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isometric_family_intersection_eq : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι ℤ)) (D : ℕ), IsArithVar P (D + 1) → ∀ (I : Ideal (MRing ι ℤ) → (n : ℕ) → (Fin n → HermLine ι) → ℝ), IsIntersectionFamily I → ∀ (σ : Type) [Fintype σ] (S : Finset Nat.Primes) (T : LocPair ι ℤ σ), T.IsVertOff P S → ∀ A A' : σ → HermLine ι, (∀ i, IsSmoothHerm (A i)) → (∀ i, IsSmoothHerm (A' i)) → T.IsIsometric P A A' → ∀ (V : MvPolynomial (σ ⊕ σ) ℝ) (Gs : σ → MvPolynomial (σ ⊕ σ) ℝ), IsMixExpansion D V Gs → arNum I P (Sum.elim A A') V = ∑ p ∈ S, Real.log (p : ℕ) * (T.map (Int.castRingHom (ZP p))).val (extTo (ZP p) P) Gs := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.TopLink.arNum_eq_sum_log_val | exact GlobalTheory.CompanionTheory.Ar.Num.TopLink.arNum_eq_sum_log_val | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.TopLink.arNum_eq_sum_log_val <;> assumption)
end
end
