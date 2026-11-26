module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinVertDivIff
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinGradedFrameIff
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.AssemblyBridgeFull
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.MemDivSuppOfDivCycleNeZero
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PPairConeLinesIndep

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinFlagPairIff
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle)

universe u v w

namespace FlagPairCharacterisation

section Flags

variable {Ω : Type*} [Field Ω] {E : Type*} [AddCommGroup E] [Module Ω E] {N : ℕ}

theorem finrank_flag (w : Module.Basis (Fin N) Ω E) (i : Fin (N + 1)) :
    Module.finrank Ω (Submodule.span Ω (w '' {j : Fin N | (j : ℕ) < i})) = i := by
  classical
  have hli : LinearIndependent Ω (fun x : {j : Fin N | (j : ℕ) < i} => w x) :=
    w.linearIndependent.comp _ Subtype.val_injective
  rw [Set.image_eq_range, finrank_span_eq_card hli]
  simp only [Fintype.card_subtype, Set.mem_ofPred_eq]
  rw [Fin.card_filter_val_lt]
  exact min_eq_right (Nat.lt_succ_iff.mp i.isLt)

theorem flag_eq (w : Module.Basis (Fin N) Ω E) {Vs : Fin (N + 1) → Submodule Ω E} (mono : Monotone Vs)
    (dim : ∀ i, Module.finrank Ω (Vs i) = (i : ℕ)) (hmem : ∀ j, w j ∈ Vs j.succ) (i : Fin (N + 1)) :
    Vs i = Submodule.span Ω (w '' {j : Fin N | (j : ℕ) < i}) := by
  have : FiniteDimensional Ω E := Module.Finite.of_basis w
  symm
  refine Submodule.eq_of_le_of_finrank_eq ?_ (by rw [finrank_flag, dim])
  rw [Submodule.span_le]
  rintro _ ⟨j, hj, rfl⟩
  exact mono (Fin.le_def.mpr (by simpa using hj)) (hmem j)

theorem flag_mono (w : Module.Basis (Fin N) Ω E) :
    Monotone fun i : Fin (N + 1) => Submodule.span Ω (w '' {j : Fin N | (j : ℕ) < i}) :=
  fun _ _ hij => Submodule.span_mono (Set.image_mono fun _ hk => lt_of_lt_of_le hk (Fin.le_def.mp hij))

theorem mem_flag_iff (w : Module.Basis (Fin N) Ω E) (n : ℕ) (x : E) :
    x ∈ Submodule.span Ω (w '' {j : Fin N | (j : ℕ) < n}) ↔ ∀ j : Fin N, n ≤ (j : ℕ) → w.repr x j = 0 := by
  rw [Module.Basis.mem_span_image]
  constructor
  · intro h j hj
    by_contra hne
    exact absurd (h (Finsupp.mem_support_iff.mpr hne)) (by simpa using hj)
  · intro h j hj
    by_contra hne
    exact Finsupp.mem_support_iff.mp hj (h j (by simpa using hne))

theorem linearIndependent_of_not_mem {Vs : Fin (N + 1) → Submodule Ω E} (mono : Monotone Vs)
    {gen : Fin N → E} (hmem : ∀ i, gen i ∈ Vs i.succ) (hnot : ∀ i, gen i ∉ Vs i.castSucc) :
    LinearIndependent Ω gen := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro a ha
  by_contra hne
  push Not at hne
  set S := Finset.univ.filter (fun q : Fin N => a q ≠ 0) with hS
  have hSne : S.Nonempty := by
    obtain ⟨q, hq⟩ := hne
    exact ⟨q, by simp [hS, hq]⟩
  set i := S.max' hSne
  have hi : a i ≠ 0 := by
    have := S.max'_mem hSne
    simpa [hS] using this
  have hrest : ∑ q ∈ Finset.univ.erase i, a q • gen q ∈ Vs i.castSucc := by
    refine Submodule.sum_mem _ fun q hq => ?_
    by_cases haq : a q = 0
    · rw [haq, zero_smul]
      exact Submodule.zero_mem _
    · have hle : q ≤ i := S.le_max' q (by simp [hS, haq])
      have hlt : q < i := lt_of_le_of_ne hle (Finset.ne_of_mem_erase hq)
      exact Submodule.smul_mem _ _ (mono (Fin.le_def.mpr (by simp; omega)) (hmem q))
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at ha
  have hai : a i • gen i ∈ Vs i.castSucc := by
    rw [eq_neg_of_add_eq_zero_left ha]
    exact Submodule.neg_mem _ hrest
  apply hnot i
  have := Submodule.smul_mem _ (a i)⁻¹ hai
  rwa [smul_smul, inv_mul_cancel₀ hi, one_smul] at this

end Flags

section Frames

variable {o : Type*} [CommRing o] {Ω : Type*} [Field Ω] [Algebra o Ω] {K : Type} [Fintype K]
  {ι : K → Type} [∀ k, Fintype (ι k)] {y : (Σ k, ι k) → Ω} {N : ℕ} {E : Type*}
  [AddCommGroup E] [Module Ω E] {B : ChartBundle o (segreVec y) N E}


omit [∀ k, Fintype (ι k)] in
theorem linearIndependent_gen {Vs : Fin (N + 1) → Submodule Ω E} (mono : Monotone Vs)
    (dim : ∀ i, Module.finrank Ω (Vs i) = (i : ℕ)) {m : Fin N → K → ℤ} {gen : Fin N → E}
    (hmem : ∀ i, gen i ∈ Vs i.succ) (hfr : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsGradedFrame o y B Vs m gen)
    {c : ∀ k, ι k} (hc : segreVec y c ≠ 0) : LinearIndependent Ω gen := by
  classical
  obtain ⟨k, fs, cs, -, -, hsum, hl⟩ := hfr c hc
  have hk : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · subst h0
      simp at hsum
    · exact h0
  obtain ⟨b, hli, hsp, -, hb⟩ := hl ⟨0, hk⟩
  have : FiniteDimensional Ω E := Module.Finite.of_basis (Module.Basis.mk hli hsp.ge)
  refine linearIndependent_of_not_mem mono hmem fun i hi => ?_
  have hbV : ∀ j : Fin N, j ≤ i → b j ∈ Vs i.castSucc := by
    intro j hj
    obtain ⟨u, -, hu⟩ := hb j
    have h1 : gen j ∈ Vs i.castSucc := by
      rcases hj.lt_or_eq with hlt | rfl
      · exact mono (Fin.le_def.mpr (by simp; omega)) (hmem j)
      · exact hi
    have h2 : Vs j.castSucc ≤ Vs i.castSucc := mono (Fin.le_def.mpr (by simpa using hj))
    have := Submodule.add_mem _ (h2 hu) (Submodule.smul_mem _ (u * IndefiniteRowSideFullHecke.NumbersDVR.Bundles.chartMon y c (m j)) h1)
    simpa using this
  have hli' : LinearIndependent Ω
      (fun j : {j : Fin N // j ≤ i} => (⟨b j, hbV j j.2⟩ : Vs i.castSucc)) :=
    LinearIndependent.of_comp (Vs i.castSucc).subtype (hli.comp Subtype.val Subtype.val_injective)
  have hcard := hli'.fintype_card_le_finrank
  rw [dim] at hcard
  simp only [Fintype.card_subtype, Fin.val_castSucc] at hcard
  have hfl : (Finset.univ.filter fun j : Fin N => j ≤ i) =
      Finset.univ.filter fun j : Fin N => (j : ℕ) < (i : ℕ) + 1 := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.le_def]
    omega
  rw [hfl, Fin.card_filter_val_lt, min_eq_right (Nat.succ_le_of_lt i.isLt)] at hcard
  omega

theorem eval_ne_zero {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O Ω]
    [DecidableEq K] {b : K → ℤ} {f g : MRing ι O}
    (h : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsVertDiv O (pointIdeal O y) b f g) : aeval y g ≠ 0 := by
  obtain ⟨⟨α, β, -, hβ, -⟩, -, hg, -⟩ := h
  intro h0
  apply hg
  rw [pointIdeal, RingHom.mem_ker, FlagTypings.pointConeMap_of_isMultiHomog y hβ, h0, map_zero,
    zero_mul]

end Frames

theorem proof : Statement.{u, v, w} := by
  intro O _ _ _ Ω _ _ K _ _ ι _ y N E _ _ B B' ϖ hϖ hP
  have hV : ∀ (b : K → ℤ) (f g : MRing ι O), IsVerticalDivisor (pointIdeal O y) ϖ b f g ↔
      IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsVertDiv O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O y) b f g :=
    fun b f g => (VerticalDivisorCharacterisation.proof O K ι (pointIdeal O y) ϖ b f g hϖ hP).symm
  have hG := fun (B₀ : ChartBundle O (segreVec y) N E) (w₀ : Module.Basis (Fin N) Ω E)
      (b : Fin N → K → ℤ) => GradedFrameCharacterisation.proof O Ω K ι y N E B₀ w₀ b
  refine ⟨fun w w' x x' f g => ⟨fun h => ?_, ?_⟩, fun hc F => ?_⟩
  · have hvert := fun i => (hV _ _ _).1 (h.vertical i)
    have hgy : ∀ i, aeval y (g i) ≠ 0 := fun i => eval_ne_zero (hvert i)
    have hflip := FlagTypings.triangular_flip w w' h.sameFlag
    have hspan : (fun i : Fin (N + 1) => Submodule.span Ω (w' '' {j : Fin N | (j : ℕ) < i})) =
        fun i : Fin (N + 1) => Submodule.span Ω (w '' {j : Fin N | (j : ℕ) < i}) := by
      funext i
      refine flag_eq w (flag_mono w') (finrank_flag w') (fun j => ?_) i
      rw [mem_flag_iff]
      intro q hq
      exact hflip.1 j q (Fin.lt_def.mpr (by simp at hq; omega))
    refine ⟨{ Vs := fun i : Fin (N + 1) => Submodule.span Ω (w '' {j : Fin N | (j : ℕ) < i})
              mono := flag_mono w
              dim := finrank_flag w
              top := ?_
              deg := x
              gen := w
              gen_mem := fun i => ?_
              frame := (hG B w x).1 h.flag
              deg' := x'
              gen' := w'
              gen'_mem := fun i => ?_
              frame' := ?_
              f := f
              g := g
              rel := fun i => ?_
              vert := hvert }, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · show Submodule.span Ω (w '' {j : Fin N | (j : ℕ) < (Fin.last N : ℕ)}) = ⊤
      have hu : {j : Fin N | (j : ℕ) < (Fin.last N : ℕ)} = Set.univ := by
        ext j
        simp
      rw [hu, Set.image_univ, w.span_eq]
    · show w i ∈ Submodule.span Ω (w '' {j : Fin N | (j : ℕ) < (i.succ : ℕ)})
      rw [mem_flag_iff]
      intro q hq
      rw [w.repr_self, Finsupp.single_apply, if_neg]
      rintro rfl
      simp at hq
    · show w' i ∈ Submodule.span Ω (w '' {j : Fin N | (j : ℕ) < (i.succ : ℕ)})
      rw [mem_flag_iff]
      intro q hq
      exact h.sameFlag i q (Fin.lt_def.mpr (by simp at hq; omega))
    · have := (hG B' w' x').1 h.flag'
      rwa [hspan] at this
    · show _ ∈ Submodule.span Ω (w '' {j : Fin N | (j : ℕ) < (i.castSucc : ℕ)})
      rw [mem_flag_iff]
      intro q hq
      rw [map_sub, map_smul, w.repr_self, Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul,
        Finsupp.single_apply]
      by_cases hiq : i = q
      · subst hiq
        rw [if_pos rfl, mul_one, h.generic i, mul_div_cancel_right₀ _ (hgy i), sub_self]
      · rw [if_neg hiq, mul_zero, sub_zero]
        exact h.sameFlag i q (lt_of_le_of_ne (Fin.le_def.mpr (by simpa using hq)) hiq)
  · rintro ⟨F, hgen, hgen', rfl, rfl, rfl, rfl⟩
    have hVs : F.Vs = fun i : Fin (N + 1) => Submodule.span Ω (w '' {j : Fin N | (j : ℕ) < i}) :=
      funext (flag_eq w F.mono F.dim fun j => by rw [← hgen]; exact F.gen_mem j)
    have hVs' : F.Vs = fun i : Fin (N + 1) => Submodule.span Ω (w' '' {j : Fin N | (j : ℕ) < i}) :=
      funext (flag_eq w' F.mono F.dim fun j => by rw [← hgen']; exact F.gen'_mem j)
    refine ⟨(hG B w F.deg).2 ?_, (hG B' w' F.deg').2 ?_, fun i j hij => ?_,
      fun i => (hV _ _ _).2 (F.vert i), fun i => ?_⟩
    · have := F.frame
      rwa [hVs, hgen] at this
    · have := F.frame'
      rwa [hVs', hgen'] at this
    · have := F.gen'_mem i
      rw [hVs, hgen'] at this
      exact (mem_flag_iff w _ _).1 this j (by simp; omega)
    · have := F.rel i
      rw [hVs, hgen, hgen'] at this
      have h2 := (GradedFrameCharacterisation.repr_of_sub_mem w this).2
      rw [h2, div_mul_cancel₀ _ (eval_ne_zero (F.vert i))]
  · obtain ⟨c, hc⟩ := hc
    exact ⟨linearIndependent_gen F.mono F.dim F.gen_mem F.frame hc,
      linearIndependent_gen F.mono F.dim F.gen'_mem F.frame' hc⟩

end FlagPairCharacterisation

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsBisLast
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle)
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IFamily IsFieldIntersection)

def FlagPairValueIndependence.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω]
    [Algebra O Ω] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (x : (Σ k, ι k) → Ω) (d N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V]
    (E E' : ChartBundle O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mseg x) N V),
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O x) d →
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.SameGeneric O x E E' →
    ∀ (φ₁ φ₂ : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.FlagPair O x E E')
      (I : IFamily (IsLocalRing.ResidueField O) ι), IsFieldIntersection I →
    ∀ G : MvPolynomial (Fin N) ℤ, G.IsSymmetric →
    ∀ (r : ℕ) (y y' : Fin r → K → ℤ) (f g : Fin r → MRing ι O),
      (∀ l, IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsVertDiv O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O x) (y l - y' l)
        (f l) (g l)) →
    ∀ (c : ℕ) (Q : MvPolynomial (Fin r) ℤ), c ≤ d + 1 → G.IsHomogeneous c →
      Q.IsHomogeneous (d + 1 - c) →
      IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pairNum O I (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O x) d
                                (Fin.append φ₁.deg y) (Fin.append φ₁.deg' y') (Fin.append φ₁.f f) (Fin.append φ₁.g g)
                                (rename (Fin.castAdd r) G * rename (Fin.natAdd N) Q) =
        IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pairNum O I (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O x) d
          (Fin.append φ₂.deg y) (Fin.append φ₂.deg' y') (Fin.append φ₂.f f) (Fin.append φ₂.g g)
          (rename (Fin.castAdd r) G * rename (Fin.natAdd N) Q)

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.InhabitAlt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle)
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IFamily IsFieldIntersection)

def FlagModelRootIndependence.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω]
    [Algebra O Ω] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (x : (Σ k, ι k) → Ω) (d N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V]
    (E E' : ChartBundle O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mseg x) N V),
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O x) d →
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.SameGeneric O x E E' →
    ∀ (F₁ F₂ : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.FlagModel O x d N E E')
      (I₁ : IFamily (IsLocalRing.ResidueField O) (Sum.elim ι F₁.ι'))
      (I₂ : IFamily (IsLocalRing.ResidueField O) (Sum.elim ι F₂.ι')),
      IsFieldIntersection I₁ → IsFieldIntersection I₂ →
    ∀ (c : ℕ) (G : MvPolynomial (Fin N) ℤ), G.IsSymmetric → G.IsHomogeneous c → c ≤ d →
    ∀ (q : ℕ) (L : Fin q → K → ℤ) (Q : MvPolynomial (Fin q) ℤ), Q.IsHomogeneous (d - c) →
    ∀ a : O, a ≠ 0 →
      IndefiniteRowSideFullHecke.NumbersDVR.Bundles.vEval O (fun W => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.polyNum I₁ W d
                                (Fin.append F₁.flag.deg fun l => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := F₁.K') (L l))
                                (rename (Fin.castAdd q) G * rename (Fin.natAdd N) Q))
        (Finsupp.mapRange (fun n : ℕ => (n : ℤ)) Nat.cast_zero (ReciprocityTheory.ChartRestriction.G.Geo.divCycle
          (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.joinCoord x F₁.z)) (C a))) =
      IndefiniteRowSideFullHecke.NumbersDVR.Bundles.vEval O (fun W => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.polyNum I₂ W d
                                (Fin.append F₂.flag.deg fun l => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := F₂.K') (L l))
                                (rename (Fin.castAdd q) G * rename (Fin.natAdd N) Q))
        (Finsupp.mapRange (fun n : ℕ => (n : ℤ)) Nat.cast_zero (ReciprocityTheory.ChartRestriction.G.Geo.divCycle
          (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.joinCoord x F₂.z)) (C a)))

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PPolynomialLocalizedLength
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open IsLocalRing

universe u

theorem length_localizedModule_quotient_eq {A : Type*} [CommRing A] (K W : Ideal A) [W.IsPrime] :
    Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (A ⧸ K)) =
      Module.length (Localization.AtPrime W)
        (Localization.AtPrime W ⧸ K.map (algebraMap A (Localization.AtPrime W))) := by
  let g := Submodule.toLocalizedQuotient' (Localization.AtPrime W) W.primeCompl
    (Algebra.linearMap A (Localization.AtPrime W)) K
  let e := (IsLocalizedModule.linearEquiv W.primeCompl g
    (LocalizedModule.mkLinearMap W.primeCompl (A ⧸ K))).restrictScalars (Localization.AtPrime W)
  have hK : Submodule.localized' (Localization.AtPrime W) W.primeCompl
      (Algebra.linearMap A (Localization.AtPrime W)) K = K.map (algebraMap A (Localization.AtPrime W)) := by
    rw [Submodule.localized'_eq_span]
    rfl
  rw [← e.length_eq]
  exact (Submodule.quotEquivOfEq _ _ hK).length_eq

theorem comap_C_map_C_polynomial {R : Type*} [CommRing R] (p : Ideal R) :
    (p.map (Polynomial.C : R →+* Polynomial R)).comap (Polynomial.C : R →+* Polynomial R) = p := by
  ext r
  rw [Ideal.mem_comap, Ideal.mem_map_C_iff]
  constructor
  · intro h
    simpa using h 0
  · intro h n
    rw [Polynomial.coeff_C]
    split_ifs
    · exact h
    · exact p.zero_mem

theorem PolynomialLocalizedLength.full : PolynomialLocalizedLength.Statement.{u} := by
  intro R _ q _ I
  set Q := q.map (Polynomial.C : R →+* Polynomial R) with hQdef
  have : Q.LiesOver q := ⟨by
    rw [Ideal.under, Polynomial.algebraMap_eq, hQdef]
    exact (comap_C_map_C_polynomial q).symm⟩
  let := Localization.AtPrime.algebraOfLiesOver q Q
  set A := Localization.AtPrime q
  set B := Localization.AtPrime Q
  have : IsLocalHom (algebraMap A B) :=
    inferInstanceAs (IsLocalHom (Localization.localRingHom q Q (algebraMap R (Polynomial R))
      Ideal.LiesOver.over))
  have hm : (maximalIdeal A).map (algebraMap A B) = maximalIdeal B := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map, ← IsScalarTower.algebraMap_eq,
      IsScalarTower.algebraMap_eq R (Polynomial R) B, ← Ideal.map_map, Polynomial.algebraMap_eq,
      ← hQdef, Localization.AtPrime.map_eq_maximalIdeal]
  have h1 : Module.length B (B ⧸ maximalIdeal B) = 1 := by
    have : IsSimpleModule B (B ⧸ maximalIdeal B) :=
      isSimpleModule_iff_quot_maximal.mpr ⟨_, maximalIdeal.isMaximal B, ⟨LinearEquiv.refl _ _⟩⟩
    exact Module.length_eq_one _ _
  have key := IsLocalRing.length_baseChange A B (A ⧸ I.map (algebraMap R A))
  rw [hm, h1, mul_one, ← (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B
    (I.map (algebraMap R A))).toLinearEquiv.length_eq, Ideal.map_map, ← IsScalarTower.algebraMap_eq,
    IsScalarTower.algebraMap_eq R (Polynomial R) B, ← Ideal.map_map, Polynomial.algebraMap_eq] at key
  rw [length_localizedModule_quotient_eq, length_localizedModule_quotient_eq]
  exact key

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PGenericProjClosureModel
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

theorem GenericProjClosureModel.proof (h₁ : TwistedDualGensExist.Statement)
    (h₂ : GenericProjClosureDim.Statement) (h₃ : GenericProjClosureDivisor.Statement) :
    GenericProjClosureModel.Statement := by
  intro O _ _ _ ϖ hϖ Ω _ _ K _ _ ι _ y d hV N hN E _ _ B B' hB Φ _ _ _ _ e t ht
  obtain ⟨a₁, ha₁⟩ := h₁ O Ω K ι y N E B
  obtain ⟨M, φ, hφ⟩ := ha₁ a₁ le_rfl
  obtain ⟨a₁', ha₁'⟩ := h₁ O Ω K ι y N E B'
  obtain ⟨M', φ', hφ'⟩ := ha₁' a₁' le_rfl
  have hZ := h₂ O ϖ hϖ Ω K ι y d hV N hN E B B' hB M M' a₁ a₁' φ φ' hφ hφ' Φ e t ht
  obtain ⟨f₀, g₀, hD, hfg⟩ :=
    h₃ O ϖ hϖ Ω K ι y d hV N hN E B B' hB M M' a₁ a₁' φ φ' hφ hφ' Φ e t ht hZ
  exact ⟨M, M', a₁, a₁', φ, φ', hφ, hφ', hZ, f₀, g₀, hD, hfg⟩

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsPairBundleTrdeg
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def PairBundleTrdeg.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (Ω : Type) [Field Ω] [Algebra O Ω]
      (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (y : (Σ k, ι k) → Ω) (d : ℕ), IsModelOver (pointIdeal O y) d →
    ∀ (N : ℕ), 0 < N → ∀ (E : Type) [AddCommGroup E] [Module Ω E]
      (B B' : ChartBundle O (segreVec y) N E), SameGenericFibre ϖ B B' →
    ∀ (M M' : ℕ) (a₀ a₀' : K → ℤ) (φ : Fin M → Module.Dual Ω E) (φ' : Fin M' → Module.Dual Ω E),
      IsTwistedDualGens y B a₀ φ → IsTwistedDualGens y B' a₀' φ' →
    ∀ (Φ : Type) [Field Φ] [Algebra Ω Φ] [Algebra O Φ] [IsScalarTower O Ω Φ]
      (e : Module.Basis (Fin N) Ω E) (t : Fin N → Φ), AlgebraicIndependent Ω t →
      Algebra.trdeg O (MRing (bundleIdx (bundleIdx ι M) M') O ⧸ pointIdeal O (pairProjCoord y e φ φ' t)) =
        Algebra.trdeg O (MRing ι O ⧸ pointIdeal O y) + ((N + 1 : ℕ) : Cardinal)

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsMoreTer
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IFamily IsFieldIntersection)
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (IsVertDiv mcIdeal joinCoord fnField midDeg midVar)

def PairNumberJoinRight.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω]
    [Algebra O Ω] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (x : (Σ k, ι k) → Ω) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (z : (Σ k, ι' k) → Ω) (K₂ : Type) [Fintype K₂] (ι₂ : K₂ → Type) [∀ k, Fintype (ι₂ k)]
    (w : (Σ k, ι₂ k) → Ω) (d : ℕ),
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O (joinCoord x z)) d →
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O (joinCoord x (joinCoord w z))) d →
    fnField O (joinCoord x (joinCoord w z)) = fnField O (joinCoord x z) →
    ∀ (I : IFamily (IsLocalRing.ResidueField O) (Sum.elim ι (Sum.elim ι₂ ι')))
      (I₁ : IFamily (IsLocalRing.ResidueField O) (Sum.elim ι ι')),
      IsFieldIntersection I → IsFieldIntersection I₁ →
    ∀ (n : ℕ) (a a' : Fin n → K ⊕ K' → ℤ)
      (f g : Fin n → ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O (Sum.elim ι ι')),
      (∀ i, IsVertDiv O (mcIdeal O (joinCoord x z)) (a i - a' i) (f i) (g i)) →
    ∀ H : MvPolynomial (Fin n) ℤ, H.IsHomogeneous (d + 1) →
      IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pairNum O I₁ (mcIdeal O (joinCoord x z)) d a a' f g H =
        IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pairNum O I (mcIdeal O (joinCoord x (joinCoord w z))) d
          (fun i => midDeg (K₂ := K₂) (a i)) (fun i => midDeg (K₂ := K₂) (a' i))
          (fun i => rename (midVar ι₂) (f i)) (fun i => rename (midVar ι₂) (g i)) H

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsSegreFlagClosureTrdeg
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def SegreFlagClosureTrdeg.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (Ω : Type) [Field Ω] [Algebra O Ω]
      (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (y : (Σ k, ι k) → Ω) (d : ℕ), IsModelOver (pointIdeal O y) d →
    ∀ (N : ℕ) (E : Type) [AddCommGroup E] [Module Ω E]
      (B B' : ChartBundle O (segreVec y) N E), SameGenericFibre ϖ B B' →
    ∀ (w w' : Module.Basis (Fin N) Ω E) (x x' : Fin N → K → ℤ) (f g : Fin N → MRing ι O),
      IsFlagPair ϖ y B B' w w' x x' f g →
    ∀ (M M' : ℕ) (a₀ a₀' : K → ℤ) (φ : Fin M → Module.Dual Ω E) (φ' : Fin M' → Module.Dual Ω E),
      IsTwistedDualGens y B a₀ φ → IsTwistedDualGens y B' a₀' φ' →
    ∀ (Φ : Type) [Field Φ] [Algebra Ω Φ] [Algebra O Φ] [IsScalarTower O Ω Φ]
      (e : Module.Basis (Fin N) Ω E) (t : Fin N → Φ), AlgebraicIndependent Ω t →
    ∀ k : ℕ, 1 ≤ k → k ≤ N →
      Algebra.trdeg O (MRing (bundleIdx (bundleIdx ι M) M') O ⧸
          pointIdeal O (flagClosurePt y w e φ φ' t k)) =
        Algebra.trdeg O (MRing ι O ⧸ pointIdeal O y) + ((k + 1 : ℕ) : Cardinal)

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PLocCyclePos
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

theorem localizedModule_quot_nontrivial {R : Type u} [CommRing R] (J W : Ideal R) [W.IsPrime]
    (hJW : J ≤ W) : Nontrivial (LocalizedModule W.primeCompl (R ⧸ J)) := by
  refine ⟨⟨LocalizedModule.mk (1 : R ⧸ J) 1, 0, fun h => ?_⟩⟩
  rw [← LocalizedModule.zero_mk (1 : W.primeCompl), LocalizedModule.mk_eq] at h
  obtain ⟨v, hv⟩ := h
  have hv' : ((v : R) : R ⧸ J) = 0 := by
    simpa [Submonoid.smul_def, Algebra.smul_def] using hv
  exact v.2 (hJW (Ideal.Quotient.eq_zero_iff_mem.mp hv'))

theorem LocCyclePos.proof : LocCyclePos.Statement := by
  intro R _ _ J W hW
  have : W.IsPrime := hW.1.1
  have hfin := ReciprocityTheory.ChartRestriction.G.AI.I1.locLen_ne_top hW
  unfold ReciprocityTheory.ChartRestriction.G.AI.locLen at hfin
  have := localizedModule_quot_nontrivial J W hW.1.2
  have hpos : 0 < Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (R ⧸ J)) :=
    Module.length_pos
  unfold locCycle
  rw [dite_eq_left hW]
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hfin
  simp only at hn
  rw [← hn] at hpos ⊢
  simp only [ENat.toNat_natCast, Nat.cast_pos]
  exact_mod_cast hpos

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinVertDivSupportFibre
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

theorem VerticalDivisorSupportFibre.fibreVarieties : FibreVarieties.Statement.{0} :=
  FibreVarieties.proof GenericFibProps.proof (GenericDimBound.proof MaximalIdealHeightFG.proof)
    GenericDimGe.proof SpecialIdealCorresp.proof SpecialIdealMultiHomog.proof SupSpanMultiHomog.proof
    MinimalPrimeMultiHomog.proof SpecialQuotDim.proof ComponentDim.proof

theorem VerticalDivisorSupportFibre.proof : VerticalDivisorSupportFibre.Statement := by
  classical
  intro O _ _ _ K _ ι _ P d hP b f g hV W hW
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨-, hP1⟩ := (BundleExamples.isModelOver_iff O P d).mp hP
  have hV1 := (VerticalDivisorCharacterisation.proof O K ι P ϖ b f g hϖ hP1.multiProj).mp hV
  rw [BundleExamples.ratCyc_eq] at hW
  have hϖW := hV1.vertical W hW
  rw [BundleExamples.redIdeal_eq]

  have key : ∀ (h : MRing ι O) (bh : K → ℕ), IsMultiHomog h bh → h ∉ P → divCycle P h W ≠ 0 →
      ReciprocityTheory.ChartRestriction.G.AI.I1.IsProjVarF (specialIdeal W) d := by
    intro h bh hh hhP hne
    unfold divCycle at hne
    split_ifs at hne with hc
    · obtain ⟨hmp, hdim⟩ := VerticalComponentFibre.proof VerticalDivisorSupportFibre.fibreVarieties O ϖ hϖ
        K ι P d hP1 h bh hh hhP W hc.1 hc.2 hϖW
      obtain ⟨hpr, hho, hre⟩ := hmp
      exact ⟨⟨hpr, (VocabMultiHomogIdeal.proof VocabMultiHomog.proof _ K ι _).2 hho, hre⟩, hdim⟩
    · exact absurd rfl hne
  obtain ⟨bf, bg, hf, hg, -⟩ := hV1.degrees
  by_cases hfW : divCycle P f W = 0
  · refine key g bg hg hV1.den_not_mem fun hgW => hW ?_
    simp [ratDiv, hfW, hgW]
  · exact key f bf hf hV1.num_not_mem hfW

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsPairConeAlg
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def PairConeAlg.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (Ω : Type) [Field Ω] [Algebra O Ω]
      (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (y : (Σ k, ι k) → Ω) (d : ℕ), IsModelOver (pointIdeal O y) d →
    ∀ (N : ℕ), 0 < N → ∀ (E : Type) [AddCommGroup E] [Module Ω E]
      (B B' : ChartBundle O (segreVec y) N E), SameGenericFibre ϖ B B' →
    ∀ (M M' : ℕ) (a₀ a₀' : K → ℤ) (φ : Fin M → Module.Dual Ω E) (φ' : Fin M' → Module.Dual Ω E),
      IsTwistedDualGens y B a₀ φ → IsTwistedDualGens y B' a₀' φ' →
    ∀ (Φ : Type) [Field Φ] [Algebra Ω Φ] [Algebra O Φ] [IsScalarTower O Ω Φ]
      (e : Module.Basis (Fin N) Ω E) (t : Fin N → Φ), AlgebraicIndependent Ω t →
    ∃ (l : Fin N → Fin M) (m' : Fin M'), LinearIndependent Ω (φ ∘ l) ∧
      pairProjCoord y e φ φ' t ⟨none, m'⟩ ≠ 0 ∧
      ∀ p : Σ o, bundleIdx (bundleIdx ι M) M' o,
        IsAlgebraic
          (Algebra.adjoin O
            (Set.range (fun q : Σ k, ι k =>
                (C (algebraMap Ω Φ (y q)) * X (some (some q.1)) : MvPolynomial (Option (Option K)) Φ)) ∪
              Set.range (Sum.elim
                (fun i : Fin N => C (pairProjCoord y e φ φ' t ⟨some none, l i⟩) * X (some none))
                (fun _ : Unit => C (pairProjCoord y e φ φ' t ⟨none, m'⟩) * X none))))
          (C (pairProjCoord y e φ φ' t p) * X p.1)

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.RingKrullDimQuotComapRename
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

set_option linter.unusedSectionVars false

namespace ProjectiveBundleNumbers

theorem sum_choose_succ (n : ℕ) (U : ℕ → ℤ) :
    ∑ k ∈ Finset.range (n + 2), ((n + 1).choose k : ℤ) * U k =
      ∑ k ∈ Finset.range (n + 1), (n.choose k : ℤ) * U k +
        ∑ k ∈ Finset.range (n + 1), (n.choose k : ℤ) * U (k + 1) := by
  rw [Finset.sum_range_succ', Finset.sum_range_succ' (fun k => (n.choose k : ℤ) * U k)]
  simp only [Nat.choose_succ_succ', Nat.cast_add, add_mul, Finset.sum_add_distrib,
    Nat.choose_zero_right]
  rw [Finset.sum_range_succ (fun k => (n.choose (k + 1) : ℤ) * U (k + 1)),
    Nat.choose_succ_self, Nat.cast_zero, zero_mul, add_zero]
  ring

section ProjBundle

variable {K : Type*} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {F : Type*} [Field F] {Ω : Type*} [Field Ω] [Algebra F Ω]
variable {E : Type*} [AddCommGroup E] [Module Ω E] {N : ℕ}

end ProjBundle

section Rename

variable {F : Type} [Field F] {S : Type} [Fintype S] [DecidableEq S] {κ ι' : S → Type}
  [∀ s, Fintype (κ s)] [∀ s, Fintype (ι' s)]

end Rename

end ProjectiveBundleNumbers

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsSegreFlagClosureBirational
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

abbrev lineBlocks (M M' : ℕ) : Option Unit → Type := bundleIdx (fun _ : Unit => Fin M) M'

section Objects

variable {Ω : Type*} [Field Ω] {N M M' : ℕ} {E : Type*} [AddCommGroup E] [Module Ω E] {Φ : Type*} [Field Φ]
  [Algebra Ω Φ]

def flagLinePt (w e : Module.Basis (Fin N) Ω E) (φ : Fin M → Module.Dual Ω E) (φ' : Fin M' → Module.Dual Ω E)
    (t : Fin N → Φ) (k : ℕ) : (Σ o, lineBlocks M M' o) → Φ
  | ⟨none, l⟩ => ∑ i, flagCoord w e t k i * algebraMap Ω Φ (φ' l (w i))
  | ⟨some _, l⟩ => ∑ i, flagCoord w e t k i * algebraMap Ω Φ (φ l (w i))

end Objects

def SegreFlagClosureBirational.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (Ω : Type) [Field Ω] [Algebra O Ω]
      (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (y : (Σ k, ι k) → Ω) (d : ℕ), IsModelOver (pointIdeal O y) d →
    ∀ (N : ℕ) (E : Type) [AddCommGroup E] [Module Ω E]
      (B B' : ChartBundle O (segreVec y) N E), SameGenericFibre ϖ B B' →
    ∀ (w w' : Module.Basis (Fin N) Ω E) (x x' : Fin N → K → ℤ) (f g : Fin N → MRing ι O),
      IsFlagPair ϖ y B B' w w' x x' f g →
    ∀ (M M' : ℕ) (a₀ a₀' : K → ℤ) (φ : Fin M → Module.Dual Ω E) (φ' : Fin M' → Module.Dual Ω E),
      IsTwistedDualGens y B a₀ φ → IsTwistedDualGens y B' a₀' φ' →
    ∀ (Φ : Type) [Field Φ] [Algebra Ω Φ] [Algebra O Φ] [IsScalarTower O Ω Φ]
      (e : Module.Basis (Fin N) Ω E) (t : Fin N → Φ), AlgebraicIndependent Ω t → 1 ≤ N →
      IsBirationalJoin O (fun p => algebraMap Ω Φ (y p)) (flagLinePt w e φ φ' t 1)

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.JoinCoordCompMidSwapVars
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

variable {K K' K₂ : Type}

def midSwapBlocks : K ⊕ (K₂ ⊕ K') ≃ K ⊕ (K' ⊕ K₂) :=
  Equiv.sumCongr (Equiv.refl K) (Equiv.sumComm K₂ K')

def midSwapVars (ι : K → Type) (ι' : K' → Type) (ι₂ : K₂ → Type) :
    (Σ k : K ⊕ (K₂ ⊕ K'), Sum.elim ι (Sum.elim ι₂ ι') k) ≃
      (Σ k : K ⊕ (K' ⊕ K₂), Sum.elim ι (Sum.elim ι' ι₂) k) where
  toFun
    | ⟨.inl k, i⟩ => ⟨.inl k, i⟩
    | ⟨.inr (.inl k), i⟩ => ⟨.inr (.inr k), i⟩
    | ⟨.inr (.inr k), i⟩ => ⟨.inr (.inl k), i⟩
  invFun
    | ⟨.inl k, i⟩ => ⟨.inl k, i⟩
    | ⟨.inr (.inl k), i⟩ => ⟨.inr (.inr k), i⟩
    | ⟨.inr (.inr k), i⟩ => ⟨.inr (.inl k), i⟩
  left_inv := by
    rintro ⟨k | k | k, i⟩ <;> rfl
  right_inv := by
    rintro ⟨k | k | k, i⟩ <;> rfl

theorem midSwapVars_fst {ι : K → Type} {ι' : K' → Type} {ι₂ : K₂ → Type}
    (v : Σ k : K ⊕ (K₂ ⊕ K'), Sum.elim ι (Sum.elim ι₂ ι') k) :
    (midSwapVars ι ι' ι₂ v).1 = midSwapBlocks v.1 := by
  obtain ⟨k | k | k, i⟩ := v <;> rfl

theorem joinCoord_comp_midSwapVars {ι : K → Type} {ι' : K' → Type} {ι₂ : K₂ → Type} {Ω : Type*}
    (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω) (w : (Σ k, ι₂ k) → Ω) :
    joinCoord x (joinCoord z w) ∘ midSwapVars ι ι' ι₂ = joinCoord x (joinCoord w z) := by
  funext v
  obtain ⟨k | k | k, i⟩ := v <;> rfl

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IFamily IsFieldIntersection)
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (IsVertDiv mcIdeal joinCoord fnField pairNum midSwapBlocks midSwapVars
  ptCoord ptIdx unif)

def PairNumberRelabelAlt.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω]
    [Algebra O Ω] (K₁ : Type) [Fintype K₁] (ι₁ : K₁ → Type) [∀ k, Fintype (ι₁ k)]
    (K₂ : Type) [Fintype K₂] (ι₂ : K₂ → Type) [∀ k, Fintype (ι₂ k)]
    (e : K₁ ≃ K₂) (σ : (Σ k, ι₁ k) ≃ (Σ k, ι₂ k)), (∀ v, (σ v).1 = e v.1) →
    ∀ (y : (Σ k, ι₂ k) → Ω) (d : ℕ),
      IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O (y ∘ σ)) d →
        IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O y) d ∧ fnField O y = fnField O (y ∘ σ) ∧
        (∀ (b : K₂ → ℤ) (f g : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι₁),
          IsVertDiv O (mcIdeal O (y ∘ σ)) (b ∘ e) f g →
            IsVertDiv O (mcIdeal O y) b (rename σ f) (rename σ g)) ∧
        ∀ (I₁ : IFamily (IsLocalRing.ResidueField O) ι₁) (I : IFamily (IsLocalRing.ResidueField O) ι₂),
          IsFieldIntersection I₁ → IsFieldIntersection I →
        ∀ (n : ℕ) (a a' : Fin n → K₂ → ℤ) (f g : Fin n → ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι₁),
          (∀ i, IsVertDiv O (mcIdeal O (y ∘ σ)) (a i ∘ e - a' i ∘ e) (f i) (g i)) →
        ∀ H : MvPolynomial (Fin n) ℤ, H.IsHomogeneous (d + 1) →
          IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pairNum O I₁ (mcIdeal O (y ∘ σ)) d (fun i => a i ∘ e) (fun i => a' i ∘ e) f g H =
            IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pairNum O I (mcIdeal O y) d a a' (fun i => rename σ (f i)) (fun i => rename σ (g i)) H

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinJoinVertDiv
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (liftVar pullDeg joinCoord mcIdeal IsVertDiv)


open JoinPointVerticalDivisor in
theorem JoinVerticalDivisor.proof : JoinVerticalDivisor.Statement := by
  intro O _ _ _ Ω _ _ K _ ι _ x K' _ ι' _ z b f g hD
  obtain ⟨⟨α, β, hf, hg, hb⟩, hfP, hgP, hU⟩ := hD
  refine ⟨⟨Sum.elim α 0, Sum.elim β 0, isMultiHomog_rename hf, isMultiHomog_rename hg, ?_⟩,
    ?_, ?_, ?_⟩
  · rintro (k | k)
    · simpa [pullDeg] using hb k
    · simp [pullDeg]
  · rwa [rename_mem_mcIdeal_iff]
  · rwa [rename_mem_mcIdeal_iff]
  · intro Q hQ hPQ hQO
    have hle : mcIdeal O x ≤ Q.comap (rename (liftVar (ι := ι) ι')) := fun h hh =>
      Ideal.mem_comap.mpr (hPQ ((rename_mem_mcIdeal_iff O x z h).mpr hh))
    have hO : (Q.comap (rename (liftVar (ι := ι) ι'))).comap
        (C : O →+* ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι) = ⊥ := by
      rw [eq_bot_iff] at hQO ⊢
      intro c hc
      apply hQO
      simpa [Ideal.mem_comap, rename_C] using hc
    obtain ⟨u, v, ⟨γ, hu⟩, ⟨δ, hv⟩, huQ, hvQ, huv⟩ := hU _ (comap_isMultiProjPrime hQ) hle hO
    refine ⟨rename (liftVar ι') u, rename (liftVar ι') v, ⟨_, isMultiHomog_rename hu⟩,
      ⟨_, isMultiHomog_rename hv⟩, huQ, hvQ, ?_⟩
    have := (rename_mem_mcIdeal_iff O x z _).mpr huv
    simpa only [map_sub, map_mul] using this

end GroundTheory.Heights₂.Heights.NumbersDVR
end
