module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.ComplexConjugationsConjugateCaseThree
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.PRedTanA
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.PFibY
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.AutOf4Of
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.ConjDiag
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.SmulTnMap
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.FiniteOrderCongruences.PGoodJ
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.FiniteOrderCongruences.PTauOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.FiniteOrderCongruences.ExistsWeightFourAuxiliaryCharacters
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.ModularityRankFourOfPromodularity
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.PChainIV

@[expose] public section

attribute [-instance] Formalism.LFunctionChainParameters.LChain6.FamC.indexKFirst Formalism.LFunctionChainParameters.LChain6.FamC.indexKSecond Formalism.LFunctionChainParameters.LChain6.FamC.indexKThird Formalism.LFunctionChainParameters.LChain6.FamC.indexKFourth Formalism.BasicNotions.NTypes.instMray Formalism.BasicNotions.NTypes.nfMray Formalism.BasicNotions.NTypes.algKM UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing UpperTheory.V.Pr.IsCD.complete UpperTheory.V.Pr.IsCD.fin UpperTheory.V.Pr.IsCD.isLocalHom

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.KapEx
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N IsLocalRing Polynomial
open UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S3
open UpperTheory.V.Cu
open scoped Matrix
namespace UpperTheory.V.Cu2
def KapExAlt : Prop :=
  _root_.UpperTheory.V.Af.Hypotheses' → ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ)
    (K' : IntermediateField ℚ Ω) [NumberField K'], l ≠ 2 → Module.finrank ℚ K' = 2 → IsTotallyComplex K' → ¬ (l : ℤ) ∣ discr K' →
    (∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → Dec (F := ℚ) A ≤ K'.fixingSubgroup) → (∃ cc : G ℚ Ω, Sd.IsCC cc) →
    ∃ (m : ℕ) (κ : G K' Ω →* (Qbar l)ˣ), ∀ j : ℕ, 1 ≤ j → KapDat ι K' (m * j) (κ ^ j)
end UpperTheory.V.Cu2
end
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.ReductionTypeChainOfRedAYCoinFibY
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Cu
namespace UpperTheory.V.Cu.RankFourReductionTypeChain
private theorem ch_num {x y : WithBot ℕ∞} {a b c N : ℕ} (h1 : x ≤ y + (a : ℕ)) (h2 : y + (b : ℕ) ≤ (c : ℕ))
    (h : c + a < N + b) : x < N := by
  refine h1.trans_lt ?_
  induction y using WithBot.recBotCoe with
  | bot => simp
  | coe y =>
    induction y using ENat.recTopCoe with
    | top => exact absurd h2 (by norm_cast)
    | coe y =>
      have h3 : y + b ≤ c := by exact_mod_cast h2
      exact_mod_cast (by omega : y + a < N)
private theorem supp_of {Γ A R K : Type} [Group Γ] [CommRing A] [CommRing R] [CommRing K] (r : Γ →* M4 A) (f : A →+* R)
    (φ : R →+* K) (q : Ideal R) (hq : ∀ z ∈ q, φ z = 0) {S : Finset (ℤ × ℤ)} (h : redIdeal S (mapRep f r) ≤ q) :
    Supp S (mapRep (φ.comp f) r) := fun g i j hij hw => by
  simpa [mapRep_apply] using hq _ (h (Ideal.subset_span ⟨g, i, j, hij, hw, rfl⟩))
private theorem ent_of {Γ A R K : Type} [Group Γ] [CommRing A] [CommRing R] [Field K] (r : Γ →* M4 A) (f : A →+* R)
    (φ : R →+* K) (q : Ideal R) (hq : ∀ z, φ z = 0 ↔ z ∈ q) (hY : redIdeal yY (mapRep f r) ≤ q)
    {S : Finset (ℤ × ℤ)} (hS : ¬ redIdeal S (mapRep f r) ≤ q) {w : ℤ × ℤ} (hw : ∀ u ∈ yY, u ∉ S → u = w) :
    Ent (mapRep (φ.comp f) r) w := by
  classical
  by_contra hn
  refine hS (Ideal.span_le.2 ?_)
  rintro _ ⟨g, i, j, hij, hwS, rfl⟩
  by_cases hy : wt i j ∈ yY
  · refine (hq _).1 ?_
    by_contra h0
    exact hn ⟨g, i, j, hw _ hy hwS, by simpa [mapRep_apply] using h0⟩
  · exact hY (Ideal.subset_span ⟨g, i, j, hij, hy, rfl⟩)
private theorem w1 : ∀ u ∈ yY, u ∉ ({wBe, -wBe, -wAl, -wTh, -wPs} : Finset (ℤ × ℤ)) → u = wTh := by
  first
  | decide
  | (intro u hu hS
     simp only [yY, Finset.mem_insert, Finset.mem_singleton] at hu
     rcases hu with rfl | rfl | rfl | rfl <;> first | rfl | (exfalso; exact hS (by simp)))
private theorem w2 : ∀ u ∈ yY, u ∉ ({wBe, -wBe, wAl, wTh, wPs} : Finset (ℤ × ℤ)) → u = -wTh := by
  first
  | decide
  | (intro u hu hS
     simp only [yY, Finset.mem_insert, Finset.mem_singleton] at hu
     rcases hu with rfl | rfl | rfl | rfl <;> first | rfl | (exfalso; exact hS (by simp)))
private theorem w3 : ∀ u ∈ yY, u ∉ ({wTh, -wTh, wPs, wBe, -wAl} : Finset (ℤ × ℤ)) → u = -wBe := by
  first
  | decide
  | (intro u hu hS
     simp only [yY, Finset.mem_insert, Finset.mem_singleton] at hu
     rcases hu with rfl | rfl | rfl | rfl <;> first | rfl | (exfalso; exact hS (by simp)))
private theorem w4 : ∀ u ∈ yY, u ∉ ({wTh, -wTh, -wPs, -wBe, wAl} : Finset (ℤ × ℤ)) → u = wBe := by
  first
  | decide
  | (intro u hu hS
     simp only [yY, Finset.mem_insert, Finset.mem_singleton] at hu
     rcases hu with rfl | rfl | rfl | rfl <;> first | rfl | (exfalso; exact hS (by simp)))
private theorem t1 : ({wBe, -wBe, -wAl, -wTh, -wPs} : Finset (ℤ × ℤ)) ∈ redTypes ∧
    ({wBe, -wBe, -wAl, -wTh, -wPs} : Finset (ℤ × ℤ)) ≠ yY :=
  ⟨List.Mem.head _, by first | decide | (intro h; have := congrArg (fun s => -wAl ∈ s) h; simp [yY, wAl, wBe, wTh, wPs] at this)⟩
private theorem t2 : ({wBe, -wBe, wAl, wTh, wPs} : Finset (ℤ × ℤ)) ∈ redTypes ∧
    ({wBe, -wBe, wAl, wTh, wPs} : Finset (ℤ × ℤ)) ≠ yY :=
  ⟨List.Mem.tail _ (List.Mem.head _), by first | decide | (intro h; have := congrArg (fun s => wAl ∈ s) h; simp [yY, wAl, wBe, wTh, wPs] at this)⟩
private theorem t3 : ({wTh, -wTh, wPs, wBe, -wAl} : Finset (ℤ × ℤ)) ∈ redTypes ∧
    ({wTh, -wTh, wPs, wBe, -wAl} : Finset (ℤ × ℤ)) ≠ yY :=
  ⟨List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)), by first | decide | (intro h; have := congrArg (fun s => wPs ∈ s) h; simp [yY, wAl, wBe, wTh, wPs] at this)⟩
private theorem t4 : ({wTh, -wTh, -wPs, -wBe, wAl} : Finset (ℤ × ℤ)) ∈ redTypes ∧
    ({wTh, -wTh, -wPs, -wBe, wAl} : Finset (ℤ × ℤ)) ≠ yY :=
  ⟨List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))), by first | decide | (intro h; have := congrArg (fun s => -wPs ∈ s) h; simp [yY, wAl, wBe, wTh, wPs] at this)⟩
private theorem ch_core4 (hRA : RedA) (hYC : YCoin) (hFY : FibY) {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ]
    [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ] {Φ : Fr O Γ} {l : ℕ} [Fact l.Prime] {Λ : Type}
    [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] [Finite (ResidueField Λ)]
    {a : O →+* Λ} (hS : Φ.Std l a) (hne : Nonempty Φ.ι)
    (X : Space Φ a) (J : Ideal X.B) (U : Φ.ι → Set Γ) (hU : ∀ v, ∀ s ∈ U v, s ∈ Φ.Gv v) {d C dv N : ℕ}
    (hB : Φ.Bounds ((residue Λ).comp a) d C) (hN1 : d + 20 * C + 1 < N)
    (hN2 : 2 * d + 1 + (2 + 4 * Nat.card Φ.ι) < N + dv)
    (hnn : ∀ v i j, i ≠ j → ∀ q : Ideal X.B, q.IsPrime → J ≤ q → (maximalIdeal Λ).map (algebraMap Λ X.B) ≤ q →
      (∀ s ∈ U v, X.ψ v i s - X.ψ v j s ∈ q) → ringKrullDim (X.B ⧸ q) + dv ≤ (2 * d + 1 : ℕ))
    (hp1 : ∀ (k : Type) [Field k] [Finite k] [Algebra Λ k] (y : X.A →ₐ[Λ] PowerSeries k),
      (∀ b ∈ maximalIdeal X.B, PowerSeries.constantCoeff (y (algebraMap X.B X.A b)) = 0) →
      (∀ b ∈ J, y (algebraMap X.B X.A b) = 0) →
      (∀ v i j, i ≠ j → ∃ s ∈ U v, y (X.P.ψ v i s) ≠ y (X.P.ψ v j s)) →
      Irr (mapRep ((algebraMap (PowerSeries k) (FractionRing (PowerSeries k))).comp (y : X.A →+* PowerSeries k)) X.P.r) →
      X.LocZero J (y : X.A →+* PowerSeries k))
    {c : PD Φ.ι Γ (ResidueField Λ)} (hc : Φ.IsRes ((residue Λ).comp a) c) (hIA : InA c)
    (hE : Ent c.r (-wPs) ∨ (Ent c.r (-wBe) ∧ Ent c.r (-wTh)))
    {R : Type} [CommRing R] [Algebra Λ R] [IsCO Λ R] (f : X.A →ₐ[Λ] R) (hdef : Φ.IsDef a c (X.P.map (f : X.A →+* R)))
    {P Q : Ideal R} (hPQ : Ch.Adj R (N + 1) P Q) (hP : J ≤ P.comap ((f : X.A →+* R).comp (algebraMap X.B X.A))) :
    J ≤ Q.comap ((f : X.A →+* R).comp (algebraMap X.B X.A)) := by
  classical
  haveI := hS.char
  let φ : X.B →+* R := (f : X.A →+* R).comp (algebraMap X.B X.A)
  have hφ : ∀ t : Λ, φ (algebraMap Λ X.B t) = algebraMap Λ R t := fun t => by
    show f (algebraMap X.B X.A _) = _
    rw [← IsScalarTower.algebraMap_apply, AlgHom.commutes]
  obtain ⟨ϖ, hϖ⟩ := (IsPrincipalIdealRing.principal (maximalIdeal Λ)).1
  have hm : ∀ q : Ideal R, algebraMap Λ R ϖ ∈ q → ∀ t ∈ maximalIdeal Λ, algebraMap Λ R t ∈ q := fun q hq t ht => by
    rw [hϖ] at ht
    obtain ⟨u, rfl⟩ := Ideal.mem_span_singleton'.1 ht
    rw [map_mul]
    exact q.mul_mem_left _ hq
  have hϖm : algebraMap Λ R ϖ ∈ maximalIdeal R :=
    map_nonunit _ _ (show ϖ ∈ maximalIdeal Λ by rw [hϖ]; exact Ideal.mem_span_singleton_self ϖ)
  let A : {S // S ∈ redTypes ∧ S ≠ yY} → Ideal R := fun S => redIdeal S.1 (X.P.map (f : X.A →+* R)).r
  let B : {t : Φ.ι × Fin 4 × Fin 4 // t.2.1 ≠ t.2.2} → Ideal R := fun t =>
    J.map φ ⊔ Ideal.span {algebraMap Λ R ϖ} ⊔ Ideal.span ((fun s => φ (X.ψ t.1.1 t.1.2.1 s - X.ψ t.1.1 t.1.2.2 s)) '' U t.1.1)
  haveI : Finite {S // S ∈ redTypes ∧ S ≠ yY} :=
    Set.Finite.to_subtype (show Set.Finite {S | S ∈ redTypes ∧ S ≠ yY} from
      (List.finite_toSet redTypes).subset (by intro S h; exact h.1))
  have hb : ∀ t, ∀ q : Ideal R, q.IsPrime → B t ≤ q → (∀ S, ¬ A S ≤ q) → ringKrullDim (R ⧸ q) < N := by
    intro t q hq hle hr
    haveI := hq
    have hq0 : ∀ z, ((algebraMap (R ⧸ q) (FractionRing (R ⧸ q))).comp (Ideal.Quotient.mk q)) z = 0 ↔ z ∈ q := fun z => by
      rw [RingHom.comp_apply, map_eq_zero_iff _ (IsFractionRing.injective (R ⧸ q) (FractionRing (R ⧸ q))),
        Ideal.Quotient.eq_zero_iff_mem]
    have hfib : ringKrullDim (R ⧸ q) ≤
        ringKrullDim (X.B ⧸ q.comap ((f : X.A →+* R).comp (algebraMap X.B X.A))) + (2 + 4 * Nat.card Φ.ι : ℕ) := by
      by_cases hYq : redIdeal yY (X.P.map (f : X.A →+* R)).r ≤ q
      · exact hFY Φ l a hS X c hc R f hdef q _ rfl (supp_of X.P.r _ _ q (fun z hz => (hq0 z).2 hz) hYq)
          (ent_of X.P.r _ _ q hq0 hYq (hr ⟨_, t4⟩) w4)
          (ent_of X.P.r _ _ q hq0 hYq (hr ⟨_, t3⟩) w3)
          (ent_of X.P.r _ _ q hq0 hYq (hr ⟨_, t1⟩) w1)
          (ent_of X.P.r _ _ q hq0 hYq (hr ⟨_, t2⟩) w2)
      · exact fib Φ l a hS X c hc R f hdef q (Ch.irr hS.ok hc hdef.1
          ((algebraMap (R ⧸ q) (FractionRing (R ⧸ q))).comp (Ideal.Quotient.mk q)) q (fun z hz => (hq0 z).1 hz)
          fun S hS' => by
            by_cases hSY : S = yY
            · subst hSY
              exact hYq
            · exact hr ⟨S, hS', hSY⟩)
    exact ch_num hfib
      (hnn t.1.1 _ _ t.2 (q.comap φ) (Ideal.comap_isPrime _ _)
        (Ideal.map_le_iff_le_comap.1 (le_sup_left.trans (le_sup_left.trans hle)))
        (Ideal.map_le_iff_le_comap.2 fun u hu => by
          show φ (algebraMap Λ X.B u) ∈ q
          rw [hφ]
          exact hm q (hle (Ideal.mem_sup_left (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)))) u hu)
        fun s hs => hle (Ideal.mem_sup_right (Ideal.subset_span ⟨s, hs, rfl⟩))) hN2
  obtain ⟨p, hp, hIp, hdim, hϖp, hA, hBp⟩ := Ch.nice _ hϖm N (by omega) A B
    (fun S => (hRA Φ l a hS d C hB c hc hIA hE R _ hdef S.1 S.2.1 S.2.2).trans_lt (by exact_mod_cast hN1))
    hb _ hPQ.2.2
  have hJp : ∀ b ∈ J, φ b ∈ p := fun b hb => hIp (Ideal.mem_sup_left (hP hb))
  have hYp : ¬ redIdeal yY (X.P.map (f : X.A →+* R)).r ≤ p := by
    intro hle
    haveI := hp
    obtain ⟨v⟩ := hne
    have hq0 : ∀ z ∈ p, ((algebraMap (R ⧸ p) (FractionRing (R ⧸ p))).comp (Ideal.Quotient.mk p)) z = 0 := fun z hz => by
      rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.2 hz, map_zero]
    have hpair := hdef.1.pair.map ((algebraMap (R ⧸ p) (FractionRing (R ⧸ p))).comp (Ideal.Quotient.mk p))
    rw [PD.map_map] at hpair
    have hsupp := supp_of X.P.r (f : X.A →+* R) _ p hq0 hle
    have h1 : res Λ R ((f : X.A →+* R) (X.P.n v 1 0)) = c.n v 1 0 := by
      rw [← hdef.1.red]
      rfl
    have hu : IsUnit ((f : X.A →+* R) (X.P.n v 1 0)) := by
      by_contra hu
      have h4 := (res_eq_zero_iff Λ R _).2 ((mem_maximalIdeal _).2 hu)
      rw [h1] at h4
      exact hIA.2 v h4
    have hn : (X.P.map (((algebraMap (R ⧸ p) (FractionRing (R ⧸ p))).comp (Ideal.Quotient.mk p)).comp
        (f : X.A →+* R))).n v 1 0 ≠ 0 := by
      have := (hu.map ((algebraMap (R ⧸ p) (FractionRing (R ⧸ p))).comp (Ideal.Quotient.mk p))).ne_zero
      simpa only [PD.map_n, Matrix.map_apply, RingHom.comp_apply] using this
    have hBle : ∀ (i i' : Fin 4) (hi : i ≠ i'), (∀ s ∈ Φ.Gv v,
        (X.P.map (((algebraMap (R ⧸ p) (FractionRing (R ⧸ p))).comp (Ideal.Quotient.mk p)).comp
          (f : X.A →+* R))).ψ v i s =
        (X.P.map (((algebraMap (R ⧸ p) (FractionRing (R ⧸ p))).comp (Ideal.Quotient.mk p)).comp
          (f : X.A →+* R))).ψ v i' s) → B ⟨(v, i, i'), hi⟩ ≤ p := fun i i' hi hh => by
      refine sup_le (sup_le (Ideal.map_le_iff_le_comap.2 hJp) ((Ideal.span_singleton_le_iff_mem _).2 hϖp))
        (Ideal.span_le.2 ?_)
      rintro _ ⟨s, hs, rfl⟩
      have e := hh s (hU v s hs)
      simp only [PD.map_ψ, RingHom.comp_apply] at e
      have e2 : ∀ k, φ (X.ψ v k s) = (f : X.A →+* R) (X.P.ψ v k s) := fun k => by
        show (f : X.A →+* R) (algebraMap X.B X.A (X.ψ v k s)) = _
        rw [X.ψ_map v k s (hU v s hs)]
      show φ (X.ψ v i s - X.ψ v i' s) ∈ p
      rw [map_sub, e2, e2, ← Ideal.Quotient.eq_zero_iff_mem,
        ← map_eq_zero_iff _ (IsFractionRing.injective (R ⧸ p) (FractionRing (R ⧸ p))), map_sub, map_sub, e, sub_self]
    rcases hYC Φ _ _ hpair hsupp v hn with h01 | h13
    · exact hBp ⟨(v, 0, 1), (by decide : (0 : Fin 4) ≠ 1)⟩ (hBle 0 1 (by decide) h01)
    · exact hBp ⟨(v, 1, 3), (by decide : (1 : Fin 4) ≠ 3)⟩ (hBle 1 3 (by decide) h13)
  have hirr : ∀ S ∈ redTypes, ¬ redIdeal S (X.P.map (f : X.A →+* R)).r ≤ p := fun S hS' => by
    by_cases hSY : S = yY
    · subst hSY
      exact hYp
    · exact hA ⟨S, hS', hSY⟩
  obtain ⟨K, _, _, _, j, hj, hj0⟩ := Ch.curve l Λ R p hp hdim (hm p hϖp)
  haveI : Q.IsPrime := hPQ.2.1.1.1
  refine hp1 K (j.comp f) (fun b hb => hj0 _ ?_) (fun b hb => (hj _).2 (hJp b hb)) (fun v i i' hi => ?_)
    (Ch.irr hS.ok hc hdef.1 ((algebraMap (PowerSeries K) (FractionRing (PowerSeries K))).comp (j : R →+* PowerSeries K)) p
      (fun x hx => (hj x).1 ((map_eq_zero_iff _ (IsFractionRing.injective _ _)).1 hx)) hirr)
    _ (Ideal.comap_isPrime _ _) fun s hs => (hj _).2 (hIp (Ideal.mem_sup_right hs))
  · show (f.comp (IsScalarTower.toAlgHom Λ X.B X.A)) b ∈ maximalIdeal R
    rw [← res_eq_zero_iff Λ, res_map, res_eq_zero_iff]
    exact hb
  · by_contra hn
    push Not at hn
    refine hBp ⟨(v, i, i'), hi⟩ (sup_le (sup_le (Ideal.map_le_iff_le_comap.2 hJp)
      ((Ideal.span_singleton_le_iff_mem _).2 hϖp)) (Ideal.span_le.2 ?_))
    rintro _ ⟨s, hs, rfl⟩
    refine (hj _).1 ?_
    show (j.comp f) (algebraMap X.B X.A (X.ψ v i s - X.ψ v i' s)) = 0
    rw [map_sub, map_sub, X.ψ_map v i s (hU v s hs), X.ψ_map v i' s (hU v s hs), hn s hs, sub_self]
end UpperTheory.V.Cu.RankFourReductionTypeChain
theorem UpperTheory.V.Cu.chain_rank_four_of_red_a_y_coin_fib_y : RedA → YCoin → FibY → _root_.UpperTheory.V.Cu.ChainRankFour := by
  intro hRA hYC hFY
  unfold _root_.UpperTheory.V.Cu.ChainRankFour
  intro hC Ω _ _ _ l _ c D T hF hD ι c' h X J hPM C hB hd x hx hg hsome
  unfold Good4 at hg
  rcases hg with hg | hg
  · exact _root_.UpperTheory.V.Ws.residual_charpoly_rank_four hC D T hF hD ι c' h X J hPM C hB hd x hx hg hsome
  obtain ⟨q₀, hq₀, hq₀x, hq₀J⟩ := hsome
  intro q hq hqx
  have hIA : InA (X.P.map (x : X.A →+* ResidueField c'.O)) := by
    rcases hg with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact h1
    · exact h1
  have hE : Ent (X.P.map (x : X.A →+* ResidueField c'.O)).r (-wPs) ∨
      (Ent (X.P.map (x : X.A →+* ResidueField c'.O)).r (-wBe) ∧ Ent (X.P.map (x : X.A →+* ResidueField c'.O)).r (-wTh)) := by
    rcases hg with ⟨-, h2⟩ | ⟨-, h2, h3⟩
    · exact Or.inl h2
    · exact Or.inr ⟨h2, h3⟩
  haveI : Finite (ResidueField c'.O) := (UpperTheory.V.abelian₂.dvr_finite l c'.O).2.1
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : IsAlgClosure T.F Ω := ⟨inferInstance, inferInstance⟩
  haveI : IsGalois T.F Ω := {}
  haveI : CompactSpace (G T.F Ω) := inferInstanceAs (CompactSpace (Ω ≃ₐ[T.F] Ω))
  haveI : TotallyDisconnectedSpace (G T.F Ω) := inferInstanceAs (TotallyDisconnectedSpace (Ω ≃ₐ[T.F] Ω))
  have hS := (std hC D T hF ∅ c' h).1 (Finset.notMem_empty 0)
  obtain ⟨R, _, _, _, f, hdef, hfl, hres⟩ := cmplEx (T.fr ∅) l (inc h) hS X x hx
  obtain ⟨a, b, π, e, hπ, hk, hab⟩ := x1 hC D T hF hD c' h _ hx R _ hdef
  obtain ⟨dv, hdv⟩ := chDv D T
  have hg' : Nat.card T.ι ≤ C := hB.card
  have hdv' : 30 * (C + 1) ≤ dv := by
    by_contra hn
    have h1 : dv * Nat.card T.ι ≤ 30 * (C + 1) * C := Nat.mul_le_mul (by omega) hg'
    nlinarith
  have hd' : 30 * (C + 1) ≤ T.d := le_trans (Nat.le_mul_of_pos_right _ (by omega)) hd
  have hne : Nonempty T.ι := by
    have hpos : 0 < Nat.card T.ι := Nat.pos_of_ne_zero fun h0 => by
      rw [h0, mul_zero] at hdv
      omega
    exact (Nat.card_pos_iff.1 hpos).1
  obtain ⟨N, hN⟩ : ∃ N, N + 2 * Nat.card T.ι = 2 * T.d + 1 := ⟨2 * T.d + 1 - 2 * Nat.card T.ι, by omega⟩
  have hker : RingHom.ker x = (maximalIdeal R).comap (f : X.A →+* R) := by
    ext z
    rw [RingHom.mem_ker, ← hres]
    exact res_eq_zero_iff c'.O R (f z)
  obtain ⟨P, hP, rfl⟩ := Ch.flat_min _ hfl hq₀ (hker ▸ hq₀x)
  obtain ⟨Q, hQ, rfl⟩ := Ch.flat_min _ hfl hq (hker ▸ hqx)
  rw [Ideal.map_le_iff_le_comap, Ideal.comap_comap] at hq₀J ⊢
  have hch := Ch.chain c'.O (D := N + 1) π e hπ hk (by omega) hP hQ
  clear hq hqx hQ
  induction hch with
  | refl => exact hq₀J
  | tail _ hPQ ih =>
    exact RankFourReductionTypeChain.ch_core4 hRA hYC hFY hS hne X J T.U1 (fun v s hs => Ine_le_Dec _ hs.1) (dv := dv) hB (by omega)
      (by show _ + (2 + 4 * Nat.card T.ι) < _; omega)
      (fun v i j hij q h1 h2 h3 h4 => _root_.UpperTheory.V.Ws.off_diagonal_nilpotent_rank_four hC D T hF hD ι c' h X J hPM v i j hij q h1 h2 h3 h4 dv hdv) hPM.p1 hx hIA hE
      f hdef hPQ ih
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PromodularityCaseThreeOfLemmas
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Cu
private theorem chain_rank_four_good {O Γ R : Type} [CommRing O] [Group Γ] [CommRing R] {Φ : Fr O Γ} {a : O →+* R} {P : PD Φ.ι Γ R}
    [TopologicalSpace Γ] {P' : PD Φ.ι Γ R} (hP : Φ.IsRes a P) (h : Chain4 Φ a P P') :
    Φ.IsRes a P' ∧ Good4 Φ a P' := by
  obtain ⟨hg, hc⟩ := h
  induction hc with
  | refl => exact ⟨hP, hg⟩
  | tail _ hl _ => exact ⟨Asm.linked_isRes hl.2, hl.1⟩
private theorem allIn_of_chain4 {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
    [TotallyDisconnectedSpace Γ] {Φ : Fr O Γ} {l : ℕ} [Fact l.Prime] {Λ : Type} [CommRing Λ] [IsDomain Λ]
    [IsDiscreteValuationRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] [Finite (ResidueField Λ)] {a : O →+* Λ} (hΦ : Φ.Std l a)
    (X : Space Φ a) (J : Ideal X.B)
    (hch : ∀ x : X.A →ₐ[Λ] ResidueField Λ, Φ.IsRes ((residue Λ).comp a) (X.P.map (x : X.A →+* ResidueField Λ)) →
      Good4 Φ ((residue Λ).comp a) (X.P.map (x : X.A →+* ResidueField Λ)) → X.SomeIn J (RingHom.ker x) → X.AllIn J (RingHom.ker x))
    (x₀ x₁ : X.A →ₐ[Λ] ResidueField Λ) (hs : Φ.IsRes ((residue Λ).comp a) (X.P.map (x₀ : X.A →+* ResidueField Λ)))
    (hc : Chain4 Φ ((residue Λ).comp a) (X.P.map (x₀ : X.A →+* ResidueField Λ)) (X.P.map (x₁ : X.A →+* ResidueField Λ)))
    (h₁ : X.SomeIn J (RingHom.ker x₁)) : X.AllIn J (RingHom.ker x₀) := by
  have key : ∀ s, Relation.ReflTransGen (fun x y => Good4 Φ ((residue Λ).comp a) y ∧ Φ.Linked ((residue Λ).comp a) x y) s
      (X.P.map (x₁ : X.A →+* ResidueField Λ)) → Φ.IsRes ((residue Λ).comp a) s → Good4 Φ ((residue Λ).comp a) s →
      ∀ x : X.A →ₐ[Λ] ResidueField Λ, X.P.map (x : X.A →+* ResidueField Λ) = s → X.AllIn J (RingHom.ker x) := by
    intro s h
    induction h using Relation.ReflTransGen.head_induction_on with
    | refl =>
      intro k1 k2 x e
      refine hch x (e ▸ k1) (e ▸ k2) ((conn Φ l a hΦ X J x x₁ ?_).2 (hch x₁ k1 k2 h₁))
      rw [e]
      exact Asm.linked_self k1
    | head hl _ ih =>
      rintro k1 k2 x rfl
      obtain ⟨x', rfl⟩ := Asm.end_pt X hl.2
      exact hch x k1 k2 ((conn Φ l a hΦ X J x x' hl.2).2 (ih (Asm.linked_isRes hl.2) hl.1 x' rfl))
  exact key _ hc.2 hs hc.1 x₀ rfl
private theorem conj_trans {H R : Type} [Group H] [CommRing R] {r r' r'' : H →* M4 R} (h : IsConj4 r r') (h' : IsConj4 r' r'') :
    IsConj4 r r'' := by
  obtain ⟨u, hu⟩ := h
  obtain ⟨v, hv⟩ := h'
  exact ⟨v * u, fun g => by rw [hv, hu, mul_inv_rev, Units.val_mul, Units.val_mul]; simp only [mul_assoc]⟩
private theorem res_self (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] :
    (res O O : O →+* ResidueField O) = residue O := RingHom.ext fun x => (res O O).commutes x
private theorem last_step (hCh : _root_.UpperTheory.V.Cu.ChainRankFour) (hCD : ChainDesc4) (hC : CohomologyHyp) (hPM : _root_.UpperTheory.V.Ws.PMExAlt) {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime]
    {c : Coef l} {D : Raw Ω c} (T : Tower D) (hF : T.Fit) (hD : T.Deep) (ι : PadicAlgCl l ≃+* ℂ) (𝔞 : Amb l) (C : ℕ)
    (hB : ∀ (k : Type) [Field k] (a : c.O →+* k), (∀ x ∈ maximalIdeal c.O, a x = 0) → (T.fr ∅).Bounds a T.d C)
    (hd : 30 * (C + 1) * (C + 1) ≤ T.d) {c₁ : Coef l} {h₁ : c.O ≤ c₁.O} {Q : PD T.ι (G T.F Ω) c₁.O} (hQ : T.SeedPairAlt ι h₁ Q)
    {P : PD T.ι (G T.F Ω) 𝔞.V} (hs : 𝔞.Small P) (hp : (T.fr ∅).IsPair (𝔞.a c) P)
    (hr : (T.fr ∅).IsRes (𝔞.red c) (P.map (residue 𝔞.V)))
    (hch : Chain4 (T.fr ∅) (𝔞.red c) (P.map (residue 𝔞.V)) (Q.map (𝔞.red c₁))) :
    ∃ (c' : Coef l) (h : c.O ≤ c'.O) (X : Space (T.fr ∅) (inc h)) (J : Ideal X.B) (y : X.A →+* 𝔞.V), T.PotentialModularityTower ι X J ∧
      y.comp (algebraMap c'.O X.A) = 𝔞.a c' ∧ (∀ b ∈ maximalIdeal X.B, y (algebraMap X.B X.A b) ∈ maximalIdeal 𝔞.V) ∧
      (∀ b ∈ J, y (algebraMap X.B X.A b) = 0) ∧ X.P.map y = P := by
  obtain ⟨c₂, k₂⟩ := hCD 𝔞 c (T.fr ∅) _ _ hr hch
  obtain ⟨c₃, k₃⟩ := smallCo 𝔞 P hs
  obtain ⟨c₄, k₄⟩ := hPM Ω l c D T hF hD ι
  obtain ⟨d₁, a₁, a₂⟩ := (coefSup l).1 c₁ c₂
  obtain ⟨d₂, a₃, a₄⟩ := (coefSup l).1 c₃ c₄
  obtain ⟨c', b₁, b₂⟩ := (coefSup l).1 d₁ d₂
  have e₁ : c₁.O ≤ c'.O := a₁.trans b₁
  have h : c.O ≤ c'.O := h₁.trans e₁
  haveI : Finite (ResidueField c'.O) := by
    haveI : IsLocalHom (algebraMap ℤ_[l] c'.O) := (dvrFacts l c'.O).2.2.1
    haveI : Finite (ResidueField ℤ_[l]) := Finite.of_equiv _ (PadicInt.residueField (p := l)).symm.toEquiv
    exact Module.finite_of_finite (ResidueField ℤ_[l])
  have hS := (std hC D T hF ∅ c' h).1 (Finset.notMem_empty 0)
  obtain ⟨X⟩ := spaceEx (T.fr ∅) l (inc h) hS
  obtain ⟨J, hJ⟩ := k₄ c' h (a₄.trans b₂) X
  obtain ⟨s, t, es, et, rs, cst⟩ := k₂ c' h (a₂.trans b₁)
  obtain ⟨R, _, _, _, f, QR, fi, fa, fr, qc, rfl⟩ := k₃ c' (a₃.trans b₂)
  have inj := (chainMap (T.fr ∅) ((residue c'.O).comp (inc h)) (𝔞.j c') s).2.2
  have loc : ∀ {d : Coef l} (e : d.O ≤ c'.O), maximalIdeal d.O ≤ (maximalIdeal c'.O).comap (inc e) := fun {d} e x hx hu => by
    have h2 : IsUnit (𝔞.a d x) := 𝔞.compat d c' e x ▸ hu.map (𝔞.a c')
    exact hx (IsLocalHom.map_nonunit x h2)
  have jc : (𝔞.j c').comp ((residue c'.O).comp (inc e₁)) = 𝔞.red c₁ :=
    RingHom.ext fun x => congrArg (residue 𝔞.V) (𝔞.compat c₁ c' e₁ x)
  have lQ : (T.fr ∅).Lifts (inc h) t (Q.map (inc e₁)) := by
    refine ⟨hQ.pair.map (inc e₁), hQ.cont.map _ (loc e₁), inj ?_⟩
    show ((Q.map _).map _).map _ = t.map _
    rw [et, res_self, PD.map_map, PD.map_map, ← jc]
    rfl
  obtain ⟨f₁, hf₁⟩ := X.univ c'.O t _ (chain_rank_four_good rs cst).1 lQ
  have sd := hJ.seed ((Algebra.ofId c'.O (PadicAlgCl l)).comp f₁) (by
    have e : X.P.map (((Algebra.ofId c'.O (PadicAlgCl l)).comp f₁ : X.A →ₐ[c'.O] PadicAlgCl l) : X.A →+* PadicAlgCl l) =
        Q.map (algebraMap c₁.O (PadicAlgCl l)) := by
      show (X.P.map (f₁ : X.A →+* c'.O)).map (algebraMap c'.O (PadicAlgCl l)) = _
      rw [hf₁]
      rfl
    rw [e]
    exact hQ.seed)
  have s₁ : X.SomeIn J (RingHom.ker ((res c'.O c'.O).comp f₁)) := Asm.someIn_of_locZero X J _ sd fun z hz => by
    have h0 : f₁ z = 0 := Subtype.ext hz
    show res c'.O c'.O (f₁ z) = 0
    rw [h0, map_zero]
  have e₁' : X.P.map (((res c'.O c'.O).comp f₁ : X.A →ₐ[c'.O] ResidueField c'.O) : X.A →+* ResidueField c'.O) = t := by
    show (X.P.map (f₁ : X.A →+* c'.O)).map (res c'.O c'.O : c'.O →+* ResidueField c'.O) = t
    rw [hf₁]
    exact lQ.red
  have lR : (T.fr ∅).Lifts (inc h) s QR := by
    refine ⟨Asm.pair_of f fi ?_, qc, inj ?_⟩
    · rw [← RingHom.comp_assoc, fa]
      have : (𝔞.a c').comp (inc h) = 𝔞.a c := RingHom.ext fun x => 𝔞.compat c c' h x
      rw [this]
      exact hp
    · show (QR.map _).map _ = s.map _
      rw [es, PD.map_map, PD.map_map, fr]
  obtain ⟨f₀, hf₀⟩ := X.univ R s _ rs lR
  have e₀ : X.P.map (((res c'.O R).comp f₀ : X.A →ₐ[c'.O] ResidueField c'.O) : X.A →+* ResidueField c'.O) = s := by
    show (X.P.map (f₀ : X.A →+* R)).map (res c'.O R : R →+* ResidueField c'.O) = s
    rw [hf₀]
    exact lR.red
  have all := allIn_of_chain4 hS X J
    (hCh hC D T hF hD ι c' h X J hJ C (hB _ _ fun x hx => (residue_eq_zero_iff _).2 (loc h hx)) hd)
    ((res c'.O R).comp f₀) ((res c'.O c'.O).comp f₁) (e₀ ▸ rs) (e₀ ▸ e₁' ▸ cst) s₁
  refine ⟨c', h, X, J, f.comp (f₀ : X.A →+* R), hJ, ?_, fun b hb => ?_, Asm.zero_of_allIn X J _ all fun z hz => ?_, ?_⟩
  · rw [RingHom.comp_assoc, AlgHom.comp_algebraMap, fa]
  · have h0 : res c'.O R ((f₀.comp (IsScalarTower.toAlgHom c'.O X.B X.A)) b) = 0 := by
      rw [res_map, res_eq_zero_iff]
      exact hb
    refine (residue_eq_zero_iff _).1 ((RingHom.congr_fun fr (f₀ (algebraMap X.B X.A b))).trans ?_)
    exact (congrArg (𝔞.j c') h0).trans (map_zero _)
  · have h0 : f₀ z = 0 := (map_eq_zero_iff f fi).1 hz
    show res c'.O R (f₀ z) = 0
    rw [h0, map_zero]
  · exact congrArg (fun Z => PD.map Z f) hf₀
theorem UpperTheory.V.Cu.promodularity_case_three_of_chain_reduction : ExistsTensorFactorTower → _root_.UpperTheory.V.Cu.ChainRankFour → ChainDesc4 → _root_.UpperTheory.V.Cu.RankFourChainReductionDense → _root_.UpperTheory.V.Cu.PromodularityCaseThreeDense := by
  intro hLem hCh hCD hCIV hC hFW hH h4 hPM Ω _ _ _ l _ c D hD ι 𝔞 r u hK hS
  have hG : D.Good := hD.1
  obtain ⟨pr, hl, hP⟩ := labels D hG 𝔞 r u hK
  obtain ⟨T₀, rfl, ok, four, tame₀⟩ := hLem D hD pr hl
  have hF₀ : T₀.Fit := hH D T₀ hD ok four
  have hc := hCIV hC hH h4 D T₀ hD ok four tame₀ ι 𝔞
  obtain ⟨P, qP, nP, cP, sP⟩ := hP _ hF₀.1.dist
  obtain ⟨P', qP', cP', lP'⟩ := lat hC D hG 𝔞 _ _ hl hF₀.1.dist P qP nP (sP hS)
  obtain ⟨T₁, le₁, tame, hT⟩ := hc _ lP'
  have f₁ := leFit D hG T₀ T₁ le₁
  have hF₁ := f₁.2.2.2.2.1 hF₀
  obtain ⟨C, hB⟩ := x2 hC hFW D T₁ hF₁ tame
  obtain ⟨T, m, le, lay, deep, hd⟩ := layerEx D hG T₁ hF₁ tame (30 * (C + 1) * (C + 1))
  have hF := (leFit D hG T₁ T le).2.2.2.2.1 hF₁
  obtain ⟨c₁, h₁, Q, hQ, hch⟩ := hT T le deep
  obtain ⟨P'', sm, pr'', er, ov, rs, ine⟩ := restrQ D hG T₀ T hF₀ (f₁.2.2.2.2.2.2 T le) 𝔞 P' qP' lP'
  obtain ⟨c', h, X, J, y, k1, k2, k3, k4, k5⟩ :=
    last_step hCh hCD hC hPM T hF deep ι 𝔞 C (hB T m le lay) hd hQ sm pr'' rs (hch _ ov rs)
  refine ⟨T, c', h, X, J, y, P'.r, hF, deep, k1, k2, k3, k4, conj_trans cP cP', qP'.pair.mult, by rw [k5, er],
    fun v i s hs => ?_⟩
  subst k5
  exact (PD.map_ψ X.P y v i s).symm.trans (ine v i s hs)
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.CuPChainIV
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.SeedRes
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws
namespace UpperTheory.V.Ws.Chn
section Abs
variable {O Γ k : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [Field k] {Φ : Fr O Γ} {a : O →+* k}
end Abs
section In
variable {ι Γ R : Type} [Group Γ] [CommRing R] {P P' : PD ι Γ R}
end In
section Map
variable {O Γ R R' : Type} [CommRing O] [Group Γ] [CommRing R] [CommRing R'] {Φ : Fr O Γ} {a : O →+* R}
end Map
section Gal
variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c}
theorem seed_res_alt (T : Tower D) (𝔞 : Amb l) {ι : PadicAlgCl l ≃+* ℂ} {c₁ : Coef l} {h : c.O ≤ c₁.O}
    {Q : PD T.ι (G T.F Ω) c₁.O} (hQ : T.SeedPairAlt ι h Q) : (T.fr ∅).IsRes (𝔞.red c) (Q.map (𝔞.red c₁)) := by
  have h1 : (T.fr ∅).IsRes ((residue c₁.O).comp (inc h)) (Q.map (residue c₁.O)) := by
    refine ⟨pair_map hQ.pair _, hQ.res, fun i j n => ?_⟩
    have h2 := (hQ.cont i j 1).comp (Ideal.Quotient.lift (maximalIdeal c₁.O ^ 1) (residue c₁.O)
      fun x hx => (residue_eq_zero_iff x).2 (by rwa [pow_one] at hx))
    exact h2.comp (Ideal.Quotient.mk ((⊥ : Ideal (ResidueField c₁.O)) ^ n))
  have h2 := (chainMap (T.fr ∅) _ (𝔞.j c₁) _).1.2 h1
  have e1 : (𝔞.j c₁).comp ((residue c₁.O).comp (inc h)) = 𝔞.red c :=
    RingHom.ext fun x => congrArg (residue 𝔞.V) (𝔞.compat c c₁ h x)
  rw [e1] at h2
  exact h2
end Gal
end UpperTheory.V.Ws.Chn
end
end

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws
namespace UpperTheory.V.Cu.RankFourChainReduction
open UpperTheory.V.Ws.Chn
end UpperTheory.V.Cu.RankFourChainReduction
open UpperTheory.V.Cu UpperTheory.V.Ws.Chn UpperTheory.V.Cu.RankFourChainReduction in
theorem UpperTheory.V.Cu.chainIV_alt : _root_.UpperTheory.V.Cu.RankFourChainReductionDense := by
  intro hC hH hS Ω _ _ _ l _ c D T₀ h3 hok h4 htame ι 𝔞 c₀ hc₀
  have hG : D.Good := h3.1
  have hF : T₀.Fit := hH D T₀ h3 hok h4
  have ha := red_zero 𝔞 c
  have ok0 : (T₀.fr ∅).Ok (𝔞.red c) := (std hC D T₀ hF ∅ c le_rfl).2 _ _ ha
  obtain ⟨w, s, hw, hsp, hs, hsM, hseed⟩ := hS Ω l c D T₀ h3 hok h4 ι 𝔞
  obtain ⟨p0, hp0, hov0⟩ := UpperTheory.exists_residualRep_restriction_of_latticeShape D hG T₀ hF _ _ ha ok0 c₀ hc₀
  obtain ⟨-, hp0P, -⟩ := goodQ D hG T₀ hF _ _ ha _ c₀ p0 hc₀ (fun w hw => rt_ne (Φ := T₀.fr ∅) ok0 w hw) hov0 hp0 ∅
  obtain ⟨W1, p2, hW1, hW1s, hp2, hp2Q, hp2A, hp2E⟩ :=
    gysinPs hC D T₀ hF _ _ ha {w} (by simpa using ⟨hw, hsp⟩) s hs hsM
  obtain ⟨W2, p3, p4, hW2, hW2s, hp3, hp4, hp3Q, hp4Q, h30, h42, h34, h3E⟩ :=
    gysinAl hC D T₀ hF _ _ ha W1 hW1s p0 p2 (res_mono T₀ (Finset.empty_subset _) hp0) hp2 hp0P (qP hp2Q)
  obtain ⟨T₁, hL1, ht1, hd1⟩ := diesEx D hG T₀ htame hok W2 hW2s
  refine ⟨T₁, hL1, ht1, fun T hL _ => ?_⟩
  have hT : T₀.Le T := (leFit D hG T₀ T₁ hL1).2.2.2.2.2.2 T hL
  obtain ⟨lo, -, -, -, lf, -, -⟩ := leFit D hG T₀ T hT
  have hd : ∀ w ∈ W2, Dies l w T.F := fun w hw => dies_mono hL.le (hd1 w hw)
  obtain ⟨c₁, h, Q, hQ, hovs, hQA, hQB, hQT⟩ := hseed T hT (lo hok) (hd w (hW2 (hW1 (Finset.mem_singleton_self w))))
  refine ⟨c₁, h, Q, hQ, fun u hu hur => ?_⟩
  have okT : (T.fr ∅).Ok (𝔞.red c) := (std hC D T (lf hF) ∅ c le_rfl).2 _ _ ha
  have hq := _root_.UpperTheory.V.Ws.Chn.seed_res_alt T 𝔞 hQ
  replace hs := res_mono T₀ (hW1.trans hW2) hs
  replace hp0 := res_mono T₀ (Finset.empty_subset W2) hp0
  replace hp2 := res_mono T₀ hW2 hp2
  have R := fun x hx => restrT D hG T₀ T hT hF _ _ ha W2 hW2s hd x hx (Or.inl h4.five)
  obtain ⟨q0, hq0, o0⟩ := R p0 hp0
  obtain ⟨q2, hq2, o2⟩ := R p2 hp2
  obtain ⟨q3, hq3, o3⟩ := R p3 hp3
  obtain ⟨q4, hq4, o4⟩ := R p4 hp4
  have O := overFacts D hG T₀ T hT hF _ _ ha W2 ∅
  obtain ⟨-, -, -, a1, -, -, -, a2⟩ := O p0 p3 q0 q3 hp0 hp3 hq0 hq3 o0 o3
  obtain rfl : u = q0 := a2 c₀ _ hc₀.res.pair hov0 u hur hu
  obtain ⟨-, b0, b1, -, b2, -, b4, -⟩ := O p3 p4 q3 q4 hp3 hp4 hq3 hq4 o3 o4
  obtain ⟨-, c0, c1, c2, -, -, -, -⟩ := O p4 p2 q4 q2 hp4 hp2 hq4 hq2 o4 o2
  obtain ⟨-, d0, d1, -, d2, d3, -, -⟩ := O p2 s q2 _ hp2 hs hq2 hq o2 hovs
  obtain ⟨-, e0, -, -, -, -, -, -⟩ := O s s _ _ hs hs hq hq hovs hovs
  have hlat : LatShape D T.pr (resQ T₀.F T₀.g0) (𝔞.red c) c₀ := hT.pr ▸ hc₀
  have hrt : ∀ w ∈ roots, 𝔞.red c ((frQ D T.pr (resQ T₀.F T₀.g0)).rt w (resQ T₀.F T₀.g0)) ≠ 1 := by
    rw [hT.pr]; exact fun w hw => rt_ne (Φ := T₀.fr ∅) ok0 w hw
  obtain ⟨-, uP, ug⟩ := goodQ D hG T (lf hF) _ _ ha _ c₀ u hlat hrt hu hur ∅
  have P3 := b1 (qP hp3Q)
  have P4 := c1 (qP hp4Q)
  have P2 := d1 (qP hp2Q)
  have M3 := b0 _ (qM hp3Q.1)
  have M4 := c0 _ (qM hp4Q.1)
  have M2 := d0 _ (qM hp2Q.1)
  have Ms := e0 _ hsM
  have s03 := a1 hp0P (qP hp3Q) (samePs_symm h30)
  have s34 := b2 (qM hp3Q.1) (qM hp4Q.1) h34
  have s42 := c2 (qP hp4Q) (qP hp2Q) h42
  have s2s := d2 (qM hp2Q.1) hsM hp2A
  have A3 := (b4 (qM hp3Q.1)).1 h3E
  have E2 := d3 (qP hp2Q).1 hp2E
  have g0 : Good4 (T.fr ∅) (𝔞.red c) u :=
    Or.inl (ug.elim (fun x => Or.inl ⟨x.1, Or.inl x.2⟩) fun x => Or.inr (Or.inr (Or.inl x)))
  have g3 : Good4 (T.fr ∅) (𝔞.red c) q3 :=
    Or.inl (ug.elim (fun x => Or.inl ⟨(samePs_ent hur hq3 uP.1 P3.1 s03).1 x.1, Or.inr A3⟩)
      fun x => Or.inr (Or.inr (Or.inl ⟨samePs_inV hq3 P3 s03 x.1, A3⟩)))
  have g4 : Good4 (T.fr ∅) (𝔞.red c) q4 :=
    Or.inl (Or.inl ⟨(samePs_ent hq4 hq2 P4.1 P2.1 s42).2 E2, Or.inr ((sameAl_ent hq3 hq4 M3 M4 s34).1 A3)⟩)
  have g2 : Good4 (T.fr ∅) (𝔞.red c) q2 :=
    Or.inr (Or.inl ⟨inA_of hq2 (d0 _ hp2Q.1) s2s hQA, E2⟩)
  have gs : Good4 (T.fr ∅) (𝔞.red c) (Q.map (𝔞.red c₁)) := Or.inr (Or.inr ⟨hQA, hQB, hQT⟩)
  exact ⟨g0, (((Relation.ReflTransGen.single ⟨g3, lineP _ _ okT _ _ hur hq3 uP P3 s03⟩).tail
    ⟨g4, lineM _ _ okT _ _ hq3 hq4 M3 M4 s34⟩).tail ⟨g2, lineP _ _ okT _ _ hq4 hq2 P4 P2 s42⟩).tail
    ⟨gs, lineM _ _ okT _ _ hq2 hq M2 Ms s2s⟩⟩
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.MPKapEx
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N IsLocalRing Polynomial
open UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S3
open UpperTheory.V.Cu
open scoped Matrix
namespace UpperTheory.V.Cu2
namespace KapEx
end KapEx
open UpperTheory.V.Cu2.KapEx in
theorem kapEx_alt (h1 : TwistIne) (h2 : AlgType) : _root_.UpperTheory.V.Cu2.KapExAlt := by
  intro hP Ω _ _ _ l _ ι K' _ hl2 hK2 hTC hld hsp hcc
  obtain ⟨cc, hcc⟩ := hcc
  have : IsTotallyComplex K' := hTC
  have : IsAlgClosure K' Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) K'⟩
  have : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  have : IsGalois K' Ω := IsGalois.tower_top_of_isGalois ℚ K' Ω
  have : CompactSpace (G K' Ω) := inferInstanceAs (CompactSpace (Ω ≃ₐ[K'] Ω))
  obtain ⟨κ₀, htw⟩ := _root_.UpperTheory.V.Sd.twist_of_printed_results hP K' Ω hK2 l hl2 hld ι cc hcc
  obtain ⟨art, Y, a, τ, hart, hYa, hL, ha1, ha0, -⟩ := htw.alg
  obtain ⟨mo, hmo0, -, hmo⟩ := htw.ord
  have hi : (galOf ℚ K' Ω).index = 2 := (galEmbTop ℚ K' Ω).2.2.trans hK2
  have hccK : cc ∉ galOf ℚ K' Ω := cc_notMem K' hcc
  have hfix : ∀ t : G ℚ Ω, t ∈ K'.fixingSubgroup → t ∈ galOf ℚ K' Ω := fun t h =>
    (mem_galOf ℚ K' Ω).2 fun x => (IntermediateField.mem_fixingSubgroup_iff K' t).1 h x x.2
  have hIne : ∀ (A : ValuationSubring Ω) (h : G K' Ω), resQ K' h ∈ Ine (F := ℚ) A → h ∈ Ine (F := K') A :=
    fun A h hh => ⟨hh.1, hh.2⟩
  have hεc : Continuous (cycBar K' Ω l) := by
    have hf : Continuous (((algebraMap ℚ_[l] (Qbar l)).comp PadicInt.Coe.ringHom).toMonoidHom : ℤ_[l] → Qbar l) :=
      (continuous_algebraMap ℚ_[l] (Qbar l)).comp continuous_subtype_val
    exact (Units.continuous_map hf).comp (continuous_cycZ K' Ω l)
  have hεunr : ∀ A : ValuationSubring Ω, ¬ A.valuation (l : Ω) < 1 → ∀ h ∈ Ine (F := K') A, cycBar K' Ω l h = 1 := by
    intro A hA h hh
    have e : cycZ K' Ω l h = 1 := MonoidHom.mem_ker.1 (((places K' Ω l A).2.2.2 hA) hh)
    simp only [cycBar, MonoidHom.comp_apply, e, map_one]
  have hεres : ∀ h : G K' Ω, cycBar K' Ω l h = cycBar ℚ Ω l (resQ K' h) := fun h => rfl
  have hlam : ∀ h : G K' Ω, (κ₀ ^ 2 * cycBar K' Ω l) h = κ₀ h ^ 2 * cycBar K' Ω l h := fun h => by
    rw [MonoidHom.mul_apply, MonoidHom.pow_apply]
  have hlamc : Continuous ⇑(κ₀ ^ 2 * cycBar K' Ω l : G K' Ω →* (Qbar l)ˣ) := by
    have e : ⇑(κ₀ ^ 2 * cycBar K' Ω l : G K' Ω →* (Qbar l)ˣ) = fun h => κ₀ h ^ 2 * cycBar K' Ω l h := funext hlam
    rw [e]
    exact (htw.cont.pow 2).mul hεc
  obtain ⟨d, hd0, hd⟩ := exists_pow_cong _ hlamc
  refine ⟨d * mo, (κ₀ ^ 2 * cycBar K' Ω l) ^ (d * mo), fun j hj => ?_⟩
  rw [← pow_mul]
  have hN : 0 < d * mo * j := Nat.mul_pos (Nat.mul_pos hd0 hmo0) (by omega)
  obtain ⟨Y', hY', hL'⟩ := h2 K' Ω l ι art Y a κ₀ hart hYa hL (2 * (d * mo * j)) (d * mo * j)
  have hpw : (κ₀ ^ 2 * cycBar K' Ω l) ^ (d * mo * j) =
      κ₀ ^ (2 * (d * mo * j)) * cycBar K' Ω l ^ (d * mo * j) := by
    rw [mul_pow, ← pow_mul]
  refine ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have e : ⇑((κ₀ ^ 2 * cycBar K' Ω l) ^ (d * mo * j) : G K' Ω →* (Qbar l)ˣ) = fun h => (κ₀ h ^ 2 * cycBar K' Ω l h) ^ (d * mo * j) :=
      funext fun h => by rw [MonoidHom.pow_apply, hlam]
    rw [e]
    exact ((htw.cont.pow 2).mul hεc).pow _
  · refine ⟨art, Y', _, τ, hart, hY', by rw [hpw]; exact hL', ?_, ?_⟩
    · show ((2 * (d * mo * j) : ℕ) : ℤ) * a τ + ((d * mo * j : ℕ) : ℤ) = -((d * mo * j : ℕ) : ℤ)
      rw [ha1]
      push_cast
      ring
    · show ((2 * (d * mo * j) : ℕ) : ℤ) * a (ComplexEmbedding.conjugate τ) + ((d * mo * j : ℕ) : ℤ) = ((d * mo * j : ℕ) : ℤ)
      rw [ha0]
      push_cast
      ring
  · intro t ht h h' hh'
    have htg : t ∉ galOf ℚ K' Ω := fun h0 => ht (by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      exact (mem_galOf ℚ K' Ω).1 h0 ⟨x, hx⟩)
    have hu : cc⁻¹ * t ∈ galOf ℚ K' Ω := by
      rw [Subgroup.mul_mem_iff_of_index_two hi, inv_mem_iff]
      exact iff_of_false hccK htg
    rw [← range_galEmb] at hu
    obtain ⟨v, hv⟩ := hu
    have hh'' : galEmb ℚ K' Ω h' = t * galEmb ℚ K' Ω h * t⁻¹ := hh'
    have hs : galEmb ℚ K' Ω h' = cc * galEmb ℚ K' Ω (v * h * v⁻¹) * cc⁻¹ := by
      rw [map_mul, map_mul, map_inv, hv, hh'']
      group
    have hc := htw.conj (v * h * v⁻¹) h' hs
    simp only [map_mul, map_inv, mul_inv_cancel_comm] at hc
    have hε' : cycBar K' Ω l h' = cycBar K' Ω l h := by
      rw [hεres, hεres h, hh', map_mul, map_mul, map_inv, mul_inv_cancel_comm]
    rw [MonoidHom.pow_apply, MonoidHom.pow_apply, ← mul_pow, hlam, hlam, hε', mul_mul_mul_comm, ← mul_pow, hc,
      ← sq (cycBar K' Ω l h), inv_pow, inv_mul_cancel, one_pow]
  · intro t ht h hh
    have htg : t ∉ galOf ℚ K' Ω := fun h0 => ht (by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      exact (mem_galOf ℚ K' Ω).1 h0 ⟨x, hx⟩)
    have e1 := htw.ver h t htg hh
    have e2 : cycBar K' Ω l h = cycBar ℚ Ω l t * cycBar ℚ Ω l t := by
      rw [hεres, hh, map_mul]
    rw [MonoidHom.pow_apply, hlam, e1, e2, neg_sq, inv_pow, ← sq (cycBar ℚ Ω l t), inv_mul_cancel, one_pow]
  · intro h
    apply cong_of_mem
    rw [MonoidHom.pow_apply, pow_mul, pow_mul]
    exact pow_mem (pow_mem (hd h) mo) j
  · intro A hA h hh
    have h' := hIne A h hh
    rw [MonoidHom.pow_apply, hlam, hεunr A hA h h', mul_one, ← pow_mul,
      show 2 * (d * mo * j) = mo * (2 * d * j) by ring, pow_mul, hmo A hA h h', one_pow]
  · intro A hA
    rcases h1 Ω l ι K' hK2 hTC hld hsp cc κ₀ htw A hA with e | e
    · refine Or.inr fun h hh => ?_
      rw [MonoidHom.pow_apply, hlam, e h (hIne A h hh), zpow_neg, zpow_natCast, sq, mul_assoc, inv_mul_cancel, mul_one,
        inv_pow]
    · refine Or.inl fun h hh => ?_
      rw [MonoidHom.pow_apply, hlam, e h (hIne A h hh), one_pow, one_mul, zpow_natCast]
end UpperTheory.V.Cu2
end
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.MPTauEx
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N IsLocalRing Polynomial
open UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S3
open UpperTheory.V.Cu
open scoped Matrix
namespace UpperTheory.V.Cu2
private theorem ce_char {l : ℕ} [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [T2Space Γ] (ka : Γ →* (PadicAlgCl l)ˣ) (h : Continuous ka) :
    ∃ E : IntermediateField ℚ_[l] (PadicAlgCl l), FiniteDimensional ℚ_[l] E ∧
      ∀ g, (ka g).val ∈ E ∧ ‖(ka g).val‖ ≤ 1 := by
  have hc : Continuous fun g => (ka g).val := Units.continuous_val.comp h
  let r : Γ →* GL (Fin 1) (PadicAlgCl l) :=
    (Units.map (Matrix.scalar (Fin 1) : PadicAlgCl l →+* _).toMonoidHom).comp ka
  have hr : ∀ (g : Γ) (i j : Fin 1), (r g).val i j = (ka g).val := by
    intro g i j
    obtain rfl : i = j := Subsingleton.elim _ _
    simp [r]
  obtain ⟨E, hE, hm⟩ := GlobalTheory.CompactRepField.exists_finiteDimensional_entries_mem l Γ 1 r
    (fun i j => by simp only [hr]; exact hc)
  refine ⟨E, hE, fun g => ⟨hr g 0 0 ▸ hm g 0 0, ?_⟩⟩
  obtain ⟨C, hC⟩ := (isCompact_range hc.norm).bddAbove
  by_contra hg
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt C (not_le.1 hg)
  have := hC ⟨g ^ N, rfl⟩
  simp only [map_pow, Units.val_pow_eq_pow_val, norm_pow] at this
  exact absurd hN (not_lt.2 this)
theorem tauEx' (h1 : _root_.UpperTheory.V.Cu2.KapExAlt) (h2 : TauOf) : _root_.UpperTheory.V.Cu.TauExAlt := by
  intro hP Ω _ _ _ l _ ι K' _ hl2 hK hTC hdisc hdec hcc g0 hg0
  obtain ⟨m, κ, hκ⟩ := h1 hP Ω l ι K' hl2 hK hTC hdisc hdec hcc
  haveI : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  haveI : IsGalois K' Ω := IsGalois.tower_top_of_isGalois ℚ K' Ω
  haveI : CompactSpace (G K' Ω) := inferInstanceAs (CompactSpace (Ω ≃ₐ[K'] Ω))
  haveI : T2Space (G K' Ω) := inferInstanceAs (T2Space (Ω ≃ₐ[K'] Ω))
  have hc : Continuous κ := by simpa using (hκ 1 le_rfl).cont
  obtain ⟨E, hE, hmE⟩ := ce_char (G K' Ω) κ hc
  haveI := hE
  obtain ⟨c₁, hc₁⟩ := UpperTheory.V.X.So.coefOf l E
  refine ⟨m, c₁, κ, fun c₂ hc₂ j hj => ?_⟩
  refine h2 Ω l ι K' hl2 hK hdec g0 hg0 (m * j) (κ ^ j) (hκ j hj) c₂ fun h => ?_
  have e : (((κ ^ j) h : (Qbar l)ˣ) : Qbar l) = ((κ h : (Qbar l)ˣ) : Qbar l) ^ j := by
    rw [MonoidHom.pow_apply, Units.val_pow_eq_pow_val]
  rw [e]
  exact pow_mem (hc₂ ((hc₁ _).2 (hmE h))) j
end UpperTheory.V.Cu2
end
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.MPAlgType
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N IsLocalRing Polynomial
open UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S3
open UpperTheory.V.Cu
open scoped Matrix
namespace UpperTheory.V.Cu2
namespace AlgType
variable {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] {l : ℕ} [Fact l.Prime]
end AlgType
open AlgType in
theorem algType_alt (hP : _root_.UpperTheory.V.Af.Hypotheses') : AlgType := by
  intro K Ω _ _ _ _ _ l _ ι art Y a κ ha h1 h2 n j
  have H : Good art ι a κ := ⟨Y, h1, h2⟩
  have H1 : Good art ι (fun _ => 1) (cycBar K Ω l) := good_cyc ha ι
  have H0 : Good art ι 0 1 := good_one H
  have key0 : ∀ j : ℕ, Good art ι (fun _ => (j : ℤ)) (cycBar K Ω l ^ j) := by
    intro j
    induction j with
    | zero => exact good_cong H0 (funext fun _ => by simp) (pow_zero _).symm
    | succ j ih =>
      exact good_cong (good_mul ih H1) (funext fun _ => by simp only [Pi.add_apply, Nat.cast_add, Nat.cast_one] <;> ring)
        (pow_succ _ _).symm
  have key : ∀ n : ℕ, Good art ι (fun e => (n : ℤ) * a e + j) (κ ^ n * cycBar K Ω l ^ j) := by
    intro n
    induction n with
    | zero => exact good_cong (key0 j) (funext fun _ => by simp) (by simp)
    | succ n ih =>
      refine good_cong (good_mul ih H) (funext fun e => ?_) ?_
      · simp only [Pi.add_apply, Nat.cast_add, Nat.cast_one] <;> ring
      · rw [pow_succ]
        exact mul_right_comm _ _ _
  exact key n
end UpperTheory.V.Cu2
end
end
end

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open UpperTheory.V UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.GradeZeroInterpolatingElement
namespace UpperTheory.V.Cu
theorem main4_alt : _root_.UpperTheory.V.Cu.AutomorphyRankFourDense := _root_.UpperTheory.V.Cu.modularity_rank_four_of_promodularity_case_three (_root_.UpperTheory.V.Cu.promodularity_case_three_of_chain_reduction existsTensorSeedTower_holds (_root_.UpperTheory.V.Cu.chain_rank_four_of_red_a_y_coin_fib_y (redA_of redTanA) yCoin (fibY_of torusY)) chainDesc4 _root_.UpperTheory.V.Cu.chainIV_alt)
theorem tauEx' : _root_.UpperTheory.V.Cu.TauExAlt := fun hP => _root_.UpperTheory.V.Cu2.tauEx' (_root_.UpperTheory.V.Cu2.kapEx_alt Cu2.twistIne (_root_.UpperTheory.V.Cu2.algType_alt hP)) Cu2.tauOf hP
end UpperTheory.V.Cu
end
