module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TameValuesGaloisCharFormResidueUnitCharacter
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RankOneBaseWeightEqCmTheta
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLevelGroupWithCharacterAtTypePlaces

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlacesAvoidAuxiliary
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlacesAvoidAuxiliary
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

namespace GlobalTheory.LevelPlaceSep

theorem not_mem_two {D : D7} (P : PlE D.host) {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (h1 : P ∈ placesOver D.host.E p) (h2 : P ∈ placesOver D.host.E q) : False := by
  obtain ⟨a, b, hab⟩ : IsCoprime (p : ℤ) (q : ℤ) := Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hp hq).2 hpq)
  have e := congrArg (Int.cast : ℤ → 𝓞 D.host.E) hab
  push_cast at e
  apply P.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← e]
  have h1' : ((p : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal := h1
  have h2' : ((q : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal := h2
  exact P.asIdeal.add_mem (P.asIdeal.mul_mem_left _ h1') (P.asIdeal.mul_mem_left _ h2')

theorem mem_placesOver_of_comap {D : D7} {P P' : PlE D.host}
    (h : P.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) = P'.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E))) {p : ℕ}
    (hP : P ∈ placesOver D.host.E p) : P' ∈ placesOver D.host.E p := by
  have e : ((p : ℕ) : 𝓞 D.host.E) = (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) (p : 𝓞 (maximalRealSubfield D.host.E)) := (map_natCast _ p).symm
  show ((p : ℕ) : 𝓞 D.host.E) ∈ P'.asIdeal
  have hP' : ((p : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal := hP
  rw [e, ← Ideal.mem_comap, ← h, Ideal.mem_comap, ← e]
  exact hP'

theorem isConjPl_conjPlE {D : D7} (P : PlE D.host) : Formalism.BasicNotions.IsConjPl D.host P (GlobalTheory.SplitConjPlace.conjPlE P) := by
  intro x y hxy
  rw [GlobalTheory.SplitConjPlace.mem_conjPlE]
  have : IsCMField.ringOfIntegersComplexConj D.host.E y = x := by
    apply RingOfIntegers.ext
    rw [IsCMField.coe_ringOfIntegersComplexConj, hxy, GlobalTheory.LocM.complexConj_eq_conj,
      GlobalTheory.FixedPlaceSplit.host_conj_conj]
  rw [this]

theorem eq_of_qpOf {D : D7} (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host)
    (hPq : ∀ v, NG.OverPl (Pq v) v) (S : Finset (PlE D.host)) {P P' : PlE D.host}
    (hP : P ∈ qpOf D Pq S) (hP' : P' ∈ qpOf D Pq S) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)))
    (hv : P.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) = v.asIdeal) (hv' : P'.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) = v.asIdeal) : P = P' := by
  rcases GlobalTheory.SplitConjPlace.eq_or_eq_conjPlE P P' (hv'.trans hv.symm) with e | e
  · exact e.symm
  have hw : (Pq v).asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) = v.asIdeal := hPq v
  have hS : Pq v ∈ S := by
    rcases GlobalTheory.SplitConjPlace.eq_or_eq_conjPlE P (Pq v) (hw.trans hv.symm) with e' | e'
    · rw [e']; exact qpOf_sub D Pq S hP
    · rw [e', ← e]; exact qpOf_sub D Pq S hP'
  exact (qpOf_eq D Pq S hP hv hS).trans (qpOf_eq D Pq S hP' hv' hS).symm

theorem g_ne_g {D : D7} {k k' : Fin 2} (h : k ≠ k') : D.host.g k ≠ D.host.g k' := by
  have h0 := D.host.g_ne
  fin_cases k <;> fin_cases k' <;> simp_all [eq_comm]

theorem levelPlaces_sep : ∀ (D : D7) (T : TwR D.LL0 D.nd) (i : T.Tw) (Q : Finset (PlE D.host))
    (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (sp : PlE D.host → SplitPlace D.host.E),
    (∀ v, NG.OverPl (Pq v) v) → (∀ P ∈ Q, IsSplitPl D.host P) →
    (∀ P ∈ Q, P ∉ T.pD i ∧ ∀ k' : Fin 2, P ∉ placesOver D.host.E (D.host.g k')) → (∀ P ∈ T.pD i, IsSplitPl D.host P) →
    (∀ P, (P ∈ qpOf D Pq Q ∨ P ∈ qpOf D Pq (T.pD i) ∨ ∃ kv, P = NX.pG D kv) → (sp P).w = P) →
    (∀ P P', (P ∈ qpOf D Pq Q ∨ P ∈ qpOf D Pq (T.pD i) ∨ ∃ kv, P = NX.pG D kv) →
      (P' ∈ qpOf D Pq Q ∨ P' ∈ qpOf D Pq (T.pD i) ∨ ∃ kv, P' = NX.pG D kv) → (sp P).v = (sp P').v → P = P') ∧
    (∀ P ∈ qpOf D Pq Q, P ∉ qpOf D Pq (T.pD i)) ∧ (∀ kv, NX.pG D kv ∉ qpOf D Pq Q ∧ NX.pG D kv ∉ qpOf D Pq (T.pD i)) ∧
    ∀ kv kv', NX.pG D kv = NX.pG D kv' → kv = kv' := by
  intro D T i Q Pq sp hPq hQs hQ hpDs hsp
  obtain ⟨pp, hpp, hne, hpD⟩ : ∃ pp : ℕ, pp.Prime ∧ (∀ k, pp ≠ D.host.g k) ∧
      ∀ P, P ∈ T.pD i ↔ P ∈ placesOver D.host.E pp := by
    refine ⟨if T.l i = D.host.pde then D.host.pde' else D.host.pde, ?_, ?_,
      fun P => by rw [← Finset.mem_coe, T.pD_eq i]⟩
    · split_ifs
      · exact D.host.pde'_prime
      · exact D.host.pde_prime
    · intro k
      split_ifs
      · exact (D.host.pde_ne_g k).2
      · exact (D.host.pde_ne_g k).1
  have hG : ∀ kv, NX.pG D kv ∈ placesOver D.host.E (D.host.g kv.1) := fun kv => D.naut.plGw_over kv.1 kv.2
  have c2 : ∀ P ∈ qpOf D Pq Q, P ∉ qpOf D Pq (T.pD i) := fun P hP hP' =>
    (hQ P (qpOf_sub D Pq Q hP)).1 (qpOf_sub D Pq _ hP')
  have c3 : ∀ kv, NX.pG D kv ∉ qpOf D Pq Q ∧ NX.pG D kv ∉ qpOf D Pq (T.pD i) := fun kv =>
    ⟨fun h => (hQ _ (qpOf_sub D Pq Q h)).2 kv.1 (hG kv),
     fun h => not_mem_two _ hpp (D.host.g_prime kv.1) (hne kv.1) ((hpD _).1 (qpOf_sub D Pq _ h)) (hG kv)⟩
  have c4 : ∀ kv kv', NX.pG D kv = NX.pG D kv' → kv = kv' := by
    rintro ⟨k, v⟩ ⟨k', v'⟩ h
    by_cases hk : k = k'
    · subst hk
      have : v = v' := D.naut.plGw_inj k h
      rw [this]
    · exact (not_mem_two _ (D.host.g_prime k) (D.host.g_prime k') (g_ne_g hk) (hG ⟨k, v⟩)
        (by rw [h]; exact hG ⟨k', v'⟩)).elim
  refine ⟨?_, c2, c3, c4⟩
  intro P P' hP hP' hv
  have hcP : P.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) = (sp P).v.asIdeal := by
    have := (sp P).w_under; rw [hsp P hP] at this; exact this
  have hcP' : P'.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) = (sp P).v.asIdeal := by
    have := (sp P').w_under; rw [hsp P' hP'] at this; rw [this, hv]
  have hc : P.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) = P'.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) := hcP.trans hcP'.symm
  have same : ∀ {p : ℕ}, P' ∈ placesOver D.host.E p → P ∈ placesOver D.host.E p :=
    fun h => mem_placesOver_of_comap hc.symm h
  have same' : ∀ {p : ℕ}, P ∈ placesOver D.host.E p → P' ∈ placesOver D.host.E p :=
    fun h => mem_placesOver_of_comap hc h
  rcases hP with hP | hP | ⟨kv, rfl⟩ <;> rcases hP' with hP' | hP' | ⟨kv', rfl⟩
  · exact eq_of_qpOf Pq hPq Q hP hP' _ hcP hcP'
  · exact ((hQ P (qpOf_sub D Pq Q hP)).1 ((hpD P).2 (same ((hpD P').1 (qpOf_sub D Pq _ hP'))))).elim
  · exact ((hQ P (qpOf_sub D Pq Q hP)).2 kv'.1 (same (hG kv'))).elim
  · exact ((hQ P' (qpOf_sub D Pq Q hP')).1 ((hpD P').2 (same' ((hpD P).1 (qpOf_sub D Pq _ hP))))).elim
  · exact eq_of_qpOf Pq hPq _ hP hP' _ hcP hcP'
  · exact (not_mem_two P hpp (D.host.g_prime kv'.1) (hne kv'.1) ((hpD P).1 (qpOf_sub D Pq _ hP))
      (same (hG kv'))).elim
  · exact ((hQ P' (qpOf_sub D Pq Q hP')).2 kv.1 (same' (hG kv))).elim
  · exact (not_mem_two P' hpp (D.host.g_prime kv.1) (hne kv.1) ((hpD P').1 (qpOf_sub D Pq _ hP'))
      (same' (hG kv))).elim
  · obtain ⟨k, v⟩ := kv
    obtain ⟨k', v'⟩ := kv'
    by_cases hk : k = k'
    · subst hk
      rcases GlobalTheory.SplitConjPlace.eq_or_eq_conjPlE (NX.pG D ⟨k, v⟩) (NX.pG D ⟨k, v'⟩) hc.symm with e | e
      · exact e.symm
      · have hc2 := isConjPl_conjPlE (NX.pG D ⟨k, v⟩)
        rw [← e] at hc2
        exact (D.naut.plGw_nconj k v v' hc2).elim
    · exact (not_mem_two _ (D.host.g_prime k) (D.host.g_prime k') (g_ne_g hk) (hG ⟨k, v⟩)
        (same (hG ⟨k', v'⟩))).elim

end GlobalTheory.LevelPlaceSep
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlacesAvoidAuxiliaryStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_places_avoid_auxiliary : ∀ (D : D7) (T : TwR D.LL0 D.nd) (i : T.Tw) (Q : Finset (PlE D.host))
    (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (sp : PlE D.host → SplitPlace D.host.E),
    (∀ v, NG.OverPl (Pq v) v) → (∀ P ∈ Q, IsSplitPl D.host P) →
    (∀ P ∈ Q, P ∉ T.pD i ∧ ∀ k' : Fin 2, P ∉ placesOver D.host.E (D.host.g k')) → (∀ P ∈ T.pD i, IsSplitPl D.host P) →
    (∀ P, (P ∈ qpOf D Pq Q ∨ P ∈ qpOf D Pq (T.pD i) ∨ ∃ kv, P = NX.pG D kv) → (sp P).w = P) →
    (∀ P P', (P ∈ qpOf D Pq Q ∨ P ∈ qpOf D Pq (T.pD i) ∨ ∃ kv, P = NX.pG D kv) →
      (P' ∈ qpOf D Pq Q ∨ P' ∈ qpOf D Pq (T.pD i) ∨ ∃ kv, P' = NX.pG D kv) → (sp P).v = (sp P').v → P = P') ∧
    (∀ P ∈ qpOf D Pq Q, P ∉ qpOf D Pq (T.pD i)) ∧ (∀ kv, NX.pG D kv ∉ qpOf D Pq Q ∧ NX.pG D kv ∉ qpOf D Pq (T.pD i)) ∧
    ∀ kv kv', NX.pG D kv = NX.pG D kv' → kv = kv' := by
  first | exact @GlobalTheory.LevelPlaceSep.levelPlaces_sep | exact GlobalTheory.LevelPlaceSep.levelPlaces_sep | (intros; apply GlobalTheory.LevelPlaceSep.levelPlaces_sep <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSplitPlaceOfIsSplitPlaceCmField
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSplitPlaceOfIsSplitPlaceCmField
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

namespace GlobalTheory.HeightCounting.SplitPlaceOf

theorem exists_splitPlace : ∀ (D : D7) (P : PlE D.host), IsSplitPl D.host P →
    ∃ s : SplitPlace D.host.E, s.w = P :=
  fun D P hP => GlobalTheory.RowUnitProof.exists_splitPlace_eq D P hP

end GlobalTheory.HeightCounting.SplitPlaceOf
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSplitPlaceOfIsSplitPlaceCmFieldStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_splitPlace_of_isSplitPlace_cmField : ∀ (D : D7) (P : PlE D.host), IsSplitPl D.host P → ∃ s : SplitPlace D.host.E, s.w = P := by
  first | exact @GlobalTheory.HeightCounting.SplitPlaceOf.exists_splitPlace | exact GlobalTheory.HeightCounting.SplitPlaceOf.exists_splitPlace | (intros; apply GlobalTheory.HeightCounting.SplitPlaceOf.exists_splitPlace <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChosenHalfSplitPlacesMeetsConjugatePairOnce
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChosenHalfSplitPlacesMeetsConjugatePairOnce
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.ChosenHalf

theorem isConjPl_unique (D : D7) {P w w' : PlE D.host} (h : IsConjPl D.host P w) (h' : IsConjPl D.host P w') :
    w = w' := by
  apply HeightOneSpectrum.ext
  ext y
  obtain ⟨x, hx⟩ := (RingOfIntegers.mapRingEquiv D.host.conj.toRingEquiv).surjective y
  have hy : (y : D.host.E) = D.host.conj (x : D.host.E) := by
    rw [← hx]; rfl
  rw [← h x y hy, ← h' x y hy]

theorem not_isConjPl_self (D : D7) {P : PlE D.host} (hs : IsSplitPl D.host P) : ¬ IsConjPl D.host P P := by
  intro hc
  obtain ⟨x, hx, hy⟩ := hs
  have hyx : ((RingOfIntegers.mapRingEquiv D.host.conj.toRingEquiv x : 𝓞 D.host.E) : D.host.E) =
      D.host.conj (x : D.host.E) := rfl
  exact hy _ hyx ((hc x _ hyx).1 hx)

theorem overPl_unique (D : D7) {P : PlE D.host} {v v' : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E))}
    (h : NG.OverPl P v) (h' : NG.OverPl P v') : v = v' :=
  HeightOneSpectrum.ext (h.symm.trans h')

theorem qpOf_half : ∀ (D : D7) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host), (∀ v, NG.OverPl (Pq v) v) →
    ∀ S : Finset (PlE D.host), (∀ P ∈ S, IsSplitPl D.host P) →
    (∀ P ∈ S, ∃ P' ∈ qpOf D Pq S, P' = P ∨ IsConjPl D.host P P') ∧ ∀ P ∈ qpOf D Pq S, ∀ P' ∈ qpOf D Pq S, ¬ IsConjPl D.host P P' := by
  classical
  intro D Pq hPq S hS
  have pair := GlobalTheory.T.comap_realSubfield_eq_iff_eq_or_isConjPlace D
  have memq : ∀ P, P ∈ qpOf D Pq S ↔ P ∈ S ∧ ∀ v, NG.OverPl P v → P = Pq v ∨ Pq v ∉ S := by
    intro P
    unfold qpOf
    rw [Finset.mem_filter]
  refine ⟨fun P hP => ?_, fun P hP P' hP' hc => ?_⟩
  · by_cases hq : P ∈ qpOf D Pq S
    · exact ⟨P, hq, Or.inl rfl⟩
    · have hn : ¬ ∀ v, NG.OverPl P v → P = Pq v ∨ Pq v ∉ S := fun h => hq ((memq P).2 ⟨hP, h⟩)
      push_neg at hn
      obtain ⟨v, hv, -, hin⟩ := hn
      refine ⟨Pq v, (memq _).2 ⟨hin, fun v' hv' => Or.inl ?_⟩, ?_⟩
      · rw [overPl_unique D (hPq v) hv']
      · rcases (pair P (Pq v)).1 (hv.trans (hPq v).symm) with h | h
        · exact Or.inl h.symm
        · exact Or.inr h
  · have hPS := ((memq P).1 hP).1
    have hP'S := ((memq P').1 hP').1
    let v := HeightOneSpectrum.under (𝓞 (maximalRealSubfield D.host.E)) P
    have hv : NG.OverPl P v := rfl
    have hv' : NG.OverPl P' v := ((pair P P').2 (Or.inr hc)).symm.trans hv
    have hqS : Pq v ∈ S := by
      rcases (pair P (Pq v)).1 (hv.trans (hPq v).symm) with h | h
      · rw [← h]; exact hPS
      · rw [← isConjPl_unique D hc h]; exact hP'S
    have e1 := qpOf_eq D Pq S hP hv hqS
    have e2 := qpOf_eq D Pq S hP' hv' hqS
    have e : P' = P := e2.trans e1.symm
    rw [e] at hc
    exact not_isConjPl_self D (hS P hPS) hc

end GlobalTheory.ChosenHalf
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChosenHalfSplitPlacesMeetsConjugatePairOnceStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chosenHalf_splitPlaces_meets_conjugatePair_once : ∀ (D : D7) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host), (∀ v, NG.OverPl (Pq v) v) →
    ∀ S : Finset (PlE D.host), (∀ P ∈ S, IsSplitPl D.host P) →
    (∀ P ∈ S, ∃ P' ∈ qpOf D Pq S, P' = P ∨ IsConjPl D.host P P') ∧ ∀ P ∈ qpOf D Pq S, ∀ P' ∈ qpOf D Pq S, ¬ IsConjPl D.host P P' := by
  first | exact @GlobalTheory.ChosenHalf.qpOf_half | exact GlobalTheory.ChosenHalf.qpOf_half | (intros; apply GlobalTheory.ChosenHalf.qpOf_half <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FifteenNotMemAndDeltaInertiaOrderDividesFifteenP
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FifteenNotMemAndDeltaInertiaOrderDividesFifteenP
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

namespace GlobalTheory.Member.DeltaTame

theorem delta_tame_and_15 : ∀ (D : D7) (T : TwR D.LL0 D.nd) (i : T.Tw) (P : PlE D.host), P ∈ T.pD i →
    ((15 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal ∧ ∀ A : ValuationSubring D.nd.Om, IsPlaceOver A P → ∀ σ ∈ Ine (F := D.host.E) A,
      ∃ N : ℕ, T.delta i σ ^ (15 ^ N) = 1 := by
  intro D T i P hP
  refine ⟨?_, ?_⟩
  · intro h15
    have hmem : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal := Ideal.absNorm_mem _
    have hmod := T.delta_tame i P hP
    have hdecomp : Ideal.absNorm P.asIdeal = 15 * (Ideal.absNorm P.asIdeal / 15) + 1 := by
      have := Nat.div_add_mod (Ideal.absNorm P.asIdeal) 15
      omega
    rw [hdecomp] at hmem
    push_cast at hmem h15
    have h1 : (1 : 𝓞 D.host.E) ∈ P.asIdeal := by
      have hm2 : (15 : 𝓞 D.host.E) * ((Ideal.absNorm P.asIdeal / 15 : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal :=
        P.asIdeal.mul_mem_right _ h15
      have := P.asIdeal.sub_mem hmem hm2
      simpa using this
    exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1)
  · intro A hA σ hσ
    have h15 := T.delta_15 i P hP A hA
    have hfin : Finite ((Ine (F := D.host.E) A).map (T.delta i)) :=
      Nat.finite_of_card_ne_zero (by rw [h15]; norm_num)
    have hpow := pow_card_eq_one' (G := (Ine (F := D.host.E) A).map (T.delta i))
      (x := ⟨T.delta i σ, Subgroup.mem_map_of_mem _ hσ⟩)
    rw [h15] at hpow
    refine ⟨1, ?_⟩
    have := congrArg Subtype.val hpow
    simpa using this

end GlobalTheory.Member.DeltaTame
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FifteenNotMemAndDeltaInertiaOrderDividesFifteenPStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fifteen_not_mem_and_delta_inertia_order_divides_fifteen_pow : ∀ (D : D7) (T : TwR D.LL0 D.nd) (i : T.Tw) (P : PlE D.host), P ∈ T.pD i →
    ((15 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal ∧ ∀ A : ValuationSubring D.nd.Om, IsPlaceOver A P → ∀ σ ∈ Ine (F := D.host.E) A,
      ∃ N : ℕ, T.delta i σ ^ (15 ^ N) = 1 := by
  first | exact @GlobalTheory.Member.DeltaTame.delta_tame_and_15 | exact GlobalTheory.Member.DeltaTame.delta_tame_and_15 | (intros; apply GlobalTheory.Member.DeltaTame.delta_tame_and_15 <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AuxiliaryPrimePlacesNonempty
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AuxiliaryPrimePlacesNonempty
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.PdPlace

theorem exists_place_over_prime (E : Type) [Field E] [NumberField E] (p : ℕ) (hp : p.Prime) :
    (Formalism.BasicNotions.placesOver E p).Nonempty := by
  have hnu : ¬ IsUnit ((p : ℕ) : 𝓞 E) := by
    intro hu
    have h1 := hu.map (Algebra.norm ℤ : 𝓞 E →* ℤ)
    rw [show ((p : ℕ) : 𝓞 E) = algebraMap ℤ (𝓞 E) (p : ℤ) by simp, Algebra.norm_algebraMap] at h1
    have h2 := Int.isUnit_iff_natAbs_eq.1 h1
    have h3 : 0 < Module.finrank ℤ (𝓞 E) := Module.finrank_pos
    rw [Int.natAbs_pow, Int.natAbs_natCast] at h2
    rcases Nat.pow_eq_one.1 h2 with h | h
    · exact hp.one_lt.ne' h
    · exact h3.ne' h
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal (Ideal.span {((p : ℕ) : 𝓞 E)})
    (by rwa [Ne, Ideal.span_singleton_eq_top])
  have hmem : ((p : ℕ) : 𝓞 E) ∈ M := hle (Ideal.subset_span rfl)
  refine ⟨⟨M, hM.isPrime, fun h => ?_⟩, hmem⟩
  rw [h, Ideal.mem_bot] at hmem
  exact hp.ne_zero (by exact_mod_cast hmem)

theorem pD_nonempty : ∀ (D : D7) (T : TwR D.LL0 D.nd) (i : T.Tw), (T.pD i).Nonempty := by
  intro D T i
  have hp : (if T.l i = D.host.pde then D.host.pde' else D.host.pde).Prime := by
    split_ifs
    exacts [D.host.pde'_prime, D.host.pde_prime]
  obtain ⟨v, hv⟩ := exists_place_over_prime D.host.E _ hp
  rw [← T.pD_eq i] at hv
  exact ⟨v, hv⟩

end GlobalTheory.PdPlace
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AuxiliaryPrimePlacesNonemptyStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.auxiliaryPrimePlaces_nonempty : ∀ (D : D7) (T : TwR D.LL0 D.nd) (i : T.Tw), (T.pD i).Nonempty := by
  first | exact @GlobalTheory.PdPlace.pD_nonempty | exact GlobalTheory.PdPlace.pD_nonempty | (intros; apply GlobalTheory.PdPlace.pD_nonempty <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsResidueHomZmodAtTypePlace
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsResidueHomZmodAtTypePlace
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.TypePlaceResidue

theorem residueHom_zmod : ∀ (D : D7) (kv : Σ k : Fin 2, D.nd.PlG k) (s : SplitPlace D.host.E), s.w = NX.pG D kv →
    Nonempty (s.v.adicCompletionIntegers (maximalRealSubfield D.host.E) →+* ZMod (D.host.g kv.1)) := by
  intro D kv s hs
  have hp := D.host.g_prime kv.1
  haveI : Fact (D.host.g kv.1).Prime := ⟨hp⟩
  have hN := GlobalTheory.TameLabels.normV_eq_of_split hp (D.nd.g_split kv.1) (D.naut.plGw_over kv.1 kv.2)
  have hc : Nat.card (IsLocalRing.ResidueField (s.v.adicCompletionIntegers (maximalRealSubfield D.host.E))) =
      D.host.g kv.1 := by
    rw [ReciprocityTheory.Bridge.ResidueFieldCardinality.card_residue, ← s.card_quot, hs]
    rw [← hN]
    rfl
  haveI : Finite (IsLocalRing.ResidueField (s.v.adicCompletionIntegers (maximalRealSubfield D.host.E))) :=
    Nat.finite_of_card_ne_zero (by rw [hc]; exact hp.ne_zero)
  letI := Fintype.ofFinite (IsLocalRing.ResidueField (s.v.adicCompletionIntegers (maximalRealSubfield D.host.E)))
  have hcF : Fintype.card (IsLocalRing.ResidueField (s.v.adicCompletionIntegers (maximalRealSubfield D.host.E))) =
      D.host.g kv.1 := by rw [Fintype.card_eq_nat_card]; exact hc
  haveI := charP_of_card_eq_prime hcF
  exact ⟨(ZMod.ringEquiv _ hcF).symm.toRingHom.comp (IsLocalRing.residue _)⟩

end GlobalTheory.TypePlaceResidue
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsResidueHomZmodAtTypePlaceStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_residueHom_zmod_at_typePlace : ∀ (D : D7) (kv : Σ k : Fin 2, D.nd.PlG k) (s : SplitPlace D.host.E), s.w = NX.pG D kv →
    Nonempty (s.v.adicCompletionIntegers (maximalRealSubfield D.host.E) →+* ZMod (D.host.g kv.1)) := by
  first | exact @GlobalTheory.TypePlaceResidue.residueHom_zmod | exact GlobalTheory.TypePlaceResidue.residueHom_zmod | (intros; apply GlobalTheory.TypePlaceResidue.residueHom_zmod <;> assumption)
end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.LevForms

theorem typeSpF_finiteDimensional : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (K : Type) [Field K] {W : Type} [AddCommGroup W] [Module K W]
    [FiniteDimensional K W] (ρ : Representation K (GQ L n) W) (J : Subgroup (GAf L n)) (χ : J →* Kˣ),
    (∃ N : ℕ, 0 < N ∧ ∀ κ, NG.Cong L n N κ → ∃ h : κ ∈ J, χ ⟨κ, h⟩ = 1) →
    FiniteDimensional K ↥(NX.TypeSpF L n K ρ J χ) := by
  intro L _ _ _ n K _ W _ _ _ ρ J χ hJ
  classical
  obtain ⟨N, hN, hNJ⟩ := hJ
  obtain ⟨T, hT⟩ := GlobalTheory.T.finite_doubleCosets_definiteUnitary_maximalLevel L n
  obtain ⟨Jc, hJc⟩ := GlobalTheory.AlgFormsFin.exists_cover L n hN
  let Φ : ↥(NX.TypeSpF L n K ρ J χ) →ₗ[K] (↥(T ×ˢ Jc) → W) :=
    { toFun := fun f p => (f : GAf L n → W) (p.1.1 * p.1.2)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine Module.Finite.of_injective Φ ((injective_iff_map_eq_zero Φ).2 fun f hf => ?_)
  refine Subtype.ext (funext fun g => ?_)
  obtain ⟨γ, t, u, ht, hu, rfl⟩ := hT g
  obtain ⟨j, hj, κ, hκ, rfl⟩ := hJc u hu
  have h0 : (f : GAf L n → W) (t * j) = 0 :=
    congrFun hf ⟨(t, j), Finset.mem_product.2 ⟨ht, hj⟩⟩
  obtain ⟨hκJ, hκ1⟩ := hNJ κ hκ
  have e : (γ : GAf L n) * t * (j * κ) = ((γ : GAf L n) * (t * j)) * κ := by simp only [mul_assoc]
  show (f : GAf L n → W) _ = 0
  rw [e, f.2.2 ⟨κ, hκJ⟩, hκ1, f.2.1 γ, h0, map_zero, Units.val_one, one_smul]

end GlobalTheory.LevForms
