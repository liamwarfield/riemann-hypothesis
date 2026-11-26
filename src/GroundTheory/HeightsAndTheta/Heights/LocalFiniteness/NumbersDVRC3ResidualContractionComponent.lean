module

public import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.HilbertSamuelGrowthOffHypersurfacePolynomial
public import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.IsolatedPointsCount
public import GroundTheory.GlobalFields.TateThesis.PrimeZetaPole
public import GroundTheory.GlobalFields.ComplexMultiplication.AlgebraicityDescent
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBlowUpLocRingFracCut
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PHomLocRingDimLe

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ResidualNewVarMem
section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.RingKrullDimQuotientLeComapAddOne
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

theorem ringKrullDim_quotient_le_comap_add_one {K : Type} [Fintype K] {ι : K → Type}
    [∀ k, Fintype (ι k)] {J : Type} {R : Type*} [CommRing R] [IsNoetherianRing R]
    (G' : Ideal (MRing (extIdx ι J) R)) [G'.IsPrime] (j₀ : J)
    (hY : ∀ j, j ≠ j₀ → (newVar j : MRing (extIdx ι J) R) ∈ G') :
    ringKrullDim (MRing (extIdx ι J) R ⧸ G') ≤
      ringKrullDim (MRing ι R ⧸ G'.comap (liftForm (J := J) (ι := ι) (R := R))) + 1 := by
  set G := G'.comap (liftForm (J := J) (ι := ι) (R := R)) with hGdef
  let φ : (MRing ι R ⧸ G) →+* (MRing (extIdx ι J) R ⧸ G') :=
    Ideal.quotientMap G' (liftForm (J := J) (ι := ι) (R := R)).toRingHom le_rfl
  let ψ : Polynomial (MRing ι R ⧸ G) →+* (MRing (extIdx ι J) R ⧸ G') :=
    Polynomial.eval₂RingHom φ (Ideal.Quotient.mk G' (newVar j₀))
  have hψ : Function.Surjective ψ := by
    intro y
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective y
    induction p using MvPolynomial.induction_on with
    | C a =>
      refine ⟨Polynomial.C (Ideal.Quotient.mk G (C a)), ?_⟩
      simp [ψ, φ, Ideal.quotientMap_mk, liftForm]
    | add p q hp hq =>
      obtain ⟨a, ha⟩ := hp
      obtain ⟨b, hb⟩ := hq
      exact ⟨a + b, by rw [ψ.map_add, ha, hb, (Ideal.Quotient.mk G').map_add]⟩
    | mul_X p v hp =>
      obtain ⟨a, ha⟩ := hp
      obtain ⟨o, i⟩ := v
      cases o with
      | none =>
        by_cases hi : i = j₀
        · subst hi
          refine ⟨a * Polynomial.X, ?_⟩
          rw [map_mul, ha, map_mul]
          congr 1
          simp [ψ, newVar]
        · refine ⟨0, ?_⟩
          rw [map_zero, eq_comm, Ideal.Quotient.eq_zero_iff_mem]
          exact G'.mul_mem_left _ (hY i hi)
      | some k =>
        refine ⟨a * Polynomial.C (Ideal.Quotient.mk G (X ⟨k, i⟩)), ?_⟩
        rw [map_mul, ha, map_mul]
        congr 1
        simp [ψ, φ, Ideal.quotientMap_mk, liftForm, rename_X]
  calc ringKrullDim (MRing (extIdx ι J) R ⧸ G')
      ≤ ringKrullDim (Polynomial (MRing ι R ⧸ G)) := ringKrullDim_le_of_surjective ψ hψ
    _ = ringKrullDim (MRing ι R ⧸ G) + 1 := Polynomial.ringKrullDim_of_isNoetherianRing

theorem mem_minimalPrimes_of_ringKrullDim {A : Type*} [CommRing A] (P G : Ideal A) [P.IsPrime]
    [G.IsPrime] (s : A) (hsP : s ∉ P) (N : ℕ) (hP : ringKrullDim (A ⧸ P) = (N : WithBot ℕ∞))
    (hle : P ⊔ Ideal.span {s} ≤ G) (hG : (N : WithBot ℕ∞) ≤ ringKrullDim (A ⧸ G) + 1) :
    G ∈ (P ⊔ Ideal.span {s}).minimalPrimes := by
  refine ⟨⟨inferInstance, hle⟩, fun Q hQ hQG => ?_⟩
  have : Q.IsPrime := hQ.1
  by_contra hGQ
  have hsQ : s ∈ Q := hQ.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self s))
  have hPQ : P < Q := lt_of_le_of_ne (le_sup_left.trans hQ.2) fun h => hsP (h ▸ hsQ)
  have h1 := DimStrictDrop.proof A Q G (lt_of_le_not_ge hQG hGQ)
  have h2 := DimStrictDrop.proof A P Q hPQ
  have h3 : (N : WithBot ℕ∞) + 1 ≤ (N : WithBot ℕ∞) :=
    calc (N : WithBot ℕ∞) + 1 ≤ ringKrullDim (A ⧸ G) + 1 + 1 := by gcongr
      _ ≤ ringKrullDim (A ⧸ Q) + 1 := by gcongr
      _ ≤ N := hP ▸ h2
  have h4 : ((N + 1 : ℕ) : WithBot ℕ∞) ≤ (N : WithBot ℕ∞) := by exact_mod_cast h3
  have h5 : N + 1 ≤ N := by exact_mod_cast h4
  omega

end GroundTheory.Heights₂.Heights.NumbersDVR
end

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

theorem residual_newVar_mem {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {R : Type u}
    [CommRing R] [IsNoetherianRing R] {P : Ideal (MRing ι R)} [P.IsPrime] {s g f m : MRing ι R}
    (e : K → ℕ) (hfP : f ∉ P) (hmP : m ∉ P) {G' : Ideal (MRing (extIdx ι (BlowUpIdx ι)) R)}
    (hP'G' : blowUpOf P (blowUpGens s g f m e) ≤ G')
    (hres : 0 < ratDiv (blowUpOf P (blowUpGens s g f m e)) (newVar (some none)) (liftForm m) G') :
    ∀ j, j ≠ none → (newVar j : MRing (extIdx ι (BlowUpIdx ι)) R) ∈ G' := by
  set P' := blowUpOf P (blowUpGens s g f m e) with hP'def
  have hP'prime : P'.IsPrime := RingHom.ker_isPrime _
  have hmul := DivCycleMul.proof R (Option K) (extIdx ι (BlowUpIdx ι)) P'
  have hlm : liftForm (J := BlowUpIdx ι) m ∉ P' := fun h => by
    rw [hP'def, blowUpOf, RingHom.mem_ker, aeval_blowUpSubst_liftForm, Polynomial.C_eq_zero,
      Ideal.Quotient.eq_zero_iff_mem] at h
    exact hmP h
  have hY₁P' : (newVar (some none) : MRing (extIdx ι (BlowUpIdx ι)) R) ∉ P' := fun h => by
    rw [hP'def, blowUpOf, RingHom.mem_ker] at h
    simp only [newVar, aeval_X, blowUpSubst, blowUpGens, mul_eq_zero, Polynomial.X_ne_zero, or_false,
      Polynomial.C_eq_zero, Ideal.Quotient.eq_zero_iff_mem] at h
    exact (Ideal.IsPrime.mem_or_mem inferInstance h).elim hfP hmP
  have hnonneg : ∀ x W, 0 ≤ divCycle P' x W := fun x W => by
    unfold divCycle; split_ifs <;> simp
  have hY₁G' : (newVar (some none) : MRing (extIdx ι (BlowUpIdx ι)) R) ∈ G' := by
    apply form_mem_of_divCycle_ne_zero (P := P')
    have := hnonneg (liftForm m) G'
    unfold ratDiv at hres; omega
  rintro (_ | _ | i) hj
  · exact absurd rfl hj
  · exact hY₁G'
  by_contra hYi
  have hrel : liftForm (powMonomial e i) * newVar (some none) -
      liftForm m * newVar (some (some i)) ∈ P' := by
    rw [hP'def, blowUpOf, RingHom.mem_ker]
    simp only [map_sub, map_mul, aeval_blowUpSubst_liftForm, newVar, aeval_X, blowUpSubst, blowUpGens]
    ring
  have hYiP' : (newVar (some (some i)) : MRing (extIdx ι (BlowUpIdx ι)) R) ∉ P' := fun h => hYi (hP'G' h)
  by_cases hp : liftForm (J := BlowUpIdx ι) (powMonomial e i : MRing ι R) ∈ P'
  · have h := P'.sub_mem (P'.mul_mem_right (newVar (some none)) hp) hrel
    rw [sub_sub_cancel] at h
    exact (hP'prime.mem_or_mem h).elim hlm hYiP'
  · have h1 := congrFun (divCycle_congr_of_sub_mem hrel) G'
    rw [hmul _ _ hP'prime hp hY₁P', hmul _ _ hP'prime hlm hYiP'] at h1
    simp only [Pi.add_apply] at h1
    have h2 : divCycle P' (newVar (some (some i))) G' = 0 := by
      by_contra h; exact hYi (form_mem_of_divCycle_ne_zero h)
    have h3 := hnonneg (liftForm (powMonomial e i)) G'
    unfold ratDiv at hres; omega

theorem ResidualContractionComponent.proof (hpieces : BlowUpDecomposition.Statement.{u}) :
    ResidualContractionComponent.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP b f g hD c s hs hsP hsH e he m hm hmP hmH G' hϖG' hsG' hresG'
  obtain ⟨hP', hsc', hsP', -⟩ := hpieces O ϖ hϖ K ι P d hP b f g hD c s hs hsP hsH e he m hm hmP hmH
  have : P.IsPrime := hP.multiProj.isPrime
  have hG'supp : G' ∈ (blowUpOf P (blowUpGens s g f m e) ⊔ Ideal.span {liftForm s}).minimalPrimes ∧
      IsRelevant G' := by
    unfold divCycle at hsG'
    split_ifs at hsG' with hG'
    · exact hG'
    · exact (lt_irrefl _ hsG').elim
  have : G'.IsPrime := hG'supp.1.1.1
  have hP'G' : blowUpOf P (blowUpGens s g f m e) ≤ G' := le_sup_left.trans hG'supp.1.1.2
  have hY := residual_newVar_mem e hD.1.num_not_mem hmP hP'G' hresG'
  have hdim' := ComponentDim.proof O ϖ hϖ (Option K) (extIdx ι (BlowUpIdx ι)) _ (d + 1) hP'
    (liftMDeg c) (liftForm s) hsc' hsP' G' hsG'.ne' hϖG'
  have hdim := ringKrullDim_quotient_le_comap_add_one G' none hY
  refine mem_minimalPrimes_of_ringKrullDim P _ s hsP (d + 1 + 1 + Fintype.card K) hP.dim ?_ ?_
  · refine sup_le (fun p hp => hP'G' ?_) ?_
    · rw [blowUpOf, RingHom.mem_ker, aeval_blowUpSubst_liftForm,
        Ideal.Quotient.eq_zero_iff_mem.mpr hp, map_zero]
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      exact hG'supp.1.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  · rw [Fintype.card_option, show d + 1 + (Fintype.card K + 1) = d + 1 + 1 + Fintype.card K by omega]
      at hdim'
    exact hdim' ▸ hdim

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.RingKrullDimLeOfIsAlgebraicAdjoinSingleton
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

noncomputable section

section Helpers

theorem ringKrullDim_le_of_isAlgebraic_adjoin_singleton {A B : Type u} [CommRing A] [IsDomain A]
    [IsNoetherianRing A] [CommRing B] [IsDomain B] [Algebra A B] [Algebra.FiniteType A B]
    (hinj : Function.Injective (algebraMap A B)) (y : B)
    [Algebra.IsAlgebraic (Algebra.adjoin A ({y} : Set B)) B] (N : ℕ)
    (hA : ringKrullDim A < (N : WithBot ℕ∞)) : ringKrullDim B ≤ (N : WithBot ℕ∞) := by
  rw [ringKrullDim_le_iff_height_le]
  intro 𝔓 h𝔓
  have key := DimensionInequality.full A B hinj 𝔓
  have htd : Algebra.trdeg A B ≤ 1 := by
    simpa using Algebra.IsAlgebraic.trdeg_le_cardinalMk A ({y} : Set B)
  have hp : (𝔓.under A).height + 1 ≤ (N : ℕ∞) := by
    have h1 := Ideal.height_le_ringKrullDim_of_ne_top (Ideal.IsPrime.ne_top (inferInstance :
      (𝔓.under A).IsPrime))
    have h2 : ((𝔓.under A).height : WithBot ℕ∞) < (N : WithBot ℕ∞) := h1.trans_lt hA
    have h3 : (𝔓.under A).height < (N : ℕ∞) := by exact_mod_cast h2
    exact Order.add_one_le_of_lt h3
  have hc : Cardinal.ofENat 𝔓.height ≤ Cardinal.ofENat (N : ℕ∞) := by
    calc Cardinal.ofENat 𝔓.height
        ≤ Cardinal.ofENat 𝔓.height + Algebra.trdeg (A ⧸ 𝔓.under A) (B ⧸ 𝔓) := le_self_add
      _ ≤ Cardinal.ofENat (𝔓.under A).height + Algebra.trdeg A B := key
      _ ≤ Cardinal.ofENat (𝔓.under A).height + 1 := by gcongr
      _ = Cardinal.ofENat ((𝔓.under A).height + 1) := by simp
      _ ≤ Cardinal.ofENat (N : ℕ∞) := Cardinal.ofENat_le_ofENat.mpr hp
  exact_mod_cast Cardinal.ofENat_le_ofENat.mp hc

private theorem lt_natCast_of_add_one_le_withBotENat {x : WithBot ℕ∞} {n : ℕ} (h : x + 1 ≤ (n : WithBot ℕ∞)) :
    x < (n : WithBot ℕ∞) := by
  induction x using WithBot.recBotCoe with
  | bot => exact WithBot.bot_lt_coe _
  | coe a =>
    induction a using ENat.recTopCoe with
    | top => exact absurd h (by norm_cast)
    | coe a =>
      norm_cast at h ⊢

end Helpers

section Proof

theorem ExceptionalContraction.proof (h₁ : BlowUpDecomposition.Statement.{u}) :
    ExceptionalContraction.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP b f g hD c s hs hsP hH e hce m hm hmP hmH G' hϖG' hY₀ hE
  obtain ⟨hQm, -, -, hY₀Q, hD₁, -, -, -⟩ :=
    h₁ O ϖ hϖ K ι P d hP b f g hD c s hs hsP hH e hce m hm hmP hmH
  set Q := blowUpOf P (blowUpGens s g f m e) with hQdef
  set G := G'.comap (liftForm (J := BlowUpIdx ι)) with hGdef
  have hPp : P.IsPrime := hP.multiProj.isPrime
  have hQp : Q.IsPrime := hQm.multiProj.isPrime
  obtain ⟨hG'p, hQG', hG'rel⟩ := le_and_isRelevant_of_divCycle_ne_zero hY₀.ne'
  obtain ⟨hGp, hPG, hGrel, -⟩ := comap_liftForm_facts hG'p hQG' hG'rel

  have hlift : ∀ {p : MRing ι O}, p ∉ P → liftForm (J := BlowUpIdx ι) p ∉ Q :=
    fun hp => liftForm_not_mem_blowUpOf hp
  have hfP : f ∉ P := hD.1.num_not_mem
  have hgP : g ∉ P := hD.1.den_not_mem
  have hY₁Q : (newVar (some none) : MRing (extIdx ι (BlowUpIdx ι)) O) ∉ Q := hD₁.1.num_not_mem
  have hmul := DivCycleMul.proof O (Option K) (extIdx ι (BlowUpIdx ι)) Q
  have hnm : ∀ {x y}, x ∉ Q → y ∉ Q → x * y ∉ Q := fun hx hy h => (hQp.mem_or_mem h).elim hx hy
  have e1 := congrFun (divCycle_congr_of_sub_mem (blowUp_relation P s g f m e)) G'
  rw [map_mul, hmul _ _ hQp (hnm (hlift hsP) (hlift hgP)) hY₁Q, hmul _ _ hQp (hlift hsP) (hlift hgP),
    hmul _ _ hQp (hlift (fun h => (hPp.mem_or_mem h).elim hfP hmP)) hY₀Q] at e1
  simp only [Pi.add_apply] at e1
  have hE' := hE
  unfold ratDiv at hE'
  rw [hmul _ _ hQp (hlift hgP) hY₁Q] at hE'
  simp only [Pi.add_apply] at hE'
  have hspos : 0 < divCycle Q (liftForm s) G' := by linarith
  have hsG' : liftForm (J := BlowUpIdx ι) s ∈ G' := form_mem_of_divCycle_ne_zero hspos.ne'
  have hsG : s ∈ G := hsG'

  have hY₀G' : (newVar none : MRing (extIdx ι (BlowUpIdx ι)) O) ∈ G' :=
    form_mem_of_divCycle_ne_zero hY₀.ne'
  obtain ⟨i, hi⟩ := powMonomial_not_mem hGp hGrel e
  have := hGp
  have := hG'p
  let φ : MRing ι O ⧸ G →+* MRing (extIdx ι (BlowUpIdx ι)) O ⧸ G' :=
    Ideal.quotientMap G' (liftForm (J := BlowUpIdx ι) : MRing ι O →ₐ[O] _).toRingHom le_rfl
  let _ : Algebra (MRing ι O ⧸ G) (MRing (extIdx ι (BlowUpIdx ι)) O ⧸ G') := φ.toAlgebra
  have hφ : ∀ p : MRing ι O, algebraMap (MRing ι O ⧸ G) (MRing (extIdx ι (BlowUpIdx ι)) O ⧸ G')
      (Ideal.Quotient.mk G p) = Ideal.Quotient.mk G' (liftForm p) := fun p => Ideal.quotientMap_mk
  have : IsScalarTower O (MRing ι O ⧸ G) (MRing (extIdx ι (BlowUpIdx ι)) O ⧸ G') := by
    refine IsScalarTower.of_algebraMap_eq (R := O) (S := MRing ι O ⧸ G)
      (A := MRing (extIdx ι (BlowUpIdx ι)) O ⧸ G') fun r => ?_
    change Ideal.Quotient.mk G' (algebraMap O (MRing (extIdx ι (BlowUpIdx ι)) O) r) =
      algebraMap (MRing ι O ⧸ G) _ (Ideal.Quotient.mk G (algebraMap O (MRing ι O) r))
    rw [hφ, MvPolynomial.algebraMap_eq, MvPolynomial.algebraMap_eq, liftForm_C]
  have hinj : Function.Injective (algebraMap (MRing ι O ⧸ G) (MRing (extIdx ι (BlowUpIdx ι)) O ⧸ G')) :=
    Ideal.quotientMap_injective
  have : Algebra.FiniteType O (MRing (extIdx ι (BlowUpIdx ι)) O ⧸ G') :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ O G') (Ideal.Quotient.mkₐ_surjective O G')
  have : Algebra.FiniteType (MRing ι O ⧸ G) (MRing (extIdx ι (BlowUpIdx ι)) O ⧸ G') :=
    Algebra.FiniteType.of_restrictScalars_finiteType O _ _
  set y : MRing (extIdx ι (BlowUpIdx ι)) O ⧸ G' := Ideal.Quotient.mk G' (newVar (some (some i))) with hy
  set Cy := Algebra.adjoin (MRing ι O ⧸ G) ({y} : Set (MRing (extIdx ι (BlowUpIdx ι)) O ⧸ G'))
  let _ : CommRing Cy := inferInstance
  have hAalg : ∀ a : MRing ι O ⧸ G, IsAlgebraic Cy
      (algebraMap (MRing ι O ⧸ G) (MRing (extIdx ι (BlowUpIdx ι)) O ⧸ G') a) := fun a =>
    isAlgebraic_algebraMap (⟨_, Subalgebra.algebraMap_mem Cy a⟩ : Cy)
  have hpi : Ideal.Quotient.mk G' (liftForm (J := BlowUpIdx ι) (powMonomial e i)) ≠ 0 := by
    rw [Ne, Ideal.Quotient.eq_zero_iff_mem]
    exact hi
  have hX : ∀ v, IsAlgebraic Cy (Ideal.Quotient.mk G' (X v : MRing (extIdx ι (BlowUpIdx ι)) O)) := by
    rintro ⟨_ | k, j⟩
    · rcases j with _ | j'
      · change IsAlgebraic Cy (Ideal.Quotient.mk G' (newVar none))
        rw [Ideal.Quotient.eq_zero_iff_mem.mpr hY₀G']
        exact isAlgebraic_zero
      · set c : MRing ι O := Option.elim j' m (fun i' => powMonomial e i') with hc
        have hrel : newVar (some j') * liftForm (powMonomial e i) - newVar (some (some i)) * liftForm c ∈ Q :=
          mem_blowUpOf_of_sub (by
            rcases j' with _ | i' <;> simp only [blowUpGens, hc, Option.elim] <;>
              convert P.zero_mem using 1 <;> ring)
        have hrel' := Ideal.Quotient.eq_zero_iff_mem.mpr (hQG' hrel)
        rw [map_sub, map_mul, map_mul] at hrel'
        let a' : Cy := ⟨_, Subalgebra.algebraMap_mem Cy (Ideal.Quotient.mk G (powMonomial e i))⟩
        let z' : Cy := ⟨y * algebraMap (MRing ι O ⧸ G) _ (Ideal.Quotient.mk G c),
          Cy.mul_mem (Algebra.subset_adjoin rfl) (Subalgebra.algebraMap_mem Cy _)⟩
        refine ⟨Polynomial.C a' * Polynomial.X - Polynomial.C z', fun h0 => hpi ?_, ?_⟩
        · have h1 := congrArg (fun p : Polynomial Cy => p.coeff 1) h0
          simp only [Polynomial.coeff_sub, Polynomial.coeff_C_mul_X, ite_true,
            Polynomial.coeff_C_of_ne_zero one_ne_zero, sub_zero, Polynomial.coeff_zero] at h1
          have h2 := congrArg Subtype.val h1
          simpa [a', hφ] using h2
        · simp only [map_sub, map_mul, Polynomial.aeval_C, Polynomial.aeval_X]
          change (algebraMap (MRing ι O ⧸ G) _ (Ideal.Quotient.mk G (powMonomial e i))) *
            Ideal.Quotient.mk G' (newVar (some j')) -
            y * algebraMap (MRing ι O ⧸ G) _ (Ideal.Quotient.mk G c) = 0
          rw [hφ, hφ, hy]
          linear_combination hrel'
    · rw [← liftForm_X (J := BlowUpIdx ι) (R := O) ⟨k, j⟩, ← hφ]
      exact hAalg _
  have : Algebra.IsAlgebraic Cy (MRing (extIdx ι (BlowUpIdx ι)) O ⧸ G') := ⟨fun x => by
    obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective x
    induction t using MvPolynomial.induction_on with
    | C r =>
      have : Ideal.Quotient.mk G' (C r : MRing (extIdx ι (BlowUpIdx ι)) O) =
          algebraMap (MRing ι O ⧸ G) _ (Ideal.Quotient.mk G (C r)) := by
        rw [hφ, liftForm_C]
      rw [this]
      exact hAalg _
    | add p q hp hq => rw [map_add (f := _)]; exact hp.add hq
    | mul_X p v hp => rw [map_mul]; exact hp.mul (hX v)⟩
  have hdimB := ComponentDim.proof O ϖ hϖ (Option K) (extIdx ι (BlowUpIdx ι)) Q (d + 1) hQm
    (Pi.single none 1) (newVar none) (isWeightedHomogeneous_X _ _ _) hY₀Q G' hY₀.ne' hϖG'
  have hdimA : ¬ ringKrullDim (MRing ι O ⧸ G) < ((d + 1 + Fintype.card K : ℕ) : WithBot ℕ∞) := by
    intro hlt
    have h := ringKrullDim_le_of_isAlgebraic_adjoin_singleton hinj y _ hlt
    rw [hdimB, Fintype.card_option] at h
    have h' : d + 1 + (Fintype.card K + 1) ≤ d + 1 + Fintype.card K := by exact_mod_cast h
    omega

  have hsum : ringKrullDim (MRing ι O ⧸ (P ⊔ Ideal.span {s})) <
      ((d + 1 + Fintype.card K + 1 : ℕ) : WithBot ℕ∞) := by
    have := hPp
    have h := ringKrullDim_succ_le_of_surjective
      (Ideal.Quotient.factor (le_sup_left : P ≤ P ⊔ Ideal.span {s})) (Ideal.Quotient.factor_surjective _)
      (r := Ideal.Quotient.mk P s)
      (mem_nonZeroDivisors_of_ne_zero (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]))
      (by rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]
          exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self s))
    rw [hP.dim] at h
    exact lt_natCast_of_add_one_le_withBotENat (by convert h using 2; omega)
  exact TopDimMinimal.proof DimStrictDrop.proof (MRing ι O) (P ⊔ Ideal.span {s}) G
    (d + 1 + Fintype.card K) (sup_le hPG ((Ideal.span_singleton_le_iff_mem _).mpr hsG)) hsum hdimA

end Proof

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PLocalCoeffRing
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

universe u

private theorem mem_minimalPrimes_of_locCycle_ne_zero {S : Type*} [CommRing S] {J W : Ideal S}
    (h : locCycle J W ≠ 0) : W ∈ J.minimalPrimes := by
  by_contra hc
  exact h (by unfold locCycle; rw [dite_eq_right hc])

theorem LocalCoeffRing.proof (h₁ : LocalQuotRing.Statement.{u}) (h₂ : LocalQuotPrimes.Statement.{u})
    (h₃ : LocCycleLocalQuot.Statement.{u}) (h₄ : LocalQuotColon.Statement.{u})
    (h₅ : LocalQuotFinsum.Statement.{u}) (h₆ : LocalCoeffLocal.Statement.{u}) :
    LocalCoeffRing.Statement.{u} := by
  intro R _ _ P U hP hU hPU hchain f g s u v hf hg hs hu huv hno
  have := hU
  obtain ⟨hdom, hloc, hunit, hker⟩ := h₁ R P U hP hPU
  have := hdom
  have := hloc
  obtain ⟨hup, hdown⟩ := h₂ R P U hPU
  have hmin := fun {J W : Ideal R} (h : locCycle J W ≠ 0) => mem_minimalPrimes_of_locCycle_ne_zero h
  have hmin' := fun {J W : Ideal (localQuot P U)} (h : locCycle J W ≠ 0) =>
    mem_minimalPrimes_of_locCycle_ne_zero h

  have hm : IsLocalRing.maximalIdeal (localQuot P U) = U.map (localQuotMap P U) := by
    ext y
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, hunit, not_not]
  have hUc : (U.map (localQuotMap P U)).comap (localQuotMap P U) = U := (hup U hU hPU le_rfl).2
  have hPbot : P.map (localQuotMap P U) = ⊥ :=
    (Ideal.map_eq_bot_iff_le_ker _).mpr fun y hy => RingHom.mem_ker.mpr ((hker y).2 hy)
  have hmapx : ∀ x : R, (P ⊔ Ideal.span {x}).map (localQuotMap P U) =
      Ideal.span {localQuotMap P U x} := by
    intro x
    rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton, hPbot, bot_sup_eq]

  have hchain' : ∀ Q₁ Q₂ : Ideal (localQuot P U), Q₁.IsPrime → Q₂.IsPrime → ⊥ < Q₁ → Q₁ < Q₂ →
      Q₂ < IsLocalRing.maximalIdeal (localQuot P U) → False := by
    intro Q₁ Q₂ hQ₁ hQ₂ h0 h12 h2m
    obtain ⟨hP1, -, he1⟩ := hdown Q₁ hQ₁
    obtain ⟨-, hU2, he2⟩ := hdown Q₂ hQ₂
    exact hchain _ _ (Ideal.comap_isPrime _ _) (Ideal.comap_isPrime _ _)
      (lt_of_le_of_ne hP1 fun h => h0.ne (by rw [← he1, ← h, hPbot]))
      (lt_of_le_of_ne (Ideal.comap_mono h12.le) fun h => h12.ne (by rw [← he1, ← he2, h]))
      (lt_of_le_of_ne hU2 fun h => h2m.ne (by rw [← he2, h, hm]))
  have hne : ∀ x : R, x ∉ P → localQuotMap P U x ≠ 0 := fun x hx h => hx ((hker x).1 h)
  have hloc' := h₆ (localQuot P U) hchain' (localQuotMap P U f) (localQuotMap P U g)
    (localQuotMap P U s) (localQuotMap P U u) (localQuotMap P U v) (hne f hf) (hne g hg) (hne s hs)
    ((hunit _).2 fun h => hu (hUc ▸ Ideal.mem_comap.mpr h))
    (by rw [← sub_eq_zero, ← map_mul, ← map_mul, ← map_sub]; exact (hker _).2 huv) ?_
  swap
  ·
    intro W hW
    have hWm := hmin' hW
    have := hWm.1.1
    obtain ⟨hPW, hWU, hWe⟩ := hdown W hWm.1.1
    have h := hno (W.comap (localQuotMap P U)) hWU
    rw [h₃ R P U _ _ le_sup_left inferInstance hPW hWU, h₃ R P U (P ⊔ Ideal.span {f}) _ le_sup_left
      inferInstance hPW hWU, h₃ R P U (P ⊔ Ideal.span {g}) _ le_sup_left inferInstance hPW hWU,
      hmapx, hmapx, hmapx, hWe] at h
    exact h hW
  rw [hm] at hloc'
  convert hloc' using 1
  ·
    apply h₅ R P U hPU
    · intro G hG
      have hGU : G ≤ U := le_sup_left.trans (hmin (right_ne_zero_of_mul hG)).1.2
      have h2 := left_ne_zero_of_mul hG
      by_cases h : locCycle (P ⊔ Ideal.span {f}) G = 0
      · rw [h, zero_sub, neg_ne_zero] at h2
        exact ⟨(hmin h2).1.1, le_sup_left.trans (hmin h2).1.2, hGU⟩
      · exact ⟨(hmin h).1.1, le_sup_left.trans (hmin h).1.2, hGU⟩
    · intro p hp
      have h2 := left_ne_zero_of_mul hp
      by_cases h : locCycle (Ideal.span {localQuotMap P U f}) p = 0
      · rw [h, zero_sub, neg_ne_zero] at h2
        exact (hmin' h2).1.1
      · exact (hmin' h).1.1
    · intro G hG hPG hGU
      rw [h₃ R P U _ G le_sup_left hG hPG hGU, h₃ R P U (P ⊔ Ideal.span {g}) G le_sup_left hG hPG hGU,
        h₃ R P U (G ⊔ Ideal.span {s}) U (le_sup_of_le_left hPG) hU hPU le_rfl, hmapx, hmapx,
        Ideal.map_sup, Ideal.map_span, Set.image_singleton]
  ·
    apply h₅ R P U hPU
    · intro W hW
      have h1 := hmin (left_ne_zero_of_mul hW)
      have h2 := hmin (right_ne_zero_of_mul hW)
      exact ⟨h1.1.1, le_sup_left.trans h1.1.2, le_sup_left.trans h2.1.2⟩
    · intro p hp
      exact (hmin' (left_ne_zero_of_mul hp)).1.1
    · intro W hW hPW hWU
      rw [h₃ R P U _ W le_sup_left hW hPW hWU, h₃ R P U (W ⊔ _) U (le_sup_of_le_left hPW) hU hPU le_rfl,
        hmapx, Ideal.map_sup, h₄ R P U f g]

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PLocalQuotColon
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

universe u

theorem LocalQuotColon.proof : LocalQuotColon.Statement.{u} := by
  intro R _ P U _ f g
  set S := Localization.AtPrime U
  set I := P.map (algebraMap R S)
  have hφ : ∀ x : R, localQuotMap P U x = Ideal.Quotient.mk I (algebraMap R S x) := fun _ => rfl
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, Submodule.mem_colon_singleton, smul_eq_mul]
    rw [Submodule.mem_colon_singleton, smul_eq_mul] at hx
    obtain ⟨p, hp, z, hz, hpz⟩ := Submodule.mem_sup.mp hx
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hz
    have hp0 : localQuotMap P U p = 0 := by
      rw [hφ, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mem_map_of_mem _ hp
    refine Ideal.mem_span_singleton'.mpr ⟨localQuotMap P U a, ?_⟩
    rw [← map_mul, ← map_mul, ← hpz, map_add (f := _), hp0, zero_add, map_mul]
  · intro y hy
    rw [Submodule.mem_colon_singleton, smul_eq_mul] at hy
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp hy
    obtain ⟨y0, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨b0, rfl⟩ := Ideal.Quotient.mk_surjective b
    obtain ⟨⟨r, t⟩, rfl⟩ := IsLocalization.mk'_surjective U.primeCompl y0
    obtain ⟨⟨r', t'⟩, rfl⟩ := IsLocalization.mk'_surjective U.primeCompl b0
    simp only [hφ] at hb
    have hI := Ideal.Quotient.eq.mp hb
    have e1 := IsLocalization.mk'_spec S r t
    have e2 := IsLocalization.mk'_spec S r' t'
    have hw : algebraMap R S ((t : R) * r' * f - (t' : R) * r * g) ∈ I := by
      have := I.mul_mem_left (algebraMap R S ((t : R) * t')) hI
      convert this using 1
      simp only [map_mul, map_sub]
      linear_combination (algebraMap R S t' * algebraMap R S g) * e1 -
        (algebraMap R S t * algebraMap R S f) * e2
    obtain ⟨⟨p, s⟩, hps⟩ := (IsLocalization.mem_map_algebraMap_iff U.primeCompl S).mp hw
    rw [← map_mul] at hps
    obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists U.primeCompl S).mp hps
    have hx : (c : R) * s * t' * r ∈ (P ⊔ Ideal.span {f}).colon {g} := by
      rw [Submodule.mem_colon_singleton, smul_eq_mul]
      refine Submodule.mem_sup.mpr ⟨-((c : R) * p), P.neg_mem (P.mul_mem_left _ p.2),
        (c : R) * s * t * r' * f, Ideal.mem_span_singleton'.mpr ⟨_, rfl⟩, ?_⟩
      linear_combination hc
    have hy' : Ideal.Quotient.mk I (IsLocalization.mk' S r t) =
        localQuotMap P U ((c : R) * s * t' * r) *
          Ideal.Quotient.mk I (IsLocalization.mk' S (1 : R) (c * s * t' * t)) := by
      rw [hφ, ← map_mul, IsLocalization.mul_mk'_eq_mk'_of_mul, mul_one]
      congr 1
      rw [IsLocalization.mk'_eq_iff_eq]
      congr 1
      push_cast
      ring
    rw [hy']
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hx)

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PLocalQuotRing
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

universe u

theorem LocalQuotRing.proof : LocalQuotRing.Statement.{u} := by
  intro R _ P U _ hP hPU
  have hdisj : Disjoint (U.primeCompl : Set R) (P : Set R) :=
    Set.disjoint_left.mpr fun x hx hxP => hx (hPU hxP)
  have hPS : (P.map (algebraMap R (Localization.AtPrime U))).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint U.primeCompl (Localization.AtPrime U) P hP hdisj
  have hker : (P.map (algebraMap R (Localization.AtPrime U))).comap
      (algebraMap R (Localization.AtPrime U)) = P :=
    IsLocalization.under_map_of_isPrime_disjoint U.primeCompl (Localization.AtPrime U) hP hdisj
  haveI := hPS
  have hdom : IsDomain (localQuot P U) := Ideal.Quotient.isDomain _
  have hloc : IsLocalRing (localQuot P U) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  have hmax : U.map (localQuotMap P U) = IsLocalRing.maximalIdeal (localQuot P U) := by
    rw [localQuotMap, ← Ideal.map_map, Localization.AtPrime.map_eq_maximalIdeal]
    exact IsLocalRing.map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective
  refine ⟨hdom, hloc, fun y => ?_, fun x => ?_⟩
  · rw [hmax, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]
  · rw [localQuotMap, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem, ← Ideal.mem_comap, hker]

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpHorizontalCorresp
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

theorem finsum_eq_finsum_mem_of_support_subset' {α : Type*} (f : α → ℤ) {s : Set α}
    (h : Function.support f ⊆ s) : ∑ᶠ i, f i = ∑ᶠ i ∈ s, f i := by
  rw [finsum_mem_def, Set.indicator_eq_self.2 h]

theorem BlowUpHorizontalCorresp.proof (hsat : BlowUpHorizontalSat.Statement.{u})
    (hmult : BlowUpHorizontalMult.Statement.{u}) (hlift : BlowUpHorizontalLift.Statement.{u})
    (hstrict : BlowUpHorizontalStrict.Statement.{u}) : BlowUpHorizontalCorresp.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ J _ P n hP N u hu hex hloc c x hx hxP
  have sat := hsat O ϖ hϖ K ι J P n hP N u hu hex hloc c x hx hxP
  have mult := hmult O ϖ hϖ K ι J P n hP N u hu hex hloc c x hx hxP
  have lift := hlift O ϖ hϖ K ι J P n hP N u hu hex hloc c x hx hxP
  have strict := hstrict O ϖ hϖ K ι J P n hP N u hu hex hloc c x hx hxP
  have hC : ∀ W : Ideal (MRing (extIdx ι J) O),
      (C ϖ : MRing ι O) ∈ W.comap (liftForm (ι := ι) (J := J) (R := O)) ↔
        (C ϖ : MRing (extIdx ι J) O) ∈ W := by
    intro W
    rw [Ideal.mem_comap]
    simp [liftForm]
  refine ⟨fun h => ?_, fun W hW hϖW => ⟨by rw [mult W hW hϖW]; exact hW, strict W hW hϖW⟩⟩
  classical
  unfold cycEval
  let s : Set (Ideal (MRing (extIdx ι J) O)) :=
    {W | divCycle (blowUpOf P u) (liftForm x) W ≠ 0 ∧ (C ϖ : MRing (extIdx ι J) O) ∉ W}
  let t : Set (Ideal (MRing ι O)) := {W | divCycle P x W ≠ 0 ∧ (C ϖ : MRing ι O) ∉ W}
  rw [finsum_eq_finsum_mem_of_support_subset' _ (s := s) ?hs,
    finsum_eq_finsum_mem_of_support_subset' _ (s := t) ?ht]
  case hs =>
    intro W hW
    rw [Function.mem_support] at hW
    exact ⟨fun h0 => hW (by rw [h0, zero_mul]), fun hc => hW (by simp only [if_pos hc, mul_zero])⟩
  case ht =>
    intro W hW
    rw [Function.mem_support] at hW
    exact ⟨fun h0 => hW (by rw [h0, zero_mul]), fun hc => hW (by simp only [if_pos hc, mul_zero])⟩
  refine finsum_mem_eq_of_bijOn (fun W => W.comap (liftForm (ι := ι) (J := J) (R := O)))
    ⟨?_, ?_, ?_⟩ ?_
  · intro W hW
    exact ⟨by rw [mult W hW.1 hW.2]; exact hW.1, fun h => hW.2 ((hC W).1 h)⟩
  · intro W₁ h₁ W₂ h₂ he
    ext F
    rw [sat W₁ h₁.1 h₁.2 F, sat W₂ h₂.1 h₂.2 F]
    simp only at he
    rw [he]
  · intro W hW
    obtain ⟨W', h1, h2, h3⟩ := lift W hW.1 hW.2
    exact ⟨W', ⟨h1, h2⟩, h3⟩
  · intro W hW
    simp only
    rw [if_neg hW.2, if_neg (fun h => hW.2 ((hC W).1 h)), mult W hW.1 hW.2]

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpHorizontalLift
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

noncomputable section

theorem BlowUpHorizontalLift.full : BlowUpHorizontalLift.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ J _ P n hP N u hu hex hloc c x hx hxP W hW hϖW
  classical
  have hPp : P.IsPrime := hP.multiProj.isPrime
  obtain ⟨hWp, hPW, hrelW⟩ := le_and_isRelevant_of_divCycle_ne_zero hW
  have hWmin : W ∈ (P ⊔ Ideal.span {x}).minimalPrimes := by
    unfold divCycle at hW
    split_ifs at hW with h
    · exact h.1
    · exact absurd rfl hW
  have hxW : x ∈ W := hWmin.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self x))
  obtain ⟨j₀, hj₀⟩ := hloc W hWp hPW hrelW hϖW
  choose v w hvW hvw using hj₀

  have hu₀ : u j₀ ∉ P := by
    intro h0
    obtain ⟨j, hj⟩ := hex
    have h1 : v j * u j ∈ P := by
      have h2 := P.add_mem (hvw j) (P.mul_mem_left (w j) h0)
      rwa [sub_add_cancel] at h2
    rcases hPp.mem_or_mem h1 with h2 | h2
    · exact hvW j (hPW h2)
    · exact hj h2

  set V : MRing ι O := ∏ j, v j with hV
  set a : J → MRing ι O := fun j => w j * ∏ i ∈ Finset.univ.erase j, v i with ha_def
  have hVW : V ∉ W := by
    intro h
    obtain ⟨j, -, hj⟩ := Ideal.IsPrime.prod_mem_iff.mp h
    exact hvW j hj
  have ha : ∀ j, V * u j - u j₀ * a j ∈ P := by
    intro j
    have e : V * u j - u j₀ * a j = (∏ i ∈ Finset.univ.erase j, v i) * (v j * u j - w j * u j₀) := by
      simp only [hV, ha_def]
      rw [← Finset.mul_prod_erase Finset.univ v (Finset.mem_univ j)]
      ring
    rw [e]
    exact P.mul_mem_left _ (hvw j)
  have hVa : V - a j₀ ∈ P := by
    have h1 : (V - a j₀) * u j₀ ∈ P := by
      have h2 := ha j₀
      rwa [show V * u j₀ - u j₀ * a j₀ = (V - a j₀) * u j₀ by ring] at h2
    exact (hPp.mem_or_mem h1).resolve_right hu₀
  have haW : a j₀ ∉ W := fun h => hVW (by simpa using W.add_mem (hPW hVa) h)

  set Wt : Ideal (MRing (extIdx ι J) O) :=
    (Ideal.map (Polynomial.C : MRing ι O →+* Polynomial (MRing ι O)) W).comap
      (aeval (R := O) (chartSubst a)) with hWt
  have hWtp : Wt.IsPrime := Ideal.comap_isPrime _ _
  have hcomap : ∀ s, liftForm (J := J) s ∈ Wt ↔ s ∈ W := by
    intro s
    rw [hWt, Ideal.mem_comap, aeval_chartSubst_liftForm]
    constructor
    · intro h
      simpa using Ideal.mem_map_C_iff.mp h 0
    · intro h
      exact Ideal.mem_map_of_mem _ h
  have hBWt : blowUpOf P u ≤ Wt := fun F hF =>
    Ideal.map_mono hPW (aeval_chartSubst_mem_of_mem_blowUpOf hPp hu₀ ha hF)
  have hxWt : liftForm x ∈ Wt := (hcomap x).2 hxW
  have hrelWt : IsRelevant Wt := by
    rintro (_ | k)
    · refine ⟨j₀, fun h => haW ?_⟩
      rw [hWt, Ideal.mem_comap] at h
      simp only [aeval_X, chartSubst] at h
      simpa using Ideal.mem_map_C_iff.mp h 1
    · obtain ⟨i, hi⟩ := hrelW k
      refine ⟨i, fun h => hi ((hcomap _).1 ?_)⟩
      rw [liftForm_X]
      exact h

  have hmin : Wt ∈ (blowUpOf P u ⊔ Ideal.span {liftForm x}).minimalPrimes := by
    refine ⟨⟨hWtp, sup_le hBWt ((Ideal.span_singleton_le_iff_mem _).mpr hxWt)⟩, fun Q hQ hQWt => ?_⟩
    have hQp := hQ.1
    have hBQ : blowUpOf P u ≤ Q := le_sup_left.trans hQ.2
    have hxQ : liftForm x ∈ Q := hQ.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    have hle : Q.comap (liftForm (J := J)) ≤ W := fun s hs => (hcomap s).1 (hQWt hs)
    have hQ₀ : Q.comap (liftForm (J := J)) = W :=
      le_antisymm hle (hWmin.2 ⟨Ideal.comap_isPrime _ _,
        sup_le (fun p hp => hBQ (liftForm_mem_blowUpOf hp))
          ((Ideal.span_singleton_le_iff_mem _).mpr hxQ)⟩ hle)
    intro F hF
    refine mem_of_aeval_chartSubst_mem hQp hQ₀.ge j₀ (fun h => haW ?_) (fun j => hBQ ?_) hF
    · rw [← hQ₀]
      exact h
    · apply mem_blowUpOf_of_sub
      have e : u j * a j₀ - u j₀ * a j = (V * u j - u j₀ * a j) - u j * (V - a j₀) := by ring
      rw [e]
      exact P.sub_mem (ha j) (P.mul_mem_left _ hVa)
  refine ⟨Wt, ?_, fun h => hϖW ((hcomap _).1 (by rw [liftForm_C]; exact h)), ?_⟩
  ·
    unfold divCycle
    rw [dite_eq_left ⟨hmin, hrelWt⟩]
    have hne := length_localizedQuot_ne_top (blowUpOf P u ⊔ Ideal.span {liftForm x}) Wt hmin
    have hnz : multAt (blowUpOf P u ⊔ Ideal.span {liftForm x}) Wt ≠ 0 := by
      unfold multAt
      rw [Ne, Module.length_eq_zero_iff, LocalizedModule.subsingleton_iff]
      intro hs
      obtain ⟨r, hr, hr0⟩ := hs (Ideal.Quotient.mk _ 1)
      rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, mul_one,
        Ideal.Quotient.eq_zero_iff_mem] at hr0
      exact hr (hmin.1.2 hr0)
    have htn : (multAt (blowUpOf P u ⊔ Ideal.span {liftForm x}) Wt).toNat ≠ 0 :=
      fun h0 => (ENat.toNat_eq_zero.mp h0).elim hnz hne
    exact_mod_cast htn
  · ext s
    rw [Ideal.mem_comap]
    exact hcomap s

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpHorizontalStrict
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

noncomputable section

section Helpers

set_option linter.unusedSectionVars false

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} {J : Type} {R : Type*} [CommRing R]

theorem blowUpOf_mono {P W : Ideal (MRing ι R)} (h : P ≤ W) (u : J → MRing ι R) :
    blowUpOf P u ≤ blowUpOf W u := by
  intro F hF
  let φ := Polynomial.mapRingHom (Ideal.Quotient.factor h)
  have key : φ.comp (aeval (R := R) (blowUpSubst P u)).toRingHom =
      (aeval (R := R) (blowUpSubst W u)).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [φ]
      rfl
    · rintro ⟨_ | k, i⟩
      · simp [φ, blowUpSubst, Ideal.Quotient.factor_mk]
      · simp [φ, blowUpSubst, Ideal.Quotient.factor_mk]
  have e := DFunLike.congr_fun key F
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] at e
  rw [blowUpOf, RingHom.mem_ker] at hF ⊢
  rw [← e, hF, map_zero]

theorem blowUpOf_isPrime {W : Ideal (MRing ι R)} (hW : W.IsPrime) (u : J → MRing ι R) :
    (blowUpOf W u).IsPrime := by
  have := hW
  exact RingHom.ker_isPrime _

theorem blowUpOf_comap_le {P : Ideal (MRing ι R)} {u : J → MRing ι R} {H : Ideal (MRing (extIdx ι J) R)}
    (hH : H.IsPrime) (hPH : blowUpOf P u ≤ H) {j₀ : J}
    (hj₀ : u j₀ ∉ H.comap (liftForm (ι := ι) (J := J) (R := R))) :
    blowUpOf (H.comap (liftForm (ι := ι) (J := J) (R := R))) u ≤ H := by
  have := hH
  let L := FractionRing (MRing (extIdx ι J) R ⧸ H)
  let q : MRing (extIdx ι J) R →+* L := (algebraMap _ L).comp (Ideal.Quotient.mk H)
  have hq : ∀ y, q y = 0 ↔ y ∈ H := by
    intro y
    simp only [q, RingHom.comp_apply]
    rw [map_eq_zero_iff _ (IsFractionRing.injective _ L), Ideal.Quotient.eq_zero_iff_mem]
  have hu₀ : q (liftForm (u j₀)) ≠ 0 := fun h0 => hj₀ ((hq _).mp h0)
  let ψ : MRing ι R ⧸ H.comap (liftForm (ι := ι) (J := J) (R := R)) →+* L :=
    Ideal.Quotient.lift _ (q.comp (liftForm (ι := ι) (J := J) (R := R)).toRingHom) fun a ha => (hq _).mpr ha
  let ε : Polynomial (MRing ι R ⧸ H.comap (liftForm (ι := ι) (J := J) (R := R))) →+* L :=
    Polynomial.eval₂RingHom ψ (q (newVar j₀) / q (liftForm (u j₀)))
  have hψ : ∀ a : MRing ι R, ψ (Ideal.Quotient.mk _ a) = q (liftForm a) := fun a =>
    Ideal.Quotient.lift_mk _ _ _

  have hrelq : ∀ j : J, q (newVar j) * q (liftForm (u j₀)) = q (liftForm (u j)) * q (newVar j₀) := by
    intro j
    have hr : newVar j * liftForm (u j₀) - newVar j₀ * liftForm (u j) ∈ H :=
      hPH (mem_blowUpOf_of_sub (P := P) (u := u) (j := j) (j' := j₀) (a := u j₀) (a' := u j)
        (by rw [show u j * u j₀ - u j₀ * u j = 0 from by ring]; exact P.zero_mem))
    have h1 := (hq _).mpr hr
    rw [map_sub, map_mul, map_mul, sub_eq_zero] at h1
    rw [h1, mul_comm]
  have key : ε.comp (aeval (R := R) (blowUpSubst (H.comap (liftForm (ι := ι) (J := J) (R := R))) u)).toRingHom =
      q := by
    apply MvPolynomial.ringHom_ext
    · intro r
      rw [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, aeval_C,
        Polynomial.algebraMap_apply, ← Ideal.Quotient.mk_algebraMap]
      simp only [ε, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
      rw [hψ, AlgHom.commutes]
      rfl
    · rintro ⟨_ | k, i⟩
      · rw [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, aeval_X]
        show ε (Polynomial.C (Ideal.Quotient.mk _ (u i)) * Polynomial.X) = q (newVar i)
        simp only [ε, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_mul, Polynomial.eval₂_C,
          Polynomial.eval₂_X]
        rw [hψ, ← mul_div_assoc, div_eq_iff hu₀]
        exact (hrelq i).symm
      · rw [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, aeval_X]
        show ε (Polynomial.C (Ideal.Quotient.mk _ (X ⟨k, i⟩))) = q (X ⟨some k, i⟩)
        simp only [ε, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
        rw [hψ, liftForm_X]
  intro F hF
  rw [blowUpOf, RingHom.mem_ker] at hF
  have h3 := DFunLike.congr_fun key F
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] at h3
  rw [hF, map_zero] at h3
  exact (hq F).mp h3.symm

end Helpers

theorem BlowUpHorizontalStrict.full : BlowUpHorizontalStrict.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ J _ P n hP N u hu hex hloc c x hx hxP W hW hϖW hj
  obtain ⟨j₀, hj₀⟩ := hj
  obtain ⟨hWp, hBW, -⟩ := le_and_isRelevant_of_divCycle_ne_zero hW
  have hmin : W ∈ (blowUpOf P u ⊔ Ideal.span {liftForm x}).minimalPrimes := by
    unfold divCycle at hW
    split_ifs at hW with h
    · exact h.1
    · exact absurd rfl hW
  have hPW₀ : P ≤ W.comap (liftForm (ι := ι) (J := J) (R := O)) := fun p hp => hBW (liftForm_mem_blowUpOf hp)
  have hle := blowUpOf_comap_le hWp hBW hj₀
  have hxW : liftForm x ∈ W := hmin.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  refine le_antisymm (hmin.2 ⟨blowUpOf_isPrime (Ideal.comap_isPrime _ _) u,
    sup_le (blowUpOf_mono hPW₀ u) ((Ideal.span_singleton_le_iff_mem _).mpr ?_)⟩ hle) hle
  exact liftForm_mem_blowUpOf (P := W.comap (liftForm (ι := ι) (J := J) (R := O))) hxW

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

set_option maxSynthPendingDepth 1

theorem GroundTheory.Heights₂.Heights.AutoClose.Inter_R1Indep : GroundTheory.Heights₂.Heights.Inter.RegularityIndependence.Statement :=
  @GroundTheory.Heights₂.Heights.Inter.RegularityIndependence.of_remaining GroundTheory.Heights₂.Heights.AutoClose.Inter_R1RegMaxSurj

theorem GroundTheory.Heights₂.Heights.AutoClose.chart_norm_count : GroundTheory.Heights₂.Heights.Inter.ChartNormCount.Statement :=
  @GroundTheory.Heights₂.Heights.Inter.ChartNormCount.proof GroundTheory.Heights₂.Heights.AutoClose.Inter_ChartSpecCount GroundTheory.Heights₂.Heights.Inter.ChartNormPts.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_ConeVarInj.{u} : GroundTheory.Heights₂.Heights.FieldNumbers.ConeVarInj.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.FieldNumbers.ConeVarInj.proof.{u} GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_ConeVarNumerator

theorem GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_ConeVarUnit.{u} : GroundTheory.Heights₂.Heights.FieldNumbers.ConeVarUnit.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.FieldNumbers.ConeVarUnit.proof.{u} GroundTheory.Heights₂.Heights.FieldNumbers.DegZeroLocQuot.proof GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_ConeVarNumerator

theorem GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_FunctionFieldFinite.{u} : GroundTheory.Heights₂.Heights.FieldNumbers.FunctionFieldFinite.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.FieldNumbers.FunctionFieldFinite.proof.{u} GroundTheory.Heights₂.Heights.FieldNumbers.MChartDehomog.proof GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_MChartTrdeg

theorem GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_DegZeroLocDim.{u} : GroundTheory.Heights₂.Heights.FieldNumbers.DegZeroLocDim.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.FieldNumbers.DegZeroLocDim.proof.{u} GroundTheory.Heights₂.Heights.FieldNumbers.MChartHomog.proof GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_MChartTrdeg GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_MChartLocDim

theorem GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_SegreFlagClosureModel : GroundTheory.Heights₂.Heights.NumbersDVR.SegreFlagClosureModel.Statement :=
  @GroundTheory.Heights₂.Heights.NumbersDVR.SegreFlagClosureModel.proof GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_SegreFlagClosureTrdeg

theorem GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_FlagProjTrdegLe : GroundTheory.Heights₂.Heights.NumbersDVR.FlagProjTrdegLe.Statement :=
  @GroundTheory.Heights₂.Heights.NumbersDVR.FlagProjTrdegLe.proof GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_SegreFlagClosureTrdeg

theorem GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_C3ExceptionalContraction.{u} : GroundTheory.Heights₂.Heights.NumbersDVR.ExceptionalContraction.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.NumbersDVR.ExceptionalContraction.proof.{u} GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_C3BlowUpPieces

theorem GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_BlowUpHorizontalCorresp.{u} : GroundTheory.Heights₂.Heights.NumbersDVR.BlowUpHorizontalCorresp.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.NumbersDVR.BlowUpHorizontalCorresp.proof.{u} GroundTheory.Heights₂.Heights.NumbersDVR.BlowUpHorizontalSat.full GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_BlowUpHorizontalMult GroundTheory.Heights₂.Heights.NumbersDVR.BlowUpHorizontalLift.full GroundTheory.Heights₂.Heights.NumbersDVR.BlowUpHorizontalStrict.full

theorem GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_C3ResidualContractionComponent.{u} : GroundTheory.Heights₂.Heights.NumbersDVR.ResidualContractionComponent.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.NumbersDVR.ResidualContractionComponent.proof.{u} GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_C3BlowUpPieces

theorem GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_LocalCoeffRing.{u} : GroundTheory.Heights₂.Heights.NumbersDVR.LocalCoeffRing.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.NumbersDVR.LocalCoeffRing.proof.{u} GroundTheory.Heights₂.Heights.NumbersDVR.LocalQuotRing.proof GroundTheory.Heights₂.Heights.NumbersDVR.LocalQuotPrimes.proof GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_LocCycleLocalQuot GroundTheory.Heights₂.Heights.NumbersDVR.LocalQuotColon.proof GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_LocalQuotFinsum GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_LocalCoeffLocal

theorem GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_HomLocRingDimLe.{u} : GroundTheory.Heights₂.Heights.NumbersDVR.HomLocRingDimLe.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.NumbersDVR.HomLocRingDimLe.proof.{u} GroundTheory.Heights₂.Heights.NumbersDVR.HomLocRingMem.proof GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_HomLocRingIsLocal

theorem GroundTheory.Heights₂.Heights.AutoClose.TubeDeepAreaCount : GroundTheory.Heights₂.Heights.TubeDeepAreaCount.Statement :=
  @GroundTheory.Heights₂.Heights.TubeDeepAreaCount.proof GroundTheory.Heights₂.Heights.AutoClose.IsolatedPointsCount
