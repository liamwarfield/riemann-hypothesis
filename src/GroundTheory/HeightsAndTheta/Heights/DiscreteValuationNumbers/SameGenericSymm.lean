module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.JoinCoordMidVar
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PContractRelDimLe
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.CutIdentityRightSideCongrOfSubMem
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PRepresentative

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.SameGenericSymm
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1

universe u

section Statements

variable (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O]
variable (Ω : Type*) [Field Ω] [Algebra O Ω]
variable {K : Type} [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]

def Ba.Statement : Prop :=
  ∀ (x : (Σ k, ι k) → Ω) (d N : ℕ) (V : Type u) [AddCommGroup V] [Module Ω V]
    (E E' E'' : ChartBundle O (mseg x) N V),
    IsModelOver O (mcIdeal O x) d → SameGeneric O x E E' → SameGeneric O x E' E'' →
    ∀ (k : ℕ), 1 ≤ k → k ≤ d + 1 → ∀ (q : ℕ) (L : Fin q → K → ℤ) (Q : MvPolynomial (Fin q) ℤ),
      Q.IsHomogeneous (d + 1 - k) →
      ck O x d N E E'' k L Q = ck O x d N E E' k L Q + ck O x d N E' E'' k L Q ∧
        ck O x d N E' E k L Q = -ck O x d N E E' k L Q

def Bb.Statement : Prop :=
  ∀ (x : (Σ k, ι k) → Ω) (d N N₁ N₂ : ℕ) (V V₁ V₂ : Type u) [AddCommGroup V] [Module Ω V]
    [AddCommGroup V₁] [Module Ω V₁] [AddCommGroup V₂] [Module Ω V₂]
    (E E' : ChartBundle O (mseg x) N V) (i : V₁ →ₗ[Ω] V) (p : V →ₗ[Ω] V₂)
    (E₁ E₁' : ChartBundle O (mseg x) N₁ V₁) (E₂ E₂' : ChartBundle O (mseg x) N₂ V₂),
    IsModelOver O (mcIdeal O x) d → SameGeneric O x E E' → IsSubQuot O x E i p E₁ E₂ →
    IsSubQuot O x E' i p E₁' E₂' →
    ∀ (k : ℕ), 1 ≤ k → k ≤ d + 1 → ∀ (q : ℕ) (L : Fin q → K → ℤ) (Q : MvPolynomial (Fin q) ℤ),
      Q.IsHomogeneous (d + 1 - k) →
      ck O x d N E E' k L Q = ck O x d N₁ E₁ E₁' k L Q + ck O x d N₂ E₂ E₂' k L Q

def Bd.Statement : Prop :=
  ∀ (x : (Σ k, ι k) → Ω) (d N : ℕ) (V : Type u) [AddCommGroup V] [Module Ω V]
    (E E' : ChartBundle O (mseg x) N V) (g : O), g ≠ 0 →
    IsModelOver O (mcIdeal O x) d →
    (∀ s, mseg x s ≠ 0 → ∀ v, v ∈ E'.lat s ↔ ∃ e ∈ E.lat s, v = algebraMap O Ω g • e) →
    ∀ (k : ℕ), 1 ≤ k → k ≤ d + 1 → ∀ (q : ℕ) (L : Fin q → K → ℤ) (Q : MvPolynomial (Fin q) ℤ),
      Q.IsHomogeneous (d + 1 - k) →
      ck O x d N E E' k L Q = (k : ℤ) * rootNum O x d N E (psum (Fin N) ℤ (k - 1)) L Q g ∧
        ∀ (m n : ℕ) (h w : O), IsUnit w → 1 ≤ m → g ^ m = w * h ^ n →
          (m : ℤ) * rootNum O x d N E (psum (Fin N) ℤ (k - 1)) L Q g =
            (n : ℤ) * rootNum O x d N E (psum (Fin N) ℤ (k - 1)) L Q h

end Statements

section FieldStatements

variable (F : Type*) [Field F] (Ω : Type*) [Field Ω] [Algebra F Ω]
variable {K : Type} [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]

def SegreFlagIndep.Statement : Prop :=
  ∀ (x : (Σ k, ι k) → Ω) (e : ℕ), IsProjVarF (mcIdeal F x) e →
    ∀ (N : ℕ) (E : Type u) [AddCommGroup E] [Module Ω E] (B : ChartBundle F (mseg x) N E)
      (fl₁ fl₂ : FullFlag F x B) (I₀ : IFamily F ι), IsFieldIntersection I₀ →
    ∀ G : MvPolynomial (Fin N) ℤ, G.IsSymmetric → ∀ (c n : ℕ) (Y : Fin n → K → ℤ),
      G.IsHomogeneous c → c + n = e →
      polyNum I₀ (mcIdeal F x) e (Fin.append fl₁.deg Y)
          (rename (Fin.castAdd n) G * ∏ j : Fin n, X (Fin.natAdd N j)) =
        polyNum I₀ (mcIdeal F x) e (Fin.append fl₂.deg Y)
          (rename (Fin.castAdd n) G * ∏ j : Fin n, X (Fin.natAdd N j))

end FieldStatements

section Inhabitants

variable (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem sameGeneric_symm {Ω : Type*} [Field Ω] [Algebra O Ω] {K : Type} [Fintype K] {ι : K → Type}
    [∀ k, Fintype (ι k)] {x : (Σ k, ι k) → Ω} {N : ℕ} {V : Type*} [AddCommGroup V] [Module Ω V]
    {E E' : ChartBundle O (mseg x) N V} (h : SameGeneric O x E E') : SameGeneric O x E' E :=
  fun s hs => ⟨(h s hs).2, (h s hs).1⟩

end Inhabitants

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.IsFieldIntersectionExample
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1

noncomputable section

universe u

namespace Numbers

abbrev Statement : Prop := IntNumIsFieldIntersection.Statement.{u}

variable {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  [∀ k, Fintype (ι k)]

theorem agree_of_existsUnique (hN : Statement.{u}) (hU : ExistsUniqueStatement F ι)
    (I : IFamily F ι) (hI : IsFieldIntersection I) (V : Ideal (MRingOver F ι)) (n : ℕ)
    (L : Fin n → K → ℤ) (hV : IsProjVarF V n) : I V n L = intNum F V L := by
  obtain ⟨I₀, -, h₀⟩ := hU
  exact (h₀ I hI V n L hV).trans (h₀ _ (hN F K ι) V n L hV).symm

theorem existsUnique_iff (hN : Statement.{u}) :
    ExistsUniqueStatement F ι ↔ ∀ I : IFamily F ι, IsFieldIntersection I →
      ∀ (V : Ideal (MRingOver F ι)) (n : ℕ) (L : Fin n → K → ℤ), IsProjVarF V n →
        I V n L = intNum F V L :=
  ⟨fun hU I hI V n L hV => agree_of_existsUnique hN hU I hI V n L hV,
    fun h => ⟨fun V _ L => intNum F V L, hN F K ι, h⟩⟩


omit [DecidableEq K] [∀ k, Fintype (ι k)] in
theorem ringKrullDim_eq_of_relDim (V : Ideal (MRing ι F)) (n : ℕ)
    (h : FieldNumbers.relDim V = (n : WithBot (WithTop ℤ))) :
    ringKrullDim (MRing ι F ⧸ V) = ((n + Fintype.card K : ℕ) : WithBot ℕ∞) := by
  unfold FieldNumbers.relDim at h
  generalize ringKrullDim (MRing ι F ⧸ V) = d at h ⊢
  induction d using WithBot.recBotCoe with
  | bot => exact absurd h (by simp)
  | coe e =>
    induction e using ENat.recTopCoe with
    | top =>
      have h₁ : ((⊤ : WithTop ℤ) : WithBot (WithTop ℤ)) = (n : WithBot (WithTop ℤ)) := h
      have h' : (⊤ : WithTop ℤ) = (n : WithTop ℤ) := by exact_mod_cast h₁
      exact absurd h' (WithTop.top_ne_coe)
    | coe m =>
      have h₁ : ((((m : ℤ) - Fintype.card K : ℤ) : WithTop ℤ) : WithBot (WithTop ℤ)) =
          (n : WithBot (WithTop ℤ)) := h
      have h' : (m : ℤ) - Fintype.card K = n := by exact_mod_cast h₁
      have hm : m = n + Fintype.card K := by omega
      rw [hm]
      rfl

theorem finsum_mul_eq_sum {α : Type*} (D : α →₀ ℤ) (J : α → ℤ) :
    ∑ᶠ W, D W * J W = D.sum fun W m => m * J W := by
  classical
  rw [Finsupp.sum, finsum_eq_sum_of_support_subset]
  intro W hW
  rw [Function.mem_support] at hW
  rw [Finset.mem_coe, Finsupp.mem_support_iff]
  intro h0
  exact hW (by rw [h0, zero_mul])

theorem isIntersectionTheory (hPt : IntNumPoint.Statement.{u})
    (hBase : FieldNumbers.IntNumBase.Statement.{u}) {I : IFamily F ι}
    (hI : IsFieldIntersection I) : FieldNumbers.IsIntersectionTheory F I := by
  refine ⟨?_, ?_⟩
  · intro P hP h0
    have hdim := ringKrullDim_eq_of_relDim P 0 (by rw [h0]; rfl)
    choose i hi using hP.relevant
    rw [hI.1 P ![] i ⟨(Objects.isMultiProjPrime_iff P).mp hP, hdim⟩ hi,
      ← hPt F K ι P i hP hdim hi]
    obtain ⟨-, h2⟩ := hBase F K ι P hP h0
    rw [h2, FieldNumbers.resDeg, dite_eq_left hP.isPrime]
  · intro P n hP hdim bf bg f g hf hg hfP hgP bs
    have hd := ringKrullDim_eq_of_relDim P (n + 1) hdim
    have hs : IsRatSection P (fun k => (bf k : ℤ) - bg k) f g :=
      ⟨bf, bg, (Objects.isMultiHomog_iff f bf).mp hf, (Objects.isMultiHomog_iff g bg).mp hg,
        hfP, hgP, fun k => rfl⟩
    rw [hI.2 P n bs _ f g ⟨(Objects.isMultiProjPrime_iff P).mp hP, hd⟩ hs]
    have hD : ∀ W, ReciprocityTheory.ChartRestriction.G.AI.I1.ratDiv P f g W = ratDiv P f g W := by
      intro W
      simp only [ratDiv, ReciprocityTheory.ChartRestriction.G.AI.I1.ratDiv, Finsupp.sub_apply, Finsupp.mapRange_apply]
      rw [VocabDivCycle.proof F K ι P f W, VocabDivCycle.proof F K ι P g W]
    simp only [cycEval, ReciprocityTheory.ChartRestriction.G.AI.I1.cycEval, ← hD]
    exact (finsum_mul_eq_sum _ _).symm

theorem agree (hUq : FieldNumbers.IntNumUnique.Statement.{u}) (hPt : IntNumPoint.Statement.{u})
    (hBase : FieldNumbers.IntNumBase.Statement.{u}) (I : IFamily F ι)
    (hI : IsFieldIntersection I) (V : Ideal (MRingOver F ι)) (n : ℕ) (L : Fin n → K → ℤ)
    (hV : IsProjVarF V n) : I V n L = intNum F V L :=
  hUq F K ι I (isIntersectionTheory hPt hBase hI) V ((Objects.isMultiProjPrime_iff V).mpr hV.1) n
    (relDim_eq_of_ringKrullDim V n hV.2) L

theorem existsUnique (hN : Statement.{u}) (hUq : FieldNumbers.IntNumUnique.Statement.{u})
    (hPt : IntNumPoint.Statement.{u}) (hBase : FieldNumbers.IntNumBase.Statement.{u}) :
    ExistsUniqueStatement F ι :=
  (existsUnique_iff hN).mpr (agree hUq hPt hBase)

theorem agree_of (hBase : FieldNumbers.IntNumBase.Statement.{u})
    (hCut : FieldNumbers.CutRational.Statement.{u}) (hEx : FieldNumbers.ExistsForm.Statement.{u})
    (hDiv : FieldNumbers.DivCycleSupport.Statement.{u}) (I : IFamily F ι)
    (hI : IsFieldIntersection I) (V : Ideal (MRingOver F ι)) (n : ℕ) (L : Fin n → K → ℤ)
    (hV : IsProjVarF V n) : I V n L = intNum F V L :=
  agree (FieldNumbers.IntNumUnique.proof hCut hBase hEx hDiv) (IntNumPoint.proof hBase) hBase I hI
    V n L hV

end Numbers

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.RelevantMinimalOfDivCycleNeZero
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

section Avoid

variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} {R : Type*} [CommRing R]

theorem exists_form_avoid_primes (S : Finset (Ideal (MRing ι R)))
    (hS : ∀ W ∈ S, W.IsPrime ∧ IsMultiHomogIdeal W ∧ IsRelevant W) (e₀ : K → ℕ) :
    ∃ (e : K → ℕ) (h : MRing ι R), IsMultiHomog h e ∧ e₀ ≤ e ∧ ∀ W ∈ S, h ∉ W := by
  classical
  set T := S.filter (fun W => ∀ W' ∈ S, W ≤ W' → W' = W) with hT
  have hTS : ∀ W ∈ T, W ∈ S := fun W hW => (Finset.mem_filter.mp hW).1
  have hTmax : ∀ W ∈ T, ∀ W' ∈ S, W ≤ W' → W' = W := fun W hW => (Finset.mem_filter.mp hW).2
  have hle : ∀ W ∈ S, ∃ W' ∈ T, W ≤ W' := by
    intro W hW
    obtain ⟨W', hWW', hW'⟩ := (S.finite_toSet).exists_le_maximal hW
    exact ⟨W', Finset.mem_filter.mpr ⟨hW'.prop, fun W'' hW'' h => le_antisymm (hW'.2 hW'' h) h⟩, hWW'⟩
  have hsep : ∀ W ∈ T, ∃ (a : MRing ι R) (A : K → ℕ), IsMultiHomog a A ∧ a ∉ W ∧
      ∀ W' ∈ T.erase W, a ∈ W' := by
    intro W hW
    have := (hS W (hTS W hW)).1
    refine exists_form_separator (T.erase W) fun W' hW' => ⟨(hS W' (hTS W' (Finset.mem_of_mem_erase hW'))).2.1,
      fun hle' => Finset.ne_of_mem_erase hW' ?_⟩
    exact (hTmax W' (Finset.mem_of_mem_erase hW') W (hTS W hW) hle').symm
  choose! a A haH haW haMem using hsep
  set e : K → ℕ := e₀ + ∑ W ∈ T, A W with he
  have hAe : ∀ W ∈ T, A W ≤ e := fun W hW =>
    le_add_left (Finset.single_le_sum (f := A) (fun _ _ => fun _ => Nat.zero_le _) hW)
  have hmon : ∀ W ∈ T, ∃ m : MRing ι R, IsMultiHomog m (e - A W) ∧ m ∉ W := by
    intro W hW
    have := (hS W (hTS W hW)).1
    exact exists_form_not_mem_of_isRelevant (hS W (hTS W hW)).2.2 _
  choose! m hmH hmW using hmon
  refine ⟨e, ∑ W ∈ T, a W * m W, ?_, le_self_add, ?_⟩
  · refine IsWeightedHomogeneous.sum _ _ _ fun W hW => ?_
    have := (haH W hW).mul (hmH W hW)
    rwa [add_tsub_cancel_of_le (hAe W hW)] at this
  · have key : ∀ W₀ ∈ T, (∑ W ∈ T, a W * m W) ∉ W₀ := by
      intro W₀ hW₀ hmem
      have hp := (hS W₀ (hTS W₀ hW₀)).1
      rw [← Finset.add_sum_erase _ _ hW₀] at hmem
      have hrest : (∑ W ∈ T.erase W₀, a W * m W) ∈ W₀ :=
        Ideal.sum_mem _ fun W hW => Ideal.mul_mem_right _ _ (haMem W (Finset.mem_of_mem_erase hW) W₀
          (Finset.mem_erase.mpr ⟨(Finset.ne_of_mem_erase hW).symm, hW₀⟩))
      rcases hp.mem_or_mem ((Ideal.add_mem_iff_left _ hrest).mp hmem) with h2 | h2
      · exact haW W₀ hW₀ h2
      · exact hmW W₀ hW₀ h2
    intro W hW hmem
    obtain ⟨W', hW', hle'⟩ := hle W hW
    exact key W' hW' (hle' hmem)

end Avoid

theorem mem_minimalPrimes_sup_span_of_mem {A : Type*} [CommRing A] [IsNoetherianRing A] {P H : Ideal A}
    [hP : P.IsPrime] {x y : A} (hH : H ∈ (P ⊔ Ideal.span {x}).minimalPrimes) (hy : y ∉ P)
    (hyH : y ∈ H) : H ∈ (P ⊔ Ideal.span {y}).minimalPrimes := by
  have : H.IsPrime := hH.1.1
  have hPH : P ≤ H := le_sup_left.trans hH.1.2
  obtain ⟨Q, hQ, hQH⟩ := Ideal.exists_minimalPrimes_le
    (sup_le hPH ((Ideal.span_singleton_le_iff_mem _).mpr hyH))
  have : Q.IsPrime := hQ.1.1
  have hPQ : P ≤ Q := le_sup_left.trans hQ.1.2
  have hyQ : y ∈ Q := hQ.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self y))
  suffices hQH' : Q = H by rw [← hQH']; exact hQ
  by_contra hne
  have hlt : Q < H := lt_of_le_of_ne hQH hne
  let φ := Ideal.Quotient.mk P
  have hφ : Function.Surjective φ := Ideal.Quotient.mk_surjective
  have hHm : (H.map φ).IsPrime := Ideal.map_isPrime_of_surjective hφ (by rwa [Ideal.mk_ker])
  have hQm : (Q.map φ).IsPrime := Ideal.map_isPrime_of_surjective hφ (by rwa [Ideal.mk_ker])
  have hcomap : ∀ I : Ideal A, P ≤ I → (I.map φ).comap φ = I := fun I hI => by
    rw [Ideal.comap_map_of_surjective φ hφ, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.mpr hI]
  have h_lt : Q.map φ < H.map φ := (Ideal.map_mono hlt.le).lt_of_not_ge fun h => hlt.not_ge (by
    simpa only [hcomap Q hPQ, hcomap H hPH] using Ideal.comap_mono (f := φ) h)
  have h1 := Ideal.map_height_le_one_of_mem_minimalPrimes hH
  have : (H.map φ).FiniteHeight := ⟨Or.inr (h1.trans_lt (WithTop.coe_lt_top 1)).ne⟩
  have h0 := (Ideal.height_strict_mono_of_isPrime_of_isPrime h_lt).trans_le h1
  rw [Order.lt_one_iff, Ideal.height_eq_zero_iff] at h0
  have : (⊥ : Ideal (A ⧸ P)).IsPrime := Ideal.isPrime_bot
  have h0' : Q.map φ ∈ (⊥ : Ideal (A ⧸ P)).minimalPrimes := h0
  rw [Ideal.minimalPrimes_eq_subsingleton_self] at h0'
  have : φ y ∈ Q.map φ := Ideal.mem_map_of_mem φ hyQ
  rw [show Q.map φ = ⊥ from h0', Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at this
  exact hy this

theorem relevant_minimal_of_divCycle_ne_zero {K : Type*} {ι : K → Type*} {R : Type*} [CommRing R]
    {P W : Ideal (MRing ι R)} {x : MRing ι R} (h : divCycle P x W ≠ 0) :
    W ∈ (P ⊔ Ideal.span {x}).minimalPrimes ∧ IsRelevant W := by
  unfold divCycle at h
  split_ifs at h with hW
  · exact hW
  · exact absurd rfl h

theorem AvoidingFormExists.proof : AvoidingFormExists.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP b f g hD e₀
  have hPp : P.IsPrime := hP.multiProj.isPrime
  have hD1 := hD.1
  obtain ⟨bf, bg, hf, hg, -⟩ := hD1.degrees

  have hfin : ∀ x : MRing ι O, {W | W ∈ (P ⊔ Ideal.span {x}).minimalPrimes ∧ IsRelevant W}.Finite :=
    fun x => (Ideal.finite_minimalPrimes_of_isNoetherianRing _ _).subset fun W hW => hW.1
  have hmin : ∀ (x : MRing ι O) (c : K → ℕ), IsMultiHomog x c →
      ∀ W ∈ {W | W ∈ (P ⊔ Ideal.span {x}).minimalPrimes ∧ IsRelevant W},
        W.IsPrime ∧ IsMultiHomogIdeal W ∧ IsRelevant W := fun x c hx W hW =>
    ⟨hW.1.1.1, MinimalPrimeMultiHomog.proof O K ι _ W
      (SupSpanMultiHomog.proof O K ι P x c hP.multiProj.multiHomog hx) hW.1, hW.2⟩
  obtain ⟨e, h, hh, he, hS⟩ := exists_form_avoid_primes
    (insert P ((hfin f).toFinset ∪ (hfin g).toFinset)) (by
      intro W hW
      rcases Finset.mem_insert.mp hW with rfl | hW
      · exact ⟨hPp, hP.multiProj.multiHomog, hP.multiProj.relevant⟩
      rcases Finset.mem_union.mp hW with hW | hW
      · exact hmin f bf hf W ((hfin f).mem_toFinset.mp hW)
      · exact hmin g bg hg W ((hfin g).mem_toFinset.mp hW)) e₀
  have hhP : h ∉ P := hS P (Finset.mem_insert_self _ _)
  have hhf : ∀ W ∈ (P ⊔ Ideal.span {f}).minimalPrimes, IsRelevant W → h ∉ W := fun W hW hr =>
    hS W (Finset.mem_insert_of_mem (Finset.mem_union_left _ ((hfin f).mem_toFinset.mpr ⟨hW, hr⟩)))
  have hhg : ∀ W ∈ (P ⊔ Ideal.span {g}).minimalPrimes, IsRelevant W → h ∉ W := fun W hW hr =>
    hS W (Finset.mem_insert_of_mem (Finset.mem_union_right _ ((hfin g).mem_toFinset.mpr ⟨hW, hr⟩)))

  have hG : ∀ G, ratDiv P f g G ≠ 0 → divCycle P h G = 0 := by
    intro G hG
    by_contra hhG
    have hhG' : h ∈ G := (relevant_minimal_of_divCycle_ne_zero hhG).1.1.2
      (Ideal.mem_sup_right (Ideal.mem_span_singleton_self h))
    by_cases hfG : divCycle P f G = 0
    · have hgG : divCycle P g G ≠ 0 := fun h0 => hG (by unfold ratDiv; rw [hfG, h0, sub_zero])
      obtain ⟨hm, hr⟩ := relevant_minimal_of_divCycle_ne_zero hgG
      exact hhg G hm hr hhG'
    · obtain ⟨hm, hr⟩ := relevant_minimal_of_divCycle_ne_zero hfG
      exact hhf G hm hr hhG'
  have hterm : ∀ s : MRing ι O, ∀ G, ratDiv P f g G ≠ 0 →
      divCycle P (s * h) G = divCycle P s G ∨ s ∈ P := by
    intro s G hr
    by_cases hsP : s ∈ P
    · exact Or.inr hsP
    · left
      rw [DivCycleMul.proof O K ι P s h hPp hsP hhP, Pi.add_apply, hG G hr, add_zero]
  refine ⟨e, h, hh, hhP, he, ?_, fun G _ hr => hG G hr, ?_, ?_⟩
  ·
    intro H hH _
    obtain ⟨hm, hr⟩ := relevant_minimal_of_divCycle_ne_zero hH
    have : H.IsPrime := hm.1.1
    have hPH : P ≤ H := le_sup_left.trans hm.1.2
    have hhH : h ∈ H := hm.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self h))
    refine IsVerticalDivisor.of_unit_off_special hD1.degrees
      (fun hfH => hhf H (mem_minimalPrimes_sup_span_of_mem hm hD1.num_not_mem hfH) hr hhH)
      (fun hgH => hhg H (mem_minimalPrimes_sup_span_of_mem hm hD1.den_not_mem hgH) hr hhH) (by
        intro W hW hHW hrW hϖW
        obtain ⟨u, v, hu, hv, huv⟩ := hD1.unit_off_special W hW (hPH.trans hHW) hrW hϖW
        exact ⟨u, v, hu, hv, hPH huv⟩)
  ·
    refine Nat.le_zero.mp (ciSup_le' fun G => ?_)
    by_cases hr : ratDiv P f g G.1 = 0
    · simp [hr]
    · simp [hG G.1 hr]
  ·
    intro s hsP
    unfold commonExcess
    congr 1
    funext G
    by_cases hr : ratDiv P f g G.1 = 0
    · simp [hr]
    · rcases hterm s G.1 hr with h1 | h1
      · rw [h1]
      · exact absurd h1 hsP

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagBundleSectionDiv
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section


open Classical in
def FlagBundleSectionDiv.Statement : Prop :=
  ∀ (F : Type) [Field F] (Ω : Type) [Field Ω] [Algebra F Ω]
    (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (y : (Σ k, ι k) → Ω) (e : ℕ),
    IsMultiProjPrime (pointIdeal F y) →
    ringKrullDim (MRing ι F ⧸ pointIdeal F y) = ((e + Fintype.card K : ℕ) : WithBot ℕ∞) →
    ∀ (N : ℕ) (E : Type) [AddCommGroup E] [Module Ω E]
      (B : ChartBundle F (segreVec y) N E) (w : Module.Basis (Fin N) Ω E) (b : Fin N → K → ℤ),
      IsFlagFrame y B w b →
    ∀ (M : ℕ) (a : K → ℤ) (φ : Fin M → Module.Dual Ω E), IsTwistedDualGens y B a φ →
    ∀ (Φ : Type) [Field Φ] [Algebra Ω Φ] (t : Fin N → Φ), AlgebraicIndependent Ω t →
    ∀ i : Fin N, 1 ≤ (i : ℕ) →
    ∀ (bf bg : Option K → ℕ) (f g : MRing (bundleIdx ι M) F),
      IsMultiHomog f bf → IsMultiHomog g bg →
      (fun o => (bf o : ℤ) - bg o) = zetaDeg + liftDeg (b i - a) →
      g ∉ projIdeal F y w φ (truncCoord t ((i : ℕ) + 1)) →
      eval₂ ((algebraMap Ω Φ).comp (algebraMap F Ω)) (projCoord y w φ (truncCoord t ((i : ℕ) + 1))) f =
        t i * eval₂ ((algebraMap Ω Φ).comp (algebraMap F Ω))
          (projCoord y w φ (truncCoord t ((i : ℕ) + 1))) g →
      ∀ W : Ideal (MRing (bundleIdx ι M) F),
        ratDiv (projIdeal F y w φ (truncCoord t ((i : ℕ) + 1))) f g W =
          if W = projIdeal F y w φ (truncCoord t i) then 1 else 0

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.BlowUpPushHypothesesExample
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

section Lemmas

def BlowUpVerticalPush.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (J : Type) [Fintype J] (P : Ideal (MRing ι O)) (n : ℕ), IsModelOver P n →
    ∀ (N : K → ℕ) (u : J → MRing ι O), (∀ j, IsMultiHomog (u j) N) → (∃ j, u j ∉ P) →
    ∀ (c : K → ℕ) (x : MRing ι O), IsMultiHomog x c → x ∉ P →
    ∀ a : Fin n → K → ℤ,
      (open Classical in
        cycEval (fun W => if (C ϖ : MRing (extIdx ι J) O) ∈ W then vNum W (liftDegs a) else 0)
          (divCycle (blowUpOf P u) (liftForm x))) =
      (open Classical in
        cycEval (fun W => if (C ϖ : MRing ι O) ∈ W then vNum W a else 0) (divCycle P x))

def BlowUpDivisorPush.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (J : Type) [Fintype J] (P : Ideal (MRing ι O)) (n : ℕ), IsModelOver P n →
    ∀ (b : K → ℤ) (f g : MRing ι O), IsVerticalDivisor P ϖ b f g →
    ∀ (N : K → ℕ) (u : J → MRing ι O), (∀ j, IsMultiHomog (u j) N) → (∃ j, u j ∉ P) →
    ∀ a : Fin n → K → ℤ,
      cycEval (fun G => vNum G (liftDegs a)) (ratDiv (blowUpOf P u) (liftForm (J := J) f) (liftForm g)) =
        cycEval (fun G => vNum G a) (ratDiv P f g)

def BlowUpHorizontalCorresp.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (J : Type) [Fintype J] (P : Ideal (MRing ι O)) (n : ℕ), IsModelOver P n →
    ∀ (N : K → ℕ) (u : J → MRing ι O), (∀ j, IsMultiHomog (u j) N) → (∃ j, u j ∉ P) →
    (∀ W : Ideal (MRing ι O), W.IsPrime → P ≤ W → IsRelevant W → (C ϖ : MRing ι O) ∉ W →
      ∃ j, ∀ j', ∃ v w : MRing ι O, v ∉ W ∧ v * u j' - w * u j ∈ P) →
    ∀ (c : K → ℕ) (x : MRing ι O), IsMultiHomog x c → x ∉ P →
    (∀ h : Ideal (MRing ι O) → ℤ,
      (open Classical in
        cycEval (fun W => if (C ϖ : MRing (extIdx ι J) O) ∈ W then 0
            else h (W.comap (liftForm (ι := ι) (J := J) (R := O))))
          (divCycle (blowUpOf P u) (liftForm x))) =
      (open Classical in
        cycEval (fun W => if (C ϖ : MRing ι O) ∈ W then 0 else h W) (divCycle P x))) ∧
    ∀ W : Ideal (MRing (extIdx ι J) O), divCycle (blowUpOf P u) (liftForm x) W ≠ 0 →
      (C ϖ : MRing (extIdx ι J) O) ∉ W →
      divCycle P x (W.comap (liftForm (ι := ι) (J := J) (R := O))) ≠ 0 ∧
      ((∃ j, u j ∉ W.comap (liftForm (ι := ι) (J := J) (R := O))) →
        W = blowUpOf (W.comap (liftForm (ι := ι) (J := J) (R := O))) u)

def HorizontalComponentModel.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P (d + 1) →
    ∀ (c : K → ℕ) (x : MRing ι O), IsMultiHomog x c → x ∉ P →
    ∀ W : Ideal (MRing ι O), divCycle P x W ≠ 0 → (C ϖ : MRing ι O) ∉ W → IsModelOver W d

end Lemmas

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PConeTrdegFnField
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRingOver)
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mcMap mcIdeal fnField)

noncomputable section

theorem ConeTrdegFnField.trdeg_eq_of_le_of_isAlgebraic {O B : Type} [CommRing O] [IsDomain O] [CommRing B]
    [IsDomain B] [Algebra O B] (hinj : Function.Injective (algebraMap O B)) {S T : Subalgebra O B}
    (hST : S ≤ T) (halg : ∀ t ∈ T, IsAlgebraic S t) : Algebra.trdeg O S = Algebra.trdeg O T := by
  let _ : Algebra S T := (Subalgebra.inclusion hST).toRingHom.toAlgebra
  have _ : IsScalarTower O S T := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have _ : FaithfulSMul O S :=
    (faithfulSMul_iff_algebraMap_injective O S).2 fun a b h => hinj (congrArg Subtype.val h)
  have _ : FaithfulSMul S T :=
    (faithfulSMul_iff_algebraMap_injective S T).2 (Subalgebra.inclusion_injective hST)
  let f : T →ₐ[S] B := { T.val.toRingHom with commutes' := fun _ => rfl }
  have _ : Algebra.IsAlgebraic S T :=
    ⟨fun t => (isAlgebraic_algHom_iff f Subtype.val_injective).1 (halg t t.2)⟩
  have h := trdeg_add_eq O S (A := T)
  rw [trdeg_eq_zero (R := S) (A := T), add_zero] at h
  exact h

section Cone

variable {O : Type} [CommRing O] {Ω : Type} [Field Ω] [Algebra O Ω]
variable {K : Type} {ι : K → Type}

theorem ConeTrdegFnField.mem_fnField_of_mem_adjoin (y : (Σ k, ι k) → Ω) {a : Ω}
    (ha : a ∈ Algebra.adjoin O (fnField O y : Set Ω)) : a ∈ fnField O y := by
  induction ha using Algebra.adjoin_induction with
  | mem x hx => exact hx
  | algebraMap r => exact Subfield.subset_closure (Or.inl ⟨r, rfl⟩)
  | add x z _ _ hx hz => exact add_mem hx hz
  | mul x z _ _ hx hz => exact mul_mem hx hz

def ConeTrdegFnField.coneMap (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) :
    MvPolynomial K (Algebra.adjoin O (fnField O y : Set Ω)) →ₐ[O] MvPolynomial K Ω :=
  ((aeval fun k => C (y ⟨k, c k⟩) * X k : MvPolynomial K Ω →ₐ[Ω] MvPolynomial K Ω).restrictScalars O).comp
    (MvPolynomial.mapAlgHom (Algebra.adjoin O (fnField O y : Set Ω)).val)

theorem ConeTrdegFnField.coneMap_C (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k)
    (a : Algebra.adjoin O (fnField O y : Set Ω)) :
    ConeTrdegFnField.coneMap y c (C a) = C (a : Ω) := by
  simp [ConeTrdegFnField.coneMap]

theorem ConeTrdegFnField.coneMap_X (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (k : K) :
    ConeTrdegFnField.coneMap (O := O) y c (X k) = C (y ⟨k, c k⟩) * X k := by
  simp [ConeTrdegFnField.coneMap]

theorem ConeTrdegFnField.mcMap_X (y : (Σ k, ι k) → Ω) (p : Σ k, ι k) :
    mcMap O y (X p) = C (y p) * X p.1 := by
  simp [mcMap]

theorem ConeTrdegFnField.coneMap_injective (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) :
    Function.Injective (ConeTrdegFnField.coneMap (O := O) y c) := by
  let ψ : MvPolynomial K Ω →ₐ[Ω] MvPolynomial K Ω := aeval fun k => C (y ⟨k, c k⟩) * X k
  let ψ' : MvPolynomial K Ω →ₐ[Ω] MvPolynomial K Ω := aeval fun k => C (y ⟨k, c k⟩)⁻¹ * X k
  have hinv : ψ'.comp ψ = AlgHom.id Ω _ := by
    refine MvPolynomial.algHom_ext fun k => ?_
    simp only [ψ, ψ', AlgHom.comp_apply, aeval_X, map_mul, aeval_C, AlgHom.id_apply,
      MvPolynomial.algebraMap_eq]
    rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ (hc k), map_one, one_mul]
  have hψ : Function.Injective ψ := Function.LeftInverse.injective (g := ψ') fun p => by
    rw [← AlgHom.comp_apply, hinv, AlgHom.id_apply]
  exact hψ.comp (MvPolynomial.map_injective _ Subtype.val_injective)

end Cone

theorem ConeTrdegFnField.proof : ConeTrdegFnField.Statement := by
  intro O _ _ Ω _ _ hinj K _ ι _ y hy
  choose c hc using hy
  set F₀ := Algebra.adjoin O (fnField O y : Set Ω)
  have hF : ∀ w ∈ fnField O y, w ∈ F₀ := fun w hw => Algebra.subset_adjoin hw
  have hu : ∀ p : Σ k, ι k, y p / y ⟨p.1, c p.1⟩ ∈ F₀ := fun p =>
    hF _ (Subfield.subset_closure (Or.inr ⟨⟨p.1, (p.2, c p.1)⟩, rfl⟩))

  let ρ : MRingOver O ι →ₐ[O] MvPolynomial K F₀ := aeval fun p => C (⟨_, hu p⟩ : F₀) * X p.1
  have hfac : mcMap O y = (ConeTrdegFnField.coneMap (O := O) y c).comp ρ := by
    refine MvPolynomial.algHom_ext fun p => ?_
    rw [ConeTrdegFnField.mcMap_X, AlgHom.comp_apply, aeval_X, map_mul, ConeTrdegFnField.coneMap_C,
      ConeTrdegFnField.coneMap_X, ← mul_assoc, ← map_mul]
    simp only [div_mul_cancel₀ _ (hc p.1)]
  set R := (mcMap O y).range
  have hle : R ≤ (ConeTrdegFnField.coneMap (O := O) y c).range := by
    show (mcMap O y).range ≤ _
    rw [hfac]; exact AlgHom.range_comp_le_range _ _
  have hXR : ∀ p : Σ k, ι k, (C (y p) * X p.1 : MvPolynomial K Ω) ∈ R := fun p =>
    ⟨X p, ConeTrdegFnField.mcMap_X y p⟩

  have halgC : ∀ w ∈ fnField O y, IsAlgebraic R (C w : MvPolynomial K Ω) := by
    intro w hw
    induction hw using Subfield.closure_induction with
    | mem x hx =>
      rcases hx with ⟨r, rfl⟩ | ⟨q, rfl⟩
      · have e : (C (algebraMap O Ω r) : MvPolynomial K Ω) = algebraMap O (MvPolynomial K Ω) r := by
          rw [MvPolynomial.algebraMap_apply]
        rw [e]
        exact isAlgebraic_algebraMap (⟨_, R.algebraMap_mem r⟩ : R)
      · dsimp only
        by_cases h0 : y ⟨q.1, q.2.2⟩ = 0
        · rw [h0, div_zero, map_zero]; exact isAlgebraic_zero
        · refine IsAlgebraic.of_mul (y := C (y ⟨q.1, q.2.2⟩) * X q.1)
            (mem_nonZeroDivisors_of_ne_zero (mul_ne_zero (C_ne_zero.2 h0) (X_ne_zero _)))
            (isAlgebraic_algebraMap (⟨_, hXR ⟨q.1, q.2.2⟩⟩ : R)) ?_
          have e : (C (y ⟨q.1, q.2.2⟩) * X q.1 : MvPolynomial K Ω) * C (y ⟨q.1, q.2.1⟩ / y ⟨q.1, q.2.2⟩) =
              C (y ⟨q.1, q.2.1⟩) * X q.1 := by
            rw [mul_comm, ← mul_assoc, ← map_mul, div_mul_cancel₀ _ h0]
          rw [e]
          exact isAlgebraic_algebraMap (⟨_, hXR ⟨q.1, q.2.1⟩⟩ : R)
    | one => rw [map_one]; exact isAlgebraic_one
    | add x z _ _ hx hz => rw [map_add (f := _)]; exact hx.add hz
    | neg x _ hx => rw [map_neg]; exact hx.neg
    | inv x _ hx =>
      by_cases h0 : x = 0
      · rw [h0, inv_zero, map_zero]; exact isAlgebraic_zero
      · refine IsAlgebraic.of_mul (y := C x) (mem_nonZeroDivisors_of_ne_zero (C_ne_zero.2 h0)) hx ?_
        rw [← map_mul, mul_inv_cancel₀ h0, map_one]; exact isAlgebraic_one
    | mul x z _ _ hx hz => rw [map_mul]; exact hx.mul hz
  have halg : ∀ t ∈ (ConeTrdegFnField.coneMap (O := O) y c).range, IsAlgebraic R t := by
    rintro _ ⟨q, rfl⟩
    change IsAlgebraic R (ConeTrdegFnField.coneMap (O := O) y c q)
    induction q using MvPolynomial.induction_on with
    | C a =>
      rw [ConeTrdegFnField.coneMap_C]
      exact halgC a (ConeTrdegFnField.mem_fnField_of_mem_adjoin y a.2)
    | add p q hp hq => rw [map_add (f := _)]; exact hp.add hq
    | mul_X p k hp =>
      rw [map_mul, ConeTrdegFnField.coneMap_X]
      exact hp.mul (isAlgebraic_algebraMap (⟨_, hXR ⟨k, c k⟩⟩ : R))
  have hinjP : Function.Injective (algebraMap O (MvPolynomial K Ω)) := by
    rw [IsScalarTower.algebraMap_eq O Ω (MvPolynomial K Ω)]
    exact (C_injective K Ω).comp hinj
  have h1 : Algebra.trdeg O (MRingOver O ι ⧸ mcIdeal O y) = Algebra.trdeg O R :=
    (Ideal.quotientKerEquivRange (mcMap O y)).trdeg_eq
  have h2 : Algebra.trdeg O (ConeTrdegFnField.coneMap (O := O) y c).range = Algebra.trdeg O (MvPolynomial K F₀) :=
    (AlgEquiv.ofInjective (ConeTrdegFnField.coneMap (O := O) y c)
      (ConeTrdegFnField.coneMap_injective y c hc)).trdeg_eq.symm
  have _ : FaithfulSMul O F₀ :=
    (faithfulSMul_iff_algebraMap_injective O F₀).2 fun a b h => hinj (congrArg Subtype.val h)
  have _ : FaithfulSMul F₀ (MvPolynomial K F₀) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (C_injective K _)
  have h3 : Algebra.trdeg O (MvPolynomial K F₀) = Algebra.trdeg O F₀ + Fintype.card K := by
    rw [← trdeg_add_eq O F₀ (A := MvPolynomial K F₀), MvPolynomial.trdeg_of_isDomain, Cardinal.lift_id,
      Cardinal.mk_fintype]
  rw [h1, ConeTrdegFnField.trdeg_eq_of_le_of_isAlgebraic hinjP hle halg, h2, h3]

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsSpanBundleDim
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def SpanBundleDim.Statement : Prop :=
  ∀ (F : Type) [Field F] (Ω : Type) [Field Ω] [Algebra F Ω]
    (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (y : (Σ k, ι k) → Ω) (e : ℕ),
    IsMultiProjPrime (pointIdeal F y) →
    ringKrullDim (MRing ι F ⧸ pointIdeal F y) = ((e + Fintype.card K : ℕ) : WithBot ℕ∞) →
    ∀ (M i : ℕ) (G : Fin M → Fin i → Ω), 0 < i → LinearIndependent Ω (fun j l => G l j) →
    ∀ (c : ∀ k, ι k) (a : K → ℤ) (H : Matrix (Fin i) (Fin i) Ω), segreVec y c ≠ 0 → IsUnit H.det →
      (∀ l m, (Matrix.of G * H) l m ∈ degLat F y a c) →
    ∀ (Φ : Type) [Field Φ] [Algebra Ω Φ] (s : Fin i → Φ), AlgebraicIndependent Ω s →
      IsMultiProjPrime (projIdeal F y (Pi.basisFun Ω (Fin i))
          (fun l => LinearMap.proj l ∘ₗ (Matrix.of G).mulVecLin) s) ∧
        FieldNumbers.relDim (projIdeal F y (Pi.basisFun Ω (Fin i))
          (fun l => LinearMap.proj l ∘ₗ (Matrix.of G).mulVecLin) s) =
          ((e + i - 1 : ℕ) : WithBot (WithTop ℤ))

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.LocCycle
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

section Defs

variable {R : Type*} [CommRing R]


open scoped Classical in
open Classical in
def locCycle (J W : Ideal R) : ℤ :=
  if h : W ∈ J.minimalPrimes then
    haveI : W.IsPrime := h.1.1
    ((Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (R ⧸ J))).toNat : ℤ)
  else 0

end Defs

section Lemmas

def LeftTermSupport.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O)
    (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι O)), IsMultiHomogIdeal P →
    ∀ (b : K → ℤ) (f g : MRing ι O), IsVerticalDivisor P ϖ b f g →
    ∀ (c : K → ℕ) (s : MRing ι O), IsMultiHomog s c →
    ∀ G U : Ideal (MRing ι O),
      ¬ (U.IsPrime ∧ IsMultiHomogIdeal U ∧ IsRelevant U ∧ (C ϖ : MRing ι O) ∈ U ∧ P ≤ U) →
      ratDiv P f g G * divCycle G s U = 0

def RightTermSupport.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O)
    (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι O)), IsMultiHomogIdeal P →
    ∀ (b : K → ℤ) (f g : MRing ι O), IsEffectiveVertical P ϖ b f g →
    ∀ (c : K → ℕ) (s : MRing ι O), IsMultiHomog s c →
    (∀ H, divCycle P s H ≠ 0 → (C ϖ : MRing ι O) ∉ H → IsVerticalDivisor H ϖ b f g) →
    ∀ W U : Ideal (MRing ι O),
      ¬ (U.IsPrime ∧ IsMultiHomogIdeal U ∧ IsRelevant U ∧ (C ϖ : MRing ι O) ∈ U ∧ P ≤ U) →
      divCycle P s W * idealCycle (W ⊔ divisorIdeal P f g) U = 0

def LocalCoeffRing.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] (P U : Ideal R), P.IsPrime → U.IsPrime → P ≤ U →
    (∀ Q₁ Q₂ : Ideal R, Q₁.IsPrime → Q₂.IsPrime → P < Q₁ → Q₁ < Q₂ → Q₂ < U → False) →
    ∀ f g s u v : R, f ∉ P → g ∉ P → s ∉ P → u ∉ U → u * f - v * g ∈ P →
    (∀ W : Ideal R, W ≤ U → locCycle (P ⊔ Ideal.span {s}) W ≠ 0 →
      locCycle (P ⊔ Ideal.span {f}) W = locCycle (P ⊔ Ideal.span {g}) W) →
    ∑ᶠ G, (locCycle (P ⊔ Ideal.span {f}) G - locCycle (P ⊔ Ideal.span {g}) G) *
        locCycle (G ⊔ Ideal.span {s}) U =
      ∑ᶠ W, locCycle (P ⊔ Ideal.span {s}) W *
        locCycle (W ⊔ (P ⊔ Ideal.span {f}).colon {g}) U

end Lemmas

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PVerticalDivisorJoinPullback
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

section JoinPullback

variable {K K' : Type} {ι : K → Type} {ι' : K' → Type}

theorem joinCoords_inl {Ω : Type*} [Field Ω] (y : (Σ k, ι k) → Ω) (y' : (Σ k, ι' k) → Ω) (k : K)
    (i : ι k) : joinCoords y y' ⟨Sum.inl k, i⟩ = y ⟨k, i⟩ := rfl

theorem pointConeMap_joinCoords_joinForm {Ω : Type*} [Field Ω] (R : Type*) [CommRing R]
    [Algebra R Ω] (y : (Σ k, ι k) → Ω) (y' : (Σ k, ι' k) → Ω) (f : MRing ι R) :
    pointConeMap R (joinCoords y y') (joinForm f) =
      rename (Sum.inl : K → K ⊕ K') (pointConeMap R y f) := by
  simp only [pointConeMap, joinForm, aeval_rename]
  induction f using MvPolynomial.induction_on with
  | C a => simp [algebraMap_eq]
  | add p q hp hq => simp [hp, hq]
  | mul_X p v hp =>
    obtain ⟨k, i⟩ := v
    simp [hp, joinCoords_inl]

theorem joinForm_mem_pointIdeal_iff {Ω : Type*} [Field Ω] (R : Type*) [CommRing R] [Algebra R Ω]
    (y : (Σ k, ι k) → Ω) (y' : (Σ k, ι' k) → Ω) (f : MRing ι R) :
    joinForm f ∈ pointIdeal R (joinCoords y y') ↔ f ∈ pointIdeal R y := by
  simp only [pointIdeal, RingHom.mem_ker, pointConeMap_joinCoords_joinForm]
  exact map_eq_zero_iff _ (rename_injective _ Sum.inl_injective)

theorem isMultiHomog_joinForm [DecidableEq K] [DecidableEq K'] {R : Type*} [CommRing R]
    {f : MRing ι R} {bf : K → ℕ} (hf : IsMultiHomog f bf) :
    IsMultiHomog (joinForm (ι' := ι') f) (Sum.elim bf 0) := by
  unfold IsMultiHomog at hf ⊢
  induction hf using IsWeightedHomogeneous.induction_on with
  | zero => simpa [joinForm] using isWeightedHomogeneous_zero R _ _
  | add p q hp hq ihp ihq => simpa [joinForm, map_add (f := _)] using ihp.add ihq
  | monomial d r hr =>
    simp only [joinForm, rename_monomial]
    apply isWeightedHomogeneous_monomial
    subst hr
    rw [Finsupp.weight_apply, Finsupp.sum_mapDomain_index (by simp) (by intros; simp [add_smul]),
      Finsupp.weight_apply]
    funext s
    simp only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply, blockWeight]
    rcases s with k | k
    · simp [Pi.single_apply]
    · simp

end JoinPullback

theorem VerticalDivisorJoinPullback.proof : VerticalDivisorJoinPullback.Statement := by
  intro O _ _ _ ϖ Ω _ _ K _ _ ι _ K' _ _ ι' _ y y' b f g hD
  refine IsVerticalDivisor.of_unit_off_special ?_ ?_ ?_ ?_
  · obtain ⟨bf, bg, hf, hg, hb⟩ := hD.degrees
    refine ⟨Sum.elim bf 0, Sum.elim bg 0, isMultiHomog_joinForm hf, isMultiHomog_joinForm hg, ?_⟩
    funext s
    rcases s with k | k
    · simp [joinDeg, ← hb]
    · simp [joinDeg]
  · rw [joinForm_mem_pointIdeal_iff]; exact hD.num_not_mem
  · rw [joinForm_mem_pointIdeal_iff]; exact hD.den_not_mem
  · intro W hW hPW hrel hϖ
    let φ : MRing ι O →ₐ[O] MRing (Sum.elim ι ι') O :=
      rename (fun p : (Σ k, ι k) => (⟨Sum.inl p.1, p.2⟩ : Σ s : K ⊕ K', Sum.elim ι ι' s))
    have hφ : ∀ h, joinForm (ι' := ι') h = φ h := fun _ => rfl
    have hle : pointIdeal O y ≤ W.comap φ := by
      intro h hh
      rw [Ideal.mem_comap, ← hφ]
      exact hPW ((joinForm_mem_pointIdeal_iff O y y' h).mpr hh)
    have hrel' : IsRelevant (W.comap φ) := by
      intro k
      obtain ⟨i, hi⟩ := hrel (Sum.inl k)
      exact ⟨i, by rw [Ideal.mem_comap]; simpa [φ, rename_X] using hi⟩
    have hϖ' : (C ϖ : MRing ι O) ∉ W.comap φ := by
      rw [Ideal.mem_comap]; simpa [φ, rename_C] using hϖ
    obtain ⟨u, v, hu, hv, huv⟩ :=
      hD.unit_off_special (W.comap φ) (Ideal.comap_isPrime φ W) hle hrel' hϖ'
    refine ⟨joinForm u, joinForm v, hu, hv, ?_⟩
    have := (joinForm_mem_pointIdeal_iff O y y' _).mpr huv
    simpa [hφ, map_sub, map_mul] using this

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end
