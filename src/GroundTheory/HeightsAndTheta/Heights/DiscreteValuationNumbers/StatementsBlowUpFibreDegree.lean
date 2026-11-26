module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PFlagIndependence
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ClassListMapDomainPerm

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBlowUpFibreDegree
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

section Objects

variable {K : Type} [DecidableEq K] {ι : K → Type} {J : Type}
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]


open Classical in
def specialRelDeg (W' : Ideal (MRing (extIdx ι J) O)) : ℕ :=
  if h : (specialIdeal W').IsPrime then
    haveI := h
    FieldNumbers.relDeg Function.Embedding.some (specialIdeal W')
  else 0

end Objects

section Lemmas

def BlowUpFibreDegree.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (J : Type) [Fintype J] (P : Ideal (MRing ι O)) (n : ℕ), IsModelOver P n →
    ∀ (N : K → ℕ) (u : J → MRing ι O), (∀ j, IsMultiHomog (u j) N) → (∃ j, u j ∉ P) →
    ∀ (c : K → ℕ) (x : MRing ι O), IsMultiHomog x c → x ∉ P →
    ∀ W : Ideal (MRing ι O), (C ϖ : MRing ι O) ∈ W → divCycle P x W ≠ 0 →
      (open Classical in
        ∑ᶠ W' : Ideal (MRing (extIdx ι J) O),
          if W'.comap (liftForm (ι := ι) (J := J) (R := O)) = W then
            divCycle (blowUpOf P u) (liftForm x) W' * (specialRelDeg W' : ℤ)
          else 0) =
        divCycle P x W

end Lemmas

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PLocalQuotPrimes
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

universe u

theorem LocalQuotPrimes.proof : LocalQuotPrimes.Statement.{u} := by
  intro R _ P U _ hPU
  let S := Localization.AtPrime U
  let PS : Ideal S := P.map (algebraMap R S)
  have hsurj : Function.Surjective (Ideal.Quotient.mk PS) := Ideal.Quotient.mk_surjective
  have hmap : ∀ I : Ideal R,
      I.map (localQuotMap P U) = (I.map (algebraMap R S)).map (Ideal.Quotient.mk PS) := by
    intro I
    rw [Ideal.map_map]
    rfl
  have hcomap : ∀ J : Ideal (localQuot P U),
      J.comap (localQuotMap P U) = (J.comap (Ideal.Quotient.mk PS)).comap (algebraMap R S) := by
    intro J
    rw [Ideal.comap_comap]
    rfl
  refine ⟨fun W hW hPW hWU => ?_, fun p hp => ?_⟩
  · have hdisj : Disjoint (U.primeCompl : Set R) W := by
      rw [Set.disjoint_left]
      intro x hx hxW
      exact hx (hWU hxW)
    have hWS : (W.map (algebraMap R S)).IsPrime :=
      IsLocalization.isPrime_of_isPrime_disjoint U.primeCompl S W hW hdisj
    have hWSc : (W.map (algebraMap R S)).comap (algebraMap R S) = W :=
      IsLocalization.under_map_of_isPrime_disjoint U.primeCompl S hW hdisj
    have hker : RingHom.ker (Ideal.Quotient.mk PS) ≤ W.map (algebraMap R S) := by
      rw [Ideal.mk_ker]
      exact Ideal.map_mono hPW
    refine ⟨?_, ?_⟩
    · rw [hmap]
      exact Ideal.map_isPrime_of_surjective hsurj hker
    · rw [hmap, hcomap, Ideal.comap_map_of_surjective _ hsurj, ← RingHom.ker_eq_comap_bot,
        sup_eq_left.mpr hker, hWSc]
  · let q : Ideal S := p.comap (Ideal.Quotient.mk PS)
    have hq : q.IsPrime := Ideal.comap_isPrime _ p
    have hq' := (IsLocalization.isPrime_iff_isPrime_disjoint U.primeCompl S q).mp hq
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      rw [Ideal.mem_comap]
      have h0 : localQuotMap P U x = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ hx)
      rw [h0]
      exact p.zero_mem
    · intro x hx
      by_contra hxU
      rw [hcomap] at hx
      exact Set.disjoint_left.mp hq'.2 (show x ∈ U.primeCompl from hxU) hx
    · rw [hmap, hcomap]
      have hloc : (q.comap (algebraMap R S)).map (algebraMap R S) = q :=
        IsLocalization.map_under U.primeCompl S q
      rw [hloc]
      exact Ideal.map_comap_of_surjective _ hsurj p

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinPlainPairNum
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

namespace plainPairNumber

section ClassNum

variable {K : Type} [DecidableEq K] {ι : K → Type}
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem classNum_rename {σ τ : Type*} (e : σ → τ) (he : Function.Injective e) (cls : τ → K → ℤ)
    (H : MvPolynomial σ ℤ) (Q : List (K → ℤ)) (W : Ideal (MRing ι O)) :
    classNum cls (rename e H) Q W = classNum (cls ∘ e) H Q W := by
  classical
  unfold classNum
  rw [support_rename_of_injective he,
    Finset.sum_image fun a _ b _ h => Finsupp.mapDomain_injective he h]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [coeff_rename_mapDomain e he]
  congr 2
  unfold classList
  rw [← Finsupp.toMultiset_map, Multiset.map_map]

theorem classNum_eq_sum_of_subset {σ : Type*} (cls : σ → K → ℤ) (H : MvPolynomial σ ℤ)
    (Q : List (K → ℤ)) (W : Ideal (MRing ι O)) {S : Finset (σ →₀ ℕ)} (hS : H.support ⊆ S) :
    classNum cls H Q W = ∑ μ ∈ S, H.coeff μ * vNumL W (classList cls μ ++ Q) :=
  Finset.sum_subset hS fun μ _ hμ => by
    rw [mem_support_iff, not_not] at hμ
    rw [hμ, zero_mul]


omit [DecidableEq K] in
theorem classList_add_perm {σ : Type*} (cls : σ → K → ℤ) (μ ν : σ →₀ ℕ) :
    (classList cls (μ + ν)).Perm (classList cls μ ++ classList cls ν) := by
  rw [← Multiset.coe_eq_coe, ← Multiset.coe_add]
  simp only [classList, Multiset.coe_toList, map_add (f := _), Multiset.map_add (f := _)]


theorem classNum_mul_monomial {σ : Type*} [DecidableEq σ] (cls : σ → K → ℤ) (A : MvPolynomial σ ℤ)
    (t : σ →₀ ℕ) (Q : List (K → ℤ)) (W : Ideal (MRing ι O)) :
    classNum cls (A * monomial t 1) Q W = classNum cls A (classList cls t ++ Q) W := by
  have hsub : (A * monomial t 1).support ⊆ A.support.image (· + t) := by
    intro ν hν
    rw [mem_support_iff, coeff_mul_monomial'] at hν
    split_ifs at hν with hle
    · rw [mul_one] at hν
      exact Finset.mem_image.mpr ⟨ν - t, mem_support_iff.mpr hν, tsub_add_cancel_of_le hle⟩
    · exact absurd rfl hν
  rw [classNum_eq_sum_of_subset cls _ Q W hsub,
    Finset.sum_image fun a _ b _ h => add_right_cancel h]
  unfold classNum
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [coeff_mul_monomial, mul_one, ← List.append_assoc,
    FlagTypings.vNumL_perm W ((classList_add_perm cls μ t).append_right Q)]

end ClassNum

section DivDiff

def term {r : ℕ} (l : Fin r) (μ : Fin r →₀ ℕ) : MvPolynomial (Fin r ⊕ Fin r) ℤ :=
  (∏ j ∈ Finset.univ.filter (fun j => j < l), X (Sum.inr j) ^ μ j) *
    (∑ a ∈ Finset.range (μ l), X (Sum.inl l) ^ a * X (Sum.inr l) ^ (μ l - 1 - a)) *
    ∏ j ∈ Finset.univ.filter (fun j => l < j), X (Sum.inl j) ^ μ j

theorem rename_divDiff_eq_sum {r : ℕ} (l : Fin r) (G : MvPolynomial (Fin r) ℤ)
    {S : Finset (Fin r →₀ ℕ)} (hS : G.support ⊆ S) :
    rename finSumFinEquiv.symm (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.divDiff l G) =
      ∑ μ ∈ S, C (G.coeff μ) * term l μ := by
  unfold IndefiniteRowSideFullHecke.NumbersDVR.Bundles.divDiff
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, map_prod, map_pow, rename_X, rename_C,
    finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd]
  refine (Finset.sum_subset hS ?_).trans (Finset.sum_congr rfl fun μ _ => ?_)
  · intro μ _ hμ
    rw [mem_support_iff, not_not] at hμ
    simp [hμ]
  · unfold term
    ring

end DivDiff

end plainPairNumber

end GroundTheory.Heights₂.Heights.NumbersDVR
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PJoinVariety
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (ptIdx liftVar)

noncomputable section

namespace JoinVariety

variable {K : Type} {ι : K → Type}

def varEquiv : Option (Σ k, ι k) ≃ (Σ k : K ⊕ Unit, Sum.elim ι ptIdx k) where
  toFun
    | none => ⟨.inr (), (0 : Fin 1)⟩
    | some p => liftVar (ι := ι) ptIdx p
  invFun
    | ⟨.inl k, i⟩ => some ⟨k, i⟩
    | ⟨.inr _, _⟩ => none
  left_inv := by
    rintro (_ | ⟨k, i⟩) <;> rfl
  right_inv := by
    rintro ⟨(k | u), i⟩
    · rfl
    · cases u
      have : i = (0 : Fin 1) := Subsingleton.elim (α := Fin 1) _ _
      subst this
      rfl

theorem liftVar_injective : Function.Injective (liftVar (ι := ι) ptIdx) :=
  (varEquiv (ι := ι)).injective.comp (Option.some_injective _)

def retr (F : Type) [Field F] :
    MvPolynomial (Σ k : K ⊕ Unit, Sum.elim ι ptIdx k) F →ₐ[F] MvPolynomial (Σ k, ι k) F :=
  aeval fun t => match t with
    | ⟨.inl k, i⟩ => X ⟨k, i⟩
    | ⟨.inr _, _⟩ => 1

theorem retr_rename (F : Type) [Field F] (p : MvPolynomial (Σ k, ι k) F) :
    retr F (rename (liftVar (ι := ι) ptIdx) p) = p := by
  have : (retr F).comp (rename (liftVar (ι := ι) ptIdx)) = AlgHom.id F _ := by
    ext ⟨k, i⟩
    simp [retr, liftVar]
  exact congrArg (fun φ => φ p) this

end JoinVariety

open JoinVariety in
theorem JoinVariety.proof : JoinVariety.Statement := by
  intro F _ K _ ι _ V n hV
  obtain ⟨⟨hprime, ⟨S0, hS0, hspan⟩, hrel⟩, hdim⟩ := hV
  set V' := V.map (rename (liftVar (ι := ι) ptIdx))

  let Φ : Polynomial (MvPolynomial (Σ k, ι k) F) ≃ₐ[F] MvPolynomial (Σ k : K ⊕ Unit, Sum.elim ι ptIdx k) F :=
    (optionEquivLeft F (Σ k, ι k)).symm.trans (renameEquiv F varEquiv)
  have hΦC : (Φ : Polynomial (MvPolynomial (Σ k, ι k) F) →+* _).comp Polynomial.C =
      (rename (liftVar (ι := ι) ptIdx) : MvPolynomial (Σ k, ι k) F →ₐ[F] _).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      have h1 : (optionEquivLeft F (Σ k, ι k)).symm (Polynomial.C (C r)) = C r := by
        rw [AlgEquiv.symm_apply_eq]; simp
      show renameEquiv F varEquiv ((optionEquivLeft F (Σ k, ι k)).symm (Polynomial.C (C r))) = _
      rw [h1]
      simp
    · intro s
      have h1 : (optionEquivLeft F (Σ k, ι k)).symm (Polynomial.C (X s)) = X (some s) := by
        rw [AlgEquiv.symm_apply_eq]; simp
      show renameEquiv F varEquiv ((optionEquivLeft F (Σ k, ι k)).symm (Polynomial.C (X s))) = _
      rw [h1]
      simp [varEquiv]
  have hV' : V' = (V.map (Polynomial.C : MvPolynomial (Σ k, ι k) F →+* Polynomial (MvPolynomial (Σ k, ι k) F))).map (Φ : Polynomial (MvPolynomial (Σ k, ι k) F) →+* _) := by
    rw [Ideal.map_map, hΦC]
    rfl

  have hmem : ∀ y, y ∈ V' → retr F y ∈ V := by
    have : V' ≤ V.comap (retr F : _ →ₐ[F] MvPolynomial (Σ k, ι k) F).toRingHom := by
      rw [Ideal.map_le_iff_le_comap]
      intro v hv
      simpa [Ideal.mem_comap, retr_rename] using hv
    exact fun y hy => this hy
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · rw [hV']
    exact Ideal.map_isPrime_of_equiv _
  · refine ⟨rename (liftVar (ι := ι) ptIdx) '' S0, ?_, ?_⟩
    · rintro _ ⟨f, hf, rfl⟩
      obtain ⟨a, ha⟩ := hS0 f hf
      refine ⟨Sum.elim a 0, ?_⟩
      classical
      intro m hm k
      rw [support_rename_of_injective liftVar_injective] at hm
      obtain ⟨m0, hm0, rfl⟩ := Finset.mem_image.mp hm
      cases k with
      | inl k =>
        change ∑ i : ι k, (Finsupp.mapDomain (liftVar (ι := ι) ptIdx) m0)
          (liftVar (ι := ι) ptIdx ⟨k, i⟩) = a k
        simp only [Finsupp.mapDomain_apply_of_injective liftVar_injective]
        exact ha m0 hm0 k
      | inr u =>
        simp only [Sum.elim_inr, Pi.zero_apply]
        refine Finset.sum_eq_zero fun i _ => Finsupp.mapDomain_of_notMem_range _ _ ?_
        rintro ⟨p, hp⟩
        cases hp
    · change V.map _ = _
      rw [hspan, Ideal.map_span]
  · rintro (k | u)
    · obtain ⟨i, hi⟩ := hrel k
      refine ⟨i, fun h => hi ?_⟩
      have := hmem _ h
      simpa [retr] using this
    · refine ⟨(0 : Fin 1), fun h => hprime.ne_top ?_⟩
      have := hmem _ h
      rw [Ideal.eq_top_iff_one]
      simpa [retr] using this
  · have e1 : (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F (Sum.elim ι ptIdx) ⧸ V') ≃+*
        Polynomial (MvPolynomial (Σ k, ι k) F ⧸ V) :=
      (Ideal.quotientEquiv _ _ Φ.toRingEquiv hV').symm.trans
        (Ideal.polynomialQuotientEquivQuotientPolynomial V).symm
    refine (ringKrullDim_eq_of_ringEquiv
      (S := Polynomial (MvPolynomial (Σ k, ι k) F ⧸ V)) e1).trans ?_
    rw [Polynomial.ringKrullDim_of_isNoetherianRing]
    change ringKrullDim (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι ⧸ V) + 1 = _
    rw [hdim, Fintype.card_sum, Fintype.card_unit]
    norm_cast

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpHorizontalSat
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

noncomputable section

section Saturation

variable {K : Type*} {ι : K → Type} {J : Type} {R : Type*} [CommRing R]

theorem exists_pow_mul_mem_of_aeval_chartSubst_mem {P : Ideal (MRing ι R)} {u a : J → MRing ι R}
    {W : Ideal (MRing ι R)} (j₀ : J)
    (hrel : ∀ j, newVar j * liftForm (a j₀) - newVar j₀ * liftForm (a j) ∈ blowUpOf P u)
    {F : MRing (extIdx ι J) R}
    (hF : aeval (chartSubst a) F ∈ Ideal.map (Polynomial.C : MRing ι R →+* Polynomial (MRing ι R)) W) :
    ∃ n : ℕ, liftForm (a j₀ ^ n) * F ∈
      blowUpOf P u ⊔ Ideal.map (liftForm (J := J) : MRing ι R →ₐ[R] MRing (extIdx ι J) R) W := by
  set B' := blowUpOf P u ⊔ Ideal.map (liftForm (J := J) : MRing ι R →ₐ[R] MRing (extIdx ι J) R) W
  let π := Ideal.Quotient.mk B'
  let x₀ := π (liftForm (a j₀))
  let L := Localization.Away x₀
  let q : MRing (extIdx ι J) R →+* L := (algebraMap _ L).comp π
  let t : L := IsLocalization.Away.invSelf x₀
  have hinv : q (liftForm (a j₀)) * t = 1 := IsLocalization.Away.mul_invSelf x₀
  let ψ : Polynomial (MRing ι R) →+* L :=
    Polynomial.eval₂RingHom (q.comp (liftForm (J := J) : MRing ι R →ₐ[R] _).toRingHom) (q (newVar j₀) * t)
  have key : ψ.comp (aeval (R := R) (chartSubst a)).toRingHom = q := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [ψ]
    · rintro ⟨_ | k, i⟩
      · change J at i
        have hm : π (newVar i * liftForm (a j₀) - newVar j₀ * liftForm (a i)) = 0 :=
          Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_sup_left (hrel i))
        have h1 : q (newVar i * liftForm (a j₀) - newVar j₀ * liftForm (a i)) = 0 := by
          show algebraMap _ L (π _) = 0
          rw [hm, map_zero]
        rw [map_sub, map_mul, map_mul, sub_eq_zero] at h1
        simp only [ψ, chartSubst, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
          aeval_X, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_mul, Polynomial.eval₂_C,
          Polynomial.eval₂_X]
        change q (liftForm (a i)) * (q (newVar j₀) * t) = q (newVar i)
        linear_combination (-t) * h1 + q (newVar i) * hinv
      · simp [ψ, chartSubst, liftForm]
  have hle : Ideal.map (Polynomial.C : MRing ι R →+* Polynomial (MRing ι R)) W ≤ RingHom.ker ψ := by
    rw [Ideal.map_le_iff_le_comap]
    intro p hp
    rw [Ideal.mem_comap, RingHom.mem_ker]
    simp only [ψ, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, RingHom.comp_apply,
      AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, q]
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_sup_right (Ideal.mem_map_of_mem _ hp)), map_zero]
  have h2 := RingHom.mem_ker.mp (hle hF)
  have h3 := DFunLike.congr_fun key F
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] at h3
  rw [h3] at h2
  obtain ⟨⟨m, n, rfl⟩, hm⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers x₀) L (π F)).mp h2
  refine ⟨n, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul, map_pow, map_pow]
  exact hm

end Saturation

theorem BlowUpHorizontalSat.full : BlowUpHorizontalSat.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ J _ P n hP N u hu hex hloc c x hx hxP W hW hϖW F
  classical
  have hPp : P.IsPrime := hP.multiProj.isPrime

  have hWsupp : W ∈ (blowUpOf P u ⊔ Ideal.span {liftForm x}).minimalPrimes ∧ IsRelevant W := by
    by_contra h
    exact hW (by rw [divCycle, dif_neg h])
  obtain ⟨hmin, hWrel⟩ := hWsupp
  have hWp : W.IsPrime := hmin.1.1
  have hBW : blowUpOf P u ≤ W := le_sup_left.trans hmin.1.2
  set W₀ := W.comap (liftForm (ι := ι) (J := J) (R := O)) with hW₀
  obtain ⟨hW₀p, hPW₀, hrel₀, -⟩ := comap_liftForm_facts hWp hBW hWrel
  have hϖW₀ : (C ϖ : MRing ι O) ∉ W₀ := by rw [Ideal.mem_comap, liftForm_C]; exact hϖW
  obtain ⟨j₀, hj₀⟩ := hloc W₀ hW₀p hPW₀ hrel₀ hϖW₀
  choose v w hv hvw using hj₀

  have huj₀ : u j₀ ∉ P := by
    intro h
    obtain ⟨j, hj⟩ := hex
    have h1 : v j * u j ∈ P := by
      have := P.add_mem (hvw j) (P.mul_mem_left (w j) h)
      rwa [sub_add_cancel] at this
    exact hj ((hPp.mem_or_mem h1).resolve_left fun h' => hv j (hPW₀ h'))

  obtain ⟨u₀, a, hu₀W, hrelP⟩ : ∃ (u₀ : MRing ι O) (a : J → MRing ι O), u₀ ∉ W₀ ∧
      ∀ j, u₀ * u j - u j₀ * a j ∈ P := by
    have := hW₀p
    refine ⟨∏ j, v j, fun j => w j * ∏ j' ∈ Finset.univ.erase j, v j',
      fun h => W₀.primeCompl.prod_mem (fun j _ => hv j) h, fun j => ?_⟩
    have e : (∏ j, v j) * u j - u j₀ * (w j * ∏ j' ∈ Finset.univ.erase j, v j') =
        (∏ j' ∈ Finset.univ.erase j, v j') * (v j * u j - w j * u j₀) := by
      rw [← Finset.mul_prod_erase Finset.univ v (Finset.mem_univ j)]; ring
    rw [e]
    exact P.mul_mem_left _ (hvw j)
  have hu₀P : u₀ ∉ P := fun h => hu₀W (hPW₀ h)
  have ha₀ : a j₀ ∉ W₀ := by
    intro h
    have h1 : u j₀ * (u₀ - a j₀) ∈ P := by
      have := hrelP j₀
      rwa [show u₀ * u j₀ - u j₀ * a j₀ = u j₀ * (u₀ - a j₀) by ring] at this
    have h2 : u₀ - a j₀ ∈ W₀ := hPW₀ ((hPp.mem_or_mem h1).resolve_left huj₀)
    exact hu₀W (by simpa using W₀.add_mem h2 h)

  have hrelB : ∀ j, newVar j * liftForm (a j₀) - newVar j₀ * liftForm (a j) ∈ blowUpOf P u := by
    intro j
    apply mem_blowUpOf_of_sub
    have e : u₀ * (u j * a j₀ - u j₀ * a j) =
        a j₀ * (u₀ * u j - u j₀ * a j) - a j * (u₀ * u j₀ - u j₀ * a j₀) := by ring
    have h1 : u₀ * (u j * a j₀ - u j₀ * a j) ∈ P := by
      rw [e]; exact P.sub_mem (P.mul_mem_left _ (hrelP j)) (P.mul_mem_left _ (hrelP j₀))
    exact (hPp.mem_or_mem h1).resolve_left hu₀P

  have := hW₀p
  let Q' := (Ideal.map (Polynomial.C : MRing ι O →+* Polynomial (MRing ι O)) W₀).comap
    (aeval (R := O) (chartSubst a))
  have hQ'p : Q'.IsPrime := Ideal.comap_isPrime _ _
  have hxW : liftForm x ∈ W := hmin.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  have hBQ' : blowUpOf P u ⊔ Ideal.span {liftForm x} ≤ Q' := by
    refine sup_le (fun G hG => ?_) ((Ideal.span_singleton_le_iff_mem _).mpr ?_)
    · exact Ideal.map_mono hPW₀ (aeval_chartSubst_mem_of_mem_blowUpOf hPp huj₀ hrelP hG)
    · rw [Ideal.mem_comap, aeval_chartSubst_liftForm]
      exact Ideal.mem_map_of_mem _ hxW
  have hQ'W : Q' ≤ W := fun G hG =>
    mem_of_aeval_chartSubst_mem hWp le_rfl j₀ ha₀ (fun j => hBW (hrelB j)) hG
  have hWQ' : W ≤ Q' := hmin.2 ⟨hQ'p, hBQ'⟩ hQ'W
  constructor
  · intro hF
    obtain ⟨m, hm⟩ := exists_pow_mul_mem_of_aeval_chartSubst_mem j₀ hrelB (hWQ' hF)
    exact ⟨a j₀ ^ m, fun h => ha₀ (hW₀p.mem_of_pow_mem _ h), hm⟩
  · rintro ⟨s, hs, hsF⟩
    have h1 : liftForm s * F ∈ W := sup_le hBW Ideal.map_comap_le hsF
    exact (hWp.mem_or_mem h1).resolve_left hs

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSpanBundleTrdegGe
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

theorem SpanBundleTrdegGe.algebraicIndependent_linComb {Ω Φ : Type*} [Field Ω] [Field Φ] [Algebra Ω Φ]
    {i : ℕ} (s : Fin i → Φ) (hs : AlgebraicIndependent Ω s) (A : Matrix (Fin i) (Fin i) Ω)
    (hA : IsUnit A) : AlgebraicIndependent Ω (fun r => ∑ j, s j * algebraMap Ω Φ (A r j)) := by
  classical
  let L : Matrix (Fin i) (Fin i) Ω → MvPolynomial (Fin i) Ω →ₐ[Ω] MvPolynomial (Fin i) Ω :=
    fun B => aeval fun r => ∑ j, C (B r j) * X j
  have hcomp : ∀ B B', (L B').comp (L B) = L (B * B') := by
    intro B B'
    apply MvPolynomial.algHom_ext
    intro r
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [L, AlgHom.comp_apply, aeval_X, map_sum, map_mul, aeval_C, algebraMap_eq,
      Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul, mul_assoc]
    exact Finset.sum_comm
  have hid : L 1 = AlgHom.id Ω _ := by
    apply MvPolynomial.algHom_ext
    intro r
    simp [L, Matrix.one_apply]
  have heq : (aeval fun r => ∑ j, s j * algebraMap Ω Φ (A r j)) = (aeval s).comp (L A) := by
    apply MvPolynomial.algHom_ext
    intro r
    simp [L, mul_comm]
  have hAinv : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A ((Matrix.isUnit_iff_isUnit_det A).1 hA)
  have hinj : Function.Injective (L A) := Function.LeftInverse.injective (g := L A⁻¹) fun p => by
    rw [← AlgHom.comp_apply, hcomp, hAinv, hid, AlgHom.id_apply]
  rw [algebraicIndependent_iff_injective_aeval, heq]
  exact (algebraicIndependent_iff_injective_aeval.1 hs).comp hinj

theorem SpanBundleTrdegGe.injective_aeval_mul_X {Ω Φ : Type*} [Field Ω] [Field Φ] [Algebra Ω Φ] {i : ℕ}
    (σ : Fin i → Φ) (hσ : AlgebraicIndependent Ω σ) :
    Function.Injective (aeval (fun r => Polynomial.C (σ r) * Polynomial.X) :
      MvPolynomial (Fin i) Ω →ₐ[Ω] Polynomial Φ) := by
  let H : MvPolynomial (Fin i) Ω →ₐ[Ω] Polynomial (MvPolynomial (Fin i) Ω) :=
    aeval fun r => Polynomial.C (X r) * Polynomial.X
  have hH : Function.Injective H := by
    have h1 : ((Polynomial.aeval (1 : MvPolynomial (Fin i) Ω)).restrictScalars Ω).comp H =
        AlgHom.id Ω _ := by
      apply MvPolynomial.algHom_ext
      intro r
      simp [H]
    exact Function.LeftInverse.injective (g := (Polynomial.aeval (1 : MvPolynomial (Fin i) Ω)).restrictScalars Ω)
      fun p => by rw [← AlgHom.comp_apply, h1, AlgHom.id_apply]
  have heq : (aeval (fun r => Polynomial.C (σ r) * Polynomial.X) :
      MvPolynomial (Fin i) Ω →ₐ[Ω] Polynomial Φ) = (Polynomial.mapAlgHom (aeval σ)).comp H := by
    apply MvPolynomial.algHom_ext
    intro r
    simp [H]
  rw [heq]
  exact (Polynomial.map_injective _ (algebraicIndependent_iff_injective_aeval.1 hσ)).comp hH

theorem SpanBundleTrdegGe.exists_injective_cone {Ω Φ : Type*} [Field Ω] [Field Φ] [Algebra Ω Φ]
    (K : Type*) {i : ℕ} (σ : Fin i → Φ) (hσ : AlgebraicIndependent Ω σ) :
    ∃ Ψ : MvPolynomial (Fin i) (MvPolynomial K Ω) →+* MvPolynomial (Option K) Φ, Function.Injective Ψ ∧
      (∀ p, Ψ (C p) = rename some (map (algebraMap Ω Φ) p)) ∧ ∀ r, Ψ (X r) = C (σ r) * X none := by
  let θ : MvPolynomial (Fin i) Ω →+* Polynomial Φ :=
    (aeval (fun r => Polynomial.C (σ r) * Polynomial.X) :
      MvPolynomial (Fin i) Ω →ₐ[Ω] Polynomial Φ).toRingHom
  have hθ : Function.Injective θ := SpanBundleTrdegGe.injective_aeval_mul_X σ hσ
  let e := (optionEquivRight Φ K).symm
  have heC : ∀ a : Φ, e (C (Polynomial.C a)) = C a := fun a =>
    (AlgEquiv.symm_apply_eq _).2 (optionEquivRight_C Φ K a).symm
  have heX : ∀ k, e (X k) = X (some k) := fun k =>
    (AlgEquiv.symm_apply_eq _).2 (optionEquivRight_X_some Φ K k).symm
  have heN : e (C Polynomial.X) = X none :=
    (AlgEquiv.symm_apply_eq _).2 (optionEquivRight_X_none Φ K).symm
  refine ⟨e.toRingEquiv.toRingHom.comp ((map θ).comp (commAlgEquiv Ω (Fin i) K).toRingEquiv.toRingHom),
    e.injective.comp ((map_injective θ hθ).comp (commAlgEquiv Ω (Fin i) K).injective), ?_, ?_⟩
  · intro p
    induction p using MvPolynomial.induction_on with
    | C a =>
      have h1 : θ (C a) = Polynomial.C (algebraMap Ω Φ a) := by simp [θ]
      simp [h1, heC]
    | add p q hp hq => simp only [map_add (f := _), hp, hq]
    | mul_X p k hp =>
      rw [C_mul, map_mul, hp, map_mul, map_mul]
      have h2 : (e.toRingEquiv.toRingHom.comp ((map θ).comp (commAlgEquiv Ω (Fin i) K).toRingEquiv.toRingHom))
          (C (X k)) = X (some k) := by
        simp [heX]
      rw [h2, map_X, rename_X]
  · intro r
    have h3 : θ (X r) = Polynomial.C (σ r) * Polynomial.X := by simp [θ]
    have h4 : e (C (Polynomial.C (σ r) * Polynomial.X)) = C (σ r) * X none := by
      rw [C_mul, map_mul, heC, heN]
    simp [h3, heC, heN]

theorem SpanBundleTrdegGe.proof : SpanBundleTrdegGe.Statement := by
  intro F _ Ω _ _ K ι y M i G hG Φ _ _ s hs
  classical
  let : Algebra F Φ := ((algebraMap Ω Φ).comp (algebraMap F Ω)).toAlgebra
  have : IsScalarTower F Ω Φ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  set z := projCoord y (Pi.basisFun Ω (Fin i))
    (fun l => LinearMap.proj l ∘ₗ (Matrix.of G).mulVecLin) s with hz
  change Algebra.trdeg F (MRing ι F ⧸ pointIdeal F y) + i ≤
    Algebra.trdeg F (MRing (bundleIdx ι M) F ⧸ pointIdeal F z)
  have hzn : ∀ m, z ⟨none, m⟩ = ∑ j, s j * algebraMap Ω Φ (G m j) := by
    intro m
    simp [hz, projCoord, Matrix.col]
    rfl
  have hzs : ∀ k (q : ι k), z ⟨some k, q⟩ = algebraMap Ω Φ (y ⟨k, q⟩) := fun _ _ => rfl

  obtain ⟨l, hl⟩ : ∃ l : Fin i → Fin M, IsUnit (Matrix.of fun r j => G (l r) j) := by
    have hrk : (Matrix.of G).rank = i := by
      rw [← Matrix.rank_transpose]
      simpa using LinearIndependent.rank_matrix (M := Matrix.transpose (Matrix.of G)) hG
    obtain ⟨κ, a, -, hsp, hli⟩ := exists_linearIndependent' Ω (Matrix.of G).row
    have : Finite κ := hli.finite
    let : Fintype κ := Fintype.ofFinite κ
    have hcard : Fintype.card κ = i := by
      rw [← finrank_span_eq_card hli, hsp, ← Matrix.rank_eq_finrank_span_row, hrk]
    let e : Fin i ≃ κ := (Fintype.equivFinOfCardEq hcard).symm
    refine ⟨a ∘ e, Matrix.linearIndependent_rows_iff_isUnit.1 ?_⟩
    exact hli.comp e e.injective
  set σ : Fin i → Φ := fun r => ∑ j, s j * algebraMap Ω Φ (G (l r) j) with hσdef
  have hσ : AlgebraicIndependent Ω σ :=
    SpanBundleTrdegGe.algebraicIndependent_linComb s hs _ hl

  have : (pointIdeal F y).IsPrime := RingHom.ker_isPrime _
  have : (pointIdeal F z).IsPrime := RingHom.ker_isPrime _
  set Ay := MRing ι F ⧸ pointIdeal F y
  set Az := MRing (bundleIdx ι M) F ⧸ pointIdeal F z
  let qy : Ay →ₐ[F] MvPolynomial K Ω := Ideal.kerLiftAlg (pointConeMap F y)
  have hqy : Function.Injective qy := Ideal.kerLiftAlg_injective _
  let qz : Az →ₐ[F] MvPolynomial (Option K) Φ := Ideal.kerLiftAlg (pointConeMap F z)
  let emb : MvPolynomial K Ω →+* MvPolynomial (Option K) Φ :=
    (rename (R := Φ) some).toRingHom.comp (map (algebraMap Ω Φ))
  let σ' : (Σ k, ι k) → (Σ o, bundleIdx ι M o) := fun p => ⟨some p.1, p.2⟩
  have hE1 : ∀ g : MRing ι F, pointConeMap F z (rename σ' g) = emb (pointConeMap F y g) := by
    intro g
    induction g using MvPolynomial.induction_on with
    | C a => simp [pointConeMap, emb, MvPolynomial.algebraMap_eq, RingHom.algebraMap_toAlgebra]
    | add p q hp hq => simp only [map_add (f := _), hp, hq]
    | mul_X p q hp =>
      simp only [map_mul, hp, rename_X]
      simp [pointConeMap, emb, σ', hzs]
  have hle : pointIdeal F y ≤ (pointIdeal F z).comap (rename σ' : MRing ι F →ₐ[F] _) := by
    intro g hg
    simp only [Ideal.mem_comap, pointIdeal, RingHom.mem_ker] at hg ⊢
    rw [hE1, hg, map_zero]
  let fy : Ay →ₐ[F] Az := Ideal.quotientMapₐ (pointIdeal F z) (rename σ') hle
  let Θ : MvPolynomial (Fin i) Ay →ₐ[F] Az :=
    aevalTower fy fun r => Ideal.Quotient.mk _ (X ⟨none, l r⟩)

  obtain ⟨Ψ, hΨ, hΨC, hΨX⟩ := SpanBundleTrdegGe.exists_injective_cone K σ hσ
  have key : ∀ a, qz (Θ a) = Ψ (map qy.toRingHom a) := by
    intro a
    induction a using MvPolynomial.induction_on with
    | C c =>
      obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective c
      simp only [Θ, aevalTower_C, map_C]
      rw [hΨC]
      change qz (Ideal.Quotient.mk _ (rename σ' g)) = emb (qy (Ideal.Quotient.mk _ g))
      simp only [qz, qy]
      exact hE1 g
    | add p q hp hq =>
      rw [map_add Θ, map_add qz, (map qy.toRingHom : MvPolynomial (Fin i) Ay →+* _).map_add, map_add Ψ, hp, hq]
    | mul_X p r hp =>
      simp only [map_mul, hp, map_X, hΨX]
      congr 1
      simp only [Θ, aevalTower_X]
      refine (Ideal.kerLiftAlg_mk (pointConeMap F z) _).trans ?_
      simp only [pointConeMap, aeval_X]
      exact congrArg (fun a => C a * X none) (hzn (l r))
  have hΘ : Function.Injective Θ := by
    intro a b hab
    apply map_injective qy.toRingHom hqy
    apply hΨ
    rw [← key, ← key, hab]

  have : FaithfulSMul F Ay :=
    (faithfulSMul_iff_algebraMap_injective F Ay).2 (algebraMap F Ay).injective
  have : FaithfulSMul Ay (MvPolynomial (Fin i) Ay) :=
    (faithfulSMul_iff_algebraMap_injective Ay _).2 (C_injective _ _)
  have e1 := trdeg_add_eq F Ay (A := MvPolynomial (Fin i) Ay)
  rw [MvPolynomial.trdeg_of_isDomain, Cardinal.lift_id, Cardinal.mk_fin] at e1
  rw [e1]
  exact trdeg_le_of_injective Θ hΘ

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpVerticalPush
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

open Classical in
theorem BlowUpVerticalPush.proof (hfib : BlowUpVerticalFibre.Statement.{u}) :
    BlowUpVerticalPush.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ J _ P n hP N u hu hu' c x hx hxP a
  have hZ : (Function.support (divCycle (blowUpOf P u) (liftForm (J := J) x))).Finite :=
    DivCycleFiniteSupport.proof O (Option K) (extIdx ι J) _ _

  have hC : ∀ W' : Ideal (MRing (extIdx ι J) O), (C ϖ : MRing (extIdx ι J) O) ∈ W' ↔
      (C ϖ : MRing ι O) ∈ W'.comap (liftForm (ι := ι) (J := J) (R := O)) := by
    intro W'
    rw [Ideal.mem_comap]
    simp [liftForm]
  set g : Ideal (MRing (extIdx ι J) O) → ℤ := fun W' =>
    divCycle (blowUpOf P u) (liftForm x) W' *
      (if (C ϖ : MRing (extIdx ι J) O) ∈ W' then vNum W' (liftDegs a) else 0) with hg_def
  have hg : Function.support g ⊆ hZ.toFinset := fun W' hW' =>
    hZ.mem_toFinset.mpr (Function.support_mul_subset_left _ _ hW')

  have key : ∀ W : Ideal (MRing ι O),
      (∑ W' ∈ hZ.toFinset with W'.comap (liftForm (ι := ι) (J := J) (R := O)) = W, g W') =
        divCycle P x W * (if (C ϖ : MRing ι O) ∈ W then vNum W a else 0) := by
    intro W
    by_cases hW : (C ϖ : MRing ι O) ∈ W
    · rw [if_pos hW, ← hfib O ϖ hϖ K ι J P n hP N u hu hu' c x hx hxP a W hW,
        finsum_eq_sum_of_support_subset _ (s := hZ.toFinset), Finset.sum_filter]
      · refine Finset.sum_congr rfl fun W' _ => ?_
        by_cases h1 : W'.comap (liftForm (ι := ι) (J := J) (R := O)) = W
        · rw [if_pos h1, if_pos h1, hg_def]
          dsimp only
          rw [if_pos ((hC W').mpr (by rw [h1]; exact hW))]
        · rw [if_neg h1, if_neg h1]
      · intro W' hW'
        refine hZ.mem_toFinset.mpr ?_
        rw [Function.mem_support] at hW' ⊢
        intro h0
        apply hW'
        simp [h0]
    · rw [if_neg hW, mul_zero]
      refine Finset.sum_eq_zero fun W' hW' => ?_
      have h1 := (Finset.mem_filter.mp hW').2
      rw [hg_def]
      dsimp only
      rw [if_neg (fun h => hW (h1 ▸ (hC W').mp h)), mul_zero]
  unfold cycEval
  calc (∑ᶠ W', divCycle (blowUpOf P u) (liftForm x) W' *
          (if (C ϖ : MRing (extIdx ι J) O) ∈ W' then vNum W' (liftDegs a) else 0))
      = ∑ W' ∈ hZ.toFinset, g W' := finsum_eq_sum_of_support_subset g hg
    _ = ∑ᶠ W, ∑ W' ∈ hZ.toFinset with W'.comap (liftForm (ι := ι) (J := J) (R := O)) = W, g W' :=
        (finsum_sum_filter _ _ _).symm
    _ = _ := finsum_congr key

end GroundTheory.Heights₂.Heights.NumbersDVR
end
