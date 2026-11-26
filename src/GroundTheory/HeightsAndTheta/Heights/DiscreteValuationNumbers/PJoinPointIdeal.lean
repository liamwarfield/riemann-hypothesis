module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PNumericalSegre
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.SameGenericSymm

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PJoinPointIdeal
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (ptIdx ptCoord liftVar joinCoord mcIdeal mcMap)

namespace JoinPointIdeal

noncomputable section

variable {K : Type} {ι : K → Type}

def joinIdx : (Σ k : K ⊕ Unit, Sum.elim ι ptIdx k) ≃ Unit ⊕ (Σ k, ι k) where
  toFun
    | ⟨.inl k, i⟩ => .inr ⟨k, i⟩
    | ⟨.inr _, _⟩ => .inl ()
  invFun
    | .inr p => ⟨.inl p.1, p.2⟩
    | .inl _ => ⟨.inr (), (0 : Fin 1)⟩
  left_inv := by
    rintro ⟨(k | ⟨⟩), i⟩
    · rfl
    · show (⟨.inr (), (0 : Fin 1)⟩ : Σ k : K ⊕ Unit, Sum.elim ι ptIdx k) = ⟨.inr (), i⟩
      congr 1
      exact (Fin.fin_one_eq_zero i).symm
  right_inv := by
    rintro (⟨⟩ | p) <;> rfl

variable (R : Type) [CommRing R]

def srcEquiv : MvPolynomial (Σ k : K ⊕ Unit, Sum.elim ι ptIdx k) R ≃+*
    MvPolynomial Unit (MvPolynomial (Σ k, ι k) R) :=
  (renameEquiv R joinIdx).toRingEquiv.trans (sumRingEquiv R Unit (Σ k, ι k))

def tgtEquiv (Ω : Type) [CommRing Ω] : MvPolynomial (K ⊕ Unit) Ω ≃+* MvPolynomial Unit (MvPolynomial K Ω) :=
  (renameEquiv Ω (Equiv.sumComm K Unit)).toRingEquiv.trans (sumRingEquiv Ω Unit K)

variable (Ω : Type) [Field Ω] [Algebra R Ω]

theorem cone_comp (y : (Σ k, ι k) → Ω) :
    ((tgtEquiv (K := K) Ω : MvPolynomial (K ⊕ Unit) Ω →+* MvPolynomial Unit (MvPolynomial K Ω))).comp
        ((mcMap R (joinCoord y (ptCoord (Ω := Ω))) :
            MvPolynomial (Σ k : K ⊕ Unit, Sum.elim ι ptIdx k) R →ₐ[R] MvPolynomial (K ⊕ Unit) Ω) :
          MvPolynomial (Σ k : K ⊕ Unit, Sum.elim ι ptIdx k) R →+* MvPolynomial (K ⊕ Unit) Ω) =
      (MvPolynomial.map ((pointConeMap R y : MRing ι R →ₐ[R] MvPolynomial K Ω) : MRing ι R →+* _)).comp
        (srcEquiv (ι := ι) R :
          MvPolynomial (Σ k : K ⊕ Unit, Sum.elim ι ptIdx k) R →+* MvPolynomial Unit (MRing ι R)) := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [tgtEquiv, srcEquiv, mcMap, pointConeMap, MvPolynomial.algebraMap_eq]
  · rintro ⟨(k | ⟨⟩), i⟩
    · simp [tgtEquiv, srcEquiv, mcMap, pointConeMap, joinCoord, joinIdx]
    · simp [tgtEquiv, srcEquiv, mcMap, pointConeMap, joinCoord, joinIdx, ptCoord]

theorem rename_liftVar_eq :
    ((rename (liftVar (ι := ι) ptIdx) : MRing ι R →ₐ[R] MvPolynomial (Σ k : K ⊕ Unit, Sum.elim ι ptIdx k) R) :
        MRing ι R →+* MvPolynomial (Σ k : K ⊕ Unit, Sum.elim ι ptIdx k) R) =
      ((srcEquiv (ι := ι) R).symm : MvPolynomial Unit (MRing ι R) →+* _).comp
        (C : MRing ι R →+* MvPolynomial Unit (MRing ι R)) := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [srcEquiv]
  · intro p
    simp [srcEquiv, liftVar, joinIdx]

end

end JoinPointIdeal

theorem JoinPointIdeal.proof : JoinPointIdeal.Statement := by
  intro R _ Ω _ _ K _ ι _ y
  set φ : MRing ι R →+* MvPolynomial K Ω :=
    ((pointConeMap R y : MRing ι R →ₐ[R] MvPolynomial K Ω) : MRing ι R →+* MvPolynomial K Ω) with hφ
  have h1 : mcIdeal R (joinCoord y (ptCoord (Ω := Ω))) =
      Ideal.comap (JoinPointIdeal.srcEquiv (ι := ι) R :
          MvPolynomial (Σ k : K ⊕ Unit, Sum.elim ι ptIdx k) R →+* MvPolynomial Unit (MRing ι R))
        (RingHom.ker (MvPolynomial.map (σ := Unit) φ)) := by
    ext f
    have hc := RingHom.congr_fun (JoinPointIdeal.cone_comp R Ω y) f
    simp only [RingHom.comp_apply] at hc
    rw [Ideal.mem_comap, RingHom.mem_ker, ← hc]
    simp only [RingHom.coe_coe, EmbeddingLike.map_eq_zero_iff]
    exact RingHom.mem_ker
  rw [h1, pointIdeal, show RingHom.ker (pointConeMap R y) = RingHom.ker φ from rfl, ← Ideal.map_coe, JoinPointIdeal.rename_liftVar_eq, ← Ideal.map_map, Ideal.map_coe, Ideal.map_symm, ← MvPolynomial.ker_map]
  rfl

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PFlagBundleDim
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

theorem FlagBundleDim.proof (hspan : TwistedDualGensSpan.Statement)
    (hdim : SpanBundleDim.Statement) : FlagBundleDim.Statement := by
  intro F _ Ω _ _ K _ _ ι _ y e hV hdimV N E _ _ B w b hflag M a φ hφ Φ _ _ t ht i hi1 hiN

  have hne : ∀ k, ∃ j, y ⟨k, j⟩ ≠ 0 := fun k => by
    obtain ⟨j, hj⟩ := hV.relevant k
    refine ⟨j, fun h0 => hj ?_⟩
    rw [pointIdeal, RingHom.mem_ker]
    simp [pointConeMap, h0]
  choose c hc using hne
  have hyc : segreVec y c ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hc k
  have hsp := hspan F Ω K ι y N E B a M φ hφ c hyc

  have hv : ∀ m : Fin N, ∃ v ∈ B.lat c, (∀ j, m < j → w.repr v j = 0) ∧
      w.repr v m = ∏ k, y ⟨k, c k⟩ ^ b m k := by
    intro m
    have hmem : (∏ k, y ⟨k, c k⟩ ^ b m k) ∈ degLat F y (b m) c := ⟨1, one_mem _, (one_mul _).symm⟩
    rw [← hflag.graded c hyc m] at hmem
    exact hmem
  choose v hvl hvz hvd using hv
  obtain ⟨ι', hι'⟩ : ∃ ι' : Fin i → Fin N, ι' = Fin.castLE hiN := ⟨_, rfl⟩
  have hsum : ∀ {β : Type} [AddCommMonoid β] (f : Fin N → β), (∀ j : Fin N, i ≤ (j : ℕ) → f j = 0) →
      ∑ j, f j = ∑ j : Fin i, f (ι' j) := by
    intro β _ f hf
    have hm : ∑ j : Fin i, f (ι' j) = ∑ j ∈ Finset.univ.map (Fin.castLEEmb hiN), f j := by
      rw [Finset.sum_map, hι']
      rfl
    rw [hm]
    refine (Finset.sum_subset (Finset.subset_univ _) fun j _ hj => hf j ?_).symm
    by_contra h
    exact hj (Finset.mem_map.mpr ⟨⟨j, by omega⟩, Finset.mem_univ _, rfl⟩)
  obtain ⟨G, hG⟩ : ∃ G : Fin M → Fin i → Ω, G = fun l j => φ l (w (ι' j)) := ⟨_, rfl⟩
  obtain ⟨H, hH⟩ : ∃ H : Matrix (Fin i) (Fin i) Ω, H = Matrix.of fun j m => w.repr (v (ι' m)) (ι' j) :=
    ⟨_, rfl⟩
  have hinj : Function.Injective ι' := by
    rw [hι']
    exact Fin.castLE_injective hiN
  have hval : ∀ m : Fin i, ((ι' m : Fin N) : ℕ) = m := fun m => by
    rw [hι', Fin.val_castLE]
  have hlt : ∀ m j : Fin i, m < j → ι' m < ι' j := fun m j h => by
    rw [Fin.lt_def, hval, hval]
    exact Fin.lt_def.mp h
  have hGH : ∀ l m, (Matrix.of G * H) l m = φ l (v (ι' m)) := by
    intro l m
    conv_rhs => rw [← w.sum_repr (v (ι' m))]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, hsum]
    · simp [Matrix.mul_apply, hG, hH, mul_comm]
    · intro j hj
      have hm := m.isLt
      rw [map_smul, hvz _ j (by rw [Fin.lt_def, hval]; omega), zero_smul]
  have hdet : IsUnit H.det := by
    rw [Matrix.det_of_isUpperTriangular (M := H) fun j m hjm => by
      rw [hH, Matrix.of_apply]
      exact hvz _ _ (hlt m j hjm)]
    refine isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun m _ => ?_)
    simp only [hH, Matrix.of_apply, hvd]
    exact Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hc k)
  have hlin : LinearIndependent Ω (fun j l => G l j) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hall : ∀ ψ ∈ Submodule.span Ω (Set.range φ), ψ (∑ j, g j • w (ι' j)) = 0 := by
      intro ψ hψ
      induction hψ using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨l, rfl⟩ := hx
        have := congrFun hg l
        set_option synthInstance.maxHeartbeats 100000 in
          simpa [hG, map_sum, Finset.sum_apply, mul_comm] using this
      | zero => simp
      | add x z _ _ hx hz => rw [LinearMap.add_apply, hx, hz, add_zero]
      | smul r x _ hx => rw [LinearMap.smul_apply, hx, smul_zero]
    rw [hsp] at hall
    have hw := (Module.forall_dual_apply_eq_zero_iff Ω _).mp fun ψ => hall ψ Submodule.mem_top
    exact Fintype.linearIndependent_iff.mp (w.linearIndependent.comp ι' hinj) g hw
  have hcoord : projCoord y w φ (truncCoord t i) =
      projCoord y (Pi.basisFun Ω (Fin i)) (fun l => LinearMap.proj l ∘ₗ (Matrix.of G).mulVecLin) (t ∘ ι') := by
    funext p
    rcases p with ⟨_ | k, l⟩
    · show ∑ j, truncCoord t i j * _ = ∑ j, _
      rw [hsum]
      · refine Finset.sum_congr rfl fun j _ => ?_
        have hj : ((ι' j : Fin N) : ℕ) < i := by rw [hval]; exact j.isLt
        simp only [truncCoord, hj, if_true, hG, Function.comp_apply, Pi.basisFun_apply]
        rw [LinearMap.comp_apply, Matrix.mulVecLin_apply, Matrix.mulVec_single_one]
        rfl
      · intro j hj
        simp [truncCoord, not_lt.mpr hj]
    · rfl
  have hproj : projIdeal F y w φ (truncCoord t i) = projIdeal F y (Pi.basisFun Ω (Fin i))
      (fun l => LinearMap.proj l ∘ₗ (Matrix.of G).mulVecLin) (t ∘ ι') := by
    unfold projIdeal
    rw [hcoord]
  rw [hproj]
  exact hdim F Ω K ι y e hV hdimV M i G (by omega) hlin c a H hyc hdet
    (fun l m => by rw [hGH]; exact hφ.sections c hyc l _ (hvl _)) Φ (t ∘ ι')
    (ht.comp ι' hinj)

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinJoinVertDivRight
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (IsVertDiv mcIdeal mcMap joinCoord midDeg midVar)

noncomputable section

namespace JoinVerticalDivisorRight

variable {K K' K₂ : Type} {ι : K → Type} {ι' : K' → Type} {ι₂ : K₂ → Type}

def midNat (a : K ⊕ K' → ℕ) : K ⊕ (K₂ ⊕ K') → ℕ :=
  Sum.elim (fun k => a (.inl k)) (Sum.elim 0 (fun k => a (.inr k)))

theorem midNat_injective : Function.Injective (midNat (K := K) (K' := K') (K₂ := K₂)) := by
  intro a b e
  funext l
  rcases l with k | k
  · exact congrFun e (.inl k)
  · exact congrFun e (.inr (.inr k))

theorem midVar_injective : Function.Injective (midVar (ι := ι) (ι' := ι') ι₂) := by
  rintro ⟨k | k, i⟩ ⟨l | l, j⟩ h <;> dsimp only [midVar] at h <;> cases h <;> rfl

theorem mcMap_rename_midVar (R : Type) [CommRing R] {Ω : Type} [Field Ω] [Algebra R Ω]
    (x : (Σ k, ι k) → Ω) (w : (Σ k, ι₂ k) → Ω) (z : (Σ k, ι' k) → Ω)
    (h : MvPolynomial (Σ k : K ⊕ K', Sum.elim ι ι' k) R) :
    mcMap R (joinCoord x (joinCoord w z)) (rename (midVar ι₂) h) =
      rename (Sum.map id Sum.inr) (mcMap R (joinCoord x z) h) := by
  induction h using MvPolynomial.induction_on with
  | C a => simp [mcMap, algebraMap_eq]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, hp, rename_X]
    congr 1
    obtain ⟨k | k, i⟩ := v <;> simp [mcMap, midVar, joinCoord]

theorem rename_mem_mcIdeal_iff (R : Type) [CommRing R] {Ω : Type} [Field Ω] [Algebra R Ω]
    (x : (Σ k, ι k) → Ω) (w : (Σ k, ι₂ k) → Ω) (z : (Σ k, ι' k) → Ω)
    (h : MvPolynomial (Σ k : K ⊕ K', Sum.elim ι ι' k) R) :
    rename (midVar ι₂) h ∈ mcIdeal R (joinCoord x (joinCoord w z)) ↔ h ∈ mcIdeal R (joinCoord x z) := by
  simp only [mcIdeal, RingHom.mem_ker, mcMap_rename_midVar]
  exact map_eq_zero_iff _ (rename_injective _ (Sum.map_injective.mpr ⟨Function.injective_id,
    Sum.inr_injective⟩))

variable [Fintype K] [Fintype K'] [Fintype K₂] [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)]
  [∀ k, Fintype (ι₂ k)]

theorem weight_mapDomain_midVar [DecidableEq K] [DecidableEq K'] [DecidableEq K₂]
    (d : (Σ k : K ⊕ K', Sum.elim ι ι' k) →₀ ℕ) :
    Finsupp.weight (blockWeight (Sum.elim ι (Sum.elim ι₂ ι'))) (Finsupp.mapDomain (midVar ι₂) d) =
      midNat (Finsupp.weight (blockWeight (Sum.elim ι ι')) d) := by
  funext l
  rw [Objects.weight_blockWeight_apply]
  rcases l with k | k | k
  · change _ = Finsupp.weight (blockWeight (Sum.elim ι ι')) d (.inl k)
    rw [Objects.weight_blockWeight_apply]
    exact Finset.sum_congr rfl fun i _ => Finsupp.mapDomain_apply_of_injective midVar_injective d ⟨.inl k, i⟩
  · change _ = 0
    refine Finset.sum_eq_zero fun i _ => Finsupp.mapDomain_of_notMem_range _ _ ?_
    rintro ⟨⟨k' | k', j⟩, h⟩ <;> dsimp only [midVar] at h <;> cases h
  · change _ = Finsupp.weight (blockWeight (Sum.elim ι ι')) d (.inr k)
    rw [Objects.weight_blockWeight_apply]
    exact Finset.sum_congr rfl fun i _ => Finsupp.mapDomain_apply_of_injective midVar_injective d ⟨.inr k, i⟩

theorem isMultiHomog_rename [DecidableEq K] [DecidableEq K'] [DecidableEq K₂] {R : Type} [CommRing R]
    {f : MvPolynomial (Σ k : K ⊕ K', Sum.elim ι ι' k) R} {a : K ⊕ K' → ℕ} (hf : IsMultiHomog f a) :
    IsMultiHomog (rename (midVar ι₂) f) (midNat a) := by
  unfold IsMultiHomog at hf ⊢
  induction hf using IsWeightedHomogeneous.induction_on with
  | zero => simpa using isWeightedHomogeneous_zero R _ _
  | add p q hp hq ihp ihq => simpa [map_add (f := _)] using ihp.add ihq
  | monomial d r hr =>
    rw [rename_monomial]
    exact isWeightedHomogeneous_monomial _ _ _ (by rw [weight_mapDomain_midVar, hr])

theorem isMultiHomog_rename' {R : Type} [CommRing R] {f : MvPolynomial (Σ k : K ⊕ K', Sum.elim ι ι' k) R}
    {a : K ⊕ K' → ℕ} (hf : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f a) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (rename (midVar ι₂) f) (midNat a) := by
  classical
  rw [← Objects.isMultiHomog_iff] at hf ⊢
  exact isMultiHomog_rename hf

theorem rename_weightedHomogeneousComponent [DecidableEq K] [DecidableEq K'] [DecidableEq K₂] {R : Type}
    [CommRing R] (b : K ⊕ K' → ℕ) (h : MvPolynomial (Σ k : K ⊕ K', Sum.elim ι ι' k) R) :
    rename (midVar ι₂) (weightedHomogeneousComponent (blockWeight (Sum.elim ι ι')) b h) =
      weightedHomogeneousComponent (blockWeight (Sum.elim ι (Sum.elim ι₂ ι'))) (midNat b)
        (rename (midVar ι₂) h) := by
  induction h using MvPolynomial.induction_on' with
  | monomial d r =>
    have hm : IsMultiHomog (monomial d r : MvPolynomial (Σ k : K ⊕ K', Sum.elim ι ι' k) R)
        (Finsupp.weight (blockWeight (Sum.elim ι ι')) d) := isWeightedHomogeneous_monomial _ _ _ rfl
    have hj := isMultiHomog_rename (ι₂ := ι₂) hm
    by_cases hb : b = Finsupp.weight (blockWeight (Sum.elim ι ι')) d
    · subst hb
      rw [IsWeightedHomogeneous.weightedHomogeneousComponent_same hm,
        IsWeightedHomogeneous.weightedHomogeneousComponent_same hj]
    · rw [IsWeightedHomogeneous.weightedHomogeneousComponent_ne b hm hb,
        IsWeightedHomogeneous.weightedHomogeneousComponent_ne _ hj (fun e => hb (midNat_injective e)),
        map_zero]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]

theorem comap_isMultiProjPrime {R : Type} [CommRing R]
    {Q : Ideal (MvPolynomial (Σ k : K ⊕ (K₂ ⊕ K'), Sum.elim ι (Sum.elim ι₂ ι') k) R)}
    (hQ : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiProjPrime Q) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiProjPrime (Q.comap (rename (midVar (ι := ι) (ι' := ι') ι₂))) := by
  classical
  rw [← Objects.isMultiProjPrime_iff] at hQ ⊢
  have := hQ.isPrime
  refine ⟨Ideal.comap_isPrime _ Q, fun h hh b => ?_, fun k => ?_⟩
  · rw [Ideal.mem_comap] at hh ⊢
    rw [rename_weightedHomogeneousComponent]
    exact hQ.multiHomog _ hh _
  · rcases k with k | k
    · obtain ⟨i, hi⟩ := hQ.relevant (Sum.inl k)
      exact ⟨i, by rw [Ideal.mem_comap, rename_X]; exact hi⟩
    · obtain ⟨i, hi⟩ := hQ.relevant (Sum.inr (Sum.inr k))
      exact ⟨i, by rw [Ideal.mem_comap, rename_X]; exact hi⟩

end JoinVerticalDivisorRight


open JoinVerticalDivisorRight in
theorem JoinVerticalDivisorRight.proof : JoinVerticalDivisorRight.Statement := by
  intro O _ _ _ Ω _ _ K _ ι _ x K' _ ι' _ z K₂ _ ι₂ _ w b f g hD
  obtain ⟨⟨α, β, hf, hg, hb⟩, hfP, hgP, hU⟩ := hD
  refine ⟨⟨midNat α, midNat β, isMultiHomog_rename' hf, isMultiHomog_rename' hg, ?_⟩, ?_, ?_, ?_⟩
  · rintro (k | k | k)
    · exact hb (.inl k)
    · simp [midNat, midDeg]
    · exact hb (.inr k)
  · rwa [rename_mem_mcIdeal_iff]
  · rwa [rename_mem_mcIdeal_iff]
  · intro Q hQ hPQ hQO
    have hle : mcIdeal O (joinCoord x z) ≤ Q.comap (rename (midVar (ι := ι) (ι' := ι') ι₂)) :=
      fun h hh => Ideal.mem_comap.mpr (hPQ ((rename_mem_mcIdeal_iff O x w z h).mpr hh))
    have hO : (Q.comap (rename (midVar (ι := ι) (ι' := ι') ι₂))).comap
        (C : O →+* ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O (Sum.elim ι ι')) = ⊥ := by
      rw [eq_bot_iff] at hQO ⊢
      intro c hc
      apply hQO
      simpa [Ideal.mem_comap, rename_C] using hc
    obtain ⟨u, v, ⟨γ, hu⟩, ⟨δ, hv⟩, huQ, hvQ, huv⟩ := hU _ (comap_isMultiProjPrime hQ) hle hO
    refine ⟨rename (midVar ι₂) u, rename (midVar ι₂) v, ⟨_, isMultiHomog_rename' hu⟩,
      ⟨_, isMultiHomog_rename' hv⟩, huQ, hvQ, ?_⟩
    have := (rename_mem_mcIdeal_iff O x w z _).mpr huv
    simpa only [map_sub, map_mul] using this

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinJoinVertDivLeft
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (joinCoord mcIdeal mcMap assocDeg assocVar joinCoord_assocVar IsVertDiv)

noncomputable section

namespace JoinVerticalDivisorLeft

variable {K K' K₂ : Type} {ι : K → Type} {ι' : K' → Type} {ι₂ : K₂ → Type}

theorem assocVar_fst (p : Σ k : K ⊕ K', Sum.elim ι ι' k) :
    (assocVar ι₂ p).1 = Sum.map id Sum.inl p.1 := by
  obtain ⟨k | k, i⟩ := p <;> rfl

theorem assocBlock_injective :
    Function.Injective (Sum.map id Sum.inl : K ⊕ K' → K ⊕ (K' ⊕ K₂)) :=
  Sum.map_injective.mpr ⟨Function.injective_id, Sum.inl_injective⟩

variable [Fintype K] [Fintype K'] [Fintype K₂] [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)]
  [∀ k, Fintype (ι₂ k)]


omit [Fintype K] [Fintype K'] [Fintype K₂] [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)]
  [∀ k, Fintype (ι₂ k)] in
theorem mcMap_rename_assocVar (R : Type) [CommRing R] {Ω : Type} [Field Ω] [Algebra R Ω]
    (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω) (w : (Σ k, ι₂ k) → Ω)
    (h : MvPolynomial (Σ k : K ⊕ K', Sum.elim ι ι' k) R) :
    mcMap R (joinCoord x (joinCoord z w)) (rename (assocVar ι₂) h) =
      rename (Sum.map id Sum.inl) (mcMap R (joinCoord x z) h) := by
  induction h using MvPolynomial.induction_on with
  | C a => simp [mcMap, MvPolynomial.algebraMap_eq]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p n hp =>
    simp only [map_mul, rename_X, hp]
    congr 1
    simp [mcMap, joinCoord_assocVar, assocVar_fst]


omit [Fintype K] [Fintype K'] [Fintype K₂] [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)]
  [∀ k, Fintype (ι₂ k)] in
theorem rename_assocVar_mem_mcIdeal_iff (R : Type) [CommRing R] {Ω : Type} [Field Ω] [Algebra R Ω]
    (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω) (w : (Σ k, ι₂ k) → Ω)
    (h : MvPolynomial (Σ k : K ⊕ K', Sum.elim ι ι' k) R) :
    rename (assocVar ι₂) h ∈ mcIdeal R (joinCoord x (joinCoord z w)) ↔ h ∈ mcIdeal R (joinCoord x z) := by
  simp only [mcIdeal, RingHom.mem_ker]
  rw [mcMap_rename_assocVar]
  exact map_eq_zero_iff _ (rename_injective _ assocBlock_injective)


omit [Fintype K] [Fintype K'] [Fintype K₂] [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)]
  [∀ k, Fintype (ι₂ k)] in
theorem blockWeight_assocVar [DecidableEq K] [DecidableEq K'] [DecidableEq K₂]
    (p : Σ k : K ⊕ K', Sum.elim ι ι' k) (s : K ⊕ (K' ⊕ K₂)) :
    blockWeight (Sum.elim ι (Sum.elim ι' ι₂)) (assocVar ι₂ p) s =
      Sum.elim (fun k => blockWeight (Sum.elim ι ι') p (.inl k))
        (Sum.elim (fun k => blockWeight (Sum.elim ι ι') p (.inr k)) 0) s := by
  obtain ⟨k | k, i⟩ := p <;> rcases s with l | l | l <;> simp [blockWeight, assocVar, Pi.single_apply]


omit [Fintype K] [Fintype K'] [Fintype K₂] [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)]
  [∀ k, Fintype (ι₂ k)] in
theorem weight_mapDomain_assocVar [DecidableEq K] [DecidableEq K'] [DecidableEq K₂]
    (d : (Σ k : K ⊕ K', Sum.elim ι ι' k) →₀ ℕ) :
    Finsupp.weight (blockWeight (Sum.elim ι (Sum.elim ι' ι₂))) (Finsupp.mapDomain (assocVar ι₂) d) =
      Sum.elim (fun k => Finsupp.weight (blockWeight (Sum.elim ι ι')) d (.inl k))
        (Sum.elim (fun k => Finsupp.weight (blockWeight (Sum.elim ι ι')) d (.inr k)) 0) := by
  rw [Finsupp.weight_apply, Finsupp.sum_mapDomain_index (by simp) (by intros; simp [add_smul]),
    Finsupp.weight_apply]
  funext s
  simp only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, blockWeight_assocVar]
  rcases s with l | l | l <;> simp


omit [Fintype K] [Fintype K'] [Fintype K₂] [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)]
  [∀ k, Fintype (ι₂ k)] in
theorem isMultiHomog_rename_assocVar' [DecidableEq K] [DecidableEq K'] [DecidableEq K₂] {R : Type}
    [CommRing R] {f : MvPolynomial (Σ k : K ⊕ K', Sum.elim ι ι' k) R} {a : K ⊕ K' → ℕ}
    (hf : IsMultiHomog f a) :
    IsMultiHomog (rename (assocVar ι₂) f)
      (Sum.elim (fun k => a (.inl k)) (Sum.elim (fun k => a (.inr k)) 0)) := by
  unfold IsMultiHomog at hf ⊢
  induction hf using IsWeightedHomogeneous.induction_on with
  | zero => simpa using isWeightedHomogeneous_zero R _ _
  | add p q hp hq ihp ihq => simpa [map_add (f := _)] using ihp.add ihq
  | monomial d r hr =>
    rw [rename_monomial]
    apply isWeightedHomogeneous_monomial
    subst hr
    exact weight_mapDomain_assocVar d

theorem isMultiHomog_rename_assocVar {R : Type} [CommRing R]
    {f : MvPolynomial (Σ k : K ⊕ K', Sum.elim ι ι' k) R} {a : K ⊕ K' → ℕ}
    (hf : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f a) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (rename (assocVar ι₂) f)
      (Sum.elim (fun k => a (.inl k)) (Sum.elim (fun k => a (.inr k)) 0)) := by
  classical
  rw [← Objects.isMultiHomog_iff] at hf ⊢
  exact isMultiHomog_rename_assocVar' hf


omit [Fintype K] [Fintype K'] [Fintype K₂] [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)]
  [∀ k, Fintype (ι₂ k)] in
theorem rename_weightedHomogeneousComponent [DecidableEq K] [DecidableEq K'] [DecidableEq K₂] {R : Type}
    [CommRing R] (c : K ⊕ K' → ℕ) (h : MvPolynomial (Σ k : K ⊕ K', Sum.elim ι ι' k) R) :
    rename (assocVar ι₂) (weightedHomogeneousComponent (blockWeight (Sum.elim ι ι')) c h) =
      weightedHomogeneousComponent (blockWeight (Sum.elim ι (Sum.elim ι' ι₂)))
        (Sum.elim (fun k => c (.inl k)) (Sum.elim (fun k => c (.inr k)) 0)) (rename (assocVar ι₂) h) := by
  induction h using MvPolynomial.induction_on' with
  | monomial d r =>
    have hm : IsMultiHomog (monomial d r : MRing (Sum.elim ι ι') R)
        (Finsupp.weight (blockWeight (Sum.elim ι ι')) d) :=
      isWeightedHomogeneous_monomial _ _ _ rfl
    have hj := isMultiHomog_rename_assocVar' (ι₂ := ι₂) hm
    by_cases hc : c = Finsupp.weight (blockWeight (Sum.elim ι ι')) d
    · subst hc
      rw [IsWeightedHomogeneous.weightedHomogeneousComponent_same hm,
        IsWeightedHomogeneous.weightedHomogeneousComponent_same hj]
    · have hc' : (Sum.elim (fun k => c (.inl k)) (Sum.elim (fun k => c (.inr k)) 0) :
            K ⊕ (K' ⊕ K₂) → ℕ) ≠
          Sum.elim (fun k => Finsupp.weight (blockWeight (Sum.elim ι ι')) d (.inl k))
            (Sum.elim (fun k => Finsupp.weight (blockWeight (Sum.elim ι ι')) d (.inr k)) 0) := by
        intro e
        apply hc
        funext k
        rcases k with k | k
        · exact congrFun e (.inl k)
        · exact congrFun e (.inr (.inl k))
      rw [IsWeightedHomogeneous.weightedHomogeneousComponent_ne c hm hc,
        IsWeightedHomogeneous.weightedHomogeneousComponent_ne _ hj hc', map_zero]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]

theorem comap_isMultiProjPrime {R : Type} [CommRing R]
    {Q : Ideal (MvPolynomial (Σ k : K ⊕ (K' ⊕ K₂), Sum.elim ι (Sum.elim ι' ι₂) k) R)}
    (hQ : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiProjPrime Q) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiProjPrime (Q.comap (rename (assocVar (ι := ι) (ι' := ι') ι₂))) := by
  classical
  rw [← Objects.isMultiProjPrime_iff] at hQ ⊢
  have := hQ.isPrime
  refine ⟨Ideal.comap_isPrime _ Q, fun h hh c => ?_, fun k => ?_⟩
  · rw [Ideal.mem_comap] at hh ⊢
    rw [rename_weightedHomogeneousComponent]
    exact hQ.multiHomog _ hh _
  · rcases k with k | k
    · obtain ⟨i, hi⟩ := hQ.relevant (.inl k)
      exact ⟨i, by rw [Ideal.mem_comap, rename_X]; exact hi⟩
    · obtain ⟨i, hi⟩ := hQ.relevant (.inr (.inl k))
      exact ⟨i, by rw [Ideal.mem_comap, rename_X]; exact hi⟩

end JoinVerticalDivisorLeft


open JoinVerticalDivisorLeft in
theorem JoinVerticalDivisorLeft.proof : JoinVerticalDivisorLeft.Statement := by
  intro O _ _ _ Ω _ _ K _ ι _ x K' _ ι' _ z K₂ _ ι₂ _ w b f g hD
  obtain ⟨⟨α, β, hf, hg, hb⟩, hfP, hgP, hU⟩ := hD
  refine ⟨⟨_, _, isMultiHomog_rename_assocVar (ι₂ := ι₂) hf, isMultiHomog_rename_assocVar (ι₂ := ι₂) hg, ?_⟩,
    ?_, ?_, ?_⟩
  · rintro (k | k | k)
    · simpa [assocDeg] using hb (.inl k)
    · simpa [assocDeg] using hb (.inr k)
    · simp [assocDeg]
  · rwa [rename_assocVar_mem_mcIdeal_iff]
  · rwa [rename_assocVar_mem_mcIdeal_iff]
  · intro Q hQ hPQ hQO
    have hle : mcIdeal O (joinCoord x z) ≤ Q.comap (rename (assocVar (ι := ι) (ι' := ι') ι₂)) :=
      fun h hh => Ideal.mem_comap.mpr (hPQ ((rename_assocVar_mem_mcIdeal_iff O x z w h).mpr hh))
    have hO : (Q.comap (rename (assocVar (ι := ι) (ι' := ι') ι₂))).comap
        (C : O →+* ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O (Sum.elim ι ι')) = ⊥ := by
      rw [eq_bot_iff] at hQO ⊢
      intro c hc
      apply hQO
      simpa [Ideal.mem_comap, rename_C] using hc
    obtain ⟨u, v, ⟨γ, hu⟩, ⟨δ, hv⟩, huQ, hvQ, huv⟩ := hU _ (comap_isMultiProjPrime hQ) hle hO
    refine ⟨rename (assocVar ι₂) u, rename (assocVar ι₂) v, ⟨_, isMultiHomog_rename_assocVar hu⟩,
      ⟨_, isMultiHomog_rename_assocVar hv⟩, huQ, hvQ, ?_⟩
    have := (rename_assocVar_mem_mcIdeal_iff O x z w _).mpr huv
    simpa only [map_sub, map_mul] using this

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinJoinPull
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing div_mem_chartRing exists_pow_mul_mem_chartRing)
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg joinCoord restrictChart IsPull SameGeneric)

namespace JoinPullbackAlt

section Charts

variable {Ω : Type*} [Field Ω] {K K' : Type} [Fintype K] [Fintype K'] {ι : K → Type} {ι' : K' → Type}

def zChart (s : ∀ k : K ⊕ K', Sum.elim ι ι' k) : ∀ k, ι' k :=
  fun k => s (.inr k)

def combChart (t : ∀ k, ι k) (u : ∀ k, ι' k) : ∀ k : K ⊕ K', Sum.elim ι ι' k
  | .inl k => t k
  | .inr k => u k

theorem restrictChart_combChart (t : ∀ k, ι k) (u : ∀ k, ι' k) :
    restrictChart (combChart t u) = t :=
  rfl

theorem zChart_combChart (t : ∀ k, ι k) (u : ∀ k, ι' k) : zChart (combChart t u) = u :=
  rfl

theorem mseg_joinCoord (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω) (s : ∀ k : K ⊕ K', Sum.elim ι ι' k) :
    mseg (joinCoord x z) s = mseg x (restrictChart s) * mseg z (zChart s) := by
  simp only [mseg, Fintype.prod_sum_type]
  rfl

variable (O : Type*) [CommRing O] [Algebra O Ω]

theorem chartRing_le_join (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω) (s : ∀ k : K ⊕ K', Sum.elim ι ι' k)
    (hs : mseg (joinCoord x z) s ≠ 0) :
    chartRing O (mseg x) (restrictChart s) ≤ chartRing O (mseg (joinCoord x z)) s := by
  have hz : mseg z (zChart s) ≠ 0 := by
    rw [mseg_joinCoord] at hs
    exact right_ne_zero_of_mul hs
  unfold chartRing
  apply Algebra.adjoin_le
  rintro _ ⟨t', rfl⟩
  have h : mseg x t' / mseg x (restrictChart s) =
      mseg (joinCoord x z) (combChart t' (zChart s)) / mseg (joinCoord x z) s := by
    rw [mseg_joinCoord x z (combChart t' (zChart s)), mseg_joinCoord x z s, restrictChart_combChart,
      zChart_combChart, mul_div_mul_right _ _ hz]
  simp only
  rw [h]
  exact div_mem_chartRing (o := O) _ _ _

end Charts

section Pull

variable (O : Type*) [CommRing O] {Ω : Type*} [Field Ω] [Algebra O Ω]
variable {K K' : Type} [Fintype K] [Fintype K'] {ι : K → Type} {ι' : K' → Type}
  [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)]
variable {N : ℕ} {V : Type*} [AddCommGroup V] [Module Ω V]

end Pull

end JoinPullbackAlt


end GroundTheory.Heights₂.Heights.NumbersDVR
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsTer
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

theorem LocalCoefficient.proof (h₁ : LeftTermSupport.Statement.{u})
    (h₂ : RightTermSupport.Statement.{u}) (h₃ : LocalCoeffRing.Statement.{u}) :
    LocalCoefficient.Statement.{u} := by
  intro O _ _ _ ϖ _ K _ _ ι _ P d hP b f g hD c s hs hsP hH hno U hUdim
  by_cases hU : U.IsPrime ∧ IsMultiHomogIdeal U ∧ IsRelevant U ∧ (C ϖ : MRing ι O) ∈ U ∧ P ≤ U
  swap
  ·
    have hl := h₁ O ϖ K ι P hP.multiProj.multiHomog b f g hD.1 c s hs
    have hr := h₂ O ϖ K ι P hP.multiProj.multiHomog b f g hD c s hs hH
    unfold cycEval
    rw [finsum_congr fun G => hl G U hU, finsum_congr fun W => hr W U hU, finsum_zero]
  obtain ⟨hUp, hUm, hUr, hϖU, hPU⟩ := hU
  have hUdim' := hUdim hUp hUm hUr hϖU
  have hPp : P.IsPrime := hP.multiProj.isPrime

  have hrel : ∀ W : Ideal (MRing ι O), W ≤ U → IsRelevant W := fun W hW k =>
    let ⟨i, hi⟩ := hUr k
    ⟨i, fun h => hi (hW h)⟩
  have hcyc : ∀ J W : Ideal (MRing ι O), IsRelevant W → idealCycle J W = locCycle J W := by
    intro J W hW
    unfold idealCycle locCycle
    by_cases hm : W ∈ J.minimalPrimes
    · rw [dite_eq_left ⟨hm, hW⟩, dite_eq_left hm]
      rfl
    · rw [dite_eq_right fun h => hm h.1, dite_eq_right hm]
  have hzero : ∀ J : Ideal (MRing ι O), ¬ J ≤ U → locCycle J U = 0 := by
    intro J hJ
    unfold locCycle
    rw [dite_eq_right fun h => hJ h.1.2]
  have hL : ∀ G, ratDiv P f g G * divCycle G s U =
      (locCycle (P ⊔ Ideal.span {f}) G - locCycle (P ⊔ Ideal.span {g}) G) *
        locCycle (G ⊔ Ideal.span {s}) U := by
    intro G
    rw [divCycle_eq_idealCycle, hcyc _ _ hUr]
    by_cases hG : G ≤ U
    · unfold ratDiv
      rw [divCycle_eq_idealCycle, divCycle_eq_idealCycle, hcyc _ _ (hrel G hG), hcyc _ _ (hrel G hG)]
    · rw [hzero _ fun h => hG (le_sup_left.trans h), mul_zero, mul_zero]
  have hR : ∀ W, divCycle P s W * idealCycle (W ⊔ divisorIdeal P f g) U =
      locCycle (P ⊔ Ideal.span {s}) W * locCycle (W ⊔ (P ⊔ Ideal.span {f}).colon {g}) U := by
    intro W
    show divCycle P s W * idealCycle (W ⊔ (P ⊔ Ideal.span {f}).colon {g}) U = _
    rw [hcyc _ _ hUr]
    by_cases hW : W ≤ U
    · rw [divCycle_eq_idealCycle, hcyc _ _ (hrel W hW)]
    · rw [hzero _ fun h => hW (le_sup_left.trans h), mul_zero, mul_zero]

  have hchain : ∀ Q₁ Q₂ : Ideal (MRing ι O), Q₁.IsPrime → Q₂.IsPrime → P < Q₁ → Q₁ < Q₂ → Q₂ < U →
      False := by
    intro Q₁ Q₂ _ _ hPQ hQQ hQU
    have e₁ := DimStrictDrop.proof (MRing ι O) P Q₁ hPQ
    have e₂ := DimStrictDrop.proof (MRing ι O) Q₁ Q₂ hQQ
    have e₃ := DimStrictDrop.proof (MRing ι O) Q₂ U hQU
    rw [hP.dim] at e₁
    have key : ((d + Fintype.card K : ℕ) : WithBot ℕ∞) + 1 + 1 + 1 ≤
        ((d + 1 + 1 + Fintype.card K : ℕ) : WithBot ℕ∞) :=
      ((add_le_add (add_le_add (add_le_add hUdim' le_rfl) le_rfl) le_rfl).trans
        ((add_le_add (add_le_add e₃ le_rfl) le_rfl).trans ((add_le_add e₂ le_rfl).trans e₁)))
    have key' : ((d + Fintype.card K + 3 : ℕ) : WithBot ℕ∞) ≤ ((d + 1 + 1 + Fintype.card K : ℕ) : WithBot ℕ∞) := by
      simpa only [Nat.cast_add, Nat.cast_ofNat, add_assoc, one_add_one_eq_two, two_add_one_eq_three] using key
    have := WithBot.coe_le_coe.mp key'
    norm_cast at this
    omega

  obtain ⟨u', v', hu', huv⟩ := hD.2 U hUp hPU hUr

  have hnc : ∀ W : Ideal (MRing ι O), W ≤ U → locCycle (P ⊔ Ideal.span {s}) W ≠ 0 →
      locCycle (P ⊔ Ideal.span {f}) W = locCycle (P ⊔ Ideal.span {g}) W := by
    intro W hW h
    have hs' : divCycle P s W ≠ 0 := by rwa [divCycle_eq_idealCycle, hcyc _ _ (hrel W hW)]
    have hr : ratDiv P f g W = 0 := by
      by_cases hϖW : (C ϖ : MRing ι O) ∈ W
      · exact hno W hϖW hs'
      · by_contra h
        exact hϖW (hD.1.vertical W h)
    unfold ratDiv at hr
    rw [divCycle_eq_idealCycle, divCycle_eq_idealCycle, hcyc _ _ (hrel W hW),
      hcyc _ _ (hrel W hW)] at hr
    omega
  unfold cycEval
  rw [finsum_congr hL, finsum_congr hR]
  exact h₃ (MRing ι O) P U hPp hUp hPU hchain f g s u' v' hD.1.num_not_mem hD.1.den_not_mem hsP hu'
    huv hnc

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpDivisorPush
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

section Pullback

variable {K : Type*} {ι : K → Type} {J : Type} {R : Type*} [CommRing R]

theorem liftForm_mem_blowUpOf_of_mem (P : Ideal (MRing ι R)) (u : J → MRing ι R) {p : MRing ι R}
    (hp : p ∈ P) : liftForm (J := J) p ∈ blowUpOf P u := by
  let φ : MRing ι R →ₐ[R] Polynomial (MRing ι R ⧸ P) :=
    (Polynomial.CAlgHom (R := R) (A := MRing ι R ⧸ P)).comp (Ideal.Quotient.mkₐ R P)
  have hcomp : (aeval (blowUpSubst P u)).comp (liftForm (ι := ι) (J := J) (R := R)) = φ := by
    apply MvPolynomial.algHom_ext
    intro v
    rw [AlgHom.comp_apply, liftForm, rename_X, aeval_X]
    rfl
  have h := DFunLike.congr_fun hcomp p
  rw [AlgHom.comp_apply] at h
  unfold blowUpOf
  rw [RingHom.mem_ker, h]
  show Polynomial.C (Ideal.Quotient.mk P p) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hp, map_zero]

end Pullback

section Sums

open scoped Classical in
open Classical in
theorem finsum_sub_mul_eq_of_support {α : Type*} (Z₁ Z₂ n : α → ℤ) (p : α → Prop)
    (h₁ : (Function.support Z₁).Finite) (h₂ : (Function.support Z₂).Finite)
    (hv : ∀ W, Z₁ W - Z₂ W ≠ 0 → p W) :
    ∑ᶠ W, (Z₁ W - Z₂ W) * n W =
      ∑ᶠ W, Z₁ W * (if p W then n W else 0) - ∑ᶠ W, Z₂ W * (if p W then n W else 0) := by
  have e : ∀ W, (Z₁ W - Z₂ W) * n W =
      Z₁ W * (if p W then n W else 0) - Z₂ W * (if p W then n W else 0) := by
    intro W
    by_cases h : Z₁ W - Z₂ W = 0
    · rw [h, zero_mul, sub_eq_zero.mp h, sub_self]
    · rw [ite_eq_left (hv W h), ← sub_mul]
  rw [finsum_congr e, finsum_sub_distrib]
  · exact h₁.subset fun W hW => left_ne_zero_of_mul hW
  · exact h₂.subset fun W hW => left_ne_zero_of_mul hW

end Sums

theorem BlowUpDivisorPush.proof (hvert : BlowUpVerticalPush.Statement.{u}) :
    BlowUpDivisorPush.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ J _ P n hP b f g hD N u hu hu' a
  have hfin := DivCycleFiniteSupport.proof.{u}
  obtain ⟨bf, bg, hbf, hbg, -⟩ := hD.degrees

  have hvertB : ∀ W, divCycle (blowUpOf P u) (liftForm (J := J) f) W -
      divCycle (blowUpOf P u) (liftForm (J := J) g) W ≠ 0 → (C ϖ : MRing (extIdx ι J) O) ∈ W := by
    intro W hW
    by_contra hϖW
    have hsupp : W.IsPrime ∧ blowUpOf P u ≤ W ∧ IsRelevant W := by
      by_cases h1 : divCycle (blowUpOf P u) (liftForm (J := J) f) W = 0
      · have h2 : divCycle (blowUpOf P u) (liftForm (J := J) g) W ≠ 0 := by
          intro h2; apply hW; rw [h1, h2, sub_zero]
        exact le_and_isRelevant_of_divCycle_ne_zero h2
      · exact le_and_isRelevant_of_divCycle_ne_zero h1
    obtain ⟨hWp, hBW, hWrel⟩ := hsupp
    let W₀ : Ideal (MRing ι O) := W.comap (liftForm (ι := ι) (J := J) (R := O))
    have hW₀ : W₀.IsPrime := Ideal.comap_isPrime _ _
    have hPW₀ : P ≤ W₀ := fun p hp => hBW (liftForm_mem_blowUpOf_of_mem P u hp)
    have hrel₀ : IsRelevant W₀ := by
      intro k
      obtain ⟨i, hi⟩ := hWrel (some k)
      refine ⟨i, fun h => hi ?_⟩
      have h' : liftForm (ι := ι) (J := J) (R := O) (X ⟨k, i⟩) ∈ W := h
      rwa [liftForm, rename_X] at h'
    have hϖ₀ : (C ϖ : MRing ι O) ∉ W₀ := by
      intro h
      have h' : liftForm (ι := ι) (J := J) (R := O) (C ϖ) ∈ W := h
      rw [liftForm, rename_C] at h'
      exact hϖW h'
    obtain ⟨s, t, hs, ht, hst⟩ := hD.unit_off_special W₀ hW₀ hPW₀ hrel₀ hϖ₀
    apply hW
    rw [divCycle_eq_of_mul_sub_mem (u := liftForm (J := J) s) (v := liftForm (J := J) t) hs ht ?_,
      sub_self]
    have := liftForm_mem_blowUpOf_of_mem (J := J) P u hst
    rwa [map_sub, map_mul, map_mul] at this
  have e₁ := hvert O ϖ hϖ K ι J P n hP N u hu hu' bf f hbf hD.num_not_mem a
  have e₂ := hvert O ϖ hϖ K ι J P n hP N u hu hu' bg g hbg hD.den_not_mem a
  unfold cycEval at e₁ e₂
  unfold cycEval ratDiv
  rw [finsum_sub_mul_eq_of_support (divCycle (blowUpOf P u) (liftForm (J := J) f))
      (divCycle (blowUpOf P u) (liftForm (J := J) g)) _ _ (hfin _ _ _ _ _) (hfin _ _ _ _ _) hvertB,
    finsum_sub_mul_eq_of_support (divCycle P f) (divCycle P g) _ _ (hfin _ _ _ _ _)
      (hfin _ _ _ _ _) hD.vertical, e₁, e₂]

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end
