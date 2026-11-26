module

public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualCotangentKer

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PIntCoordGeoNum
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

noncomputable section

namespace IntegralCoordGeometricNumber

variable {T T₂ : Type} [Fintype T] [DecidableEq T] [Fintype T₂] [DecidableEq T₂]

def substR (R : Type) [CommRing R] (A : Matrix T T₂ ℤ) :
    MRingOver R (dualBlocks T₂) →ₐ[R] MRingOver R (dualBlocks T) :=
  aeval fun p => ∑ t, C ((A t p.2 : ℤ) : R) * X (⟨(), t⟩ : Σ k : Unit, dualBlocks T k)


omit [Fintype T₂] [DecidableEq T] [DecidableEq T₂] in
theorem substR_int (A : Matrix T T₂ ℤ) : substR ℤ A = intCoordSubst A := by
  unfold substR intCoordSubst
  simp


omit [DecidableEq T₂] in
theorem substR_substR (R : Type) [CommRing R] {A : Matrix T T₂ ℤ} {B : Matrix T₂ T ℤ}
    (hAB : A * B = 1) (f : MRingOver R (dualBlocks T)) : substR R A (substR R B f) = f := by
  have h : (substR R A).comp (substR R B) = AlgHom.id R _ := by
    refine MvPolynomial.algHom_ext fun p => ?_
    obtain ⟨⟨⟩, t⟩ := p
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [AlgHom.comp_apply, AlgHom.id_apply, substR, aeval_X, map_sum, map_mul, aeval_C,
      algebraMap_eq]
    simp_rw [Finset.mul_sum, ← mul_assoc, ← C_mul]
    rw [Finset.sum_comm]
    set_option synthInstance.maxHeartbeats 100000 in
      simp_rw [← Finset.sum_mul, ← map_sum C, ← Int.cast_mul, ← Int.cast_sum]
    have h1 : ∀ x : T, ∑ s, B s t * A x s = (A * B) x t := fun x => by
      simp [Matrix.mul_apply, mul_comm]
    simp_rw [h1, hAB, Matrix.one_apply]
    simp
  exact DFunLike.congr_fun h f


omit [DecidableEq T] in
theorem isWH_iff {R : Type} [CommRing R] (f : MRingOver R (dualBlocks T)) (m : Unit → ℕ) :
    IsWeightedHomogeneous (NumbersDVR.blockWeight (dualBlocks T)) f m ↔ f.IsHomogeneous (m ()) := by
  have hw : ∀ d : (Σ k : Unit, dualBlocks T k) →₀ ℕ,
      Finsupp.weight (1 : (Σ k : Unit, dualBlocks T k) → ℕ) d = ∑ i : T, d ⟨(), i⟩ := by
    intro d
    rw [Pi.one_def, ← Finsupp.degree_eq_weight_one, Finsupp.degree_eq_sum, Fintype.sum_sigma]
    simp
  unfold IsHomogeneous IsWeightedHomogeneous
  simp only [Bridge.weight_blockWeight, hw, funext_iff]
  constructor
  · intro h d hd
    exact h hd ()
  · intro h d hd u
    cases u
    exact h hd


omit [DecidableEq T] [DecidableEq T₂] in
theorem substR_isWH (R : Type) [CommRing R] (A : Matrix T T₂ ℤ) {f : MRingOver R (dualBlocks T₂)}
    {m : Unit → ℕ} (hf : IsWeightedHomogeneous (NumbersDVR.blockWeight (dualBlocks T₂)) f m) :
    IsWeightedHomogeneous (NumbersDVR.blockWeight (dualBlocks T)) (substR R A f) m := by
  rw [isWH_iff] at hf ⊢
  have hg : ∀ p : Σ k : Unit, dualBlocks T₂ k,
      (∑ t, C ((A t p.2 : ℤ) : R) * X (⟨(), t⟩ : Σ k : Unit, dualBlocks T k)).IsHomogeneous 1 := by
    intro p
    refine IsHomogeneous.sum _ _ _ fun t _ => ?_
    have := (isHomogeneous_C (Σ k : Unit, dualBlocks T k) ((A t p.2 : ℤ) : R)).mul
      (isHomogeneous_X R (⟨(), t⟩ : Σ k : Unit, dualBlocks T k))
    rwa [zero_add] at this
  have := hf.eval₂ (algebraMap R _) _ (fun r => by rw [algebraMap_eq]; exact isHomogeneous_C _ r) hg
  rw [one_mul] at this
  unfold substR
  rw [aeval_def]
  exact this

theorem comap_substR (R : Type) [CommRing R] {A : Matrix T T₂ ℤ} {B : Matrix T₂ T ℤ}
    (hAB : A * B = 1) (hBA : B * A = 1) (V : Ideal (MRingOver R (dualBlocks T))) :
    V.comap (substR R A) = V.map (substR R B) := by
  apply le_antisymm
  · intro f hf
    rw [← substR_substR R hBA f]
    exact Ideal.mem_map_of_mem _ hf
  · rw [Ideal.map_le_iff_le_comap]
    intro g hg
    rw [Ideal.mem_comap, Ideal.mem_comap, substR_substR R hAB]
    exact hg


omit [Fintype T₂] [DecidableEq T] [DecidableEq T₂] in
theorem red_substR (p : ℕ) (A : Matrix T T₂ ℤ) (f : MRingOver ℤ (dualBlocks T₂)) :
    MvPolynomial.map (Int.castRingHom (ZMod p)) (substR ℤ A f) =
      substR (ZMod p) A (MvPolynomial.map (Int.castRingHom (ZMod p)) f) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [substR]
  | add f g hf hg => rw [map_add (f := _), map_add (f := _), hf, hg, map_add (f := _), map_add (f := _)]
  | mul_X f q hf =>
    rw [map_mul, map_mul, hf, map_mul, map_mul, map_X]
    congr 1
    set_option synthInstance.maxHeartbeats 100000 in
      simp [substR, map_sum]

theorem hilbFn_comap (F : Type) [Field F] {A : Matrix T T₂ ℤ} {B : Matrix T₂ T ℤ}
    (hAB : A * B = 1) (hBA : B * A = 1) (Q : Ideal (MRingOver F (dualBlocks T))) :
    NumbersDVR.hilbFn (Q.comap (substR F A)) = NumbersDVR.hilbFn Q := by
  let e : MRingOver F (dualBlocks T₂) ≃ₐ[F] MRingOver F (dualBlocks T) :=
    AlgEquiv.ofAlgHom (substR F A) (substR F B) (AlgHom.ext fun f => substR_substR F hAB f)
      (AlgHom.ext fun f => substR_substR F hBA f)
  have hQ : Q = (Q.comap (substR F A)).map (e : MRingOver F (dualBlocks T₂) →+* MRingOver F (dualBlocks T)) :=
    (Ideal.map_comap_of_surjective _ e.surjective Q).symm
  let qe := Ideal.quotientEquivAlg (Q.comap (substR F A)) Q e hQ
  have hcomp : qe.toLinearEquiv.toLinearMap ∘ₗ (Ideal.Quotient.mkₐ F (Q.comap (substR F A))).toLinearMap =
      (Ideal.Quotient.mkₐ F Q).toLinearMap ∘ₗ (substR F A).toLinearMap :=
    LinearMap.ext fun x => rfl
  have hH : ∀ m : Unit → ℕ,
      (weightedHomogeneousSubmodule F (NumbersDVR.blockWeight (dualBlocks T₂)) m).map
        (substR F A).toLinearMap =
      weightedHomogeneousSubmodule F (NumbersDVR.blockWeight (dualBlocks T)) m := by
    intro m
    apply le_antisymm
    · rw [Submodule.map_le_iff_le_comap]
      intro f hf
      rw [Submodule.mem_comap, mem_weightedHomogeneousSubmodule] at *
      exact substR_isWH F A hf
    · intro g hg
      rw [mem_weightedHomogeneousSubmodule] at hg
      exact ⟨substR F B g, (mem_weightedHomogeneousSubmodule _ _ _ _).mpr (substR_isWH F B hg),
        substR_substR F hAB g⟩
  funext m
  unfold NumbersDVR.hilbFn
  split_ifs with hm
  · have key : (NumbersDVR.gradedPiece (Q.comap (substR F A)) fun k => (m k).toNat).map
        qe.toLinearEquiv.toLinearMap = NumbersDVR.gradedPiece Q fun k => (m k).toNat := by
      unfold NumbersDVR.gradedPiece
      rw [← Submodule.map_comp, hcomp, Submodule.map_comp, hH]
    congr 1
    rw [← key]
    exact (LinearEquiv.finrank_map_eq qe.toLinearEquiv _).symm
  · rfl

end IntegralCoordGeometricNumber


open IntegralCoordGeometricNumber in
theorem IntCoordGeoNum.proof : IntCoordGeoNum.Statement := by
  intro T T₂ _ _ _ _ A B hAB hBA V n p hV hp hpV hdim a
  have : Fact p.Prime := ⟨hp⟩
  rw [← substR_int]
  have hsurj : Function.Surjective (substR ℤ A) := fun f => ⟨substR ℤ B f, substR_substR ℤ hAB f⟩
  have hV' : IsMultiProjPrime (V.comap (substR ℤ A)) := by
    have : V.IsPrime := hV.1
    refine ⟨inferInstance, ?_, ?_⟩
    · obtain ⟨S, hS, hVS⟩ := hV.2.1
      refine ⟨substR ℤ B '' S, ?_, ?_⟩
      · rintro _ ⟨f, hf, rfl⟩
        obtain ⟨b, hb⟩ := hS f hf
        exact ⟨b, (Bridge.isMultiHomog_iff _ b).mp
          (substR_isWH ℤ B ((Bridge.isMultiHomog_iff f b).mpr hb))⟩
      · rw [comap_substR ℤ hAB hBA, hVS, Ideal.map_span]
    · intro k
      obtain ⟨t, ht⟩ := hV.2.2 k
      by_contra h
      push Not at h
      apply ht
      have hmem : substR ℤ B (X ⟨k, t⟩) ∈ V.comap (substR ℤ A) := by
        simp only [substR, aeval_X]
        exact Ideal.sum_mem _ fun s _ => Ideal.mul_mem_left _ _ (h s)
      rwa [Ideal.mem_comap, substR_substR ℤ hAB] at hmem
  have hpV' : (C (p : ℤ) : MRing (dualBlocks T₂)) ∈ V.comap (substR ℤ A) := by
    rw [Ideal.mem_comap]
    simpa [substR] using hpV
  have hdim' : ringKrullDim (MRing (dualBlocks T₂) ⧸ V.comap (substR ℤ A)) =
      ((n + Fintype.card Unit : ℕ) : WithBot ℕ∞) := by
    rw [← hdim]
    exact ringKrullDim_eq_of_ringEquiv ((Ideal.quotEquivOfEq (by
        rw [← RingHom.comap_ker, Ideal.mk_ker]
        try rfl)).trans
      (RingHom.quotientKerEquivOfSurjective (f := (Ideal.Quotient.mk V).comp
        (substR ℤ A : MRing (dualBlocks T₂) →+* MRing (dualBlocks T)))
        (Ideal.Quotient.mk_surjective.comp hsurj)))
  rw [← Bridge.intNum_map_eq_geoNum p n V hV hpV hdim a,
    ← Bridge.intNum_map_eq_geoNum p n _ hV' hpV' hdim' a]
  have e1 : V.map (substR ℤ B) =
      V.map (substR ℤ B : MRingOver ℤ (dualBlocks T) →+* MRingOver ℤ (dualBlocks T₂)) := rfl
  have e2 : (V.map (MvPolynomial.map (Int.castRingHom (ZMod p)))).map (substR (ZMod p) B) =
      (V.map (MvPolynomial.map (Int.castRingHom (ZMod p)))).map
        (substR (ZMod p) B : MRingOver (ZMod p) (dualBlocks T) →+* MRingOver (ZMod p) (dualBlocks T₂)) := rfl
  have hred : (V.comap (substR ℤ A)).map (MvPolynomial.map (Int.castRingHom (ZMod p))) =
      (V.map (MvPolynomial.map (Int.castRingHom (ZMod p)))).comap (substR (ZMod p) A) := by
    rw [comap_substR ℤ hAB hBA, comap_substR (ZMod p) hAB hBA, e1, e2, Ideal.map_map, Ideal.map_map]
    congr 1
    exact RingHom.ext fun f => red_substR p B f
  unfold NumbersDVR.intNum
  rw [hred, hilbFn_comap (ZMod p) hAB hBA]

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PIntCoordArInt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial MeasureTheory

noncomputable section

namespace IntegralCoordArithIntersection

set_option linter.unusedSectionVars false

variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] {e : ℕ}

def segreMap (M : Matrix X Y ℤ) :
    (((k : Unit) → dualBlocks X k) → ℂ) →ₗ[ℂ] (((k : Unit) → dualBlocks Y k) → ℂ) where
  toFun w := fun i => ∑ x : X, w (fun _ => x) * (M x (i ()) : ℂ)
  map_add' v w := by
    funext i
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' c w := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum, mul_assoc]

theorem sum_sum_mul {M : Matrix X Y ℤ} {N : Matrix Y X ℤ} (h : M * N = 1) (v : X → ℂ) (x : X) :
    ∑ y, (∑ x', v x' * (M x' y : ℂ)) * (N y x : ℂ) = v x := by
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  have h1 : ∀ x', ∑ y, v x' * (M x' y : ℂ) * (N y x : ℂ) = v x' * (((M * N) x' x : ℤ) : ℂ) := by
    intro x'
    simp [Matrix.mul_apply, mul_assoc, Finset.mul_sum]
  simp_rw [h1, h, Matrix.one_apply]
  simp

theorem pt_pt {M : Matrix X Y ℤ} {N : Matrix Y X ℤ} (h : M * N = 1) (z : (Σ _ : Unit, X) → ℂ) :
    intCoordPt N (intCoordPt M z) = z := by
  funext p
  obtain ⟨⟨⟩, x⟩ := p
  exact sum_sum_mul h (fun x' => z ⟨(), x'⟩) x

theorem segreMap_segreMap {M : Matrix X Y ℤ} {N : Matrix Y X ℤ} (h : M * N = 1)
    (w : ((k : Unit) → dualBlocks X k) → ℂ) : segreMap N (segreMap M w) = w := by
  funext i
  have hi : i = fun _ => i () := funext fun u => by cases u; rfl
  simp only [segreMap, LinearMap.coe_mk, AddHom.coe_mk]
  rw [sum_sum_mul h (fun x => w (fun _ => x)) (i ()), ← hi]

theorem segre_pt (M : Matrix X Y ℤ) (z : (Σ _ : Unit, X) → ℂ) :
    segre (ι := dualBlocks Y) (intCoordPt M z) = segreMap M (segre (ι := dualBlocks X) z) := by
  funext i
  simp [segre, segreMap, intCoordPt]

theorem eval_subst (M : Matrix X Y ℤ) (f : MRing (dualBlocks Y)) (z : (Σ _ : Unit, X) → ℂ) :
    eval z (map (Int.castRingHom ℂ) (intCoordSubst M f)) = eval (intCoordPt M z) (map (Int.castRingHom ℂ) f) := by
  have : ((eval z).comp ((map (Int.castRingHom ℂ)).comp (intCoordSubst M).toRingHom)) =
      (eval (intCoordPt M z)).comp (map (Int.castRingHom ℂ)) := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun p => ?_)
    · simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      rw [show (C r : MRing (dualBlocks Y)) = algebraMap ℤ _ r from rfl, AlgHom.commutes]
      simp
    · obtain ⟨⟨⟩, y⟩ := p
      simp [intCoordSubst, intCoordPt, mul_comm]
  exact RingHom.congr_fun this f

theorem differentiableAt_pt (M : Matrix X Y ℤ) {γ : (Fin e → ℂ) → (Σ _ : Unit, X) → ℂ} {y : Fin e → ℂ}
    (h : DifferentiableAt ℂ γ y) : DifferentiableAt ℂ (fun y' => intCoordPt M (γ y')) y := by
  rw [differentiableAt_pi]
  intro p
  simp only [intCoordPt]
  exact DifferentiableAt.fun_sum fun x _ => ((differentiableAt_pi.1 h) ⟨(), x⟩).mul_const _

variable {A : Matrix X Y ℤ} {B : Matrix Y X ℤ}

theorem mem_mcPts (hAB : A * B = 1) (hBA : B * A = 1) (Q : Ideal (MRing (dualBlocks X)))
    (z₂ : (Σ _ : Unit, Y) → ℂ) :
    z₂ ∈ mcPts (Q.comap (intCoordSubst A)) ↔ intCoordPt B z₂ ∈ mcPts Q := by
  constructor
  · rintro ⟨hz, hf⟩
    refine ⟨intCoordPt_ne_zero ⟨A, hBA⟩ hz, fun g hg => ?_⟩
    rw [← eval_subst]
    apply hf
    rw [Ideal.mem_comap, TopDualBasisChange.subst_subst hAB]
    exact hg
  · rintro ⟨hz, hf⟩
    refine ⟨?_, fun f hf' => ?_⟩
    · have := intCoordPt_ne_zero ⟨B, hAB⟩ hz
      rwa [pt_pt hBA] at this
    · rw [← TopDualBasisChange.subst_subst hBA f, eval_subst]
      exact hf _ (Ideal.mem_comap.1 hf')

theorem isGoodProj_comp (hAB : A * B = 1) (hBA : B * A = 1) {Q : Ideal (MRing (dualBlocks X))}
    {Ψ₂ : (((k : Unit) → dualBlocks Y k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)}
    (h : IsGoodProj (Q.comap (intCoordSubst A)) Ψ₂) : IsGoodProj Q (Ψ₂ ∘ₗ segreMap A) := by
  intro z hz
  rw [LinearMap.comp_apply, ← segre_pt]
  apply h
  rw [mem_mcPts hAB hBA, pt_pt hAB]
  exact hz

theorem isGoodProj_comp' (hAB : A * B = 1) (hBA : B * A = 1) {Q : Ideal (MRing (dualBlocks X))}
    {Ψ : (((k : Unit) → dualBlocks X k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)}
    (h : IsGoodProj Q Ψ) : IsGoodProj (Q.comap (intCoordSubst A)) (Ψ ∘ₗ segreMap B) := by
  intro z₂ hz₂
  rw [LinearMap.comp_apply, ← segre_pt]
  exact h _ ((mem_mcPts hAB hBA Q z₂).1 hz₂)

theorem bijOn_fibre (hAB : A * B = 1) (hBA : B * A = 1) (Q : Ideal (MRing (dualBlocks X)))
    (Ψ₂ : (((k : Unit) → dualBlocks Y k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (y : Fin e → ℂ) :
    Set.BijOn (segreMap B) (ReciprocityTheory.ChartRestriction.G.Geo.fibre (Q.comap (intCoordSubst A)) Ψ₂ y) (ReciprocityTheory.ChartRestriction.G.Geo.fibre Q (Ψ₂ ∘ₗ segreMap A) y) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro w₂ ⟨z₂, hz₂, rfl, hΨ⟩
    refine ⟨intCoordPt B z₂, (mem_mcPts hAB hBA Q z₂).1 hz₂, segre_pt B z₂, ?_⟩
    rw [LinearMap.comp_apply, segreMap_segreMap hBA]
    exact hΨ
  · intro v _ w _ hvw
    rw [← segreMap_segreMap hBA v, ← segreMap_segreMap hBA w, hvw]
  · rintro w ⟨z, hz, rfl, hΨ⟩
    refine ⟨segre (intCoordPt A z), ⟨intCoordPt A z, ?_, rfl, ?_⟩, ?_⟩
    · rw [mem_mcPts hAB hBA, pt_pt hAB]
      exact hz
    · rw [segre_pt]
      exact hΨ
    · rw [segre_pt, segreMap_segreMap hAB]

theorem isSheet_pt (hAB : A * B = 1) (hBA : B * A = 1) {Q : Ideal (MRing (dualBlocks X))}
    {Ψ₂ : (((k : Unit) → dualBlocks Y k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} {y : Fin e → ℂ}
    {w₂ : ((k : Unit) → dualBlocks Y k) → ℂ} {γ₂ : (Fin e → ℂ) → (Σ _ : Unit, Y) → ℂ}
    (h : IsSheet (Q.comap (intCoordSubst A)) Ψ₂ y w₂ γ₂) :
    IsSheet Q (Ψ₂ ∘ₗ segreMap A) y (segreMap B w₂) (fun y' => intCoordPt B (γ₂ y')) := by
  refine ⟨by rw [segre_pt, h.1], h.2.mono fun y' hy' => ⟨differentiableAt_pt B hy'.1,
    (mem_mcPts hAB hBA Q _).1 hy'.2.1, ?_⟩⟩
  rw [LinearMap.comp_apply, segre_pt, segreMap_segreMap hBA]
  exact hy'.2.2

theorem isSheet_pt' (hAB : A * B = 1) (hBA : B * A = 1) {Q : Ideal (MRing (dualBlocks X))}
    {Ψ₂ : (((k : Unit) → dualBlocks Y k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} {y : Fin e → ℂ}
    {w₂ : ((k : Unit) → dualBlocks Y k) → ℂ} {γ : (Fin e → ℂ) → (Σ _ : Unit, X) → ℂ}
    (h : IsSheet Q (Ψ₂ ∘ₗ segreMap A) y (segreMap B w₂) γ) :
    IsSheet (Q.comap (intCoordSubst A)) Ψ₂ y w₂ (fun y' => intCoordPt A (γ y')) := by
  refine ⟨by rw [segre_pt, h.1, segreMap_segreMap hBA], h.2.mono fun y' hy' => ⟨differentiableAt_pt A hy'.1,
    ?_, ?_⟩⟩
  · rw [mem_mcPts hAB hBA, pt_pt hAB]
    exact hy'.2.1
  · rw [segre_pt]
    exact hy'.2.2

theorem logNorm_pt (hBA : B * A = 1) (Ab : ReciprocityTheory.ChartRestriction.G.Geo.HermLine (dualBlocks X)) (s : MRing (dualBlocks X))
    (z₂ : (Σ _ : Unit, Y) → ℂ) :
    logNorm (intCoordLine B ⟨A, hBA⟩ Ab) (intCoordSubst B s) z₂ = logNorm Ab s (intCoordPt B z₂) := by
  simp only [logNorm, eval_subst]
  rfl

theorem ptsIntegralAt_eq (hSheet : SheetIndepStatement) (hAB : A * B = 1) (hBA : B * A = 1)
    (Q : Ideal (MRing (dualBlocks X))) (L : Fin e → ReciprocityTheory.ChartRestriction.G.Geo.HermLine (dualBlocks X)) (Ab : ReciprocityTheory.ChartRestriction.G.Geo.HermLine (dualBlocks X))
    (s : MRing (dualBlocks X)) (hQ : IsArithVar Q (e + 1)) (hL : ∀ j, IsSmoothHerm (L j))
    (hAb : IsSmoothHerm Ab) (hs : IsSectionOn Q Ab s)
    (Ψ₂ : (((k : Unit) → dualBlocks Y k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (hΨ₂ : IsGoodProj (Q.comap (intCoordSubst A)) Ψ₂) :
    ptsIntegralAt (Q.comap (intCoordSubst A)) Ψ₂
        (fun j z => Real.log ((intCoordLine B ⟨A, hBA⟩ (L j)).h z))
        (logNorm (intCoordLine B ⟨A, hBA⟩ Ab) (intCoordSubst B s)) =
      ptsIntegralAt Q (Ψ₂ ∘ₗ segreMap A) (fun j z => Real.log ((L j).h z)) (logNorm Ab s) := by
  have hΨ := isGoodProj_comp hAB hBA hΨ₂
  unfold ptsIntegralAt
  refine integral_congr_ae ?_
  filter_upwards [hSheet Unit (dualBlocks X) Q e _ L Ab s hQ hΨ hL hAb hs] with y hy
  refine finsum_mem_eq_of_bijOn (segreMap B) (bijOn_fibre hAB hBA Q Ψ₂ y) fun w₂ _ => ?_
  unfold sheetDensity
  by_cases h₂ : ∃ γ₂, IsSheet (Q.comap (intCoordSubst A)) Ψ₂ y w₂ γ₂
  · have h : ∃ γ, IsSheet Q (Ψ₂ ∘ₗ segreMap A) y (segreMap B w₂) γ :=
      ⟨_, isSheet_pt hAB hBA h₂.choose_spec⟩
    rw [dite_eq_left h₂, dite_eq_left h]
    have key := hy _ _ _ (isSheet_pt hAB hBA h₂.choose_spec) h.choose_spec
    simp only [pot] at key
    simp only [logNorm_pt hBA]
    exact key
  · have h : ¬ ∃ γ, IsSheet Q (Ψ₂ ∘ₗ segreMap A) y (segreMap B w₂) γ :=
      fun ⟨γ, hγ⟩ => h₂ ⟨_, isSheet_pt' hAB hBA hγ⟩
    rw [dite_eq_right h₂, dite_eq_right h]

end IntegralCoordArithIntersection


open IntegralCoordArithIntersection in
theorem IntCoordArInt.proof (hInd : PtsIndepStatement) (hSheet : SheetIndepStatement) :
    IntCoordArInt.Statement := by
  intro T T₂ _ _ _ _ A B hAB hBA Q e L Ab s hQ hL hAb hs
  unfold arInt ptsIntegral
  by_cases h₂ : ∃ Ψ₂ : (((k : Unit) → dualBlocks T₂ k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ),
      IsGoodProj (Q.comap (intCoordSubst A)) Ψ₂
  · have h : ∃ Ψ : (((k : Unit) → dualBlocks T k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ), IsGoodProj Q Ψ :=
      ⟨_, isGoodProj_comp hAB hBA h₂.choose_spec⟩
    rw [dite_eq_left h₂, dite_eq_left h, ptsIntegralAt_eq hSheet hAB hBA Q L Ab s hQ hL hAb hs _ h₂.choose_spec]
    exact hInd Unit (dualBlocks T) Q e _ _ L Ab s hQ (isGoodProj_comp hAB hBA h₂.choose_spec) h.choose_spec
      hL hAb hs
  · have h : ¬ ∃ Ψ : (((k : Unit) → dualBlocks T k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ), IsGoodProj Q Ψ :=
      fun ⟨Ψ, hΨ⟩ => h₂ ⟨_, isGoodProj_comp' hAB hBA hΨ⟩
    rw [dite_eq_right h₂, dite_eq_right h]

end

end GroundTheory.Heights₂.Heights
end
