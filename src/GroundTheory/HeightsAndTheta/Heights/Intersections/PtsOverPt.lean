module

public import GroundTheory.HeightsAndTheta.Heights.Intersections.CardLeRingKrullDim
public import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsSemilocRing

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.PtsOverPt
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

section Over

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]

def ptsOverPt (P' : Ideal (MRing ι')) (v : (Σ k, ι k) → (Σ k', ι' k')) (z : (Σ k, ι k) → ℂ) :
    Set (Set ((Σ k', ι' k') → ℂ)) :=
  {O | ∃ z' ∈ mcPts P', O = {z'' | SameOrbit z'' z'} ∧ SameOrbit (fun p => z' (v p)) z}

end Over

def GenericPointsAvoidBadLocus.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (n : ℕ)
    (G : GenFibre v P') (i : ∀ k : FibreBlock κ, ι' k.1),
    IsBlockMap κ v → IsArithVar P' (n + 1) → IsArithVar (imageZ v P') (n + 1) →
    (∀ k : FibreBlock κ, G.x' ⟨k.1, i k⟩ ≠ 0) →
    ∃ (D : MRing ι) (a : K → ℕ), ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog D a ∧ D ∉ imageZ v P' ∧
      ∀ z ∈ mcPts (imageZ v P'), eval z (map (Int.castRingHom ℂ) D) ≠ 0 →
        (ptsOverPt P' v z).ncard = Module.finrank G.Φ (IntermediateField.adjoin G.Φ
          (Set.range fun q : Σ k : FibreBlock κ, ι' k.1 => G.x' ⟨q.1.1, q.2⟩ / G.x' ⟨q.1.1, i q.1⟩))

section Inhabitants

open IndefiniteRowSideFullHecke.Inter

end Inhabitants

end GroundTheory.Heights₂.Heights.Inter
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsSemilocFinite
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter

def SemilocFinite.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (n : ℕ) (s : MRing ι) (α : K → ℕ)
    (W : Ideal (MRing ι)) (hv : IsBlockMap κ v) (hP' : IsArithVar P' (n + 1)),
    IsArithVar (imageZ v P') (n + 1) → ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s α → s ∉ imageZ v P' → W ∈ divSupp (imageZ v P') s →
    haveI := hP'.2.1.1
    letI := (locToSemiloc hv P' W).toAlgebra
    Module.Finite (locRing (imageZ v P') W) (semiLocRing P' (fibreOver v P' W)) ∧
      Module.IsTorsionFree (locRing (imageZ v P') W) (semiLocRing P' (fibreOver v P' W))

end GroundTheory.Heights₂.Heights.Inter
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.PPFFibreSum
section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsPFFibreMult
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

def PFFibreMult.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (d e : ℕ)
    (G : GenFibre v P') (s : MRing ι') (W : Ideal (MRing ι')),
    IsBlockMap κ v → IsArithVar P' e → IsArithVar (imageZ v P') d →
    W ∈ divSupp P' s → IsHorizontal W → imageZ v W = imageZ v P' →
    multAt (ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal κ G ⊔ Ideal.span {baseSubst κ G s}) (fibreOf κ G W) = multAt (P' ⊔ Ideal.span {s}) W

end

end GroundTheory.Heights₂.Heights.Inter
end

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

section Homog

variable {R : Type*} [CommRing R] {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)]

theorem weight_blockSingle (d : (Σ k, ι k) →₀ ℕ) :
    Finsupp.weight (fun q : Σ k, ι k => (Pi.single q.1 1 : K → ℕ)) d = fun k => ∑ i, d ⟨k, i⟩ := by
  funext k
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply, Fintype.sum_sigma]
  simp [Pi.single_apply]

theorem isMultiHomog_iff_weighted (f : MRingOver R ι) (a : K → ℕ) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f a ↔ IsWeightedHomogeneous (fun q : Σ k, ι k => (Pi.single q.1 1 : K → ℕ)) f a := by
  constructor
  · intro h d hd
    rw [weight_blockSingle]
    funext k
    exact h d (mem_support_iff.mpr hd) k
  · intro h m hm k
    have := h (mem_support_iff.mp hm)
    rw [weight_blockSingle] at this
    exact congrFun this k

end Homog

section Subst

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
  {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} {P' : Ideal (MRing ι')}


omit [Fintype K'] [∀ k, Fintype (ι' k)] in
theorem aeval_baseSubst (hv : IsBlockMap κ v) (G : GenFibre v P') (f : MRing ι') :
    aeval (fun q : Σ k : FibreBlock κ, ι' k.1 => G.x' ⟨q.1.1, q.2⟩) (baseSubst κ G f) = aeval G.x' f := by
  have h : ((aeval (fun q : Σ k : FibreBlock κ, ι' k.1 => G.x' ⟨q.1.1, q.2⟩) :
      MRingOver G.Φ (fibreIdx ι' κ) →ₐ[G.Φ] G.Φ').toRingHom.comp (baseSubst κ G)) =
      (aeval G.x' : MRing ι' →ₐ[ℤ] G.Φ').toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp only [show (C r : MRing ι') = (r : MRing ι') from eq_intCast C r, map_intCast]
    · intro q
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X]
      unfold baseSubst
      rw [eval₂Hom_X']
      split_ifs with h h'
      · rw [aeval_C, ← G.compat, h'.choose_spec]
      · exact absurd (hv.2.2.2 q h) h'
      · rw [aeval_X]
  exact DFunLike.congr_fun h f

theorem baseSubst_isMultiHomog (G : GenFibre v P') {s : MRing ι'} {a : K' → ℕ} (hs : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s a) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (baseSubst κ G s) (fun k : FibreBlock κ => a k.1) := by
  classical
  rw [isMultiHomog_iff_weighted] at hs ⊢
  have hg : ∀ q : Σ k', ι' k', IsWeightedHomogeneous
      (fun q : Σ k : FibreBlock κ, ι' k.1 => (Pi.single q.1 1 : FibreBlock κ → ℕ))
      (if h : q.1 ∈ Set.range κ then (if h' : q ∈ Set.range v then C (G.x h'.choose) else 0)
        else X ⟨⟨q.1, h⟩, q.2⟩ : MRingOver G.Φ (fibreIdx ι' κ))
      (fun k : FibreBlock κ => (Pi.single q.1 1 : K' → ℕ) k.1) := by
    intro q
    by_cases h : q.1 ∈ Set.range κ
    · have h0 : (fun k : FibreBlock κ => (Pi.single q.1 1 : K' → ℕ) k.1) = 0 := by
        funext k
        have : k.1 ≠ q.1 := fun e => k.2 (e ▸ h)
        simp [this]
      rw [dite_eq_left h, h0]
      split_ifs
      · exact isWeightedHomogeneous_C _ _
      · exact isWeightedHomogeneous_zero _ _ _
    · rw [dite_eq_right h]
      have e : (fun k : FibreBlock κ => (Pi.single q.1 1 : K' → ℕ) k.1) =
          (Pi.single (⟨q.1, h⟩ : FibreBlock κ) 1 : FibreBlock κ → ℕ) := by
        funext k
        simp [Pi.single_apply, Subtype.ext_iff]
      rw [e]
      exact isWeightedHomogeneous_X G.Φ _ (⟨⟨q.1, h⟩, q.2⟩ : Σ k : FibreBlock κ, ι' k.1)
  induction hs using IsWeightedHomogeneous.induction_on with
  | zero => rw [map_zero]; exact isWeightedHomogeneous_zero _ _ _
  | add p q hp hq ihp ihq => rw [map_add (f := _)]; exact ihp.add ihq
  | monomial d r hr =>
    unfold baseSubst
    rw [coe_eval₂Hom, eval₂_monomial, MvPolynomial.algebraMap_apply, Finsupp.prod]
    convert ((IsWeightedHomogeneous.prod d.support _ _ fun q _ => (hg q).pow (d q)).C_mul _) using 1
    funext k
    rw [← hr]
    simp [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply]

end Subst

theorem PFFibreSum.proof (hFD : FibreDimStatement) (hBij : PFFibreBij.Statement) (hMult : PFFibreMult.Statement) :
    PFFibreSum.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' d r G J N s a hv hP' hP hJ hNa hs hsP
  classical
  have hV : IsProjVarF (ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal κ G) (r + 1) := hFD K ι K' ι' κ v P' d (r + 1) G hv hP' hP
  have hmem : ∀ g : MRing ι', baseSubst κ G g ∈ ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal κ G ↔ g ∈ P' := by
    intro g
    rw [ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal, RingHom.mem_ker, aeval_baseSubst hv, ← RingHom.mem_ker, G.genericFibre_ker_target]
  have hsec : IsRatSection (ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal κ G) (fibreDeg κ (N (Fin.last r)).a) (baseSubst κ G s) 1 := by
    refine ⟨fun k => a k.1, 0, baseSubst_isMultiHomog G hs,
      (isMultiHomog_iff_weighted _ _).mpr (isWeightedHomogeneous_one _ _), fun h => hsP ((hmem s).mp h),
      fun h1 => hV.1.1.ne_top ((Ideal.eq_top_iff_one _).mpr h1), fun k => ?_⟩
    simp [fibreDeg, hNa]
  have hb' : J (ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal κ G) (r + 1) (fun j => fibreDeg κ (N j).a) =
      cycEval (fun W => J W r (fun j => fibreDeg κ (N (Fin.castSucc j)).a))
        (ratDiv (ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal κ G) (baseSubst κ G s) 1) := by
    rw [← hJ.2 _ r _ _ _ _ hV hsec]
    exact congrArg _ (Fin.snoc_init_self (α := fun _ => FibreBlock κ → ℤ) (fun j => fibreDeg κ (N j).a)).symm
  have hdiv1 : ReciprocityTheory.ChartRestriction.G.Geo.divCycle (ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal κ G) 1 = 0 := by
    ext W
    simp only [ReciprocityTheory.ChartRestriction.G.Geo.divCycle, Finsupp.ofSupportFinite_coe, Finsupp.coe_zero, Pi.zero_apply]
    rw [if_neg]
    simp [divSupp, Ideal.span_singleton_one, Ideal.minimalPrimes_top]
  set L := fun j : Fin r => fibreDeg κ (N (Fin.castSucc j)).a
  set V := ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal κ G
  set f := baseSubst κ G s
  have hD : ∀ Q, (ReciprocityTheory.ChartRestriction.G.Geo.divCycle V f Q : ℝ) = if Q ∈ divSupp V f then (multAt (V ⊔ Ideal.span {f}) Q : ℝ) else 0 := by
    intro Q
    simp only [ReciprocityTheory.ChartRestriction.G.Geo.divCycle, Finsupp.ofSupportFinite_coe]
    split_ifs <;> simp

  have hR : ((cycEval (fun W => J W r L) (ratDiv V f 1) : ℤ) : ℝ) =
      ∑ᶠ Q ∈ divSupp V f, (multAt (V ⊔ Ideal.span {f}) Q : ℝ) * (J Q r L : ℝ) := by
    rw [ratDiv, hdiv1, Finsupp.mapRange_zero, sub_zero, cycEval,
      Finsupp.sum_mapRange_index (fun _ => zero_mul _), Finsupp.sum, Int.cast_sum,
      finsum_mem_def]
    simp only [Int.cast_mul, Int.cast_natCast]
    have hsupp : Function.support (fun Q => (ReciprocityTheory.ChartRestriction.G.Geo.divCycle V f Q : ℝ) * (J Q r L : ℝ)) ⊆ ↑(ReciprocityTheory.ChartRestriction.G.Geo.divCycle V f).support := by
      intro Q hQ
      rw [Function.mem_support] at hQ
      rw [Finset.mem_coe, Finsupp.mem_support_iff]
      intro h0
      exact hQ (by rw [h0]; simp)
    rw [← finsum_eq_sum_of_support_subset _ hsupp]
    congr 1
    funext Q
    rw [hD]
    by_cases hQ : Q ∈ divSupp V f <;> simp [hQ, Set.indicator]

  have hL : ∑ᶠ W ∈ divSupp P' s, (multAt (P' ⊔ Ideal.span {s}) W : ℝ) *
        (if IsHorizontal W ∧ imageZ v W = imageZ v P' then (J (fibreOf κ G W) r L : ℝ) else 0) =
      ∑ᶠ W ∈ {W | W ∈ divSupp P' s ∧ IsHorizontal W ∧ imageZ v W = imageZ v P'},
        (multAt (P' ⊔ Ideal.span {s}) W : ℝ) * (J (fibreOf κ G W) r L : ℝ) := by
    rw [finsum_mem_def, finsum_mem_def]
    congr 1
    funext W
    by_cases hW : W ∈ divSupp P' s <;> by_cases hH : IsHorizontal W ∧ imageZ v W = imageZ v P' <;>
      simp [Set.indicator, hW, hH]
  rw [hb', hR, hL]
  refine finsum_mem_eq_of_bijOn (fibreOf κ G) (hBij K ι K' ι' κ v P' d (d + r + 1) G s hv hP' hP) ?_
  rintro W ⟨hW, hH, hI⟩
  rw [hMult K ι K' ι' κ v P' d (d + r + 1) G s W hv hP' hP hW hH hI]

end

end GroundTheory.Heights₂.Heights.Inter
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsMoreTail
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter

def FibreDimensionZero.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (p : ℕ) [Fact p.Prime] (W' : Ideal (MRing ι')) (n : ℕ),
    IsBlockMap κ v → ((p : ℕ) : MRing ι') ∈ W' →
    IsProjVarF (W'.map (MvPolynomial.map (Int.castRingHom (ZMod p)))) n →
    IsProjVarF (imageVar (ZMod p) v (W'.map (MvPolynomial.map (Int.castRingHom (ZMod p))))) n →
    ∀ G' : GenFibre v W', IsProjVarF (ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal κ G') 0

section Inhabitants

end Inhabitants

end GroundTheory.Heights₂.Heights.Inter
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsLocRingDimOne
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter

def LocRingDimOne.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (s : MRing ι) (a : K → ℕ)
    (W : Ideal (MRing ι)),
    IsMultiProjPrime P → ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s a → s ∉ P → W ∈ divSupp P s →
    IsNoetherianRing (locRing P W) ∧ IsLocalRing (locRing P W) ∧ ringKrullDim (locRing P W) = 1

end GroundTheory.Heights₂.Heights.Inter
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsSemilocIntegral
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter

def SemilocIntegral.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (n : ℕ) (s : MRing ι) (α : K → ℕ)
    (W : Ideal (MRing ι)) (hv : IsBlockMap κ v) (hP' : IsArithVar P' (n + 1)),
    IsArithVar (imageZ v P') (n + 1) → ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s α → s ∉ imageZ v P' → W ∈ divSupp (imageZ v P') s →
    haveI := hP'.2.1.1
    letI := (locToSemiloc hv P' W).toAlgebra
    Algebra.IsIntegral (locRing (imageZ v P') W) (semiLocRing P' (fibreOver v P' W))

end GroundTheory.Heights₂.Heights.Inter
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.ExistsSheetPullW
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M
  Topology Filter

namespace pullbackDensity_holds

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
  {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} {P' J' : Ideal (MRing ι')} {n : ℕ}
  (R : AnLogRes P' J' n) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ))


omit [Fintype K'] in
theorem pullQ_eq_local (hv : IsBlockMap κ v) {x z : R.X} (hz : z ∈ R.U x) :
    pullQ R v Ψ z = fun i => Ψ (segre (fun p => R.lift x z (v p))) i.succ /
      Ψ (segre (fun p => R.lift x z (v p))) 0 := by
  obtain ⟨c, hc, hzc⟩ := R.compat z x z ⟨R.mem_U z, hz⟩
  have hpt : pullPt R v z = fun p => c (κ p.1) * R.lift x z (v p) := by
    funext p
    simp only [pullPt, hzc, hv.2.2.1 p]
  have hpc : ∏ k, c (κ k) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hc (κ k)
  have hsm := segre_smul (fun k => c (κ k)) (fun p => R.lift x z (v p))
  funext i
  simp only [pullQ, hpt, hsm, map_smul, Pi.smul_apply, smul_eq_mul]
  exact mul_div_mul_left _ _ hpc

theorem exists_sheet_pullW (hv : IsBlockMap κ v) (hP : IsArithVar (imageZ v P') (n + 1))
    (L : Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (L' : Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι') (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (A' : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι') (s : MRing ι)
    (hL : ∀ j, IsSmoothHerm (L j)) (hLL' : ∀ j, IsPullHerm κ v (L j) (L' j)) (hAA' : IsPullHerm κ v A A')
    (hs : IsSectionOn (imageZ v P') A s) (x : R.X) (hx : x ∉ pullBad R v Ψ) :
    ∃ γ : (Fin n → ℂ) → (Σ k, ι k) → ℂ, IsSheet (imageZ v P') Ψ (pullQ R v Ψ x) (pullW R v Ψ x) γ ∧
      logNorm A s (γ (pullQ R v Ψ x)) * maDensity (fun j y' => pot L j (γ y')) (pullQ R v Ψ x) =
        logNorm A' (rename v s) (R.lift x x) * pushDens R.A (fun j => potOf R (L' j)) (pullQ R v Ψ) x := by
  classical
  obtain ⟨k0⟩ := hP.1
  have hPh : IsMultiHomogIdeal (imageZ v P') := hP.2.1.2.1
  set j := chartIdx R.A x with hjdef
  have hj : x ∈ (R.A.chart j).source := Classical.choose_spec (R.A.cover x)
  set u := R.A.chart j x with hudef
  have hsu : (R.A.chart j).symm u = x := (R.A.chart j).left_inv hj
  have huU : u ∈ (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x :=
    ⟨(R.A.chart j).map_source hj, by rw [Set.mem_preimage, hsu]; exact R.mem_U x⟩
  have hgood : AnalyticAt ℂ (pullQ R v Ψ ∘ (R.A.chart j).symm) u ∧
      LinearMap.det (fderiv ℂ (pullQ R v Ψ ∘ (R.A.chart j).symm) u :
        (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) ≠ 0 := by
    by_contra h
    exact hx (Or.inr ⟨j, hj, h⟩)
  obtain ⟨hQa, hQd⟩ := hgood
  have h0x : Ψ (segre (pullPt R v x)) 0 ≠ 0 := fun h => hx (Or.inl (Or.inr h))
  have hmemx : pullPt R v x ∈ mcPts (imageZ v P') :=
    IntersectionWithSection.comp_mem_mcPts hv (R.mem x x (R.mem_U x))
  set Q := pullQ R v Ψ ∘ (R.A.chart j).symm with hQdef
  set Df := fderiv ℂ Q u with hDf
  have hdet : Df.det ≠ 0 := hQd
  set Ce := Df.toContinuousLinearEquivOfDetNeZero hdet with hCe
  have hCe' : (Ce : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)) = Df :=
    ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero Df hdet
  have hstrict : HasStrictFDerivAt Q (Ce : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)) u := by
    rw [hCe']; exact hQa.hasStrictFDerivAt
  set F := hstrict.toOpenPartialHomeomorph Q with hF
  have hFc : (F : (Fin n → ℂ) → (Fin n → ℂ)) = Q := hstrict.toOpenPartialHomeomorph_coe
  have hus : u ∈ F.source := hstrict.mem_toOpenPartialHomeomorph_source
  have hyt : Q u ∈ F.target := hstrict.image_mem_toOpenPartialHomeomorph_target
  have hσu : F.symm (Q u) = u := by
    have := F.left_inv hus
    rwa [hFc] at this
  have hy0 : Q u = pullQ R v Ψ x := by simp only [hQdef, Function.comp_apply, hsu]
  have hσa : AnalyticAt ℂ F.symm (Q u) := by
    refine F.analyticAt_symm (i := Ce) hyt ?_ ?_
    · rw [hσu, hFc]; exact hQa
    · rw [hσu, hFc, hCe']
  have hσd : HasFDerivAt F.symm (Ce.symm : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)) (Q u) := by
    refine F.hasFDerivAt_symm hyt ?_
    rw [hσu, hFc, hCe']
    exact hQa.differentiableAt.hasFDerivAt
  have hl₀ : AnalyticAt ℂ (fun w => fun p => R.lift x ((R.A.chart j).symm w) (v p)) u :=
    analyticAt_pi_iff.mpr fun p => analyticAt_pi_iff.mp (analyticAt_lift_chart R x j huU) (v p)
  set γ₀ : (Fin n → ℂ) → (Σ k, ι k) → ℂ :=
    fun y' p => R.lift x ((R.A.chart j).symm (F.symm y')) (v p) with hγ₀
  have hγ₀a : AnalyticAt ℂ γ₀ (Q u) := hl₀.comp_of_eq hσa hσu
  have hγ₀u : γ₀ (Q u) = pullPt R v x := by
    funext p
    simp only [hγ₀, hσu, hsu, pullPt]
  have hsegl : AnalyticAt ℂ (fun w => Ψ (segre (fun p => R.lift x ((R.A.chart j).symm w) (v p)))) u := by
    have hs' : AnalyticAt ℂ (fun w => segre (fun p => R.lift x ((R.A.chart j).symm w) (v p))) u := by
      refine analyticAt_pi_iff.mpr fun i => ?_
      simp only [segre]
      exact Finset.analyticAt_fun_prod _ fun k _ => analyticAt_pi_iff.mp hl₀ _
    exact (LinearMap.toContinuousLinearMap Ψ).analyticAt _ |>.comp hs'
  set ψ0 : (Fin n → ℂ) → ℂ := fun y' => Ψ (segre (γ₀ y')) 0 with hψ0
  have hψ0a : AnalyticAt ℂ ψ0 (Q u) :=
    analyticAt_pi_iff.mp (hsegl.comp_of_eq hσa hσu) 0
  have hψ0u : ψ0 (Q u) ≠ 0 := by
    simp only [hψ0, hγ₀u]; exact h0x
  set c : (Fin n → ℂ) → K → ℂ := fun y' => Function.update (fun _ => (1 : ℂ)) k0 (ψ0 y')⁻¹
    with hcdef
  have hc_ne : ∀ y', ψ0 y' ≠ 0 → ∀ k, c y' k ≠ 0 := by
    intro y' h k
    by_cases hk : k = k0
    · subst hk; simp [hcdef, h]
    · simp [hcdef, Function.update_of_ne hk]
  have hca : ∀ k, AnalyticAt ℂ (fun y' => c y' k) (Q u) := by
    intro k
    by_cases hk : k = k0
    · subst hk; simp only [hcdef, Function.update_self]; exact hψ0a.inv hψ0u
    · simp only [hcdef, Function.update_of_ne hk]; exact analyticAt_const
  set γ : (Fin n → ℂ) → (Σ k, ι k) → ℂ := fun y' => bsmul (c y') (γ₀ y') with hγdef
  have hγa : AnalyticAt ℂ γ (Q u) :=
    analyticAt_pi_iff.mpr fun p => (hca p.1).mul (analyticAt_pi_iff.mp hγ₀a p)
  have hprod : ∀ y', ∏ k, c y' k = (ψ0 y')⁻¹ := fun y' => by
    simp [hcdef, Finset.prod_update_of_mem (Finset.mem_univ k0)]
  have hseg : ∀ y', segre (γ y') = (ψ0 y')⁻¹ • segre (γ₀ y') := fun y' => by
    rw [← hprod y']; exact segre_smul (c y') (γ₀ y')
  refine ⟨γ, ⟨?_, ?_⟩, ?_⟩
  · rw [← hy0, hseg]
    simp only [hψ0, hγ₀u]
    rfl
  · rw [← hy0]
    have hU : ∀ᶠ y' in 𝓝 (Q u),
        F.symm y' ∈ (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x :=
      hσa.continuousAt.preimage_mem_nhds (by
        rw [hσu]; exact ((R.A.chart j).isOpen_inter_preimage_symm (R.isOpen_U x)).mem_nhds huU)
    filter_upwards [hγa.eventually_analyticAt, hU, F.open_target.mem_nhds hyt,
      hψ0a.continuousAt.eventually_ne hψ0u] with y' ha hUy ht h0
    refine ⟨ha.differentiableAt, mcPts_smul hPh (c y') (hc_ne y' h0)
      (IntersectionWithSection.comp_mem_mcPts hv (R.mem x _ hUy.2)), ?_⟩
    have hq : Q (F.symm y') = y' := by
      have := F.right_inv ht
      rwa [hFc] at this
    rw [hQdef, Function.comp_apply, pullQ_eq_local R Ψ hv hUy.2] at hq
    rw [hseg, map_smul]
    funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp only [Pi.smul_apply, smul_eq_mul, Fin.cons_zero]
      exact inv_mul_cancel₀ h0
    · simp only [Pi.smul_apply, smul_eq_mul, Fin.cons_succ]
      rw [← congrFun hq i, div_eq_inv_mul]
  · rw [← hy0]
    obtain ⟨a, ha, hsa, -⟩ := hs
    have hlog : logNorm A s (γ (Q u)) = logNorm A' (rename v s) (R.lift x x) := by
      show logNorm A s (bsmul (c (Q u)) (γ₀ (Q u))) = _
      rw [logNorm_bsmul A ha hsa (hc_ne _ hψ0u), hγ₀u]
      unfold logNorm
      rw [hAA'.2 (R.lift x x), map_rename, eval_rename]
      rfl
    rw [hlog]
    congr 1
    have hblk : ∀ k, ∃ i, γ₀ (Q u) ⟨k, i⟩ ≠ 0 := by
      rw [hγ₀u]; exact hmemx.1
    have hH : ∀ i, cxHessian (fun y' => pot L i (γ y')) (Q u) =
        cxHessian (fun y' => pot L i (γ₀ y')) (Q u) := by
      intro i
      set G : (Fin n → ℂ) → ℂ :=
        fun y' => ((-((L i).a k0 : ℝ) : ℝ) : ℂ) * Complex.log (ψ0 y' / ψ0 (Q u)) with hG
      set C : ℝ := -(((L i).a k0 : ℝ) * Real.log ‖ψ0 (Q u)‖) with hC
      have hGa : AnalyticAt ℂ G (Q u) := by
        refine analyticAt_const.mul ((hψ0a.div analyticAt_const hψ0u).clog ?_)
        show ψ0 (Q u) / ψ0 (Q u) ∈ Complex.slitPlane
        rw [div_self hψ0u]
        exact Complex.one_mem_slitPlane
      have heq : (fun y' => pot L i (γ y')) =ᶠ[𝓝 (Q u)]
          fun y' => pot L i (γ₀ y') + (G y').re + C := by
        filter_upwards [hψ0a.continuousAt.eventually_ne hψ0u,
          hγ₀a.continuousAt.eventually (isOpen_blockNonzero.mem_nhds hblk)] with y' h0 hb
        have hpos : 0 < (L i).h (γ₀ y') := (L i).pos _ hb
        have hn0 : ‖(ψ0 y')⁻¹‖ ^ (L i).a k0 ≠ 0 :=
          zpow_ne_zero _ (norm_ne_zero_iff.mpr (inv_ne_zero h0))
        simp only [pot, hγdef]
        rw [show bsmul (c y') (γ₀ y') = fun p => c y' p.1 * γ₀ y' p from rfl,
          (L i).smul _ _ (hc_ne y' h0), prod_norm_update_zpow, Real.log_mul hn0 hpos.ne',
          hG, hC, Complex.re_ofReal_mul, Complex.log_re, norm_div,
          Real.log_div (norm_ne_zero_iff.mpr h0) (norm_ne_zero_iff.mpr hψ0u), Real.log_zpow,
          norm_inv, Real.log_inv]
        ring
      rw [cxHessian_congr heq, cxHessian_add_re (φ := fun y' => pot L i (γ₀ y')) C
        (ReciprocityTheory.ChartRestriction.G.Geo.pot_contDiffAt (hL i) hγ₀a hblk) hGa]
    have hmd : maDensity (fun i y' => pot L i (γ y')) (Q u) =
        maDensity (fun i y' => pot L i (γ₀ y')) (Q u) := by
      simp only [maDensity, hH]
    rw [hmd, maDensity_eq_maDens]
    have hcd : ∀ i, ContDiffAt ℝ 2
        (fun w => pot L i (fun p => R.lift x ((R.A.chart j).symm w) (v p))) (F.symm (Q u)) := by
      intro i
      rw [hσu]
      refine ReciprocityTheory.ChartRestriction.G.Geo.pot_contDiffAt (hL i) hl₀ ?_
      show ∀ k, ∃ i, R.lift x ((R.A.chart j).symm u) (v ⟨k, i⟩) ≠ 0
      rw [hsu]
      exact hmemx.1
    have hcomp : ReciprocityTheory.AnForm.maDens (fun i y' => pot L i (γ₀ y')) (Q u) =
        ReciprocityTheory.AnForm.maDens (fun i w => pot L i (fun p => R.lift x ((R.A.chart j).symm w) (v p)))
          (F.symm (Q u)) * Complex.normSq (ReciprocityTheory.AnForm.A.jacC F.symm (Q u)).det :=
      ReciprocityTheory.AnForm.A.maDens_comp
        (fun i w => pot L i (fun p => R.lift x ((R.A.chart j).symm w) (v p))) F.symm (Q u) hσa hcd
    have hdetinv : LinearMap.det ((Ce.symm : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)) :
        (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) =
          (LinearMap.det (Df : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)))⁻¹ := by
      have := ContinuousLinearEquiv.det_coe_symm Ce
      rw [hCe'] at this
      exact this
    have hloc : ReciprocityTheory.AnForm.maDens
        (fun i w => pot L i (fun p => R.lift x ((R.A.chart j).symm w) (v p))) u =
          locDens R.A (fun i => potOf R (L' i)) j u := by
      unfold locDens
      rw [hsu]
      congr 1
      funext i w
      show Real.log ((L i).h _) = Real.log ((L' i).h _)
      rw [(hLL' i).2]
    rw [hcomp, hσu, ReciprocityTheory.AnForm.A.det_jacC, hσd.fderiv, hdetinv, hloc, Complex.normSq_inv,
      Complex.normSq_eq_norm_sq]
    unfold pushDens
    rw [div_eq_mul_inv]

end pullbackDensity_holds

theorem pullbackDensity_holds.proof : pullbackDensity_holds.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' J' n R Ψ L L' A A' s hv _hP' hP hΨ hL hLL' hA hAA' hs
  filter_upwards [sheetIndep K ι (imageZ v P') n Ψ L A s hP hΨ hL hA hs] with y hind
  intro x hx
  obtain ⟨γ, hγ, hval⟩ := pullbackDensity_holds.exists_sheet_pullW R Ψ hv hP L L' A A' s hL hLL' hAA' hs x hx.2
  rw [show pullQ R v Ψ x = y from hx.1] at hγ hval
  unfold sheetDensity
  rw [dite_eq_left ⟨γ, hγ⟩]
  exact ((hind _ _ _ (Exists.choose_spec
    (⟨γ, hγ⟩ : ∃ γ, IsSheet (imageZ v P') Ψ y (pullW R v Ψ x) γ)) hγ).trans hval).symm

end GroundTheory.Heights₂.Heights.Inter
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.StLocRingInj
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def LocRingInj.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P W W' : Ideal (MRing ι)),
    P.IsPrime → IsMultiProjPrime W → IsMultiProjPrime W' → P ≤ W → P ≤ W' →
    locRing P W = locRing P W' → W = W'

end

end GroundTheory.Heights₂.Heights.Inter
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsMoreTer
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def RegularityLocalize.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P W : Ideal (MRing ι))
    (y : FractionRing (MRing ι ⧸ P)),
    IsArithVar P 1 → IsClosedPt W → P ≤ W → y ∈ locRing P W →
    ∃ s x : regRing P, (∃ z ∈ locRing P W, ((s : funField P) : FractionRing (MRing ι ⧸ P)) * z = 1) ∧
      y * ((s : funField P) : FractionRing (MRing ι ⧸ P)) = ((x : funField P) : FractionRing (MRing ι ⧸ P))

end

end GroundTheory.Heights₂.Heights.Inter
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsLocRingIntClosure
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter

def LocRingIntClosureFinite.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (n : ℕ) (s : MRing ι) (α : K → ℕ)
    (W : Ideal (MRing ι)) (_hv : IsBlockMap κ v) (hP' : IsArithVar P' (n + 1)),
    IsArithVar (imageZ v P') (n + 1) → ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s α → s ∉ imageZ v P' → W ∈ divSupp (imageZ v P') s →
    haveI := hP'.2.1.1
    letI := ((fracMapZ v P').comp (locRing (imageZ v P') W).subtype).toAlgebra
    letI : Module (locRing (imageZ v P') W) (FractionRing (MRing ι' ⧸ P')) := Algebra.toModule
    ∃ t : Finset (FractionRing (MRing ι' ⧸ P')), ∀ x ∈ semiLocRing P' ∅,
      IsIntegral (locRing (imageZ v P') W) x → x ∈ Submodule.span (locRing (imageZ v P') W) (t : Set _)

end GroundTheory.Heights₂.Heights.Inter
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsSemilocRank
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter

def SemilocRank.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (n : ℕ)
    (G : GenFibre v P') (J : IFamily G.Φ (fibreIdx ι' κ)) (s : MRing ι) (α : K → ℕ)
    (W : Ideal (MRing ι)) (hv : IsBlockMap κ v) (hP' : IsArithVar P' (n + 1)),
    IsArithVar (imageZ v P') (n + 1) → IsFieldIntersection J → ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s α → s ∉ imageZ v P' →
    W ∈ divSupp (imageZ v P') s →
    haveI := hP'.2.1.1
    letI := (locToSemiloc hv P' W).toAlgebra
    (Module.finrank (locRing (imageZ v P') W) (semiLocRing P' (fibreOver v P' W)) : ℤ) =
      J (ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal κ G) 0 Fin.elim0

end GroundTheory.Heights₂.Heights.Inter
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsFurtherRest
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

def PullbackEliminationOfVariable.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' J' : Ideal (MRing ι')) (n : ℕ),
    IsBlockMap κ v → IsArithVar P' (n + 1) → IsArithVar (imageZ v P') (n + 1) →
    IsMultiHomogIdeal J' → ¬ J' ≤ P' →
    ∃ (h : MRing ι) (a : K → ℕ), ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog h a ∧ h ∉ imageZ v P' ∧
      ∀ z' ∈ mcPts P', z' ∈ mcPts J' → eval (fun p => z' (v p)) (map (Int.castRingHom ℂ) h) = 0

section Inhabitants

open IndefiniteRowSideFullHecke.Inter

end Inhabitants

end GroundTheory.Heights₂.Heights.Inter
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsFurtherSide
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter

def VerticalDegreeAfterAdjoining.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (p : ℕ) [Fact p.Prime] (W' : Ideal (MRing ι')) (n : ℕ)
    (i' : ∀ k', ι' k'),
    IsBlockMap κ v → ((p : ℕ) : MRing ι') ∈ W' →
    IsProjVarF (W'.map (MvPolynomial.map (Int.castRingHom (ZMod p)))) n →
    IsProjVarF (imageVar (ZMod p) v (W'.map (MvPolynomial.map (Int.castRingHom (ZMod p))))) n →
    IsChart (W'.map (MvPolynomial.map (Int.castRingHom (ZMod p)))) i' →
    ∀ G' : GenFibre v W',
      fnDeg v (W'.map (MvPolynomial.map (Int.castRingHom (ZMod p)))) i' =
        Module.finrank G'.Φ (IntermediateField.adjoin G'.Φ
          (Set.range fun q : Σ k : FibreBlock κ, ι' k.1 => G'.x' ⟨q.1.1, q.2⟩ / G'.x' ⟨q.1.1, i' q.1.1⟩))

section Inhabitants

end Inhabitants

end GroundTheory.Heights₂.Heights.Inter
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsSemilocLength
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter

def SemilocLength.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (n : ℕ) (s t : MRing ι) (α : K → ℕ)
    (W : Ideal (MRing ι)) (E : Ideal (MRing ι') → ℤ) (hv : IsBlockMap κ v) (hP' : IsArithVar P' (n + 1))
    (y : locRing (imageZ v P') W),
    IsArithVar (imageZ v P') (n + 1) → ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s α → ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog t α → s ∉ imageZ v P' →
    W ∈ divSupp (imageZ v P') s → t ∉ W →
    (y : FractionRing (MRing ι ⧸ imageZ v P')) * algebraMap _ _ (Ideal.Quotient.mk (imageZ v P') t) =
      algebraMap _ _ (Ideal.Quotient.mk (imageZ v P') s) →
    (∀ W' ∈ divSupp P' (rename v s), imageZ v W' = W →
      ∃ (G' : GenFibre v W') (J' : IFamily G'.Φ (fibreIdx ι' κ)),
        IsFieldIntersection J' ∧ E W' = J' (ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal κ G') 0 Fin.elim0) →
    haveI := hP'.2.1.1
    letI := (locToSemiloc hv P' W).toAlgebra
    ∃ N : ℕ, Module.length (locRing (imageZ v P') W)
        (semiLocRing P' (fibreOver v P' W) ⧸ LinearMap.range
          (LinearMap.lsmul (locRing (imageZ v P') W) (semiLocRing P' (fibreOver v P' W)) y)) = N ∧
      (N : ℤ) = ∑ᶠ W' ∈ {W' | W' ∈ divSupp P' (rename v s) ∧ imageZ v W' = W},
        (multAt (P' ⊔ Ideal.span {rename v s}) W' : ℤ) * E W'

end GroundTheory.Heights₂.Heights.Inter
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsAlt
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 PointVertical

theorem ArithmeticIntersectionVertical.proof
    (hGeo : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)], GeoNumStatement ι)
    (hR4 : ∀ (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)],
      ExistsUniqueStatement F ι)
    (hPC : ∀ (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)], ProjContractStatement F ι ι')
    (hPD : ∀ (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)], ProjDegStatement F ι ι')
    (hDeg : VerticalDegree.Statement) :
    ArithmeticIntersectionVertical.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' n a s α W' hv hP' hP hs hsP hW' hvert
  classical

  have hs' : IsSectionOn P' (ReciprocityTheory.ChartRestriction.G.Geo.HermLine.sqMetric (ι := ι') (Function.extend κ α 0)) (rename v s) :=
    ⟨Function.extend κ α 0, fun _ => rfl, isMultiHomog_rename hv hs, hsP⟩
  obtain ⟨hW'm, hpr, hW'd⟩ := (divSuppArith K' ι' P' n _ _ W' hP' hs' hW').2 hvert
  set p := charOf W' with hpdef
  have : Fact p.Prime := ⟨hpr⟩
  have hpW' : ((p : ℕ) : MRing ι') ∈ W' := ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.natCast_mem_of_charOf W'
  have hW'p : IsProjVarF (W'.map (red p)) n :=
    ⟨isMultiProjPrime_red p hW'm hpW', by rw [ringKrullDim_red p hpW', hW'd]⟩

  have hWm : IsMultiProjPrime (imageZ v W') := isMultiProjPrime_imageZ hv hW'm
  have hpW : ((p : ℕ) : MRing ι) ∈ imageZ v W' := by
    show rename v ((p : ℕ) : MRing ι) ∈ W'
    simpa using hpW'
  have hVm := isMultiProjPrime_red p hWm hpW

  obtain ⟨I, hI, -⟩ := hR4 (ZMod p) K ι
  obtain ⟨I', hI', -⟩ := hR4 (ZMod p) K' ι'
  have hgeo' : geoNum n W' (fun j => pullDeg κ (a j)) = I' (W'.map (red p)) n (fun j => pullDeg κ (a j)) :=
    hGeo K' ι' p I' hI' W' n _ hW'm hpW' hW'p
  by_cases hmem : imageZ v W' ∈ divSupp (imageZ v P') s
  ·
    refine Or.inl ⟨hmem, fun G' J' hJ' => ?_⟩
    have hsW : IsSectionOn (imageZ v P') (ReciprocityTheory.ChartRestriction.G.Geo.HermLine.sqMetric (ι := ι) α) s := ⟨α, fun _ => rfl, hs, hsP⟩
    have hWvert : ¬ IsHorizontal (imageZ v W') := fun h => by
      have h2 : ((p : ℕ) : ℤ) ∈ (imageZ v W').comap (C : ℤ →+* MRing ι) := by
        rw [Ideal.mem_comap, map_natCast]
        exact hpW
      rw [h, Ideal.mem_bot] at h2
      exact hpr.ne_zero (by exact_mod_cast h2)
    obtain ⟨-, -, hWd⟩ := (divSuppArith K ι (imageZ v P') n _ _ _ hP hsW hmem).2 hWvert
    have hWp : IsProjVarF ((imageZ v W').map (red p)) n := ⟨hVm, by rw [ringKrullDim_red p hpW, hWd]⟩
    have hVi : IsProjVarF (imageVar (ZMod p) v (W'.map (red p))) n := by
      rw [imageVar_red p v hpW']
      exact hWp
    obtain ⟨i', hi'⟩ : ∃ i' : ∀ k', ι' k', IsChart (W'.map (red p)) i' :=
      ⟨fun k => (hW'p.1.2.2 k).choose, fun k => (hW'p.1.2.2 k).choose_spec⟩
    rw [hgeo', hPD (ZMod p) K ι K' ι' I I' hI hI' κ v _ n a i' hv hW'p hVi hi', imageVar_red p v hpW',
      ← hGeo K ι p I hI _ n a hWm hpW hWp, hDeg K ι K' ι' κ v p W' n i' hv hpW' hW'p hVi hi' G' J' hJ']
  ·
    refine Or.inr ⟨hmem, ?_⟩
    have hsW' : rename v s ∈ W' := hW'.1.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    have hle : imageZ v P' ⊔ Ideal.span {s} ≤ imageZ v W' :=
      sup_le (Ideal.comap_mono (le_sup_left.trans hW'.1.1.2))
        (Ideal.span_le.2 (Set.singleton_subset_iff.2 hsW'))
    have := hWm.1
    obtain ⟨Q, hQ, hQW⟩ := Ideal.exists_minimalPrimes_le hle
    have hQne : Q ≠ imageZ v W' := fun h => hmem ⟨h ▸ hQ, hWm.2.2⟩
    obtain ⟨x, hxW, hxQ⟩ : ∃ x ∈ imageZ v W', x ∉ Q := by
      by_contra hc
      exact hQne (le_antisymm hQW fun y hy => by_contra fun h => hc ⟨y, hy, h⟩)
    have := hQ.1.1
    have := hP.2.1.1
    have h1 := dim_quot_minimal_add_one (imageZ v P') Q s hsP hQ
    rw [hP.2.2.2] at h1
    have hQd : ringKrullDim (MRing ι ⧸ Q) = ((n + Fintype.card K : ℕ) : WithBot ℕ∞) :=
      withBot_eq_of_add_one (by rw [h1, show n + 1 + Fintype.card K = n + Fintype.card K + 1 by omega])
    have hdim := krullDim_quot_add_one_le hQW hxW hxQ
    obtain ⟨D, hKD, hD⟩ := exists_dim_F p _ hVm
    rw [← ringKrullDim_red p hpW, hD, hQd] at hdim
    have hD' : D + 1 ≤ n + Fintype.card K := by exact_mod_cast hdim
    have hVi : IsProjVarF (imageVar (ZMod p) v (W'.map (red p))) (D - Fintype.card K) := by
      rw [imageVar_red p v hpW']
      exact ⟨hVm, by rw [hD, Nat.sub_add_cancel hKD]⟩
    rw [hgeo']
    exact hPC (ZMod p) K ι K' ι' I' hI' κ v _ n (D - Fintype.card K) a hv hW'p hVi (by omega)

end GroundTheory.Heights₂.Heights.Inter
end
end
