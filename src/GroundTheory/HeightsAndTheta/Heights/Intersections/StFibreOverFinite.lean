module

public import GroundTheory.HeightsAndTheta.Heights.Intersections.PtsOverPt

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.StFibreOverFinite
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter

def FibreOverFinite.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (n : ℕ) (s : MRing ι) (α : K → ℕ)
    (W : Ideal (MRing ι)), IsBlockMap κ v → IsArithVar P' (n + 1) →
    IsArithVar (imageZ v P') (n + 1) → ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s α → s ∉ imageZ v P' → W ∈ divSupp (imageZ v P') s →
    (fibreOver v P' W).Finite

end GroundTheory.Heights₂.Heights.Inter
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsFibreDivSupp
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter

def FibreDivSupp.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (n : ℕ) (s : MRing ι) (α : K → ℕ)
    (W : Ideal (MRing ι)), IsBlockMap κ v → IsArithVar P' (n + 1) →
    IsArithVar (imageZ v P') (n + 1) → ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s α → s ∉ imageZ v P' → W ∈ divSupp (imageZ v P') s →
    ∀ W' : Ideal (MRing ι'),
      (W' ∈ fibreOver v P' W ∧ rename v s ∈ W') ↔ (W' ∈ divSupp P' (rename v s) ∧ imageZ v W' = W)

end GroundTheory.Heights₂.Heights.Inter
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.PtsOverChart
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

section Over

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]

def ptsOverChart (P' : Ideal (MRing ι')) (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k'))
    (j : ∀ k : FibreBlock κ, ι' k.1) (z : (Σ k, ι k) → ℂ) : Set (Set ((Σ k', ι' k') → ℂ)) :=
  {O | ∃ z' ∈ mcPts P', O = {z'' | SameOrbit z'' z'} ∧ SameOrbit (fun p => z' (v p)) z ∧
    ∀ k : FibreBlock κ, z' ⟨k.1, j k⟩ ≠ 0}

end Over

def GenericPointsInAffineChart.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (n : ℕ)
    (G : GenFibre v P') (j : ∀ k : FibreBlock κ, ι' k.1),
    IsBlockMap κ v → IsArithVar P' (n + 1) → IsArithVar (imageZ v P') (n + 1) →
    (∀ k : FibreBlock κ, G.x' ⟨k.1, j k⟩ ≠ 0) →
    ∃ (D : MRing ι) (a : K → ℕ), ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog D a ∧ D ∉ imageZ v P' ∧
      ∀ z ∈ mcPts (imageZ v P'), eval z (map (Int.castRingHom ℂ) D) ≠ 0 →
        (ptsOverChart P' κ v j z).Finite ∧
        (ptsOverChart P' κ v j z).ncard = Module.finrank G.Φ (IntermediateField.adjoin G.Φ
          (Set.range fun q : Σ k : FibreBlock κ, ι' k.1 => G.x' ⟨q.1.1, q.2⟩ / G.x' ⟨q.1.1, j q.1⟩)) ∧
        ∀ z' ∈ mcPts P', SameOrbit (fun p => z' (v p)) z → (∀ k : FibreBlock κ, z' ⟨k.1, j k⟩ ≠ 0) →
          ∀ q : Σ k : FibreBlock κ, ι' k.1, G.x' ⟨q.1.1, q.2⟩ ≠ 0 → z' ⟨q.1.1, q.2⟩ ≠ 0

end GroundTheory.Heights₂.Heights.Inter
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.IntCastMemRegMaxAt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem regRing_mem_locRing {P W : Ideal (MRing ι)} (hW : IsClosedPt W) (hPW : P ≤ W) (x : regRing P) :
    ((x : funField P) : FractionRing (MRing ι ⧸ P)) ∈ locRing P W :=
  x.2 W hW hPW

def regToLoc (P W : Ideal (MRing ι)) (hW : IsClosedPt W) (hPW : P ≤ W) : regRing P →+* locRing P W where
  toFun x := ⟨((x : funField P) : FractionRing (MRing ι ⧸ P)), regRing_mem_locRing hW hPW x⟩
  map_one' := Subtype.ext (by simp)
  map_mul' _ _ := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' _ _ := Subtype.ext (by simp)

theorem regToLoc_apply {P W : Ideal (MRing ι)} (hW : IsClosedPt W) (hPW : P ≤ W) (x : regRing P) :
    regToLoc P W hW hPW x = ⟨((x : funField P) : FractionRing (MRing ι ⧸ P)), regRing_mem_locRing hW hPW x⟩ :=
  rfl

theorem regToLoc_coe {P W : Ideal (MRing ι)} (hW : IsClosedPt W) (hPW : P ≤ W) (x : regRing P) :
    ((regToLoc P W hW hPW x : locRing P W) : FractionRing (MRing ι ⧸ P)) =
      ((x : funField P) : FractionRing (MRing ι ⧸ P)) :=
  (congrArg Subtype.val (regToLoc_apply hW hPW x)).trans (Subtype.coe_mk _ _)

def regMaxAt (P W : Ideal (MRing ι)) (hW : IsClosedPt W) (hPW : P ≤ W) (hloc : IsLocalRing (locRing P W)) :
    Ideal (regRing P) :=
  (IsLocalRing.maximalIdeal (locRing P W)).comap (regToLoc P W hW hPW)

theorem not_mem_regMaxAt_iff {P W : Ideal (MRing ι)} (hW : IsClosedPt W) (hPW : P ≤ W)
    (hloc : IsLocalRing (locRing P W)) (x : regRing P) :
    x ∉ regMaxAt P W hW hPW hloc ↔
      ∃ z ∈ locRing P W, ((x : funField P) : FractionRing (MRing ι ⧸ P)) * z = 1 := by
  have hc : ∀ b : locRing P W, ((regToLoc P W hW hPW x * b : locRing P W) : FractionRing (MRing ι ⧸ P)) =
      ((x : funField P) : FractionRing (MRing ι ⧸ P)) * b := fun b => by
    rw [Subring.coe_mul, regToLoc_coe]
  simp only [regMaxAt, Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]
  constructor
  · intro h
    obtain ⟨b, hb⟩ := h.exists_right_inv
    refine ⟨b.1, b.2, ?_⟩
    rw [← hc b, hb, Subring.coe_one]
  · rintro ⟨z, hz, h⟩
    refine IsUnit.of_mul_eq_one (a := regToLoc P W hW hPW x) ⟨z, hz⟩ (Subtype.ext ?_)
    rw [hc, Subring.coe_one]
    exact h

theorem intCast_mem_regMaxAt (hL : LocRingLocal.Statement) {P W : Ideal (MRing ι)} (hPp : P.IsPrime)
    (hW : IsClosedPt W) (hPW : P ≤ W) (hloc : IsLocalRing (locRing P W)) {n : ℤ} (hn : C n ∈ W) :
    (n : regRing P) ∈ regMaxAt P W hW hPW hloc := by
  by_contra h
  obtain ⟨z, hz, h⟩ := (not_mem_regMaxAt_iff hW hPW hloc _).1 h
  have h1W : (1 : MRing ι) ∉ W := fun h => hW.1.1.ne_top ((Ideal.eq_top_iff_one _).mpr h)
  have hu := ((hL K ι P W hPp hW.1.1 hPW).2 (n : locRing P W) (C n) 1 0 (RegularityDenominator.isMultiHomog_C n)
    AvoidRing.isMultiHomog_one h1W (by simp [eq_intCast C n])).1
  refine hu (IsUnit.of_mul_eq_one (a := (n : locRing P W)) ⟨z, hz⟩ (Subtype.ext ?_)) hn
  simpa using h

theorem regMaxAt_isMaximal (hO : RegularityOrder.Statement) (hL : LocRingLocal.Statement) {P W : Ideal (MRing ι)}
    (hP : IsArithVar P 1) (hW : IsClosedPt W) (hPW : P ≤ W) (hloc : IsLocalRing (locRing P W)) :
    (regMaxAt P W hW hPW hloc).IsMaximal := by
  have : (regMaxAt P W hW hPW hloc).IsPrime := by unfold regMaxAt; infer_instance
  have : Module.Finite ℤ (regRing P) := (hO K ι P hP).2.1
  have hvert : W.comap (C : ℤ →+* MRing ι) ≠ ⊥ := fun hh =>
    arithVarZero K ι W ⟨hP.1, hW.1, hh, by rw [zero_add]; exact hW.2⟩
  obtain ⟨n, hnW, hn0⟩ := (Submodule.ne_bot_iff _).mp hvert
  have hn : n ∈ (regMaxAt P W hW hPW hloc).comap (algebraMap ℤ (regRing P)) := by
    rw [Ideal.mem_comap, algebraMap_int_eq, eq_intCast]
    exact intCast_mem_regMaxAt hL hP.2.1.1 hW hPW hloc hnW
  exact Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (algebraMap ℤ (regRing P))
    Algebra.IsIntegral.isIntegral _
    (_root_.IsPrime.to_maximal_ideal fun h => hn0 (by rw [h] at hn; exact hn))

theorem RegularityMaximalSpectrum.proof (hO : RegularityOrder.Statement)
    (hZ : RegularityLocalize.Statement) (hI : LocRingInj.Statement) (hS : RegularityMaximalSurjective.Statement) :
    RegularityMaximalSpectrum.Statement := by
  classical
  have hL : LocRingLocal.Statement := LocRingLocal.proof LocRingFrac.proof
  intro K _ ι _ P hP
  have hPp : P.IsPrime := hP.2.1.1
  have hloc : ∀ W : {W : Ideal (MRing ι) // IsClosedPt W ∧ P ≤ W}, IsLocalRing (locRing P W.1) :=
    fun W => (hL K ι P W.1 hPp W.2.1.1.1 W.2.2).1
  let m : {W : Ideal (MRing ι) // IsClosedPt W ∧ P ≤ W} → Ideal (regRing P) := fun W =>
    regMaxAt P W.1 W.2.1 W.2.2 (hloc W)
  have hm : ∀ W (x : regRing P), x ∉ m W ↔
      ∃ z ∈ locRing P W.1, ((x : funField P) : FractionRing (MRing ι ⧸ P)) * z = 1 :=
    fun W => not_mem_regMaxAt_iff W.2.1 W.2.2 (hloc W)

  have hsub : ∀ W W', m W = m W' → locRing P W.1 ≤ locRing P W'.1 := by
    intro W W' hWW' y hy
    obtain ⟨s, x, hsu, hys⟩ := hZ K ι P W.1 y hP W.2.1 W.2.2 hy
    obtain ⟨z, hz, hsz⟩ := (hm W' s).1 (hWW' ▸ (hm W s).2 hsu)
    rw [show y = ((x : funField P) : FractionRing (MRing ι ⧸ P)) * z by rw [← hys, mul_assoc, hsz, mul_one]]
    exact mul_mem (regRing_mem_locRing W'.2.1 W'.2.2 x) hz
  let f : {W : Ideal (MRing ι) // IsClosedPt W ∧ P ≤ W} → MaximalSpectrum (regRing P) := fun W =>
    ⟨m W, regMaxAt_isMaximal hO hL hP W.2.1 W.2.2 (hloc W)⟩
  have hbij : Function.Bijective f := by
    refine ⟨fun W W' h => Subtype.ext (hI K ι P W.1 W'.1 hPp W.2.1.1 W'.2.1.1 W.2.2 W'.2.2
      (le_antisymm (hsub W W' (congrArg MaximalSpectrum.asIdeal h))
        (hsub W' W (congrArg MaximalSpectrum.asIdeal h).symm))), ?_⟩
    rintro ⟨M, hM⟩
    obtain ⟨W, hWc, hPW, hW⟩ := hS K ι P hP M hM
    refine ⟨⟨W, hWc, hPW⟩, ?_⟩
    have hle : M ≤ m ⟨W, hWc, hPW⟩ := fun x hx => by
      by_contra hc
      obtain ⟨z, hz, h⟩ := (hm _ x).1 hc
      exact hW x hx z hz h
    exact MaximalSpectrum.ext (hM.eq_of_le (regMaxAt_isMaximal hO hL hP hWc hPW _).ne_top hle).symm
  refine ⟨Equiv.ofBijective f hbij, fun W y => ⟨fun hy => ?_, ?_⟩⟩
  · obtain ⟨s, x, hsu, hys⟩ := hZ K ι P W.1 y hP W.2.1 W.2.2 hy
    exact ⟨x, s, (hm W s).2 hsu, hys⟩
  · rintro ⟨x, s, hs, hys⟩
    obtain ⟨z, hz, hsz⟩ := (hm W s).1 hs
    rw [show y = ((x : funField P) : FractionRing (MRing ι ⧸ P)) * z by rw [← hys, mul_assoc, hsz, mul_one]]
    exact mul_mem (regRing_mem_locRing W.2.1 W.2.2 x) hz

end

end GroundTheory.Heights₂.Heights.Inter
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsEvalKerKrullDim
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

def EvalKerKrullDim.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (F L : Type) [Field F] [Field L] [Algebra F L]
    (y : (Σ k, ι k) → L),
    ringKrullDim (MRingOver F ι ⧸ RingHom.ker (aeval y : MRingOver F ι →ₐ[F] L)) =
      ((Algebra.trdeg F (IntermediateField.adjoin F (Set.range y))).toENat : WithBot ℕ∞)

end GroundTheory.Heights₂.Heights.Inter
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsFibreIncomp
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter

def FibreIncomp.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (n : ℕ) (s : MRing ι) (α : K → ℕ)
    (W : Ideal (MRing ι)), IsBlockMap κ v → IsArithVar P' (n + 1) →
    IsArithVar (imageZ v P') (n + 1) → ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s α → s ∉ imageZ v P' → W ∈ divSupp (imageZ v P') s →
    ∀ W₁ W₂ : Ideal (MRing ι'), W₁ ∈ fibreOver v P' W → W₂ ∈ fibreOver v P' W → W₁ ≤ W₂ → W₁ = W₂

end GroundTheory.Heights₂.Heights.Inter
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.StValCentreZ
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter

def IsValCentre {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) [P.IsPrime]
    (R : ValuationSubring (FractionRing (MRing ι ⧸ P))) (y : Ideal (MRing ι)) : Prop :=
  IsMultiProjPrime y ∧ P ≤ y ∧
    ∀ (b : K → ℕ) (f g : MRing ι), ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f b → ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g b → g ∉ y →
      algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P f) /
          algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P g) ∈ R ∧
        (f ∈ y ↔ algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P f) /
          algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P g) ∈ R.nonunits)

def ValCentreZ.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (hP : IsMultiProjPrime P),
    haveI := hP.1
    ∀ R : ValuationSubring (FractionRing (MRing ι ⧸ P)), ∃ y : Ideal (MRing ι), IsValCentre P R y

end GroundTheory.Heights₂.Heights.Inter
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.PPFFibreBij
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

section Loc

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} {ι' : K' → Type}
  {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} {P' : Ideal (MRing ι')}

theorem baseSubst_rename (hv : IsBlockMap κ v) (G : GenFibre v P') (g : MRing ι) :
    baseSubst κ G (rename v g) = C (aeval G.x g) := by
  have h : (baseSubst κ G).comp (rename v : MRing ι →ₐ[ℤ] MRing ι').toRingHom =
      (C : G.Φ →+* MRingOver G.Φ (fibreIdx ι' κ)).comp (aeval G.x : MRing ι →ₐ[ℤ] G.Φ).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp only [show (C r : MRing ι) = (r : MRing ι) from eq_intCast C r, map_intCast]
    · intro p
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, rename_X, aeval_X]
      unfold baseSubst
      rw [eval₂Hom_X']
      have h1 : (v p).1 ∈ Set.range κ := ⟨p.1, (hv.2.2.1 p).symm⟩
      have h2 : v p ∈ Set.range v := ⟨p, rfl⟩
      rw [dite_eq_left h1, dite_eq_left h2, hv.2.1 h2.choose_spec]
  exact DFunLike.congr_fun h g

theorem baseSubst_X_fibre (G : GenFibre v P') (q : Σ k : FibreBlock κ, ι' k.1) :
    baseSubst κ G (X ⟨q.1.1, q.2⟩) = X q := by
  unfold baseSubst
  rw [eval₂Hom_X', dite_eq_right q.1.2]

theorem mem_of_baseSubst_eq_zero (hv : IsBlockMap κ v) (G : GenFibre v P') {f : MRing ι'}
    (hf : baseSubst κ G f = 0) : f ∈ P' := by
  rw [← G.genericFibre_ker_target, RingHom.mem_ker, ← aeval_baseSubst hv, hf, map_zero]

theorem baseSubst_mem_fibreIdeal (hv : IsBlockMap κ v) (G : GenFibre v P') (f : MRing ι') :
    baseSubst κ G f ∈ ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal κ G ↔ f ∈ P' := by
  rw [ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal, RingHom.mem_ker, aeval_baseSubst hv, ← RingHom.mem_ker, G.genericFibre_ker_target]

theorem exists_mul_eq_baseSubst (hv : IsBlockMap κ v) (G : GenFibre v P') (c : MRingOver G.Φ (fibreIdx ι' κ)) :
    ∃ (F : MRing ι') (g : MRing ι), aeval G.x g ≠ 0 ∧ c * C (aeval G.x g) = baseSubst κ G F := by
  induction c using MvPolynomial.induction_on with
  | C a =>
    obtain ⟨f, g, hg, rfl⟩ := G.gen a
    refine ⟨rename v f, g, hg, ?_⟩
    rw [baseSubst_rename hv, ← C_mul, div_mul_cancel₀ _ hg]
  | add c₁ c₂ ih₁ ih₂ =>
    obtain ⟨F₁, g₁, h₁, e₁⟩ := ih₁
    obtain ⟨F₂, g₂, h₂, e₂⟩ := ih₂
    refine ⟨F₁ * rename v g₂ + F₂ * rename v g₁, g₁ * g₂, by rw [map_mul]; exact mul_ne_zero h₁ h₂, ?_⟩
    simp only [map_add (f := _), map_mul, baseSubst_rename hv]
    rw [← e₁, ← e₂]
    ring
  | mul_X c q ih =>
    obtain ⟨F, g, hg, e⟩ := ih
    refine ⟨F * X ⟨q.1.1, q.2⟩, g, hg, ?_⟩
    rw [map_mul, ← e, baseSubst_X_fibre]
    ring

theorem mem_fibreOf_of_mul_eq (G : GenFibre v P') {I : Ideal (MRing ι')} {c : MRingOver G.Φ (fibreIdx ι' κ)}
    {F : MRing ι'} {g : MRing ι} (hg : aeval G.x g ≠ 0) (e : c * C (aeval G.x g) = baseSubst κ G F) (hF : F ∈ I) :
    c ∈ fibreOf κ G I := by
  have : c = baseSubst κ G F * C (aeval G.x g)⁻¹ := by
    rw [← e, mul_assoc, ← C_mul, mul_inv_cancel₀ hg, C_1, mul_one]
  rw [this]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hF)

theorem fibreOf_comap (hv : IsBlockMap κ v) (G : GenFibre v P') (Q : Ideal (MRingOver G.Φ (fibreIdx ι' κ))) :
    fibreOf κ G (Q.comap (baseSubst κ G)) = Q := by
  refine le_antisymm Ideal.map_comap_le fun c hc => ?_
  obtain ⟨F, g, hg, e⟩ := exists_mul_eq_baseSubst hv G c
  refine mem_fibreOf_of_mul_eq G hg e ?_
  rw [Ideal.mem_comap, ← e]
  exact Q.mul_mem_right _ hc

theorem comap_fibreOf (hv : IsBlockMap κ v) (G : GenFibre v P') {W : Ideal (MRing ι')} (hW : W.IsPrime)
    (hPW : P' ≤ W) (hI : imageZ v W = imageZ v P') : (fibreOf κ G W).comap (baseSubst κ G) = W := by
  refine le_antisymm (fun f hf => ?_) Ideal.le_comap_map
  have key : ∀ c ∈ fibreOf κ G W, ∃ w ∈ W, ∃ g : MRing ι, aeval G.x g ≠ 0 ∧
      c * C (aeval G.x g) = baseSubst κ G w := by
    intro c hc
    unfold fibreOf Ideal.map Ideal.span at hc
    induction hc using Submodule.span_induction with
    | mem c hc =>
      obtain ⟨w, hw, rfl⟩ := hc
      exact ⟨w, hw, 1, by simp, by simp⟩
    | zero => exact ⟨0, W.zero_mem, 1, by simp, by simp⟩
    | add c₁ c₂ _ _ ih₁ ih₂ =>
      obtain ⟨w₁, hw₁, g₁, h₁, e₁⟩ := ih₁
      obtain ⟨w₂, hw₂, g₂, h₂, e₂⟩ := ih₂
      refine ⟨w₁ * rename v g₂ + w₂ * rename v g₁, W.add_mem (W.mul_mem_right _ hw₁) (W.mul_mem_right _ hw₂),
        g₁ * g₂, by rw [map_mul]; exact mul_ne_zero h₁ h₂, ?_⟩
      simp only [map_add (f := _), map_mul, baseSubst_rename hv]
      rw [← e₁, ← e₂]
      ring
    | smul a c _ ih =>
      obtain ⟨w, hw, g, h, e⟩ := ih
      obtain ⟨F, g', h', e'⟩ := exists_mul_eq_baseSubst hv G a
      refine ⟨F * w, W.mul_mem_left _ hw, g' * g, by rw [map_mul]; exact mul_ne_zero h' h, ?_⟩
      simp only [smul_eq_mul, map_mul]
      rw [← e', ← e]
      ring
  obtain ⟨w, hw, g, hg, e⟩ := key _ hf
  have h0 : f * rename v g - w ∈ P' :=
    mem_of_baseSubst_eq_zero hv G (by rw [map_sub, map_mul, baseSubst_rename hv, e, sub_self])
  have h1 : f * rename v g ∈ W := by simpa using W.add_mem (hPW h0) hw
  rcases hW.mem_or_mem h1 with h | h
  · exact h
  · refine absurd ?_ hg
    have hg' : g ∈ imageZ v W := h
    rw [hI, ← G.ker_x] at hg'
    exact hg'

theorem fibreOf_isPrime (hv : IsBlockMap κ v) (G : GenFibre v P') {W : Ideal (MRing ι')} (hW : W.IsPrime)
    (hPW : P' ≤ W) (hI : imageZ v W = imageZ v P') : (fibreOf κ G W).IsPrime := by
  have hc := comap_fibreOf hv G hW hPW hI
  refine ⟨fun h => hW.ne_top ?_, fun {a b} hab => ?_⟩
  · rw [← hc, h, Ideal.comap_top]
  · obtain ⟨F, g, hg, e⟩ := exists_mul_eq_baseSubst hv G a
    obtain ⟨H, g', hg', e'⟩ := exists_mul_eq_baseSubst hv G b
    have hFH : F * H ∈ W := by
      rw [← hc, Ideal.mem_comap, map_mul, ← e, ← e']
      have : a * C (aeval G.x g) * (b * C (aeval G.x g')) = a * b * (C (aeval G.x g) * C (aeval G.x g')) := by
        ring
      rw [this]
      exact Ideal.mul_mem_right _ _ hab
    rcases hW.mem_or_mem hFH with h | h
    · exact Or.inl (mem_fibreOf_of_mul_eq G hg e h)
    · exact Or.inr (mem_fibreOf_of_mul_eq G hg' e' h)

theorem imageZ_comap (hv : IsBlockMap κ v) (G : GenFibre v P') {Q : Ideal (MRingOver G.Φ (fibreIdx ι' κ))}
    (hQ : Q ≠ ⊤) : imageZ v (Q.comap (baseSubst κ G)) = imageZ v P' := by
  ext g
  rw [← G.ker_x, RingHom.mem_ker, imageZ, Ideal.mem_comap, Ideal.mem_comap]
  show baseSubst κ G (rename v g) ∈ Q ↔ _
  rw [baseSubst_rename hv]
  constructor
  · intro h
    by_contra hne
    exact hQ (Q.eq_top_of_isUnit_mem h ((isUnit_iff_ne_zero.mpr hne).map C))
  · intro h
    rw [h, map_zero]
    exact Q.zero_mem

end Loc

theorem PFFibreBij.proof : PFFibreBij.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' d e G s hv hP' hP
  classical
  have hPrel : ReciprocityTheory.ChartRestriction.G.Geo.IsRelevant (imageZ v P') := hP.2.1.2.2
  have hPhor : IsHorizontal (imageZ v P') := hP.2.2.1
  have hfib : ∀ {W : Ideal (MRing ι')}, P' ≤ W → ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal κ G ≤ fibreOf κ G W := by
    intro W hW c hc
    obtain ⟨F, g, hg, e⟩ := exists_mul_eq_baseSubst hv G c
    refine mem_fibreOf_of_mul_eq G hg e (hW ?_)
    rw [← baseSubst_mem_fibreIdeal hv G, ← e]
    exact Ideal.mul_mem_right _ _ hc
  have hle : ∀ {Q : Ideal (MRingOver G.Φ (fibreIdx ι' κ))}, ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal κ G ≤ Q → P' ≤ Q.comap (baseSubst κ G) :=
    fun hQ f hf => hQ ((baseSubst_mem_fibreIdeal hv G f).mpr hf)
  refine ⟨?_, ?_, ?_⟩
  · rintro W ⟨⟨⟨⟨hWp, hWle⟩, hWmin⟩, hWrel⟩, -, hWI⟩
    have hPW := (sup_le_iff.mp hWle).1
    have hsW := (Ideal.span_singleton_le_iff_mem _).mp (sup_le_iff.mp hWle).2
    have hcW := comap_fibreOf hv G hWp hPW hWI
    refine ⟨⟨⟨fibreOf_isPrime hv G hWp hPW hWI, sup_le (hfib hPW)
      ((Ideal.span_singleton_le_iff_mem _).mpr (Ideal.mem_map_of_mem _ hsW))⟩, ?_⟩, ?_⟩
    · rintro Q' ⟨hQ'p, hQ'le⟩ hQ'Q
      have hsQ' := (Ideal.span_singleton_le_iff_mem _).mp (sup_le_iff.mp hQ'le).2
      have hm := hWmin ⟨Ideal.IsPrime.comap _ (hK := hQ'p), sup_le (hle (sup_le_iff.mp hQ'le).1)
        ((Ideal.span_singleton_le_iff_mem _).mpr (Ideal.mem_comap.mpr hsQ'))⟩
        (by rw [← hcW]; exact Ideal.comap_mono hQ'Q)
      calc fibreOf κ G W ≤ fibreOf κ G (Q'.comap (baseSubst κ G)) := Ideal.map_mono hm
        _ = Q' := fibreOf_comap hv G Q'
    · intro k
      obtain ⟨i, hi⟩ := hWrel k.1
      refine ⟨i, fun h => hi ?_⟩
      rw [← hcW, Ideal.mem_comap, baseSubst_X_fibre G ⟨k, i⟩]
      exact h
  · rintro W₁ ⟨⟨⟨⟨h1p, h1le⟩, -⟩, -⟩, -, h1I⟩ W₂ ⟨⟨⟨⟨h2p, h2le⟩, -⟩, -⟩, -, h2I⟩ heq
    rw [← comap_fibreOf hv G h1p (sup_le_iff.mp h1le).1 h1I, heq,
      comap_fibreOf hv G h2p (sup_le_iff.mp h2le).1 h2I]
  · rintro Q ⟨⟨⟨hQp, hQle⟩, hQmin⟩, hQrel⟩
    have hWp : (Q.comap (baseSubst κ G)).IsPrime := Ideal.IsPrime.comap _ (hK := hQp)
    have hPW : P' ≤ Q.comap (baseSubst κ G) := hle (sup_le_iff.mp hQle).1
    have hsW : s ∈ Q.comap (baseSubst κ G) :=
      Ideal.mem_comap.mpr ((Ideal.span_singleton_le_iff_mem _).mp (sup_le_iff.mp hQle).2)
    have hWI : imageZ v (Q.comap (baseSubst κ G)) = imageZ v P' := imageZ_comap hv G hQp.ne_top
    have hmap : fibreOf κ G (Q.comap (baseSubst κ G)) = Q := fibreOf_comap hv G Q
    refine ⟨Q.comap (baseSubst κ G), ⟨⟨⟨⟨hWp, sup_le hPW ((Ideal.span_singleton_le_iff_mem _).mpr hsW)⟩, ?_⟩, ?_⟩,
      ?_, hWI⟩, hmap⟩
    · rintro W' ⟨hW'p, hW'le⟩ hW'W
      have hPW' := (sup_le_iff.mp hW'le).1
      have hsW' := (Ideal.span_singleton_le_iff_mem _).mp (sup_le_iff.mp hW'le).2
      have hW'I : imageZ v W' = imageZ v P' :=
        le_antisymm (by rw [← hWI]; exact Ideal.comap_mono hW'W) (Ideal.comap_mono hPW')
      have hm := hQmin ⟨fibreOf_isPrime hv G hW'p hPW' hW'I, sup_le (hfib hPW')
        ((Ideal.span_singleton_le_iff_mem _).mpr (Ideal.mem_map_of_mem _ hsW'))⟩
        (by rw [← hmap]; exact Ideal.map_mono hW'W)
      calc Q.comap (baseSubst κ G) ≤ (fibreOf κ G W').comap (baseSubst κ G) := Ideal.comap_mono hm
        _ = W' := comap_fibreOf hv G hW'p hPW' hW'I
    · intro k'
      by_cases hk : k' ∈ Set.range κ
      · obtain ⟨k, rfl⟩ := hk
        obtain ⟨i, hi⟩ := hPrel k
        have hx : (X (v ⟨k, i⟩) : MRing ι') ∉ Q.comap (baseSubst κ G) := fun h => hi (by
          rw [← hWI, imageZ, Ideal.mem_comap]
          show rename v (X ⟨k, i⟩) ∈ Q.comap (baseSubst κ G)
          rw [rename_X]
          exact h)
        have hvk := hv.2.2.1 ⟨k, i⟩
        generalize v ⟨k, i⟩ = q at hx hvk
        obtain ⟨k'', j⟩ := q
        simp only at hvk
        subst hvk
        exact ⟨j, hx⟩
      · obtain ⟨i, hi⟩ := hQrel ⟨k', hk⟩
        refine ⟨i, fun h => hi ?_⟩
        rw [← baseSubst_X_fibre G ⟨⟨k', hk⟩, i⟩]
        exact h
    · rw [IsHorizontal, eq_bot_iff]
      intro n hn
      have hn' : n ∈ (imageZ v P').comap (C : ℤ →+* MRing ι) := by
        rw [Ideal.mem_comap, ← hWI, imageZ, Ideal.mem_comap]
        show rename v (C n) ∈ Q.comap (baseSubst κ G)
        rw [rename_C]
        exact Ideal.mem_comap.mp hn
      rw [hPhor] at hn'
      exact hn'

end

end GroundTheory.Heights₂.Heights.Inter
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsMoreLast
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter

def ArithmeticIntersectionFibreMultiHomogeneous.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (p : ℕ) [Fact p.Prime] (W' : Ideal (MRing ι')),
    IsBlockMap κ v → ((p : ℕ) : MRing ι') ∈ W' →
    IsMultiHomogIdeal (W'.map (MvPolynomial.map (Int.castRingHom (ZMod p)))) →
    ∀ G' : GenFibre v W', IsMultiHomogIdeal (ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal κ G')

section Inhabitants

end Inhabitants

end GroundTheory.Heights₂.Heights.Inter
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsSemilocRankAdjoin
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter

def SemilocRankAdjoin.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (n : ℕ)
    (G : GenFibre v P') (s : MRing ι) (α : K → ℕ) (W : Ideal (MRing ι)) (i' : ∀ k', ι' k')
    (hv : IsBlockMap κ v) (hP' : IsArithVar P' (n + 1)),
    IsArithVar (imageZ v P') (n + 1) → ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s α → s ∉ imageZ v P' →
    W ∈ divSupp (imageZ v P') s → (∀ k', (X ⟨k', i' k'⟩ : MRing ι') ∉ P') →
    haveI := hP'.2.1.1
    letI := (locToSemiloc hv P' W).toAlgebra
    Module.finrank (locRing (imageZ v P') W) (semiLocRing P' (fibreOver v P' W)) =
      Module.finrank G.Φ (IntermediateField.adjoin G.Φ
        (Set.range fun q : Σ k : FibreBlock κ, ι' k.1 => G.x' ⟨q.1.1, q.2⟩ / G.x' ⟨q.1.1, i' q.1.1⟩))

end GroundTheory.Heights₂.Heights.Inter
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsFurtherAlt
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter

def FibreTranscendenceDegreeAlt.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (p : ℕ) [Fact p.Prime] (W' : Ideal (MRing ι')) (n : ℕ),
    IsBlockMap κ v → ((p : ℕ) : MRing ι') ∈ W' →
    IsProjVarF (W'.map (MvPolynomial.map (Int.castRingHom (ZMod p)))) n →
    IsProjVarF (imageVar (ZMod p) v (W'.map (MvPolynomial.map (Int.castRingHom (ZMod p))))) n →
    ∀ G' : GenFibre v W',
      Algebra.trdeg G'.Φ (IntermediateField.adjoin G'.Φ
        (Set.range fun q : (Σ k : FibreBlock κ, ι' k.1) => G'.x' ⟨q.1.1, q.2⟩)) = Fintype.card (FibreBlock κ)

section Inhabitants

end Inhabitants

end GroundTheory.Heights₂.Heights.Inter
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsRest
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

theorem VerticalDegree.proof (h₁ : FibreDimensionZero.Statement) (h₂ : ChartRankAdjoin.Statement)
    (h₃ : VerticalDegreeAfterAdjoining.Statement) : VerticalDegree.Statement := by
  intro K _ ι _ K' _ ι' _ κ v p _ W' n i' hv hp hW hV hch G' J' hJ
  have hfib := h₁ K ι K' ι' κ v p W' n hv hp hW hV G'
  have hz : ∀ k : FibreBlock κ, G'.x' ⟨k.1, i' k.1⟩ ≠ 0 := by
    intro k h0
    apply hch k.1
    have hX : (X ⟨k.1, i' k.1⟩ : MRing ι') ∈ W' := by
      rw [← G'.genericFibre_ker_target, RingHom.mem_ker, aeval_X]
      exact h0
    simpa using Ideal.mem_map_of_mem (MvPolynomial.map (Int.castRingHom (ZMod p))) hX
  have hj : IsChart (ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal κ G') (fun k => i' k.1) := by
    intro k hk
    apply hz k
    rw [ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal, RingHom.mem_ker, aeval_X] at hk
    exact hk
  rw [hJ.1 _ Fin.elim0 _ hfib hj, h₃ K ι K' ι' κ v p W' n i' hv hp hW hV hch G']
  congr 1
  exact (h₂ (FibreBlock κ) (fibreIdx ι' κ) G'.Φ G'.Φ' (fun q => G'.x' ⟨q.1.1, q.2⟩) (fun k => i' k.1) hz
    hfib.1.2.1).symm

end GroundTheory.Heights₂.Heights.Inter
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsSemilocLengthSum
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter

def SemilocLengthSum.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (n : ℕ) (s t : MRing ι) (α : K → ℕ)
    (W : Ideal (MRing ι)) (E : Ideal (MRing ι') → ℤ) (hv : IsBlockMap κ v) (hP' : IsArithVar P' (n + 1))
    (y : locRing (imageZ v P') W),
    IsArithVar (imageZ v P') (n + 1) → ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s α → ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog t α → s ∉ imageZ v P' →
    W ∈ divSupp (imageZ v P') s → t ∉ W →
    (y : FractionRing (MRing ι ⧸ imageZ v P')) * algebraMap _ _ (Ideal.Quotient.mk (imageZ v P') t) =
      algebraMap _ _ (Ideal.Quotient.mk (imageZ v P') s) →
    (∀ W' ∈ fibreOver v P' W, rename v s ∈ W' →
      ∃ (G' : GenFibre v W') (J' : IFamily G'.Φ (fibreIdx ι' κ)),
        IsFieldIntersection J' ∧ E W' = J' (ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal κ G') 0 Fin.elim0) →
    haveI := hP'.2.1.1
    letI := (locToSemiloc hv P' W).toAlgebra
    (fibreOver v P' W).Finite ∧
      ∃ N : ℕ, Module.length (locRing (imageZ v P') W)
          (semiLocRing P' (fibreOver v P' W) ⧸ LinearMap.range
            (LinearMap.lsmul (locRing (imageZ v P') W) (semiLocRing P' (fibreOver v P' W)) y)) = N ∧
        (N : ℤ) = ∑ᶠ W' ∈ {W' | W' ∈ fibreOver v P' W ∧ rename v s ∈ W'},
          ((Module.length (locRing P' W') (locRing P' W' ⧸ locIdeal P' W' (fracMapZ v P' y))).toNat : ℤ) * E W'

end GroundTheory.Heights₂.Heights.Inter
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.PLocRingInj
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

theorem LocRingInj.le_of_locRing_eq {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {P W W' : Ideal (MRing ι)} (hP : P.IsPrime) (hW : IsMultiProjPrime W) (hW' : IsMultiProjPrime W')
    (hPW : P ≤ W) (hPW' : P ≤ W') (heq : locRing P W = locRing P W') : W ≤ W' := by
  classical
  have := hP
  have hL := LocRingLocal.proof LocRingFrac.proof
  set φ := algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) with hφ
  have hne : ∀ {f : MRing ι}, f ∉ P → φ (Ideal.Quotient.mk P f) ≠ 0 := fun hf h => hf <| by
    rwa [hφ, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem] at h

  have hunit : ∀ {y : FractionRing (MRing ι ⧸ P)} (hy : y ∈ locRing P W) (hy' : y ∈ locRing P W'),
      IsUnit (⟨y, hy'⟩ : locRing P W') → IsUnit (⟨y, hy⟩ : locRing P W) := by
    intro y hy hy' hu
    obtain ⟨b, hb⟩ := isUnit_iff_exists_inv.mp hu
    have hb' : y * (b : FractionRing (MRing ι ⧸ P)) = 1 := by
      have := congrArg Subtype.val hb
      rwa [Subring.coe_mul, Subring.coe_one, Subtype.coe_mk] at this
    have hbW : (b : FractionRing (MRing ι ⧸ P)) ∈ locRing P W := by rw [heq]; exact b.2
    refine IsUnit.of_mul_eq_one (⟨b, hbW⟩ : locRing P W) (Subtype.ext ?_)
    rw [Subring.coe_mul, Subring.coe_one, Subtype.coe_mk, Subtype.coe_mk, hb']
  choose i hi using hW.2.2
  choose j hj using hW'.2.2

  have hjW : ∀ k, (X ⟨k, j k⟩ : MRing ι) ∉ W := by
    intro k
    have hiP : (X ⟨k, i k⟩ : MRing ι) ∉ P := fun h => hi k (hPW h)
    have hjP : (X ⟨k, j k⟩ : MRing ι) ∉ P := fun h => hj k (hPW' h)
    have h1 : φ (Ideal.Quotient.mk P (X ⟨k, i k⟩)) / φ (Ideal.Quotient.mk P (X ⟨k, j k⟩)) ∈ locRing P W :=
      heq ▸ frac_mem_locRing hPW' (AvoidRing.isMultiHomog_X k (i k)) (AvoidRing.isMultiHomog_X k (j k))
        (hj k) (div_mul_cancel₀ _ (hne hjP))
    have h2 : φ (Ideal.Quotient.mk P (X ⟨k, j k⟩)) / φ (Ideal.Quotient.mk P (X ⟨k, i k⟩)) ∈ locRing P W :=
      frac_mem_locRing hPW (AvoidRing.isMultiHomog_X k (j k)) (AvoidRing.isMultiHomog_X k (i k))
        (hi k) (div_mul_cancel₀ _ (hne hiP))
    have hu : IsUnit (⟨_, h2⟩ : locRing P W) := by
      refine IsUnit.of_mul_eq_one (⟨_, h1⟩ : locRing P W) (Subtype.ext ?_)
      rw [Subring.coe_mul, Subring.coe_one, Subtype.coe_mk, Subtype.coe_mk]
      have := hne hiP
      have := hne hjP
      field_simp
    exact ((hL K ι P W hP hW.1 hPW).2 _ _ _ _ (AvoidRing.isMultiHomog_X k (j k))
      (AvoidRing.isMultiHomog_X k (i k)) (hi k) (div_mul_cancel₀ _ (hne hiP))).mp hu

  obtain ⟨S, hS, hWS⟩ := hW.2.1
  rw [hWS, Ideal.span_le]
  intro f hf
  obtain ⟨a, ha⟩ := hS f hf
  have hfW : f ∈ W := hWS ▸ Ideal.subset_span hf
  by_contra hfW'
  have htW := AvoidRing.coordProd_not_mem hW.1 j hjW a
  have htW' := AvoidRing.coordProd_not_mem hW'.1 j hj a
  have ht := AvoidRing.isMultiHomog_coordProd (R := ℤ) (ι := ι) j a
  have hy := div_mul_cancel₀ (φ (Ideal.Quotient.mk P f)) (hne fun h => htW (hPW h))
  have hyW := frac_mem_locRing hPW ha ht htW hy
  have hyW' := frac_mem_locRing hPW' ha ht htW' hy
  have hu' : IsUnit (⟨_, hyW'⟩ : locRing P W') :=
    ((hL K ι P W' hP hW'.1 hPW').2 _ f _ a ha ht htW' hy).mpr hfW'
  exact ((hL K ι P W hP hW.1 hPW).2 _ f _ a ha ht htW hy).mp (hunit hyW hyW' hu') hfW

theorem LocRingInj.proof : LocRingInj.Statement := by
  intro K _ ι _ P W W' hP hW hW' hPW hPW' heq
  exact le_antisymm (LocRingInj.le_of_locRing_eq hP hW hW' hPW hPW' heq)
    (LocRingInj.le_of_locRing_eq hP hW' hW hPW' hPW heq.symm)

end

end GroundTheory.Heights₂.Heights.Inter
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.PDiagOrdOne
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI

noncomputable section

namespace DiagonalOrderOne

section Length

variable {A : Type*} [CommRing A]

theorem length_eq_one_of_sat (J W : Ideal A) [W.IsPrime] (hJ : J ≤ W) (hs : ∀ d ∈ W, ∃ u ∉ W, u * d ∈ J) :
    Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (A ⧸ J)) = 1 := by
  have hz : ∀ (r : A) (s : W.primeCompl),
      LocalizedModule.mk (Ideal.Quotient.mk J r) s = 0 ↔ r ∈ W := by
    intro r s
    rw [← LocalizedModule.zero_mk s, LocalizedModule.mk_eq]
    constructor
    · rintro ⟨u, hu⟩
      rw [smul_zero, smul_zero, Submonoid.smul_def, Submonoid.smul_def, Algebra.smul_def, Algebra.smul_def,
        Ideal.Quotient.algebraMap_eq, ← map_mul, ← map_mul, Ideal.Quotient.eq_zero_iff_mem] at hu
      rcases ‹W.IsPrime›.mem_or_mem (hJ hu) with h | h
      · exact absurd h u.2
      rcases ‹W.IsPrime›.mem_or_mem h with h | h
      · exact absurd h s.2
      · exact h
    · intro hr
      obtain ⟨u, hu, hud⟩ := hs r hr
      refine ⟨⟨u, hu⟩, ?_⟩
      rw [smul_zero, smul_zero, Submonoid.smul_def, Submonoid.smul_def, Algebra.smul_def, Algebra.smul_def,
        Ideal.Quotient.algebraMap_eq, ← map_mul, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
      have e : u * ((s : A) * r) = u * r * s := by ring
      rw [show ((⟨u, hu⟩ : W.primeCompl) : A) = u from rfl, e]
      exact J.mul_mem_right _ hud
  have hgen : ∀ (q : A) (t : W.primeCompl) (r : A) (s : W.primeCompl) (hr : r ∉ W),
      LocalizedModule.mk (Ideal.Quotient.mk J q) t =
        Localization.mk (q * s) (t * ⟨r, hr⟩) • LocalizedModule.mk (Ideal.Quotient.mk J r) s := by
    intro q t r s hr
    rw [LocalizedModule.mk_smul_mk, LocalizedModule.mk_eq]
    refine ⟨1, ?_⟩
    simp only [one_smul, Submonoid.smul_def, Submonoid.coe_mul, Algebra.smul_def, Ideal.Quotient.algebraMap_eq,
      ← map_mul]
    congr 1
    ring
  have h1 : LocalizedModule.mk (Ideal.Quotient.mk J 1) (1 : W.primeCompl) ≠ 0 :=
    fun h => ‹W.IsPrime›.ne_top ((Ideal.eq_top_iff_one W).2 ((hz 1 1).1 h))
  have : Nontrivial (LocalizedModule W.primeCompl (A ⧸ J)) := ⟨⟨_, 0, h1⟩⟩
  rw [Module.length_eq_one_iff, isSimpleModule_iff]
  refine { eq_bot_or_eq_top := fun N => ?_ }
  by_cases hN : N = ⊥
  · exact Or.inl hN
  right
  obtain ⟨n, hnN, hn0⟩ := (Submodule.ne_bot_iff N).1 hN
  induction n using LocalizedModule.induction_on with
  | h m s =>
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective m
    have hr : r ∉ W := fun h => hn0 ((hz r s).2 h)
    rw [eq_top_iff]
    intro y _
    induction y using LocalizedModule.induction_on with
    | h m' t =>
      obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective m'
      rw [hgen q t r s hr]
      exact N.smul_mem _ hnN

end Length

section Graded

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ]

end Graded

end DiagonalOrderOne


end

end GroundTheory.Heights₂.Heights.Inter
end
