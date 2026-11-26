module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LabesseWaldspurger
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspidalNoRadicalFixed
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCyclicOfFiniteQuotient
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckePointLawsOfTransport

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CommuteOfWittFrameWeights
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CommuteOfWittFrameWeights
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp
open Polynomial

namespace GlobalTheory.Cusp.WeightCommute

open Matrix

variable {D : D7} {V : HSp D}

theorem ratAct_mul' (a b : GF V) (v : V.V) :
    GlobalTheory.Cusp.ratAct D.sp.cm V (a * b) v = GlobalTheory.Cusp.ratAct D.sp.cm V a (GlobalTheory.Cusp.ratAct D.sp.cm V b v) := by
  simp only [GlobalTheory.Cusp.ratAct]
  rw [show (a * b).1.1 = a.1.1 * b.1.1 from rfl, Matrix.toLin_mul V.frame V.frame V.frame]
  rfl

theorem ratAct_one' (v : V.V) : GlobalTheory.Cusp.ratAct D.sp.cm V 1 v = v := by
  simp only [GlobalTheory.Cusp.ratAct]
  rw [show (1 : GF V).1.1 = 1 from rfl, Matrix.toLin_one]
  rfl

theorem hT_ratAct (γ : GF V) (a b : V.V) :
    V.hT (GlobalTheory.Cusp.ratAct D.sp.cm V γ a) (GlobalTheory.Cusp.ratAct D.sp.cm V γ b) = V.hT a b := by
  have hγ : Formalism.UG.cT (↑D.sp.cm.sig) γ.1.1 * V.gram * γ.1.1 = V.gram := γ.2
  have hc : Formalism.UG.cT (↑D.sp.cm.sig) γ.1.1 = Matrix.conjTranspose γ.1.1 := by
    ext i j; rfl
  rw [hc] at hγ
  have hr : ∀ w, V.frame.repr (GlobalTheory.Cusp.ratAct D.sp.cm V γ w) = γ.1.1 *ᵥ V.frame.repr w := fun w => by
    rw [← LinearMap.toMatrix_mulVec_repr V.frame V.frame, GlobalTheory.Cusp.ratAct, LinearMap.toMatrix_toLin]
  have hform : ∀ x y : Fin V.rank → D.host.E,
      ∑ i, ∑ j, star (x i) * V.gram i j * y j = star x ⬝ᵥ (V.gram *ᵥ y) := by
    intro x y
    simp [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  rw [GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.hT_coord, GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.hT_coord, hr, hr, hform, hform, Matrix.star_mulVec,
    ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hγ]

theorem hT_frame (Φ : WittFrame V) (i j : Fin (wittIndex V)) :
    V.hT (Φ.f j) (Φ.e i) = (if i = j then 1 else 0) ∧ V.hT (Φ.e j) (Φ.f i) = (if i = j then 1 else 0) ∧
    V.hT (Φ.e j) (Φ.e i) = 0 ∧ V.hT (Φ.f j) (Φ.f i) = 0 := by
  refine ⟨Φ.ef i j, ?_, Φ.ee i j, Φ.ff i j⟩
  rw [← V.herm.eq (Φ.f i) (Φ.e j)]
  have h : V.hT (Φ.f i) (Φ.e j) = if j = i then 1 else 0 := Φ.ef j i
  rw [h]
  by_cases hij : i = j
  · subst hij; simp
  · rw [if_neg (Ne.symm hij), if_neg hij, map_zero]

end GlobalTheory.Cusp.WeightCommute


open GlobalTheory.Cusp.WeightCommute in
theorem GlobalTheory.Cusp.WeightCommute.commute_of_weights : ∀ (D : D7) (V : HSp D) (Φ : WittFrame V) (u : SV (wittIndex V)) (γ g : GF V) (t : D.host.E), (∀ x ∈ Φ.sub u, GlobalTheory.Cusp.ratAct D.sp.cm V γ x ∈ Φ.sub u) → (∀ x ∈ Φ.sub (-u), GlobalTheory.Cusp.ratAct D.sp.cm V γ x ∈ Φ.sub (-u)) → (∀ x ∈ Φ.sub u, GlobalTheory.Cusp.ratAct D.sp.cm V γ⁻¹ x ∈ Φ.sub u) → (∀ x ∈ Φ.sub (-u), GlobalTheory.Cusp.ratAct D.sp.cm V γ⁻¹ x ∈ Φ.sub (-u)) → (∀ x ∈ Φ.sub u, GlobalTheory.Cusp.ratAct D.sp.cm V g x = t • x) → (∀ x ∈ Φ.sub (-u), GlobalTheory.Cusp.ratAct D.sp.cm V g x = t⁻¹ • x) → (∀ z, (∀ x ∈ Φ.sub u, V.hT x z = 0) → (∀ x ∈ Φ.sub (-u), V.hT x z = 0) → GlobalTheory.Cusp.ratAct D.sp.cm V g z = z) → g * γ = γ * g := by
  intro D V Φ u γ g t h1 h2 h3 h4 h5 h6 h7
  classical
  obtain ⟨xv, hxv⟩ : ∃ xv : Fin (wittIndex V) → V.V, ∀ i, xv i = if u i = 1 then Φ.e i else Φ.f i :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨yv, hyv⟩ : ∃ yv : Fin (wittIndex V) → V.V, ∀ i, yv i = if u i = 1 then Φ.f i else Φ.e i :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨S, hS⟩ : ∃ S : Finset (Fin (wittIndex V)), ∀ i, i ∈ S ↔ u i ≠ 0 :=
    ⟨Finset.univ.filter (fun i => u i ≠ 0), fun i => by simp⟩
  have hsgn : ∀ s : SignType, s ≠ 0 → s = 1 ∨ s = -1 := by decide
  have hne : (-1 : SignType) ≠ 1 := by decide
  have hs : ∀ i ∈ S, u i = 1 ∨ u i = -1 := fun i hi => hsgn _ ((hS i).1 hi)
  have key := hT_frame Φ
  have neq : ∀ i j, u i = 1 → u j = -1 → i ≠ j := by
    rintro i j a b rfl; rw [a] at b; exact hne b.symm

  have mx : ∀ i ∈ S, xv i ∈ Φ.sub u := by
    intro i hi
    rw [WittFrame.sub]
    rcases hs i hi with a | a
    · rw [hxv, if_pos a]; exact Submodule.subset_span (Or.inl ⟨i, a, rfl⟩)
    · rw [hxv, if_neg (by rw [a]; exact hne)]; exact Submodule.subset_span (Or.inr ⟨i, a, rfl⟩)
  have my : ∀ i ∈ S, yv i ∈ Φ.sub (-u) := by
    intro i hi
    rw [WittFrame.sub]
    rcases hs i hi with a | a
    · rw [hyv, if_pos a]
      exact Submodule.subset_span (Or.inr ⟨i, show -(u i) = -1 by rw [a], rfl⟩)
    · rw [hyv, if_neg (by rw [a]; exact hne)]
      exact Submodule.subset_span (Or.inl ⟨i, show -(u i) = 1 by rw [a]; rfl, rfl⟩)

  have genX : ∀ z, (∀ i ∈ S, V.hT (xv i) z = 0) → ∀ w ∈ Φ.sub u, V.hT w z = 0 := by
    intro z hz w hw
    have hle : Φ.sub u ≤ LinearMap.ker (V.hT.flip z) := by
      rw [WittFrame.sub, Submodule.span_le]
      rintro _ (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩)
      · have hiS : i ∈ S := (hS i).2 (by rw [show u i = 1 from hi]; decide)
        have := hz i hiS
        rw [hxv, if_pos (show u i = 1 from hi)] at this
        exact this
      · have hiS : i ∈ S := (hS i).2 (by rw [show u i = -1 from hi]; decide)
        have := hz i hiS
        rw [hxv, if_neg (by rw [show u i = -1 from hi]; exact hne)] at this
        exact this
    exact hle hw
  have genY : ∀ z, (∀ i ∈ S, V.hT (yv i) z = 0) → ∀ w ∈ Φ.sub (-u), V.hT w z = 0 := by
    intro z hz w hw
    have hle : Φ.sub (-u) ≤ LinearMap.ker (V.hT.flip z) := by
      rw [WittFrame.sub, Submodule.span_le]
      rintro _ (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩)
      · have a : u i = -1 := neg_eq_iff_eq_neg.1 (show -(u i) = 1 from hi)
        have hiS : i ∈ S := (hS i).2 (by rw [a]; decide)
        have := hz i hiS
        rw [hyv, if_neg (by rw [a]; exact hne)] at this
        exact this
      · have a : u i = 1 := by
          have h' : -(u i) = -1 := hi
          simpa using h'
        have hiS : i ∈ S := (hS i).2 (by rw [a]; decide)
        have := hz i hiS
        rw [hyv, if_pos a] at this
        exact this
    exact hle hw

  have pxx : ∀ i ∈ S, ∀ j ∈ S, V.hT (xv j) (xv i) = 0 := by
    intro i hi j hj
    rcases hs i hi with a | a <;> rcases hs j hj with b | b <;> simp only [hxv, a, b, if_true, if_neg hne]
    · exact (key i j).2.2.1
    · rw [(key i j).1, if_neg (neq i j a b)]
    · rw [(key i j).2.1, if_neg (neq j i b a).symm]
    · exact (key i j).2.2.2
  have pyy : ∀ i ∈ S, ∀ j ∈ S, V.hT (yv j) (yv i) = 0 := by
    intro i hi j hj
    rcases hs i hi with a | a <;> rcases hs j hj with b | b <;> simp only [hyv, a, b, if_true, if_neg hne]
    · exact (key i j).2.2.2
    · rw [(key i j).2.1, if_neg (neq i j a b)]
    · rw [(key i j).1, if_neg (neq j i b a).symm]
    · exact (key i j).2.2.1
  have pyx : ∀ i ∈ S, ∀ j ∈ S, V.hT (yv j) (xv i) = if i = j then 1 else 0 := by
    intro i hi j hj
    rcases hs i hi with a | a <;> rcases hs j hj with b | b <;> simp only [hxv, hyv, a, b, if_true, if_neg hne]
    · exact (key i j).1
    · rw [(key i j).2.2.1, if_neg (neq i j a b)]
    · rw [(key i j).2.2.2, if_neg (neq j i b a).symm]
    · exact (key i j).2.1
  have pxy : ∀ i ∈ S, ∀ j ∈ S, V.hT (xv j) (yv i) = if i = j then 1 else 0 := by
    intro i hi j hj
    rcases hs i hi with a | a <;> rcases hs j hj with b | b <;> simp only [hxv, hyv, a, b, if_true, if_neg hne]
    · exact (key i j).2.1
    · rw [(key i j).2.2.2, if_neg (neq i j a b)]
    · rw [(key i j).2.2.1, if_neg (neq j i b a).symm]
    · exact (key i j).1

  have decomp : ∀ v : V.V, ∃ x ∈ Φ.sub u, ∃ y ∈ Φ.sub (-u), ∃ z, (∀ w ∈ Φ.sub u, V.hT w z = 0) ∧
      (∀ w ∈ Φ.sub (-u), V.hT w z = 0) ∧ v = x + y + z := by
    intro v
    refine ⟨∑ i ∈ S, V.hT (yv i) v • xv i, Submodule.sum_mem _ (fun i hi => Submodule.smul_mem _ _ (mx i hi)),
      ∑ i ∈ S, V.hT (xv i) v • yv i, Submodule.sum_mem _ (fun i hi => Submodule.smul_mem _ _ (my i hi)),
      v - (∑ i ∈ S, V.hT (yv i) v • xv i) - ∑ i ∈ S, V.hT (xv i) v • yv i, genX _ ?_, genY _ ?_, by abel⟩
    · intro j hj
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sub, map_sub, map_sum, map_sum,
        Finset.sum_eq_zero (fun i hi => by rw [map_smul, pxx i hi j hj, smul_zero]),
        Finset.sum_eq_single j (fun i hi hij => by rw [map_smul, pxy i hi j hj, if_neg hij, smul_zero])
          (fun h => absurd hj h),
        map_smul, pxy j hj j hj, if_pos rfl, smul_eq_mul, mul_one]
      simp
    · intro j hj
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sub, map_sub, map_sum, map_sum,
        Finset.sum_eq_single j (fun i hi hij => by rw [map_smul, pyx i hi j hj, if_neg hij, smul_zero])
          (fun h => absurd hj h),
        Finset.sum_eq_zero (fun i hi => by rw [map_smul, pyy i hi j hj, smul_zero]),
        map_smul, pyx j hj j hj, if_pos rfl, smul_eq_mul, mul_one]
      simp

  have inv_app : ∀ w, GlobalTheory.Cusp.ratAct D.sp.cm V γ (GlobalTheory.Cusp.ratAct D.sp.cm V γ⁻¹ w) = w := by
    intro w; rw [← ratAct_mul', mul_inv_cancel, ratAct_one']
  have zX : ∀ z, (∀ w ∈ Φ.sub u, V.hT w z = 0) →
      ∀ w ∈ Φ.sub u, V.hT w (GlobalTheory.Cusp.ratAct D.sp.cm V γ z) = 0 := by
    intro z hz w hw
    rw [← inv_app w, hT_ratAct]; exact hz _ (h3 w hw)
  have zY : ∀ z, (∀ w ∈ Φ.sub (-u), V.hT w z = 0) →
      ∀ w ∈ Φ.sub (-u), V.hT w (GlobalTheory.Cusp.ratAct D.sp.cm V γ z) = 0 := by
    intro z hz w hw
    rw [← inv_app w, hT_ratAct]; exact hz _ (h4 w hw)
  have hmat : (g * γ).1.1 = (γ * g).1.1 := by
    apply (Matrix.toLin V.frame V.frame).injective
    apply LinearMap.ext
    intro v
    show GlobalTheory.Cusp.ratAct D.sp.cm V (g * γ) v = GlobalTheory.Cusp.ratAct D.sp.cm V (γ * g) v
    rw [ratAct_mul', ratAct_mul']
    obtain ⟨x, hx, y, hy, z, hzX, hzY, rfl⟩ := decomp v
    simp only [map_add (f := _)]
    rw [h5 _ (h1 x hx), h6 _ (h2 y hy), h7 _ (zX z hzX) (zY z hzY), h5 x hx, h6 y hy, h7 z hzX hzY,
      map_smul, map_smul]
  exact Subtype.ext (Units.ext hmat)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CommuteOfWittFrameWeightsStatement
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp
open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.commute_of_wittFrame_weights : ∀ (D : D7) (V : HSp D) (Φ : WittFrame V) (u : SV (wittIndex V)) (γ g : GF V) (t : D.host.E), (∀ x ∈ Φ.sub u, GlobalTheory.Cusp.ratAct D.sp.cm V γ x ∈ Φ.sub u) → (∀ x ∈ Φ.sub (-u), GlobalTheory.Cusp.ratAct D.sp.cm V γ x ∈ Φ.sub (-u)) → (∀ x ∈ Φ.sub u, GlobalTheory.Cusp.ratAct D.sp.cm V γ⁻¹ x ∈ Φ.sub u) → (∀ x ∈ Φ.sub (-u), GlobalTheory.Cusp.ratAct D.sp.cm V γ⁻¹ x ∈ Φ.sub (-u)) → (∀ x ∈ Φ.sub u, GlobalTheory.Cusp.ratAct D.sp.cm V g x = t • x) → (∀ x ∈ Φ.sub (-u), GlobalTheory.Cusp.ratAct D.sp.cm V g x = t⁻¹ • x) → (∀ z, (∀ x ∈ Φ.sub u, V.hT x z = 0) → (∀ x ∈ Φ.sub (-u), V.hT x z = 0) → GlobalTheory.Cusp.ratAct D.sp.cm V g z = z) → g * γ = γ * g := by
  first | exact @GlobalTheory.Cusp.WeightCommute.commute_of_weights | exact GlobalTheory.Cusp.WeightCommute.commute_of_weights | (intros; apply GlobalTheory.Cusp.WeightCommute.commute_of_weights <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeKernelValueSumWeightTriangularFrame
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeKernelValueSumWeightTriangularFrame
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.HeckeWeight
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HeckePointLaw (scaleAt tanMap tanMap_scale scaleAt_comm isCombAt_iff tanMap_left)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l}

theorem comp_listProd {X Y : Over Xo.X} (f : X ⟶ Y) (L : List (Y ⟶ Xo.univ.t.G)) :
    f ≫ L.prod = (L.map (f ≫ ·)).prod := by
  induction L with
  | nil => simp [MonObj.comp_one]
  | cons b L ih => simp [List.prod_cons, MonObj.comp_mul, ih]

theorem isLieImg_comb {Ω : Type} [Field Ω] {x x' : Sp Ω ⟶ Xo.X} {ψ : Gx x ⟶ Gx x'} (h : IsLinHom ψ) (p : ℕ)
    {m : ℕ} {v v' : Fin m → (Sp (DualNumber Ω) ⟶ Xo.univ.t.G.left)} (hv : ∀ k, IsLieImg p ψ (v k) (v' k))
    {cf : Fin m → Ω} {w w' : Sp (DualNumber Ω) ⟶ Xo.univ.t.G.left} (hw : IsCombAt x v cf w)
    (hw' : IsCombAt x' v' cf w') (ht : IsTanAt x w) (ht' : IsTanAt x' w') : IsLieImg p ψ w w' := by
  choose a ha hpa using fun k => (hv k).2.2
  let b : Fin m → (tEps x' ⟶ Xo.univ.t.G) := fun k => Over.homMk (v' k) (hv k).2.1.1
  have hb : ∀ k, tanMap h (a k) = scaleAt x' p ≫ b k := fun k => Over.OverMorphism.ext (by
    rw [tanMap_left, Over.comp_left, ← hpa k]; rfl)
  let W : tEps x ⟶ Xo.univ.t.G := Over.homMk w ht.1
  let W' : tEps x' ⟶ Xo.univ.t.G := Over.homMk w' ht'.1
  have eW : (List.ofFn fun k => scaleAt x (cf k) ≫ a k).prod = W := by
    rw [← isCombAt_iff]
    have : v = fun k => (a k).left := funext fun k => (ha k).symm
    subst this
    exact hw
  have eW' : (List.ofFn fun k => scaleAt x' (cf k) ≫ b k).prod = W' := (isCombAt_iff b cf W').1 hw'
  refine ⟨ht, ht', W, rfl, ?_⟩
  have key : scaleAt x' p ≫ W' = tanMap h W := by
    rw [← eW, ← eW', comp_listProd, map_list_prod, List.map_ofFn, List.map_ofFn]
    congr 2
    funext k
    simp only [Function.comp_apply]
    rw [tanMap_scale, hb, ← Category.assoc, ← Category.assoc, scaleAt_comm]
  have := congrArg (·.left) key
  simp only [Over.comp_left, tanMap_left] at this
  exact this


open GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection (TotalAt FunAt) in
theorem hkVal_frBor : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (P : Ideal (𝓞 E)) (p i : ℕ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), admitted l P p → GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.TotalAt Xo c P p i → GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.FunAt Xo c P p i → ∀ f ∈ sec Xo c a n, ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra c.F Ω] (t : Ix Dw → Ωˣ) (y y' : FrPt Xo c Ω), FrBor t y y' → hkVal (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (fun Ω _ _ _ y => hkKer (Xo := Xo) P p i Ω y) (fun Ω _ _ _ y C z => hkRelFr P p i (hkTr Xo c p) Ω y C z) f y' = wchar (ex Dw a n) t * hkVal (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (fun Ω _ _ _ y => hkKer (Xo := Xo) P p i Ω y) (fun Ω _ _ _ y C z => hkRelFr P p i (hkTr Xo c p) Ω y C z) f y := by
  intro E _ _ _ H Dw l Xo c P p i a n hA hT hF f hf Ω _ _ _ t y y' hB
  have hS : GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori.IsSplitOff l P p := hA
  obtain ⟨g, hgt, hgd, hch⟩ := (frBor_iff_frChg y y' t).1 hB
  have hdet : ∀ τ, IsUnit (g τ).det := fun τ => by
    rw [Matrix.det_of_lowerTriangular _ (fun i j hij => hgt τ i j hij)]
    exact isUnit_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun j _ => by rw [hgd]; exact Units.ne_zero _)
  obtain ⟨x', xo', u', tan', eig', bas', s', gen'⟩ := y'
  obtain rfl : x' = y.x := hch.1
  have hw0 : wchar (ex Dw a n) t ≠ (0 : Ω) := by
    unfold wchar
    exact Finset.prod_ne_zero_iff.2 fun j _ => pow_ne_zero _ (t j).ne_zero
  have key : ∀ C : hkKer (Xo := Xo) P p i Ω y,
      hkTerm (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z)
        (fun Ω _ _ _ y => hkKer (Xo := Xo) P p i Ω y) (fun Ω _ _ _ y C z => hkRelFr P p i (hkTr Xo c p) Ω y C z)
        f (⟨y.x, xo', u', tan', eig', bas', s', gen'⟩ : FrPt Xo c Ω) C =
      wchar (ex Dw a n) t * hkTerm (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z)
        (fun Ω _ _ _ y => hkKer (Xo := Xo) P p i Ω y) (fun Ω _ _ _ y C z => hkRelFr P p i (hkTr Xo c p) Ω y C z)
        f y C := by
    intro C
    have ex' := hT Ω (⟨y.x, xo', u', tan', eig', bas', s', gen'⟩ : FrPt Xo c Ω) C
    have ex := hT Ω y C
    unfold hkTerm
    rw [dite_eq_left ex', dite_eq_left ex]
    have hz' := ex'.choose_spec
    have hz := ex.choose_spec
    generalize ex'.choose = z' at hz' ⊢
    generalize ex.choose = z at hz ⊢
    obtain ⟨ψ, hψ, hL, hθ⟩ := (GlobalTheory.HeckeFrCompare.hkPt_iff hS _ y C.1 z).1 hz
    rw [hkTr, Equiv.apply_symm_apply] at hθ
    obtain ⟨z'', hz'', -⟩ := existsUnique_frChg E H Dw l Xo c Ω z g (t none) hdet
    have hB' : FrBor t z z'' := (frBor_iff_frChg _ _ t).2 ⟨g, hgt, hgd, hz''⟩
    obtain ⟨x'', xo'', u'', tan'', eig'', bas'', s'', gen''⟩ := z''
    obtain rfl : x'' = z.x := hz''.1
    have hP : hkRelFr P p i (hkTr Xo c p) Ω (⟨y.x, xo', u', tan', eig', bas', s', gen'⟩ : FrPt Xo c Ω) C
        ⟨z.x, xo'', u'', tan'', eig'', bas'', s'', gen''⟩ := by
      show HkPt p (hkTr Xo c p Ω) (⟨y.x, xo', u', tan', eig', bas', s', gen'⟩ : FrPt Xo c Ω) C.1
        ⟨z.x, xo'', u'', tan'', eig'', bas'', s'', gen''⟩
      refine (GlobalTheory.HeckeFrCompare.hkPt_iff hS (hkTr Xo c p Ω) (⟨y.x, xo', u', tan', eig', bas', s', gen'⟩ : FrPt Xo c Ω) C.1
        ⟨z.x, xo'', u'', tan'', eig'', bas'', s'', gen''⟩).2 ⟨ψ, hψ, fun τ j => ?_, ?_⟩
      · exact GlobalTheory.HeckeWeight.isLieImg_comb hψ.2.1 p (hL τ) (hch.2.1 τ j) (hz''.2.1 τ j) (tan' τ j) (tan'' τ j)
      · rw [hkTr, Equiv.apply_symm_apply]
        exact hθ.smul (toΓ Ω (t none : Ω)) ((ChgOf.secBC_id_iff _ _ _ _).1 hch.2.2)
          ((ChgOf.secBC_id_iff _ _ _ _).1 hz''.2.2)
    obtain rfl := (frMap_unique_refl_iff E H Dw l Xo c Ω Ω (AlgHom.id c.F Ω) z').1 _ _
      (frMap_unique_refl_iff E H Dw l Xo c Ω Ω (AlgHom.id c.F Ω) z').2.1 (hF Ω (⟨y.x, xo', u', tan', eig', bas', s', gen'⟩ : FrPt Xo c Ω) C z' _ hz' hP)
    exact (algebraic_laws lawsFieldsSeparately.2.1 E H Dw l Xo c).2.2.2.2.2.2 Ω inferInstance a n f hf t z _ hB'
  unfold hkVal
  refine (finsum_congr key).trans ?_
  exact (mul_finsum _ _).symm

end GlobalTheory.HeckeWeight
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeKernelValueSumWeightTriangularFrameStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeKernel_value_sum_weight_triangular_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (P : Ideal (𝓞 E)) (p i : ℕ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), admitted l P p → GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.TotalAt Xo c P p i → GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.FunAt Xo c P p i → ∀ f ∈ sec Xo c a n, ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra c.F Ω] (t : Ix Dw → Ωˣ) (y y' : FrPt Xo c Ω), FrBor t y y' → hkVal (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (fun Ω _ _ _ y => hkKer (Xo := Xo) P p i Ω y) (fun Ω _ _ _ y C z => hkRelFr P p i (hkTr Xo c p) Ω y C z) f y' = wchar (ex Dw a n) t * hkVal (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (fun Ω _ _ _ y => hkKer (Xo := Xo) P p i Ω y) (fun Ω _ _ _ y C z => hkRelFr P p i (hkTr Xo c p) Ω y C z) f y := by
  first | exact @GlobalTheory.HeckeWeight.hkVal_frBor | exact GlobalTheory.HeckeWeight.hkVal_frBor | (intros; apply GlobalTheory.HeckeWeight.hkVal_frBor <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIntertwinerOfInvariantPairingAdmissible
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIntertwinerOfInvariantPairingAdmissible
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.S

noncomputable section

namespace GlobalTheory.InvPairing

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {W : Type} [AddCommGroup W] [Module ℂ W]

def stab {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (v : V) : Subgroup G where
  carrier := {g | ρ g v = v}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    rw [map_mul, Module.End.mul_apply, hb, ha]
  one_mem' := by simp
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at *
    conv_lhs => rw [← ha]
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

theorem mem_fixed_iff (σ : Representation ℂ G W) (H : Subgroup G) (v : W) :
    v ∈ GlobalTheory.PRep.fixed σ H ↔ ∀ h ∈ H, σ h v = v := by
  constructor
  · intro hv h hh
    have := hv ⟨h, hh⟩
    simpa using this
  · intro hv h
    simpa using hv h h.2

theorem exists_fixed_avg (σ : Representation ℂ G W) (hs : GlobalTheory.PRep.IsSmooth σ) (K : Subgroup G)
    (hK : IsCompact (K : Set G)) (x : W) :
    ∃ x₀ ∈ GlobalTheory.PRep.fixed σ K, ∀ ℓ : W →ₗ[ℂ] ℂ, (∀ k ∈ K, ∀ v, ℓ (σ k v) = ℓ v) → ℓ x = ℓ x₀ := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hSo : IsOpen ((stab σ x : Subgroup G) : Set G) := hs x
  haveI : Finite (K ⧸ (stab σ x).subgroupOf K) :=
    Subgroup.quotient_finite_of_isOpen _ (hSo.preimage continuous_subtype_val)
  let f : K ⧸ (stab σ x).subgroupOf K → W := fun q => Quotient.liftOn' q (fun k : K => σ k x) (by
    intro a b hab
    rw [QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf] at hab
    change σ ((a : G)⁻¹ * b) x = x at hab
    show σ a x = σ b x
    calc σ a x = σ a (σ ((a : G)⁻¹ * b) x) := by rw [hab]
      _ = σ b x := by rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left])
  have hrange : Set.range f = Set.range (fun k : K => σ k x) := by
    ext w
    constructor
    · rintro ⟨q, rfl⟩
      induction q using QuotientGroup.induction_on with
      | H k => exact ⟨k, rfl⟩
    · rintro ⟨k, rfl⟩
      exact ⟨QuotientGroup.mk k, rfl⟩
  have hfin : (Set.range (fun k : K => σ k x)).Finite := hrange ▸ Set.finite_range f
  set O := hfin.toFinset with hO
  have hxO : x ∈ O := by
    rw [hO, Set.Finite.mem_toFinset]
    exact ⟨1, by simp⟩
  have hperm : ∀ k ∈ K, ∑ v ∈ O, σ k v = ∑ v ∈ O, v := by
    intro k hk
    refine Finset.sum_nbij' (fun v => σ k v) (fun v => σ k⁻¹ v) ?_ ?_ ?_ ?_ ?_
    · intro v hv
      rw [hO, Set.Finite.mem_toFinset] at hv ⊢
      obtain ⟨j, rfl⟩ := hv
      exact ⟨⟨k, hk⟩ * j, by simp [Module.End.mul_apply]⟩
    · intro v hv
      rw [hO, Set.Finite.mem_toFinset] at hv ⊢
      obtain ⟨j, rfl⟩ := hv
      exact ⟨⟨k, hk⟩⁻¹ * j, by simp [Module.End.mul_apply]⟩
    · intro v _
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    · intro v _
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    · intro v _
      rfl
  refine ⟨((O.card : ℂ))⁻¹ • ∑ v ∈ O, v, ?_, ?_⟩
  · rw [mem_fixed_iff]
    intro k hk
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_smul, map_sum, hperm k hk]
  · intro ℓ hℓ
    have hconst : ∀ v ∈ O, ℓ v = ℓ x := by
      intro v hv
      rw [hO, Set.Finite.mem_toFinset] at hv
      obtain ⟨j, rfl⟩ := hv
      exact hℓ j j.2 x
    have hcard : (O.card : ℂ) ≠ 0 := by
      have : 0 < O.card := Finset.card_pos.mpr ⟨x, hxO⟩
      exact_mod_cast this.ne'
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_smul, map_sum, Finset.sum_congr rfl hconst, Finset.sum_const, smul_eq_mul, nsmul_eq_mul,
      ← mul_assoc, inv_mul_cancel₀ hcard, one_mul]

theorem exists_rep (U : Submodule ℂ W) [FiniteDimensional ℂ U]
    (B : W →ₗ[ℂ] W →ₛₗ[starRingEnd ℂ] ℂ) (hB : ∀ x, x ≠ 0 → 0 < (B x x).re) (f : U →ₗ[ℂ] ℂ) :
    ∃ z : U, ∀ x : U, f x = B x z := by
  let T : U →ₗ[ℝ] Module.Dual ℂ U :=
    { toFun := fun z => (B.flip (z : W)).comp U.subtype
      map_add' := by intro a b; ext x; simp
      map_smul' := by
        intro r z
        ext x
        simp only [RingHom.id_apply, LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.flip_apply,
          Submodule.coe_smul]
        rw [RCLike.real_smul_eq_coe_smul (K := ℂ) r z, Submodule.coe_smul, LinearMap.map_smulₛₗ, Complex.real_smul,
          RCLike.conj_ofReal, smul_eq_mul]
        rfl }
  have hinj : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro z hz
    by_contra hne
    have h1 : B z z = 0 := by
      have := LinearMap.congr_fun hz z
      simpa [T] using this
    have := hB z (fun h => hne (Subtype.ext h))
    rw [h1] at this
    simp at this
  have hrank : Module.finrank ℝ U = Module.finrank ℝ (Module.Dual ℂ U) := by
    rw [← Module.finrank_mul_finrank ℝ ℂ U, ← Module.finrank_mul_finrank ℝ ℂ (Module.Dual ℂ U),
      Subspace.dual_finrank_eq]
  have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank).mp hinj
  obtain ⟨z, hz⟩ := hsurj f
  exact ⟨z, fun x => by rw [← hz]; rfl⟩

end GlobalTheory.InvPairing

namespace GlobalTheory.InvPairing

theorem exists_intertwiner : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K : Subgroup G), IsOpen (K : Set G) → IsCompact (K : Set G) → ∀ (W W' : Type) [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W'] (σ : Representation ℂ G W) (σ' : Representation ℂ G W'), IsAdmissible σ → GlobalTheory.PRep.IsSmooth σ' → ∀ (B : W →ₗ[ℂ] W →ₛₗ[starRingEnd ℂ] ℂ) (C : W →ₗ[ℂ] W' →ₛₗ[starRingEnd ℂ] ℂ), (∀ x, x ≠ 0 → 0 < (B x x).re) → (∀ g x y, B (σ g x) (σ g y) = B x y) → (∀ g x y, C (σ g x) (σ' g y) = C x y) → ∃ φ : W' →ₗ[ℂ] W, (∀ g y, φ (σ' g y) = σ g (φ y)) ∧ ∀ x y, C x y = B x (φ y) := by
  intro G _ _ _ K hKo hKc W W' _ _ _ _ σ σ' hσ hσ' B C hB hBinv hCinv
  have huniq : ∀ z z' : W, (∀ x, B x z = B x z') → z = z' := by
    intro z z' h
    by_contra hne
    have hne' : z - z' ≠ 0 := sub_ne_zero.mpr hne
    have hpos := hB _ hne'
    have h0 : B (z - z') (z - z') = 0 := by rw [map_sub (B (z - z')), h (z - z'), sub_self]
    rw [h0] at hpos
    simp at hpos
  have hex : ∀ y, ∃ z, ∀ x, C x y = B x z := by
    intro y
    set K' := K ⊓ stab σ' y with hK'
    have hSo : IsOpen ((stab σ' y : Subgroup G) : Set G) := hσ' y
    have hKo' : IsOpen (K' : Set G) := hKo.inter hSo
    have hKc' : IsCompact (K' : Set G) := hKc.inter_right (Subgroup.isClosed_of_isOpen _ hSo)
    haveI := hσ.2 K' hKo' hKc'
    obtain ⟨z, hz⟩ := exists_rep (GlobalTheory.PRep.fixed σ K') B hB ((C.flip y).comp (GlobalTheory.PRep.fixed σ K').subtype)
    refine ⟨z, fun x => ?_⟩
    obtain ⟨x₀, hx₀, hℓ⟩ := exists_fixed_avg σ hσ.1 K' hKc' x
    have e1 := hℓ (C.flip y) (fun k hk v => by
      have hy : σ' k y = y := (Subgroup.mem_inf.mp hk).2
      simp only [LinearMap.flip_apply]
      conv_lhs => rw [← hy]
      exact hCinv k v y)
    have e2 := hℓ (B.flip z) (fun k hk v => by
      have hz' : σ k z = z := (mem_fixed_iff σ K' z).mp z.2 k hk
      simp only [LinearMap.flip_apply]
      conv_lhs => rw [← hz']
      exact hBinv k v z)
    simp only [LinearMap.flip_apply] at e1 e2
    rw [e1, e2]
    exact hz ⟨x₀, hx₀⟩
  choose φ₀ hφ₀ using hex
  refine ⟨{ toFun := φ₀, map_add' := ?_, map_smul' := ?_ }, ?_, fun x y => hφ₀ y x⟩
  · intro a b
    apply huniq
    intro x
    rw [map_add (B x), ← hφ₀, ← hφ₀, ← hφ₀, map_add (f := _)]
  · intro c a
    apply huniq
    intro x
    rw [RingHom.id_apply, LinearMap.map_smulₛₗ (B x), ← hφ₀, ← hφ₀, LinearMap.map_smulₛₗ]
  · intro g y
    apply huniq
    intro x
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    rw [← hφ₀]
    have hx : x = σ g (σ g⁻¹ x) := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    rw [hx, hCinv, hBinv]
    exact hφ₀ y _

end GlobalTheory.InvPairing
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIntertwinerOfInvariantPairingAdmissibleStatement
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.S
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_intertwiner_of_invariantPairing_admissible : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K : Subgroup G), IsOpen (K : Set G) → IsCompact (K : Set G) → ∀ (W W' : Type) [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W'] (σ : Representation ℂ G W) (σ' : Representation ℂ G W'), IsAdmissible σ → GlobalTheory.PRep.IsSmooth σ' → ∀ (B : W →ₗ[ℂ] W →ₛₗ[starRingEnd ℂ] ℂ) (C : W →ₗ[ℂ] W' →ₛₗ[starRingEnd ℂ] ℂ), (∀ x, x ≠ 0 → 0 < (B x x).re) → (∀ g x y, B (σ g x) (σ g y) = B x y) → (∀ g x y, C (σ g x) (σ' g y) = C x y) → ∃ φ : W' →ₗ[ℂ] W, (∀ g y, φ (σ' g y) = σ g (φ y)) ∧ ∀ x y, C x y = B x (φ y) := by
  first | exact @GlobalTheory.InvPairing.exists_intertwiner | exact GlobalTheory.InvPairing.exists_intertwiner | (intros; apply GlobalTheory.InvPairing.exists_intertwiner <;> assumption)
end
end
