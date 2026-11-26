module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalComparisonInert
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPairDecomposition
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductIrreducibleFiniteLength
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfIsSmoothModerate
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.CProps

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ComplexPointLiftsToMulticone
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ComplexPointLiftsToMulticone
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit)

noncomputable section

namespace GlobalTheory.CompanionTheory.MPDict.UnderIdeal

section Alg

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {A Ω : Type*} [CommRing A] [Field Ω]

theorem eval_eq_zero_of_mem_mCoordIdeal (e : A →+* Ω) (he : Function.Injective e) (ρ : (Σ k, ι k) → A)
    {f : Geo.MRing ι} (hf : f ∈ Geo.mCoordIdeal fun p => e (ρ p)) (ε : A →+* ℂ) (t : K → ℂ) :
    eval (fun p => t p.1 * ε (ρ p)) (MvPolynomial.map (Int.castRingHom ℂ) f) = 0 := by
  let q : Geo.MRing ι →+* MvPolynomial K A := eval₂Hom (Int.castRingHom _) fun p => C (ρ p) * X p.1
  have h1 : (MvPolynomial.map e).comp q =
      (Geo.mConeMap (fun p => e (ρ p)) : Geo.MRing ι →ₐ[ℤ] MvPolynomial K Ω).toRingHom := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun p => ?_)
    · simp [q]
    · simp [q, Geo.mConeMap]
  have h0 : q f = 0 := by
    refine map_injective e he ?_
    rw [map_zero]
    have := congrArg (fun g => g f) h1
    refine this.trans ?_
    exact hf
  have h2 : (eval₂Hom ε t).comp q =
      (eval (fun p => t p.1 * ε (ρ p))).comp (MvPolynomial.map (Int.castRingHom ℂ)) := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun p => ?_)
    · simp [q]
    · simp [q, mul_comm]
  have := congrArg (fun g => g f) h2
  simp only [RingHom.comp_apply, h0, map_zero] at this
  exact this.symm

end Alg

variable {m : ℕ} {n : Fin (m + 1) → ℕ}

theorem ptCoord_eq_mul (x : MP ℤ m n) (c : ∀ k, Bk n k) (hx : x ∈ mchart c) :
    ∃ b : Fin (m + 1) → (MP ℤ m n).residueField x, (∀ k, b k ≠ 0) ∧ ∀ p : Σ k, Bk n k,
      ptCoord x p = b p.1 * (MP ℤ m n).evaluation (mchart c) x hx
        (resG _ (mchart_le c p.1) (pullRatio (prB n p.1) _ (c p.1) le_rfl p.2)) := by
  have key : ∀ k, ∃ b : (MP ℤ m n).residueField x, b ≠ 0 ∧ ∀ j : Bk n k,
      ptCoord x ⟨k, j⟩ = b * (MP ℤ m n).evaluation (blockChart n k (c k)) x (mchart_le c k hx)
        (pullRatio (prB n k) _ (c k) le_rfl j) := by
    intro k
    let W₀ := blockChart n k (ptChart x k)
    let W₁ := blockChart n k (c k)
    let V := W₀ ⊓ W₁
    have hxV : x ∈ V := ⟨mem_ptChart x k, mchart_le c k hx⟩
    have hV₀ : V ≤ prB n k ⁻¹ᵁ chart ℤ (n k) (ptChart x k) := inf_le_left
    have hV₁ : V ≤ prB n k ⁻¹ᵁ chart ℤ (n k) (c k) := inf_le_right
    have e₀ : ∀ j : Bk n k, ptCoord x ⟨k, j⟩ =
        (MP ℤ m n).evaluation V x hxV (pullRatio (prB n k) V (ptChart x k) hV₀ j) := by
      intro j
      show (MP ℤ m n).evaluation W₀ x (mem_ptChart x k) (pullRatio (prB n k) W₀ (ptChart x k) le_rfl j) = _
      rw [← ProjImage.evaluation_resG (inf_le_left : V ≤ W₀) x hxV]
      exact congrArg _ (resG_pullRatio (φ := prB n k) (hi := le_rfl) inf_le_left)
    have e₁ : ∀ j : Bk n k, (MP ℤ m n).evaluation W₁ x (mchart_le c k hx)
        (pullRatio (prB n k) W₁ (c k) le_rfl j) =
        (MP ℤ m n).evaluation V x hxV (pullRatio (prB n k) V (c k) hV₁ j) := by
      intro j
      rw [← ProjImage.evaluation_resG (inf_le_right : V ≤ W₁) x hxV]
      exact congrArg _ (resG_pullRatio (φ := prB n k) (hi := le_rfl) inf_le_right)
    refine ⟨(MP ℤ m n).evaluation V x hxV (pullRatio (prB n k) V (ptChart x k) hV₀ (c k)), ?_, fun j => ?_⟩
    · intro h0
      have e := congrArg ((MP ℤ m n).evaluation V x hxV)
        ((pullRatio_mul_pullRatio (φ := prB n k) (hi := hV₀) (hj := hV₁) (k := ptChart x k)).trans pullRatio_self)
      rw [map_mul, h0, zero_mul, map_one] at e
      exact zero_ne_one e
    · refine (e₀ j).trans ?_
      rw [e₁ j, ← map_mul]
      exact congrArg _ (pullRatio_mul_pullRatio (φ := prB n k) (hi := hV₀) (hj := hV₁) (k := j)).symm
  choose b hb hbe using key
  refine ⟨b, hb, fun p => ?_⟩
  rw [ProjImage.evaluation_resG]
  exact hbe p.1 p.2

theorem evaluation_genericPoint_injective {X : Scheme.{0}} [IsIntegral X] (U : X.Opens) (h : genericPoint X ∈ U) :
    Function.Injective (X.evaluation U (genericPoint X) h) := by
  have h1 : Function.Injective (X.residue (genericPoint X)).hom :=
    RingHom.injective (R := X.functionField) (X.residue (genericPoint X)).hom
  exact h1.comp (fnOf_injective U h)

end GlobalTheory.CompanionTheory.MPDict.UnderIdeal

namespace GlobalTheory.CompanionTheory.MPDict


open UnderIdeal in
theorem exists_mem_mcPts_isUnder : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (X : Scheme.{0}) [IsIntegral X] (i : X ⟶ MP ℤ m n) [IsClosedImmersion i]
    (y : GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀), ∃ z ∈ mcPts (ptIdeal (i (genericPoint X))), IsUnder (PtsOver.map i rfl _ y) z := by
  intro m n X _ i _ y
  obtain ⟨z, hz, hu⟩ := exists_isUnder_of_cxPt m n (PtsOver.map i rfl _ y)
  refine ⟨z, ⟨hz, fun f hf => ?_⟩, hu⟩
  choose c hc using hz
  have hwk : ∀ k, PtsOver.map i rfl _ y ∈ ptsIn (mpStr ℤ m n) σ₀ (blockChart n k (c k)) :=
    fun k => (hu k (c k)).1.2 (hc k)
  have hwV : PtsOver.map i rfl _ y ∈ ptsIn (mpStr ℤ m n) σ₀ (mchart c) :=
    CxPts.mem_ptsIn.2 (Set.mem_iInter.2 fun k => CxPts.mem_ptsIn.1 (hwk k))
  have hyV : y ∈ ptsIn (i ≫ mpStr ℤ m n) σ₀ (i ⁻¹ᵁ mchart c) := hwV
  have hη : genericPoint X ∈ i ⁻¹ᵁ mchart c :=
    ((genericPoint_spec X).mem_open_set_iff (i ⁻¹ᵁ mchart c).isOpen).2 ⟨_, trivial, CxPts.mem_ptsIn.1 hyV⟩
  obtain ⟨b, hb, hbe⟩ := ptCoord_eq_mul (i (genericPoint X)) c hη
  let r : (Σ k, Bk n k) → Γ(MP ℤ m n, mchart c) := fun p =>
    resG _ (mchart_le c p.1) (pullRatio (prB n p.1) _ (c p.1) le_rfl p.2)
  let ρ : (Σ k, Bk n k) → Γ(X, i ⁻¹ᵁ mchart c) := fun p => (i.app (mchart c)).hom (r p)
  let φ := (i.residueFieldMap (genericPoint X)).hom
  have hf' : f ∈ Geo.mCoordIdeal fun p => (X.evaluation _ _ hη).hom (ρ p) := by
    have e := ProjImage.imageZ_mCoordIdeal_of_eq (ι := Bk n) (ι' := Bk n) id Function.injective_id id (fun _ => rfl) φ
      (fun k => φ (b k)) (fun k => (map_ne_zero φ).2 (hb k))
      (ptCoord (i (genericPoint X))) (fun p => (X.evaluation _ _ hη).hom (ρ p)) (fun p => by
        rw [hbe p, map_mul]
        congr 1
        exact Scheme.evaluation_naturality_apply _ _ _ _)
    rw [ptIdeal, ← e] at hf
    simpa [ReciprocityTheory.ChartRestriction.G.AI.I4.imageZ] using hf
  have h := eval_eq_zero_of_mem_mCoordIdeal (X.evaluation _ _ hη).hom
    (evaluation_genericPoint_injective _ hη) ρ hf' (evHom hyV) (fun k => z ⟨k, c k⟩)
  have hz' : (fun p : Σ k, Bk n k => z ⟨p.1, c p.1⟩ * evHom hyV (ρ p)) = z := by
    funext ⟨k, j⟩
    have e1 : evHom hyV (ρ ⟨k, j⟩) = z ⟨k, j⟩ / z ⟨k, c k⟩ := by
      rw [← CxPts.ev_eq hyV]
      refine Eq.trans ?_ ((hu k (c k)).2 j (hwk k))
      refine Eq.trans ?_ (CxPts.ev_res (mchart_le c k) hwV _)
      exact (valR_comp y.1 i (mchart c) (r ⟨k, j⟩)).symm
    show z ⟨k, c k⟩ * evHom hyV (ρ ⟨k, j⟩) = z ⟨k, j⟩
    rw [e1, mul_div_cancel₀ _ (hc k)]
  rw [hz'] at h
  exact h

end GlobalTheory.CompanionTheory.MPDict
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ComplexPointLiftsToMulticoneStatement
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complex_point_lifts_to_multicone : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (X : Scheme.{0}) [IsIntegral X] (i : X ⟶ MP ℤ m n) [IsClosedImmersion i]
    (y : GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀), ∃ z ∈ mcPts (ptIdeal (i (genericPoint X))), IsUnder (PtsOver.map i rfl _ y) z := by
  first | exact @GlobalTheory.CompanionTheory.MPDict.exists_mem_mcPts_isUnder | exact GlobalTheory.CompanionTheory.MPDict.exists_mem_mcPts_isUnder | (intros; apply GlobalTheory.CompanionTheory.MPDict.exists_mem_mcPts_isUnder <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralOfTwistConjugatePlace
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host
open GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.SuppFinTw

open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

def atH (a b : ℕ) (w : Pl E) : Gf E a b →* GLw a w × GLw b w :=
  (GeneralLinearGroup.map (pLoc E w)).prodMap (GeneralLinearGroup.map (pLoc E w))

abbrev thW (a b : ℕ) (w : Pl E) : GLw a w × GLw b w →* GLw a w × GLw b w := (thL a w).prodMap (thL b w)

abbrev dW (w : Pl E) (δ₁ : GL (Fin a) E) (δ₂ : GL (Fin b) E) : GLw a w × GLw b w := (locEl a w δ₁, locEl b w δ₂)

abbrev dG (δ₁ : GL (Fin a) E) (δ₂ : GL (Fin b) E) : Gf E a b := (ratF E a δ₁, ratF E b δ₂)

abbrev KK (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) : Subgroup (Gf E a b) := (Kf E a).prod (Kf E b)


theorem mem_KK_iff (g : Gf E a b) : g ∈ KK E a b ↔ ∀ u : Pl E, atH a b u g ∈ K2 a b u := by
  simp only [KK, Subgroup.mem_prod, Kf, Subgroup.mem_iInf, Subgroup.mem_comap]
  exact ⟨fun h u => ⟨h.1 u, h.2 u⟩, fun h => ⟨fun u => (h u).1, fun u => (h u).2⟩⟩

theorem ext_atH {g h : Gf E a b} (H : ∀ u : Pl E, atH a b u g = atH a b u h) : g = h :=
  Prod.ext (GlobalTheory.EulerTwRestr.gl_ext fun u => congrArg Prod.fst (H u))
    (GlobalTheory.EulerTwRestr.gl_ext fun u => congrArg Prod.snd (H u))

theorem ae_mem_GL {n : ℕ} (x : GL (Fin n) (Af E)) :
    ∀ᶠ w in cofinite, GeneralLinearGroup.map (pLoc E w) x ∈ GlobalTheory.LFun.KGL w (n := n) := by
  have h1 : ∀ᶠ w in cofinite, ∀ i j, pLoc E w (x.1 i j) ∈ (w : Pl E).adicCompletionIntegers E :=
    eventually_all.2 fun i => eventually_all.2 fun j => (x.1 i j).2
  have h2 : ∀ᶠ w in cofinite, ∀ i j, pLoc E w ((x⁻¹).1 i j) ∈ (w : Pl E).adicCompletionIntegers E :=
    eventually_all.2 fun i => eventually_all.2 fun j => ((x⁻¹).1 i j).2
  filter_upwards [h1, h2] with w h1 h2
  exact GlobalTheory.EulerTwRestr.mem_KGL_iff.2 ⟨fun i j => by rw [GlobalTheory.EulerTwRestr.loc_val]; exact h1 i j,
    fun i j => by rw [GlobalTheory.EulerTwRestr.loc_inv_val]; exact h2 i j⟩

theorem ae_mem (g : Gf E a b) : ∀ᶠ u in cofinite, atH a b u g ∈ K2 a b u := by
  filter_upwards [ae_mem_GL g.1, ae_mem_GL g.2] with u h1 h2
  exact ⟨h1, h2⟩

theorem exists_GL_of_family {n : ℕ} (z : ∀ u : Pl E, GLw n u) (hz : ∀ᶠ u in cofinite, z u ∈ GlobalTheory.LFun.KGL u (n := n)) :
    ∃ g : GL (Fin n) (Af E), ∀ u, GeneralLinearGroup.map (pLoc E u) g = z u := by
  let M : Matrix (Fin n) (Fin n) (Af E) := Matrix.of fun i j =>
    ⟨fun w => (z w).1 i j, hz.mono fun w h => (GlobalTheory.EulerTwRestr.mem_KGL_iff.1 h).1 i j⟩
  let M' : Matrix (Fin n) (Fin n) (Af E) := Matrix.of fun i j =>
    ⟨fun w => ((z w)⁻¹).1 i j, hz.mono fun w h => (GlobalTheory.EulerTwRestr.mem_KGL_iff.1 h).2 i j⟩
  have hloc : ∀ P Q : Matrix (Fin n) (Fin n) (Af E),
      (∀ w : Pl E, P.map (pLoc E w) = Q.map (pLoc E w)) → P = Q := fun P Q h =>
    Matrix.ext fun i j => Subtype.ext (funext fun w => congrFun (congrFun (h w) i) j)
  have hMM' : M * M' = 1 := hloc _ _ fun w => by
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact (z w).mul_inv
  have hM'M : M' * M = 1 := hloc _ _ fun w => by
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact (z w).inv_mul
  exact ⟨⟨M, M', hMM', hM'M⟩, fun u => Units.ext (Matrix.ext fun i j => rfl)⟩

theorem exists_of_family (z : ∀ u : Pl E, GLw a u × GLw b u) (hz : ∀ᶠ u in cofinite, z u ∈ K2 a b u) :
    ∃ g : Gf E a b, ∀ u, atH a b u g = z u := by
  obtain ⟨g₁, h₁⟩ := exists_GL_of_family (fun u => (z u).1) (hz.mono fun u h => h.1)
  obtain ⟨g₂, h₂⟩ := exists_GL_of_family (fun u => (z u).2) (hz.mono fun u h => h.2)
  exact ⟨(g₁, g₂), fun u => Prod.ext (h₁ u) (h₂ u)⟩

theorem thP_thP (y : Gf E a b) : thP E a b (thP E a b y) = y :=
  Prod.ext (GlobalTheory.EulerTw.Comm.thF_thF y.1) (GlobalTheory.EulerTw.Comm.thF_thF y.2)

theorem atH_thP_congr {u v : Pl E} (huv : GlobalTheory.EulerTw.cPl E u = v) {g h : Gf E a b}
    (H : atH a b v g = atH a b v h) : atH a b u (thP E a b g) = atH a b u (thP E a b h) := by
  subst huv
  refine Prod.ext ?_ ?_
  · change GeneralLinearGroup.map (pLoc E u) (thF E a g.1) = GeneralLinearGroup.map (pLoc E u) (thF E a h.1)
    rw [GlobalTheory.EulerTw.IntRead.map_thF, GlobalTheory.EulerTw.IntRead.map_thF]
    exact congrArg _ (congrArg Prod.fst H)
  · change GeneralLinearGroup.map (pLoc E u) (thF E b g.2) = GeneralLinearGroup.map (pLoc E u) (thF E b h.2)
    rw [GlobalTheory.EulerTw.IntRead.map_thF, GlobalTheory.EulerTw.IntRead.map_thF]
    exact congrArg _ (congrArg Prod.snd H)

theorem integral_of_twist_conjugate_place (u : Pl E) {g : Gf E a b} (H : atH a b u (thP E a b g) ∈ K2 a b u) :
    atH a b (GlobalTheory.EulerTw.cPl E u) g ∈ K2 a b (GlobalTheory.EulerTw.cPl E u) := by
  refine ⟨GlobalTheory.EulerTw.IntRead.mem_KGL_of_thAt u _ ?_, GlobalTheory.EulerTw.IntRead.mem_KGL_of_thAt u _ ?_⟩
  · have := H.1
    change GeneralLinearGroup.map (pLoc E u) (thF E a g.1) ∈ _ at this
    rwa [GlobalTheory.EulerTw.IntRead.map_thF] at this
  · have := H.2
    change GeneralLinearGroup.map (pLoc E u) (thF E b g.2) ∈ _ at this
    rwa [GlobalTheory.EulerTw.IntRead.map_thF] at this

theorem map_thF_of_not_split {n : ℕ} {w : Pl E} (hw : ¬ IsSplitAt w) (g : GL (Fin n) (Af E)) :
    GeneralLinearGroup.map (pLoc E w) (thF E n g) = thL n w (GeneralLinearGroup.map (pLoc E w) g) := by
  rw [GlobalTheory.EulerTw.IntRead.map_thF]
  refine Units.ext (Matrix.ext fun i j => ?_)
  have h2 := GlobalTheory.ThetaPull.thetaGL_apply (a := n) (cj w) (GeneralLinearGroup.map (pLoc E w) g) i j
  have e : thL n w = thetaGL n (cj w) := if_neg hw
  rw [e, h2, GlobalTheory.EulerTw.IntRead.thAt_apply, GlobalTheory.EulerTwRestr.loc_inv_val, GlobalTheory.EulerTwRestr.loc_inv_val]
  congr 1
  exact GlobLev.conjLoc_eq_cj hw _

theorem usage₇ {w : Pl E} (hw : ¬ IsSplitAt w) (g : Gf E a b) :
    atH a b w (thP E a b g) = thW a b w (atH a b w g) :=
  Prod.ext (map_thF_of_not_split hw g.1) (map_thF_of_not_split hw g.2)

theorem thW_of_split {w : Pl E} (hw : IsSplitAt w) (y : GLw a w × GLw b w) : thW a b w y = y := by
  simp [thL, hw]

theorem atH_dG_of_not_split {w : Pl E} (hw : ¬ IsSplitAt w) (δ₁ : GL (Fin a) E) (δ₂ : GL (Fin b) E) :
    atH a b w (dG δ₁ δ₂) = dW w δ₁ δ₂ := by
  refine Prod.ext ?_ ?_
  · simp only [locEl, if_neg hw]; rfl
  · simp only [locEl, if_neg hw]; rfl

theorem atH_norm_of_split {w : Pl E} (hw : IsSplitAt w) (δ₁ : GL (Fin a) E) (δ₂ : GL (Fin b) E) :
    atH a b w (dG δ₁ δ₂ * thP E a b (dG δ₁ δ₂)) = dW w δ₁ δ₂ := by
  refine Prod.ext ?_ ?_
  · simp only [locEl, if_pos hw]
    change GeneralLinearGroup.map (pLoc E w) (ratF E a δ₁ * thF E a (ratF E a δ₁)) = _
    rw [← GlobalTheory.EulerTw.Comm.thF_ratF, ← map_mul]; rfl
  · simp only [locEl, if_pos hw]
    change GeneralLinearGroup.map (pLoc E w) (ratF E b δ₂ * thF E b (ratF E b δ₂)) = _
    rw [← GlobalTheory.EulerTw.Comm.thF_ratF, ← map_mul]; rfl

theorem mem_or_conj {S : Set (Pl E)} (hS : IsSection S) (u : Pl E) : u ∈ S ∨ ∃ v ∈ S, u = GlobalTheory.EulerTw.cPl E v := by
  obtain ⟨v, ⟨hv, hvu⟩, -⟩ := hS u
  rcases GlobLev.eq_or_eq_conjSrc hvu.symm with h | h
  · exact Or.inl (h ▸ hv)
  · exact Or.inr ⟨v, hv, h⟩

theorem split_of_conj_ne {v : Pl E} (h : GlobalTheory.EulerTw.cPl E v ≠ v) : IsSplitAt v := by
  by_contra hv
  exact h (GlobLev.conjSrc_eq_of_not_split hv)

theorem cPl_cPl (v : Pl E) : GlobalTheory.EulerTw.cPl E (GlobalTheory.EulerTw.cPl E v) = v := GlobalTheory.ThetaPull.conjSrc_conjSrc _

theorem conj_not_mem {S : Set (Pl E)} (hS : IsSection S) {v : Pl E} (hv : v ∈ S) (h : IsSplitAt v) :
    GlobalTheory.EulerTw.cPl E v ∉ S := by
  intro hc
  obtain ⟨u, hne, hu⟩ := h
  have h1 : (GlobalTheory.EulerTw.cPl E v).under (𝓞 (maximalRealSubfield E)) = v.under (𝓞 (maximalRealSubfield E)) :=
    (GlobalTheory.EulerTwRestr.mem_orb_iff v _).1 (by simp [GlobalTheory.EulerTw.orb])
  have h2 : GlobalTheory.EulerTw.cPl E v = v := (hS v).unique ⟨hc, h1⟩ ⟨hv, rfl⟩
  rcases GlobLev.eq_or_eq_conjSrc hu with h3 | h3
  · exact hne h3
  · exact hne (h3.trans h2)

end GlobalTheory.CompanionTheory.SuppFinTw

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DehomogenizedEvalEqRatio
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DehomogenizedEvalEqRatio
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit)

noncomputable section

namespace GlobalTheory.CompanionTheory.MixZ

theorem ev_dehomog_of_isUnder : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (c : ∀ k, Bk n k) (f : Pol n) (a : Fin (m + 1) → ℕ), IsMultiHomog f a →
    ∀ (w : GlobalTheory.CxPts (mpStr ℤ m n) σ₀) (z : (Σ k, Bk n k) → ℂ), IsUnder w z → w ∈ ptsIn (mpStr ℤ m n) σ₀ (mchart c) →
    ev (mpStr ℤ m n) σ₀ (mchart c) (dehomog c f) w =
      eval z (map (Int.castRingHom ℂ) f) / ∏ k, z ⟨k, c k⟩ ^ a k := by
  intro m n c f a hf w z H hw
  have hmem : ∀ k, w ∈ ptsIn (mpStr ℤ m n) σ₀ (blockChart n k (c k)) := fun k =>
    GlobalTheory.CxPts.ptsIn_mono (mchart_le c k) hw
  have hX : ∀ q, GlobalTheory.CxPts.evHom hw (dehomog c (X q)) = z q / z ⟨q.1, c q.1⟩ := by
    rintro ⟨k, i⟩
    rw [← GlobalTheory.CxPts.ev_eq hw]
    simp only [dehomog, coe_eval₂Hom, eval₂_X]
    rw [GlobalTheory.CxPts.ev_res _ hw]
    exact (H k (c k)).2 i (hmem k)
  have hφ : (GlobalTheory.CxPts.evHom hw).comp (dehomog c) =
      eval₂Hom (Int.castRingHom ℂ) (fun q => z q / z ⟨q.1, c q.1⟩) := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun q => ?_)
    · simp
    · simpa using hX q
  have hv : GlobalTheory.CxPts.evHom hw (dehomog c f) =
      eval₂ (Int.castRingHom ℂ) (fun q => z q / z ⟨q.1, c q.1⟩) f := by
    simpa using congrArg (fun φ => φ f) hφ
  rw [GlobalTheory.CxPts.ev_eq hw, hv, MvPolynomial.eval_map, eval₂_eq', eval₂_eq', Finset.sum_div]
  refine Finset.sum_congr rfl fun e he => ?_
  have hden : ∏ q : Σ k, Bk n k, z ⟨q.1, c q.1⟩ ^ e q = ∏ k, z ⟨k, c k⟩ ^ a k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    exact (Finset.prod_pow_eq_pow_sum Finset.univ (fun i : Bk n k => e ⟨k, i⟩) (z ⟨k, c k⟩)).trans (by rw [hf e he k])
  simp only [div_pow, Finset.prod_div_distrib, hden]
  rw [mul_div_assoc]

end GlobalTheory.CompanionTheory.MixZ
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DehomogenizedEvalEqRatioStatement
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dehomogenized_eval_eq_ratio : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (c : ∀ k, Bk n k) (f : Pol n) (a : Fin (m + 1) → ℕ), IsMultiHomog f a →
    ∀ (w : GlobalTheory.CxPts (mpStr ℤ m n) σ₀) (z : (Σ k, Bk n k) → ℂ), IsUnder w z → w ∈ ptsIn (mpStr ℤ m n) σ₀ (mchart c) →
    ev (mpStr ℤ m n) σ₀ (mchart c) (dehomog c f) w =
      eval z (map (Int.castRingHom ℂ) f) / ∏ k, z ⟨k, c k⟩ ^ a k := by
  first | exact @GlobalTheory.CompanionTheory.MixZ.ev_dehomog_of_isUnder | exact GlobalTheory.CompanionTheory.MixZ.ev_dehomog_of_isUnder | (intros; apply GlobalTheory.CompanionTheory.MixZ.ev_dehomog_of_isUnder <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RestrictedFormNonzeroOnGenericPoint
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RestrictedFormNonzeroOnGenericPoint
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit)
noncomputable section

namespace GlobalTheory.CompanionTheory.MixZ.FnForm

variable {m : ℕ} {n : Fin (m + 1) → ℕ}

theorem evaluation_resG_apply {X : Scheme.{0}} {U V : X.Opens} (h : V ≤ U) (x : X) (hx : x ∈ V) (s : Γ(X, U)) :
    (X.evaluation V x hx).hom (resG X h s) = (X.evaluation U x (h hx)).hom s := by
  show X.residue x (X.presheaf.germ V x hx (X.presheaf.map (homOfLE h).op s)) = _
  rw [TopCat.Presheaf.germ_res_apply]
  rfl

def chartCoord (c : ∀ k, Bk n k) (x : MP ℤ m n) (hx : x ∈ mchart c) (p : Σ k, Bk n k) :
    (MP ℤ m n).residueField x :=
  ((MP ℤ m n).evaluation (mchart c) x hx).hom
    (resG _ (mchart_le c p.1) (pullRatio (prB n p.1) _ (c p.1) le_rfl p.2))

theorem ptCoord_eq_mul_chartCoord (c : ∀ k, Bk n k) (x : MP ℤ m n) (hx : x ∈ mchart c) (p : Σ k, Bk n k) :
    ptCoord x p = ptCoord x ⟨p.1, c p.1⟩ * chartCoord c x hx p := by
  obtain ⟨k, j⟩ := p
  let P : MP ℤ m n ⟶ PSpace ℤ (n k) := prB n k
  let W₀ : (MP ℤ m n).Opens := blockChart n k (ptChart x k)
  let W₁ : (MP ℤ m n).Opens := blockChart n k (c k)
  have h₀ : W₀ ≤ P ⁻¹ᵁ chart ℤ (n k) (ptChart x k) := le_rfl
  have h₁ : W₁ ≤ P ⁻¹ᵁ chart ℤ (n k) (c k) := le_rfl
  have hx₀ : x ∈ W₀ := mem_ptChart x k
  have hx₁ : x ∈ W₁ := mchart_le c k hx
  let V := W₀ ⊓ W₁
  have hxV : x ∈ V := ⟨hx₀, hx₁⟩
  have hV₀ : V ≤ P ⁻¹ᵁ chart ℤ (n k) (ptChart x k) := inf_le_left.trans h₀
  have hV₁ : V ≤ P ⁻¹ᵁ chart ℤ (n k) (c k) := inf_le_right.trans h₁
  have e₀ : ∀ l : Bk n k, ptCoord x ⟨k, l⟩ =
      ((MP ℤ m n).evaluation V x hxV).hom (pullRatio P V (ptChart x k) hV₀ l) := by
    intro l
    show ((MP ℤ m n).evaluation W₀ x hx₀).hom (pullRatio P W₀ (ptChart x k) h₀ l) = _
    rw [← evaluation_resG_apply (inf_le_left : V ≤ W₀) x hxV]
    exact congrArg _ (resG_pullRatio (φ := P) (hi := h₀) inf_le_left)
  have e₁ : chartCoord c x hx ⟨k, j⟩ =
      ((MP ℤ m n).evaluation V x hxV).hom (pullRatio P V (c k) hV₁ j) := by
    show ((MP ℤ m n).evaluation (mchart c) x hx).hom (resG _ (mchart_le c k) (pullRatio P W₁ (c k) h₁ j)) = _
    rw [evaluation_resG_apply, ← evaluation_resG_apply (inf_le_right : V ≤ W₁) x hxV]
    exact congrArg _ (resG_pullRatio (φ := P) (hi := h₁) inf_le_right)
  show ptCoord x ⟨k, j⟩ = ptCoord x ⟨k, c k⟩ * chartCoord c x hx ⟨k, j⟩
  rw [e₀ j, e₀ (c k), e₁, ← map_mul]
  exact congrArg _ (pullRatio_mul_pullRatio (φ := P) (hi := hV₀) (hj := hV₁) (k := j)).symm

theorem evaluation_dehomog (c : ∀ k, Bk n k) (x : MP ℤ m n) (hx : x ∈ mchart c) (f : Pol n) :
    ((MP ℤ m n).evaluation (mchart c) x hx).hom (dehomog c f) = aeval (chartCoord c x hx) f := by
  have e : ((MP ℤ m n).evaluation (mchart c) x hx).hom.comp (dehomog c) =
      (aeval (chartCoord c x hx) : Pol n →ₐ[ℤ] _).toRingHom :=
    MvPolynomial.ringHom_ext (fun r => by simp) (fun p => by simp [dehomog, chartCoord])
  exact congrArg (fun φ => φ f) e

theorem aeval_ptCoord_eq_mul (c : ∀ k, Bk n k) (x : MP ℤ m n) (hx : x ∈ mchart c) {f : Pol n}
    {a : Fin (m + 1) → ℕ} (hf : IsMultiHomog f a) :
    aeval (ptCoord x) f = (∏ k, ptCoord x ⟨k, c k⟩ ^ a k) *
      ((MP ℤ m n).evaluation (mchart c) x hx).hom (dehomog c f) := by
  rw [evaluation_dehomog, ← GroundTheory.Heights₂.Heights.HilbertSamuel.BlockImageInverse.aeval_smul hf]
  exact congrArg (fun v => aeval v f) (funext (ptCoord_eq_mul_chartCoord c x hx))

theorem fnAt_ne_zero_of_notMem_ptIdeal : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (X : Scheme.{0}) [IsIntegral X] (i : X ⟶ MP ℤ m n) [IsClosedImmersion i]
    (c : ∀ k, Bk n k) (h : genericPoint X ∈ i ⁻¹ᵁ mchart c) (f : Pol n) (a : Fin (m + 1) → ℕ), IsMultiHomog f a →
    f ∉ ptIdeal (i (genericPoint X)) → fnAt i c h f ≠ 0 := by
  intro m n X _ i _ c h f a hf hnot h0
  refine hnot ((mem_ptIdeal_iff_aeval_ptCoord m n _ f a hf).2 ?_)
  have hx : i (genericPoint X) ∈ mchart c := h
  have h1 : i.app (mchart c) (dehomog c f) = 0 :=
    fnOf_injective _ h (h0.trans (map_zero _).symm)
  have h2 : ((MP ℤ m n).evaluation (mchart c) _ hx).hom (dehomog c f) = 0 := by
    apply (i.residueFieldMap (genericPoint X)).hom.injective
    rw [map_zero]
    refine (Scheme.evaluation_naturality_apply i (genericPoint X) hx _).trans ?_
    rw [h1, map_zero]
  rw [aeval_ptCoord_eq_mul c _ hx hf, h2, mul_zero]

end GlobalTheory.CompanionTheory.MixZ.FnForm
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RestrictedFormNonzeroOnGenericPointStatement
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.restricted_form_nonzero_on_generic_point : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (X : Scheme.{0}) [IsIntegral X] (i : X ⟶ MP ℤ m n) [IsClosedImmersion i]
    (c : ∀ k, Bk n k) (h : genericPoint X ∈ i ⁻¹ᵁ mchart c) (f : Pol n) (a : Fin (m + 1) → ℕ), IsMultiHomog f a →
    f ∉ ptIdeal (i (genericPoint X)) → fnAt i c h f ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.MixZ.FnForm.fnAt_ne_zero_of_notMem_ptIdeal | exact GlobalTheory.CompanionTheory.MixZ.FnForm.fnAt_ne_zero_of_notMem_ptIdeal | (intros; apply GlobalTheory.CompanionTheory.MixZ.FnForm.fnAt_ne_zero_of_notMem_ptIdeal <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalGramFibrationDisintegration
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalGramFibrationDisintegration
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.Free.FibreInv

theorem isFibreFamily_map_homeo {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V]
    [TopologicalSpace X] [MeasurableSpace X] (μ : Measure V) (ν : Measure X) (f : V → Y) (ι : X → Y)
    (e : V ≃ₜ V) (hf : ∀ v, f (e v) = f v) (U : Set V) (hU : e ⁻¹' U = U) (hμ : μ.map e = μ)
    (B : Set X) (fib : X → Measure V) (h : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι U ν B fib) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι U ν B (fun b => (fib b).map e) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hemb : MeasurableEmbedding e := e.measurableEmbedding
  refine ⟨?_, ?_, ?_⟩
  · intro b
    have hset : e ⁻¹' (f ⁻¹' {ι b} ∩ U)ᶜ = (f ⁻¹' {ι b} ∩ U)ᶜ := by
      rw [Set.preimage_compl, Set.preimage_inter, hU]
      congr 2
      ext v
      simp only [Set.mem_preimage, Set.mem_singleton_iff, hf]
    show ((fib b).map e) _ = 0
    rw [hemb.map_apply, hset]
    exact h1 b
  · intro φ hφ
    have hr : μ.restrict U = (μ.restrict U).map e := by
      have := hemb.restrict_map μ U
      rw [hμ, hU] at this
      exact this
    rw [hr, hemb.lintegral_map, h2 (fun v => φ (e v)) (hφ.comp e.measurable)]
    refine lintegral_congr fun b => ?_
    simp only [hemb.lintegral_map]
  · intro φ hφ hcs hts
    have hts' : tsupport (φ ∘ e) ⊆ U := by
      rw [tsupport_comp_eq_preimage, ← hU]
      exact Set.preimage_mono hts
    obtain ⟨hi, hcont⟩ := h3 (φ ∘ e) (hφ.comp e.continuous)
      (hcs.comp_isClosedEmbedding e.isClosedEmbedding) hts'
    refine ⟨fun b hb => ?_, ?_⟩
    · rw [hemb.integrable_map_iff]
      exact hi b hb
    · have : (fun b => ∫ v, φ v ∂((fib b).map e)) = fun b => ∫ v, (φ ∘ e) v ∂(fib b) := by
        funext b
        exact hemb.integral_map φ
      rw [this]
      exact hcont

theorem linearIndependent_mulVec {K : Type} [CommRing K] {M n : ℕ} (g : GL (Fin M) K) (X : Fin n → Fin M → K)
    (hX : LinearIndependent K X) :
    LinearIndependent K (fun a => (g : Matrix (Fin M) (Fin M) K).mulVec (X a)) := by
  have hinj : Function.Injective (Matrix.mulVecLin (g : Matrix (Fin M) (Fin M) K)) := by
    intro x y hxy
    have h2 := congrArg (((g⁻¹ : GL (Fin M) K) : Matrix (Fin M) (Fin M) K).mulVec) hxy
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at h2
    exact h2
  exact hX.map' (Matrix.mulVecLin (g : Matrix (Fin M) (Fin M) K)) (LinearMap.ker_eq_bot.2 hinj)

theorem map_actW_fibre_free : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n : ℕ), ∀ (μ : Measure (Fin n → Fin M → R ⊗[F] E)) (ν : Measure (HermR R σ n)) (m : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → IsGramFibFree R σ J n μ ν m → ∀ (h : HA R σ J) (S : HermR R σ n), (m S).map (actW R σ J h) = m S := by
  intro F E _ _ _ _ _ σ hσ M J hJ R _ _ _ _ _ hR n μ ν m hμ hν hm h S
  have hR' := hR
  obtain ⟨_, _, _, _, -, -, -, -⟩ := hR'
  obtain ⟨_, _, _, _, -, -, -, hbor, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ R
  have hbor' := hbor n M
  obtain ⟨_, _, _, _, hlift⟩ := GlobalTheory.CompanionTheory.SW.HermTop.herm_top F E σ hσ R n
  obtain ⟨g, hgc, hgf⟩ := hlift M J hJ
  obtain ⟨_, -, -, -, -, hact⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hσ M J hJ R
  obtain ⟨hcont, hone, hmul, hgr⟩ := hact n
  have hcg : ∀ k : HA R σ J, Continuous (actW R σ J k : (Fin n → Fin M → R ⊗[F] E) → _) := fun k =>
    hcont.comp (Continuous.prodMk_right k)
  let e : (Fin n → Fin M → R ⊗[F] E) ≃ₜ (Fin n → Fin M → R ⊗[F] E) :=
    { toFun := actW R σ J h
      invFun := actW R σ J h⁻¹
      left_inv := fun X => by rw [← hmul, inv_mul_cancel, hone]
      right_inv := fun X => by rw [← hmul, mul_inv_cancel, hone]
      continuous_toFun := hcg h
      continuous_invFun := hcg h⁻¹ }
  let W : Set (Fin n → Fin M → R ⊗[F] E) := {X | LinearIndependent (R ⊗[F] E) X}
  have hWo : IsOpen W := GlobalTheory.T.linearly_independent_frames_open F E σ hσ R hR n M
  have hfree : ∀ (k : HA R σ J) (X : Fin n → Fin M → R ⊗[F] E), X ∈ W → actW R σ J k X ∈ W :=
    fun k X hX => linearIndependent_mulVec (HA.mat R σ J k) X hX
  have hU : e ⁻¹' W = W := by
    ext X
    refine ⟨fun hX => ?_, hfree h X⟩
    have h2 : actW R σ J h⁻¹ (actW R σ J h X) ∈ W := hfree h⁻¹ _ hX
    have h3 : actW R σ J h⁻¹ (actW R σ J h X) = X := by rw [← hmul, inv_mul_cancel, hone]
    rw [h3] at h2
    exact h2
  have hμm : μ.map e = μ := GlobalTheory.T.unitary_action_preserves_haar_local F E σ hσ M J hJ R hR n μ hμ h
  have ht := isFibreFamily_map_homeo μ ν (gramR R σ J) Subtype.val e (fun X => hgr h X) W hU hμm
    Set.univ m hm
  have hm0 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ (gramR R σ J) Subtype.val (g ⁻¹' Set.univ ∩ W) ν Set.univ m := by
    rw [Set.preimage_univ, Set.univ_inter]
    exact hm
  have ht0 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ (gramR R σ J) Subtype.val (g ⁻¹' Set.univ ∩ W) ν Set.univ
      (fun b => (m b).map e) := by
    rw [Set.preimage_univ, Set.univ_inter]
    exact ht
  exact GlobalTheory.T.measurable_embedding_of_injective_proper _ _ _ μ ν (gramR R σ J) g Subtype.val Subtype.val_injective hgc hgf W hWo Set.univ Set.univ
    isOpen_univ isOpen_univ subset_rfl m (fun b => (m b).map e) hm0 ht0 S (Set.mem_univ S)

end GlobalTheory.CompanionTheory.WeilSiegel.Free.FibreInv
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalGramFibrationDisintegrationStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_gram_fibration_disintegration : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n : ℕ), ∀ (μ : Measure (Fin n → Fin M → R ⊗[F] E)) (ν : Measure (HermR R σ n)) (m : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → IsGramFibFree R σ J n μ ν m → ∀ (h : HA R σ J) (S : HermR R σ n), (m S).map (actW R σ J h) = m S := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.Free.FibreInv.map_actW_fibre_free | exact GlobalTheory.CompanionTheory.WeilSiegel.Free.FibreInv.map_actW_fibre_free | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.Free.FibreInv.map_actW_fibre_free <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalSupportFacts
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalSupportFacts
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT PositivityTheory.Rg.BcB.G8
open scoped Classical

namespace GlobalTheory.CompanionTheory.TwistOrbit

theorem finite_of_subset_mul' {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (T K' : Subgroup G)
    (hK' : IsOpen (K' : Set G)) (D : Set G) (hD : IsCompact D)
    (P : G → Prop) (hP : ∀ x, P x → ∃ t ∈ T, ∃ d ∈ D, x = t * d) :
    {q : DoubleCoset.Quotient (T : Set G) (K' : Set G) | P (Quotient.out q)}.Finite := by
  obtain ⟨s, hs⟩ := compact_covered_by_mul_left_translates hD
    (show (interior (K' : Set G)).Nonempty from ⟨1, hK'.interior_eq.symm ▸ K'.one_mem⟩)
  refine (s.finite_toSet.image fun g => DoubleCoset.mk T K' g⁻¹).subset ?_
  intro q hq
  obtain ⟨t, ht, d, hd, hx⟩ := hP _ hq
  have := hs hd
  simp only [Set.mem_iUnion, Set.mem_preimage, SetLike.mem_coe] at this
  obtain ⟨g, hg, hgd⟩ := this
  refine ⟨g, hg, ?_⟩
  rw [← DoubleCoset.out_eq' q, DoubleCoset.eq]
  exact ⟨t, ht, g * d, hgd, by simp [hx, mul_assoc]⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem nrmL_twConj' (hU : Unr E) (n : ℕ) (w : Pl E) (x y : GLw n w) :
    nrmL n w (x⁻¹ * y * thL n w x) = x⁻¹ * nrmL n w y * x := by
  by_cases hs : IsSplitAt w
  · have h1 : thL n w = MonoidHom.id _ := by rw [thL, if_pos hs]
    simp only [nrmL, if_pos hs, h1, MonoidHom.id_apply]
  · have h1 : thL n w = thetaGL n (cj w) := by rw [thL, if_neg hs]
    have h2 := (GlobalTheory.BCT.thL_continuous_involutive E hU n w).2
    rw [h1] at h2
    simp only [nrmL, if_neg hs, h1, map_mul, map_inv, h2]
    group

theorem continuous_nrmL' (hU : Unr E) (n : ℕ) (w : Pl E) : Continuous (nrmL n w) := by
  by_cases hs : IsSplitAt w
  · have e : nrmL n w = fun u => u := funext fun u => by simp [nrmL, hs]
    rw [e]; exact continuous_id
  · have h1 : thL n w = thetaGL n (cj w) := by rw [thL, if_neg hs]
    have hc := (GlobalTheory.BCT.thL_continuous_involutive E hU n w).1
    rw [h1] at hc
    have e : nrmL n w = fun u => u * thetaGL n (cj w) u := funext fun u => by simp [nrmL, hs]
    rw [e]; exact continuous_id.mul hc

theorem proper' (hU : Unr E) (n : ℕ) (w : Pl E) (y : GLw n w) (hy : (nrmL n w y).val.charpoly.Separable)
    (C : Set (GLw n w)) (hC : IsCompact C) : ∃ D : Set (GLw n w), IsCompact D ∧
      ∀ x : GLw n w, x⁻¹ * y * thL n w x ∈ C → ∃ t ∈ twCent (thL n w) y, ∃ d ∈ D, x = t * d := by
  have hθ := (GlobalTheory.BCT.thL_continuous_involutive E hU n w).1
  obtain ⟨D₁, hD₁, h₁⟩ := GlobalTheory.T.orbit_compact_mod_centralizer_separable_local E hU n w (nrmL n w y) hy _ (hC.image (continuous_nrmL' hU n w))
  set C₂ := (fun p : GLw n w × GLw n w × GLw n w => p.1 * p.2.1 * (thL n w p.2.2)⁻¹) '' (D₁ ×ˢ C ×ˢ D₁)
  have hC₂ : IsCompact C₂ := (hD₁.prod (hC.prod hD₁)).image (by fun_prop)
  obtain ⟨D₂, hD₂, h₂⟩ := GlobalTheory.NormOneProper.main E hU n w y hy C₂ hC₂
  refine ⟨(fun p : GLw n w × GLw n w => p.1 * p.2) '' (D₂ ×ˢ D₁), (hD₂.prod hD₁).image (by fun_prop), ?_⟩
  intro x hx
  obtain ⟨z, hz, d, hd, rfl⟩ := h₁ x ⟨_, hx, by rw [nrmL_twConj' hU]⟩
  have hz2 : z⁻¹ * y * thL n w z ∈ C₂ := ⟨(d, (z * d)⁻¹ * y * thL n w (z * d), d), ⟨hd, hx, hd⟩, by
    simp only [map_mul]; group⟩
  obtain ⟨t, ht, d₂, hd₂, rfl⟩ := h₂ z hz hz2
  exact ⟨t, ht, d₂ * d, ⟨(d₂, d), ⟨hd₂, hd⟩, rfl⟩, by group⟩

theorem continuous_thPair (hU : Unr E) (a b : ℕ) (w : Pl E) :
    Continuous ((thL a w).prodMap (thL b w)) := by
  have h1 := (GlobalTheory.BCT.thL_continuous_involutive E hU a w).1
  have h2 := (GlobalTheory.BCT.thL_continuous_involutive E hU b w).1
  exact (h1.comp continuous_fst).prodMk (h2.comp continuous_snd)

theorem isOpen_isCompact_pair_integral_points (a b : ℕ) (w : Pl E) :
    IsOpen (K2 a b w : Set (GLw a w × GLw b w)) ∧ IsCompact (K2 a b w : Set (GLw a w × GLw b w)) := by
  obtain ⟨o₁, c₁⟩ := GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w a
  obtain ⟨o₂, c₂⟩ := GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w b
  rw [K2, Subgroup.coe_prod]
  exact ⟨o₁.prod o₂, c₁.prod c₂⟩

theorem proper_pair (hU : Unr E) (a b : ℕ) (w : Pl E) (y : GLw a w × GLw b w)
    (h₁ : (nrmL a w y.1).val.charpoly.Separable) (h₂ : (nrmL b w y.2).val.charpoly.Separable)
    (C : Set (GLw a w × GLw b w)) (hC : IsCompact C) :
    ∃ D : Set (GLw a w × GLw b w), IsCompact D ∧ ∀ x : GLw a w × GLw b w,
      x⁻¹ * y * ((thL a w).prodMap (thL b w)) x ∈ C →
        ∃ t ∈ twCent ((thL a w).prodMap (thL b w)) y, ∃ d ∈ D, x = t * d := by
  obtain ⟨D₁, hD₁, p₁⟩ := proper' hU a w y.1 h₁ _ (hC.image continuous_fst)
  obtain ⟨D₂, hD₂, p₂⟩ := proper' hU b w y.2 h₂ _ (hC.image continuous_snd)
  refine ⟨D₁ ×ˢ D₂, hD₁.prod hD₂, fun x hx => ?_⟩
  obtain ⟨t₁, ht₁, d₁, hd₁, e₁⟩ := p₁ x.1 ⟨_, hx, rfl⟩
  obtain ⟨t₂, ht₂, d₂, hd₂, e₂⟩ := p₂ x.2 ⟨_, hx, rfl⟩
  refine ⟨(t₁, t₂), ?_, (d₁, d₂), ⟨hd₁, hd₂⟩, Prod.ext e₁ e₂⟩
  exact Prod.ext ht₁ ht₂

theorem finite_doubleCosets (hU : Unr E) (a b : ℕ) (w : Pl E) (y : GLw a w × GLw b w)
    (h₁ : (nrmL a w y.1).val.charpoly.Separable) (h₂ : (nrmL b w y.2).val.charpoly.Separable)
    (C : Set (GLw a w × GLw b w)) (hC : IsCompact C) :
    {q : DoubleCoset.Quotient (twCent ((thL a w).prodMap (thL b w)) y : Set (GLw a w × GLw b w))
        (K2 a b w : Set (GLw a w × GLw b w)) |
      ∃ k ∈ K2 a b w, (Quotient.out q * k)⁻¹ * y * ((thL a w).prodMap (thL b w)) (Quotient.out q * k) ∈ C}.Finite := by
  obtain ⟨hKo, hKc⟩ := isOpen_isCompact_pair_integral_points (E := E) a b w
  obtain ⟨D, hD, hp⟩ := proper_pair hU a b w y h₁ h₂ C hC
  have hD' : IsCompact ((fun p : (GLw a w × GLw b w) × (GLw a w × GLw b w) => p.1 * p.2⁻¹) ''
      (D ×ˢ (K2 a b w : Set (GLw a w × GLw b w)))) :=
    (hD.prod hKc).image (continuous_fst.mul continuous_snd.inv)
  refine finite_of_subset_mul' _ (K2 a b w) hKo _ hD'
    (fun x => ∃ k ∈ K2 a b w, (x * k)⁻¹ * y * ((thL a w).prodMap (thL b w)) (x * k) ∈ C) ?_
  rintro x ⟨k, hk, hx⟩
  obtain ⟨t, ht, d, hd, e⟩ := hp _ hx
  refine ⟨t, ht, d * k⁻¹, ⟨(d, k), ⟨hd, hk⟩, rfl⟩, ?_⟩
  rw [← mul_assoc, ← e, mul_inv_cancel_right]

theorem rStab_index_ne_zero (hU : Unr E) (a b : ℕ) (w : Pl E) (y : GLw a w × GLw b w)
    (K' : Subgroup (GLw a w × GLw b w)) (f : GLw a w × GLw b w → ℂ) (ho : IsOpen (K' : Set (GLw a w × GLw b w)))
    (hf : IsHecke K' f) (x : K2 a b w) :
    (rStab fun k : K2 a b w => f (((x * k : K2 a b w) : GLw a w × GLw b w)⁻¹ * y *
      ((thL a w).prodMap (thL b w)) ((x : GLw a w × GLw b w) * k))).index ≠ 0 := by
  obtain ⟨-, hKc⟩ := isOpen_isCompact_pair_integral_points (E := E) a b w
  have hθ := continuous_thPair hU a b w
  set θ := (thL a w).prodMap (thL b w) with hθdef
  set W : Subgroup (GLw a w × GLw b w) := K' ⊓ K'.comap θ with hW
  have hWo : IsOpen (W : Set (GLw a w × GLw b w)) := by
    rw [hW, Subgroup.coe_inf]
    exact ho.inter (ho.preimage hθ)
  haveI : CompactSpace (K2 a b w) := isCompact_iff_compactSpace.mp hKc
  have hWo' : IsOpen ((W.subgroupOf (K2 a b w) : Subgroup (K2 a b w)) : Set (K2 a b w)) :=
    hWo.preimage continuous_subtype_val
  haveI := Subgroup.quotient_finite_of_isOpen _ hWo'
  haveI : (W.subgroupOf (K2 a b w)).FiniteIndex := ⟨Subgroup.index_ne_zero_of_finite⟩
  have hle : W.subgroupOf (K2 a b w) ≤ rStab fun k : K2 a b w => f (((x * k : K2 a b w) : GLw a w × GLw b w)⁻¹ * y *
      θ ((x : GLw a w × GLw b w) * k)) := by
    intro k' hk' k
    have hk'W : (k' : GLw a w × GLw b w) ∈ W := Subgroup.mem_subgroupOf.mp hk'
    have hl : (k' : GLw a w × GLw b w)⁻¹ ∈ K' := K'.inv_mem hk'W.1
    have hr : θ (k' : GLw a w × GLw b w) ∈ K' := hk'W.2
    have e : (((x * (k * k') : K2 a b w) : GLw a w × GLw b w)⁻¹ * y * θ ((x : GLw a w × GLw b w) * (k * k' : K2 a b w))) =
        (k' : GLw a w × GLw b w)⁻¹ * ((((x * k : K2 a b w) : GLw a w × GLw b w)⁻¹ * y *
          θ ((x : GLw a w × GLw b w) * k)) * θ (k' : GLw a w × GLw b w)) := by
      simp only [Subgroup.coe_mul, map_mul, _root_.mul_inv_rev, mul_assoc]
    show f _ = f _
    rw [e, (hf.2 _ hl _).1, (hf.2 _ hr _).2]
  exact (Subgroup.finiteIndex_of_le hle).index_ne_zero

theorem locSupp : PositivityTheory.Rg.BcB.G8.Fin.LocSupp := by
  intro E _ _ _ hU a b w y h₁ h₂
  exact ⟨fun C hC => finite_doubleCosets hU a b w y h₁ h₂ C hC,
    fun K' f ho _ hf x => rStab_index_ne_zero hU a b w y K' f ho hf x⟩

end GlobalTheory.CompanionTheory.TwistOrbit

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalSupportFactsStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_support_facts : PositivityTheory.Rg.BcB.G8.Fin.LocSupp := by
  first | exact @GlobalTheory.CompanionTheory.TwistOrbit.locSupp | exact GlobalTheory.CompanionTheory.TwistOrbit.locSupp | (intros; apply GlobalTheory.CompanionTheory.TwistOrbit.locSupp <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsUnderOfSameOrbit
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsUnderOfSameOrbit
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit)

namespace GlobalTheory.CompanionTheory.MixZ.Orbit

theorem isUnder_of_sameOrbit : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (w : GlobalTheory.CxPts (mpStr ℤ m n) σ₀) (z z' : (Σ k, Bk n k) → ℂ),
    IsUnder w z → SameOrbit z' z → IsUnder w z' := by
  rintro m n w z z' h ⟨c, hc, rfl⟩ k i
  refine ⟨(h k i).1.trans ?_, fun j hy => ((h k i).2 j hy).trans ?_⟩
  · show z ⟨k, i⟩ ≠ 0 ↔ c k * z ⟨k, i⟩ ≠ 0
    simp [hc k]
  · exact (mul_div_mul_left _ _ (hc k)).symm

end GlobalTheory.CompanionTheory.MixZ.Orbit
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsUnderOfSameOrbitStatement
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isUnder_of_same_orbit : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (w : GlobalTheory.CxPts (mpStr ℤ m n) σ₀) (z z' : (Σ k, Bk n k) → ℂ),
    IsUnder w z → SameOrbit z' z → IsUnder w z' := by
  first | exact @GlobalTheory.CompanionTheory.MixZ.Orbit.isUnder_of_sameOrbit | exact GlobalTheory.CompanionTheory.MixZ.Orbit.isUnder_of_sameOrbit | (intros; apply GlobalTheory.CompanionTheory.MixZ.Orbit.isUnder_of_sameOrbit <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedFiniteIntegral
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedFiniteIntegral
namespace GlobalTheory.CompanionTheory.Gunr

open NumberField IsDedekindDomain Filter

theorem finInt : PositivityTheory.SiegelWeilFormula.Gunr.FinInt := by
  intro F _ _ X
  have hone : ∀ x : F, ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite,
      algebraMap F (v.adicCompletion F) x ∈ v.adicCompletionIntegers F := by
    intro x
    have hfin : {v : HeightOneSpectrum (𝓞 F) | 1 < v.valuation F x}.Finite :=
      HeightOneSpectrum.Support.finite (𝓞 F) x
    have hev : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, ¬ 1 < v.valuation F x := by
      rw [eventually_cofinite]
      simpa using hfin
    refine hev.mono fun v hv => ?_
    have e : Valued.v (algebraMap F (v.adicCompletion F) x) = v.valuation F x :=
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, e]
    exact not_lt.mp hv
  have hall : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite,
      ∀ x ∈ X, algebraMap F (v.adicCompletion F) x ∈ v.adicCompletionIntegers F :=
    (Filter.eventually_all_finset X).2 fun x _ => hone x
  exact hall

end GlobalTheory.CompanionTheory.Gunr
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedFiniteIntegralStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_finite_integral : PositivityTheory.SiegelWeilFormula.Gunr.FinInt := by
  first | exact @GlobalTheory.CompanionTheory.Gunr.finInt | exact GlobalTheory.CompanionTheory.Gunr.finInt | (intros; apply GlobalTheory.CompanionTheory.Gunr.finInt <;> assumption)
end
end
