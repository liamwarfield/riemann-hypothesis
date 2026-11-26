module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaKernelLeftInvariantRationalUnitary
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationDataNsmulRescaleKeepsLaws
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomTriangleExistsNonzero

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLabelsSurjectiveHomLatticeModLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLabelsSurjectiveHomLatticeModLevel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.GSep.Labels

theorem comp_pow_overScheme_grpObj {S : Scheme.{0}} {A T T' : Over S} [GrpObj A] (ρ : T' ⟶ T) (x : T ⟶ A) (n : ℕ) :
    ρ ≫ x ^ n = (ρ ≫ x) ^ n := by
  induction n with
  | zero => simp only [pow_zero, MonObj.comp_one]
  | succ n ih => rw [pow_succ, MonObj.comp_mul, ih, pow_succ]


open GlobalTheory.TorusExt in
attribute [local instance] gtGroup in
theorem yy_hom : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ), (∀ a, ∃ mu, 𝔪.YY a mu) ∧ (∀ mu, ∃ a, 𝔪.YY a mu) ∧ (∀ a mu mu', 𝔪.YY a mu → (𝔪.YY a mu' ↔ CongMod (X₁.S.r * X₁.S.N) mu' mu)) ∧ (∀ a a' mu mu', 𝔪.YY a mu → 𝔪.YY a' mu' → 𝔪.YY (a + a') (mu + mu')) := by
  intro I X₁ z₁ act V _ _ _ ev X _ t δ 𝔪
  haveI : CharZero V := 𝔪.cn.2.2.2
  have hL : GlobalTheory.UT.LL := GlobalTheory.firstFiveLaws
  have hA : AdmBase V (maximalIdeal V) := ⟨𝔪.cn.1, inferInstance, 𝔪.cn.2.1, 𝔪.cn.2.2.1⟩
  have hB := 𝔪.D.tau_bimult
  have hk : 1 ≤ X₁.S.r * X₁.S.N := by
    have := X₁.S.r_pos; have := X₁.S.N_ge
    exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  obtain ⟨x, hx, xadd, -, xonto⟩ := GlobalTheory.ThetaDvr.torsion_points 𝔪.yK 𝔪.cart
  obtain ⟨rig, e, -, he, -⟩ := GlobalTheory.ThetaDvr.frames 𝔪.yK 𝔪.cart ⟨𝔪.wl, 𝔪.wl_gen⟩ x hx
  obtain ⟨f, f₁, f₂, f₃, f₄, -⟩ := GlobalTheory.TorsionIso.torsion_eq hL V (maximalIdeal V) hA 𝔪.D 𝔪.A 𝔪.G 𝔪.semi 𝔪.U
    (AlgebraicClosure (FractionRing V)) (X₁.S.r * X₁.S.N) hk
  have tor : ∀ p y, QkToAkU 𝔪.U.toUnifPre (AlgebraicClosure (FractionRing V)) (X₁.S.r * X₁.S.N) p y →
      y ^ (X₁.S.r * X₁.S.N) = 1 := fun p y h => by
    obtain ⟨w, hw⟩ := 𝔪.U.ext
    exact (h w hw).1
  have uniq : ∀ a (y : TFK (R := V) (AlgebraicClosure (FractionRing V)) ⟶ 𝔪.A.A), y ^ (X₁.S.r * X₁.S.N) = 1 →
      y.left ≫ 𝔪.φ = spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp 𝔪.yK) ≫
        (X₁.ρ.pt a).left → y = x a := by
    intro a y hy hya
    obtain ⟨b, rfl⟩ := xonto y hy
    obtain ⟨c, -, hc⟩ := X₁.ρ.pt_bij (AlgebraicClosure (FractionRing V))
      (spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp 𝔪.yK))
      ((Over.homMk (spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp 𝔪.yK)) (by simp) :
        Over.mk (spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp 𝔪.yK)) ⟶
          baseOver (Sp X₁.S.R)) ≫ X₁.ρ.pt a)
      (by rw [← comp_pow_overScheme_grpObj, (X₁.ρ.fr_tors a).1, MonObj.comp_one])
    have h1 := hc a rfl
    have h2 := hc b (by
      ext1
      simp only [Over.comp_left, Over.homMk_left]
      rw [← hx b, hya])
    rw [h1.trans h2.symm]
  have ex : ∀ a, ∃ p, QkToAkU 𝔪.U.toUnifPre (AlgebraicClosure (FractionRing V)) (X₁.S.r * X₁.S.N) p (x a) :=
    fun a => by
      obtain ⟨p, hp⟩ := f₂ (x a) (he a).1
      exact ⟨p, (f₁ _ _).2 hp.symm⟩
  have yyI : ∀ a mu, 𝔪.YY a mu ↔ ∃ p : QkPt 𝔪.D.toPre (AlgebraicClosure (FractionRing V)) (X₁.S.r * X₁.S.N),
      p.y = 𝔪.e₈ mu ∧ QkToAkU 𝔪.U.toUnifPre (AlgebraicClosure (FractionRing V)) (X₁.S.r * X₁.S.N) p (x a) := by
    intro a mu
    constructor
    · rintro ⟨p, y, hpy, hq, hov⟩
      obtain rfl := uniq a y (tor p y hq) hov
      exact ⟨p, hpy, hq⟩
    · rintro ⟨p, hpy, hq⟩
      exact ⟨p, x a, hpy, hq, hx a⟩
  refine ⟨fun a => ?_, fun mu => ?_, fun a mu mu' h => ?_, fun a a' mu mu' h h' => ?_⟩
  · obtain ⟨p, hp⟩ := ex a
    exact ⟨𝔪.e₈.symm p.y, (yyI a _).2 ⟨p, by simp, hp⟩⟩
  · obtain ⟨p, hp⟩ := exists_qkPt (F := AlgebraicClosure (FractionRing V)) hL.1.mulN (Or.inr hL.1.polBaseChange) hB
      (n := X₁.S.r * X₁.S.N) (by omega) (𝔪.e₈ mu)
    obtain ⟨a, ha⟩ := xonto (f p) (tor p _ ((f₁ _ _).2 rfl))
    exact ⟨a, (yyI a mu).2 ⟨p, hp, (f₁ _ _).2 ha.symm⟩⟩
  · obtain ⟨p, hpy, hq⟩ := (yyI a mu).1 h
    rw [yyI]
    constructor
    · rintro ⟨p', hpy', hq'⟩
      have hpp : QkPt.Equiv _ _ p p' := (f₃ p p').1 (((f₁ _ _).1 hq).symm.trans ((f₁ _ _).1 hq'))
      obtain ⟨z, hz, -⟩ := (GlobalTheory.TorusExt.equiv_iff hB p p').1 hpp
      have e' : mu' = mu + (X₁.S.r * X₁.S.N) • 𝔪.e₈.symm z := 𝔪.e₈.injective (by
        rw [map_add (f := _), map_nsmul, AddEquiv.apply_symm_apply, ← hpy, ← hpy', hz])
      exact ⟨𝔪.e₈.symm z, e'⟩
    · intro hc
      obtain ⟨w, hw⟩ := hc
      refine ⟨qkShift hB p (𝔪.e₈ w), ?_, (f₁ _ _).2 (((f₁ _ _).1 hq).trans ((f₃ _ _).2 (equiv_qkShift hB p _)))⟩
      show p.y + (X₁.S.r * X₁.S.N) • 𝔪.e₈ w = 𝔪.e₈ mu'
      rw [hpy, ← map_nsmul, ← map_add (f := _)]
      rw [hw]
  · obtain ⟨p, hpy, hq⟩ := (yyI a mu).1 h
    obtain ⟨p', hpy', hq'⟩ := (yyI a' mu').1 h'
    refine (yyI _ _).2 ⟨qkAdd hB p p', ?_, ?_⟩
    · show p.y + p'.y = 𝔪.e₈ (mu + mu')
      rw [map_add (f := _), hpy, hpy']
    · rw [f₁, f₄ _ _ _ (qkAdd_qkAdd hB p p'), ← (f₁ _ _).1 hq, ← (f₁ _ _).1 hq', xadd]

end GlobalTheory.GSep.Labels
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLabelsSurjectiveHomLatticeModLevelStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLabels_surjective_hom_lattice_mod_level : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ), (∀ a, ∃ mu, 𝔪.YY a mu) ∧ (∀ mu, ∃ a, 𝔪.YY a mu) ∧ (∀ a mu mu', 𝔪.YY a mu → (𝔪.YY a mu' ↔ CongMod (X₁.S.r * X₁.S.N) mu' mu)) ∧ (∀ a a' mu mu', 𝔪.YY a mu → 𝔪.YY a' mu' → 𝔪.YY (a + a') (mu + mu')) := by
  first | exact @GlobalTheory.GSep.Labels.yy_hom | exact GlobalTheory.GSep.Labels.yy_hom | (intros; apply GlobalTheory.GSep.Labels.yy_hom <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchingTripleSignature
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneParamSubgroupFockOrbitFiniteDimensional
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneParamSubgroupFockOrbitFiniteDimensional
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexOrder Matrix

namespace GlobalTheory.OneParamOrbit

theorem eps_true_of_posDef {D : D7} {X : HSp D} (B : GlobalTheory.ChainFr.Fr X) (τ : D.what₂.Tau)
    (hG : (gramAt D X τ).PosDef) (i : Fin X.rank) : B.ε τ i = true := by
  have hu : IsUnit (B.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).mp (B.fr_unit τ)
  have hinj : Function.Injective ((B.fr τ)⁻¹).mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr ((Matrix.isUnit_nonsing_inv_iff).mpr (B.fr_unit τ))
  have hJ : ((B.fr τ)⁻¹)ᴴ * gramAt D X τ * (B.fr τ)⁻¹ = Formalism.REAL.Jm (B.ε τ) := by
    rw [← B.fr_gram τ]
    have h1 : ((B.fr τ)⁻¹)ᴴ * (B.fr τ)ᴴ = 1 := by
      rw [← Matrix.conjTranspose_mul, Matrix.mul_nonsing_inv _ hu, Matrix.conjTranspose_one]
    calc ((B.fr τ)⁻¹)ᴴ * ((B.fr τ)ᴴ * Formalism.REAL.Jm (B.ε τ) * B.fr τ) * (B.fr τ)⁻¹
        = (((B.fr τ)⁻¹)ᴴ * (B.fr τ)ᴴ) * Formalism.REAL.Jm (B.ε τ) * (B.fr τ * (B.fr τ)⁻¹) := by
          simp only [Matrix.mul_assoc]
      _ = Formalism.REAL.Jm (B.ε τ) := by rw [h1, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul, Matrix.mul_one]
  have hpos := (hG.conjTranspose_mul_mul_same hinj).diag_pos (i := i)
  rw [hJ] at hpos
  by_contra hne
  simp only [Formalism.REAL.Jm, Matrix.diagonal_apply_eq, hne] at hpos
  norm_num at hpos

theorem conj_mem_Kset {D : D7} {X : HSp D} (B : GlobalTheory.ChainFr.Fr X) (τ : D.what₂.Tau)
    (hG : (gramAt D X τ).PosDef) {E : Matrix (Fin X.rank) (Fin X.rank) ℂ}
    (hE : Eᴴ * gramAt D X τ * E = gramAt D X τ) :
    B.fr τ * E * (B.fr τ)⁻¹ ∈ Formalism.REAL.Kset (B.ε τ) := by
  have hu : IsUnit (B.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).mp (B.fr_unit τ)
  have hJ1 : Formalism.REAL.Jm (B.ε τ) = 1 := by
    have : B.ε τ = fun _ => true := funext (eps_true_of_posDef B τ hG)
    rw [this]; simp [Formalism.REAL.Jm]
  have hgram : (B.fr τ)ᴴ * B.fr τ = gramAt D X τ := by
    rw [← B.fr_gram τ, hJ1, Matrix.mul_one]
  refine ⟨?_, by rw [hJ1, Matrix.mul_one, Matrix.one_mul]⟩
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  have h1 : ((B.fr τ)⁻¹)ᴴ * (B.fr τ)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, Matrix.mul_nonsing_inv _ hu, Matrix.conjTranspose_one]
  calc (B.fr τ * E * (B.fr τ)⁻¹)ᴴ * (B.fr τ * E * (B.fr τ)⁻¹)
      = ((B.fr τ)⁻¹)ᴴ * (Eᴴ * ((B.fr τ)ᴴ * B.fr τ) * E) * (B.fr τ)⁻¹ := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = ((B.fr τ)⁻¹)ᴴ * (B.fr τ)ᴴ * (B.fr τ * (B.fr τ)⁻¹) := by
        rw [hgram, hE, ← hgram]; simp only [Matrix.mul_assoc]
    _ = 1 := by rw [h1, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul]

theorem orbit_finiteDimensional : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
    ∀ (M X : HSp D) (A : GlobalTheory.ChainFr.Fr M) (B : GlobalTheory.ChainFr.Fr X) (χ χ' : (AE D)ˣ →* Circle) (ω : GlobalTheory.Grid.WRep M X),
    GlobalTheory.Grid.IsWeil ψ false M X χ χ' ω → (∀ τ, ∃ a b : ℚ, HasInfExp D χ τ a ∧ HasInfExp D χ' τ b) →
    (∀ τ, Formalism.UG.HasSignature (gramAt D X τ) X.rank 0) →
    ∀ τ, ∀ Y ∈ lieAt X τ, ∀ Φ ∈ algF ψ θ false A B,
      ∃ V : Submodule ℂ (WO M X → ℂ), FiniteDimensional ℂ V ∧ ∀ t : ℝ, ω (1, oneP θ X τ Y t) Φ ∈ V := by
  intro D ψ θ _hψ hθ M X A B χ χ' ω hω hexp hsig τ Y hY Φ hΦ
  have hG : (gramAt D X τ).PosDef := GlobalTheory.IndefiniteRowSideFullHecke.MassFormulaPositivity.posDef_of_hasSignature (hsig τ)
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, P, hf, rfl⟩ := hx
    by_cases hf0 : f = 0
    · subst hf0
      have h0 : fockF ψ θ false A B 0 P = 0 := by
        have := GlobalTheory.FiniteFock.pureTensorO_smul ψ θ (GlobalTheory.Grid.sgn false M) X (frSgn false A).cart B.cart
          A.onb B.onb 0 0 P
        rwa [zero_smul, zero_smul] at this
      refine ⟨⊥, inferInstance, fun t => ?_⟩
      rw [h0, map_zero]; exact zero_mem _
    · obtain ⟨a, b, ha, hb⟩ := hexp τ
      obtain ⟨x, y, -, -, hK⟩ := GlobalTheory.CompactFockAction.compactFockAll D (GlobalTheory.Grid.sgn false M) X
        (frSgn false A) B θ ψ χ χ' (ω.toSgn false) f τ a b hθ hω ha hb hf hf0
      refine ⟨(MvPolynomial.restrictTotalDegree _ ℂ P.totalDegree).map (fockF ψ θ false A B f),
        inferInstance, fun t => ?_⟩
      have hu : IsUnit (B.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).mp (B.fr_unit τ)
      have hE : (NormedSpace.exp (t • Y))ᴴ * gramAt D X τ * NormedSpace.exp (t • Y) = gramAt D X τ :=
        GlobalTheory.SmoothAutCheck.exp_mem_UH (Matrix.isUnit_iff_isUnit_det _ |>.mp hG.isUnit) hY t
      have hk := conj_mem_Kset B τ hG hE
      have hA1 : (frSgn false A).elt θ τ 1 = 1 := by
        have hAu : IsUnit (A.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).mp (A.fr_unit τ)
        show atTau θ _ τ ((A.fr τ)⁻¹ * 1 * A.fr τ) = 1
        rw [Matrix.mul_one, Matrix.nonsing_inv_mul _ hAu]
        exact GlobalTheory.PointAtPlaceHom.atTau_one hθ _ τ
      have hBk : B.elt θ τ (B.fr τ * NormedSpace.exp (t • Y) * (B.fr τ)⁻¹) = oneP θ X τ Y t := by
        show atTau θ X τ ((B.fr τ)⁻¹ * (B.fr τ * NormedSpace.exp (t • Y) * (B.fr τ)⁻¹) * B.fr τ) = _
        rw [show (B.fr τ)⁻¹ * (B.fr τ * NormedSpace.exp (t • Y) * (B.fr τ)⁻¹) * B.fr τ
            = ((B.fr τ)⁻¹ * B.fr τ) * NormedSpace.exp (t • Y) * ((B.fr τ)⁻¹ * B.fr τ) by
              simp only [Matrix.mul_assoc],
          Matrix.nonsing_inv_mul _ hu, Matrix.one_mul, Matrix.mul_one]
        rfl
      have hω1 : ω (1, oneP θ X τ Y t)
          = (ω.toSgn false) ((frSgn false A).elt θ τ 1, B.elt θ τ (B.fr τ * NormedSpace.exp (t • Y) * (B.fr τ)⁻¹)) := by
        rw [hA1, hBk]
        show ω (1, _) = ω ((GlobalTheory.Grid.ofSgn false M) 1, _)
        rw [map_one]
      have key := hK 1 (GlobalTheory.Chain.RealIt.one_mem_Kset _) _ hk P
      have hfock : fockF ψ θ false A B f P = GlobalTheory.ChainFr.ptF ψ θ (frSgn false A) B f P := rfl
      rw [hfock, hω1, key]
      refine Submodule.smul_mem _ _ ⟨_, (MvPolynomial.mem_restrictTotalDegree _ _ _).2
        (GlobalTheory.Chain.RealIt.SubstDeg.totalDegree_subst_le _ _ _ _ _ _ _ _ _), rfl⟩
  | zero => exact ⟨⊥, inferInstance, fun t => by rw [map_zero]; exact zero_mem _⟩
  | add x y _ _ hx hy =>
    obtain ⟨V₁, h₁, hV₁⟩ := hx
    obtain ⟨V₂, h₂, hV₂⟩ := hy
    exact ⟨V₁ ⊔ V₂, Submodule.finiteDimensional_sup V₁ V₂, fun t => by
      rw [map_add]; exact add_mem (Submodule.mem_sup_left (hV₁ t)) (Submodule.mem_sup_right (hV₂ t))⟩
  | smul c x _ hx =>
    obtain ⟨V, h, hV⟩ := hx
    exact ⟨V, h, fun t => by rw [map_smul]; exact Submodule.smul_mem _ _ (hV t)⟩

end GlobalTheory.OneParamOrbit
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneParamSubgroupFockOrbitFiniteDimensionalStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.oneParamSubgroup_fockOrbit_finiteDimensional : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
    ∀ (M X : HSp D) (A : GlobalTheory.ChainFr.Fr M) (B : GlobalTheory.ChainFr.Fr X) (χ χ' : (AE D)ˣ →* Circle) (ω : GlobalTheory.Grid.WRep M X),
    GlobalTheory.Grid.IsWeil ψ false M X χ χ' ω → (∀ τ, ∃ a b : ℚ, HasInfExp D χ τ a ∧ HasInfExp D χ' τ b) →
    (∀ τ, Formalism.UG.HasSignature (gramAt D X τ) X.rank 0) →
    ∀ τ, ∀ Y ∈ lieAt X τ, ∀ Φ ∈ algF ψ θ false A B,
      ∃ V : Submodule ℂ (WO M X → ℂ), FiniteDimensional ℂ V ∧ ∀ t : ℝ, ω (1, oneP θ X τ Y t) Φ ∈ V := by
  first | exact @GlobalTheory.OneParamOrbit.orbit_finiteDimensional | exact GlobalTheory.OneParamOrbit.orbit_finiteDimensional | (intros; apply GlobalTheory.OneParamOrbit.orbit_finiteDimensional <;> assumption)
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.DefIrred

theorem integrable_algF {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ)
    {M X : HSp D} (A : GlobalTheory.ChainFr.Fr M) (B : GlobalTheory.ChainFr.Fr X) {χ χ' : (AE D)ˣ →* Circle} {ω : GlobalTheory.Grid.WRep M X}
    (hω : GlobalTheory.Grid.IsWeil ψ false M X χ χ' ω) (hs : ∀ τ, Formalism.UG.HasSignature (gramAt D M τ) M.rank 0)
    {ν : Measure (GA D M)} {𝓕 : Set (GA D M)} (hν : IsHaarFD M ν 𝓕) :
    ∀ Φ ∈ algF ψ θ false A B, ∀ h, IntegrableOn (fun g => thetaKO ω g h Φ) 𝓕 ν := by
  intro Φ hΦ
  have hth : IsThetaFunO ψ (GlobalTheory.Grid.sgn false M) X Φ := by
    induction hΦ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨f, P, hf, rfl⟩ := hx
      exact GlobalTheory.Chain.InnerSteps.theta_pureTensorO hψ hθ _ _ _ _ hf.1 P
    | zero => exact GlobalTheory.OrientedHeis.theta_zero
    | add x y _ _ hx hy => exact GlobalTheory.OrientedHeis.theta_add hx hy
    | smul c x _ hx => exact GlobalTheory.OrientedHeis.theta_smul c hx
  exact (GlobalTheory.T.thetaIntegral_definiteSource_converges_continuous_invariant D ψ false M X χ χ' ω ν 𝓕 Φ hω (fun τ => GlobalTheory.IndefiniteRowSideFullHecke.MassFormulaPositivity.posDef_of_hasSignature (hs τ)) hν.1 hν.2
    hth).1

end GlobalTheory.DefIrred

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBottomTriplePeriodConst
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BotFormula

theorem conj_finsum {α : Type*} (f : α → ℂ) : starRingEnd ℂ (∑ᶠ a, f a) = ∑ᶠ a, starRingEnd ℂ (f a) := by
  by_cases hs : (Function.support f).Finite
  · exact map_finsum (starRingEnd ℂ) hs
  · have hs' : ¬ (Function.support fun a => starRingEnd ℂ (f a)).Finite := by
      have : (Function.support fun a => starRingEnd ℂ (f a)) = Function.support f := by ext a; simp
      rwa [this]
    rw [finsum_of_infinite_support hs, finsum_of_infinite_support hs', map_zero]

end GlobalTheory.BotFormula
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LbIsoOfPullbackQuasiInverseIsogenyTrivialAxes
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.QuasiInvPull


open GlobalTheory.CechPic in
theorem lbIso_of_pullback_quasiInverseIsogeny_trivial_axes : ∀ (Y : Scheme.{0}) (A B : Over Y) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B]
    (k : ℕ) (ψ : A ⟶ B) (ψ' : B ⟶ A) (Q₁ Q₂ : LB (G2 B).left), IsAbelianScheme B → 0 < k →
    IsUnit (k : Γ(Y, ⊤)) → IsQuasiInv k ψ ψ' → IsAxesTriv B Q₁ → IsAxesTriv B Q₂ →
    LBIso (Q₁.pull (Hecke.sq2 ψ)) (Q₂.pull (Hecke.sq2 ψ)) → LBIso Q₁ Q₂ := by
  intro Y A B _ _ _ _ k ψ ψ' Q₁ Q₂ hB hk _ hq h₁ h₂ hiso
  obtain ⟨hψ, hψ', -, hc⟩ := hq
  haveI := hψ
  haveI := hψ'
  have o₁ : (1 : B ⟶ B) ≫ (𝟙 B) ^ k = 1 := by
    rw [← hc, ← Category.assoc, GlobalTheory.BirigUniq.one_comp_monHom, GlobalTheory.BirigUniq.one_comp_monHom]
  obtain ⟨hL₁, r₁₁, r₁₂⟩ := h₁
  obtain ⟨hL₂, r₂₁, r₂₂⟩ := h₂
  obtain ⟨hfl, hsu, hqc⟩ := GlobalTheory.UPel.HT.SiegUniqBase.flat_surjective_qc_pow Y B hB k hk
  have pull_comp_left {S : Scheme.{0}} {U V W : Over S} (g : U ⟶ V) (f : V ⟶ W) (c : Pic W.left) :
      pull (g ≫ f).left c = pull g.left (pull f.left c) := by
    rw [Over.comp_left, pull_comp]
  have pic_eq_zero_of_fpqc {S : Scheme.{0}} (X Y Y' : Over S) [GrpObj X] (hX : IsAbelianScheme X)
      (c : Y' ⟶ Y) (hfl : Flat c.left) (hsu : Surjective c.left) (hqc : QuasiCompact c.left)
      (d : Pic (X ⊗ Y).left)
      (h0 : pull (lift (1 : Y ⟶ X) (𝟙 Y)).left d = 0)
      (h1 : pull (lift (fst X Y') (snd X Y' ≫ c)).left d = 0) : d = 0 := by
    obtain ⟨D, hD, rfl⟩ := cls_surj d
    have t := GlobalTheory.RigDesc.triv_of_triv_zero_of_fpqc S X Y Y' hX c hfl hsu hqc D hD
      ((cls_eq_zero_iff (pull_isLB hD _)).1 h0) ((cls_eq_zero_iff (pull_isLB hD _)).1 h1)
    exact (cls_eq_zero_iff hD).2 t
  let d := cls Q₁ hL₁ - cls Q₂ hL₂
  have z₁₁ : pull (lift (1 : B ⟶ B) (𝟙 B)).left (cls Q₁ hL₁) = 0 := (cls_eq_zero_iff (pull_isLB hL₁ _)).2 r₁₁
  have z₁₂ : pull (lift (𝟙 B) (1 : B ⟶ B)).left (cls Q₁ hL₁) = 0 := (cls_eq_zero_iff (pull_isLB hL₁ _)).2 r₁₂
  have z₂₁ : pull (lift (1 : B ⟶ B) (𝟙 B)).left (cls Q₂ hL₂) = 0 := (cls_eq_zero_iff (pull_isLB hL₂ _)).2 r₂₁
  have z₂₂ : pull (lift (𝟙 B) (1 : B ⟶ B)).left (cls Q₂ hL₂) = 0 := (cls_eq_zero_iff (pull_isLB hL₂ _)).2 r₂₂
  have d₁ : pull (lift (1 : B ⟶ B) (𝟙 B)).left d = 0 := by simp only [d, map_sub, z₁₁, z₂₁, sub_zero]
  have d₂ : pull (lift (𝟙 B) (1 : B ⟶ B)).left d = 0 := by simp only [d, map_sub, z₁₂, z₂₂, sub_zero]
  have dψ : pull (lift (fst A A ≫ ψ) (snd A A ≫ ψ)).left d = 0 := by
    have e : pull (Hecke.sq2 ψ) (cls Q₁ hL₁) = pull (Hecke.sq2 ψ) (cls Q₂ hL₂) :=
      (cls_eq_iff (pull_isLB hL₁ _) (pull_isLB hL₂ _)).2 hiso
    simp only [d, map_sub]
    exact sub_eq_zero.2 e

  have dk : pull (lift (fst B B ≫ (𝟙 B) ^ k) (snd B B ≫ (𝟙 B) ^ k)).left d = 0 := by
    have : lift (fst B B ≫ (𝟙 B) ^ k) (snd B B ≫ (𝟙 B) ^ k) =
        lift (fst B B ≫ ψ') (snd B B ≫ ψ') ≫ lift (fst A A ≫ ψ) (snd A A ≫ ψ) := by
      rw [← hc]; apply CartesianMonoidalCategory.hom_ext <;> simp
    rw [this, pull_comp_left, dψ, map_zero]

  have hD : pull (lift (fst B B ≫ (𝟙 B) ^ k) (snd B B)).left d = 0 := by
    refine pic_eq_zero_of_fpqc B B B hB ((𝟙 B) ^ k) hfl hsu hqc _ ?_ ?_
    · rw [← pull_comp_left]
      have : lift (1 : B ⟶ B) (𝟙 B) ≫ lift (fst B B ≫ (𝟙 B) ^ k) (snd B B) = lift (1 : B ⟶ B) (𝟙 B) := by
        apply CartesianMonoidalCategory.hom_ext <;> simp [o₁]
      rw [this, d₁]
    · rw [← pull_comp_left]
      have : lift (fst B B) (snd B B ≫ (𝟙 B) ^ k) ≫ lift (fst B B ≫ (𝟙 B) ^ k) (snd B B) =
          lift (fst B B ≫ (𝟙 B) ^ k) (snd B B ≫ (𝟙 B) ^ k) := by
        apply CartesianMonoidalCategory.hom_ext <;> simp
      rw [this, dk]

  have hQ : pull (lift (snd B B) (fst B B)).left d = 0 := by
    refine pic_eq_zero_of_fpqc B B B hB ((𝟙 B) ^ k) hfl hsu hqc _ ?_ ?_
    · rw [← pull_comp_left]
      have : lift (1 : B ⟶ B) (𝟙 B) ≫ lift (snd B B) (fst B B) = lift (𝟙 B) (1 : B ⟶ B) := by
        apply CartesianMonoidalCategory.hom_ext <;> simp
      rw [this, d₂]
    · rw [← pull_comp_left]
      have : lift (fst B B) (snd B B ≫ (𝟙 B) ^ k) ≫ lift (snd B B) (fst B B) =
          lift (snd B B) (fst B B) ≫ lift (fst B B ≫ (𝟙 B) ^ k) (snd B B) := by
        apply CartesianMonoidalCategory.hom_ext <;> simp
      rw [this, pull_comp_left, hD, map_zero]
  have hsw : lift (snd B B) (fst B B) ≫ lift (snd B B) (fst B B) = 𝟙 (B ⊗ B) := by
    apply CartesianMonoidalCategory.hom_ext <;> simp
  have hd : d = 0 := by
    have H : pull (lift (snd B B) (fst B B) ≫ lift (snd B B) (fst B B)).left d = d := by
      rw [hsw, Over.id_left, pull_id]
    rw [pull_comp_left, hQ, map_zero] at H
    exact H.symm
  exact (cls_eq_iff hL₁ hL₂).1 (sub_eq_zero.1 hd)

end GlobalTheory.QuasiInvPull
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvExp
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EpiPowOfIsAbelianScheme
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
open GlobalTheory.ZM GlobalTheory.SiegelTor

namespace GlobalTheory.UPel.HT.MulEpi

attribute [local instance] Over.cartesianMonoidalCategory

theorem epi_pow_of_isAbelianScheme (S : Scheme.{0}) (A : Over S) [GrpObj A] (hA : IsAbelianScheme A)
    (k : ℕ) (hk : 0 < k) : Epi ((𝟙 A) ^ k) := by
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.UPel.HT.SiegUniqBase.flat_surjective_qc_pow S A hA k hk
  haveI : Epi ((𝟙 A) ^ k).left := Flat.epi_of_flat_of_surjective _
  exact (Over.forget S).epi_of_epi_map this

end GlobalTheory.UPel.HT.MulEpi
end

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

namespace GlobalTheory.UPel.HT.ESDual

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ} {S : Scheme.{0}}

def scaleTate {k : Type} [Field k] {Q : Type} [Group Q] {act : D.O → Q → Q} {w : ℕ → Q → Q → kˣ → Prop}
    (I : TateIsoO D k Q act w) (e : ℕ) : TateIsoO D k Q act w where
  ζ n := I.ζ n ^ ((p ^ e) ^ 2)
  ζ_prim n hn hp := (I.ζ_prim n hn hp).pow_of_coprime _ ((hp.symm.pow_left e).pow_left 2)
  ζ_pow n m hn hm h := by rw [pow_right_comm, I.ζ_pow n m hn hm h]
  ev n x := I.ev n (p ^ e • x)
  add n x y := by rw [smul_add, I.add]
  lin n c x := by rw [smul_comm, I.lin]
  ker n hn hp x := by
    rw [I.ker n hn hp]
    constructor
    · rintro ⟨y, hy⟩
      obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.2 (hp.symm.pow_left e)
      refine ⟨u • y + v • x, ?_⟩
      rw [smul_add, smul_comm n u, ← hy, smul_comm n v, ← natCast_zsmul x, ← natCast_zsmul x, smul_smul, smul_smul,
        ← add_smul, huv, one_smul]
    · rintro ⟨y, rfl⟩
      exact ⟨p ^ e • y, smul_comm _ _ _⟩
  onto n hn hp q := by
    rw [I.onto n hn hp]
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.2 (hp.symm.pow_left e)
      refine ⟨u • x, ?_⟩
      have e1 : x = p ^ e • u • x + n • v • x := by
        rw [smul_comm _ u, smul_comm n v, ← natCast_zsmul x, ← natCast_zsmul x, smul_smul, smul_smul,
          ← add_smul, huv, one_smul]
      have e2 := (I.ker n hn hp (n • v • x)).2 ⟨_, rfl⟩
      conv_rhs => rw [e1, I.add, e2, _root_.mul_one]
    · rintro ⟨x, rfl⟩
      exact ⟨_, rfl⟩
  tower n m hn hm h x := I.tower n m hn hm h _
  isom n hn hp x y := by
    have h := I.isom n hn hp (p ^ e • x) (p ^ e • y)
    have e1 : (2 * D.EF (p ^ e • x) (p ^ e • y) : ℤ) = (((p ^ e) ^ 2 : ℕ) : ℤ) * (2 * D.EF x y) := by
      simp only [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul]
      push_cast
      ring
    rw [e1, zpow_mul, zpow_natCast] at h
    exact h

def scale {s : S ⟶ Sp R} (o : Obj b N s) (e : ℕ) {s' : S ⟶ Sp R} (h : s = s') : Obj b N s' where
  A := o.A
  ab := o.ab
  act := o.act
  P := o.P
  isLB := o.isLB
  rig₁ := o.rig₁
  rig₂ := o.rig₂
  symm := o.symm
  ample := o.ample
  kerP := o.kerP
  rosati := o.rosati
  lie := h ▸ o.lie
  lieRank := h ▸ o.lieRank
  eta x := o.eta (p ^ e • x)
  eta_add x y := by rw [smul_add, o.eta_add]
  eta_lin c x := by rw [smul_comm, o.eta_lin]
  eta_ker x := by rw [smul_comm, o.eta_ker]
  geom k _ _ x β hx := by
    obtain ⟨I, hI⟩ := o.geom k x β (h ▸ hx)
    exact ⟨scaleTate I e, fun y => hI _⟩

theorem eta_nsmul {s : S ⟶ Sp R} (o : Obj b N s) (n : ℕ) (x : D.La) : o.eta (n • x) = o.eta x ^ n := by
  induction n with
  | zero => rw [zero_smul, pow_zero, eta_zero]
  | succ n ih => rw [succ_nsmul, o.eta_add, ih, pow_succ]

theorem eta_congr {s : S ⟶ Sp R} (o : Obj b N s) {n : ℕ} (hn : n ≡ 1 [MOD N]) (hn0 : 0 < n) (x : D.La) :
    o.eta (n • x) = o.eta x := by
  obtain ⟨k, hk⟩ := (Nat.modEq_iff_dvd' hn0).1 hn.symm
  have : n = 1 + N * k := by omega
  rw [this, add_smul, one_smul, mul_smul, o.eta_add, o.eta_ker, _root_.mul_one]

theorem exists_inv_exp (hN : 0 < N) (hp : N.Coprime p) (e : ℕ) : ∃ f : ℕ, p ^ (e + f) ≡ 1 [MOD N] := by
  refine ⟨e * (N.totient - 1), ?_⟩
  have h1 : 1 ≤ N.totient := Nat.totient_pos.2 hN
  have : e + e * (N.totient - 1) = N.totient * e := by
    obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le h1
    rw [hm]; simp; ring
  rw [this, pow_mul]
  simpa using (Nat.ModEq.pow_totient hp.symm).pow e

def idMap {s : S ⟶ Sp R} (o : Obj b N s) : ObjMap o o (𝟙 S) where
  φ := 𝟙 _
  φ₂ := 𝟙 _
  cart := GlobalTheory.SiegLower.isGrpPullback_id o.A
  sq := ⟨by simp, by simp⟩
  act c := by simp
  pol := GlobalTheory.SiegLower.lbIso_pull_id o.isLB
  eta y := by simp

def compMap {S₁ S₂ S₃ : Scheme.{0}} {s₁ : S₁ ⟶ Sp R} {s₂ : S₂ ⟶ Sp R} {s₃ : S₃ ⟶ Sp R} {o₁ : Obj b N s₁}
    {o₂ : Obj b N s₂} {o₃ : Obj b N s₃} {f : S₁ ⟶ S₂} {g : S₂ ⟶ S₃} (h₁ : ObjMap o₁ o₂ f) (h₂ : ObjMap o₂ o₃ g) :
    ObjMap o₁ o₃ (f ≫ g) where
  φ := h₁.φ ≫ h₂.φ
  φ₂ := h₁.φ₂ ≫ h₂.φ₂
  cart := h₁.cart.comp h₂.cart
  sq := by
    constructor
    · rw [Category.assoc, h₂.sq.1, ← Category.assoc, h₁.sq.1, Category.assoc]
    · rw [Category.assoc, h₂.sq.2, ← Category.assoc, h₁.sq.2, Category.assoc]
  act c := by rw [← Category.assoc, h₁.act, Category.assoc, h₂.act, Category.assoc]
  pol := by
    have H : LBIso (o₂.P.pull h₁.φ₂) ((o₃.P.pull h₂.φ₂).pull h₁.φ₂) :=
      LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull o₂.P h₁.φ₂ h₁.φ₂ rfl) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull (o₃.P.pull h₂.φ₂) h₁.φ₂ h₁.φ₂ rfl) h₂.pol
    have H' : LBIso (o₂.P.pull h₁.φ₂) (o₃.P.pull (h₁.φ₂ ≫ h₂.φ₂)) :=
      LBIso.chartPull (chartPullId _) (chartPullIn o₃.P (fun _ : PUnit => h₂.φ₂) (fun _ => 1) h₁.φ₂) H
    exact LBIso.trans o₁.isLB (pull_isLB o₂.isLB _) (pull_isLB o₃.isLB _) h₁.pol H'
  eta y := by rw [← Category.assoc, h₁.eta, Category.assoc, h₂.eta, Category.assoc]

theorem pow_left_comm {S' : Scheme.{0}} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {f : S' ⟶ S}
    {φ : A'.left ⟶ A.left} (h : IsGrpPullback A' A f φ) (c : ℕ) :
    ((𝟙 A') ^ c).left ≫ φ = φ ≫ ((𝟙 A) ^ c).left := by
  let u : Over.mk (A'.hom ≫ f) ⟶ A := Over.homMk φ h.1.w
  have key : ∀ n : ℕ, (u ^ n).left = ((𝟙 A') ^ n).left ≫ φ := by
    intro n
    induction n with
    | zero =>
      let v : Over.mk (A'.hom ≫ f) ⟶ A := Over.homMk ((1 : A' ⟶ A').left ≫ φ) (by
        rw [Category.assoc, h.1.w, Over.w_assoc]; rfl)
      have h1 := h.2 A' 1 1 v v rfl rfl
      rw [_root_.mul_one] at h1
      have h2 : v = 1 := mul_eq_left.1 (Over.OverMorphism.ext h1 : v * v = v)
      rw [pow_zero, pow_zero, ← h2]; rfl
    | succ n ih =>
      rw [pow_succ, pow_succ]
      exact h.2 A' _ _ _ _ ih (Category.id_comp _).symm
  rw [← key]
  have : u ^ c = u ≫ (𝟙 A) ^ c := by rw [MonObj.comp_pow, Category.comp_id]
  rw [this]; rfl

theorem square_dual {S' : Scheme.{0}} {A B : Over S} {A' B' : Over S'} [GrpObj A] [GrpObj A'] [GrpObj B'] {f : S' ⟶ S}
    {φ : A'.left ⟶ A.left} (h : IsGrpPullback A' A f φ) (hB : IsAbelianScheme B') (φ' : B'.left ⟶ B.left) {c : ℕ}
    (hc : 0 < c) {ψ : A ⟶ B} {χ : B ⟶ A} {ψ' : A' ⟶ B'} {χ' : B' ⟶ A'} (h₁ : ψ ≫ χ = (𝟙 A) ^ c)
    (h₂ : ψ' ≫ χ' = (𝟙 A') ^ c) (h₃ : χ' ≫ ψ' = (𝟙 B') ^ c) (sq : φ ≫ ψ.left = ψ'.left ≫ φ') :
    φ' ≫ χ.left = χ'.left ≫ φ := by
  obtain ⟨hfl, hsu, hqc⟩ := GlobalTheory.UPel.HT.SiegUniqBase.flat_surjective_qc_pow S' B' hB c hc
  haveI : Epi ((𝟙 B') ^ c).left := Flat.epi_of_flat_of_surjective _
  haveI : Epi (χ'.left ≫ ψ'.left) := by rw [← Over.comp_left, h₃]; infer_instance
  haveI : Epi ψ'.left := epi_of_epi χ'.left ψ'.left
  rw [← cancel_epi ψ'.left, ← Category.assoc, ← sq, Category.assoc, ← Over.comp_left, h₁, ← pow_left_comm h,
    ← h₂, Over.comp_left, Category.assoc]


open GlobalTheory.BirigidPow GlobalTheory.CechPic in
theorem val_adj {s : S ⟶ Sp R} {c : ℕ} {o o' : Obj b N s} {ψ : o.A ⟶ o'.A} (hψ : IsPIsog c o o' ψ)
    {ψ' : o'.A ⟶ o.A} [IsMonHom ψ'] (h₂ : ψ' ≫ ψ = (𝟙 o'.A) ^ c) {T : Over S} (x : T ⟶ o'.A) (y : T ⟶ o.A) :
    BirigidPow.val o'.isLB x (y ≫ ψ) = BirigidPow.val o.isLB (x ≫ ψ') y := by
  have hc := hψ.pos
  obtain ⟨-, hm, -, -, ⟨hP⟩, -⟩ := hψ
  have nat : ∀ {A : Over S} [GrpObj A] [IsCommMonObj A] {P : LB (G2 A).left} (hP : P.IsLB) {U V : Over S} (r : U ⟶ V)
      (x y : V ⟶ A), pull r.left (BirigidPow.val hP x y) = BirigidPow.val hP (r ≫ x) (r ≫ y) := by
    intro A _ _ P hP U V r x y
    rw [BirigidPow.val, BirigidPow.val, ← pull_comp, ← Over.comp_left, comp_lift]
  have hsq : ∀ {U : Over S} (x y : U ⟶ o.A), BirigidPow.val o'.isLB (x ≫ ψ) (y ≫ ψ) = c • BirigidPow.val o.isLB x y := by
    intro U x y
    have hL : (Hecke.lbPow o.P c).IsLB := LB.isLB_linComb o.isLB _ _
    have e := (cls_eq_iff hL (pull_isLB o'.isLB _)).2 hP
    rw [BirigidPow.cls_lbPow o.isLB, cls_pull o'.isLB _ (pull_isLB o'.isLB _)] at e
    have e' := congrArg (pull (lift x y).left) e
    rw [map_nsmul] at e'
    refine Eq.trans ?_ e'.symm
    have := nat o'.isLB (lift x y) (fst o.A o.A ≫ ψ) (snd o.A o.A ≫ ψ)
    rw [lift_fst_assoc, lift_snd_assoc] at this
    exact this.symm
  obtain ⟨hfl, hsu, hqc⟩ := GlobalTheory.UPel.HT.SiegUniqBase.flat_surjective_qc_pow S o'.A o'.ab c hc
  have H : BirigidPow.val o'.isLB (snd o.A o'.A) (fst o.A o'.A ≫ ψ) - BirigidPow.val o.isLB (snd o.A o'.A ≫ ψ') (fst o.A o'.A) = 0 := by
    refine GlobalTheory.BirigUniq.pic_eq_zero_of_fpqc o.A o'.A o'.A o.ab ((𝟙 o'.A) ^ c) hfl hsu hqc _ ?_ ?_
    · rw [map_sub, nat, nat, lift_fst_assoc, lift_fst, MonObj.one_comp, val_one_right _ o'.rig₂,
        val_one_right _ o.rig₂, sub_zero]
    · rw [map_sub, nat, nat, lift_fst_assoc, lift_fst, lift_snd, lift_snd_assoc, sub_eq_zero]
      conv_lhs => rw [← h₂, ← Category.assoc, hsq]
      rw [← val_pow_left o.isLB o.ab o.ample o.rig₁ o.rig₂, MonObj.comp_pow, Category.comp_id, MonObj.pow_comp]
  have := congrArg (pull (lift y x).left) H
  rw [map_sub, nat, nat, lift_fst_assoc, lift_fst, lift_snd, lift_snd_assoc, map_zero, sub_eq_zero] at this
  exact this


open GlobalTheory.BirigidPow GlobalTheory.CechPic in
theorem dual_clauses {s : S ⟶ Sp R} {c : ℕ} {o o' : Obj b N s} {ψ : o.A ⟶ o'.A} (hψ : IsPIsog c o o' ψ)
    {ψ' : o'.A ⟶ o.A} [IsMonHom ψ'] (h₁ : ψ ≫ ψ' = (𝟙 o.A) ^ c) (h₂ : ψ' ≫ ψ = (𝟙 o'.A) ^ c) :
    (∀ a : D.O, o'.act.act a ≫ ψ' = ψ' ≫ o.act.act a) ∧ (∀ x, o.eta (c • x) = o'.eta x ≫ ψ') ∧
      Nonempty (LBIso (Hecke.lbPow o'.P c) (o.P.pull (sq2 ψ'))) := by
  have hc := hψ.pos
  refine ⟨fun a => ?_, fun x => ?_, ⟨?_⟩⟩
  · haveI := GlobalTheory.UPel.HT.MulEpi.epi_pow_of_isAbelianScheme S o'.A o'.ab c hc
    haveI : Epi (ψ' ≫ ψ) := by rw [h₂]; infer_instance
    haveI : Epi ψ := epi_of_epi ψ' ψ
    haveI := o.act.hom a
    rw [← cancel_epi ψ, ← Category.assoc, ← hψ.2.2.1, Category.assoc, h₁, ← Category.assoc, h₁, MonObj.comp_pow,
      MonObj.pow_comp, Category.comp_id, Category.id_comp]
  · rw [hψ.2.2.2.1, Category.assoc, h₁, MonObj.comp_pow, Category.comp_id, eta_nsmul]
  · have hL : (Hecke.lbPow o'.P c).IsLB := LB.isLB_linComb o'.isLB _ _
    refine (cls_eq_iff hL (pull_isLB o.isLB _)).1 ?_
    rw [BirigidPow.cls_lbPow o'.isLB, cls_pull o.isLB _ (pull_isLB o.isLB _)]
    change _ = BirigidPow.val o.isLB (fst o'.A o'.A ≫ ψ') (snd o'.A o'.A ≫ ψ')
    rw [← val_adj hψ h₂, Category.assoc, h₂, MonObj.comp_pow, Category.comp_id,
      val_pow_right o'.isLB o'.ab o'.ample o'.rig₁ o'.rig₂, BirigidPow.val, lift_fst_snd, Over.id_left, pull_id]

end GlobalTheory.UPel.HT.ESDual
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.YKThNeZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

namespace GlobalTheory.GSep

theorem GMem.yK_th_ne_zero : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → 𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩ ≠ 0 := by
  intro I X₁ z₁ act V _ _ _ ev X _ t δ 𝔪 x₀ hd h0
  obtain ⟨c, -, h⟩ := GlobalTheory.ZH.GoodOut.exists_th_notMem GlobalTheory.abelianSchemeLaws_all.1 GlobalTheory.abelianSchemeLaws_all.2 X₁.ρ
    ⟨RingHom.ker 𝔪.yK, RingHom.ker_isPrime 𝔪.yK⟩ 0
  refine h (RingHom.mem_ker.2 ?_)
  have sp : ∀ w, X₁.M.Z.fromSpecStalk z₁ w ⤳ z₁ := fun w => by
    have : X₁.M.Z.fromSpecStalk z₁ w ∈ Set.range (X₁.M.Z.fromSpecStalk z₁) := ⟨w, rfl⟩
    rwa [Scheme.range_fromSpecStalk] at this
  have hd' := hd.of_specializes
    (ξ := (jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) (closedPoint (FractionRing V))) (sp _)
  have hs : ∀ w, (jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) w ⤳
      (jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) (closedPoint (FractionRing V)) :=
    RatModel.specializes_of_range_eq (RatModel.range_eq_singleton _ _)
  have e := RatModel.val_mul hs (hd'.2 (0 + c)) (𝔪.reg _ (X₁.S.th_mem x₀))
  rw [div_mul_cancel₀ _ hd.1] at e
  rw [𝔪.yK_eq] at h0 ⊢
  exact e.trans ((congrArg (_ * ·) h0).trans (mul_zero _))

end GlobalTheory.GSep
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricTorsionPointMemberHasLabel
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricTorsionPointMemberHasLabel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.GSep.IntTerm

theorem torsion_has_label : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) (xb : TFK (R := V) (AlgebraicClosure (FractionRing V)) ⟶ 𝔪.A.A), xb ^ (X₁.S.r * X₁.S.N) = 1 → ∃ a : X₁.S.Gam, xb.left ≫ 𝔪.φ = spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp 𝔪.yK) ≫ (X₁.ρ.pt a).left := by
  intro I X₁ z₁ act V _ _ _ ev X _ t δ 𝔪 xb hxb
  let T := TFK (R := V) (AlgebraicClosure (FractionRing V))
  obtain ⟨a, ha, -⟩ := X₁.ρ.pt_bij (AlgebraicClosure (FractionRing V)) (T.hom ≫ spMap 𝔪.yK) (pushHom 𝔪.cart T xb)
    (by rw [← map_pow, hxb, map_one])
  refine ⟨a, ?_⟩
  have h1 : (T.hom ≫ spMap 𝔪.yK) ≫ (X₁.ρ.pt a).left = xb.left ≫ 𝔪.φ := congrArg (fun z => z.left) ha
  rw [← h1]
  congr 1
  exact (Spec.map_comp (CommRingCat.ofHom 𝔪.yK)
    (CommRingCat.ofHom (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))))).symm

end GlobalTheory.GSep.IntTerm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricTorsionPointMemberHasLabelStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.geometricTorsionPoint_member_has_label : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) (xb : TFK (R := V) (AlgebraicClosure (FractionRing V)) ⟶ 𝔪.A.A), xb ^ (X₁.S.r * X₁.S.N) = 1 → ∃ a : X₁.S.Gam, xb.left ≫ 𝔪.φ = spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp 𝔪.yK) ≫ (X₁.ρ.pt a).left := by
  first | exact @GlobalTheory.GSep.IntTerm.torsion_has_label | exact GlobalTheory.GSep.IntTerm.torsion_has_label | (intros; apply GlobalTheory.GSep.IntTerm.torsion_has_label <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelStalkNormalNoetherianFractionRing
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelStalkNormalNoetherianFractionRing
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.GSep

theorem stalk_isNoetherian_normal_fractionRing : ∀ (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z), letI : Algebra (X₁.M.Z.presheaf.stalk z₁) X₁.Ω₁ := (X₁.M.stalkHom z₁).toAlgebra; IsDomain (X₁.M.Z.presheaf.stalk z₁) ∧ IsFractionRing (X₁.M.Z.presheaf.stalk z₁) X₁.Ω₁ ∧ IsIntegrallyClosed (X₁.M.Z.presheaf.stalk z₁) ∧ IsNoetherianRing (X₁.M.Z.presheaf.stalk z₁) := by
  intro X₁ z₁
  letI : Algebra (X₁.M.Z.presheaf.stalk z₁) X₁.Ω₁ := (X₁.M.stalkHom z₁).toAlgebra
  have hN := X₁.normal
  refine ⟨GlobalTheory.IsNormalScheme.isDomain_stalk z₁, ?_, GlobalTheory.IsNormalScheme.isIntegrallyClosed_stalk z₁, ?_⟩
  · have : FaithfulSMul (X₁.M.Z.presheaf.stalk z₁) X₁.Ω₁ :=
      (faithfulSMul_iff_algebraMap_injective _ _).2 (X₁.M.stalkHom_injective z₁)
    refine IsFractionRing.of_field _ _ fun x => ?_
    obtain ⟨a, b, -, hx⟩ := IsFractionRing.div_surjective (A := X₁.M.O z₁) x
    refine ⟨(X₁.M.stalkEquiv z₁).symm a, (X₁.M.stalkEquiv z₁).symm b, ?_⟩
    have h : ∀ c : X₁.M.O z₁, algebraMap (X₁.M.Z.presheaf.stalk z₁) X₁.Ω₁ ((X₁.M.stalkEquiv z₁).symm c) = c := fun c => by
      change X₁.M.stalkHom z₁ _ = _
      rw [← RatModel.coe_stalkEquiv, RingEquiv.apply_symm_apply]
    rw [h, h, ← hx]
    rfl
  · have : IsDedekindDomain X₁.o₁ := X₁.ar.ded
    have := X₁.M.lft
    have : IsLocallyNoetherian (Sp X₁.o₁) :=
      inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of X₁.o₁)))
    have : IsLocallyNoetherian X₁.M.Z := LocallyOfFiniteType.isLocallyNoetherian X₁.M.s
    infer_instance

end GlobalTheory.GSep
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelStalkNormalNoetherianFractionRingStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modelStalk_normal_noetherian_fractionRing : ∀ (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z), letI : Algebra (X₁.M.Z.presheaf.stalk z₁) X₁.Ω₁ := (X₁.M.stalkHom z₁).toAlgebra; IsDomain (X₁.M.Z.presheaf.stalk z₁) ∧ IsFractionRing (X₁.M.Z.presheaf.stalk z₁) X₁.Ω₁ ∧ IsIntegrallyClosed (X₁.M.Z.presheaf.stalk z₁) ∧ IsNoetherianRing (X₁.M.Z.presheaf.stalk z₁) := by
  first | exact @GlobalTheory.GSep.stalk_isNoetherian_normal_fractionRing | exact GlobalTheory.GSep.stalk_isNoetherian_normal_fractionRing | (intros; apply GlobalTheory.GSep.stalk_isNoetherian_normal_fractionRing <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaConstantNeZeroUniformisedMember
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaConstantNeZeroUniformisedMember
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.GSep

theorem GMem.exists_th_ne_zero : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ), ∃ b, 𝔪.yK ⟨X₁.S.th b, X₁.S.th_mem b⟩ ≠ 0 := by
  intro I X₁ z₁ act V _ _ _ ev X _ t δ 𝔪
  haveI : CharZero V := 𝔪.cn.2.2.2
  haveI : CharZero (FractionRing V) :=
    (RingHom.charZero_iff (IsFractionRing.injective V (FractionRing V))).1 inferInstance
  exact GlobalTheory.ThetaGeneric.exists_th_ne_zero GlobalTheory.abelianSchemeLaws_all.1 GlobalTheory.abelianSchemeLaws_all.2 _ _ X₁.S X₁.ρ
    (FractionRing V) 𝔪.yK

end GlobalTheory.GSep

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaConstantNeZeroUniformisedMemberStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_thetaConstant_ne_zero_uniformisedMember : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ), ∃ b, 𝔪.yK ⟨X₁.S.th b, X₁.S.th_mem b⟩ ≠ 0 := by
  first | exact @GlobalTheory.GSep.GMem.exists_th_ne_zero | exact GlobalTheory.GSep.GMem.exists_th_ne_zero | (intros; apply GlobalTheory.GSep.GMem.exists_th_ne_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemiAbelianExtendingModelAboveThetaSystem
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemiAbelianExtendingModelAboveThetaSystem
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open Classical

theorem GlobalTheory.GSep.exists_zhAbove : ∀ (X₁ : GlobalTheory.GSep.GSet), ∃ (Y : RatModel X₁.o₁ X₁.Ω₁) (πY : Y.Z ⟶ X₁.M.Z),
    GlobalTheory.GSep.ZHAbove X₁ Y πY := by
  intro X₁
  obtain ⟨m, c, hc⟩ := RatModel.exists_isCl_of_isProjOver X₁.projM
  have hc0 : ∃ j, c j ≠ 0 := by
    obtain ⟨j, hj⟩ := hc.1 (genericPoint X₁.M.Z)
    exact ⟨j, hj.1⟩
  obtain ⟨Y, U₀, EE, hO, hdiv, hE, ⟨G⟩⟩ := GlobalTheory.zhSt_holds X₁.o₁ X₁.Ω₁ X₁.S X₁.ρ X₁.big (Fin (m + 1)) c hc0
    (GlobalTheory.ZH.finite_closure_theta_ratios_of_isCl X₁.o₁ X₁.Ω₁ X₁.S X₁.M (Fin (m + 1)) c hc)
  obtain ⟨q, hq⟩ := hc.exists_isHom (M' := Y) (φ := AlgHom.id X₁.o₁ X₁.Ω₁) hdiv
  have hYp : IsProper Y.s := ((GlobalTheory.isProjOver_iff_isProper_and_exists_isAmpleLB _).1 hO.proj).1
  have hsep : IsSeparated X₁.M.s := X₁.M.sep
  have hqp : IsProper q := by
    haveI : IsProper (q ≫ X₁.M.s) := by rw [hq.inducedModelMorphism_comp_structureMap]; exact hYp
    exact IsProper.of_comp q X₁.M.s
  exact ⟨Y, q, U₀, EE, ⟨G⟩, hO, hE, hq, hqp⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemiAbelianExtendingModelAboveThetaSystemStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_semiAbelianExtendingModel_above_thetaSystem : ∀ (X₁ : GlobalTheory.GSep.GSet), ∃ (Y : RatModel X₁.o₁ X₁.Ω₁) (πY : Y.Z ⟶ X₁.M.Z), GlobalTheory.GSep.ZHAbove X₁ Y πY := by
  first | exact @GlobalTheory.GSep.exists_zhAbove | exact GlobalTheory.GSep.exists_zhAbove | (intros; apply GlobalTheory.GSep.exists_zhAbove <;> assumption)
end
end
