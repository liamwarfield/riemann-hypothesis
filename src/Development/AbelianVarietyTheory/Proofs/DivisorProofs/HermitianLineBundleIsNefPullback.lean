module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithHeightProjectionFormulaEveryPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateTopBoundOfInputs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolarizationSectionBasisPullbackAffine
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomExistsIntegrable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernFormFieldDbarCohomologousTwoConnections
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAndAwayFormula
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightOfSizeBound
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsParallelWeightInvertibleSection

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianLineBundleIsNefPullback
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianLineBundleIsNefPullback
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSNef

theorem isNef_pull : GlobalTheory.Published.ArCalc → SemiPull → ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) [IsIntegral X]
    [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (D E : ℕ), IsArithVar p D → IsArithVar q E →
    ∀ (π : Y ⟶ X) (hπ : π ≫ p = q) (L : HermLB p), L.IsNef D → (L.pull π hπ).IsNef E := by
  intro hA hS k _ X Y _ _ p q D E hX hY π hπ L hN
  obtain ⟨h, hh⟩ := ((hA.arExists k X p D hX).1 L)
  obtain ⟨h', hh'⟩ := ((hA.arExists k Y q E hY).1 (L.pull π hπ))
  have hL := (hh.isNef_iff hX).1 hN
  refine (hh'.isNef_iff hY).2 ⟨hS k X Y p q D E hX hY π hπ L hN.semiPos, fun Z i _ _ hd => ?_⟩
  rw [GlobalTheory.MixHt.heightProj k X Y p q D E hX hY π hπ L h h' hh hh' (i (genericPoint Z))]
  by_cases h0 : π.residueDegree (i (genericPoint Z)) = 0
  · simp [h0]
  refine mul_nonneg (Nat.cast_nonneg _) ?_
  have hAY := GlobalTheory.MixHt.isAmb_of_isArithVar hY
  have hAX := GlobalTheory.MixHt.isAmb_of_isArithVar hX
  obtain ⟨-, -, -, -, hcl, hgd⟩ := GlobalTheory.MixHt.hasDim_basic k Y q hAY
  obtain ⟨⟨m', hm'⟩, -, -, -, hcl', hgd'⟩ := GlobalTheory.MixHt.hasDim_basic k X p hAX
  have hy : GlobalTheory.MixHt.HasDim (i (genericPoint Z)) 1 := (hcl Z i _ 1).2 ((hgd Z 1).2 (by exact_mod_cast hd))
  obtain ⟨d', -, hd'⟩ := hm' (π (i (genericPoint Z)))
  obtain ⟨-, hiff⟩ := GlobalTheory.DimDeg.dim_le_and_residueDegree_ne_zero_iff k X Y p q hAX hAY π hπ _ 1 d' hy hd'
  have e1 : 1 = d' := hiff.1 h0
  subst e1
  obtain ⟨W, j, _, _, hj⟩ := exists_isClosedImmersion_genericPoint (π (i (genericPoint Z)))
  have hW : topologicalKrullDim W = (1 : ℕ) := (hgd' W 1).1 ((hcl' W j _ 1).1 (hj ▸ hd'))
  have := hL.2 W j (by exact_mod_cast hW)
  rwa [hj] at this

end GlobalTheory.HSNef
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianLineBundleIsNefPullbackStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianLineBundle_isNef_pullback : GlobalTheory.Published.ArCalc → SemiPull → ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (D E : ℕ), IsArithVar p D → IsArithVar q E → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q) (L : HermLB p), L.IsNef D → (L.pull π hπ).IsNef E := by
  first | exact @GlobalTheory.HSNef.isNef_pull | exact GlobalTheory.HSNef.isNef_pull | (intros; apply GlobalTheory.HSNef.isNef_pull <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColengthRangeMapGe
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColengthRangeMapGe
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

namespace GlobalTheory.Dieu

theorem colength_range_map_ge (p : ℕ) [Fact p.Prime] (T : GlobalTheory.Dieu.Theory p) (k : Type) [Field k] [CharP k p]
    [PerfectRing k p] (G H : PDivGroup p k) (q : G ⟶ H) :
    (Module.finrank k (G.omega ⧸ LinearMap.range (omegaMap G H q)) : ℕ∞) ≤
        Module.length (WittVector p k) (T.M G ⧸ LinearMap.range (T.map q)) ∧
      (Module.finrank k (G.dual.Lie ⧸ LinearMap.range (lieMap H.dual G.dual (dualHom G H q))) : ℕ∞) ≤
        Module.length (WittVector p k) (T.M G ⧸ LinearMap.range (T.map q)) := by
  have hp : (p : k) = 0 := CharP.cast_eq_zero k p
  haveI : Module.Finite k G.RigExt := (GlobalTheory.T.finrank_rigidExtensions_eq_height_and_dim_add_dual p k hp G).2.1
  obtain ⟨θ, hθ⟩ := GlobalTheory.Dieu.theta_exists p T k
  have hred : ∀ m : T.M H, T.red G (T.map q m) = rigExtMap q (T.red H m) := fun m => by
    show T.base.red G trivial (T.base.smap trivial trivial (SemiHom.ofHom q) m) = _
    rw [T.base.red_smap, SemiHom.ofHom_rig]
  constructor
  · haveI : Module.Finite k G.omega :=
      Module.Finite.of_injective G.rigOfOmega (G.rigOfOmega_injective_of_eq_zero hp)
    obtain ⟨-, hsurj, -, hsemi, hnat⟩ := hθ G
    let Q := LinearMap.range (omegaMap G H q)
    refine (GlobalTheory.T.length_ge_finrank_of_semilinear_surjective p k (T.M G) (G.omega ⧸ Q) (WittVector.frobeniusEquiv p k)
      (Q.mkQ.toAddMonoidHom.comp (θ G)) (Q.mkQ_surjective.comp hsurj) (fun a n => ?_)
      (LinearMap.range (T.map q))).1 ?_
    · show Q.mkQ (θ G (WittVector.frobenius a • n)) = WittVector.constantCoeff a • Q.mkQ (θ G n)
      exact (congrArg Q.mkQ (hsemi a n)).trans (Q.mkQ.map_smul _ _)
    · rintro _ ⟨m, rfl⟩
      show Q.mkQ (θ G (T.map q m)) = 0
      rw [hnat, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact ⟨_, rfl⟩
  · haveI : Module.Finite k G.dual.Lie := Module.Finite.of_surjective (G.rigToLie hp) (G.rigToLie_surjective hp)
    let Q := LinearMap.range (lieMap H.dual G.dual (dualHom G H q))
    refine (GlobalTheory.T.length_ge_finrank_of_semilinear_surjective p k (T.M G) (G.dual.Lie ⧸ Q) (RingEquiv.refl _)
      ((Q.mkQ ∘ₗ G.rigToLie hp).toAddMonoidHom.comp (T.red G).toAddMonoidHom)
      ((Q.mkQ_surjective.comp (G.rigToLie_surjective hp)).comp (T.base.red_surjective G trivial))
      (fun a n => ?_) (LinearMap.range (T.map q))).1 ?_
    · show Q.mkQ (G.rigToLie hp (T.red G (a • n))) = WittVector.constantCoeff a • Q.mkQ (G.rigToLie hp (T.red G n))
      rw [LinearMap.map_smulₛₗ]
      exact (congrArg Q.mkQ ((G.rigToLie hp).map_smul _ _)).trans (Q.mkQ.map_smul _ _)
    · rintro _ ⟨m, rfl⟩
      show Q.mkQ (G.rigToLie hp (T.red G (T.map q m))) = 0
      rw [hred]
      have heq := rigToLie_rigExtMap hp q (T.red H m)
      apply (congrArg Q.mkQ heq).trans
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact ⟨_, rfl⟩

end GlobalTheory.Dieu
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColengthRangeMapGeStatement
open CategoryTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

theorem GlobalTheory.T.finrank_quot_range_le_length_quot_range_map
    (p : ℕ) [Fact p.Prime] (T : GlobalTheory.Dieu.Theory p) (k : Type) [Field k] [CharP k p]
    [PerfectRing k p] (G H : PDivGroup p k) (q : G ⟶ H) :
    (Module.finrank k (G.omega ⧸ LinearMap.range (omegaMap G H q)) : ℕ∞) ≤
        Module.length (WittVector p k) (T.M G ⧸ LinearMap.range (T.map q)) ∧
      (Module.finrank k (G.dual.Lie ⧸ LinearMap.range (lieMap H.dual G.dual (dualHom G H q))) : ℕ∞) ≤
        Module.length (WittVector p k) (T.M G ⧸ LinearMap.range (T.map q)) :=
  GlobalTheory.Dieu.colength_range_map_ge p T k G H q
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SignatureRigidifications
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SqTower.StageExists

theorem hasSignature_map_conj {n p q : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : Formalism.UG.HasSignature M p q) :
    Formalism.UG.HasSignature (M.map (starRingEnd ℂ)) p q := by
  obtain ⟨e, P, hP⟩ := h
  refine ⟨e, Matrix.GeneralLinearGroup.map (starRingEnd ℂ) P, ?_⟩
  have := congrArg (fun A => Matrix.map A (starRingEnd ℂ)) hP
  simp only [Matrix.map_mul] at this
  have hJ : (Formalism.UG.Jpq p q : Matrix _ _ ℂ).map (starRingEnd ℂ) = Formalism.UG.Jpq p q := by
    ext (a | a) (b | b) <;> simp [Formalism.UG.Jpq, Matrix.one_apply, apply_ite]
  rw [hJ] at this
  exact this

def withIdx {D : D7} (V : HSp D) (p : ℕ) : HSp D := { V with sig := fun _ => (V.rank - p, p) }

theorem withIdx_sigOK {D : D7} {V : HSp D} {p : ℕ} (h : NegIdx V p) : (withIdx V p).SigOK := by
  intro σ
  show Formalism.UG.HasSignature (V.gram.map σ) (V.rank - p) p
  obtain ⟨τ, hσ | hσ⟩ := GlobalTheory.DefiniteMult.exists_tauE_or_conj D σ
  · subst hσ
    simpa [gramAt] using h τ
  · subst hσ
    have h1 := hasSignature_map_conj (by simpa [gramAt] using h τ)
    rw [Matrix.map_map] at h1
    exact h1


open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle in
theorem rig_exists {D : D7} {V : HSp D} {p : ℕ} (h : NegIdx V p) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (hΛ : IsSelfDualC V Λ) : ∃ r : Rig V, r.Λ = Λ ∧ r.Is := by
  obtain ⟨r, e, hr⟩ := GlobalTheory.T.self_dual_lattice_has_rigidification D (withIdx V p) Λ (withIdx_sigOK h) hΛ
  exact ⟨⟨r.Λ, r.β, r.s, r.B⟩, e, hr⟩


open GlobalTheory.Grid GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle in
theorem vac_exists {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ)
    {S WW : HSp D} {p q : ℕ} (hS : NegIdx S p) (hW : NegIdx WW q) {r : Rig S} {rW : Rig WW} (h : r.Is) (h' : rW.Is) :
    (∃ f, IsVacO ψ θ (neg S) WW (fun τ => -r.s τ) rW.s r.Λ rW.Λ f) ∧ ∃ f, IsVacO ψ θ S WW r.s rW.s r.Λ rW.Λ f := by
  have hneg : IsSelfDualC (neg S) r.Λ := by
    refine ⟨h.1.1, fun y => (h.1.2 y).trans (forall₂_congr fun x _ => ⟨fun ⟨c, hc⟩ => ⟨-c, ?_⟩, fun ⟨c, hc⟩ => ⟨-c, ?_⟩⟩)⟩
    · simp [neg_gram, hc]
    · simp [neg_gram] at hc ⊢
      exact neg_eq_iff_eq_neg.2 hc
  constructor
  · obtain ⟨f, h0, h1, ⟨a, b, c, d⟩, h2, h3, h4⟩ := GlobalTheory.VacuumO.vacExists D ψ θ hψ hθ (neg (withIdx S p)) (withIdx WW q) (fun τ => -r.s τ) rW.s
      (sigOK_sgn true (withIdx_sigOK hS)) (withIdx_sigOK hW) (fun τ => isCartanInv_sgn true S τ (h.2.2 τ).1)
      (fun τ => (h'.2.2 τ).1) r.Λ rW.Λ hneg h'.1
    exact ⟨f, h0, h1, ⟨a, b, c, d⟩, h2, h3, h4⟩
  · obtain ⟨f, h0, h1, ⟨a, b, c, d⟩, h2, h3, h4⟩ := GlobalTheory.VacuumO.vacExists D ψ θ hψ hθ (withIdx S p) (withIdx WW q) r.s rW.s
      (withIdx_sigOK hS) (withIdx_sigOK hW) (fun τ => (h.2.2 τ).1) (fun τ => (h'.2.2 τ).1) r.Λ rW.Λ h.1 h'.1
    exact ⟨f, h0, h1, ⟨a, b, c, d⟩, h2, h3, h4⟩


end GlobalTheory.SqTower.StageExists

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteBottomThetaIntegralNormSqEqPetersson
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteBottomThetaIntegralNormSqEqPetersson
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate Matrix NNReal
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (sZero)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP (Pair Unram SphFun openOff integrand wcoef rcoef up)

namespace GlobalTheory.NormBigDict

theorem normSq_eq_petersson : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} (W : G.Weil) (i j : Fin D.R.m)
    (A A' WW : HSp D) (X : Tri T A A' WW), IsBottomTri W i j X → ∀ (t : T) (P : PolF D WW.rank A.rank)
    (ν : Measure (GA D WW)) (𝓕 : Set (GA D WW)), ν.IsHaarMeasure → IsFundamentalDomain (GQ WW) 𝓕 ν →
    ∃ m : Measure (GA D (GlobalTheory.Grid.neg A)), m.IsHaarMeasure ∧
      ((∫ h in 𝓕, ‖X.I W.ψ W.θ t P h‖ ^ 2 ∂ν : ℝ) : ℂ) =
        petersson WW ν (up ((X.ω t).toSgn true) m (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P) fun _ => 1) (up ((X.ω t).toSgn true) m (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P) fun _ => 1) := by
  intro D T L sc G W i j A A' WW X hX t P ν 𝓕 hν h𝓕
  have h := hX.is
  obtain ⟨ν₁, hν₁, hfd, hint⟩ := GlobalTheory.SgnIdent.meas_sgn true A X.m X.fd h.meas.1 h.meas.2
  refine ⟨ν₁, hν₁, ?_⟩
  have hW := h.weil t
  have hΦ := GlobalTheory.Chain.InnerSteps.theta_pureTensorO (S := GlobalTheory.Grid.neg A) h.isVac.1 h.isVac.2.inf (fun τ => -X.rA.s τ)
    X.rA.B X.rW.s X.rW.B (GlobalTheory.ConstRatio.theta_f h t).1 P
  set Φ := pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P with hΦd
  set om := (X.ω t).toSgn true with hom

  have hg : ∀ y : GA D WW, AutomorphicL2Unitary.LeftInv (GQ (GlobalTheory.Grid.neg A)) (fun g => thetaKO om g y Φ * (fun _ => (1 : ℂ)) g) := by
    intro y γ hγ g
    show om (γ * g, y) Φ 0 * 1 = om (g, y) Φ 0 * 1
    have e : ((γ * g, y) : GA D (GlobalTheory.Grid.neg A) × GA D WW) = (γ, 1) * (g, y) := by rw [Prod.mk_mul_mk, one_mul]
    rw [e, map_mul, Module.End.mul_apply]
    rw [hW.om_aut γ hγ 1 (GQ WW).one_mem _ (hW.om_pres _ _ hΦ)]

  have hup : ∀ y, up om ν₁ Φ (fun _ => 1) y = X.I W.ψ W.θ t P y := by
    intro y
    haveI := hν₁
    simp only [up, AutomorphicL2Unitary.autMeasure]
    rw [integral_quotMeasure hfd]
    simp only [(hg y).descend_mk]
    simp only [mul_one]
    exact (hint fun g => thetaKO (X.ω t) g y Φ).2

  have hinv : AutomorphicL2Unitary.LeftInv (GQ WW) (up om ν₁ Φ fun _ => 1) := by
    intro γ hγ y
    rw [hup, hup]
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Tri.I, GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Tri.ker]
    congr 1
    funext g
    exact GlobalTheory.ThetaMean.leftInv_theta hW hΦ ((GlobalTheory.Grid.ofSgn true A).symm g) γ hγ y
  haveI := hν
  simp only [petersson, pet]
  rw [integral_quotMeasure h𝓕]
  simp only [hinv.descend_mk, hup, Complex.mul_conj, ← Complex.sq_norm]
  exact (integral_ofReal).symm

end GlobalTheory.NormBigDict

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteBottomThetaIntegralNormSqEqPeterssonStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate Matrix NNReal
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (sZero)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP (Pair Unram SphFun openOff integrand wcoef rcoef up)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definiteBottom_thetaIntegral_normSq_eq_petersson : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} (W : G.Weil) (i j : Fin D.R.m)
    (A A' WW : HSp D) (X : Tri T A A' WW), IsBottomTri W i j X → ∀ (t : T) (P : PolF D WW.rank A.rank)
    (ν : Measure (GA D WW)) (𝓕 : Set (GA D WW)), ν.IsHaarMeasure → IsFundamentalDomain (GQ WW) 𝓕 ν →
    ∃ m : Measure (GA D (GlobalTheory.Grid.neg A)), m.IsHaarMeasure ∧
      ((∫ h in 𝓕, ‖X.I W.ψ W.θ t P h‖ ^ 2 ∂ν : ℝ) : ℂ) =
        petersson WW ν (up ((X.ω t).toSgn true) m (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P) fun _ => 1) (up ((X.ω t).toSgn true) m (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P) fun _ => 1) := by
  first | exact @GlobalTheory.NormBigDict.normSq_eq_petersson | exact GlobalTheory.NormBigDict.normSq_eq_petersson | (intros; apply GlobalTheory.NormBigDict.normSq_eq_petersson <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullFlagGradedLineChernFormsSmoothDbarClosed
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullFlagGradedLineChernFormsSmoothDbarClosed
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ChernCalc.GradedForm

variable {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {ι : Type} {m : ι → ℕ}

def lineGram (E : Fr (ratOf X) m m) (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ) (x : Root m) (y z : CxPts X.str σ) :
    Matrix (Fin 1) (Fin 1) ℂ := fun _ _ => ((grD (gramAt E H x.1 y z) x.2 : ℝ) : ℂ)

variable [Finite ι] {E : Fr (ratOf X) m m} {H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ}

theorem grD_pos (h : IsMetricFr E H) (x : Root m) (y : CxPts X.str σ) : 0 < grD (gramAt E H x.1 y y) x.2 :=
  ((GlobalTheory.T.gramLowerTriangularFactor_posDef_properties _ _ (h.posDef y _ (E.nonempty (under y)).choose_spec x.1)).2.1 x.2).1

theorem lineGram_smooth (h : IsMetricFr E H) (x : Root m) (y : CxPts X.str σ) :
    SmoothUnitAt (atlas X σ) (lineGram E H x y) y := by
  refine ⟨?_, fun c hc => ?_⟩
  · rw [Matrix.det_fin_one]
    exact isUnit_iff_ne_zero.2 (Complex.ofReal_ne_zero.2 (grD_pos h x y).ne')
  · filter_upwards [(GlobalTheory.T.flaggedBundleMetric_smoothUnit_etaleChart F σ X ι m m E H h y _ (E.nonempty (under y)).choose_spec x.1).2 c hc] with v hv
    intro a b
    exact Complex.ofRealCLM.contDiff.contDiffAt.comp v ((GlobalTheory.T.gramLowerTriangularFactor_gradedLength_smooth _ _ _ v hv.1 hv.2).2 x.2)

theorem isGramPair_lineGram (h : IsMetricFr E H) (x : Root m) :
    IsGramPair (atlas X σ) (lineGram E H x) (lineGram E H x) := by
  refine ⟨fun y => ⟨lineGram_smooth h x y, lineGram_smooth h x y⟩, fun y => ?_⟩
  have hy := (E.nonempty (under y)).choose_spec
  filter_upwards [GlobalTheory.T.adaptedFrame_eventually_frame_near_complex_point F σ X ι m m E y _ hy] with z hyz
  have hz := (E.nonempty (under z)).choose_spec
  set A := (E.nonempty (under y)).choose with hA
  set B := (E.nonempty (under z)).choose with hB
  have hP := (Fr.mem_iff hyz).1 hz
  have hhol := GlobalTheory.T.isHolomorphicUnitMatrixAt_rational_matrix_values F σ X _ ((B * A⁻¹) x.1) z (fun i j => mem_O_ratOf.1 ((hP x.1).1 i j)) (hP x.1).2.1
    (mem_O_ratOf.1 (hP x.1).2.2.1)
  have hval : ∀ w : CxPts X.str σ, A ∈ E.S (under w) → B ∈ E.S (under w) →
      Par m ⊤ ((B * A⁻¹).map (ratVal · w)) := fun w h1 h2 => by
    obtain ⟨ψ, hψ⟩ := exists_ratVal_hom w
    exact ((Fr.mem_iff h1).1 h2).map_of _ ψ hψ
  let T : CxPts X.str σ → Matrix (Fin 1) (Fin 1) ℂ := fun w _ _ => ratVal ((B * A⁻¹) x.1 x.2 x.2) w
  have hT : HolUnitAt (atlas X σ) T z := by
    refine ⟨?_, fun c hc _ _ => hhol.2 c hc x.2 x.2⟩
    rw [Matrix.det_fin_one]
    have hp := hval z hyz hz x.1
    have hd := hp.2.1
    rw [Matrix.det_of_lowerTriangular _ (fun i j hij => hp.2.2.2 i j i.2 hij)] at hd
    exact isUnit_iff_ne_zero.2 (Finset.prod_ne_zero_iff.1 hd x.2 (Finset.mem_univ _))
  refine ⟨T, T, T, hT, hT, hT, ?_⟩
  filter_upwards [GlobalTheory.T.adaptedFrame_eventually_frame_near_complex_point F σ X ι m m E z _ hyz, GlobalTheory.T.adaptedFrame_eventually_frame_near_complex_point F σ X ι m m E z _ hz] with w h1 h2
  rw [and_self]
  have hp := hval w h1 h2 x.1
  have e := (GlobalTheory.T.gramLowerTriangularFactor_lowerTriangular_conj _ _ _ (h.posDef w A h1 x.1) (fun i j hij => hp.2.2.2 i j i.2 hij)
    (isUnit_iff_ne_zero.2 hp.2.1)).2 x.2
  rw [← h.trans w A h1 B h2 x.1] at e
  ext a b
  simp only [Matrix.mul_apply, Fin.sum_univ_one, Matrix.conjTranspose_apply]
  change ((grD (H B w x.1) x.2 : ℝ) : ℂ) = ((B * A⁻¹).map (ratVal · w) x.1 x.2 x.2) * ((grD (H A w x.1) x.2 : ℝ) : ℂ) *
    star ((B * A⁻¹).map (ratVal · w) x.1 x.2 x.2)
  rw [e, mul_right_comm, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  rfl

theorem chernFld_lineGram (h : IsMetricFr E H) (x : Root m) :
    chernFld (atlas X σ) (lineGram E H x) 1 = grF E H x := by
  funext p
  have hs := ((lineGram_smooth h x p.pt).2 p.1.1 p.2).self_of_nhds
  have e := GlobalTheory.T.chernForm_triangular_eq_esymm_firstChernForms _ 1 (fun v => lineGram E H x p.pt (p.ch.symm v))
    (fun _ v => grD (gramAt E H x.1 p.pt (p.ch.symm v)) x.2) p.crd hs
    (fun _ => by
      have : p.ch.symm p.crd = p.pt := p.ch.left_inv p.2
      rw [this]; exact grD_pos h x _)
    (Eventually.of_forall fun v => ⟨fun i j hij => absurd (Subsingleton.elim i j) hij.ne, fun _ => rfl⟩) 1
  refine e.trans ?_
  rw [esymm_one, Fin.sum_univ_one, aeval_X]
  rfl

theorem dbarCoh_grF : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (ι : Type) [Finite ι] (m : ι → ℕ)
    (E : Fr (ratOf X) m m) (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ), IsMetricFr E H →
    ∀ x : Root m, DbarCoh (atlas X σ) (grF E H x) (grF E H x) := by
  intro F _ σ X ι _ m E H h x
  rw [← chernFld_lineGram h x]
  exact GlobalTheory.T.chernFormField_dbarCohomologous_two_connections _ _ _ _ _ _ (isGramPair_lineGram h x) 1

end GlobalTheory.ChernCalc.GradedForm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullFlagGradedLineChernFormsSmoothDbarClosedStatement
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fullFlagGradedLineChernForms_smooth_dbarClosed : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (ι : Type) [Finite ι] (m : ι → ℕ) (E : Fr (ratOf X) m m) (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ), IsMetricFr E H → ∀ x : Root m, DbarCoh (atlas X σ) (grF E H x) (grF E H x) := by
  first | exact @GlobalTheory.ChernCalc.GradedForm.dbarCoh_grF | exact GlobalTheory.ChernCalc.GradedForm.dbarCoh_grF | (intros; apply GlobalTheory.ChernCalc.GradedForm.dbarCoh_grF <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfinitePartIdentity
open Matrix NumberField
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace GlobalTheory.QuotientNormCoisometry

theorem norm_one_le {k : ℕ} : ‖(1 : Matrix (Fin k) (Fin k) ℂ)‖ ≤ 1 := by
  rw [← diagonal_one, l2_opNorm_diagonal]
  exact (pi_norm_le_iff_of_nonneg zero_le_one).2 fun _ => by simp

theorem norm_mul_coisom {m k l : ℕ} (T : Matrix (Fin m) (Fin k) ℂ) (W : Matrix (Fin k) (Fin l) ℂ)
    (hW : W * Wᴴ = 1) : ‖T * W‖ = ‖T‖ := by
  have hWt : ‖Wᴴ‖ ≤ 1 := by
    have h1 : ‖Wᴴ‖ * ‖Wᴴ‖ = ‖W * Wᴴ‖ := by
      rw [← l2_opNorm_conjTranspose_mul_self, conjTranspose_conjTranspose]
    rw [hW] at h1
    nlinarith [norm_nonneg Wᴴ, norm_one_le (k := k)]
  have hW1 : ‖W‖ ≤ 1 := by rwa [l2_opNorm_conjTranspose] at hWt
  apply le_antisymm
  · calc ‖T * W‖ ≤ ‖T‖ * ‖W‖ := l2_opNorm_mul _ _
      _ ≤ ‖T‖ := mul_le_of_le_one_right (norm_nonneg _) hW1
  · calc ‖T‖ = ‖T * W * Wᴴ‖ := by rw [Matrix.mul_assoc, hW, Matrix.mul_one]
      _ ≤ ‖T * W‖ * ‖Wᴴ‖ := l2_opNorm_mul _ _
      _ ≤ ‖T * W‖ := mul_le_of_le_one_right (norm_nonneg _) hWt

theorem inv_met {k : ℕ} (Y : Matrix (Fin k) (Fin k) ℂ) (hY : IsUnit Y.det) :
    ((Y⁻¹)ᴴ * Y⁻¹)⁻¹ = Y * Yᴴ := by
  rw [Matrix.mul_inv_rev, nonsing_inv_nonsing_inv _ hY, conjTranspose_nonsing_inv,
    nonsing_inv_nonsing_inv _ (by rw [det_conjTranspose]; exact hY.star)]

theorem norm_quot {n d D : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (P : Matrix (Fin D) (Fin n) ℂ)
    (XQ : Matrix (Fin D) (Fin D) ℂ) (X : Matrix (Fin n) (Fin n) ℂ) (Y : Matrix (Fin d) (Fin d) ℂ)
    (hQ : IsUnit XQ.det ∧ (XQ⁻¹)ᴴ * XQ⁻¹ = (P * A⁻¹ * Pᴴ)⁻¹) (hX : IsUnit X.det ∧ (X⁻¹)ᴴ * X⁻¹ = A)
    (V : Matrix (Fin d) (Fin D) ℂ) : ‖Y * V * XQ‖ = ‖Y * (V * P) * X‖ := by
  have hA : A⁻¹ = X * Xᴴ := by rw [← hX.2, inv_met X hX.1]
  have hQinv : IsUnit (XQ⁻¹).det := isUnit_nonsing_inv_det XQ hQ.1
  have hBu : IsUnit (P * A⁻¹ * Pᴴ).det := by
    rw [← isUnit_nonsing_inv_det_iff, ← hQ.2, det_mul, det_conjTranspose]
    exact hQinv.star.mul hQinv
  have hB : P * A⁻¹ * Pᴴ = XQ * XQᴴ := by
    rw [← nonsing_inv_nonsing_inv _ hBu, ← hQ.2, inv_met XQ hQ.1]
  have hW : (XQ⁻¹ * P * X) * (XQ⁻¹ * P * X)ᴴ = 1 := by
    rw [conjTranspose_mul, conjTranspose_mul]
    calc XQ⁻¹ * P * X * (Xᴴ * (Pᴴ * (XQ⁻¹)ᴴ)) = XQ⁻¹ * (P * (X * Xᴴ) * Pᴴ) * (XQ⁻¹)ᴴ := by
          simp only [Matrix.mul_assoc]
      _ = XQ⁻¹ * (XQ * XQᴴ) * (XQ⁻¹)ᴴ := by rw [← hA, hB]
      _ = (XQ⁻¹ * XQ) * (XQᴴ * (XQ⁻¹)ᴴ) := by simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [nonsing_inv_mul _ hQ.1, Matrix.one_mul, ← conjTranspose_mul, nonsing_inv_mul _ hQ.1, conjTranspose_one]
  have e : Y * (V * P) * X = (Y * V * XQ) * (XQ⁻¹ * P * X) := by
    calc Y * (V * P) * X = Y * V * (XQ * XQ⁻¹) * P * X := by
          rw [mul_nonsing_inv _ hQ.1]; simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = _ := by simp only [Matrix.mul_assoc]
  rw [e, norm_mul_coisom _ _ hW]

theorem htMap_quot {K : Type} [Field K] [NumberField K] [StarRing K] {n d D : ℕ} (H : Matrix (Fin n) (Fin n) K)
    (P : Matrix (Fin D) (Fin n) K) (XQ : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ)
    (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (X' : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ)
    (hQ : Formalism.DivisionValues.IsQuotMetric P H XQ)
    (hX : ∀ v : InfinitePlace K, IsUnit (X v).det ∧ ((X v)⁻¹)ᴴ * (X v)⁻¹ = H.map v.embedding)
    (vb : Matrix (Fin d) (Fin D) K) :
    Formalism.HN.htMap (Pi.basisFun K (Fin D)) XQ (Pi.basisFun K (Fin d)) X' vb.mulVecLin =
      Formalism.HN.htMap (Pi.basisFun K (Fin n)) X (Pi.basisFun K (Fin d)) X' (vb * P).mulVecLin := by
  unfold Formalism.HN.htMap
  congr 1
  refine Finset.sum_congr rfl fun v _ => ?_
  unfold Formalism.HN.opNormAt
  have hm : ∀ {a b : ℕ} (M : Matrix (Fin b) (Fin a) K),
      LinearMap.toMatrix (Pi.basisFun K (Fin a)) (Pi.basisFun K (Fin b)) M.mulVecLin = M := fun M => by
    ext i j
    simp [LinearMap.toMatrix_apply, Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [hm, hm]
  have e : ∀ {a b : ℕ} (M : Matrix (Fin a) (Fin b) ℂ),
      ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin M)‖ = ‖M‖ := fun M => (l2_opNorm_def M).symm
  rw [e, e, Matrix.map_mul, norm_quot (H.map v.embedding) (P.map v.embedding) (XQ v) (X v) (X' v)⁻¹ (hQ v) (hX v)]

section Bound

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open _root_.Formalism.L2 _root_.Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links _root_.Formalism.L2.Indef.Tree
open GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SumSize

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

theorem bound_le {p : PtAt ex Csz} {CF C : ℝ} (d : FunIn p CF) (hC0 : 0 ≤ C) (hC : CF ≤ C) :
    (D.R.m : ℝ) * aOne d.G C p.Z.b ≤ d.O.bIPa C p.Z.b := by
  have hS := LeafFixedPointPairing.GlobalTheory.CompanionTheory.LeafFixedPointPlaceNorm.sig_le d ∅ (fun _ => 0) hC
  have hN := GlobalTheory.BigTop.Fun.Model.N_eq d
  unfold FunData.bIPa aOne
  rw [hN]
  show (D.R.m : ℝ) * (C * D.R.f * (GlobalTheory.ChiGrid.bigN D : ℝ) * p.Z.b * Real.log p.Z.b +
      C * D.R.m * (GlobalTheory.ChiGrid.bigN D : ℝ) ^ 2 * sig d.G) ≤
    C * D.R.f * D.R.m * (GlobalTheory.ChiGrid.bigN D : ℝ) * p.Z.b * Real.log p.Z.b +
      C * (D.R.m : ℝ) ^ 2 * (GlobalTheory.ChiGrid.bigN D : ℝ) ^ 2 * (d.data (fun _ => 1) ∅ fun _ => 0).Sig0 C p.Z.b
  have h0 : 0 ≤ C * (D.R.m : ℝ) ^ 2 * (GlobalTheory.ChiGrid.bigN D : ℝ) ^ 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hS h0]

end Bound


end GlobalTheory.QuotientNormCoisometry

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BigRouteKernelEqConstMulTheta
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BigRouteKernelEqConstMulTheta
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.BigKernel

theorem end_finsupp_sum {α β : Type} (A : Module.End ℂ (β → ℂ)) (Θ : α →₀ ℂ) (f : α → β → ℂ) :
    A (Θ.sum fun d c => c • f d) = Θ.sum fun d c => c • A (f d) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Finsupp.sum, map_sum, map_smul]

theorem finsupp_sum_apply {α β : Type} (Θ : α →₀ ℂ) (f : α → β → ℂ) (w : β) :
    (Θ.sum fun d c => c • f d) w = Θ.sum fun d c => c * f d w := by
  simp only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

theorem isHecke_div {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    {χ χ' : (AF F ⊗[F] E)ˣ →* Circle} (h : GlobalTheory.LFun.IsHecke F E χ) (h' : GlobalTheory.LFun.IsHecke F E χ') :
    GlobalTheory.LFun.IsHecke F E (χ / χ') := by
  refine ⟨h.1.div' h'.1, fun x => ?_⟩
  simp only [MonoidHom.div_apply, h.2 x, h'.2 x, div_one]

theorem resEtaPow_div {R E : Type} [CommRing R] [CommRing E] [Algebra R E] {K : Subgroup Rˣ}
    {χ χ' : Eˣ →* Circle} {n m : ℕ} (h : GlobalTheory.WeilM.ResEtaPow K χ n) (h' : GlobalTheory.WeilM.ResEtaPow K χ' m) :
    GlobalTheory.WeilM.ResEtaPow K (χ / χ') (n + m) := by
  intro a
  have e1 := h a
  have e2 := h' a
  simp only [MonoidHom.div_apply, Circle.coe_div] at *
  rw [e1, e2]
  split_ifs
  · simp
  · have hm : ((-1 : ℂ) ^ m) * ((-1 : ℂ) ^ m) = 1 := by rw [← pow_add, ← two_mul, pow_mul]; simp
    rw [div_eq_iff (by simp), pow_add, mul_assoc, hm, mul_one]


set_option maxHeartbeats 1000000 in
theorem kerBig_eq_theta : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (M : Vol G)
    (Θ : TotT G (routeBig t i j)) (Θ' : TotT G (routeSmall t i j)) (hΘ : IsMatched B t ρ i j Θ Θ')
    (e : Num G i j) (Bs : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (X : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E)
    (om : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (h : IsTripleOf W M t i j e Bs Γ X), IsTriple Bs Γ X om om' → ∀ Φ, IsDatumA W e Γ Θ Φ → ∀ g g₁, ∃ ξ : ℂ, ξ ≠ 0 ∧
      ∀ u, kerBig W Θ g g₁ u = ξ * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.theta om Φ (conjU _ 1 h.JW u) (blkU _ _ e h.JWW (g, g₁)) := by
  intro D T L sc G μ₀ hL W B ρ t i j M Θ Θ' hΘ e Bs Γ X om om' h hTr Φ hΦ g g₁
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.T.hermitianSelfDualLatticeSpace_form_hermitian_nondeg_unimodular D Bs hTr.base _ Γ.V _ _ hTr.geo.hV
  obtain ⟨hJ, LS, hLS, h4, h5, h6⟩ := GlobalTheory.T.skewHermitian_neg_traceZero_inv_hermitian_unimodular D Bs hTr.base _ Γ.W _ _ hTr.geo.hW
  have hξ0 : D.host.xi0 ≠ 0 := GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D
  have eA : Γ.V.J = (GlobalTheory.WeilSchrodinger.hspOf D Γ.V.Jᵀ h1 h2 Γ.V.L hTr.geo.hV.lat.toIsLattice h3 (fun _ => (0, 0))).gramᵀ := by
    rw [GlobalTheory.WeilSchrodinger.gram_hspOf]; exact (Matrix.transpose_transpose _).symm
  have eB : (-1 : AF D.host.F ⊗[D.host.F] D.host.E) • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (D.host.xi0 •
      (GlobalTheory.WeilSchrodinger.hspOf D (-D.host.xi0 • Γ.W.J⁻¹) h4 h5 LS hLS h6 (fun _ => (0, 0))).gram⁻¹) := by
    rw [GlobalTheory.WeilSchrodinger.gram_hspOf]
    have e1 : (-D.host.xi0 • Γ.W.J⁻¹)⁻¹ = (-D.host.xi0)⁻¹ • Γ.W.J := Matrix.inv_eq_left_inv (by
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_nonsing_inv _ hJ,
        inv_mul_cancel₀ (neg_ne_zero.2 hξ0), one_smul])
    have e2 : D.host.xi0 • (-D.host.xi0)⁻¹ • Γ.W.J = -Γ.W.J := by
      rw [smul_smul, inv_neg, mul_neg, mul_inv_cancel₀ hξ0, neg_one_smul]
    show (-1 : AF D.host.F ⊗[D.host.F] D.host.E) • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J =
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (D.host.xi0 • (-D.host.xi0 • Γ.W.J⁻¹)⁻¹)
    rw [e1, e2]
    funext a b
    simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM]
  obtain ⟨ω, hω, -, hth⟩ := GlobalTheory.WeilBridge.exists_theta_eq D Bs hTr.base
    (GlobalTheory.WeilSchrodinger.hspOf D (-D.host.xi0 • Γ.W.J⁻¹) h4 h5 LS hLS h6 (fun _ => (0, 0)))
    (GlobalTheory.WeilSchrodinger.hspOf D Γ.V.Jᵀ h1 h2 Γ.V.L hTr.geo.hV.lat.toIsLattice h3 (fun _ => (0, 0))) Γ.V Γ.W _ _ _ _ hTr.geo.hV hTr.geo.hW eA eB
    Γ.M hTr.geo.hM X.β (X.β / X.α) hTr.chars.heckeβ (isHecke_div hTr.chars.heckeβ hTr.chars.heckeα) hTr.chars.resβ
    (resEtaPow_div hTr.chars.resβ hTr.chars.resα) om hTr.weil
  rw [h.ψ] at hω
  obtain ⟨ξ, hξ, hss⟩ := GlobalTheory.T.bigRoute_seesaw_arrow_kernels_product W t i j M e Bs Γ X om om' h hTr h1 h2 _ hTr.geo.hV.lat.toIsLattice h3 _ h4 h5 LS hLS h6 _ ω hω g g₁
  refine ⟨ξ, hξ, fun u => ?_⟩
  obtain ⟨g', h', hh', hg'⟩ := GlobalTheory.WeilSchrodinger.match_pair D
    (GlobalTheory.WeilSchrodinger.hspOf D (-D.host.xi0 • Γ.W.J⁻¹) h4 h5 LS hLS h6 (fun _ => (0, 0)))
    (GlobalTheory.WeilSchrodinger.hspOf D Γ.V.Jᵀ h1 h2 Γ.V.L hTr.geo.hV.lat.toIsLattice h3 (fun _ => (0, 0))) Γ.V.J Γ.W.J (-1) eA eB (conjU (spW G i j) 1 h.JW u)
    (blkU (spV G i j) (spV₁ G i j) e h.JWW (g, g₁))
  have key := hth _ _ g' h' hh' hg' Φ hΦ.1
  refine Eq.trans ?_ (congrArg (fun z => ξ * z) key.symm)
  have htr : GlobalTheory.WeilSchrodinger.thetaTr D.host.F Γ.M.co Bs.ψ Φ =
      Θ.sum fun d c => c • GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.boxA e d := by
    funext w
    show GlobalTheory.WeilM.thetaSum D.host.F (Γ.M.co.rho Bs.ψ w Φ) = _
    rw [h.ψ, hΦ.2 w]
    exact (finsupp_sum_apply _ _ w).symm
  refine Eq.trans ?_ (congrArg (fun f => ξ * ω (g', h') f 0) htr.symm)
  refine Eq.trans ?_ (congrArg (fun z => ξ * z)
    (congrFun (end_finsupp_sum (ω (g', h')) Θ (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.boxA e)) 0).symm)
  rw [finsupp_sum_apply, kerBig, Finsupp.sum, Finsupp.sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  obtain ⟨t1, t2⟩ := GlobalTheory.RouteSeesaw.data_theta W B ρ t i j hΘ d hd
  rw [hss d.1.2 d.2 t1 t2 u g' h' hh' hg', mul_left_comm]
  rfl

end GlobalTheory.BigKernel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BigRouteKernelEqConstMulThetaStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.big_route_kernel_eq_const_mul_theta : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (M : Vol G)
    (Θ : TotT G (routeBig t i j)) (Θ' : TotT G (routeSmall t i j)) (hΘ : IsMatched B t ρ i j Θ Θ')
    (e : Num G i j) (Bs : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (X : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E)
    (om : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (h : IsTripleOf W M t i j e Bs Γ X), IsTriple Bs Γ X om om' → ∀ Φ, IsDatumA W e Γ Θ Φ → ∀ g g₁, ∃ ξ : ℂ, ξ ≠ 0 ∧
      ∀ u, kerBig W Θ g g₁ u = ξ * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.theta om Φ (conjU _ 1 h.JW u) (blkU _ _ e h.JWW (g, g₁)) := by
  first | exact @GlobalTheory.BigKernel.kerBig_eq_theta | exact GlobalTheory.BigKernel.kerBig_eq_theta | (intros; apply GlobalTheory.BigKernel.kerBig_eq_theta <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaDistributionRationalPointsInvariantTriple
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaDistributionRationalPointsInvariantTriple
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.RatInvTheta

theorem inclR_inj (D : D7) : Function.Injective (inclR (F := D.host.F) (E := D.host.E) (AF D.host.F)) :=
  Algebra.TensorProduct.includeRight_injective (AdeleRing.algebraMap_injective (𝓞 D.host.F) D.host.F)

theorem sigR_inclR (D : D7) (e : D.host.E) :
    sigR (AF D.host.F) D.sp.cm.sig (inclR (F := D.host.F) (AF D.host.F) e) =
      inclR (F := D.host.F) (AF D.host.F) (D.sp.cm.sig e) := by
  simp [sigR, inclR]

theorem mem_GQ_of {D : D7} (V : HSp D) (g : GA D V) (z : GL (Fin V.rank) D.host.E)
    (hz : mt V g = (z : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (inclR (F := D.host.F) (AF D.host.F))) :
    g ∈ GQ V := by
  refine ⟨z, ?_, Units.ext ?_⟩
  · have hm : Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) (mt V g) * JR (AF D.host.F) V.gram * mt V g =
        JR (AF D.host.F) V.gram := g.2
    have hcT : Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig)
        ((z : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (inclR (F := D.host.F) (AF D.host.F))) =
        (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (z : Matrix (Fin V.rank) (Fin V.rank) D.host.E)).map
          (inclR (F := D.host.F) (AF D.host.F)) := by
      ext i j; exact sigR_inclR D _
    rw [hz, hcT] at hm
    show Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (z : Matrix (Fin V.rank) (Fin V.rank) D.host.E) * V.gram *
      (z : Matrix (Fin V.rank) (Fin V.rank) D.host.E) = V.gram
    apply Matrix.map_injective (inclR_inj D)
    dsimp only
    rw [Matrix.map_mul, Matrix.map_mul]
    exact hm
  · exact hz.symm

theorem thetaSum_rat_inv : ∀ {D : D7} {a a' : ℕ} (Bs : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig a a') (X : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E)
    (om : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W), IsTriple Bs Γ X om om' →
    ∀ γ ∈ ratU D.sp.cm.sig Γ.V.J, ∀ γ' ∈ ratU D.sp.cm.sig Γ.W.J, ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F (Fin a × Fin (a + a')),
      GlobalTheory.WeilM.thetaSum D.host.F (om (γ, γ') Φ) = GlobalTheory.WeilM.thetaSum D.host.F Φ := by
  intro D a a' Bs Γ X om om' hT γ hγ γ' hγ' Φ hΦ
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.T.hermitianSelfDualLatticeSpace_form_hermitian_nondeg_unimodular D Bs hT.base a Γ.V _ _ hT.geo.hV
  obtain ⟨hJ, L, hL, h4, h5, h6⟩ := GlobalTheory.T.skewHermitian_neg_traceZero_inv_hermitian_unimodular D Bs hT.base (a + a') Γ.W _ _ hT.geo.hW
  have hξ : D.host.xi0 ≠ 0 := GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D
  let T := GlobalTheory.WeilSchrodinger.hspOf D Γ.V.Jᵀ h1 h2 Γ.V.L hT.geo.hV.lat.toIsLattice h3 (fun _ => (a - Γ.p, Γ.p))
  let S := GlobalTheory.WeilSchrodinger.hspOf D (-D.host.xi0 • Γ.W.J⁻¹) h4 h5 L hL h6
    (fun _ => (Γ.p + Γ.q, a + a' - (Γ.p + Γ.q)))
  have eA : Γ.V.J = T.gramᵀ := by rw [GlobalTheory.WeilSchrodinger.gram_hspOf]; rfl
  have eB : (-1 : AF D.host.F ⊗[D.host.F] D.host.E) • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J =
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (D.host.xi0 • S.gram⁻¹) := by
    rw [GlobalTheory.WeilSchrodinger.gram_hspOf]
    have e1 : (-D.host.xi0 • Γ.W.J⁻¹)⁻¹ = (-D.host.xi0)⁻¹ • Γ.W.J := Matrix.inv_eq_left_inv (by
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_nonsing_inv _ hJ,
        inv_mul_cancel₀ (neg_ne_zero.2 hξ), one_smul])
    have e2 : D.host.xi0 • (-D.host.xi0)⁻¹ • Γ.W.J = -Γ.W.J := by
      rw [smul_smul, inv_neg, mul_neg, mul_inv_cancel₀ hξ, neg_one_smul]
    show (-1 : AF D.host.F ⊗[D.host.F] D.host.E) • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J =
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (D.host.xi0 • (-D.host.xi0 • Γ.W.J⁻¹)⁻¹)
    rw [e1, e2]
    funext i j
    simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM]
  have hcW : GlobalTheory.LFun.IsHecke D.host.F D.host.E (X.β / X.α) :=
    ⟨hT.chars.heckeβ.1.div' hT.chars.heckeα.1, fun x => by
      rw [MonoidHom.div_apply, hT.chars.heckeβ.2 x, hT.chars.heckeα.2 x, div_one]⟩
  have rW : GlobalTheory.WeilM.ResEtaPow (Units.map (algebraMap D.host.F (AF D.host.F)).toMonoidHom).range (X.β / X.α)
      (a + a') := by
    intro x
    have e₁ := hT.chars.resβ x
    have e₂ := hT.chars.resα x
    rw [MonoidHom.div_apply, Circle.coe_div, e₁, e₂, hT.geo.even.neg_one_pow]
    split_ifs
    · simp
    · rcases Nat.even_or_odd a with h | h
      · have h' : Even a' := (Nat.even_add.mp hT.geo.even).mp h
        rw [h.neg_one_pow, h'.neg_one_pow]; simp
      · have h' : Odd a' := by
          rcases Nat.even_or_odd a' with h'' | h''
          · exact absurd ((Nat.even_add.mp hT.geo.even).mpr h'') (Nat.not_even_iff_odd.mpr h)
          · exact h''
        rw [h.neg_one_pow, h'.neg_one_pow]; simp
  obtain ⟨ω, hω, -, hth⟩ := GlobalTheory.WeilBridge.exists_theta_eq D Bs hT.base S T Γ.V Γ.W _ _ _ _ hT.geo.hV hT.geo.hW
    eA eB Γ.M hT.geo.hM X.β (X.β / X.α) hT.chars.heckeβ hcW hT.chars.resβ rW om hT.weil
  obtain ⟨g, h, hh, hg⟩ := GlobalTheory.WeilSchrodinger.match_pair D S T Γ.V.J Γ.W.J (-1) eA eB γ γ'
  obtain ⟨z, hz⟩ := hγ
  obtain ⟨z', hz'⟩ := hγ'
  have hhQ : h ∈ GQ T := by
    refine mem_GQ_of T h z ?_
    rw [hh]
    exact (congrArg Units.val hz).symm
  have hgQ : g ∈ GQ S := by
    have m1 := congrArg Matrix.transpose (Units.mul_inv z')
    have m2 := congrArg Matrix.transpose (Units.inv_mul z')
    rw [Matrix.transpose_mul, Matrix.transpose_one] at m1 m2
    let Z : GL (Fin (a + a')) D.host.E :=
      ⟨((z'⁻¹ : GL (Fin (a + a')) D.host.E) : Matrix (Fin (a + a')) (Fin (a + a')) D.host.E)ᵀ,
        ((z' : GL (Fin (a + a')) D.host.E) : Matrix (Fin (a + a')) (Fin (a + a')) D.host.E)ᵀ, m1, m2⟩
    refine mem_GQ_of S g Z ?_
    rw [hg]
    have h0 : γ'.1 = Matrix.GeneralLinearGroup.map (inclR (F := D.host.F) (E := D.host.E) (AF D.host.F)) z' := hz'.symm
    show ((γ'.1)⁻¹ : GL (Fin (a + a')) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := D.host.F) (E := D.host.E))).1ᵀ = _
    rw [h0, ← map_inv]
    rfl
  have hf :=
    GlobalTheory.T.isThetaFunction_thetaTransform_rationalDarboux D Bs.ψ (GlobalTheory.T.isStdChar_neg_one_of_standardTraceAdelicAddChar D Bs.ψ hT.base.std) S T Γ.V.J Γ.W.J (-1) eA eB (Fin T.rank × Fin S.rank) Γ.M.co
      hT.geo.hM.rat Φ hΦ
  have key := hth γ γ' g h hh hg Φ hΦ
  have e0 := GlobalTheory.WeilBridge.thetaTr_zero D Γ.M.co Bs.ψ Φ
  have e1 := hω.om_aut g hgQ h hhQ _ hf
  exact key.trans (e1.trans e0)

end GlobalTheory.RatInvTheta
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaDistributionRationalPointsInvariantTripleStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_distribution_rational_points_invariant_triple : ∀ {D : D7} {a a' : ℕ} (Bs : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig a a') (X : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E)
    (om : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W), IsTriple Bs Γ X om om' →
    ∀ γ ∈ ratU D.sp.cm.sig Γ.V.J, ∀ γ' ∈ ratU D.sp.cm.sig Γ.W.J, ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F (Fin a × Fin (a + a')),
      GlobalTheory.WeilM.thetaSum D.host.F (om (γ, γ') Φ) = GlobalTheory.WeilM.thetaSum D.host.F Φ := by
  first | exact @GlobalTheory.RatInvTheta.thetaSum_rat_inv | exact GlobalTheory.RatInvTheta.thetaSum_rat_inv | (intros; apply GlobalTheory.RatInvTheta.thetaSum_rat_inv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidifiedExtensionPresentationNaturalSemilinear
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidifiedExtensionPresentationNaturalSemilinear
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

theorem GlobalTheory.Katz.rig_pull_natural_semi : ∀ (p : ℕ) (k k' : Type) [CommRing k] [CommRing k'] (σ : k →+* k') (d e : ℕ) (G : PDivGroup p k) (G' : PDivGroup p k') (c : Chart G d) (c' : Chart G' e) (s : SemiHom σ G' G) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k) (φ : Fin d → MvPowerSeries (Fin e) k') (ρ : MvPowerSeries (Fin d ⊕ Fin d) k × (Fin d → k) →ₗ[k] ((G.cocycles × G.omega) ⧸ _root_.LinearMap.range (G.cob.prod (_root_.LinearMap.codRestrict G.omegaSub ((_root_.LinearMap.piMap fun i => _root_.GlobalTheory.AugCot.d (_root_.Bialgebra.counitAlgHom _ (G.A i))).domRestrict G.funs) (fun b n => (_root_.GlobalTheory.PDiv.cotMap_d _ _).trans (_root_.congrArg _ (b.2 n))))))) (ρ' : MvPowerSeries (Fin e ⊕ Fin e) k' × (Fin e → k') →ₗ[k'] ((G'.cocycles × G'.omega) ⧸ _root_.LinearMap.range (G'.cob.prod (_root_.LinearMap.codRestrict G'.omegaSub ((_root_.LinearMap.piMap fun i => _root_.GlobalTheory.AugCot.d (_root_.Bialgebra.counitAlgHom _ (G'.A i))).domRestrict G'.funs) (fun b n => (_root_.GlobalTheory.PDiv.cotMap_d _ _).trans (_root_.congrArg _ (b.2 n))))))), c.IsLawOf μ → (∀ n j, c'.ev n (φ j) = s.app n (c.x n j)) → (∀ t w (z : G.cocycles) (u : G.omega), (∀ n, z.1 n = c.ev₂ n t) → (∀ n, u.1 n = ∑ i, w i • dUnit (R := k) (c.x n i)) → ρ (t, w) = G.rigMk (z, u)) → (∀ t w (z : G'.cocycles) (u : G'.omega), (∀ n, z.1 n = c'.ev₂ n t) → (∀ n, u.1 n = ∑ i, w i • dUnit (R := k') (c'.x n i)) → ρ' (t, w) = G'.rigMk (z, u)) → ∀ t w, IsCoc μ t → ρ' (pull2 φ (MvPowerSeries.map σ t), pullLin φ (fun i => σ (w i))) = s.rig (ρ (t, w)) := by
  intro p k k' _ _ σ d e G G' c c' s μ φ ρ ρ' hμ hφ hρ hρ' t w ht
  have hz : (fun n => c.ev₂ n t) ∈ G.cocycles := (GlobalTheory.T.isSymmetricFormalGroupCocycle_iff_mem_cocycles p k d G c μ hμ t).1 ht
  have hu : (fun n => ∑ i, w i • dUnit (R := k) (c.x n i)) ∈ G.omegaSub := (GlobalTheory.T.invariantDifferentials_connectedPDivGroup_coordinates p k d G c).1 w
  rw [hρ t w ⟨_, hz⟩ ⟨_, hu⟩ (fun _ => rfl) (fun _ => rfl), SemiHom.rig_mk]
  have hev : ∀ n, c'.ev₂ n (pull2 φ (MvPowerSeries.map σ t)) = (s.app n).two (c.ev₂ n t) := by
    intro n
    exact GlobalTheory.Katz.semiHom_ev₂_pull2 p k k' σ d e G G' c c' s φ hφ n t
  refine hρ' _ _ _ _ (fun n => ?_) (fun n => ?_)
  · rw [SemiHom.cocycles_val, hev n]
  · rw [SemiHom.omega_val]
    change (s.app n).cot (∑ i, w i • dUnit (R := k) (c.x n i)) = _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [map_smulₛₗ, SemiBialgHom.cot_d]
    have hd : ∀ i, dUnit (R := k') (s.app n (c.x n i)) = ∑ l, lin (φ i) l • dUnit (R := k') (c'.x n l) := fun i => by
      rw [← hφ n i]
      exact (GlobalTheory.T.counit_cotangentClass_powerSeriesEvalAtNilpotent k' e (G'.A n) (c'.x n) (c'.nil n) (c'.aug n) (φ i)).2
    simp only [hd, Finset.smul_sum, smul_smul, pullLin, Finset.sum_smul]
    exact Finset.sum_comm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidifiedExtensionPresentationNaturalSemilinearStatement
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rigidifiedExtension_presentation_natural_semilinear : ∀ (p : ℕ) (k k' : Type) [CommRing k] [CommRing k'] (σ : k →+* k') (d e : ℕ) (G : PDivGroup p k) (G' : PDivGroup p k') (c : Chart G d) (c' : Chart G' e) (s : SemiHom σ G' G) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k) (φ : Fin d → MvPowerSeries (Fin e) k') (ρ : MvPowerSeries (Fin d ⊕ Fin d) k × (Fin d → k) →ₗ[k] ((G.cocycles × G.omega) ⧸ _root_.LinearMap.range (G.cob.prod (_root_.LinearMap.codRestrict G.omegaSub ((_root_.LinearMap.piMap fun i => _root_.GlobalTheory.AugCot.d (_root_.Bialgebra.counitAlgHom _ (G.A i))).domRestrict G.funs) (fun b n => (_root_.GlobalTheory.PDiv.cotMap_d _ _).trans (_root_.congrArg _ (b.2 n))))))) (ρ' : MvPowerSeries (Fin e ⊕ Fin e) k' × (Fin e → k') →ₗ[k'] ((G'.cocycles × G'.omega) ⧸ _root_.LinearMap.range (G'.cob.prod (_root_.LinearMap.codRestrict G'.omegaSub ((_root_.LinearMap.piMap fun i => _root_.GlobalTheory.AugCot.d (_root_.Bialgebra.counitAlgHom _ (G'.A i))).domRestrict G'.funs) (fun b n => (_root_.GlobalTheory.PDiv.cotMap_d _ _).trans (_root_.congrArg _ (b.2 n))))))), c.IsLawOf μ → (∀ n j, c'.ev n (φ j) = s.app n (c.x n j)) → (∀ t w (z : G.cocycles) (u : G.omega), (∀ n, z.1 n = c.ev₂ n t) → (∀ n, u.1 n = ∑ i, w i • dUnit (R := k) (c.x n i)) → ρ (t, w) = G.rigMk (z, u)) → (∀ t w (z : G'.cocycles) (u : G'.omega), (∀ n, z.1 n = c'.ev₂ n t) → (∀ n, u.1 n = ∑ i, w i • dUnit (R := k') (c'.x n i)) → ρ' (t, w) = G'.rigMk (z, u)) → ∀ t w, IsCoc μ t → ρ' (pull2 φ (MvPowerSeries.map σ t), pullLin φ (fun i => σ (w i))) = s.rig (ρ (t, w)) := by
  first | (exact @GlobalTheory.Katz.rig_pull_natural_semi) | (exact GlobalTheory.Katz.rig_pull_natural_semi) | (intros; apply GlobalTheory.Katz.rig_pull_natural_semi  <;> assumption)
end
end
