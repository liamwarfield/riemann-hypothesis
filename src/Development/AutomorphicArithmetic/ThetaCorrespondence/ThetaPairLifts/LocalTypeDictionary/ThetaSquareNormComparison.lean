module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomTriangleIntegralsNeZero
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BottomThetaNormEqProdLocalFactors
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaStageNonzeroAtFinitePlaces

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.RegConstEqAwayUnitMulFactor
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaFlipInvolutiveCorrespondence
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaFlipTensorMatch
section
noncomputable section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.ChainFr Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
namespace GlobalTheory.TopFlip
open GlobalTheory.SquareComm GlobalTheory.SquareAgree GlobalTheory.Grid GlobalTheory.TripleRead GlobalTheory.TripleAssembly GlobalTheory.RouteSeesaw GlobalTheory.SquareIdent
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (incM)
variable {D : D7}
set_option maxHeartbeats 1000000 in
theorem thetaFlip_tensor_match (hH : GlobalTheory.Published.HoweDualityReal) (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (hTL : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching)
    {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hθ : IsInfFam θ) {W W₁ X : HSp D} (A : Fr W) (A₁ : Fr W₁) (B : Fr X)
    {α β : (AE D)ˣ →* Circle} (hT : IsTriple W W₁ X α β) {ωA : WRep W X} {ωB : WRep W₁ X} (hωA : IsWeil ψ true W X β (β / α) ωA)
    (hωB : IsWeil ψ false W₁ X α (α / β) ωB) {e : Fin (W.rank + W₁.rank) ≃ Fin X.rank} {Bs Γ Xc}
    (hR : IsReading ψ A A₁ B α β e Bs Γ Xc) {om₀ om₀'} (hT₀ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om₀ om₀') :
    ∃ om om' R Rf, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ Xc om om' R Rf ∧
      ∃ rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB (ModuleCat.of ℂ (PiT R Γ Rf)) rf rl p p' ∧
      (∀ f₀, Γ.M.IsGauss Bs.ψ Bs.emb f₀ → ∀ P, ∃ a : R.Pi, ∀ φ, GlobalTheory.BigNZ.IsFinPart Γ.M Xc.T φ → ∀ F : WO W X → ℂ,
        IsDatum Γ.M ψ (fun u => (HMul.hMul (uᵀ.submatrix e.symm id) (incM (sgn true W).gram) :
          Matrix (Fin X.rank) (Fin W.rank) (AE D))) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₀ φ) F →
        IsFinF ψ θ true A B F ∧
          p (fockF ψ θ true A B F P) = a ⊗ₜ GlobalTheory.SmallThetaModules.pureT (vacIm Γ Rf) fun v => Rf.p v (φ v)) ∧
      ∀ f₀, Γ.M'.IsGauss Bs.ψ Bs.emb f₀ → ∀ P, ∃ a : R.Pi, ∀ φ, GlobalTheory.BigNZ.IsFinPart Γ.M' Xc.T φ → ∀ F : WO W₁ X → ℂ,
        IsDatum Γ.M' ψ (fun u => (HMul.hMul (uᵀ.submatrix e.symm id) (incM W₁.gram) :
          Matrix (Fin X.rank) (Fin W₁.rank) (AE D))) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₀ φ) F →
        IsFinF ψ θ false A₁ B F ∧
          p' (fockF ψ θ false A₁ B F P) = a ⊗ₜ GlobalTheory.SmallThetaModules.pureT (vacIm Γ Rf) fun v => Rf.p' v (φ v) := by
  obtain rfl := hR.ψ
  have hg := hT₀.geo
  have hstd : IsStdChar D Bs.ψ (-1) := GlobalTheory.StdCharFromIsStd.isStdChar_of_isStd D Bs.ψ hT₀.base.std
  obtain ⟨om, hom, tA⟩ := GlobalTheory.TripleDarboux.exists_weil Bs hT₀.base true W X e _ _ hg.hV hg.hW 1 hR.JW
    (by rw [neg_gram, one_smul, neg_neg]) hR.JX Γ.M hg.hM hωA
  obtain ⟨om', hom', tB⟩ := GlobalTheory.TripleDarboux.exists_weil Bs hT₀.base false W₁ X e _ _ hg.hV' hg.hW (-1) hR.JW₁
    (neg_one_smul _ _) hR.JX Γ.M' hg.hM' hωB
  have hT' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' :=
    ⟨hT₀.base, hg, hT₀.chars, by rw [hR.α, hR.β]; exact hom, by rw [hR.α, hR.β]; exact hom'⟩
  obtain ⟨R, Rf, hm⟩ := hTL _ _ _ Bs _ _ Γ Xc om om' hT'
  have sA := GlobalTheory.T.fockAlgebraicThetaVectors_stable_finiteAdeles_lie D Bs.ψ θ hstd hθ true W X A B β (β / α) ωA hωA
  have sB := GlobalTheory.T.fockAlgebraicThetaVectors_stable_finiteAdeles_lie D Bs.ψ θ hstd hθ false W₁ X A₁ B α (α / β) ωB hωB
  obtain ⟨oA, oB⟩ := _root_.GlobalTheory.T.triple_algebra_map_surjective hH hP D Bs.ψ θ hstd hθ W W₁ X A A₁ B α β hT ωA ωB hωA hωB e Bs Γ Xc om om' hR tA tB R Rf hm
  obtain ⟨iA, iB⟩ := _root_.GlobalTheory.T.triple_assembly_inverse_finite hH hP D Bs.ψ θ hstd hθ W W₁ X A A₁ B α β hT ωA ωB hωA hωB e Bs Γ Xc om om' hR tA tB R Rf hm
  obtain ⟨lA, lB⟩ := _root_.GlobalTheory.T.theta_triple_lift_lie_invariant hH hP D Bs.ψ θ hstd hθ W W₁ X A A₁ B α β hT ωA ωB hωA hωB e Bs Γ Xc om om' hR tA tB R Rf hm
  obtain ⟨fA, fB⟩ := _root_.GlobalTheory.T.theta_triple_maps_equivariant hH hP D Bs.ψ θ hstd hθ W W₁ X A A₁ B α β hT ωA ωB hωA hωB e Bs Γ Xc om om' hR tA tB R Rf hm
  obtain ⟨dA, dB⟩ := _root_.GlobalTheory.T.theta_triple_lift_lie_equivariant hH hP D Bs.ψ θ hstd hθ W W₁ X A A₁ B α β hT ωA ωB hωA hωB e Bs Γ Xc om om' hR tA tB R Rf hm
  have ir := _root_.GlobalTheory.T.theta_triple_lift_irreducible hH hP D Bs.ψ θ hstd hθ W W₁ X A A₁ B α β hT ωA ωB hωA hωB e Bs Γ Xc om om' hR tA tB R Rf hm
  obtain ⟨cA, hcA⟩ := GlobalTheory.Twist.exists_addEquiv_symplecticCoords_orientedModel.coords D W X e.symm (-1) (neg_ne_zero.2 one_ne_zero)
  obtain ⟨cB, hcB⟩ := GlobalTheory.Twist.exists_addEquiv_symplecticCoords_orientedModel.coords D W₁ X e.symm 1 one_ne_zero
  have gX := GlobalTheory.RouteCoords.gram_det_ne X
  have dV : Γ.V.J.det ≠ 0 := by rw [hR.JW, one_smul]; exact GlobalTheory.RouteCoords.gram_det_ne _
  have dV' : Γ.V'.J.det ≠ 0 := by
    rw [hR.JW₁, det_smul]
    exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) (GlobalTheory.RouteCoords.gram_det_ne _)
  have dW : Γ.W.J.det ≠ 0 := by
    rw [hR.JX, det_smul, det_submatrix_equiv_self, det_transpose]
    exact mul_ne_zero (pow_ne_zero _ GlobalTheory.ChiGrid.cmHost_imaginaryGenerator_ne_zero) gX
  refine ⟨om, om', R, Rf, hm, _, _, _, _,
    ⟨hωA, hωB, ir, ⟨sA.1, sA.2, oA, iA, lA, fA, dA⟩, ⟨sB.1, sB.2, oB, iB, lB, fB, dB⟩⟩, fun f₀ g1 P => ?_, fun f₀ g2 P => ?_⟩
  · obtain ⟨a1, a2, -⟩ := fock_datum hθ true A B e.symm Bs hT₀.base hR.JW hR.JX hg.hV hg.hW
      (fun w => by
        obtain ⟨τ, a, b, -, d⟩ := hR.cart w
        exact ⟨τ, a, b.trans (one_smul _ _).symm, d⟩) Γ.M hg.hM cA hcA g1
    obtain ⟨f, hf, hPf⟩ := a2 P
    refine ⟨R.p f, fun φ p1 F kA => ?_⟩
    have p2 : ∀ᶠ v in Filter.cofinite, φ v = Γ.M.vac v := Xc.T.eventually_cofinite_notMem.mono p1.2
    have hcA' : ∀ u, cA u = (HMul.hMul (uᵀ.submatrix e.symm id) (incM (sgn true W).gram) :
        Matrix (Fin X.rank) (Fin W.rank) (AE D)) := fun u => by rw [hcA, neg_one_smul]; rfl
    replace kA : IsDatum Γ.M Bs.ψ cA (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₀ φ) F := ⟨kA.1, fun u => by rw [hcA']; exact kA.2 u⟩
    have mA := thetaLift_pure Γ.M hg.hM hT₀.base.std dV dW (GlobalTheory.RouteCoords.gram_det_ne (sgn true W)) e Bs.emb R.p Rf.p
      (vacIm Γ Rf) (Filter.Eventually.of_forall fun _ => rfl) hf p1.1 p2
    have eA := eq_thO Γ.M Bs.ψ e (GlobalTheory.RouteCoords.gram_det_ne (sgn true W)) cA hcA' (hPf φ p1.1 p2 _ kA)
    refine ⟨a1 φ p1.1 p2 _ kA, ?_⟩
    rw [eA]
    exact mA
  · obtain ⟨b1, b2, -⟩ := fock_datum hθ false A₁ B e.symm Bs hT₀.base hR.JW₁ hR.JX hg.hV' hg.hW
      (fun w => by
        obtain ⟨τ, a, -, c, d⟩ := hR.cart w
        exact ⟨τ, a, c.trans (neg_one_smul _ _).symm, d⟩) Γ.M' hg.hM' cB hcB g2
    obtain ⟨f', hf', hP'⟩ := b2 P
    refine ⟨R.p' f', fun φ' q1 F kB => ?_⟩
    have q2 : ∀ᶠ v in Filter.cofinite, φ' v = Γ.M'.vac v := Xc.T.eventually_cofinite_notMem.mono q1.2
    have hcB' : ∀ u, cB u = (HMul.hMul (uᵀ.submatrix e.symm id) (incM W₁.gram) :
        Matrix (Fin X.rank) (Fin W₁.rank) (AE D)) := fun u => by rw [hcB, one_smul]
    replace kB : IsDatum Γ.M' Bs.ψ cB (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₀ φ') F := ⟨kB.1, fun u => by rw [hcB']; exact kB.2 u⟩
    have mB := thetaLift_pure Γ.M' hg.hM' hT₀.base.std dV' dW (GlobalTheory.RouteCoords.gram_det_ne W₁) e Bs.emb R.p' Rf.p'
      (vacIm Γ Rf) (Xc.T.eventually_cofinite_notMem.mono fun v hv => (hm.fin.sph v hv).1.symm) hf' q1.1 q2
    have eB := eq_thO Γ.M' Bs.ψ e (GlobalTheory.RouteCoords.gram_det_ne W₁) cB hcB' (hP' φ' q1.1 q2 _ kB)
    refine ⟨b1 φ' q1.1 q2 _ kB, ?_⟩
    rw [eB]
    exact mB
end GlobalTheory.TopFlip
end
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory Matrix
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm GlobalTheory.BigNZ GlobalTheory.FlipMatch GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB incM)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW psiLoc chrW)
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
namespace GlobalTheory.TopFlip
variable {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {μ₀ : T}
end GlobalTheory.TopFlip
end
end
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory Matrix
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm GlobalTheory.BigNZ GlobalTheory.FlipMatch GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB incM)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW psiLoc chrW)
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
namespace GlobalTheory.TopFlip
variable {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {μ₀ : T}
set_option maxHeartbeats 1600000 in
theorem thetaFlip_tuple_match (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (hTL : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching) (hL : L.Is μ₀) (W : G.Weil) (i j : Fin D.R.m)
    {A : Fr (spW G i j)} {A₁ : Fr (spW₁ G i j)} {AV : Fr (spV G i j)} {AV₁ : Fr (spV₁ G i j)} (hA : IsGridFr W _ A)
    (hA₁ : IsGridFr W _ A₁) (hV : IsGridFr W _ AV) (hV₁ : IsGridFr W _ AV₁) (t : T) (B : Frames G) (ρ : RealMatch W) (M : Vol G)
    (hst : SquareStanding G t) (hM : M.Is t) {ωA ωB}
    (hωA : GlobalTheory.Grid.IsWeil W.ψ true _ _ (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j / GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j) ωA)
    (hωB : GlobalTheory.Grid.IsWeil W.ψ false _ _ (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j / GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j) ωB) :
    ∃ Pi rf rl p p', IsMatch W.ψ W.θ A A₁ (frSum AV AV₁) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j) ωA ωB Pi rf rl p p' ∧
      ∀ ε, IsIdemSum ε (locPl G t) → ∀ Ξ Ψ (u : Pl D.host.E → ℂ) F F',
        (∀ w ∈ locPl G t, Ξ w ∈ GlobalTheory.WeilM.SB _ ∧ Ψ w ∈ GlobalTheory.WeilM.SB _ ∧ zetaA G t i j w (Ξ w) = u w • zetaB G t i j w (Ψ w)) →
        IsLinA B t i j ρ ε Ξ F → IsLinB B t i j ρ ε Ψ F' →
        ∀ n Φ (τ : TotT G (routeBig t i j)) (τ' : TotT G (routeSmall t i j)),
        (∀ w ∈ locPl G t, depthAt G w ≤ n w ∧ IsNatDatum (unifAt w) (n w) (Φ w)) → HasFlip B t ρ i j n Φ τ τ' →
        IsFinF W.ψ W.θ true A (frSum AV AV₁) F ∧ IsFinF W.ψ W.θ false A₁ (frSum AV AV₁) F' ∧
        IsFinF W.ψ W.θ true A (frSum AV AV₁) (datumA W τ) ∧ IsFinF W.ψ W.θ false A₁ (frSum AV AV₁) (datumB W τ') ∧
        ∀ P P' (g : ℂ), p' (fockF W.ψ W.θ false A₁ (frSum AV AV₁) F' P') ≠ 0 →
          p (fockF W.ψ W.θ true A (frSum AV AV₁) F P) = g • p' (fockF W.ψ W.θ false A₁ (frSum AV AV₁) F' P') →
          ((∏ w ∈ locPl G t, u w) * ((∏ w ∈ locPl G t, levVol G t i j w : ℝ) : ℂ)) •
              p (fockF W.ψ W.θ true A (frSum AV AV₁) (datumA W τ) P) =
            g • p' (fockF W.ψ W.θ false A₁ (frSum AV AV₁) (datumB W τ') P') := by
  have hT := (GlobalTheory.SquareDict.dict hL W t i j A A₁ AV AV₁ hA hA₁ hV hV₁).1 hst M hM
  obtain ⟨e, Bs, Γ, X, om₀, om₀', h, hT₀, hti⟩ := exists_tiedBoth hL W t i j hst M hM
  have hR : GlobalTheory.TripleRead.IsReading W.ψ A A₁ (frSum AV AV₁) _ _ (e.symm.trans finSumFinEquiv) Bs Γ X :=
    ⟨h.ψ, h.JW, h.JW₁, by
      rw [h.JWW, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.skewGram, ← GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk_transpose, ← GlobalTheory.SquareIdent.blkMat_submatrix, GlobalTheory.Doubling.gram_hsum]
      rfl, fun w => by
      obtain ⟨τ, a, b, c, d⟩ := h.cart w
      refine ⟨τ, a, b.trans (hA τ).2.symm, c.trans (congrArg Neg.neg (hA₁ τ).2.symm), d.trans ?_⟩
      rw [GlobalTheory.SquareAlg.cart_frSum, (hV τ).2, (hV₁ τ).2, ← GlobalTheory.SquareIdent.blkMat_submatrix], h.α, h.β⟩
  obtain ⟨om, om', R, Rf, hm, rf, rl, p, p', hM', HA, HB⟩ :=
    _root_.GlobalTheory.TopFlip.thetaFlip_tensor_match hP.howeDualityReal hP hTL W.θ_is A A₁ _ hT hωA hωB hR hT₀
  have hT' := hm.triple
  have H := fun (w : Pl D.host.E) (hw : w ∈ locPl G t) => local_charts hL W B t i j M hst h hm hti hw
  choose! ιA ι ιB ι' l hl h1 h2 h3 h4 h5 h6 h7 using H
  obtain ⟨f, -, f2, f3⟩ := GlobalTheory.T.exists_gaussianVacuum_product_unitVacua hL W ρ t i j M hst e Bs Γ X om om' h hT' hti.1
  obtain ⟨f', -, g2, g3⟩ := GlobalTheory.T.unitVacua_product_eq_gaussianDatum_smallModel hL W ρ t i j M hst e Bs Γ X om om' h hT' hti
  obtain ⟨hs, a⟩ := mixglobA hL W B ρ t i j M hst e Bs Γ X om om' h hT' hti.1 f f3 ι h3
  obtain ⟨hs', b⟩ := mixglobB hL W B ρ t i j M hst e Bs Γ X om om' h hT' hti f' g3 ι' h4
  have vA : ∏ w ∈ locPl G t, ιA w (Γ.M.vac _) 0 = ∏ w ∈ locPl G t, ι w (Γ.M.vac _) 0 := Finset.prod_congr rfl fun w hw => by
    have k := GlobalTheory.T.mixedModel_vacuum_eq_integralMatrix_indicator hL W B t i j M hst e Bs Γ X om om' h hT' hti.1 w hw _ (h3 w hw)
    have k2 := fourierSum_ind (A := Fin ((locGrid G t w).rank (i + 1, j + 1))) (psiAt W w)⁻¹ (isUnif_unifAt w)
      (Assignment.one.block (Fin ((locGrid G t w).rank (i, j + 1))) (Fin ((locGrid G t w).rank (i + 1, j))))ᶜ (ι w (Γ.M.vac _) 0)
    rw [← k] at k2
    rw [h5 w hw _ (hT'.geo.hM.vac _).1 0 k2.1, k2.2]
  have vB : ∏ w ∈ locPl G t, ιB w (Γ.M'.vac _) 0 = ∏ w ∈ locPl G t, ι' w (Γ.M'.vac _) 0 := Finset.prod_congr rfl fun w hw => by
    have k := GlobalTheory.T.mixedModel_vacuum_eq_smul_integralMatrix_indicator hL W B t i j M hst e Bs Γ X om om' h hT' hti w hw _ (h4 w hw)
    have k2 := fourierSum_ind (A := Fin ((locGrid G t w).rank (i, j))) (psiAt W w) (isUnif_unifAt w)
      (Assignment.one.block (Fin ((locGrid G t w).rank (i, j + 1))) (Fin ((locGrid G t w).rank (i + 1, j)))) (ι' w (Γ.M'.vac _) 0)
    rw [← k] at k2
    rw [h6 w hw _ (hT'.geo.hM'.vac _).1 0 k2.1, k2.2]
  have la := GlobalTheory.T.negW_local_functions_theta_pure_tensor hL W B t i j M hst e Bs Γ X om om' h hT' hti.1 ρ f
    (datumA_vac ρ i j t ▸ GlobalTheory.SquareIdent.isDatum_of_isDatumA f3) ιA h1
  have lb := GlobalTheory.TopFlip.LinSmall.isDatum_linB hL W B t i j M hst e Bs Γ X om om' h hT' hti ρ f'
    (datumB_vac ρ i j t ▸ GlobalTheory.SquareIdent.isDatum_of_isDatumB g3) ιB h2
  rw [vA] at la
  rw [vB] at lb
  refine ⟨_, rf, rl, p, p', hM', fun ε hε Ξ Ψ u F F' hΞ hF hF' n Φ τ τ' hn ⟨ε', hε', c, d⟩ => ?_⟩
  have hf : ∀ w ∈ locPl G t, IsNatDatum (unifAt w) (n w) (flipAt W t i j w (n w) (Φ w)) := fun w hw =>
    LocTensor.isNatDatum_flipAt hL W i j hw (notMem_of_standing hst hw) (hn w hw).1 (hn w hw).2
  have hinj : ∀ w ∈ locPl G t, ∀ w' ∈ locPl G t, w.under (𝓞 D.host.F) = w'.under (𝓞 D.host.F) → w = w' :=
    fun w hw w' hw' e => Good.under_injOn hL G t hw hw' e
  obtain ⟨φ, p1, p2⟩ := exists_finPart hT'.geo.hM hti.1.2.2.1 hinj (fun w φ => ι w φ = flipAt W t i j w (n w) (Φ w))
    fun w hw => (h3 w hw).1.2.2 (mem_SB_of_isNatDatum (hf w hw))
  obtain ⟨φ', q1, q2⟩ := exists_finPart hT'.geo.hM' hti.1.2.2.1 hinj (fun w φ => ι' w φ = Φ w)
    fun w hw => (h4 w hw).1.2.2 (mem_SB_of_isNatDatum (hn w hw).2)
  obtain ⟨χ, r1, r2⟩ := exists_finPart hT'.geo.hM hti.1.2.2.1 hinj (fun w φ => ιA w φ = Ξ w)
    fun w hw => (h1 w hw).1.2.2 (hΞ w hw).1
  obtain ⟨χ', s1, s2⟩ := exists_finPart hT'.geo.hM' hti.1.2.2.1 hinj (fun w φ => ιB w φ = Ψ w)
    fun w hw => (h2 w hw).1.2.2 (hΞ w hw).2.1
  have dA := GlobalTheory.SquareIdent.isDatum_of_isDatumA (a ε' hε' n _ τ hf d φ p1 p2)
  have dB := GlobalTheory.SquareIdent.isDatum_of_isDatumB (b ε' hε' n _ τ' (fun w hw => (hn w hw).2) c φ' q1 q2)
  have dF := la ε hε Ξ F hF χ r1 r2
  have dF' := lb ε hε Ψ F' hF' χ' s1 s2
  have gA := isGauss_smul f2 hs
  have gB := isGauss_smul g2 hs'
  have y₀ := pureT_loc hL hm hti.1 r1 s1 (c := fun w => l w * u w) fun w hw =>
    h7 w hw _ (r1.1 _) _ (s1.1 _) _ (by rw [r2 w hw, s2 w hw]; exact (hΞ w hw).2.2)
  have y₁ := pureT_loc hL hm hti.1 p1 q1 (c := fun w => l w * ((levVol G t i j w : ℝ) : ℂ)⁻¹) fun w hw =>
    h7 w hw _ (p1.1 _) _ (q1.1 _) _ (by
      rw [h5 w hw _ (p1.1 _) (n w) (by rw [p2 w hw]; exact hf w hw), h6 w hw _ (q1.1 _) (n w) (by rw [q2 w hw]; exact (hn w hw).2),
        p2 w hw, q2 w hw]
      exact (zeta_flip hL W i j hst hw).2 _ _ (hn w hw).1 (hn w hw).2)
  obtain ⟨_, k1⟩ := HA _ gA 0
  obtain ⟨_, k2⟩ := HB _ gB 0
  refine ⟨(k1 _ r1 _ dF).1, (k2 _ s1 _ dF').1, (k1 _ p1 _ dA).1, (k2 _ q1 _ dB).1, fun P P' g hne hg => ?_⟩
  obtain ⟨x, hx⟩ := HA _ gA P
  obtain ⟨y, hy⟩ := HB _ gB P'
  rw [(hy _ s1 _ dF').2] at hne hg
  rw [(hx _ r1 _ dF).2, y₀] at hg
  rw [(hx _ p1 _ dA).2, (hy _ q1 _ dB).2, y₁]
  generalize (GlobalTheory.SmallThetaModules.pureT (GlobalTheory.TripleAssembly.vacIm Γ Rf) fun v => Rf.p' v (χ' v)) = z₀ at hne hg
  generalize (GlobalTheory.SmallThetaModules.pureT (GlobalTheory.TripleAssembly.vacIm Γ Rf) fun v => Rf.p' v (φ' v)) = z
  have hz : z₀ ≠ 0 := fun h0 => hne (by rw [h0, TensorProduct.tmul_zero])
  obtain ⟨lz, hlz⟩ := Module.Projective.exists_dual_eq_one ℂ hz
  have e1 : (∏ w ∈ locPl G t, l w * u w) • x = g • y := by
    have := congrArg (TensorProduct.rid ℂ R.Pi ∘ LinearMap.lTensor R.Pi lz) hg
    simpa [hlz] using this
  have hV : ((∏ w ∈ locPl G t, levVol G t i j w : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun w hw => (zeta_flip hL W i j hst hw).1)
  have e2 : (∏ w ∈ locPl G t, u w) * ((∏ w ∈ locPl G t, levVol G t i j w : ℝ) : ℂ) *
      ∏ w ∈ locPl G t, l w * ((levVol G t i j w : ℝ) : ℂ)⁻¹ = ∏ w ∈ locPl G t, l w * u w := by
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_inv_distrib, ← Complex.ofReal_prod]
    field_simp
  change _ • (x ⊗ₜ[ℂ] (_ • z) : GlobalTheory.TripleAssembly.PiT R Γ Rf) = g • (y ⊗ₜ[ℂ] z : GlobalTheory.TripleAssembly.PiT R Γ Rf)
  rw [TensorProduct.tmul_smul, smul_smul, e2, TensorProduct.smul_tmul', e1, TensorProduct.smul_tmul']
end GlobalTheory.TopFlip
end
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.ConstRatio (Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
namespace GlobalTheory.TopFlip
private theorem away_imaginary_inv {D : D7} {m : ℕ} {z : ℂ} (h : GlobalTheory.KappaArith.AwayIm D m z) : GlobalTheory.KappaArith.AwayIm D m z⁻¹ := by
  obtain ⟨ζ, ⟨a, k, k', ⟨b, hb⟩, ha⟩, rfl⟩ := h
  refine ⟨ζ⁻¹, ?_, map_inv₀ _ _⟩
  by_cases hm : m = 0
  · subst hm
    exact ⟨0, 1, 1, by simp, by simp⟩
  have hm' : (m : D.what₂.LL) ≠ 0 := Nat.cast_ne_zero.2 hm
  have hb' : (m : D.what₂.LL) ^ k' = (a : D.what₂.LL) * (b : D.what₂.LL) := by exact_mod_cast congrArg (fun x : 𝓞 D.what₂.LL => (x : D.what₂.LL)) hb
  have hζ : ζ ≠ 0 := fun h0 => pow_ne_zero k' hm' (by rw [hb', ← ha, h0, zero_mul, zero_mul])
  refine ⟨b * (m : 𝓞 D.what₂.LL) ^ k, k', k' + k, ⟨a, by rw [pow_add, hb]; ring⟩, ?_⟩
  have e : ((b * (m : 𝓞 D.what₂.LL) ^ k : 𝓞 D.what₂.LL) : D.what₂.LL) = (b : D.what₂.LL) * (m : D.what₂.LL) ^ k := by push_cast; rfl
  rw [e, hb', ← ha]
  field_simp
private theorem fock_move_relation {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hθ : IsInfFam θ) {W W₁ X : HSp D} {A : Fr W}
    {A₁ : Fr W₁} {B : Fr X} {α β : (AE D)ˣ →* Circle} {ωA ωB Pi rf rl p p'} (hm : IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p')
    {h : GA D X} (hh : h ∈ GfC X) {f f'} (hf : IsFinF ψ θ true A B f) (hf' : IsFinF ψ θ false A₁ B f') {a b : ℂ} (hb : b ≠ 0)
    {P P'} {g : ℂ} (hne : p' (fockF ψ θ false A₁ B f' P') ≠ 0)
    (hg : p (fockF ψ θ true A B f P) = g • p' (fockF ψ θ false A₁ B f' P')) :
    p' (fockF ψ θ false A₁ B (b⁻¹ • ωB (1, h) f') P') ≠ 0 ∧
      p (fockF ψ θ true A B (a • ωA (1, h) f) P) = (a * g * b) • p' (fockF ψ θ false A₁ B (b⁻¹ • ωB (1, h) f') P') := by
  have mA : fockF ψ θ true A B f P ∈ algF ψ θ true A B := Submodule.subset_span ⟨_, _, hf, rfl⟩
  have mB : fockF ψ θ false A₁ B f' P' ∈ algF ψ θ false A₁ B := Submodule.subset_span ⟨_, _, hf', rfl⟩
  rw [om_fockF hθ A B hm.weilA hh hf, om_fockF hθ A₁ B hm.weilB hh hf', map_smul, map_smul, hm.mapA.eqf h hh _ mA, hg, map_smul,
    hm.mapB.eqf h hh _ mB]
  refine ⟨smul_ne_zero (inv_ne_zero hb) fun h0 => hne ?_, ?_⟩
  · have e := hm.mapB.eqf h⁻¹ (inv_mem hh) _ (hm.mapB.stabX.1 h hh _ mB)
    rw [hm.mapB.eqf h hh _ mB, h0, map_zero, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, inv_mul_cancel, one_mul,
      ← Prod.one_eq_mk, map_one, Module.End.one_apply] at e
    exact e
  · rw [smul_smul, smul_smul, mul_assoc, mul_inv_cancel₀ hb, mul_one]
end GlobalTheory.TopFlip
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaFlip_involutive_correspondence : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) → NumbersIn D.what₂.embLL S μ₀ → ∀ (ρ : RealMatch W) (i j : Fin D.R.m) (X : TriG G i j), TopGrid W i j X → IsStageC W i j (pp D j) (qq D j) X →
    ∀ (A : Fr (G.V (.grid (i + 1) (j + 1)))) (A₁ : Fr (G.V (.grid i j))) (AV : Fr (G.V (.grid i (j + 1)))) (AV₁ : Fr (G.V (.grid (i + 1) j))), IsGridFr W _ A → IsGridFr W _ A₁ → IsGridFr W _ AV → IsGridFr W _ AV₁ →
    ∃ κ : T → ℂ, (∀ t, κ t ≠ 0 ∧ ∃ ζ : D.what₂.LL, GlobalTheory.Square.IsAwayUnit (Qn G t) ζ ∧ κ t = D.what₂.embLL ζ * κ μ₀) ∧
      ∀ (t : T) (M : Vol G), M.Is t → ∀ s s' : NNReal, M.ν (.grid (i + 1) (j + 1)) = s • X.m → M.ν (.grid i j) = s' • X.m' →
      ∀ Pi rf rl p p', IsMatch W.ψ W.θ A A₁ (frSum AV AV₁) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j) (X.ω t) (X.ω' t) Pi rf rl p p' →
      ∀ n Φ (τ : TotT G (routeBig t i j)) (τ' : TotT G (routeSmall t i j)), (∀ w ∈ locPl G t, depthAt G w ≤ n w ∧ IsNatDatum (unifAt w) (n w) (Φ w)) → HasFlip S.B t ρ i j n Φ τ τ' →
      ∀ P P' (g : ℂ), p' (fockF W.ψ W.θ false A₁ (frSum AV AV₁) (X.f' t) P') ≠ 0 →
        p (fockF W.ψ W.θ true A (frSum AV AV₁) (X.f t) P) = g • p' (fockF W.ψ W.θ false A₁ (frSum AV AV₁) (X.f' t) P') →
        ((s : ℝ) : ℂ) • p (fockF W.ψ W.θ true A (frSum AV AV₁) (datumA W τ) P) =
          (κ t * ((s' : ℝ) : ℂ) * g) • p' (fockF W.ψ W.θ false A₁ (frSum AV AV₁) (datumB W τ') P') := by
  intro hP hK hM
  obtain ⟨F1, H1⟩ := _root_.GlobalTheory.T.theta_parameter_dictionary_bijective hP
  obtain ⟨F2, H2⟩ := _root_.GlobalTheory.T.theta_stage_unique hP hK hM
  refine ⟨max F1 F2, fun ε CF hCF => ?_⟩
  obtain ⟨C1, x1, H1⟩ := H1 ε CF (le_of_max_le_left hCF)
  obtain ⟨C2, x2, H2⟩ := H2 ε CF (le_of_max_le_right hCF)
  refine ⟨max C1 C2, max x1 x2, fun C hC D large₂ he hx hR T Lc μ₀ hL G => ?_⟩
  replace H1 := H1 C (le_of_max_le_left hC) D large₂ he (le_of_max_le_left hx) hR T Lc μ₀ hL G
  replace H2 := H2 C (le_of_max_le_right hC) D large₂ he (le_of_max_le_right hx) hR T Lc μ₀ hL G
  have hst : ∀ t, SquareStanding G t := fun t => GlobalTheory.ThetaRegularizationComparison.standing hR hR.size.2.1.eleven_le hL G t
  intro W S hψ hN ρ i j X hTG hSC A A₁ AV AV₁ hA hA₁ hV hV₁
  obtain ⟨σ, σ', hσ⟩ := H1 W i j X hTG hSC A A₁ AV AV₁ hA hA₁ hV hV₁
  replace H2 := H2 W i j _ _ _ _ _ X hSC A A₁ (frSum AV AV₁)
  have hIs := hSC.2.2.2.2.2.2.2
  have hrk : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.eps G i j = rankV D i j % 2 := congrArg (· % 2) (Nat.add_right_cancel hSC.2.2.2.1)
  have eα : ∀ t, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j = Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2) := fun t => by
    rw [← hrk]; rfl
  have eβ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j = G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2) := by
    rw [← hrk]; rfl
  have hI : X.Is W.ψ W.θ (fun t => GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j) (fun _ => GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j) (fun t => nuH G t i j)
      (locPl G) := by
    simp only [eα, eβ]
    exact hIs
  obtain ⟨h, hh, cA, cB, y, hcA, hcB, hmv⟩ := GlobalTheory.TopFlip.exists_move hL hst S.B ρ hTG hI hV hV₁
  obtain ⟨x, hx⟩ := GlobalTheory.TopFlip.zeta_std hL W S.B X hst (hTG.1 ▸ hI.rigA.2.1) (hTG.2.1 ▸ hI.rigA'.2.1)
    (by have := hI.rigW.2.1; rwa [hTG.2.2.1] at this)
  obtain ⟨s₀, hs₀, hs⟩ := GlobalTheory.TopFlip.MeasW.exists_ratio (G := G) hL i j X.m hI.meas.1
  obtain ⟨c₁, hc₁, hc⟩ := GlobalTheory.TopFlip.MeasLevel.measure_mul_levVol (G := G) hL hst i j X.m' hI.meas'.1
  set u : T → ℂ := fun t => ∏ w ∈ locPl G t, (((locGrid G t w).nu i j (x w) : ℂˣ) : ℂ) with hu
  have hu0 : ∀ t, u t ≠ 0 := fun t => Finset.prod_ne_zero_iff.2 fun w _ => Units.ne_zero _
  have hξ0 : ∀ t, ((Lc.xi t y : Circle) : ℂ) ≠ 0 := fun t => Circle.coe_ne_zero _
  have hs₀' : ((s₀ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs₀
  have hc₁' : (c₁ : ℂ) ≠ 0 := by exact_mod_cast hc₁
  refine ⟨fun t => ((s₀ : ℝ) : ℂ) * cA⁻¹ * cB * (c₁ : ℂ)⁻¹ * ((Lc.xi t y : Circle) : ℂ) * (u t)⁻¹, fun t => ⟨?_, ?_⟩, ?_⟩
  · exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hs₀' (inv_ne_zero hcA)) hcB) (inv_ne_zero hc₁')) (hξ0 t))
      (inv_ne_zero (hu0 t))
  · obtain ⟨z, hz, ez⟩ := GlobalTheory.TopFlipNu.nu_arith hL hN.chars i j x t fun w hw => (hx t w hw).1
    obtain ⟨ζ, h1, h2⟩ := ((GlobalTheory.XiAway.xi_awayIm hL t (hN.chars.xi t) (Qn G t) y).mul
      (GlobalTheory.TopFlip.away_imaginary_inv (GlobalTheory.XiAway.xi_awayIm hL μ₀ (hN.chars.xi μ₀) (Qn G t) y))).mul (GlobalTheory.TopFlip.away_imaginary_inv hz)
    refine ⟨ζ, h1, ?_⟩
    have e : u t = z * u μ₀ := ez
    have := hξ0 μ₀
    dsimp only
    rw [h2, e, mul_inv]
    field_simp
  intro t M hM' s s' es es' Pi rf rl p p' hm n Φ τ τ' hn hfl P P' g hne hg
  obtain ⟨Pi₀, rf₀, rl₀, p₀, p₀', hm₀, H⟩ := _root_.GlobalTheory.TopFlip.thetaFlip_tuple_match hP hM hL W i j hA hA₁ hV hV₁ t S.B ρ M (hst t) hM'
    (hI.weil t) (hI.weil' t)
  obtain ⟨f1, f2, f3, f4, H⟩ := H _ (hI.idem t) _ _ _ _ _ (fun w hw => (hx t w hw).2) (hmv t).1 (hmv t).2 n Φ τ τ' hn hfl
  obtain ⟨E, c, hc0, eA, eB⟩ := H2 t Pi₀ rf₀ rl₀ p₀ p₀' Pi rf rl p p' (by rw [← eα, ← eβ]; exact hm₀) (by rw [← eα, ← eβ]; exact hm)
  obtain ⟨k1, k2⟩ := GlobalTheory.TopFlip.fock_move_relation W.θ_is hm hh (hσ t).1 (hσ t).2.1 (a := cA⁻¹) (mul_ne_zero hcB (hξ0 t)) hne hg
  rw [eB _ (Submodule.subset_span ⟨_, _, f2, rfl⟩)] at k1 k2
  rw [eA _ (Submodule.subset_span ⟨_, _, f1, rfl⟩)] at k2
  have k3 := H P P' (c⁻¹ * (cA⁻¹ * g * (cB * ((Lc.xi t y : Circle) : ℂ)))) (fun h0 => k1 (by rw [h0, map_zero]))
    (E.injective (by rw [map_smul, mul_smul, ← k2, smul_smul, inv_mul_cancel₀ hc0, one_smul]))
  rw [eA _ (Submodule.subset_span ⟨_, _, f3, rfl⟩), eB _ (Submodule.subset_span ⟨_, _, f4, rfl⟩)]
  have e1 : s = s₀ := hs t M hM' s es
  have e2 : ((s' : ℝ) : ℂ) * ((∏ w ∈ locPl G t, GlobalTheory.TopFlip.levVol G t i j w : ℝ) : ℂ) = c₁ := by exact_mod_cast hc t M hM' s' es'
  have k4 := congrArg E k3
  rw [map_smul, map_smul] at k4
  change (u t * _) • _ = _ at k4
  generalize ((∏ w ∈ locPl G t, GlobalTheory.TopFlip.levVol G t i j w : ℝ) : ℂ) = V at e2 k4
  have hV0 : V ≠ 0 := fun h0 => hc₁' (by rw [← e2, h0, mul_zero])
  have hs' : ((s' : ℝ) : ℂ) ≠ 0 := fun h0 => hc₁' (by rw [← e2, h0, zero_mul])
  have := hu0 t
  rw [(eq_inv_smul_iff₀ (mul_ne_zero this hV0)).2 k4, smul_smul, smul_smul, smul_smul, e1, ← e2]
  congr 1
  field_simp
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.ConstRatio (Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
noncomputable section
namespace GlobalTheory.ThetaRegularizationComparison
open GlobalTheory.RegCompare in
theorem regularised_thetaInt_comparison_smul (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (hK : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree) (hTA : GlobalTheory.SquareSt.ThetaIntegralsAgree)
    {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hθ : IsInfFam θ) {W W₁ X : HSp D} {A : Fr W} {A₁ : Fr W₁} {B : Fr X}
    {α β : (AE D)ˣ →* Circle} (hT : IsTriple W W₁ X α β) {ν 𝓕 ν₁ 𝓕₁} (hν : IsHaarFD W ν 𝓕) (hν₁ : IsHaarFD W₁ ν₁ 𝓕₁)
    {ωA ωB Pi rf rl p p'} (hm : IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p') :
    ∃ c : ℂ, c ≠ 0 ∧ (∀ Φ ∈ algF ψ θ true A B, p Φ = 0 → thetaInt ωA ν 𝓕 Φ = 0) ∧
      ∀ Φ ∈ algF ψ θ true A B, ∀ Φ' ∈ algF ψ θ false A₁ B, ∀ g : ℂ, p Φ = g • p' Φ' →
        (∃ z, zdeg z ≠ 0 ∧ Intg ωB ν₁ 𝓕₁ (wop ωB z Φ') ∧
          zdeg z • thetaInt ωA ν 𝓕 Φ = (c * g) • thetaInt ωB ν₁ 𝓕₁ (wop ωB z Φ')) ∧
        (Intg ωB ν₁ 𝓕₁ Φ' → thetaInt ωA ν 𝓕 Φ = (c * g) • thetaInt ωB ν₁ 𝓕₁ Φ') := by
  obtain ⟨c, hc0, hc⟩ := _root_.GlobalTheory.RegCompare.regularised_integral_comparison hP hK hTA D ψ θ hθ W W₁ X A A₁ B α β hT ν 𝓕 ν₁ 𝓕₁ hν hν₁ ωA ωB Pi rf rl p p' hm
  have kill : ∀ Φ ∈ algF ψ θ true A B, p Φ = 0 → thetaInt ωA ν 𝓕 Φ = 0 := fun Φ hΦ h0 => by
    obtain ⟨z', -, -, -, -, hz'⟩ := hc 0 (Submodule.zero_mem _)
    have h2 := thetaInt_smul ωB ν₁ 𝓕₁ 0 0
    rw [zero_smul, zero_smul] at h2
    rw [hz' _ hΦ (by rw [h0, map_zero, smul_zero]), map_zero, h2, smul_zero]
  refine ⟨c, hc0, kill, fun Φ hΦ Φ' hΦ' g hg => ?_⟩
  obtain ⟨z, -, hz0, -, hzM, hz⟩ := hc Φ' hΦ'
  have hI : zdeg z • thetaInt ωA ν 𝓕 Φ = (c * g) • thetaInt ωB ν₁ 𝓕₁ (wop ωB z Φ') := by
    by_cases h0 : g = 0
    · rw [kill Φ hΦ (by rw [hg, h0, zero_smul]), h0, mul_zero, zero_smul, smul_zero]
    · have h1 := hz ((zdeg z * g⁻¹) • Φ) (Submodule.smul_mem _ _ hΦ)
        (by rw [map_smul, hg, smul_smul, mul_assoc, inv_mul_cancel₀ h0, mul_one])
      rw [thetaInt_smul] at h1
      rw [mul_comm c, mul_smul, ← h1, smul_smul, mul_left_comm, mul_inv_cancel₀ h0, mul_one]
  refine ⟨⟨z, hz0, intg_of_modInt hzM, hI⟩, fun hi => ?_⟩
  rw [thetaInt_wop_intg hν₁ (GlobalTheory.T.thetaKernel_leftInvariant_rational_unitary D ψ θ hθ W₁ X A₁ B _ _ ωB hm.weilB Φ' hΦ') hi z, smul_comm] at hI
  exact smul_right_injective _ hz0 hI
set_option maxHeartbeats 1000000 in
theorem regulator_constant_eq : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) → NumbersIn D.what₂.embLL S μ₀ → ∀ (ρ : RealMatch W), ρ.Tied → ∀ (i j : Fin D.R.m) (X : TriG G i j) (lam : T → ℂ),
    TopGrid W i j X → IsStageC W i j (pp D j) (qq D j) X → Factor X W.ψ W.θ lam →
    ∃ κ : T → ℂ, (∀ t, κ t ≠ 0 ∧ ∃ ζ : D.what₂.LL, GlobalTheory.Square.IsAwayUnit (Qn G t) ζ ∧ κ t = D.what₂.embLL ζ * κ μ₀) ∧
      ∀ (t : T) (c₀ : ℂ), RegConst W S.B ρ t i j c₀ → c₀ = κ t * lam t := by
  intro hP hK hM
  have hLM := _root_.GlobalTheory.T.twisted_local_factors_match hP.howeDualityReal hP hK hM
  have hTA := _root_.GlobalTheory.T.twisted_square_theta_integrals_eq hP hK hM
  obtain ⟨F1, H1⟩ := _root_.GlobalTheory.T.theta_parameter_dictionary_bijective hP
  obtain ⟨F2, H2⟩ := _root_.GlobalTheory.T.thetaFlip_involutive_correspondence hP hK hM
  obtain ⟨F3, H3⟩ := _root_.GlobalTheory.T.theta_finiteData_match_each_stage hP hK hM
  refine ⟨max F1 (max F2 F3), fun ε CF hCF => ?_⟩
  obtain ⟨C1, x1, H1⟩ := H1 ε CF (le_of_max_le_left hCF)
  obtain ⟨C2, x2, H2⟩ := H2 ε CF (le_of_max_le_left (le_of_max_le_right hCF))
  obtain ⟨C3, x3, H3⟩ := H3 ε CF (le_of_max_le_right (le_of_max_le_right hCF))
  refine ⟨max C1 (max C2 C3), max (max x1 x2) (max x3 ((12 : ℝ) ^ (5 / ε))), fun C hC D large₂ he hx hR T Lc μ₀ hL G => ?_⟩
  replace H1 := H1 C (le_of_max_le_left hC) D large₂ he (le_of_max_le_left (le_of_max_le_left hx)) hR T Lc μ₀ hL G
  replace H2 := H2 C (le_of_max_le_left (le_of_max_le_right hC)) D large₂ he (le_of_max_le_right (le_of_max_le_left hx)) hR T Lc μ₀ hL G
  replace H3 := H3 C (le_of_max_le_right (le_of_max_le_right hC)) D large₂ he (le_of_max_le_left (le_of_max_le_right hx)) hR T Lc μ₀ hL G
  have hst : ∀ t, SquareStanding G t :=
    standing hR hR.size.2.1.eleven_le hL G
  intro W S hψ hN ρ hρ i j X lam hTG hSC hF
  have hbig : Node.InRange D.R.m (.grid (i + 1) (j + 1)) := ⟨i.2, j.2⟩
  have hsm : Node.InRange D.R.m (.grid i j) := ⟨i.2.le, j.2.le⟩
  obtain ⟨A, hA⟩ := exists_isGridFr W hbig
  obtain ⟨A₁, hA₁⟩ := exists_isGridFr W hsm
  obtain ⟨AV, hV⟩ := exists_isGridFr W (X := .grid i (j + 1)) ⟨i.2.le, j.2⟩
  obtain ⟨AV₁, hV₁⟩ := exists_isGridFr W (X := .grid (i + 1) j) ⟨i.2, j.2.le⟩
  obtain ⟨σ, σ', hσ⟩ := H1 W i j X hTG hSC A A₁ AV AV₁ hA hA₁ hV hV₁
  obtain ⟨κ, hκ, hflip⟩ := H2 W S hψ hN ρ i j X hTG hSC A A₁ AV AV₁ hA hA₁ hV hV₁
  replace H3 := H3 W i j _ _ _ _ _ X hSC A A₁ (frSum AV AV₁)
  have hIs := hSC.2.2.2.2.2.2.2
  have hrk : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.eps G i j = rankV D i j % 2 := congrArg (· % 2) (Nat.add_right_cancel hSC.2.2.2.1)
  have eα : ∀ t, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j = Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2) := fun t => by
    rw [← hrk]; rfl
  have eβ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j = G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2) := by
    rw [← hrk]; rfl
  have hD := fun t => dict hL W t i j A A₁ AV AV₁ hA hA₁ hV hV₁
  have hT : ∀ t, IsTriple _ _ _ (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j) := fun t =>
    (hD t).1 (hst t) _ (exists_vol G hL t).choose_spec
  choose a b ha hb _ using (hT μ₀).gap
  obtain ⟨ι, -, hιA⟩ := GlobalTheory.SquareIdent.realA hL W i j A AV AV₁ hA hV hV₁
  obtain ⟨ι', -, hιB⟩ := GlobalTheory.SquareIdent.realB hL W i j A₁ AV AV₁ hA₁ hV hV₁
  obtain ⟨Pr, q, q', hq, hq', H⟩ := hLM D W.ψ W.θ W.ψ_std W.θ_is _ _ _ A A₁ (frSum AV AV₁) a b
  obtain ⟨hlam, PF, pF, pF', J, -, hJ, -, hI, hI', P₀, hP₀, hP₀i⟩ := hF
  obtain ⟨P₁, hP₁⟩ := hq (q' (σ' P₀))
  have key : ∀ t, ∃ l m : ℂ, m ≠ 0 ∧ pF (σ.symm P₁) = m • pF' P₀ ∧ (∀ x ∈ ρ.rel i j, q (ι x.1) = l • q' (ι' x.2)) ∧
      (∃ x ∈ ρ.rel i j, q (ι x.1) ≠ 0) ∧ ∀ c₀, RegConst W S.B ρ t i j c₀ → c₀ = l * m * κ t * lam t := by
    intro t
    obtain ⟨M, hM', a₀, τ, τ', n, Φ, hn, hfl, g, g₁, hne⟩ :=
      GlobalTheory.BigNZ.exists_integral_ne_zero hP.strongApproxSU hK hM hL W S.B ρ t i j (hst t)
    have wA : GlobalTheory.Grid.IsWeil W.ψ true _ _ (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j)
        (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j / GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j) (X.ω t) := by rw [eα, eβ]; exact hIs.weil t
    have wB : GlobalTheory.Grid.IsWeil W.ψ false _ _ (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j)
        (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j / GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j) (X.ω' t) := by rw [eα, eβ]; exact hIs.weil' t
    obtain ⟨Pi, rf, rl, p, p', hm, hcore⟩ := _root_.GlobalTheory.SquareIdent.square_identity_reduction hP.howeDualityReal hP hM hL W i j A A₁ AV AV₁ hA hA₁ hV hV₁ t S.B ρ M
      (hst t) hM' (hT t) _ _ wA wB
    obtain ⟨fτ, fτ', -⟩ := (hcore 0).choose_spec n Φ τ τ' hn hfl
    obtain ⟨Pf, r, r', e, -, -, hp, hp'⟩ := (H _ _ (hT t) fun τ =>
      ⟨GlobalTheory.SquareRel.hasInfExp_alpha G i j hL μ₀ t τ (ha τ), hb τ⟩).2 _ _ _ _ _ _ _ hm
    obtain ⟨ff, ff', hk, hk'⟩ := hσ t
    obtain ⟨γ, hγ0, hγ⟩ := H3 t ff ff' Pi rf rl p p' (by rw [← eα, ← eβ]; exact hm) Pr Pf q q' r r' e hq hq' hp hp'
    have hνA : IsHaarFD _ (M.ν _) (M.fd _) := (hM'.vtx _ hbig).haar_fund
    have hνB : IsHaarFD _ (M.ν _) (M.fd _) := (hM'.vtx _ hsm).haar_fund
    obtain ⟨s, hs0, hs⟩ := exists_haar_smul _ X.m _ hIs.meas.1 hνA.1
    obtain ⟨s', hs0', hs'⟩ := exists_haar_smul _ X.m' _ hIs.meas'.1 hνB.1
    have hsC : ((s : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs0
    have hsC' : ((s' : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs0'
    obtain ⟨c, hc0, kill, hc⟩ := _root_.GlobalTheory.ThetaRegularizationComparison.regularised_thetaInt_comparison_smul hP hK hTA W.θ_is (hT t) hνA hνB hm
    have mA : fockF W.ψ W.θ true A (frSum AV AV₁) (X.f t) P₁ ∈ algF W.ψ W.θ true A (frSum AV AV₁) :=
      Submodule.subset_span ⟨_, _, ff, rfl⟩
    have mB : fockF W.ψ W.θ false A₁ (frSum AV AV₁) (X.f' t) (σ' P₀) ∈ algF W.ψ W.θ false A₁ (frSum AV AV₁) :=
      Submodule.subset_span ⟨_, _, ff', rfl⟩
    have cA := fun h => integral_change _ hIs.meas hνA hs
      (fun u => thetaKO (X.ω t) u h (fockF W.ψ W.θ true A (frSum AV AV₁) (X.f t) P₁))
      fun γ hγ u => GlobalTheory.SquareIdent.thetaKO_left_neg W.θ_is _ _ wA mA γ hγ u h
    have cB := fun h => integral_change _ hIs.meas' hνB hs'
      (fun u => thetaKO (X.ω' t) u h (fockF W.ψ W.θ false A₁ (frSum AV AV₁) (X.f' t) (σ' P₀)))
      fun γ hγ u => GlobalTheory.T.thetaKernel_leftInvariant_rational_unitary D W.ψ W.θ W.θ_is _ _ _ _ _ _ _ wB _ mB γ hγ u h
    have iB : GlobalTheory.RegCompare.Intg (X.ω' t) (M.ν _) (M.fd _) (fockF W.ψ W.θ false A₁ (frSum AV AV₁) (X.f' t) (σ' P₀)) :=
      fun h => (cB h).1 (by simpa only [← hk'] using hP₀i t h)
    have eA : thetaInt (X.ω t) (M.ν _) (M.fd _) (fockF W.ψ W.θ true A (frSum AV AV₁) (X.f t) P₁) =
        J t ((((s : ℝ) : ℂ) * lam t) • pF (σ.symm P₁)) := by
      rw [map_smul, mul_smul, ← hI]
      funext h
      refine (cA h).2.trans ?_
      simp only [_root_.Pi.smul_apply, smul_eq_mul, Tri.I, hk, LinearEquiv.apply_symm_apply]
    have eB : thetaInt (X.ω' t) (M.ν _) (M.fd _) (fockF W.ψ W.θ false A₁ (frSum AV AV₁) (X.f' t) (σ' P₀)) =
        J t (((s' : ℝ) : ℂ) • pF' P₀) := by
      rw [map_smul, ← hI' t P₀ (hP₀i t)]
      funext h
      refine (cB h).2.trans ?_
      simp only [_root_.Pi.smul_apply, smul_eq_mul, Tri.I', hk']
    have hne' : p' (fockF W.ψ W.θ false A₁ (frSum AV AV₁) (X.f' t) (σ' P₀)) ≠ 0 := fun h0 => by
      have h1 := (hc 0 (Submodule.zero_mem _) _ mB 1 (by rw [h0, map_zero, smul_zero])).2 iB
      rw [kill 0 (Submodule.zero_mem _) (map_zero _), eB, ← map_smul, ← map_zero (J t)] at h1
      have h2 := (hJ t h1).symm
      simp [hc0, hs0', hP₀] at h2
    have hstd : p (fockF W.ψ W.θ true A (frSum AV AV₁) (X.f t) P₁) =
        γ • p' (fockF W.ψ W.θ false A₁ (frSum AV AV₁) (X.f' t) (σ' P₀)) := by
      rw [hp _ ff, hp' _ ff', hP₁, hγ, TensorProduct.tmul_smul, map_smul]
    have hu : (((s : ℝ) : ℂ) * lam t) • pF (σ.symm P₁) = (c * γ) • ((s' : ℝ) : ℂ) • pF' P₀ := by
      have h1 := (hc _ mA _ mB γ hstd).2 iB
      rw [eA, eB, ← map_smul (J t)] at h1
      exact hJ t h1
    have hy : q' (σ' P₀) ≠ 0 := fun h0 => hne' (by rw [hp' _ ff', h0, TensorProduct.zero_tmul, map_zero])
    have hfp := hflip t M hM' s s' hs hs' Pi rf rl p p' hm n Φ τ τ' hn hfl P₁ (σ' P₀) γ hne' hstd
    rw [hp _ fτ, hp' _ fτ', hP₁, ← map_smul, ← map_smul, ← TensorProduct.tmul_smul, ← TensorProduct.tmul_smul] at hfp
    have hr := tmul_cancel_left hy (e.injective hfp)
    set δ : ℂ := ((s : ℝ) : ℂ)⁻¹ * (κ t * ((s' : ℝ) : ℂ) * γ) with hδ
    have hδ0 : δ ≠ 0 := mul_ne_zero (inv_ne_zero hsC) (mul_ne_zero (mul_ne_zero (hκ t).1 hsC') hγ0)
    have hr' : r (datumA W τ) = δ • r' (datumB W τ') := by
      rw [hδ, mul_smul, ← hr, smul_smul, inv_mul_cancel₀ hsC, one_smul]
    obtain ⟨c₁, hc₁⟩ := hρ i j A A₁ AV AV₁ hA hA₁ hV hV₁ t _ _ Pi rf rl p p' hm S.B n Φ τ τ' hn hfl
    obtain ⟨b', hb'⟩ := ρ.onto_big i j (toTens a₀)
    obtain ⟨b₀, rfl⟩ : ∃ b₀ : PolT G (routeSmall t i j) →₀ ℂ, toTens b₀ = b' := toTens_surjective b'
    have hΘ : IsMatched S.B t ρ i j (tensT W a₀ τ) (tensT W b₀ τ') := ⟨a₀, b₀, τ, τ', n, Φ, hb', hn, hfl, rfl, rfl⟩
    obtain ⟨ξ, hξ⟩ := (hD t).2 _ _ wA wB
    obtain ⟨aA, aB, -, kB, jA, jB⟩ := hξ S.B ρ _ _ hΘ
    have hp0 : p (datumA W (tensT W a₀ τ)) ≠ 0 := fun h0 => hne (by rw [jA, kill _ aA h0]; exact mul_zero _)
    have hp1 := hp0
    rw [hιA t S.B ρ n Φ τ τ' hfl, hp _ fτ] at hp1
    have hx0 : q (ι (toTens a₀)) ≠ 0 := fun h0 => hp1 (by rw [h0, TensorProduct.zero_tmul, map_zero])
    have hr0 : r' (datumB W τ') ≠ 0 := fun h0 => hp1 (by rw [hr', h0, smul_zero, TensorProduct.tmul_zero, map_zero])
    have hm0 : ((s : ℝ) : ℂ) * lam t ≠ 0 := mul_ne_zero hsC (hlam t)
    refine ⟨δ⁻¹ * c₁, (((s : ℝ) : ℂ) * lam t)⁻¹ * (c * γ * ((s' : ℝ) : ℂ)),
      mul_ne_zero (inv_ne_zero hm0) (mul_ne_zero (mul_ne_zero hc0 hγ0) hsC'), ?_, ?_, ⟨_, hb', hx0⟩, fun c₀ h₀ => ?_⟩
    · rw [mul_smul, mul_smul, ← hu, smul_smul, inv_mul_cancel₀ hm0, one_smul]
    · rintro ⟨x, y⟩ hxy
      obtain ⟨x, rfl⟩ : ∃ x₀ : PolT G (routeBig t i j) →₀ ℂ, toTens x₀ = x := toTens_surjective x
      obtain ⟨y, rfl⟩ : ∃ y₀ : PolT G (routeSmall t i j) →₀ ℂ, toTens y₀ = y := toTens_surjective y
      have h1 := hc₁ x y hxy
      rw [hιA t S.B ρ n Φ τ τ' hfl, hιB t S.B ρ n Φ τ τ' hfl, hp _ fτ, hp' _ fτ', hr', ← map_smul e, TensorProduct.tmul_smul,
        TensorProduct.smul_tmul', TensorProduct.smul_tmul'] at h1
      have h2 := tmul_cancel_right hr0 (e.injective h1)
      show q (ι (toTens x)) = (δ⁻¹ * c₁) • q' (ι' (toTens y))
      rw [mul_smul, ← h2, smul_smul, inv_mul_cancel₀ hδ0, one_smul]
    · obtain ⟨z, hz0, hzi, hz⟩ := (hc _ aA _ aB c₁ (hc₁ a₀ b₀ hb')).1
      have ez : zact (X.ω' t) z (datumB W (tensT W b₀ τ')) = GlobalTheory.RegCompare.wop (X.ω' t) z (datumB W (tensT W b₀ τ')) :=
        (GlobalTheory.RegCompare.wop_apply _ _ _).symm
      have h1 : c₀ = c * c₁ := by
        refine eq_of_regConst hK hL (hst t) hM' hΘ hne hz0 ?_ ?_ h₀
        · rw [funext (kB z g g₁), ez]
          exact (hzi _).const_mul _
        · rw [jA, jB, ez]
          have := congrFun hz (blk _ _ (g, g₁))
          simp only [_root_.Pi.smul_apply, smul_eq_mul] at this
          linear_combination ξ (g, g₁) * this
      have := hlam t
      have := (hκ t).1
      rw [h1, hδ]
      field_simp
  choose l m hm0 hm hl hx hc using key
  have em : ∀ t, m t = m μ₀ := fun t => smul_left_injective ℂ hP₀ ((hm t).symm.trans (hm μ₀))
  obtain ⟨x, hxr, hx0⟩ := hx μ₀
  have hy0 : q' (ι' x.2) ≠ 0 := fun h => hx0 (by rw [hl μ₀ x hxr, h, smul_zero])
  have hl0 : l μ₀ ≠ 0 := fun h => hx0 (by rw [hl μ₀ x hxr, h, zero_smul])
  have el : ∀ t, l t = l μ₀ := fun t => smul_left_injective ℂ hy0 ((hl t x hxr).symm.trans (hl μ₀ x hxr))
  refine ⟨fun t => l μ₀ * m μ₀ * κ t, fun t => ⟨mul_ne_zero (mul_ne_zero hl0 (hm0 μ₀)) (hκ t).1, ?_⟩, fun t c₀ h => ?_⟩
  · obtain ⟨ζ, h1, h2⟩ := (hκ t).2
    exact ⟨ζ, h1, by dsimp only; rw [h2]; ring⟩
  · rw [hc t c₀ h, em t, el t]
end GlobalTheory.ThetaRegularizationComparison
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.ConstRatio (Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regConst_eq_away_unit_mul_factor : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) → NumbersIn D.what₂.embLL S μ₀ → ∀ (ρ : RealMatch W), ρ.Tied → ∀ (i j : Fin D.R.m) (X : TriG G i j) (lam : T → ℂ),
    TopGrid W i j X → IsStageC W i j (pp D j) (qq D j) X → Factor X W.ψ W.θ lam →
    ∃ κ : T → ℂ, (∀ t, κ t ≠ 0 ∧ ∃ ζ : D.what₂.LL, GlobalTheory.Square.IsAwayUnit (Qn G t) ζ ∧ κ t = D.what₂.embLL ζ * κ μ₀) ∧
      ∀ (t : T) (c₀ : ℂ), RegConst W S.B ρ t i j c₀ → c₀ = κ t * lam t := by
  first | exact @_root_.GlobalTheory.ThetaRegularizationComparison.regulator_constant_eq | exact _root_.GlobalTheory.ThetaRegularizationComparison.regulator_constant_eq | (intros; apply _root_.GlobalTheory.ThetaRegularizationComparison.regulator_constant_eq <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ExistsTiedPairOfStandingHypotheses
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.ChainFr Matrix
open scoped TensorProduct
noncomputable section
namespace GlobalTheory.GridFrameExistence
open GlobalTheory.SquareComm GlobalTheory.SquareDict GlobalTheory.SquareAgree GlobalTheory.Grid
variable {D : D7}
theorem tied_pair_scalar_match (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (hL : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching) {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D}
    (hθ : IsInfFam θ) {W W₁ X : HSp D} {A : Fr W} {A₁ : Fr W₁} {B : Fr X} {α β : (AE D)ˣ →* Circle} (hT : IsTriple W W₁ X α β)
    {ν 𝓕 ν₁ 𝓕₁} (hν : IsHaarFD W ν 𝓕) (hν₁ : IsHaarFD W₁ ν₁ 𝓕₁) {ωA ωB Pi₀ rf₀ rl₀ p₀ p₀' Pi rf rl p p'}
    (h₀ : IsMatch ψ θ A A₁ B α β ωA ωB Pi₀ rf₀ rl₀ p₀ p₀') (hM : IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p') :
    ∃ s : ℂ, s ≠ 0 ∧ ∀ Φ ∈ algF ψ θ true A B, ∀ Φ' ∈ algF ψ θ false A₁ B, p₀ Φ = p₀' Φ' → p' Φ' = s • p Φ := by
  obtain ⟨e, Bs, Γ, Xc, om, om', cA, cB, hO, hTD⟩ :=
    GlobalTheory.T.exists_placewise_seesaw_triple_over_hermitian D ψ θ hθ W W₁ X A A₁ B α β hT ν 𝓕 ν₁ 𝓕₁ hν hν₁ ωA ωB hM.weilA hM.weilB
  obtain ⟨R, Rf, hR⟩ := hL D.host.F D.host.E D.sp.cm.sig Bs W.rank W₁.rank Γ Xc om om' hTD
  have hRe := hP.howeDualityReal
  have kA : ∀ Φ ∈ algF ψ θ true A B, p Φ = 0 ↔ p₀ Φ = 0 := fun Φ hΦ => by
    obtain ⟨ΦD, hΦD, hD⟩ := hO.algA Φ hΦ
    exact (_root_.GlobalTheory.SquareAgree.theta_kernel_match_on_parabolic hRe hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hT hO hTD R Rf hR
      Pi rf rl p p' hM Φ hΦ ΦD hΦD hD).trans (_root_.GlobalTheory.SquareAgree.theta_kernel_match_on_parabolic hRe hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om'
      cA cB hθ hT hO hTD R Rf hR Pi₀ rf₀ rl₀ p₀ p₀' h₀ Φ hΦ ΦD hΦD hD).symm
  have kB : ∀ Φ ∈ algF ψ θ false A₁ B, p' Φ = 0 ↔ p₀' Φ = 0 := fun Φ hΦ => by
    obtain ⟨ΦD, hΦD, hD⟩ := hO.algB Φ hΦ
    exact (_root_.GlobalTheory.SquareAgree.theta_kernel_match_on_opposite_parabolic hRe hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hT hO hTD R Rf hR
      Pi rf rl p p' hM Φ hΦ ΦD hΦD hD).trans (_root_.GlobalTheory.SquareAgree.theta_kernel_match_on_opposite_parabolic hRe hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc
      om om' cA cB hθ hT hO hTD R Rf hR Pi₀ rf₀ rl₀ p₀ p₀' h₀ Φ hΦ ΦD hΦD hD).symm
  let S : Submodule ℂ (Pi × Pi) :=
    { carrier := {x | ∃ Φ ∈ algF ψ θ true A B, ∃ Φ' ∈ algF ψ θ false A₁ B, p₀ Φ = p₀' Φ' ∧ x = (p Φ, p' Φ')}
      add_mem' := by
        rintro _ _ ⟨Φ, hΦ, Φ', hΦ', h, rfl⟩ ⟨Ψ, hΨ, Ψ', hΨ', k, rfl⟩
        exact ⟨Φ + Ψ, add_mem hΦ hΨ, Φ' + Ψ', add_mem hΦ' hΨ', by rw [map_add (f := _), map_add (f := _), h, k],
          Prod.ext (map_add p Φ Ψ).symm (map_add p' Φ' Ψ').symm⟩
      zero_mem' := ⟨0, zero_mem _, 0, zero_mem _, by rw [map_zero, map_zero],
        Prod.ext (map_zero p).symm (map_zero p').symm⟩
      smul_mem' := by
        rintro c _ ⟨Φ, hΦ, Φ', hΦ', h, rfl⟩
        exact ⟨c • Φ, Submodule.smul_mem _ c hΦ, c • Φ', Submodule.smul_mem _ c hΦ', by rw [map_smul, map_smul, h],
          Prod.ext (map_smul p c Φ).symm (map_smul p' c Φ').symm⟩ }
  obtain ⟨s, hs, H⟩ := eq_smul_of_stable_graph D X Pi rf rl hM.irred
    (_root_.GlobalTheory.SquareAgree.rank_polarization_pi_le_aleph0 hRe hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hT hO hTD R Rf hR
      Pi rf rl p p' hM) S
    (by
      rintro g hg _ ⟨Φ, hΦ, Φ', hΦ', h, rfl⟩
      refine ⟨_, hM.mapA.stabX.1 g hg Φ hΦ, _, hM.mapB.stabX.1 g hg Φ' hΦ', ?_, ?_⟩
      · rw [h₀.mapA.eqf g hg Φ hΦ, h₀.mapB.eqf g hg Φ' hΦ', h]
      · rw [hM.mapA.eqf g hg Φ hΦ, hM.mapB.eqf g hg Φ' hΦ'])
    (by
      rintro τ Y hY _ ⟨Φ, hΦ, Φ', hΦ', h, rfl⟩
      obtain ⟨Ψ, hΨ, hd⟩ := hM.mapA.stabX.2 τ Y hY Φ hΦ
      obtain ⟨Ψ', hΨ', hd'⟩ := hM.mapB.stabX.2 τ Y hY Φ' hΦ'
      refine ⟨Ψ, hΨ, Ψ', hΨ', ?_, ?_⟩
      · rw [h₀.mapA.eql τ Y hY Φ hΦ Ψ hΨ hd, h₀.mapB.eql τ Y hY Φ' hΦ' Ψ' hΨ' hd', h]
      · rw [hM.mapA.eql τ Y hY Φ hΦ Ψ hΨ hd, hM.mapB.eql τ Y hY Φ' hΦ' Ψ' hΨ' hd'])
    (by
      rintro x ⟨Φ, hΦ, Φ', hΦ', h, hx⟩
      obtain ⟨rfl, h0⟩ := Prod.mk.inj hx
      exact (kA Φ hΦ).2 (h.trans ((kB Φ' hΦ').1 h0.symm)))
    (by
      rintro y ⟨Φ, hΦ, Φ', hΦ', h, hy⟩
      obtain ⟨h0, rfl⟩ := Prod.mk.inj hy
      exact (kB Φ' hΦ').2 (h.symm.trans ((kA Φ hΦ).1 h0.symm)))
    (by
      intro x
      obtain ⟨Φ, hΦ, rfl⟩ : x ∈ (algF ψ θ true A B).map p := hM.mapA.onto ▸ Submodule.mem_top
      obtain ⟨Φ', hΦ', h⟩ : p₀ Φ ∈ (algF ψ θ false A₁ B).map p₀' := h₀.mapB.onto ▸ Submodule.mem_top
      exact ⟨p' Φ', Φ, hΦ, Φ', hΦ', h.symm, rfl⟩)
  exact ⟨s, hs, fun Φ hΦ Φ' hΦ' h => H _ _ ⟨Φ, hΦ, Φ', hΦ', h, rfl⟩⟩
open GlobalTheory.SquareIdent in
theorem tied_pair_square_relation (hH : GlobalTheory.Published.HoweDualityReal) (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (hTL : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching)
    (hLM : GlobalTheory.SquareSt.LocalMatching) {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀)
    (hst : ∀ t, SquareStanding G t) (W : G.Weil) (i j : Fin D.R.m) :
    ∃ r : Submodule ℂ (PolRoute G (.grid i (j + 1)) (.grid (i + 1) (j + 1)) (.grid (i + 1) j) ×
      PolRoute G (.grid i (j + 1)) (.grid i j) (.grid (i + 1) j)), (∀ a, ∃ b, (a, b) ∈ r) ∧ (∀ b, ∃ a, (a, b) ∈ r) ∧ r ≠ ⊤ ∧
    ∀ (ρ : RealMatch W) (A : Fr (G.V (.grid (i + 1) (j + 1)))) (A₁ : Fr (G.V (.grid i j))) (AV : Fr (G.V (.grid i (j + 1))))
      (AV₁ : Fr (G.V (.grid (i + 1) j))), IsGridFr W _ A → IsGridFr W _ A₁ → IsGridFr W _ AV → IsGridFr W _ AV₁ →
      ∀ (t : T) ωA ωB Pi rf rl p p', IsMatch W.ψ W.θ A A₁ (frSum AV AV₁) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j)
        (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j) ωA ωB Pi rf rl p p' →
      ∀ B : Frames G, ∃ c : ℂ, ∀ n Φ τ τ', (∀ w ∈ locPl G t, depthAt G w ≤ n w ∧ IsNatDatum (unifAt w) (n w) (Φ w)) →
        HasFlip B t ρ i j n Φ τ τ' → ∀ (a : PolT G (routeBig t i j) →₀ ℂ) (b : PolT G (routeSmall t i j) →₀ ℂ),
          (toTens a, toTens b) ∈ r → p (datumA W (tensT W a τ)) = c • p' (datumB W (tensT W b τ')) := by
  obtain ⟨A, hA⟩ := exists_isGridFr W (X := .grid (i + 1) (j + 1)) ⟨i.2, j.2⟩
  obtain ⟨A₁, hA₁⟩ := exists_isGridFr W (X := .grid i j) ⟨i.2.le, j.2.le⟩
  obtain ⟨AV, hV⟩ := exists_isGridFr W (X := .grid i (j + 1)) ⟨i.2.le, j.2⟩
  obtain ⟨AV₁, hV₁⟩ := exists_isGridFr W (X := .grid (i + 1) j) ⟨i.2, j.2.le⟩
  choose M hM using exists_vol G hL
  have hT := fun t => (dict hL W t i j A A₁ AV AV₁ hA hA₁ hV hV₁).1 (hst t) (M t) (hM t)
  choose a b ha hb _ using (hT μ₀).gap
  obtain ⟨ι, hι, hιA⟩ := realA hL W i j A AV AV₁ hA hV hV₁
  obtain ⟨ι', hι', hιB⟩ := realB hL W i j A₁ AV AV₁ hA₁ hV hV₁
  obtain ⟨Pr, q, q', hq, hq', H⟩ := hLM D W.ψ W.θ W.ψ_std W.θ_is _ _ _ A A₁ (frSum AV AV₁) a b
  have hexp : ∀ t τ, HasInfExp D (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j) τ (a τ) ∧ HasInfExp D (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j) τ (b τ) :=
    fun t τ => ⟨GlobalTheory.SquareRel.hasInfExp_alpha G i j hL μ₀ t τ (ha τ), hb τ⟩
  have hqi : Function.Surjective (q ∘ₗ ι) := hq.comp hι
  have hqi' : Function.Surjective (q' ∘ₗ ι') := hq'.comp hι'
  haveI hPr : Nontrivial Pr := by
    obtain ⟨⟨ωA, ωB, Pi, rf, rl, p, p', hm⟩, H2⟩ := H _ _ (hT μ₀) (hexp μ₀)
    obtain ⟨Pf, -, -, e, -⟩ := H2 ωA ωB Pi rf rl p p' hm
    haveI : Nontrivial Pi := hm.irred.1
    exact GlobalTheory.SquareRel.nontrivial_of_tensor e
  refine ⟨GlobalTheory.SquareRel.relOf (q ∘ₗ ι) (q' ∘ₗ ι'), GlobalTheory.SquareRel.relOf_fst hqi', GlobalTheory.SquareRel.relOf_snd hqi,
    GlobalTheory.SquareRel.relOf_ne_top hqi, ?_⟩
  intro ρ A' A₁' AV' AV₁' hA' hA₁' hV' hV₁' t ωA ωB Pi rf rl p p' hm B
  obtain rfl := gridFr_unique hA hA'
  obtain rfl := gridFr_unique hA₁ hA₁'
  obtain rfl := gridFr_unique hV hV'
  obtain rfl := gridFr_unique hV₁ hV₁'
  obtain ⟨Pi₀, rf₀, rl₀, p₀, p₀', hm₀, hcore⟩ := _root_.GlobalTheory.SquareIdent.square_identity_reduction hH hP hTL hL W i j A A₁ AV AV₁ hA hA₁ hV hV₁ t B ρ (M t) (hst t) (hM t)
    (hT t) ωA ωB hm.weilA hm.weilB
  obtain ⟨Pf, r, r', e, -, -, hp, hp'⟩ := (H _ _ (hT t) (hexp t)).2 ωA ωB Pi₀ rf₀ rl₀ p₀ p₀' hm₀
  obtain ⟨x₀, hx₀⟩ := exists_ne (0 : Pr)
  obtain ⟨P₀, rfl⟩ := hq x₀
  obtain ⟨P₀', hP₀⟩ := hcore P₀
  obtain ⟨lam, hlam⟩ := exists_scalar (Q := Pf) hx₀ (q' P₀')
  have hbig : Node.InRange D.R.m (.grid (i + 1) (j + 1)) := ⟨i.2, j.2⟩
  have hsm : Node.InRange D.R.m (.grid i j) := ⟨i.2.le, j.2.le⟩
  obtain ⟨s, hs, hs'⟩ := _root_.GlobalTheory.GridFrameExistence.tied_pair_scalar_match hP hTL W.θ_is (hT t) ((hM t).vtx _ hbig).haar_fund ((hM t).vtx _ hsm).haar_fund hm₀ hm
  refine ⟨s⁻¹ * lam, fun n Φ τ τ' hn hF a' b' hab => ?_⟩
  obtain ⟨f1, f2, f3⟩ := hP₀ n Φ τ τ' hn hF
  rw [hp _ f1, hp' _ f2] at f3
  have h1 := hlam _ _ (e.injective f3)
  have h2 : q (ι (toTens a')) = q' (ι' (toTens b')) := hab
  rw [hιA t B ρ n Φ τ τ' hF, hιB t B ρ n Φ τ τ' hF]
  have h3 := hs' _ (Submodule.subset_span ⟨_, ι (toTens a'), f1, rfl⟩)
    _ (Submodule.smul_mem _ lam (Submodule.subset_span ⟨_, ι' (toTens b'), f2, rfl⟩))
    (by rw [map_smul, hp _ f1, hp' _ f2, h1, h2, TensorProduct.tmul_smul, map_smul])
  rw [map_smul] at h3
  rw [mul_smul, h3, smul_smul, inv_mul_cancel₀ hs, one_smul]
open GlobalTheory.SquareIdent in
theorem tied_pair_regularization_constant (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (hK : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree) (hWC : GlobalTheory.SquareSt.WeilConvergence)
    (hTA : GlobalTheory.SquareSt.ThetaIntegralsAgree) {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀)
    (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (hst : SquareStanding G t) (i j : Fin D.R.m)
    {A : Fr (G.V (.grid (i + 1) (j + 1)))} {A₁ : Fr (G.V (.grid i j))} {AV : Fr (G.V (.grid i (j + 1)))}
    {AV₁ : Fr (G.V (.grid (i + 1) j))} (hA : IsGridFr W _ A) (hA₁ : IsGridFr W _ A₁) (hV : IsGridFr W _ AV) (hV₁ : IsGridFr W _ AV₁)
    {ωA ωB Pi rf rl p p'} (hm : IsMatch W.ψ W.θ A A₁ (frSum AV AV₁) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j)
      (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j) ωA ωB Pi rf rl p p') {lam : ℂ}
    (hlam : ∀ Θ Θ', IsMatched B t ρ i j Θ Θ' → p (datumA W Θ) = lam • p' (datumB W Θ')) :
    ∃ c : ℂ, GlobalTheory.SqTower.RegConst W B ρ t i j c := by
  have hD := dict hL W t i j A A₁ AV AV₁ hA hA₁ hV hV₁
  obtain ⟨M₁, hM₁⟩ := exists_vol G hL t
  have hT := hD.1 hst M₁ hM₁
  have hbig : Node.InRange D.R.m (.grid (i + 1) (j + 1)) := ⟨i.2, j.2⟩
  have hsm : Node.InRange D.R.m (.grid i j) := ⟨i.2.le, j.2.le⟩
  obtain ⟨c₀, -, hc₀⟩ := _root_.GlobalTheory.RegCompare.regularised_integral_comparison hP hK hTA D W.ψ W.θ W.θ_is _ _ _ A A₁
    (frSum AV AV₁) _ _ hT _ _ _ _ (hM₁.vtx _ hbig).haar_fund (hM₁.vtx _ hsm).haar_fund ωA ωB Pi rf rl p p' hm
  obtain ⟨κ, hκ⟩ := hD.2 ωA ωB hm.weilA hm.weilB
  refine ⟨lam * c₀, fun M hM Θ Θ' hΘ g g₁ => ?_⟩
  obtain ⟨aA, aB, kA, kB, iA, iB⟩ := hκ B ρ Θ Θ' hΘ
  have hconv := GlobalTheory.T.bigRoute_kernel_integrableOn_unitary_quotient hWC hL W B ρ t i j (GlobalTheory.T.squareThetaTripleHypotheses_of_standing hL W t i j hst) M hM Θ Θ' hΘ g₁ g
  have hpp := hlam Θ Θ' hΘ
  obtain ⟨z, -, hz0, hzS, hzM, hz⟩ := hc₀ _ aB
  have ez : zact ωB z (datumB W Θ') = GlobalTheory.RegCompare.wop ωB z (datumB W Θ') := (GlobalTheory.RegCompare.wop_apply _ _ _).symm
  have hI : zdeg z • thetaInt ωA (M₁.ν _) (M₁.fd _) (datumA W Θ) =
      (lam * c₀) • thetaInt ωB (M₁.ν _) (M₁.fd _) (GlobalTheory.RegCompare.wop ωB z (datumB W Θ')) := by
    by_cases h0 : lam = 0
    · obtain ⟨z', -, -, -, -, hz'⟩ := hc₀ 0 (Submodule.zero_mem _)
      have h1 := hz' _ aA (by rw [hpp, h0, zero_smul, map_zero, smul_zero])
      have h2 := GlobalTheory.RegCompare.thetaInt_smul ωB (M₁.ν _) (M₁.fd _) 0 0
      rw [zero_smul, zero_smul] at h2
      rw [h1, map_zero, h2, h0, zero_mul, zero_smul, smul_zero, smul_zero]
    · have h1 := hz ((zdeg z * lam⁻¹) • datumA W Θ) (Submodule.smul_mem _ _ aA)
        (by rw [map_smul, hpp, smul_smul, mul_assoc, inv_mul_cancel₀ h0, mul_one])
      rw [GlobalTheory.RegCompare.thetaInt_smul] at h1
      rw [mul_smul, ← h1, smul_smul, mul_left_comm, mul_inv_cancel₀ h0, mul_one]
  have invA : ∀ γ ∈ GQ (G.V (.grid (i + 1) (j + 1))), ∀ u, kerBig W Θ g g₁ (γ * u) = kerBig W Θ g g₁ u := fun γ hγ u => by
    rw [kA, kA, thetaKO_left_neg W.θ_is _ _ hm.weilA aA γ hγ]
  have invB : ∀ γ ∈ GQ (G.V (.grid i j)), ∀ u, translates z (kerSmall W Θ' g g₁) (γ * u) = translates z (kerSmall W Θ' g g₁) u :=
    fun γ hγ u => by
      rw [kB, kB, ez, GlobalTheory.SquareComm.ThetaLeft.main D W.ψ W.θ W.θ_is _ _ _ _ _ _ ωB hm.weilB _ hzS γ hγ]
  refine ⟨z, hz0, ⟨hconv, ?_⟩, ?_⟩
  · rw [GlobalTheory.VolIdent.vol_integrableOn_iff M M₁ hM hM₁ hsm _ invB, funext (kB z g g₁), ez]
    exact (GlobalTheory.RegCompare.intg_of_modInt hzM _).const_mul _
  · rw [GlobalTheory.VolIdent.vol_setIntegral_eq M M₁ hM hM₁ hbig _ invA, GlobalTheory.VolIdent.vol_setIntegral_eq M M₁ hM hM₁ hsm _ invB,
      iA, iB, ez]
    have := congrFun hI (blk _ _ (g, g₁))
    simp only [_root_.Pi.smul_apply, smul_eq_mul] at this
    linear_combination κ (g, g₁) * this
theorem exists_tied_pair_of_standing_hypotheses (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (hK : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree)
    (hTL : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching) {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀)
    (hst : ∀ t, SquareStanding G t) (W : G.Weil) (rm : RealMatch W) :
    ∃ ρ : RealMatch W, ρ.vX = rm.vX ∧ ρ.vT = rm.vT ∧ ρ.Tied ∧
      ∀ (B : Frames G) (i j : Fin D.R.m) (t : T), ∃ c : ℂ, GlobalTheory.SqTower.RegConst W B ρ t i j c := by
  have hLM := _root_.GlobalTheory.T.twisted_local_factors_match hP.howeDualityReal hP hK hTL
  choose r hr1 hr2 hr3 hr4 using _root_.GlobalTheory.GridFrameExistence.tied_pair_square_relation hP.howeDualityReal hP hTL hLM hL hst W
  let rel' : ∀ i j : ℕ, Submodule ℂ (PolRoute G (.grid i (j + 1)) (.grid (i + 1) (j + 1)) (.grid (i + 1) j) ×
      PolRoute G (.grid i (j + 1)) (.grid i j) (.grid (i + 1) j)) := fun i j =>
    if h : i < D.R.m ∧ j < D.R.m then r ⟨i, h.1⟩ ⟨j, h.2⟩ else rm.rel i j
  have e : ∀ i j : Fin D.R.m, rel' i j = r i j := fun i j => dif_pos ⟨i.2, j.2⟩
  let ρ : RealMatch W := { rm with
    rel := rel'
    onto_big := fun i j a => by
      by_cases h : i < D.R.m ∧ j < D.R.m
      · simp only [rel', dif_pos h]; exact hr1 ⟨i, h.1⟩ ⟨j, h.2⟩ a
      · simp only [rel', dif_neg h]; exact rm.onto_big i j a
    onto_small := fun i j b => by
      by_cases h : i < D.R.m ∧ j < D.R.m
      · simp only [rel', dif_pos h]; exact hr2 ⟨i, h.1⟩ ⟨j, h.2⟩ b
      · simp only [rel', dif_neg h]; exact rm.onto_small i j b
    proper := fun i j => by
      by_cases h : i < D.R.m ∧ j < D.R.m
      · simp only [rel', dif_pos h]; exact hr3 ⟨i, h.1⟩ ⟨j, h.2⟩
      · simp only [rel', dif_neg h]; exact rm.proper i j }
  refine ⟨ρ, rfl, rfl, fun i j A A₁ AV AV₁ hA hA₁ hV hV₁ t ωA ωB Pi rf rl p p' hm B n Φ τ τ' hn hF => ?_, fun B i j t => ?_⟩
  · obtain ⟨c, hc⟩ := hr4 i j ρ A A₁ AV AV₁ hA hA₁ hV hV₁ t ωA ωB Pi rf rl p p' hm B
    exact ⟨c, fun a b hab => hc n Φ τ τ' hn hF a b (e i j ▸ hab)⟩
  obtain ⟨A, hA⟩ := exists_isGridFr W (X := .grid (i + 1) (j + 1)) ⟨i.2, j.2⟩
  obtain ⟨A₁, hA₁⟩ := exists_isGridFr W (X := .grid i j) ⟨i.2.le, j.2.le⟩
  obtain ⟨AV, hV⟩ := exists_isGridFr W (X := .grid i (j + 1)) ⟨i.2.le, j.2⟩
  obtain ⟨AV₁, hV₁⟩ := exists_isGridFr W (X := .grid (i + 1) j) ⟨i.2, j.2.le⟩
  obtain ⟨M, hM⟩ := exists_vol G hL t
  have hT := (dict hL W t i j A A₁ AV AV₁ hA hA₁ hV hV₁).1 (hst t) M hM
  choose a b ha hb _ using hT.gap
  obtain ⟨Pr, q, q', -, -, H⟩ := hLM D W.ψ W.θ W.ψ_std W.θ_is _ _ _ A A₁ (frSum AV AV₁) a b
  obtain ⟨ωA, ωB, Pi, rf, rl, p, p', hm⟩ := (H _ _ hT fun τ => ⟨ha τ, hb τ⟩).1
  obtain ⟨c, hc⟩ := hr4 i j ρ A A₁ AV AV₁ hA hA₁ hV hV₁ t ωA ωB Pi rf rl p p' hm B
  refine _root_.GlobalTheory.GridFrameExistence.tied_pair_regularization_constant hP hK (_root_.GlobalTheory.T.twisted_theta_integral_converges hP.siegelSetUnitary hP) (_root_.GlobalTheory.T.twisted_square_theta_integrals_eq hP hK hTL) hL W B ρ t (hst t) i j
    hA hA₁ hV hV₁ hm (lam := c) ?_
  rintro _ _ ⟨a', b', τ, τ', n, Φ, hab, hn, hF, rfl, rfl⟩
  exact hc n Φ τ τ' hn hF a' b' (e i j ▸ hab)
theorem exists_tied_pair : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    GlobalTheory.SqTop.GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil) (B : Frames G) (ρ : RealMatch W), ∃ ρ₀ : RealMatch W,
      ρ₀.vX = ρ.vX ∧ ρ₀.vT = ρ.vT ∧ ρ₀.Tied ∧ ∀ (i j : Fin D.R.m) (t : T), ∃ c₀ : ℂ, GlobalTheory.SqTower.RegConst W B ρ₀ t i j c₀ := by
  intro hP hK hTL
  refine ⟨0, fun ε CF _ => ⟨0, (12 : ℝ) ^ (5 / ε), fun C _ D large₂ he hx hR T Lc μ₀ hL G W B ρ => ?_⟩⟩
  obtain ⟨ρ₀, h1, h2, h3, h4⟩ := _root_.GlobalTheory.GridFrameExistence.exists_tied_pair_of_standing_hypotheses hP hK hTL hL
    (fun t => standing_of_size hR.size hR.size.2.1.eleven_le hL G t) W ρ
  exact ⟨ρ₀, h1, h2, h3, h4 B⟩
end GlobalTheory.GridFrameExistence
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.ConstRatio (Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tied_theta_pair : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil) (B : Frames G) (ρ : RealMatch W), ∃ ρ₀ : RealMatch W, ρ₀.vX = ρ.vX ∧ ρ₀.vT = ρ.vT ∧ ρ₀.Tied ∧
    ∀ (i j : Fin D.R.m) (t : T), ∃ c₀ : ℂ, RegConst W B ρ₀ t i j c₀ := by
  first | exact @_root_.GlobalTheory.GridFrameExistence.exists_tied_pair | exact _root_.GlobalTheory.GridFrameExistence.exists_tied_pair | (intros; apply _root_.GlobalTheory.GridFrameExistence.exists_tied_pair <;> assumption)
end
end

section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.ConstRatio (Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
namespace GlobalTheory.SqCompare
theorem theta_square_comparison : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) → NumbersIn D.what₂.embLL S μ₀ → ∀ (ρ : RealMatch W) (i j : Fin D.R.m) (X : TriG G i j) (lam : T → ℂ),
    TopGrid W i j X → IsStageC W i j (pp D j) (qq D j) X → Factor X W.ψ W.θ lam →
    ∃ κ : T → ℂ, (∀ t, κ t ≠ 0 ∧ ∃ ζ : D.what₂.LL, GlobalTheory.Square.IsAwayUnit (Qn G t) ζ ∧ κ t = D.what₂.embLL ζ * κ μ₀) ∧
      ∀ (t : T) (c' : ℂ), SquareNonzero W S.B ρ t i j → IsSquareConst W S.B ρ t i j c' → c' = κ t * lam t := by
  intro hP hK hM
  refine gBig_three (_root_.GlobalTheory.T.exists_tied_theta_pair hP hK hM) (_root_.GlobalTheory.T.theta_real_places_separation hP hK hM) (_root_.GlobalTheory.T.regConst_eq_away_unit_mul_factor hP hK hM) ?_
  intro D T Lc sc G μ₀ C x b hex hreal hcmp W S hstd hN ρ i j X lam hT hX hl
  obtain ⟨ρ₀, hvX, hvT, htied, hreg⟩ := hex W S.B ρ
  obtain ⟨l, hl0, hl1⟩ := hreal W S.B ρ ρ₀ hvX hvT i j
  obtain ⟨κ, hκ, hc⟩ := hcmp W S hstd hN ρ₀ htied i j X lam hT hX hl
  refine ⟨fun t => l * κ t, fun t => ?_, fun t c' _ hc' => ?_⟩
  · obtain ⟨h0, ζ, hζ, he⟩ := hκ t
    refine ⟨mul_ne_zero hl0 h0, ζ, hζ, ?_⟩
    show l * κ t = _ * (l * κ μ₀)
    rw [he]; ring
  · obtain ⟨c₀, h₀⟩ := hreg i j t
    have h1 := (hl1 t c' c₀ hc' h₀).2
    have h2 := hc t c₀ h₀
    show c' = l * κ t * lam t
    rw [h1, h2]; ring
end GlobalTheory.SqCompare
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.ConstRatio (Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_square_norm_comparison : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) → NumbersIn D.what₂.embLL S μ₀ → ∀ (ρ : RealMatch W) (i j : Fin D.R.m) (X : TriG G i j) (lam : T → ℂ),
    TopGrid W i j X → IsStageC W i j (pp D j) (qq D j) X → Factor X W.ψ W.θ lam →
    ∃ κ : T → ℂ, (∀ t, κ t ≠ 0 ∧ ∃ ζ : D.what₂.LL, GlobalTheory.Square.IsAwayUnit (Qn G t) ζ ∧ κ t = D.what₂.embLL ζ * κ μ₀) ∧
      ∀ (t : T) (c' : ℂ), SquareNonzero W S.B ρ t i j → IsSquareConst W S.B ρ t i j c' → c' = κ t * lam t := by
  first | exact @_root_.GlobalTheory.SqCompare.theta_square_comparison | exact _root_.GlobalTheory.SqCompare.theta_square_comparison | (intros; apply _root_.GlobalTheory.SqCompare.theta_square_comparison <;> assumption)
end
