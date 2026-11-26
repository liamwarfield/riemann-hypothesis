module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareDeRhamDualityOfHodgeDeRhamDual
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLieBasisDualPointsOfTangentModuleBasis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightPositivityPrincipalisation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightPositivityPrincipalisationDeep
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ToroidalFlagProportionalityOfGoodChernWeil
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorIntegralModelIsProperOfCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionValueInFrameLocalRingPoint

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeFirstDeRhamStructure
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianDeRhamOfHodgeDualPoincare
namespace GlobalTheory

theorem abelianDeRham_of_hodge_dual_poincare :
    GlobalTheory.Published.AbelianHodgeDeRham → GlobalTheory.Published.DualAbelianScheme →
      GlobalTheory.Published.PoincareDeRhamDuality → GlobalTheory.Published.AbelianDeRham :=
  fun h₁ h₂ h₃ => GlobalTheory.T.abelianSchemeDeRhamStructure_of_cube_dual_poincare h₁ GlobalTheory.T.theoremOfCubeAbelianScheme_over_arbitrary_base h₂ h₃

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeFirstDeRhamStructure
namespace GlobalTheory

theorem abelianDeRham : GlobalTheory.Published.AbelianDeRham :=
  GlobalTheory.abelianDeRham_of_hodge_dual_poincare GlobalTheory.T.abelianScheme_deRham_locallyFree_hodgeDegenerates GlobalTheory.T.dualAbelianScheme_exists_biduality
    (GlobalTheory.PoincareDeRhamDualityProof.poincareDeRhamDuality_of_hodge GlobalTheory.T.abelianScheme_deRham_locallyFree_hodgeDegenerates GlobalTheory.T.dualAbelianScheme_exists_biduality)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeFirstDeRhamStructureStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianScheme_firstDeRham_structure : GlobalTheory.Published.AbelianDeRham := by
  first | exact @GlobalTheory.abelianDeRham | exact GlobalTheory.abelianDeRham | (intros; apply GlobalTheory.abelianDeRham <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallThetaKernelTranslateIntegrable
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.SmallConv

theorem splitBound_ge : Big fun {D} _ _ _ _ _ _ _ _ _ _ _ _ => 11 ≤ D.host.splitBound := by
  exact ⟨0, fun _ _ _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hS _ _ _ => hS.size.2.1.eleven_le⟩⟩

theorem standing : Big fun ch => ∀ t, SquareStanding ch.G t := by
  obtain ⟨CF0, hH⟩ := splitBound_ge.and GlobalTheory.T.test_places_prime_to_level
  refine ⟨CF0, fun ε CF hCF => ?_⟩
  obtain ⟨x₀, hx⟩ := hH ε CF hCF
  refine ⟨x₀, fun D large₂ he hx0 Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hch hsc t => ?_⟩
  obtain ⟨h11, hW⟩ := hx D large₂ he hx0 Γ Pl0 T A Ks R F hS ch hch hsc
  refine ⟨h11, fun w hw => ?_⟩
  classical
  unfold locPl at hw
  rcases Finset.mem_union.1 hw with hw | hw
  · exact hW w hw
  · intro hmem
    have h1 := (hS.core.lev.Q_off t w hw).1
    have h2 := hS.guard.2 t w hw
    push_cast at hmem h1 h2
    rcases w.isPrime.mem_or_mem hmem with h | h
    · exact h1 (Ideal.mul_mem_right _ _ h)
    · exact h2 (Ideal.mul_mem_left _ _ h)

end GlobalTheory.SmallConv

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BirationalOnWeightParameters
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSApp

theorem gap_add_vec {N : ℕ} (v w : Fin N → ℤ) (k : ℕ) : gap (v + w) k = gap v k + gap w k := by
  unfold gap
  split_ifs
  · simp only [Pi.add_apply]; ring
  · simp

theorem gaps_u₁_u₂_of_wtBig {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    (P : WtPar Dw) (hB : WtBig P) (τ : Psi H) (a b : Fin (Dw.p + Dw.q)) (hab : (b : ℕ) = a + 1) :
    (((CompHt.dimFlag Dw + 3) ^ 2 + 2 * (Dw.p + Dw.q) : ℕ) : ℤ) ≤ P.u₁ τ a - P.u₁ τ b ∧
    (((CompHt.dimFlag Dw + 3) ^ 2 + 2 * (Dw.p + Dw.q) : ℕ) : ℤ) ≤ P.u₂ τ a - P.u₂ τ b := by
  have hk : (a : ℕ) + 1 < Dw.p + Dw.q := by have := b.2; omega
  have g1 := hB.gaps τ a hk
  have g2 := (P.gap_rem τ a).1
  have e1 : P.u₁ τ a - P.u₁ τ b = gap (P.u₁ τ) a := (gap_eq _ hab).symm
  have e2 : P.u₂ τ a - P.u₂ τ b = gap (P.u₁ τ) a + gap (P.rem τ) a := by
    rw [← gap_eq _ hab]
    exact gap_add_vec (P.u₁ τ) (P.rem τ) a
  have hn : (CompHt.dimFlag Dw + 3) ^ 2 + 2 * (Dw.p + Dw.q) ≤
      (FlagTan.dimFlag Dw + 3) * ((FlagTan.dimFlag Dw + 1).choose 2 + 4 * (Dw.p + Dw.q) + FlagTan.dimFlag Dw + 3) := by
    rw [dimFlag_eq]
    generalize FlagTan.dimFlag Dw = D
    generalize Dw.p + Dw.q = N
    generalize (D + 1).choose 2 = C
    nlinarith [Nat.zero_le (D * C), Nat.zero_le (D * N), Nat.zero_le C]
  have hn' : (((CompHt.dimFlag Dw + 3) ^ 2 + 2 * (Dw.p + Dw.q) : ℕ) : ℤ) ≤
      (((FlagTan.dimFlag Dw + 3) * ((FlagTan.dimFlag Dw + 1).choose 2 + 4 * (Dw.p + Dw.q) + FlagTan.dimFlag Dw + 3) : ℕ) : ℤ) :=
    by exact_mod_cast hn
  rw [e1, e2]
  exact ⟨hn'.trans g1, by linarith⟩

end GlobalTheory.HSApp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricOfHyp
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.CovHt.GeomBound

theorem strictAnti_of_step {N : ℕ} {f : Fin N → ℤ} (h : ∀ a b : Fin N, (b : ℕ) = a + 1 → f b < f a) : StrictAnti f := by
  rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
  simp only [Fin.mk_lt_mk] at hab
  induction b with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hab with h' | h'
    · exact (h ⟨n, by omega⟩ ⟨n + 1, hb⟩ rfl).trans (ih (by omega) h')
    · subst h'
      exact h ⟨a, ha⟩ ⟨a + 1, hb⟩ rfl

section Point

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)

theorem quo_gaps {PP A M : ℝ} (hN : HostNum D L PP A M) (hw : WtNum p i PP) (hi : (i : ℕ) + 1 < D.R.m)
    (u1 : AllWt.Weight (dat p i)) (hu : Quo p i PP u1) :
    ∀ τ (a b : Fin ((dat p i).p + (dat p i).q)), (b : ℕ) = a + 1 →
      (((dimFlag (dat p i) + 3) ^ 2 + 2 * ((dat p i).p + (dat p i).q) : ℕ) : ℤ) ≤ u1 τ a - u1 τ b := by
  obtain ⟨hsig1, hsig2, hsigr⟩ := hw.sig
  obtain ⟨h0, S, eta, -, -, -, h4T, -, hHyp⟩ := hw.hyp hi
  have hdiv := (quo_iff p i PP h0 S eta u1).1 hu
  have G := GlobalTheory.MeanTop.divided_gaps _ _ _ (hHyp u1) hdiv
  simp only [wtsAt] at G
  have hk := D.R.m_add_three_le_k
  have hm := D.R.two_le_m
  have hp1 : 1 ≤ (dat p i).p := by rw [hsig1]; simp only [Ranks.sigW]; omega
  have hq1 : 1 ≤ (dat p i).q := by rw [hsig2]; simp only [Ranks.sigW]; omega
  have hr2 : 2 ≤ D.R.r := by omega
  have hD1 : 1 ≤ dimFlag (dat p i) := by
    rw [hw.dim]
    exact Nat.mul_pos (by have := hN.f8; omega) (Nat.choose_pos hr2)

  have hz : (4 : ℝ) ≤ zBase L := by
    unfold zBase
    have c1 : (8 : ℝ) ≤ D.R.f := by exact_mod_cast hN.f8
    have c2 : (2 : ℝ) ≤ D.R.r := by exact_mod_cast hr2
    have c3 : (10 : ℝ) ≤ L.sc.L := hN.big.2.1
    have : (8 : ℝ) * 2 * 10 ≤ D.R.f * D.R.r * L.sc.L := by gcongr
    linarith
  have hPP : (4 : ℝ) ≤ PP := hz.trans ((le_self_pow₀ (by linarith) (by norm_num)).trans hN.ppLow)
  have hT : 16 * dimFlag (dat p i) ^ 2 ≤ lenT p i PP := by
    have h1 : (16 * dimFlag (dat p i) ^ 2 : ℝ) ≤ PP ^ 2 * (dimFlag (dat p i) : ℝ) ^ 2 * (D.R.k : ℝ) / (D.R.m : ℝ) := by
      have c3 : (0 : ℝ) < D.R.m := by exact_mod_cast (by omega : 0 < D.R.m)
      have c4 : (D.R.m : ℝ) ≤ D.R.k := by exact_mod_cast (by omega : D.R.m ≤ D.R.k)
      have c5 : (16 : ℝ) ≤ PP ^ 2 := by nlinarith
      rw [le_div_iff₀ c3]
      have c6 : (0 : ℝ) ≤ (dimFlag (dat p i) : ℝ) ^ 2 := by positivity
      calc (16 * (dimFlag (dat p i) : ℝ) ^ 2) * D.R.m ≤ (PP ^ 2 * (dimFlag (dat p i) : ℝ) ^ 2) * D.R.m :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right c5 c6) c3.le
        _ ≤ PP ^ 2 * (dimFlag (dat p i) : ℝ) ^ 2 * D.R.k := mul_le_mul_of_nonneg_left c4 (by positivity)
    have h2 := h1.trans (Nat.le_ceil _)
    unfold lenT
    exact_mod_cast h2
  intro τ a b hb
  obtain ⟨g1, g2, -⟩ := G τ a b hb
  have hTz : (16 * (dimFlag (dat p i) : ℤ) ^ 2) ≤ (lenT p i PP : ℤ) := by exact_mod_cast hT
  have hD1z : (1 : ℤ) ≤ dimFlag (dat p i) := by exact_mod_cast hD1
  have hsq : (dimFlag (dat p i) : ℤ) ≤ (dimFlag (dat p i) : ℤ) ^ 2 := by nlinarith
  push_cast at G ⊢
  by_cases hbp : (b : ℕ) = (dat p i).p
  · have g := (g2 hbp).2
    have hT0 : (0 : ℤ) < 4 * (lenT p i PP : ℤ) := by nlinarith
    have hle : (lenT p i PP : ℤ) ≤ u1 τ a - u1 τ b - 3 * (((dat p i).p + (dat p i).q : ℕ) : ℤ) := by
      by_contra hc
      push_neg at hc
      have := mul_lt_mul_of_pos_left hc hT0
      nlinarith
    push_cast at hle
    linarith
  · have g := g1 hbp
    push_cast at g
    linarith

end Point

end GlobalTheory.CovHt.GeomBound

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniquePullbackOfRaynaudTorusWeightZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniquePullbackOfRaynaudTorusWeightZero
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section
open GlobalTheory.TorusModel GlobalTheory.TorusExt GlobalTheory.Serre ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht

namespace GlobalTheory.Heat.Descend

variable {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X]
  {oa : Q.OAct O}

theorem q_props (Y : Ray oa) : Flat Y.q.left ∧ Surjective Y.q.left ∧ QuasiCompact Y.q.left := by
  obtain ⟨c⟩ := GlobalTheory.TorusModel.nonempty_gtCoord GlobalTheory.allSixLaws.1.globalFns Y.isGt ⊥ 0
  have := c.q_hom
  have := c.q_flat
  have := c.q_surj
  have := c.q_affine
  let F := fstG (⊥ : Ideal R) 0 Y.H
  let j := inv F.left
  have hF : F.left ≫ Y.H.hom = (thickObj R ⊥ 0 Y.H).hom ≫ thick R ⊥ 0 := Over.w F
  let ξ := Y.Φ Y.H (𝟙 _)
  obtain ⟨x, hx⟩ := GlobalTheory.TorusCoord.exists_point c (T := Y.H) (Y.H.hom ≫ inv (thick R ⊥ 0)) (by simp) ξ
  obtain ⟨ξ', hξ'⟩ := GlobalTheory.TorusCoord.exists_isPointOf c (T := Y.H) j (by
    rw [← hF]; exact IsIso.inv_hom_id_assoc _ _)
  let b : Y.H ⟶ Y.H := (Y.Φ Y.H).symm ξ'
  have hb : Y.Φ Y.H b = ξ' := Equiv.apply_symm_apply _ _
  let a := x ≫ F.left
  have ha : a ≫ Y.H.hom = Y.H.hom := by
    rw [Category.assoc, hF]
    exact GlobalTheory.TorusCoord.IsPointOf.comp_hom c hx
  let a' : Y.H ⟶ Y.H := Over.homMk a ha
  have haj : a ≫ j = x := by simp [a, j]
  have e1 : b.left ≫ x = j := by
    have h1 : GtPt.IsPull b.left ξ (Y.Φ Y.H (b ≫ 𝟙 _)) := Y.rep.1 Y.H Y.H b (𝟙 _)
    rw [Category.comp_id, hb] at h1
    exact (GlobalTheory.TorusCoord.IsPointOf.pull c hx h1).unique_left c hξ'
  have e1' : b.left ≫ a = 𝟙 _ := by
    rw [← Category.assoc, e1]; simp [j]
  have e2 : a' ≫ b = 𝟙 _ := by
    have h2 : GtPt.IsPull a (Y.Φ Y.H b) (Y.Φ Y.H (a' ≫ b)) := Y.rep.1 Y.H Y.H a' b
    rw [hb] at h2
    have h3 := GlobalTheory.TorusCoord.IsPointOf.pull c hξ' h2
    rw [haj] at h3
    exact (Y.Φ Y.H).injective (h3.unique_right c hx)
  have e2' : a ≫ b.left = 𝟙 _ := congrArg (·.left) e2
  have : IsIso a := ⟨⟨b.left, e2', e1'⟩⟩
  have hq : Y.q.left = a ≫ j ≫ c.q.left ≫ pullback.fst Q.P.A.hom (thick R ⊥ 0) := by
    rw [← Category.assoc a j, haj, ← GlobalTheory.TorusCoord.pG_left]
    exact hx.1
  rw [hq]
  exact ⟨inferInstance, inferInstance, inferInstance⟩

def chrUnit {S : Type} [CommRing S] {φ : R →+* S} (τ : Over.mk (spMap φ) ⟶ splitTorus (Sp R) (GlobalTheory.RayEv.Chr Q))
    (χ : GlobalTheory.RayEv.Chr Q) : Sˣ :=
  Units.map (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom.toMonoidHom
    (IsUnit.of_mul_eq_one (a := (coord τ).hom (AddMonoidAlgebra.single χ 1))
      ((coord τ).hom (AddMonoidAlgebra.single (-χ) 1)) (by
      rw [← map_mul, AddMonoidAlgebra.single_mul_single, add_neg_cancel, _root_.mul_one]
      exact map_one _)).unit

theorem unitOn_chrUnit {S : Type} [CommRing S] {φ : R →+* S}
    (τ : Over.mk (spMap φ) ⟶ splitTorus (Sp R) (GlobalTheory.RayEv.Chr Q)) (χ : GlobalTheory.RayEv.Chr Q) :
    (unitOn (chrUnit τ χ)).val = (coord τ).hom (AddMonoidAlgebra.single χ 1) := by
  simp [unitOn, chrUnit]

theorem cv_translate (Y : Ray oa) {S : Type} [CommRing S] {φ : R →+* S}
    (τ : Over.mk (spMap φ) ⟶ splitTorus (Sp R) (GlobalTheory.RayEv.Chr Q)) (x : Over.mk (spMap φ) ⟶ Y.H) :
    ∀ χ y J, Good Q.P.L y J →
      val ((Y.Φ _ ((τ ≫ Y.i) * x)).s χ) (𝟙 _) y J =
        gm (𝟙 (Over.mk (spMap φ)).left) y ⊤ (unitOn (chrUnit τ χ)) * val ((Y.Φ _ x).s χ) (𝟙 _) y J := by
  intro χ y J hJ
  have h1 := ((GlobalTheory.TorusModel.isAdd_iff _ _ _).1 (Y.rep.2 _ x (τ ≫ Y.i))).2 χ y J hJ
  have C : IsCub (DVR.th Q (T := Over.mk (spMap φ)) y J) := isCub_cubV Q.cub hJ
  rw [(Y.Φ_i τ).1, C.face₃, _root_.mul_one] at h1
  rw [mul_comm (τ ≫ Y.i) x]
  show GlobalTheory.TorusModel.cv _ χ y J = _ * GlobalTheory.TorusModel.cv _ χ y J
  rw [h1, mul_comm]
  congr 1
  apply Units.ext
  rw [(Y.Φ_i τ).2 χ y J hJ, ← gs_unit (𝟙 _) y ⊤ trivial]
  exact congrArg (gs (𝟙 _) y ⊤) (unitOn_chrUnit τ χ).symm

theorem invariant (Y : Ray oa) (V : Q.P.A.left.Opens) (f : Γ(Y.H.left, Y.q.left ⁻¹ᵁ V))
    (hf : IsWt Y 0 (Y.q.left ⁻¹ᵁ V) f) (Z : Over (Sp R)) (t : Z ⟶ splitTorus (Sp R) (GlobalTheory.RayEv.Chr Q)) (g : Z ⟶ Y.H)
    (h₁ : ⊤ ≤ ((t ≫ Y.i) * g).left ⁻¹ᵁ (Y.q.left ⁻¹ᵁ V)) (h₂ : ⊤ ≤ g.left ⁻¹ᵁ (Y.q.left ⁻¹ᵁ V)) :
    (((t ≫ Y.i) * g).left.appLE _ ⊤ h₁).hom f = (g.left.appLE _ ⊤ h₂).hom f := by
  rw [← sub_eq_zero]
  refine GlobalTheory.Heat.Adjust.eq_zero_of_valR_points ⊤ _ fun S _ p hp => ?_
  rw [WtAlg.valR_sub' p ⊤ hp, HolHom.valR_appLE p _ _ _ _ _ hp, HolHom.valR_appLE p _ _ _ _ _ hp, sub_eq_zero]
  obtain ⟨φ', hφ'⟩ := Spec.map_surjective (R := CommRingCat.of R) (S := CommRingCat.of S) (p ≫ Z.hom)
  let φ : R →+* S := φ'.hom
  have hφ : p ≫ Z.hom = spMap φ := hφ'.symm
  let P : Over.mk (spMap φ) ⟶ Z := Over.homMk p hφ
  have hqm : IsMonHom Y.q := Y.q_linear.isMonHom
  have e : P ≫ ((t ≫ Y.i) * g) = ((P ≫ t) ≫ Y.i) * (P ≫ g) := by rw [MonObj.comp_mul, Category.assoc]
  have hq : (P ≫ ((t ≫ Y.i) * g)) ≫ Y.q = (P ≫ g) ≫ Y.q := by
    rw [e, MonObj.mul_comp, Category.assoc, Y.i_q, MonObj.comp_one, _root_.one_mul]
  have hc : ∀ χ y J, Good Q.P.L y J →
      val ((Y.Φ _ (P ≫ ((t ≫ Y.i) * g))).s χ) (𝟙 _) y J =
        gm (𝟙 (Over.mk (spMap φ)).left) y ⊤ (unitOn (chrUnit (P ≫ t) χ)) * val ((Y.Φ _ (P ≫ g)).s χ) (𝟙 _) y J := by
    rw [e]; exact cv_translate Y (P ≫ t) (P ≫ g)
  have key := hf S φ (P ≫ g) (P ≫ ((t ≫ Y.i) * g)) (chrUnit (P ≫ t)) _ _ rfl rfl
    (fun z _ => h₂ (Set.mem_univ (p z))) (fun z _ => h₁ (Set.mem_univ (p z))) hq hc
  rw [WtAlg.c_zero _ _ _ hc, Units.val_one, _root_.one_mul] at key
  exact key

end GlobalTheory.Heat.Descend

namespace GlobalTheory.Heat

theorem exists_unique_pbT_of_isWt_zero : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (V : Q.P.A.left.Opens) (f : Γ(Y.H.left, Y.q.left ⁻¹ᵁ V)), IsWt Y 0 _ f → ∃! f' : Γ(Q.P.A.left, V), pbT Y.q.left f' (Y.q.left ⁻¹ᵁ V) = f := by
  intro R _ _ Q O _ _ _ oa Y V f hf
  obtain ⟨h1, h2, h3⟩ := Descend.q_props Y
  have H := GlobalTheory.invariant_functions_descend (Sp R) Y.H Q.P.A _ Y.q Y.i Y.q_linear.isMonHom Y.i_linear.isMonHom
    h1 h2 h3 Y.isKernel V
  have hp : ∀ f', pbT Y.q.left f' (Y.q.left ⁻¹ᵁ V) = (Y.q.left.app V).hom f' := fun f' => by
    rw [GlobalTheory.KS.pbT_of_le _ le_rfl, Scheme.Hom.app_eq_appLE]
  obtain ⟨a, ha⟩ := H.2.2 f (fun Z t g h₁ h₂ => Descend.invariant Y V f hf Z t g h₁ h₂)
  exact ⟨a, (hp a).trans ha, fun b hb => H.1 (((hp b).symm.trans hb).trans ha.symm)⟩

end GlobalTheory.Heat
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniquePullbackOfRaynaudTorusWeightZeroStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_pullback_of_raynaudTorusWeight_zero : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (V : Q.P.A.left.Opens) (f : Γ(Y.H.left, Y.q.left ⁻¹ᵁ V)), IsWt Y 0 _ f → ∃! f' : Γ(Q.P.A.left, V), pbT Y.q.left f' (Y.q.left ⁻¹ᵁ V) = f := by
  first | exact @GlobalTheory.Heat.exists_unique_pbT_of_isWt_zero | exact GlobalTheory.Heat.exists_unique_pbT_of_isWt_zero | (intros; apply GlobalTheory.Heat.exists_unique_pbT_of_isWt_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinOrderIsRingActionOnProduct
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinOrderIsRingActionOnProduct
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

noncomputable section

namespace GlobalTheory.ZarhinFam.RAct

section Grp

variable {M M' : Type*} [CommGroup M] [CommGroup M']

def E (x y : Fin 4 → M) (α β : Fin 4 → ℤ) : M := ∏ k, x k ^ α k * y k ^ β k

theorem map_E (f : M →* M') (x y : Fin 4 → M) (α β : Fin 4 → ℤ) :
    f (E x y α β) = E (fun k => f (x k)) (fun k => f (y k)) α β := by
  simp only [E, map_prod, map_mul, map_zpow]

theorem E_zero (x y : Fin 4 → M) : E x y 0 0 = 1 := by simp [E]

theorem E_add (x y : Fin 4 → M) (α β α' β' : Fin 4 → ℤ) :
    E x y (α + α') (β + β') = E x y α β * E x y α' β' := by
  simp only [E, Pi.add_apply, zpow_add, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun k _ => mul_mul_mul_comm _ _ _ _

theorem E_zsmul (x y : Fin 4 → M) (n : ℤ) (α β : Fin 4 → ℤ) :
    E x y (n • α) (n • β) = E x y α β ^ n := by
  simp only [E, ← Finset.prod_zpow, Pi.smul_apply, smul_eq_mul]
  exact Finset.prod_congr rfl fun k _ => by
    rw [mul_zpow, ← zpow_mul, ← zpow_mul, mul_comm (α k), mul_comm (β k)]

theorem E_sum {J : Type*} (s : Finset J) (x y : Fin 4 → M) (α β : J → Fin 4 → ℤ) :
    E x y (∑ j ∈ s, α j) (∑ j ∈ s, β j) = ∏ j ∈ s, E x y (α j) (β j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, Finset.prod_empty]; exact E_zero x y
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, Finset.prod_insert hj, E_add, ih]

theorem E_nest (x y : Fin 4 → M) (a b c e : Fin 4 → Fin 4 → ℤ) (gm dl : Fin 4 → ℤ) :
    E (fun j => E x y (a j) (b j)) (fun j => E x y (c j) (e j)) gm dl =
      E x y (∑ j, (gm j • a j + dl j • c j)) (∑ j, (gm j • b j + dl j • e j)) := by
  rw [E_sum]
  exact Finset.prod_congr rfl fun j _ => by rw [E_add, E_zsmul, E_zsmul]

theorem E_mul (x y x' y' : Fin 4 → M) (α β : Fin 4 → ℤ) :
    E (fun k => x k * x' k) (fun k => y k * y' k) α β = E x y α β * E x' y' α β := by
  simp only [E, mul_zpow, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun k _ => mul_mul_mul_comm _ _ _ _

theorem E_pow_left (x y : Fin 4 → M) (n : ℕ) (α β : Fin 4 → ℤ) :
    E (fun k => x k ^ n) y α β = E x y ((n : ℤ) • α) β := by
  simp only [E, Pi.smul_apply, smul_eq_mul]
  exact Finset.prod_congr rfl fun k _ => by rw [← zpow_natCast, ← zpow_mul]

theorem E_pow_right (x y : Fin 4 → M) (n : ℕ) (α β : Fin 4 → ℤ) :
    E x (fun k => y k ^ n) α β = E x y α ((n : ℤ) • β) := by
  simp only [E, Pi.smul_apply, smul_eq_mul]
  exact Finset.prod_congr rfl fun k _ => by rw [← zpow_natCast (y k), ← zpow_mul]

end Grp

section Hom

variable {S : Scheme.{0}}

theorem isMonHom_of_mul_comp {G H : Over S} [GrpObj G] [GrpObj H] (f : G ⟶ H)
    (h : ∀ (T : Over S) (x y : T ⟶ G), (x * y) ≫ f = (x ≫ f) * (y ≫ f)) : IsMonHom f := by
  refine ⟨?_, ?_⟩
  · rw [MonObj.one_eq_one G, MonObj.one_eq_one H]
    exact map_one (MonoidHom.mk' (fun x : 𝟙_ (Over S) ⟶ G ↦ x ≫ f) (h _))
  · rw [MonObj.mul_eq_mul G, MonObj.mul_eq_mul H, MonObj.comp_mul, tensorHom_fst, tensorHom_snd]
    exact h _ _ _

def preHom {T T' G : Over S} [GrpObj G] (p : T' ⟶ T) : (T ⟶ G) →* (T' ⟶ G) :=
  MonoidHom.mk' (fun a => p ≫ a) fun a b => MonObj.comp_mul p a b

def postHom {T G H : Over S} [GrpObj G] [GrpObj H] (g : G ⟶ H) [IsMonHom g] : (T ⟶ G) →* (T ⟶ H) :=
  MonoidHom.mk' (fun a => a ≫ g) fun a b => MonObj.mul_comp a b g

theorem comp_E {T T' G : Over S} [GrpObj G] [IsCommMonObj G] (p : T' ⟶ T) (x y : Fin 4 → (T ⟶ G))
    (α β : Fin 4 → ℤ) : p ≫ E x y α β = E (fun k => p ≫ x k) (fun k => p ≫ y k) α β :=
  map_E (preHom p) x y α β

theorem E_comp {T G H : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj H] [IsCommMonObj H] (g : G ⟶ H) [IsMonHom g]
    (x y : Fin 4 → (T ⟶ G)) (α β : Fin 4 → ℤ) : E x y α β ≫ g = E (fun k => x k ≫ g) (fun k => y k ≫ g) α β :=
  map_E (postHom g) x y α β

end Hom

section Zob

variable {S : Scheme.{0}} (A B : Over S) [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B]

abbrev Mt := Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ

theorem mkZ_pa {T : Over S} (u : Fin 4 → (T ⟶ A)) (v : Fin 4 → (T ⟶ B)) (i : Fin 4) :
    mkZ A B u v ≫ pa A B i = u i := by
  simp only [mkZ, pa, lift_fst_assoc]
  exact (Out.powIsLimit A 4).fac (Fan.mk T u) ⟨i⟩

theorem mkZ_pb {T : Over S} (u : Fin 4 → (T ⟶ A)) (v : Fin 4 → (T ⟶ B)) (j : Fin 4) :
    mkZ A B u v ≫ pb A B j = v j := by
  simp only [mkZ, pb, lift_snd_assoc]
  exact (Out.powIsLimit B 4).fac (Fan.mk T v) ⟨j⟩

theorem hom_ext {T : Over S} {f g : T ⟶ Zob A B} (ha : ∀ i, f ≫ pa A B i = g ≫ pa A B i)
    (hb : ∀ j, f ≫ pb A B j = g ≫ pb A B j) : f = g := by
  apply CartesianMonoidalCategory.hom_ext
  · apply (Out.powIsLimit A 4).hom_ext
    rintro ⟨i⟩
    simpa [pa] using ha i
  · apply (Out.powIsLimit B 4).hom_ext
    rintro ⟨j⟩
    simpa [pb] using hb j

instance pa_isMonHom (i : Fin 4) : IsMonHom (pa A B i) := by unfold pa; infer_instance

instance pb_isMonHom (j : Fin 4) : IsMonHom (pb A B j) := by unfold pb; infer_instance

variable {A B} (d : ℕ) (la : A ⟶ B) (mu : B ⟶ A)

theorem actZ_pa (N : ord d) (i : Fin 4) :
    actZ A B d la mu N ≫ pa A B i =
      E (fun k => pa A B k) (fun k => pb A B k ≫ mu) (fun j => (N : Mt) (.inl j) (.inl i))
        (fun j => (N : Mt) (.inr j) (.inl i) / (d : ℤ)) := by
  rw [actZ, mkZ_pa]; rfl

theorem actZ_pb (N : ord d) (i : Fin 4) :
    actZ A B d la mu N ≫ pb A B i =
      E (fun k => pa A B k ≫ la) (fun k => pb A B k) (fun j => (N : Mt) (.inl j) (.inr i))
        (fun j => (N : Mt) (.inr j) (.inr i)) := by
  rw [actZ, mkZ_pb]; rfl

variable {d la mu}

theorem actZ_pb_mu [IsMonHom mu] (hla : la ≫ mu = 𝟙 A ^ d) (N : ord d) (i : Fin 4) :
    actZ A B d la mu N ≫ pb A B i ≫ mu =
      E (fun k => pa A B k) (fun k => pb A B k ≫ mu) ((d : ℤ) • fun j => (N : Mt) (.inl j) (.inr i))
        (fun j => (N : Mt) (.inr j) (.inr i)) := by
  rw [← Category.assoc, actZ_pb, E_comp]
  have e : ∀ k, (pa A B k ≫ la) ≫ mu = pa A B k ^ d := fun k => by
    rw [Category.assoc, hla, MonObj.comp_pow, Category.comp_id]
  simp only [e, Category.assoc]
  exact E_pow_left (fun k => pa A B k) _ d _ _

theorem actZ_pa_la [IsMonHom la] (hml : mu ≫ la = 𝟙 B ^ d) (N : ord d) (i : Fin 4) :
    actZ A B d la mu N ≫ pa A B i ≫ la =
      E (fun k => pa A B k ≫ la) (fun k => pb A B k) (fun j => (N : Mt) (.inl j) (.inl i))
        ((d : ℤ) • fun j => (N : Mt) (.inr j) (.inl i) / (d : ℤ)) := by
  rw [← Category.assoc, actZ_pa, E_comp]
  have e : ∀ k, (pb A B k ≫ mu) ≫ la = pb A B k ^ d := fun k => by
    rw [Category.assoc, hml, MonObj.comp_pow, Category.comp_id]
  simp only [e]
  exact E_pow_right _ (fun k => pb A B k) d _ _

theorem actZ_isMonHom [IsMonHom la] [IsMonHom mu] (N : ord d) : IsMonHom (actZ A B d la mu N) := by
  refine isMonHom_of_mul_comp _ fun T x y => hom_ext A B (fun i => ?_) (fun i => ?_)
  · simp only [Category.assoc, actZ_pa, MonObj.mul_comp, comp_E]
    exact E_mul _ _ _ _ _ _
  · simp only [Category.assoc, actZ_pb, MonObj.mul_comp, comp_E]
    exact E_mul _ _ _ _ _ _

theorem actZ_one : actZ A B d la mu 1 = 𝟙 _ := by
  refine hom_ext A B (fun i => ?_) (fun i => ?_)
  · rw [actZ_pa, Category.id_comp]
    simp [E, Matrix.one_apply]
  · rw [actZ_pb, Category.id_comp]
    simp [E, Matrix.one_apply]

theorem actZ_add (N N' : ord d) : actZ A B d la mu (N + N') = actZ A B d la mu N * actZ A B d la mu N' := by
  refine hom_ext A B (fun i => ?_) (fun i => ?_)
  · rw [MonObj.mul_comp, actZ_pa, actZ_pa, actZ_pa, ← E_add]
    congr 1
    funext j
    exact Int.add_ediv_of_dvd_left (N.2 j i)
  · rw [MonObj.mul_comp, actZ_pb, actZ_pb, actZ_pb, ← E_add]
    congr 1 <;> funext j <;> simp

theorem actZ_mul [IsMonHom la] [IsMonHom mu] (hla : la ≫ mu = 𝟙 A ^ d) (hml : mu ≫ la = 𝟙 B ^ d) (hd : 0 < d)
    (N N' : ord d) : actZ A B d la mu (N * N') = actZ A B d la mu N ≫ actZ A B d la mu N' := by
  have hd0 : (d : ℤ) ≠ 0 := by exact_mod_cast hd.ne'
  obtain ⟨q, hq⟩ : ∃ q : Fin 4 → Fin 4 → ℤ, ∀ i j, (N : Mt) (.inr i) (.inl j) = d * q i j :=
    ⟨fun i j => Classical.choose (N.2 i j), fun i j => Classical.choose_spec (N.2 i j)⟩
  obtain ⟨q', hq'⟩ : ∃ q : Fin 4 → Fin 4 → ℤ, ∀ i j, (N' : Mt) (.inr i) (.inl j) = d * q i j :=
    ⟨fun i j => Classical.choose (N'.2 i j), fun i j => Classical.choose_spec (N'.2 i j)⟩
  refine hom_ext A B (fun i => ?_) (fun i => ?_)
  · simp only [Category.assoc, actZ_pa, comp_E, actZ_pb_mu hla]
    rw [E_nest]
    congr 1 <;> funext k
    · simp only [Subring.coe_mul, Matrix.mul_apply, Fintype.sum_sum_type, Finset.sum_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul, hq', Int.mul_ediv_cancel_left _ hd0]
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun x _ => by ring
    · simp only [Subring.coe_mul, Matrix.mul_apply, Fintype.sum_sum_type, Finset.sum_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul, hq, hq', Int.mul_ediv_cancel_left _ hd0]
      refine Int.ediv_eq_of_eq_mul_right hd0 ?_
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun x _ => by ring
  · simp only [Category.assoc, actZ_pb, comp_E, actZ_pa_la hml]
    rw [E_nest]
    congr 1 <;> funext k
    · simp only [Subring.coe_mul, Matrix.mul_apply, Fintype.sum_sum_type, Finset.sum_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul]
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun x _ => by ring
    · simp only [Subring.coe_mul, Matrix.mul_apply, Fintype.sum_sum_type, Finset.sum_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul, hq, Int.mul_ediv_cancel_left _ hd0]
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun x _ => by ring

end Zob

theorem actZ_isRAct : ∀ (h M d : ℕ) (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t)
    (B : Over S) [GrpObj B] [IsCommMonObj B] (Q : LB (c.A ⊗ B).left) (la : c.A ⟶ B) (mu : B ⟶ c.A)
    (hZ : GlobalTheory.ZarhinFam.ZData c d B Q la mu), 1 ≤ h → 3 ≤ M → Odd M → 0 < d → M.Coprime d →
    IsUnit ((d : ℕ) : Γ(S, ⊤)) → SiegKerBy c d →
    IsRAct (GlobalTheory.ZarhinFam.Zob c.A B) (GlobalTheory.ZarhinFam.actZ c.A B d la mu) := by
  intro h M d S t c B _ _ Q la mu hZ _ _ _ hd _ _ _
  obtain ⟨-, -, -, hla, hmu, hlm, hml, -⟩ := hZ
  haveI := hla
  haveI := hmu
  exact ⟨fun N => actZ_isMonHom N, actZ_one, fun N N' => actZ_mul hlm hml hd N N', fun N N' => actZ_add N N'⟩

end GlobalTheory.ZarhinFam.RAct
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinOrderIsRingActionOnProductStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zarhinOrder_isRingAction_on_product : ∀ (h M d : ℕ) (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (B : Over S) [GrpObj B] [IsCommMonObj B] (Q : LB (c.A ⊗ B).left) (la : c.A ⟶ B) (mu : B ⟶ c.A) (hZ : GlobalTheory.ZarhinFam.ZData c d B Q la mu), 1 ≤ h → 3 ≤ M → Odd M → 0 < d → M.Coprime d → IsUnit ((d : ℕ) : Γ(S, ⊤)) → SiegKerBy c d → IsRAct (GlobalTheory.ZarhinFam.Zob c.A B) (GlobalTheory.ZarhinFam.actZ c.A B d la mu) := by
  first | (exact @GlobalTheory.ZarhinFam.RAct.actZ_isRAct) | (exact GlobalTheory.ZarhinFam.RAct.actZ_isRAct) | (intros; apply GlobalTheory.ZarhinFam.RAct.actZ_isRAct <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreKilled
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory.KerKilledNear

def FibreKilled (d : ℕ) {S' : Scheme.{0}} (G : Over S') [GrpObj G] (P : LB (G2 G).left) (s : S') : Prop :=
  ∀ (T' : Over S') (x : T' ⟶ G),
    (∃ f : T'.left ⟶ Spec (S'.residueField s), T'.hom = f ≫ S'.fromSpecResidueField s) →
    (∃ c : (P.pull (lift (snd G T' ≫ x) (fst G T')).left).Gen, c.IsGen) → x ^ d = 1

end GlobalTheory.KerKilledNear
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProjOverOfCompactB
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

namespace GlobalTheory.UPel.HT

theorem Model.isProjOver_of_compactB (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R]
    [IsDomain R] [CharZero R] [IsNoetherianRing R] (b : Base D R) (N : ℕ) (_hN : 3 ≤ N) (_hNp : N.Coprime p)
    (hD : D.CompactB) (M : Model b N) : IsProjOver M.s :=
  GlobalTheory.UPel.isProjOver_of_isQProjOver_of_isProper R M.X M.s M.qproj
    (GlobalTheory.T.harrisTaylor_integralModel_isProper_of_compact p D R b N M hD)

end GlobalTheory.UPel.HT
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvariantFieldCoefficientsOfLinearVectorFi
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVectorFieldCoeffsGluedFromAffineOpens
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVectorFieldCoeffsGluedFromAffineOpens
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TangentOrigin

noncomputable section

namespace GlobalTheory.VertCoeffGlue

theorem affine_cover {X : Scheme.{0}} (O : X.Opens) :
    O ≤ ⨆ l : {V : X.Opens // IsAffineOpen V ∧ V ≤ O}, l.1 := by
  intro x hx
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hle⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (show x ∈ (O : Set X) from hx) O.isOpen
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨U, hU, fun y hy => hle hy⟩, hxU⟩

theorem exists_coeff : ∀ {X : Scheme.{0}} {n : ℕ} (W : X.Opens) (δ : Fld X) (dd : Fin n → Fld X), IsField W δ → (∀ a, IsField ⊤ (dd a)) →
    (∀ V V' : X.Opens, IsAffineOpen V → IsAffineOpen V' → V ≤ W → V' ≤ V →
      ∃! c : Fin n → Γ(X, V'), ∀ f : Γ(X, V), rsT (δ V f) V' = ∑ a, c a * rsT (dd a V f) V') →
    ∃ c : Fin n → Γ(X, W), ∀ O, O ≤ W → ∀ f, δ O f = ∑ a, rsT (c a) O * dd a O f := by
  intro X n W δ dd hδ hdd H
  let J : Type := {V : X.Opens // IsAffineOpen V ∧ V ≤ W}
  choose c hc using fun j : J => (H j.1 j.1 j.2.1 j.2.1 j.2.2 le_rfl).exists
  have hl : ∀ (l : J) (O : X.Opens) (h : l.1 ≤ O), O ≤ W → ∀ f : Γ(X, O),
      rsT (δ O f) l.1 = ∑ a, c l a * rsT (dd a O f) l.1 := by
    intro l O h hO f
    have e1 := hδ.2.2 O l.1 h hO f
    have e2 := hc l (resG X h f)
    simp only [GlobalTheory.KS.rsT_self] at e2
    rw [GlobalTheory.KS.rsT_of_le h, ← e1, e2]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [(hdd a).2.2 O l.1 h le_top f, GlobalTheory.KS.rsT_of_le h]
  have sub : ∀ j l : J, l.1 ≤ j.1 → ∀ a, rsT (c j a) l.1 = c l a := by
    intro j l h a
    refine congrFun ((H j.1 l.1 j.2.1 l.2.1 j.2.2 h).unique (y₁ := fun a => rsT (c j a) l.1) (y₂ := c l) ?_ ?_) a
    · intro f
      have := hc j f
      simp only [GlobalTheory.KS.rsT_self] at this
      rw [this, GlobalTheory.KS.rsT_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [GlobalTheory.KS.rsT_mul]
    · exact hl l j.1 h j.2.2
  have glue : ∀ a, ∃ s : Γ(X, W), ∀ j : J, rsT s j.1 = c j a := fun a => by
    refine GlobalTheory.KS.exists_rsT_eq (fun j : J => j.1) (fun j => j.2.2) (affine_cover W) (fun j => c j a)
      fun j k => ?_
    refine GlobalTheory.KS.eq_of_rsT_eq (fun l : {V : X.Opens // IsAffineOpen V ∧ V ≤ j.1 ⊓ k.1} => l.1)
      (fun l => l.2.2) (affine_cover _) _ _ fun l => ?_
    have hj : l.1 ≤ j.1 := l.2.2.trans inf_le_left
    have hk : l.1 ≤ k.1 := l.2.2.trans inf_le_right
    rw [GlobalTheory.KS.rsT_rsT inf_le_left l.2.2, GlobalTheory.KS.rsT_rsT inf_le_right l.2.2,
      sub j ⟨l.1, l.2.1, hj.trans j.2.2⟩ hj, sub k ⟨l.1, l.2.1, hk.trans k.2.2⟩ hk]
  choose s hs using glue
  refine ⟨s, fun O hO f => ?_⟩
  refine GlobalTheory.KS.eq_of_rsT_eq (fun l : {V : X.Opens // IsAffineOpen V ∧ V ≤ O} => l.1) (fun l => l.2.2)
    (affine_cover O) _ _ fun l => ?_
  rw [hl ⟨l.1, l.2.1, l.2.2.trans hO⟩ O l.2.2 hO f, GlobalTheory.KS.rsT_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [GlobalTheory.KS.rsT_mul, GlobalTheory.KS.rsT_rsT hO l.2.2, hs a ⟨l.1, l.2.1, l.2.2.trans hO⟩]

end GlobalTheory.VertCoeffGlue
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVectorFieldCoeffsGluedFromAffineOpensStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TangentOrigin

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_vectorField_coeffs_glued_from_affineOpens : ∀ {X : Scheme.{0}} {n : ℕ} (W : X.Opens) (δ : Fld X) (dd : Fin n → Fld X), IsField W δ → (∀ a, IsField ⊤ (dd a)) →
    (∀ V V' : X.Opens, IsAffineOpen V → IsAffineOpen V' → V ≤ W → V' ≤ V →
      ∃! c : Fin n → Γ(X, V'), ∀ f : Γ(X, V), rsT (δ V f) V' = ∑ a, c a * rsT (dd a V f) V') →
    ∃ c : Fin n → Γ(X, W), ∀ O, O ≤ W → ∀ f, δ O f = ∑ a, rsT (c a) O * dd a O f := by
  first | exact @GlobalTheory.VertCoeffGlue.exists_coeff | exact GlobalTheory.VertCoeffGlue.exists_coeff | (intros; apply GlobalTheory.VertCoeffGlue.exists_coeff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvariantFieldCoefficientsOfLinearVectorFi
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.VertCoeffRing
open GlobalTheory.TangentOrigin
open GlobalTheory.KS (rsT_add rsT_mul rsT_zero)

variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]

theorem evalPt_lieExp {m : ℕ} (u : Fin m → TanM (𝟙 (Sp R)) G) (dd : Fin m → Fld G.left)
    (hd : ∀ i, IsInv G (u i) (dd i)) (B : Type) [CommRing B] [Algebra R B] (e : Fin m → B)
    (he : ∀ i j, e i * e j = 0) (z : ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := R) B ⟶ G) (O : G.left.Opens)
    (h : ⊤ ≤ z.left ⁻¹ᵁ O) :
    ∃ h' : ⊤ ≤ (GlobalTheory.SqZero.lieExp (fun i => tvE (u i)) e (fun i => he i i) * z).left ⁻¹ᵁ O, ∀ f,
      evalPt _ O h' f = evalPt z.left O h f + ∑ i, e i * evalPt z.left O h (dd i O f) := by
  induction m with
  | zero =>
    have : GlobalTheory.SqZero.lieExp (fun i => tvE (u i)) e (fun i => he i i) * z = z := by
      simp [GlobalTheory.SqZero.lieExp]
    rw [this]
    exact ⟨h, fun f => by simp⟩
  | succ m ih =>
    obtain ⟨h₁, H₁⟩ := ih (fun i => u i.succ) (fun i => dd i.succ) (fun i => hd i.succ) (fun i => e i.succ)
      (fun i j => he _ _)
    obtain ⟨h₂, H₂⟩ := GlobalTheory.T.value_at_invariantField_translate_sqZero (hd 0) (e 0) (he 0 0) _ O h₁
    have : GlobalTheory.SqZero.lieExp (fun i => tvE (u i)) e (fun i => he i i) * z =
        (ReciprocityTheory.ChartRestriction.G.Chart.spMap (GlobalTheory.SqZero.epsTo R (e 0) (he 0 0)) ≫ tvE (u 0)) *
          (GlobalTheory.SqZero.lieExp (fun i => tvE (u i.succ)) (fun i => e i.succ) (fun i => he i.succ i.succ) * z) := by
      rw [GlobalTheory.SqZero.lieExp, GlobalTheory.SqZero.lieExp, Fin.prod_univ_succ, _root_.mul_assoc]
    rw [this]
    refine ⟨h₂, fun f => ?_⟩
    rw [H₂, H₁, H₁, Fin.sum_univ_succ, mul_add, Finset.mul_sum]
    simp only [← _root_.mul_assoc, he, zero_mul, Finset.sum_const_zero]
    ring

theorem exists_coeff : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], Smooth G.hom →
    ∀ (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) G)) (dd : Fin n → Fld G.left), (∀ a, IsInv G (v a) (dd a)) →
    ∀ (W : G.left.Opens) (δ : Fld G.left), IsField W δ → (∀ O, O ≤ W → ∀ r, δ O (constFn G.hom O r) = 0) →
    ∃ c : Fin n → Γ(G.left, W), ∀ O, O ≤ W → ∀ f, δ O f = ∑ a, rsT (c a) O * dd a O f := by
  intro R _ G _ _ hs n v dd hd W δ hδ hc
  have hb := GlobalTheory.T.isLieBasis_dualPoints_of_tangentModule_basis v
  refine GlobalTheory.T.exists_vectorField_coeffs_glued_from_affineOpens W δ dd hδ (fun a => (hd a).1) fun V V' hV hV' hVW hV'V => ?_
  exact GlobalTheory.T.existsUnique_lieBasis_coeffs_of_derivation_affineOpen _ hb dd (fun B _ _ e he z O h => evalPt_lieExp v dd hd B e he z O h) V V' hV hV' hV'V
    (fun f => rsT (δ V f) V') (fun f f' => by simp only [hδ.1 V hVW, rsT_add])
    (fun f f' => by simp only [hδ.2.1 V hVW, rsT_add, rsT_mul])
    (fun r => by simp only [hc V hVW r, rsT_zero])

end GlobalTheory.VertCoeffRing
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvariantFieldCoefficientsOfLinearVectorFiStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_invariant_field_coefficients_of_linear_vectorField : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], Smooth G.hom →
    ∀ (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) G)) (dd : Fin n → Fld G.left), (∀ a, IsInv G (v a) (dd a)) →
    ∀ (W : G.left.Opens) (δ : Fld G.left), IsField W δ → (∀ O, O ≤ W → ∀ r, δ O (constFn G.hom O r) = 0) →
    ∃ c : Fin n → Γ(G.left, W), ∀ O, O ≤ W → ∀ f, δ O f = ∑ a, rsT (c a) O * dd a O f := by
  first | exact @GlobalTheory.VertCoeffRing.exists_coeff | exact GlobalTheory.VertCoeffRing.exists_coeff | (intros; apply GlobalTheory.VertCoeffRing.exists_coeff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjointCancelNonzeroMultiple
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AdjCancel

variable {K : Type} [Field K]

theorem evc_zpow {A A' : AbVar K} {P : LB (A.X ⊗ A'.X).left} (hP : AbDual.IsDual A.X A'.X P)
    {Y : Over (Sp K)} (a : Y ⟶ A.X) (b : Y ⟶ A'.X) (k : ℤ) :
    AbDual.evc hP.isLB a (b ^ k) = k • AbDual.evc hP.isLB a b ∧ AbDual.evc hP.isLB a 1 = 0 := by
  let F : (Y ⟶ A'.X) →* Multiplicative (Pic Y.left) :=
    MonoidHom.mk' (fun b => Multiplicative.ofAdd (AbDual.evc hP.isLB a b)) (fun b b' => by
      rw [GlobalTheory.T.poincareClass_additive_in_dual_variable K A A' P hP Y a b b']; rfl)
  refine ⟨?_, ?_⟩
  · have := map_zpow F b k
    exact this
  · have := map_one F
    exact this

end GlobalTheory.AdjCancel
end
