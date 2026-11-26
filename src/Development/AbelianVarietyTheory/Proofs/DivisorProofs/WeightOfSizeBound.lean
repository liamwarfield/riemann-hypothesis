module

public import Development.AbelianVarietyTheory.Definitions.Divisors.TieTest
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanSectionFlatWeight
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSetupDividingLabelPersistsDeeperLevel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologicalLocalComponentExponents
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSphericalTwistOfUnr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.E8ThetaSetupGenericPointExists
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDoubledSchrodingerModelTransposedSiegelRul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularLocalStatementStatement
public import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.DifferentiableAtChart

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightOfSizeBound
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim

namespace GlobalTheory.BigTop.Fun

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.FunObj.SqNum GlobalTheory.SignedHC

section Arith

variable {D : D7}

theorem rankV_lt_gap {i j : ℕ} (hi : i < D.R.m) (hj : j < D.R.m) : rankV D (i + 1) (j + 1) < gap D 1 := by
  have h1 : (j + 1) * D.R.t ≤ D.R.m * D.R.t := Nat.mul_le_mul_right _ hj
  have h2 : (i + 1) * sLen D ≤ D.R.m * sLen D := Nat.mul_le_mul_right _ hi
  have h3 : rankV D (i + 1) (j + 1) ≤ bigN D := by
    have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
    have hk := D.R.m_add_three_le_k
    unfold rankV bigN
    rw [mul_add, mul_add, mul_one]
    omega
  have h4 := (isLeast_gap D 1).1.2.1
  have h5 : bigN D ≤ bigN D ^ 3 := Nat.le_self_pow (by norm_num) _
  omega

theorem numE_bounds {L : SizeData₂ D} (hs : GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows L) (τ : D.what₂.Tau) {j : ℕ} (hj : j < D.R.m) :
    0 ≤ (num D 1 τ).e (j + 1) ∧ ((num D 1 τ).e (j + 1) : ℝ) ≤ 4 * L.sc.b := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hbe, -⟩ := hs
  have e1 : (D.hc τ).e ⟨j, hj⟩ = ((num D 1 τ).e (j + 1) : ℚ) :=
    (GridData.ofHCParam_spec (D.hc τ) (sLen D) (gap D 1) (cen D 1 τ)).2.2 ⟨j, hj⟩
  obtain ⟨hb0, he4⟩ := hbe τ ⟨j, hj⟩
  have hg := (D.hc τ).gap_be ⟨j, hj⟩
  have ht : (0 : ℚ) ≤ D.R.t := by positivity
  rw [e1] at hg he4
  refine ⟨?_, by exact_mod_cast he4⟩
  have : (0 : ℚ) ≤ ((num D 1 τ).e (j + 1) : ℚ) := by linarith
  exact_mod_cast this

theorem cen_bounds {L : SizeData₂ D} (hs : GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows L) (τ : D.what₂.Tau) {i : ℕ} (h1 : 1 ≤ i)
    (h2 : i ≤ D.R.m) : 0 ≤ cen D 1 τ i ∧ (cen D 1 τ i : ℝ) ≤ L.sc.b := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hgap, -, -⟩ := hs
  set G0 := GridData.ofHCParam (D.hc τ) (sLen D) (gap D 1) 0 with hG0
  have hk := D.R.m_add_three_le_k
  have ev : (D.hc τ).v ⟨0, by omega⟩ = (G0.v 2 : ℚ) :=
    (GridData.ofHCParam_spec (D.hc τ) (sLen D) (gap D 1) 0).1 ⟨0, by omega⟩
  obtain ⟨v0, v1⟩ := L.cloud_v τ ⟨0, by omega⟩
  rw [ev] at v0 v1
  have hmid : G0.mid i = (G0.v 2 : ℚ) + 1 / 2 + ((D.R.m : ℚ) + 1 - i) * (gap D 1 : ℚ) + (gap D 1 : ℚ) / 2 :=
    G0.mid_eq h1
  have hc : cen D 1 τ i = ⌊G0.mid i⌋ := rfl
  have hS := L.Sc_pos
  have hi1 : (1 : ℝ) ≤ i := by exact_mod_cast h1
  have hi2 : (i : ℝ) ≤ D.R.m := by exact_mod_cast h2
  have hγ : (0 : ℝ) ≤ gap D 1 := by positivity
  have hmR : ((G0.mid i : ℚ) : ℝ) = (G0.v 2 : ℝ) + 1 / 2 + ((D.R.m : ℝ) + 1 - i) * (gap D 1 : ℝ) + (gap D 1 : ℝ) / 2 := by
    rw [hmid]; push_cast; ring
  have v0' : (0 : ℝ) ≤ (G0.v 2 : ℝ) := by exact_mod_cast v0
  have v1' : (G0.v 2 : ℝ) ≤ L.Sc := by exact_mod_cast v1
  have m0 : (0 : ℝ) ≤ ((G0.mid i : ℚ) : ℝ) := by
    rw [hmR]; have : (0 : ℝ) ≤ ((D.R.m : ℝ) + 1 - i) * (gap D 1 : ℝ) := mul_nonneg (by linarith) hγ
    linarith
  have m1 : ((G0.mid i : ℚ) : ℝ) ≤ L.sc.b := by
    rw [hmR]
    have : ((D.R.m : ℝ) + 1 - i) * (gap D 1 : ℝ) + (gap D 1 : ℝ) / 2 ≤ ((D.R.m : ℝ) + 1) * gap D 1 := by nlinarith
    linarith
  have m0q : (0 : ℚ) ≤ G0.mid i := by exact_mod_cast m0
  refine ⟨hc ▸ Int.floor_nonneg.2 m0q, ?_⟩
  have hf : ((⌊G0.mid i⌋ : ℚ) : ℝ) ≤ ((G0.mid i : ℚ) : ℝ) := by exact_mod_cast Int.floor_le (G0.mid i)
  rw [hc]
  push_cast at hf ⊢
  linarith

theorem gap_le_b {L : SizeData₂ D} (hs : GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows L) : (gap D 1 : ℝ) ≤ L.sc.b ∧ 675 ≤ L.sc.b := by
  obtain ⟨-, -, -, hm, -, -, -, -, -, -, -, hgap, -, -⟩ := hs
  have hS := L.Sc_pos
  have h4 := (isLeast_gap D 1).1.2.1
  have h15 : 15 ≤ gap D 1 := by have : 6 ≤ sLen D := by unfold sLen; omega
                                omega
  have hγ : (15 : ℝ) ≤ gap D 1 := by exact_mod_cast h15
  have hm' : (44 : ℝ) ≤ D.R.m := by exact_mod_cast hm
  constructor <;> nlinarith

theorem maxWt_le {L : SizeData₂ D} (hs : GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows L) :
    1 ≤ (maxWt D 1 : ℝ) ∧ (maxWt D 1 : ℝ) ≤ 10 * L.sc.b ∧ 675 ≤ L.sc.b := by
  obtain ⟨hγb, hb⟩ := gap_le_b hs
  have key : ∀ x : Fin D.R.m × Fin D.R.m × D.what₂.Tau,
      max (wtA D 1 x.1 x.2.1 x.2.2).natAbs (wtA' D 1 x.1 x.2.1 x.2.2).natAbs ≤ ⌊10 * L.sc.b⌋₊ := by
    rintro ⟨i, j, τ⟩
    have hr := rankV_lt_gap (D := D) i.2 j.2
    have hij : rankV D i j ≤ rankV D (i + 1) (j + 1) := by unfold rankV; gcongr <;> omega
    have hbs : botSmall D i j ≤ rankV D (i + 1) (j + 1) := by unfold botSmall; omega
    have hbb : botBig D i j ≤ rankV D (i + 1) (j + 1) := by unfold botBig; omega
    have hp : rankV D i j % 2 ≤ 1 := Nat.le_of_lt_succ (Nat.mod_lt _ (by norm_num))
    obtain ⟨e0, e1⟩ := numE_bounds hs τ j.2
    obtain ⟨c0, c1⟩ := cen_bounds hs τ (i := D.R.m - i) (by omega) (by omega)
    dsimp only
    refine max_le (Nat.le_floor ?_) (Nat.le_floor ?_)
    · have hA : |wtA D 1 i j τ| ≤ 2 * (num D 1 τ).e (j + 1) + 1 + gap D 1 := by
        rw [abs_le]
        unfold wtA
        constructor <;> omega
      have hA' : |((wtA D 1 i j τ : ℤ) : ℝ)| ≤ 2 * ((num D 1 τ).e (j + 1) : ℝ) + 1 + (gap D 1 : ℝ) := by
        exact_mod_cast hA
      rw [Nat.cast_natAbs, Int.cast_abs]
      linarith
    · have hA : |wtA' D 1 i j τ| ≤ 2 * cen D 1 τ (D.R.m - i) + 1 + gap D 1 := by
        rw [abs_le]
        unfold wtA'
        constructor <;> omega
      have hA' : |((wtA' D 1 i j τ : ℤ) : ℝ)| ≤ 2 * (cen D 1 τ (D.R.m - i) : ℝ) + 1 + (gap D 1 : ℝ) := by
        exact_mod_cast hA
      rw [Nat.cast_natAbs, Int.cast_abs]
      linarith
  have hsup : maxWt D 1 ≤ max 1 ⌊10 * L.sc.b⌋₊ := max_le_max le_rfl (Finset.sup_le fun x _ => key x)
  have hfl : (⌊10 * L.sc.b⌋₊ : ℝ) ≤ 10 * L.sc.b := Nat.floor_le (by linarith)
  refine ⟨by exact_mod_cast le_max_left 1 _, ?_, hb⟩
  have : (maxWt D 1 : ℝ) ≤ ((max 1 ⌊10 * L.sc.b⌋₊ : ℕ) : ℝ) := by exact_mod_cast hsup
  rw [Nat.cast_max, Nat.cast_one] at this
  exact this.trans (max_le (by linarith) hfl)

end Arith

end GlobalTheory.BigTop.Fun

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InducedModelDominantCurveRestriction
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic
open Formalism.BasicNotions GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.VertForm

namespace GlobalTheory.NefHodgeTateAt

section Curves

variable {k : Type} [CommRing k] [Module.Finite ℤ k] {X : Scheme.{0}} {p : X ⟶ Sp k}

theorem topSelf_of_cls_eq_add (hp : IsProjOver p) {N A B : LB X} (hN : N.IsLB) (hA : A.IsLB) (hB : B.IsLB)
    (h : cls N hN = cls A hA + cls B hB) (Z : Scheme.{0}) (i : Z ⟶ X) [IsClosedImmersion i] (κ : Type) [Field κ] [Finite κ]
    [Algebra κ Γ(Z, ⊤)] (hd : topologicalKrullDim Z = 1) :
    topSelfIntersection κ (N.pull i) 1 = topSelfIntersection κ (A.pull i) 1 + topSelfIntersection κ (B.pull i) 1 := by
  obtain ⟨hpr, H, hH⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hp
  have : IsFinite (spMap (Int.castRingHom k)) := by
    rw [spMap, IsFinite.SpecMap_iff]
    exact (RingHom.finite_algebraMap (A := ℤ) (B := k)).2 inferInstance
  have e : strHom κ Z ≫ spMap (Int.castRingHom κ) = i ≫ p ≫ spMap (Int.castRingHom k) :=
    specZIsTerminal.hom_ext _ _
  have : IsProper (strHom κ Z ≫ spMap (Int.castRingHom κ)) := by rw [e]; infer_instance
  have : IsProper (strHom κ (X := Z)) := IsProper.of_comp _ (spMap (Int.castRingHom κ))
  have e2 (L : LB X) : topSelfIntersection κ (L.pull i) 1 = interNum κ (structureModule Z) ![L.pull i] := by
    rw [topSelf_def]
    congr 1
    funext j
    fin_cases j
    rfl
  rw [e2, e2, e2]
  refine interNum_one_of_cls_eq_add (hH.pull_of_isClosedImmersion i) hd (LB.isLB_pull hN i) (LB.isLB_pull hA i)
    (LB.isLB_pull hB i) ?_
  rw [cls_pull hN, cls_pull hA, cls_pull hB, h, map_add (f := _)]

theorem topSelf_pow (hp : IsProjOver p) (L : HermLB p) (m : ℕ) (Z : Scheme.{0}) (i : Z ⟶ X) [IsClosedImmersion i]
    (κ : Type) [Field κ] [Finite κ] [Algebra κ Γ(Z, ⊤)] (hd : topologicalKrullDim Z = 1) :
    topSelfIntersection κ ((L.pow m).B.pull i) 1 = m * topSelfIntersection κ (L.B.pull i) 1 := by
  have c (n : ℕ) : cls (L.pow n).B (L.pow n).isLB = n • cls L.B L.isLB := cls_lbPow L.isLB n _
  induction m with
  | zero =>
    have := topSelf_of_cls_eq_add hp (L.pow 0).isLB (L.pow 0).isLB (L.pow 0).isLB (by rw [c]; simp) Z i κ hd
    simp only [Nat.cast_zero, zero_mul]
    linarith
  | succ n ih =>
    rw [topSelf_of_cls_eq_add hp (L.pow (n + 1)).isLB (L.pow n).isLB L.isLB (by rw [c, c, succ_nsmul]) Z i κ hd, ih]
    push_cast
    ring


end Curves

section Covers

variable {F : Type} [Field F] [NumberField F] {Y : Var F}

end Covers

open Formalism.MainNotions _root_.Formalism.L2.Pj Formalism.BasicNotions.TH _root_.Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4
open scoped ENNReal Classical

end GlobalTheory.NefHodgeTateAt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NuHTwisted
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SqTop NumberField IsDedekindDomain
open GlobalTheory.FunObj.SqNum (nuH halfRank IsTor)

noncomputable section

namespace GlobalTheory.ThmAUpper

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz)

theorem xiH_base : p.R.toRealDat.toLevCh.xiH p.P.A3.A.μ0 = 1 := by
  have h0 : p.tupT D.what₂.mu0 = p.P.A3.A.μ0 := by
    rw [← p.P.div.tup.mu0]; exact p.tupT_tup _
  rw [← h0, p.tupXi _ (Or.inl rfl), p.Tp.trueColumnChoices_heckeChar_reference_eq_one]

theorem xiH_twisted (w : HeightOneSpectrum (𝓞 D.what₂.LL)) (hw : p.R.mu w ≠ p.P.A3.A.μ0) :
    TwistedAt D (D.plEq.symm w) ∧ p.R.toRealDat.toLevCh.xiH (p.R.mu w) =
      p.R.C.delAt (D.what₂.places.resChar (D.plEq.symm w)) * p.Tp.psi (D.plEq.symm w) := by
  have h0 : p.tupT D.what₂.mu0 = p.P.A3.A.μ0 := by
    rw [← p.P.div.tup.mu0]; exact p.tupT_tup _
  have e1 : p.R.mu w = p.tupT (D.what₂.muAt (D.plEq.symm w)) := by rw [p.tupAt]; simp
  have htw : D.what₂.muAt (D.plEq.symm w) ≠ D.what₂.mu0 := fun e => hw (by rw [e1, e, h0])
  have hmt : D.what₂.muAt (D.plEq.symm w) = D.what₂.muTw (D.plEq.symm w) := (D.what₂.muAt_or _).resolve_left htw
  refine ⟨htw, ?_⟩
  rw [e1, p.tupXi _ (Or.inr ⟨_, rfl⟩), hmt, p.Tp.xi_tw]

end

theorem resChar_eq {D : D7} (w : D.what₂.places.Pl) {l : ℕ} (hl : l.Prime)
    (h : ((l : ℕ) : 𝓞 D.what₂.LL) ∈ (D.plEq w).asIdeal) : D.what₂.places.resChar w = l := by
  by_contra hq
  have hq' := D.what₂.places.resChar_prime w
  have hnot : ((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL) ∉ (D.plEq w).asIdeal := by
    intro hin
    obtain ⟨a, b, hab⟩ : IsCoprime ((D.what₂.places.resChar w : ℕ) : ℤ) (l : ℤ) :=
      Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hq' hl).2 hq)
    apply (D.plEq w).isPrime.ne_top
    rw [Ideal.eq_top_iff_one]
    have e : (1 : 𝓞 D.what₂.LL) = (a : 𝓞 D.what₂.LL) * ((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL) +
        (b : 𝓞 D.what₂.LL) * ((l : ℕ) : 𝓞 D.what₂.LL) := by
      exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 D.what₂.LL) hab.symm
    rw [e]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hin) (Ideal.mul_mem_left _ _ h)
  have h1 : (D.plEq w).valuation D.what₂.LL (algebraMap (𝓞 D.what₂.LL) D.what₂.LL ((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL)) = 1 := by
    rw [HeightOneSpectrum.valuation_of_algebraMap]
    exact HeightOneSpectrum.intValuation_eq_one_iff.2 hnot
  have h2 := D.what₂.places.val_resChar w
  rw [D.val_eq w _ (Nat.cast_ne_zero.2 hq'.ne_zero)] at h2
  have h3 : vAdd (D.plEq w) ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) = (D.what₂.places.ramIdx w : ℕ) := by
    exact_mod_cast h2
  have h4 : vAdd (D.plEq w) ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) = 0 := by
    unfold vAdd
    rw [show ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) =
      algebraMap (𝓞 D.what₂.LL) D.what₂.LL ((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL) by simp, h1]
    simp
  have := D.what₂.places.ramIdx_pos w
  omega

theorem nuH_twisted {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) {CF : ℝ} (G : Grid p CF) (w : HeightOneSpectrum (𝓞 D.what₂.LL)) (hw : p.R.mu w ≠ p.P.A3.A.μ0)
    (i j : Fin D.R.m) : nuH G (p.R.mu w) i j = nuH G p.P.A3.A.μ0 i j *
      p.R.C.delAt (D.what₂.places.resChar (D.plEq.symm w)) * p.Tp.psi (D.plEq.symm w) := by
  unfold nuH
  rw [(xiH_twisted p w hw).2, xiH_base p, mul_one, div_eq_mul_inv, div_eq_mul_inv]
  ac_rfl

end GlobalTheory.ThmAUpper
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareCharactersIsGoodGridPlaces
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareCharactersIsGoodGridPlaces
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.FunObj

theorem squareChars_isGood : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (_hL : L.Is μ₀) (t : T)
    (i j : Fin D.R.m), SquareStanding G t → ∃ S₀ Q : Finset (HeightOneSpectrum (𝓞 D.host.F)),
      (∀ v ∈ S₀ ∪ Q, (∃ w ∈ locPl G t, w.under (𝓞 D.host.F) = v) ∧
        Nonempty (D.host.E →ₐ[D.host.F] Fv D.host.F v)) ∧
      ∀ B : Base D.host.F D.host.E, S₀ ∪ Q ⊆ B.P → B.v₁ ∉ S₀ ∪ Q → SplitsFully D.host.E B.v₁ →
        HasExp B.emb (alpha G t i j) B.mα → HasExp B.emb (beta G i j) B.mβ →
        Chars.IsGood B ⟨alpha G t i j, beta G i j, S₀, Q⟩ (spW G i j).rank (spW₁ G i j).rank := by
  intro D T L sc G μ₀ hL t i j _hst
  refine ⟨G.pl.S0, (L.Q t).image (fun P => P.under (𝓞 D.host.F)) \ G.pl.S0, ?_, ?_⟩
  · intro v hv
    rcases Finset.mem_union.1 hv with hv | hv
    · have hw : G.pl.w v ∈ locPl G t := Finset.mem_union_left _ (Finset.mem_image_of_mem _ hv)
      have e := G.pl.under_w hv
      exact ⟨⟨_, hw, e⟩, e ▸ GlobalTheory.T.gridLocalTensorPlaces_over_split_places hL t _ hw⟩
    · obtain ⟨P, hP, e⟩ := Finset.mem_image.1 (Finset.mem_sdiff.1 hv).1
      have hw : P ∈ locPl G t := Finset.mem_union_right _ hP
      exact ⟨⟨P, hw, e⟩, e ▸ GlobalTheory.T.gridLocalTensorPlaces_over_split_places hL t _ hw⟩
  · intro B hsub hv₁ hsp hα hβ
    have h2 : Module.finrank D.host.F D.host.E = 2 := D.sp.cm.deg2
    obtain ⟨rα, rβ⟩ := GlobalTheory.T.thetaGrid_alpha_beta_restrict_quadratic_pow_rank hL t i j
    refine ⟨?_, ?_, GlobalTheory.T.restrictsToQuadraticSignPow_of_restrictsToQuadraticCharPow _ _ h2 _ _ rα, GlobalTheory.T.restrictsToQuadraticSignPow_of_restrictsToQuadraticCharPow _ _ h2 _ _ rβ, hα, hβ, ?_, hsub, ?_, ?_, ?_, ⟨hv₁, hsp⟩⟩
    · have hm := (hL.mu0 j).1
      have hx := (hL.xi t).1
      have he := hL.eta.1
      refine ⟨(hm.1.mul hx.1).mul (he.1.pow _), fun x => ?_⟩
      have e1 := hm.2 x
      have e2 := hx.2 x
      have e3 := he.2 x
      show L.mu0 ((j : ℕ) + 1) _ * L.xi t _ * (L.eta ^ _) _ = 1
      rw [MonoidHom.pow_apply]
      rw [e1, e2, e3]
      simp
    · have hc := (G.ch.chi_eq (D.R.m - (i : ℕ)) (by omega) (by omega)).1
      have he := hL.eta.1
      refine ⟨hc.1.mul (he.1.pow _), fun x => ?_⟩
      have e1 := hc.2 x
      have e3 := he.2 x
      show G.ch.chi (D.R.m - (i : ℕ)) _ * (L.eta ^ _) _ = 1
      rw [MonoidHom.pow_apply, e1, e3]
      simp
    · exact Finset.disjoint_sdiff
    · intro w hw
      rcases Finset.mem_union.1 hw with hw | hw
      · rcases (G.pl.mem_S0_of_sum_eq).1 hw with h | h
        · exact GlobalTheory.T.not_unrAt_of_under_eq_v0 hL t i j w h
        · exact GlobalTheory.T.alpha_div_beta_ramified_first hL t i j w h
      · obtain ⟨h1, h2⟩ := Finset.mem_sdiff.1 hw
        obtain ⟨P, hP, e⟩ := Finset.mem_image.1 h1
        exact GlobalTheory.T.alpha_div_beta_ramified_at_level hL t i j w P hP e h2
    · intro w hw
      have hw' : w.under (𝓞 D.host.F) ∉ G.pl.S0 ∪ ((L.Q t).image (fun P => P.under (𝓞 D.host.F)) \ G.pl.S0) := hw
      refine GlobalTheory.T.alpha_unramified_outside hL t i j w (fun h => hw' (Finset.mem_union_left _ h)) fun P hP e => hw' ?_
      by_cases h : w.under (𝓞 D.host.F) ∈ G.pl.S0
      · exact Finset.mem_union_left _ h
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.2 ⟨Finset.mem_image.2 ⟨P, hP, e⟩, h⟩)
    · intro w hw
      have hw' : w.under (𝓞 D.host.F) ∉ G.pl.S0 ∪ ((L.Q t).image (fun P => P.under (𝓞 D.host.F)) \ G.pl.S0) := hw
      exact GlobalTheory.T.beta_unramified_outside hL i j w (fun h => hw' (Finset.mem_union_left _ h))

end GlobalTheory.FunObj

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareCharactersIsGoodGridPlacesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.squareCharacters_isGood_gridPlaces : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (_hL : L.Is μ₀) (t : T)
    (i j : Fin D.R.m), SquareStanding G t → ∃ S₀ Q : Finset (HeightOneSpectrum (𝓞 D.host.F)),
      (∀ v ∈ S₀ ∪ Q, (∃ w ∈ locPl G t, w.under (𝓞 D.host.F) = v) ∧
        Nonempty (D.host.E →ₐ[D.host.F] Fv D.host.F v)) ∧
      ∀ B : Base D.host.F D.host.E, S₀ ∪ Q ⊆ B.P → B.v₁ ∉ S₀ ∪ Q → SplitsFully D.host.E B.v₁ →
        HasExp B.emb (alpha G t i j) B.mα → HasExp B.emb (beta G i j) B.mβ →
        Chars.IsGood B ⟨alpha G t i j, beta G i j, S₀, Q⟩ (spW G i j).rank (spW₁ G i j).rank := by
  first | exact @GlobalTheory.FunObj.squareChars_isGood | exact GlobalTheory.FunObj.squareChars_isGood | (intros; apply GlobalTheory.FunObj.squareChars_isGood <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionQuotientsTranscendenceBasisBasepointFree
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranscendenceBasisSectionTupleQuotients
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranscendenceBasisSectionTupleQuotients
open Filter Topology MvPolynomial GlobalTheory.HSAmp

set_option autoImplicit false

namespace GlobalTheory.HSAmp.TrBasis

variable {K : Type} [Field K]

theorem isAlgebraic_div_of_mem {s : Set K} {a b : K} (ha : a ∈ Algebra.adjoin ℤ s)
    (hb : b ∈ Algebra.adjoin ℤ s) (hb0 : b ≠ 0) : IsAlgebraic (Algebra.adjoin ℤ s) (a / b) := by
  refine ⟨Polynomial.C (⟨b, hb⟩ : Algebra.adjoin ℤ s) * Polynomial.X - Polynomial.C ⟨a, ha⟩, ?_, ?_⟩
  · intro h
    have h1 := congrArg (fun p : Polynomial (Algebra.adjoin ℤ s) => p.coeff 1) h
    simp at h1
    exact hb0 (congrArg Subtype.val h1)
  · simp [mul_div_cancel₀ _ hb0]

theorem isAlgebraic_trans [CharZero K] {s t : Set K}
    (ht : Algebra.IsAlgebraic (Algebra.adjoin ℤ t) K)
    (hts : ∀ w ∈ t, IsAlgebraic (Algebra.adjoin ℤ s) w) :
    Algebra.IsAlgebraic (Algebra.adjoin ℤ s) K := by
  rw [← AlgebraicIndependent.matroid_spanning_iff] at ht ⊢
  rw [Matroid.spanning_iff_closure_eq] at ht ⊢
  refine Set.eq_univ_of_univ_subset ?_
  rw [AlgebraicIndependent.matroid_e] at ht
  rw [← ht]
  refine Matroid.closure_subset_closure_of_subset_closure ?_
  intro w hw
  rw [AlgebraicIndependent.matroid_closure_eq]
  exact (Subalgebra.mem_algebraicClosure _ _).2 (hts w hw)

theorem trBasis_of_integral_ratR (K : Type) [Field K] [CharZero K] (D : ℕ) (x : Fin (D + 1) → K) (l : Fin (D + 1))
    (A : Subring K) (htr : Algebra.trdeg ℤ K = D) (hl : x l ≠ 0) (hA : Algebra.FiniteType ℤ A)
    (hint : ∀ w ∈ A, IsIntegral (ratR x l) w)
    (hfr : ∀ w : K, ∃ a ∈ A, ∃ b ∈ A, b ≠ 0 ∧ w = a / b) :
    (∀ j, x j ≠ 0) ∧ AlgebraicIndependent ℤ (fun j : Fin D => x j.succ / x 0) ∧
      FiniteDimensional (ratF x) K := by
  haveI : FaithfulSMul ℤ K := (faithfulSMul_iff_algebraMap_injective ℤ K).mpr Int.cast_injective
  set y : Fin (D + 1) → K := fun j => x j / x l with hy
  have hle : ratR x l ≤ (Algebra.adjoin ℤ (Set.range y)).toSubring :=
    Subring.closure_le.2 Algebra.subset_adjoin
  let φ : ratR x l →+* Algebra.adjoin ℤ (Set.range y) :=
    { toFun := fun v => ⟨v, hle v.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hAlgA : ∀ w ∈ (A : Set K), IsAlgebraic (Algebra.adjoin ℤ (Set.range y)) w := fun w hw =>
    (IsIntegral.map_of_comp_eq φ (RingHom.id K) (by ext; rfl) (hint w hw)).isAlgebraic
  have hAlgY : Algebra.IsAlgebraic (Algebra.adjoin ℤ (Set.range y)) K := by
    refine isAlgebraic_trans (t := (A : Set K)) ⟨fun w => ?_⟩ hAlgA
    obtain ⟨a, ha, b, hb, hb0, rfl⟩ := hfr w
    exact isAlgebraic_div_of_mem (Algebra.subset_adjoin ha) (Algebra.subset_adjoin hb) hb0
  set z : Fin D → K := fun j => x (l.succAbove j) / x l with hz
  have hAlgZ : Algebra.IsAlgebraic (Algebra.adjoin ℤ (Set.range z)) K := by
    refine isAlgebraic_trans hAlgY ?_
    rintro _ ⟨j, rfl⟩
    rcases Fin.eq_self_or_eq_succAbove l j with h | ⟨j', rfl⟩
    · subst h
      simp only [hy, div_self hl]
      exact isAlgebraic_one
    · exact isAlgebraic_algebraMap (⟨z j', Algebra.subset_adjoin ⟨j', rfl⟩⟩ :
        Algebra.adjoin ℤ (Set.range z))
  have hZ : IsTranscendenceBasis ℤ z :=
    Algebra.IsAlgebraic.isTranscendenceBasis_of_le_trdeg_of_finite ℤ z (by rw [htr]; simp)
  have hx : ∀ j, x j ≠ 0 := by
    intro j
    rcases Fin.eq_self_or_eq_succAbove l j with h | ⟨j', rfl⟩
    · exact h ▸ hl
    · intro h0
      exact hZ.1.ne_zero j' (by simp [hz, h0])
  set u : Fin D → K := fun j => x j.succ / x 0 with hu
  have hv : ∀ k, x k / x 0 ∈ Algebra.adjoin ℤ (Set.range u) := by
    intro k
    refine Fin.cases ?_ (fun j => ?_) k
    · rw [div_self (hx 0)]; exact Subalgebra.one_mem _
    · exact Algebra.subset_adjoin ⟨j, rfl⟩
  have hAlgU : Algebra.IsAlgebraic (Algebra.adjoin ℤ (Set.range u)) K := by
    refine isAlgebraic_trans hAlgZ ?_
    rintro _ ⟨j, rfl⟩
    have e : z j = (x (l.succAbove j) / x 0) / (x l / x 0) := by
      simp only [hz]; field_simp [hx 0, hl]
    rw [e]
    exact isAlgebraic_div_of_mem (hv _) (hv _) (div_ne_zero hl (hx 0))
  have hU : IsTranscendenceBasis ℤ u :=
    Algebra.IsAlgebraic.isTranscendenceBasis_of_le_trdeg_of_finite ℤ u (by rw [htr]; simp)
  refine ⟨hx, hU.1, ?_⟩

  have hleF : ∀ {v : K}, v ∈ Algebra.adjoin ℤ (Set.range u) → v ∈ ratF x := fun hv =>
    Algebra.adjoin_le (S := subalgebraOfSubring (ratF x).toSubring) Subfield.subset_closure hv
  let ψ : Algebra.adjoin ℤ (Set.range u) →+* ratF x :=
    { toFun := fun v => ⟨v, hleF v.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hψ : Function.Injective ψ := fun a b h => by
    have h' := congrArg Subtype.val h
    exact Subtype.ext h'
  have hAlgF : Algebra.IsAlgebraic (ratF x) K :=
    ⟨fun w => (hAlgU.isAlgebraic w).ringHom_of_comp_eq ψ (RingHom.id K) hψ (by ext; rfl)⟩
  obtain ⟨t, ht⟩ := hA.out
  let T : Set K := (Subtype.val : A → K) '' (t : Set A)
  haveI : Finite T := (t.finite_toSet.image _).to_subtype
  have hfd : FiniteDimensional (ratF x) (IntermediateField.adjoin (ratF x) T) :=
    IntermediateField.finiteDimensional_adjoin fun w _ => (hAlgF.isAlgebraic w).isIntegral
  have hmemA : ∀ a : A, (a : K) ∈ IntermediateField.adjoin (ratF x) T := by
    intro a
    have ha : a ∈ Algebra.adjoin ℤ (t : Set A) := ht ▸ Algebra.mem_top
    induction ha using Algebra.adjoin_induction with
    | mem c hc => exact IntermediateField.subset_adjoin _ _ ⟨c, hc, rfl⟩
    | algebraMap n => simpa using IntermediateField.intCast_mem _ n
    | add a b _ _ ha hb => simpa using add_mem ha hb
    | mul a b _ _ ha hb => simpa using mul_mem ha hb
  have htop : IntermediateField.adjoin (ratF x) T = ⊤ := by
    refine eq_top_iff.2 fun w _ => ?_
    obtain ⟨a, ha, b, hb, _, rfl⟩ := hfr w
    exact div_mem (hmemA ⟨a, ha⟩) (hmemA ⟨b, hb⟩)
  rw [htop] at hfd
  exact IntermediateField.topEquiv.toLinearEquiv.finiteDimensional

end GlobalTheory.HSAmp.TrBasis
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranscendenceBasisSectionTupleQuotientsStatement
open Filter Topology MvPolynomial GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transcendenceBasis_sectionTupleQuotients : ∀ (K : Type) [Field K] [CharZero K] (D : ℕ) (x : Fin (D + 1) → K) (l : Fin (D + 1)) (A : Subring K), Algebra.trdeg ℤ K = D → x l ≠ 0 → Algebra.FiniteType ℤ A → (∀ w ∈ A, IsIntegral (ratR x l) w) → (∀ w : K, ∃ a ∈ A, ∃ b ∈ A, b ≠ 0 ∧ w = a / b) → (∀ j, x j ≠ 0) ∧ AlgebraicIndependent ℤ (fun j : Fin D => x j.succ / x 0) ∧ FiniteDimensional (ratF x) K := by
  first | exact @GlobalTheory.HSAmp.TrBasis.trBasis_of_integral_ratR | exact GlobalTheory.HSAmp.TrBasis.trBasis_of_integral_ratR | (intros; apply GlobalTheory.HSAmp.TrBasis.trBasis_of_integral_ratR <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionQuotientsTranscendenceBasisBasepointFree
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

namespace GlobalTheory.HSAmp

theorem gens_quot_trBasis : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.L.B → ∀ (e : ℕ) (x : Fin (D + 1) → X.functionField), Gens P D e x → (∀ j, x j ≠ 0) ∧ AlgebraicIndependent ℤ (fun j : Fin D => x j.succ / x 0) ∧ FiniteDimensional (ratF x) X.functionField := by
  intro k _ X _ p D hX P hA e x hG
  obtain ⟨l, hl⟩ := hG.cover (genericPoint X)
  have hxl : x l ≠ 0 := ((GlobalTheory.T.regularNonvanishingLocusSection_properties k X p P (e : ℤ) 0 (x l) (hG.mem l)).2.1).1 hl
  obtain ⟨U, hU, hUeq, -, hreg, hft, hfrac, -⟩ :=
    GlobalTheory.T.nonvanishingLocus_ample_section_isAffine_model k X p D hX P hA e (x l) hG.pos (hG.mem l) hxl
  obtain ⟨hch, htr⟩ := GlobalTheory.T.projArith_functionField_charZero_trdeg k X p D hX
  refine GlobalTheory.T.transcendenceBasis_sectionTupleQuotients X.functionField D x l (fnOf U hU).range htr hxl hft ?_ hfrac
  intro w hw
  refine GlobalTheory.T.isIntegral_quotientRing_sectionTuple_locus k X p D hX P e x hG l w hxl ?_
  intro z hz
  rw [← hUeq] at hz
  exact (hreg w).2 hw z hz

end GlobalTheory.HSAmp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionQuotientsTranscendenceBasisBasepointFreeStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sectionQuotients_transcendenceBasis_basepointFree : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.L.B → ∀ (e : ℕ) (x : Fin (D + 1) → X.functionField), Gens P D e x → (∀ j, x j ≠ 0) ∧ AlgebraicIndependent ℤ (fun j : Fin D => x j.succ / x 0) ∧ FiniteDimensional (ratF x) X.functionField := by
  first | exact @GlobalTheory.HSAmp.gens_quot_trBasis | exact GlobalTheory.HSAmp.gens_quot_trBasis | (intros; apply GlobalTheory.HSAmp.gens_quot_trBasis <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSphericalOfHasSatGL
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.GenericUnitary

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.TempSatUnr

open GlobalTheory.TempSat

theorem isSpherical_of_hasSatGL {E : Type} [Field E] [NumberField E] {a : ℕ} {w : HeightOneSpectrum (𝓞 E)}
    {V : Type} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ (GL (Fin a) (w.adicCompletion E)) V}
    {S : Multiset ℂˣ} (hS : GlobalTheory.LFun.HasSatGL w ρ S) : GlobalTheory.SmGL.IsSpherical ρ := by
  have hK : GlobalTheory.SplitWeil.KO (w.adicCompletion E) (Fin a) = GlobalTheory.LFun.KGL w (n := a) :=
    GlobalTheory.SmGL.SphCompletion.KO_completion w a
  unfold GlobalTheory.SmGL.IsSpherical GlobalTheory.SmGL.IsSphericalFor
  rw [hK]
  exact hS.1

end GlobalTheory.TempSatUnr
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsometricShiftOfIsometric
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CovTest.GeoSwap

open HermLB

section Shift

variable {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k}



theorem gdeg_shift_const (L : HermLB p) (t : (k →+* ℂ) → ℝ) (ht : ∀ σ, t ((starRingEnd ℂ).comp σ) = t σ) (D : ℕ) :
    gdeg (L.shift t ht) D = gdeg L D := by
  simp only [gdeg, chInt, HermLB.shift, Weight.chernInt, Weight.chernPart_addFn_const]

end Shift

end GlobalTheory.CovTest.GeoSwap

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SetAtOfSizeAt
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim

namespace GlobalTheory.BigTop.Fun.SetFromSize

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

theorem finite_tup (p : PtAt ex Csz) : Finite p.P.T := by
  classical
  have h1 := p.charW.tup.mu_off
  have h2 := p.charW.tup.mu_used
  have : (Set.univ : Set p.P.T) ⊆ insert p.P.A3.A.μ0 (p.R.mu '' (p.R.twPl : Set _)) := fun t _ => by
    rcases h2 t with h | ⟨w, rfl⟩
    · exact Or.inl h
    · by_cases hw : w ∈ p.R.twPl
      · exact Or.inr ⟨w, hw, rfl⟩
      · exact Or.inl (h1 w hw)
  exact Set.finite_univ_iff.1 ((((p.R.twPl).finite_toSet.image _).insert _).subset this)


end GlobalTheory.BigTop.Fun.SetFromSize

namespace GlobalTheory.BigTop.Fun

end GlobalTheory.BigTop.Fun

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDoubleCosetRationalProductOfLocalLevels
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDoubleCosetRationalProductOfLocalLevels
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.ClassFinLev

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def finPart : UA E n →* finU (E := E) (n := n) where
  toFun u := ⟨⟨finGL E n (GeneralLinearGroup.map (pFin E) u.1), GlobalTheory.DefU.ClassFin.finGL_mem_UA _ (GlobalTheory.DefU.ClassFin.cT_pFin u)⟩,
    pInf_finGL _⟩
  map_one' := Subtype.ext (Subtype.ext (by simp))
  map_mul' a b := Subtype.ext (Subtype.ext (by simp))

theorem finPart_fin (k : finU (E := E) (n := n)) : finPart (k : UA E n) = k :=
  Subtype.ext (Subtype.ext (GlobalTheory.DefU.ClassFin.finGL_pFin k))

theorem finPart_inf {x : UA E n} (hx : x ∈ infU E n) : finPart x = 1 := by
  have h : GeneralLinearGroup.map (pFin E) x.1 = 1 := hx
  refine Subtype.ext (Subtype.ext ?_)
  change finGL E n (GeneralLinearGroup.map (pFin E) x.1) = 1
  rw [h, map_one]

theorem finPart_rat {γ : UA E n} (hγ : γ ∈ ratU E n) : finPart γ ∈ ratFinU E n := by
  obtain ⟨γ₀, hγ₀'⟩ := hγ
  have hγ₀ : ratGL E n γ₀ = γ.1 := hγ₀'
  have hg : cT (conjAd E) γ.1.val * 1 * γ.1.val = 1 := γ.2
  rw [← hγ₀, mul_one] at hg
  have hv : (ratGL E n γ₀).val = γ₀.val.map (algebraMap E (Ad E)) := rfl
  rw [hv, GlobalTheory.DefU.ClassFin.cT_map (algebraMap E (Ad E)) (IsCMField.complexConj E).toRingEquiv.toRingHom (conjAd E)
    (fun y => (conjAd_algebraMap y).symm), ← Matrix.map_mul] at hg
  have hU : γ₀ ∈ UE E n := by
    change cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ₀.val * 1 * γ₀.val = 1
    rw [mul_one]
    ext i j
    have := congrFun₂ hg i j
    rw [Matrix.map_apply, Matrix.one_apply] at this
    rw [Matrix.one_apply]
    haveI hnt : Nontrivial (Ad E) := show Nontrivial (InfiniteAdeleRing E × FiniteAdeleRing (𝓞 E) E) from inferInstance
    apply (algebraMap E (Ad E)).injective
    rw [this]
    split_ifs <;> simp
  refine ⟨γ₀, hU, ?_⟩
  change finGL E n (ratF E n γ₀) = finGL E n (GeneralLinearGroup.map (pFin E) γ.1)
  rw [← hγ₀]
  rfl

theorem finite_doubleCoset_of_isOpen (K : Subgroup (finU (E := E) (n := n))) (hK : IsOpen (K : Set (finU (E := E) (n := n)))) :
    Finite (DoubleCoset.Quotient (ratFinU E n : Set (finU (E := E) (n := n))) (K : Set (finU (E := E) (n := n)))) := by
  obtain ⟨T, hT⟩ := GlobalTheory.DefU.ClassFin.classSet_finite E n K hK
  let φ : T → DoubleCoset.Quotient (ratFinU E n : Set (finU (E := E) (n := n))) (K : Set (finU (E := E) (n := n))) :=
    fun s => DoubleCoset.mk _ _ (finPart (s : UA E n))
  refine Finite.of_surjective φ fun q => ?_
  obtain ⟨g, rfl⟩ : ∃ g, DoubleCoset.mk _ _ g = q := ⟨q.out, DoubleCoset.out_eq' q⟩
  obtain ⟨γ, hγ, s, hs, x, hx, k, hk, e⟩ := hT (g : UA E n)
  refine ⟨⟨s, hs⟩, ?_⟩
  have hg : g = finPart γ * finPart s * k := by
    have := congrArg finPart e
    rw [finPart_fin, map_mul, map_mul, map_mul, finPart_inf hx, mul_one, finPart_fin] at this
    exact this
  show DoubleCoset.mk _ _ (finPart (s : UA E n)) = DoubleCoset.mk _ _ g
  rw [hg]
  exact (@DoubleCoset.eq _ _ _ _ _ _).2 ⟨finPart γ, finPart_rat hγ, k, hk, rfl⟩

end GlobalTheory.BCT.ClassFinLev


open GlobalTheory.BCT.ClassFinLev in
theorem GlobalTheory.BCT.finite_doubleCoset_globLev : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → Finite (DoubleCoset.Quotient (ratFinU E n : Set (finU (E := E) (n := n))) (globLev S K' : Set (finU (E := E) (n := n)))) := by
  intro E _ _ _ hE n _ S _ K' hK
  exact finite_doubleCoset_of_isOpen _ (GlobalTheory.T.isOpen_productOfLocalLevelsUnitary E hE n S K' hK)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDoubleCosetRationalProductOfLocalLevelsStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_doubleCoset_rational_productOfLocalLevels : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → Finite (DoubleCoset.Quotient (ratFinU E n : Set (finU (E := E) (n := n))) (globLev S K' : Set (finU (E := E) (n := n)))) := by
  first | exact @GlobalTheory.BCT.finite_doubleCoset_globLev | exact GlobalTheory.BCT.finite_doubleCoset_globLev | (intros; apply GlobalTheory.BCT.finite_doubleCoset_globLev <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetNeZeroOfNondeg
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.WeilBridge
open GlobalTheory.WeilSchrodinger

theorem det_ne_zero_of_nondeg (D : D7) {k : ℕ} (G : Matrix (Fin k) (Fin k) D.host.E)
    (h : (sesq D G).Nondegenerate) : G.det ≠ 0 := by
  intro h0
  obtain ⟨v, hv, hGv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  apply hv
  apply h.2 v
  intro x
  have e : ∀ i, ∑ j, G i j * v j = 0 := fun i => by
    have := congrFun hGv i
    simpa [Matrix.mulVec, dotProduct] using this
  simp only [sesq, Matrix.toLinearMapₛₗ₂'_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  simp only [smul_eq_mul, RingHom.id_apply, ← Finset.mul_sum]
  rw [Finset.sum_congr rfl fun j _ => mul_comm (v j) (G i j), e i, mul_zero]

theorem exists_isTransport (D : D7) (B : Base D.host.F D.host.E) (hB : B.IsGood D.sp.cm.sig)
    (S T : HSp D) (X : Spc D.host.F D.host.E T.rank) (Y : Spc D.host.F D.host.E S.rank) (r s r' s' : ℕ)
    (hX : X.IsHerm D.sp.cm.sig B r s) (hY : Y.IsSkew D.sp.cm.sig B r' s')
    (eA : X.J = T.gramᵀ)
    (eB : (-1 : AF D.host.F ⊗[D.host.F] D.host.E) • incM D.host.F Y.J = incM D.host.F (D.host.xi0 • S.gram⁻¹))
    (Mo : Model D.sp.cm.sig X Y) (hMo : Mo.IsGood B.ψ) (χX χW : Chr D.host.F D.host.E)
    (hcX : GlobalTheory.LFun.IsHecke D.host.F D.host.E χX) (hcW : GlobalTheory.LFun.IsHecke D.host.F D.host.E χW)
    (rX : GlobalTheory.WeilM.ResEtaPow (Units.map (algebraMap D.host.F (AF D.host.F)).toMonoidHom).range χX T.rank)
    (rW : GlobalTheory.WeilM.ResEtaPow (Units.map (algebraMap D.host.F (AF D.host.F)).toMonoidHom).range χW S.rank)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig X Y) (hom : Mo.IsWeil B.ψ χX χW om) :
    ∃ ω : GA D S × GA D T →* Module.End ℂ (Formalism.IndefR.Datum.WO S T → ℂ),
      Formalism.IndefR.Datum.IsWeilDatumO B.ψ S T χW χX ω ∧ IsTransport B.ψ Mo.co ω om := by
  have hψ : IsStdChar D B.ψ (-1) := GlobalTheory.T.isStdChar_neg_one_of_standardTraceAdelicAddChar D B.ψ hB.std
  have rS := GlobalTheory.T.restrictsToQuadraticSignPow_idelic_restriction D χW S.rank rW
  have rT := GlobalTheory.T.restrictsToQuadraticSignPow_idelic_restriction D χX T.rank rX
  obtain ⟨ω, hω⟩ := GlobalTheory.weilRepresentationUnitaryPair D B.ψ S T χW χX hψ hcW hcX rS rT
  obtain ⟨om₀, hom₀⟩ := GlobalTheory.T.exists_weilDatum_transport_adelicSchwartz_thetaTransform D B.ψ hψ S T χW χX hcW hcX rS rT X.J Y.J (-1) eA eB
    (Fin T.rank × Fin S.rank) Mo.co hMo.rat ω hω
  have h2 := GlobalTheory.T.transportedWeil_preserves_schwartz_heisenberg_equivariant D B.ψ hψ S T χW χX hcW hcX rS rT X.J Y.J (-1) eA eB _ Mo.co hMo.rat ω hω om₀ hom₀
  have h3 := GlobalTheory.T.transportedWeilDatum_keeps_admissible_forms D B.ψ hψ S T χW χX hcW hcX rS rT X.J Y.J (-1) eA eB _ Mo.co hMo.rat ω hω om₀ hom₀
  have h4 := GlobalTheory.T.transportedWeilDatum_isUnitary_adelicSchwartz D B.ψ hψ S T χW χX hcW hcX rS rT X.J Y.J (-1) eA eB _ Mo.co hMo.rat ω hω om₀ hom₀
  have h5 := GlobalTheory.T.continuous_transported_weilDatum_adelicSchwartz D B.ψ hψ S T χW χX hcW hcX rS rT X.J Y.J (-1) eA eB _ Mo.co hMo.rat ω hω om₀ hom₀
  have h6 := GlobalTheory.T.exists_doubledWeil_blockEmbedding_acts_on_first_boxFactor D B.ψ hψ S T χW χX hcW hcX rS rT X.J Y.J (-1) eA eB _ Mo.co hMo.rat ω hω om₀ hom₀
  have h7 := GlobalTheory.T.exists_doubled_schrodingerModel_transposed_siegelRule D B.ψ hψ S T χW χX hcW hcX rS rT X.J Y.J (-1) eA eB _ Mo.co hMo.rat ω hω om₀ hom₀
  have hsp : GlobalTheory.WeilM.IsUSplitting (GlobalTheory.WeilM.adeleClass D.host.F) B.ψ Mo.co
      (GlobalTheory.WeilM.actAB (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig)) om₀ := ⟨⟨h2.1, h2.2, h3⟩, h4, h5⟩
  have hw₀ : Mo.IsWeil B.ψ χX χW om₀ :=
    ⟨⟨isUSplitting_inr hsp, h6⟩, ⟨transD _ Mo.co, transD_e Mo.co, isUSplitting_inl hsp, h7⟩, h5⟩
  obtain ⟨h1X, h2X, -⟩ := GlobalTheory.T.hermitianSelfDualLatticeSpace_form_hermitian_nondeg_unimodular D B hB T.rank X r s hX
  obtain ⟨hdY, -⟩ := GlobalTheory.T.skewHermitian_neg_traceZero_inv_hermitian_unimodular D B hB S.rank Y r' s' hY
  have hdX : X.J.det ≠ 0 := by
    have := det_ne_zero_of_nondeg D X.Jᵀ h2X
    rwa [Matrix.det_transpose] at this
  have huniq := GlobalTheory.T.adelicWeilRep_schrodingerModel_unique D.host.F D.host.E D.sp.cm.sig hB.cm T.rank S.rank X Y Mo B.ψ χX χW hB.std hX.herm hdX
    hY.skew hdY.ne_zero om om₀ hom hw₀
  refine ⟨ω, hω, fun a b g h ha hb Φ hΦ => ?_⟩
  rw [huniq (a, b) Φ hΦ]
  exact hom₀ a b g h ha hb Φ hΦ

theorem thetaTr_zero (D : D7) {W : Type} [AddCommGroup W] [Module (AF D.host.F) W] {Bf : W → W → AF D.host.F}
    {κ : Type} [Fintype κ] (d : GlobalTheory.WeilM.Darboux Bf κ) (ψ : AddChar (AF D.host.F) ℂ) (Φ : (κ → AF D.host.F) → ℂ) :
    thetaTr D.host.F d ψ Φ 0 = GlobalTheory.WeilM.thetaSum D.host.F Φ := by
  have : GlobalTheory.WeilM.schr ψ (0 : (κ → AF D.host.F) × (κ → AF D.host.F)) Φ = Φ := by
    funext x
    simp [GlobalTheory.WeilM.schr]
  simp [thetaTr, GlobalTheory.WeilM.Darboux.rho, this]

theorem exists_theta_eq (D : D7) (B : Base D.host.F D.host.E) (hB : B.IsGood D.sp.cm.sig)
    (S T : HSp D) (X : Spc D.host.F D.host.E T.rank) (Y : Spc D.host.F D.host.E S.rank) (r s r' s' : ℕ)
    (hX : X.IsHerm D.sp.cm.sig B r s) (hY : Y.IsSkew D.sp.cm.sig B r' s')
    (eA : X.J = T.gramᵀ)
    (eB : (-1 : AF D.host.F ⊗[D.host.F] D.host.E) • incM D.host.F Y.J = incM D.host.F (D.host.xi0 • S.gram⁻¹))
    (Mo : Model D.sp.cm.sig X Y) (hMo : Mo.IsGood B.ψ) (χX χW : Chr D.host.F D.host.E)
    (hcX : GlobalTheory.LFun.IsHecke D.host.F D.host.E χX) (hcW : GlobalTheory.LFun.IsHecke D.host.F D.host.E χW)
    (rX : GlobalTheory.WeilM.ResEtaPow (Units.map (algebraMap D.host.F (AF D.host.F)).toMonoidHom).range χX T.rank)
    (rW : GlobalTheory.WeilM.ResEtaPow (Units.map (algebraMap D.host.F (AF D.host.F)).toMonoidHom).range χW S.rank)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig X Y) (hom : Mo.IsWeil B.ψ χX χW om) :
    ∃ ω : GA D S × GA D T →* Module.End ℂ (Formalism.IndefR.Datum.WO S T → ℂ),
      Formalism.IndefR.Datum.IsWeilDatumO B.ψ S T χW χX ω ∧ IsTransport B.ψ Mo.co ω om ∧
      ∀ (a : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig X.J) (b : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig Y.J) (g : GA D S) (h : GA D T),
        mt T h = a.1.1 → mt S g = (b⁻¹).1.1ᵀ → ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F (Fin T.rank × Fin S.rank),
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.theta om Φ a b = ω (g, h) (thetaTr D.host.F Mo.co B.ψ Φ) 0 := by
  obtain ⟨ω, hω, htr⟩ := exists_isTransport D B hB S T X Y r s r' s' hX hY eA eB Mo hMo χX χW hcX hcW rX rW om hom
  refine ⟨ω, hω, htr, fun a b g h ha hb Φ hΦ => ?_⟩
  rw [← (htr a b g h ha hb Φ hΦ).2, thetaTr_zero]
  rfl

end GlobalTheory.WeilBridge
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DenominatorFittedIdentity
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SqTop

namespace GlobalTheory.BigTop.Fun

theorem halfRank_eq_sqRank_div (D : D7) (ij : Sq D) :
    GlobalTheory.FunObj.SqNum.halfRank D ij.1 ij.2 = sqRank D ij / 2 := by
  unfold GlobalTheory.FunObj.SqNum.halfRank sqRank
  congr 1
  simp only [GlobalTheory.ChiGrid.rankV]
  ring

end GlobalTheory.BigTop.Fun

end
end
