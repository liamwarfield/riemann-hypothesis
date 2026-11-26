module

public import Development.WeilBound.CoreStatements.PublishedTheorems.NefNumerics.NefRiemannRoch.NefLineBundleNumericalTheoremsProof
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenyFlatFinrank
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonFibre
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsLab
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLatticeIsoOfTwoPadicAlgClUniformisations
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinitePoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTraitModuliOfStalkCompleteDVR
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumMultResCycIndicatorSymm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralFramePointStalk
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsModelRuleSection
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlatWeightRuleReadsNonvanishingDetSection
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantLengthOfReadingHorizontalSection

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAmpleTensorOfNefFibresAmple
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAmpleTensorNefAmpleFiniteFieldFibre
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAmpleTensorNefAmpleFiniteFieldFibre
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.AmpleFibre

theorem isAmpleLB_fibre : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ L A : HermLB p, NefFib L → IsAmpleLB A.B → ∀ (l : ℕ) [Fact l.Prime], IsAmpleLB ((L.tens A).B.pull (Limits.pullback.fst (p ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom (ZMod l))))) := by
  intro k _ X _ p D hX L A hL hA l _
  haveI := hX.finite
  have hc := GlobalTheory.NefFibPrime.isClosedImmersion_spMap_zmod l
  haveI : IsClosedImmersion (Limits.pullback.fst (p ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom (ZMod l)))) :=
    IsClosedImmersion.isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback _ _).flip hc
  set f := Limits.pullback.fst (p ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom (ZMod l))) with hf
  set g := Limits.pullback.snd (p ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom (ZMod l))) with hg
  letI := GlobalTheory.algebraΓOfHom g
  have hproj : IsProjOver g := by
    have h := GlobalTheory.FibreNef.isProjOver_fibre hX.isProjOver l f
    rwa [GlobalTheory.strHom_eq (f := g) fun _ => rfl] at h
  have hN : IsNef (ZMod l) (L.B.pull f) :=
    GlobalTheory.FibreNef.isNef_pull_of_nefOver l f L ((GlobalTheory.VertForm.nefFib_iff L).1 hL l Fact.out)
  have hAf : IsAmpleLB (A.B.pull f) := hA.pull_of_isClosedImmersion f
  have hK := IsAmpleLB.tens_of_isNef GlobalTheory.nefNumerics_outright (ZMod l) _ g hproj _ _ hAf hN
  refine hK.of_lbIso (LB.isLB_pull (L.tens A).isLB f) ?_
  refine (CechPic.cls_eq_iff (LB.isLB_pull (L.tens A).isLB f)
    (CechPic.isLB_tens (LB.isLB_pull A.isLB f) (LB.isLB_pull L.isLB f))).1 ?_
  show CechPic.pull f (CechPic.cls L.B L.isLB + CechPic.cls A.B A.isLB) =
    CechPic.pull f (CechPic.cls A.B A.isLB) + CechPic.pull f (CechPic.cls L.B L.isLB)
  rw [map_add (f := _), add_comm]

end GlobalTheory.AmpleFibre
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAmpleTensorNefAmpleFiniteFieldFibreStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAmple_tensor_nef_ample_finiteFieldFibre : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ L A : HermLB p, NefFib L → IsAmpleLB A.B → ∀ (l : ℕ) [Fact l.Prime], IsAmpleLB ((L.tens A).B.pull (Limits.pullback.fst (p ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom (ZMod l))))) := by
  first | exact @GlobalTheory.AmpleFibre.isAmpleLB_fibre | exact GlobalTheory.AmpleFibre.isAmpleLB_fibre | (intros; apply GlobalTheory.AmpleFibre.isAmpleLB_fibre <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAmpleTensorOfNefFibresAmple
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
open Limits

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.AmpleNefFibZ

theorem exists_prime_le (P : Ideal ℤ) [P.IsPrime] :
    ∃ l : ℕ, l.Prime ∧ ∀ r : ℤ, r ∉ Ideal.span {(l : ℤ)} → r ∉ P := by
  obtain ⟨M, hM, hPM⟩ := Ideal.exists_le_maximal P (Ideal.IsPrime.ne_top ‹_›)
  set m := Submodule.IsPrincipal.generator M
  have hmM : Ideal.span {m} = M := Submodule.IsPrincipal.span_singleton_generator M
  have hm0 : m ≠ 0 := by
    rintro h
    have := Ideal.bot_lt_of_maximal M Int.not_isField
    rw [← hmM, h, Ideal.span_singleton_eq_bot.2 rfl] at this
    exact lt_irrefl _ this
  have hmp : Prime m := (Ideal.span_singleton_prime hm0).1 (hmM ▸ hM.isPrime)
  refine ⟨m.natAbs, Int.prime_iff_natAbs_prime.1 hmp, fun r hr hrP => hr ?_⟩
  rw [Ideal.mem_span_singleton, Int.natAbs_dvd]
  rw [← Ideal.mem_span_singleton, hmM]
  exact hPM hrP

theorem isAmpleLB_tens_of_nefFib : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ L A : HermLB p, NefFib L → IsAmpleLB A.B → IsAmpleLB (L.tens A).B := by
  intro k _ X _ p D hX L A hL hA
  haveI : Module.Finite ℤ k := hX.finite
  set s : X ⟶ Sp ℤ := p ≫ spMap (Int.castRingHom k) with hs_def
  have hsZ : s = ShFam.Pad.toSpZ X := specZIsTerminal.hom_ext _ _
  have hP : IsProjOver s := hsZ ▸ ShFam.Pad.isProjOver_toSpZ hX.isProjOver
  have hPB : AbLaw.IsProjBy s := (ProjSpace.isProjBy_iff_isProjOver s).2 hP
  haveI : IsProper s := hsZ ▸ FibreProj.isProper_of_isArithVar (ShFam.Pad.isArithVar_toSpZ hX)
  have hM : (L.tens A).B.IsLB := (L.tens A).isLB
  haveI : IsProper (Over.mk s).hom := ‹IsProper s›
  refine (relAmple_iff_isAmpleLB_of_isAffine (Over.mk s) hM).1 ?_
  refine AmpleLocal.relAmple_of_locally _ (Over.mk s) _ hM inferInstance inferInstance fun P => ?_
  obtain ⟨l, hl, hlP⟩ := @exists_prime_le P.asIdeal P.isPrime
  haveI : Fact l.Prime := ⟨hl⟩
  have F := GlobalTheory.T.isAmple_tensor_nef_ample_finiteFieldFibre k X p D hX L A hL hA l
  have hFib : Out.RelAmple ((Over.pullback (Spec.map (CommRingCat.ofHom (Int.castRingHom (ZMod l))))).obj (Over.mk s))
      ((L.tens A).B.pull (pullback.fst s (Spec.map (CommRingCat.ofHom (Int.castRingHom (ZMod l)))))) := by
    haveI : IsProper ((Over.pullback (Spec.map (CommRingCat.ofHom (Int.castRingHom (ZMod l))))).obj (Over.mk s)).hom :=
      inferInstanceAs (IsProper (pullback.snd s _))
    exact (relAmple_iff_isAmpleLB_of_isAffine _ (LB.isLB_pull hM _)).2 F
  have hfrac : ∀ y : ZMod l, ∃ a b : ℤ, Int.castRingHom (ZMod l) b ≠ 0 ∧
      y * Int.castRingHom (ZMod l) b = Int.castRingHom (ZMod l) a :=
    fun y => ⟨(y.val : ℤ), 1, by simp, by simp⟩
  obtain ⟨r, hr, hA'⟩ := AmpleNear.relAmple_near_fibre ℤ (Over.mk s) (L.tens A).B hX.flat hPB hM (ZMod l)
    (Int.castRingHom (ZMod l)) hfrac hFib
  have hrl : r ∉ Ideal.span {(l : ℤ)} := by
    rw [Ideal.mem_span_singleton]
    intro h
    exact hr ((ZMod.intCast_zmod_eq_zero_iff_dvd r l).2 h)
  let U : (Spec (CommRingCat.of ℤ)).Opens := PrimeSpectrum.basicOpen r
  haveI : IsAffine U.toScheme := IsAffineOpen.Spec_basicOpen (R := CommRingCat.of ℤ) r
  exact ⟨U, hlP r hrl, AmpleFibres.relAmple_restrict U (Over.mk s) hM hA'⟩

end GlobalTheory.AmpleNefFibZ
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAmpleTensorOfNefFibresAmpleStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAmple_tensor_of_nef_fibres_ample : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ L A : HermLB p, NefFib L → IsAmpleLB A.B → IsAmpleLB (L.tens A).B := by
  first | exact @GlobalTheory.AmpleNefFibZ.isAmpleLB_tens_of_nefFib | exact GlobalTheory.AmpleNefFibZ.isAmpleLB_tens_of_nefFib | (intros; apply GlobalTheory.AmpleNefFibZ.isAmpleLB_tens_of_nefFib <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSetupLabellingTransportGaloisConjugate
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSetupLabellingTransportGaloisConjugate
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Poinc.GalTrans

section Cong
variable {X : Type} [AddCommGroup X]

theorem cm_symm {N : ℕ} {x y : X} (h : CongMod N x y) : CongMod N y x := by
  obtain ⟨w, hw⟩ := h
  exact ⟨-w, by rw [hw, smul_neg]; abel⟩

theorem cm_trans {N : ℕ} {x y z : X} (h : CongMod N x y) (h' : CongMod N y z) : CongMod N x z := by
  obtain ⟨w, hw⟩ := h
  obtain ⟨w', hw'⟩ := h'
  exact ⟨w' + w, by rw [hw, hw', smul_add]; abel⟩

theorem cm_map {Y : Type} [AddCommGroup Y] (f : X →+ Y) {N : ℕ} {x y : X} (h : CongMod N x y) :
    CongMod N (f x) (f y) := by
  obtain ⟨w, hw⟩ := h
  exact ⟨f w, by rw [hw, map_add (f := _), map_nsmul]⟩

theorem cm_of_mk {N : ℕ} {x y : X}
    (h : (QuotientAddGroup.mk x : X ⧸ (nsmulAddMonoidHom N : X →+ X).range) = QuotientAddGroup.mk y) :
    CongMod N x y := by
  obtain ⟨w, hw⟩ := QuotientAddGroup.eq.mp h
  change N • w = -x + y at hw
  refine ⟨-w, ?_⟩
  rw [smul_neg, hw]
  abel

theorem cm_mk {N : ℕ} {x y : X} (h : CongMod N x y) :
    (QuotientAddGroup.mk x : X ⧸ (nsmulAddMonoidHom N : X →+ X).range) = QuotientAddGroup.mk y := by
  obtain ⟨w, hw⟩ := h
  refine QuotientAddGroup.eq.mpr ⟨-w, ?_⟩
  change N • (-w) = -x + y
  rw [hw, smul_neg]
  abel
private theorem charZero_uTest_V {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {ρ : S.Real}
    {p : ℕ} [Fact p.Prime] {y₀ : S.R →+* PadicAlgCl p} (u : ρ.UTest p y₀) : CharZero u.V :=
  ((algebraMap (FractionRing u.V) (PadicAlgCl p)).comp (algebraMap u.V (FractionRing u.V))).charZero

def matAct (E : Matrix (Fin 8) (Fin 8) ℤ) : (Fin 8 → X) →+ (Fin 8 → X) where
  toFun v a := ∑ b, E a b • v b
  map_zero' := by ext a; simp
  map_add' v w := by ext a; simp [smul_add, Finset.sum_add_distrib]

end Cong


open MonObj in
theorem compare {o Ω o' Ω' : Type} [CommRing o] [Field Ω] [Algebra o Ω] [CommRing o'] [Field Ω'] [Algebra o' Ω']
    {S : ThetaSys o Ω} {S' : ThetaSys o' Ω'} {ρ : S.Real} {ρ' : S'.Real} {p : ℕ} [Fact p.Prime]
    {y₀ : S.R →+* PadicAlgCl p} {y₁ : S'.R →+* PadicAlgCl p} (u : ρ.UTest p y₀) (u' : ρ'.UTest p y₁) (l : u.Lab)
    (l' : u'.Lab) (P₀ : PolAV (Sp (PadicAlgCl p))) (a : P₀.A.left ⟶ u.A.A.left) (a' : P₀.A.left ⟶ u'.A.A.left)
    (ha : IsGrpPullback P₀.A u.A.A (spMap (algebraMap (FractionRing u.V) (PadicAlgCl p))) a)
    (ha' : IsGrpPullback P₀.A u'.A.A (spMap (algebraMap (FractionRing u'.V) (PadicAlgCl p))) a')
    (hL : LBIso P₀.L (u.A.L.pull a)) (hL' : LBIso P₀.L (u'.A.L.pull a')) :
    ∃ e : u.D.toPre.X ≃+ u'.D.toPre.X, (∀ χ, l'.q (e χ) = l.q χ) ∧
      (∀ (m : ℕ) (x : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A) (x' : TFK (R := u'.V) (PadicAlgCl p) ⟶ u'.A.A)
        (w : Sp (PadicAlgCl p) ⟶ P₀.A.left), 1 ≤ m → x ^ m = 1 → x' ^ m = 1 → w ≫ P₀.A.hom = 𝟙 _ → w ≫ a = x.left →
        w ≫ a' = x'.left → ∃ pk pk', QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk x ∧
          QkToAkU u'.U.toUnifPre (PadicAlgCl p) m pk' x' ∧ CongMod m pk'.y (e pk.y)) ∧
      ∀ (m : ℕ) (pk' : QkPt u'.D.toPre (PadicAlgCl p) m) (x' : TFK (R := u'.V) (PadicAlgCl p) ⟶ u'.A.A), 1 ≤ m →
        QkToAkU u'.U.toUnifPre (PadicAlgCl p) m pk' x' → ∃ (pk : QkPt u.D.toPre (PadicAlgCl p) m)
          (x : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A) (w : Sp (PadicAlgCl p) ⟶ P₀.A.left),
          QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk x ∧ x ^ m = 1 ∧ w ≫ P₀.A.hom = 𝟙 _ ∧ w ≫ a = x.left ∧
          w ≫ a' = x'.left ∧ CongMod m pk'.y (e pk.y) := by
  obtain ⟨e, hps, hcg⟩ := GlobalTheory.T.exists_latticeIso_of_two_padicAlgCl_uniformisations S S' ρ ρ' p y₀ y₁ u u' P₀ a a' ha ha' hL hL'
  haveI := charZero_uTest_V u
  haveI := charZero_uTest_V u'
  refine ⟨e, fun χ => ?_, fun m x x' w hm hx hx' hw hwa hwa' => ?_, fun m pk' x' hm hpk' => ?_⟩
  · have h1 := (hps χ _).1 (l.q_eq χ)
    have h2 := l'.q_eq (e χ)
    have h3 := Real.exp_injective (GlobalTheory.ZH.RealCase.psiNorm_unique u' (e χ) h2 h1)
    linarith
  · obtain ⟨f, hf1, hf2, -⟩ := GlobalTheory.ZH.uTors_closed u.V u.complete u.A u.G u.D u.U (PadicAlgCl p) m hm
    obtain ⟨f', hf1', hf2', -⟩ := GlobalTheory.ZH.uTors_closed u'.V u'.complete u'.A u'.G u'.D u'.U (PadicAlgCl p) m hm
    obtain ⟨pk, rfl⟩ := hf2 x hx
    obtain ⟨pk', rfl⟩ := hf2' x' hx'
    have q1 := (hf1 pk (f pk)).2 rfl
    have q2 := (hf1' pk' (f' pk')).2 rfl
    exact ⟨pk, pk', q1, q2, hcg m pk pk' _ _ w hm q1 q2 hw hwa hwa'⟩
  · have hx' : x' ^ m = 1 := by
      have h0 := hpk'
      unfold QkToAkU at h0
      obtain ⟨w0, hw0⟩ := u'.U.ext
      have h1 := h0 w0 hw0
      unfold QkToAk at h1
      exact h1.1
    obtain ⟨w, x, hw, hwa', hwa, hx⟩ :=
      GlobalTheory.PtTrans.ptTrans (PadicAlgCl p) u'.A u.A P₀ a' a ha' ha m x' hx'
    obtain ⟨f, hf1, hf2, -⟩ := GlobalTheory.ZH.uTors_closed u.V u.complete u.A u.G u.D u.U (PadicAlgCl p) m hm
    obtain ⟨pk, rfl⟩ := hf2 x hx
    have q1 := (hf1 pk (f pk)).2 rfl
    exact ⟨pk, f pk, w, q1, hx, hw, hwa, hwa', hcg m pk pk' _ _ w hm q1 hpk' hw hwa hwa'⟩

set_option maxHeartbeats 1000000 in
theorem isLab_conj : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsDiagEnd F W X₁.ρ.P X₁.u ε₁ → ∀ (D : Deep X₁ ε₁) (σ : D.X.Ω₁ ≃ₐ[X₁.Ω₁] D.X.Ω₁), ∀ (s : D.X.M.Z ⟶ D.X.M.Z), D.X.M.pt ≫ s = spMap (σ : D.X.Ω₁ →+* D.X.Ω₁) ≫ D.X.M.pt → ∀ a : D.X.S.Gam ≃+ D.X.S.Gam, D.GalLab σ a → ∀ (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (c : CTrait X₁ p z₁) (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = c.y) (h' : (y ≫ s) ≫ D.q = c.y) (yy : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) (Fin 8 → c.T.D.toPre.X)), IsLab D.X D.ε (D.lift c y h) yy → IsLab D.X D.ε (D.lift c (y ≫ s) h') (yy.comp a.toAddMonoidHom) := by
  intro g n F W Z i X₁ hg hn hodd hi hE8 hth hpr ε₁ hdiag D σ s hs a hga p _ z₁ c y h h' yy hlab
  obtain ⟨c₀, hc, R', fg, frac, hth', hev, ρ', ε', hsame', hi₀', hR', y₀, hy₀, u, l, j, hq, hlabl, hmat⟩ := hlab
  obtain ⟨yy₂, hlab₂⟩ := exists_isLab g n F W Z i D.X hg hn hodd hi hE8 hth D.proj D.ε D.diag p
    ((y ≫ s) (cPt p)) (D.lift c (y ≫ s) h')
  obtain ⟨c₂, hc₂, R₂, fg₂, frac₂, hth₂, hev₂, ρ₂, ε₂, hsame₂, hi₀₂, hR₂, y₁, hy₁, u₂, l₂, j₂, hq₂, -, -⟩ := hlab₂
  obtain ⟨P₀, b, t, ε₀, hb, ht, lb, lt, hε, hp⟩ := hga
  obtain ⟨Q, b', b'', hb', hb'', lb', lb'', hpts, hend⟩ :=
    exists_generic D.X.ρ D.ε ρ' ε' ρ₂ ε₂ (fun x => x) (fun x => x) hsame' hsame₂ (σ : D.X.Ω₁ →+* D.X.Ω₁) a P₀ b t ε₀
      hb ht lb lt hε hp
  haveI : IsDedekindDomain D.X.o₁ := ArithBase.ded (Ω := D.X.Ω₁)
  have hR₂' : R₂ ≤ D.X.M.O (((gPt p ≫ y) ≫ s) (closedPoint (PadicAlgCl p))) := by
    rw [Category.assoc]; exact hR₂
  have hy₁' : ∀ r : R₂, y₁ r = D.X.M.val ((gPt p ≫ y) ≫ s) r := by
    intro r; rw [Category.assoc]; exact hy₁ r
  have hM : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme D.X.M.Z := by
    have hn := D.X.normal
    unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme
    obtain ⟨h1, h2⟩ := hn
    exact fun x => ⟨h1 x, h2 x⟩
  obtain ⟨P₁, a₁, a₂, ha₁, ha₂, la₁, la₂, hpt, hen⟩ :=
    spread D.X.M hM ρ' ρ₂ (σ : D.X.Ω₁ →+* D.X.Ω₁) s hs (gPt p ≫ y) hR' hR₂' y₀ y₁ hy₀ hy₁' u u₂ Q hb' hb''
      lb' lb''
  obtain ⟨e, heq, hfw, hbk⟩ := compare u u₂ l l₂ P₁ a₁ a₂ ha₁ ha₂ la₁ la₂
  have hN : 1 ≤ D.X.S.r * D.X.S.N := by
    obtain ⟨jj, -, hr⟩ := D.X.ρ.r_eq
    rw [hr, D.X.ρ.N_eq]
    have hnp := D.X.ρ.n_prime.pos
    exact Nat.mul_pos (pow_pos hnp _) (pow_pos (pow_pos hnp _) _)
  refine ⟨c₂, hc₂, R₂, fg₂, frac₂, hth₂, hev₂, ρ₂, ε₂, hsame₂, hi₀₂, hR₂, y₁, hy₁, u₂, l₂, e.symm.trans j, ?_, ?_, ?_⟩
  · intro χ
    have h1 := heq (e.symm χ)
    rw [AddEquiv.apply_symm_apply] at h1
    rw [h1]
    exact hq (e.symm χ)
  · intro bb χ hb2
    obtain ⟨wg, hwg, hwg1, hwg2⟩ := hpts bb
    obtain ⟨w1, x1, x2, hw1, hw1a, hw1b, hx1, hx2⟩ := hpt (a bb) bb wg hwg hwg1 hwg2
    have hx1p := GlobalTheory.LabelTorsion.pow_eq_one_of_over_label _ ρ' p y₀ u (a bb) x1 hx1
    have hx2p := GlobalTheory.LabelTorsion.pow_eq_one_of_over_label _ ρ₂ p y₁ u₂ bb x2 hx2
    obtain ⟨pk, pk2, hq1, hq2, hc12⟩ := hfw (D.X.S.r * D.X.S.N) x1 x2 w1 hN hx1p hx2p hw1 hw1a hw1b
    have e1 := l.yy_eq (a bb) pk x1 hq1 hx1
    have e2 := l₂.yy_eq bb pk2 x2 hq2 hx2
    have c1 : CongMod (D.X.S.r * D.X.S.N) χ pk2.y := cm_of_mk (hb2.symm.trans e2)
    have c2 := cm_trans c1 hc12
    have c3 : CongMod (D.X.S.r * D.X.S.N) (e.symm χ) pk.y := by
      have c4 := cm_map e.symm.toAddMonoidHom c2
      simpa using c4
    have e3 : l.yy (a bb) = QuotientAddGroup.mk (e.symm χ) := e1.trans (cm_mk (cm_symm c3))
    exact hlabl (a bb) (e.symm χ) e3
  · intro m pk pk' x x' E hm hq hq' hxx
    obtain ⟨pk0, x0, w0, hq0, hx0, hw0, hw0a, hw0b, hc0⟩ := hbk m pk x hm hq
    obtain ⟨pk0', x0', w0', hq0', hx0', hw0', hw0a', hw0b', hc0'⟩ := hbk m pk' x' hm hq'
    obtain ⟨η, hη1, hη2⟩ := hend E
    have hyp : w0' ≫ a₂ ≫ u₂.φ = w0 ≫ a₂ ≫ u₂.φ ≫ (ε₂ E).left := by
      rw [← hw0b', ← hw0b] at hxx
      simpa only [Category.assoc] using hxx
    have key : x0'.left ≫ u.φ = x0.left ≫ u.φ ≫ (ε' E).left := by
      have k1 := hen (ε' E) (ε₂ E) η hη1 hη2 w0 w0' hw0 hw0' hyp
      rw [← hw0a', ← hw0a]
      simpa only [Category.assoc] using k1
    have hm0 := hmat m pk0 pk0' x0 x0' E hm hq0 hq0' key
    have A : CongMod m (j (e.symm pk'.y)) (j pk0'.y) := by
      have A1 := cm_map (e.symm.trans j).toAddMonoidHom hc0'
      simpa using A1
    have B : CongMod m (j (e.symm pk.y)) (j pk0.y) := by
      have B1 := cm_map (e.symm.trans j).toAddMonoidHom hc0
      simpa using B1
    have B2 := cm_map (matAct E) B
    exact cm_trans A (cm_trans hm0 (cm_symm B2))

end GlobalTheory.Poinc.GalTrans
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSetupLabellingTransportGaloisConjugateStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaSetup_labelling_transport_galoisConjugate : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsDiagEnd F W X₁.ρ.P X₁.u ε₁ → ∀ (D : Deep X₁ ε₁) (σ : D.X.Ω₁ ≃ₐ[X₁.Ω₁] D.X.Ω₁), ∀ (s : D.X.M.Z ⟶ D.X.M.Z), D.X.M.pt ≫ s = spMap (σ : D.X.Ω₁ →+* D.X.Ω₁) ≫ D.X.M.pt → ∀ a : D.X.S.Gam ≃+ D.X.S.Gam, D.GalLab σ a → ∀ (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (c : CTrait X₁ p z₁) (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = c.y) (h' : (y ≫ s) ≫ D.q = c.y) (yy : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) (Fin 8 → c.T.D.toPre.X)), IsLab D.X D.ε (D.lift c y h) yy → IsLab D.X D.ε (D.lift c (y ≫ s) h') (yy.comp a.toAddMonoidHom) := by
  first | exact @GlobalTheory.Poinc.GalTrans.isLab_conj | exact GlobalTheory.Poinc.GalTrans.isLab_conj | (intros; apply GlobalTheory.Poinc.GalTrans.isLab_conj <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatTensorVanishesUnlessLastRowBounded
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatTensorVanishesUnlessLastRowBounded
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory ValuativeRel
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV

noncomputable section

namespace GlobalTheory.FunObj.FlatLast

open GlobalTheory.RootEx

section Step
variable {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}


open Classical in
theorem stepPt_add_apply (x₀ : Matrix n n' k) (e δ : StepVar n c n' → k) (a : n ⊕ Fin c) (b : n' ⊕ Fin (c + 1)) :
    stepPt x₀ (e + δ) a b =
      stepPt x₀ e a b + if h : Free (c / 2 + 1) (a, b) ∨ Kept (a, b) then δ ⟨(a, b), h⟩ else 0 := by
  simp only [stepPt, Matrix.add_apply, Matrix.of_apply, Pi.add_apply]
  split_ifs <;> ring

end Step

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {G : Grid k}


open Classical in
def shiftVar (j₀ : Fin (G.m - 1)) (r : ℕ) (t : k) : Vars G := fun j w =>
  if j = j₀ ∧ Sum.elim (fun a : Fin (topRank G (j + 1)) => (a : ℕ) = r) (fun _ => False) w.1.1 ∧
    w.1.2.isRight = true then t else 0

theorem valuation_shiftVar_le (j₀ : Fin (G.m - 1)) (r : ℕ) {t s₀ : k} (ht : valuation k t ≤ valuation k s₀)
    (j : Fin (G.m - 1)) (w) : valuation k (shiftVar j₀ r t j w) ≤ valuation k s₀ := by
  unfold shiftVar
  split_ifs
  · exact ht
  · simp

theorem ch_shift (x : ColArgs G) (e : Vars G) (j₀ : Fin (G.m - 1)) (r : ℕ) (t : k) (j : Fin (G.m - 1)) :
    ch (stepPt (x j) ((e + shiftVar j₀ r t) j)) = ch (stepPt (x j) (e j)) := by
  unfold ch
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.add_apply, stepPt_add_apply]
  split_ifs <;> simp [shiftVar]

theorem rowVar_shift (x : ColArgs G) (e : Vars G) (j₀ : Fin (G.m - 1)) (r : ℕ) (t : k) (j : ℕ) (s) :
    rowVar x (e + shiftVar j₀ r t) j s = rowVar x e j s := by
  unfold rowVar
  split_ifs with h
  · refine Finset.sum_congr rfl fun l _ => ?_
    split_ifs
    · rw [Pi.add_apply, stepPt_add_apply]
      split_ifs <;> simp [shiftVar]
    · rfl
  · rfl

theorem colVar_shift (x : ColArgs G) (e : Vars G) (j₀ : Fin (G.m - 1)) (hj₀ : (j₀ : ℕ) + 2 = G.m) (r : ℕ) (t : k)
    (j : Fin (G.m - 1)) (r' : Fin (topRank G (j + 1))) :
    colVar x (e + shiftVar j₀ r t) j r' = colVar x e j r' + if j = j₀ ∧ (r' : ℕ) = r then t else 0 := by
  unfold colVar
  rw [Pi.add_apply, stepPt_add_apply]
  congr 1
  by_cases hj : j = j₀
  · subst hj
    rw [dite_eq_left (Or.inr ⟨by rw [show G.m - 2 - (j : ℕ) = 0 by omega]; exact ⟨0, rfl⟩, rfl⟩)]
    simp [shiftVar]
  · simp [shiftVar, hj]

theorem phase_shift (x : ColArgs G) (e : Vars G) (j₀ : Fin (G.m - 1)) (hj₀ : (j₀ : ℕ) + 2 = G.m)
    (r : Fin (topRank G ((j₀ : ℕ) + 1))) (t : k) :
    phase x (e + shiftVar j₀ r t) = phase x e + rowVar x e ((j₀ : ℕ) + 1) r * t := by
  unfold phase
  have key : ∀ j : Fin (G.m - 1), (ch (stepPt (x j) ((e + shiftVar j₀ r t) j)) +
      if Even (G.m - 2 - j) then ∑ r', rowVar x (e + shiftVar j₀ r t) (j + 1) r' *
        colVar x (e + shiftVar j₀ r t) j r' else 0) =
      (ch (stepPt (x j) (e j)) + if Even (G.m - 2 - j) then ∑ r', rowVar x e (j + 1) r' * colVar x e j r' else 0) +
      if j = j₀ then rowVar x e ((j₀ : ℕ) + 1) r * t else 0 := by
    intro j
    rw [ch_shift]
    simp only [rowVar_shift, colVar_shift x e j₀ hj₀]
    by_cases hj : j = j₀
    · subst hj
      have hev : Even (G.m - 2 - (j : ℕ)) := by rw [show G.m - 2 - (j : ℕ) = 0 by omega]; exact ⟨0, rfl⟩
      rw [if_pos hev, if_pos hev, if_pos rfl]
      simp only [true_and, mul_add, Finset.sum_add_distrib, add_assoc]
      congr 2
      simp_rw [Fin.val_inj, mul_ite, mul_zero]
      rw [Finset.sum_ite_eq']
      simp
    · simp [hj]
  rw [Finset.sum_congr rfl fun j _ => key j, Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp

variable (hs : 1 ≤ G.s)

theorem valuation_downMap_sub_le (x : ColArgs G) (e δ : Vars G) {s₀ : k}
    (hδ : ∀ j w, valuation k (δ j w) ≤ valuation k s₀) (j : ℕ) (a b) :
    valuation k (downMap hs x (e + δ) j a b - downMap hs x e j a b) ≤ valuation k s₀ := by
  classical
  unfold downMap
  split_ifs with h1 h2
  · simp only [reindex_apply, submatrix_apply, Pi.add_apply]
    rw [stepPt_add_apply, add_sub_cancel_left]
    split_ifs
    · exact hδ _ _
    · simp
  · simp
  · simp

theorem valuation_fill_sub_le (x : ColArgs G) (y : RowArgs G) (e δ : Vars G) {s₀ : k}
    (hδ : ∀ j w, valuation k (δ j w) ≤ valuation k s₀) (b : Edge) (r s) :
    valuation k ((fill hs x y (e + δ) - fill hs x y e) b r s) ≤ valuation k s₀ := by
  rcases b with ⟨i, j⟩ | ⟨i, j⟩
  · simp only [fill, Pi.sub_apply]
    split_ifs with h
    · simp only [Matrix.sub_apply, transpose_apply, submatrix_apply]
      exact valuation_downMap_sub_le hs x e δ hδ j _ _
    · simp
  · simp only [fill, Pi.sub_apply]
    split_ifs with h
    · simp
    · simp

end GlobalTheory.FunObj.FlatLast

namespace GlobalTheory.FunObj.FlatLast
open GlobalTheory.RootEx

theorem flatTensor_lastRow_bounded : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (G : Grid k) (hs : 1 ≤ G.s) (ψ : AddChar k Circle) (ν : Measure k) [ν.IsAddHaarMeasure] (ϖ : kˣ) (e : ℕ) (T : G.Args → ℂ) (keep : Bool) (g : G.VertexGroup), 2 ≤ G.m → IsUnif ϖ → HasConductor ψ 1 → G.IsTensor ϖ e (oppositePath G.m) T → ∃ n : ℕ, ∀ (x : ColArgs G) (y : RowArgs G), flatTensor hs ψ ν (moved G keep g T) x y ≠ 0 → ∀ s, valuation k (x (G.m - 1) (topLast G (G.m - 1 + 1)) s) ≤ valuation k (((ϖ ^ n)⁻¹ : kˣ) : k) := by
  intro k _ _ _ _ _ _ G hs ψ ν _ ϖ e T keep g hm hϖ hψ hT
  obtain ⟨n, -, hper⟩ := GlobalTheory.MovedBound.moved_bounded_locConst G ϖ e T keep g hϖ hT
  refine ⟨n, fun x y hF => ?_⟩
  let j₀ : Fin (G.m - 1) := ⟨G.m - 2, by omega⟩
  have hj₀ : (j₀ : ℕ) + 2 = G.m := by simp only [j₀]; omega
  suffices key : ∀ r : Fin (topRank G ((j₀ : ℕ) + 1)),
      valuation k (x ((j₀ : ℕ) + 1) (topLast G ((j₀ : ℕ) + 1 + 1)) r) ≤ valuation k (((ϖ ^ n)⁻¹ : kˣ) : k) by
    have h : G.m - 1 = (j₀ : ℕ) + 1 := by omega
    rw [h]
    exact key
  intro r
  by_contra hlt
  have hu : x ((j₀ : ℕ) + 1) (topLast G ((j₀ : ℕ) + 1 + 1)) r ∉ cball (1 * (ϖ ^ n)⁻¹) := by
    simpa [cball] using hlt
  obtain ⟨t, ht, hne⟩ := hψ.exists_ne_one (ϖ ^ n) hu
  set u := x ((j₀ : ℕ) + 1) (topLast G ((j₀ : ℕ) + 1 + 1)) r with hu_def
  have hrow : ∀ e' : Vars G, rowVar x e' ((j₀ : ℕ) + 1) r = u := fun e' => by
    rw [rowVar, dite_eq_right (by omega)]
  let δ : Vars G := shiftVar j₀ r (-t)
  have hδ : ∀ j w, valuation k (δ j w) ≤ valuation k ((ϖ ^ n : kˣ) : k) :=
    valuation_shiftVar_le _ _ (by simpa [cball, Valuation.map_neg] using ht)
  have hS : ∀ e' : Vars G, moved G keep g T (fill hs x y (e' + δ)) = moved G keep g T (fill hs x y e') := fun e' => by
    have := hper (fill hs x y e') (fill hs x y (e' + δ) - fill hs x y e')
      (fun b _ r s => valuation_fill_sub_le hs x y e' δ hδ b r s)
    rwa [add_sub_cancel] at this
  have hI : ∀ e' : Vars G, flatIntegrand hs ψ (moved G keep g T) x y (e' + δ) =
      (ψ (t * u) : ℂ) * flatIntegrand hs ψ (moved G keep g T) x y e' := fun e' => by
    unfold flatIntegrand
    rw [hS, phase_shift x e' j₀ hj₀ r (-t), hrow,
      show -(phase x e' + u * -t) = -phase x e' + t * u by ring, AddChar.map_add_eq_mul, Circle.coe_mul]
    ring
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have hFeq : flatTensor hs ψ ν (moved G keep g T) x y =
      (ψ (t * u) : ℂ) * flatTensor hs ψ ν (moved G keep g T) x y := by
    have : SigmaFinite ν := inferInstance
    have : ν.IsAddRightInvariant := inferInstance
    have : (varsVol G ν).IsAddRightInvariant := by unfold varsVol; infer_instance
    unfold flatTensor
    calc ∫ e', flatIntegrand hs ψ (moved G keep g T) x y e' ∂(varsVol G ν)
        = ∫ e', flatIntegrand hs ψ (moved G keep g T) x y (e' + δ) ∂(varsVol G ν) :=
          (integral_add_right_eq_self _ δ).symm
      _ = ∫ e', (ψ (t * u) : ℂ) * flatIntegrand hs ψ (moved G keep g T) x y e' ∂(varsVol G ν) := by simp_rw [hI]
      _ = _ := integral_const_mul (ψ (t * u) : ℂ) _
  have hne' : (ψ (t * u) : ℂ) ≠ 1 := fun h => hne (Circle.ext (by simpa using h))
  have : (1 - (ψ (t * u) : ℂ)) * flatTensor hs ψ ν (moved G keep g T) x y = 0 := by
    rw [sub_mul, one_mul, ← hFeq, sub_self]
  rcases mul_eq_zero.1 this with h | h
  · exact hne' (sub_eq_zero.1 h).symm
  · exact hF h

end GlobalTheory.FunObj.FlatLast
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatTensorVanishesUnlessLastRowBoundedStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory ValuativeRel
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flatTensor_vanishes_unless_lastRow_bounded : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (G : Grid k) (hs : 1 ≤ G.s) (ψ : AddChar k Circle) (ν : Measure k) [ν.IsAddHaarMeasure] (ϖ : kˣ) (e : ℕ) (T : G.Args → ℂ) (keep : Bool) (g : G.VertexGroup), 2 ≤ G.m → IsUnif ϖ → HasConductor ψ 1 → G.IsTensor ϖ e (oppositePath G.m) T → ∃ n : ℕ, ∀ (x : ColArgs G) (y : RowArgs G), flatTensor hs ψ ν (moved G keep g T) x y ≠ 0 → ∀ s, valuation k (x (G.m - 1) (topLast G (G.m - 1 + 1)) s) ≤ valuation k (((ϖ ^ n)⁻¹ : kˣ) : k) := by
  first | exact @GlobalTheory.FunObj.FlatLast.flatTensor_lastRow_bounded | exact GlobalTheory.FunObj.FlatLast.flatTensor_lastRow_bounded | (intros; apply GlobalTheory.FunObj.FlatLast.flatTensor_lastRow_bounded <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramPosDefOfL2Definite
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramPosDefOfL2Definite
open Filter Topology MeasureTheory GlobalTheory.HSAmp
open scoped ComplexOrder Matrix

namespace GlobalTheory.HSAmp

theorem gram_posDef : ∀ (S : Type) (Y : S → Type) [∀ σ, MeasurableSpace (Y σ)] (ι : Type) [Fintype ι] [DecidableEq ι]
    (μ : ∀ σ, Measure (Y σ)) (v : ∀ σ, Y σ → ι → ℂ), IsFam μ v → (∀ c : ι → ℂ, l2 μ v c = 0 → c = 0) →
    (gram μ v).PosDef := by
  intro S Y _ ι _ _ μ v hF hinj
  obtain ⟨hH, hl⟩ := GlobalTheory.T.gram_isHermitian_l2_eq_double_sum S Y ι μ v hF
  refine Matrix.posDef_iff_dotProduct_mulVec.2 ⟨hH, fun x hx => ?_⟩
  obtain ⟨-, h0, heq⟩ := hl (fun i => (starRingEnd ℂ) (x i))
  have hform : star x ⬝ᵥ (gram μ v *ᵥ x) = ((l2 μ v (fun i => (starRingEnd ℂ) (x i)) : ℝ) : ℂ) := by
    rw [heq]
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply, Complex.star_def, Complex.conj_conj]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hform]
  have hne : l2 μ v (fun i => (starRingEnd ℂ) (x i)) ≠ 0 := by
    intro h
    apply hx
    funext i
    have := congrFun (hinj _ h) i
    simpa using this
  exact_mod_cast lt_of_le_of_ne h0 (Ne.symm hne)

end GlobalTheory.HSAmp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramPosDefOfL2DefiniteStatement
open Filter Topology MeasureTheory GlobalTheory.HSAmp
open scoped ComplexOrder Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gram_posDef_of_l2_definite : ∀ (S : Type) (Y : S → Type) [∀ σ, MeasurableSpace (Y σ)] (ι : Type) [Fintype ι] [DecidableEq ι] (μ : ∀ σ, Measure (Y σ)) (v : ∀ σ, Y σ → ι → ℂ), IsFam μ v → (∀ c : ι → ℂ, l2 μ v c = 0 → c = 0) → (gram μ v).PosDef := by
  first | exact @GlobalTheory.HSAmp.gram_posDef | exact GlobalTheory.HSAmp.gram_posDef | (intros; apply GlobalTheory.HSAmp.gram_posDef <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenyCompAndDegreeMul
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenyCompAndDegreeMul
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem isIsogeny_comp_and_deg_comp : ∀ (K : Type) [Field K] (A B C : AbVar K) (f : A ⟶ B) (g : B ⟶ C),
    IsIsogeny f → IsIsogeny g → IsIsogeny (f ≫ g) ∧ deg (f ≫ g) = deg f * deg g := by
  intro K _ A B C f g hf hg
  obtain ⟨-, hflf, -, hrf⟩ := GlobalTheory.T.dim_eq_flat_finrank_eq_deg_of_isIsogeny K A B f hf
  obtain ⟨-, hflg, -, -⟩ := GlobalTheory.T.dim_eq_flat_finrank_eq_deg_of_isIsogeny K B C g hg
  have : IsFinite f.hom.left := hf.1
  have : Surjective f.hom.left := hf.2
  have : IsFinite g.hom.left := hg.1
  have : Surjective g.hom.left := hg.2
  have hc : IsIsogeny (f ≫ g) := by
    refine ⟨?_, ?_⟩
    · rw [comp_hom, Over.comp_left]; infer_instance
    · rw [comp_hom, Over.comp_left]; infer_instance
  refine ⟨hc, ?_⟩
  have hdg : deg g = g.hom.left.finrank C.origin := if_pos hg
  have hdc : deg (f ≫ g) = (f ≫ g).hom.left.finrank C.origin := if_pos hc
  rw [hdc, hdg, comp_hom, Over.comp_left]
  exact GlobalTheory.FinrankComp.finrank_comp_of_const f.hom.left g.hom.left (deg f) hrf C.origin

end GlobalTheory.AV.AbVar
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenyCompAndDegreeMulStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isogeny_comp_and_degree_mul : ∀ (K : Type) [Field K] (A B C : AbVar K) (f : A ⟶ B) (g : B ⟶ C), IsIsogeny f → IsIsogeny g → IsIsogeny (f ≫ g) ∧ deg (f ≫ g) = deg f * deg g := by
  first | exact @GlobalTheory.AV.AbVar.isIsogeny_comp_and_deg_comp | exact GlobalTheory.AV.AbVar.isIsogeny_comp_and_deg_comp | (intros; apply GlobalTheory.AV.AbVar.isIsogeny_comp_and_deg_comp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InductiveMixedHeightTensorAdditive
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InductiveMixedHeightTensorAdditive
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

namespace GlobalTheory.MixHt

theorem recVal_tens_cons : ArchInteg → ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k), IsAmb q → ∀ e : ℕ, topologicalKrullDim Y = (e + 1 + 1 : ℕ) → ∀ T, IsMix q (e + 1) T → ∀ (M : HermLB q) (r : M.B.ι → Y.functionFieldˣ) (hr : IsRatSec M.B r) (A B : HermLB q) (L : Fin e → HermLB q), recVal (T (e + 1) (Fin.cons (A.tens B) L)) (Fin.cons (A.tens B) L : Fin (e + 1) → HermLB q) M hr = recVal (T (e + 1) (Fin.cons A L)) (Fin.cons A L : Fin (e + 1) → HermLB q) M hr + recVal (T (e + 1) (Fin.cons B L)) (Fin.cons B L : Fin (e + 1) → HermLB q) M hr := by
  intro hA k _ Y _ _ q hq e hdim T hT M r hr A B L
  have hN := hq.isNoetherian
  have hfin := (M.div hr).finite_support_mult
  have hm := (GlobalTheory.T.mixedArchIntegral_additive_and_diagonal hA k Y q hq M r hr).1 e hdim A B L
  have hsupp : ∀ (f : Y → ℝ), (Function.support fun z => ((M.div hr).mult z : ℝ) * f z).Finite := fun f =>
    hfin.subset fun z hz h => hz (by simp [h])
  unfold recVal
  rw [hm]
  have hsum : (∑ᶠ z, ((M.div hr).mult z : ℝ) * T (e + 1) (Fin.cons (A.tens B) L) z) =
      (∑ᶠ z, ((M.div hr).mult z : ℝ) * T (e + 1) (Fin.cons A L) z) +
        ∑ᶠ z, ((M.div hr).mult z : ℝ) * T (e + 1) (Fin.cons B L) z := by
    rw [← finsum_add_distrib (hsupp _) (hsupp _)]
    refine finsum_congr fun z => ?_
    by_cases h0 : (M.div hr).mult z = 0
    · simp [h0]
    · have hc := CartierDiv.coheight_eq_one_of_mult_ne_zero h0
      have hd := ((GlobalTheory.T.coheight_one_iff_pointClosure_dim_projArith k Y q hq (e + 1) hdim).1 z).1 hc
      rw [hT.add e A B L z le_rfl hd, mul_add]
  rw [hsum]
  ring

end GlobalTheory.MixHt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InductiveMixedHeightTensorAdditiveStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inductiveMixedHeight_tensor_additive : ArchInteg → ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k), IsAmb q → ∀ e : ℕ, topologicalKrullDim Y = (e + 1 + 1 : ℕ) → ∀ T, IsMix q (e + 1) T → ∀ (M : HermLB q) (r : M.B.ι → Y.functionFieldˣ) (hr : IsRatSec M.B r) (A B : HermLB q) (L : Fin e → HermLB q), recVal (T (e + 1) (Fin.cons (A.tens B) L)) (Fin.cons (A.tens B) L : Fin (e + 1) → HermLB q) M hr = recVal (T (e + 1) (Fin.cons A L)) (Fin.cons A L : Fin (e + 1) → HermLB q) M hr + recVal (T (e + 1) (Fin.cons B L)) (Fin.cons B L : Fin (e + 1) → HermLB q) M hr := by
  first | exact @GlobalTheory.MixHt.recVal_tens_cons | exact GlobalTheory.MixHt.recVal_tens_cons | (intros; apply GlobalTheory.MixHt.recVal_tens_cons <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralFramePointStalkCompat
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlatValZero

section Gen

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD _root_.Formalism.L2.Pj Formalism.BasicNotions
  GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.FlatCore GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ}

theorem nonempty_keySec (hL : Laws U x) : Nonempty (KeySec Xo c) := by
  obtain ⟨κ, k₁, k₂, -, k₄, -, k₆, -, -⟩ := GlobalTheory.KeyFamClosing.keyFam_one
  let e : Fin (Fintype.card (Σ τ : E →+* ℂ, Fin (Dw.mult τ))) ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ) :=
    (Fintype.equivFin _).symm
  obtain ⟨K, hKmem, hKval⟩ := GlobalTheory.T.exists_unit_section_thetaKeyRule_weightFour κ k₁ k₂ k₆ E H Dw l Xo c _ e hL.pos
  have hσ0 := goodEmb_goodOf c c.F.val.toRingHom
  obtain ⟨ρ, -⟩ := GlobalTheory.T.exists_keySection_fourthRoot_perComponent κ k₁ k₂ k₆ k₄ E H Dw l Xo c _ e _ r (U _) K hσ0 (hL.unf _ hσ0) hL.geo hL.pos
    hKmem hKval
  exact ⟨ρ⟩

def unitsV (T : CDVR) : Submonoid T.Fr where
  carrier := {z | z ≠ 0 ∧ vV T.V z = 0}
  one_mem' := ⟨one_ne_zero, by simp [vV]⟩
  mul_mem' := fun {a b} ha hb => ⟨mul_ne_zero ha.1 hb.1, by rw [vV_mul ha.1 hb.1, ha.2, hb.2, add_zero]⟩

end Gen

end GlobalTheory.FlatValZero

open GlobalTheory.FlatValZero


end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoIffDegEqOne
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.AV.AbVar

theorem isIso_of_isIso_left {K : Type} [Field K] {A B : AbVar K} (f : A ⟶ B) [IsIso f.hom.left] : IsIso f := by
  have : IsIso ((Over.forget _).map f.hom) := by simpa using (inferInstance : IsIso f.hom.left)
  have : IsIso f.hom := isIso_of_reflects_iso f.hom (Over.forget _)
  have : IsMonHom (inv f.hom) := inferInstanceAs (IsMonHom (asIso f.hom).inv)
  let g : B ⟶ A := Hom.mk (A := B) (B := A) (inv f.hom)
  refine ⟨g, ?_, ?_⟩
  · apply Subtype.ext
    change Hom.hom (f ≫ g) = Hom.hom (𝟙 A)
    simp [g]
  · apply Subtype.ext
    change Hom.hom (g ≫ f) = Hom.hom (𝟙 B)
    simp [g]

instance isIso_left_of_isIso {K : Type} [Field K] {A B : AbVar K} (f : A ⟶ B) [IsIso f] : IsIso f.hom.left := by
  have : IsIso f.hom := ⟨(inv f).hom, by rw [← comp_hom, IsIso.hom_inv_id, id_hom], by rw [← comp_hom, IsIso.inv_hom_id, id_hom]⟩
  exact (inferInstance : IsIso ((Over.forget _).map f.hom))

theorem isIso_iff_deg_eq_one : ∀ (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B),
    (IsIso f → IsIsogeny f ∧ deg f = 1) ∧ (deg f = 1 → IsIso f) := by
  intro K _ A B f
  refine ⟨fun hf => ?_, fun hd => ?_⟩
  · have hI : IsIsogeny f := ⟨inferInstance, inferInstance⟩
    refine ⟨hI, ?_⟩
    rw [deg, if_pos hI, Scheme.Hom.finrank_eq_one_of_isIso]
    rfl
  · have hI : IsIsogeny f := by
      by_contra h
      rw [deg, if_neg h] at hd
      exact zero_ne_one hd
    obtain ⟨-, hfl, -, hr⟩ := GlobalTheory.T.dim_eq_flat_finrank_eq_deg_of_isIsogeny K A B f hI
    have : IsFinite f.hom.left := hI.1
    have : IsIso f.hom.left := by
      rw [Scheme.Hom.isIso_iff_finrank_eq]
      funext y
      rw [hr y, hd]
      rfl
    exact isIso_of_isIso_left f

end GlobalTheory.AV.AbVar
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionValueUnitFrameConjPointEqPhaseConj
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionValueUnitFrameConjPointEqPhaseConj
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSAmp

def conjPt {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} (y : CxPts p σ) :
    CxPts p ((starRingEnd ℂ).comp σ) :=
  ⟨spMap (starRingEnd ℂ) ≫ y.1, by
    have e : spMap ((starRingEnd ℂ).comp σ) = spMap (starRingEnd ℂ) ≫ spMap σ := by
      rw [spMap, spMap, spMap, ← Spec.map_comp]
      rfl
    rw [Category.assoc, y.2, e]⟩

theorem ratVal_conj {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {q : X ⟶ Sp k} {σ σ' : k →+* ℂ}
    {f : X.functionField} {y : CxPts q σ} {y' : CxPts q σ'}
    (h : y'.1 = spMap (starRingEnd ℂ) ≫ y.1) (hf : RegAt (under y) f) :
    ratVal f y' = starRingEnd ℂ (ratVal f y) := by
  obtain ⟨U, hU, a, rfl⟩ := hf.exists_fnOf
  have hy : y ∈ ptsIn q σ U := mem_ptsIn.2 hU
  rw [ratVal_fnOf hy, ratVal_fnOf (CxPts.mem_ptsIn_conj h hy), CxPts.ev_conj h hy]

theorem val_conj : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (P : Pair p), ∀ (a b : ℤ) (σ : k →+* ℂ) (y : CxPts p σ), ∃ (σ' : k →+* ℂ) (y' : CxPts p σ') (θ : ℂ), ‖θ‖ = 1 ∧ ∀ f ∈ P.H a b, val P a b σ' y' f = θ * (starRingEnd ℂ) (val P a b σ y f) := by
  intro k _ X _ p P a b σ y
  have h : (conjPt y).1 = spMap (starRingEnd ℂ) ≫ y.1 := rfl
  have hi := mem_pick (P.L.φ σ).isLB y
  have hj := mem_pick (P.A.φ σ).isLB y
  obtain ⟨θ₁, h₁, e₁⟩ := GlobalTheory.T.sectionValueUnitFrame_eq_localFunction_unitScalar k X p P a b σ y _ _ hi hj
  obtain ⟨θ₂, h₂, e₂⟩ := GlobalTheory.T.sectionValueUnitFrame_eq_localFunction_unitScalar k X p P a b _ (conjPt y) _ _
    (CxPts.mem_ptsIn_conj h hi) (CxPts.mem_ptsIn_conj h hj)
  refine ⟨_, conjPt y, θ₂ * θ₁, by rw [norm_mul, h₁, h₂, one_mul], fun f hf => ?_⟩
  have hreg := hf _ _ _ (mem_ptsIn.1 hi) (mem_ptsIn.1 hj)
  rw [e₁ f hf, e₂ f hf, ratVal_conj h hreg, P.L.conj σ _ _ y _ h hi, P.A.conj σ _ _ y _ h hj]
  have hθ : θ₁ * starRingEnd ℂ θ₁ = 1 := by
    rw [Complex.mul_conj', h₁]
    simp
  simp only [map_mul, Complex.conj_ofReal]
  linear_combination (-(θ₂ * starRingEnd ℂ (ratVal (P.loc a b f (pick (P.L.φ σ).isLB y) (pick (P.A.φ σ).isLB y)) y) *
    ((Real.exp (-(a * (P.L.φ σ).φ (pick (P.L.φ σ).isLB y) y + b * (P.A.φ σ).φ (pick (P.A.φ σ).isLB y) y) / 2) : ℝ) : ℂ))) * hθ

end GlobalTheory.HSAmp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionValueUnitFrameConjPointEqPhaseConjStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sectionValueUnitFrame_conj_point_eq_phase_conj : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (P : Pair p), ∀ (a b : ℤ) (σ : k →+* ℂ) (y : CxPts p σ), ∃ (σ' : k →+* ℂ) (y' : CxPts p σ') (θ : ℂ), ‖θ‖ = 1 ∧ ∀ f ∈ P.H a b, val P a b σ' y' f = θ * (starRingEnd ℂ) (val P a b σ y f) := by
  first | exact @GlobalTheory.HSAmp.val_conj | exact GlobalTheory.HSAmp.val_conj | (intros; apply GlobalTheory.HSAmp.val_conj <;> assumption)
end
end
