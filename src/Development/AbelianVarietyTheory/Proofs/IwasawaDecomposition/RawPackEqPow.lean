module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnlocalizedSaturatedState
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistDataAgreeAcrossCoefficientsLocalized
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GeometricWeakTiesOfStrong
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.OntoAlong
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OneParamSubgroupTransposeGramUnitaryDecomposes
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftAdelicFormLevelTypeEqColumnLevel
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TranslatedStdLatticeEqDecoratedLatticeReindexed
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DofOTw

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RawPackEqPow
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HeightCounting.Rigid

theorem exists_frob (hc : GlobalTheory.TwSys.Cheb) (D : D7) (i : D.ntw.Tw) (Q : Finset (PlE D.host)) {p : ℕ} (hp : p ≠ 0)
    (γ : D.ntw.RCG i Q) :
    ∃ w, w ∉ Q ∧ w ∉ placesOver D.host.E p ∧ ∃ (B : ValuationSubring D.nd.Om) (σ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om),
      Formalism.ConjugateSelfDual.IsPlaceOver B w ∧ Formalism.ConjugateSelfDual.IsFrob B (Formalism.ConjugateSelfDual.normV w) σ ∧ D.ntw.art i Q σ = γ := by
  classical
  obtain ⟨g, rfl⟩ := D.ntw.art_surj i Q γ
  obtain ⟨w, hwA, -, -, B, hB, -, σ, hσ, hU⟩ := hc D.host.E D.nd.Om (D.ntw.art i Q).ker (D.ntw.art_cont i Q) inferInstance g
    (Q ∪ (placesOver_finite_av D.host.E p hp).toFinset)
  refine ⟨w, fun h => hwA (Finset.mem_union_left _ h),
    fun h => hwA (Finset.mem_union_right _ ((Set.Finite.mem_toFinset _).2 h)), B, σ, hB, hσ, ?_⟩
  rwa [MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one] at hU

theorem pow_of_tied (hc : GlobalTheory.TwSys.Cheb) {D : D7} (cf : CharFrame D) (C : NChoice D) (tp : TupTied D cf C)
    (v : D.what₂.places.Pl) (ψ : D.ntw.RCG (C.twI v) (C.Q v) →* (D.ntw.Ok (C.twI v) (C.k' v))ˣ)
    (ι : TwChar.RootIso D (C.twI v) (C.k' v))
    (hF : TwChar.FrobPick (C.twI v) (C.Q v) (C.k' v) ψ ι (tp.psi v)) (hT : PsiChoiceCompatible D cf C tp)
    (htw : TwistedAt D v) (hk : 1 ≤ C.k' v)
    (hL : ∀ z : ℂ, z ^ D.what₂.places.resChar v ^ C.k' v = 1 → ∃ x : D.what₂.LL, D.what₂.embLL x = z) :
    ∃ a : ℕ, a.Coprime (D.ntw.l (C.twI v)) ∧ C.psi' v = ψ ^ a := by
  haveI : NeZero (D.ntw.l (C.twI v) ^ C.k' v) := ⟨pow_ne_zero _ (D.ntw.lPrime _).out.ne_zero⟩
  have hL' : ∀ z : ℂ, z ^ (D.ntw.l (C.twI v) ^ C.k' v) = 1 → ∃ x : D.what₂.LL, D.what₂.embLL x = z := fun z hz =>
    hL z (by rw [← C.twI_l v]; exact hz)
  let j : D.ntw.Ok (C.twI v) (C.k' v) →+* FractionRing (C.Oe v) :=
    (algebraMap (C.Oe v) (FractionRing (C.Oe v))).comp (algebraMap (D.ntw.Ok (C.twI v) (C.k' v)) (C.Oe v))
  have hj : Function.Injective j := (IsFractionRing.injective (C.Oe v) (FractionRing (C.Oe v))).comp (C.Oe_inj v)
  obtain ⟨a, ha, hax⟩ := TwChar.exists_exponent ι (D.ntw.zk_prim _ _) D.what₂.embLL hL' (C.embW v) j hj
  refine ⟨a, Nat.Coprime.coprime_dvd_right (dvd_pow_self _ (by omega)) ha, MonoidHom.ext fun γ => Units.ext ?_⟩
  have hp : D.what₂.places.resChar v ≠ 0 := by rw [← C.twI_l v]; exact (D.ntw.lPrime _).out.ne_zero
  obtain ⟨w, hwQ, hwl, B, σ, hB, hσ, rfl⟩ := exists_frob hc D (C.twI v) (C.Q v) hp γ
  obtain ⟨u, hu, hχ⟩ := hF w hwQ B hB σ hσ
  obtain ⟨x, hx⟩ := hL' ((ι u : ℂˣ) : ℂ) (by rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity _ _).1 (ι u).2, Units.val_one])
  have h1 := hT v htw w hwQ hwl B σ hB hσ x (by rw [hχ, inv_inv]; exact hx)
  have h2 := hax u x hx
  have h3 := hj (h1.symm.trans h2)
  rw [MonoidHom.pow_apply, ← hu]
  exact h3


set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem transfer {D₁ D₂ : D7} (h : SameExport D₁ D₂) (p : TwPack D₁) (A : Finset (PlE D₁.host))
    (ι : TwChar.RootIso D₁ p.1 p.2.2.1) (χ : HChar D₁.host.E) (hO : BlochKatoReduction.Gen.PsiOk p.1 A p.2.1 p.2.2.1 p.2.2.2)
    (hF : TwChar.FrobPick p.1 p.2.1 p.2.2.1 p.2.2.2 ι χ) (i₂ : D₂.ntw.Tw) (Q₂ : Finset (PlE D₂.host)) (k₂ : ℕ)
    (χ₂ : HChar D₂.host.E) (hi : HEq i₂ p.1) (hQ : HEq Q₂ p.2.1) (hk : k₂ = p.2.2.1) (hχ : HEq χ₂ χ) :
    ∃ (ψ₂ : D₂.ntw.RCG i₂ Q₂ →* (D₂.ntw.Ok i₂ k₂)ˣ) (ι₂ : TwChar.RootIso D₂ i₂ k₂) (A₂ : Finset (PlE D₂.host)),
      BlochKatoReduction.Gen.PsiOk i₂ A₂ Q₂ k₂ ψ₂ ∧ TwChar.FrobPick i₂ Q₂ k₂ ψ₂ ι₂ χ₂ ∧ D₂.ntw.l i₂ = D₁.ntw.l p.1 ∧
      ∀ a : ℤ, HEq (⟨i₂, Q₂, k₂, ψ₂ ^ a⟩ : TwPack D₂) (GlobalTheory.HeightCounting.twPackPow D₁ a p) := by
  obtain ⟨h1, h2, -, -, -⟩ := h
  obtain ⟨i, Q, k, ψ⟩ := p
  dsimp only at hi hQ hk hO hF ι ⊢
  subst hk
  obtain ⟨a1, a2, a3, nOm, ninstOm, nalgOm, nplOm, nPlG⟩ := h1
  obtain ⟨xcc, xTw, xl, fixedFieldTransport_baseIntegerRing_heq, fixedFieldTransport_baseIntegerCommRing_heq, fixedFieldTransport_baseIntegerAlgebra_heq, fixedFieldTransport_baseIntegerTopology_heq, xO, xcrO, xalgO, xOk, xcrOk, xalgOk, xzk, xpD, xchi1, xSig, xfinSig, xjS, xside, xrhoS, fixedFieldTransport_initialPlaceSet_heq, xhEig, xLam, xsideL, xRCG, xgrpRCG, xfinRCG, xart, xth⟩ := h2
  cases D₁; cases D₂
  dsimp only at a1 a2 a3
  subst a1; subst a2; subst a3
  cases ‹NData _ _ _›; cases ‹NData _ _ _›
  dsimp only at nOm ninstOm nalgOm nplOm nPlG
  subst nOm; subst ninstOm; subst nalgOm; subst nplOm; subst nPlG
  cases ‹@NTw _ _ _ _ _ _ _›; cases ‹@NTw _ _ _ _ _ _ _›
  dsimp only at xcc xTw xl fixedFieldTransport_baseIntegerRing_heq fixedFieldTransport_baseIntegerCommRing_heq fixedFieldTransport_baseIntegerAlgebra_heq fixedFieldTransport_baseIntegerTopology_heq xO xcrO xalgO xOk xcrOk xalgOk xzk xpD xchi1 xSig xfinSig xjS xside xrhoS fixedFieldTransport_initialPlaceSet_heq xhEig xLam xsideL xRCG xgrpRCG xfinRCG xart xth
  subst xcc; subst xTw; subst xl; subst fixedFieldTransport_baseIntegerRing_heq; subst fixedFieldTransport_baseIntegerCommRing_heq; subst fixedFieldTransport_baseIntegerAlgebra_heq; subst fixedFieldTransport_baseIntegerTopology_heq; subst xO; subst xcrO; subst xalgO; subst xOk; subst xcrOk; subst xalgOk; subst xzk; subst xpD; subst xchi1; subst xSig; subst xfinSig; subst xjS; subst xside; subst xrhoS; subst fixedFieldTransport_initialPlaceSet_heq; subst xhEig; subst xLam; subst xsideL; subst xRCG; subst xgrpRCG; subst xfinRCG; subst xart; subst xth
  subst hi; subst hQ; subst hχ
  exact ⟨ψ, ι, A, hO, hF, rfl, fun _ => HEq.rfl⟩

end GlobalTheory.HeightCounting.Rigid
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AgreeOfData
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.IndefR.NX ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 4000000

noncomputable section

namespace GlobalTheory.HeightCounting.Up.ThirdAgree

open Formalism.BasicNotions.TH _root_.Formalism.L2.Theta _root_.Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.RecTie GlobalTheory.Mem.R3.Tr GlobalTheory.HeightCounting.Up.RealOfReading

section Gen

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3} {X0 : BaseLevelRowSide D}

theorem agree_of_data (Y : GlobalTheory.Mem.R3.Read (A3 := A3) R.toRealDat F.lv2 X0) {cf : CharFrame D} {nch : NChoice D}
    (tp : TupTied D cf nch) (hC : R.C = cf) (Xd : DivX D) (E : EigIdx D Xd) (labPi : E.Pi → A3.A.fam.base.Ix) (hb htup hg hf)
    (M : MtFam D) (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r) (hrep : ∀ σ, (rep σ).Iso (principalLevelFrame.rowRepR R.θ (Y.eFT σ)))
    (c : ∀ i, CoefA (Vc D i)) (hc : R.cV = c) (PV : ∀ i : Fin D.R.m, principalLevelFrame.RowPsi (Vc D i) D.R.nV)
    (std : ∀ i, R3.StdFrame Y.hF (PV i))
    (eW : ∀ μ, Used0 D μ → ∀ i : Fin D.R.m, (M μ (i.1 + 1) (by omega) (by omega)).wt.W ≃ₗ[ℂ] (c i).W)
    (jm : ∀ μ, Used0 D μ → ∀ i : Fin D.R.m, D.what₂.Mt μ (i.1 + 1) → GA D (Vc D i) → (c i).W)
    (hj : ∀ μ h i x, HEq (Y.IL.jMt μ h i x).1 (jm μ h i x))
    (read : ∀ μ (h : Used0 D μ) (i : Fin D.R.m) (x : D.what₂.Mt μ (i.1 + 1)) (g : GAf D.host.E D.R.nV),
      eW μ h i ((M μ (i.1 + 1) (by omega) (by omega)).real x g) = jm μ h i x ((PV i).ψ g))
    (rat : ∀ (i : Fin D.R.m) (g : GAf D.host.E D.R.nV), g ∈ ReciprocityTheory.Aut.GQ D.host.E D.R.nV ↔
      ∃ γ ∈ Formalism.L2.Theta.GQ (Vc D i), finHom (Vc D i) γ = finHom (Vc D i) ((PV i).ψ g))
    (wt : ∀ μ (h : Used0 D μ) (i : Fin D.R.m) (g : ReciprocityTheory.Aut.GQ D.host.E D.R.nV), ∀ γ ∈ Formalism.L2.Theta.GQ (Vc D i),
      finHom (Vc D i) γ = finHom (Vc D i) ((PV i).ψ g) → ∀ v,
        eW μ h i ((M μ (i.1 + 1) (by omega) (by omega)).wt.ρ g v) = (c i).ρ γ (eW μ h i v)) :
    Nonempty (GlobalTheory.NJoin.Agree (realOfRead R.toRealDat F.lv2 Y tp hC Xd E labPi hb htup hg hf) M rep) := by
  subst hc
  refine ⟨⟨Y.hF, PV, fun j => (StandardFrameAgreement.stdFrame_iff _ _).1 (std j), fun j => (StandardFrameAgreement.stdFrame_iff _ _).1 (Y.stdPsi.2 j),
    fun _ => 1, ?_, fun μ hμ j => (eW μ hμ j).symm, ?_, ?_, hrep⟩⟩
  · intro j h
    simp only [inv_one, one_mul, mul_one]
    exact rat j h
  · intro μ hμ j h γ hγ he v
    have he' := he
    simp only [inv_one, one_mul, mul_one] at he'
    have key := wt μ hμ j h γ hγ he' ((eW μ hμ j).symm v)
    refine (LinearEquiv.symm_apply_eq _).2 ?_
    refine Eq.trans ?_ key.symm
    exact congrArg _ (LinearEquiv.apply_symm_apply _ v).symm
  · intro μ hμ j x h
    refine (LinearEquiv.eq_symm_apply _).2 ?_
    refine (read μ hμ j x h).trans ?_
    simp only [inv_one, one_mul]
    exact (congrFun (eq_of_heq (hj μ hμ j x)) _).symm

theorem heq_apply {Mt : D.what₂.Tup → ℕ → Hs} {c c' : ∀ i, CoefA (Vc D i)} (h : c = c')
    (j : ∀ μ (i : Fin D.R.m), (Mt μ ((i : ℕ) + 1)).T →ₗ[ℂ] (GA D (Vc D i) → (c i).W))
    (j' : ∀ μ (i : Fin D.R.m), (Mt μ ((i : ℕ) + 1)).T →ₗ[ℂ] (GA D (Vc D i) → (c' i).W)) (hj : HEq j j') (μ i x) :
    HEq (j μ i x) (j' μ i x) := by
  subst h
  cases hj
  rfl

end Gen

section Copy

variable {B : Base} {C : Cols B} {a : Late B C} (b : Late B C) {px : PreX B.toPre} {I : ColIn B px} {hX : B.fields.Ok} {T : TwDat B}
  {Wt : Set B.places.Pl}

def cpR (z : Dat a.st I hX T Wt) :
    @RealDat3 b.st.toD7 _ _ _ _ _ _ (famR b.st I hX (usedOf I T Wt) z.Xg z.tr) (coreJ b z.core).Q.c.F _ _ ((by exact @alg B C a b (↥(@ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff.F (@Formalism.HC.HostRaw.E (@Late.st B C a).toD7.R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.st B C a).toD7.R.toFrame (@Host.toHostAx (@Late.st B C a).toD7.R (@Late.st B C a).toD7.host))) (@Formalism.HC.HostRaw.instField (@Late.st B C a).toD7.R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.st B C a).toD7.R.toFrame (@Host.toHostAx (@Late.st B C a).toD7.R (@Late.st B C a).toD7.host))) (@Formalism.HC.HostRaw.instNF (@Late.st B C a).toD7.R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.st B C a).toD7.R.toFrame (@Host.toHostAx (@Late.st B C a).toD7.R (@Late.st B C a).toD7.host))) (Pj.instCMHost (@Late.st B C a).toD7) (@Pj.Par.H (@Late.st B C a).toD7 (@Pj.Core.Q (@Late.st B C a).toD7 (@Pj.CoreJ.toCore (@Late.st B C a).toD7 (@Dat.core (@Late.st B C a) px I hX T Wt z)))) (@Pj.Par.l (@Late.st B C a).toD7 (@Pj.Core.Q (@Late.st B C a).toD7 (@Pj.CoreJ.toCore (@Late.st B C a).toD7 (@Dat.core (@Late.st B C a) px I hX T Wt z)))) (@Pj.Par.c (@Late.st B C a).toD7 (@Pj.Core.Q (@Late.st B C a).toD7 (@Pj.CoreJ.toCore (@Late.st B C a).toD7 (@Dat.core (@Late.st B C a) px I hX T Wt z)))))) (@IntermediateField.toField Rat Complex Rat.instField Complex.instField (@DivisionRing.toRatAlgebra Complex (@Field.toDivisionRing Complex Complex.instField) Complex.instCharZero) (@ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff.F (@Formalism.HC.HostRaw.E (@Late.st B C a).toD7.R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.st B C a).toD7.R.toFrame (@Host.toHostAx (@Late.st B C a).toD7.R (@Late.st B C a).toD7.host))) (@Formalism.HC.HostRaw.instField (@Late.st B C a).toD7.R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.st B C a).toD7.R.toFrame (@Host.toHostAx (@Late.st B C a).toD7.R (@Late.st B C a).toD7.host))) (@Formalism.HC.HostRaw.instNF (@Late.st B C a).toD7.R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.st B C a).toD7.R.toFrame (@Host.toHostAx (@Late.st B C a).toD7.R (@Late.st B C a).toD7.host))) (Pj.instCMHost (@Late.st B C a).toD7) (@Pj.Par.H (@Late.st B C a).toD7 (@Pj.Core.Q (@Late.st B C a).toD7 (@Pj.CoreJ.toCore (@Late.st B C a).toD7 (@Dat.core (@Late.st B C a) px I hX T Wt z)))) (@Pj.Par.l (@Late.st B C a).toD7 (@Pj.Core.Q (@Late.st B C a).toD7 (@Pj.CoreJ.toCore (@Late.st B C a).toD7 (@Dat.core (@Late.st B C a) px I hX T Wt z)))) (@Pj.Par.c (@Late.st B C a).toD7 (@Pj.Core.Q (@Late.st B C a).toD7 (@Pj.CoreJ.toCore (@Late.st B C a).toD7 (@Dat.core (@Late.st B C a) px I hX T Wt z)))))) (@Dat.alg (@Late.st B C a) px I hX T Wt z))) :=
  (by with_unfolding_all exact ((real3 b (iK := z.alg) z.R) :))

def cpV (c : ∀ i, CoefA (Vc a.D i)) : ∀ i, CoefA (Vc b.D i) := fun i => (by with_unfolding_all exact ((coefA b (c ((by with_unfolding_all exact (i :))))) :))

theorem cV_copy (z₀ : Dat a.st I hX T Wt) (z : Dat b.st I hX T Wt) (h1 : z.Xg = z₀.Xg) (h2 : z.tr = z₀.tr)
    (h3 : HEq z.core (coreJ b z₀.core)) (h4 : HEq z.R (real3 b (iK := z₀.alg) z₀.R)) : z.R.cV = cpV b z₀.R.cV := by
  obtain @⟨Xg, tr, core, al, alg_eq, R, cG, geo, pins, lev, idG, good, mu, l1, l2⟩ := z
  dsimp only at h1 h2 h3 h4
  subst h1 h2
  obtain rfl : core = coreJ b z₀.core := eq_of_heq h3
  have e : al = (by with_unfolding_all exact ((alg b z₀.alg) :)) := by
    refine Algebra.algebra_ext _ _ fun y => B.embLL.injective ?_
    exact (alg_eq y).trans ((by with_unfolding_all exact ((z₀.alg_eq ((by with_unfolding_all exact (y :)))).symm :)))
  subst e
  obtain rfl : R = cpR b z₀ := eq_of_heq (h4.trans ((by with_unfolding_all exact ((HEq.refl (cpR b z₀)) :))))
  exact (by with_unfolding_all exact ((Eq.refl (cpV b z₀.R.cV)) :))

theorem cV_two (b' : Late B C) {c₀ : ∀ i, CoefA (Vc a.D i)} {c : ∀ i, CoefA (Vc b.D i)} {c' : ∀ i, CoefA (Vc b'.D i)}
    (h : c = cpV b c₀) (h' : c' = cpV b' c₀) : c' = cpV b' c := by
  subst h h'
  exact (by with_unfolding_all exact ((Eq.refl (cpV b' c₀)) :))

end Copy

section Main

theorem iso_of_eq {Lf : Type} [Field Lf] [NumberField Lf] [IsCMField Lf] {n : ℕ} {π π' : NG.FinTyp Lf n} (h : π = π') : π.Iso π' :=
  h ▸ NG.IsoRep.refl _


end Main

end GlobalTheory.HeightCounting.Up.ThirdAgree

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClassSumDivisibilityBundle
section -- merged from Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ClassSumOfPin
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.FWT Formalism.IndefR.NX Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.BigTop

namespace GlobalTheory.ExportPin.Model

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

theorem theta_cast (j : ℕ) (μ ν : D.what₂.Tup) (h : μ = ν) (x : D.what₂.MtL μ j) :
    D.what₂.thetaP ν j (D.what₂.jMt ν j (h ▸ x)) = D.what₂.thetaP μ j (D.what₂.jMt μ j x) := by
  subst h; rfl



end GlobalTheory.ExportPin.Model
end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.BigTop

namespace GlobalTheory.ClassSumPinLink

open _root_.Formalism.L2 _root_.Formalism.L2.Theta _root_.Formalism.L2.DIV _root_.Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}


set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem classSumPin_of_read (p : PtAt ex Csz) (Yr : R3.Read (A3 := p.P.A3) p.R.toRealDat p.F.lv2 ex.p0)
    (hjW : ∀ (i : Fin D.R.m) (v : Fin ((p.P.A3.indefDown p.P.S0).dW i) → D.what₂.LL)
      (y : Fin (Module.finrank D.what₂.LL (p.R.toRealDat.WL p.F.lv2 false i)) → D.what₂.LL), HEq v y →
      Yr.mj.eW i (p.P.I.jW i v) = (p.R.FW i).j (sg0 D p.P.A3.A) (jDL p.R p.F.lv2 i y))
    (hth : GlobalTheory.HeightCounting.EMtTheta Yr p.nexp ex.nch)
    (hD : DivRows3 D p.P.A3 p.P.P0 p.P.ψ0 p.P.Ps p.P.ψs p.P.Zs p.P.S0 p.P.S1 ex.p0 p.P.C p.P.NuC p.P.I) :
    GlobalTheory.ExportPin.ClassSumPin p := by
  intro w i h1 h2 t ht hw c x hx hxT y hy n a f hsum
  subst hx
  apply hth w i hw _ hxT n a f
  rw [hsum, GlobalTheory.ExportPin.Model.theta_cast _ _ _ ht, hD.thTheta, hjW i _ y hy]

end GlobalTheory.ClassSumPinLink

namespace GlobalTheory.ClassSumPinLink

open _root_.Formalism.L2 _root_.Formalism.L2.Theta _root_.Formalism.L2.DIV _root_.Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX

section Pack

variable {D : D7} {O : Obj D}




end Pack

end GlobalTheory.ClassSumPinLink

namespace GlobalTheory.ClassSumPinLink

open _root_.Formalism.L2 _root_.Formalism.L2.Theta _root_.Formalism.L2.DIV _root_.Formalism.L2.Indef _root_.Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX


set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem eMtTheta_of_pack {D : D7} {nch : NChoice D} {X0 : BaseLevelRowSide D} {G G' : Type} {g : Group G} {g' : Group G'} {fi : Fintype G}
    {fi' : Fintype G'} {Pl0 I0 T Pl0' I0' T' : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
    {A3' : FamIn3 D.what₂.LL G' Pl0' I0' (List ℕ) T' D.R.m}
    {C C' : CoreJ D} {al : Algebra C.Q.c.F D.what₂.LL} {al' : Algebra C'.Q.c.F D.what₂.LL} {R : RealDat3 D A3 C.Q.c.F}
    {R' : RealDat3 D A3' C'.Q.c.F} {F : Face3 D A3} {F' : Face3 D A3'} {kap : ℝ} {lam : type_of% R'.lam3} {err : type_of% R'.err0}
    {Dc : ∀ Zs : DefSub A3'.fam3.amb3, DefCols (A3'.side3 F'.P1 F'.ψ1 Zs)} {Sp : ∀ Zs, SPer (Dc Zs)}
    {Zsc : DefSub A3'.fam3.amb3 → IndefScale A3'.fam3.base3}
    {cG : G0 R.Pg D.R.r ≃* G0g D.nd} {cG' : G0 R'.Pg D.R.r ≃* G0g D.nd}
    {cG'' : G0 ((R'.updS kap lam).withErr err).Pg D.R.r ≃* G0g D.nd}
    (pack : (⟨G, g, fi, Pl0, I0, T, A3, C, al, R, F, cG⟩ :
      Σ' (G : Type) (_ : Group G) (_ : Fintype G) (Pl0 I0 T0 : Type)
        (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m) (C : CoreJ D)
        (_ : Algebra C.Q.c.F D.what₂.LL) (R : RealDat3 D A3 C.Q.c.F) (_ : Face3 D A3),
        G0 R.Pg D.R.r ≃* G0g D.nd) =
      ⟨G', g', fi', Pl0', I0', T', A3', C', al', (R'.updS kap lam).withErr err, R3.reFace F' Dc Sp Zsc, cG''⟩)
    (Y : R3.Read (A3 := A3) R.toRealDat F.lv2 X0) (Y' : R3.Read (A3 := A3') R'.toRealDat F'.lv2 X0)
    (hW : HEq Y.mj.eW Y'.mj.eW) {S S' : RatDat D.ntw} (hS : S = S')
    (E : NExpRealS R cG S) (E' : NExpRealS R' cG' S') (hF : HEq E.eF E'.eF) (hi : HEq E.fi E'.fi)
    (h : GlobalTheory.HeightCounting.EMtTheta Y' E' nch) : GlobalTheory.HeightCounting.EMtTheta Y E nch := by
  cases pack
  cases hS
  intro w i hw x hx n a f hs
  have e1 : E.eF = E'.eF := eq_of_heq hF
  have e2 : E.fi = E'.fi := eq_of_heq hi
  have e3 : Y.mj.eW = Y'.mj.eW := eq_of_heq hW
  rw [e2, e3] at hs
  rw [e1]
  exact h w i hw x hx n a f hs


end GlobalTheory.ClassSumPinLink

namespace GlobalTheory.ClassSumPinLink


end GlobalTheory.ClassSumPinLink
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftFormLvlOp
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.HeightCounting GlobalTheory.CenFrame
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CenTranslate

section Act
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

theorem extV_act (hr : R.grp_red_L) (hj : R.models_jV) (hc : R.models_cV) (i : Fin D.R.m) (t : T0) (g : G)
    (κ : GA D (Vc D i)) (hκ : IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) (R.eG g) κ) (u : (A.fam.L i t).S.Forms)
    (h : GA D (Vc D i)) :
    R.extV i t (R.jV i t ((A.fam.L i t).r g u)) h =
      (levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) κ)⁻¹ • R.extV i t (R.jV i t u) (h * κ) := by
  have hT := GlobalTheory.RationalFormsAction.isTranslate_act_V R hr hj i t g u
  have hq : (finHom (Vc D i)).rangeRestrict κ ∈ (levEnv (Vc D i) (R.βV i) (R.datVt i t)).Q := by
    have h1 := hκ.2.1
    exact ⟨h1, trivial⟩
  let q : (levEnv (Vc D i) (R.βV i) (R.datVt i t)).Q := ⟨_, hq⟩
  have hl : GlobalTheory.IndefiniteRowSideFullHecke.TranslateRepresentations.LiftsTo (Vc D i) (R.βV i) (R.datVt i t) q (R.eG g) := hκ.2.2
  have e := hT.2 q hl ((finHom (Vc D i)).rangeRestrict h)
  have hk : (R.cV i).ρ κ⁻¹ = 1 := (hc i).1 _ (inv_mem hκ.1)
  have hρ : (R.cV i).ρ (h * κ)⁻¹ = (R.cV i).ρ h⁻¹ := by
    rw [mul_inv_rev, MonoidHom.map_mul, hk, one_mul]
  have hrr : (finHom (Vc D i)).rangeRestrict (h * κ) = (finHom (Vc D i)).rangeRestrict h * (q : Bridge.Gf (Vc D i)) := map_mul _ _ _
  show (R.cV i).ρ h⁻¹ ((R.HV i t).e (R.jV i t ((A.fam.L i t).r g u)) ((finHom (Vc D i)).rangeRestrict h)) =
      (levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) κ)⁻¹ •
        (R.cV i).ρ (h * κ)⁻¹ ((R.HV i t).e (R.jV i t u) ((finHom (Vc D i)).rangeRestrict (h * κ)))
  have hch : levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) κ =
      (((levEnv (Vc D i) (R.βV i) (R.datVt i t)).ch q : ℂˣ) : ℂ) :=
    congrArg Units.val ((congrArg (levFn (R.βV i) (flagL (R.datVt i t))) (finE_eq (Vc D i) κ)).trans
      (GlobalTheory.LiftEquivariance.ch_eq q).symm)
  refine (congrArg ((R.cV i).ρ h⁻¹) e).trans ?_
  refine (LinearMap.map_smul _ _ _).trans ?_
  exact congrArg₂ (fun (a : ℂ) w => a • w) ((Units.val_inv_eq_inv_val _).trans (congrArg (·⁻¹) hch.symm))
    (congrArg₂ (fun (f : Module.End ℂ (R.cV i).W) w => f w) hρ.symm (congrArg ((R.HV i t).e (R.jV i t u)) hrr.symm))
end Act

section Read
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A3.A Ks} {F : Face D A3.A} {X0 : BaseLevelRowSide D}

theorem liftForm_lvlOp (hOk : A3.A.fam.Ok 1) (i : Fin D.R.m) (t : T) (a : MonoidAlgebra D.what₂.LL G) (ha : ∀ b, b * a = a * b)
    (x : Fin (lDim D A3.A F.P0 F.ψ0 i t) → D.what₂.LL) :
    liftForm A3.A F.P0 F.ψ0 i t (((A3.A.fam.L i t).S.lvlOp (A3.A.fam.L i t).r (A3.A.fam.lvlA F.P0 F.ψ0).P
          (A3.A.fam.lvlA F.P0 F.ψ0).ψ a).mulVec x) =
      ∑ g, a.coeff g • (A3.A.fam.L i t).r g (liftForm A3.A F.P0 F.ψ0 i t x) :=
  GlobalTheory.ClassSumIdentity.lvlE_lvlOp hOk.conj (A3.A.fam.L i t).S ((hOk.lifts i t).hpos _) (A3.A.fam.L i t).r (hOk.lifts i t).act
    _ _ a ha x

theorem read_rat (hB : R.BaseW F) (hOk : A3.A.fam.Ok 1) (Y : R3.Read (A3 := A3) R F X0) (cG : G0 R.Pg D.R.r ≃* G0g D.nd)
    (hC : CenRead Y cG) (i : Fin D.R.m) (t : T) (ht : Used0 D (Y.tup t)) (κ : G → GA D (Vc D i))
    (hκ : ∀ g, IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) (R.eG g) (κ g))
    (z : Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd))) (a : MonoidAlgebra D.what₂.LL G) (ha : ∀ b, b * a = a * b)
    (hza : ∀ g, D.what₂.embLL (a.coeff g) = (z : MonoidAlgebra ℂ (G0g D.nd)).coeff ((R.eG.trans cG) g))
    (x : Fin (lDim D A3.A F.P0 F.ψ0 i t) → D.what₂.LL) (h : GA D (Vc D i)) :
    (Y.IL.jMt (Y.tup t) ht i (D.ntypes.cenMt (Y.tup t) ((i : ℕ) + 1) z
        (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t x)))).1 h =
      ∑ g : G, ((z : MonoidAlgebra ℂ (G0g D.nd)).coeff ((R.eG.trans cG) g) *
        (levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) (κ g))⁻¹) •
        (Y.IL.jMt (Y.tup t) ht i (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t x))).1 (h * κ g) := by
  have e1 := congrArg (fun y => (Y.IL.jMt (Y.tup t) ht i y).1 h) (hC i t z a hza x)
  refine e1.trans ?_
  refine (congrFun (Y.mtRead i t ht _) h).trans ?_
  refine Eq.trans ?_ (Finset.sum_congr rfl fun g _ =>
    congrArg (fun w => ((z : MonoidAlgebra ℂ (G0g D.nd)).coeff ((R.eG.trans cG) g) *
        (levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) (κ g))⁻¹) • w) (congrFun (Y.mtRead i t ht x) (h * κ g)).symm)
  have e2 := liftForm_lvlOp (F := F) hOk i t a ha x
  refine (congrArg (fun v => R.extV i t (R.jV i t v) h) e2).trans ?_
  have e3 := map_sum (R.jV i t) (fun g => a.coeff g • (A3.A.fam.L i t).r g (liftForm A3.A F.P0 F.ψ0 i t x)) Finset.univ
  have e4 := map_sum (R.extV i t) (fun g => (R.jV i t) (a.coeff g • (A3.A.fam.L i t).r g (liftForm A3.A F.P0 F.ψ0 i t x))) Finset.univ
  refine (congrArg (fun f => f h) ((congrArg (R.extV i t) e3).trans e4)).trans ?_
  refine (Finset.sum_apply h _ _).trans ?_
  refine Finset.sum_congr rfl fun g _ => ?_
  have e5 := map_smulₛₗ (R.jV i t) (a.coeff g) ((A3.A.fam.L i t).r g (liftForm A3.A F.P0 F.ψ0 i t x))
  have e6 := LinearMap.map_smul (R.extV i t) (D.what₂.embLL (a.coeff g)) (R.jV i t ((A3.A.fam.L i t).r g (liftForm A3.A F.P0 F.ψ0 i t x)))
  refine (congrArg (fun f => f h) ((congrArg (R.extV i t) e5).trans e6)).trans ?_
  refine (Pi.smul_apply (D.what₂.embLL (a.coeff g)) (R.extV i t (R.jV i t ((A3.A.fam.L i t).r g (liftForm A3.A F.P0 F.ψ0 i t x)))) h).trans ?_
  have e7 := extV_act hB.grp.red_L hB.models.jV hB.models.cV i t g (κ g) (hκ g) (liftForm A3.A F.P0 F.ψ0 i t x) h
  refine (congrArg (fun w => D.what₂.embLL (a.coeff g) • w) e7).trans ?_
  refine (smul_smul _ _ _).trans ?_
  exact congrArg (fun c : ℂ => (c * (levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) (κ g))⁻¹) •
    R.extV i t (R.jV i t (liftForm A3.A F.P0 F.ψ0 i t x)) (h * κ g)) (hza g)

end Read

theorem sum_reindex {G H W : Type} [Group G] [Fintype G] [Group H] [Fintype H] [AddCommGroup W] [Module ℂ W] (e : G ≃* H)
    (c : H → ℂ) (ch : G → ℂ) (w : G → W) :
    ∑ g, (c (e g) * ch g) • w g = ∑ g₀, c g₀ • (ch (e.symm g₀) • w (e.symm g₀)) :=
  Fintype.sum_equiv e.toEquiv _ _ fun g => by simp [smul_smul]

theorem main : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A3.A Ks) (F : Face D A3.A) (X0 : BaseLevelRowSide D) (Y : R3.Read (A3 := A3) R F X0) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), R.BaseW F → A3.A.fam.Ok 1 → CenRead Y cG → ∀ (i : Fin D.R.m) (t : T) (ht : Used0 D (Y.tup t)) (κ : G → GA D (Vc D i)), (∀ g, IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) (R.eG g) (κ g)) → ∀ (z : Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd))) (y : D.what₂.Mt (Y.tup t) ((i : ℕ) + 1)) (h : GA D (Vc D i)), (Y.IL.jMt (Y.tup t) ht i (D.ntypes.cenMt (Y.tup t) ((i : ℕ) + 1) z y)).1 h = ∑ g : G, ((z : MonoidAlgebra ℂ (G0g D.nd)).coeff ((R.eG.trans cG) g) * (levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) (κ g))⁻¹) • (Y.IL.jMt (Y.tup t) ht i y).1 (h * κ g) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F X0 Y cG hB hOk hC i t ht κ hκ z y h
  letI : Fintype (G0g D.nd) := Fintype.ofEquiv G (R.eG.trans cG).toEquiv
  let ad : GA D (Vc D i) → D.what₂.Mt (Y.tup t) ((i : ℕ) + 1) →ₗ[ℂ] (R.cV i).W := fun h' =>
    { toFun := fun y' => (Y.IL.jMt (Y.tup t) ht i y').1 h'
      map_add' := fun y₁ y₂ => by rw [map_add (f := _)]; rfl
      map_smul' := fun c y₁ => by rw [map_smul]; rfl }
  let ch : G → ℂ := fun g => (levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) (κ g))⁻¹
  have key : ∀ (g₁ : G0g D.nd) (y' : D.what₂.Mt (Y.tup t) ((i : ℕ) + 1)),
      ad h (D.ntypes.cenMt (Y.tup t) ((i : ℕ) + 1) ⟨GlobalTheory.CenLocAt.avgC g₁, GlobalTheory.CenLocAt.avgC_mem g₁⟩ y') =
        ∑ g : G, ((GlobalTheory.CenLocAt.avgC g₁).coeff ((R.eG.trans cG) g) * ch g) • ad (h * κ g) y' := by
    intro g₁
    have tie : ∀ g, D.what₂.embLL ((GlobalTheory.CenLocAt.avgK D.what₂.LL ((R.eG.trans cG).symm g₁)).coeff g) =
        (GlobalTheory.CenLocAt.avgC g₁).coeff ((R.eG.trans cG) g) := fun g => by
      rw [GlobalTheory.CenLocAt.avgK_coeff D.what₂.embLL (R.eG.trans cG), MulEquiv.apply_symm_apply]
    let F1 : D.what₂.Mt (Y.tup t) ((i : ℕ) + 1) →ₗ[ℂ] (R.cV i).W :=
      (ad h).comp (D.ntypes.cenMt (Y.tup t) ((i : ℕ) + 1) ⟨GlobalTheory.CenLocAt.avgC g₁, GlobalTheory.CenLocAt.avgC_mem g₁⟩)
    let F2 : D.what₂.Mt (Y.tup t) ((i : ℕ) + 1) →ₗ[ℂ] (R.cV i).W :=
      ∑ g : G, ((GlobalTheory.CenLocAt.avgC g₁).coeff ((R.eG.trans cG) g) * ch g) • ad (h * κ g)
    have hb := (D.what₂.jMt_basis (Y.tup t) ((i : ℕ) + 1)
      (Module.Free.chooseBasis D.what₂.LL (D.what₂.MtL (Y.tup t) ((i : ℕ) + 1)))).2
    have hF : F1 = F2 := by
      refine LinearMap.ext_on_range hb (fun b => ?_)
      obtain ⟨x', hx'⟩ := (Y.eMt i t).surjective (Module.Free.chooseBasis D.what₂.LL (D.what₂.MtL (Y.tup t) ((i : ℕ) + 1)) b)
      rw [← hx']
      refine (read_rat hB hOk Y cG hC i t ht κ hκ ⟨_, GlobalTheory.CenLocAt.avgC_mem g₁⟩ _ (GlobalTheory.CenLocAt.avgK_comm _ _) tie x' h).trans ?_
      simp only [F2, LinearMap.sum_apply, LinearMap.smul_apply]
      rfl
    intro y'
    have := LinearMap.congr_fun hF y'
    simpa only [F1, F2, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply] using this
  let Φ : ↥(Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd))) →ₗ[ℂ] (R.cV i).W :=
    { toFun := fun z' => ad h (D.ntypes.cenMt (Y.tup t) ((i : ℕ) + 1) z' y)
      map_add' := fun z₁ z₂ => by simp only [map_add (f := _), LinearMap.add_apply]
      map_smul' := fun c z₁ => by simp only [map_smul, LinearMap.smul_apply, RingHom.id_apply] }
  have hl := GlobalTheory.CenLocAt.lin_center Φ (fun g₀ => ch ((R.eG.trans cG).symm g₀) • ad (h * κ ((R.eG.trans cG).symm g₀)) y)
    (fun g₁ => (key g₁ y).trans (sum_reindex _ _ _ _)) z
  exact hl.trans (sum_reindex (R.eG.trans cG) _ ch (fun g => ad (h * κ g) y)).symm

end GlobalTheory.CenTranslate
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCommonCoefficientMapLiftPresentation
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCommonCoefficientMapLiftPresentation
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.Mem.R3.LiftPresStd

theorem vv_cast_equiv : ∀ {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] [StarRing K] {ι : Type} [Fintype ι]
    (emb : ι → E →+* K) {n n' : ℕ} (h : n = n') (lam : ι → DomWeight n) (lam' : ι → DomWeight n'),
    (∀ τ a, (lam τ).w a = (lam' τ).w (Fin.cast h a)) →
    ∃ e : VV K lam ≃ₗ[K] VV K lam',
      (∀ (g : GL (Fin n') E) v, e (rhoVr emb lam (LiftBrg.castGL h.symm g) v) = rhoVr emb lam' g (e v)) ∧
      (∀ (J : Matrix (Fin n) (Fin n) E) x y,
        pairVr emb lam' (J.reindex (finCongr h) (finCongr h)) (e x) (e y) = pairVr emb lam J x y) ∧
      (∀ N : Submodule (𝓞 E) (Fin n → E), (nabAtr emb lam N).map (e.toLinearMap.restrictScalars (𝓞 K)) =
        nabAtr emb lam' (N.map (LinearEquiv.funCongrLeft (𝓞 E) E (finCongr h).symm).toLinearMap)) ∧
      (∀ N : Submodule (𝓞 E) (Fin n → E), (delAtr emb lam N).map (e.toLinearMap.restrictScalars (𝓞 K)) =
        delAtr emb lam' (N.map (LinearEquiv.funCongrLeft (𝓞 E) E (finCongr h).symm).toLinearMap)) ∧
      (∀ i j, (bVV K lam').repr (e (bVV K lam i)) j ∈ Formalism.DivisionValues.cmMax K) ∧
      (∀ (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] (σ : K →+* ℂ) (c0 : VV K lam' →ₛₗ[σ] W),
        LinearIndependent ℂ (fun i => c0 (bVV K lam' i)) → Submodule.span ℂ (Set.range fun i => c0 (bVV K lam' i)) = ⊤ →
        LinearIndependent ℂ (fun i => c0 (e (bVV K lam i))) ∧ Submodule.span ℂ (Set.range fun i => c0 (e (bVV K lam i))) = ⊤) := by
  intro E K _ _ _ _ _ ι _ emb n n' h lam lam' hl
  subst h
  have hlam : lam = lam' := by
    funext τ
    have h1 := hl τ
    rcases hw : lam τ with ⟨w, hw1⟩
    rcases hw' : lam' τ with ⟨w', hw1'⟩
    rw [hw, hw'] at h1
    have : w = w' := funext fun a => by simpa using h1 a
    subst this
    rfl
  subst hlam
  have hN : ∀ N : Submodule (𝓞 E) (Fin n → E),
      N.map (LinearEquiv.funCongrLeft (𝓞 E) E (finCongr (rfl : n = n)).symm).toLinearMap = N := by
    intro N
    ext x
    simp only [Submodule.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      convert hy using 1
      funext a
      rfl
    · intro hx
      exact ⟨x, hx, rfl⟩
  refine ⟨LinearEquiv.refl K _, fun g v => ?_, fun J x y => ?_, fun N => ?_, fun N => ?_, fun i j => ?_, fun W _ _ σ c0 h1 h2 => ⟨h1, h2⟩⟩
  · have : LiftBrg.castGL (rfl : n = n).symm g = g := by ext a b; simp [LiftBrg.castGL]
    rw [this]; rfl
  · have : J.reindex (finCongr (rfl : n = n)) (finCongr (rfl : n = n)) = J := by ext a b; simp
    rw [this]; rfl
  · rw [hN]; exact Submodule.map_id _
  · rw [hN]; exact Submodule.map_id _
  · show (bVV K lam).repr (bVV K lam i) j ∈ Formalism.DivisionValues.cmMax K
    rw [Module.Basis.repr_self, Finsupp.single_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _

theorem ufGL_ratHom : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) (γ : Formalism.L2.Col.URat hc n),
    Formalism.L2.Col.ufGL E n (Formalism.L2.Col.ratHom hc n γ) = (γ : GL (Fin n) E) := by
  intro F E _ _ _ _ _ _ hc n γ
  apply Units.ext
  ext a b
  simp [Formalism.L2.Col.ufGL, Formalism.L2.Col.toGLm, Formalism.L2.Col.ratHom, Formalism.UG.glEquiv, Matrix.GeneralLinearGroup.toLin, LinearMap.GeneralLinearGroup.generalLinearEquiv]

theorem formRho_colGl {X : Formalism.L2.Col.Fields} {n : ℕ} [NeZero n] {SG : Finset (HeightOneSpectrum (𝓞 X.E))} (hc : Formalism.BasicNotions.CMData X.F X.E)
    (C : Formalism.L2.Col.CoefPk X n (Formalism.L2.Col.DecoSet (E := X.E) (n := n) (ST := ∅) (SG := SG))) (Λ : Formalism.L2.Col.LevFam X.E X.K n SG)
    (γ : Formalism.L2.Col.URat hc n) (k : Bridge.colJ hc n ∅ SG Λ.grp) (v : C.V) :
    (Formalism.L2.Col.formGSD C Λ).ρ (Bridge.colGl (Formalism.L2.Col.rf_onDeco C Λ) (γ, k)) v =
      ((Λ.chr (Formalism.L2.Col.redH hc n ∅ SG Λ.grp ((Bridge.colJEquiv hc n ∅ SG Λ.grp).symm k)) : X.Kˣ) : X.K) •
        C.rho (Formalism.L2.Col.ratHom hc n γ) v := rfl

theorem castGL_symm_castGL {R : Type} [CommRing R] {m n : ℕ} (h : m = n) (g : GL (Fin m) R) :
    LiftBrg.castGL h.symm (LiftBrg.castGL h g) = g := by
  subst h
  ext a b
  simp [LiftBrg.castGL]

theorem exists_oneCoef_presStd : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG → ∀ (cV : ∀ i, CoefA (Vc X.toD7 i)) (i : Fin X.toD7.R.m)
    (c0L : VV X.toD7.what₂.LL (fun τ => Bridge.lamLdef (Vc X.toD7 i).rank ((i : ℕ) + 1) τ) →ₛₗ[X.toD7.what₂.embLL] (cV i).W),
    (cV i).Is → Bridge.CoefMapTie (Vc X.toD7 i) (cV i).coef c0L (rhoVr (labLL X.toD7) _) →
    (∀ x y, inner ℂ (c0L x) (c0L y) = X.toD7.what₂.embLL (pairVr (labLL X.toD7) _
      (if X.toD7.sp.Vneg ((i : ℕ) + 1) then -(Vc X.toD7 i).gram else (Vc X.toD7 i).gram) x y)) →
    L.βV i = 1 → (Vc X.toD7 i).gram = 1 →
    ∃ c : VV X.B.fields.K (X.B.wts.lamV ((i : ℕ) + 1)) →ₛₗ[X.B.embLL] (cV i).W, (∀ (γ : GQ (Vc X.toD7 i)) (γE : GL (Fin (Vc X.toD7 i).rank) X.toD7.host.E), Bridge.IsRatMat (Vc X.toD7 i) γ γE →
      ∀ v, c (rhoVr X.B.fields.emb (X.B.wts.lamV ((i : ℕ) + 1)) (LiftBrg.castGL (LiftBrg.rkEq X i).symm γE) v) = (cV i).coef.ρ γ (c v)) ∧
      ∀ t : TupU I U, ∃ P : LiftBrg.PresL X I hX U Xg tr L cV i t, LiftBrg.ReadsStd X I hX U Xg tr L cV i t 1 1 P ∧
        (∀ v, P.coef v = c v) ∧ Bridge.CoefTie (X.toD7.sp.V ((i : ℕ) + 1)) (cV i).coef P (fun τ => Bridge.lamLdef (Vc X.toD7 i).rank ((i : ℕ) + 1) τ) c0L
        (pairVr (labLL X.toD7) _
          (if X.toD7.sp.Vneg ((i : ℕ) + 1) then -(X.toD7.sp.V ((i : ℕ) + 1)).gram else (X.toD7.sp.V ((i : ℕ) + 1)).gram))
        (nabAtr (labLL X.toD7) _) (delAtr (labLL X.toD7) _) := by
  intro X px I hX U Xg tr L eG0 hI hV hL hG cV i c0L hcV hmap hin hβ hgram
  obtain ⟨e0, he_rho, he_pair, he_nab, he_del, he_rat, he_li⟩ :=
    vv_cast_equiv X.B.fields.emb (LiftBrg.rkEq X i) (X.B.wts.lamV ((i : ℕ) + 1))
      (fun τ => Bridge.lamLdef (D := X.toD7) (Vc X.toD7 i).rank ((i : ℕ) + 1) τ) (GlobalTheory.T.baseWeight_eq_forcedLiftWeight X i)
  let c : VV X.B.fields.K (X.B.wts.lamV ((i : ℕ) + 1)) →ₛₗ[X.B.embLL] (cV i).W :=
    { toFun := fun v => c0L (e0 v)
      map_add' := fun v w => by show c0L (e0 (v + w)) = c0L (e0 v) + c0L (e0 w); rw [map_add (f := _)]; exact c0L.map_add _ _
      map_smul' := fun a v => by show c0L (e0 (a • v)) = _; rw [LinearEquiv.map_smul]; exact c0L.map_smulₛₗ a (e0 v) }
  have hc : ∀ v, c v = c0L (e0 v) := fun v => rfl
  have hint : ∀ (γ : GQ (Vc X.toD7 i)) (γE : GL (Fin (Vc X.toD7 i).rank) X.toD7.host.E), Bridge.IsRatMat (Vc X.toD7 i) γ γE →
      ∀ v, c (rhoVr X.B.fields.emb (X.B.wts.lamV ((i : ℕ) + 1)) (LiftBrg.castGL (LiftBrg.rkEq X i).symm γE) v) = (cV i).coef.ρ γ (c v) := by
    intro γ γE h v
    exact (congrArg c0L (he_rho γE v)).trans (hmap.1 γ γE h (e0 v))
  refine ⟨c, hint, fun t => ?_⟩
  obtain ⟨eG, eΓ, hchar, hι, hrat⟩ := GlobalTheory.T.exists_unitaryGroups_equiv_unitForm_gram_one X i hgram
  obtain ⟨hJ, hχ⟩ := GlobalTheory.T.liftAdelicForm_level_type_eq_columnLevel X px I U L hI hV hL i t eG hchar

  letI : Algebra X.toD7.host.F X.B.fields.E := inferInstanceAs (Algebra X.toD7.host.F X.toD7.host.E)
  have hneg : X.toD7.sp.Vneg ((i : ℕ) + 1) = false := X.B.V_pos _ (by omega) i.2
  have hgr : (if X.toD7.sp.Vneg ((i : ℕ) + 1) then -(Vc X.toD7 i).gram else (Vc X.toD7 i).gram) =
      (1 : Matrix (Fin X.B.R.nV) (Fin X.B.R.nV) X.toD7.host.E).reindex (finCongr (LiftBrg.rkEq X i)) (finCongr (LiftBrg.rkEq X i)) := by
    rw [hneg, if_neg (by simp), hgram]
    ext a b
    simp [Matrix.one_apply]
  have hSG : Formalism.L2.Col.DecoPtSurj X.toD7.sp.cm X.B.R.nV ∅ (LiftBrg.sgL X I U t) :=
    Formalism.L2.Col.decoPtSurj_of _ _ _ _ (Formalism.L2.Col.unimodGenus_holds _ _) Formalism.L2.DIV.reduction_surjective_bis
      (by classical convert GlobalTheory.T.rowFormLevelPrimes_isSplitSet X px I U L hI hL t using 1; exact Finset.empty_union _) (Finset.disjoint_empty_left _)
  let o := Formalism.L2.Col.rf_onDeco (X := X.B.fields) (n := X.B.R.nV) (ST := ∅) (SG := LiftBrg.sgL X I U t)
    (Formalism.L2.Col.mtVal (Pr := X.B.primes px) X.B.wts ((i : ℕ) + 1) _) (Formalism.L2.Col.mtTyKK I.Ch I.sel t.1 ((i : ℕ) + 1)).inv
  have hmem : ∀ k : Bridge.colJ X.toD7.sp.cm X.B.R.nV ∅ (LiftBrg.sgL X I U t) (Formalism.L2.Col.mtTyKK I.Ch I.sel t.1 ((i : ℕ) + 1)).inv.grp,
      (eG.toMonoidHom.comp (Subgroup.subtype _)) k ∈ (levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).J := fun k => by
    rw [hJ]; exact Subgroup.mem_map_of_mem _ k.2
  let χc := (levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).χ.comp ((eG.toMonoidHom.comp (Subgroup.subtype _)).codRestrict _ hmem)
  have hχc : ∀ k, ((χc k)⁻¹ : ℂˣ) = Units.map X.toD7.what₂.embLL.toMonoidHom ((Formalism.L2.Col.mtTyKK I.Ch I.sel t.1 ((i : ℕ) + 1)).inv.chr
      (Formalism.L2.Col.redH X.toD7.sp.cm X.B.R.nV ∅ (LiftBrg.sgL X I U t) _
        ((Bridge.colJEquiv X.toD7.sp.cm X.B.R.nV ∅ (LiftBrg.sgL X I U t) _).symm k))) := fun k => (hχ k (hmem k)).1
  have hK1 : ∀ k : Bridge.colJ X.toD7.sp.cm X.B.R.nV ∅ (LiftBrg.sgL X I U t) (Formalism.L2.Col.mtTyKK I.Ch I.sel t.1 ((i : ℕ) + 1)).inv.grp,
      (k : Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV) ∈ Bridge.principalCongruenceSubgroup X.toD7.sp.cm X.B.R.nV ∅ (LiftBrg.sgL X I U t) → χc k = 1 :=
    fun k hk => (hχ k (hmem k)).2 hk
  have hli := he_li (cV i).W X.toD7.what₂.embLL c0L hmap.2.1 hmap.2.2
  have hpair : ∀ x x', inner ℂ (c x) (c x') = X.toD7.what₂.embLL ((Formalism.L2.Col.mtKGSD X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).pair x x') := by
    intro x x'
    refine (hin (e0 x) (e0 x')).trans ?_
    congr 1
    rw [hgr]
    exact he_pair 1 x x'
  have hgl : ∀ (γ : Formalism.L2.Col.URat X.toD7.sp.cm X.B.R.nV) k (v : (Formalism.L2.Col.mtKGSD X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).V),
      c ((Formalism.L2.Col.mtKGSD X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).ρ (Bridge.colGl o (γ, k)) v) =
        ((χc k)⁻¹ : ℂˣ) • ((cV i).coef.ρ.comp eΓ.toMonoidHom) γ (c v) := by
    intro γ k v
    rw [show (Formalism.L2.Col.mtKGSD X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).ρ (Bridge.colGl o (γ, k)) v = _ from
      formRho_colGl (X := X.B.fields) X.toD7.sp.cm _ _ γ k v]
    refine (c.map_smulₛₗ _ _).trans ?_
    have e3 : (Formalism.L2.Col.mtVal (Pr := X.B.primes px) X.B.wts ((i : ℕ) + 1) (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1)).rho
        (Formalism.L2.Col.ratHom X.toD7.sp.cm X.B.R.nV γ) v =
        rhoVr X.B.fields.emb (X.B.wts.lamV ((i : ℕ) + 1))
          (LiftBrg.castGL (LiftBrg.rkEq X i).symm (LiftBrg.castGL (LiftBrg.rkEq X i) (γ : GL (Fin X.B.R.nV) X.toD7.host.E))) v := by
      show rhoVr X.B.fields.emb (X.B.wts.lamV ((i : ℕ) + 1))
        (Formalism.L2.Col.ufGL X.toD7.host.E X.B.R.nV (Formalism.L2.Col.ratHom X.toD7.sp.cm X.B.R.nV γ)) v = _
      rw [ufGL_ratHom]
      exact congrArg (fun g => rhoVr X.B.fields.emb (X.B.wts.lamV ((i : ℕ) + 1)) g v) (castGL_symm_castGL (LiftBrg.rkEq X i) _).symm
    have e2 := hint (eΓ γ) _ (hrat γ) v
    have e4 := (congrArg c e3).trans e2
    rw [hχc k, Units.smul_def]
    erw [e4]
    rfl

  let A := Bridge.colAdPts o hSG
  let P0 := Bridge.colClassPres (hc := X.toD7.sp.cm) o hSG (Formalism.L2.Col.mtKOk X.B.wts I.Ch I.sel t.1 hX ((i : ℕ) + 1)) X.toD7.what₂.embLL
    ((cV i).coef.ρ.comp eΓ.toMonoidHom) χc c hli.1 hli.2 hpair hK1 hgl
  let P : LiftBrg.PresL X I hX U Xg tr L cV i t :=
    P0.transport eG eΓ hι (fun _ => rfl) hJ (fun k hk => rfl)
  refine ⟨P, ?_, fun v => rfl, e0, he_rat, fun x => rfl, ?_, ?_, ?_⟩

  · intro f g
    have h5 := GlobalTheory.T.transportedClassSetPresentation_reads_equivariant (ι' := Bridge.ratF (Vc X.toD7 i)) (ρ' := (cV i).coef.ρ) (J' := (levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).J)
      (χ' := (levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).χ) A (Formalism.L2.Col.mtKOk X.B.wts I.Ch I.sel t.1 hX ((i : ℕ) + 1)) X.toD7.what₂.embLL
      ((cV i).coef.ρ.comp eΓ.toMonoidHom) χc c hli.1 hli.2 hpair hK1 hgl eG eΓ hι (fun _ => rfl) hJ (fun k hk => rfl) f g
    refine h5.trans ?_
    have hq : A.q (eG.symm g) = LiftBrg.ptL X I U i t 1 1 g := by
      show Formalism.L2.Col.decoPt X.toD7.sp.cm X.B.R.nV ∅ (LiftBrg.sgL X I U t) (QuotientGroup.mk (eG.symm g)) = _
      rw [Formalism.L2.Col.decoPt_mk]
      unfold LiftBrg.ptL
      congr 1
      have := hchar (eG.symm g)
      rw [MulEquiv.apply_symm_apply] at this
      rw [this]
      simp
    erw [hq]
    rfl
  · intro x x'
    rw [hgr]
    exact he_pair 1 x x'
  · intro cl
    have h6 := GlobalTheory.T.translatedStdLattice_eq_decoratedLattice_reindexed X i (L.ΛV i) (by rw [← hβ]; exact hL.is.βV i) (LiftBrg.sgL X I U t) eG hchar (A.y cl)
    have hy := A.q_y cl
    have hy' : Formalism.L2.Col.decoPt X.toD7.sp.cm X.B.R.nV ∅ (LiftBrg.sgL X I U t) (QuotientGroup.mk (A.y cl)) =
        (Formalism.L2.Col.mtKGSD X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).outSec.rep cl := hy
    refine Eq.trans ?_ (congrArg (nabAtr (labLL X.toD7) (fun τ => Bridge.lamLdef (D := X.toD7) (Vc X.toD7 i).rank ((i : ℕ) + 1) τ)) h6).symm
    rw [hy']
    exact he_nab _
  · intro cl
    have h6 := GlobalTheory.T.translatedStdLattice_eq_decoratedLattice_reindexed X i (L.ΛV i) (by rw [← hβ]; exact hL.is.βV i) (LiftBrg.sgL X I U t) eG hchar (A.y cl)
    have hy := A.q_y cl
    have hy' : Formalism.L2.Col.decoPt X.toD7.sp.cm X.B.R.nV ∅ (LiftBrg.sgL X I U t) (QuotientGroup.mk (A.y cl)) =
        (Formalism.L2.Col.mtKGSD X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).outSec.rep cl := hy
    refine Eq.trans ?_ (congrArg (delAtr (labLL X.toD7) (fun τ => Bridge.lamLdef (D := X.toD7) (Vc X.toD7 i).rank ((i : ℕ) + 1) τ)) h6).symm
    rw [hy']
    exact he_del _

end GlobalTheory.Mem.R3.LiftPresStd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCommonCoefficientMapLiftPresentationStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_common_coefficientMap_liftPresentation : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG → ∀ (cV : ∀ i, CoefA (Vc X.toD7 i)) (i : Fin X.toD7.R.m)
    (c0L : VV X.toD7.what₂.LL (fun τ => Bridge.lamLdef (Vc X.toD7 i).rank ((i : ℕ) + 1) τ) →ₛₗ[X.toD7.what₂.embLL] (cV i).W),
    (cV i).Is → Bridge.CoefMapTie (Vc X.toD7 i) (cV i).coef c0L (rhoVr (labLL X.toD7) _) →
    (∀ x y, inner ℂ (c0L x) (c0L y) = X.toD7.what₂.embLL (pairVr (labLL X.toD7) _
      (if X.toD7.sp.Vneg ((i : ℕ) + 1) then -(Vc X.toD7 i).gram else (Vc X.toD7 i).gram) x y)) →
    L.βV i = 1 → (Vc X.toD7 i).gram = 1 →
    ∃ c : VV X.B.fields.K (X.B.wts.lamV ((i : ℕ) + 1)) →ₛₗ[X.B.embLL] (cV i).W, (∀ (γ : GQ (Vc X.toD7 i)) (γE : GL (Fin (Vc X.toD7 i).rank) X.toD7.host.E), Bridge.IsRatMat (Vc X.toD7 i) γ γE →
      ∀ v, c (rhoVr X.B.fields.emb (X.B.wts.lamV ((i : ℕ) + 1)) (LiftBrg.castGL (LiftBrg.rkEq X i).symm γE) v) = (cV i).coef.ρ γ (c v)) ∧
      ∀ t : TupU I U, ∃ P : LiftBrg.PresL X I hX U Xg tr L cV i t, LiftBrg.ReadsStd X I hX U Xg tr L cV i t 1 1 P ∧
        (∀ v, P.coef v = c v) ∧ Bridge.CoefTie (X.toD7.sp.V ((i : ℕ) + 1)) (cV i).coef P (fun τ => Bridge.lamLdef (Vc X.toD7 i).rank ((i : ℕ) + 1) τ) c0L
        (pairVr (labLL X.toD7) _
          (if X.toD7.sp.Vneg ((i : ℕ) + 1) then -(X.toD7.sp.V ((i : ℕ) + 1)).gram else (X.toD7.sp.V ((i : ℕ) + 1)).gram))
        (nabAtr (labLL X.toD7) _) (delAtr (labLL X.toD7) _) := by
  first | exact @GlobalTheory.Mem.R3.LiftPresStd.exists_oneCoef_presStd | exact GlobalTheory.Mem.R3.LiftPresStd.exists_oneCoef_presStd | (intros; apply GlobalTheory.Mem.R3.LiftPresStd.exists_oneCoef_presStd <;> assumption)
end
end
