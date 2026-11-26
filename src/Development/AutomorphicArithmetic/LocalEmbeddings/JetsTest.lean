module

public import Development.AutomorphicArithmetic.LocalEmbeddings.JetsGlue
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AuxiliaryVectorDecompositionEqZero

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRealModelSq
section -- merged from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RealDataStabilizer
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult
  MeasureTheory Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IndefiniteRowSideFullHecke.BasisPolynomialParabolics

variable {D : D7}

abbrev Bas (V : HSp D) : Type := D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ

abbrev Pol (S T : HSp D) : Type := MvPolynomial (FVar D T.rank S.rank) ℂ

abbrev cmp (θ : InfFam D) (V : HSp D) (τ : D.what₂.Tau) (g : GA D V) : Matrix (Fin V.rank) (Fin V.rank) ℂ :=
  infMat D.sp.cm.sig V.gram (θ τ) g

def StrictInterlace (n : ℕ) (A B : Finset ℚ) : Prop :=
  ∃ (a : Fin (n + 1) → ℚ) (b : Fin n → ℚ), A = Finset.univ.image a ∧ B = Finset.univ.image b ∧
    ∀ i : Fin n, b i < a i.castSucc ∧ a i.succ < b i

section Pair

variable (θ : InfFam D) {S T : HSp D} (BS : Bas S) (BT : Bas T) (e : D.what₂.Tau → ℚ)

def vacChar (g : GA D S) (h : GA D T) : ℂ :=
  ∏ τ, (cmp θ S τ g).det ^ ⌊e τ - (T.rank : ℚ) / 2⌋ * (cmp θ T τ h).det ^ (-⌊e τ - (S.rank : ℚ) / 2⌋)

def subst (g : GA D S) (h : GA D T) (x : FVar D T.rank S.rank) : Pol S T :=
  ∑ i, ∑ c, MvPolynomial.C (((BT x.1)⁻¹ * cmp θ T x.1 h * BT x.1) i x.2.1 * ((BS x.1)⁻¹ * cmp θ S x.1 g⁻¹ * BS x.1) x.2.2 c) *
    MvPolynomial.X (x.1, i, c)

def polAct (g : GA D S) (h : GA D T) : Pol S T →ₗ[ℂ] Pol S T :=
  vacChar θ e g h • (MvPolynomial.aeval (subst θ BS BT g h)).toLinearMap

variable (π : CoefA S) (π' : CoefA T)

end Pair

def fp (V : HSp D) (g : GA D V) : GfC V := ⟨GlobalTheory.LevelNbhd.finPartG V g, GlobalTheory.LevelNbhd.finPartG_mem_GfC V g⟩

section Global

variable (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) {S T : HSp D} (BS : Bas S) (BT : Bas T)

variable {π : CoefA S} {π' : CoefA T}

end Global

section Last

variable {V A L : HSp D} (o : OrthDec V A L) (π : CoefA V) (δ : CoefA A)

end Last

section Chain

variable (P : TPar D) (θ : InfFam D) (X : ℕ → HSp D) {X' L : HSp D} (o : OrthDec (X D.R.m) X' L) (B : ∀ j, Bas (X j))

variable {X} (π : ∀ j, CoefA (X j))

variable (ψ : AddChar (AF D.host.F) ℂ) (om : ∀ j, Om (X j) (X (j + 1))) (f : ∀ j, WO (X j) (X (j + 1)) → ℂ)

variable (μ : ∀ j, Measure (GA D (X j))) (𝓕 : ∀ j, Set (GA D (X j)))



end Chain

end GlobalTheory.IndefiniteRowSideFullHecke.BasisPolynomialParabolics

end
end

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus posDef_dual)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowClaim.RealTypeOf

section Wt

variable {ι : Type} [Fintype ι] {n : ℕ}

theorem rhoK_congr {lam lam' : ι → DomWeight n} (h : lam = lam') (g : ι → GL (Fin n) ℂ) (x : VV ℂ lam) (y : VV ℂ lam')
    (hxy : (x : Pol ℂ ι n) = y) : ((rhoK lam g x : VV ℂ lam) : Pol ℂ ι n) = rhoK lam' g y := by
  subst h
  rw [Subtype.ext hxy]

end Wt

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc)

def wtTopEquiv : VV ℂ (wt G (.top 0)) ≃ₗ[ℂ] VV ℂ (LaP G) := LinearEquiv.ofEq _ _ (congrArg (VV ℂ) (wt_top_eq G))

def colFun (θ : InfFam D) (ξ : Module.Dual ℂ (coefPlus G θ).W) : Module.Dual ℂ (VV ℂ (wt G (.top 0))) :=
  ξ ∘ₗ (GlobalTheory.CoefModel.toHilb (LaP G) (posDef_dual G)).toLinearMap ∘ₗ (wtTopEquiv G).toLinearMap

theorem arg_eq (θ : InfFam D) (Ψ : GLf G → WtSp G) (h : GA D (G.V (.top 0))) :
    rhoK (LaP G) (invTrK (GlobalTheory.CoefModel.realGL θ (Xp G) h⁻¹))
      (GlobalTheory.CoefModel.mapVV D.what₂.embLL (LaP G) (Ψ (Formalism.IndefR.Lev.finE (Xp G) h))) =
    wtTopEquiv G (rhoK (wt G (.top 0)) (invTrK (GlobalTheory.CoefModel.realGL θ (G.V (.top 0)) h⁻¹))
        (psiC Ψ (GlobalTheory.IndefiniteRowSideFullHecke.BasisPolynomialParabolics.fp (G.V (.top 0)) h))) := by
  refine Subtype.ext ?_
  rw [wtTopEquiv, LinearEquiv.coe_ofEq_apply]
  refine (rhoK_congr (wt_top_eq G) _ _ _ ?_).symm
  show (GlobalTheory.CoefModel.mapVV D.what₂.embLL (LaP G) (Ψ (finG (Xp G) (GlobalTheory.IndefiniteRowSideFullHecke.BasisPolynomialParabolics.fp (G.V (.top 0)) h)))).1 = _
  have e : finG (Xp G) (GlobalTheory.IndefiniteRowSideFullHecke.BasisPolynomialParabolics.fp (G.V (.top 0)) h) = Formalism.IndefR.Lev.finE (Xp G) h :=
    GlobalTheory.SuppLevO.finE_finPartG _ h
  rw [e]

end GlobalTheory.RowClaim.RealTypeOf

namespace GlobalTheory.RowClaim.RealTypeOf

open GlobalTheory.CoefModel

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

theorem colFn_eq (ch : Choice R) (a : Fin ch.n) (g : GA D (ch.G.V (.top 0))) :
    colFn ch a g = colFun ch.G ch.W.θ ch.ξ (rhoK (wt ch.G (.top 0)) (invTrK (realGL ch.W.θ (ch.G.V (.top 0)) g⁻¹))
      (psiC (ch.Psi a) (GlobalTheory.IndefiniteRowSideFullHecke.BasisPolynomialParabolics.fp (ch.G.V (.top 0)) g))) := by
  have h1 : colFn ch a g = scal ch.W.θ (ch.ξ ∘ₗ (toHilb (LaP ch.G) (posDef_dual ch.G)).toLinearMap) (ch.Psi a) g :=
    congr_fun (pairVec_colOf ch.W.θ ch.ξ (ch.Psi a)) g
  rw [h1]
  unfold scal colFun
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [arg_eq]
  rfl

theorem exists_real_model_sq (V : HSp D) (θ : InfFam D) (c : CoefA V) (lam : D.what₂.Tau → DomWeight V.rank)
    (c0 : VV D.what₂.LL lam →ₛₗ[D.what₂.embLL] c.coef.W) (hθ : IsInfFam θ) (hc : c.Is)
    (ht : Bridge.CoefMapTie V c.coef c0 (rhoV (labLL D) lam)) :
    ∃ e : VV ℂ lam ≃ₗ[ℂ] c.W, (∀ v, e (mapVV D.what₂.embLL lam v) = c0 v) ∧
      ∀ u ∈ GinfC V, ∀ v, c.ρ u (e v) = e (rhoK lam (realGL θ V u) v) := by
  obtain ⟨e, he⟩ : ∃ e : VV ℂ lam ≃ₗ[ℂ] c.W, ∀ v, e (mapVV D.what₂.embLL lam v) = c0 v :=
    GlobalTheory.CoefReal.exists_scalarExt D.what₂.embLL lam c0 ht.2.1 ht.2.2
  refine ⟨e, he, fun u hu v => ?_⟩
  haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  have hlab : ∀ τ x, D.what₂.embLL (labLL D τ x) = tauE D τ x := fun τ x =>
    DFunLike.congr_fun (GlobalTheory.ThetaFiresProbe.labE_fixed τ) x
  have hrat : ∀ (γ : GQ V) (v : VV ℂ lam), c.ρ γ.1 (e v) = e (rhoK lam (realGL θ V γ.1) v) := by
    intro γ v
    obtain ⟨γE, hγ⟩ : ∃ γE, Bridge.IsRatMat V γ γE := by
      obtain ⟨γ, ⟨g, -, hg⟩⟩ := γ
      exact ⟨g, hg.symm⟩
    have e1 : (fun τ => Formalism.UG.bc D.what₂.embLL (embGL (labLL D) γE τ)) = realGL θ V γ := by
      funext τ
      apply Units.ext
      rw [bc_coe, realGL_rat hθ V γ γE hγ, embGL_coe, bc_coe]
      ext a b
      exact hlab _ _
    have : (c.ρ γ).comp e.toLinearMap = e.toLinearMap.comp (rhoK lam (realGL θ V γ)) := by
      refine LinearMap.ext_on_range (span_mapVV D.what₂.embLL lam) fun i => ?_
      show c.ρ γ (e _) = e (rhoK lam (realGL θ V γ) _)
      rw [← e1, ← mapVV_rhoK, he, he]
      exact (ht.1 γ γE hγ _).symm
    exact LinearMap.congr_fun this v
  have hfin : ∀ k ∈ GfC V, realGL θ V k = 1 := fun k hk => funext fun τ => by
    show Formalism.UG.bc (θ τ) (infHom V k) = 1
    rw [show infHom V k = 1 from hk, map_one]
  rw [← e.symm_apply_eq]
  refine Subtype.ext (MvPolynomial.ext _ _ fun m => ?_)
  let Lf : c.W →ₗ[ℂ] ℂ := MvPolynomial.lcoeff ℂ m ∘ₗ (VV ℂ lam).subtype ∘ₗ e.symm.toLinearMap
  have hf : Continuous fun h => Lf (c.ρ h (e v)) := Lf.continuous_of_finiteDimensional.comp (hc.2.2.1 _)
  have hg : Continuous fun h => AddMonoidAlgebra.coeff (actP lam (realGL θ V h) v.1) m :=
    GlobalTheory.CoefReal.continuous_coeff_actP lam _ (fun τ => (realGL_laws hθ V).1 τ) _ m
  by_contra hne
  obtain ⟨γ, hγ, k, hk, hU, -⟩ := GlobalTheory.RealApprox.weak_approx_real V u hu _ (isOpen_ne_fun hf hg) hne
  refine hU ?_
  show Lf (c.ρ (γ * k) (e v)) = AddMonoidAlgebra.coeff (actP lam (realGL θ V (γ * k)) v.1) m
  rw [map_mul, map_mul (realGL θ V), hc.1 k hk, hfin k hk, mul_one, mul_one, hrat ⟨γ, hγ⟩ v]
  simp [Lf, rhoK_coe]

end GlobalTheory.RowClaim.RealTypeOf

namespace GlobalTheory.RowClaim.RealTypeOf

open GlobalTheory.CoefModel

def castGL {N n : ℕ} (h : N = n) : GL (Fin N) ℂ →* GL (Fin n) ℂ := h ▸ MonoidHom.id _

theorem rhoK_rename {ι : Type} [Fintype ι] {N n : ℕ} (h : N = n) (lam : ι → DomWeight N) (lam' : ι → DomWeight n)
    (hw : ∀ τ a, (lam' τ).w (Fin.cast h a) = (lam τ).w a) (g : ι → GL (Fin N) ℂ) (x : VV ℂ lam) (y : VV ℂ lam')
    (hxy : y.1 = MvPolynomial.rename (Prod.map id (Prod.map (Fin.cast h) (Fin.cast h))) x.1) :
    (rhoK lam' (fun τ => castGL h (g τ)) y).1 =
      MvPolynomial.rename (Prod.map id (Prod.map (Fin.cast h) (Fin.cast h))) (rhoK lam g x).1 := by
  subst h
  have e : lam' = lam := funext fun τ => by
    have := hw τ
    generalize lam' τ = a at this
    generalize lam τ = b at this
    cases a
    cases b
    congr
    funext i
    exact this i
  subst e
  have hr : (Prod.map id (Prod.map (Fin.cast rfl) (Fin.cast rfl)) : ι × Fin N × Fin N → ι × Fin N × Fin N) = id := by
    funext x
    rfl
  rw [hr, MvPolynomial.rename_id_apply] at hxy ⊢
  rw [Subtype.ext hxy]
  rfl

variable {D : D7}

theorem realGL_cast_inv (θ : InfFam D) {Λ : Submodule (𝓞 D.host.E) (Fin D.sp.X'.rank → D.host.E)} (Y : LSp D)
    (hY : Y = ⟨D.sp.X', Λ⟩) (k : GA D Y.sp) (τ : D.what₂.Tau) :
    realGL θ Y.sp k⁻¹ τ = castGL (congrArg (fun X : LSp D => X.sp.rank) hY).symm
      (realGL θ D.sp.X' (cast (congrArg (fun X : LSp D => GA D X.sp) hY) k)⁻¹ τ) := by
  subst hY
  rfl

theorem finHom_cast_finPart {Λ : Submodule (𝓞 D.host.E) (Fin D.sp.X'.rank → D.host.E)} (Y : LSp D) (hY : Y = ⟨D.sp.X', Λ⟩)
    (k : GA D Y.sp) :
    (finHom D.sp.X').rangeRestrict (cast (congrArg (fun X : LSp D => GA D X.sp) hY) (GlobalTheory.LevelNbhd.finPartG Y.sp k)) =
      (finHom D.sp.X').rangeRestrict (cast (congrArg (fun X : LSp D => GA D X.sp) hY) k) := by
  subst hY
  exact Subtype.ext (GlobalTheory.LevelNbhd.finHom_finPartG _ k)

end GlobalTheory.RowClaim.RealTypeOf

namespace GlobalTheory.RowClaim.RealTypeOf

open GlobalTheory.CoefModel

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

theorem colFn_realType (ch : Choice R) : ∃ Λ : Module.Dual ℂ (VV ℂ (wt ch.G (.top 0))), ∀ a g,
    colFn ch a g = Λ (rhoK (wt ch.G (.top 0)) (invTrK (realGL ch.W.θ (ch.G.V (.top 0)) g⁻¹))
      (psiC (ch.Psi a) (GlobalTheory.IndefiniteRowSideFullHecke.BasisPolynomialParabolics.fp (ch.G.V (.top 0)) g))) :=
  ⟨colFun ch.G ch.W.θ ch.ξ, colFn_eq ch⟩

theorem co_eq_of (ch : Choice R) (c₀ : VV D.what₂.LL (fun τ => Bridge.lamRdef (Ptw D) τ) →ₛₗ[D.what₂.embLL] R.cX.W)
    (hco : ∀ v, (ch.S.co (c₀ v)).1 = MvPolynomial.rename
      (Prod.map id (Prod.map (Fin.cast (rank_zero_m ch.G)) (Fin.cast (rank_zero_m ch.G)))) (MvPolynomial.map D.what₂.embLL v.1))
    (e : VV ℂ (fun τ => Bridge.lamRdef (Ptw D) τ) ≃ₗ[ℂ] R.cX.W) (he : ∀ v, e (mapVV D.what₂.embLL _ v) = c₀ v)
    (x : VV ℂ (fun τ => Bridge.lamRdef (Ptw D) τ)) :
    (ch.S.co (e x)).1 = MvPolynomial.rename
      (Prod.map id (Prod.map (Fin.cast (rank_zero_m ch.G)) (Fin.cast (rank_zero_m ch.G)))) x.1 := by
  have : (VV ℂ (listedWt ch.G (.grid 0 D.R.m))).subtype ∘ₗ ch.S.co ∘ₗ e.toLinearMap =
      (MvPolynomial.rename (Prod.map id (Prod.map (Fin.cast (rank_zero_m ch.G)) (Fin.cast (rank_zero_m ch.G))))).toLinearMap ∘ₗ
        (VV ℂ (fun τ => Bridge.lamRdef (Ptw D) τ)).subtype := by
    refine LinearMap.ext_on_range (span_mapVV D.what₂.embLL _) fun i => ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Submodule.subtype_apply, AlgHom.toLinearMap_apply]
    rw [he, hco, mapVV_coe]
  exact LinearMap.congr_fun this x

theorem co_injective (ch : Choice R) : Function.Injective ch.S.co := by
  obtain ⟨gram, c₀, c₁, ht, hco⟩ := ch.S.co_is
  obtain ⟨e, he⟩ := GlobalTheory.CoefReal.exists_scalarExt D.what₂.embLL _ c₀ ht.mapR.2.1 ht.mapR.2.2
  intro w w' h
  obtain ⟨x, rfl⟩ := e.surjective w
  obtain ⟨x', rfl⟩ := e.surjective w'
  have h1 := congrArg Subtype.val h
  have h2 : MvPolynomial.rename (Prod.map id (Prod.map (Fin.cast (rank_zero_m ch.G)) (Fin.cast (rank_zero_m ch.G)))) x.1 =
      MvPolynomial.rename (Prod.map id (Prod.map (Fin.cast (rank_zero_m ch.G)) (Fin.cast (rank_zero_m ch.G)))) x'.1 := by
    rw [← co_eq_of ch c₀ hco e he x, ← co_eq_of ch c₀ hco e he x']
    exact h1
  have hinj : Function.Injective (Prod.map id (Prod.map (Fin.cast (rank_zero_m ch.G)) (Fin.cast (rank_zero_m ch.G))) :
      D.what₂.Tau × Fin D.sp.X'.rank × Fin D.sp.X'.rank → _) :=
    Function.injective_id.prodMap ((Fin.cast_injective _).prodMap (Fin.cast_injective _))
  rw [Subtype.ext (MvPolynomial.rename_injective _ hinj h2)]

theorem co_real (ch : Choice R) (hc : R.cX.Is) (u : GA D D.sp.X')
    (hu : u ∈ GinfC D.sp.X') (w : R.cX.W) :
    ch.S.co (R.cX.ρ u w) = rhoK (listedWt ch.G (.grid 0 D.R.m))
      (fun τ => castGL (rank_zero_m ch.G) (realGL ch.W.θ D.sp.X' u τ)) (ch.S.co w) := by
  have hF := GlobalTheory.ForcedWeights.lamRForced D
  obtain ⟨gram, c₀, c₁, ht, hco⟩ := ch.S.co_is
  obtain ⟨e, he, hre⟩ := exists_real_model_sq D.sp.X' ch.W.θ R.cX _ c₀ ch.W.θ_is hc ht.mapR
  obtain ⟨x, rfl⟩ := e.surjective w
  have hw : ∀ τ a, (listedWt ch.G (.grid 0 D.R.m) τ).w (Fin.cast (rank_zero_m ch.G) a) =
      (Bridge.lamRdef (Ptw D) τ).w a := fun τ a => by
    change (wtOf _ (GlobalTheory.SignedHC.entries (parV D ch.sc.cGap 0 D.R.m τ))).w _ = _
    rw [parV_zero D ch.sc.cGap le_rfl τ]
    exact wtOf_entries_eq (rank_zero_m ch.G) (hF τ) a
  rw [hre u hu x]
  refine Subtype.ext ?_
  rw [co_eq_of ch c₀ hco e he, rhoK_rename (rank_zero_m ch.G) _ _ hw _ x _ (co_eq_of ch c₀ hco e he x)]

theorem formTop_eq (ch : Choice R) (hc : R.cX.Is)
    (j : VV ℂ (listedWt ch.G (.grid 0 D.R.m)) →ₗ[ℂ] R.cX.W) (hj : ∀ w, j (ch.S.co w) = w) (t : T) (y : (R.HX t).H)
    (g : GA D (ch.G.V (.grid 0 D.R.m))) :
    formTop ch t y g = R.prX (j (rhoK (listedWt ch.G (.grid 0 D.R.m)) (realGL ch.W.θ (ch.G.V (.grid 0 D.R.m)) g⁻¹)
      (ch.S.formC t y (GlobalTheory.IndefiniteRowSideFullHecke.BasisPolynomialParabolics.fp (ch.G.V (.grid 0 D.R.m)) g)))) ch.cv.v := by
  obtain ⟨g', hg'⟩ : ∃ g' : GA D D.sp.X', g' = cast (congrArg (fun X : LSp D => GA D X.sp) (colY_m R.toLevCh)) g := ⟨_, rfl⟩
  have hL : formTop ch t y g = R.prX (R.cX.ρ g'⁻¹ ((R.HX t).e y ((finHom D.sp.X').rangeRestrict g'))) ch.cv.v := by
    subst hg'
    rfl
  have hG : realGL ch.W.θ (ch.G.V (.grid 0 D.R.m)) g⁻¹ =
      fun τ => castGL (rank_zero_m ch.G) (realGL ch.W.θ D.sp.X' g'⁻¹ τ) := by
    funext τ
    have := realGL_cast_inv ch.W.θ (columnBlock R.toLevCh D.R.m) (colY_m R.toLevCh) g τ
    rw [← hg'] at this
    exact this
  have hF' : ch.S.formC t y (GlobalTheory.IndefiniteRowSideFullHecke.BasisPolynomialParabolics.fp (ch.G.V (.grid 0 D.R.m)) g) =
      ch.S.co ((R.HX t).e y ((finHom D.sp.X').rangeRestrict g')) := by
    have := finHom_cast_finPart (columnBlock R.toLevCh D.R.m) (colY_m R.toLevCh) g
    rw [← hg'] at this
    exact congrArg (fun z => ch.S.co ((R.HX t).e y z)) this
  obtain ⟨k, hkdef⟩ : ∃ k, k = GlobalTheory.LevelNbhd.finPartG D.sp.X' g' := ⟨_, rfl⟩
  have hk : k ∈ GfC D.sp.X' := hkdef ▸ GlobalTheory.LevelNbhd.finPartG_mem_GfC _ _
  have hu : k⁻¹ * g' ∈ GinfC D.sp.X' := hkdef ▸ GlobalTheory.LevelNbhd.inv_finPartG_mul_mem_GinfC _ _
  have hinv : g'⁻¹ = (k⁻¹ * g')⁻¹ * k⁻¹ := by group
  have hρ : R.cX.ρ g'⁻¹ = R.cX.ρ (k⁻¹ * g')⁻¹ := by rw [hinv, map_mul, hc.1 _ (inv_mem hk), mul_one]
  have hfin : realGL ch.W.θ D.sp.X' k⁻¹ = 1 := funext fun τ => by
    show Formalism.UG.bc (ch.W.θ τ) (infHom D.sp.X' k⁻¹) = 1
    rw [show infHom D.sp.X' k⁻¹ = 1 from inv_mem hk, map_one]
  have hR : realGL ch.W.θ D.sp.X' g'⁻¹ = realGL ch.W.θ D.sp.X' (k⁻¹ * g')⁻¹ := by
    rw [hinv, map_mul, hfin, mul_one]
  have h2 : realGL ch.W.θ (ch.G.V (.grid 0 D.R.m)) g⁻¹ =
      fun τ => castGL (rank_zero_m ch.G) (realGL ch.W.θ D.sp.X' (k⁻¹ * g')⁻¹ τ) := hG.trans (by rw [hR])
  have e1 : rhoK (listedWt ch.G (.grid 0 D.R.m)) (realGL ch.W.θ (ch.G.V (.grid 0 D.R.m)) g⁻¹)
      (ch.S.formC t y (GlobalTheory.IndefiniteRowSideFullHecke.BasisPolynomialParabolics.fp (ch.G.V (.grid 0 D.R.m)) g)) =
      rhoK (listedWt ch.G (.grid 0 D.R.m)) (fun τ => castGL (rank_zero_m ch.G) (realGL ch.W.θ D.sp.X' (k⁻¹ * g')⁻¹ τ))
        (ch.S.co ((R.HX t).e y ((finHom D.sp.X').rangeRestrict g'))) :=
    congr (congrArg (fun M => ⇑(rhoK (listedWt ch.G (.grid 0 D.R.m)) M)) h2) hF'
  have key := (congrArg j e1).trans ((congrArg j (co_real ch hc _ (inv_mem hu) _).symm).trans
    ((hj _).trans (LinearMap.congr_fun hρ.symm _)))
  exact hL.trans (congrArg (fun z => R.prX z ch.cv.v) key.symm)

theorem formTop_realType (ch : Choice R) (hc : R.cX.Is) :
    ∃ Λ : Module.Dual ℂ (VV ℂ (listedWt ch.G (.grid 0 D.R.m))), ∀ t y g,
      formTop ch t y g = Λ (rhoK (listedWt ch.G (.grid 0 D.R.m)) (realGL ch.W.θ (ch.G.V (.grid 0 D.R.m)) g⁻¹)
        (ch.S.formC t y (GlobalTheory.IndefiniteRowSideFullHecke.BasisPolynomialParabolics.fp (ch.G.V (.grid 0 D.R.m)) g))) := by
  obtain ⟨j, hj⟩ := ch.S.co.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 (co_injective ch))
  exact ⟨R.prX.flip ch.cv.v ∘ₗ j, fun t y g => by
    rw [formTop_eq ch hc j (fun w => LinearMap.congr_fun hj w) t y g]
    rfl⟩

end GlobalTheory.RowClaim.RealTypeOf
end
end

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.DefStep
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsOpenCompactLevel IsDefiniteSpace)
open scoped ComplexOrder Topology

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.JetsOne

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

theorem fp_eq (V : HSp D) (g : GA D V) : GlobalTheory.IndefiniteRowSideFullHecke.BasisPolynomialParabolics.fp V g = finOf V g :=
  ClassFin.finG_injective V ((GlobalTheory.SuppLevO.finE_finPartG V g).trans (finG_finOf V g).symm)

theorem frame_real {L : LevCh D T} {sc : Consts} {G : GridData L sc} {U : Set T} (θ : InfFam D) (N : Std G U) (X : Node)
    (g : GA D (G.V X)) (v : VV ℂ (wt G X)) :
    rhoVr (tauE D) (wt G X) (N.fr X) (realAct θ N.fr X g (rhoVr (tauE D) (wt G X) (N.fr X)⁻¹ v)) =
      rhoK (wt G X) (invTrK (GlobalTheory.CoefModel.realGL θ (G.V X) g)) v := by
  have e' : realAct θ N.fr X = GlobalTheory.RealType.rhoAt θ N X := rfl
  rw [e', GlobalTheory.RealType.rhoVr_rhoAt, ← Module.End.mul_apply (rhoVr _ _ _), ← map_mul, mul_inv_cancel, map_one,
    Module.End.one_apply, GlobalTheory.RealType.rhoFr_one]

theorem col_real (ch : Choice R) : ∃ Λ : Module.Dual ℂ (VV ℂ (wt ch.G (.top 0))), ∀ a,
    IsFinReal (realAct ch.W.θ ch.S.N.fr (.top 0)) (colFn ch a) Λ
      fun x => rhoVr (tauE D) _ (ch.S.N.fr (.top 0))⁻¹ (psiC (ch.Psi a) x) := by
  obtain ⟨Λ, h⟩ := RealTypeOf.colFn_realType ch
  refine ⟨Λ ∘ₗ rhoVr (tauE D) _ (ch.S.N.fr (.top 0)), fun a g => ?_⟩
  rw [h, fp_eq, LinearMap.comp_apply, frame_real]

theorem form_real (ch : Choice R) (hc : R.cX.Is) : ∃ Λ : Module.Dual ℂ (VV ℂ (wt ch.G (.grid 0 D.R.m))), ∀ t y,
    IsFinReal (realAct ch.W.θ ch.S.N.fr (.grid 0 D.R.m)) (formTop ch t y) Λ
      fun x => rhoVr (tauE D) (wt ch.G (.grid 0 D.R.m)) (ch.S.N.fr (.grid 0 D.R.m))⁻¹
        (funOf (listedWt ch.G (.grid 0 D.R.m)) (ch.S.formC t y x)) := by
  obtain ⟨Λ, h⟩ := RealTypeOf.formTop_realType ch hc
  let φ := GlobalTheory.FunObj.funEquiv (K := ℂ) (listedWt ch.G (.grid 0 D.R.m))
  have hφ : ∀ F, funOf (listedWt ch.G (.grid 0 D.R.m)) F = φ F := fun F =>
    (GlobalTheory.FunObj.isFunForm_iff_eq _ _ _).1 ((readOK_of_equiv _ φ (GlobalTheory.FunObj.isFunForm_funEquiv _)).1 F)
  refine ⟨Λ ∘ₗ φ.symm.toLinearMap ∘ₗ rhoVr (tauE D) (wt ch.G (.grid 0 D.R.m)) (ch.S.N.fr (.grid 0 D.R.m)), fun t y g => ?_⟩
  rw [h, fp_eq]
  have e1 := frame_real ch.W.θ ch.S.N (.grid 0 D.R.m) g⁻¹
    (funOf (listedWt ch.G (.grid 0 D.R.m)) (ch.S.formC t y (finOf _ g)))
  have e2 := GlobalTheory.FunObj.funEquiv_rhoK (K := ℂ) (listedWt ch.G (.grid 0 D.R.m))
    (GlobalTheory.CoefModel.realGL ch.W.θ (ch.G.V (.grid 0 D.R.m)) g⁻¹) (ch.S.formC t y (finOf _ g))
  have e3 := e2.trans ((congrArg _ (hφ _).symm).trans e1.symm)
  exact congrArg Λ ((φ.symm_apply_apply _).symm.trans (congrArg φ.symm e3))

theorem psiC_right (ch : Choice R) (a : Fin ch.n) (x k : FinPt ch.G (.top 0)) (hk : finG (ch.G.V (.top 0)) k ∈ ch.G.Kplus) :
    psiC (ch.Psi a) (x * k) = psiC (ch.Psi a) x := by
  have e : ch.Psi a (finG (Xp ch.G) (x * k)) = ch.Psi a (finG (Xp ch.G) x) := by
    rw [show finG (Xp ch.G) (x * k) = finG (Xp ch.G) x * finG (Xp ch.G) k from map_mul _ _ _]
    exact psi_right _ _ a _ hk
  exact Subtype.ext (congrArg (fun z => (GlobalTheory.CoefModel.mapVV D.what₂.embLL (LaP ch.G) z).1) e)

theorem col_left (ch : Choice R) (a : Fin ch.n) : ∀ γ ∈ GQ (ch.G.V (.top 0)), ∀ g, colFn ch a (γ * g) = colFn ch a g :=
  fun γ hγ g => GlobalTheory.RowBplus.pairVec_left ch.G ch.W.θ ch.ξ (col_mem ch a) hγ g

theorem real_right {V : HSp D} {M : Type} [AddCommGroup M] [Module ℂ M] {ρ : GA D V →* Module.End ℂ M}
    (hρ : ∀ g ∈ GfC V, ρ g = 1) {F : GA D V → ℂ} {Λ : Module.Dual ℂ M} {v : GfC V → M} (h : IsFinReal ρ F Λ v)
    (k : GfC V) (hk : ∀ x, v (x * k) = v x) (g : GA D V) : F (g * k) = F g := by
  rw [h, h, finOf_mul_fin, hk, mul_inv_rev, map_mul, hρ _ (inv_mem k.2), one_mul]

theorem col_fix (ch : Choice R) (a : Fin ch.n) (hK : IsOpenCompactLevel (ch.G.V (.top 0)) ch.G.Kplus) :
    ∀ᶠ k in 𝓝 (1 : GA D (ch.G.V (.top 0))), k ∈ GfC _ → ∀ g, colFn ch a (g * k) = colFn ch a g := by
  obtain ⟨Λ, h⟩ := col_real ch
  filter_upwards [hK.1.mem_nhds (one_mem _)] with k hk hf g
  exact real_right (fun g hg => realAct_fin _ _ _ hg) (h a) ⟨k, hf⟩ (fun x => congrArg _ (psiC_right ch a x ⟨k, hf⟩ hk)) g

theorem aut_cast' {Λ : Submodule (𝓞 D.host.E) (Fin D.sp.X'.rank → D.host.E)} (X : LSp D) (h : X = ⟨D.sp.X', Λ⟩)
    (φ : GA D D.sp.X' → ℂ) (hφ : IsAutFun D.sp.X' φ) :
    IsAutFun X.sp (fun g => φ (cast (congrArg (fun X : LSp D => GA D X.sp) h) g)) := by
  subst h
  exact hφ

theorem form_aut {large₂ : SizeData₂ D} {F : Face D A} (hS : HidaSetting large₂ R F) (ch : Choice R) (t : T) (y : (R.HX t).H) :
    (∀ γ ∈ GQ (ch.G.V (.grid 0 D.R.m)), ∀ g, formTop ch t y (γ * g) = formTop ch t y g) ∧
    ∀ᶠ k in 𝓝 (1 : GA D (ch.G.V (.grid 0 D.R.m))), k ∈ GfC _ → ∀ g, formTop ch t y (g * k) = formTop ch t y g := by
  have hm := hS.core.models
  obtain ⟨h1, -, -⟩ := GlobalTheory.EndCusp.formX_props R hm.inf hm.cX hm.prX hm.HX ch.cv t y
  have k := aut_cast' (columnBlock R.toLevCh D.R.m) (colY_m R.toLevCh) (ch.cv.formX t y) h1.toIsAutFun
  obtain ⟨U, hU, e⟩ := k.level
  refine ⟨k.left, ?_⟩
  filter_upwards [hU.mem_nhds (one_mem _)] with z hz using e z hz

end GlobalTheory.JetsOne

end
