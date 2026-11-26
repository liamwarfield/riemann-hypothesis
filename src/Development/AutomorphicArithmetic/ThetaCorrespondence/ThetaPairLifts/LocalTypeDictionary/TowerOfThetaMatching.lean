module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TowerOfThetaMatching
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaSquareNormComparison
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.WittTowerNormStepOfLargeRank

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.WittTowerNormStepOfSmallRank
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.SeesawFirstReductionLevel
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TowerStageSuccessorCoefficients
section
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
namespace GlobalTheory.HermitianSkewAdaptation
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.PlaneSkew
open GlobalTheory.AdelicU (IsSplitBasis)
open scoped Matrix
section Planes
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
end Planes
section Transport
open GlobalTheory.SqStepK GlobalTheory.SqStepBig
variable {D : D7}
end Transport
section Cast
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem const_pair_alt (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (hK : ThetaIntegralsAgree) (hM : LocalMatching) {B : Base F E} (hB : B.IsGood σ)
    {a a' : ℕ} {Γ : Geo σ a a'} (g : Γ.IsGood B) {Xa Xb : Chars F E} (xa : Xa.IsGood B a a') (xb : Xb.IsGood B a a') {la lb : ℂ}
    (hlb : lb ≠ 0)
    (H : ∀ R om om' Rf om₀ om₀' Rf₀ (c c₀ : ℂ), IsMatched B Γ Xa om om' R Rf → IsMatched B Γ Xb om₀ om₀' R Rf₀ →
      IsConst B Γ Xa om om' R Rf c → IsConst B Γ Xb om₀ om₀' R Rf₀ c₀ →
      ∃ k : (AE F E)ˣ, c * lb = ((Xa.ν k / Xb.ν k : Circle) : ℂ) * (c₀ * la))
    {V : Spc F E a} {V' : Spc F E a'} {Z : Spc F E (a + a')} (g₂ : (reG Γ V V' Z).IsGood B) :
    ∃ (R : RealMaps F a a') (d : ℂ) (k : (AE F E)ˣ), d ≠ 0 ∧
      GlobalTheory.SqStepK.HasConstR B (reG Γ V V' Z) R Xa (d * ((Xa.ν k / Xb.ν k : Circle) : ℂ) * la) ∧
      GlobalTheory.SqStepK.HasConstR B (reG Γ V V' Z) R Xb (d * ((Xb.ν k / Xb.ν k : Circle) : ℂ) * lb) := by
  obtain ⟨oa, oa', ob, ob', R, Ra, Rb, da, db, m1, m2, k1, k2, hdb, k, hk⟩ := _root_.GlobalTheory.SqStepBig.theta_tower_step_pair_real_part hP hK hM hB g xa xb H g₂
  refine ⟨R, db / lb, k, div_ne_zero hdb hlb, ⟨oa, oa', Ra, m1, ?_⟩, ⟨ob, ob', Rb, m2, ?_⟩⟩
  · convert k1 using 1
    field_simp
    linear_combination -hk
  · convert k2 using 1
    rw [div_self', Circle.coe_one, mul_one, div_mul_cancel₀ _ hlb]
end Cast
open GlobalTheory.SqStepBig in
theorem tower_stage_successor_relation_alt : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) →
    NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (p q : ℕ) (A A' WW B' WW₁ : HSp D) (X : Tri T A A' WW)
      (Y : Tri T A B' WW₁) (lam c : T → ℂ) (e : ℕ), GlobalTheory.SqTower.IsStageC W i j p (q + 1) X →
      GlobalTheory.SqTower.IsStageC W i j p q Y → GlobalTheory.SqStepK.IsStepB X Y → Factor X W.ψ W.θ lam → Factor Y W.ψ W.θ c →
      A.rank = A'.rank + 2 * e → ∀ t, ∃ (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (b : ℕ)
        (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig A.rank (b + 2)) (Γ₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig A.rank b)
        (H : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Plane D.host.E (b + 2) b) (H' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Plane D.host.E (A.rank + (b + 2)) (A.rank + b))
        (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps D.host.F A.rank (b + 2)) (R₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps D.host.F A.rank b) (d d₁ : ℂ)
        (k k₁ : (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := D.host.F) (E := D.host.E))ˣ),
        GlobalTheory.SqStep.BaseFits G W i j t Bs ∧ A'.rank = b + 2 ∧ Γ₁.V = Γ.V ∧ Γ₁.p = Γ.p ∧ Γ₁.q + 1 = Γ.q ∧
        H.IsAdapted D.sp.cm.sig Bs Γ.V' Γ₁.V' 0 (b + 1) ∧ H'.IsAdapted D.sp.cm.sig Bs Γ.W Γ₁.W A.rank (A.rank + b + 1) ∧
        d ≠ 0 ∧ d₁ ≠ 0 ∧ ∀ t' ∈ ({t, μ₀} : Set T),
          GlobalTheory.SqStepK.HasConstR Bs Γ R (GlobalTheory.SqStep.chs G i j t')
            (d * (((GlobalTheory.SqStep.chs G i j t').ν k / (GlobalTheory.SqStep.chs G i j μ₀).ν k : Circle) : ℂ) * lam t') ∧
          GlobalTheory.SqStepK.HasConstR Bs Γ₁ R₁ (GlobalTheory.SqStep.chs G i j t')
            (d₁ * (((GlobalTheory.SqStep.chs G i j t').ν k₁ / (GlobalTheory.SqStep.chs G i j μ₀).ν k₁ : Circle) : ℂ) * c t') := by
  intro hP hK hM
  refine gbig_of_three GlobalTheory.T.exists_realEmbeddings_sharedBase_towerStage (_root_.GlobalTheory.T.tower_stage_fit_factor_alt hP hK hM) GlobalTheory.T.exists_realEmbeddings_sharedBase_towerStage ?_
  rintro D T Lc sc G μ₀ C x b qb qd - W S hψ hN i j p q A A' WW B' WW₁ X Y lam c e hX hY ⟨hA, ⟨ι, x, y, hs⟩, ι', x', y', hs'⟩ hF hc he t
  obtain ⟨emb, hemb⟩ := qb W hψ i j _ _ A A' WW X hX
  obtain ⟨Bs, -, f⟩ := hemb t
  have hn : A'.rank = B'.rank + 2 := hs.1
  have f₁ : Fit G W i j t μ₀ Bs A.rank B'.rank := Fit.down_right (hn ▸ f)
  obtain ⟨Γ, o, pΓ, qΓ, g, HX⟩ := qd W hψ i j _ _ A A' WW X lam t Bs hX hF f
  obtain ⟨Γ₁, o₁, pΓ₁, qΓ₁, g₁, HY⟩ := qd W hψ i j _ _ A B' WW₁ Y c t Bs hY hc f₁
  obtain ⟨U, H, hU, hH⟩ := plane_herm f.2.1 hs (neg_ne_zero.2 one_ne_zero) o.2.1 o₁.2.1 g.hV' g₁.hV' (i₀ := 0) (i₁ := B'.rank + 1)
    (by omega) (by omega)
  obtain ⟨Z, H', hZ, hH'⟩ := plane_skew f.2.1 hs' o.2.2 o₁.2.2 g.hW g₁.hW (i₀ := A.rank) (i₁ := A.rank + B'.rank + 1)
    (by omega) (by omega)
  have eV : reS Γ₁.V Γ.V = reS Γ.V Γ.V := reS_congr Γ.V (o.1.eq (hA ▸ o₁.1))
  have hV : (reS Γ.V Γ.V).IsHerm D.sp.cm.sig Bs (A.rank - Γ.p) Γ.p := g.hV
  have g₂ : (reG Γ Γ.V U Z).IsGood Bs := isGood_reG g hV hU hZ
  have g₃ : (reG Γ₁ Γ.V Γ₁.V' Γ₁.W).IsGood Bs := isGood_reG g₁ (by rw [eV, pΓ₁, ← pΓ]; exact hV) g₁.hV' g₁.hW
  obtain ⟨R, d, k, hd, c1, c2⟩ := _root_.GlobalTheory.HermitianSkewAdaptation.const_pair_alt hP hK hM f.2.1 g f.2.2.2.1 f.2.2.2.2.1 (hF.1 μ₀) HX g₂
  obtain ⟨R₁, d₁, k₁, hd₁, c3, c4⟩ := _root_.GlobalTheory.HermitianSkewAdaptation.const_pair_alt hP hK hM f.2.1 g₁ f₁.2.2.2.1 f₁.2.2.2.2.1 (hc.1 μ₀) HY g₃
  obtain ⟨Γ', K, K', R', e1, e2, e3, e4, e5, e6⟩ := cast_rank Bs hn (reG Γ Γ.V U Z) (reG Γ₁ Γ.V Γ₁.V' Γ₁.W) H H' R eV
    (pΓ₁.trans pΓ.symm) (by show Γ₁.q + 1 = Γ.q; rw [qΓ, qΓ₁]) hH hH'
  refine ⟨Bs, B'.rank, Γ', _, K, K', R', R₁, d, d₁, k, k₁, f.1, hn, e1, e2, e3, e4, e5, hd, hd₁, ?_⟩
  rintro t' (rfl | rfl)
  · exact ⟨e6 _ _ c1, c3⟩
  · exact ⟨e6 _ _ c2, c4⟩
end GlobalTheory.HermitianSkewAdaptation
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem _root_.GlobalTheory.T.tower_stage_successor_coefficients_alt : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) →
    NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (p q : ℕ) (A A' WW B' WW₁ : HSp D) (X : Tri T A A' WW)
      (Y : Tri T A B' WW₁) (lam c : T → ℂ) (e : ℕ), GlobalTheory.SqTower.IsStageC W i j p (q + 1) X →
      GlobalTheory.SqTower.IsStageC W i j p q Y → GlobalTheory.SqStepK.IsStepB X Y → Factor X W.ψ W.θ lam → Factor Y W.ψ W.θ c →
      A.rank = A'.rank + 2 * e → ∀ t, ∃ (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (b : ℕ)
        (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig A.rank (b + 2)) (Γ₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig A.rank b)
        (H : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Plane D.host.E (b + 2) b) (H' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Plane D.host.E (A.rank + (b + 2)) (A.rank + b))
        (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps D.host.F A.rank (b + 2)) (R₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps D.host.F A.rank b) (d d₁ : ℂ)
        (k k₁ : (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := D.host.F) (E := D.host.E))ˣ),
        GlobalTheory.SqStep.BaseFits G W i j t Bs ∧ A'.rank = b + 2 ∧ Γ₁.V = Γ.V ∧ Γ₁.p = Γ.p ∧ Γ₁.q + 1 = Γ.q ∧
        H.IsAdapted D.sp.cm.sig Bs Γ.V' Γ₁.V' 0 (b + 1) ∧ H'.IsAdapted D.sp.cm.sig Bs Γ.W Γ₁.W A.rank (A.rank + b + 1) ∧
        d ≠ 0 ∧ d₁ ≠ 0 ∧ ∀ t' ∈ ({t, μ₀} : Set T),
          GlobalTheory.SqStepK.HasConstR Bs Γ R (GlobalTheory.SqStep.chs G i j t')
            (d * (((GlobalTheory.SqStep.chs G i j t').ν k / (GlobalTheory.SqStep.chs G i j μ₀).ν k : Circle) : ℂ) * lam t') ∧
          GlobalTheory.SqStepK.HasConstR Bs Γ₁ R₁ (GlobalTheory.SqStep.chs G i j t')
            (d₁ * (((GlobalTheory.SqStep.chs G i j t').ν k₁ / (GlobalTheory.SqStep.chs G i j μ₀).ν k₁ : Circle) : ℂ) * c t') := by
  first | exact @_root_.GlobalTheory.HermitianSkewAdaptation.tower_stage_successor_relation_alt | exact _root_.GlobalTheory.HermitianSkewAdaptation.tower_stage_successor_relation_alt | (intros; apply _root_.GlobalTheory.HermitianSkewAdaptation.tower_stage_successor_relation_alt <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.QuadraticTowerStepStageInduction
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ExistsSmallTripleOfWeilVacuum
section
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
namespace GlobalTheory.SmallTriple
open GlobalTheory.Grid MeasureTheory
variable {D : D7}
private theorem eta_sq_eq_one_alt {η : (AF D.host.F)ˣ →* Circle} (h : IsEta D η) (a : (AF D.host.F)ˣ) : η a ^ 2 = 1 := by
  have h2 : Module.finrank D.host.F D.host.E = 2 := D.sp.cm.deg2
  have : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  have e := h.2.2.1 (idF D a)
  have e2 : Units.map (Algebra.norm (AF D.host.F) : AE D →* AF D.host.F) (idF D a) = a ^ 2 := by
    ext1
    show Algebra.norm (AF D.host.F) (algebraMap (AF D.host.F) (AE D) (a : AF D.host.F)) = ((a ^ 2 : (AF D.host.F)ˣ) : AF D.host.F)
    let b := (Module.finBasis D.host.F D.host.E).baseChange (AF D.host.F)
    rw [Algebra.norm_algebraMap_of_basis b, Fintype.card_fin, h2, Units.val_pow_eq_pow_val]
  rwa [e2, map_pow] at e
private theorem restriction_eta_add_two {χ : (AE D)ˣ →* Circle} {n : ℕ} (h : ResEta D χ (n + 2)) : ResEta D χ n :=
  ⟨h.1, fun η hη a => by rw [h.2 η hη a, pow_add, eta_sq_eq_one_alt hη, mul_one]⟩
private theorem exists_weil_representation (hP : GlobalTheory.Published.WeilRepresentationUnitaryPair) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1))
    (ε : Bool) (S W : HSp D) {χS χW : (AE D)ˣ →* Circle} (h1 : IsHeckeChar D χS) (h2 : IsHeckeChar D χW)
    (h3 : ResEta D χS S.rank) (h4 : ResEta D χW W.rank) : ∃ ω : WRep S W, IsWeil ψ ε S W χS χW ω := by
  obtain ⟨om, h⟩ := hP D ψ (sgn ε S) W χS χW hψ h1 h2 h3 h4
  exact ⟨om.comp ((ofSgn ε S).symm.toMonoidHom.prodMap (MonoidHom.id _)), h⟩
private theorem exists_vacuum_vector (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ)
    (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (hS : ∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) (hT : ∀ τ, IsCartanInv (gramAt D T τ) (sT τ))
    (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E))
    (dS : IsSelfDualC S ΛS) (dT : IsSelfDualC T ΛT) : ∃ f, IsVacO ψ θ S T sS sT ΛS ΛT f := by
  obtain ⟨f, f0, hf⟩ := GlobalTheory.VacuumO.exists_ne_zero ψ θ hψ hθ S T sS sT hS hT ΛS ΛT dS dT
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hcov⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  let _ : MeasurableSpace (WO S T) := measMx _ _
  have : BorelSpace (WO S T) := ⟨rfl⟩
  have h1 := (hf 1).1
  simp only [one_mul] at h1
  obtain ⟨⟨μ, 𝓕, hμ⟩, c, hc⟩ := GlobalTheory.T.exists_normalise_meanSquare_of_cocompact' (WO S T) (ratL T S) K hK hcov f h1.cont f0 (by
    rintro _ ⟨g, rfl⟩ w
    have e := h1.quasi g w
    have e' := congrArg norm e
    rw [norm_mul, hψ.1.2.1, one_mul] at e'
    exact e')
  exact ⟨fun w => c * f w, hψ, hθ, (hf c).1, (hf c).2.1, (hf c).2.2, ⟨(μ, 𝓕), hμ⟩,
    fun p hp => hc p.1 p.2 hp.1 hp.2.1 hp.2.2⟩
theorem exists_small_triple : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (T : Type) (A A' WW B' WW₁ : HSp D) (X : Tri T A A' WW)
    (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (α β : T → ((AE D)ˣ →* Circle)) (νH : T → HChar D.host.E)
    (S : T → Finset (Formalism.L2.DIV.Pl D.host.E)) (rB : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Rig B') (rW : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Rig WW₁),
    IsInfFam θ → X.Is ψ θ α β νH S → rB.Is → rW.Is → B'.rank + 2 = A'.rank → WW₁.rank + 2 = WW.rank →
    ∃ Y : Tri T A B' WW₁, Y.rA = X.rA ∧ Y.rA' = rB ∧ Y.rW = rW ∧ Y.Is ψ θ α β νH S := by
  intro hP D T A A' WW B' WW₁ X ψ θ α β νH S rB rW hθ hX hB hW eB eW
  have hψ : IsStdChar D ψ (-1) := hX.isVac.1
  have hA := hX.rigA
  choose ω hω using fun t => exists_weil_representation hP.weilRepresentationUnitaryPair hψ true A WW₁ (hX.weil t).hecS (hX.weil t).hecT
    (hX.weil t).resS (restriction_eta_add_two (eW ▸ (hX.weil t).resT))
  choose ω' hω' using fun t => exists_weil_representation hP.weilRepresentationUnitaryPair hψ false B' WW₁ (hX.weil' t).hecS (hX.weil' t).hecT
    (restriction_eta_add_two (eB ▸ (show ResEta D (α t) A'.rank from (hX.weil' t).resS))) (restriction_eta_add_two (eW ▸ (hX.weil' t).resT))
  have hneg : IsSelfDualC (neg A) X.rA.Λ := by
    refine ⟨hA.1.1, fun y => (hA.1.2 y).trans (forall₂_congr fun x _ => ⟨fun ⟨c, hc⟩ => ⟨-c, ?_⟩, fun ⟨c, hc⟩ => ⟨-c, ?_⟩⟩)⟩
    · simp [neg_gram, hc]
    · simp [neg_gram] at hc ⊢
      exact neg_eq_iff_eq_neg.2 hc
  obtain ⟨vac, hv⟩ := exists_vacuum_vector ψ θ hψ hθ (neg A) WW₁ (fun τ => -X.rA.s τ) rW.s
    (fun τ => isCartanInv_sgn true _ τ (hA.2.2 τ).1) (fun τ => (hW.2.2 τ).1) X.rA.Λ rW.Λ hneg hW.1
  obtain ⟨vac', hv'⟩ := exists_vacuum_vector ψ θ hψ hθ B' WW₁ rB.s rW.s
    (fun τ => (hB.2.2 τ).1) (fun τ => (hW.2.2 τ).1) rB.Λ rW.Λ hB.1 hW.1
  have hν : ∀ t, IsHeckeChar D (α t / β t) := fun t => (hX.weil' t).hecT
  choose f hf _ using fun t => GlobalTheory.T.first_standard_pair_member_has_theta_function D ψ θ A WW₁ X.rA rW _ _ _ _ _ hA hW (hν t) (hX.idem t)
    (GlobalTheory.ConstRatio.ideal_ne_bot X S t) hv
  choose f' hf' _ using fun t => GlobalTheory.T.exists_thetaFunction_standardPairSecond D ψ θ B' WW₁ rB rW _ _ _ _ A.rank _ hB hW (hν t) (hX.idem t)
    (GlobalTheory.ConstRatio.ideal_ne_bot X S t) hv'
  obtain ⟨m', fd', hm'⟩ := GlobalTheory.ConstRatio.exists_meas B'
  have hr := hX.rank
  exact ⟨⟨X.rA, rB, rW, ω, ω', vac, vac', X.e, X.c, f, f', X.m, X.fd, m', fd'⟩, rfl, rfl, rfl,
    ⟨by omega, hA, hB, hW, hω, hω', hv, hv', hX.idem, hX.expo, hf, hf', hX.meas, hm'⟩⟩
end GlobalTheory.SmallTriple
end
theorem _root_.GlobalTheory.T.exists_small_triple_of_weil_vacuum : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (T : Type) (A A' WW B' WW₁ : HSp D) (X : Tri T A A' WW)
    (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (α β : T → ((AE D)ˣ →* Circle)) (νH : T → HChar D.host.E)
    (S : T → Finset (Formalism.L2.DIV.Pl D.host.E)) (rB : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Rig B') (rW : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Rig WW₁),
    IsInfFam θ → X.Is ψ θ α β νH S → rB.Is → rW.Is → B'.rank + 2 = A'.rank → WW₁.rank + 2 = WW.rank →
    ∃ Y : Tri T A B' WW₁, Y.rA = X.rA ∧ Y.rA' = rB ∧ Y.rW = rW ∧ Y.Is ψ θ α β νH S := _root_.GlobalTheory.SmallTriple.exists_small_triple
end
end

section
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
namespace GlobalTheory.SqStepK.PiLocalization₂
theorem quadratic_tower_step_base_stage : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) →
    NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (p q : ℕ) (A A' WW : HSp D) (X : Tri T A A' WW),
      GlobalTheory.SqTower.IsStageC W i j p (q + 1) X → ∃ (B' WW₁ : HSp D) (Y : Tri T A B' WW₁),
        GlobalTheory.SqTower.IsStageC W i j p q Y ∧ GlobalTheory.SqStepK.IsStepB X Y := by
  intro hP _ _
  refine ⟨0, fun ε CF _ => ⟨0, 0, fun C _ D large₂ _ _ _ T Lc μ₀ _ G => ?_⟩⟩
  intro W S hψ hN i j p q A A' WW X hX
  obtain ⟨hp, hq, hrA, hrA', hnA, hnA', hnW, hXI⟩ := hX
  have hk := D.R.m_add_three_le_k
  have hm := D.R.two_le_m
  have hrk := hXI.rank
  have hb1 : 2 * qq D j + 3 ≤ rankV D i j := by
    simp only [rankV, qq, Formalism.BasicNotions.Ranks.r]; omega
  have hb2 : 2 * pp D j ≤ rankV D (i + 1) (j + 1) := by
    simp only [rankV, pp, Formalism.BasicNotions.Ranks.r]; omega
  obtain ⟨B', Λ₁, ι, x, y, hs, hsig, hsd, hneg⟩ := GlobalTheory.T.hyperbolicPlane_split_selfDual_hermitian_complement D A' X.rA'.Λ q hXI.rigA'.1 hnA' (by omega) (by omega)
  obtain ⟨WW₁, ΛW, ι', x', y', hs', hsig', hsd', hneg'⟩ :=
    GlobalTheory.T.hyperbolicPlane_split_selfDual_hermitian_complement D WW X.rW.Λ (p + q) hXI.rigW.1 (by simpa only [add_assoc] using hnW) (by omega) (by omega)
  obtain ⟨rB, eB, hB⟩ := GlobalTheory.RigExists.exists_rig D B' Λ₁ hsig hsd
  obtain ⟨rW, eW, hW⟩ := GlobalTheory.RigExists.exists_rig D WW₁ ΛW hsig' hsd'
  obtain ⟨Y, e1, e2, e3, hY⟩ := _root_.GlobalTheory.T.exists_small_triple_of_weil_vacuum hP D T A A' WW B' WW₁ X W.ψ W.θ _ _ _ _ rB rW W.θ_is hXI hB hW
    (by have := hs.1; omega) (by have := hs'.1; omega)
  refine ⟨B', WW₁, Y, ⟨hp, by omega, hrA, by have := hs.1; omega, hnA, hneg, hneg', hY⟩, e1, ⟨ι, x, y, ?_⟩, ⟨ι', x', y', ?_⟩⟩
  · rw [e2, eB]; exact hs
  · rw [e3, eW]; exact hs'
end GlobalTheory.SqStepK.PiLocalization₂
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quadratic_tower_step_stage_induction : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) →
    NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (p q : ℕ) (A A' WW : HSp D) (X : Tri T A A' WW),
      GlobalTheory.SqTower.IsStageC W i j p (q + 1) X → ∃ (B' WW₁ : HSp D) (Y : Tri T A B' WW₁),
        GlobalTheory.SqTower.IsStageC W i j p q Y ∧ GlobalTheory.SqStepK.IsStepB X Y := by
  first | exact @_root_.GlobalTheory.SqStepK.PiLocalization₂.quadratic_tower_step_base_stage | exact _root_.GlobalTheory.SqStepK.PiLocalization₂.quadratic_tower_step_base_stage | (intros; apply _root_.GlobalTheory.SqStepK.PiLocalization₂.quadratic_tower_step_base_stage <;> assumption)
end
end

section
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
namespace GlobalTheory.SqStepK
section Values
open GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
end Values
theorem seesaw_first_reduction : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) →
    NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (p q : ℕ) (A A' WW : HSp D) (X : Tri T A A' WW) (lam : T → ℂ) (e : ℕ),
      GlobalTheory.SqTower.IsStageC W i j p (q + 1) X → Factor X W.ψ W.θ lam → A.rank = A'.rank + 2 * e →
      ∃ (B B' WW₁ : HSp D) (Y : Tri T B B' WW₁) (c : T → ℂ), GlobalTheory.SqTower.IsStageC W i j p q Y ∧ Y.IsConst W.ψ W.θ c ∧
        (∀ t, c t ≠ 0) ∧ ∀ t, ∃ (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (e₁ e₂ s : ℤˣ)
          (𝔟 𝔠 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E), GlobalTheory.SqStep.BaseFits G W i j t Bs ∧
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.stepFac Bs (GlobalTheory.SqStep.chs G i j t) e₁ e₂ s 𝔟 𝔠 (-(e : ℤ)) ≠ 0 ∧
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.stepFac Bs (GlobalTheory.SqStep.chs G i j μ₀) e₁ e₂ s 𝔟 𝔠 (-(e : ℤ)) ≠ 0 ∧
          GlobalTheory.LFun.charL (GlobalTheory.SqStep.chs G i j t).ν (G.pl.S0 : Set (HeightOneSpectrum (𝓞 D.host.F))) ((e + 1 : ℕ) : ℂ) ≠ 0 ∧
          GlobalTheory.LFun.charL (GlobalTheory.SqStep.chs G i j μ₀).ν (G.pl.S0 : Set (HeightOneSpectrum (𝓞 D.host.F))) ((e + 1 : ℕ) : ℂ) ≠ 0 ∧
          lam t * GlobalTheory.LFun.charL (GlobalTheory.SqStep.chs G i j t).ν (G.pl.S0 : Set (HeightOneSpectrum (𝓞 D.host.F))) ((e + 1 : ℕ) : ℂ) *
              GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.stepFac Bs (GlobalTheory.SqStep.chs G i j t) e₁ e₂ s 𝔟 𝔠 (-(e : ℤ)) * c μ₀ =
            lam μ₀ * GlobalTheory.LFun.charL (GlobalTheory.SqStep.chs G i j μ₀).ν (G.pl.S0 : Set (HeightOneSpectrum (𝓞 D.host.F))) ((e + 1 : ℕ) : ℂ) *
              GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.stepFac Bs (GlobalTheory.SqStep.chs G i j μ₀) e₁ e₂ s 𝔟 𝔠 (-(e : ℤ)) * c t := by
  intro hP hK hM
  obtain ⟨e₁, e₂, s, hSB⟩ := hK.2.1
  refine gbig_three_is (_root_.GlobalTheory.T.quadratic_tower_step_stage_induction hP hK hM) (_root_.GlobalTheory.T.tower_stage_successor_coefficients_alt hP hK hM) (_root_.GlobalTheory.T.exists_factor_of_isStageC hP hK hM) ?_
  intro D T Lc sc G μ₀ C x b hL hy hd hf W S hψ hN i j p q A A' WW X lam e hX hF he
  obtain ⟨B', WW₁, Y, hY, hst⟩ := hy W S hψ hN i j p q A A' WW X hX
  obtain ⟨c, hc⟩ := hf W S hψ hN i j p q A B' WW₁ Y hY
  haveI : Nonempty T := ⟨μ₀⟩
  refine ⟨A, B', WW₁, Y, c, hY, hc.isConst, hc.1, fun t => ?_⟩
  obtain ⟨Bs, bb, Γ, Γ₁, H, H', R, R₁, d, d₁, k, k₁, hfit, hb, hV, hp, hq, hH, hH', hd0, hd10, hk⟩ :=
    hd W S hψ hN i j p q A A' WW B' WW₁ X Y lam c e hX hY hst hF hc he t
  obtain ⟨C₀, hC₀, hstep⟩ := hSB D.host.F D.host.E D.sp.cm.sig Bs A.rank bb Γ Γ₁ H H' R R₁ hV hp hq hH hH'
  have hE : (A.rank - (bb + 2)) / 2 = e := by omega
  have key : ∀ t' ∈ ({t, μ₀} : Set T),
      d * (((GlobalTheory.SqStep.chs G i j t').ν k / (GlobalTheory.SqStep.chs G i j μ₀).ν k : Circle) : ℂ) * lam t' *
      GlobalTheory.LFun.charL (GlobalTheory.SqStep.chs G i j t').ν (G.pl.S0 : Set (HeightOneSpectrum (𝓞 D.host.F))) ((e + 1 : ℕ) : ℂ) *
      (C₀ * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.stepFac Bs (GlobalTheory.SqStep.chs G i j t') e₁ e₂ s H.𝔟 H'.𝔟 (-(e : ℤ))) =
      d₁ * (((GlobalTheory.SqStep.chs G i j t').ν k₁ / (GlobalTheory.SqStep.chs G i j μ₀).ν k₁ : Circle) : ℂ) * c t' := by
    intro t' ht'
    obtain ⟨⟨om, om', Rf, hm, hκ⟩, ⟨om₁, om₁', Rf₁, hm₁, hκ₁⟩⟩ := hk t' ht'
    obtain ⟨u, hu1, hu2⟩ := hstep _ om om' Rf om₁ om₁' Rf₁ hm hm₁ _ _ hκ hκ₁
    rw [hE] at hu1 hu2
    have e1 : (((e : ℕ) : ℂ) + 1) = ((e + 1 : ℕ) : ℂ) := by push_cast; ring
    rw [e1] at hu2
    change _ * GlobalTheory.LFun.charL _ (G.pl.S0 : Set (HeightOneSpectrum (𝓞 D.host.F))) _ = _ at hu2
    rw [hu2, mul_right_comm, hu1, one_mul]
  have good : ∀ t' ∈ ({t, μ₀} : Set T), GlobalTheory.LFun.IsHecke D.host.F D.host.E (GlobalTheory.SqStep.chs G i j t').ν ∧
      ∀ᶠ w in Filter.cofinite, GlobalTheory.LFun.UnrAt (GlobalTheory.SqStep.chs G i j t').ν w := by
    intro t' ht'
    obtain ⟨⟨om, om', Rf, hm, -⟩, -⟩ := hk t' ht'
    exact nu_good hm.triple.chars
  obtain ⟨gt, ut⟩ := good t (by simp)
  obtain ⟨gμ, uμ⟩ := good μ₀ (by simp)
  obtain ⟨n, hn, hv⟩ := val_quot_pow G hL W S hN i j t
  obtain ⟨𝔟, r, hr, st, sμ⟩ := exists_stepFac_twist Bs (X := GlobalTheory.SqStep.chs G i j t) (Y := GlobalTheory.SqStep.chs G i j μ₀)
    ⟨gt.1.div' gμ.1, fun y => by simp only [MonoidHom.div_apply, gt.2 y, gμ.2 y, div_one]⟩
    ((ut.and uμ).mono fun w hw => by rw [div_eq_mul_inv]; exact hw.1.mul hw.2.inv) hn hv e₁ e₂ s H.𝔟 H'.𝔟 (-(e : ℤ)) (k / k₁)
  have kt := key t (by simp)
  have kμ := key μ₀ (by simp)
  rw [div_self', div_self', Circle.coe_one, mul_one, mul_one] at kμ
  have ek : (((GlobalTheory.SqStep.chs G i j t).ν k / (GlobalTheory.SqStep.chs G i j μ₀).ν k : Circle) : ℂ) =
      (((GlobalTheory.SqStep.chs G i j t).ν (k / k₁) / (GlobalTheory.SqStep.chs G i j μ₀).ν (k / k₁) : Circle) : ℂ) *
        (((GlobalTheory.SqStep.chs G i j t).ν k₁ / (GlobalTheory.SqStep.chs G i j μ₀).ν k₁ : Circle) : ℂ) := by
    rw [← Circle.coe_mul, div_mul_div_comm, ← map_mul, ← map_mul, div_mul_cancel]
  rw [ek] at kt
  have z₀ := Circle.coe_ne_zero ((GlobalTheory.SqStep.chs G i j t).ν (k / k₁) / (GlobalTheory.SqStep.chs G i j μ₀).ν (k / k₁))
  have z₁ := Circle.coe_ne_zero ((GlobalTheory.SqStep.chs G i j t).ν k₁ / (GlobalTheory.SqStep.chs G i j μ₀).ν k₁)
  have nt := mul_ne_zero (mul_ne_zero hd10 z₁) (hc.1 t)
  have nμ : d₁ * c μ₀ ≠ 0 := mul_ne_zero hd10 (hc.1 μ₀)
  rw [← kt] at nt
  rw [← kμ] at nμ
  refine ⟨Bs, e₁, e₂, s, 𝔟, H'.𝔟, hfit, ?_, ?_, right_ne_zero_of_mul (left_ne_zero_of_mul nt),
    right_ne_zero_of_mul (left_ne_zero_of_mul nμ), ?_⟩
  · rw [st]
    exact mul_ne_zero (mul_ne_zero z₀ hr) (right_ne_zero_of_mul (right_ne_zero_of_mul nt))
  · rw [sμ]
    exact mul_ne_zero hr (right_ne_zero_of_mul (right_ne_zero_of_mul nμ))
  · rw [st, sμ]
    refine mul_left_cancel₀ (mul_ne_zero (mul_ne_zero hd0 hC₀) z₁) ?_
    linear_combination (r * c μ₀) * kt -
      (r * c t * (((GlobalTheory.SqStep.chs G i j t).ν k₁ / (GlobalTheory.SqStep.chs G i j μ₀).ν k₁ : Circle) : ℂ)) * kμ
end GlobalTheory.SqStepK
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem _root_.GlobalTheory.T.seesaw_first_reduction_level : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) →
    NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (p q : ℕ) (A A' WW : HSp D) (X : Tri T A A' WW) (lam : T → ℂ) (e : ℕ),
      GlobalTheory.SqTower.IsStageC W i j p (q + 1) X → Factor X W.ψ W.θ lam → A.rank = A'.rank + 2 * e →
      ∃ (B B' WW₁ : HSp D) (Y : Tri T B B' WW₁) (c : T → ℂ), GlobalTheory.SqTower.IsStageC W i j p q Y ∧ Y.IsConst W.ψ W.θ c ∧
        (∀ t, c t ≠ 0) ∧ ∀ t, ∃ (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (e₁ e₂ s : ℤˣ)
          (𝔟 𝔠 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E), GlobalTheory.SqStep.BaseFits G W i j t Bs ∧
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.stepFac Bs (GlobalTheory.SqStep.chs G i j t) e₁ e₂ s 𝔟 𝔠 (-(e : ℤ)) ≠ 0 ∧
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.stepFac Bs (GlobalTheory.SqStep.chs G i j μ₀) e₁ e₂ s 𝔟 𝔠 (-(e : ℤ)) ≠ 0 ∧
          GlobalTheory.LFun.charL (GlobalTheory.SqStep.chs G i j t).ν (G.pl.S0 : Set (HeightOneSpectrum (𝓞 D.host.F))) ((e + 1 : ℕ) : ℂ) ≠ 0 ∧
          GlobalTheory.LFun.charL (GlobalTheory.SqStep.chs G i j μ₀).ν (G.pl.S0 : Set (HeightOneSpectrum (𝓞 D.host.F))) ((e + 1 : ℕ) : ℂ) ≠ 0 ∧
          lam t * GlobalTheory.LFun.charL (GlobalTheory.SqStep.chs G i j t).ν (G.pl.S0 : Set (HeightOneSpectrum (𝓞 D.host.F))) ((e + 1 : ℕ) : ℂ) *
              GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.stepFac Bs (GlobalTheory.SqStep.chs G i j t) e₁ e₂ s 𝔟 𝔠 (-(e : ℤ)) * c μ₀ =
            lam μ₀ * GlobalTheory.LFun.charL (GlobalTheory.SqStep.chs G i j μ₀).ν (G.pl.S0 : Set (HeightOneSpectrum (𝓞 D.host.F))) ((e + 1 : ℕ) : ℂ) *
              GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.stepFac Bs (GlobalTheory.SqStep.chs G i j μ₀) e₁ e₂ s 𝔟 𝔠 (-(e : ℤ)) * c t := by
  first | exact @_root_.GlobalTheory.SqStepK.seesaw_first_reduction | exact _root_.GlobalTheory.SqStepK.seesaw_first_reduction | (intros; apply _root_.GlobalTheory.SqStepK.seesaw_first_reduction <;> assumption)
end
end

section
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
namespace GlobalTheory.SqStep
theorem theta_tower_norm_step_small_rank : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) →
    NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (p q : ℕ) (A A' WW : HSp D) (X : Tri T A A' WW) (lam : T → ℂ) (e : ℕ) (Lf : T → ℂ → ℂ),
      GlobalTheory.SqTower.IsStageC W i j p (q + 1) X → Factor X W.ψ W.θ lam → A.rank = A'.rank + 2 * e →
      (∀ t, IsHeckeL (nuH G t i j) (Lf t)) → ∃ (B B' WW₁ : HSp D) (Y : Tri T B B' WW₁) (c y : T → ℂ),
        GlobalTheory.SqTower.IsStageC W i j p q Y ∧ Y.IsConst W.ψ W.θ c ∧
        (∀ t, y t ≠ 0 ∧ lam t * Lf t ((e + 1 : ℕ) : ℂ) = y t * c t) ∧ ∀ t, GlobalTheory.Square.StepRatio D.what₂.embLL (Qn G t) G.pl.S0 (condExp G.pl) (fun v => Ideal.absNorm v.asIdeal) (y t) (y μ₀) := by
  intro hP hK hM
  refine gbig_three (_root_.GlobalTheory.T.seesaw_first_reduction_level hP hK hM) GlobalTheory.T.thetaStepFactor_ratio_unit_gaussSumQuotient GlobalTheory.T.partialHeckeLFunction_square_eq_primitive ?_
  intro D T Lc sc G μ₀ C x b hk ha hl W S hψ hN i j p q A A' WW X lam e Lf hX hF he hLf
  obtain ⟨B, B', WW₁, Y, c, hY, hc, hc0, H⟩ := hk W S hψ hN i j p q A A' WW X lam e hX hF he
  have he1 : 1 ≤ e := by
    obtain ⟨h1, h2, a1, a2, -⟩ := hX
    have e2 : rankV D (↑i + 1) (↑j + 1) = rankV D ↑i ↑j + D.R.t + sLen D := by simp only [rankV]; ring
    have h3 := D.R.three_m_lt_t
    have hpp : pp D j ≤ D.R.m := by unfold pp; omega
    have hqq : qq D j ≤ D.R.m := by unfold qq; omega
    omega
  have hLeq : ∀ t, GlobalTheory.LFun.charL (chs G i j t).ν (G.pl.S0 : Set (HeightOneSpectrum (𝓞 D.host.F))) ((e + 1 : ℕ) : ℂ) =
      Lf t ((e + 1 : ℕ) : ℂ) := fun t => hl i j t (e + 1) (Lf t) (by omega) (hLf t)
  refine ⟨B, B', WW₁, Y, c, fun t => lam t * Lf t ((e + 1 : ℕ) : ℂ) / c t, hY, hc, fun t => ⟨?_, ?_⟩, fun t => ?_⟩
  · obtain ⟨Bs, e₁, e₂, s, 𝔟, 𝔠, -, -, -, hL0, -, -⟩ := H t
    rw [hLeq t] at hL0
    exact div_ne_zero (mul_ne_zero (hF.1 t) hL0) (hc0 t)
  · rw [div_mul_cancel₀ _ (hc0 t)]
  · obtain ⟨Bs, e₁, e₂, s, 𝔟, 𝔠, hfit, hsf, hsf0, -, -, heq⟩ := H t
    rw [hLeq t, hLeq μ₀] at heq
    obtain ⟨bb, g, g', hb, hg, e3⟩ := ha W S hψ hN i j t Bs e₁ e₂ s 𝔟 𝔠 (-(e : ℤ)) hfit hsf
    refine ⟨bb, g, g', hb, hg, ?_⟩
    have h0 := hc0 μ₀
    have ht := hc0 t
    rw [e3] at heq
    have key := mul_right_cancel₀ hsf (show (lam t * Lf t ((e + 1 : ℕ) : ℂ) * c μ₀) * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.stepFac Bs (chs G i j t) e₁ e₂ s 𝔟 𝔠 (-(e : ℤ)) =
      (D.what₂.embLL (bb * ∏ v ∈ G.pl.S0, ((g v : D.what₂.LL) / (g' v : D.what₂.LL))) * (lam μ₀ * Lf μ₀ ((e + 1 : ℕ) : ℂ)) * c t) *
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.stepFac Bs (chs G i j t) e₁ e₂ s 𝔟 𝔠 (-(e : ℤ)) by linear_combination heq)
    field_simp
    linear_combination key
end GlobalTheory.SqStep
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem _root_.GlobalTheory.T.witt_tower_norm_step_of_small_rank : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) →
    NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (p q : ℕ) (A A' WW : HSp D) (X : Tri T A A' WW) (lam : T → ℂ) (e : ℕ) (Lf : T → ℂ → ℂ),
      GlobalTheory.SqTower.IsStageC W i j p (q + 1) X → Factor X W.ψ W.θ lam → A.rank = A'.rank + 2 * e →
      (∀ t, IsHeckeL (nuH G t i j) (Lf t)) → ∃ (B B' WW₁ : HSp D) (Y : Tri T B B' WW₁) (c y : T → ℂ),
        GlobalTheory.SqTower.IsStageC W i j p q Y ∧ Y.IsConst W.ψ W.θ c ∧
        (∀ t, y t ≠ 0 ∧ lam t * Lf t ((e + 1 : ℕ) : ℂ) = y t * c t) ∧ ∀ t, GlobalTheory.Square.StepRatio D.what₂.embLL (Qn G t) G.pl.S0 (condExp G.pl) (fun v => Ideal.absNorm v.asIdeal) (y t) (y μ₀) := by
  first | exact @_root_.GlobalTheory.SqStep.theta_tower_norm_step_small_rank | exact _root_.GlobalTheory.SqStep.theta_tower_norm_step_small_rank | (intros; apply _root_.GlobalTheory.SqStep.theta_tower_norm_step_small_rank <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.WittTowerTopStageThetaNormFormula
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ExistsGridOfSquareTower
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.ConstRatio (Factor NegIdx)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
namespace GlobalTheory.SqTower.TopGridExists
set_option maxHeartbeats 1000000 in
open GlobalTheory.Grid GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle GlobalTheory.Doubling GlobalTheory.SqTower.TopExists in
theorem square_tower_grid_exists : _root_.GlobalTheory.FunPr.ThetaLocalInputs →
  GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m), ∃ X : TriG G i j, TopGrid W i j X ∧ IsStageC W i j (pp D j) (qq D j) X := by
  intro _
  refine ⟨0, fun _ _ _ => ⟨0, 0, fun C _ D large₂ _ _ _ T Lc μ₀ hL G W i j => ?_⟩⟩
  have hi := i.2
  have hj := j.2
  have a := node_isV G hL (X := .grid (i + 1) (j + 1)) ⟨by omega, by omega⟩
  have a' := node_isV G hL (X := .grid i j) ⟨by omega, by omega⟩
  have b := node_isV G hL (X := .grid i (j + 1)) ⟨by omega, by omega⟩
  have b' := node_isV G hL (X := .grid (i + 1) j) ⟨by omega, by omega⟩
  have ng : ∀ {X : LSp D} {ν q : ℕ}, X.IsV ν q → NegIdx X.sp q := fun h =>
    GlobalTheory.Grid.Vertex.negIdx_of_sig _ _ h.sigOK fun τ => by rw [h.sig, h.rank]
  have ho : ∀ (x : (G.V (.grid i (j + 1))).V) (y : (G.V (.grid (i + 1) j)).V),
      (hsum (G.V (.grid i (j + 1))) (G.V (.grid (i + 1) j))).hD (LinearMap.inl D.host.E _ _ x) (LinearMap.inr D.host.E _ _ y) = 0 :=
    fun x y => by simp [HSpace.hD, orthSum_apply]
  have hsig := sigOK_hsum b.sigOK b'.sigOK
  have hsd := GlobalTheory.Twist.OrthSum.selfDual_hsum b.sd b'.sd
  have hneg := negIdx_of_orth rfl _ _ (isIsomEmb_inl _ _) (isIsomEmb_inr _ _) ho (ng b) (ng b')
  obtain ⟨FA, hFA⟩ := exists_isGridFr W (X := .grid (i + 1) (j + 1)) ⟨by omega, by omega⟩
  obtain ⟨FA', hFA'⟩ := exists_isGridFr W (X := .grid i j) ⟨by omega, by omega⟩
  obtain ⟨FV, hFV⟩ := exists_isGridFr W (X := .grid i (j + 1)) ⟨by omega, by omega⟩
  obtain ⟨FV', hFV'⟩ := exists_isGridFr W (X := .grid (i + 1) j) ⟨by omega, by omega⟩
  obtain ⟨rA, eA, sA, hA⟩ := exists_rig_of_frame FA _ a.sd
  obtain ⟨rA', eA', sA', hA'⟩ := exists_rig_of_frame FA' _ a'.sd
  obtain ⟨rW, eW, sW, hW⟩ := exists_rig_of_frame (frSum FV FV') _ hsd
  have hrk : (hsum (G.V (.grid i (j + 1))) (G.V (.grid (i + 1) j))).rank = rankV D (i + 1) (j + 1) + rankV D i j := by
    have h0 : (hsum (G.V (.grid i (j + 1))) (G.V (.grid (i + 1) j))).rank =
      (G.V (.grid i (j + 1))).rank + (G.V (.grid (i + 1) j)).rank := rfl
    have h1 : (G.V (.grid i (j + 1))).rank = rankV D i (j + 1) := b.rank
    have h2 : (G.V (.grid (i + 1) j)).rank = rankV D (i + 1) j := b'.rank
    rw [h0, h1, h2]; simp only [rankV]; ring
  have htg : ∀ (AV : Fr (G.V (.grid i (j + 1)))) (AV₁ : Fr (G.V (.grid (i + 1) j))), IsGridFr W _ AV → IsGridFr W _ AV₁ →
      rW.s = (frSum AV AV₁).cart := fun AV AV₁ h h₁ => by
    rw [sW]; funext τ
    rw [GlobalTheory.SquareAlg.cart_frSum, GlobalTheory.SquareAlg.cart_frSum, (h τ).2, (h₁ τ).2, (hFV τ).2, (hFV' τ).2]
  have ch := chars G hL W i j
  have hψ := W.ψ_std
  have hθ := W.θ_is
  have hη := GlobalTheory.WeilParts.exists_isEtaTilde_unramified D
  have rA1 : (G.V (.grid (i + 1) (j + 1))).rank = rankV D (i + 1) (j + 1) := a.rank
  have rA2 : (G.V (.grid i j)).rank = rankV D i j := a'.rank
  choose ω hω using fun t => GlobalTheory.ConstRatio.exists_isWeil hψ hη true (G.V (.grid (i + 1) (j + 1))) (hsum (G.V (.grid i (j + 1))) (G.V (.grid (i + 1) j))) (ch t).2.1
    (ch t).2.2.2.1 (by rw [rA1]; exact (ch t).2.2.2.2.2.1) (by rw [hrk]; exact (ch t).2.2.2.2.2.2.2)
  choose ω' hω' using fun t => GlobalTheory.ConstRatio.exists_isWeil hψ hη false (G.V (.grid i j)) (hsum (G.V (.grid i (j + 1))) (G.V (.grid (i + 1) j))) (ch t).1
    (ch t).2.2.1 (by rw [rA2]; exact (ch t).2.2.2.2.1) (by rw [hrk]; exact (ch t).2.2.2.2.2.2.1)
  have hneg' : IsSelfDualC (neg (G.V (.grid (i + 1) (j + 1)))) rA.Λ := by
    refine ⟨hA.1.1, fun y => (hA.1.2 y).trans (forall₂_congr fun x _ => ⟨fun ⟨c, hc⟩ => ⟨-c, ?_⟩, fun ⟨c, hc⟩ => ⟨-c, ?_⟩⟩)⟩
    · simp [neg_gram, hc]
    · simp [neg_gram] at hc ⊢
      exact neg_eq_iff_eq_neg.2 hc
  obtain ⟨vac, hv⟩ := GlobalTheory.VacuumO.vacExists D W.ψ W.θ hψ hθ (neg (G.V (.grid (i + 1) (j + 1)))) (hsum (G.V (.grid i (j + 1))) (G.V (.grid (i + 1) j))) (fun τ => -rA.s τ) rW.s
    (sigOK_sgn true a.sigOK) hsig (fun τ => isCartanInv_sgn true _ τ (hA.2.2 τ).1) (fun τ => (hW.2.2 τ).1) rA.Λ rW.Λ hneg' hW.1
  obtain ⟨vac', hv'⟩ := GlobalTheory.VacuumO.vacExists D W.ψ W.θ hψ hθ (G.V (.grid i j)) (hsum (G.V (.grid i (j + 1))) (G.V (.grid (i + 1) j))) rA'.s rW.s
    a'.sigOK hsig (fun τ => (hA'.2.2 τ).1) (fun τ => (hW.2.2 τ).1) rA'.Λ rW.Λ hA'.1 hW.1
  choose e he using idem_exists G hL W
  choose c hc using fun t w => GlobalTheory.ConstRatio.exists_expAt (nuH G t i j) w
  have hI : ∀ t, (∏ w ∈ locPl G t, w.asIdeal ^ c t w) ≠ ⊥ := fun t =>
    Finset.prod_ne_zero_iff.2 fun w _ => pow_ne_zero _ w.ne_bot
  choose f hf _ using fun t => GlobalTheory.T.first_standard_pair_member_has_theta_function D W.ψ W.θ _ (hsum (G.V (.grid i (j + 1))) (G.V (.grid (i + 1) j))) rA rW _ _ _ _ _ hA hW (ch t).2.2.1 (he t) (hI t) hv
  choose f' hf' _ using fun t =>
    GlobalTheory.T.exists_thetaFunction_standardPairSecond D W.ψ W.θ _ (hsum (G.V (.grid i (j + 1))) (G.V (.grid (i + 1) j))) rA' rW _ _ _ _ (G.V (.grid (i + 1) (j + 1))).rank _ hA' hW (ch t).2.2.1 (he t) (hI t) hv'
  obtain ⟨m, fd, hm⟩ := GlobalTheory.ConstRatio.exists_meas (G.V (.grid (i + 1) (j + 1)))
  obtain ⟨m', fd', hm'⟩ := GlobalTheory.ConstRatio.exists_meas (G.V (.grid i j))
  refine ⟨⟨rA, rA', rW, ω, ω', vac, vac', e, c, f, f', m, fd, m', fd'⟩,
    ⟨eA, eA', eW, sA.trans (funext fun τ => (hFA τ).2), sA'.trans (funext fun τ => (hFA' τ).2), htg⟩,
    le_rfl, le_rfl, by rw [rA1], by rw [rA2], ng a, ng a', hneg,
    ⟨by rw [hrk, rA1, rA2], hA, hA', hW, hω, hω', hv, hv', he, fun t w _ => hc t w, hf, hf', hm, hm'⟩⟩
end GlobalTheory.SqTower.TopGridExists
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.ConstRatio (Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_grid_of_square_tower : _root_.GlobalTheory.FunPr.ThetaLocalInputs →
  GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m), ∃ X : TriG G i j, TopGrid W i j X ∧ IsStageC W i j (pp D j) (qq D j) X := by
  first | exact @_root_.GlobalTheory.SqTower.TopGridExists.square_tower_grid_exists | exact _root_.GlobalTheory.SqTower.TopGridExists.square_tower_grid_exists | (intros; apply _root_.GlobalTheory.SqTower.TopGridExists.square_tower_grid_exists <;> assumption)
end
end

section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.SqTower
theorem theta_tower_top_stage_norm_eq : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) →
    NumbersIn D.what₂.embLL S μ₀ → ∀ (ρ : RealMatch W) (i j : Fin D.R.m), ∃ (A A' WW : HSp D) (X : Tri T A A' WW) (c κ : T → ℂ),
      GlobalTheory.SqTower.IsStageC W i j (pp D j) (qq D j) X ∧ X.IsConst W.ψ W.θ c ∧
      (∀ t, κ t ≠ 0 ∧ ∃ ζ : D.what₂.LL, GlobalTheory.Square.IsAwayUnit (Qn G t) ζ ∧ κ t = D.what₂.embLL ζ * κ μ₀) ∧
      ∀ (t : T) (c' : ℂ), SquareNonzero W S.B ρ t i j → IsSquareConst W S.B ρ t i j c' → c' = κ t * c t := by
  intro hP hK hM
  refine gBig_of₃ (_root_.GlobalTheory.T.exists_grid_of_square_tower hP) (_root_.GlobalTheory.T.exists_factor_of_isStageC hP hK hM) (_root_.GlobalTheory.T.theta_square_norm_comparison hP hK hM) ?_
  intro D T Lc sc G μ₀ C x b hex hfac hcmp W S hstd hN ρ i j
  obtain ⟨X, hT, hX⟩ := hex W i j
  obtain ⟨lam, hl⟩ := hfac W S hstd hN i j (pp D j) (qq D j) _ _ _ X hX
  obtain ⟨κ, hκ, hc⟩ := hcmp W S hstd hN ρ i j X lam hT hX hl
  haveI : Nonempty T := ⟨μ₀⟩
  exact ⟨_, _, _, X, lam, κ, hX, hl.isConst, hκ, hc⟩
end GlobalTheory.SqTower
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.witt_tower_top_stage_theta_norm_formula : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) →
    NumbersIn D.what₂.embLL S μ₀ → ∀ (ρ : RealMatch W) (i j : Fin D.R.m), ∃ (A A' WW : HSp D) (X : Tri T A A' WW) (c κ : T → ℂ),
      GlobalTheory.SqTower.IsStageC W i j (pp D j) (qq D j) X ∧ X.IsConst W.ψ W.θ c ∧
      (∀ t, κ t ≠ 0 ∧ ∃ ζ : D.what₂.LL, GlobalTheory.Square.IsAwayUnit (Qn G t) ζ ∧ κ t = D.what₂.embLL ζ * κ μ₀) ∧
      ∀ (t : T) (c' : ℂ), SquareNonzero W S.B ρ t i j → IsSquareConst W S.B ρ t i j c' → c' = κ t * c t := by
  first | exact @_root_.GlobalTheory.SqTower.theta_tower_top_stage_norm_eq | exact _root_.GlobalTheory.SqTower.theta_tower_top_stage_norm_eq | (intros; apply _root_.GlobalTheory.SqTower.theta_tower_top_stage_norm_eq <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.WittTowerConstantRatioEqBottom
section
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
namespace GlobalTheory.SqTower
theorem theta_tower_bottom_constant_ratio : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) →
    NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (A A' WW : HSp D) (X : Tri T A A' WW) (B B' WW₁ : HSp D) (Y : Tri T B B' WW₁) (c : T → ℂ),
      IsBottomTri W i j X → GlobalTheory.SqTower.IsStageC W i j 0 0 Y → Y.IsConst W.ψ W.θ c → ∃ v : T → ℂ,
        X.IsConst W.ψ W.θ (fun t => v t * c t) ∧
        ∀ t, v t ≠ 0 ∧ ∃ ζ : D.what₂.LL, GlobalTheory.Square.IsAwayUnit (Qn G t) ζ ∧ v t = D.what₂.embLL ζ * v μ₀ := by
  intro _ _ _
  refine ⟨0, fun ε CF _ => ⟨0, 0, fun C _ D large₂ _ _ _ T Lc μ₀ hμ G => ?_⟩⟩
  intro W S _ hN i j A A' WW X B B' WW₁ Y c hX hY hc
  obtain ⟨Y₁, hY₁, hc₁⟩ := GlobalTheory.T.definiteBottom_stage_transport_same_constants W i j X Y hX hY
  obtain ⟨Z₁, v₁, hZ₁, e1, e2, e3, hv₁, hc₂⟩ := GlobalTheory.T.definiteBottom_lattice_change_constants_awayUnit μ₀ hμ W S hN i j X Y₁ hX hY₁
  obtain ⟨Z₂, v₂, hZ₂, f1, f2, f3, f4, f5, f6, hv₂, hc₃⟩ := GlobalTheory.T.definiteBottom_framesChange_stageZero μ₀ hμ W S hN i j X Z₁ hX hZ₁ e1 e2 e3
  obtain ⟨κ, hκ, hX'⟩ := GlobalTheory.T.definiteBottom_tower_constants_differ_by_factor W i j X Z₂ hX hZ₂ f1 f2 f3 f4 f5 f6 _ (hc₃ _ (hc₂ _ (hc₁ c hc)))
  refine ⟨fun t => κ * (v₂ t * v₁ t), ?_, fun t => ?_⟩
  · convert hX' using 2 with t
    ring
  · obtain ⟨h1, ζ₁, u₁, q₁⟩ := hv₁ t
    obtain ⟨h2, ζ₂, u₂, q₂⟩ := hv₂ t
    refine ⟨mul_ne_zero hκ (mul_ne_zero h2 h1), ζ₂ * ζ₁, u₂.mul u₁, ?_⟩
    show κ * (v₂ t * v₁ t) = _ * (κ * (v₂ μ₀ * v₁ μ₀))
    rw [q₁, q₂, map_mul]
    ring
end GlobalTheory.SqTower
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.witt_tower_constant_ratio_eq_bottom : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) →
    NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (A A' WW : HSp D) (X : Tri T A A' WW) (B B' WW₁ : HSp D) (Y : Tri T B B' WW₁) (c : T → ℂ),
      IsBottomTri W i j X → GlobalTheory.SqTower.IsStageC W i j 0 0 Y → Y.IsConst W.ψ W.θ c → ∃ v : T → ℂ,
        X.IsConst W.ψ W.θ (fun t => v t * c t) ∧
        ∀ t, v t ≠ 0 ∧ ∃ ζ : D.what₂.LL, GlobalTheory.Square.IsAwayUnit (Qn G t) ζ ∧ v t = D.what₂.embLL ζ * v μ₀ := by
  first | exact @_root_.GlobalTheory.SqTower.theta_tower_bottom_constant_ratio | exact _root_.GlobalTheory.SqTower.theta_tower_bottom_constant_ratio | (intros; apply _root_.GlobalTheory.SqTower.theta_tower_bottom_constant_ratio <;> assumption)
end
end

section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.SqTower
section Units
variable {K : Type} [Field K] [NumberField K] [StarRing K]
end Units
section Descent
variable {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData Lc sc} {W : G.Weil} {μ₀ : T}
end Descent
end GlobalTheory.SqTower
namespace GlobalTheory.SqTower
open GlobalTheory.SqTower
theorem tower_alt_bis : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → LNe → Tower := by
  intro hP hK hM hL
  have H := gbig_and (_root_.GlobalTheory.T.witt_tower_top_stage_theta_norm_formula hP hK hM) (gbig_and (_root_.GlobalTheory.T.exists_factor_of_isStageC hP hK hM) (gbig_and (_root_.GlobalTheory.T.witt_tower_norm_step_of_small_rank hP hK hM)
    (gbig_and (_root_.GlobalTheory.T.witt_tower_norm_step_of_large_rank hP hK hM) (gbig_and (_root_.GlobalTheory.T.witt_tower_constant_ratio_eq_bottom hP hK hM) hL))))
  unfold Tower
  refine gbig_mono H ?_
  intro D T Lc sc G μ₀ C x b hμ hQ
  obtain ⟨htop, hfac, hsm, hbig, hbot, hlne⟩ := hQ
  intro W S ρ hψ hN i j t c c₀ A A' WW X c0 Λ Λ₀ hnz hc hnz₀ hc₀ hX hc0 hΛ hΛ₀
  choose Lf hLf using (hlne i j).1
  have eΛ : Λ = Lf t := hΛ.unique (hLf t).1
  have eΛ₀ : Λ₀ = Lf μ₀ := hΛ₀.unique (hLf μ₀).1
  subst eΛ eΛ₀
  have rk := ranks_exact D i j
  obtain ⟨u1, hu1⟩ := D.R.t_odd
  obtain ⟨v1, hv1⟩ := odd_sLen D
  have e2 : rankV D (↑i + 1) (↑j + 1) = rankV D ↑i ↑j + D.R.t + sLen D := by simp only [rankV]; ring
  have h3 := D.R.three_m_lt_t
  have hm : D.R.m ≤ rankV D ↑i ↑j := by
    have := D.R.m_add_three_le_k
    simp only [rankV]; unfold Ranks.r; omega
  have hpp : pp D j ≤ D.R.m := by unfold pp; omega
  have hqq : qq D j ≤ D.R.m := by unfold qq; omega
  have hpe : pp D j ≤ eTop D i j := by unfold eTop; omega
  have hqh : eTop D i j + qq D j ≤ halfRank D i j := by unfold eTop; omega
  obtain ⟨A1, A1', WW1, X1, ct, κT, hst, hct, hκT, hsq⟩ := htop W S hψ hN ρ i j
  have ec := hsq t c hnz hc
  have ec₀ := hsq μ₀ c₀ hnz₀ hc₀
  obtain ⟨lamT, hlamT⟩ := hfac W S hψ hN i j _ _ A1 A1' WW1 X1 hst
  obtain ⟨κ1, hκ1, e1⟩ := hlamT.eq_mul hct
  have hct0 : ∀ t, ct t ≠ 0 := fun t => by rw [e1 t]; exact mul_ne_zero hκ1 (hlamT.1 t)
  have hrk : A1.rank = A1'.rank + 2 * eTop D i j := by
    obtain ⟨-, -, a1, a2, -⟩ := hst
    unfold eTop; omega
  obtain ⟨B, B', W₁, Y, cY, u, κ, hY, hcY, hκ, hu, hid⟩ := descent (W := W) (μ₀ := μ₀) (hfac W S hψ hN)
    (hsm W S hψ hN) (hbig W S hψ hN) i j Lf (fun t => (hLf t).1) (qq D j) (pp D j) (eTop D i j) X1 ct hst hct hrk hpe
  obtain ⟨v, hv, hvr⟩ := hbot W S hψ hN i j A A' WW X B B' W₁ Y cY hX hY hcY
  obtain ⟨lam0, hlam0⟩ := hfac W S hψ hN i j 0 0 A A' WW X (IsBottomTri.isStageC hX)
  obtain ⟨a, ha, ea⟩ := hlam0.eq_mul hc0
  obtain ⟨b', hb', eb⟩ := hlam0.eq_mul hv
  have ec0 : ∀ t, c0 t = a / b' * (v t * cY t) := fun t => by
    rw [ea t, eb t]; field_simp
  have hLne : ∀ n : ℕ, 1 ≤ n → n ≤ halfRank D i j → Lf μ₀ (n : ℂ) ≠ 0 := fun n h1 h2 => by
    have := (hLf μ₀).2 (n : ℤ) (by omega) (by exact_mod_cast h2)
    rwa [Int.cast_natCast] at this
  have hP0 : ∏ k ∈ range (qq D j), Lf μ₀ ((eTop D i j + k + 1 : ℕ) : ℂ) ≠ 0 :=
    prod_ne_zero_iff.2 fun k hk => hLne _ (by omega) (by rw [mem_range] at hk; omega)
  have hP0' : ∏ k ∈ range (pp D j), Lf μ₀ ((eTop D i j + qq D j - k : ℕ) : ℂ) ≠ 0 :=
    prod_ne_zero_iff.2 fun k hk => by rw [mem_range] at hk; exact hLne _ (by omega) (by omega)
  have hU0 : ∏ k ∈ range (pp D j + qq D j), u k μ₀ ≠ 0 := prod_ne_zero_iff.2 fun k _ => (hu k μ₀).1
  have hcY0 : cY μ₀ ≠ 0 := fun h0 => by
    have := hid μ₀
    rw [h0, mul_zero, zero_mul] at this
    exact mul_ne_zero (hct0 μ₀) hP0 this
  have hκT0 := (hκT μ₀).1
  have hv0 := (hvr μ₀).1
  obtain ⟨-, ζT, hζT, eκT⟩ := hκT t
  obtain ⟨hvt, ζv, hζv, ev⟩ := hvr t
  have hζv0 : ζv ≠ 0 := fun h0 => hvt (by rw [ev, h0, map_zero, zero_mul])
  have hσv : D.what₂.embLL ζv ≠ 0 := (map_ne_zero _).2 hζv0
  refine ⟨fun k => u k t / u k μ₀, fun k => stepRatio_div (hu k t).2 (hu k μ₀).1, ζT * ζv⁻¹,
    hζT.mul (isAwayUnit_inv hζv hζv0), ?_⟩
  rw [Fin.prod_univ_eq_prod_range (fun k => u k t / u k μ₀), prod_div_distrib, prod_div_distrib, prod_div_distrib,
    map_mul, map_inv₀, ec0, ec0]
  have L1 : c / c₀ * ((∏ k ∈ range (qq D j), Lf t ((eTop D i j + k + 1 : ℕ) : ℂ)) /
      ∏ k ∈ range (qq D j), Lf μ₀ ((eTop D i j + k + 1 : ℕ) : ℂ)) =
      κT t / κT μ₀ * ((ct t * ∏ k ∈ range (qq D j), Lf t ((eTop D i j + k + 1 : ℕ) : ℂ)) /
        (ct μ₀ * ∏ k ∈ range (qq D j), Lf μ₀ ((eTop D i j + k + 1 : ℕ) : ℂ))) := by
    rw [ec, ec₀]
    have := hct0 μ₀
    field_simp
  rw [L1, hid t, hid μ₀, eκT, ev]
  field_simp
end GlobalTheory.SqTower
end
end

section
open GlobalTheory.SqTop
theorem _root_.GlobalTheory.T.tower_of_theta_matching_lNe : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → LNe → Tower := by
  first | exact @_root_.GlobalTheory.SqTower.tower_alt_bis | exact _root_.GlobalTheory.SqTower.tower_alt_bis | (intros; apply _root_.GlobalTheory.SqTower.tower_alt_bis <;> assumption)
end
