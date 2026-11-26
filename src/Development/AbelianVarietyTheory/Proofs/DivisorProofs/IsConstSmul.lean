module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomExistsIntegrable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsParallelWeightInvertibleSection
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolarizationSectionBasisPullbackAffine
public import Development.AbelianVarietyTheory.Definitions.Divisors.MulVecEqOfBasis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightOfSizeBound
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateTopBoundOfInputs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentKummerCupProductBijectiveStrictlyHenselia

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConstSmul
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BotTransfer

variable {D : D7} {T : Type} {A A' WW : HSp D}

theorem ker_smul (X : Tri T A A' WW) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (t : T) (κ : ℂ)
    (P : PolF D WW.rank A.rank) (h : GA D WW) (g : GA D A) :
    X.ker ψ θ t (κ • P) h g = κ * X.ker ψ θ t P h g := by
  simp only [Tri.ker, thetaKO, map_smul, Pi.smul_apply, smul_eq_mul]

theorem isConst_smul {X : Tri T A A' WW} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {c : T → ℂ}
    (h : X.IsConst ψ θ c) {κ : ℂ} (hκ : κ ≠ 0) : X.IsConst ψ θ fun t => κ * c t := by
  obtain ⟨⟨t₁, h₁⟩, P, P', H⟩ := h
  refine ⟨⟨t₁, mul_ne_zero hκ h₁⟩, κ • P, P', fun t => ⟨fun g => ⟨?_, ((H t).1 g).2⟩, (H t).2.1, fun g => ?_⟩⟩
  · have := ((H t).1 g).1.const_mul κ
    have e : X.ker ψ θ t (κ • P) g = fun x => κ * X.ker ψ θ t P g x := funext fun x => ker_smul X ψ θ t κ P g x
    rw [IntegrableOn, e]
    exact this
  · have e : X.I ψ θ t (κ • P) g = κ * X.I ψ θ t P g := by
      simp only [Tri.I, ker_smul, MeasureTheory.integral_const_mul]
    rw [e, (H t).2.2 g, mul_assoc]

end GlobalTheory.BotTransfer
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomTorsionFree
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomTorsionFree
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem hom_torsionFree : ∀ (K : Type) [Field K] (A B : AbVar K) (n : ℤ) (f : A ⟶ B), n ≠ 0 → n • f = 0 → f = 0 := by
  intro K _ A B n f hn h
  have hs := (GlobalTheory.T.abelianVariety_intCast_smul_isogeny_degree K A n hn).1.2
  refine GlobalTheory.T.cancel_of_surjective_abelianVarietyHom K A A (n • 𝟙 A) hs B f 0 ?_
  rw [Preadditive.zsmul_comp, Category.id_comp, Limits.comp_zero, h]

end GlobalTheory.AV.AbVar
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomTorsionFreeStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abVar_hom_eq_zero_of_nsmul_eq_zero : ∀ (K : Type) [Field K] (A B : AbVar K) (n : ℤ) (f : A ⟶ B), n ≠ 0 → n • f = 0 → f = 0 := by
  first | exact @GlobalTheory.AV.AbVar.hom_torsionFree | exact GlobalTheory.AV.AbVar.hom_torsionFree | (intros; apply GlobalTheory.AV.AbVar.hom_torsionFree <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardTorsionGeometricPointsEqPowTwoDim
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardTorsionGeometricPointsEqPowTwoDim
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem comp_pow_id_torscard {S : Scheme.{0}} {G T : Over S} [GrpObj G] (x : T ⟶ G) (n : ℕ) :
    x ≫ (𝟙 G) ^ n = x ^ n := by
  induction n with
  | zero => simp [MonObj.comp_one]
  | succ k ih => rw [pow_succ, MonObj.comp_mul, ih, Category.comp_id, pow_succ]

theorem card_torsion_pt (K : Type) [Field K] (A : AbVar K) (n : ℕ) (hn : (n : K) ≠ 0) :
    Nat.card {x : A.Pt // x ^ n = 1} = n ^ (2 * A.dim) := by
  have hn0 : (n : ℤ) ≠ 0 := by
    intro h; apply hn; simp at h; simp [h]
  obtain ⟨hiso, hdeg⟩ := GlobalTheory.T.abelianVariety_intCast_smul_isogeny_degree K A (n : ℤ) hn0
  have hf : ((n : ℤ) • 𝟙 A).hom = (𝟙 A.X) ^ n := by
    rw [natCast_zsmul, nsmul_hom, id_hom]
  have hker : ∀ {T : Over (Sp K)} (x : T ⟶ A.X), x ≫ ((n : ℤ) • 𝟙 A).hom = x ^ n := by
    intro T x; rw [hf, comp_pow_id_torscard]
  have hd := GlobalTheory.T.isogenyDegree_eq_card_kernel_of_killed_by_invertible K A A ((n : ℤ) • 𝟙 A) n hn hiso (fun T x hx => by rw [← hker]; exact hx)
  rw [hdeg, Int.natAbs_natCast] at hd
  rw [hd]
  apply Nat.card_congr
  exact Equiv.subtypeEquivRight (fun x => by rw [MonoidHom.mem_ker, ptMap_apply, hker])

end GlobalTheory.AV.AbVar
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardTorsionGeometricPointsEqPowTwoDimStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_torsion_geometricPoints_eq_pow_two_dim : ∀ (K : Type) [Field K] (A : AbVar K) (n : ℕ), (n : K) ≠ 0 → Nat.card {x : A.Pt // x ^ n = 1} = n ^ (2 * A.dim) := by
  first | exact @GlobalTheory.AV.AbVar.card_torsion_pt | exact GlobalTheory.AV.AbVar.card_torsion_pt | (intros; apply GlobalTheory.AV.AbVar.card_torsion_pt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBottomTriIs
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

noncomputable section
namespace GlobalTheory.BottomIPData

variable {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts}

def alphaB (L : LevCh D T) (i j : Fin D.R.m) (t : T) : (AE D)ˣ →* Circle := L.mu t (j + 1) * L.eta ^ (rankV D i j % 2)

def betaB (G : GridData L sc) (i j : Fin D.R.m) : (AE D)ˣ →* Circle := G.ch.chi (D.R.m - i) * L.eta ^ (rankV D i j % 2)


open Classical in
def sfB (G : GridData L sc) (t : T) : Finset (GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.FinPl D) :=
  (locPl G t).image fun w => w.under (𝓞 D.host.F)

theorem isBottomTri_is {G : GridData L sc} {W : G.Weil} {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}
    (h : IsBottomTri W i j X) :
    X.Is W.ψ W.θ (alphaB L i j) (fun _ => betaB G i j) (fun t => SqNum.nuH G t i j) (locPl G) := h.is

theorem gbig_mono {Q Q' : GP} (h : GBig Q) (H : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts}
    (G : GridData Lc sc) (μ₀ : T) (C x b : ℝ), Q G μ₀ C x b → Q' G μ₀ C x b) : GBig Q' := by
  obtain ⟨CF0, h⟩ := h
  refine ⟨CF0, fun ε CF hCF => ?_⟩
  obtain ⟨C0, x₀, h⟩ := h ε CF hCF
  exact ⟨C0, x₀, fun C hC D large₂ he hx hR T Lc μ₀ hL G => H _ _ _ _ _ (h C hC D large₂ he hx hR T Lc μ₀ hL G)⟩

theorem gbig_and {Q Q' : GP} (h : GBig Q) (h' : GBig Q') : GBig fun G μ₀ C x b => Q G μ₀ C x b ∧ Q' G μ₀ C x b := by
  obtain ⟨CF0, h⟩ := h
  obtain ⟨CF0', h'⟩ := h'
  refine ⟨max CF0 CF0', fun ε CF hCF => ?_⟩
  obtain ⟨C0, x₀, h⟩ := h ε CF (le_of_max_le_left hCF)
  obtain ⟨C0', x₀', h'⟩ := h' ε CF (le_of_max_le_right hCF)
  exact ⟨max C0 C0', max x₀ x₀', fun C hC D large₂ he hx hR T Lc μ₀ hL G =>
    ⟨h C (le_of_max_le_left hC) D large₂ he (le_of_max_le_left hx) hR T Lc μ₀ hL G,
      h' C (le_of_max_le_right hC) D large₂ he (le_of_max_le_right hx) hR T Lc μ₀ hL G⟩⟩

end GlobalTheory.BottomIPData
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilRepDualPairCharactersBetaQuotient
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilRepDualPairCharactersBetaQuotient
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.WeilTripleW

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

end GlobalTheory.WeilTripleW

theorem GlobalTheory.WeilTripleW.exists_isWeil : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (_hL : L.Is μ₀) (t : T)
    (i j : Fin D.R.m), SquareStanding G t → ∀ (B : Base D.host.F D.host.E), B.IsGood D.sp.cm.sig →
    ∀ (X : Spc D.host.F D.host.E (spW G i j).rank) (Y : Spc D.host.F D.host.E ((spW G i j).rank + (spW₁ G i j).rank))
      (r s r' s' : ℕ), X.IsHerm D.sp.cm.sig B r s → Y.IsSkew D.sp.cm.sig B r' s' →
      ∀ Mo : Model D.sp.cm.sig X Y, Mo.IsGood B.ψ →
      ∃ om, Mo.IsWeil B.ψ (beta G i j) (beta G i j / alpha G t i j) om := by
  intro D T L sc G μ₀ hL t i j hS B hB X Y r s r' s' hX hY Mo hMo
  obtain ⟨hb, ha, rb, ra⟩ := GlobalTheory.SquareChars.square_chars hL t i j hS
  exact GlobalTheory.T.exists_adelicWeilRep_unitaryPair_schroedingerModel D B hB _ _ X Y r s r' s' hX hY Mo hMo
    (beta G i j) (beta G i j / alpha G t i j) hb (GlobalTheory.WeilTripleW.isHecke_div hb ha) rb
    (GlobalTheory.WeilTripleW.resEtaPow_div rb ra)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilRepDualPairCharactersBetaQuotientStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_weilRep_dualPair_characters_beta_quotient : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (_hL : L.Is μ₀) (t : T)
    (i j : Fin D.R.m), SquareStanding G t → ∀ (B : Base D.host.F D.host.E), B.IsGood D.sp.cm.sig →
    ∀ (X : Spc D.host.F D.host.E (spW G i j).rank) (Y : Spc D.host.F D.host.E ((spW G i j).rank + (spW₁ G i j).rank))
      (r s r' s' : ℕ), X.IsHerm D.sp.cm.sig B r s → Y.IsSkew D.sp.cm.sig B r' s' →
      ∀ Mo : Model D.sp.cm.sig X Y, Mo.IsGood B.ψ →
      ∃ om, Mo.IsWeil B.ψ (beta G i j) (beta G i j / alpha G t i j) om := by
  first | exact @GlobalTheory.WeilTripleW.exists_isWeil | exact GlobalTheory.WeilTripleW.exists_isWeil | (intros; apply GlobalTheory.WeilTripleW.exists_isWeil <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaEV0EqICPqRows
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.L2 Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Indef Formalism.IndefR.Cx GlobalTheory.BigTop GlobalTheory.BigTop.Fun
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BigTop.Fun

open _root_.Formalism.L2.DIV Formalism.IndefR.Cx Formalism.IndefR.Cx.CxData
open scoped InnerProductSpace Matrix

theorem iC_cpt_eq_theta_toR {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A)
    {fc : DefSub A → DefFace Bs} (cr : Crd A fc) (b : Bool) (t : Bs.Tup) (z : Fin ((lv (fc X.zs) b).dQ t) → K) :
    X.iC cr b t (cpt Bs.v0.embedding z) = X.Θ t (X.jR t (cr.toR X.zs b t z)) := by
  conv_rhs => rw [pi_eq_sum_univ z]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, LinearMap.map_smulₛₗ, iC, lin, Fintype.linearCombination_apply, cpt]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 4
  ext j
  simp [Pi.single_apply, eq_comm]

theorem theta_jR_eq_zero_of_perp {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A)
    (cv : CrdV A) (hJ : X.JIsoR cv) (hZ : X.RatZ) (t : Bs.Tup) (x : A.FR t) (hx : ∀ w ∈ X.Z t, cv.hR t w x = 0) :
    X.Θ t (X.jR t x) = 0 := by
  have hperp : ∀ m ∈ Submodule.span ℂ ((X.jR t) '' (X.Z t : Set (A.FR t))), ⟪m, X.jR t x⟫_ℂ = 0 := by
    intro m hm
    induction hm using Submodule.span_induction with
    | mem m hm =>
      obtain ⟨w, hw, rfl⟩ := hm
      rw [hJ t w x, hx w hw, map_zero]
    | zero => exact inner_zero_left _
    | add a b _ _ ha hb => rw [inner_add_left, ha, hb, add_zero]
    | smul c a _ ha => rw [inner_smul_left, ha, mul_zero]
  refine ext_inner_left ℂ fun e => ?_
  rw [inner_zero_right, ← LinearMap.adjoint_inner_left]
  apply hperp
  rw [hZ.1 t]
  exact LinearMap.mem_range_self _ _

theorem sub_zE_Pq_mem_U {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type}
    (B : BlockDat K G Pl0) (ℓ : Lvl K G) (Z : Submodule K B.S.Forms) (hs : Function.Surjective (B.Pq ℓ Z).mulVec)
    (y : Fin (B.nV ℓ) → K) : y - (B.zE ℓ Z).mulVec ((B.Pq ℓ Z).mulVec y) ∈ B.U ℓ Z := by
  set E := B.zE ℓ Z with hE
  set H := B.HV ℓ with hH
  have hdet : IsUnit (Eᴴ * H * E).det := by
    by_contra hu
    have h0 : B.Pq ℓ Z = 0 := by
      show (Eᴴ * H * E)⁻¹ * (Eᴴ * H) = 0
      rw [Matrix.nonsing_inv_apply_not_isUnit _ hu, Matrix.zero_mul]
    apply hu
    have hd : B.dZ ℓ Z = 0 := by
      by_contra hne
      obtain ⟨i⟩ : Nonempty (Fin (B.dZ ℓ Z)) := ⟨⟨0, Nat.pos_of_ne_zero hne⟩⟩
      obtain ⟨x, hx⟩ := hs (Pi.single i 1)
      rw [h0, Matrix.zero_mulVec] at hx
      have := congrFun hx i
      simp at this
    have : IsEmpty (Fin (B.dZ ℓ Z)) := ⟨fun i => by have := i.2; omega⟩
    rw [Matrix.det_isEmpty]
    exact isUnit_one
  have hO := (Formalism.DivisionValues.exponent_index_lattice.isOrthProj_formula H E hdet).2
  intro z hz
  obtain ⟨c, rfl⟩ : ∃ c, E.mulVec c = z := by
    have h := (Formalism.L2.DIV.subspace_image_spec K _ (B.Z0 ℓ Z)).2
    have : z ∈ LinearMap.range (subE (B.Z0 ℓ Z)).mulVecLin := by rw [h]; exact hz
    obtain ⟨c, hc⟩ := this
    exact ⟨c, hc⟩
  rw [Formalism.DivisionValues.RationalHermitianForm.hform_eq_dot, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec]
  have : Eᴴ *ᵥ (H *ᵥ (y - E *ᵥ (B.Pq ℓ Z *ᵥ y))) = (Eᴴ * H * (1 - E * B.Pq ℓ Z)) *ᵥ y := by
    simp only [Matrix.mulVec_sub, Matrix.mul_sub, Matrix.sub_mulVec, Matrix.mulVec_mulVec, Matrix.mul_one, Matrix.mul_assoc]
  rw [this]
  show star c ⬝ᵥ (Eᴴ * H * (1 - E * ((Eᴴ * H * E)⁻¹ * (Eᴴ * H)))) *ᵥ y = 0
  rw [hO, Matrix.zero_mulVec, dotProduct_zero]

theorem csum_goodPart_perp_eq_zero {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type}
    (B : BlockDat K G Pl0) (s : ℕ) (hB : B.Ok s) (v0 : InfinitePlace K) (hv : Formalism.DivisionValues.IsConjAt v0) (ℓ : Lvl K G)
    (hX : ∀ χ ∈ ℓ.X, IsAbsIrrChar χ) (Z : Submodule K B.S.Forms) (hZ : ∀ g, Z ≤ Z.comap (B.r g))
    (u : Fin (B.nV ℓ) → K) (hu : u ∈ B.U ℓ Z) (w : B.S.Forms) (hw : w ∈ Z) :
    B.S.csum (w : B.S.Cl → B.S.V) ((B.S.basis.equivFun.symm ((B.vE ℓ).mulVec u) : B.S.Forms) : B.S.Cl → B.S.V) = 0 := by
  classical
  have hpe := good_at_spec K v0 hv G ℓ.X hX ℓ.P ℓ.ψ
  obtain ⟨hO, hEP⟩ := orthogonal_projection_spec K v0 hv B.S (hB.hpos v0) G B.r hB.act _ hpe.idem hpe.selfAdj
  have hadj := group_action_matrix_adjoint K B.S G B.r hB.act (goodAt ℓ.X ℓ.P ℓ.ψ)
  rw [hpe.selfAdj] at hadj
  have hE : B.vE ℓ = B.S.cutE B.r (goodAt ℓ.X ℓ.P ℓ.ψ) := rfl
  set Gm := B.S.gaMat B.r (goodAt ℓ.X ℓ.P ℓ.ψ) with hGm
  set E := B.vE ℓ with hEdef
  set x := B.S.basis.equivFun w with hx
  have hw' : (w : B.S.Cl → B.S.V) = B.S.I x := by simp [CSD.I, x]
  have hv' : ((B.S.basis.equivFun.symm (E.mulVec u) : B.S.Forms) : B.S.Cl → B.S.V) = B.S.I (E.mulVec u) := rfl
  rw [hw', hv', CSD.csum_sum, ← Formalism.DivisionValues.RationalHermitianForm.hform_apply]
  have hGE : Gm *ᵥ (E *ᵥ u) = E *ᵥ u := by
    have hO1 : B.S.cutPr B.r (goodAt ℓ.X ℓ.P ℓ.ψ) * E = 1 := hO.1
    rw [← hEP, Matrix.mulVec_mulVec, ← hE, Matrix.mul_assoc, hO1, Matrix.mul_one]
  rw [← hGE]
  have hmove : Formalism.DivisionValues.hform B.S.H x (Gm *ᵥ (E *ᵥ u)) = Formalism.DivisionValues.hform B.S.H (Gm *ᵥ x) (E *ᵥ u) := by
    rw [Formalism.DivisionValues.RationalHermitianForm.hform_eq_dot, Formalism.DivisionValues.RationalHermitianForm.hform_eq_dot, Matrix.mulVec_mulVec, ← hadj,
      ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.star_mulVec]
  set z' := B.S.cutPr B.r (goodAt ℓ.X ℓ.P ℓ.ψ) *ᵥ x with hz'def
  have hGx : Gm *ᵥ x = E *ᵥ z' := by rw [← hEP, ← Matrix.mulVec_mulVec, hE]
  have hz' : z' ∈ B.Z0 ℓ Z := by
    show (E.mulVecLin z') ∈ B.coord Z
    rw [Matrix.mulVecLin_apply, ← hGx]
    refine ⟨B.S.gaOp B.r (goodAt ℓ.X ℓ.P ℓ.ψ) w, ?_, ?_⟩
    · show (B.S.gaOp B.r (goodAt ℓ.X ℓ.P ℓ.ψ) w) ∈ Z
      simp only [CSD.gaOp, LinearMap.sum_apply, LinearMap.smul_apply]
      exact Submodule.sum_mem _ fun t _ => Submodule.smul_mem _ _ (hZ t hw)
    set_option synthInstance.maxHeartbeats 100000 in
      · simp only [CSD.gaOp, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, hGm,
        CSD.gaMat, Matrix.sum_mulVec, Matrix.smul_mulVec]
        refine Finset.sum_congr rfl fun t _ => ?_
        congr 1
        show B.S.basis.equivFun (B.r t w) = (LinearMap.toMatrix B.S.basis B.S.basis (B.r t)) *ᵥ (B.S.basis.equivFun w)
        rw [Module.Basis.equivFun_apply, Module.Basis.equivFun_apply, LinearMap.toMatrix_mulVec_repr]
  rw [hmove, hGx, ← Formalism.L2.DIV.hform_cut]
  have hP : (Nat.card ℓ.P : K) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hH : Eᴴ * B.S.H * E = (Nat.card ℓ.P : K) • B.HV ℓ := by
    simp only [hEdef, BlockDat.HV, BlockDat.vE, CSD.goodPartHermitianForm, CSD.cutH, CSD.V0E, smul_smul, mul_inv_cancel₀ hP, one_smul]
  rw [hH, Formalism.DivisionValues.RationalHermitianForm.hform_eq_dot, Matrix.smul_mulVec, dotProduct_smul, ← Formalism.DivisionValues.RationalHermitianForm.hform_eq_dot,
    hu z' hz', smul_zero]


end GlobalTheory.BigTop.Fun

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricPointsDivisible
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem pt_comp_id_pow {K : Type} [Field K] (A : AbVar K) (x : A.Pt) (n : ℕ) :
    x ≫ (𝟙 A.X) ^ n = x ^ n := by
  induction n with
  | zero => simp [MonObj.comp_one]
  | succ k ih => rw [pow_succ, MonObj.comp_mul, ih, Category.comp_id, pow_succ]

theorem pt_divisible : ∀ (K : Type) [Field K] (A : AbVar K) (n : ℕ), n ≠ 0 → ∀ x : A.Pt, ∃ y : A.Pt, y ^ n = x := by
  intro K _ A n hn x
  have hz : ((n : ℤ)) ≠ 0 := by exact_mod_cast hn
  have hiso := (GlobalTheory.T.abelianVariety_intCast_smul_isogeny_degree K A (n : ℤ) hz).1
  have hs : Function.Surjective (ptMap ((n : ℤ) • 𝟙 A)) := (GlobalTheory.T.abVar_surjective_iff_ptMap_surjective K A A _).1 hiso.2
  obtain ⟨y, hy⟩ := hs x
  refine ⟨y, ?_⟩
  rw [← hy, ptMap_apply, natCast_zsmul, nsmul_hom, id_hom, pt_comp_id_pow]

end GlobalTheory.AV.AbVar
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuasiInverseIsogeny
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuasiInverseIsogeny
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem exists_quasiInverse_isogeny : ∀ (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B), IsIsogeny f →
    ∃ (n : ℕ) (g : B ⟶ A), 0 < n ∧ IsIsogeny g ∧ f ≫ g = n • 𝟙 A ∧ g ≫ f = n • 𝟙 B := by
  intro K _ A B f hf
  obtain ⟨hdim, -, -, -⟩ := GlobalTheory.T.dim_eq_flat_finrank_eq_deg_of_isIsogeny K A B f hf
  obtain ⟨n, hn, hker⟩ := GlobalTheory.T.abelianVariety_finiteHom_kernel_killed_by_nat K A B f hf.1
  have hB := B.smooth
  have hA := A.smooth
  rw [hdim] at hA
  obtain ⟨h, hh, hfh, hhf⟩ := GlobalTheory.IsogenyQuasiInverse.exists_quasiInverse K A.X B.X B.dim A.ab B.ab hA hB
    f.hom inferInstance n hn hker
  let g : B ⟶ A := Hom.mk (A := B) (B := A) h (h := hh)
  have e1 : f ≫ g = n • 𝟙 A := by
    apply Subtype.ext
    change (f ≫ g).hom = (n • 𝟙 A).hom
    simp [g, hfh]
  have e2 : g ≫ f = n • 𝟙 B := by
    apply Subtype.ext
    change (g ≫ f).hom = (n • 𝟙 B).hom
    simp [g, hhf]
  refine ⟨n, g, hn, ?_, e1, e2⟩
  have hm : IsIsogeny ((n : ℤ) • 𝟙 B) := (GlobalTheory.T.abelianVariety_intCast_smul_isogeny_degree K B n (by exact_mod_cast hn.ne')).1
  rw [natCast_zsmul, ← e2] at hm
  exact (((GlobalTheory.T.isIsogeny_comp_iff_and_degree_mul K B A B g f hdim.symm hdim).1).mp hm).1

end GlobalTheory.AV.AbVar
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuasiInverseIsogenyStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_quasiInverse_isogeny' : ∀ (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B), IsIsogeny f → ∃ (n : ℕ) (g : B ⟶ A), 0 < n ∧ IsIsogeny g ∧ f ≫ g = n • 𝟙 A ∧ g ≫ f = n • 𝟙 B := by
  first | exact @GlobalTheory.AV.AbVar.exists_quasiInverse_isogeny | exact GlobalTheory.AV.AbVar.exists_quasiInverse_isogeny | (intros; apply GlobalTheory.AV.AbVar.exists_quasiInverse_isogeny <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLineBundleIsNefTens
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLineBundleIsNefTens
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false

noncomputable section

open GlobalTheory.CechPic

namespace GlobalTheory.NefTens

theorem isNef_tens : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k)
    (D : ℕ), IsArithVar p D → ∀ L M : HermLB p, L.IsNef D → M.IsNef D → (L.tens M).IsNef D := by
  intro HC k _ X _ p D hX L M NL NM
  have HE := HC.arExists
  have hex (L : HermLB p) : ∃ h, L.IsArithHeight h := (HE k X p D hX).1 L
  have : Module.Finite ℤ k := hX.finite
  have hp : IsProjOver p := hX.isProjOver
  refine ⟨NL.semiPos.tens NM.semiPos, ?_, fun Z i _ _ _ hc hd => ?_⟩
  · intro Z i _ _ κ _ _ _ hd
    rw [NefHodgeTateAt.topSelf_of_cls_eq_add hp (L.tens M).isLB L.isLB M.isLB (cls_tens L.isLB M.isLB _) Z i κ hd]
    exact add_nonneg (NL.vertical Z i κ hd) (NM.vertical Z i κ hd)
  · obtain ⟨h, H⟩ := hex L
    obtain ⟨h', H'⟩ := hex M
    obtain ⟨h'', H''⟩ := hex (L.tens M)
    obtain ⟨r, hr⟩ := exists_isRatSec ((L.tens M).restr i).isLB
    obtain ⟨r₁, hr₁, h1⟩ := NL.horizontal Z i hc hd
    obtain ⟨r₂, hr₂, h2⟩ := NM.horizontal Z i hc hd
    refine ⟨r, hr, ?_⟩
    rw [← H''.point Z i hc hd r hr,
      PtHtComb.height_tens hX H H' H'' (HtSelfInter.isAlgPt_genericPoint i hc hd),
      H.point Z i hc hd r₁ hr₁, H'.point Z i hc hd r₂ hr₂]
    exact add_nonneg h1 h2

end GlobalTheory.NefTens
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLineBundleIsNefTensStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermLineBundle_isNef_tens : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ L M : HermLB p, L.IsNef D → M.IsNef D → (L.tens M).IsNef D := by
  first | exact @GlobalTheory.NefTens.isNef_tens | exact GlobalTheory.NefTens.isNef_tens | (intros; apply GlobalTheory.NefTens.isNef_tens <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfiniteTopOfDictionaryDepth
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat

open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.SumSize GlobalTheory.KerConjMean

namespace GlobalTheory.KerConjMean

theorem sizes : ∀ (D : D7) (large₂ : SizeData₂ D) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 T : Type) (A : FamIn D.what₂.LL Γ Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), HidaSetting large₂ R F →
    1 ≤ Real.log large₂.sc.b ∧ Real.log D.host.rdE ≤ Real.log large₂.sc.b ∧ |logDerivativeAtOne D| ≤ Real.log large₂.sc.b := by
  intro D large₂ Γ _ _ Pl0 T A Ks _ _ _ R F hS
  obtain ⟨-, hSz, -, -, -, -, -, -, -, hrd, hcond, -⟩ := hS.size
  have hb : Real.log large₂.sc.b = large₂.sc.x ^ large₂.sc.eps := by
    simp [Formalism.BasicNotions.Scale.b, Formalism.BasicNotions.Scale.L]
  have hL1 : 1 ≤ large₂.sc.x ^ large₂.sc.eps := Real.one_le_rpow large₂.sc.one_lt_alt.le large₂.sc.eps_pos.le
  have hqd : |large₂.logDerivativeAtOne| ≤ large₂.sc.x ^ large₂.sc.eps := hSz.2.2.2.2.2.2.1.2.2.2.2.2.1
  have he : large₂.logDerivativeAtOne = logDerivativeAtOne D := by
    rw [large₂.logDerivative_at_one_eq]
    rfl
  rw [hb]
  refine ⟨hL1, ?_, he ▸ hqd⟩
  have : Real.log D.host.rdE ≤ large₂.sc.L / 100 := hrd.trans hcond
  simp only [Formalism.BasicNotions.Scale.L] at this
  linarith

theorem meanInf_affine (K : Type) [Field K] [NumberField K] (a0 nD Gd : ℝ) (f g : InfinitePlace K → ℝ) (ha0 : 0 ≤ a0) :
    Formalism.PairingDivisionLocalBalance.meanInf K (fun v => a0 + nD * f v + Gd * g v) ≤
      2 * a0 + nD * Formalism.PairingDivisionLocalBalance.meanInf K f + Gd * Formalism.PairingDivisionLocalBalance.meanInf K g := by
  unfold Formalism.PairingDivisionLocalBalance.meanInf
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]
  have hn : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  have hc : (Fintype.card (InfinitePlace K) : ℝ) ≤ Module.finrank ℚ K := by
    have h1 := InfinitePlace.card_add_two_mul_card_eq_rank K
    have h2 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces (K := K)
    exact_mod_cast (by omega : Fintype.card (InfinitePlace K) ≤ Module.finrank ℚ K)
  have h3 : 2 / (Module.finrank ℚ K : ℝ) * ((Fintype.card (InfinitePlace K) : ℝ) * a0) ≤ 2 * a0 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hn]
    nlinarith
  nlinarith [h3]

theorem exists_avg {α : Type} (S : Set α) (hS : S.Finite) (hne : S.Nonempty) (a0 nD Gd : ℝ) (h1 h2 : α → ℝ) :
    (∃ ρ ∈ S, a0 + nD * h1 ρ + Gd * h2 ρ ≤
      a0 + nD * ((∑ᶠ ρ ∈ S, h1 ρ) / Nat.card S) + Gd * ((∑ᶠ ρ ∈ S, h2 ρ) / Nat.card S)) ∧
    (∃ ρ ∈ S, a0 + nD * ((∑ᶠ ρ ∈ S, h1 ρ) / Nat.card S) + Gd * ((∑ᶠ ρ ∈ S, h2 ρ) / Nat.card S) ≤
      a0 + nD * h1 ρ + Gd * h2 ρ) := by
  set s := hS.toFinset with hs
  have hsne : s.Nonempty := by rwa [hs, Set.Finite.toFinset_nonempty]
  have hcard : (Nat.card S : ℝ) = s.card := by
    rw [hs, Nat.card_eq_card_finite_toFinset hS]
  have hs1 : ∑ᶠ ρ ∈ S, h1 ρ = ∑ ρ ∈ s, h1 ρ := finsum_mem_eq_finite_toFinset_sum _ hS
  have hs2 : ∑ᶠ ρ ∈ S, h2 ρ = ∑ ρ ∈ s, h2 ρ := finsum_mem_eq_finite_toFinset_sum _ hS
  have hc0 : (0 : ℝ) < s.card := by exact_mod_cast hsne.card_pos
  set m := a0 + nD * ((∑ᶠ ρ ∈ S, h1 ρ) / Nat.card S) + Gd * ((∑ᶠ ρ ∈ S, h2 ρ) / Nat.card S) with hm
  have key : ∑ ρ ∈ s, (a0 + nD * h1 ρ + Gd * h2 ρ) = ∑ _ρ ∈ s, m := by
    rw [Finset.sum_const, nsmul_eq_mul, hm, hs1, hs2, hcard, Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
    field_simp
  constructor
  · obtain ⟨ρ, hρ, h⟩ := Finset.exists_le_of_sum_le hsne key.le
    exact ⟨ρ, by rwa [hs, Set.Finite.mem_toFinset] at hρ, h⟩
  · obtain ⟨ρ, hρ, h⟩ := Finset.exists_le_of_sum_le hsne key.ge
    exact ⟨ρ, by rwa [hs, Set.Finite.mem_toFinset] at hρ, h⟩

end GlobalTheory.KerConjMean
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarFundamentalDomainUnitaryQuotientVolume
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.VolQAndIntegrableIff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.LiftRows GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.QuotFundDom

theorem volQ_and_integrable_iff : ∀ (D : D7) (V : HSp D) (ν : Measure (GA D V)) (X : Set (GA D V)), ν.IsHaarMeasure → IsFundamentalDomain (GQ V) X ν → GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.volQ V ν = (ν X).toReal ∧ ∀ F : GA D V → ℂ, (∀ γ ∈ GQ V, ∀ g, F (γ * g) = F g) → AEStronglyMeasurable F ν → (Integrable (GlobalTheory.AutomorphicL2Unitary.descend (GQ V) F) (GlobalTheory.AutomorphicL2Unitary.autMeasure V ν) ↔ IntegrableOn F X ν) := by
  intro D V ν X hν hX
  refine ⟨?_, fun F hF _ => ?_⟩
  · rw [GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.volQ, Measure.real, GlobalTheory.AutomorphicL2Unitary.autMeasure, GlobalTheory.AutomorphicL2Unitary.quotMeasure_univ hX]
  · have hL : GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ V) F := hF
    rw [← memLp_one_iff_integrable, GlobalTheory.AutomorphicL2Unitary.autMeasure, GlobalTheory.AutomorphicL2Unitary.memLp_quotMeasure_iff hX, hL.lift_descend,
      memLp_one_iff_integrable]
    rfl

end GlobalTheory.QuotFundDom
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarFundamentalDomainUnitaryQuotientVolume
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

noncomputable section

namespace GlobalTheory.RowTest.BottomMeas

theorem exists_haar_fd_volQ_ne_zero : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} (W : G.Weil) (i j : Fin D.R.m)
    (A A' WW : HSp D) (X : Tri T A A' WW), IsBottomTri W i j X →
    ∃ (ν : Measure (GA D WW)) (𝓕 : Set (GA D WW)), ν.IsHaarMeasure ∧ IsFundamentalDomain (GQ WW) 𝓕 ν ∧ volQ WW ν ≠ 0 := by
  intro D T L sc G W i j A A' WW X _
  obtain ⟨ν, 𝓕, hν, h𝓕⟩ := GlobalTheory.ConstRatio.exists_meas WW
  have : BorelSpace (GA D WW) := ⟨rfl⟩
  refine ⟨ν, 𝓕, hν, h𝓕, ?_⟩
  haveI := GlobalTheory.RegSch.Ibp.isFiniteMeasure_autMeasure (V := WW) ν
  rw [(GlobalTheory.QuotFundDom.volQ_and_integrable_iff D WW ν 𝓕 hν h𝓕).1]
  refine ENNReal.toReal_ne_zero.2 ⟨h𝓕.measure_ne_zero (NeZero.ne ν), ?_⟩
  exact (GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol WW ν _ hν h𝓕).ne

end GlobalTheory.RowTest.BottomMeas

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarFundamentalDomainUnitaryQuotientVolumeStatement
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
theorem _root_.GlobalTheory.T.exists_haar_fundamentalDomain_unitaryQuotientVolume_ne_zero : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} (W : G.Weil) (i j : Fin D.R.m)
    (A A' WW : HSp D) (X : Tri T A A' WW), IsBottomTri W i j X →
    ∃ (ν : Measure (GA D WW)) (𝓕 : Set (GA D WW)), ν.IsHaarMeasure ∧ IsFundamentalDomain (GQ WW) 𝓕 ν ∧ volQ WW ν ≠ 0 := by
  first | exact @GlobalTheory.RowTest.BottomMeas.exists_haar_fd_volQ_ne_zero | exact GlobalTheory.RowTest.BottomMeas.exists_haar_fd_volQ_ne_zero | (intros; apply GlobalTheory.RowTest.BottomMeas.exists_haar_fd_volQ_ne_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNsmulEqOfKillsTorsion
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompEqOneOfKillsGeometricTorsionPoints
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompEqOneOfKillsGeometricTorsionPoints
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AV.AbVar

theorem comp_hom_eq_one_of_torsion_pts (K : Type) [Field K] (A C : AbVar K) (f : A ⟶ C) (n : ℕ)
    (hn : (n : K) ≠ 0) (hker : ∀ x : A.Pt, x ^ n = 1 → x ≫ f.hom = 1)
    (T : Over (Sp K)) (x : T ⟶ A.X) (hx : x ^ n = 1) : x ≫ f.hom = 1 := by
  have hA := A.ab
  have hC := C.ab
  have := hA.proper
  have := hC.proper
  have := hA.smooth
  have hu : IsUnit (n : Γ(Sp K, ⊤)) := by
    simpa using (isUnit_iff_ne_zero.2 hn).map (Scheme.ΓSpecIso (.of K)).inv.hom
  obtain ⟨_, h3, h4⟩ := GrpTangent.finiteEtale_mulN_torsion A.X hu
  have hι : torsion.ι A.X n ≫ mulN A.X n = 1 := by
    rw [Hom.one_def]
    exact pullback.condition.trans (congrArg (· ≫ η[A.X]) (toUnit_unique _ _))
  set L := AlgebraicClosure K
  set t : Sp L ⟶ Sp K := spMap (algebraMap K L) with ht
  let P := (Over.pullback t).obj (torsion A.X n)
  let C' := (Over.pullback t).obj C.X
  have hP : Etale P.hom := by
    change Etale (pullback.snd (torsion A.X n).hom t)
    infer_instance
  have hPf : LocallyOfFiniteType P.hom := by
    change LocallyOfFiniteType (pullback.snd (torsion A.X n).hom t)
    infer_instance
  have hC' : IsProper C'.hom := by
    change IsProper (pullback.snd C.X.hom t)
    infer_instance
  have hPr : IsReduced P.left := isReduced_of_smooth_of_isReduced P.hom
  have hfst : ∀ g : torsion A.X n ⟶ C.X, ((Over.pullback t).map g).left ≫ pullback.fst C.X.hom t =
      pullback.fst (torsion A.X n).hom t ≫ g.left := fun g => by
    simp
  have hEq : (Over.pullback t).map (torsion.ι A.X n ≫ f.hom) =
      (Over.pullback t).map (1 : torsion A.X n ⟶ C.X) := by
    refine TorsionDivisible.hom_ext_of_rationalPoints _ _ fun y => ?_
    let z : Sp L ⟶ (torsion A.X n).left := y.left ≫ pullback.fst (torsion A.X n).hom t
    have hz : z ≫ (torsion A.X n).hom = t := by
      have e1 : y.left ≫ P.hom = 𝟙 _ := by
        change y.left ≫ pullback.snd (torsion A.X n).hom t = _
        simpa using Over.w y
      simp only [z, Category.assoc, pullback.condition]
      rw [← Category.assoc]
      change (y.left ≫ P.hom) ≫ t = t
      rw [e1, Category.id_comp]
    let z' : ptOver K L ⟶ torsion A.X n := Over.homMk z hz
    have hw : (z' ≫ torsion.ι A.X n) ^ n = 1 := by
      rw [← GrpTangent.comp_mulN, Category.assoc, hι, MonObj.comp_one]
    have hk := hker (z' ≫ torsion.ι A.X n) hw
    have hk' : z' ≫ (torsion.ι A.X n ≫ f.hom) = z' ≫ (1 : torsion A.X n ⟶ C.X) := by
      rw [MonObj.comp_one, ← Category.assoc, hk]
    have hkl : z ≫ (torsion.ι A.X n ≫ f.hom).left = z ≫ (1 : torsion A.X n ⟶ C.X).left :=
      congrArg CommaMorphism.left hk'
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · simp only [Over.comp_left, Category.assoc, hfst]
      simpa [z] using hkl
    · have w1 := Over.w (y ≫ (Over.pullback t).map (torsion.ι A.X n ≫ f.hom))
      have w2 := Over.w (y ≫ (Over.pullback t).map (1 : torsion A.X n ⟶ C.X))
      change _ ≫ pullback.snd C.X.hom t = _ at w1 w2
      rw [w1, w2]
  have hred : IsReduced (torsion A.X n).left := isReduced_of_smooth_of_isReduced (torsion A.X n).hom
  have hdom : IsDominant (pullback.fst (torsion A.X n).hom t) := inferInstance
  have h6 : torsion.ι A.X n ≫ f.hom = 1 := by
    apply Over.OverMorphism.ext
    refine ext_of_isDominant_of_isSeparated C.X.hom (by rw [Over.w, Over.w]) (pullback.fst (torsion A.X n).hom t) ?_
    rw [← hfst, ← hfst, hEq]
  have e : x ≫ mulN A.X n = toUnit T ≫ η[A.X] := by rw [GrpTangent.comp_mulN, hx, Hom.one_def]
  obtain ⟨y, e'⟩ : ∃ y : T ⟶ torsion A.X n, y ≫ torsion.ι A.X n = x :=
    ⟨pullback.lift x (toUnit T) e, pullback.lift_fst _ _ _⟩
  rw [← e', Category.assoc, h6, MonObj.comp_one]

end GlobalTheory.AV.AbVar

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompEqOneOfKillsGeometricTorsionPointsStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.comp_eq_one_of_kills_geometric_torsionPoints : ∀ (K : Type) [Field K] (A C : AbVar K) (f : A ⟶ C) (n : ℕ), (n : K) ≠ 0 → (∀ x : A.Pt, x ^ n = 1 → x ≫ f.hom = 1) → ∀ (T : Over (Sp K)) (x : T ⟶ A.X), x ^ n = 1 → x ≫ f.hom = 1 := by
  first | exact @GlobalTheory.AV.AbVar.comp_hom_eq_one_of_torsion_pts | exact GlobalTheory.AV.AbVar.comp_hom_eq_one_of_torsion_pts | (intros; apply GlobalTheory.AV.AbVar.comp_hom_eq_one_of_torsion_pts <;> assumption)
end
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem comp_id_pow_eq {K : Type} [Field K] (A : AbVar K) {T : Over (Sp K)} (x : T ⟶ A.X) (n : ℕ) :
    x ≫ (𝟙 A.X) ^ n = x ^ n := by
  induction n with
  | zero => simp [pow_zero, MonObj.comp_one]
  | succ k ih => rw [pow_succ, pow_succ, MonObj.comp_mul, ih, Category.comp_id]

theorem exists_nsmul_eq_of_kills_torsion : ∀ (K : Type) [Field K] (A C : AbVar K) (f : A ⟶ C) (n : ℕ),
    (n : K) ≠ 0 → (∀ x : A.Pt, x ^ n = 1 → x ≫ f.hom = 1) → ∃ g : A ⟶ C, f = n • g := by
  intro K _ A C f n hn hf
  have hn0 : (n : ℤ) ≠ 0 := by
    intro h
    apply hn
    have : n = 0 := by exact_mod_cast h
    simp [this]
  obtain ⟨hiso, -⟩ := GlobalTheory.T.abelianVariety_intCast_smul_isogeny_degree K A (n : ℤ) hn0
  have hiso' : IsIsogeny (n • 𝟙 A) := by rwa [natCast_zsmul] at hiso
  have hkill := GlobalTheory.T.comp_eq_one_of_kills_geometric_torsionPoints K A C f n hn hf
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_factor_through_isogeny_of_kills_kernel K A A C (n • 𝟙 A) f hiso' (fun T x hx => by
    apply hkill T x
    rw [nsmul_hom, id_hom, comp_id_pow_eq] at hx
    exact hx)
  refine ⟨g, ?_⟩
  rw [← hg, Preadditive.nsmul_comp, Category.id_comp]

end GlobalTheory.AV.AbVar
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentKummerCupProductBijectiveStrictlyHenseliaStatement
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.laurentKummerCupProduct_bijective_strictlyHenselian : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], SH A → IsUnit (q : A) → ∀ i : ℤ, Function.Bijective (gmPhi q A i) := by
  first | (exact @GlobalTheory.EtC.gmPhi_bijective) | (exact GlobalTheory.EtC.gmPhi_bijective) | (intros; apply GlobalTheory.EtC.gmPhi_bijective  <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDoubleCosetDefiniteUnitaryRationalOfIsOpen
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDoubleCosetDefiniteUnitaryRationalOfIsOpen
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TraceBlocks
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem GlobalTheory.BCT.finite_doubleCoset_ratFinU_isOpen : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (L : Subgroup (finU (E := E) (n := n))), IsOpen (L : Set (finU (E := E) (n := n))) → Finite (DoubleCoset.Quotient (ratFinU E n : Set (finU (E := E) (n := n))) (L : Set (finU (E := E) (n := n)))) := by
  intro E _ _ _ n L hL
  exact GlobalTheory.BCT.ClassFinLev.finite_doubleCoset_of_isOpen L hL
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDoubleCosetDefiniteUnitaryRationalOfIsOpenStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TraceBlocks
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_doubleCoset_definiteUnitaryRational_of_isOpen : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (L : Subgroup (finU (E := E) (n := n))), IsOpen (L : Set (finU (E := E) (n := n))) → Finite (DoubleCoset.Quotient (ratFinU E n : Set (finU (E := E) (n := n))) (L : Set (finU (E := E) (n := n)))) := by
  first | exact @GlobalTheory.BCT.finite_doubleCoset_ratFinU_isOpen | exact GlobalTheory.BCT.finite_doubleCoset_ratFinU_isOpen | (intros; apply GlobalTheory.BCT.finite_doubleCoset_ratFinU_isOpen <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NefOnFiniteFieldFibresPowTens
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NefOnFiniteFieldFibresPowTens
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

set_option autoImplicit false

noncomputable section

open GlobalTheory.CechPic

namespace GlobalTheory.NefFibTens

theorem nefFib_pow_tens : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (L A : HermLB p) (n : ℕ), NefFib L → NefFib A → NefFib ((L.pow n).tens A) := by
  intro k _ X _ p D hX L A n hL hA Z i _ _ κ _ _ _ hd
  have : Module.Finite ℤ k := hX.finite
  have hp : IsProjOver p := hX.isProjOver
  rw [NefHodgeTateAt.topSelf_of_cls_eq_add hp ((L.pow n).tens A).isLB (L.pow n).isLB A.isLB
    (cls_tens (L.pow n).isLB A.isLB _) Z i κ hd, NefHodgeTateAt.topSelf_pow hp L n Z i κ hd]
  exact add_nonneg (mul_nonneg (Nat.cast_nonneg _) (hL Z i κ hd)) (hA Z i κ hd)

end GlobalTheory.NefFibTens
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NefOnFiniteFieldFibresPowTensStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nefOnFiniteFieldFibres_pow_tens : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (L A : HermLB p) (n : ℕ), NefFib L → NefFib A → NefFib ((L.pow n).tens A) := by
  first | exact @GlobalTheory.NefFibTens.nefFib_pow_tens | exact GlobalTheory.NefFibTens.nefFib_pow_tens | (intros; apply GlobalTheory.NefFibTens.nefFib_pow_tens <;> assumption)
end
end
