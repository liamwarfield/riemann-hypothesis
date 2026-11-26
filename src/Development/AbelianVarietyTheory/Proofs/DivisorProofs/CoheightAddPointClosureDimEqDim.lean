module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsProjSpaceMapOfTupleHasDivisor
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantsListedFiniteGaloisExtension
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasThetaConstantsTwoLevelsMoveCartesian
public import Development.AutomorphicArithmetic.LocalEmbeddings.ThinCover
public import Development.AutomorphicArithmetic.LocalEmbeddings.ThinCore
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SizeBoundStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasUnramifiedIntegralFramedPointsOfGoodPlaces
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedFactorExistsUniqueConstMulIntegralGenerat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightConditionsAtIndex

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoheightAddPointClosureDimEqDim
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoheightAddPointClosureDimEqDim
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

namespace GlobalTheory.DimCoheight

theorem trdeg_eq_of_isFractionRing (R A K : Type) [CommRing R] [Nontrivial R] [CommRing A] [IsDomain A]
    [Field K] [Algebra R A] [Algebra A K] [Algebra R K] [IsScalarTower R A K] [FaithfulSMul R A]
    [IsFractionRing A K] : Algebra.trdeg R K = Algebra.trdeg R A := by
  have _ : FaithfulSMul A K :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (IsFractionRing.injective A K)
  have _ : Algebra.IsAlgebraic A K := IsLocalization.isAlgebraic K (nonZeroDivisors A)
  rw [← trdeg_add_eq R A (A := K), trdeg_eq_zero (R := A) (A := K), add_zero]

theorem exists_ringKrullDim_affine_eq (Y : Scheme.{0}) [IsIntegral Y]
    (hft : ∀ U : Y.Opens, IsAffineOpen U → Algebra.FiniteType ℤ Γ(Y, U)) :
    ∃ c : WithBot ℕ∞, ∀ U : Y.Opens, IsAffineOpen U → Nonempty U → ringKrullDim Γ(Y, U) = c := by
  by_cases h0 : CharZero Y.functionField
  · refine ⟨((Cardinal.toENat (Algebra.trdeg ℤ Y.functionField) + 1 : ℕ∞) : WithBot ℕ∞),
      fun U hU _ => ?_⟩
    have := hft U hU
    have := functionField_isFractionRing_of_isAffineOpen Y U hU
    have hK := IsFractionRing.injective Γ(Y, U) Y.functionField
    have : CharZero Γ(Y, U) := ⟨fun a b h => by
      have := congrArg (algebraMap Γ(Y, U) Y.functionField) h
      simpa using this⟩
    have hinj : Function.Injective (algebraMap ℤ Γ(Y, U)) := RingHom.injective_int _
    have : FaithfulSMul ℤ Γ(Y, U) := (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
    rw [IntFiniteTypeDim.ringKrullDim_eq_trdeg_add_one _ hinj,
      ← trdeg_eq_of_isFractionRing ℤ Γ(Y, U) Y.functionField]
  · obtain ⟨p, hp⟩ := CharP.exists Y.functionField
    have hp0 : p ≠ 0 := by
      rintro rfl
      exact h0 (CharP.charP_to_charZero _)
    have : Fact p.Prime := ⟨(CharP.char_is_prime_or_zero Y.functionField p).resolve_right hp0⟩
    letI : Algebra (ZMod p) Y.functionField := ZMod.algebra _ p
    refine ⟨((Algebra.trdeg (ZMod p) Y.functionField).toENat : WithBot ℕ∞), fun U hU _ => ?_⟩
    have := hft U hU
    have := functionField_isFractionRing_of_isAffineOpen Y U hU
    have hK := IsFractionRing.injective Γ(Y, U) Y.functionField
    have : CharP Γ(Y, U) p := (algebraMap Γ(Y, U) Y.functionField).charP hK p
    letI : Algebra (ZMod p) Γ(Y, U) := ZMod.algebra _ p
    have : IsScalarTower (ZMod p) Γ(Y, U) Y.functionField := IsScalarTower.of_algebraMap_eq
      fun x => congrArg (· x) (RingHom.ext_zmod (algebraMap (ZMod p) Y.functionField)
        ((algebraMap Γ(Y, U) Y.functionField).comp (algebraMap (ZMod p) Γ(Y, U))))
    have : Algebra.FiniteType (ZMod p) Γ(Y, U) :=
      Algebra.FiniteType.of_restrictScalars_finiteType ℤ (ZMod p) Γ(Y, U)
    exact GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_eq_trdeg_fractionRing (ZMod p) Y.functionField

end GlobalTheory.DimCoheight

namespace GlobalTheory.DimCoheight

theorem finiteType_of_isAmb {k : Type} [CommRing k] {Y : Scheme.{0}} {q : Y ⟶ Sp k} (hq : IsAmb q)
    (U : Y.Opens) (hU : IsAffineOpen U) : Algebra.FiniteType ℤ Γ(Y, U) := by
  have := hq.finite
  have : IsProper q := CommonModel.isProper_of_isProjOver hq.isProjOver
  have : LocallyOfFiniteType (spMap (Int.castRingHom k)) := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  have hl : LocallyOfFiniteType (Spec.map (Spec.preimage (hU.fromSpec ≫ q ≫ spMap (Int.castRingHom k)))) := by
    rw [Spec.map_preimage]; infer_instance
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at hl
  have e : (Spec.preimage (hU.fromSpec ≫ q ≫ spMap (Int.castRingHom k))).hom = algebraMap ℤ Γ(Y, U) :=
    RingHom.ext_int _ _
  rw [e] at hl
  exact RingHom.finiteType_algebraMap.mp hl

theorem coheight_add_eq : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp k),
    IsAmb q → ∀ d : ℕ, topologicalKrullDim Y = d → ∀ (z : Y) (e : ℕ), HasDim z e →
    Order.coheight z + (e : ℕ∞) = d := by
  intro k _ Y _ q hq d hd z e hz
  have hft := finiteType_of_isAmb hq
  obtain ⟨c, hc⟩ := exists_ringKrullDim_affine_eq Y hft

  have hdc : (d : WithBot ℕ∞) ≤ c := by
    rw [← hd]
    refine topologicalKrullDim_le_of_forall_exists_isOpen fun y => ?_
    obtain ⟨_, ⟨U, hU, rfl⟩, hyU, -⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
    have hU : IsAffineOpen U := hU
    refine ⟨(U : Set Y), U.isOpen, hyU, ?_⟩
    have hne : Nonempty U := ⟨⟨y, hyU⟩⟩
    rw [topologicalKrullDim_eq_of_isEmbedding hU.fromSpec.isOpenEmbedding.isEmbedding hU.range_fromSpec]
    exact (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _).le.trans (hc U hU hne).le

  obtain ⟨_, ⟨U, hU, rfl⟩, hzU, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ z) isOpen_univ
  have hU : IsAffineOpen U := hU
  have hne : Nonempty U := ⟨⟨z, hzU⟩⟩
  obtain ⟨P, hP⟩ : ∃ P : PrimeSpectrum Γ(Y, U), hU.fromSpec P = z := by
    have : z ∈ Set.range hU.fromSpec := by rw [hU.range_fromSpec]; exact hzU
    exact this
  have := hft U hU
  have hcA := hc U hU hne

  obtain ⟨M, hM, hMd⟩ : ∃ M : Ideal Γ(Y, U), M.IsMaximal ∧ (d : WithBot ℕ∞) ≤ M.height := by
    rcases Nat.eq_zero_or_eq_succ_pred d with h | h
    · obtain ⟨M, hM⟩ := Ideal.exists_maximal Γ(Y, U)
      exact ⟨M, hM, by rw [h]; exact_mod_cast bot_le⟩
    · by_contra hne
      push_neg at hne
      have : ringKrullDim Γ(Y, U) ≤ ((d.pred : ℕ) : WithBot ℕ∞) := by
        refine (ringKrullDim_le_iff_isMaximal_height_le _).2 fun m hm => ?_
        have h1 := hne m hm
        rw [h] at h1
        have h2 : m.height < ((d.pred + 1 : ℕ) : ℕ∞) := by exact_mod_cast h1
        exact_mod_cast Order.le_of_lt_add_one (by exact_mod_cast h2)
      have h3 := hdc.trans (hcA.symm.le.trans this)
      rw [h] at h3
      have : d.pred + 1 ≤ d.pred := by exact_mod_cast h3
      omega
  have h2 := FinTypeIntCatenary.height_maximal_le Γ(Y, U) P.asIdeal M

  let x : Spec Γ(Y, U) := P
  have eS := (asIso (hU.fromSpec.stalkMap x) ≪≫ Spec.stalkIso Γ(Y, U) x).commRingCatIsoToRingEquiv
  have hPh : (P.asIdeal.height : WithBot ℕ∞) = Order.coheight z := by
    rw [← IsLocalization.AtPrime.ringKrullDim_eq_height P.asIdeal (Localization.AtPrime P.asIdeal),
      ← ringKrullDim_eq_of_ringEquiv eS, ← ringKrullDim_stalk_eq_coheight]
    rw [← hP]

  have h3 : ringKrullDim (Γ(Y, U) ⧸ P.asIdeal) ≤ e := by
    rw [← topologicalKrullDim_range_inter_closure_eq (B := Γ(Y, U)) hU.fromSpec P, hP, ← hz]
    exact (Topology.IsEmbedding.inclusion Set.inter_subset_right).isInducing.topologicalKrullDim_le
  have hge : (d : WithBot ℕ∞) ≤ (Order.coheight z : WithBot ℕ∞) + (e : WithBot ℕ∞) := by
    rw [← hPh]
    exact hMd.trans (h2.trans (add_le_add le_rfl h3))

  have hle : topologicalKrullDim (closure ({z} : Set Y)) + Order.coheight z ≤ topologicalKrullDim Y := by
    haveI : QuasiSober (closure ({z} : Set Y)) := isClosed_closure.isClosedEmbedding_subtypeVal.quasiSober
    exact DimCodim.dim_add_le_of_le_coheight continuous_subtype_val Subtype.val_injective _
      fun w => Order.coheight_anti (specializes_iff_mem_closure.2 w.2)
  rw [hz, hd] at hle
  have a1 : (e : ℕ∞) + Order.coheight z ≤ d := by exact_mod_cast hle
  have a2 : (d : ℕ∞) ≤ Order.coheight z + e := by exact_mod_cast hge
  rw [add_comm] at a1
  exact le_antisymm a1 a2

end GlobalTheory.DimCoheight
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoheightAddPointClosureDimEqDimStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coheight_add_pointClosureDim_eq_dim : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp k), IsAmb q → ∀ d : ℕ, topologicalKrullDim Y = d → ∀ (z : Y) (e : ℕ), HasDim z e → Order.coheight z + (e : ℕ∞) = d := by
  first | exact @GlobalTheory.DimCoheight.coheight_add_eq | exact GlobalTheory.DimCoheight.coheight_add_eq | (intros; apply GlobalTheory.DimCoheight.coheight_add_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TowerStageFinitePlacesUnramifiedOrSplit
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.StageRam

private theorem pow_apply' {E : Type} [Field E] [NumberField E] (χ : HChar E) (a : ℕ) (x) : (χ ^ a).1 x = χ.1 x ^ a := by
  rw [SubgroupClass.coe_pow, MonoidHom.pow_apply]

private theorem loc_pow {E : Type} [Field E] [NumberField E] (χ : HChar E) (a : ℕ) (v x) :
    (χ ^ a).loc v x = χ.loc v x ^ a :=
  pow_apply' χ a _

private theorem locK_pow {E : Type} [Field E] [NumberField E] (χ : HChar E) (a : ℕ) (v x) :
    (χ ^ a).locK v x = χ.locK v x ^ a :=
  pow_apply' χ a _

private theorem unrAt_pow {E : Type} [Field E] [NumberField E] {χ : HChar E} {v} (h : χ.UnrAt v) (a : ℕ) :
    (χ ^ a).UnrAt v :=
  fun x hx => by rw [loc_pow, h x hx, one_pow]

private theorem chrEq_pow {D : D7} {c : (AE D)ˣ →* Circle} {χ : HChar D.host.E} (h : ChrEq c χ) (a : ℕ) :
    ChrEq (c ^ a) (χ ^ a) := by
  refine ⟨⟨?_, fun x => ?_⟩, fun P e he k x hx => ?_⟩
  · have : ((c ^ a : (AE D)ˣ →* Circle) : (AE D)ˣ → Circle) = fun x => c x ^ a := by
      funext x; simp
    rw [this]
    exact h.1.1.pow a
  · have h1 := h.1.2 x
    simp only [MonoidHom.pow_apply, h1, one_pow]
  · rw [MonoidHom.pow_apply, locK_pow, Units.val_pow_eq_pow_val, ← h.2 P e he k x hx]
    exact map_pow Circle.coeHom _ _

private theorem not_nonSplitAt_of_emb {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F}
    (hε : IsPlaceIdem D v ε) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) : ¬ GlobalTheory.WeilParts.NonSplitAt D v ε := by
  intro h
  refine h.2 ⟨GlobalTheory.EmbChart.idem τ, GlobalTheory.EmbChart.isSplitIdem_idem τ, ?_⟩
  have he : ε = GlobalTheory.EmbChart.atPlace v 1 := by
    obtain ⟨α, rfl, h1, h0⟩ := hε
    rw [GlobalTheory.EmbChart.atPlace_apply]
    congr 1
    refine FiniteAdeleRing.ext _ fun u => ?_
    change evalV D.host.F u α = evalV D.host.F u (GlobalTheory.AdelicU.singleFin v 1)
    by_cases e : u = v
    · subst e; rw [GlobalTheory.AdelicU.evalV_singleFin_self, h1]
    · rw [GlobalTheory.AdelicU.evalV_singleFin_ne e, h0 u e]
  rw [he, GlobalTheory.EmbChart.cA_idem, GlobalTheory.EmbChart.idem, ← LinearMap.map_add (f := _), add_sub_cancel]; rfl

private theorem levelLe_one_of_unrAt {L : Type} [Field L] [NumberField L] {χ : HChar L} {w : HeightOneSpectrum (𝓞 L)}
    (h : χ.UnrAt w) : χ.LevelLe w 1 :=
  fun x hx _ => h x hx

private theorem natCast_mem_of_card {E : Type} [Field E] [NumberField E] {P : HeightOneSpectrum (𝓞 E)} {ℓ : ℕ}
    (hℓ : ℓ.Prime) (h : Nat.card (𝓞 E ⧸ P.asIdeal) = ℓ) : (ℓ : 𝓞 E) ∈ P.asIdeal := by
  have : Finite (𝓞 E ⧸ P.asIdeal) := Nat.finite_of_card_ne_zero (h ▸ hℓ.ne_zero)
  letI := Fintype.ofFinite (𝓞 E ⧸ P.asIdeal)
  have h0 : ((Fintype.card (𝓞 E ⧸ P.asIdeal) : ℕ) : 𝓞 E ⧸ P.asIdeal) = 0 := Nat.cast_card_eq_zero _
  rw [← Nat.card_eq_fintype_card, h] at h0
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact h0


open Classical in
theorem _root_.GlobalTheory.T.towerStage_finitePlaces_unramified_or_split : GBig fun {D} {T} {Lc} {sc} G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (p q : ℕ) (A A' WW : HSp D) (X : Tri T A A' WW), GlobalTheory.SqTower.IsStageC W i j p q X → ∀ (t : T) (v : HeightOneSpectrum (𝓞 D.host.F)) (e : AF D.host.F), IsPlaceIdem D v e → (GlobalTheory.WeilParts.UnramAt e (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2)) ∧ GlobalTheory.WeilParts.UnramAt e (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2))) ∨ (¬ GlobalTheory.WeilParts.NonSplitAt D v e ∧ ¬ GlobalTheory.WeilParts.UnramAt e (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2) / (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2))) ∧ ¬ v.asIdeal ∣ differentIdeal ℤ (𝓞 D.host.F)) := by
  refine ⟨0, fun _ _ _ => ⟨0, 0, fun _ _ D large₂ _ _ hR T Lc μ₀ hL G => ?_⟩⟩
  intro W i j p q A A' WW X _ t v e he
  have hm1 : 1 ≤ D.R.m - (i : ℕ) := by omega
  have hm2 : D.R.m - (i : ℕ) ≤ D.R.m := by omega
  have hα : ChrEq (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2)) (alphaH Lc t i j) :=
    GlobalTheory.TwistChr.chrEq_mul (GlobalTheory.TwistChr.chrEq_mul (hL.mu0 j) (hL.xi t)) (chrEq_pow hL.eta _)
  have hβ : ChrEq (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)) (betaH G i j) :=
    GlobalTheory.TwistChr.chrEq_mul (G.ch.chi_eq _ hm1 hm2) (chrEq_pow hL.eta _)
  have hν : ChrEq (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2) / (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)))
      (nuH G t i j) := by
    rw [mul_div_mul_right_eq_div]
    exact chrEq_nu G t i j hL
  have hmu : ∀ P : HeightOneSpectrum (𝓞 D.host.E), P.under (𝓞 D.host.F) ∉ S1 D → (Lc.C.mu0 j).UnrAt P :=
    fun P hP => (Lc.C.isMu0 j).unr _ fun k hk => hP (by
      have h : ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ (P.under (𝓞 D.host.F)).asIdeal := by
        show algebraMap _ (𝓞 D.host.E) _ ∈ P.asIdeal
        rw [map_natCast]; exact hk
      refine (S1_mem_OmF D).2 ?_
      fin_cases k
      · exact Or.inl h
      · exact Or.inr (Or.inl h))
  have hxi : ∀ P : HeightOneSpectrum (𝓞 D.host.E),
      (∀ PP ∈ Lc.Q t, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ≠ P.under (𝓞 D.host.F)) → (Lc.xiH t).UnrAt P := fun P hP => by
    by_contra hc
    rcases (hL.Q_ram t P).1 hc with h | ⟨PP', h, hc'⟩
    · exact hP P h rfl
    · exact hP PP' h (GlobalTheory.LevelPlaces.under_eq_of_isConjPl hc')
  have hchi : ∀ P : HeightOneSpectrum (𝓞 D.host.E), P.under (𝓞 D.host.F) ∉ G.pl.S0 →
      (G.ch.chiH (D.R.m - i)).UnrAt P := fun P hP => G.ch.unr _ hm1 hm2 P hP
  have heta : ∀ P : HeightOneSpectrum (𝓞 D.host.E), (Lc.C.eta ^ (rankV D i j % 2)).UnrAt P :=
    fun P => unrAt_pow (Lc.C.isEta.unr P) _
  by_cases hS : v ∈ G.pl.S0 ∨ ∃ PP ∈ Lc.Q t, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) = v
  · right
    obtain ⟨w, hw, hwv⟩ : ∃ w ∈ locPl G t, w.under (𝓞 D.host.F) = v := by
      rcases hS with h | ⟨PP, hP, hPv⟩
      · exact ⟨G.pl.w v, Finset.mem_union_left _ (Finset.mem_image_of_mem _ h), G.pl.under_w h⟩
      · exact ⟨PP, Finset.mem_union_right _ hP, hPv⟩
    have hns : ¬ GlobalTheory.WeilParts.NonSplitAt D v e := by
      obtain ⟨τ⟩ := GlobalTheory.LocPlSplit.locPl_split hL t w hw
      rw [hwv] at τ
      exact not_nonSplitAt_of_emb he τ
    refine ⟨hns, fun hu => ?_, ?_⟩
    · have key : ∀ P : HeightOneSpectrum (𝓞 D.host.E), P.under (𝓞 D.host.F) = v → (nuH G t i j).UnrAt P :=
        fun P hP => (GlobalTheory.LFun.unrAt_iff_of_chrEq hν P).1 (GlobalTheory.UnrOverPlace.unrAt_of_unramAt D _ v e he hu P hP)
      by_cases h0 : v = G.pl.v0
      · subst h0
        exact GlobalTheory.RowTest.squareNuHeckeCharacter_not_unramified_at_chosenPlace hL G t i j (key _ (G.pl.under_w (G.pl.mem_S0_of_sum_eq.2 (Or.inl rfl))))
      · by_cases h1 : v ∈ S1 D
        · have hv : v ∈ G.pl.S0 := G.pl.mem_S0_of_sum_eq.2 (Or.inr h1)
          have hwv' := G.pl.under_w hv
          apply (G.ch.lev1 _ hm1 hm2 (G.pl.w v) (by rw [hwv']; exact h1)).2
          have ee : G.ch.chiH (D.R.m - i) = Lc.C.mu0 j * Lc.xiH t / nuH G t i j := by
            rw [nuH, div_div_cancel]
          rw [ee, div_eq_mul_inv]
          exact HChar.LevelLe.mul (HChar.LevelLe.mul ((Lc.C.isMu0 j).tame _) (hL.xi_tame t _))
            (HChar.LevelLe.inv (levelLe_one_of_unrAt (key _ hwv')))
        · obtain ⟨PP, hP, hPv⟩ := hS.resolve_left fun h => (G.pl.mem_S0_of_sum_eq.1 h).elim h0 h1
          apply (hL.Q_ram t PP).2 (Or.inl hP)
          have ee : Lc.xiH t = nuH G t i j * G.ch.chiH (D.R.m - i) / Lc.C.mu0 j := by
            rw [nuH, div_mul_cancel, mul_div_cancel_left]
          rw [ee, div_eq_mul_inv]
          exact ((key PP hPv).mul (hchi PP (by rw [hPv]; exact fun h => (G.pl.mem_S0_of_sum_eq.1 h).elim h0 h1))).mul
            (hmu PP (by rw [hPv]; exact h1)).inv
    · by_cases h0 : v = G.pl.v0
      · subst h0
        exact GlobalTheory.DifferentAtBasePlace.not_dvd_different G
      · by_cases h1 : v ∈ S1 D
        · exact GlobalTheory.DiffSOne.not_dvd_differentIdeal large₂ hR v h1
        · obtain ⟨PP, hP, hPv⟩ := hS.resolve_left fun h => (G.pl.mem_S0_of_sum_eq.1 h).elim h0 h1
          obtain ⟨⟨ℓ, hℓ, hcard, hℓ2, -⟩, -⟩ := hL.Q_pl t PP hP
          have hℓP : ((ℓ : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := natCast_mem_of_card hℓ hcard
          have hle : v.asIdeal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) ≤ PP.asIdeal := by
            rw [← hPv]
            exact Ideal.map_comap_le
          refine GlobalTheory.SplitUnram.not_dvd_different hℓ v ?_ ?_
          · rw [← hPv]
            show algebraMap _ (𝓞 D.host.E) _ ∈ PP.asIdeal
            rw [map_natCast]; exact hℓP
          · intro hv2
            have h' := Ideal.mem_map_of_mem (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) hv2
            rw [Ideal.map_pow, map_natCast] at h'
            exact hℓ2 (Ideal.pow_right_mono hle 2 h')
  · left
    push_neg at hS
    obtain ⟨hS0, hQ⟩ := hS
    have hS1 : v ∉ S1 D := fun h => hS0 (G.pl.mem_S0_of_sum_eq.2 (Or.inr h))
    refine ⟨GlobalTheory.T.isUnramifiedAtPlaceIdempotent_of_heckeChar_unramified_above D _ _ hα v e he fun P hP => ?_, GlobalTheory.T.isUnramifiedAtPlaceIdempotent_of_heckeChar_unramified_above D _ _ hβ v e he fun P hP => ?_⟩
    · exact ((hmu P (by rw [hP]; exact hS1)).mul (hxi P fun PP hPP h => hQ PP hPP (h.trans hP))).mul (heta P)
    · exact (hchi P (by rw [hP]; exact hS0)).mul (heta P)

end GlobalTheory.StageRam

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointClosureDimLeAndResidueDegreeNeZeroIff
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointClosureDimLeAndResidueDegreeNeZeroIff
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

namespace GlobalTheory.DimDeg

def DimFormula (R : Type) [CommRing R] (c : ℕ) : Prop :=
  ∀ (B : Type) [CommRing B] [IsDomain B] [Algebra R B] [FaithfulSMul R B] [Algebra.FiniteType R B] (e : ℕ),
    Algebra.trdeg R B = e → ringKrullDim B = (e + c : ℕ)

theorem dimFormula_field (F : Type) [Field F] : DimFormula F 0 := by
  intro B _ _ _ _ _ e he
  obtain ⟨d, h₁, h₂⟩ := exists_ringKrullDim_eq_and_trdeg_eq F B
  have : d = e := by exact_mod_cast h₂.symm.trans he
  rw [h₁, this, add_zero]

theorem dimFormula_int : DimFormula ℤ 1 := by
  intro B _ _ _ _ _ e he
  have : CharZero B := charZero_of_injective_algebraMap (FaithfulSMul.algebraMap_injective ℤ B)
  refine le_antisymm ?_ (PrimeDivDim.succ_trdeg_le_ringKrullDim B he)
  have hZ1 : ringKrullDim ℤ ≤ 1 := by
    exact_mod_cast Ring.krullDimLE_iff.mp (inferInstance : Ring.KrullDimLE 1 ℤ)
  refine (IntModel.ringKrullDim_le_add (O := ℤ) ℚ).trans ?_
  rw [ringKrullDim_genericFibre_eq ℤ ℚ he]
  refine (add_le_add hZ1 (le_refl ((e : ℕ) : WithBot ℕ∞))).trans_eq ?_
  push_cast
  exact add_comm _ _

theorem exists_dim_quotient_ker {R : Type} [CommRing R] [IsDomain R] {c : ℕ} (hR : DimFormula R c)
    (hs : Function.Surjective (Int.cast : ℤ → R)) {A K : Type} [CommRing A] (hA : (Int.castRingHom A).FiniteType)
    [Field K] [Algebra R K] [FaithfulSMul R K] (φ : A →+* K) (hφ : ∀ z : K, ∃ a b : A, z = φ a / φ b) :
    ∃ e : ℕ, Algebra.trdeg R K = e ∧ ringKrullDim (A ⧸ RingHom.ker φ) = (e + c : ℕ) := by
  let B : Subalgebra R K :=
    { φ.range.toSubsemiring with
      algebraMap_mem' := fun r => by
        obtain ⟨n, rfl⟩ := hs r
        exact ⟨n, by simp⟩ }
  let ψ : A →+* B := φ.codRestrict B fun a => ⟨a, rfl⟩
  have hψ : Function.Surjective ψ := by
    rintro ⟨_, a, rfl⟩
    exact ⟨a, rfl⟩
  have hft : Algebra.FiniteType R B := by
    have h1 : (ψ.comp (Int.castRingHom A)).FiniteType := (RingHom.FiniteType.of_surjective ψ hψ).comp hA
    rw [Subsingleton.elim (ψ.comp (Int.castRingHom A)) ((algebraMap R B).comp (Int.castRingHom R))] at h1
    exact RingHom.finiteType_algebraMap.1 h1.of_comp_finiteType
  have : FaithfulSMul R B := (faithfulSMul_iff_algebraMap_injective _ _).2 fun a b h =>
    FaithfulSMul.algebraMap_injective R K (by
      rw [IsScalarTower.algebraMap_apply R B K, IsScalarTower.algebraMap_apply R B K, h])
  have : IsFractionRing B K := IsFractionRing.of_field B K fun z => by
    obtain ⟨a, b, h⟩ := hφ z
    exact ⟨ψ a, ψ b, h⟩
  have : Algebra.IsAlgebraic B K := IsLocalization.isAlgebraic K (nonZeroDivisors B)
  obtain ⟨e, he⟩ := exists_trdeg_eq_natCast R (A := B)
  refine ⟨e, (trdeg_eq_of_isAlgebraic_top R B K).trans he, ?_⟩
  have hk : RingHom.ker φ = RingHom.ker ψ := Ideal.ext fun a => by
    simp only [RingHom.mem_ker]
    exact (Subtype.ext_iff (a1 := ψ a) (a2 := 0)).symm
  rw [← hR B e he, hk]
  exact ringKrullDim_eq_of_ringEquiv (RingHom.quotientKerEquivOfSurjective hψ)

theorem exists_dim_inter {R : Type} [CommRing R] [IsDomain R] {c : ℕ} (hR : DimFormula R c)
    (hs : Function.Surjective (Int.cast : ℤ → R)) {X : Scheme.{0}} (t : X ⟶ Sp ℤ) [LocallyOfFiniteType t] (x : X)
    [Algebra R (X.residueField x)] [FaithfulSMul R (X.residueField x)] {U : X.Opens} (hU : IsAffineOpen U) (hx : x ∈ U) :
    ∃ e : ℕ, Algebra.trdeg R (X.residueField x) = e ∧
      topologicalKrullDim ((U : Set X) ∩ closure {x} : Set X) = (e + c : ℕ) := by
  have hA : (Int.castRingHom Γ(X, U)).FiniteType := by
    let φ := Spec.preimage (hU.fromSpec ≫ t)
    have hφ : Spec.map φ = hU.fromSpec ≫ t := Spec.map_preimage _
    have h := (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType) (φ := φ)).mp (hφ ▸ inferInstance)
    rwa [Subsingleton.elim (Int.castRingHom Γ(X, U)) φ.hom]
  letI : Algebra Γ(X, U) (X.presheaf.stalk x) := (X.presheaf.germ U x hx).hom.toAlgebra
  have hloc : IsLocalization.AtPrime (X.presheaf.stalk x) (hU.primeIdealOf ⟨x, hx⟩).asIdeal :=
    hU.isLocalization_stalk ⟨x, hx⟩
  obtain ⟨e, h₁, h₂⟩ := exists_dim_quotient_ker hR hs hA (X.evaluation U x hx).hom (by
    intro z
    obtain ⟨w, rfl⟩ := X.residue_surjective x z
    obtain ⟨⟨a, b⟩, h⟩ := IsLocalization.surj (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl (S := X.presheaf.stalk x) w
    have hu := (IsLocalization.map_units (X.presheaf.stalk x) b).map (X.residue x).hom
    refine ⟨a, b, (eq_div_iff hu.ne_zero).2 ?_⟩
    exact (map_mul (X.residue x).hom _ _).symm.trans (congrArg (X.residue x).hom h))
  refine ⟨e, h₁, ?_⟩
  have hk : RingHom.ker (X.evaluation U x hx).hom = (hU.primeIdealOf ⟨x, hx⟩).asIdeal := by
    ext f
    rw [RingHom.mem_ker]
    refine (X.evaluation_eq_zero_iff_notMem_basicOpen x hx f).trans ?_
    have h := hU.fromSpec_preimage_basicOpen f
    have h' : hU.fromSpec (hU.primeIdealOf ⟨x, hx⟩) ∈ X.basicOpen f ↔ f ∉ (hU.primeIdealOf ⟨x, hx⟩).asIdeal :=
      SetLike.ext_iff.1 h (hU.primeIdealOf ⟨x, hx⟩)
    rw [hU.fromSpec_primeIdealOf] at h'
    exact h'.not.trans not_not
  have h := topologicalKrullDim_range_inter_closure_eq (B := Γ(X, U)) hU.fromSpec (hU.primeIdealOf ⟨x, hx⟩)
  rw [← h₂, hk, ← h]
  have h3 := hU.fromSpec_primeIdealOf ⟨x, hx⟩
  have h4 := hU.range_fromSpec
  exact congrArg (fun s : Set X => topologicalKrullDim s)
    (congrArg₂ (· ∩ ·) h4.symm (congrArg (fun z => closure {z}) h3.symm))

theorem exists_hasDim {R : Type} [CommRing R] [IsDomain R] {c : ℕ} (hR : DimFormula R c)
    (hs : Function.Surjective (Int.cast : ℤ → R)) {X : Scheme.{0}} (t : X ⟶ Sp ℤ) [LocallyOfFiniteType t] (x : X)
    [Algebra R (X.residueField x)] [FaithfulSMul R (X.residueField x)] :
    ∃ e : ℕ, Algebra.trdeg R (X.residueField x) = e ∧ HasDim x (e + c) := by
  obtain ⟨U, hU, hxU, -⟩ := Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens (Opens.mem_top x)
  obtain ⟨e, h₁, h₂⟩ := exists_dim_inter hR hs t x hU hxU
  refine ⟨e, h₁, le_antisymm ?_ ?_⟩
  · refine topologicalKrullDim_le_of_forall_exists_isOpen fun z => ?_
    obtain ⟨V, hV, hzV, -⟩ := Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens (Opens.mem_top z.1)
    have hxV : x ∈ V := (specializes_iff_mem_closure.2 z.2).mem_open V.isOpen hzV
    obtain ⟨e', h₁', h₂'⟩ := exists_dim_inter hR hs t x hV hxV
    obtain rfl : e = e' := by exact_mod_cast h₁.symm.trans h₁'
    refine ⟨Subtype.val ⁻¹' (V : Set X), V.isOpen.preimage continuous_subtype_val, hzV, ?_⟩
    rw [← h₂']
    refine (topologicalKrullDim_eq_of_isEmbedding
      (Topology.IsEmbedding.subtypeVal.comp Topology.IsEmbedding.subtypeVal) ?_).ge
    rw [Set.range_comp, Subtype.range_val, Subtype.image_preimage_val, Set.inter_comm]
  · rw [← h₂]
    exact (Topology.IsEmbedding.inclusion Set.inter_subset_right).isInducing.topologicalKrullDim_le

theorem locallyOfFiniteType_of_isAmb {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} (h : IsAmb p) :
    LocallyOfFiniteType p := by
  obtain ⟨N, jN, _, hjN⟩ := h.isProjOver
  have := isProper_str k N
  have : IsProper p := hjN ▸ inferInstance
  infer_instance

theorem le_and_iff_of_dimFormula {R : Type} [CommRing R] [IsDomain R] {c : ℕ} (hR : DimFormula R c)
    (hs : Function.Surjective (Int.cast : ℤ → R)) {X Y : Scheme.{0}} (t : X ⟶ Sp ℤ) [LocallyOfFiniteType t]
    (π : Y ⟶ X) [LocallyOfFiniteType π] (y : Y) [Algebra R (X.residueField (π y))]
    [FaithfulSMul R (X.residueField (π y))] (d d' : ℕ) (hd : HasDim y d) (hd' : HasDim (π y) d') :
    d' ≤ d ∧ (π.residueDegree y ≠ 0 ↔ d = d') := by
  letI := (π.residueFieldMap y).hom.toAlgebra
  letI : Algebra R (Y.residueField y) := ((π.residueFieldMap y).hom.comp (algebraMap R _)).toAlgebra
  haveI : IsScalarTower R (X.residueField (π y)) (Y.residueField y) := IsScalarTower.of_algebraMap_eq' rfl
  haveI : FaithfulSMul R (Y.residueField y) := (faithfulSMul_iff_algebraMap_injective _ _).2
    ((π.residueFieldMap y).hom.injective.comp (FaithfulSMul.algebraMap_injective R _))
  haveI : Algebra.EssFiniteType (X.residueField (π y)) (Y.residueField y) :=
    RingHom.EssFiniteType.residueFieldMap (LocallyOfFiniteType.stalkMap π y)
  obtain ⟨e, h₁, h₂⟩ := exists_hasDim hR hs (π ≫ t) y
  obtain ⟨e', h₁', h₂'⟩ := exists_hasDim hR hs t (π y)
  obtain rfl : d = e + c := by exact_mod_cast hd.symm.trans h₂
  obtain rfl : d' = e' + c := by exact_mod_cast hd'.symm.trans h₂'
  have hadd := trdeg_add_eq R (X.residueField (π y)) (A := Y.residueField y)
  rw [h₁, h₁'] at hadd
  have hle : e' ≤ e := by exact_mod_cast (self_le_add_right _ _).trans_eq hadd
  refine ⟨by omega, ?_⟩
  change Module.finrank (X.residueField (π y)) (Y.residueField y) ≠ 0 ↔ _
  constructor
  · intro h
    have : Module.Finite (X.residueField (π y)) (Y.residueField y) := Module.finite_of_finrank_pos (Nat.pos_of_ne_zero h)
    rw [trdeg_eq_zero, add_zero] at hadd
    have : e' = e := by exact_mod_cast hadd
    rw [this]
  · intro h
    obtain rfl : e = e' := by omega
    have h0 : Algebra.trdeg (X.residueField (π y)) (Y.residueField y) = 0 := by
      rcases (Cardinal.add_eq_left_iff).1 hadd with h | h
      · exact absurd (le_trans (le_max_left _ _) h) (not_le.2 Cardinal.natCast_lt_aleph0)
      · exact h
    have : Algebra.IsAlgebraic (X.residueField (π y)) (Y.residueField y) := trdeg_eq_zero_iff.1 h0
    have : Module.Finite (X.residueField (π y)) (Y.residueField y) := Algebra.finite_of_essFiniteType_of_isAlgebraic
    exact Module.finrank_pos.ne'

theorem dim_le_and_residueDegree_ne_zero_iff : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k), IsAmb p → IsAmb q → ∀ (π : Y ⟶ X), π ≫ p = q → ∀ (y : Y) (d d' : ℕ), HasDim y d → HasDim (π y) d' → d' ≤ d ∧ (π.residueDegree y ≠ 0 ↔ d = d') := by
  intro k _ X Y p q hp hq π hπ y d d' hd hd'
  have := locallyOfFiniteType_of_isAmb hp
  have : LocallyOfFiniteType (π ≫ p) := hπ ▸ locallyOfFiniteType_of_isAmb hq
  have : LocallyOfFiniteType π := locallyOfFiniteType_of_comp π p
  have : IsFinite (spMap (Int.castRingHom k)) :=
    (IsFinite.SpecMap_iff _).2 (RingHom.finite_algebraMap.2 hp.finite)
  obtain ⟨l, hl⟩ := CharP.exists (X.residueField (π y))
  rcases CharP.char_is_prime_or_zero (X.residueField (π y)) l with h | rfl
  · haveI : Fact l.Prime := ⟨h⟩
    letI := ZMod.algebra (X.residueField (π y)) l
    exact le_and_iff_of_dimFormula (dimFormula_field (ZMod l)) (ZMod.intCast_surjective)
      (p ≫ spMap (Int.castRingHom k)) π y d d' hd hd'
  · haveI := CharP.charP_to_charZero (X.residueField (π y))
    exact le_and_iff_of_dimFormula dimFormula_int (fun n => ⟨n, rfl⟩)
      (p ≫ spMap (Int.castRingHom k)) π y d d' hd hd'

end GlobalTheory.DimDeg
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointClosureDimLeAndResidueDegreeNeZeroIffStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pointClosureDim_le_and_residueDegree_ne_zero_iff : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k), IsAmb p → IsAmb q → ∀ (π : Y ⟶ X), π ≫ p = q → ∀ (y : Y) (d d' : ℕ), HasDim y d → HasDim (π y) d' → d' ≤ d ∧ (π.residueDegree y ≠ 0 ↔ d = d') := by
  first | exact @GlobalTheory.DimDeg.dim_le_and_residueDegree_ne_zero_iff | exact GlobalTheory.DimDeg.dim_le_and_residueDegree_ne_zero_iff | (intros; apply GlobalTheory.DimDeg.dim_le_and_residueDegree_ne_zero_iff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyMumfordClassMulLeft
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyMumfordClassMulLeft
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem lam_mul_left_of_cube : ∀ (K : Type) [Field K] (A : AbVar K) (c : Pic A.X.left) (Y : Over (Sp K))
    (x x' y : Y ⟶ A.X), AbVar.lam c (x * x') y = AbVar.lam c x y + AbVar.lam c x' y := by
  intro K _ A c Y x x' y
  obtain ⟨L, hL, rfl⟩ := GlobalTheory.CechPic.cls_surj c
  have h := GlobalTheory.CubeTop.cubeTheorem (Sp K) A.X A.ab L hL Y x x' y
  have hl := LB.isLB_linComb hL (fun k : Fin 8 ↦ (![x * x' * y, x * x', x * y, x' * y, x, x', y, 1] k).left)
    ![1, -1, -1, -1, 1, 1, 1, -1]
  have e := (GlobalTheory.CechPic.cls_eq_zero_iff hl).2 h
  rw [GlobalTheory.CechPic.cls_linComb hL _ _ hl, Fin.sum_univ_eight] at e
  simp only [Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, neg_smul] at e
  rw [AbVar.lam_eq, AbVar.lam_eq, AbVar.lam_eq]
  simp only [GlobalTheory.CechPic.lam, _root_.mul_one]
  rw [← sub_eq_zero, ← e]
  abel

end GlobalTheory.AV.AbVar
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyMumfordClassMulLeftStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianVarietyMumfordClass_mul_left : ∀ (K : Type) [Field K] (A : AbVar K) (c : Pic A.X.left) (Y : Over (Sp K)) (x x' y : Y ⟶ A.X), AbVar.lam c (x * x') y = AbVar.lam c x y + AbVar.lam c x' y := by
  first | exact @GlobalTheory.AV.AbVar.lam_mul_left_of_cube | exact GlobalTheory.AV.AbVar.lam_mul_left_of_cube | (intros; apply GlobalTheory.AV.AbVar.lam_mul_left_of_cube <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMapCoordsOfSymmetricThetaIsomorphicFibre
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMapCoordsOfSymmetricThetaIsomorphicFibre
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UMin

theorem pCrd_of_symAt : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (g m n : ℕ) (o : Type) [CommRing o] (X : Scheme.{0}) (q : X ⟶ S) (f : X ⟶ PSpace o n) (S' : Scheme.{0}) (A : Over S') [GrpObj A] [IsCommMonObj A] (L' : LB A.left) (ρ' : LB.Gen (L'.pull (eSec A))) (Ω : Type) [Field Ω] [CharZero Ω] (x : Sp Ω ⟶ X) (x' : Sp Ω ⟶ S') (P : PolAV (Sp Ω)) (α : P.A.left ⟶ G.left) (α' : P.A.left ⟶ A.left) (θ : SecAt A L' x') (e : Fin (n + 1) → Ω), Odd m → n + 1 = m ^ (4 * g) → ThMap G L ρ m q f → L'.IsLB → ρ'.IsGen → P.g = g → IsGrpPullback P.A G (x ≫ q) α → LBIso P.L (L.pull α) → IsGrpPullback P.A A x' α' → LBIso P.L (L'.pull α') → IsGenSec A L' _ θ → SymAt A L' ρ' m x' θ e → PCrd (x ≫ f) e := by
  intro S G _ _ L ρ hL hρ g m n o _ X q f S' A _ _ L' ρ' Ω _ _ x x' P α α' θ e hm hn hf hL' hρ' hg hα hw hα' hw' hθ he
  have hpol : PolFib A L' g x' := ⟨P, α', hg, hα', hw'⟩
  obtain ⟨Ω', _, _, pt, c, -, -, -, hl, -⟩ := GlobalTheory.T.theta_constants_listed_finite_galois_extension S' A L' ρ' hL' hρ' g m (n + 1) Ω x' θ hm hn hpol
  have hgen := (GlobalTheory.T.principallyPolarisedFibre_exists_generator_stable S' A L' hL' g Ω x' hpol).2 θ hθ Ω' (algebraMap Ω Ω')
  have h₁ : HasTh₂ A L' ρ' m m (spMap (algebraMap Ω Ω') ≫ x') c c := hasTh_iff.1 ⟨_, pt, hgen, hl⟩
  obtain ⟨w, hw₀⟩ := id hw
  obtain ⟨ρP, hρP, -⟩ := exists_rigidificationPullbackCompatibleIso hα hw₀ hL P.isLB hρ
  haveI : IsCommMonObj P.A := P.isAb.comm
  have h₂ := (GlobalTheory.T.hasThetaConstantsTwoLevels_move_cartesian S' A L' ρ' hL' hρ' _ P.A P.L ρP x' α' P.isLB hρP hα' hw' m m _ _ Ω' _ c c).2 h₁
  have h₃ := (GlobalTheory.T.hasThetaConstantsTwoLevels_move_cartesian S G L ρ hL hρ _ P.A P.L ρP (x ≫ q) α P.isLB hρP hα hw m m _ _ Ω' _ c c).1 h₂
  rw [← Category.assoc] at h₃
  have h₄ := hf Ω' _ c (hasTh_iff.2 h₃)
  refine GlobalTheory.T.projectiveHomogeneousCoords_field_determine_descend.2.2 o Ω Ω' n _ e (algebraMap Ω Ω') ?_
  rw [← Category.assoc, funext (he Ω' _ pt c hl)]
  exact h₄

end GlobalTheory.UMin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMapCoordsOfSymmetricThetaIsomorphicFibreStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaMap_coords_of_symmetric_theta_isomorphic_fibre : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (g m n : ℕ) (o : Type) [CommRing o] (X : Scheme.{0}) (q : X ⟶ S) (f : X ⟶ PSpace o n) (S' : Scheme.{0}) (A : Over S') [GrpObj A] [IsCommMonObj A] (L' : LB A.left) (ρ' : LB.Gen (L'.pull (eSec A))) (Ω : Type) [Field Ω] [CharZero Ω] (x : Sp Ω ⟶ X) (x' : Sp Ω ⟶ S') (P : PolAV (Sp Ω)) (α : P.A.left ⟶ G.left) (α' : P.A.left ⟶ A.left) (θ : SecAt A L' x') (e : Fin (n + 1) → Ω), Odd m → n + 1 = m ^ (4 * g) → ThMap G L ρ m q f → L'.IsLB → ρ'.IsGen → P.g = g → IsGrpPullback P.A G (x ≫ q) α → LBIso P.L (L.pull α) → IsGrpPullback P.A A x' α' → LBIso P.L (L'.pull α') → IsGenSec A L' _ θ → SymAt A L' ρ' m x' θ e → PCrd (x ≫ f) e := by
  first | exact @GlobalTheory.UMin.pCrd_of_symAt | exact GlobalTheory.UMin.pCrd_of_symAt | (intros; apply GlobalTheory.UMin.pCrd_of_symAt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothWeightedLineBundleLogSectionNormProperties
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothWeightedLineBundleLogSectionNormProperties
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
open scoped ContDiff

set_option autoImplicit false

namespace GlobalTheory.Mix.SecNorm

theorem logSec_basic : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) (M : MLine p σ) (s : M.B.Sec), Measurable (M.logSec s) ∧ (∀ y : CxPts p σ, 0 < M.φ.nsq (secVal p σ s) y ↔ y ∈ ptsIn p σ (nonzeroLocus s)) ∧ (∀ y, CInfAt (M.φ.nsq (secVal p σ s)) y) ∧ ∀ (u : CxPts p σ → ℝ) (hu : ∀ y, CInfAt u y), ∀ y ∈ ptsIn p σ (nonzeroLocus s), (M.addFn u hu).logSec s y = M.logSec s y - u y / 2 := by
  intro k _ X p σ M s
  have hpos : ∀ y : CxPts p σ, 0 < M.φ.nsq (secVal p σ s) y ↔ y ∈ ptsIn p σ (nonzeroLocus s) := fun y => by
    rw [← secVal_ne_zero_iff s (mem_pick M.φ.isLB y), Weight.nsq, mul_pos_iff_of_pos_right (Real.exp_pos _),
      sq_pos_iff, norm_ne_zero_iff]
  refine ⟨?_, hpos, fun y => ?_, fun u hu y hy => ?_⟩
  · exact (Real.measurable_log.comp (M.cInf.continuous_nsq s).measurable).div_const 2
  · have hi := mem_pick M.φ.isLB y
    have ho := (isOpen_ptsIn (p := p) (σ := σ) _).mem_nhds hi
    have h1 : CInfAt (fun z => ‖ev p σ (M.B.U (pick M.φ.isLB y)) (s.f _) z‖ ^ 2) y :=
      ⟨_, Unit, inferInstance, fun _ => s.f _, fun v => ‖v ()‖ ^ 2, univ, hi, isOpen_univ, trivial,
        ((contDiff_apply ℝ (fun _ => ℂ) ()).norm_sq ℂ).contDiffOn, EventuallyEq.rfl⟩
    refine (h1.comp₂ (M.cInf _ y hi) (G := fun x => x.1 * Real.exp (-x.2))
      (contDiff_fst.mul contDiff_snd.neg.exp)).congr ?_
    exact eventually_of_mem ho fun z hz => M.φ.nsq_eq (secVal_mem s) hz
  · have h := (hpos y).2 hy
    change Real.log ((M.φ.addFn u).nsq (secVal p σ s) y) / 2 = Real.log (M.φ.nsq (secVal p σ s) y) / 2 - u y / 2
    rw [Weight.nsq_addFn, Real.log_mul h.ne' (Real.exp_pos _).ne', Real.log_exp]
    ring

end GlobalTheory.Mix.SecNorm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothWeightedLineBundleLogSectionNormPropertiesStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smoothWeightedLineBundle_logSectionNorm_properties : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) (M : MLine p σ) (s : M.B.Sec), Measurable (M.logSec s) ∧ (∀ y : CxPts p σ, 0 < M.φ.nsq (secVal p σ s) y ↔ y ∈ ptsIn p σ (nonzeroLocus s)) ∧ (∀ y, CInfAt (M.φ.nsq (secVal p σ s)) y) ∧ ∀ (u : CxPts p σ → ℝ) (hu : ∀ y, CInfAt u y), ∀ y ∈ ptsIn p σ (nonzeroLocus s), (M.addFn u hu).logSec s y = M.logSec s y - u y / 2 := by
  first | exact @GlobalTheory.Mix.SecNorm.logSec_basic | exact GlobalTheory.Mix.SecNorm.logSec_basic | (intros; apply GlobalTheory.Mix.SecNorm.logSec_basic <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameExponentialVolumeLarge
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt

namespace GlobalTheory.ThinBerg

open MeasureTheory
open scoped ENNReal

theorem pnorm_pos' {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) (la : Wt X.Ψ r)
    {P : Frame X.Ψ r → ℂ} {x : Frame X.Ψ r} (hx : x ∈ X.dom) (hP : P x ≠ 0) : 0 < X.pnorm la P x := by
  have hd : ∀ τ i, dmin X.Gm x τ i ≠ 0 := fun τ i h => by
    have := (hx τ).2 i
    rw [h] at this
    simp at this
  unfold Data.pnorm
  exact mul_pos (norm_pos_iff.2 hP) (Finset.prod_pos fun τ _ => Finset.prod_pos fun i _ =>
    Real.rpow_pos_of_pos (norm_pos_iff.2 (div_ne_zero (hd _ _) (hd _ _))) _)

theorem le_bergOn_of_ratio {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {σ : c.F →+* ℂ} (U : Unf Xo c σ r)
    {D : D7} (V : HSp D) (dict : GA D V → Σ k, Frame (U.X k).Ψ r) (hd : ∀ g, (dict g).2 ∈ (U.X (dict g).1).dom)
    (Z : Comp Xo c) (G : WTZ E) (y : FPt U.X) (P : FDSec U.X) (hP : P ∈ holSub U.X (modelWt U G)) {e : ℝ}
    (he : 0 < e) (hy : 0 < ptN (modelWt U G) P ⟨y.1, y.2.1⟩)
    (hb : ∀ z : FPt U.X, e * ptN (modelWt U G) P ⟨z.1, z.2.1⟩ ≤ ptN (modelWt U G) P ⟨y.1, y.2.1⟩) :
    ENNReal.ofReal (e ^ 2) ≤ bergOn U V dict Z G y := by
  set A : ℝ≥0∞ := ENNReal.ofReal (ptN (modelWt U G) P ⟨y.1, y.2.1⟩) with hA
  have hA0 : A ≠ 0 := by rw [hA]; exact (ENNReal.ofReal_pos.2 hy).ne'
  have hsup : supE U.X (modelWt U G) P ≤ ENNReal.ofReal e⁻¹ * A := by
    unfold supE
    refine iSup_le fun z => ?_
    rw [hA, ← ENNReal.ofReal_mul (inv_nonneg.2 he.le)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h := hb z
    rw [le_inv_mul_iff₀ he]
    exact h
  have hpet : petE V dict (muOn U V dict Z) (modelWt U G) P ≤ ENNReal.ofReal e⁻¹ * A :=
    (petE_le_supE V dict _ (muPart_univ_le V dict _) hd _ P).trans hsup
  unfold bergOn bergE
  refine le_trans ?_ (le_iSup₂_of_le P hP le_rfl)
  rw [ENNReal.le_div_iff_mul_le (Or.inr (pow_ne_zero 2 hA0)) (Or.inr (ENNReal.pow_ne_top ENNReal.ofReal_ne_top))]
  calc ENNReal.ofReal (e ^ 2) * petE V dict (muOn U V dict Z) (modelWt U G) P ^ 2
      ≤ ENNReal.ofReal (e ^ 2) * (ENNReal.ofReal e⁻¹ * A) ^ 2 := by gcongr
    _ = ENNReal.ofReal (e ^ 2 * e⁻¹ ^ 2) * A ^ 2 := by
        rw [mul_pow, ← mul_assoc, ENNReal.ofReal_mul (sq_nonneg e), ENNReal.ofReal_pow (inv_nonneg.2 he.le)]
    _ = A ^ 2 := by
        rw [← mul_pow, mul_inv_cancel₀ he.ne', one_pow, ENNReal.ofReal_one, one_mul]

end GlobalTheory.ThinBerg

namespace GlobalTheory.ThinBerg

open MeasureTheory

end GlobalTheory.ThinBerg
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHolomorphicUnitMatrixAtRationalMatrixValues
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHolomorphicUnitMatrixAtRationalMatrixValues
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ChernCalc

theorem holUnitAt_ratVal : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (s : ℕ) (T : Matrix (Fin s) (Fin s) X.Fn)
    (y : CxPts X.str σ), (∀ i j, RegAt (under y) (T i j)) → T.det ≠ 0 → RegAt (under y) (T.det)⁻¹ →
    HolUnitAt (atlas X σ) (fun z => T.map (ratVal · z)) y := by
  intro F _ σ X s T y hT hd hdi
  refine ⟨?_, fun c hc a b => ?_⟩
  · obtain ⟨ψ, hψ⟩ := exists_ratVal_hom y
    let T' : Matrix (Fin s) (Fin s) ((ratOf X).O (under y)).toSubring :=
      Matrix.of fun i j => ⟨T i j, mem_O_ratOf.2 (hT i j)⟩
    have e1 : T.map (ratVal · y) = T'.map ψ := by
      ext i j
      exact hψ (T' i j)
    have e2 : ((T'.det : ((ratOf X).O (under y)).toSubring) : X.Fn) = T.det :=
      (RingHom.map_det (((ratOf X).O (under y)).toSubring.subtype) T').trans rfl
    have hu : UnitAt (under y) T.det := (unitAt_iff hd).2 ⟨e2 ▸ mem_O_ratOf.1 T'.det.2, hdi⟩
    have hne := ratVal_ne_zero (y := y) hu
    rw [← e2, hψ] at hne
    show IsUnit (T.map (ratVal · y)).det
    rw [e1, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact isUnit_iff_ne_zero.2 hne
  · obtain ⟨U, hU, g, e⟩ := (hT a b).exists_fnOf
    have hyU : y ∈ ptsIn X.str σ U := mem_ptsIn.2 hU
    filter_upwards [(GlobalTheory.ChartGlue.isOpen_over c.e (isOpen_ptsIn U)).mem_nhds (GlobalTheory.ChartGlue.mem_over c.e hc hyU)] with v hv
    have hdv : DifferentiableAt ℂ (ev X.str σ U g ∘ c.e.symm) v :=
      (c.holo U g).differentiableAt ((GlobalTheory.ChartGlue.isOpen_over c.e (isOpen_ptsIn U)).mem_nhds hv)
    refine hdv.congr_of_eventuallyEq ?_
    filter_upwards [(GlobalTheory.ChartGlue.isOpen_over c.e (isOpen_ptsIn U)).mem_nhds hv] with u hu
    show ratVal (T a b) (c.e.symm u) = ev X.str σ U g (c.e.symm u)
    rw [← e, ratVal_fnOf hu.2]

end GlobalTheory.ChernCalc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHolomorphicUnitMatrixAtRationalMatrixValuesStatement
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isHolomorphicUnitMatrixAt_rational_matrix_values : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (s : ℕ) (T : Matrix (Fin s) (Fin s) X.Fn) (y : CxPts X.str σ), (∀ i j, RegAt (under y) (T i j)) → T.det ≠ 0 → RegAt (under y) (T.det)⁻¹ → HolUnitAt (atlas X σ) (fun z => T.map (ratVal · z)) y := by
  first | exact @GlobalTheory.ChernCalc.holUnitAt_ratVal | exact GlobalTheory.ChernCalc.holUnitAt_ratVal | (intros; apply GlobalTheory.ChernCalc.holUnitAt_ratVal <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReducedClosureOfPointProperties
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReducedClosureOfPointProperties
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory.ClosFacts

theorem range_closι {X : Scheme.{0}} (z : X) : range (closι z) = closure {z} :=
  range_redι (Closeds.closure {z})

theorem isIntegral_clos {X : Scheme.{0}} (z : X) : IsIntegral (clos z) :=
  isIntegral_red (Z := Closeds.closure {z}) isIrreducible_singleton.closure

theorem clos_facts : ∀ (X : Scheme.{0}) (z : X), ∃ _ : IsIntegral (clos z), closι z (genericPoint (clos z)) = z ∧ topologicalKrullDim (clos z) = topologicalKrullDim (closure ({z} : Set X)) ∧ ∀ (Y : Scheme.{0}) [IsIntegral Y] (π : Y ⟶ X), π (genericPoint Y) = z → ∃ g : Y ⟶ clos z, g ≫ closι z = π ∧ g (genericPoint Y) = genericPoint (clos z) ∧ g.residueDegree (genericPoint Y) = π.residueDegree (genericPoint Y) ∧ (IsClosedImmersion π → IsIso g) := by
  intro X z
  have hI := isIntegral_clos z
  have hr := range_closι z
  have hi : closι z (genericPoint (clos z)) = z := by
    have h₁ := (genericPoint_spec (clos z)).image (closι z).continuous
    rw [image_univ, hr, closure_closure] at h₁
    exact h₁.eq isGenericPoint_closure
  refine ⟨hI, hi, (topologicalKrullDim_eq_of_isEmbedding (closι z).isClosedEmbedding.isEmbedding hr), ?_⟩
  intro Y _ π hπ
  have : Surjective (Limits.pullback.snd (closι z) π) := ⟨by
    rw [← Set.range_eq_univ, Scheme.Pullback.range_snd, hr, ← hπ]
    exact eq_univ_of_forall fun y => ((genericPoint_specializes y).map π.continuous).mem_closure⟩
  have := isIso_of_isClosedImmersion_of_surjective (Limits.pullback.snd (closι z) π)
  obtain ⟨g, rfl⟩ : ∃ g : Y ⟶ clos z, g ≫ closι z = π :=
    ⟨inv (Limits.pullback.snd (closι z) π) ≫ Limits.pullback.fst (closι z) π, by
      rw [Category.assoc, Limits.pullback.condition, IsIso.inv_hom_id_assoc]⟩
  have hg : g (genericPoint Y) = genericPoint (clos z) :=
    (closι z).isClosedEmbedding.injective (hπ.trans hi.symm)
  refine ⟨g, rfl, hg, ?_, fun hc => ?_⟩
  · rw [GlobalTheory.CurveDegreesCompare.residueDegree_comp, GlobalTheory.Published.residueDegree_of_isClosedImmersion (closι z), one_mul]
  · have : IsClosedImmersion g := IsClosedImmersion.of_comp_isClosedImmersion g (closι z)
    have : Surjective g := ⟨by
      rw [← Set.range_eq_univ]
      have h₁ := (genericPoint_spec Y).image g.continuous
      rw [image_univ, g.isClosedEmbedding.isClosed_range.closure_eq, hg] at h₁
      exact h₁.def.symm.trans (genericPoint_spec (clos z)).def⟩
    exact isIso_of_isClosedImmersion_of_surjective g

end GlobalTheory.ClosFacts
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReducedClosureOfPointPropertiesStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reducedClosureOfPoint_properties : ∀ (X : Scheme.{0}) (z : X), ∃ _ : IsIntegral (clos z), closι z (genericPoint (clos z)) = z ∧ topologicalKrullDim (clos z) = topologicalKrullDim (closure ({z} : Set X)) ∧ ∀ (Y : Scheme.{0}) [IsIntegral Y] (π : Y ⟶ X), π (genericPoint Y) = z → ∃ g : Y ⟶ clos z, g ≫ closι z = π ∧ g (genericPoint Y) = genericPoint (clos z) ∧ g.residueDegree (genericPoint Y) = π.residueDegree (genericPoint Y) ∧ (IsClosedImmersion π → IsIso g) := by
  first | exact @GlobalTheory.ClosFacts.clos_facts | exact GlobalTheory.ClosFacts.clos_facts | (intros; apply GlobalTheory.ClosFacts.clos_facts <;> assumption)
end
end
