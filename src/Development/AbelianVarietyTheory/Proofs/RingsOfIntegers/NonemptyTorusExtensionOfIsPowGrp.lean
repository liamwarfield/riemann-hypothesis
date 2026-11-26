module

public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ValuationThetaRatioEqBilinear
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.RankAndGOfIsPowDeg
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.LevelFrameOfLaws
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.RosatiAdjPow
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsBoxSec

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.NonemptyTorusExtensionOfIsPowGrp
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.PowGrp

theorem nonempty_torusExtension_of_isPowGrp : ∀ (K : Type) [Field K] (G' G : Over (Spec (CommRingCat.of K))) [GrpObj G'] [GrpObj G] (j : ℕ), IsPowGrp G' G j → Nonempty (TorusExtension G) → Nonempty (TorusExtension G') := by
  intro K _ G' G _ _ j p hT
  obtain ⟨T⟩ := hT
  cases T with
  | mk X B hB q hqm0 hqf0 hqs0 hqc0 i him0 hker =>
    have pB := ReciprocityTheory.ChartRestriction.G.Out.powIsPowGrp B j
    have pT := GlobalTheory.SplitTorusPow.isPowGrp (Spec (CommRingCat.of K)) (AddEquiv.refl (Fin j → X))
    obtain ⟨q', hq, hqm, hqf, hqs, hqc, -⟩ := GlobalTheory.PowMap.main _ G' G _ B j p pB q
    obtain ⟨i', hi, him, -⟩ := GlobalTheory.PowMap.main _ _ _ G' G j pT p i
    exact ⟨{ X := Fin j → X
             addCommGroup := inferInstance
             free := inferInstance
             finite := inferInstance
             B := ReciprocityTheory.ChartRestriction.G.Out.powObj B j
             grpB := inferInstance
             isAbelian := (GlobalTheory.PowGrp.powers _ _ _ j pB).2.2.2.1 hB
             q := q'
             q_hom := hqm hqm0
             q_flat := hqf hqf0
             q_surjective := hqs hqs0
             q_quasiCompact := hqc hqc0
             i := i'
             i_hom := him him0
             isKernel := GlobalTheory.PowKernel.main _ _ _ G' G _ _ j pT p pB i q i' q' hi hq hker }⟩

theorem isSemiAbelian_pow : ∀ (S : Scheme.{0}) (G' G : Over S) [GrpObj G'] [IsCommMonObj G'] [GrpObj G] [IsCommMonObj G] (j : ℕ) (p : IsPowGrp G' G j), IsSemiAbelian G → IsSemiAbelian G' := by
  intro S G' G _ _ _ _ j p' hG
  obtain ⟨_, hs, hsep, hqc, hgc, hf⟩ := hG
  have hpow := GlobalTheory.PowGrp.powers S G' G j p'
  have hqg := GlobalTheory.PowGrp.quasiCompact_geomConnected_pow S G' G j p'
  refine ⟨inferInstance, hpow.1 hs, hpow.2.1 hsep, hqg.1 hqc, hqg.2 hs hgc, ?_⟩
  intro Ω _ _ x
  obtain ⟨px, -⟩ := GlobalTheory.isPowGrp_baseChange S _ x G' G j p'
  exact nonempty_torusExtension_of_isPowGrp Ω _ _ j px (hf Ω x)

end GlobalTheory.PowGrp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExpansionValueZero
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory

namespace ExpansionValueZero

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem cst_comp {A C : Type} [CommRing A] [CommRing C] {Z : Scheme.{0}} (q : Z ⟶ Sp C) (φ : A →+* C) (z : Z) (a : A) :
    cst (q ≫ spMap φ) z a = cst q z (φ a) := by
  rw [← H1.cst_stalkMap, H1.gs_spec, H1.cst_stalkMap, Category.comp_id]

theorem cst_sum {A : Type} [CommRing A] {Z : Scheme.{0}} (q : Z ⟶ Sp A) (z : Z) {K : Type} (S : Finset K) (a : K → A) :
    cst q z (∑ i ∈ S, a i) = ∑ i ∈ S, cst q z (a i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [cst, gs_eq q z ⊤ trivial, map_sum]

theorem exists_coeff {A : Type} [CommRing A] {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K K' : Type} [Fintype K]
    [Fintype K'] {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Sp A ⟶ X)} {ε' : K' → ℤ}
    (s : LB.Sec (LB.LinComb L φ ε)) (e : Sp A ⟶ Y) (t : LB.Gen (LB.LinComb L φ' ε')) (ht : t.IsGen)
    (h : FormEq (fun k => e ≫ φ k) ε φ' ε') :
    ∃ a : A, ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp A) (z : Z) (J), Good L z J →
      sval s (r ≫ e) z J = cst r z a * (val t r z J).val := by
  obtain ⟨s', hv⟩ := exists_sec hL (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim) (fun U _ f => by
      refine (Fintype.prod_sum_type _).trans (Eq.trans ?_ (Fintype.prod_empty _).symm)
      simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib]
      rw [h U f, mul_inv_cancel])
    (pullMulSec s e (LB.invGen L _ _ t) (DVR.invGen_isGen _ _ _ _ ht))
  have le : (⊤ : (Sp A).Opens) ≤ LB.wchart L (PEmpty.elim : PEmpty → (Sp A ⟶ X)) PEmpty.elim := fun _ _ =>
    Set.mem_iInter.2 fun k => k.elim
  obtain ⟨a, ha⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of A)).inv).2
    (((Sp A).presheaf.map (homOfLE le).op).hom (s'.f PEmpty.elim))
  refine ⟨a, fun Z r z J hJ => ?_⟩
  have e₁ := hv Z r z J hJ
  rw [sval_pullMulSec _ _ _ _ _ _ hJ, val_inv, sval_of s' r z J PEmpty.elim (fun k => k.elim)] at e₁
  have e₂ : cst r z a = sval s (r ≫ e) z J * ((val t r z J)⁻¹).val :=
    (congrArg (gs r z ⊤) ha).trans ((gs_res r z le trivial _).trans e₁)
  rw [e₂, Units.inv_mul_cancel_right]

section Geometry

variable {R : Type} [CommRing R] [IsDomain R] (I : Ideal R)

omit [IsDomain R] in
theorem eSec_fstG (e : ℕ) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] :
    eSec (thickObj R I e G) ≫ (fstG I e G).left = thick R I e ≫ eSec G := by
  show eSec (thickObj R I e G) ≫ pullback.fst G.hom (thick R I e) = _
  simp [eSec]

theorem eSec_pG {D : DegPre R} {e : ℕ} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
    [IsCommMonObj G] (g : GtCoord I D e G) :
    eSec (thickObj R I e G) ≫ g.pG.left = thick R I e ≫ eSec D.P.A := by
  have := g.q_hom
  have h : eSec (thickObj R I e G) ≫ g.q.left = eSec (thickObj R I e D.P.A) :=
    congrArg (·.left) (IsMonHom.one_hom g.q)
  rw [← eSec_fstG I e D.P.A, ← h, Category.assoc]
  rfl

theorem formEq_zero (D : DegPre R) (k : ℕ) (α : D.X) :
    FormEq (fun i => eSec D.P.A ≫ D.famφB α i) (DegPre.famε k) (fun _ : PUnit => eSec D.P.A)
      (fun _ => (k : ℤ) * 1) := by
  intro U _ f
  have a₀ : eSec D.P.A ≫ D.famφB α 0 = eSec D.P.A := Category.comp_id _
  have a₁ : eSec D.P.A ≫ D.famφB α 1 = eSec D.P.A ≫ D.famφB α 2 := by
    have : η[D.P.A] ≫ ((𝟙 D.P.A) * (toUnit _ ≫ D.c α)) = η[D.P.A] ≫ (toUnit _ ≫ D.c α) := by
      rw [MonObj.comp_mul, Category.comp_id]
      have : η[D.P.A] = (1 : 𝟙_ _ ⟶ D.P.A) := by simp [Hom.one_def]
      rw [this, _root_.one_mul]
    exact congrArg (fun z => z.left) this
  have a₃ : eSec D.P.A ≫ D.famφB α 3 = eSec D.P.A := by
    have : η[D.P.A] ≫ (toUnit D.P.A ≫ η[D.P.A]) = η[D.P.A] := by
      rw [← Category.assoc, comp_toUnit, toUnit_unit, Category.id_comp]
    exact congrArg (fun z => z.left) this
  rw [Fin.prod_univ_four, Fintype.prod_unique]
  simp only [a₀, a₁, a₃]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_zpow, DegPre.famε, Matrix.cons_val]
  module

theorem exists_value (D : DegPre R) (k : ℕ) (α : D.X) (g : D.SecB k α) :
    ∃ a : R, ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp R) (z : Z) (J), Good D.P.L z J →
      sval g (r ≫ eSec D.P.A) z J = cst r z a * (val (L := D.P.L) D.rig r z J ^ k).val := by
  obtain ⟨a, ha⟩ := exists_coeff (A := R) D.P.isLB g (eSec D.P.A) (GeneratorPullback.powGen D.P.L _ _ D.rig k)
    (powGen_isGen _ _ _ _ D.rig_gen k) (formEq_zero D k α)
  exact ⟨a, fun Z r z J hJ => (ha Z r z J hJ).trans (by rw [val_pow])⟩

end Geometry

section Congruence

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)


variable (I G) in
omit [IsDomain R] in
abbrev unitE (e : ℕ) : Sp (R ⧸ I ^ (e + 1)) ⟶ (thickObj R I e G).left := eSec (thickObj R I e G)

theorem wv_rig (e : ℕ) (z : Sp (R ⧸ I ^ (e + 1))) {J J'} (hJ : Good D.toPre.P.L z J) (hJ' : Good U.LG.L z J') :
    wv U e (unitE I G e) z (J (unitE I G e ≫ pGl U e)) (J' (thick R I e ≫ eSec G)) *
      val (L := U.LG.L) U.LG.rig (thick R I e) z J' = val (L := D.toPre.P.L) D.toPre.rig (thick R I e) z J := by
  have hp : unitE I G e ≫ pGl U e = thick R I e ≫ eSec D.toPre.P.A := eSec_pG I (U.gt e)
  have hf : unitE I G e ≫ fGl I G e = thick R I e ≫ eSec G := eSec_fstG I e G
  rw [hp]
  have m₁ : z ∈ unitE I G e ⁻¹ᵁ
      ((D.toPre.P.L.pull (U.gt e).pG.left).U (fun _ => J (thick R I e ≫ eSec D.toPre.P.A)) ⊓
        (U.LG.L.pull (fstG I e G).left).U (fun _ => J' (thick R I e ≫ eSec G))) :=
    ⟨mem_pull.2 ((congrArg (fun q => q z ∈ D.toPre.P.L.U (J (thick R I e ≫ eSec D.toPre.P.A))) hp).mpr (hJ _)),
      mem_pull.2 ((congrArg (fun q => q z ∈ U.LG.L.U (J' (thick R I e ≫ eSec G))) hf).mpr (hJ' _))⟩
  have m₂ : z ∈ thick R I e ⁻¹ᵁ (U.LG.L.pull (eSec G)).U (fun _ => J' (thick R I e ≫ eSec G)) :=
    mem_pull.2 (hJ' (thick R I e ≫ eSec G))
  have m₃ : z ∈ thick R I e ⁻¹ᵁ (D.toPre.P.L.pull (eSec D.toPre.P.A)).U
      (fun _ => J (thick R I e ≫ eSec D.toPre.P.A)) := mem_pull.2 (hJ (thick R I e ≫ eSec D.toPre.P.A))
  have W := congrArg (gm (𝟙 _) z _) (U.w_rig e (fun _ => J (thick R I e ≫ eSec D.toPre.P.A),
    fun _ => J' (thick R I e ≫ eSec G)) (_ ⊓ _ ⊓ _) (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right)
    inf_le_right)
  exact ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_rp₁ _ z _ _ _ (by exact ⟨⟨m₁, m₂⟩, m₃⟩) _)
    (gm_rp₁ _ z _ _ _ (by exact ⟨⟨m₁, m₂⟩, m₃⟩) _))).symm.trans (W.trans (gm_rp₁ _ z _ _ _ (by exact ⟨⟨m₁, m₂⟩, m₃⟩) _))

theorem value_sub_sum_mem (e k : ℕ) (σ : H0 U.LG.L k) (g : ∀ α : D.toPre.X, D.toPre.SecB k α)
    (hE : U.ExpandsAt e k σ g) (x : R)
    (hx : ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp R) (z : Z) (J), Good U.LG.L z J →
      sval σ (r ≫ eSec G) z J = cst r z x * (val (L := U.LG.L) U.LG.rig r z J ^ k).val)
    (a : D.toPre.X → R)
    (ha : ∀ α (Z : Scheme.{0}) (r : Z ⟶ Sp R) (z : Z) (J), Good D.toPre.P.L z J →
      sval (g α) (r ≫ eSec D.toPre.P.A) z J = cst r z (a α) * (val (L := D.toPre.P.L) D.toPre.rig r z J ^ k).val) :
    ∃ S : Finset D.toPre.X, ∀ T : Finset D.toPre.X, S ⊆ T → x - ∑ α ∈ T, a α ∈ I ^ (e + 1) := by
  obtain ⟨S, hS⟩ := expandsAt_val U e k σ g hE
  have hp : unitE I G e ≫ pGl U e = thick R I e ≫ eSec D.toPre.P.A := eSec_pG I (U.gt e)
  have hf : unitE I G e ≫ fGl I G e = thick R I e ≫ eSec G := eSec_fstG I e G
  have hc : ∀ (z : Sp (R ⧸ I ^ (e + 1))) (c : R),
      cst (thick R I e) z c = cst (𝟙 _) z (Ideal.Quotient.mk (I ^ (e + 1)) c) := fun z c => H1.gs_spec _ z c
  refine ⟨S, fun T hT => ?_⟩
  rw [← Ideal.Quotient.eq]
  refine H1.cst_ext fun z => ?_
  rw [← hc, ← hc, cst_sum]
  choose J hJ using fun ψ : Sp (R ⧸ I ^ (e + 1)) ⟶ D.toPre.P.A.left => exists_chart D.toPre.P.isLB (ψ z)
  choose J' hJ' using fun ψ : Sp (R ⧸ I ^ (e + 1)) ⟶ G.left => exists_chart U.LG.isLB (ψ z)
  have hJ : Good D.toPre.P.L z J := hJ
  have hJ' : Good U.LG.L z J' := hJ'
  obtain ⟨h₀, h₁⟩ := hS _ (unitE I G e) z J hJ
  have h₂ := h₁ (J' (thick R I e ≫ eSec G))
    ((congrArg (fun q => q z ∈ U.LG.L.U (J' (thick R I e ≫ eSec G))) hf).mpr (hJ' _))
  have hs : sv U k σ (unitE I G e ≫ fGl I G e) z (J' (thick R I e ≫ eSec G)) =
      cst (thick R I e) z x * (val (L := U.LG.L) U.LG.rig (thick R I e) z J' ^ k).val := by
    rw [hf]
    exact (sval_of σ _ z J' (fun _ => J' (thick R I e ≫ eSec G)) (fun _ => by rw [Category.comp_id])).symm.trans
      (hx _ _ z J' hJ')
  have ht : ∀ α, val (tG U e α) (unitE I G e) z J = 1 := fun α => by
    have := (val_pull hJ (tG U e α) (unitE I G e) (𝟙 _)).symm.trans
      ((val_corr hJ ((U.gt e).t_unit α) _).trans (val_one _))
    rwa [Category.id_comp] at this
  have hg : ∀ α, sval (g α) (unitE I G e ≫ pGl U e) z J =
      cst (thick R I e) z (a α) * (val (L := D.toPre.P.L) D.toPre.rig (thick R I e) z J ^ k).val := fun α => by
    rw [hp]; exact ha α _ _ z J hJ
  have hw := wv_rig U e z hJ hJ'
  refine (val (L := D.toPre.P.L) D.toPre.rig (thick R I e) z J ^ k).mul_left_inj.1 ?_
  rw [Finset.sum_mul, ← Finset.sum_subset hT (fun α _ hα => (hg α).symm.trans (h₀ α hα))]
  rw [hs, mul_left_comm, ← Units.val_mul, ← mul_pow] at h₂
  refine Eq.trans (by rw [← hw]) (h₂.trans (Finset.sum_congr rfl fun α _ => ?_))
  rw [ht, hg, Units.val_one, _root_.mul_one]

end Congruence

section Value

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  (D : DegData V (maximalIdeal V)) (F : Type) [Field F] [Algebra (FractionRing V) F]

variable {F} in
theorem le_val_of_mem_pow {ϖ : V} (hϖ : Irreducible ϖ) {v : AddValuation F (WithTop ℚ)} (hv : ValOver ϖ F v)
    (n : ℕ) {c : V} (hc : c ∈ maximalIdeal V ^ n) :
    (((n : ℕ) : ℚ) : WithTop ℚ) ≤ v (algebraMap (FractionRing V) F (algebraMap V (FractionRing V) c)) := by
  rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow] at hc
  obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 hc
  have h : HasVal ϖ (algebraMap V (FractionRing V) (ϖ ^ n)) (n : ℤ) := ⟨1, by simp⟩
  rw [map_mul, map_mul, AddValuation.map_mul, hv _ _ h]
  simpa using le_add_of_nonneg_left (GC.v_alg_nonneg hϖ hv b)

end Value

end ExpansionValueZero

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.TwistingStatementsOfLaws
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem twisting_statements_of_laws :
    Laws → TwistBaseChangeStatement → TWStatement ∧ FiniteOrderValuationInvariance ∧ PullbackValuationForwardBound := by
  intro hL hT

  have hG : GlobalFnsSt := hL.globalFns
  have hTW : TWStatement := TWM.tw_of hG (twistBCSpan_of hT) GlobalTheory.T.valuation_thetaRatio_eq_bilinear
  exact ⟨hTW, galois_fixed_adelic_matrices_descend hL hTW, pullback_valuation_forward_of (pullGen_of hG) (QuadraticAlgebraValuation.qAl_of hL)⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.TauBalPow
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.TauBalBox

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.BoxFamily

variable {R : Type} [CommRing R] [IsDomain R] {j : ℕ} {D D' : DegPre R}

theorem tau_val (D : DegPre R) {Z : Scheme.{0}} {y : Z} {J} (hJ : Good D.P.L y J) (p q : D.X) (r : Z ⟶ (TK R).left) :
    val (D.tau p q) r y J = val (D.psi (p + q)) r y J * (val (D.psi p) r y J)⁻¹ * (val (D.psi q) r y J)⁻¹ *
      (val D.rigK r y J)⁻¹ := by
  unfold DegPre.tau
  rw [val_mul hJ, val_mul hJ, val_mul hJ, val_inv, val_inv, val_inv]

private theorem inv_mul_mul_mul_inv_mul_eq_commGroup {G : Type*} [CommGroup G] (A B C E a b c e : G) :
    A⁻¹ * B * C * E⁻¹ * (a * b⁻¹ * c⁻¹ * e⁻¹) = A⁻¹ * a * (B⁻¹ * b)⁻¹ * (C⁻¹ * c)⁻¹ * (E * e)⁻¹ := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem tau_box (pD : IsPowDeg D' D j) {y : (TK R).left} {J J'} (hJ : Good D.P.L y J) (hJ' : Good D'.P.L y J')
    (p q : D'.X) :
    ((om pD.w y J J' (cP D' (TK R) p * cP D' (TK R) q).left)⁻¹ * om pD.w y J J' (cP D' (TK R) p).left *
      om pD.w y J J' (cP D' (TK R) q).left *
      (om pD.w y J J' (𝟙 _ ≫ (toUnit (TK R)).left ≫ eSec D'.P.A))⁻¹) * val (D'.tau p q) (𝟙 _) y J' =
      ∏ i, val (D.tau (pD.xe p i) (pD.xe q i)) (𝟙 _) y J := by
  have hc : ∀ x : D'.X, 𝟙 _ ≫ D'.xK x = (cP D' (TK R) x).left := fun x => by
    simp only [Category.id_comp, DegPre.xK, ptK, cP]
  have hpq : cP D' (TK R) (p + q) = cP D' (TK R) p * cP D' (TK R) q := by
    unfold cP
    rw [D'.c_add, padd, comp_lift_assoc]
    rfl
  have h1 := psi_val pD hJ hJ' (p + q) (𝟙 _)
  have h2 := psi_val pD hJ hJ' p (𝟙 _)
  have h3 := psi_val pD hJ hJ' q (𝟙 _)
  have h4 := rig_val pD hJ hJ' (𝟙 _)
  rw [hc, hpq] at h1
  rw [hc] at h2 h3
  have e : ∀ i, val (D.tau (pD.xe p i) (pD.xe q i)) (𝟙 _) y J =
      val (D.psi (pD.xe (p + q) i)) (𝟙 _) y J * (val (D.psi (pD.xe p i)) (𝟙 _) y J)⁻¹ *
        (val (D.psi (pD.xe q i)) (𝟙 _) y J)⁻¹ * (val D.rigK (𝟙 _) y J)⁻¹ := fun i => by
    rw [tau_val D hJ, map_add (f := _), Pi.add_apply]
  rw [Finset.prod_congr rfl (fun i _ => e i), Finset.prod_mul_distrib, Finset.prod_mul_distrib,
    Finset.prod_mul_distrib, Finset.prod_inv_distrib, Finset.prod_inv_distrib, Finset.prod_inv_distrib, ← h1, ← h2,
    ← h3, ← h4, tau_val D' hJ' p q (𝟙 _)]
  exact inv_mul_mul_mul_inv_mul_eq_commGroup _ _ _ _ _ _ _ _

theorem rosatiφ_pr {S : Scheme.{0}} {A A' : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A']
    (π : A' ⟶ A) [IsMonHom π] {f g : A ⟶ A} {f' g' : A' ⟶ A'} (hf : f' ≫ π = π ≫ f) (hg : g' ≫ π = π ≫ g)
    (a : Fin 6) : rosatiφ A' f' g' a ≫ π.left = (π ⊗ₘ π).left ≫ rosatiφ A f g a := by
  fin_cases a <;>
    simp [rosatiφ, padd, ← Over.comp_left, comp_lift_assoc, IsMonHom.mul_hom, lift_map_assoc, hf, hg,
      tensorHom_fst_assoc, tensorHom_snd_assoc, tensorHom_fst, tensorHom_snd]

private theorem mul_eq_of_four_relations_commGroup {G : Type*} [CommGroup G] (X1 X2 X3 X4 LinearSubstitution X6 Eo t1 t2 U P1 P2 PU : G)
    (hT1 : X1⁻¹ * X2 * X3 * Eo⁻¹ * t1 = P1) (hT2 : X4⁻¹ * LinearSubstitution * X6 * Eo⁻¹ * t2 = P2)
    (hBU : X1 * X2⁻¹ * X3⁻¹ * X4⁻¹ * LinearSubstitution * X6 * U = PU) (hB : P1 * PU = P2) : t1 * U = t2 := by
  subst hT1 hBU hB
  apply mul_left_cancel (a := X4⁻¹ * LinearSubstitution * X6 * Eo⁻¹)
  rw [hT2]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

private theorem mul_inv_inv_inv_mul_mul_eq_one {G : Type*} [CommGroup G] (x : G) : x * x⁻¹ * x⁻¹ * x⁻¹ * x * x = 1 := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_one]
  abel

theorem tauBal_pow : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (j : ℕ) (D D' : DegPre R) (pD : IsPowDeg D' D j) (f g : D.P.A ⟶ D.P.A) (f' g' : D'.P.A ⟶ D'.P.A), IsMonHom f → IsMonHom g → IsMonHom f' → IsMonHom g' → (∀ i, f' ≫ pD.pw.pr i = pD.pw.pr i ≫ f) → (∀ i, g' ≫ pD.pw.pr i = pD.pw.pr i ≫ g) → RosatiAdj D.P.A D.P.L f g → ∀ (a a' : D.X → D.X) (b b' : D'.X → D'.X), (∀ x i, pD.xe (b x) i = a (pD.xe x i)) → (∀ x i, pD.xe (b' x) i = a' (pD.xe x i)) → (∀ y, D.c (a y) = D.c y ≫ f) → (∀ y, D.c (a' y) = D.c y ≫ g) → D.TauBal f g a a' → D'.TauBal f' g' b b' := by
  intro hG R _ _ j D D' pD f g f' g' hfm hgm hfm' hgm' hf hg hr a a' b b' hb hb' ca ca' hB
  have hcb : ∀ x, cP D' (TK R) x ≫ f' = cP D' (TK R) (b x) := fun x => by
    unfold cP
    rw [Category.assoc]
    congr 1
    refine pD.pw.lim.hom_ext (fun k => ?_)
    rcases k with ⟨i⟩
    simp only [Fan.mk_π_app, Category.assoc, hf i, pD.c_pr, ← reassoc_of% (pD.c_pr x i), hb, ca]
  have hcb' : ∀ x, cP D' (TK R) x ≫ g' = cP D' (TK R) (b' x) := fun x => by
    unfold cP
    rw [Category.assoc]
    congr 1
    refine pD.pw.lim.hom_ext (fun k => ?_)
    rcases k with ⟨i⟩
    simp only [Fan.mk_π_app, Category.assoc, hg i, pD.c_pr, ← reassoc_of% (pD.c_pr x i), hb', ca']
  unfold DegPre.TauBal
  intro u' hu' h0' y y'
  obtain ⟨u, hu, h0⟩ := exists_ros hG D.P.isAb D.P.isLB f g hr
  apply corr_of_val D'.P.isLB
  intro z J' hJ'
  obtain ⟨J, hJ⟩ := exists_good_at D.P.isLB z
  rw [val_mul hJ', val_pull hJ', Category.id_comp]
  have T1 := tau_box pD hJ hJ' (b y) y'
  have T2 := tau_box pD hJ hJ' y (b' y')
  have HB : ∀ i, val (D.tau (pD.xe (b y) i) (pD.xe y' i)) (𝟙 _) z J *
      val u (D.pt2 (pD.xe y i) (pD.xe y' i)) z J = val (D.tau (pD.xe y i) (pD.xe (b' y') i)) (𝟙 _) z J := fun i => by
    rw [hb, hb']
    have := val_corr hJ (hB u hu h0 (pD.xe y i) (pD.xe y' i)) (𝟙 _)
    rwa [val_mul hJ, val_pull hJ, Category.id_comp] at this
  have hpt : ∀ i, D'.pt2 y y' ≫ (pD.pw.pr i ⊗ₘ pD.pw.pr i).left = D.pt2 (pD.xe y i) (pD.xe y' i) := fun i => by
    show (lift (cP D' (TK R) y) (cP D' (TK R) y')).left ≫ _ = (lift (cP D (TK R) _) (cP D (TK R) _)).left
    rw [← Over.comp_left, lift_map, cPoint_pr pD, cPoint_pr pD]
  have hψ : ∀ i k, rosatiφ D'.P.A f' g' k ≫ (pD.pw.pr i).left =
      (pD.pw.pr i ⊗ₘ pD.pw.pr i).left ≫ rosatiφ D.P.A f g k := fun i k => by
    have := pD.pw.hom i
    exact rosatiφ_pr (pD.pw.pr i) (hf i) (hg i) k
  have hp : Function.Surjective (D'.P.A ⊗ D'.P.A).hom.appTop.hom := by
    have h1 := surj_comp (surj_snd hG D'.P.isAb D'.P.A) (hG _ D'.P.A D'.P.isAb).2
    rwa [Over.w] at h1
  have hone : ∀ {Z : Scheme.{0}} (z₀ : Z) (J₀ : (Z ⟶ D'.P.A.left) → D'.P.L.ι), Good D'.P.L z₀ J₀ → ∀ (r : Z ⟶ (𝟙_ (Over (Spec (CommRingCat.of R)))).left), val u' (r ≫ zero2 D'.P.A) z₀ J₀ = 1 := by
    intro Z z₀ J₀ hJ₀ r
    have := val_corr hJ₀ h0' r
    rwa [val_pull hJ₀, val_one] at this
  have hcond : ∀ (y₀ : (𝟙_ (Over (Spec (CommRingCat.of R)))).left) J₀ J₀', Good D.P.L y₀ J₀ → Good D'.P.L y₀ J₀' →
      (∏ k, bw pD.w (zero2 D'.P.A ≫ rosatiφ D'.P.A f' g' k) y₀
        (fun i => J₀ ((zero2 D'.P.A ≫ rosatiφ D'.P.A f' g' k) ≫ (pD.pw.pr i).left))
        (J₀' (zero2 D'.P.A ≫ rosatiφ D'.P.A f' g' k)) ^ rosatiε k) * val u' (zero2 D'.P.A) y₀ J₀' =
      ∏ i, val u (zero2 D'.P.A ≫ (pD.pw.pr i ⊗ₘ pD.pw.pr i).left) y₀ J₀ := by
    intro y₀ J₀ J₀' hJ₀ hJ₀'
    have hz : ∀ i, zero2 D'.P.A ≫ (pD.pw.pr i ⊗ₘ pD.pw.pr i).left = 𝟙 _ ≫ zero2 D.P.A := fun i => by
      have := pD.pw.hom i
      rw [Category.id_comp]
      unfold zero2
      rw [← Over.comp_left, lift_map, IsMonHom.one_hom]
    have hz' := hone y₀ J₀' hJ₀' (𝟙 _)
    rw [Category.id_comp] at hz'
    have hu0 : val u (𝟙 _ ≫ zero2 D.P.A) y₀ J₀ = 1 := by
      have := val_corr hJ₀ h0 (𝟙 _)
      rwa [val_pull hJ₀, val_one] at this
    simp only [hz, hu0, Finset.prod_const_one, hz', _root_.mul_one]
    have PR0 := prod_ros f' g' (η[D'.P.A]) (η[D'.P.A]) (fun ψ => om pD.w y₀ J₀ J₀' ψ)
    beta_reduce at PR0
    have e1 : (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D'.P.A) = η[D'.P.A] := by
      show toUnit _ ≫ η[D'.P.A] = η[D'.P.A]
      rw [toUnit_unit, Category.id_comp]
    have e2 : η[D'.P.A] * η[D'.P.A] = η[D'.P.A] := by rw [← e1, _root_.mul_one]
    rw [IsMonHom.one_hom, IsMonHom.one_hom, e2] at PR0
    exact PR0.trans (mul_inv_inv_inv_mul_mul_eq_one _)
  have BU := CubBox.box_unique D.P.isLB D'.P.isLB pD.w pD.w_gen hψ hu' hu ((D'.P.A ⊗ D'.P.A).hom) (zero2 D'.P.A)
    (by unfold zero2; exact Over.w (lift η[D'.P.A] η[D'.P.A])) hp hcond (TK R).left (D'.pt2 y y') z J J' hJ hJ'
  simp only [hpt] at BU
  have BU2 : (∏ k, om pD.w z J J' ((lift (cP D' (TK R) y) (cP D' (TK R) y')).left ≫ rosatiφ D'.P.A f' g' k) ^
      rosatiε k) * val u' (D'.pt2 y y') z J' = ∏ i, val u (D.pt2 (pD.xe y i) (pD.xe y' i)) z J := BU
  have PR := prod_ros f' g' (cP D' (TK R) y) (cP D' (TK R) y') (fun ψ => om pD.w z J J' ψ)
  beta_reduce at PR
  rw [hcb, hcb'] at PR
  rw [PR] at BU2
  exact mul_eq_of_four_relations_commGroup _ _ _ _ _ _ _ _ _ _ _ _ _ T1 T2 BU2
    (by rw [← Finset.prod_mul_distrib]; exact Finset.prod_congr rfl (fun i _ => HB i))

end GlobalTheory.TauBalBox
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IntegralFamilyLevelOne
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem integralFamily_levelOne : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ → ∀ (D : DegData V (maximalIdeal V)) (Q : D.toPre.X → ℤ), QForm.IsQ D.toPre ϖ Q → ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v → ∀ (θ : Fam D.toPre F 1) (g : ∀ α : D.toPre.X, D.toPre.SecB 1 α), (∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε 1) (θ.s α) (D.toPre.famφB α) (DegPre.famε 1) (g α) (DegPre.prB D.toPre F).left 1) → NuGe D Q F v 1 θ 0 ∧ ∀ χ, χ ≠ 0 → ∃ g' : D.toPre.SecB 1 χ, SecIsMul D.toPre.P.A.hom ϖ (g χ) g' := by
  intro V _ _ _ ϖ hϖ D Q hQ F _ _ v hv θ g hg
  have hν : NuGe D Q F v 1 θ 0 := by
    refine (n1a V ϖ hϖ D Q hQ F v hv 1 le_rfl {0} (fun χ => ⟨0, Finset.mem_singleton_self _, χ, by simp⟩) θ 0).2 ?_
    intro α hα
    rw [Finset.mem_singleton] at hα
    subst hα
    refine ⟨1, fun _ => 1, fun _ => g 0, fun _ => θ.s 0, fun _ => hg 0, fun _ => ?_, fun j => ?_⟩
    · rw [QForm.Q_zero hϖ D hQ]; simp
    · simp [DegPre.constBF]
  refine ⟨hν, fun χ hχ => ?_⟩
  obtain ⟨n, a₀, τ, τF, hτ, hva, hsum⟩ := hν χ
  have hb : ∀ i, 0 < v (a₀ i) := fun i => by
    refine lt_of_lt_of_le ?_ (hva i)
    have h1 : (1 : ℚ) ≤ (Q χ : ℚ) := by exact_mod_cast QForm.Q_pos hϖ D hQ hχ
    have h2 : (0 : ℚ) < 0 + (Q χ : ℚ) / ((1 : ℕ) : ℚ) := by simp; exact_mod_cast (by linarith : (0 : ℚ) < (Q χ : ℚ))
    exact_mod_cast h2
  have vc : ∀ (t : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F χ) (DegPre.famε 1))) (x : F)
      {Z : Scheme.{0}} (q : Z ⟶ (DegPre.BF D.toPre F).left) (z : Z) (j), q z ∈ LB.wchart D.toPre.P.L (DegPre.famφ D.toPre F χ) j →
      gs q z (LB.wchart D.toPre.P.L (DegPre.famφ D.toPre F χ) j) (DegPre.constBF D.toPre F x _ * t.f j) =
        cst (q ≫ (fst (TF (R := V) F) D.toPre.P.A).left) z x *
          gs q z (LB.wchart D.toPre.P.L (DegPre.famφ D.toPre F χ) j) (t.f j) := fun t x Z q z j hz =>
    (gs_mul q z _ hz _ _).trans (congrArg₂ (· * ·) ((gs_res q z le_top hz _).trans
      (gs_pull q (fst (TF (R := V) F) D.toPre.P.A).left z ⊤ trivial _)) rfl)
  have div₁ := H1.dvd_of_comb hϖ D.toPre F v hv (g χ) τ a₀ hb (fun Z q z J hJ =>
    (H1.sval_scal (hg χ) q z hJ).symm.trans
      ((congrArg (gs _ z _) (hsum _)).trans ((H1.gs_sum q z _ (hJ.mem _ q) _).trans (Finset.sum_congr rfl fun i _ =>
        (vc (τF i) (a₀ i) q z _ (hJ.mem _ q)).trans (congrArg₂ (· * ·) rfl (H1.sval_scal (hτ i) q z hJ))))))
  have := D.toPre.P.isAb.smooth
  exact exists_div_sec D.toPre.P.A.hom hϖ.ne_zero (g χ) div₁

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.BoxFamLinearIndependent
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory

namespace BoxFamIndep

open ReciprocityTheory.ChartRestriction.G.Geo.Tor BoxIndep

theorem exists_tensor_pow (F O : Type) [Field F] [CommRing O] [Algebra F O] {A : Type} {m : ℕ} (β : A → Fin m → O)
    (hβ : ∀ c : Fin m → F, (∀ α, ∑ l, c l • β α l = 0) → c = 0) (j : ℕ) :
    ∃ (B : Type) (_ : CommRing B) (_ : Algebra F B) (em : Fin j → (O →ₐ[F] B)),
      ∀ c : (Fin j → Fin m) → F,
        (∀ α : Fin j → A, ∑ a, c a • ∏ i, em i (β (α i) (a i)) = 0) → c = 0 := by
  induction j with
  | zero =>
    refine ⟨F, inferInstance, inferInstance, fun i => i.elim0, fun c hc => ?_⟩
    have := hc (fun i => i.elim0)
    funext a
    rw [Fintype.sum_unique] at this
    rw [Subsingleton.elim a default]
    simpa using this
  | succ j ih =>
    obtain ⟨B, _, _, em, h⟩ := ih
    refine ⟨TensorProduct F O B, inferInstance, inferInstance,
      Fin.cons Algebra.TensorProduct.includeLeft
        (fun i => (Algebra.TensorProduct.includeRight).comp (em i)), fun c hc => ?_⟩
    have key : ∀ (α₀ : A) (α : Fin j → A), ∑ l : Fin m, β α₀ l ⊗ₜ[F]
        (∑ a : Fin j → Fin m, c (Fin.cons l a) • ∏ i, em i (β (α i) (a i))) = 0 := by
      intro α₀ α
      rw [← hc (Fin.cons α₀ α), ← (Fin.consEquiv (fun _ : Fin (j+1) => Fin m)).sum_comp, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [TensorProduct.tmul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      simp only [Fin.consEquiv_apply, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, AlgHom.comp_apply]
      rw [← map_prod, Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply,
        Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one, _root_.one_mul, TensorProduct.tmul_smul]
    have key2 : ∀ l, (fun a : Fin j → Fin m => c (Fin.cons l a)) = 0 := fun l => h _ fun α => by
      refine (Module.forall_dual_apply_eq_zero_iff F _).1 fun φ => ?_
      refine congrFun (hβ (fun l => φ (∑ a : Fin j → Fin m, c (Fin.cons l a) • ∏ i, em i (β (α i) (a i))))
        fun α₀ => ?_) l
      have := congrArg (fun t => TensorProduct.rid F O (LinearMap.lTensor O φ t)) (key α₀ α)
      set_option synthInstance.maxHeartbeats 100000 in
        simpa only [map_sum (LinearMap.lTensor O φ), map_sum (TensorProduct.rid F O), LinearMap.lTensor_tmul,
        TensorProduct.rid_tmul, map_zero] using this
    funext a
    have := congrFun (key2 (a 0)) (Fin.tail a)
    simp only [Fin.cons_self_tail] at this
    exact this

variable {X Z : Scheme.{0}}

theorem exists_test {F : Type} [Field F] (p : X ⟶ Spec (CommRingCat.of F)) (x : X) {A : Type} {U : A → X.Opens}
    (hx : ∀ α, x ∈ U α) {m : ℕ} (s : ∀ α, Fin m → Γ(X, U α))
    (hs : ∀ c : Fin m → F, (∀ α, ∑ l, germOf p x (c l) * gs (𝟙 X) x (U α) (s α l) = 0) → c = 0) (j : ℕ) :
    ∃ (Z : Scheme.{0}) (q : Z ⟶ Spec (CommRingCat.of F)) (r : Fin j → (Z ⟶ X)), (∀ i, r i ≫ p = q) ∧
      (∀ i z α, r i z ∈ U α) ∧ ∀ c : (Fin j → Fin m) → F,
        (∀ (α : Fin j → A) z, ∑ a, germOf q z (c a) * ∏ i, gs (r i) z (U (α i)) (s (α i) (a i)) = 0) → c = 0 := by
  let : Algebra F (X.presheaf.stalk x) := (germOf p x).toAlgebra
  obtain ⟨B, _, _, em, h⟩ := exists_tensor_pow F _ (fun α l => gs (𝟙 X) x (U α) (s α l))
    (fun c hc => hs c fun α => by
      have := hc α
      simp only [Algebra.smul_def] at this
      exact this) j
  refine ⟨Spec (CommRingCat.of B), Spec.map (CommRingCat.ofHom (algebraMap F B)),
    fun i => (Spec.map (CommRingCat.ofHom (em i).toRingHom) : _ ⟶ Spec (X.presheaf.stalk x)) ≫ X.fromSpecStalk x,
    fun i => ?_, fun i z α => fromSpecStalk_mem x (hx α) _, fun c hc => ?_⟩
  · rw [Category.assoc, fromSpecStalk_comp]
    refine (Spec.map_comp _ _).symm.trans (congrArg Spec.map ?_)
    ext a
    exact (em i).commutes a
  · refine h c fun α => eq_zero_of_germOf (B := CommRingCat.of B) _ fun z => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hc α z, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Algebra.smul_def, map_mul, map_prod]
    congr 1
    · rw [← Category.id_comp (Spec.map _), germOf_map]; rfl
    · refine Finset.prod_congr rfl fun i _ => ?_
      rw [gs_fromSpecStalk x (hx _)]
      exact (germOf_map (B := X.presheaf.stalk x) (𝟙 _) (CommRingCat.ofHom (em i).toRingHom) z _).symm

variable {R : Type} [CommRing R] [IsDomain R] {F : Type} [Field F] [Algebra (FractionRing R) F] {k : ℕ}

theorem sum_f {D : DegPre R} {K : Type} (S : Finset K) (b : K → Fam D F k) (α : D.X) (jj) :
    ((∑ l ∈ S, b l).s α).f jj = ∑ l ∈ S, ((b l).s α).f jj := by
  classical
  induction S using Finset.induction_on with
  | empty => rfl
  | insert a S ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, add_f, ih]

theorem gs_comb {D : DegPre R} {K : Type} [Fintype K] (c : K → F) (b : K → Fam D F k) (α : D.X) (jj)
    (r : Z ⟶ (DegPre.BF D F).left) (z : Z) (hz : r z ∈ LB.wchart D.P.L (DegPre.famφ D F α) jj) :
    gs r z (LB.wchart D.P.L (DegPre.famφ D F α) jj) (((∑ l, c l • b l).s α).f jj) =
      ∑ l, germOf (B := CommRingCat.of F) (r ≫ (fst (TF (R := R) F) D.P.A).left) z (c l) *
        gs r z (LB.wchart D.P.L (DegPre.famφ D F α) jj) (((b l).s α).f jj) := by
  refine (congrArg _ (sum_f _ _ α jj)).trans ?_
  refine (gs_fsum r z _ hz _ _).trans (Finset.sum_congr rfl fun l _ => ?_)
  refine (gs_mul r z _ hz _ _).trans (congrArg (· * _) ?_)
  exact (gs_res r z le_top hz _).trans
    ((gs_pull r (fst (TF (R := R) F) D.P.A).left z ⊤ trivial _).trans (germOf_apply _ _ _).symm)

theorem main {j : ℕ} {D D' : DegPre R} (pD : IsPowDeg D' D j) {m : ℕ} (b : Fin m → Fam D F k)
    (hb : LinearIndependent F b) (b' : (Fin j → Fin m) → Fam D' F k)
    (hb' : ∀ a, IsBoxFam pD F k (b' a) (fun i => b (a i))) : LinearIndependent F b' := by
  refine Fintype.linearIndependent_iff.2 fun c hc => congrFun (?_ : c = 0)
  have := D.P.isAb.smooth
  have := D.P.isAb.geomConnected
  have hg := geometricallyIntegral_of_smooth_of_geometricallyConnected_fibres D.P.A.hom
  have hint : IsIntegral (DegPre.BF D F).left :=
    hg.geometrically_isIntegral (TF (R := R) F).hom _ _ (IsPullback.of_hasPullback (TF (R := R) F).hom D.P.A.hom).flip
  choose J₀ hJ₀ using fun χ : (DegPre.BF D F).left ⟶ D.P.A.left =>
    exists_chart D.P.isLB (χ (genericPoint (DegPre.BF D F).left))
  have hx : ∀ α, genericPoint (DegPre.BF D F).left ∈
      LB.wchart D.P.L (DegPre.famφ D F α) (fun a => J₀ (DegPre.famφ D F α a)) :=
    fun α => Set.mem_iInter.2 fun a => hJ₀ _
  obtain ⟨Z, q, r, hq, hr, H⟩ := exists_test (F := F) (fst (TF (R := R) F) D.P.A).left _ hx
    (fun α l => ((b l).s α).f (fun a => J₀ (DegPre.famφ D F α a)))
    (fun c hc => funext <| Fintype.linearIndependent_iff.1 hb c <| fam_ext fun α jj => by
      refine fn_ext fun y hy => congrArg _ ?_
      have hy' : genericPoint (DegPre.BF D F).left ∈ LB.wchart D.P.L (DegPre.famφ D F α) jj :=
        ((genericPoint_spec _).mem_open_set_iff (TopologicalSpace.Opens.isOpen _)).mpr ⟨y, trivial, hy⟩
      apply germ_injective_of_isIntegral _ _ hy'
      refine (gs_eq (𝟙 _) _ _ hy' _).symm.trans (Eq.trans ?_ (map_zero _).symm)
      refine (sec_trans _ (𝟙 _) _ hy' (hx α)).trans ?_
      refine (congrArg _ ((gs_comb c b α _ (𝟙 _) _ (hx α)).trans ?_)).trans (mul_zero _)
      rw [Category.id_comp]
      exact hc α) j
  let T : Over (Spec (CommRingCat.of R)) := Over.mk (q ≫ (TF (R := R) F).hom)
  let q' : T ⟶ TF (R := R) F := Over.homMk q rfl
  let r' : Fin j → (T ⟶ DegPre.BF D F) := fun i => Over.homMk (r i) (by
    rw [← Over.w (fst (TF (R := R) F) D.P.A), ← Category.assoc, hq]; rfl)
  let ρ : T ⟶ DegPre.BF D' F := lift q' (Fan.IsLimit.lift pD.pw.lim fun i => r' i ≫ snd _ _)
  have hρ : ∀ i, ρ ≫ TF (R := R) F ◁ pD.pw.pr i = r' i := fun i => by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, whiskerLeft_fst, lift_fst]
      exact Over.OverMorphism.ext (hq i).symm
    · rw [Category.assoc, whiskerLeft_snd, ← Category.assoc, lift_snd]
      exact Fan.IsLimit.fac pD.pw.lim _ i
  have hρ' : ∀ i, (ρ.left : Z ⟶ _) ≫ prB pD F i = r i := fun i => congrArg (fun g => g.left) (hρ i)
  have hρq : (ρ.left : Z ⟶ _) ≫ (fst (TF (R := R) F) D'.P.A).left = q :=
    congrArg (fun g => g.left) (lift_fst q' (Fan.IsLimit.lift pD.pw.lim fun i => r' i ≫ snd _ _))
  refine H c fun α z => ?_
  obtain ⟨α', rfl⟩ := pD.xe.surjective α
  choose J hJ using fun ψ : Z ⟶ D.P.A.left => exists_chart D.P.isLB (ψ z)
  have hJ : Good D.P.L z J := hJ
  choose J' hJ' using fun ψ : Z ⟶ D'.P.A.left => exists_chart D'.P.isLB (ψ z)
  have hJ' : Good D'.P.L z J' := hJ'
  have hm := hJ'.mem (DegPre.famφ D' F α') (ρ.left : Z ⟶ _)
  have E := (gs_comb c b' α' _ (ρ.left : Z ⟶ _) z hm).symm.trans
    ((congrArg (fun s : Fam D' F k => gs (Y := Z) ρ.left z _ ((s.s α').f _)) hc).trans (gs_zero _ _ _ hm))
  rw [hρq] at E
  have E' := fun a => BoxPhi.fam_val pD (hb' a) α' (Z := Z) ρ.left z hJ hJ'
  simp only [hρ'] at E'
  obtain ⟨u, hu⟩ : ∃ u : Z.presheaf.stalk z, ∀ a, u * sval (Z := Z) ((b' a).s α') ρ.left z J' =
      ∏ i, sval ((b (a i)).s (pD.xe α' i)) (r i) z J := ⟨_, E'⟩
  obtain ⟨v, hv⟩ : ∃ v : Fin j → Z.presheaf.stalk z, ∀ i l,
      gs (r i) z (LB.wchart D.P.L (DegPre.famφ D F (pD.xe α' i)) (fun a => J₀ (DegPre.famφ D F (pD.xe α' i) a)))
        (((b l).s (pD.xe α' i)).f (fun a => J₀ (DegPre.famφ D F (pD.xe α' i) a))) =
      v i * sval ((b l).s (pD.xe α' i)) (r i) z J :=
    ⟨_, fun i l => sec_trans _ (r i) z (hr i z _) (hJ.mem _ (r i))⟩
  refine Eq.trans (Finset.sum_congr rfl fun a _ => ?_) ((Finset.mul_sum _ _ ((∏ i, v i) * u)).symm.trans
    ((congrArg _ E).trans (mul_zero _)))
  refine Eq.trans (congrArg _ (((Finset.prod_congr rfl fun i _ => hv i (a i)).trans Finset.prod_mul_distrib).trans
    (congrArg _ (hu a).symm))) ?_
  exact (congrArg _ (_root_.mul_assoc _ _ _).symm).trans (mul_left_comm _ _ _)

end BoxFamIndep

theorem boxFam_linearIndependent : ∀ (R : Type) [CommRing R] [IsDomain R] (j : ℕ) (D D' : DegPre R) (pD : IsPowDeg D' D j) (F : Type) [Field F] [Algebra (FractionRing R) F] (k m : ℕ) (b : Fin m → Fam D F k), LinearIndependent F b → ∀ b' : (Fin j → Fin m) → Fam D' F k, (∀ a, IsBoxFam pD F k (b' a) (fun i => b (a i))) → LinearIndependent F b' :=
  fun _ _ _ _ _ _ pD _ _ _ _ _ b hb b' hb' => BoxFamIndep.main pD b hb b' hb'

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SpanEqTopOfCard
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory

namespace BoxSpan

theorem span_eq_top_of_card {C M : Type} [CommRing C] (hC : IsField C) [AddCommGroup M] [Module C M]
    {I I' : Type} [Fintype I] [Fintype I'] (b : I → M) (hli : LinearIndependent C b)
    (hsp : Submodule.span C (Set.range b) = ⊤) (v : I' → M) (hv : LinearIndependent C v)
    (hc : Fintype.card I' = Fintype.card I) : Submodule.span C (Set.range v) = ⊤ := by
  let _ : Field C := hC.toField
  have hb : Module.finrank C M = Fintype.card I :=
    Module.finrank_eq_card_basis (Module.Basis.mk hli hsp.ge)
  have _ : Module.Finite C M := Module.Finite.of_basis (Module.Basis.mk hli hsp.ge)
  exact hv.span_eq_top_of_card_eq_finrank' (hc.trans hb.symm)

theorem exists_basis (hS : SecBaseChangeSt) {K : Type} [Field K] (P : PolAV (Spec (CommRingCat.of K))) (n : ℕ)
    (hn : 1 ≤ n) (F : Type) [CommRing F] (q : Spec (CommRingCat.of F) ⟶ Spec (CommRingCat.of K)) :
    ∃ b : Fin (n ^ P.g) → SecM P.A P.L n (Over.mk q), LinearIndependent Γ((Over.mk q).left, ⊤) b ∧
      Submodule.span Γ((Over.mk q).left, ⊤) (Set.range b) = ⊤ := by
  obtain ⟨V, hpV, b, hb⟩ := hS (Spec (CommRingCat.of K)) P n hn default
  have hbo : (baseOver (Spec (CommRingCat.of K))).hom = 𝟙 _ := rfl
  have hr : Set.range q ⊆ Set.range V.ι := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    have : q x = default := Subsingleton.elim _ _
    rw [this]
    exact hpV
  obtain ⟨t, rfl⟩ : ∃ t : Spec (CommRingCat.of F) ⟶ V.toScheme, t ≫ V.ι ≫ (baseOver (Spec (CommRingCat.of K))).hom = q := by
    refine ⟨IsOpenImmersion.lift V.ι q hr, ?_⟩
    rw [hbo]
    erw [Category.comp_id]
    exact IsOpenImmersion.lift_fac _ _ _
  unfold LPow at b
  choose b' hb' using fun i => GlobalTheory.IndivisibleSection.exists_pull_chart (b i) (homAt (V := V) t ▷ P.A).left
    (fun _ => (snd (baseAt (V := V) t) P.A).left) (fun _ => by rw [← Over.comp_left, whiskerRight_snd])
  obtain ⟨hli, hsp⟩ := hb F t b' (fun i j => hb' i j _)
  exact ⟨fun i => SecM.ofSec P.A (b' i), hli, hsp⟩

theorem comb_apply {S : Scheme.{0}} (A : Over S) [GrpObj A] (L : LB A.left) (a : ℤ) (T : Over S) {I : Type}
    [Fintype I] (c : I → Γ(T.left, ⊤)) (v : I → SecM A L a T) (jj) :
    (∑ l, c l • v l).1 jj = ∑ l, liftFun A _ (c l) * (v l).1 jj := by
  rw [Submodule.coe_sum, Finset.sum_apply]
  exact Finset.sum_congr rfl fun l _ => rfl

private theorem ΓSpecIso_inv_hom_apply (F : Type) [CommRing F] (x : Γ(Spec (CommRingCat.of F), ⊤)) :
    (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom x) = x := by
  rw [← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply]

end BoxSpan


open BoxSpan in
theorem boxProduct_span : Laws → ∀ (R : Type) [CommRing R] [IsDomain R] (j : ℕ) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (pA : IsPowPolAV A' A j) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ), 1 ≤ k → ∀ s : LB.Sec (LB.LinComb A'.L (K := Fin 1) (fun _ => (snd (TFK (R := R) F) A'.A).left) (fun _ => (k : ℤ))), ∃ (n : ℕ) (c : Fin n → F) (t : Fin n → Fin j → LB.Sec (LB.LinComb A.L (K := Fin 1) (fun _ => (snd (TFK (R := R) F) A.A).left) (fun _ => (k : ℤ)))) (t' : Fin n → LB.Sec (LB.LinComb A'.L (K := Fin 1) (fun _ => (snd (TFK (R := R) F) A'.A).left) (fun _ => (k : ℤ)))), (∀ l, (∀ (Z : Scheme.{0}) (r : Z ⟶ ((TFK (R := R) F) ⊗ A'.A).left) (z : Z) (J J'), Geo.Tor.Good A.L z J → Geo.Tor.Good A'.L z J' → (bw pA.w (r ≫ (snd (TFK (R := R) F) A'.A).left) z (fun i => J ((r ≫ (snd (TFK (R := R) F) A'.A).left) ≫ (pA.pr i).left)) (J' (r ≫ (snd (TFK (R := R) F) A'.A).left)) ^ k).val * Geo.Tor.sval (t' l) r z J' = ∏ i, Geo.Tor.sval (t l i) (r ≫ ((TFK (R := R) F) ◁ pA.pr i).left) z J)) ∧ ∀ jj, s.f jj = ∑ l, liftFun A'.A _ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (c l)) * (t' l).f jj := by
  intro hL R _ _ j A A' pA F _ _ k hk s
  obtain ⟨b, hbi, -⟩ := exists_basis hL.secBaseChange A k hk F (TFK (R := R) F).hom
  obtain ⟨b', hbi', hbs'⟩ := exists_basis hL.secBaseChange A' k hk F (TFK (R := R) F).hom
  let σ : Fin (k ^ A.g) → LB.Sec (LB.LinComb A.L (K := Fin 1) (fun _ => (snd (TFK (R := R) F) A.A).left)
      (fun _ => (k : ℤ))) := fun l => ⟨(b l).1, fun i i' => (b l).2 i i'⟩
  have hb : ∀ c : Fin (k ^ A.g) → F, (∀ jj, ∑ l, liftFun A.A _
      ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (c l)) * (σ l).f jj = 0) → c = 0 := by
    intro c hc
    have h0 := Fintype.linearIndependent_iff.mp hbi
      (fun l => (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (c l)) (by
        apply Subtype.ext
        funext jj
        exact (comb_apply A.A A.L (k : ℤ) (Over.mk (TFK (R := R) F).hom) _ b jj).trans (hc jj))
    funext l
    have h1 := congrArg (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom (h0 l)
    rw [← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply, map_zero] at h1
    exact h1
  choose t' ht' using fun a : Fin j → Fin (k ^ A.g) =>
    exists_boxSec_pow_ext R j A A' pA F k (fun i => σ (a i))
  have hind := boxProduct_linearIndependent R j A A' pA F k (k ^ A.g) σ hb t' ht'
  have hli : LinearIndependent Γ((Over.mk (TFK (R := R) F).hom).left, ⊤)
      (fun a => (SecM.ofSec A'.A (t' a) : SecM A'.A A'.L (k : ℤ) (Over.mk (TFK (R := R) F).hom))) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg a
    have hc := hind (fun a => (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom (g a)) (by
      intro jj
      have h1 := congrArg (fun x : SecM A'.A A'.L (k : ℤ) (Over.mk (TFK (R := R) F).hom) => x.1 jj) hg
      have h2 := (comb_apply A'.A A'.L (k : ℤ) (Over.mk (TFK (R := R) F).hom) g
        (fun a => SecM.ofSec A'.A (t' a)) jj).symm.trans h1
      refine Eq.trans (Finset.sum_congr rfl fun a _ => ?_) h2
      exact congrArg (fun x => liftFun (T := TFK (R := R) F) A'.A _ x * (t' a).f jj) (ΓSpecIso_inv_hom_apply F (g a)))
    have h2 := congrFun hc a
    rw [Pi.zero_apply] at h2
    rw [← ΓSpecIso_inv_hom_apply F (g a), h2, map_zero]
  have hfield : IsField Γ((Over.mk (TFK (R := R) F).hom).left, ⊤) :=
    MulEquiv.isField (Field.toIsField F)
      (Scheme.ΓSpecIso (CommRingCat.of F)).commRingCatIsoToRingEquiv.toMulEquiv
  have hcard : Fintype.card (Fin j → Fin (k ^ A.g)) = Fintype.card (Fin (k ^ A'.g)) := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, polAV_g_of_isPowPolAV _ j A A' pA, ← pow_mul,
      mul_comm]
    exact (Fintype.card_fin _).symm
  have hspan := span_eq_top_of_card hfield b' hbi' hbs' _ hli hcard
  have hmem : (SecM.ofSec A'.A s : SecM A'.A A'.L (k : ℤ) (Over.mk (TFK (R := R) F).hom)) ∈
      Submodule.span Γ((Over.mk (TFK (R := R) F).hom).left, ⊤)
        (Set.range fun a => (SecM.ofSec A'.A (t' a) : SecM A'.A A'.L (k : ℤ) (Over.mk (TFK (R := R) F).hom))) := by
    rw [hspan]
    exact Submodule.mem_top
  obtain ⟨g, hg⟩ := Submodule.mem_span_range_iff_exists_fun _ |>.mp hmem
  let e := Fintype.equivFin (Fin j → Fin (k ^ A.g))
  refine ⟨Fintype.card (Fin j → Fin (k ^ A.g)), fun l => (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom (g (e.symm l)),
    fun l i => σ (e.symm l i), fun l => t' (e.symm l), fun l => ht' (e.symm l), ?_⟩
  intro jj
  have h1 := congrArg (fun x : SecM A'.A A'.L (k : ℤ) (Over.mk (TFK (R := R) F).hom) => x.1 jj) hg
  have h2 := (comb_apply A'.A A'.L (k : ℤ) (Over.mk (TFK (R := R) F).hom) g
    (fun a => SecM.ofSec A'.A (t' a)) jj).symm.trans h1
  refine h2.symm.trans ?_
  rw [← e.symm.sum_comp]
  refine Finset.sum_congr rfl fun l _ => ?_
  congr 1
  congr 1
  exact (ΓSpecIso_inv_hom_apply F _).symm

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.NuGeIffOfIsActOfOfQkToAkU
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem nuGe_iff_of_isActOf_of_qkToAkU : Laws → TWStatement → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ → ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G] (U : Unif (maximalIdeal V) D A G), Geo.Tor.ExpBijF U.toUnifPre → ∀ (Q : D.toPre.X → ℤ), QForm.IsQ D.toPre ϖ Q → ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v → ∀ (k : ℕ), 1 ≤ k → ∀ (w : LB.Iso (A.L.pull U.gen.hom.left) (U.LG.L.pull (pullback.fst G.hom (jK V)))), w.IsGen → ∀ (θ : ThetaGrp A.A A.L (k : ℤ) (TFK (R := V) F)) (p : QkPt D.toPre F k), QkToAkU U.toUnifPre F k p θ.pt → ∀ (n : ℕ), 1 ≤ n → θ.pt ^ n = 1 → LB.Gen.Corr A.L _ _ _ _ (Out.powGen A.A A.L (k : ℤ) θ n) (LB.oneGen A.L) → ∀ (t t' : LB.Sec (LPow A.A A.L (k : ℤ) (TFK (R := V) F))) (s s' : Fam D.toPre F k), U.ExpandsF F k w t s → U.ExpandsF F k w t' s' → IsActOf A.A A.L (k : ℤ) θ t t' → ∀ r : ℚ, NuGe D Q F v k s r ↔ NuGe D Q F v k s' r := by
  intro hL hTW V _ _ _ ϖ hϖ D A G _ _ U hB Q hQ F _ _ v hv k hk w hw θ p hp n hn hx hc t t' s s' hs hs' hact r
  obtain ⟨w₀, hw₀, hΦθ⟩ := (hp w hw).2 θ rfl
  obtain ⟨hB₁, hB₂⟩ := hB F k hk w hw
  obtain ⟨Φ, hΦ⟩ := phiFun_of hL V (maximalIdeal V) D F k hk p w₀ hw₀
  choose act hact' using fun x : LB.Sec (LPow A.A A.L (k : ℤ) (TFK (R := V) F)) =>
    (VVRank.exists_isTwistPull A.A A.isLB θ.isGen x : ∃ y, IsActOf A.A A.L (k : ℤ) θ x y)
  have hfin : FinOrd D F k p w₀ 1 := by
    refine ⟨n, hn, fun ss ts hss => ?_⟩
    obtain ⟨t₀, ht₀, -⟩ := hB₂ (ss 0)
    have key : ∀ (i : ℕ) (hi : i < n + 1), U.ExpandsF F k w (act^[i] t₀) (ss ⟨i, hi⟩) := by
      intro i
      induction i with
      | zero => exact fun _ => ht₀
      | succ i ih =>
        intro hi
        obtain ⟨s₁, hs₁, -⟩ := hB₁ (act^[i + 1] t₀)
        have h₁ := (hΦ _ _).1 (hΦθ _ _ _ _ (ih (by omega)) hs₁
          (by rw [Function.iterate_succ_apply']; exact hact' _))
        obtain ⟨h₂, h₃⟩ := hss ⟨i, by omega⟩
        have h₄ : ss ⟨i + 1, hi⟩ = s₁ :=
          ((ReciprocityTheory.ChartRestriction.G.DVR.isSmul_iff _ _ _).1 h₃).trans
            ((one_smul F _).trans (((hΦ _ _).1 h₂).trans h₁.symm))
        rw [h₄]; exact hs₁
    have hcyc := thetaGrp_act_iterate_eq_of_pow_eq_one _ A.A A.L A.isLB (k : ℤ) _ θ n hx hc
      (fun i => act^[i.val] t₀) (fun i => by
        show IsActOf _ _ _ θ (act^[i.val] t₀) (act^[i.val + 1] t₀)
        rw [Function.iterate_succ_apply']; exact hact' _)
    have he : act^[n] t₀ = t₀ := by
      have ext : ∀ a b : LB.Sec (LPow A.A A.L (k : ℤ) (TFK (R := V) F)), (∀ j, a.f j = b.f j) → a = b := by
        rintro ⟨a, _⟩ ⟨b, _⟩ h
        obtain rfl : a = b := funext h
        rfl
      exact ext _ _ hcyc
    have h₅ := key n (Nat.lt_succ_self n)
    rw [he] at h₅
    have h₆ : ss (Fin.last n) = ss 0 := (hB₁ t₀).unique h₅ ht₀
    intro α j
    rw [h₆]
  exact galois_fixed_adelic_matrices_descend hL hTW V ϖ hϖ D Q hQ F v hv k hk p w₀ hw₀ 1 one_ne_zero hfin s s' s'
    (hΦθ t t' s s' hs hs' hact) ((ReciprocityTheory.ChartRestriction.G.DVR.isSmul_iff _ _ _).2 (one_smul F _).symm) r

end GlobalTheory
end
