module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSemiAbelianModelSplitSpecialFibre
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SecCmp
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AbelianPartIsoIsMonHomAndRigidified
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsScalarFormTraceForm
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LineBundleTrivialIsoDescendField

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniformisedModel
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniformisedModel
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UniformisedModel

theorem exists_finite_factor {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {p : ℕ} [Fact p.Prime]
    (y₀ : R →+* PadicAlgCl p) (Fs : Finset (PadicAlgCl p)) :
    ∃ (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (_ : FiniteDimensional ℚ_[p] K) (y : R →+* K),
      (∀ a, (y a : PadicAlgCl p) = y₀ a) ∧ ∀ x ∈ Fs, x ∈ K := by
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := ℤ) (A := R)
  let t : Finset (PadicAlgCl p) := s.image y₀ ∪ Fs
  let K := IntermediateField.adjoin ℚ_[p] (t : Set (PadicAlgCl p))
  have hK : FiniteDimensional ℚ_[p] K :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  have hy : ∀ a, y₀ a ∈ K := fun a => by
    have ha : a ∈ Algebra.adjoin ℤ (s : Set R) := hs ▸ Algebra.mem_top
    induction ha using Algebra.adjoin_induction with
    | mem x hx =>
      exact IntermediateField.subset_adjoin _ _
        (Finset.mem_coe.2 (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hx)))
    | algebraMap n => rw [eq_intCast, map_intCast]; exact intCast_mem K n
    | add a b _ _ ha hb => rw [map_add (f := _)]; exact K.add_mem ha hb
    | mul a b _ _ ha hb => rw [map_mul]; exact K.mul_mem ha hb
  exact ⟨K, hK, y₀.codRestrict K hy, fun _ => rfl, fun x hx =>
    IntermediateField.subset_adjoin _ _ (Finset.mem_coe.2 (Finset.mem_union_right _ hx))⟩

theorem spMap_spMap {R R₁ R₂ : Type} [CommRing R] [CommRing R₁] [CommRing R₂] (a : R →+* R₁) (b : R₁ →+* R₂) :
    spMap b ≫ spMap a = spMap (b.comp a) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem exists_polBaseChange (hB : PolBaseChangeSt) {S S' : Scheme.{0}} (f : S' ⟶ S) (P : PolAV S) :
    ∃ (P' : PolAV S') (φ : P'.A.left ⟶ P.A.left), IsGrpPullback P'.A P.A f φ ∧ LBIso P'.L (P.L.pull φ) := by
  obtain ⟨P', φ, hφ, -, hm, t, ht⟩ := hB S S' f P
  refine ⟨P', φ, ⟨hφ, fun T x y x₀ y₀ hx hy => ?_⟩, LBIso.symm ⟨t, ht⟩⟩
  rw [(Over.OverMorphism.ext hx : x₀ = toBase hφ.w x), (Over.OverMorphism.ext hy : y₀ = toBase hφ.w y), ← hm]
  rfl

theorem exists_isGrpPullback_jK {V K R : Type} [CommRing V] [IsDomain V] [CommRing K] [CommRing R] (a : V →+* K)
    (b : K →+* FractionRing V) (e : b.comp a = algebraMap V (FractionRing V)) (u : R →+* K)
    (G : Over (Sp V)) [GrpObj G] (A : Over (Sp R)) [GrpObj A] {φ : pullback G.hom (spMap a) ⟶ A.left}
    (hφ : IsGrpPullback ((Over.pullback (spMap a)).obj G) A (spMap u) φ) :
    ∃ ψ, IsGrpPullback ((Over.pullback (jK V)).obj G) A (spMap (b.comp u)) ψ := by
  obtain ⟨i, hi, -⟩ := grpPullback_iso (isGrpPullback_pullback G (jK V))
    (((isGrpPullback_pullback ((Over.pullback (spMap a)).obj G) (spMap b)).comp
      (isGrpPullback_pullback G _)).congr (by rw [spMap_spMap, e]) rfl)
  exact ⟨_, ((isGrpPullback_of_iso i).comp ((isGrpPullback_pullback _ (spMap b)).comp hφ)).congr
    (by rw [Category.id_comp, spMap_spMap]) rfl⟩

end GlobalTheory.UniformisedModel

namespace GlobalTheory


open UniformisedModel in
theorem exists_uniformised_model : GlobalTheory.Published.SemistableReductionSt → ThmUSt → PolBaseChangeSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (Fs : Finset (PadicAlgCl p)), ∃ u : ρ.UTest p y₀, ∀ x ∈ Fs, x ∈ Set.range (algebraMap (FractionRing u.V) (PadicAlgCl p)) := by
  intro hN hU hB o Ω _ _ _ _ S ρ p _ y₀ Fs
  haveI := ArithBase.ft (o := o) (Ω := Ω)
  haveI : Algebra.FiniteType o S.R := (Subalgebra.fg_iff_finiteType S.R).1 S.fg
  haveI : Algebra.FiniteType ℤ S.R := Algebra.FiniteType.trans (S := o) inferInstance inferInstance
  obtain ⟨K, _, y, hy, hFs⟩ := exists_finite_factor y₀ Fs
  obtain ⟨P, φ₀, hφ₀, -⟩ := exists_polBaseChange hB (spMap y) ρ.P
  obtain ⟨K', h, _, _, G, _, hG, hE, φ, hφ⟩ := exists_semiAbelian_model_split_specialFibre hN p K P
  let V := integralClosure ℤ_[p] K'
  let e : FractionRing V ≃ₐ[V] K' := FractionRing.algEquiv V K'
  let y' : S.R →+* K' := (IntermediateField.inclusion h).toRingHom.comp y
  let b : K' →+* FractionRing V := e.symm.toRingEquiv.toRingHom
  have hb : b.comp (algebraMap V K') = algebraMap V (FractionRing V) := RingHom.ext fun x => e.symm.commutes x
  obtain ⟨ψ, hψ⟩ := exists_isGrpPullback_jK (algebraMap V K') b hb y' G ρ.P.A
    ((hφ.comp hφ₀).congr (spMap_spMap _ _) rfl)
  obtain ⟨A, χ, hχ, hL⟩ := exists_polBaseChange hB (spMap (b.comp y')) ρ.P
  obtain ⟨gen, hgen, -⟩ := grpPullback_iso hψ hχ
  haveI : CharZero V := charZero_integralClosure_padicInt
  haveI := hG.comm
  have hc : IsAdicComplete (IsLocalRing.maximalIdeal V) V :=
    CompleteFiniteExtension.isAdicComplete_of_finite_local ℤ_[p] V
  obtain ⟨D, U, -⟩ := hU V hc A G hG hE
    (SymBaseChange.hypS_baseChange _ _ ρ.P.A A.A _ χ ρ.P.L A.L ρ.P.isLB A.isLB hχ hL ρ.hypS) gen hgen
  let c : FractionRing V →+* PadicAlgCl p := (algebraMap K' (PadicAlgCl p)).comp e.toRingEquiv.toRingHom
  have hcb : ∀ x : K', c (b x) = x := fun x => congrArg Subtype.val (e.apply_symm_apply x)
  refine ⟨{ V := V, complete := hc, alg := c.toAlgebra, norm_le := fun x => ?_, yK := b.comp y'
            fac := RingHom.ext fun a => (hcb (y' a)).trans (hy a), A := A, φ := χ, cart := hχ, lb := hL, G := G
            semi := hG, D := D, U := U }, fun x hx => ⟨b ⟨x, h (hFs x hx)⟩, hcb _⟩⟩
  refine (mem_integralClosure_padicInt_iff K' (e x)).symm.trans ⟨fun hx => ⟨⟨e x, hx⟩, ?_⟩, ?_⟩
  · exact e.injective (e.commutes _)
  · rintro ⟨v, rfl⟩
    rw [e.commutes]
    exact v.2

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniformisedModelStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_uniformised_model' : GlobalTheory.Published.SemistableReductionSt → ThmUSt → PolBaseChangeSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (Fs : Finset (PadicAlgCl p)), ∃ u : ρ.UTest p y₀, ∀ x ∈ Fs, x ∈ Set.range (algebraMap (FractionRing u.V) (PadicAlgCl p)) := by
  first | exact @GlobalTheory.exists_uniformised_model | exact GlobalTheory.exists_uniformised_model | (intros; apply GlobalTheory.exists_uniformised_model <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.RigidificationComparisonUniformisation
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.RigidificationComparisonUniformisation
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
open GlobalTheory.PsiRing

noncomputable section
namespace GlobalTheory.RigCmpPf

theorem eSec_comm {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G']
    [IsCommMonObj G'] {f : S' ⟶ S} {F : G'.left ⟶ G.left} (h : IsGrpPullback G' G f F) :
    eSec G' ≫ F = f ≫ eSec G := (cubeMapOf h).e_comm

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

def upt (G : Over (Spec (CommRingCat.of R))) [GrpObj G] {e : ℕ} {Z : Scheme.{0}}
    (a : Z ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) : Z ⟶ (thickObj R I e G).left :=
  a ≫ eSec (thickObj R I e G)

omit [IsDomain R] [IsCommMonObj G] in
theorem eSec_fst (e : ℕ) {Z : Scheme.{0}} (a : Z ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) :
    (upt G a) ≫ (fstG I e G).left = (a ≫ thick R I e) ≫ eSec G :=
  (Category.assoc _ _ _).trans ((congrArg (a ≫ ·) (UnitValue.eSec_pullback_fst (thick R I e) G)).trans
    (Category.assoc _ _ _).symm)

theorem eSec_pG {e : ℕ} (g : GtCoord I D e G) {Z : Scheme.{0}} (a : Z ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) :
    (upt G a) ≫ g.pG.left = (a ≫ thick R I e) ≫ eSec D.P.A := by
  have := g.q_hom
  have h1 : (η[thickObj R I e G] ≫ g.q) = η[thickObj R I e D.P.A] := IsMonHom.one_hom _
  have h2 : eSec (thickObj R I e G) ≫ g.q.left = eSec (thickObj R I e D.P.A) := congrArg Over.Hom.left h1
  refine Eq.trans ?_ (eSec_fst (G := D.P.A) e a)
  unfold upt
  rw [← h2]
  exact (Category.assoc _ _ _).trans ((congrArg (a ≫ ·) (Category.assoc _ _ _).symm).trans
    (Category.assoc _ _ _).symm)

theorem rig_val (U : PreU I D A G) (e : ℕ) {Z : Scheme.{0}} (a : Z ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))
    (z : Z) {JG : (Z ⟶ G.left) → U.P.L.L.ι} {J : (Z ⟶ D.P.A.left) → D.P.L.ι} (hJG : Good U.P.L.L z JG)
    (hJ : Good D.P.L z J) :
    val (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig (a ≫ thick R I e) z J =
      gw (U.w e) (upt G a) z (J ((upt G a) ≫ (U.gt e).pG.left))
          (fun _ => JG ((upt G a) ≫ (fstG I e G).left)) *
        val (L := U.P.L.L) (φ := fun _ : PUnit => eSec G) (ε := fun _ => 1) U.P.L.rig (a ≫ thick R I e) z JG := by
  have h := (U.w_vals e (Over.mk a) z JG J hJG hJ _ (fun _ => rfl)).1
  rw [one_left] at h
  exact h

theorem rig_level {V : Type} [CommRing V] [IsDomain V] {I' : Ideal V} {D' : DegPre V}
    {A' : PolAV (Spec (CommRingCat.of (FractionRing V)))} {G' : Over (Spec (CommRingCat.of V))} [GrpObj G']
    [IsCommMonObj G'] {φ : R →+* V} {U : PreU I D A G} {U' : PreU I' D' A' G'} {F : G'.left ⟶ G.left}
    (C : Cmp φ U U' F) (e : ℕ) {Z : Scheme.{0}} (a : Z ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))
    (a' : Z ⟶ Spec (CommRingCat.of (V ⧸ I' ^ (e + 1))))
    (ha : a ≫ thick R I e = (a' ≫ thick V I' e) ≫ spMap φ) (z : Z) {J J'} (hJ : Good D.P.L z J)
    (hJ' : Good D'.P.L z J') :
    val (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig (a ≫ thick R I e) z J =
      gw C.v (upt G' a' ≫ (U'.gt e).pG.left) z (J (upt G a ≫ (U.gt e).pG.left))
          (J' (upt G' a' ≫ (U'.gt e).pG.left)) *
        val (L := D'.P.L) (φ := fun _ : PUnit => eSec D'.P.A) (ε := fun _ => 1) D'.rig (a' ≫ thick V I' e) z J' := by
  have hG := eSec_comm C.pb
  obtain ⟨K, hK⟩ := exists_good_pt U.P.L.isLB z
  obtain ⟨K', hK'⟩ := exists_good_pt U'.P.L.isLB z
  have e₁ := rig_val U e a z hK hJ
  have e₂ := rig_val U' e a' z hK' hJ'
  have e₃ := (C.wL_map.vals (Over.mk (a' ≫ thick V I' e)) z K' K hK' hK _ (fun _ => rfl)).1
  rw [one_left] at e₃
  have hx : upt G a ≫ (fstG I e G).left = (upt G' a' ≫ (fstG I' e G').left) ≫ F := by
    rw [eSec_fst e a, eSec_fst e a', ha]
    exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hG.symm).trans (Category.assoc _ _ _).symm)
  have e₄ := ((C.lev e _ _ _ (hx.trans (Category.assoc _ _ _))).2 z J J' hJ hJ').2 _ _
    (hK (upt G a ≫ (fstG I e G).left)) (hK' (upt G' a' ≫ (fstG I' e G').left))
  have f₃ : val (L := U.P.L.L) (φ := fun _ : PUnit => eSec G) (ε := fun _ => 1) U.P.L.rig (a ≫ thick R I e) z K =
      gw C.wL (upt G' a' ≫ (fstG I' e G').left) z (K (upt G a ≫ (fstG I e G).left))
        (K' (upt G' a' ≫ (fstG I' e G').left)) *
      val (L := U'.P.L.L) (φ := fun _ : PUnit => eSec G') (ε := fun _ => 1) U'.P.L.rig
        (a' ≫ thick V I' e) z K' := by
    rw [ha, hx, eSec_fst e a']
    exact e₃
  exact e₁.trans ((congrArg _ f₃).trans ((_root_.mul_assoc _ _ _).symm.trans
    ((congrArg (· * _) e₄.symm).trans ((_root_.mul_assoc _ _ _).trans (congrArg _ e₂.symm)))))

end GlobalTheory.RigCmpPf

namespace GlobalTheory


open RigCmpPf in
theorem rigCmp_of_cmp : ∀ (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] [IsLocalRing V] [IsNoetherianRing V] (I : Ideal R) (I' : Ideal V) (φ : R →+* V), I' ≠ ⊤ → I.map φ ≤ I' → ∀ (D : DegPre R) (D' : DegPre V) (A : PolAV (Sp (FractionRing R))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (A' : PolAV (Sp (FractionRing V))) (G' : Over (Spec (CommRingCat.of V))) [GrpObj G'] [IsCommMonObj G'] (U : PreU I D A G) (U' : PreU I' D' A' G') (F : G'.left ⟶ G.left) (C : Cmp φ U U' F), RigCmp φ D D' C.β C.v := by
  intro R V _ _ _ _ _ _ I I' φ hI' hφ D D' A G _ _ A' G' _ _ U U' F C
  have hB := eSec_comm C.pbB
  have key := AbelianPartIso.pmaps_of_thickenings hI' D.P.isLB D'.P.isLB C.v C.v_gen (eSec D'.P.A)
    (spMap φ ≫ eSec D.P.A) hB D'.rig D'.rig_gen
    (LB.pullGen D.P.L (fun _ : PUnit => eSec D.P.A) (fun _ => 1) D.rig (spMap φ))
    (DVR.pullGen_isGen _ _ _ _ D.rig_gen _) fun e z p q hp hq => by
      have hle : I ^ (e + 1) ≤ (I' ^ (e + 1)).comap φ := by
        rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
        exact Ideal.pow_right_mono hφ _
      let a : Spec (CommRingCat.of (V ⧸ I' ^ (e + 1))) ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1))) :=
        spMap (Ideal.quotientMap _ φ hle)
      have ha : a ≫ thick R I e = (𝟙 _ ≫ thick V I' e) ≫ spMap φ := by
        rw [Category.id_comp, ← Spec.map_comp, ← Spec.map_comp]
        rfl
      obtain ⟨J, hJ, eJ⟩ := exists_good D.P.L D.P.isLB z (fun _ : Unit => thick V I' e ≫ spMap φ ≫ eSec D.P.A)
        (fun _ => p) (fun _ _ _ => rfl) (fun _ => hp)
      obtain ⟨J', hJ', eJ'⟩ := exists_good D'.P.L D'.P.isLB z (fun _ : Unit => thick V I' e ≫ eSec D'.P.A)
        (fun _ => q) (fun _ _ _ => rfl) (fun _ => hq)
      have E := rig_level C e a (𝟙 _) ha z hJ hJ'
      have hp' : (a ≫ thick R I e) ≫ eSec D.P.A = thick V I' e ≫ spMap φ ≫ eSec D.P.A := by
        rw [ha, Category.id_comp]
        exact Category.assoc _ _ _
      rw [eSec_pG (U.gt e) a, eSec_pG (U'.gt e) (𝟙 _), hp', ha, Category.id_comp, eJ (), eJ' (),
        val_of _ _ z J (fun _ => p) (fun _ => (congrArg J (Category.assoc _ _ _)).trans (eJ ())),
        val_of _ _ z J' (fun _ => q) (fun _ => eJ' ())] at E
      refine Eq.trans ?_ E
      have m₁ : thick V I' e z ∈ LB.wchart D.P.L (fun _ : PUnit => spMap φ ≫ eSec D.P.A) (fun _ => p) :=
        Set.mem_iInter.2 fun _ => hp
      have m₂ : spMap φ (thick V I' e z) ∈ LB.wchart D.P.L (fun _ : PUnit => eSec D.P.A) (fun _ => p) :=
        Set.mem_iInter.2 fun _ => hp
      exact (gm_res _ z _ m₁ _).trans (gm_pull _ (spMap φ) z _ m₂ _)
  intro Z r z p q hp hq
  have hm : (spMap φ ≫ eSec D.P.A) (r z) ∈ D.P.L.U (p PUnit.unit) :=
    (congrArg (fun g => g (r z) ∈ D.P.L.U (p PUnit.unit)) hB).mp (hp PUnit.unit)
  refine Eq.trans ?_ (key Z r z p q hp hq)
  rw [Category.comp_id]
  have m₁ : r z ∈ LB.wchart D.P.L (fun _ : PUnit => spMap φ ≫ eSec D.P.A) p := Set.mem_iInter.2 fun _ => hm
  have m₂ : spMap φ (r z) ∈ LB.wchart D.P.L (fun _ : PUnit => eSec D.P.A) p := Set.mem_iInter.2 fun _ => hm
  exact ((gm_res r z _ m₁ _).trans (gm_pull r (spMap φ) z _ m₂ _)).symm

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.RigidificationComparisonUniformisationStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
open GlobalTheory.PsiRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rigidification_comparison_uniformisation : ∀ (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] [IsLocalRing V] [IsNoetherianRing V] (I : Ideal R) (I' : Ideal V) (φ : R →+* V), I' ≠ ⊤ → I.map φ ≤ I' → ∀ (D : DegPre R) (D' : DegPre V) (A : PolAV (Sp (FractionRing R))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (A' : PolAV (Sp (FractionRing V))) (G' : Over (Spec (CommRingCat.of V))) [GrpObj G'] [IsCommMonObj G'] (U : PreU I D A G) (U' : PreU I' D' A' G') (F : G'.left ⟶ G.left) (C : Cmp φ U U' F), RigCmp φ D D' C.β C.v := by
  first | exact @GlobalTheory.rigCmp_of_cmp | exact GlobalTheory.rigCmp_of_cmp | (intros; apply GlobalTheory.rigCmp_of_cmp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PsiRelationDescendsFieldExtension
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PsiRelationDescendsFieldExtension
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PsiRelationDescent

open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.ArcPull
open GlobalTheory.PsiEvenPull (proj)

def chartPullComb {X Y Y' : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ) (h : Y' ⟶ Y) :
    ChartPull ((LB.LinComb L φ ε).pull h) (LB.LinComb L (fun k => h ≫ φ k) ε) (𝟙 Y') :=
  have le : ∀ J : PUnit → K → L.ι, ((LB.LinComb L φ ε).pull h).U J ≤
      LB.wchart L (fun k => h ≫ φ k) (J PUnit.unit) :=
    fun _ _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 (mem_pull.1 hy) k
  { idx := fun J => J PUnit.unit
    le := le
    g := fun y J J' hj hj' => by
      refine (gm_pull_g (LB.LinComb L φ ε) h (𝟙 Y') y J J' hj hj').trans
        ((gm_linComb L φ ε (𝟙 Y' ≫ h) y _ _ (mem_pull.1 hj) (mem_pull.1 hj')).trans
          (Eq.trans ?_ (gm_linComb L (fun k => h ≫ φ k) ε (𝟙 Y') y _ _ (le J hj) (le J' hj')).symm))
      simp only [Category.assoc] }

section

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O D.X]
  (oa : D.OAct O) (w : O)

abbrev mor : Fin 4 → (D.P.A.left ⟶ D.P.A.left) :=
  ![(padd D.P.A (𝟙 _) (oa.onB.act w)).left, 𝟙 D.P.A.left, (oa.onB.act w).left, (toUnit D.P.A ≫ η[D.P.A]).left]

theorem prod_mor {T : Over (Sp R)} (x : T ⟶ D.P.A) {U : Type} [CommGroup U] (h : (T.left ⟶ D.P.A.left) → U) :
    ∏ k : Fin 4, h (x.left ≫ mor oa w k) ^ (![1, -2, -1, 2] : Fin 4 → ℤ) k =
      h (x * (x ≫ oa.onB.act w)).left * (h x.left ^ 2)⁻¹ * (h (x ≫ oa.onB.act w).left)⁻¹ *
        h (1 : T ⟶ D.P.A).left ^ 2 := by
  have a₀ : x ≫ padd D.P.A (𝟙 _) (oa.onB.act w) = x * (x ≫ oa.onB.act w) :=
    (MonObj.comp_mul _ _ _).trans (by rw [Category.comp_id])
  have a₁ : x ≫ toUnit D.P.A ≫ η[D.P.A] = 1 := MonObj.comp_one (M := D.P.A) x
  rw [Fin.prod_univ_four]
  show h (x ≫ padd D.P.A (𝟙 _) (oa.onB.act w)).left ^ (1 : ℤ) * h (x.left ≫ 𝟙 _) ^ (-2 : ℤ) *
    h (x ≫ oa.onB.act w).left ^ (-1 : ℤ) * h (x ≫ toUnit D.P.A ≫ η[D.P.A]).left ^ (2 : ℤ) = _
  rw [a₀, a₁, Category.comp_id]
  simp only [zpow_neg, zpow_ofNat, pow_one]

theorem prod_mor_one {T : Over (Sp R)} {U : Type} [CommGroup U] (h : (T.left ⟶ D.P.A.left) → U) :
    ∏ k : Fin 4, h ((1 : T ⟶ D.P.A).left ≫ mor oa w k) ^ (![1, -2, -1, 2] : Fin 4 → ℤ) k = 1 := by
  have := oa.onB.hom w
  rw [prod_mor, MonObj.one_comp, _root_.mul_one]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_pow, ofMul_one]
  abel

theorem exists_normalised (u : LB.Gen (LB.LinComb D.P.L (mor oa w) ![1, -2, -1, 2])) (hu : u.IsGen) :
    ∃ t : LB.Gen (LB.LinComb D.P.L (mor oa w) ![1, -2, -1, 2]), t.IsGen ∧
      LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ t (eSec D.P.A)) (LB.oneGen D.P.L) := by
  obtain ⟨t, ht, hv⟩ := exists_gen D.P.isLB (φ' := mor oa w) (ε' := ![1, -2, -1, 2])
    (fun V _ k => by
      refine Eq.trans (prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := V) _
        (c := ∏ i, k (mor oa w i) ^ (![1, -2, -1, 2] : Fin 4 → ℤ) i) rfl
        (prod_neg _ _ (prod_mor_one oa w (T := D.P.A) k))) ?_
      simp)
    (LB.mulGen D.P.L _ _ _ _ u (LB.invGen D.P.L _ _ (LB.pullGen D.P.L _ _ u (1 : D.P.A ⟶ D.P.A).left)))
    (mulGen_isGen _ _ _ _ _ _ _ hu (invGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ hu _)))
  refine ⟨t, ht, corr_of_val D.P.isLB fun y J hJ => ?_⟩
  have e : eSec D.P.A ≫ (1 : D.P.A ⟶ D.P.A).left = eSec D.P.A :=
    (congrArg (fun q => q.left) (MonObj.comp_one (M := D.P.A) η[D.P.A])).trans (Category.id_comp _)
  rw [val_pull hJ, val_one, Category.id_comp, hv _ _ y J hJ, val_mul hJ, val_inv, val_pull hJ, e, mul_inv_cancel]

end

end GlobalTheory.PsiRelationDescent

namespace GlobalTheory


open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.ArcPull GlobalTheory.PsiRelationDescent in
theorem psi_relation_descend_field : GlobalFnsSt → ∀ (K₀ K : Type) [Field K₀] [Field K] (i : K₀ →+* K) (D : DegPre K₀) (D' : DegPre K) (hD : IsPullDeg i D D') (O : Type) [CommRing O] [StarRing O] [Module O D.X] [Module O D'.X] (oa : D.OAct O) (oa' : D'.OAct O), (∀ (a : O) (y : D'.X), hD.xe (a • y) = a • hD.xe y) → (∀ a, (oa'.onB.act a).left ≫ PsiEvenPull.proj hD = PsiEvenPull.proj hD ≫ (oa.onB.act a).left) → ∀ w : O, TraceFormTwistIso D' oa' w → TraceFormTwistIso D oa w := by
  intro hG K₀ K _ _ i D D' hD O _ _ _ _ oa oa' hx ho w ⟨u', hu', u₀', hy'⟩
  have gp := pull_grp hD
  have hφ : Function.Injective i := i.injective
  have i₁ : (𝟙 D'.P.A : D'.P.A ⟶ _).left ≫ PsiEvenPull.proj hD =
      PsiEvenPull.proj hD ≫ (𝟙 D.P.A : D.P.A ⟶ _).left :=
    (Category.id_comp _).trans (Category.comp_id _).symm
  have i₂ : (toUnit D'.P.A ≫ η[D'.P.A]).left ≫ PsiEvenPull.proj hD =
      PsiEvenPull.proj hD ≫ (toUnit D.P.A ≫ η[D.P.A]).left := by
    show (D'.P.A.hom ≫ eSec D'.P.A) ≫ PsiEvenPull.proj hD = PsiEvenPull.proj hD ≫ D.P.A.hom ≫ eSec D.P.A
    exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hD.he).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ _) gp.1.w.symm).trans (Category.assoc _ _ _))))
  have hψ : ∀ k, mor oa' w k ≫ PsiEvenPull.proj hD = PsiEvenPull.proj hD ≫ mor oa w k := fun k => by
    fin_cases k
    exacts [mul_push gp _ i₁ (ho w), i₁, ho w, i₂]
  obtain ⟨s, hs, -⟩ := exists_up_om ((isGen_iff _).1 hD.w_gen) D.P.isLB D'.P.isLB (mor oa' w)
    (fun k => PsiEvenPull.proj hD ≫ mor oa w k) _ hψ u' hu'
  obtain ⟨u₁, hu₁⟩ := (lb_gen_iso_descend_field K₀ K i _ _ D.P.A.hom D'.P.A.hom (PsiEvenPull.proj hD)
    D.P.isAb.smooth D.P.isAb.proper D.P.isAb.geomConnected gp.1).1 (LB.LinComb D.P.L (mor oa w) ![1, -2, -1, 2])
    (LB.isLB_linComb D.P.isLB _ _) ⟨_, GtBaseChange.genPull_isGen (chartPullComb D.P.L (mor oa w) _ _) hs⟩
  obtain ⟨u, hu, u₀⟩ := exists_normalised oa w u₁ hu₁
  obtain ⟨t, ht, vt⟩ := exists_down_om hD.w_gen D.P.isLB D'.P.isLB (φ' := mor oa' w) (PsiEvenPull.proj hD) hψ u hu
  have tu := gen_unique D'.P.isLB D'.P.A.hom (eSec D'.P.A) (Over.w η[D'.P.A]) (hG _ _ D'.P.isAb).2 ht hu'
    fun y J' hJ' => by
      obtain ⟨J, hJ⟩ := DegPull.exists_good' D.P.isLB y
      have o₁ : (1 : 𝟙_ (Over (Sp K)) ⟶ D'.P.A).left = eSec D'.P.A := Category.id_comp _
      have e := vt _ (1 : 𝟙_ (Over (Sp K)) ⟶ D'.P.A).left y J J' hJ hJ'
      rw [prod_mor_one, _root_.one_mul, o₁, hD.he] at e
      have e₁ := (val_pull hJ _ _ _).symm.trans ((val_corr hJ u₀ (specOf i)).trans (val_one _))
      have e₂ := (val_pull hJ' _ _ _).symm.trans ((val_corr hJ' u₀' (𝟙 _)).trans (val_one _))
      rw [Category.id_comp] at e₂
      exact e.symm.trans (e₁.trans e₂.symm)
  refine ⟨u, hu, u₀, fun y => ?_⟩
  obtain ⟨x, rfl⟩ := hD.xe.surjective y
  refine corr_of_val_field_extension _ _ (fracMap hφ) _ _ D.P.isLB _ _ _ _ _ _ _ _ fun z J hJ => ?_
  obtain ⟨J', hJ'⟩ := DegPull.exists_good' D'.P.isLB (Z := (TK K).left) z
  have sq := fracMap_sq hφ
  have hh : (TK K).hom ≫ spMap i = genMap hφ ≫ (TK K₀).hom := (Category.id_comp _).symm.trans sq
  have e := val_corr hJ' (hy' x) (𝟙 _)
  have v := vt _ (cP D' (TK K) x).left z J J' hJ hJ'
  rw [prod_mor, cPoint_proj hD _ hh, ← TorusExt.cPoint_smul oa', ← cPoint_add, tu _ _ z J' hJ'] at v
  have c₀ : ∀ x, (cP D' (TK K) x).left = D'.xK x := fun _ => rfl
  have c₁ : ∀ x, (cP D (TK K₀) x).left = D.xK x := fun _ => rfl
  simp only [c₀, c₁] at v
  rw [val_mul hJ', val_mul hJ', val_pull hJ', Category.id_comp] at e
  show val (LB.mulGen D.P.L _ _ _ _ (D.tau (hD.xe x) (w • hD.xe x)) (LB.pullGen D.P.L _ _ u (D.xK (hD.xe x))))
    (genMap hφ) z J = val (LB.mulGen D.P.L _ _ _ _ (D.psi (hD.xe x)) D.rigK) (genMap hφ) z J
  have hJ₀ : Good (Z := (TK K).left) D.P.L z J := hJ
  rw [val_mul hJ₀, val_mul hJ₀, val_pull hJ₀, v, ← hx, tau_val hD _ _ sq hJ₀ hJ', psi_val hD _ _ sq hJ₀ hJ',
    rig_val hD _ _ sq hJ₀ hJ']
  simp only [Category.id_comp]
  have e' := congrArg Additive.ofMul e
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_pow] at e' ⊢
  linear_combination (norm := abel) e'

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PsiRelationDescendsFieldExtensionStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.psi_relation_descends_field_extension : GlobalFnsSt → ∀ (K₀ K : Type) [Field K₀] [Field K] (i : K₀ →+* K) (D : DegPre K₀) (D' : DegPre K) (hD : IsPullDeg i D D') (O : Type) [CommRing O] [StarRing O] [Module O D.X] [Module O D'.X] (oa : D.OAct O) (oa' : D'.OAct O), (∀ (a : O) (y : D'.X), hD.xe (a • y) = a • hD.xe y) → (∀ a, (oa'.onB.act a).left ≫ PsiEvenPull.proj hD = PsiEvenPull.proj hD ≫ (oa.onB.act a).left) → ∀ w : O, TraceFormTwistIso D' oa' w → TraceFormTwistIso D oa w := by
  first | exact @GlobalTheory.psi_relation_descend_field | exact GlobalTheory.psi_relation_descend_field | (intros; apply GlobalTheory.psi_relation_descend_field <;> assumption)
end
end
