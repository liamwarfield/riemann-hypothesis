module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMapThetaExpansionAllTraits
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOddMultiplicationPullbackThetaFamilyDegree
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRatioOfExpansionsProportionalAtTrait

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaExpansionScalarsRatioOddMul
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExpansionSecondScalarDeterminedOfNonzero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExpansionSecondScalarDeterminedOfNonzero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem Modif.eq_comp_gp {R : Type} [CommRing R] [IsDomain R] (M : Modif R) {F : Type} [Field F]
    (ψ : FractionRing R →+* F) (x : Sp F ⟶ M.S) (hx : x ≫ M.π = spMap ψ ≫ jK R) : x = spMap ψ ≫ M.gp := by
  have := M.integral
  have hd := M.dominant
  let pt : Sp F := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum F)
  obtain ⟨B, e₀, hoi, P, hP⟩ : ∃ (B : CommRingCat) (e₀ : Spec B ⟶ M.S), IsOpenImmersion e₀ ∧ ∃ P, e₀ P = x pt :=
    ⟨_, M.S.affineCover.f (M.S.affineCover.idx (x pt)), M.S.affineCover.map_prop _, M.S.affineCover.covers (x pt)⟩
  have hsub : Set.range M.gp ⊆ Set.range e₀ := by
    obtain ⟨a, ha⟩ := hd.denseRange.exists_mem_open e₀.isOpenEmbedding.isOpen_range ⟨e₀ P, P, rfl⟩
    rintro _ ⟨x, rfl⟩
    rwa [Subsingleton.elim x a]
  have hsub' : Set.range x ⊆ Set.range e₀ := by
    rintro _ ⟨y, rfl⟩
    rw [Subsingleton.elim y pt]
    exact ⟨P, hP⟩
  obtain ⟨g', hfac⟩ : ∃ g', g' ≫ e₀ = M.gp := ⟨_, IsOpenImmersion.lift_fac e₀ M.gp hsub⟩
  obtain ⟨x', hfx⟩ : ∃ x', x' ≫ e₀ = x := ⟨_, IsOpenImmersion.lift_fac e₀ x hsub'⟩
  obtain ⟨g, rfl⟩ := Spec.map_surjective g'
  obtain ⟨g₁, rfl⟩ := Spec.map_surjective x'
  obtain ⟨ρ, hρ⟩ := Spec.map_surjective (e₀ ≫ M.π)
  have hcomp : ρ ≫ g = CommRingCat.ofHom (algebraMap R (FractionRing R)) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hρ, ← Category.assoc, hfac, M.gp_π]
  have hcomp₁ : ρ ≫ g₁ = CommRingCat.ofHom (algebraMap R (FractionRing R)) ≫ CommRingCat.ofHom ψ := by
    apply Spec.map_injective
    rw [Spec.map_comp, hρ, ← Category.assoc, hfx, hx, Spec.map_comp]
  have hc : ∀ r, g.hom (ρ.hom r) = algebraMap R (FractionRing R) r := fun r => congrArg (fun f => f.hom r) hcomp
  have hc₁ : ∀ r, g₁.hom (ρ.hom r) = ψ (algebraMap R (FractionRing R) r) := fun r => congrArg (fun f => f.hom r) hcomp₁
  have hden : DenseRange (Spec.map g) := by
    rw [denseRange_iff_closure_range, e₀.isOpenEmbedding.isInducing.closure_eq_preimage_closure_image,
      ← Set.range_comp]
    have : (e₀ ∘ Spec.map g) = M.gp := by funext x; rw [← hfac]; rfl
    rw [this, hd.denseRange.closure_range, Set.preimage_univ]
  have hinj : Function.Injective g.hom := by
    have h2 := (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical g.hom).1 hden
    have hr := (affine_isReduced_iff _).1 (isReduced_of_isOpenImmersion e₀)
    rw [nilradical_eq_zero] at h2
    exact (RingHom.injective_iff_ker_eq_bot _).2 (le_bot_iff.1 h2)
  have key : g₁ = g ≫ CommRingCat.ofHom ψ := by
    ext b
    show g₁.hom b = ψ (g.hom b)
    obtain ⟨a, s, hs, hxs⟩ := IsFractionRing.div_surjective (A := R) (g.hom b)
    have hs0 : algebraMap R (FractionRing R) s ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hs
    have h0 : ρ.hom s * b = ρ.hom a := hinj (by rw [map_mul, hc, hc, ← hxs, mul_div_cancel₀ _ hs0])
    have h1 := congrArg g₁.hom h0
    rw [map_mul, hc₁, hc₁] at h1
    rw [← hxs, map_div₀, ← h1, mul_div_cancel_left₀ _ ((map_ne_zero ψ).2 hs0)]
  rw [← hfx, ← hfac, key, Spec.map_comp, Category.assoc]

theorem PullB.unique {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'}
    {D : DegPre R} {D' : DegPre R'} {hD : IsPullDeg φ D D'} {k : ℕ} {x : D'.X} {b : D.SecB k (hD.xe x)}
    {b₁ b₂ : D'.SecB k x} (H₁ : PullB hD x b b₁) (H₂ : PullB hD x b b₂) : b₁ = b₂ := by
  refine DVR.SecOps.sec_ext fun q => fn_ext fun y hy => ?_
  choose p hp using fun κ => exists_chart D.P.isLB ((hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) (D'.famφB x κ y))
  have e₁ := H₁ _ (𝟙 _) y p q hp (Set.mem_iInter.1 hy)
  have e₂ := H₂ _ (𝟙 _) y p q hp (Set.mem_iInter.1 hy)
  exact (Units.mul_right_inj _).1 (e₁.symm.trans e₂)

theorem PullB.eq_zero {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'}
    (hφ : Function.Injective φ) {D : DegPre R} {D' : DegPre R'} {hD : IsPullDeg φ D D'} {k : ℕ} {x : D'.X}
    {b : D.SecB k (hD.xe x)} {b' : D'.SecB k x} (H : PullB hD x b b') (h : ∀ q, b'.f q = 0) (p) : b.f p = 0 := by
  have : IsDominant (specOf φ) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical φ).2 (by
    rw [(RingHom.injective_iff_ker_eq_bot _).1 hφ]; exact bot_le)⟩
  have := IsSchemeTheoreticallyDominant.of_isDominant (specOf φ)
  have : Smooth D.P.A.hom := D.P.isAb.smooth
  have : IsSchemeTheoreticallyDominant (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) :=
    IsSchemeTheoreticallyDominant.of_isPullback (pull_grp hD).1.flip
  have : QuasiCompact (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) (pull_grp hD).1.flip inferInstance
  apply (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)).app_injective
  rw [map_zero]
  refine fn_ext fun y hy => ?_
  choose q hq using fun κ => exists_chart D'.P.isLB (D'.famφB x κ y)
  have e := H _ (𝟙 _) y p q (fun κ => by
    have a := Set.mem_iInter.1 hy κ
    exact (congrArg (fun m => m y ∈ D.P.L.U (p κ)) (ExpGTrans.famφB_pull hD x κ)).mpr a) hq
  have e' := e.trans ((congrArg _ ((congrArg (gs _ y _) (h q)).trans (DVR.hr_gs_zero _ _ _))).trans (mul_zero _))
  exact (gs_pull _ _ y _ hy _).trans (e'.trans (DVR.hr_gs_zero _ _ _).symm)

theorem expands_zero {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (k : ℕ) :
    U.Expands k DVR.SecOps.secZero 0 := by
  refine ⟨1, one_ne_zero, DVR.SecOps.secZero, fun _ => DVR.SecOps.secZero, fun j₁ j₂ _ => ?_, fun α j₁ j₂ _ => ?_,
    fun e => ⟨∅, fun α _ j => map_zero _, fun p j₁ jf jt _ _ => ?_⟩⟩
  · exact ((congrArg _ (map_zero _)).trans (map_zero _)).trans ((congrArg _ (map_zero _)).trans (mul_zero _)).symm
  · exact ((congrArg _ (map_zero _)).trans (map_zero _)).trans ((congrArg _ (map_zero _)).trans (mul_zero _)).symm
  · exact ((congrArg _ ((congrArg _ (map_zero _)).trans (map_zero _))).trans (mul_zero _)).trans (Finset.sum_empty).symm

theorem IntFam.f_eq_zero {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {k : ℕ} (F : IntFam I D k)
    (h : F.F = 0) (x : D.X) (q) : (F.f x).f q = 0 := by
  have h₀ : GeneratorPullback.SecScal D.P.L (DegPre.famφ D (FractionRing R) x) (DegPre.famε k) (F.F.s x)
      (D.famφB x) (DegPre.famε k) DVR.SecOps.secZero (DegPre.prB D (FractionRing R)).left 1 := by
    rw [h]
    intro j₁ j₂ _
    exact ((congrArg _ (map_zero _)).trans (map_zero _)).trans ((congrArg _ (map_zero _)).trans (mul_zero _)).symm
  exact (IntegralExpansion.secIsMul_of_secScal D.P.isLB D.P.A.hom (a := 1) (IntegralExpansion.prB_app_injective D) h₀
    (by rw [Over.w (DegPre.prB D (FractionRing R))]; exact F.ext x) q).trans (mul_zero _)

theorem IntFam.eq_zero_of_two_scalars {W : Type} [CommRing W] [IsDomain W] {I : Ideal W} {D : DegData W I}
    {A : PolAV (Sp (FractionRing W))} {G : CategoryTheory.Over (Sp W)} [GrpObj G] [IsCommMonObj G] (U : Unif I D A G) {k : ℕ} (hk : 1 ≤ k)
    (F : IntFam I D.toPre k) {σ₁ σ₂ : H0 U.LG.L k} (e₁ : ∀ e, U.ExpandsAt e k σ₁ F.f) (e₂ : ∀ e, U.ExpandsAt e k σ₂ F.f)
    {b b' : W} (hb : b ≠ b') (H : ∀ y J, Good U.LG.L y J → ∃ u : ((pullback G.hom (jK W)).presheaf.stalk y)ˣ,
      gs (pullback.fst G.hom (jK W)) y ⊤ (scal G.hom b) * u.val * sval σ₁ (pullback.fst G.hom (jK W)) y J =
        gs (pullback.fst G.hom (jK W)) y ⊤ (scal G.hom b') * u.val * sval σ₂ (pullback.fst G.hom (jK W)) y J) :
    F.F = 0 := by
  have res : ∀ σ : H0 U.LG.L k, (∀ e, U.ExpandsAt e k σ F.f) → ∃ s : U.SecK k, U.Expands k s F.F ∧
      ∀ y J, Good U.LG.L y J → sval σ (pullback.fst G.hom (jK W)) y J = sval s (𝟙 _) y J := fun σ e => by
    obtain ⟨s, hs⟩ := UnifBaseChange.exists_secScal_one U.LG.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => (k : ℤ))
      (pullback.fst G.hom (jK W)) (fun _ => pullback.fst G.hom (jK W)) (funext fun _ => (Category.comp_id _).symm) σ
    refine ⟨s, ⟨1, one_ne_zero, σ, F.f, ?_, F.ext, e⟩, fun y J hJ => ?_⟩
    · rw [UnifBaseChange.scal_one]; exact hs
    · have v := DVR.hr_secScal_sval hs (𝟙 _) y hJ
      rwa [Category.id_comp, gs_eq _ y ⊤ trivial, map_one, map_one, _root_.one_mul] at v
  obtain ⟨s₁, x₁, v₁⟩ := res σ₁ e₁
  obtain ⟨s₂, x₂, v₂⟩ := res σ₂ e₂
  obtain rfl : s₁ = s₂ := ((U.expand k hk).2 F.F).unique x₁ x₂
  have hz : s₁ = DVR.SecOps.secZero := by
    refine DVR.SecOps.sec_ext (sec_ext_val U.LG.isLB fun y J hJ => ?_)
    obtain ⟨u, e⟩ := H y J hJ
    rw [v₁ y J hJ, v₂ y J hJ, ← sub_eq_zero, ← sub_mul, ← sub_mul] at e
    have hu : IsUnit (gs (pullback.fst G.hom (jK W)) y ⊤ (scal G.hom (b - b'))) := by
      rw [GenericCross.gs_scal, pullback.condition]
      exact GenericCross.isUnit_cst _ y (sub_ne_zero.2 hb)
    have hs : gs (pullback.fst G.hom (jK W)) y ⊤ (scal G.hom (b - b')) =
        gs (pullback.fst G.hom (jK W)) y ⊤ (scal G.hom b) - gs (pullback.fst G.hom (jK W)) y ⊤ (scal G.hom b') := by
      simp only [gs_eq _ y ⊤ trivial, scal, map_sub]
    rw [hs] at hu
    exact ((hu.mul u.isUnit).mul_right_eq_zero.1 e).trans (DVR.hr_gs_zero _ _ _).symm
  rw [hz] at x₁
  exact ((U.expand k hk).1 _).unique x₁ (expands_zero U.toUnifPre k)

theorem exists_fractionRing_square {R W : Type} [CommRing R] [IsDomain R] [CommRing W] [IsDomain W] (φ : R →+* W) (h : Function.Injective φ) :
    ∃ ψ : FractionRing R →+* FractionRing W, jK W ≫ spMap φ = spMap ψ ≫ jK R := by
  have hi : Function.Injective ((algebraMap W (FractionRing W)).comp φ) := (IsFractionRing.injective W _).comp h
  have h₀ : (algebraMap W (FractionRing W)).comp φ = (IsFractionRing.lift hi).comp (algebraMap R (FractionRing R)) :=
    RingHom.ext fun r => by rw [RingHom.comp_apply (IsFractionRing.lift hi), IsFractionRing.lift_algebraMap]
  refine ⟨IsFractionRing.lift hi, ?_⟩
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, ← h₀]

theorem Trait.exists_generic_map {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {D : DegData R (maximalIdeal R)}
    {C : LabCover D} {W : Type} [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) :
    ∃ p' : pullback T.G.hom (jK W) ⟶ C.A.A.left, pullback.fst T.G.hom (jK W) ≫ T.β = p' ≫ C.α := by
  obtain ⟨ψ, h₀⟩ := exists_fractionRing_square T.φ T.inj
  have hψ : jK W ≫ T.ξ = spMap ψ ≫ C.gp := C.toModif.eq_comp_gp ψ _ (by rw [Category.assoc, T.ξ_π, h₀])
  have w₁ : T.β ≫ C.G.hom = T.G.hom ≫ T.ξ := T.cart.1.w
  have w₂ : pullback.fst T.G.hom (jK W) ≫ T.G.hom = pullback.snd T.G.hom (jK W) ≫ jK W := pullback.condition
  have w₃ : (pullback.fst T.G.hom (jK W) ≫ T.β) ≫ C.G.hom = (pullback.snd T.G.hom (jK W) ≫ spMap ψ) ≫ C.gp := by
    rw [Category.assoc, w₁, reassoc_of% w₂, hψ, Category.assoc]
  have hp : IsPullback C.α C.A.A.hom C.G.hom C.gp := C.α_cart.1
  exact ⟨hp.lift _ _ w₃, (hp.lift_fst _ _ w₃).symm⟩

theorem Trait.exp_unique : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (k : ℕ), 1 ≤ k → ∀ (s : SecK C.P.L.L C.α k) (F : IntFam (maximalIdeal R) D.toPre k), (∃ α j, (F.f α).f j ≠ 0) → ∀ a b b' : W, a ≠ 0 → T.Exp a b s F → T.Exp a b' s F → b = b' := by
  intro R _ _ _ hR D C W _ _ _ T k hk s F hF a b b' _ h₁ h₂
  obtain ⟨α, j, hne⟩ := hF
  obtain ⟨σ₁, ⟨σ₁', f₁, c₁, p₁, e₁⟩, g₁⟩ := h₁
  obtain ⟨σ₂, ⟨σ₂', f₂, c₂, p₂, e₂⟩, g₂⟩ := h₂
  by_contra hb
  apply hne
  obtain ⟨F', hF'⟩ := exists_intFam_pull R hR D W T.φ T.D' T.hD T.inj T.loc k F
  rw [show f₁ = F'.f from funext fun x => (p₁ x).unique (hF' x)] at e₁
  rw [show f₂ = F'.f from funext fun x => (p₂ x).unique (hF' x)] at e₂
  obtain ⟨p', hp'⟩ := T.exists_generic_map
  have h₀ : F'.F = 0 := F'.eq_zero_of_two_scalars T.U hk e₁ e₂ hb fun y J' hJ' => by
    choose J hJ using fun χ : pullback T.G.hom (jK W) ⟶ C.G.left => exists_chart C.P.L.isLB (χ y)
    exact ⟨_, (c₁ _ _ y J J' hJ hJ').symm.trans ((g₁ _ _ p' hp' y J hJ).trans
      ((g₂ _ _ p' hp' y J hJ).symm.trans (c₂ _ _ y J J' hJ hJ')))⟩
  obtain ⟨x, rfl⟩ := T.hD.xe.surjective α
  exact (hF' x).eq_zero T.inj (F'.f_eq_zero h₀ x) j

end GlobalTheory.Mum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExpansionSecondScalarDeterminedOfNonzeroStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.expansion_secondScalar_determined_of_nonzero : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (k : ℕ), 1 ≤ k → ∀ (s : SecK C.P.L.L C.α k) (F : IntFam (maximalIdeal R) D.toPre k), (∃ α j, (F.f α).f j ≠ 0) → ∀ a b b' : W, a ≠ 0 → T.Exp a b s F → T.Exp a b' s F → b = b' := by
  first | exact @GlobalTheory.Mum.Trait.exp_unique | exact GlobalTheory.Mum.Trait.exp_unique | (intros; apply GlobalTheory.Mum.Trait.exp_unique <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExpansionScalarArbitraryOfMembersZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExpansionScalarArbitraryOfMembersZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.Mum.ZeroFam

theorem gs_zero' {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) : gs f y U 0 = 0 := by
  unfold gs; split_ifs <;> simp

theorem sval_eq_zero {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (s : LB.Sec (LB.LinComb L φ ε)) (hs : ∀ j, s.f j = 0) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι) :
    sval s r z J = 0 := by
  unfold sval; exact (congrArg (gs r z _) (hs _)).trans (gs_zero' _ _ _)

theorem secB_zero_of_pullB {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'}
    {D : DegPre R} {D' : DegPre R'} (hD : IsPullDeg φ D D') {k : ℕ} (x : D'.X) (b : D.SecB k (hD.xe x))
    (b' : D'.SecB k x) (hb : ∀ j, b.f j = 0) (h : PullB hD x b b') : ∀ q, b'.f q = 0 := by
  intro q
  refine fn_ext fun y hy => ?_
  choose p hp using fun κ => exists_chart D.P.isLB
    ((hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) ((D'.famφB x) κ y))
  have e := h _ (𝟙 _) y p q (fun κ => hp κ) (fun κ => Set.mem_iInter.1 hy κ)
  rw [show b.f p = 0 from hb _] at e
  have e2 := e.symm.trans (gs_zero' _ _ _)
  exact ((Units.mul_right_eq_zero _).1 e2).trans (gs_zero' _ _ _).symm

end GlobalTheory.Mum.ZeroFam

namespace GlobalTheory.Mum.ZeroFam

open GlobalTheory.ExpInt

theorem section_eq_zero_of_expansion_zero_family {W : Type} [CommRing W] [IsDomain W] {I : Ideal W} {D : DegData W I}
    {A : PolAV (Sp (FractionRing W))} {G : Over (Sp W)} [GrpObj G] [IsCommMonObj G] (U : Unif I D A G) {k : ℕ}
    (hk : 1 ≤ k) (σ : H0 U.LG.L k) (f : ∀ α : D.toPre.X, D.toPre.SecB k α) (hf : ∀ α j, (f α).f j = 0)
    (hE : ∀ e, U.ExpandsAt e k σ f) : ∀ j, σ.f j = 0 := by
  have := U.smooth
  have : Flat G.hom := inferInstance
  have ex : ∀ (φ' : Fin 1 → (pullback G.hom (jK W) ⟶ G.left))
      (_ : φ' = fun _ => pullback.fst G.hom (jK W) ≫ 𝟙 G.left),
      ∃ s' : LB.Sec (LB.LinComb U.LG.L φ' (fun _ => (k : ℤ))), ∀ z J, Good U.LG.L z J →
        sval s' (𝟙 _) z J = sval σ (pullback.fst G.hom (jK W)) z J := by
    rintro _ rfl
    exact ⟨pullSec _ _ _ σ _, fun z J hJ => (SectionScalarValuation.sval_pullSec _ _ σ _ (𝟙 _) z hJ).trans (by rw [Category.id_comp])⟩
  obtain ⟨s₀, hs₀⟩ := ex (fun _ => pullback.fst G.hom (jK W)) (funext fun _ => (Category.comp_id _).symm)
  have h1 : scal (pullback.snd G.hom (jK W) ≫ jK W) (1 : W) = 1 := by unfold scal; rw [map_one, map_one]
  have h1' : scal (DegPre.BF D.toPre (FractionRing W)).hom (1 : W) = 1 := by unfold scal; rw [map_one, map_one]
  have hF : ∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing W) α) (DegPre.famε k)
      ((0 : Fam D.toPre (FractionRing W) k).s α) (D.toPre.famφB α) (DegPre.famε k) (f α)
      (DegPre.prB D.toPre (FractionRing W)).left (scal (DegPre.BF D.toPre (FractionRing W)).hom 1) := fun α => by
    rw [h1']
    exact SectionScalarValuation.secScal_of_sval D.toPre.P.isLB fun y J _ =>
      (sval_eq_zero _ (hf α) _ y J).trans (sval_eq_zero _ (fun _ => rfl) _ y J).symm
  have hE₀ : ∀ e, U.ExpandsAt e k (SecOps.secZero : H0 U.LG.L k) f := fun e => by
    refine ⟨∅, fun α _ j => by rw [show (f α).f j = 0 from hf α j, map_zero], fun p j₁ jf jt _ _ => ?_⟩
    simp only [Finset.attach_empty, Finset.sum_empty]
    erw [show (SecOps.secZero : H0 U.LG.L k).f j₁ = 0 from rfl, map_zero, map_zero, mul_zero]
  have hEs₀ : U.Expands k s₀ 0 := ⟨1, one_ne_zero, σ, f, by
    rw [h1]
    exact SectionScalarValuation.secScal_of_sval U.LG.isLB fun y J hJ => by rw [Category.id_comp]; exact (hs₀ y J hJ).symm, hF, hE⟩
  have hEz : U.Expands k SecOps.secZero 0 := ⟨1, one_ne_zero, SecOps.secZero, f, by
    rw [h1]
    exact SectionScalarValuation.secScal_of_sval U.LG.isLB fun y J _ =>
      (sval_eq_zero _ (fun _ => rfl) _ y J).trans (sval_eq_zero _ (fun _ => rfl) _ y J).symm, hF, hE₀⟩
  have e₀ : s₀ = SecOps.secZero := ((U.expand k hk).2 0).unique hEs₀ hEz
  have hm := secIsMul_of_generic G U.LG.isLB k SecOps.secZero σ SecOps.secZero 1
    (SectionScalarValuation.secScal_of_sval U.LG.isLB fun y J _ =>
      (sval_eq_zero _ (fun _ => rfl) _ y J).trans (sval_eq_zero _ (fun _ => rfl) _ y J).symm)
    (by
      rw [h1]
      exact SectionScalarValuation.secScal_of_sval U.LG.isLB fun y J hJ => by rw [Category.id_comp, ← hs₀ y J hJ, e₀])
  intro j
  rw [hm j]
  exact mul_zero _

end GlobalTheory.Mum.ZeroFam

namespace GlobalTheory.Mum.ZeroFam

theorem exp_of_members_zero : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (k : ℕ), 1 ≤ k → ∀ (s : SecK C.P.L.L C.α k) (F : IntFam (maximalIdeal R) D.toPre k), (∀ α j, (F.f α).f j = 0) → ∀ a b : W, T.Exp a b s F → ∀ b' : W, T.Exp a b' s F := by
  intro R _ _ _ _ D C W _ _ _ T k hk s F hF a b hExp b'
  obtain ⟨σ, ⟨σ', f', hC, hP, hE⟩, hs⟩ := hExp
  have hf' : ∀ x q, (f' x).f q = 0 := fun x => secB_zero_of_pullB T.hD x _ (f' x) (hF _) (hP x)
  have hσ' := section_eq_zero_of_expansion_zero_family T.U hk σ' f' hf' hE
  refine ⟨σ, ⟨σ', f', fun Z r z J J' hJ hJ' => ?_, hP, hE⟩, hs⟩
  rw [hC Z r z J J' hJ hJ', sval_eq_zero _ hσ', mul_zero, mul_zero]

end GlobalTheory.Mum.ZeroFam
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExpansionScalarArbitraryOfMembersZeroStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.expansion_scalar_arbitrary_of_members_zero : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (k : ℕ), 1 ≤ k → ∀ (s : SecK C.P.L.L C.α k) (F : IntFam (maximalIdeal R) D.toPre k), (∀ α j, (F.f α).f j = 0) → ∀ a b : W, T.Exp a b s F → ∀ b' : W, T.Exp a b' s F := by
  first | exact @GlobalTheory.Mum.ZeroFam.exp_of_members_zero | exact GlobalTheory.Mum.ZeroFam.exp_of_members_zero | (intros; apply GlobalTheory.Mum.ZeroFam.exp_of_members_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaExpansionScalarsRatioOddMul
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem ratio_odd_mul : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (m : ℕ), Odd m → ∀ Φ : IntFam (maximalIdeal R) D.toPre (m ^ 2) → SecK C.P.L.L C.α (m ^ 2), (∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W), ∃ u : Wˣ, ∀ F, T.Exp 1 u (Φ F) F) → ∀ (F₁ : IntFam (maximalIdeal R) D.toPre 1) (θ₀ : SecK C.P.L.L C.α 1), (∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W), ∃ a b : W, a ≠ 0 ∧ b ≠ 0 ∧ T.Exp a b θ₀ F₁) → ∃ r t : R, r ≠ 0 ∧ t ≠ 0 ∧ ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W), ∃ (a b : W) (v : Wˣ), a ≠ 0 ∧ b ≠ 0 ∧ T.Exp a b θ₀ F₁ ∧ b * T.φ t = a * T.φ r * v := by
  intro R _ _ _ hR D C m hm Φ hΦ F₁ θ₀ hθ
  by_cases hz : ∀ α j, (F₁.f α).f j = 0
  · refine ⟨1, 1, one_ne_zero, one_ne_zero, fun W _ _ _ T => ?_⟩
    obtain ⟨a, b, ha, hb, h⟩ := hθ W T
    exact ⟨a, a, 1, ha, ha, GlobalTheory.T.expansion_scalar_arbitrary_of_members_zero R hR D C W T 1 le_rfl θ₀ F₁ hz a b h a, by simp⟩
  push_neg at hz
  obtain ⟨G, S, hG, hS⟩ := GlobalTheory.T.exists_oddMultiplication_pullback_thetaFamily_degree_sq R hR D C m hm F₁ θ₀
  have hGz := hG hz
  have hk : 1 ≤ m ^ 2 := Nat.one_le_pow _ _ hm.pos
  by_cases hT : ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W), Nonempty (Trait C W)
  swap
  · refine ⟨1, 1, one_ne_zero, one_ne_zero, fun W _ _ _ T => (hT ⟨W, _, _, _, ⟨T⟩⟩).elim⟩
  obtain ⟨W₀, _, _, _, ⟨T₀⟩⟩ := hT
  obtain ⟨a₀, b₀, ha₀, hb₀, h₀⟩ := hθ W₀ T₀
  obtain ⟨v₀, hv₀⟩ := hS W₀ T₀ a₀ b₀ ha₀ h₀
  obtain ⟨r, t, hr, ht, hrt⟩ := GlobalTheory.T.exists_ratio_of_expansions_proportional_at_trait R hR D C (m ^ 2) hk G S (Φ G) (fun W _ _ _ T => (hΦ W T).imp fun u hu => hu G)
    W₀ T₀ a₀ (b₀ * v₀) ha₀ (mul_ne_zero hb₀ v₀.ne_zero) hv₀
  refine ⟨r, t, hr, ht, fun W _ _ _ T => ?_⟩
  obtain ⟨a, b, ha, hb, h⟩ := hθ W T
  obtain ⟨v, hv⟩ := hS W T a b ha h
  obtain ⟨u, hu⟩ := hrt W T
  have htW : T.φ t ≠ 0 := fun h0 => ht (T.inj (h0.trans (map_zero _).symm))
  have h1 := GlobalTheory.T.coverTrait_expansion_scale_both_scalars R D C W T (m ^ 2) S G a (b * v) (T.φ t) hv
  have h2 := GlobalTheory.T.coverTrait_expansion_scale_both_scalars R D C W T (m ^ 2) S G (T.φ t) (T.φ r * u) a hu
  rw [mul_comm a (T.φ t)] at h2
  have he := GlobalTheory.T.expansion_secondScalar_determined_of_nonzero R hR D C W T (m ^ 2) hk S G hGz (T.φ t * a) _ _ (mul_ne_zero htW ha) h1 h2
  refine ⟨a, b, u * v⁻¹, ha, hb, h, ?_⟩
  have : b * T.φ t * v = a * T.φ r * u := by linear_combination he
  calc b * T.φ t = b * T.φ t * v * ↑v⁻¹ := by simp [mul_assoc]
    _ = _ := by rw [this]; push_cast; ring

end GlobalTheory.Mum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaExpansionScalarsRatioOddMulStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaExpansionScalars_ratio_odd_mul : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (m : ℕ), Odd m → ∀ Φ : IntFam (maximalIdeal R) D.toPre (m ^ 2) → SecK C.P.L.L C.α (m ^ 2), (∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W), ∃ u : Wˣ, ∀ F, T.Exp 1 u (Φ F) F) → ∀ (F₁ : IntFam (maximalIdeal R) D.toPre 1) (θ₀ : SecK C.P.L.L C.α 1), (∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W), ∃ a b : W, a ≠ 0 ∧ b ≠ 0 ∧ T.Exp a b θ₀ F₁) → ∃ r t : R, r ≠ 0 ∧ t ≠ 0 ∧ ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W), ∃ (a b : W) (v : Wˣ), a ≠ 0 ∧ b ≠ 0 ∧ T.Exp a b θ₀ F₁ ∧ b * T.φ t = a * T.φ r * v := by
  first | exact @GlobalTheory.Mum.ratio_odd_mul | exact GlobalTheory.Mum.ratio_odd_mul | (intros; apply GlobalTheory.Mum.ratio_odd_mul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolarisationSectionRatioIntegralThetaFamil
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolarisationSectionRatioIntegralThetaFamil
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_sec_exp_intFam_one : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (F₁ : IntFam (maximalIdeal R) D.toPre 1), ∃ θ₀ : SecK C.P.L.L C.α 1, ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W), ∃ a b : W, a ≠ 0 ∧ b ≠ 0 ∧ T.Exp a b θ₀ F₁ := by
  intro R _ _ _ hR D C F₁
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.T.exists_map_thetaExpansion_all_traits R hR D C 0
  refine ⟨Φ F₁, fun W _ _ _ T => ?_⟩
  obtain ⟨a, b, ha, hb, h⟩ := hΦ W T
  exact ⟨a, b, ha, hb, h F₁⟩

end GlobalTheory.Mum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolarisationSectionRatioIntegralThetaFamilStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_polarisationSection_ratio_integralThetaFamily : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (F₁ : IntFam (maximalIdeal R) D.toPre 1), ∃ θ₀ : SecK C.P.L.L C.α 1, ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W), ∃ a b : W, a ≠ 0 ∧ b ≠ 0 ∧ T.Exp a b θ₀ F₁ := by
  first | exact @GlobalTheory.Mum.exists_sec_exp_intFam_one | exact GlobalTheory.Mum.exists_sec_exp_intFam_one | (intros; apply GlobalTheory.Mum.exists_sec_exp_intFam_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitExpansionScalarRescaleDegreeOne
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitExpansionScalarRescaleDegreeOne
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.Rescale

theorem gs_comp_stalk {X Y Z : Scheme.{0}} (g : Z ⟶ Y) (f : Y ⟶ X) (z : Z) (U : X.Opens) (h : f (g z) ∈ U)
    (a : Γ(X, U)) : gs (g ≫ f) z U a = (g.stalkMap z).hom (gs f (g z) U a) := by
  rw [gs_stalkMap (g ≫ f) z U h, gs_stalkMap f (g z) U h, Scheme.Hom.stalkMap_comp]
  rfl

theorem cst_zero' {V : Type} [CommRing V] {Z : Scheme.{0}} (q : Z ⟶ Sp V) (z : Z) : cst q z 0 = 0 := by
  simp only [cst, gs_eq q z ⊤ trivial, map_zero]

theorem sval_secScale {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (c : Γ(Y, ⊤)) (s : LB.Sec (LB.LinComb L φ ε)) (r : Z ⟶ Y) (z : Z) {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    sval (ReciprocityTheory.ChartRestriction.G.DVR.SecOps.secScale c s) r z J = gs r z ⊤ c * sval s r z J :=
  (gs_mul r z _ (hJ.mem φ r) _ _).trans (congrArg (· * _) (gs_res r z le_top (hJ.mem φ r) c))

theorem gs_scal {V : Type} [CommRing V] {Y Z : Scheme.{0}} (q : Y ⟶ Sp V) (r : Z ⟶ Y) (z : Z) (a : V) :
    gs r z ⊤ (scal q a) = cst (r ≫ q) z a :=
  gs_pull r q z ⊤ trivial _

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {D : DegData R (maximalIdeal R)}

theorem cancel (C : LabCover D) {W : Type} [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W)
    (hα : Flat C.α) (b : W) (hb : b ≠ 0) (s₁ : SecK C.P.L.L T.β 1) (s₂ : SecK C.P.L.L C.α 1)
    (h : ∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ C.A.A.left), p ≫ T.β = p' ≫ C.α → ∀ z J,
      Good C.P.L.L z J → cst (p ≫ T.G.hom) z b * sval s₁ p z J = cst (p ≫ T.G.hom) z b * sval s₂ p' z J)
    (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ C.A.A.left) (hp : p ≫ T.β = p' ≫ C.α) (z : Z)
    (J : (Z ⟶ C.G.left) → C.P.L.L.ι) (hJ : Good C.P.L.L z J) : sval s₁ p z J = sval s₂ p' z J := by
  haveI := T.U.smooth
  haveI : Flat (pullback.fst T.β C.α ≫ T.G.hom) := inferInstance
  obtain ⟨g, rfl, rfl⟩ : ∃ g, g ≫ pullback.fst T.β C.α = p ∧ g ≫ pullback.snd T.β C.α = p' :=
    ⟨pullback.lift p p' hp, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  obtain ⟨J₀, hJ₀, e₀⟩ := exists_good C.P.L.L C.P.L.isLB (g z) (K := Unit)
    (fun _ => pullback.fst T.β C.α ≫ T.β) (fun _ => J ((g ≫ pullback.fst T.β C.α) ≫ T.β)) (fun _ _ _ => rfl)
    (fun _ => hJ ((g ≫ pullback.fst T.β C.α) ≫ T.β))
  have key := h _ (pullback.fst T.β C.α) (pullback.snd T.β C.α) pullback.condition (g z) J₀ hJ₀
  have eJ : J₀ (pullback.snd T.β C.α ≫ C.α) = J₀ (pullback.fst T.β C.α ≫ T.β) :=
    congrArg J₀ pullback.condition.symm
  have A₁ : sval s₁ (g ≫ pullback.fst T.β C.α) z J = (g.stalkMap z).hom (sval s₁ (pullback.fst T.β C.α) (g z) J₀) := by
    rw [sval_of s₁ _ z J (fun _ => J₀ (pullback.fst T.β C.α ≫ T.β)) (fun _ => (e₀ ()).symm),
      sval_of s₁ _ (g z) J₀ (fun _ => J₀ (pullback.fst T.β C.α ≫ T.β)) (fun _ => rfl)]
    exact gs_comp_stalk g _ z _ (hJ₀.mem _ _) _
  have A₂ : sval s₂ (g ≫ pullback.snd T.β C.α) z J = (g.stalkMap z).hom (sval s₂ (pullback.snd T.β C.α) (g z) J₀) := by
    have e₁ : J ((g ≫ pullback.snd T.β C.α) ≫ C.α) = J₀ (pullback.fst T.β C.α ≫ T.β) := by
      rw [e₀ (), Category.assoc, Category.assoc, pullback.condition]
    rw [sval_of s₂ _ z J (fun _ => J₀ (pullback.fst T.β C.α ≫ T.β)) (fun _ => e₁),
      sval_of s₂ _ (g z) J₀ (fun _ => J₀ (pullback.fst T.β C.α ≫ T.β)) (fun _ => eJ)]
    refine gs_comp_stalk g _ z _ ?_ _
    exact Set.mem_iInter.2 fun _ => by rw [← eJ]; exact hJ₀ (pullback.snd T.β C.α ≫ C.α)
  have hz : sval s₁ (pullback.fst T.β C.α) (g z) J₀ = sval s₂ (pullback.snd T.β C.α) (g z) J₀ := by
    have h0 : cst (pullback.fst T.β C.α ≫ T.G.hom) (g z) b *
        (sval s₁ (pullback.fst T.β C.α) (g z) J₀ - sval s₂ (pullback.snd T.β C.α) (g z) J₀) = 0 := by
      rw [mul_sub, key, sub_self]
    have := GlobalTheory.cst_dvd_of_cst_mul_eq_zero (pullback.fst T.β C.α ≫ T.G.hom) (g z) (a := b) (b := 0)
      (fun c hc => zero_dvd_iff.2 ((mul_eq_zero.1 hc).resolve_left hb)) h0
    rw [cst_zero', zero_dvd_iff, sub_eq_zero] at this
    exact this
  rw [A₁, A₂, hz]

end GlobalTheory.Mum.Rescale

namespace GlobalTheory.Mum.Rescale

theorem cst_unit {V : Type} [CommRing V] {Z : Scheme.{0}} (q : Z ⟶ Sp V) (z : Z) {u : V} (hu : IsUnit u) :
    IsUnit (cst q z u) := by
  obtain ⟨w, rfl⟩ := hu
  refine ⟨⟨cst q z w, cst q z ↑w⁻¹, ?_, ?_⟩, rfl⟩
  · rw [← ReciprocityTheory.ChartRestriction.G.H1.cst_mul, Units.mul_inv, ReciprocityTheory.ChartRestriction.G.H1.cst_one]
  · rw [← ReciprocityTheory.ChartRestriction.G.H1.cst_mul, Units.inv_mul, ReciprocityTheory.ChartRestriction.G.H1.cst_one]

theorem rescale : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (F₁ : IntFam (maximalIdeal R) D.toPre 1) (θ₀ : SecK C.P.L.L C.α 1) (r t : R) (x : FractionRing R), r ≠ 0 → x * algebraMap R (FractionRing R) r = algebraMap R (FractionRing R) t → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (a b : W) (v : Wˣ), a ≠ 0 → b ≠ 0 → T.Exp a b θ₀ F₁ → b * T.φ t = a * T.φ r * v → T.Exp 1 (v : W) (ReciprocityTheory.ChartRestriction.G.DVR.SecOps.secScale (scal C.A.A.hom x) θ₀) F₁ := by
  intro R _ _ _ _ D C F₁ θ₀ r t x hr hx W _ _ _ T a b v ha hb hE hbt
  obtain ⟨σ, ⟨σ', f', hC, hP, hX⟩, hσ⟩ := hE
  have hw : PGen T.ℓ := (isGen_iff T.ℓ).1 T.ℓ_gen
  obtain ⟨s, hs⟩ := sec_upK hw C.P.L.isLB T.U.LG.isLB (φ' := fun _ : Fin 1 => 𝟙 T.G.left)
    (ε := fun _ => ((1 : ℕ) : ℤ)) σ'
  have gen : ∀ ψ : Fin 1 → (T.G.left ⟶ C.G.left), ψ = (fun _ => T.β) →
      ∀ s : LB.Sec (LB.LinComb C.P.L.L ψ (fun _ => ((1 : ℕ) : ℤ))), ∃ s' : SecK C.P.L.L T.β 1,
        ∀ (Z : Scheme.{0}) (r : Z ⟶ T.G.left) z J, sval s' r z J = sval s r z J := by
    rintro ψ rfl s
    exact ⟨s, fun _ _ _ _ => rfl⟩
  obtain ⟨s', hs'⟩ := gen _ (funext fun _ => Category.id_comp _) s
  have hs₁ : ∀ (Z : Scheme.{0}) (r : Z ⟶ T.G.left) (z : Z) J J', Good C.P.L.L z J → Good T.U.LG.L z J' →
      sval s' r z J = (gw T.ℓ r z (J (r ≫ T.β)) (J' r)).val * sval σ' r z J' := by
    intro Z r z J J' hJ hJ'
    rw [hs', hs Z r z J J' hJ hJ']
    simp [pw, Fin.prod_univ_one]
  let σ₁ : SecK C.P.L.L T.β 1 := ReciprocityTheory.ChartRestriction.G.DVR.SecOps.secScale (scal T.G.hom (v : W)) s'
  have hC₁ : T.Carries (v : W) σ' σ₁ := by
    intro Z r z J J' hJ hJ'
    rw [sval_secScale _ _ _ _ hJ, hs₁ Z r z J J' hJ hJ', pow_one, _root_.mul_assoc]
  have hα : Flat C.α := MorphismProperty.of_isPullback (P := @Flat) C.α_cart.1.flip (GlobalTheory.T.genericPoint_flat_of_modification_of_domain R C.toModif)
  refine ⟨σ₁, ⟨σ', f', hC₁, hP, hX⟩, fun Z p p' hpp z J hJ => ?_⟩
  rw [gs_scal, ReciprocityTheory.ChartRestriction.G.H1.cst_one, _root_.one_mul]
  refine cancel C T hα b hb σ₁ _ (fun Z p p' hpp z J hJ => ?_) Z p p' hpp z J hJ
  choose I hI using fun χ : Z ⟶ T.G.left => exists_chart T.U.LG.isLB (χ z)
  have hI' : Good T.U.LG.L z I := hI
  have e1 := hC Z p z J I hJ hI'
  have e2 := hσ Z p p' hpp z J hJ
  rw [e1, gs_scal, gs_scal, pow_one] at e2
  rw [sval_secScale _ _ _ _ hJ, sval_secScale _ _ _ _ hJ, hs₁ Z p z J I hJ hI', gs_scal, gs_scal]

  have hρ : ∀ c : R, cst (p ≫ T.G.hom) z (T.φ c) = cst (p' ≫ C.A.A.hom) z (algebraMap R (FractionRing R) c) := by
    intro c
    have hm : (p ≫ T.G.hom) ≫ spMap T.φ = (p' ≫ C.A.A.hom) ≫ spMap (algebraMap R (FractionRing R)) := by
      have h1 : T.β ≫ C.G.hom = T.G.hom ≫ T.ξ := T.cart.1.w
      have h2 : C.α ≫ C.G.hom = C.A.A.hom ≫ C.gp := C.α_cart.1.w
      calc (p ≫ T.G.hom) ≫ spMap T.φ = p ≫ T.G.hom ≫ T.ξ ≫ C.π := by rw [T.ξ_π, Category.assoc]
        _ = (p ≫ T.β) ≫ C.G.hom ≫ C.π := by rw [← Category.assoc T.G.hom, ← h1]; simp only [Category.assoc]
        _ = (p' ≫ C.α) ≫ C.G.hom ≫ C.π := by rw [hpp]
        _ = p' ≫ C.A.A.hom ≫ C.gp ≫ C.π := by rw [Category.assoc, ← Category.assoc C.α, h2]; simp only [Category.assoc]
        _ = (p' ≫ C.A.A.hom) ≫ spMap (algebraMap R (FractionRing R)) := by rw [C.gp_π, Category.assoc]
    rw [← cst_comp, hm, cst_comp]
  have hrU : IsUnit (cst (p' ≫ C.A.A.hom) z (algebraMap R (FractionRing R) r)) :=
    cst_unit _ _ (isUnit_iff_ne_zero.2 ((map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 hr))
  have hx' : cst (p' ≫ C.A.A.hom) z x * cst (p' ≫ C.A.A.hom) z (algebraMap R (FractionRing R) r) =
      cst (p' ≫ C.A.A.hom) z (algebraMap R (FractionRing R) t) := by
    rw [← ReciprocityTheory.ChartRestriction.G.H1.cst_mul, hx]
  have hbt' : cst (p ≫ T.G.hom) z b * cst (p ≫ T.G.hom) z (T.φ t) =
      cst (p ≫ T.G.hom) z a * cst (p ≫ T.G.hom) z (T.φ r) * cst (p ≫ T.G.hom) z (v : W) := by
    rw [← ReciprocityTheory.ChartRestriction.G.H1.cst_mul, ← ReciprocityTheory.ChartRestriction.G.H1.cst_mul, ← ReciprocityTheory.ChartRestriction.G.H1.cst_mul, hbt]
  rw [hρ, hρ, ← hx'] at hbt'
  have hsc : cst (p ≫ T.G.hom) z b * cst (p' ≫ C.A.A.hom) z x =
      cst (p ≫ T.G.hom) z a * cst (p ≫ T.G.hom) z (v : W) := by
    apply hrU.mul_right_cancel
    linear_combination hbt'
  linear_combination (cst (p ≫ T.G.hom) z (v : W)) * e2 - sval θ₀ p' z J * hsc

end GlobalTheory.Mum.Rescale
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitExpansionScalarRescaleDegreeOneStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trait_expansionScalar_rescale_degreeOne : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (F₁ : IntFam (maximalIdeal R) D.toPre 1) (θ₀ : SecK C.P.L.L C.α 1) (r t : R) (x : FractionRing R), r ≠ 0 → x * algebraMap R (FractionRing R) r = algebraMap R (FractionRing R) t → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (a b : W) (v : Wˣ), a ≠ 0 → b ≠ 0 → T.Exp a b θ₀ F₁ → b * T.φ t = a * T.φ r * v → T.Exp 1 (v : W) (ReciprocityTheory.ChartRestriction.G.DVR.SecOps.secScale (scal C.A.A.hom x) θ₀) F₁ := by
  first | exact @GlobalTheory.Mum.Rescale.rescale | exact GlobalTheory.Mum.Rescale.rescale | (intros; apply GlobalTheory.Mum.Rescale.rescale <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaSectionNormalisedUnitAtTraits
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_theta_unit_at_traits : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (m : ℕ), Odd m → ∀ Φ : IntFam (maximalIdeal R) D.toPre (m ^ 2) → SecK C.P.L.L C.α (m ^ 2), (∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W), ∃ u : Wˣ, ∀ F, T.Exp 1 u (Φ F) F) → ∀ F₁ : IntFam (maximalIdeal R) D.toPre 1, ∃ θ : SecK C.P.L.L C.α 1, ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W), ∃ u : Wˣ, T.Exp 1 u θ F₁ := by
  intro R _ _ _ hR D C m hm Φ hΦ F₁
  obtain ⟨θ₀, hθ₀⟩ := GlobalTheory.T.exists_polarisationSection_ratio_integralThetaFamily R hR D C F₁
  obtain ⟨r, t, hr, ht, h⟩ := GlobalTheory.T.thetaExpansionScalars_ratio_odd_mul R hR D C m hm Φ hΦ F₁ θ₀ hθ₀
  have hr' : algebraMap R (FractionRing R) r ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 hr
  refine ⟨ReciprocityTheory.ChartRestriction.G.DVR.SecOps.secScale (scal C.A.A.hom
    (algebraMap R (FractionRing R) t / algebraMap R (FractionRing R) r)) θ₀, fun W _ _ _ T => ?_⟩
  obtain ⟨a, b, v, ha, hb, hE, hv⟩ := h W T
  exact ⟨v, GlobalTheory.T.trait_expansionScalar_rescale_degreeOne R hR D C F₁ θ₀ r t _ hr (div_mul_cancel₀ _ hr') W T a b v ha hb hE hv⟩

end GlobalTheory.Mum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaSectionNormalisedUnitAtTraitsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_thetaSection_normalised_unit_at_traits : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (m : ℕ), Odd m → ∀ Φ : IntFam (maximalIdeal R) D.toPre (m ^ 2) → SecK C.P.L.L C.α (m ^ 2), (∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W), ∃ u : Wˣ, ∀ F, T.Exp 1 u (Φ F) F) → ∀ F₁ : IntFam (maximalIdeal R) D.toPre 1, ∃ θ : SecK C.P.L.L C.α 1, ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W), ∃ u : Wˣ, T.Exp 1 u θ F₁ := by
  first | exact @GlobalTheory.Mum.exists_theta_unit_at_traits | exact GlobalTheory.Mum.exists_theta_unit_at_traits | (intros; apply GlobalTheory.Mum.exists_theta_unit_at_traits <;> assumption)
end
