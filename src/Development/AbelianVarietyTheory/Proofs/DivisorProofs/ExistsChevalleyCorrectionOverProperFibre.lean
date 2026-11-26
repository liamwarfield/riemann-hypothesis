module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionValueEqAtFirstOrderOfTangents
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyPullbackStructureModuleIso
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCorrectionApproximateIdealSections

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ApproximateGermMemCartierIdealModMaxPow
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ApproximateGermMemCartierIdealModMaxPow
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.ZH GlobalTheory.Poinc
open GlobalTheory.SiegelTor

namespace GlobalTheory.FibreCorr

theorem nonUnitAt_of_isHom {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M₁ M : RatModel o Ω} {π : M.Z ⟶ M₁.Z}
    (hπ : M₁.IsHom M (AlgHom.id o Ω) π) {x' : M.Z} {h : Ω} (hh : NonUnitAt M₁ (π x') h) : NonUnitAt M x' h := by
  obtain ⟨hO, h0⟩ := hh
  refine ⟨mem_O_of_isHom hπ hO, ?_⟩
  rcases h0 with h0 | hinv
  · exact Or.inl h0
  · right
    intro hinv'
    obtain ⟨V, g, hzV, rfl⟩ := hO
    have hV : (V : Set M₁.Z).Nonempty := ⟨_, hzV⟩
    have hnu : ¬ IsUnit (⟨valF M₁.pt V g, RatModel.valF_mem_O hzV g⟩ : M₁.O (π x')) := by
      rw [RatModel.isUnit_O_iff]
      exact fun H => hinv H.2
    rw [RatModel.isUnit_valF_iff hzV g] at hnu
    have hx : x' ∈ π ⁻¹ᵁ V := hzV
    have happ := hπ.valF_app hV g
    simp only [AlgHom.id_apply] at happ
    have hnu' : ¬ IsUnit (⟨valF M.pt (π ⁻¹ᵁ V) ((π.app V).hom g), RatModel.valF_mem_O hx _⟩ : M.O x') := by
      rw [RatModel.isUnit_valF_iff hx]
      intro hb
      apply hnu
      have : x' ∈ π ⁻¹ᵁ M₁.Z.basicOpen g := by
        rw [Scheme.preimage_basicOpen]; exact hb
      exact this
    apply hnu'
    rw [RatModel.isUnit_O_iff]
    refine ⟨?_, ?_⟩
    · show valF M.pt _ _ ≠ 0
      rw [happ]
      intro h0
      have : valF M₁.pt V g = 0 := h0
      rw [this, inv_zero] at hinv
      exact hinv (zero_mem _)
    · simpa only [happ] using hinv'

end GlobalTheory.FibreCorr

theorem GlobalTheory.FibreCorr.locbound : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (M₁ M : RatModel o Ω) (π : M.Z ⟶ M₁.Z) (hπ : M₁.IsHom M (AlgHom.id o Ω) π), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.Z → ∀ (U : M.Z.Opens) (D : EffCartierData M.Z), (U : Set M.Z).Nonempty → ∀ (z : M₁.Z) (x' : M.Z), π x' = z → IsClosed ({x'} : Set M.Z) → ∀ f', EqAt M D x' f' → ∀ e : ℕ, ∃ N : ℕ, ∀ n, N ≤ n → ∀ F ∈ GlobalTheory.FibreCorr.approxIdeal hπ U D z n, ∃ a b : M.O x', (F : Ω) = a * f' + b ∧ b ∈ maximalIdeal (M.O x') ^ e := by
  intro o Ω _ _ _ _ M₁ M π hπ hN U D hU z x' hx hc f' hf e
  obtain ⟨i, hi, rfl⟩ := hf
  have hne : valF M.pt (D.U i) (D.f i) ≠ 0 := by
    intro h0
    haveI : Nontrivial Γ(M.Z, D.U i) := RingHom.domain_nontrivial (M.Z.presheaf.germ (D.U i) x' hi).hom
    have hreg := D.regular i (D.U i) le_rfl
    have h00 : D.f i = 0 := by
      apply RatModel.valF_injective M ⟨x', hi⟩
      rw [h0]
      unfold valF
      split_ifs <;> simp
    rw [h00, map_zero] at hreg
    exact zero_notMem_nonZeroDivisors hreg
  obtain ⟨C, hC⟩ := GlobalTheory.T.izumi_bound_mod_principal_ideal o Ω M hN U hU x' hc _ (RatModel.valF_mem_O hi (D.f i)) hne
  refine ⟨C e, fun n hn F hF => ?_⟩
  have hF' := approxIdeal_antitone U D z hn hF
  have hFO : (F : Ω) ∈ M.O x' := mem_O_of_isHom hπ (hx ▸ F.2)
  obtain ⟨a, b, hab, hb⟩ := hC e ⟨F, hFO⟩ (by
    intro p _ y hy
    obtain ⟨hyx, hyU⟩ := hy
    have hz : π (y (cPt p)) = z := by rw [hyx, hx]
    rcases hF' p y hz hyU _ ⟨i, hyx ▸ hi, rfl⟩ with h1 | ⟨h, hh, hle⟩
    · exact Or.inl h1
    · refine Or.inr ⟨h, nonUnitAt_of_isHom hπ (x' := x') (by rw [hx]; exact hh), hle⟩)
  refine ⟨a, b, hab, ?_⟩
  have hsp : Ideal.span {c : M.O x' | ¬ IsUnit c} = maximalIdeal (M.O x') := Ideal.span_eq (maximalIdeal (M.O x'))
  rwa [hsp] at hb
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ApproximateGermMemCartierIdealModMaxPowStatement
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.ZH GlobalTheory.Poinc
open GlobalTheory.SiegelTor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.approximate_germ_mem_cartier_ideal_mod_max_pow : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (M₁ M : RatModel o Ω) (π : M.Z ⟶ M₁.Z) (hπ : M₁.IsHom M (AlgHom.id o Ω) π), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.Z → ∀ (U : M.Z.Opens) (D : EffCartierData M.Z), (U : Set M.Z).Nonempty → ∀ (z : M₁.Z) (x' : M.Z), π x' = z → IsClosed ({x'} : Set M.Z) → ∀ f', EqAt M D x' f' → ∀ e : ℕ, ∃ N : ℕ, ∀ n, N ≤ n → ∀ F ∈ GlobalTheory.FibreCorr.approxIdeal hπ U D z n, ∃ a b : M.O x', (F : Ω) = a * f' + b ∧ b ∈ maximalIdeal (M.O x') ^ e := by
  first | exact @GlobalTheory.FibreCorr.locbound | exact GlobalTheory.FibreCorr.locbound | (intros; apply GlobalTheory.FibreCorr.locbound <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemMapFibreDivisibilityIdealCompletionLimit
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecializesLiftClosedFibreStalkBaseChange
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecializesLiftClosedFibreStalkBaseChange
open AlgebraicGeometry CategoryTheory Limits IsLocalRing

namespace GlobalTheory

theorem specializes_lift_closedFibre_stalkBaseChange : ∀ {X Y : Scheme.{0}} (π : X ⟶ Y) (z : Y) (R : Type) [CommRing R] [IsLocalRing R] (i : Y.presheaf.stalk z →+* R) [IsLocalHom i], Function.Surjective (IsLocalRing.ResidueField.map i) → ∀ (v : ↥(pullback (Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk z) π)) (y : X), pullback.fst (Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk z) π v = IsLocalRing.closedPoint R → pullback.snd (Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk z) π v ⤳ y → π y = z → ∃ w : ↥(pullback (Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk z) π), v ⤳ w ∧ pullback.snd (Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk z) π w = y := by
  intro X Y π z R _ _ i _ hi v y hv hsp hy
  let e : IsLocalRing.ResidueField (Y.presheaf.stalk z) ≃+* IsLocalRing.ResidueField R :=
    RingEquiv.ofBijective (IsLocalRing.ResidueField.map i) ⟨(IsLocalRing.ResidueField.map i).injective, hi⟩
  let β : R →+* IsLocalRing.ResidueField (Y.presheaf.stalk z) := e.symm.toRingHom.comp (IsLocalRing.residue R)
  have hβ : β.comp i = IsLocalRing.residue _ := by
    ext x
    simp only [β, RingHom.comp_apply, RingEquiv.coe_toRingHom]
    rw [← IsLocalRing.ResidueField.map_residue]
    exact e.symm_apply_apply (IsLocalRing.residue _ x)
  have hcomp : Spec.map (CommRingCat.ofHom β : CommRingCat.of R ⟶ Y.residueField z) ≫ Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk z = Y.fromSpecResidueField z := by
    rw [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp, hβ]
    rfl
  have hβcl : Spec.map (CommRingCat.ofHom β : CommRingCat.of R ⟶ Y.residueField z) (IsLocalRing.closedPoint (Y.residueField z)) = IsLocalRing.closedPoint R := by
    have : IsLocalHom β := inferInstance
    exact IsLocalRing.comap_closedPoint β
  let g : π.fiber z ⟶ pullback (Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk z) π :=
    pullback.lift (π.fiberToSpecResidueField z ≫ (Spec.map (CommRingCat.ofHom β : CommRingCat.of R ⟶ Y.residueField z))) (π.fiberι z)
      (by rw [Category.assoc]; exact (congrArg (π.fiberToSpecResidueField z ≫ ·) hcomp).trans (π.fiber_fac z).symm)
  have hgq : g ≫ pullback.snd (Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk z) π = π.fiberι z := pullback.lift_snd _ _ _
  let h : pullback (Spec.map (CommRingCat.ofHom β : CommRingCat.of R ⟶ Y.residueField z)) (pullback.fst (Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk z) π) ⟶ π.fiber z :=
    pullback.lift (pullback.snd (Spec.map (CommRingCat.ofHom β : CommRingCat.of R ⟶ Y.residueField z)) (pullback.fst (Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk z) π) ≫ pullback.snd (Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk z) π) (pullback.fst (Spec.map (CommRingCat.ofHom β : CommRingCat.of R ⟶ Y.residueField z)) (pullback.fst (Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk z) π))
      (by
        rw [Category.assoc, ← pullback.condition (f := (Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk z)) (g := π), ← Category.assoc,
          ← pullback.condition (f := (Spec.map (CommRingCat.ofHom β : CommRingCat.of R ⟶ Y.residueField z))) (g := pullback.fst (Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk z) π), Category.assoc]; exact congrArg _ hcomp)
  have hgf : g ≫ pullback.fst (Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk z) π = π.fiberToSpecResidueField z ≫ (Spec.map (CommRingCat.ofHom β : CommRingCat.of R ⟶ Y.residueField z)) := pullback.lift_fst _ _ _
  have hhf : h ≫ π.fiberToSpecResidueField z = pullback.fst (Spec.map (CommRingCat.ofHom β : CommRingCat.of R ⟶ Y.residueField z)) (pullback.fst (Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk z) π) := pullback.lift_snd _ _ _
  have hhι : h ≫ π.fiberι z = pullback.snd (Spec.map (CommRingCat.ofHom β : CommRingCat.of R ⟶ Y.residueField z)) (pullback.fst (Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk z) π) ≫ pullback.snd (Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk z) π := pullback.lift_fst _ _ _
  have hhg : h ≫ g = pullback.snd (Spec.map (CommRingCat.ofHom β : CommRingCat.of R ⟶ Y.residueField z)) (pullback.fst (Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk z) π) := by
    apply pullback.hom_ext
    · rw [Category.assoc, hgf, ← Category.assoc, hhf]
      exact pullback.condition (f := (Spec.map (CommRingCat.ofHom β : CommRingCat.of R ⟶ Y.residueField z))) (g := pullback.fst (Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk z) π)
    · rw [Category.assoc, hgq, hhι]
  obtain ⟨u, -, hu2⟩ := Scheme.Pullback.exists_preimage_pullback (f := (Spec.map (CommRingCat.ofHom β : CommRingCat.of R ⟶ Y.residueField z))) (g := pullback.fst (Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk z) π)
    (IsLocalRing.closedPoint (Y.residueField z)) v (hβcl.trans hv.symm)
  have hga : g (h u) = v := by
    rw [← Scheme.Hom.comp_apply, hhg, hu2]
  have hfa : π.fiberι z (h u) = pullback.snd (Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk z) π v := by
    rw [← hga, ← Scheme.Hom.comp_apply g, hgq]
  let b := (π.fiberHomeo z).symm ⟨y, hy⟩
  have hb : π.fiberι z b = y := π.fiberι_fiberHomeo_symm z ⟨y, hy⟩
  have hab : h u ⤳ b := by
    rw [← (π.fiberι z).isEmbedding.toIsInducing.specializes_iff, hfa, hb]
    exact hsp
  refine ⟨g b, ?_, ?_⟩
  · rw [← hga]
    exact hab.map g.continuous
  · rw [← Scheme.Hom.comp_apply, hgq, hb]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecializesLiftClosedFibreStalkBaseChangeStatement
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_specializes_lift_pullback_snd_fromSpecStalk : ∀ {X Y : Scheme.{0}} (π : X ⟶ Y) (z : Y) (R : Type) [CommRing R] [IsLocalRing R] (i : Y.presheaf.stalk z →+* R) [IsLocalHom i], Function.Surjective (IsLocalRing.ResidueField.map i) → ∀ (v : ↥(pullback (Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk z) π)) (y : X), pullback.fst (Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk z) π v = IsLocalRing.closedPoint R → pullback.snd (Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk z) π v ⤳ y → π y = z → ∃ w : ↥(pullback (Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk z) π), v ⤳ w ∧ pullback.snd (Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk z) π w = y := by
  first | exact @GlobalTheory.specializes_lift_closedFibre_stalkBaseChange | exact GlobalTheory.specializes_lift_closedFibre_stalkBaseChange | (intros; apply GlobalTheory.specializes_lift_closedFibre_stalkBaseChange <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemMapFibreDivisibilityIdealCompletionLimit
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.ZH GlobalTheory.Poinc
open GlobalTheory.SiegelTor

noncomputable section

namespace GlobalTheory.FormalCorr

theorem mem_stalkId_of_closedPoints (P : Scheme.{0}) [CompactSpace P] (I : P.IdealSheafData) (s : Γ(P, ⊤))
    (h : ∀ v : P, IsClosed ({v} : Set P) → (P.presheaf.germ ⊤ v trivial).hom s ∈ FinalTheorems.stalkId I v) (v : P) :
    (P.presheaf.germ ⊤ v trivial).hom s ∈ FinalTheorems.stalkId I v := by
  by_contra hv
  set Z : Set P := {y | (P.presheaf.germ ⊤ y trivial).hom s ∉ FinalTheorems.stalkId I y} with hZ
  have hZc : IsClosed Z := by
    rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
    intro y hy
    have hy' : (P.presheaf.germ ⊤ y trivial).hom s ∈ FinalTheorems.stalkId I y := by
      simpa [hZ] using hy
    obtain ⟨O, hyO, hO⟩ := GlobalTheory.SpreadIdeal.exists_open_nhds_mem_stalkId P I s y hy'
    exact ⟨O, fun z hz => by simpa [hZ] using hO z hz, O.2, hyO⟩
  obtain ⟨w, hwZ, hw⟩ := hZc.exists_closed_singleton ⟨v, hv⟩
  exact hwZ (h w hw)

theorem closed_of_closed {X Y : Scheme.{0}} (π : X ⟶ Y) [UniversallyClosed π] (z : Y) (hz : IsClosed ({z} : Set Y))
    (R : Type) [CommRing R] [IsLocalRing R] (i : Y.presheaf.stalk z →+* R) [IsLocalHom i]
    (hi : Function.Surjective (ResidueField.map i))
    (v : ↥(pullback (Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk z) π)) (hv : IsClosed ({v} : Set _)) :
    pullback.fst (Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk z) π v = closedPoint R ∧
      IsClosed ({pullback.snd (Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk z) π v} : Set X) := by
  have hξc : (Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk z) (closedPoint R) = z := by
    have : Spec.map (CommRingCat.ofHom i) (closedPoint R) = closedPoint (Y.presheaf.stalk z) :=
      IsLocalRing.comap_closedPoint i
    exact (Scheme.Hom.comp_apply _ _ _).trans ((congrArg (Y.fromSpecStalk z) this).trans Scheme.fromSpecStalk_closedPoint)
  have h1 : pullback.fst _ π v = closedPoint R := by
    have hc : IsClosed ((pullback.fst _ π).base '' {v}) := (pullback.fst _ π).isClosedMap _ hv
    rw [Set.image_singleton] at hc
    exact ((IsLocalRing.specializes_closedPoint _).mem_closed hc rfl).symm
  refine ⟨h1, ?_⟩
  have hx : π (pullback.snd _ π v) = z := by
    rw [← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply, h1, hξc]
  refine closure_subset_iff_isClosed.1 fun y hy => ?_
  have hvy : pullback.snd _ π v ⤳ y := specializes_iff_mem_closure.2 hy
  have hy' : π y = z := by
    have : z ⤳ π y := hx ▸ hvy.map π.continuous
    exact (hz.closure_eq ▸ specializes_iff_mem_closure.1 this : π y ∈ ({z} : Set Y))
  obtain ⟨w, hvw, hw⟩ := GlobalTheory.T.exists_specializes_lift_pullback_snd_fromSpecStalk π z R i hi v y h1 hvy hy'
  have : w = v := (hv.closure_eq ▸ specializes_iff_mem_closure.1 hvw : w ∈ ({v} : Set _))
  rw [← hw, this]
  rfl

theorem mem_map_of_approx_closed {Z S : Scheme.{0}} (π : S ⟶ Z) [IsProper π] (I : S.IdealSheafData) (z : Z)
    (hz : IsClosed ({z} : Set Z))
    {R : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (i : Z.presheaf.stalk z →+* R) [IsLocalHom i]
    (hi : i.Flat) (hres : Function.Surjective (ResidueField.map i))
    (F : R) (a : ℕ → Z.presheaf.stalk z) (ha : ∀ n, F - i (a n) ∈ maximalIdeal R ^ n)
    (H : ∀ (x : S) (ψ : Z.presheaf.stalk z →+* S.presheaf.stalk x), IsLocalHom ψ →
      spMap ψ ≫ Z.fromSpecStalk z = S.fromSpecStalk x ≫ π → π x = z → IsClosed ({x} : Set S) →
      ∀ e : ℕ, ∃ N : ℕ, ∀ n, N ≤ n → ψ (a n) ∈ FinalTheorems.stalkId I x ⊔ maximalIdeal _ ^ e) :
    F ∈ (FinalTheorems.stalkId (I.map π) z).map i := by
  rw [← GlobalTheory.PolDiv.idlAlong_fromSpecStalk]
  have hcl := fun v hv => closed_of_closed π z hz R i hres v hv
  generalize hξ : Spec.map (CommRingCat.ofHom i) ≫ Z.fromSpecStalk z = ξ at hcl
  have hfl : Flat ξ := by
    rw [← hξ]
    haveI := GlobalTheory.LocalRingGeneralisation.flat_fromSpecStalk Z z
    haveI : Flat (Spec.map (CommRingCat.ofHom i)) := (HasRingHomProperty.Spec_iff (P := @Flat)).2 hi
    infer_instance
  have hξc : ξ (closedPoint R) = z := by
    rw [← hξ]
    have : Spec.map (CommRingCat.ofHom i) (closedPoint R) = closedPoint (Z.presheaf.stalk z) :=
      IsLocalRing.comap_closedPoint i
    exact (Scheme.Hom.comp_apply _ _ _).trans ((congrArg (Z.fromSpecStalk z) this).trans Scheme.fromSpecStalk_closedPoint)
  refine GlobalTheory.FlatPush.mem_idlAlong_map_of_flat π I ξ ?_ F ?_
  · rw [Scheme.stalkClosedPointTo, CommRingCat.hom_comp]
    exact RingHom.Flat.comp (Flat.stalkMap ξ _) (RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso _))
  haveI : CompactSpace ↥(Limits.pullback ξ π : Scheme.{0}) := QuasiCompact.compactSpace_of_compactSpace (Limits.pullback.fst ξ π)
  refine mem_stalkId_of_closedPoints _ _ _ fun v hvc => ?_
  obtain ⟨hv, hqc⟩ := hcl v hvc
  haveI : IsLocallyNoetherian (Limits.pullback ξ π) := LocallyOfFiniteType.isLocallyNoetherian (Limits.pullback.fst ξ π)
  set p := Limits.pullback.fst ξ π with hp
  set q := Limits.pullback.snd ξ π with hq
  have hpq : p ≫ ξ = q ≫ π := Limits.pullback.condition
  have hx : π (q v) = z := by
    rw [← Scheme.Hom.comp_apply, ← hpq, Scheme.Hom.comp_apply, hv, hξc]
  obtain ⟨ψ, hψ, hψc⟩ := ApproxCorr.exists_stalk_map π (q v) z hx
  let α : CommRingCat.of R ⟶ (Limits.pullback ξ π).presheaf.stalk v :=
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (Sp R).presheaf.germ ⊤ (p v) trivial) ≫ p.stalkMap v
  have hα : Spec.map α = (Limits.pullback ξ π).fromSpecStalk v ≫ p := by
    rw [Spec.map_comp, ← Spec.fromSpecStalk_eq, Scheme.SpecMap_stalkMap_fromSpecStalk]
  haveI : IsLocalHom α.hom := by
    refine (IsLocalRing.isLocalHom_iff_comap_closedPoint _).2 ?_
    change Spec.map α (closedPoint _) = _
    rw [hα]
    exact (Scheme.Hom.comp_apply _ _ _).trans ((congrArg p Scheme.fromSpecStalk_closedPoint).trans hv)
  haveI : IsLocalHom (q.stalkMap v).hom := q.toLRSHom.prop v
  have hc : CommRingCat.ofHom i ≫ α = CommRingCat.ofHom ψ ≫ q.stalkMap v := by
    refine Spec.map_injective ((cancel_mono (Z.fromSpecStalk z)).1 ?_)
    rw [Spec.map_comp _ α, Spec.map_comp _ (q.stalkMap v), Category.assoc, Category.assoc, hξ, hα, Category.assoc, hpq]
    erw [hψc]
    rw [Scheme.SpecMap_stalkMap_fromSpecStalk_assoc]
  have hc' : ∀ t, α.hom (i t) = (q.stalkMap v).hom (ψ t) := fun t => congrArg (fun f => f.hom t) hc
  have e : ((Limits.pullback ξ π).presheaf.germ ⊤ v trivial).hom (p.appTop.hom
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom F)) = α.hom F :=
    (Scheme.Hom.germ_stalkMap_apply p ⊤ v trivial _).symm
  rw [e]
  refine ApproxCorr.mem_of_forall_mem_sup _ _ fun k => ?_
  obtain ⟨N, hN⟩ := H (q v) ψ hψ hψc hx hqc k
  obtain ⟨b, hb, c, hc2, hbc⟩ := Submodule.mem_sup.1 (hN (max N k) (le_max_left _ _))
  have e2 : α.hom F = (q.stalkMap v).hom b + ((q.stalkMap v).hom c + α.hom (F - i (a (max N k)))) := by
    rw [← add_assoc, ← map_add (f := _), hbc, ← hc', map_sub]; ring
  rw [e2]
  exact Submodule.add_mem_sup (GlobalTheory.VanStalk.map_le_stalkId_comap q I v (Ideal.mem_map_of_mem _ hb))
    (add_mem (ApproxCorr.map_mem_pow _ hc2)
      (Ideal.pow_le_pow_right (le_max_right N k) (ApproxCorr.map_mem_pow _ (ha _))))

end GlobalTheory.FormalCorr

namespace GlobalTheory.FormalCorr

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

theorem stalkHom_stalkMap {M₁ M : RatModel o Ω} {π : M.Z ⟶ M₁.Z} (hπ : M₁.IsHom M (AlgHom.id o Ω) π) (x : M.Z)
    (t : M₁.Z.presheaf.stalk (π x)) : M.stalkHom x ((π.stalkMap x).hom t) = M₁.stalkHom (π x) t := by
  obtain ⟨U, hU, f, rfl⟩ := M₁.Z.presheaf.germ_exist t
  rw [Scheme.Hom.germ_stalkMap_apply, RatModel.stalkHom_germ]
  exact (RatModel.stalkHom_germ (M := M) (show x ∈ π ⁻¹ᵁ U from hU) _).trans (by rw [hπ.valF_app ⟨_, hU⟩]; rfl)

theorem stalkEquiv_mem_fibreIdeal {M₁ M : RatModel o Ω} {π : M.Z ⟶ M₁.Z} (hπ : M₁.IsHom M (AlgHom.id o Ω) π)
    (D : EffCartierData M.Z) (z : M₁.Z) (t : M₁.Z.presheaf.stalk z) (ht : t ∈ FinalTheorems.stalkId (D.idealSheaf.map π) z) :
    M₁.stalkEquiv z t ∈ GlobalTheory.FibreCorr.fibreIdeal hπ D z := by
  refine GlobalTheory.FibreCorr.mem_fibreIdeal.2 ?_
  rintro x' hx' f' ⟨j, hj, hf'⟩
  subst hx'
  have h1 : FinalTheorems.stalkId ((D.idealSheaf.map π).comap π) x' ≤ FinalTheorems.stalkId D.idealSheaf x' :=
    iSup₂_mono fun U hx => Ideal.map_mono (Scheme.IdealSheafData.comap_map_le D.idealSheaf π U)
  have h2 : (π.stalkMap x').hom t ∈ FinalTheorems.stalkId D.idealSheaf x' := by
    refine h1 ?_
    rw [GlobalTheory.VanStalk.stalkId_comap]
    exact Ideal.mem_map_of_mem _ ht
  rw [D.stalkId_idealSheaf j x' hj, Ideal.mem_span_singleton'] at h2
  obtain ⟨r, hr⟩ := h2
  have h3 : (M₁.stalkEquiv (π x') t : Ω) = M.stalkHom x' r * f' := by
    rw [RatModel.coe_stalkEquiv, ← stalkHom_stalkMap hπ, ← hr, map_mul, RatModel.stalkHom_germ, hf']
  rw [h3]
  by_cases h0 : f' = 0
  · rw [h0, div_zero]; exact zero_mem _
  · rw [mul_div_cancel_right₀ _ h0]; exact (M.stalkEquiv x' r).2

end GlobalTheory.FormalCorr

theorem GlobalTheory.FormalCorr.mem_map_fibreIdeal : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (M₁ M : RatModel o Ω) (π : M.Z ⟶ M₁.Z) (hπ : M₁.IsHom M (AlgHom.id o Ω) π), IsProper π → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M₁.Z → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.Z → ∀ (D : EffCartierData M.Z) (z : M₁.Z), IsClosed ({z} : Set M₁.Z) → ∀ (F : AdicCompletion (maximalIdeal (M₁.O z)) (M₁.O z)) (a : ℕ → M₁.O z), (∀ n, F - algebraMap (M₁.O z) (AdicCompletion (maximalIdeal (M₁.O z)) (M₁.O z)) (a n) ∈ (maximalIdeal (M₁.O z)).map (algebraMap (M₁.O z) (AdicCompletion (maximalIdeal (M₁.O z)) (M₁.O z))) ^ n) → (∀ x' : M.Z, π x' = z → IsClosed ({x'} : Set M.Z) → ∀ f', EqAt M D x' f' → ∀ e : ℕ, ∃ N : ℕ, ∀ n, N ≤ n → ∃ c d : M.O x', (a n : Ω) = c * f' + d ∧ d ∈ maximalIdeal (M.O x') ^ e) → F ∈ (GlobalTheory.FibreCorr.fibreIdeal hπ D z).map (algebraMap (M₁.O z) (AdicCompletion (maximalIdeal (M₁.O z)) (M₁.O z))) := by
  intro o Ω _ _ _ _ M₁ M π hπ hprop hn₁ hn D z hz F a ha H
  haveI := hprop
  haveI := GlobalTheory.FibreCorr.isNoetherianRing_O M₁ z
  haveI := GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion _ (maximalIdeal (M₁.O z))
  let e := M₁.stalkEquiv z
  let i : M₁.Z.presheaf.stalk z →+* AdicCompletion (maximalIdeal (M₁.O z)) (M₁.O z) :=
    (algebraMap (M₁.O z) (AdicCompletion (maximalIdeal (M₁.O z)) (M₁.O z))).comp e.toRingHom
  haveI : IsLocalHom e.toRingHom := ⟨fun a ha => by simpa using ha.map e.symm⟩
  haveI : IsLocalHom i := inferInstance
  have hfl : i.Flat := RingHom.Flat.comp (RingHom.Flat.of_bijective e.bijective)
    (RingHom.flat_algebraMap_iff.2 inferInstance)
  have hres : Function.Surjective (ResidueField.map i) := by
    intro y
    obtain ⟨r, rfl⟩ := (AdicCompletion.residueField_map_bijective (M₁.O z)).2 y
    obtain ⟨s, rfl⟩ := IsLocalRing.residue_surjective r
    refine ⟨IsLocalRing.residue _ (e.symm s), ?_⟩
    simp [i, ResidueField.map_residue]
  have key := GlobalTheory.FormalCorr.mem_map_of_approx_closed π D.idealSheaf z hz i hfl hres F (fun n => e.symm (a n))
    (fun n => by
      have h := ha n
      rw [← AdicCompletion.maximalIdeal_eq_map] at h
      simpa [i] using h) ?_
  · rw [show i = (algebraMap (M₁.O z) (AdicCompletion (maximalIdeal (M₁.O z)) (M₁.O z))).comp e.toRingHom from rfl,
      ← Ideal.map_map] at key
    exact Ideal.map_mono (Ideal.map_le_iff_le_comap.2 fun t ht =>
      Ideal.mem_comap.2 (GlobalTheory.FormalCorr.stalkEquiv_mem_fibreIdeal hπ D z t ht)) key
  · intro x ψ hψ hc hx hcl k
    subst hx
    have hψe : ψ = (π.stalkMap x).hom := by
      have h := Spec.map_injective ((cancel_mono (M₁.Z.fromSpecStalk (π x))).1
        (hc.trans (Scheme.SpecMap_stalkMap_fromSpecStalk π).symm))
      exact congrArg CommRingCat.Hom.hom h
    subst hψe
    obtain ⟨j, hj⟩ : ∃ j, x ∈ D.U j := TopologicalSpace.Opens.mem_iSup.1 (D.cover ▸ trivial)
    obtain ⟨N, hN⟩ := H x rfl hcl _ ⟨j, hj, rfl⟩ k
    refine ⟨N, fun n hn => ?_⟩
    obtain ⟨c, d, hcd, hd⟩ := hN n hn
    let E := M.stalkEquiv x
    haveI : IsLocalHom E.symm.toRingHom := ⟨fun a ha => by simpa using ha.map E⟩
    have hw : (π.stalkMap x).hom (e.symm (a n)) =
        E.symm c * (M.Z.presheaf.germ _ x hj).hom (D.f j) + E.symm d := by
      apply E.injective
      apply Subtype.ext
      rw [map_add (f := _), map_mul, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply, RatModel.stalkEquiv_germ]
      simp only [Subalgebra.coe_add, Subalgebra.coe_mul]
      rw [RatModel.coe_stalkEquiv, GlobalTheory.FormalCorr.stalkHom_stalkMap hπ, ← RatModel.coe_stalkEquiv,
        RingEquiv.apply_symm_apply, hcd]
    rw [hw, D.stalkId_idealSheaf j x hj]
    refine Submodule.add_mem_sup (Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)) ?_
    exact ApproxCorr.map_mem_pow E.symm.toRingHom hd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemMapFibreDivisibilityIdealCompletionLimitStatement
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.ZH GlobalTheory.Poinc
open GlobalTheory.SiegelTor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_map_fibreDivisibilityIdeal_completion_limit : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (M₁ M : RatModel o Ω) (π : M.Z ⟶ M₁.Z) (hπ : M₁.IsHom M (AlgHom.id o Ω) π), IsProper π → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M₁.Z → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.Z → ∀ (D : EffCartierData M.Z) (z : M₁.Z), IsClosed ({z} : Set M₁.Z) → ∀ (F : AdicCompletion (maximalIdeal (M₁.O z)) (M₁.O z)) (a : ℕ → M₁.O z), (∀ n, F - algebraMap (M₁.O z) (AdicCompletion (maximalIdeal (M₁.O z)) (M₁.O z)) (a n) ∈ (maximalIdeal (M₁.O z)).map (algebraMap (M₁.O z) (AdicCompletion (maximalIdeal (M₁.O z)) (M₁.O z))) ^ n) → (∀ x' : M.Z, π x' = z → IsClosed ({x'} : Set M.Z) → ∀ f', EqAt M D x' f' → ∀ e : ℕ, ∃ N : ℕ, ∀ n, N ≤ n → ∃ c d : M.O x', (a n : Ω) = c * f' + d ∧ d ∈ maximalIdeal (M.O x') ^ e) → F ∈ (GlobalTheory.FibreCorr.fibreIdeal hπ D z).map (algebraMap (M₁.O z) (AdicCompletion (maximalIdeal (M₁.O z)) (M₁.O z))) := by
  first | exact @GlobalTheory.FormalCorr.mem_map_fibreIdeal | exact GlobalTheory.FormalCorr.mem_map_fibreIdeal | (intros; apply GlobalTheory.FormalCorr.mem_map_fibreIdeal <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsChevalleyCorrectionOverProperFibre
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.ZH GlobalTheory.Poinc
open GlobalTheory.SiegelTor

theorem GlobalTheory.FibreCorr.exists_correction : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (M₁ M : RatModel o Ω) (π : M.Z ⟶ M₁.Z), M₁.IsHom M (AlgHom.id o Ω) π → IsProper π → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M₁.Z → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.Z → ∀ (U : M.Z.Opens) (D : EffCartierData M.Z), (U : Set M.Z).Nonempty → (∀ x ∈ D.idealSheaf.support, x ∉ U) → ∀ (z : M₁.Z), IsClosed ({z} : Set M₁.Z) → ∀ k : ℕ, ∃ e : ℕ, ∀ F : M₁.O z, (∀ (q : ℕ) [Fact q.Prime] (y : Sp (OO q) ⟶ M.Z), π (y (cPt q)) = z → Set.range (gPt q ≫ y) ⊆ U → ∀ f, EqAt M D (y (cPt q)) f → ‖M.val (gPt q ≫ y) F‖ ≤ ‖M.val (gPt q ≫ y) f‖ ∨ ∃ h, NonUnitAt M₁ z h ∧ ‖M.val (gPt q ≫ y) F‖ ≤ ‖M.val (gPt q ≫ y) h‖ ^ e) → ∃ G b : M₁.O z, (F : Ω) = G + b ∧ (∀ x' : M.Z, π x' = z → ∀ f', EqAt M D x' f' → (G : Ω) / f' ∈ M.O x') ∧ b ∈ Ideal.span {c : M₁.O z | ¬ IsUnit c} ^ k := by
  intro o Ω _ _ _ _ M₁ M π hπ hprop hn₁ hn U D hU _ z hz k
  haveI := GlobalTheory.FibreCorr.isNoetherianRing_O M₁ z
  have key : ∀ k, ∃ e, GlobalTheory.FibreCorr.approxIdeal hπ U D z e ≤
      GlobalTheory.FibreCorr.fibreIdeal hπ D z ⊔ maximalIdeal (M₁.O z) ^ k := by
    refine GlobalTheory.T.chevalley_exists_le_sup_maximalIdeal_pow_of_antitone (M₁.O z) (GlobalTheory.FibreCorr.approxIdeal hπ U D z) (GlobalTheory.FibreCorr.fibreIdeal hπ D z)
      (GlobalTheory.FibreCorr.approxIdeal_antitone U D z) (GlobalTheory.FibreCorr.pow_le_approxIdeal U D z) ?_
    intro F a ha hK
    have ha' : ∀ n, F - algebraMap (M₁.O z) (AdicCompletion (maximalIdeal (M₁.O z)) (M₁.O z)) (a n) ∈
        (maximalIdeal (M₁.O z)).map (algebraMap (M₁.O z) (AdicCompletion (maximalIdeal (M₁.O z)) (M₁.O z))) ^ n := by
      intro n
      rw [← AdicCompletion.maximalIdeal_eq_map]
      exact ha n
    refine GlobalTheory.T.mem_map_fibreDivisibilityIdeal_completion_limit o Ω M₁ M π hπ hprop hn₁ hn D z hz F a ha' ?_
    intro x' hx' hc f' hf' e
    obtain ⟨N, hN⟩ := GlobalTheory.T.approximate_germ_mem_cartier_ideal_mod_max_pow o Ω M₁ M π hπ hn U D hU z x' hx' hc f' hf' e
    exact ⟨N, fun n hn => hN n hn (a n) (hK n)⟩
  obtain ⟨e, he⟩ := key k
  refine ⟨e, fun F hF => ?_⟩
  have hF' : F ∈ GlobalTheory.FibreCorr.approxIdeal hπ U D z e := hF
  obtain ⟨G, hG, b, hb, hGb⟩ := Submodule.mem_sup.1 (he hF')
  refine ⟨G, b, ?_, fun x' hx' f' hf' => hG x' hx' f' hf', ?_⟩
  · rw [← hGb]; simp
  · have hm : Ideal.span {c : M₁.O z | ¬ IsUnit c} = maximalIdeal (M₁.O z) :=
      Ideal.span_eq (maximalIdeal (M₁.O z))
    rw [hm]
    exact hb
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsChevalleyCorrectionOverProperFibreStatement
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.ZH GlobalTheory.Poinc
open GlobalTheory.SiegelTor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_chevalley_correction_over_proper_fibre : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (M₁ M : RatModel o Ω) (π : M.Z ⟶ M₁.Z), M₁.IsHom M (AlgHom.id o Ω) π → IsProper π → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M₁.Z → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.Z → ∀ (U : M.Z.Opens) (D : EffCartierData M.Z), (U : Set M.Z).Nonempty → (∀ x ∈ D.idealSheaf.support, x ∉ U) → ∀ (z : M₁.Z), IsClosed ({z} : Set M₁.Z) → ∀ k : ℕ, ∃ e : ℕ, ∀ F : M₁.O z, (∀ (q : ℕ) [Fact q.Prime] (y : Sp (OO q) ⟶ M.Z), π (y (cPt q)) = z → Set.range (gPt q ≫ y) ⊆ U → ∀ f, EqAt M D (y (cPt q)) f → ‖M.val (gPt q ≫ y) F‖ ≤ ‖M.val (gPt q ≫ y) f‖ ∨ ∃ h, NonUnitAt M₁ z h ∧ ‖M.val (gPt q ≫ y) F‖ ≤ ‖M.val (gPt q ≫ y) h‖ ^ e) → ∃ G b : M₁.O z, (F : Ω) = G + b ∧ (∀ x' : M.Z, π x' = z → ∀ f', EqAt M D x' f' → (G : Ω) / f' ∈ M.O x') ∧ b ∈ Ideal.span {c : M₁.O z | ¬ IsUnit c} ^ k := by
  first | exact @GlobalTheory.FibreCorr.exists_correction | exact GlobalTheory.FibreCorr.exists_correction | (intros; apply GlobalTheory.FibreCorr.exists_correction <;> assumption)
end
