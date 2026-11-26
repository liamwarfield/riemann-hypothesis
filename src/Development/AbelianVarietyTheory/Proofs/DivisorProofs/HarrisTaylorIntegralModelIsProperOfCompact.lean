module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SemiAbelianReductionAlongIsogenyStrictHenselian
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PotentialGoodReductionOfLieMultZeroStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorModuliObjectPotentiallyGoodReduction
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PotentialGoodReductionOfOrderLeftAction
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PotentialGoodReductionOfDivisionAlgebraLeftActio
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PotentialGoodReductionOfDivisionAlgebraOrderActi
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankTorusExtensionCharactersLeRelDim
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankTorusExtensionCharactersLeRelDim
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem finrank_torusExtension_le : ∀ (k : Type) [Field k] (G : Over (Sp k)) [GrpObj G] (E : TorusExtension G) (g : ℕ), SmoothOfRelativeDimension g G.hom → (letI := E.addCommGroup; Module.finrank ℤ E.X) ≤ g := by
  intro k _ G _ E g hG
  letI := E.addCommGroup
  haveI := E.free
  haveI := E.finite
  letI := E.grpB
  haveI : IsSeparated E.B.hom := E.isAbelian.proper.toIsSeparated
  have hη : IsClosedImmersion (η : 𝟙_ (Over (Sp k)) ⟶ E.B).left := isClosedImmersion_of_comp_eq_id (Y := Sp k) E.B.hom _ (Over.w _)
  have hpb : IsPullback E.i.left (toUnit (splitTorus (Sp k) E.X)).left E.q.left (η : 𝟙_ (Over (Sp k)) ⟶ E.B).left :=
    E.isKernel.map (Over.forget _)
  have hi : IsClosedImmersion E.i.left :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) hpb.flip hη
  have pt : Sp k := Classical.choice inferInstance
  have hne : Nonempty (splitTorus (Sp k) E.X).left :=
    ⟨(η : 𝟙_ (Over (Sp k)) ⟶ splitTorus (Sp k) E.X).left ((toUnit (Over.mk (𝟙 (Sp k)))).left pt)⟩
  exact relDim_le_of_isClosedImmersion k _ G E.i hi hne g _ hG (ReciprocityTheory.ChartRestriction.G.H1.torus_dim (Sp k) E.X)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankTorusExtensionCharactersLeRelDimStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_torusExtension_characters_le_relDim : ∀ (k : Type) [Field k] (G : Over (Sp k)) [GrpObj G] (E : TorusExtension G) (g : ℕ), SmoothOfRelativeDimension g G.hom → (letI := E.addCommGroup; Module.finrank ℤ E.X) ≤ g := by
  first | exact @GlobalTheory.finrank_torusExtension_le | exact GlobalTheory.finrank_torusExtension_le | (intros; apply GlobalTheory.finrank_torusExtension_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisionAlgebraOrderNoSmallLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisionAlgebraOrderNoSmallLattice
open NumberField

namespace GlobalTheory

theorem divAlg_clear_denominators {B : Type} [Ring B] [Algebra ℚ B] {O : Type} [Ring O]
    (ι : O →+* B) (v : B) (hv : v ∈ Submodule.span ℚ (Set.range ι)) :
    ∃ n : ℕ, 0 < n ∧ ∃ c : O, ι c = (n : ℚ) • v := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨o, rfl⟩ := hx
    exact ⟨1, one_pos, o, by simp⟩
  | zero => exact ⟨1, one_pos, 0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨n₁, hn₁, c₁, hc₁⟩ := hx
    obtain ⟨n₂, hn₂, c₂, hc₂⟩ := hy
    refine ⟨n₁ * n₂, Nat.mul_pos hn₁ hn₂, (n₂ : O) * c₁ + (n₁ : O) * c₂, ?_⟩
    rw [map_add (f := _), map_mul, map_mul, map_natCast, map_natCast, hc₁, hc₂, ← nsmul_eq_mul,
      ← nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul ℚ n₂, ← Nat.cast_smul_eq_nsmul ℚ n₁, smul_smul,
      smul_smul, smul_add]
    push_cast
    rw [mul_comm (n₂ : ℚ) (n₁ : ℚ)]
  | smul q x _ hx =>
    obtain ⟨n, hn, c, hc⟩ := hx
    refine ⟨q.den * n, Nat.mul_pos q.den_pos hn, (q.num : O) * c, ?_⟩
    rw [map_mul, map_intCast, hc, smul_smul]
    rw [show ((q.num : B)) = algebraMap ℚ B (q.num : ℚ) by simp, ← Algebra.smul_def, smul_smul]
    congr 1
    push_cast
    rw [← Rat.mul_den_eq_num]
    ring

theorem divAlg_smul_injective {B : Type} [Ring B] [Algebra ℚ B] {O : Type} [Ring O]
    (ι : O →+* B) (hunit : ∀ x : B, x ≠ 0 → IsUnit x) (hinj : Function.Injective ι)
    (hspan : Submodule.span ℚ (Set.range ι) = ⊤)
    {X : Type} [AddCommGroup X] [Module.Free ℤ X] (ρ : O →+* Module.End ℤ X)
    (x : X) (hx : x ≠ 0) (a : O) (ha : ρ a x = 0) : a = 0 := by
  by_contra h0
  have hιa : ι a ≠ 0 := fun h => h0 (hinj (by simpa using h))
  obtain ⟨u, hu⟩ := hunit _ hιa
  obtain ⟨n, hn, c, hc⟩ := divAlg_clear_denominators ι (↑u⁻¹ : B) (by rw [hspan]; trivial)
  have hca : c * a = (n : O) := by
    apply hinj
    rw [map_mul, hc, map_natCast, ← hu, Algebra.smul_mul_assoc, Units.inv_mul,
      Algebra.smul_def, mul_one]
    simp
  have h1 : ρ (c * a) x = 0 := by rw [map_mul, Module.End.mul_apply, ha, map_zero]
  rw [hca, map_natCast] at h1
  have h2 : (n : ℤ) • x = 0 := by
    rw [natCast_zsmul]
    simpa [Module.End.natCast_apply] using h1
  rcases smul_eq_zero.mp h2 with h | h
  · omega
  · exact hx h

end GlobalTheory

namespace GlobalTheory

theorem divAlg_order_no_small_lattice : ∀ (B : Type) [Ring B] [Algebra ℚ B] [Module.Finite ℚ B]
    (O : Type) [Ring O] (ι : O →+* B), (∀ x : B, x ≠ 0 → IsUnit x) → Function.Injective ι →
    Submodule.span ℚ (Set.range ι) = ⊤ → ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X]
    [Module.Finite ℤ X] (ρ : O →+* Module.End ℤ X), Module.finrank ℤ X < Module.finrank ℚ B →
    Module.finrank ℤ X = 0 := by
  intro B _ _ _ O _ ι hunit hinj hspan X _ _ _ ρ hlt
  by_contra hne
  have hnt : Nontrivial X := Module.nontrivial_of_finrank_pos (R := ℤ) (Nat.pos_of_ne_zero hne)
  obtain ⟨x, hx⟩ := exists_ne (0 : X)

  let φ : O →ₗ[ℤ] X := (AddMonoidHom.mk' (fun a => ρ a x) (by intro a b; simp)).toIntLinearMap
  have hφ : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro a ha
    exact divAlg_smul_injective ι hunit hinj hspan ρ x hx a ha
  let ι' : O →ₗ[ℤ] B := ι.toAddMonoidHom.toIntLinearMap
  obtain ⟨b, hbsub, hbspan, hbli⟩ := exists_linearIndependent ℚ (Set.range ι)
  rw [hspan] at hbspan
  let e := Module.Basis.mk hbli (by rw [Subtype.range_coe, hbspan])
  choose f hf using fun i : b => hbsub i.2
  have li1 : LinearIndependent ℤ (fun i : b => (i : B)) := hbli.restrict_scalars' ℤ
  have li2 : LinearIndependent ℤ f := by
    apply LinearIndependent.of_comp ι'
    convert li1 using 1
    funext i
    exact hf i
  have li3 : LinearIndependent ℤ (φ ∘ f) := li2.map' φ (LinearMap.ker_eq_bot.mpr hφ)
  have hc := li3.cardinal_le_rank
  rw [Module.Basis.mk_eq_rank'' e, ← Module.finrank_eq_rank, ← Module.finrank_eq_rank] at hc
  have := Nat.cast_le.mp hc
  omega

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisionAlgebraOrderNoSmallLatticeStatement
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.divisionAlgebra_order_no_small_lattice : ∀ (B : Type) [Ring B] [Algebra ℚ B] [Module.Finite ℚ B] (O : Type) [Ring O] (ι : O →+* B), (∀ x : B, x ≠ 0 → IsUnit x) → Function.Injective ι → Submodule.span ℚ (Set.range ι) = ⊤ → ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (ρ : O →+* Module.End ℤ X), Module.finrank ℤ X < Module.finrank ℚ B → Module.finrank ℤ X = 0 := by
  first | exact @GlobalTheory.divAlg_order_no_small_lattice | exact GlobalTheory.divAlg_order_no_small_lattice | (intros; apply GlobalTheory.divAlg_order_no_small_lattice <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PotentialGoodReductionOfDivisionAlgebraOrderActi
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj

namespace GlobalTheory.DivPotGood

theorem potGood_of_divisionAlgebra_action : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (A : Over (Sp K)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (O : Type) [Ring O] (act : O → (A ⟶ A)), (∀ a, IsMonHom (act a)) → act 1 = 𝟙 A → (∀ a b, act (a * b) = act a ≫ act b) → (∀ a b, act (a + b) = act a * act b) → ∀ (B : Type) [Ring B] [Algebra ℚ B] [Module.Finite ℚ B] (jj : O →+* B), (∀ x : B, x ≠ 0 → IsUnit x) → Function.Injective jj → Submodule.span ℚ (Set.range jj) = ⊤ → g < Module.finrank ℚ B → GlobalTheory.SS.PotModel V K A (fun _ _ _ G _ => IsAbelianScheme G) := by
  intro V K _ _ _ _ _ _ _ _ A _ g hA hg O _ act hact h1 hmul hadd B _ _ _ jj hdiv hinj hspan hgB
  obtain ⟨W, L, i1, i2, i3, i4, i5, i6, i7, i8, hcomp, hfin, hloc, hcpl, G, iG, hmod, hsa, ⟨E⟩⟩ :=
    GlobalTheory.T.abelianVariety_potential_semiAbelian_splitTorus V K A hA
  refine ⟨W, L, i1, i2, i3, i4, i5, i6, i7, i8, hcomp, hfin, hloc, hcpl, G, iG, hmod, ?_⟩

  set f : Sp L ⟶ Sp K := spMap (algebraMap K L)
  set A' := (Over.pullback f).obj A
  have hψ : IsGrpPullback A' A f (pullback.fst A.hom f) := isGrpPullback_pullback A f
  obtain ⟨act₁, ⟨h1a, h1b, h1c, h1d⟩, -⟩ := GlobalTheory.T.exists_ring_action_pullback_cartesian_group_schemes (Sp K) (Sp L) f A A' _ hψ O act hact h1 hmul hadd
  obtain ⟨φ, hφ⟩ := GlobalTheory.T.isGrpPullback_of_group_scheme_model_base_change K W L A G hmod A' _ hψ
  obtain ⟨act₂, ⟨h2a, h2b, h2c, h2d⟩, -⟩ := GlobalTheory.T.exists_ring_action_extension_compatible W L G A' φ hsa hφ O act₁ h1a h1b h1c h1d
  have hres : IsGrpPullback (GlobalTheory.SS.spFibre G) G (spMap (IsLocalRing.residue W)) (pullback.fst G.hom _) :=
    isGrpPullback_pullback G _
  obtain ⟨act₃, ⟨h3a, h3b, h3c, h3d⟩, -⟩ :=
    GlobalTheory.T.exists_ring_action_pullback_cartesian_group_schemes _ _ (spMap (IsLocalRing.residue W)) G (GlobalTheory.SS.spFibre G) _ hres O act₂ h2a h2b h2c h2d
  haveI : IsCommMonObj (GlobalTheory.SS.spFibre G) := by
    haveI := hsa.comm
    infer_instance
  obtain ⟨ρ, -⟩ := GlobalTheory.T.ringHom_characterEnd_of_torusExtension_action _ (GlobalTheory.SS.spFibre G) E O act₃ h3a h3b h3c h3d

  obtain ⟨e, -⟩ := hmod
  haveI : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
  have hA'g : SmoothOfRelativeDimension g A'.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback (IsPullback.of_hasPullback A.hom f) hg
  have hGLg : SmoothOfRelativeDimension g ((Over.pullback (spMap (algebraMap W L))).obj G).hom := by
    exact (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback
      (IsPullback.of_horiz_isIso (fst := e.hom.left) (snd := ((Over.pullback (spMap (algebraMap W L))).obj G).hom)
        (f := A'.hom) (g := 𝟙 _) ⟨by rw [Category.comp_id]; exact Over.w e.hom⟩) hA'g
  have hsc : GlobalTheory.SS.SmConn G := ⟨hsa.comm, hsa.smooth, hsa.separated, hsa.quasiCompact, hsa.geomConnected⟩
  have hsp : SmoothOfRelativeDimension g (GlobalTheory.SS.spFibre G).hom := GlobalTheory.IsogRed.relDim_spFibre (K := L) G hsc g hGLg
  have hle := GlobalTheory.T.finrank_torusExtension_characters_le_relDim _ (GlobalTheory.SS.spFibre G) E g hsp
  letI := E.addCommGroup
  haveI := E.free
  haveI := E.finite
  have h0 : Module.finrank ℤ E.X = 0 := GlobalTheory.T.divisionAlgebra_order_no_small_lattice B O jj hdiv hinj hspan E.X ρ (lt_of_le_of_lt hle hgB)

  have hprop : IsProper ((Over.pullback (spMap (algebraMap W L))).obj G).hom := by
    haveI : IsProper A.hom := hA.proper
    haveI : IsProper A'.hom := inferInstanceAs (IsProper (pullback.snd A.hom f))
    rw [← Over.w e.hom]
    infer_instance
  exact GlobalTheory.T.isAbelianScheme_semiAbelian_dvr_noSpecialTorus W L G hsa hprop E h0

end GlobalTheory.DivPotGood
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PotentialGoodReductionOfDivisionAlgebraOrderActiStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.potentialGoodReduction_of_divisionAlgebra_order_action : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (A : Over (Sp K)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (O : Type) [Ring O] (act : O → (A ⟶ A)), (∀ a, IsMonHom (act a)) → act 1 = 𝟙 A → (∀ a b, act (a * b) = act a ≫ act b) → (∀ a b, act (a + b) = act a * act b) → ∀ (B : Type) [Ring B] [Algebra ℚ B] [Module.Finite ℚ B] (jj : O →+* B), (∀ x : B, x ≠ 0 → IsUnit x) → Function.Injective jj → Submodule.span ℚ (Set.range jj) = ⊤ → g < Module.finrank ℚ B → GlobalTheory.SS.PotModel V K A (fun _ _ _ G _ => IsAbelianScheme G) := by
  first | exact @GlobalTheory.DivPotGood.potGood_of_divisionAlgebra_action | exact GlobalTheory.DivPotGood.potGood_of_divisionAlgebra_action | (intros; apply GlobalTheory.DivPotGood.potGood_of_divisionAlgebra_action <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PotentialGoodReductionOfDivisionAlgebraLeftActio
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
namespace GlobalTheory

theorem potModel_of_divAlg_leftAction : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (A : Over (Sp K)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (O : Type) [Ring O] (act : O → (A ⟶ A)), (∀ a, IsMonHom (act a)) → act 1 = 𝟙 A → (∀ a b, act (a * b) = act b ≫ act a) → (∀ a b, act (a + b) = act a * act b) → ∀ (B : Type) [Ring B] [Algebra ℚ B] [Module.Finite ℚ B] (jj : O →+* B), (∀ x : B, x ≠ 0 → IsUnit x) → Function.Injective jj → Submodule.span ℚ (Set.range jj) = ⊤ → g < Module.finrank ℚ B → GlobalTheory.SS.PotModel V K A (fun _ _ _ G _ => IsAbelianScheme G) := by
  intro V K _ _ _ _ _ _ _ _ A _ g hA hg O _ act hmon h1 hmul hadd B _ _ _ jj hunit hinj hspan hdim
  haveI : Module.Finite ℚ Bᵐᵒᵖ :=
    Module.Finite.equiv (MulOpposite.opLinearEquiv ℚ (M := B))
  refine GlobalTheory.T.potentialGoodReduction_of_divisionAlgebra_order_action V K A g hA hg Oᵐᵒᵖ (fun a => act a.unop) (fun a => hmon a.unop) h1
    (fun a b => hmul b.unop a.unop) (fun a b => hadd a.unop b.unop) Bᵐᵒᵖ (RingHom.op jj)
    ?_ ?_ ?_ ?_
  · intro x hx
    have hx' : x.unop ≠ 0 := by simpa using hx
    simpa using (hunit x.unop hx').op
  · intro a b h
    exact MulOpposite.unop_injective (hinj (MulOpposite.op_injective h))
  · have : Set.range (RingHom.op jj) = (MulOpposite.opLinearEquiv ℚ (M := B)) '' Set.range jj := by
      ext x; constructor
      · rintro ⟨a, rfl⟩; exact ⟨jj a.unop, ⟨a.unop, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨a, rfl⟩, rfl⟩; exact ⟨MulOpposite.op a, rfl⟩
    rw [this, ← LinearEquiv.coe_coe, Submodule.span_image, hspan, Submodule.map_top, LinearEquiv.range]
  · rwa [(MulOpposite.opLinearEquiv ℚ (M := B)).symm.finrank_eq]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PotentialGoodReductionOfDivisionAlgebraLeftActioStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.potentialGoodReduction_of_divisionAlgebra_leftAction : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (A : Over (Sp K)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (O : Type) [Ring O] (act : O → (A ⟶ A)), (∀ a, IsMonHom (act a)) → act 1 = 𝟙 A → (∀ a b, act (a * b) = act b ≫ act a) → (∀ a b, act (a + b) = act a * act b) → ∀ (B : Type) [Ring B] [Algebra ℚ B] [Module.Finite ℚ B] (jj : O →+* B), (∀ x : B, x ≠ 0 → IsUnit x) → Function.Injective jj → Submodule.span ℚ (Set.range jj) = ⊤ → g < Module.finrank ℚ B → GlobalTheory.SS.PotModel V K A (fun _ _ _ G _ => IsAbelianScheme G) := by
  first | exact @GlobalTheory.potModel_of_divAlg_leftAction | exact GlobalTheory.potModel_of_divAlg_leftAction | (intros; apply GlobalTheory.potModel_of_divAlg_leftAction <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PotentialGoodReductionOfOrderLeftAction
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj

open scoped TensorProduct

namespace GlobalTheory

theorem DivOrder.mul_comm_of_eq_int {O : Type} [Ring O] {x y : O} {c : ℤ}
    (htf : ∀ n : ℤ, n ≠ 0 → Function.Injective (fun a : O => n • a))
    (hxy : x * y = (c : O))
    (hy : ∀ y : O, y ≠ 0 → ∃ w : O, ∃ c' : ℤ, c' ≠ 0 ∧ y * w = (c' : O)) :
    y * x = (c : O) := by
  by_cases hy0 : y = 0
  · subst hy0
    rw [mul_zero] at hxy
    rw [zero_mul, hxy]
  obtain ⟨w, c', hc', hyw⟩ := hy y hy0
  have h1 : (c : O) * w = (c' : O) * x := by
    have : x * (y * w) = (x * y) * w := (_root_.mul_assoc _ _ _).symm
    rw [hyw, hxy, ← Int.cast_comm] at this
    exact this.symm
  have h2 : (c' : O) * (y * x) = (c' : O) * (c : O) := by
    calc (c' : O) * (y * x) = y * ((c' : O) * x) := (Int.cast_commute c' y).left_comm x
      _ = y * ((c : O) * w) := by rw [h1]
      _ = (c : O) * (y * w) := ((Int.cast_commute c y).left_comm w).symm
      _ = (c' : O) * (c : O) := by rw [hyw, Int.cast_comm]
  have h3 : c' • (y * x) = c' • (c : O) := by
    simpa [zsmul_eq_mul] using h2
  exact htf c' hc' h3

theorem DivOrder.exists_zsmul_eq_tmul (O : Type) [Ring O] (z : ℚ ⊗[ℤ] O) :
    ∃ n : ℤ, n ≠ 0 ∧ ∃ x : O, n • z = (1 : ℚ) ⊗ₜ[ℤ] x := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨1, one_ne_zero, 0, by simp⟩
  | tmul q o =>
    refine ⟨(q.den : ℤ), by exact_mod_cast q.den_nz, q.num • o, ?_⟩
    rw [TensorProduct.smul_tmul', ← TensorProduct.smul_tmul]
    congr 1
    rw [zsmul_eq_mul, zsmul_eq_mul, _root_.mul_one]
    push_cast
    exact Rat.den_mul_eq_num q
  | add z₁ z₂ h₁ h₂ =>
    obtain ⟨n₁, hn₁, x₁, e₁⟩ := h₁
    obtain ⟨n₂, hn₂, x₂, e₂⟩ := h₂
    refine ⟨n₁ * n₂, mul_ne_zero hn₁ hn₂, n₂ • x₁ + n₁ • x₂, ?_⟩
    rw [smul_add, mul_comm, mul_smul, e₁, mul_comm, mul_smul, e₂, TensorProduct.tmul_add,
      TensorProduct.tmul_smul, TensorProduct.tmul_smul]

theorem DivOrder.isUnit_of_ne_zero (O : Type) [Ring O] [Module.Free ℤ O]
    (hdiv : ∀ x : O, x ≠ 0 → ∃ y : O, ∃ c : ℤ, c ≠ 0 ∧ x * y = (c : O))
    (z : ℚ ⊗[ℤ] O) (hz : z ≠ 0) : IsUnit z := by
  have hinj : Function.Injective (Algebra.TensorProduct.includeRight (R := ℤ) (A := ℚ) (B := O)) :=
    Algebra.TensorProduct.includeRight_injective (algebraMap ℤ ℚ).injective_int
  have htf : ∀ n : ℤ, n ≠ 0 → Function.Injective (fun a : O => n • a) := by
    intro n hn a b hab
    apply hinj
    have h' : (n : ℚ) • ((1 : ℚ) ⊗ₜ[ℤ] a) = (n : ℚ) • ((1 : ℚ) ⊗ₜ[ℤ] b) := by
      rw [Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul, ← TensorProduct.tmul_smul,
        ← TensorProduct.tmul_smul]
      exact congrArg _ hab
    exact smul_right_injective _ (by exact_mod_cast hn : (n : ℚ) ≠ 0) h'
  obtain ⟨n, hn, x, e⟩ := DivOrder.exists_zsmul_eq_tmul O z
  have hx : x ≠ 0 := by
    rintro rfl
    rw [TensorProduct.tmul_zero, ← Int.cast_smul_eq_zsmul ℚ] at e
    exact hz ((smul_eq_zero.mp e).resolve_left (by exact_mod_cast hn))
  obtain ⟨y, c, hc, hxy⟩ := hdiv x hx
  have hyx : y * x = (c : O) := DivOrder.mul_comm_of_eq_int htf hxy hdiv
  set jj : O →ₐ[ℤ] ℚ ⊗[ℤ] O := Algebra.TensorProduct.includeRight with hjj
  have hjx : IsUnit (jj x) := by
    rw [isUnit_iff_exists]
    refine ⟨algebraMap ℚ _ ((c : ℚ)⁻¹) * jj y, ?_, ?_⟩
    · rw [Algebra.left_comm, ← map_mul, hxy, map_intCast, ← map_intCast (algebraMap ℚ (ℚ ⊗[ℤ] O)),
        ← map_mul, inv_mul_cancel₀ (by exact_mod_cast hc), map_one]
    · rw [_root_.mul_assoc, ← map_mul, hyx, map_intCast, ← map_intCast (algebraMap ℚ (ℚ ⊗[ℤ] O)),
        ← map_mul, inv_mul_cancel₀ (by exact_mod_cast hc), map_one]
  have hz' : z = algebraMap ℚ _ ((n : ℚ)⁻¹) * jj x := by
    have : jj x = (1 : ℚ) ⊗ₜ[ℤ] x := rfl
    rw [← Algebra.smul_def, this, ← e, ← Int.cast_smul_eq_zsmul ℚ, smul_smul,
      inv_mul_cancel₀ (by exact_mod_cast hn), one_smul]
  rw [hz']
  exact ((isUnit_iff_ne_zero.mpr (inv_ne_zero (by exact_mod_cast hn))).map _).mul hjx

theorem potModel_of_intDivOrder_leftAction : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (A : Over (Sp K)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (O : Type) [Ring O] [Module.Free ℤ O] [Module.Finite ℤ O] (act : O → (A ⟶ A)), (∀ a, IsMonHom (act a)) → act 1 = 𝟙 A → (∀ a b, act (a * b) = act b ≫ act a) → (∀ a b, act (a + b) = act a * act b) → (∀ x : O, x ≠ 0 → ∃ y : O, ∃ c : ℤ, c ≠ 0 ∧ x * y = (c : O)) → g < Module.finrank ℤ O → GlobalTheory.SS.PotModel V K A (fun _ _ _ G _ => IsAbelianScheme G) := by
  intro V K _ _ _ _ _ _ _ _ A _ g hA hsm O _ _ _ act hmon h1 hmul hadd hdiv hg
  have hinj : Function.Injective (Algebra.TensorProduct.includeRight (R := ℤ) (A := ℚ) (B := O)) :=
    Algebra.TensorProduct.includeRight_injective (algebraMap ℤ ℚ).injective_int
  have hspan : Submodule.span ℚ (Set.range
      (Algebra.TensorProduct.includeRight (R := ℤ) (A := ℚ) (B := O)).toRingHom) = ⊤ := by
    rw [eq_top_iff]
    intro z _
    obtain ⟨n, hn, x, e⟩ := DivOrder.exists_zsmul_eq_tmul O z
    have hz : z = ((n : ℚ)⁻¹) • ((1 : ℚ) ⊗ₜ[ℤ] x) := by
      rw [← e, ← Int.cast_smul_eq_zsmul ℚ, smul_smul, inv_mul_cancel₀ (by exact_mod_cast hn),
        one_smul]
    rw [hz]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, rfl⟩)
  have hrank : Module.finrank ℚ (ℚ ⊗[ℤ] O) = Module.finrank ℤ O := Module.finrank_baseChange
  exact GlobalTheory.T.potentialGoodReduction_of_divisionAlgebra_leftAction V K A g hA hsm O act hmon h1 hmul hadd (ℚ ⊗[ℤ] O)
    (Algebra.TensorProduct.includeRight (R := ℤ) (A := ℚ) (B := O)).toRingHom
    (DivOrder.isUnit_of_ne_zero O hdiv) hinj hspan (hrank ▸ hg)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PotentialGoodReductionOfOrderLeftActionStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.potentialGoodReduction_of_order_leftAction : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (A : Over (Sp K)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (O : Type) [Ring O] [Module.Free ℤ O] [Module.Finite ℤ O] (act : O → (A ⟶ A)), (∀ a, IsMonHom (act a)) → act 1 = 𝟙 A → (∀ a b, act (a * b) = act b ≫ act a) → (∀ a b, act (a + b) = act a * act b) → (∀ x : O, x ≠ 0 → ∃ y : O, ∃ c : ℤ, c ≠ 0 ∧ x * y = (c : O)) → g < Module.finrank ℤ O → GlobalTheory.SS.PotModel V K A (fun _ _ _ G _ => IsAbelianScheme G) := by
  first | exact @GlobalTheory.potModel_of_intDivOrder_leftAction | exact GlobalTheory.potModel_of_intDivOrder_leftAction | (intros; apply GlobalTheory.potModel_of_intDivOrder_leftAction <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoMulRelDimEqFinrankHarrisTaylorLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoMulRelDimEqFinrankHarrisTaylorLattice
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
open GlobalTheory.UPel.HT

namespace GlobalTheory.UPel.HT

theorem two_mul_relDim_eq_finrank : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (K : Type) [Field K] (β : R →+* K) (o : Obj b N (spMap β)) (g : ℕ), SmoothOfRelativeDimension g o.A.hom → 2 * g = Module.finrank ℤ D.La := by
  intro p _ D R _ b N K _ β o g hg
  haveI := D.freeLa
  haveI := D.finLa
  obtain ⟨ℓ, hℓp, hℓ⟩ := Nat.exists_infinite_primes (p + 1)
  have hcop : ℓ.Coprime p := (Nat.coprime_primes hℓ (Fact.out)).2 (by omega)
  have hℓ0 : 0 < ℓ := hℓ.pos
  have hℓK : (ℓ : K) ≠ 0 := by
    have h := (b.unit ℓ hcop).map β
    rw [map_natCast] at h
    exact h.ne_zero
  have hx : spMap (algebraMap K (AlgebraicClosure K)) ≫ spMap β =
      spMap ((algebraMap K (AlgebraicClosure K)).comp β) := by
    simp only [spMap, ← Spec.map_comp]
    rfl
  obtain ⟨I, -⟩ := o.geom (AlgebraicClosure K) (spMap (algebraMap K (AlgebraicClosure K)))
    ((algebraMap K (AlgebraicClosure K)).comp β) hx
  have hc := GlobalTheory.SepClosedTorsion.card_torsion_sepClosed K (AlgebraicClosure K) o.A o.ab g hg ℓ hℓK
  let f : D.La →+ Additive (Over.mk (spMap (algebraMap K (AlgebraicClosure K))) ⟶ o.A) :=
    AddMonoidHom.mk' (fun a => Additive.ofMul (I.ev ℓ a)) fun a b => congrArg Additive.ofMul (I.add ℓ a b)
  have hk : f.ker = (nsmulAddMonoidHom ℓ : D.La →+ D.La).range := by
    ext a
    rw [AddMonoidHom.mem_ker, AddMonoidHom.mem_range]
    exact (I.ker ℓ hℓ0 hcop a).trans ⟨fun ⟨b, h⟩ => ⟨b, h.symm⟩, fun ⟨b, h⟩ => ⟨b, h.symm⟩⟩
  have h2 : Nat.card {x : ptOver K (AlgebraicClosure K) ⟶ o.A // x ^ ℓ = 1} = ℓ ^ Module.finrank ℤ D.La := by
    rw [← AddSubgroup.index_range_nsmul, ← hk, AddSubgroup.index_ker]
    exact Nat.card_congr (Equiv.subtypeEquiv Additive.ofMul fun u => I.onto ℓ hℓ0 hcop u)
  rw [hc] at h2
  exact Nat.pow_right_injective hℓ.two_le h2

end GlobalTheory.UPel.HT
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoMulRelDimEqFinrankHarrisTaylorLatticeStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
open GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.two_mul_relDim_eq_finrank_harrisTaylor_lattice : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (K : Type) [Field K] (β : R →+* K) (o : Obj b N (spMap β)) (g : ℕ), SmoothOfRelativeDimension g o.A.hom → 2 * g = Module.finrank ℤ D.La := by
  first | exact @GlobalTheory.UPel.HT.two_mul_relDim_eq_finrank | exact GlobalTheory.UPel.HT.two_mul_relDim_eq_finrank | (intros; apply GlobalTheory.UPel.HT.two_mul_relDim_eq_finrank <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEmbeddingLieMultiplicityZeroCharZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEmbeddingLieMultiplicityZeroCharZero
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
open GlobalTheory.UPel.HT

noncomputable section

namespace GlobalTheory.HTLie

open GlobalTheory.EigenSplit GlobalTheory.TanMod GlobalTheory.DetCompare GlobalTheory.IndefiniteRowSideFullHecke.LieCharpolyRootPairs

theorem eq_zero_of_mem_eigenSub_of_sum {O k N : Type} [CommRing O] [Field k] [AddCommGroup N] [Module k N]
    (ρ : O →+* Module.End k N) (σ : O →+* k) {κ : Type} (χ : κ → O →+* k) (hχ : ∀ i, χ i ≠ σ)
    (s : Finset κ) : ∀ (m : N) (y : κ → N), m ∈ eigenSub ρ σ → (∀ i, y i ∈ eigenSub ρ (χ i)) →
      m = ∑ i ∈ s, y i → m = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => intro m y _ _ h; simpa using h
  | insert j s hj ih =>
    intro m y hm hy h
    obtain ⟨c, hc⟩ : ∃ c, χ j c ≠ σ c := by
      by_contra hcon
      push_neg at hcon
      exact hχ j (RingHom.ext hcon)
    let f : Module.End k N := ρ c - χ j c • LinearMap.id
    have hfm : f m = (σ c - χ j c) • m := by
      simp [f, mem_eigenSub.1 hm c, sub_smul]
    have hfy : ∀ i, f (y i) = (χ i c - χ j c) • y i := fun i => by
      simp [f, mem_eigenSub.1 (hy i) c, sub_smul]
    have h1 : (σ c - χ j c) • m = ∑ i ∈ s, (χ i c - χ j c) • y i := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← hfm, h, Finset.sum_insert hj, map_add (f := _), map_sum, hfy j, sub_self, zero_smul, zero_add]
      exact Finset.sum_congr rfl fun i _ => hfy i
    have h2 := ih ((σ c - χ j c) • m) (fun i => (χ i c - χ j c) • y i)
      (Submodule.smul_mem _ _ hm) (fun i => Submodule.smul_mem _ _ (hy i)) h1
    have hne : σ c - χ j c ≠ 0 := sub_ne_zero.2 (Ne.symm hc)
    exact (smul_eq_zero.1 h2).resolve_left hne

theorem exists_ringHom_avoid {F : Type} [Field F] [NumberField F] [IsCMField F] (bar : 𝓞 F ≃+* 𝓞 F)
    (bar_eq : ∀ a : 𝓞 F, ((bar a : 𝓞 F) : F) = IsCMField.complexConj F (a : F))
    (ω : 𝓞 F) (tr nm : ℤ) (tr_eq : ω + bar ω = (tr : 𝓞 F)) (nm_eq : ω * bar ω = (nm : 𝓞 F))
    (disc_neg : tr ^ 2 - 4 * nm < 0)
    (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (ρ : k) (hρ : ρ ^ 2 - tr * ρ + nm = 0)
    (a : ℕ) (ha : 2 * a < Module.finrank ℚ F) (χ : Fin a → (𝓞 F →+* k)) :
    ∃ σ : 𝓞 F →+* k, σ ω = ρ ∧ ∀ i, χ i ≠ σ := by
  classical
  let cj : F →+* F := ((IsCMField.complexConj F : F ≃ₐ[maximalRealSubfield F] F) : F →+* F)
  have e1 : (ω : F) + ((bar ω : 𝓞 F) : F) = (tr : F) := by
    have := congrArg (fun z : 𝓞 F => (z : F)) tr_eq
    simpa using this
  have e2 : (ω : F) * ((bar ω : 𝓞 F) : F) = (nm : F) := by
    have := congrArg (fun z : 𝓞 F => (z : F)) nm_eq
    simpa using this
  have hcω : cj (ω : F) = (tr : F) - (ω : F) := by
    have : cj (ω : F) = ((bar ω : 𝓞 F) : F) := (bar_eq ω).symm
    rw [this]; linear_combination e1
  have hcc : ∀ z, cj (cj z) = z := fun z => IsCMField.complexConj_apply_apply F z
  have hroot : ∀ τ : F →+* k, τ ω ^ 2 - tr * τ ω + nm = 0 := by
    intro τ
    have h1 : (ω : F) ^ 2 - tr * (ω : F) + nm = 0 := by
      linear_combination (ω : F) * e1 - e2
    have := congrArg τ h1
    simpa using this
  have hne : ρ ≠ (tr : k) - ρ := by
    intro h
    have h3 : ((tr ^ 2 - 4 * nm : ℤ) : k) = 0 := by
      push_cast
      linear_combination (2 * ρ - tr) * h - 4 * hρ
    have h4 : tr ^ 2 - 4 * nm = 0 := by exact_mod_cast h3
    omega
  have hside : ∀ τ : F →+* k, τ ω ≠ ρ → τ ω = (tr : k) - ρ := by
    intro τ h
    have : (τ ω - ρ) * (τ ω - ((tr : k) - ρ)) = 0 := by
      linear_combination hroot τ - hρ
    rcases mul_eq_zero.1 this with h' | h'
    · exact absurd (sub_eq_zero.1 h') h
    · exact sub_eq_zero.1 h'
  have hconj : ∀ τ : F →+* k, (τ.comp cj) ω = (tr : k) - τ ω := by
    intro τ
    simp [hcω]
  let T := (Finset.univ : Finset (F →+* k)).filter (fun τ => τ ω = ρ)
  let Tc := (Finset.univ : Finset (F →+* k)).filter (fun τ => ¬ τ ω = ρ)
  have hcard : T.card = Tc.card := by
    refine Finset.card_nbij' (fun τ => τ.comp cj) (fun τ => τ.comp cj) ?_ ?_ ?_ ?_
    · intro τ hτ
      simp only [T, Tc, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hτ ⊢
      rw [hconj, hτ]
      exact fun h => hne h.symm
    · intro τ hτ
      simp only [T, Tc, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hτ ⊢
      rw [hconj, hside τ hτ]; ring
    · intro τ _; ext z; simp [hcc]
    · intro τ _; ext z; simp [hcc]
  have htot : T.card + Tc.card = Module.finrank ℚ F := by
    rw [Finset.card_filter_add_card_filter_not, Finset.card_univ, NumberField.Embeddings.card]
  by_contra hcon
  push_neg at hcon
  have hsub : T.image (fun τ => τ.comp (algebraMap (𝓞 F) F)) ⊆ Finset.univ.image χ := by
    intro σ hσ
    obtain ⟨τ, hτ, rfl⟩ := Finset.mem_image.1 hσ
    simp only [T, Finset.mem_filter, Finset.mem_univ, true_and] at hτ
    obtain ⟨i, hi⟩ := hcon (τ.comp (algebraMap (𝓞 F) F)) (by simpa using hτ)
    exact Finset.mem_image.2 ⟨i, Finset.mem_univ _, hi⟩
  have hinj : Set.InjOn (fun τ : F →+* k => τ.comp (algebraMap (𝓞 F) F)) T := by
    intro τ _ τ' _ h
    exact IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 F)) h
  have hle := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn hinj] at hle
  have hle2 := (Finset.card_image_le (s := (Finset.univ : Finset (Fin a))) (f := χ))
  rw [Finset.card_univ, Fintype.card_fin] at hle2
  omega

end GlobalTheory.HTLie

namespace GlobalTheory.HTLie

open GlobalTheory.EigenSplit GlobalTheory.TanMod GlobalTheory.DetCompare GlobalTheory.IndefiniteRowSideFullHecke.LieCharpolyRootPairs

theorem exists_lieMult_zero : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s), 2 * D.a < Module.finrank ℚ D.F → ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (x : Sp k ⟶ S) (β : R →+* k), x ≫ s = spMap β → ∃ σ : 𝓞 D.F →+* k, LieMult (o.act.toF D) x σ 0 := by
  intro p _ D R _ b N S s o ha k _ _ _ x β hx
  have hρ : β b.ρ ^ 2 - D.tr * β b.ρ + D.nm = 0 := by
    have := congrArg β b.ρ_root
    simpa using this
  obtain ⟨σ, hσω, hσ⟩ := exists_ringHom_avoid D.bar D.bar_eq D.ω D.tr D.nm D.tr_eq D.nm_eq D.disc_neg k
    (β b.ρ) hρ D.a ha (fun i => β.comp (b.t i))
  refine ⟨σ, fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun w hw =>
    ⟨Fin.elim0, ⟨Fin.elim0, fun i => Fin.elim0 i, ?_⟩, fun c _ => funext fun i => Fin.elim0 i⟩⟩
  rw [List.ofFn_zero, List.prod_nil]
  obtain ⟨w', hw', hwprod⟩ := o.lie k β x hx w ⟨hw.1, by
    have := hw.2 D.ω
    rw [hσω] at this
    exact this⟩
  have hlie : ∀ i, IsLieEigen (o.act.toF D) x (β.comp (b.t i)) (w' i) :=
    fun i => ⟨(hw' i 0).1, fun c => (hw' i c).2⟩
  obtain ⟨h1, h2⟩ := (isLieEigen_iff _ x σ w).1 hw
  choose g1 g2 using fun i => (isLieEigen_iff _ x _ (w' i)).1 (hlie i)
  have hm := (mem_eigenspace_iff _ x σ _).1 h2
  have hy := fun i => (mem_eigenspace_iff _ x _ _).1 (g2 i)
  have hsum : lieEquiv x ⟨w, h1⟩ = ∑ i ∈ Finset.univ, lieEquiv x ⟨w' i, g1 i⟩ := by
    apply TanSp.ext
    rw [TanSp.pt_sum]
    show w = ∏ i, w' i
    rw [hwprod, List.prod_ofFn]
  have h0 := eq_zero_of_mem_eigenSub_of_sum _ σ (fun i => β.comp (b.t i)) hσ Finset.univ _ _ hm hy hsum
  exact congrArg TanSp.pt h0

end GlobalTheory.HTLie
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEmbeddingLieMultiplicityZeroCharZeroStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
open GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_embedding_lie_multiplicity_zero_char_zero : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s), 2 * D.a < Module.finrank ℚ D.F → ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (x : Sp k ⟶ S) (β : R →+* k), x ≫ s = spMap β → ∃ σ : 𝓞 D.F →+* k, LieMult (o.act.toF D) x σ 0 := by
  first | exact @GlobalTheory.HTLie.exists_lieMult_zero | exact GlobalTheory.HTLie.exists_lieMult_zero | (intros; apply GlobalTheory.HTLie.exists_lieMult_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorModuliObjectPotentiallyGoodReduction
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
open GlobalTheory.UPel.HT

namespace GlobalTheory.HTPotGood

theorem potGood : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (β : R →+* K) (o : Obj b N (spMap β)), (2 * D.a < Module.finrank ℚ D.F ∨ (D.IsDivision ∧ D.n < 2 * D.m)) → GlobalTheory.SS.PotModel V K o.A (fun _ _ _ G _ => IsAbelianScheme G) := by
  intro p _ D R _ b N V K _ _ _ _ _ _ _ _ β o h
  rcases h with h | ⟨hdiv, hn⟩
  · let Ω := AlgebraicClosure K
    have hx : spMap (algebraMap K Ω) ≫ spMap β = spMap ((algebraMap K Ω).comp β) := by
      simp only [spMap, ← Spec.map_comp]
      rfl
    obtain ⟨σ, hσ⟩ := GlobalTheory.T.exists_embedding_lie_multiplicity_zero_char_zero p D R b N (Sp K) (spMap β) o h Ω (spMap (algebraMap K Ω))
      ((algebraMap K Ω).comp β) hx
    exact GlobalTheory.T.potentialGoodReduction_of_lieMult_zero V K o.A o.ab D.F (o.act.toF D) Ω (algebraMap K Ω) σ hσ
  · obtain ⟨g, hg⟩ := GlobalTheory.AbVarRelDim.exists_relDim K o.A o.ab
    have h2g := GlobalTheory.T.two_mul_relDim_eq_finrank_harrisTaylor_lattice p D R b N K β o g hg
    rw [D.rankLa] at h2g
    haveI := D.freeO
    haveI := D.finO
    have hd : 0 < Module.finrank ℚ D.F := Module.finrank_pos
    have hm := D.m_pos
    have hlt : g < Module.finrank ℤ D.O := by
      rw [D.rankO]
      have h1 : D.m * D.n * Module.finrank ℚ D.F < D.m * (2 * D.m) * Module.finrank ℚ D.F := by
        apply Nat.mul_lt_mul_of_pos_right _ hd
        exact Nat.mul_lt_mul_of_pos_left hn hm
      have h2 : D.m * (2 * D.m) * Module.finrank ℚ D.F = 2 * (D.m ^ 2 * Module.finrank ℚ D.F) := by ring
      omega
    exact GlobalTheory.T.potentialGoodReduction_of_order_leftAction V K o.A g o.ab hg D.O o.act.act o.act.hom o.act.one o.act.mul o.act.add hdiv hlt

end GlobalTheory.HTPotGood
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorModuliObjectPotentiallyGoodReductionStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
open GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylorModuliObject_potentiallyGoodReduction : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (β : R →+* K) (o : Obj b N (spMap β)), (2 * D.a < Module.finrank ℚ D.F ∨ (D.IsDivision ∧ D.n < 2 * D.m)) → GlobalTheory.SS.PotModel V K o.A (fun _ _ _ G _ => IsAbelianScheme G) := by
  first | exact @GlobalTheory.HTPotGood.potGood | exact GlobalTheory.HTPotGood.potGood | (intros; apply GlobalTheory.HTPotGood.potGood <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProperOfLiftCompleteDvrCharZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescendPointValuationRingOfDominatingLocalDomain
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescendPointValuationRingOfDominatingLocalDomain
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory

theorem descend_point_to_valuationRing_of_dominating_local_domain : ∀ (V K W L : Type) [CommRing V] [IsDomain V] [ValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] [CommRing W] [IsDomain W] [IsLocalRing W] [Field L] [Algebra W L] [IsFractionRing W L] [Algebra V W] [Algebra K L], (algebraMap W L).comp (algebraMap V W) = (algebraMap K L).comp (algebraMap V K) → IsLocalHom (algebraMap V W) → ∀ (X : Scheme.{0}) (x : Sp K ⟶ X) (f : Sp W ⟶ X), spMap (algebraMap K L) ≫ x = spMap (algebraMap W L) ≫ f → ∃ x' : Sp V ⟶ X, spMap (algebraMap V K) ≫ x' = x := by
  intro V K W L _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcomm hloc X x f hxf
  classical

  let c : Sp W := IsLocalRing.closedPoint W
  obtain ⟨U, hU, hcU, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens)
    (show f c ∈ (⊤ : X.Opens) from trivial)
  have hU' : IsAffineOpen U := hU
  have hfU : ∀ a : Sp W, f a ∈ U := fun a =>
    ((IsLocalRing.specializes_closedPoint (R := W) a).map f.continuous).mem_open U.isOpen hcU
  have hrf : Set.range f ⊆ Set.range hU'.fromSpec := by
    rw [hU'.range_fromSpec]
    rintro _ ⟨a, rfl⟩
    exact hfU a
  let pL : Sp L := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum L)
  have hrx : Set.range x ⊆ Set.range hU'.fromSpec := by
    rw [hU'.range_fromSpec]
    rintro _ ⟨a, rfl⟩
    have e := congrArg (fun h : Sp L ⟶ X => h pL) hxf
    simp only [Scheme.Hom.comp_apply] at e
    have ha : a = (spMap (algebraMap K L)) pL := by
      have h : ∀ c : PrimeSpectrum K, c.asIdeal = ⊥ := fun c => Ideal.eq_bot_of_prime c.asIdeal
      exact PrimeSpectrum.ext ((h a).trans (h _).symm)
    rw [ha, e]
    exact hfU _
  have hf₁ := IsOpenImmersion.lift_fac hU'.fromSpec f hrf
  have hx₁ := IsOpenImmersion.lift_fac hU'.fromSpec x hrx
  rw [← Spec.map_preimage (IsOpenImmersion.lift hU'.fromSpec f hrf)] at hf₁
  rw [← Spec.map_preimage (IsOpenImmersion.lift hU'.fromSpec x hrx)] at hx₁
  set β := Spec.preimage (IsOpenImmersion.lift hU'.fromSpec f hrf) with hβ
  set α := Spec.preimage (IsOpenImmersion.lift hU'.fromSpec x hrx) with hα
  have key : α ≫ CommRingCat.ofHom (algebraMap K L) = β ≫ CommRingCat.ofHom (algebraMap W L) := by
    apply Spec.map_injective
    rw [← cancel_mono hU'.fromSpec, Spec.map_comp, Spec.map_comp, Category.assoc, Category.assoc, hx₁, hf₁]
    exact hxf
  have key' : ∀ r, algebraMap K L (α.hom r) = algebraMap W L (β.hom r) := fun r => by
    have e := congrArg (fun h => h.hom r) key
    simpa only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] using e

  have hmem : ∀ r, α.hom r ∈ (algebraMap V K).range := by
    intro r
    by_cases h0 : α.hom r = 0
    · exact ⟨0, by rw [h0, map_zero]⟩
    rcases ValuationRing.isInteger_or_isInteger V (α.hom r) with ⟨v, hv⟩ | ⟨b, hb⟩
    · exact ⟨v, hv⟩
    · by_cases hb0 : IsUnit b
      · obtain ⟨u, rfl⟩ := hb0
        refine ⟨((u⁻¹ : Vˣ) : V), ?_⟩
        rw [← inv_inv (α.hom r), ← hb]
        apply eq_inv_of_mul_eq_one_left
        rw [← map_mul, Units.inv_mul, map_one]
      · exfalso
        apply hb0
        apply (isUnit_map_iff (algebraMap V W) b).1
        refine isUnit_iff_exists_inv.2 ⟨β.hom r, ?_⟩
        apply IsFractionRing.injective W L
        rw [map_mul, map_one, ← key', ← RingHom.comp_apply, hcomm, RingHom.comp_apply, hb, ← map_mul,
          inv_mul_cancel₀ h0, map_one]
  have hinj : Function.Injective (algebraMap V K) := IsFractionRing.injective V K
  let e : V ≃+* (algebraMap V K).range :=
    RingEquiv.ofBijective (algebraMap V K).rangeRestrict ⟨fun a b h => hinj (congrArg Subtype.val h),
      (algebraMap V K).rangeRestrict_surjective⟩
  let χ : Γ(X, U) →+* V := e.symm.toRingHom.comp (α.hom.codRestrict _ hmem)
  have hχ : (algebraMap V K).comp χ = α.hom := by
    ext r
    change algebraMap V K (e.symm ⟨α.hom r, hmem r⟩) = α.hom r
    have := congrArg Subtype.val (e.apply_symm_apply ⟨α.hom r, hmem r⟩)
    exact this
  refine ⟨Spec.map (CommRingCat.ofHom χ : Γ(X, U) ⟶ CommRingCat.of V) ≫ hU'.fromSpec, ?_⟩
  rw [← hx₁, ← Category.assoc]
  congr 1
  rw [← Spec.map_comp]
  congr 1
  ext r
  exact congrArg (fun h => h r) hχ

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescendPointValuationRingOfDominatingLocalDomainStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.descend_point_valuationRing_of_dominating_local_domain : ∀ (V K W L : Type) [CommRing V] [IsDomain V] [ValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] [CommRing W] [IsDomain W] [IsLocalRing W] [Field L] [Algebra W L] [IsFractionRing W L] [Algebra V W] [Algebra K L], (algebraMap W L).comp (algebraMap V W) = (algebraMap K L).comp (algebraMap V K) → IsLocalHom (algebraMap V W) → ∀ (X : Scheme.{0}) (x : Sp K ⟶ X) (f : Sp W ⟶ X), spMap (algebraMap K L) ≫ x = spMap (algebraMap W L) ≫ f → ∃ x' : Sp V ⟶ X, spMap (algebraMap V K) ≫ x' = x := by
  first | exact @GlobalTheory.descend_point_to_valuationRing_of_dominating_local_domain | exact GlobalTheory.descend_point_to_valuationRing_of_dominating_local_domain | (intros; apply GlobalTheory.descend_point_to_valuationRing_of_dominating_local_domain <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InjectiveOfFlatPointAtGenericPoints
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InjectiveOfFlatPointAtGenericPoints
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem injective_of_flat_of_range_subset_genericPoints :
    ∀ (R K : Type) [CommRing R] [IsDomain R] [Field K] (X : Scheme.{0}) (s : X ⟶ Sp R) (x : Sp K ⟶ X) (β : R →+* K), Flat s → Set.range x ⊆ genericPoints X → x ≫ s = spMap β → Function.Injective β := by
  intro R K _ _ _ X s x β hs hx hxs
  set pt : Sp K := IsLocalRing.closedPoint K with hpt
  have hp : x pt ∈ genericPoints X := hx ⟨_, rfl⟩
  let g₀ : Sp R := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R)
  have hg₀ : g₀ ⤳ s (x pt) :=
    (PrimeSpectrum.le_iff_specializes _ _).mp bot_le
  obtain ⟨y, hy, e⟩ := Flat.generalizingMap s hg₀
  have h₁ : closure ({x pt} : Set X) ⊆ closure {y} :=
    specializes_iff_closure_subset.mp hy
  have h₂ : closure ({y} : Set X) ⊆ closure {x pt} :=
    hp.2 isIrreducible_singleton.closure h₁
  have hyx : y = x pt :=
    (hy.antisymm (specializes_iff_closure_subset.mpr h₂)).eq
  have h₃ : (x ≫ s) pt = g₀ := by
    rw [Scheme.Hom.comp_apply, ← hyx, e]
  rw [hxs] at h₃
  have h₄ : (spMap β pt).asIdeal = RingHom.ker β := by
    show Ideal.comap β (IsLocalRing.maximalIdeal K) = _
    rw [IsLocalRing.maximalIdeal_eq_bot]
    rfl
  rw [h₃] at h₄
  exact (RingHom.injective_iff_ker_eq_bot β).mpr h₄.symm

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InjectiveOfFlatPointAtGenericPointsStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.injective_of_flat_point_at_generic_points : ∀ (R K : Type) [CommRing R] [IsDomain R] [Field K] (X : Scheme.{0}) (s : X ⟶ Sp R) (x : Sp K ⟶ X) (β : R →+* K), Flat s → Set.range x ⊆ genericPoints X → x ≫ s = spMap β → Function.Injective β := by
  first | exact @GlobalTheory.injective_of_flat_of_range_subset_genericPoints | exact GlobalTheory.injective_of_flat_of_range_subset_genericPoints | (intros; apply GlobalTheory.injective_of_flat_of_range_subset_genericPoints <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProperOfLiftCompleteDvrCharZero
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj

namespace GlobalTheory.ValuativeFlat

theorem isProper_of_lift_dominating : ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] [IsNoetherianRing R] (X : Scheme.{0}) (s : X ⟶ Sp R), IsQProjOver s → Flat s → (∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (β : R →+* V) (x : Sp K ⟶ X), x ≫ s = spMap ((algebraMap V K).comp β) → ∃ (W L : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W) (_ : Field L) (_ : Algebra V W) (_ : Algebra W L) (_ : Algebra K L) (_ : IsFractionRing W L), (algebraMap W L).comp (algebraMap V W) = (algebraMap K L).comp (algebraMap V K) ∧ IsLocalHom (algebraMap V W) ∧ ∃ f : Sp W ⟶ X, spMap (algebraMap K L) ≫ x = spMap (algebraMap W L) ≫ f) → IsProper s := by
  intro R _ _ _ _ X s hq hflat h
  have hq' : IsQProjOver (s ≫ 𝟙 (Sp R)) := by rwa [Category.comp_id]
  have hP := GlobalTheory.ValuativeGeneric.isProper_of_lift_generic R X (Sp R) s (𝟙 _) inferInstance hq' ?_
  · exact hP
  intro V K _ _ _ _ _ _ _ x y hx hxy
  let β : R →+* V := (Spec.preimage y).hom
  have hy : y = spMap β := by simp [β, spMap]
  have hxs : x ≫ s = spMap ((algebraMap V K).comp β) := by
    rw [hxy, hy, spMap, spMap, ← Spec.map_comp]; rfl
  have hinj : Function.Injective ((algebraMap V K).comp β) :=
    GlobalTheory.T.injective_of_flat_point_at_generic_points R K X s x _ hflat hx hxs
  have : CharZero K := charZero_of_injective_ringHom hinj
  obtain ⟨W, L, _, _, _, _, _, _, _, _, hc, hloc, f, hf⟩ := h V K β x hxs
  exact GlobalTheory.T.descend_point_valuationRing_of_dominating_local_domain V K W L hc hloc X x f hf

end GlobalTheory.ValuativeFlat
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProperOfLiftCompleteDvrCharZeroStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isProper_of_lift_completeDvr_charZero : ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] [IsNoetherianRing R] (X : Scheme.{0}) (s : X ⟶ Sp R), IsQProjOver s → Flat s → (∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (β : R →+* V) (x : Sp K ⟶ X), x ≫ s = spMap ((algebraMap V K).comp β) → ∃ (W L : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W) (_ : Field L) (_ : Algebra V W) (_ : Algebra W L) (_ : Algebra K L) (_ : IsFractionRing W L), (algebraMap W L).comp (algebraMap V W) = (algebraMap K L).comp (algebraMap V K) ∧ IsLocalHom (algebraMap V W) ∧ ∃ f : Sp W ⟶ X, spMap (algebraMap K L) ≫ x = spMap (algebraMap W L) ≫ f) → IsProper s := by
  first | exact @GlobalTheory.ValuativeFlat.isProper_of_lift_dominating | exact GlobalTheory.ValuativeFlat.isProper_of_lift_dominating | (intros; apply GlobalTheory.ValuativeFlat.isProper_of_lift_dominating <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorIntegralModelIsProperOfCompact
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
open GlobalTheory.UPel.HT

namespace GlobalTheory.UPel.HT

lemma specMap_contravariant_comp_ringHom {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, ← Spec.map_comp]; rfl

theorem isProper_model_of_compact (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsDomain R]
    [CharZero R] [IsNoetherianRing R] (b : Base D R) (N : ℕ) (M : Model b N)
    (hc : 2 * D.a < Module.finrank ℚ D.F ∨ (D.IsDivision ∧ D.n < 2 * D.m)) : IsProper M.s := by
  haveI := M.smooth
  haveI : Smooth M.s := SmoothOfRelativeDimension.smooth (D.a * (D.n - 1)) M.s
  refine GlobalTheory.T.isProper_of_lift_completeDvr_charZero R M.X M.s M.qproj inferInstance ?_
  intro V K _ _ _ _ _ _ _ _ β x hx

  obtain ⟨oK, ⟨hK⟩⟩ := GlobalTheory.T.exists_harrisTaylorObject_pullback p D R b N M.X (Sp K) M.s x M.univ
  generalize hs : x ≫ M.s = s₀ at oK hK
  obtain rfl : s₀ = spMap ((algebraMap V K).comp β) := hs.symm.trans hx

  obtain ⟨W, L, _, _, _, _, _, _, _, _, hcomp, _, hloc, _, G, _, hmod, hab⟩ :=
    GlobalTheory.T.harrisTaylorModuliObject_potentiallyGoodReduction p D R b N V K ((algebraMap V K).comp β) oK hc

  obtain ⟨oL, ⟨hL⟩⟩ := GlobalTheory.T.exists_harrisTaylorObject_pullback p D R b N (Sp K) (Sp L) (spMap ((algebraMap V K).comp β))
    (spMap (algebraMap K L)) oK
  have hLs : spMap (algebraMap K L) ≫ spMap ((algebraMap V K).comp β) =
      spMap ((algebraMap W L).comp ((algebraMap V W).comp β)) := by
    rw [specMap_contravariant_comp_ringHom, ← RingHom.comp_assoc, ← RingHom.comp_assoc, hcomp]
  generalize hs' : spMap (algebraMap K L) ≫ spMap ((algebraMap V K).comp β) = s₁ at oL hL
  obtain rfl : s₁ = spMap ((algebraMap W L).comp ((algebraMap V W).comp β)) := hs'.symm.trans hLs
  obtain ⟨φ, hφ⟩ := GlobalTheory.T.isGrpPullback_of_group_scheme_model_base_change K W L oK.A G hmod oL.A hL.φ hL.cart
  obtain ⟨oW, ⟨hW⟩⟩ := GlobalTheory.T.harrisTaylorObject_extends_over_dvr_of_abelianModel p D R b N W L ((algebraMap V W).comp β) oL G φ hab hφ
  obtain ⟨f, ⟨hfs, ⟨hf⟩⟩, -⟩ := M.rep (Sp W) _ oW
  obtain ⟨h₁⟩ := GlobalTheory.T.harrisTaylorObjectPullback_comp p D R b N _ _ _ _ _ _ oL oW M.univ _ _ hW hf
  obtain ⟨h₂⟩ := GlobalTheory.T.harrisTaylorObjectPullback_comp p D R b N _ _ _ _ _ _ oL oK M.univ _ _ hL hK
  obtain ⟨g, -, hg⟩ := M.rep (Sp L) _ oL
  have e₁ : spMap (algebraMap W L) ≫ f = g := hg _ ⟨by rw [Category.assoc, hfs, specMap_contravariant_comp_ringHom], ⟨h₁⟩⟩
  have e₂ : spMap (algebraMap K L) ≫ x = g := hg _ ⟨by rw [Category.assoc, hx, hLs], ⟨h₂⟩⟩
  exact ⟨W, L, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, hcomp, hloc, f, e₂.trans e₁.symm⟩

end GlobalTheory.UPel.HT
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorIntegralModelIsProperOfCompactStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
open GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylor_integralModel_isProper_of_compact : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsDomain R] [CharZero R] [IsNoetherianRing R] (b : Base D R) (N : ℕ) (M : Model b N), (2 * D.a < Module.finrank ℚ D.F ∨ (D.IsDivision ∧ D.n < 2 * D.m)) → IsProper M.s := by
  first | exact @GlobalTheory.UPel.HT.isProper_model_of_compact | exact GlobalTheory.UPel.HT.isProper_model_of_compact | (intros; apply GlobalTheory.UPel.HT.isProper_model_of_compact <;> assumption)
end
