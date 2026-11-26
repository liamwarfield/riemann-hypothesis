module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordTensorDataFactorInclusionProjectionProps
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoOfGenericNormalLocalBase
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEqAddNsmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RefinePolarisedMonomialPeriodsMonomialData
public import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExpandsAtSectionUniformised

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorOffClosedFibreDescended
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorOffClosedFibreDescended
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum.OffClosed

theorem nonempty_preimage {S : Scheme.{0}} {G X : Over S} (O : G.left.Opens) (w w' : G ⊗ X ⟶ G)
    (h : lift w' (snd G X) ≫ w = fst G X) (z : (G ⊗ X).left) (hz : (fst G X).left z ∈ O) :
    ((w.left ⁻¹ᵁ O : (G ⊗ X).left.Opens) : Set (G ⊗ X).left).Nonempty := by
  refine ⟨(lift w' (snd G X)).left z, ?_⟩
  rw [← h] at hz
  simpa using hz

theorem exists_section (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (hR : IsAdicComplete (maximalIdeal R) R) (G : Over (Sp R)) [GrpObj G] (hG : IsSemiAbelian G)
    (Ω : Type) [Field Ω] (x : Sp Ω ⟶ Sp R) (hx : closedPoint R ∉ Set.range x) (O : G.left.Opens) (pt : Sp Ω)
    (hO : ∃ g ∈ O, G.hom g = x pt) {J : Type} [Finite J] (k : J → (Over.mk x ⟶ G)) :
    ∃ a : 𝟙_ (Over (Sp R)) ⟶ G, ∀ i, (k i * (toUnit (Over.mk x) ≫ a)).left pt ∈ O ∧
      (k i * (toUnit (Over.mk x) ≫ a)⁻¹).left pt ∈ O := by
  have hirr : IrreducibleSpace (pullback G.hom x : Scheme.{0}) := GlobalTheory.T.irreducibleSpace_fibre_semiAbelian_fieldPoint _ G hG Ω x
  obtain ⟨g, hg, hgx⟩ := hO
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := G.hom) (g := x) g pt hgx
  let X : Over (Sp R) := Over.mk x
  have hz' : (fst G X).left z ∈ O := by
    change pullback.fst G.hom x z ∈ O
    rw [hz]; exact hg
  let w : J × Bool → (G ⊗ X ⟶ G) := fun j =>
    match j.2 with
    | true => (snd G X ≫ k j.1) * fst G X
    | false => (snd G X ≫ k j.1) * (fst G X)⁻¹
  have hw : ∀ j, (((w j).left ⁻¹ᵁ O : (G ⊗ X).left.Opens) : Set (G ⊗ X).left).Nonempty := by
    rintro ⟨i, _ | _⟩
    · refine nonempty_preimage O _ ((fst G X)⁻¹ * (snd G X ≫ k i)) ?_ z hz'
      simp only [w, MonObj.comp_mul, GrpObj.comp_inv, lift_snd_assoc, lift_fst]
      group
    · refine nonempty_preimage O _ ((snd G X ≫ k i)⁻¹ * fst G X) ?_ z hz'
      simp only [w, MonObj.comp_mul, GrpObj.comp_inv, lift_snd_assoc, lift_fst]
      group
  have hirr' : IrreducibleSpace (G ⊗ X).left := hirr
  let U : (G ⊗ X).left.Opens :=
    ⟨⋂ j, (((w j).left ⁻¹ᵁ O : (G ⊗ X).left.Opens) : Set (G ⊗ X).left),
      isOpen_iInter_of_finite fun j => ((w j).left ⁻¹ᵁ O).isOpen⟩
  have hU : (U : Set (G ⊗ X).left).Nonempty := by
    refine ⟨genericPoint (G ⊗ X).left, Set.mem_iInter.2 fun j => ?_⟩
    exact ((genericPoint_spec (G ⊗ X).left).mem_open_set_iff ((w j).left ⁻¹ᵁ O).isOpen).2 (by simpa using hw j)
  obtain ⟨a, aΩ, ha, h1, h2, h3⟩ := GlobalTheory.T.smoothGroup_sections_dense_in_fibres R hR G hG.smooth (η[G]).left (Over.w η[G]) Ω x hx hirr U hU
  let a' : 𝟙_ (Over (Sp R)) ⟶ G := Over.homMk a ha
  let u : X ⟶ G := toUnit X ≫ a'
  have hu : (lift u (𝟙 X)).left = aΩ := by
    apply pullback.hom_ext
    · refine Eq.trans ?_ h1.symm
      have : (lift u (𝟙 X)).left ≫ (fst G X).left = u.left := by rw [← Over.comp_left, lift_fst]
      exact this
    · refine Eq.trans ?_ h2.symm
      have : (lift u (𝟙 X)).left ≫ (snd G X).left = (𝟙 X : X ⟶ X).left := by rw [← Over.comp_left, lift_snd]
      exact this
  have key : ∀ j, (lift u (𝟙 X) ≫ w j).left pt ∈ O := by
    intro j
    have := Set.mem_iInter.1 (h3 ⟨pt, rfl⟩) j
    rw [← hu] at this
    exact this
  refine ⟨a', fun i => ⟨?_, ?_⟩⟩
  · have := key (i, true)
    simp only [w, MonObj.comp_mul, lift_snd_assoc, lift_fst, Category.id_comp] at this
    exact this
  · have := key (i, false)
    simp only [w, MonObj.comp_mul, GrpObj.comp_inv, lift_snd_assoc, lift_fst, Category.id_comp] at this
    exact this

theorem exists_ten (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (hR : IsAdicComplete (maximalIdeal R) R) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G)
    (O : G.left.Opens) (hO : ∃ g ∈ O, G.hom g = closedPoint R) (y : G.left) (hy : G.hom y ≠ closedPoint R) :
    ∃ a b c : G ⟶ G, ∀ f ∈ cubeTen (𝟙 G) a b c, f.left y ∈ O := by
  have := hG.smooth
  let Ω : Type := G.left.residueField y
  let yy : Sp Ω ⟶ G.left := G.left.fromSpecResidueField y
  let x : Sp Ω ⟶ Sp R := yy ≫ G.hom
  have hyy : ∀ p, yy p = y := fun p => by
    have : yy p ∈ Set.range (G.left.fromSpecResidueField y) := ⟨p, rfl⟩
    rw [Scheme.range_fromSpecResidueField] at this
    exact this
  have hx : ∀ p, x p = G.hom y := fun p => congrArg G.hom (hyy p)
  have hx' : closedPoint R ∉ Set.range x := by
    rintro ⟨p, hp⟩
    exact hy ((hx p).symm.trans hp)
  let pt : Sp Ω := closedPoint Ω
  have hO' : ∃ g ∈ O, G.hom g = x pt := by
    obtain ⟨g, hg, hgc⟩ := hO
    have hs : x pt ⤳ G.hom g := by rw [hgc]; exact specializes_closedPoint _
    obtain ⟨g', h1, h2⟩ := Flat.generalizingMap G.hom hs
    exact ⟨g', h1.mem_open O.isOpen hg, h2⟩
  let X : Over (Sp R) := Over.mk x
  let yh : X ⟶ G := Over.homMk yy rfl
  obtain ⟨a, ha⟩ := exists_section R hR G hG Ω x hx' O pt hO' ![(1 : Over.mk x ⟶ G), yh]
  obtain ⟨b, hb⟩ := exists_section R hR G hG Ω x hx' O pt hO' ![(1 : Over.mk x ⟶ G), yh]
  obtain ⟨c, hc⟩ := exists_section R hR G hG Ω x hx' O pt hO'
    ![(1 : Over.mk x ⟶ G), yh, (toUnit X ≫ b)⁻¹, yh * (toUnit X ≫ b)⁻¹]
  refine ⟨toUnit G ≫ a, toUnit G ≫ b, toUnit G ≫ c, fun f hf => ?_⟩
  have e : f.left y = (yh ≫ f).left pt := (congrArg f.left (hyy pt)).symm
  rw [e]
  have ht : ∀ d : 𝟙_ (Over (Sp R)) ⟶ G, yh ≫ toUnit G ≫ d = toUnit X ≫ d := fun d => by
    rw [← Category.assoc, comp_toUnit]
  have a0 := ha 0
  have a1 := ha 1
  have b0 := hb 0
  have b1 := hb 1
  have c0 := hc 0
  have c1 := hc 1
  have c2 := hc 2
  have c3 := hc 3
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at a0 a1 b0 b1 c0 c1 c2 c3
  rw [_root_.one_mul, _root_.one_mul] at a0 b0 c0
  simp only [cubeTen, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [MonObj.comp_mul, GrpObj.comp_inv, Category.comp_id, ht, mul_inv, ← _root_.mul_assoc]
  exacts [a1.1, a1.2, a0.1, a0.2, b1.1, c1.1, c3.2, b0.1, c0.1, c2.2]

theorem exists_gen_off_closed : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (M : Modif R) (G' : Over M.S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (P' : GlobalTheory.UU.CP G') (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback G' G M.π β → ∀ (θ : P'.L.L.Sec) (O : G.left.Opens), (∃ g ∈ O, G.hom g = closedPoint R) → (∀ g : G'.left, β g ∈ O → G.hom (β g) = closedPoint R → ∃ i, g ∈ G'.left.basicOpen (θ.f i)) → ∀ y : G.left, G.hom y ≠ closedPoint R → ∃ V : G.left.Opens, y ∈ V ∧ ∃ t : LB.Gen (P'.L.L.pull (β ⁻¹ᵁ V).ι), t.IsGen := by
  intro R _ _ _ hR M G' _ _ _ P' G _ _ β hG hpb θ O hO hθ y hy
  have := hR.1
  have hβ : IsProper β := MorphismProperty.of_isPullback (P := @IsProper) hpb.1.flip M.proper
  let O' : G.left.Opens := ⟨farSet β θ, isOpen_farSet β β.isClosedMap θ⟩
  have hO' : ∃ g ∈ O', G.hom g = closedPoint R := by
    obtain ⟨g, hg, hgc⟩ := hO
    refine ⟨g, fun g' hg' => ?_, hgc⟩
    subst hg'
    exact TopologicalSpace.Opens.mem_iSup.2 (hθ g' hg hgc)
  obtain ⟨a, b, c, h⟩ := exists_ten R hR.2.2.2 G hG O' hO' y hy
  let V : G.left.Opens := ⟨⋂ f ∈ {f | f ∈ cubeTen (𝟙 G) a b c}, ((f.left ⁻¹ᵁ O' : G.left.Opens) : Set G.left),
    (List.finite_toSet _).isOpen_biInter fun f _ => (f.left ⁻¹ᵁ O').isOpen⟩
  refine ⟨V, Set.mem_iInter₂.2 h, ?_⟩
  obtain ⟨hl, hm⟩ := GlobalTheory.T.grpPullback_points_lift_and_compat_mul_inv _ _ M.π G G' β hpb G' G β hpb.1.w
  obtain ⟨a', ha⟩ := hl a
  obtain ⟨b', hb⟩ := hl b
  obtain ⟨c', hc⟩ := hl c
  have h1 : (𝟙 G' : G' ⟶ G').left ≫ β = β ≫ (𝟙 G : G ⟶ G).left := by simp
  have mul := fun u v u' v' hu hv => (hm u v u' v' hu hv).1
  have inv := fun u u' hu => (hm u u u' u' hu hu).2
  have hten : ∀ f' ∈ cubeTen (𝟙 G') a' b' c', ∃ f ∈ cubeTen (𝟙 G) a b c, f'.left ≫ β = β ≫ f.left := by
    intro f' hf
    simp only [cubeTen, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, by simp [cubeTen], mul _ _ _ _ h1 ha⟩
    · exact ⟨_, by simp [cubeTen], mul _ _ _ _ h1 (inv _ _ ha)⟩
    · exact ⟨_, by simp [cubeTen], ha⟩
    · exact ⟨_, by simp [cubeTen], inv _ _ ha⟩
    · exact ⟨_, by simp [cubeTen], mul _ _ _ _ h1 hb⟩
    · exact ⟨_, by simp [cubeTen], mul _ _ _ _ h1 hc⟩
    · exact ⟨_, by simp [cubeTen], mul _ _ _ _ h1 (inv _ _ (mul _ _ _ _ hb hc))⟩
    · exact ⟨_, by simp [cubeTen], hb⟩
    · exact ⟨_, by simp [cubeTen], hc⟩
    · exact ⟨_, by simp [cubeTen], inv _ _ (mul _ _ _ _ hb hc)⟩
  have := GlobalTheory.T.exists_generator_of_theoremOfCube_ten_points M.S G' P' θ G' (𝟙 G') a' b' c' (β ⁻¹ᵁ V) (by
    intro f' hf' g hg
    obtain ⟨f, hf, e⟩ := hten f' hf'
    have h2 : f.left (β g) ∈ farSet β θ := Set.mem_iInter₂.1 hg f hf
    refine h2 (f'.left g) ?_
    rw [← Scheme.Hom.comp_apply, e, Scheme.Hom.comp_apply])
  have e : (β ⁻¹ᵁ V).ι ≫ (𝟙 G' : G' ⟶ G').left = (β ⁻¹ᵁ V).ι := by simp
  rw [e] at this
  exact this

end GlobalTheory.Mum.OffClosed
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorOffClosedFibreDescendedStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_generator_off_closedFibre_descended : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (M : Modif R) (G' : Over M.S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (P' : GlobalTheory.UU.CP G') (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback G' G M.π β → ∀ (θ : P'.L.L.Sec) (O : G.left.Opens), (∃ g ∈ O, G.hom g = closedPoint R) → (∀ g : G'.left, β g ∈ O → G.hom (β g) = closedPoint R → ∃ i, g ∈ G'.left.basicOpen (θ.f i)) → ∀ y : G.left, G.hom y ≠ closedPoint R → ∃ V : G.left.Opens, y ∈ V ∧ ∃ t : LB.Gen (P'.L.L.pull (β ⁻¹ᵁ V).ι), t.IsGen := by
  first | exact @GlobalTheory.Mum.OffClosed.exists_gen_off_closed | exact GlobalTheory.Mum.OffClosed.exists_gen_off_closed | (intros; apply GlobalTheory.Mum.OffClosed.exists_gen_off_closed <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTraitPeriodFormValuationSumRefinedChart
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTraitPeriodFormValuationSumRefinedChart
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.L2.Pj

noncomputable section

namespace GlobalTheory.Poinc.ChartTraitForm


open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT GlobalTheory.ArcPull GlobalTheory.PullLinear in
theorem exists_pull {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {I : Ideal R} {I' : Ideal R'}
    (hR : AdmBase R I) (hR' : AdmBase R' I') (g : R →+* R') (hg : Function.Injective g) (hI : I.map g ≤ I')
    {D : DegData R I} {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)}
    [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G) (U : Unif I D A G) :
    ∃ (D' : DegData R' I') (_ : IsPullDeg g D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R')))
      (_ : Unif I' D' A' ((Over.pullback (spMap g)).obj G)) (gA : A'.A.left ⟶ A.A.left),
      IsGrpPullback A'.A A.A (spMap (fracMap hg)) gA ∧ LBIso A'.L (A.L.pull gA) := by
  have hP : PolBaseChangeSt := polBaseChange_holds
  have hU : UnifBaseChangeSt := GlobalTheory.UnifPullGuards.unifBaseChange_holds
  have hψ : PsiOnExistsSt := psiOnExists
  have sq : spMap (fracMap hg) ≫ jK R = jK R' ≫ spMap g := (fracMap_sq hg).symm.trans (Category.id_comp _)
  obtain ⟨A', gA, pA, dA, mA, tA⟩ := hP _ _ (spMap (fracMap hg)) A
  have gpA : IsGrpPullback A'.A A.A (spMap (fracMap hg)) gA := ⟨pA, fun T x y x₀ y₀ hx hy => by
    have e₁ : x₀ = Out.toBase pA.w x := Over.OverMorphism.ext hx
    have e₂ : y₀ = Out.toBase pA.w y := Over.OverMorphism.ext hy
    rw [e₁, e₂, ← mA]; rfl⟩
  have gpG := ThetaBaseChange.grp_generic U.toUnifPre
  have gp' : IsGrpPullback ((Over.pullback (jK R')).obj ((Over.pullback (specOf g)).obj G)) G (spMap (fracMap hg) ≫ jK R)
      (pullback.fst ((Over.pullback (specOf g)).obj G).hom (jK R') ≫ pullback.fst G.hom (spMap g)) :=
    ((isGrpPullback_pullback ((Over.pullback (specOf g)).obj G) (jK R')).comp
      (isGrpPullback_pullback G (spMap g))).congr sq.symm rfl
  obtain ⟨eA, mE, heA⟩ := grpPullback_iso gp' (gpA.comp gpG)
  have hgi : U.gen.inv.left ≫ U.gen.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  have hbc : (Iso.refl ((Over.pullback (specOf g)).obj G)).hom.left ≫ pullback.fst G.hom (specOf g) =
      pullback.fst G.hom (spMap g) := Category.id_comp _
  have wA : LBIso (A'.L.pull eA.hom.left) (U.LG.L.pull (pullback.fst ((Over.pullback (specOf g)).obj G).hom (jK R') ≫
      (Iso.refl ((Over.pullback (specOf g)).obj G)).hom.left ≫ pullback.fst G.hom (specOf g))) := by
    refine LBIso.trans (pull_isLB A'.isLB _) (pull_isLB (pull_isLB A.isLB gA) eA.hom.left)
      (pull_isLB U.LG.isLB _)
      ((LBIso.symm tA).chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull A'.L _ _ rfl)
        (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull (A.L.pull gA) _ _ rfl)) ?_
    refine LBIso.chartPull (h := eA.hom.left ≫ gA ≫ U.gen.inv.left)
      (chartPullLinComb A.L gA (fun _ => eA.hom.left) (fun _ => U.gen.hom.left) _ _ fun _ => ?_)
      (chartPullSame U.LG.L _ (fun _ => pullback.fst G.hom (jK R)) _ _ fun _ => ?_) U.ext
    · rw [Category.assoc, Category.assoc, hgi, Category.comp_id]
    · rw [hbc, ← heA]; simp only [Category.assoc]
  have he : eSec ((Over.pullback (specOf g)).obj G) ≫ (Iso.refl ((Over.pullback (specOf g)).obj G)).hom.left ≫
      pullback.fst G.hom (specOf g) = specOf g ≫ eSec G := by
    rw [hbc]; exact (cubeMapOf (isGrpPullback_pullback G (spMap g))).e_comm
  have hr : (rigPullOf (G := G) (G' := (Over.pullback (specOf g)).obj G) _ (specOf g) he U.LG.L U.LG.rig).IsGen :=
    LBxP.isGen_pullAlong U.LG.L _ (specOf g) (fun _ : PUnit => eSec G) (fun _ => 1)
      (fun _ => eSec ((Over.pullback (specOf g)).obj G)) (fun _ => he) U.LG.rig U.LG.rigGen
  let L' : RigLB ((Over.pullback (specOf g)).obj G) :=
    ⟨U.LG.L.pull ((Iso.refl ((Over.pullback (specOf g)).obj G)).hom.left ≫ pullback.fst G.hom (specOf g)),
      rigPullOf (G := G) (G' := (Over.pullback (specOf g)).obj G) _ (specOf g) he U.LG.L U.LG.rig,
      pull_isLB U.LG.isLB _, hr⟩
  obtain ⟨Wo, hWo, hψ⟩ := hψ R I hR D
  have hgen : (specOf g).base (genericPoint (Spec (CommRingCat.of R'))) ∈ Wo := by
    have : (specOf g).base (genericPoint (Spec (CommRingCat.of R'))) = genericPoint (Spec (CommRingCat.of R)) := by
      rw [genericPoint_eq_bot_of_affine, genericPoint_eq_bot_of_affine]
      exact PrimeSpectrum.ext (Ideal.comap_bot_of_injective g hg)
    rw [this]; exact hWo
  have mR : IsMonHom (Iso.refl ((Over.pullback (specOf g)).obj G)).hom := by show IsMonHom (𝟙 _); infer_instance
  obtain ⟨D', hD, U', -⟩ := hU R R' I I' hR hR' g hI D A G hG U Wo hψ hgen ((Over.pullback (specOf g)).obj G)
    (Iso.refl _) mR A' dA eA mE wA L' (idIso _) he (idIso_isGen L'.isLB) (fun p => hr p.1 p.2)
  exact ⟨D', hD, A', U', gA, gpA, LBIso.symm tA⟩

theorem isMonomial_pull {R W : Type} [CommRing R] [IsDomain R] [CommRing W] [IsDomain W] [IsLocalRing W] {κ : R →+* W}
    {D : DegPre R} {D' : DegPre W} (hD : IsPullDeg κ D D') {m : ℕ} {r : Fin m → R}
    {B : Fin m → LinearMap.BilinForm ℤ D.X} (h : IsMonomial D r B) {ϖ : W} {a : Fin m → ℕ}
    (ha : ∀ k, Associated (κ (r k)) (ϖ ^ a k)) (β : LinearMap.BilinForm ℤ D'.X)
    (hβ : ∀ y, β y y = ∑ k, (a k : ℤ) * B k (hD.xe y) (hD.xe y)) : IsMonomial D' ![ϖ] ![β] := by
  intro y
  obtain ⟨u, n, hn, hc⟩ := h (hD.xe y)
  obtain ⟨u', hc'⟩ := GlobalTheory.PelCoordPull.psiCoord_pull hD y _ hc
  have h₁ : Associated (ϖ ^ ∑ k, a k * n k) (u' * κ (u * ∏ i, r i ^ n i)) := by
    refine Associated.symm ((associated_unit_mul_left _ _ u'.isUnit).trans ?_)
    rw [map_mul, map_prod, ← Finset.prod_pow_eq_pow_sum]
    refine (associated_unit_mul_left _ _ (u.isUnit.map κ)).trans (Associated.prod _ _ _ fun i _ => ?_)
    rw [map_pow, pow_mul]
    exact (ha i).pow_pow
  obtain ⟨v, hv⟩ := h₁
  refine ⟨v, ![∑ k, a k * n k], fun i => ?_, ?_⟩
  · fin_cases i
    simp only [Fin.zero_eta, Matrix.cons_val_zero, hβ, hn]
    push_cast
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  · rw [Fin.prod_univ_one, Matrix.cons_val_zero, Matrix.cons_val_zero, mul_comm, hv]
    exact hc'

theorem exists_trait : ∀ {o : Type} [CommRing o] {ζ : o} {g n : ℕ} (F : SFam g n ζ) (S : Scheme.{0}) (j : F.X ⟶ S)
    (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (Q : Data V) (ξ : Sp V ⟶ S), UnifOver F j ξ Q →
    ∀ (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ Q.X) (R' : Type) [CommRing R'] [IsDomain R']
      [IsLocalRing R'] (ρ : V →+* R') (r : Fin m → R') (D : DegData R' (maximalIdeal R')) (e : D.toPre.X ≃+ Q.X),
      IsCN R' → Function.Injective ρ → ρ.Finite → IsLocalHom ρ → (∀ k, r k ^ 2 = ρ (t k)) → (∀ k, t k ≠ 0) →
      (∀ k a b, δ k a b = δ k b a) → Refines Q ρ D.toPre e →
      IsMonomial D.toPre r (fun k => (2 : ℤ) • pull e.toIntLinearEquiv.toLinearMap (δ k)) →
    ∀ (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W], IsAdicComplete (maximalIdeal W) W →
    ∀ κ : R' →+* W, Function.Injective κ → IsLocalHom κ →
      ∃ (T : Trait F) (σ : W →+* T.V) (c : Fin m → ℕ) (e' : T.D.toPre.X ≃+ Q.X), Function.Bijective σ ∧
        jK T.V ≫ spMap σ ≫ spMap κ ≫ spMap ρ ≫ ξ = T.y ≫ j ∧ (∀ k, Associated (σ (κ (ρ (t k)))) (T.ϖ ^ c k)) ∧
        ∀ a b, T.β a b = ∑ k, (c k : ℤ) * δ k (e' a) (e' b) := by
  intro o _ ζ g n F S j V _ _ _ Q ξ hUO m t δ R' _ _ _ ρ r D e hR' hρ hρf _ hr ht hδ hRef hmon W _ _ _ hW κ hκ hκl
  obtain ⟨G', _, _, A, U, y', α, α₂, hG, hy, hα, hsq, hL⟩ := hUO.2 R' ρ hR' hρ hρf D e hRef
  have h0 : CharZero R' := hR'.2.2.2
  have hW0 : CharZero W := charZero_of_injective_ringHom hκ
  obtain ⟨D', hD, A', U', gA, gpA, tA⟩ := exists_pull (I := maximalIdeal R') (I' := maximalIdeal W)
    ⟨hR'.1, inferInstance, hR'.2.1, hR'.2.2.1⟩ ⟨inferInstance, inferInstance, inferInstance, hW⟩ κ hκ
    (Ideal.map_le_iff_le_comap.2 fun a ha => map_nonunit κ a ha) hG U
  obtain ⟨β₂, hβ₂, hΛ⟩ := GlobalTheory.Mum.lbIso_lam_pull_of_isGrpPullback _ _ _ A.A A'.A gA gpA
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible W
  have hr0 : ∀ k, κ (r k) ≠ 0 := fun k h => ht k (hρ (hκ (by rw [← hr, map_pow, h]; simp)))
  choose a u hu using fun k => IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (hr0 k) hϖ
  have ha : ∀ k, Associated (κ (r k)) (ϖ ^ a k) := fun k => by
    rw [hu]; exact associated_unit_mul_left _ _ (u k).isUnit
  let e' : D'.toPre.X ≃+ Q.X := hD.xe.trans e
  let β : LinearMap.BilinForm ℤ D'.toPre.X := ∑ k, ((2 * a k : ℕ) : ℤ) • pull e'.toIntLinearEquiv.toLinearMap (δ k)
  have hβ : ∀ x y, β x y = ∑ k, ((2 * a k : ℕ) : ℤ) * δ k (e' x) (e' y) := fun x y => by
    simp only [β, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    rfl
  have sq : spMap (GlobalTheory.ArcPull.fracMap hκ) ≫ jK R' = jK W ≫ spMap κ :=
    (GlobalTheory.ArcPull.fracMap_sq hκ).symm.trans (Category.id_comp _)
  let T : Trait F :=
    { V := W, complete := hW, ϖ := ϖ, irr := hϖ, y := spMap (GlobalTheory.ArcPull.fracMap hκ) ≫ y'
      G := (Over.pullback (spMap κ)).obj G', semi := IsSemiAbelian.pullback _ G' hG, D := D', A := A', U := U'
      α := gA ≫ α, α₂ := β₂ ≫ α₂, cart := gpA.comp hα
      sq := ⟨by rw [Category.assoc, hsq.1, ← Category.assoc, hβ₂.1, Category.assoc],
        by rw [Category.assoc, hsq.2, ← Category.assoc, hβ₂.2, Category.assoc]⟩
      lb := hΛ A.L A'.L _ F.univ.P α₂ A.isLB A'.isLB F.univ.isLB tA hL
      β := β
      symm := fun x y => by
        rw [hβ, hβ]
        exact Finset.sum_congr rfl fun k _ => by rw [hδ]
      mono := isMonomial_pull hD hmon ha β fun y => by
        rw [hβ]
        refine Finset.sum_congr rfl fun k _ => ?_
        have : ((2 : ℤ) • pull e.toIntLinearEquiv.toLinearMap (δ k)) (hD.xe y) (hD.xe y) = 2 * δ k (e' y) (e' y) := rfl
        rw [this]
        push_cast
        ring }
  refine ⟨T, RingHom.id W, fun k => 2 * a k, e', Function.bijective_id, ?_, fun k => ?_, hβ⟩
  · show jK W ≫ spMap (RingHom.id W) ≫ spMap κ ≫ spMap ρ ≫ ξ = (spMap (GlobalTheory.ArcPull.fracMap hκ) ≫ y') ≫ j
    have : spMap (RingHom.id W) = 𝟙 _ := Spec.map_id _
    rw [this, Category.id_comp, Category.assoc, hy, ← Category.assoc (spMap (GlobalTheory.ArcPull.fracMap hκ)), sq, Category.assoc]
  · show Associated (κ (ρ (t k))) (ϖ ^ (2 * a k))
    rw [← hr, map_pow, mul_comm, pow_mul]
    exact (ha k).pow_pow

end GlobalTheory.Poinc.ChartTraitForm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTraitPeriodFormValuationSumRefinedChartStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_trait_period_form_valuation_sum_refined_chart : ∀ {o : Type} [CommRing o] {ζ : o} {g n : ℕ} (F : SFam g n ζ) (S : Scheme.{0}) (j : F.X ⟶ S)
    (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (Q : Data V) (ξ : Sp V ⟶ S), UnifOver F j ξ Q →
    ∀ (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ Q.X) (R' : Type) [CommRing R'] [IsDomain R']
      [IsLocalRing R'] (ρ : V →+* R') (r : Fin m → R') (D : DegData R' (maximalIdeal R')) (e : D.toPre.X ≃+ Q.X),
      IsCN R' → Function.Injective ρ → ρ.Finite → IsLocalHom ρ → (∀ k, r k ^ 2 = ρ (t k)) → (∀ k, t k ≠ 0) →
      (∀ k a b, δ k a b = δ k b a) → Refines Q ρ D.toPre e →
      IsMonomial D.toPre r (fun k => (2 : ℤ) • pull e.toIntLinearEquiv.toLinearMap (δ k)) →
    ∀ (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W], IsAdicComplete (maximalIdeal W) W →
    ∀ κ : R' →+* W, Function.Injective κ → IsLocalHom κ →
      ∃ (T : Trait F) (σ : W →+* T.V) (c : Fin m → ℕ) (e' : T.D.toPre.X ≃+ Q.X), Function.Bijective σ ∧
        jK T.V ≫ spMap σ ≫ spMap κ ≫ spMap ρ ≫ ξ = T.y ≫ j ∧ (∀ k, Associated (σ (κ (ρ (t k)))) (T.ϖ ^ c k)) ∧
        ∀ a b, T.β a b = ∑ k, (c k : ℤ) * δ k (e' a) (e' b) := by
  first | exact @GlobalTheory.Poinc.ChartTraitForm.exists_trait | exact GlobalTheory.Poinc.ChartTraitForm.exists_trait | (intros; apply GlobalTheory.Poinc.ChartTraitForm.exists_trait <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsProjectiveSpaceMapOfModelHasDiv
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsProjectiveSpaceMapOfModelHasDiv
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UMin.CrdMap

open GlobalTheory.ProjSpace GlobalTheory.Cartier GlobalTheory.QCoh.Qcqs

theorem pCrd_pt {o A : Type} [CommRing o] [CommRing A] {n : ℕ} (c : o →+* A) (v : Fin (n + 1) → A)
    (hv : Ideal.span (Set.range v) = ⊤) : PCrd (pt c v hv) v := by
  have hφ := toProj_coord o n
  have hstr : pt c v hv ≫ PSpace.str o n = spMap c := by
    rw [pt, PSpace.str, ProjPoint.ofHom_toSpecZero_assoc, ← Spec.map_comp]
    congr 1
    ext1
    exact RingHom.ext fun r => MvPolynomial.eval₂Hom_C c v r
  have h1 := (ProjCoord.secCoord_iff (Equiv.refl _) (toProj (PSpace.str o n) (coord o n) (iSup_nonzeroLocus_coord o n))
    c (pt c v hv) (by rw [hφ, Category.comp_id]; exact hstr) v).2 ⟨by simpa using hv, by rw [hφ, Category.comp_id]; rfl⟩
  exact (FibreEmbed.secCoord_iff_of_secMaps (LB.isLB_pull (O1_isLB o n) _) (O1_isLB o n)
    (fun j => secMaps_toProjIso _ _ _ j) (iSup_nonzeroLocus_secPull (iSup_nonzeroLocus_coord o n) _)
    (iSup_nonzeroLocus_coord o n)).1 h1

section Map

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) {n : ℕ} (c : Fin (n + 1) → Ω)

def dOpen (i : Fin (n + 1)) : M.Z.Opens := ⟨{z | M.Div c i z}, M.isOpen_setOf_div c i⟩

theorem subsingleton_of_not_nonempty {X : Scheme.{0}} {V : X.Opens} (hV : ¬ (V : Set X).Nonempty) :
    Subsingleton Γ(X, V) := by
  have : V = ⊥ := SetLike.coe_injective (Set.not_nonempty_iff_eq_empty.1 hV)
  subst this
  infer_instance


variable {M} in
theorem eq_of_valF {V : M.Z.Opens} {f g : Γ(M.Z, V)}
    (h : ∀ hV : (V : Set M.Z).Nonempty, valF M.pt V f = valF M.pt V g) : f = g := by
  by_cases hV : (V : Set M.Z).Nonempty
  · exact M.valF_injective hV (h hV)
  · have := subsingleton_of_not_nonempty hV
    exact Subsingleton.elim _ _


open Classical in
def fnOf (V : M.Z.Opens) (x : Ω) : Γ(M.Z, V) :=
  if h : ∃ f : Γ(M.Z, V), valF M.pt V f = x then h.choose else 0


variable {M} in
theorem valF_fnOf {V : M.Z.Opens} {x : Ω} (h : ∃ f : Γ(M.Z, V), valF M.pt V f = x) :
    valF M.pt V (fnOf M V x) = x := by
  rw [fnOf, dite_eq_left h]
  exact h.choose_spec

def ratioFn (i j : Fin (n + 1)) : Γ(M.Z, dOpen M c i) := fnOf M (dOpen M c i) (c j / c i)

variable {M c}

theorem valF_ratioFn {i j : Fin (n + 1)} {V : M.Z.Opens} (hV : V ≤ dOpen M c i) (hne : (V : Set M.Z).Nonempty) :
    valF M.pt V (resG M.Z hV (ratioFn M c i j)) = c j / c i := by
  have hne' : ((dOpen M c i : M.Z.Opens) : Set M.Z).Nonempty := hne.mono hV
  rw [M.valF_resG hV hne, ratioFn, valF_fnOf]
  exact (RatModel.mem_ringOn_iff_exists hne').1 (RatModel.mem_ringOn.2 fun z hz => hz.2 j)

theorem valF_one' {V : M.Z.Opens} (hne : (V : Set M.Z).Nonempty) : valF M.pt V 1 = 1 := by
  rw [← M.res_apply V hne, map_one]

theorem valF_mul' {V : M.Z.Opens} (hne : (V : Set M.Z).Nonempty) (f g : Γ(M.Z, V)) :
    valF M.pt V (f * g) = valF M.pt V f * valF M.pt V g := by
  rw [← M.res_apply V hne, map_mul, M.res_apply, M.res_apply]

theorem isCoordFamily_ratioFn (hd : M.HasDiv c) : IsCoordFamily (dOpen M c) (ratioFn M c) := by
  refine { cover := top_le_iff.1 fun z _ => TopologicalSpace.Opens.mem_iSup.2 (hd z)
           self := ?_, mul := ?_, basicOpen_le := ?_ }
  · intro i
    refine eq_of_valF fun hne => ?_
    obtain ⟨z, hz⟩ := hne
    have := valF_ratioFn (j := i) (le_refl (dOpen M c i)) ⟨z, hz⟩
    rw [resG_self] at this
    rw [this, valF_one' ⟨z, hz⟩, div_self hz.1]
  · intro i j k
    refine eq_of_valF fun hne => ?_
    obtain ⟨z, hz⟩ := hne
    rw [valF_mul' ⟨z, hz⟩, valF_ratioFn _ ⟨z, hz⟩, valF_ratioFn _ ⟨z, hz⟩, valF_ratioFn _ ⟨z, hz⟩]
    have h1 := hz.1.1
    have h2 := hz.2.1
    field_simp
  · intro i j z hz
    have hzi : z ∈ dOpen M c i := M.Z.basicOpen_le _ hz
    have hu := (RatModel.isUnit_valF_iff hzi (ratioFn M c i j)).2 hz
    have e : valF M.pt (dOpen M c i) (ratioFn M c i j) = c j / c i := by
      have := valF_ratioFn (j := j) (le_refl (dOpen M c i)) ⟨z, hzi⟩
      rwa [resG_self] at this
    have e' : (⟨valF M.pt (dOpen M c i) (ratioFn M c i j), RatModel.valF_mem_O hzi _⟩ : M.O z) =
        ⟨c j / c i, (show M.Div c i z from hzi).2 j⟩ := Subtype.ext e
    rw [e'] at hu
    exact ((show M.Div c i z from hzi).div_iff_isUnit j).2 hu

end Map

section Main

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M : RatModel o Ω} {n : ℕ} {c : Fin (n + 1) → Ω}

theorem appLE_eq_fnOn {X : Scheme.{0}} (x : Sp Ω ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)) :
    (x.appLE U ⊤ h).hom f = fnOn ⊤ (valF x U f) := by
  rw [valF, dite_eq_left h, fnOn, RingHom.comp_apply, resG_self]
  simp

theorem pt_comp_toHom (hd : M.HasDiv c) (hc : Ideal.span (Set.range c) = ⊤) :
    M.pt ≫ (isCoordFamily_ratioFn hd).toHom M.s = pt (algebraMap o Ω) c hc := by
  let _ := MvPolynomial.gradedAlgebra (σ := Fin (n + 1)) (R := o)
  set H := isCoordFamily_ratioFn hd
  obtain ⟨i, hi⟩ := hd (genericPoint M.Z)
  have hpt : ⊤ ≤ M.pt ⁻¹ᵁ dOpen M c i := M.top_le_preimage_pt ⟨_, RatModel.div_genericPoint hi.1⟩
  have h₁ : ⊤ ≤ (M.pt ≫ H.toHom M.s) ⁻¹ᵁ chart o n i :=
    GlobalTheory.Points.le_preimage_comp M.pt _ (H.le_toHom_preimage M.s i) hpt
  have hchart : pt (algebraMap o Ω) c hc ⁻¹ᵁ chart o n i = spOpen (c i) := by
    rw [pt, chart, ProjPoint.ofHom_preimage_basicOpen _ _ _ one_pos (X_mem o n i),
      MvPolynomial.eval₂Hom_X']
    rfl
  have h₂ : ⊤ ≤ pt (algebraMap o Ω) c hc ⁻¹ᵁ chart o n i := by
    rw [hchart]
    exact fun y _ => mem_spOpen.2 fun hm => y.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hm (Ne.isUnit hi.1))
  have hstr : pt (algebraMap o Ω) c hc ≫ PSpace.str o n = spMap (algebraMap o Ω) := by
    rw [pt, PSpace.str, ProjPoint.ofHom_toSpecZero_assoc, ← Spec.map_comp]
    congr 1
    ext1
    exact RingHom.ext fun r => MvPolynomial.eval₂Hom_C (algebraMap o Ω) c r
  refine hom_ext (by rw [Category.assoc, H.toHom_str, M.pt_s, hstr]) fun _ => ⟨⊤, trivial, i, h₁, h₂, fun j => ?_⟩
  have hratio : pullRatio (pt (algebraMap o Ω) c hc) ⊤ i h₂ j * fnOn ⊤ (c i) = fnOn ⊤ (c j) := by
    let β := algebraMap o Ω
    have hunit : IsUnit (MvPolynomial.eval₂Hom β c (MvPolynomial.X i)) := by
      rw [MvPolynomial.eval₂Hom_X']
      exact Ne.isUnit hi.1
    have haway : pt β c hc =
        spMap (ProjPoint.awayLift (grading o n) (MvPolynomial.eval₂Hom β c) (MvPolynomial.X i) hunit) ≫ _ :=
      ProjPoint.ofHom_eq_awayι _ _ _ one_pos (X_mem o n i) hunit
    have heval := ProjPoint.awayLift_mk_mul (grading o n) (MvPolynomial.eval₂Hom β c) hunit
      (X_mem o n i) 1 (MvPolynomial.X j) (X_mem o n j)
    rw [pullRatio_of_eq haway h₂ (haway ▸ h₂), pullRatio_spMap_awayι, ← map_mul]
    exact congrArg _ (by simpa only [ratioAway, MvPolynomial.eval₂Hom_X', pow_one] using heval)
  have hu : IsUnit (fnOn (⊤ : (Sp Ω).Opens) (c i)) := (Ne.isUnit hi.1).map _
  refine hu.mul_right_cancel ?_
  rw [hratio, ← appLE_pullRatio (φ := H.toHom M.s) (hi := H.le_toHom_preimage M.s i) M.pt hpt, H.pullRatio_toHom,
    appLE_eq_fnOn, ← map_mul]
  congr 1
  have := valF_ratioFn (M := M) (c := c) (j := j) (le_refl (dOpen M c i)) ⟨_, RatModel.div_genericPoint hi.1⟩
  rw [resG_self] at this
  rw [this, div_mul_cancel₀ _ hi.1]

theorem exists_map_of_hasDiv : ∀ (k Ω : Type) [CommRing k] [Field Ω] [Algebra k Ω] (M : RatModel k Ω) (n : ℕ)
    (c : Fin (n + 1) → Ω), M.HasDiv c → ∃ h : M.Z ⟶ PSpace k n, h ≫ PSpace.str k n = M.s ∧ PCrd (M.pt ≫ h) c := by
  intro k Ω _ _ _ M n c hd
  obtain ⟨i, hi⟩ := hd (genericPoint M.Z)
  have hc : Ideal.span (Set.range c) = ⊤ :=
    Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨i, rfl⟩) (Ne.isUnit hi.1)
  refine ⟨(isCoordFamily_ratioFn hd).toHom M.s, (isCoordFamily_ratioFn hd).toHom_str M.s, ?_⟩
  rw [pt_comp_toHom hd hc]
  exact pCrd_pt _ c hc

end Main

end GlobalTheory.UMin.CrdMap
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsProjectiveSpaceMapOfModelHasDivStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_projectiveSpace_map_of_model_hasDiv : ∀ (k Ω : Type) [CommRing k] [Field Ω] [Algebra k Ω] (M : RatModel k Ω) (n : ℕ) (c : Fin (n + 1) → Ω), M.HasDiv c → ∃ h : M.Z ⟶ PSpace k n, h ≫ PSpace.str k n = M.s ∧ PCrd (M.pt ≫ h) c := by
  first | exact @GlobalTheory.UMin.CrdMap.exists_map_of_hasDiv | exact GlobalTheory.UMin.CrdMap.exists_map_of_hasDiv | (intros; apply GlobalTheory.UMin.CrdMap.exists_map_of_hasDiv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveActionThickeningEndosCompletePoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveActionThickeningEndosCompletePoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.ThickEndo

variable {S S' : Scheme.{0}}

theorem homEquiv_mul' (φ : S' ⟶ S) (X : Over S') (A : Over S) [GrpObj A]
    (a b : (Over.map φ).obj X ⟶ A) :
    (Over.mapPullbackAdj φ).homEquiv X A (a * b) =
      (Over.mapPullbackAdj φ).homEquiv X A a * (Over.mapPullbackAdj φ).homEquiv X A b := by
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Hom.mul_def,
    Hom.mul_def, Functor.obj.μ_def, ← comp_lift_assoc, ← Category.assoc (lift _ _),
    Functor.Monoidal.lift_μ, CategoryTheory.Functor.map_comp]

theorem homEquiv_symm_mul' (φ : S' ⟶ S) (X : Over S') (A : Over S) [GrpObj A]
    (a b : X ⟶ (Over.pullback φ).obj A) :
    ((Over.mapPullbackAdj φ).homEquiv X A).symm (a * b) =
      ((Over.mapPullbackAdj φ).homEquiv X A).symm a * ((Over.mapPullbackAdj φ).homEquiv X A).symm b := by
  apply ((Over.mapPullbackAdj φ).homEquiv X A).injective
  rw [homEquiv_mul', Equiv.apply_symm_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

theorem homEquiv_left' (t : S' ⟶ S) {Y : Over S'} {A : Over S} (k : (Over.map t).obj Y ⟶ A) :
    ((Over.mapPullbackAdj t).homEquiv Y A k).left ≫ pullback.fst A.hom t = k.left := by
  rw [Over.mapPullbackAdj, Adjunction.mkOfHomEquiv_homEquiv]
  exact pullback.lift_fst _ _ _

theorem homEquiv_symm_left' (t : S' ⟶ S) {Y : Over S'} {A : Over S} (q : Y ⟶ (Over.pullback t).obj A) :
    (((Over.mapPullbackAdj t).homEquiv Y A).symm q).left = q.left ≫ pullback.fst A.hom t := by
  have := homEquiv_left' t (((Over.mapPullbackAdj t).homEquiv Y A).symm q)
  rw [Equiv.apply_symm_apply] at this
  exact this.symm

end GlobalTheory.ThickEndo

namespace GlobalTheory.ThickEndo

variable {R : Type} [CommRing R] (I : Ideal R) {B : Type} [CommRing B] [IsLocalRing B]

theorem le_comap_of_mem_range {φ : CommRingCat.of R ⟶ CommRingCat.of B}
    (h : Spec.map φ (closedPoint B) ∈ Set.range (thick R I 0)) :
    I ≤ (maximalIdeal B).comap φ.hom := by
  obtain ⟨y, hy⟩ := h
  intro a ha
  have h1 : a ∈ ((thick R I 0) y).asIdeal := by
    show Ideal.Quotient.mk (I ^ (0 + 1)) a ∈ y.asIdeal
    rw [Ideal.Quotient.eq_zero_iff_mem.2 (by simpa using ha)]
    exact zero_mem _
  rw [hy] at h1
  exact h1

def lev (φ : CommRingCat.of R ⟶ CommRingCat.of B) (hI : I ≤ (maximalIdeal B).comap φ.hom) (e : ℕ) :
    Sp (B ⧸ maximalIdeal B ^ (e + 1)) ⟶ Sp (R ⧸ I ^ (e + 1)) :=
  Spec.map (CommRingCat.ofHom (Ideal.quotientMap _ φ.hom
    ((Ideal.pow_right_mono hI (e + 1)).trans (Ideal.le_comap_pow _ _))))

variable {I}

theorem lev_thick (φ : CommRingCat.of R ⟶ CommRingCat.of B) (hI : I ≤ (maximalIdeal B).comap φ.hom) (e : ℕ) :
    lev I φ hI e ≫ thick R I e = thick B (maximalIdeal B) e ≫ Spec.map φ := by
  rw [lev, ← Spec.map_comp, ← Spec.map_comp]
  congr 1

theorem adicLevelMap_lev (φ : CommRingCat.of R ⟶ CommRingCat.of B) (hI : I ≤ (maximalIdeal B).comap φ.hom)
    (e : ℕ) : adicLevelMap (maximalIdeal B) (Nat.le_succ (e + 1)) ≫ lev I φ hI (e + 1) =
      lev I φ hI e ≫ thickTrans R I e := by
  rw [lev, lev, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext1
  exact Ideal.Quotient.ringHom_ext rfl

end GlobalTheory.ThickEndo

namespace GlobalTheory.ThickEndo

section Main

variable {R : Type} [CommRing R] {I : Ideal R} {G : Over (Sp R)} [GrpObj G] {B : Type} [CommRing B]
  [IsLocalRing B] {φ : CommRingCat.of R ⟶ CommRingCat.of B} (hI : I ≤ (maximalIdeal B).comap φ.hom)

abbrev lvl (e : ℕ) : Over (Sp (R ⧸ I ^ (e + 1))) := Over.mk (lev I φ hI e)

def incl (e : ℕ) : (Over.map (thick R I e)).obj (lvl hI e) ⟶ Over.mk (Spec.map φ) :=
  Over.homMk (thick B (maximalIdeal B) e) (lev_thick φ hI e).symm

def red (e : ℕ) (x : Over.mk (Spec.map φ) ⟶ G) : lvl hI e ⟶ thickObj R I e G :=
  (Over.mapPullbackAdj (thick R I e)).homEquiv (lvl hI e) G (incl hI e ≫ x)

theorem red_fst (e : ℕ) (x : Over.mk (Spec.map φ) ⟶ G) :
    (red hI e x).left ≫ pullback.fst G.hom (thick R I e) = thick B (maximalIdeal B) e ≫ x.left :=
  homEquiv_left' _ _

theorem red_snd (e : ℕ) (x : Over.mk (Spec.map φ) ⟶ G) :
    (red hI e x).left ≫ pullback.snd G.hom (thick R I e) = lev I φ hI e :=
  Over.w (red hI e x)

omit [GrpObj G] in
theorem thickMap_fst (e : ℕ) :
    thickMap R I e G ≫ pullback.fst G.hom (thick R I (e + 1)) = pullback.fst G.hom (thick R I e) :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

omit [GrpObj G] in
theorem thickMap_snd (e : ℕ) :
    thickMap R I e G ≫ pullback.snd G.hom (thick R I (e + 1)) =
      pullback.snd G.hom (thick R I e) ≫ thickTrans R I e :=
  pullback.lift_snd _ _ _

theorem red_succ (e : ℕ) (x : Over.mk (Spec.map φ) ⟶ G) :
    adicLevelMap (maximalIdeal B) (Nat.le_succ (e + 1)) ≫ (red hI (e + 1) x).left =
      (red hI e x).left ≫ thickMap R I e G := by
  apply pullback.hom_ext
  · rw [Category.assoc, red_fst, Category.assoc, thickMap_fst, red_fst]
    exact adicLevelMap_ι_assoc (maximalIdeal B) (Nat.le_succ (e + 1)) x.left
  · rw [Category.assoc, red_snd, Category.assoc, thickMap_snd, ← Category.assoc, red_snd, adicLevelMap_lev]

variable (b : ∀ e : ℕ, thickObj R I e G ⟶ thickObj R I e G)

def fam (x : Over.mk (Spec.map φ) ⟶ G) (e : ℕ) : Sp (B ⧸ maximalIdeal B ^ (e + 1)) ⟶ G.left :=
  (red hI e x ≫ b e).left ≫ pullback.fst G.hom (thick R I e)

variable {b}

theorem fam_adic (hb : ∀ e, thickMap R I e G ≫ (b (e + 1)).left = (b e).left ≫ thickMap R I e G)
    (x : Over.mk (Spec.map φ) ⟶ G) : IsAdicFamily (maximalIdeal B) (fam hI b x) := fun e => by
  simp only [fam, Over.comp_left, Category.assoc]
  rw [← Category.assoc (adicLevelMap _ _), red_succ, Category.assoc, ← Category.assoc (thickMap R I e G),
    hb, Category.assoc, thickMap_fst]

variable (b) in
theorem fam_over (x : Over.mk (Spec.map φ) ⟶ G) (e : ℕ) :
    fam hI b x e ≫ G.hom = adicLevelι (maximalIdeal B) (e + 1) ≫ Spec.map φ := by
  have hw : (b e).left ≫ pullback.snd G.hom (thick R I e) = pullback.snd G.hom (thick R I e) := Over.w (b e)
  simp only [fam, Over.comp_left, Category.assoc]
  rw [pullback.condition, ← Category.assoc ((b e).left), hw, ← Category.assoc, red_snd, lev_thick]

variable [IsAdicComplete (maximalIdeal B) B]

theorem exists_lim (hb : ∀ e, thickMap R I e G ≫ (b (e + 1)).left = (b e).left ≫ thickMap R I e G)
    (x : Over.mk (Spec.map φ) ⟶ G) : ∃ g : Sp B ⟶ G.left, g ≫ G.hom = Spec.map φ ∧
      ∀ e, adicLevelι (maximalIdeal B) (e + 1) ≫ g = fam hI b x e :=
  (existsUnique_over_of_isAdicFamily (Spec.map φ) G.hom (fam_adic hI hb x) (fam_over hI b x)).exists

def lim (hb : ∀ e, thickMap R I e G ≫ (b (e + 1)).left = (b e).left ≫ thickMap R I e G)
    (x : Over.mk (Spec.map φ) ⟶ G) : Over.mk (Spec.map φ) ⟶ G :=
  Over.homMk (exists_lim hI hb x).choose (exists_lim hI hb x).choose_spec.1

theorem lim_level (hb : ∀ e, thickMap R I e G ≫ (b (e + 1)).left = (b e).left ≫ thickMap R I e G)
    (x : Over.mk (Spec.map φ) ⟶ G) (e : ℕ) :
    thick B (maximalIdeal B) e ≫ (lim hI hb x).left = fam hI b x e :=
  (exists_lim hI hb x).choose_spec.2 e

theorem incl_lim (hb : ∀ e, thickMap R I e G ≫ (b (e + 1)).left = (b e).left ≫ thickMap R I e G)
    (x : Over.mk (Spec.map φ) ⟶ G) (e : ℕ) :
    incl hI e ≫ lim hI hb x = ((Over.mapPullbackAdj (thick R I e)).homEquiv _ G).symm (red hI e x ≫ b e) := by
  apply Over.OverMorphism.ext
  rw [homEquiv_symm_left', Over.comp_left]
  exact lim_level hI hb x e

theorem lim_mul (hmon : ∀ e, IsMonHom (b e))
    (hb : ∀ e, thickMap R I e G ≫ (b (e + 1)).left = (b e).left ≫ thickMap R I e G)
    (x y : Over.mk (Spec.map φ) ⟶ G) : lim hI hb (x * y) = lim hI hb x * lim hI hb y := by
  have he : ∀ e, incl hI e ≫ lim hI hb (x * y) = incl hI e ≫ (lim hI hb x * lim hI hb y) := by
    intro e
    have := hmon e
    rw [comp_mul, incl_lim, incl_lim, incl_lim, red, comp_mul, homEquiv_mul', mul_comp, homEquiv_symm_mul']
    rfl
  exact Over.OverMorphism.ext (hom_ext_of_isHausdorff (maximalIdeal B) fun e => congrArg (·.left) (he e))

end Main

end GlobalTheory.ThickEndo


open GlobalTheory.ThickEndo in
theorem GlobalTheory.exists_mul_map_points_of_thickEndo : ∀ (R : Type) [CommRing R] (I : Ideal R) (G : Over (Sp R)) [GrpObj G] (b : ∀ e : ℕ, thickObj R I e G ⟶ thickObj R I e G), (∀ e, IsMonHom (b e)) → (∀ e, thickMap R I e G ≫ (b (e + 1)).left = (b e).left ≫ thickMap R I e G) → ∀ (B : Type) [CommRing B] [IsLocalRing B] [IsAdicComplete (maximalIdeal B) B] (s : Sp B ⟶ Sp R), s (closedPoint B) ∈ Set.range (thick R I 0) → ∃ Φ : (Over.mk s ⟶ G) → (Over.mk s ⟶ G), (∀ x y, Φ (x * y) = Φ x * Φ y) ∧ ∀ (x : Over.mk s ⟶ G) (e : ℕ), ∃ r : Sp (B ⧸ maximalIdeal B ^ (e + 1)) ⟶ (thickObj R I e G).left, r ≫ pullback.fst G.hom (thick R I e) = thick B (maximalIdeal B) e ≫ x.left ∧ r ≫ (b e).left ≫ pullback.fst G.hom (thick R I e) = thick B (maximalIdeal B) e ≫ (Φ x).left := by
  intro R _ I G _ b hmon hb B _ _ _ s hs
  obtain ⟨φ, rfl⟩ := Spec.map_surjective s
  have hI := le_comap_of_mem_range I hs
  refine ⟨lim hI hb, fun x y => lim_mul hI hmon hb x y, fun x e => ⟨(red hI e x).left, red_fst hI e x, ?_⟩⟩
  rw [lim_level hI hb x e]
  simp only [fam, Over.comp_left, Category.assoc]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveActionThickeningEndosCompletePointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_additive_action_thickeningEndos_completePoints : ∀ (R : Type) [CommRing R] (I : Ideal R) (G : Over (Sp R)) [GrpObj G] (b : ∀ e : ℕ, thickObj R I e G ⟶ thickObj R I e G), (∀ e, IsMonHom (b e)) → (∀ e, thickMap R I e G ≫ (b (e + 1)).left = (b e).left ≫ thickMap R I e G) → ∀ (B : Type) [CommRing B] [IsLocalRing B] [IsAdicComplete (maximalIdeal B) B] (s : Sp B ⟶ Sp R), s (closedPoint B) ∈ Set.range (thick R I 0) → ∃ Φ : (Over.mk s ⟶ G) → (Over.mk s ⟶ G), (∀ x y, Φ (x * y) = Φ x * Φ y) ∧ ∀ (x : Over.mk s ⟶ G) (e : ℕ), ∃ r : Sp (B ⧸ maximalIdeal B ^ (e + 1)) ⟶ (thickObj R I e G).left, r ≫ pullback.fst G.hom (thick R I e) = thick B (maximalIdeal B) e ≫ x.left ∧ r ≫ (b e).left ≫ pullback.fst G.hom (thick R I e) = thick B (maximalIdeal B) e ≫ (Φ x).left := by
  first | exact @GlobalTheory.exists_mul_map_points_of_thickEndo | exact GlobalTheory.exists_mul_map_points_of_thickEndo | (intros; apply GlobalTheory.exists_mul_map_points_of_thickEndo <;> assumption)
end
end
