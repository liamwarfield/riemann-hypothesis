module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.LocalFramePowerSections
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.NonemptyPerfectSectionsComplexOfSmoothProj
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PolarisationFormIntPolynomialBundles

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.TautologicalModel
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.Proof.TautologicalModel

section Taut

variable {X X' Y Z : Scheme.{0}}

theorem taut_le (L : LB X) (F : X' ⟶ X) (p : Y ⟶ X') (J : PUnit → L.ι) (K : PUnit → PUnit → L.ι) :
    (L.pull (p ≫ F)).U J ⊓ ((L.pull F).pull p).U K ≤ (p ≫ F) ⁻¹ᵁ (L.U (J ⟨⟩) ⊓ L.U (K ⟨⟩ ⟨⟩)) := fun _ hy =>
  ⟨mem_pull.1 hy.1, mem_pull (L := L) (F := F).1 (mem_pull (L := L.pull F) (F := p).1 hy.2)⟩

def taut (L : LB X) (F : X' ⟶ X) (p : Y ⟶ X') : LB.Iso ((L.pull F).pull p) (L.pull (p ≫ F)) :=
  ⟨fun q => res (taut_le L F p q.1 q.2) (pullU (p ≫ F) _ (L.g (q.1 ⟨⟩) (q.2 ⟨⟩ ⟨⟩)))⟩

theorem gw_taut (L : LB X) (F : X' ⟶ X) (p : Y ⟶ X') (f : Z ⟶ Y) (z : Z) (j : L.ι) (k : PUnit → PUnit → L.ι)
    (hj : (p ≫ F) (f z) ∈ L.U j) (hk : f z ∈ ((L.pull F).pull p).U k) :
    gw (taut L F p) f z j k = gm (f ≫ p ≫ F) z _ (L.g j (k ⟨⟩ ⟨⟩)) := by
  have hm : f z ∈ (L.pull (p ≫ F)).U (fun _ => j) ⊓ ((L.pull F).pull p).U k := ⟨mem_pull.2 hj, hk⟩
  exact (gm_res f z (taut_le L F p _ k) hm _).trans (gm_pull f (p ≫ F) z _ (taut_le L F p _ k hm) _)

theorem taut_isGen {L : LB X} (hL : L.IsLB) (F : X' ⟶ X) (p : Y ⟶ X') : (taut L F p).IsGen := by
  refine (isGen_iff _).2 fun Z f z j j' k k' hj hj' hk hk' => ?_
  have h1 : (f ≫ p) z ∈ (L.pull F).U (k ⟨⟩) := mem_pull (L := L.pull F) (F := p).1 hk
  have h1' : (f ≫ p) z ∈ (L.pull F).U (k' ⟨⟩) := mem_pull (L := L.pull F) (F := p).1 hk'
  have h2 : (f ≫ p ≫ F) z ∈ L.U (k ⟨⟩ ⟨⟩) := mem_pull (L := L) (F := F).1 h1
  have h2' : (f ≫ p ≫ F) z ∈ L.U (k' ⟨⟩ ⟨⟩) := mem_pull (L := L) (F := F).1 h1'
  rw [gw_taut L F p f z j k hj hk, gw_taut L F p f z j' k' hj' hk', gm_pull_g (L.pull F) p f z k k' hk hk',
    gm_pull_g L F (f ≫ p) z _ _ h1 h1', Category.assoc,
    ← gm_cocycle hL (f ≫ p ≫ F) z (i := j) (j := j') hj hj' h2,
    ← gm_cocycle hL (f ≫ p ≫ F) z (i := j') (j := k ⟨⟩ ⟨⟩) hj' h2 h2']
  generalize gm (f ≫ p ≫ F) z _ (L.g j j') = A
  generalize gm (f ≫ p ≫ F) z _ (L.g j' (k ⟨⟩ ⟨⟩)) = B
  generalize gm (f ≫ p ≫ F) z _ (L.g (k ⟨⟩ ⟨⟩) (k' ⟨⟩ ⟨⟩)) = C
  rw [_root_.mul_comm B C, _root_.mul_assoc, inv_mul_cancel_left]

end Taut

section Rig

variable {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} [GrpObj G'] [IsCommMonObj G'] [GrpObj G] [IsCommMonObj G]

theorem gm_rigPullOf (F : G'.left ⟶ G.left) (e : (𝟙_ (Over S')).left ⟶ (𝟙_ (Over S)).left)
    (he : eSec G' ≫ F = e ≫ eSec G) (L : LB G.left) (r : LB.Gen (L.pull (eSec G))) {Z : Scheme.{0}}
    (f : Z ⟶ (𝟙_ (Over S')).left) (z : Z) (j : PUnit → PUnit → L.ι)
    (hj : f z ∈ LB.wchart (L.pull F) (fun _ : PUnit => eSec G') j) :
    gm f z (LB.wchart (L.pull F) (fun _ : PUnit => eSec G') j) ((rigPullOf F e he L r).s j) =
      gm (f ≫ e) z (LB.wchart L (fun _ : PUnit => eSec G) (fun _ => j ⟨⟩ ⟨⟩)) (r.s (fun _ => j ⟨⟩ ⟨⟩)) :=
  (gm_res f z (rigPull_le F e he L j) hj _).trans (gm_pull f e z _ (rigPull_le F e he L j hj) _)

theorem rigPullOf_isGen (F : G'.left ⟶ G.left) (e : (𝟙_ (Over S')).left ⟶ (𝟙_ (Over S)).left)
    (he : eSec G' ≫ F = e ≫ eSec G) (L : LB G.left) (r : LB.Gen (L.pull (eSec G))) (hr : r.IsGen) :
    (rigPullOf F e he L r).IsGen := by
  intro i j
  refine unit_ext fun y hy => ?_
  have hi' := rigPull_le F e he L i hy.1
  have hj' := rigPull_le F e he L j hy.2
  refine ((gm_res _ y _ hy _).trans (gm_rigPullOf F e he L r (𝟙 _) y i hy.1)).trans (Eq.symm ?_)
  refine ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_pull_g (L.pull F) (eSec G') (𝟙 _) y i j hy.1 hy.2)
    ((gm_res _ y _ hy _).trans (gm_rigPullOf F e he L r (𝟙 _) y j hy.2)))).trans ?_
  rw [gen_trans (φ := fun _ : PUnit => eSec G) (ε := fun _ => 1) hr (𝟙 _ ≫ e) y hi' hj', trF, Fintype.prod_unique,
    zpow_one, gm_pull_g L F (𝟙 _ ≫ eSec G') y (i ⟨⟩) (j ⟨⟩) (mem_pull (L := L.pull F) (F := eSec G').1 hy.1)
      (mem_pull (L := L.pull F) (F := eSec G').1 hy.2), Category.assoc, Category.assoc, he]

end Rig

end GlobalTheory.Proof.TautologicalModel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFiniteEtaleSurjectiveLevelMap
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFiniteEtaleSurjectiveLevelMap
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

noncomputable section

namespace GlobalTheory.LevelMap

theorem of_baseChange (P : MorphismProperty Scheme.{0})
    [P.DescendsAlong (@Surjective ⊓ @Flat ⊓ @QuasiCompact)]
    {X₀ X₁ S₀ S₁ T : Scheme.{0}} (s₀ : X₀ ⟶ S₀) (s₁ : X₁ ⟶ S₁) (k : S₁ ⟶ S₀) (r : X₁ ⟶ X₀)
    (hr : r ≫ s₀ = s₁ ≫ k) (i₀ : T ⟶ S₀) (i₁ : T ⟶ S₁) (hi : i₁ ≫ k = i₀)
    [Surjective i₁] [Flat i₁] [QuasiCompact i₁]
    (rF : pullback s₁ i₁ ⟶ pullback s₀ i₀) (h₁ : rF ≫ pullback.fst _ _ = pullback.fst _ _ ≫ r)
    (h₂ : rF ≫ pullback.snd _ _ = pullback.snd _ _) (h : P rF) : P (pullback.lift r s₁ hr) := by
  subst hi
  let p : pullback s₀ (i₁ ≫ k) ⟶ pullback s₀ k :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ i₁) (by simp [pullback.condition])
  have hp : IsPullback p (pullback.snd _ _) (pullback.snd s₀ k) i₁ := by
    refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback s₀ k)
    have : p ≫ pullback.fst s₀ k = pullback.fst _ _ := pullback.lift_fst _ _ _
    rw [this]
    exact IsPullback.of_hasPullback _ _
  have hq : IsPullback (pullback.fst s₁ i₁) rF (pullback.lift r s₁ hr) p := by
    refine IsPullback.of_bot ?_ ?_ hp
    · rw [h₂, pullback.lift_snd]
      exact IsPullback.of_hasPullback _ _
    · apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc, pullback.lift_fst, pullback.lift_fst, h₁]
      · rw [Category.assoc, Category.assoc, pullback.lift_snd, pullback.lift_snd, reassoc_of% h₂, pullback.condition]
  refine MorphismProperty.of_isPullback_of_descendsAlong (P := P)
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) hq.flip ⟨⟨?_, ?_⟩, ?_⟩ h
  · exact MorphismProperty.of_isPullback (P := @Surjective) hp.flip ‹_›
  · exact MorphismProperty.of_isPullback (P := @Flat) hp.flip ‹_›
  · exact MorphismProperty.of_isPullback (P := @QuasiCompact) hp.flip ‹_›

theorem isFinite_descendsAlong_fpqc :
    MorphismProperty.DescendsAlong (@IsFinite : MorphismProperty Scheme.{0})
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by
  have := isAffineHom_descendsAlong_fpqc.{0}
  refine ⟨fun {A X Y Z fst snd f g} H hf hfst => ?_⟩
  have a2 : IsAffineHom g := MorphismProperty.of_isPullback_of_descendsAlong (P := @IsAffineHom) H hf inferInstance
  have a3 : UniversallyClosed g :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := @UniversallyClosed) H hf inferInstance
  have a4 : LocallyOfFiniteType g :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := @LocallyOfFiniteType) H hf inferInstance
  exact (IsFinite.iff_isIntegralHom_and_locallyOfFiniteType _).mpr
    ⟨IsIntegralHom.iff_universallyClosed_and_isAffineHom.mpr ⟨a3, a2⟩, a4⟩

theorem surjective_spMap {K L : Type} [Field K] [Field L] (k : K →+* L) : Surjective (spMap k) := by
  refine ⟨fun x => ?_⟩
  obtain ⟨y⟩ : Nonempty (Sp L) := inferInstanceAs (Nonempty (PrimeSpectrum L))
  exact ⟨y, Subsingleton.elim (α := PrimeSpectrum K) _ _⟩

theorem flat_spMap {K L : Type} [Field K] [Field L] (k : K →+* L) : Flat (spMap k) := by
  rw [Flat.SpecMap_iff]
  algebraize [k]
  exact (inferInstance : Module.Flat K L)

theorem finite_etale_spMap {K L : Type} [Field K] [Field L] [CharZero K] [CharZero L] [FiniteDimensional ℚ L]
    (k : K →+* L) : IsFinite (spMap k) ∧ Etale (spMap k) := by
  algebraize [k]
  have : IsScalarTower ℚ K L := IsScalarTower.of_algebraMap_eq fun x => by simp
  have hf : Module.Finite K L := Module.Finite.of_restrictScalars_finite ℚ K L
  constructor
  · rw [IsFinite.SpecMap_iff]
    exact hf
  · rw [HasRingHomProperty.Spec_iff (P := @Etale)]
    have : Algebra.FormallyEtale K L := Algebra.FormallyEtale.of_isSeparable K L
    have : Algebra.FinitePresentation K L := Algebra.FinitePresentation.of_finiteType.mp inferInstance
    exact (⟨inferInstance, inferInstance⟩ : Algebra.Etale K L)

theorem exists_levelMap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l), ToroidalLevelCompatibility (H := H) (D := D) → ∀ (l₀ l₁ : Level H), l₀.Dvd l₁ → ∃ (k : KA l₀ →+* KA l₁) (r : (Xo l₁).X ⟶ (Xo l₀).X) (ν : SABMap (Xo l₁).univ.t (Xo l₀).univ.t r) (hr : r ≫ (Xo l₀).s = (Xo l₁).s ≫ spMap k), IsInc (KA l₀).val.toRingHom (KA l₁).val.toRingHom k ∧ LevComp (Xo l₁).univ (Xo l₀).univ r ν ∧ IsFinite (pullback.lift r _ hr) ∧ Etale (pullback.lift r _ hr) ∧ Surjective (pullback.lift r _ hr) ∧ IsFinite r ∧ Etale r ∧ Surjective r := by
  intro E _ _ _ H D Xo hN l₀ l₁ hd
  obtain ⟨r, k, ν, hk, hr, h1, h2, -, hc⟩ := hN l₀ l₁ (Xo l₀) (Xo l₁) hd
  obtain ⟨c₁⟩ : Nonempty (Coeff l₁) := inferInstance
  have hle : KA l₀ ≤ c₁.F := fun x hx => by
    have := c₁.le (k ⟨x, hx⟩).2
    rwa [hk] at this
  let c₀ : Coeff l₀ :=
    { F := c₁.F
      fin := c₁.fin
      conj := c₁.conj
      zeta_mem := by
        obtain ⟨e, he⟩ := LevelExist.zeta_eq_pow_of_dvd (a := l₀.M') (LevelExist.M'_pos l₁)
          (Nat.lcm_dvd (hd.1.trans (Nat.dvd_lcm_left _ _)) (hd.2.2.trans (Nat.dvd_lcm_right _ _)) : l₀.M' ∣ l₁.M')
        rw [he]
        exact pow_mem c₁.zeta_mem e
      le := hle }
  obtain ⟨rF, e1, e2, f1, f2, f3, -⟩ := hc c₀ c₁ rfl
  have hid : spMap (IntermediateField.inclusion (le_refl c₁.F)).toRingHom = 𝟙 (Sp c₁.F) := by
    rw [← Spec.map_id]
    rfl
  have e2' : rF ≫ pullback.snd _ _ = pullback.snd _ _ := e2.trans ((congrArg _ hid).trans (Category.comp_id _))
  have hi : spMap (IntermediateField.inclusion c₁.le).toRingHom ≫ spMap k =
      spMap (IntermediateField.inclusion c₀.le).toRingHom := by
    rw [← Spec.map_comp]
    congr 1
    ext x
    exact hk x
  have := surjective_spMap (IntermediateField.inclusion c₁.le).toRingHom
  have := flat_spMap (IntermediateField.inclusion c₁.le).toRingHom
  have := isFinite_descendsAlong_fpqc
  have g1 : IsFinite (pullback.lift r _ hr) := of_baseChange @IsFinite _ _ _ r hr _ _ hi rF e1 e2' f1
  have g2 : Etale (pullback.lift r _ hr) := of_baseChange @Etale _ _ _ r hr _ _ hi rF e1 e2' f2
  have g3 : Surjective (pullback.lift r _ hr) := of_baseChange @Surjective _ _ _ r hr _ _ hi rF e1 e2' f3
  have := c₁.fin
  have : FiniteDimensional ℚ (KA l₁) :=
    FiniteDimensional.of_injective (IntermediateField.inclusion c₁.le).toLinearMap
      (IntermediateField.inclusion c₁.le).injective
  obtain ⟨k1, k2⟩ := finite_etale_spMap k
  have k3 := surjective_spMap k
  have hfac : pullback.lift r _ hr ≫ pullback.fst _ _ = r := pullback.lift_fst _ _ _
  refine ⟨k, r, ν, hr, hk, ⟨h1, h2⟩, g1, g2, g3, ?_, ?_, ?_⟩
  all_goals
    rw [← hfac]
    infer_instance

end GlobalTheory.LevelMap

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFiniteEtaleSurjectiveLevelMapStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models
theorem _root_.GlobalTheory.T.exists_finite_etale_surjective_levelMap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l), ToroidalLevelCompatibility (H := H) (D := D) → ∀ (l₀ l₁ : Level H), l₀.Dvd l₁ → ∃ (k : KA l₀ →+* KA l₁) (r : (Xo l₁).X ⟶ (Xo l₀).X) (ν : SABMap (Xo l₁).univ.t (Xo l₀).univ.t r) (hr : r ≫ (Xo l₀).s = (Xo l₁).s ≫ spMap k), IsInc (KA l₀).val.toRingHom (KA l₁).val.toRingHom k ∧ LevComp (Xo l₁).univ (Xo l₀).univ r ν ∧ IsFinite (pullback.lift r _ hr) ∧ Etale (pullback.lift r _ hr) ∧ Surjective (pullback.lift r _ hr) ∧ IsFinite r ∧ Etale r ∧ Surjective r := by
  first | exact @GlobalTheory.LevelMap.exists_levelMap | exact GlobalTheory.LevelMap.exists_levelMap | (intros; apply GlobalTheory.LevelMap.exists_levelMap <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SeesawReducedBaseAbelianSchemeOfDenseFibres
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.DenseAffine
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.TrivLocallyOfDense
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFieldPullbackAppTopBijectiveAndTriv
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.AbLaw

noncomputable section
namespace GlobalTheory.GeomFibre

theorem bijective_appTop (K : Type) [Field K] [IsAlgClosed K] {X : Scheme.{0}}
    (f : X ⟶ Spec (CommRingCat.of K)) [IsIntegral X] [IsProper f] : Function.Bijective f.appTop.hom := by
  have hfin : f.appTop.hom.Finite := finite_appTop_of_universallyClosed K f
  let e := (Scheme.ΓSpecIso (CommRingCat.of K)).inv
  have he : Function.Bijective e.hom := ConcreteCategory.bijective_of_isIso e
  have hfin' : (f.appTop.hom.comp e.hom).Finite := hfin.comp (RingHom.Finite.of_surjective _ he.2)
  have hb : Function.Bijective (f.appTop.hom.comp e.hom) :=
    IsAlgClosed.ringHom_bijective_of_isIntegral (k := K) _ hfin'.to_isIntegral
  exact (Function.Bijective.of_comp_iff _ he).1 hb

theorem exists_field_pullback_appTop_bijective_and_triv : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) (M : LB X), M.IsLB → IsProper f → GeometricallyIntegral f → ∀ (K : Type) [Field K] (g : R →+* K) (X' : Scheme.{0}) (π : X' ⟶ X) (f' : X' ⟶ Spec (CommRingCat.of K)), IsPullback π f' f (Spec.map (CommRingCat.ofHom g)) → Triv (M.pull π) → ∃ (K₀ : Type) (_ : Field K₀) (g₀ : R →+* K₀) (X₀ : Scheme.{0}) (π₀ : X₀ ⟶ X) (f₀ : X₀ ⟶ Spec (CommRingCat.of K₀)), RingHom.ker g₀ = RingHom.ker g ∧ IsPullback π₀ f₀ f (Spec.map (CommRingCat.ofHom g₀)) ∧ Function.Bijective f₀.appTop.hom ∧ Triv (M.pull π₀) := by
  intro R _ X f M _ _ _ K _ g X' π f' h ⟨t, ht⟩
  let a : K →+* AlgebraicClosure K := algebraMap K (AlgebraicClosure K)
  have h₁ := IsPullback.of_hasPullback f' (Spec.map (CommRingCat.ofHom a))
  have h₂ : IsPullback (pullback.fst f' (Spec.map (CommRingCat.ofHom a)) ≫ π)
      (pullback.snd f' (Spec.map (CommRingCat.ofHom a))) f (Spec.map (CommRingCat.ofHom (a.comp g))) := by
    rw [CommRingCat.ofHom_comp, Spec.map_comp]
    exact h₁.paste_horiz h
  have : IsIntegral (pullback f' (Spec.map (CommRingCat.ofHom a))) :=
    GeometricallyIntegral.geometrically_isIntegral _ _ _ h₂
  have : IsProper (pullback.snd f' (Spec.map (CommRingCat.ofHom a))) :=
    MorphismProperty.of_isPullback (P := @IsProper) h₂ inferInstance
  refine ⟨AlgebraicClosure K, inferInstance, a.comp g, _, _, _, RingHom.ker_comp_of_injective g a.injective,
    h₂, bijective_appTop _ _, ?_⟩
  exact ⟨_, LB.isGen_pullGen M _ _ t ht _⟩

end GlobalTheory.GeomFibre
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.AbLaw

noncomputable section
namespace GlobalTheory.SeesawReduced

theorem triv_locally_of_dense : ∀ (R : Type) [CommRing R] [IsReduced R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) (M : LB X), M.IsLB → Smooth f → IsProper f → GeometricallyIntegral f → IsProjBy f → Dense {p : PrimeSpectrum R | ∃ (K : Type) (_ : Field K) (g : R →+* K) (X' : Scheme.{0}) (π : X' ⟶ X) (f' : X' ⟶ Spec (CommRingCat.of K)), RingHom.ker g = p.asIdeal ∧ IsPullback π f' f (Spec.map (CommRingCat.ofHom g)) ∧ Triv (M.pull π)} → ∀ p : PrimeSpectrum R, ∃ r : R, r ∉ p.asIdeal ∧ ∀ (R' : Type) [CommRing R'] (g : R →+* R') (X' : Scheme.{0}) (π : X' ⟶ X) (f' : X' ⟶ Spec (CommRingCat.of R')), IsPullback π f' f (Spec.map (CommRingCat.ofHom g)) → IsUnit (g r) → Triv (M.pull π) := by
  intro R _ _ X f M hM hSm hPr hGI hPB hD p
  haveI := hPr
  haveI := hGI

  have hP : Nonempty (Perf f M) := GlobalTheory.T.nonempty_perfectSectionsComplex_of_smooth_proj R X f hSm hPB M hM
  have hQ : Nonempty (Perf f (pw M (-1))) := GlobalTheory.T.nonempty_perfectSectionsComplex_of_smooth_proj R X f hSm hPB _ (isLB_pw hM (-1))

  have hC := GlobalTheory.TrivLocus.isClosed_trivLocus R X f M hM hP hQ hPr hGI
  have hAll := hD.closure_eq.symm.trans hC.closure_eq
  have hmem : ∀ q : PrimeSpectrum R, q ∈ {p : PrimeSpectrum R | ∃ (K : Type) (_ : Field K) (g : R →+* K)
      (X' : Scheme.{0}) (π : X' ⟶ X) (f' : X' ⟶ Spec (CommRingCat.of K)), RingHom.ker g = p.asIdeal ∧
      IsPullback π f' f (Spec.map (CommRingCat.ofHom g)) ∧ Triv (M.pull π)} := by
    intro q; rw [← hAll]; exact Set.mem_univ q

  obtain ⟨K, _, g, X₁, π₁, f₁, hk, hpb, htr⟩ := hmem p
  obtain ⟨K₀, _, g₀, X₀, π₀, f₀, hk₀, hpb₀, hbij, htr₀⟩ :=
    GlobalTheory.GeomFibre.exists_field_pullback_appTop_bijective_and_triv R X f M hM hPr hGI K g X₁ π₁ f₁ hpb htr
  obtain ⟨r, I, hr, -, hI⟩ := GlobalTheory.AbLaw.Seesaw.seesaw R X f M hM hP inferInstance inferInstance
    K₀ g₀ X₀ π₀ f₀ hpb₀ hbij htr₀
  refine ⟨r, ?_, ?_⟩
  · intro hrp
    apply hr
    have hrk : r ∈ RingHom.ker g₀ := by rw [hk₀, hk]; exact hrp
    exact RingHom.mem_ker.1 hrk

  have hvan : ∀ x ∈ I, x * r = 0 := by
    intro x hx
    apply IsReduced.eq_zero
    rw [← mem_nilradical, nilradical_eq_sInf, Ideal.mem_sInf]
    intro J hJ
    let q : PrimeSpectrum R := ⟨J, hJ⟩
    by_cases hrJ : r ∈ J
    · exact J.mul_mem_left x hrJ
    · apply J.mul_mem_right r
      obtain ⟨L, _, gq, Xq, πq, fq, hkq, hpbq, htrq⟩ := hmem q
      have hu : IsUnit (gq r) := by
        rw [isUnit_iff_ne_zero]
        intro h0
        have hrk : r ∈ RingHom.ker gq := RingHom.mem_ker.2 h0
        rw [hkq] at hrk
        exact hrJ hrk
      have := ((hI L gq Xq πq fq hpbq hu).1 htrq) hx
      rw [RingHom.mem_ker] at this
      show x ∈ q.asIdeal
      rw [← hkq]; exact this
  intro R' _ g' X' π f' hpb' hu'
  refine (hI R' g' X' π f' hpb' hu').2 ?_
  intro x hx
  rw [RingHom.mem_ker]
  have h0 : g' x * g' r = 0 := by rw [← map_mul, hvan x hx, map_zero]
  exact (hu'.mul_left_eq_zero).1 h0

end GlobalTheory.SeesawReduced
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.AbLaw

noncomputable section
namespace GlobalTheory.SeesawLocal

theorem dense_affine {S X : Scheme.{0}} (f : X ⟶ S) (N : LB X) {R : Type} [CommRing R]
    (j : Spec (CommRingCat.of R) ⟶ S) [IsOpenImmersion j]
    (hd : Dense {p : S | ∃ (K : Type) (_ : Field K) (x : Sp K ⟶ S) (Y : Scheme.{0}) (ρ : Y ⟶ X) (h : Y ⟶ Sp K),
      p ∈ Set.range x ∧ IsPullback ρ h f x ∧ ∃ c : (N.pull ρ).Gen, c.IsGen}) :
    Dense {p : PrimeSpectrum R | ∃ (K : Type) (_ : Field K) (g : R →+* K) (X' : Scheme.{0})
      (π : X' ⟶ pullback f j) (f' : X' ⟶ Spec (CommRingCat.of K)), RingHom.ker g = p.asIdeal ∧
      IsPullback π f' (pullback.snd f j) (Spec.map (CommRingCat.ofHom g)) ∧
      Triv ((N.pull (pullback.fst f j)).pull π)} := by
  refine (hd.preimage j.isOpenEmbedding.isOpenMap).mono ?_
  rintro q ⟨K, hK, x, Y, ρ, h, ⟨z, hz⟩, hpb, c, hc⟩
  have hsub : Subsingleton (Sp K) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  have hr : Set.range x ⊆ Set.range j := by
    rintro _ ⟨w, rfl⟩
    exact ⟨q, by rw [Subsingleton.elim w z]; exact hz.symm⟩
  obtain ⟨x', hx'⟩ : ∃ x' : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R), x' ≫ j = x :=
    ⟨IsOpenImmersion.lift j x hr, IsOpenImmersion.lift_fac j x hr⟩
  have hmap : Spec.map (CommRingCat.ofHom (Spec.preimage x').hom) = x' := by
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  refine ⟨K, hK, (Spec.preimage x').hom, Y,
    pullback.lift ρ (h ≫ x') (by rw [hpb.w, Category.assoc, hx']), h, ?_, ?_, ?_⟩
  · have h1 : j (x' z) = j q := by rw [← hz, ← hx']; rfl
    have h2 : x' z = q := j.isOpenEmbedding.injective h1
    have h3 : Spec.map (Spec.preimage x') z = q := by rw [Spec.map_preimage]; exact h2
    rw [← h3]
    change RingHom.ker (Spec.preimage x').hom =
      Ideal.comap (Spec.preimage x').hom (z : PrimeSpectrum K).asIdeal
    rw [@Ideal.eq_bot_of_prime K _ (z : PrimeSpectrum K).asIdeal (z : PrimeSpectrum K).isPrime]
    exact RingHom.ker_eq_comap_bot _
  · rw [hmap]
    refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback f j)
    rw [pullback.lift_fst, hx']
    exact hpb
  · apply CubeOpen.triv_pull_pull
    rw [pullback.lift_fst]
    exact ⟨c, hc⟩

theorem triv_locally_of_dense : ∀ (S₀ : Scheme.{0}) (B : Over S₀) [GrpObj B] (M : LB B.left), IsAbelianScheme B → M.IsLB → Out.RelAmple B M → ∀ (S X : Scheme.{0}) [IsReduced S] (t : S ⟶ S₀) (π : X ⟶ B.left) (f : X ⟶ S) (N : LB X), IsPullback π f B.hom t → N.IsLB → Dense {p : S | ∃ (K : Type) (_ : Field K) (x : Sp K ⟶ S) (Y : Scheme.{0}) (ρ : Y ⟶ X) (h : Y ⟶ Sp K), p ∈ Set.range x ∧ IsPullback ρ h f x ∧ ∃ c : (N.pull ρ).Gen, c.IsGen} → ∀ s : S, ∃ U : S.Opens, s ∈ U ∧ ∃ c : (N.pull (f ⁻¹ᵁ U).ι).Gen, c.IsGen := by
  intro S₀ B _ M hA hM hRel S X _ t π f N hpb hN hd s
  obtain ⟨R, j, hj, ⟨pt, hpt⟩, -⟩ :=
    Scheme.exists_affine_mem_range_and_range_subset (X := S) (x := s) (U := ⊤) trivial
  have hRed : _root_.IsReduced R := by
    have := isReduced_of_isOpenImmersion j
    exact (affine_isReduced_iff R).mp inferInstance
  have hsq : IsPullback (pullback.fst f j ≫ π) (pullback.snd f j) B.hom (j ≫ t) :=
    (IsPullback.of_hasPullback f j).paste_horiz hpb
  obtain ⟨hP, hSm, hPr, hGI⟩ := AmpleBaseChange.isProjBy_smooth_isProper_geometricallyIntegral
    S₀ B M hA hM hRel R (j ≫ t) _ _ _ hsq
  obtain ⟨r, hr, H⟩ := SeesawReduced.triv_locally_of_dense R (pullback f j) (pullback.snd f j)
    (N.pull (pullback.fst f j)) (pull_isLB hN _) hSm hPr hGI hP (dense_affine f N j hd) pt
  set p : PrimeSpectrum R := pt with hp
  have h0 : p ∈ PrimeSpectrum.basicOpen r := hr
  rw [← SetLike.mem_coe, ← PrimeSpectrum.localization_away_comap_range (Localization.Away r) r] at h0
  obtain ⟨w, hw⟩ := h0
  obtain ⟨j', hj'⟩ : ∃ j' : Spec (CommRingCat.of (Localization.Away r)) ⟶ S,
      j' = Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r))) ≫ j := ⟨_, rfl⟩
  have hjo : IsOpenImmersion j' := by rw [hj']; infer_instance
  refine ⟨j'.opensRange, ?_, ?_⟩
  · show s ∈ Set.range j'
    refine ⟨w, ?_⟩
    rw [hj']
    change j ((Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r)))) w) = s
    rw [← hpt]
    exact congrArg j hw
  · have hU : IsPullback (f ⁻¹ᵁ j'.opensRange).ι (morphismRestrict f j'.opensRange ≫ j'.isoOpensRange.inv)
        f j' := by
      have hb : IsPullback j'.opensRange.ι j'.isoOpensRange.inv (𝟙 S) j' :=
        IsPullback.of_vert_isIso ⟨by simp⟩
      simpa using (isPullback_morphismRestrict f j'.opensRange).flip.paste_vert hb
    obtain ⟨π₀, h₁, h₂⟩ : ∃ π₀ : (f ⁻¹ᵁ j'.opensRange).toScheme ⟶ pullback f j,
        π₀ ≫ pullback.fst f j = (f ⁻¹ᵁ j'.opensRange).ι ∧
        π₀ ≫ pullback.snd f j = (morphismRestrict f j'.opensRange ≫ j'.isoOpensRange.inv) ≫
          Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r))) :=
      ⟨pullback.lift _ _ (by rw [hU.w]; simp only [Category.assoc]; rw [← hj']), pullback.lift_fst _ _ _,
        pullback.lift_snd _ _ _⟩
    have hsq' : IsPullback π₀ (morphismRestrict f j'.opensRange ≫ j'.isoOpensRange.inv)
        (pullback.snd f j) (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r)))) := by
      refine IsPullback.of_right ?_ h₂ (IsPullback.of_hasPullback f j)
      rw [h₁, ← hj']
      exact hU
    obtain ⟨c, hc⟩ := H (Localization.Away r) (algebraMap R (Localization.Away r)) _ π₀ _ hsq'
      (IsLocalization.Away.algebraMap_isUnit r)
    obtain ⟨d, hd'⟩ := GlobalTheory.exists_isGen_linComb_of_pull N _ _ π₀ c hc
    exact CubeOpen.triv_comp (f := π₀ ≫ pullback.fst f j) (𝟙 _) (by rw [Category.id_comp, h₁]) ⟨d, hd'⟩

end GlobalTheory.SeesawLocal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SeesawReducedBaseAbelianSchemeOfDenseFibres
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem seesaw_reduced_of_dense :
    Out.GlobalFnsSt → ∀ (S₀ : Scheme.{0}) (B : Over S₀) [GrpObj B] (M : LB B.left), IsAbelianScheme B → M.IsLB → Out.RelAmple B M → ∀ (S X : Scheme.{0}) [IsReduced S] (t : S ⟶ S₀) (π : X ⟶ B.left) (f : X ⟶ S) (N : LB X), IsPullback π f B.hom t → N.IsLB → Dense {p : S | ∃ (K : Type) (_ : Field K) (x : Sp K ⟶ S) (Y : Scheme.{0}) (ρ : Y ⟶ X) (h : Y ⟶ Sp K), p ∈ Set.range x ∧ IsPullback ρ h f x ∧ ∃ c : (N.pull ρ).Gen, c.IsGen} → ∀ σ : S ⟶ X, σ ≫ f = 𝟙 S → (∃ c : (N.pull σ).Gen, c.IsGen) → ∃ c : N.Gen, c.IsGen := by
  intro hG S₀ B _ M hB hM hA S X _ t π f N hp hN hd σ hσ hc
  exact GlobalTheory.exists_gen_of_local_of_section X S f σ N hN hσ
    (GlobalTheory.BaseChangeFns.app_surjective hG S₀ B hB S X t π f hp)
    (GlobalTheory.SeesawLocal.triv_locally_of_dense S₀ B M hB hM hA S X t π f N hp hN hd) hc

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SeesawReducedBaseAbelianSchemeOfDenseFibresStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seesaw_reduced_base_abelianScheme_of_dense_fibres : Out.GlobalFnsSt → ∀ (S₀ : Scheme.{0}) (B : Over S₀) [GrpObj B] (M : LB B.left), IsAbelianScheme B → M.IsLB → Out.RelAmple B M → ∀ (S X : Scheme.{0}) [IsReduced S] (t : S ⟶ S₀) (π : X ⟶ B.left) (f : X ⟶ S) (N : LB X), IsPullback π f B.hom t → N.IsLB → Dense {p : S | ∃ (K : Type) (_ : Field K) (x : Sp K ⟶ S) (Y : Scheme.{0}) (ρ : Y ⟶ X) (h : Y ⟶ Sp K), p ∈ Set.range x ∧ IsPullback ρ h f x ∧ ∃ c : (N.pull ρ).Gen, c.IsGen} → ∀ σ : S ⟶ X, σ ≫ f = 𝟙 S → (∃ c : (N.pull σ).Gen, c.IsGen) → ∃ c : N.Gen, c.IsGen := by
  first | exact @GlobalTheory.seesaw_reduced_of_dense | exact GlobalTheory.seesaw_reduced_of_dense | (intros; apply GlobalTheory.seesaw_reduced_of_dense <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsNormalFiniteModelOfFiniteOverOpen
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory

theorem exists_normal_finite_model_of_finite_over_open : ∀ (O F : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Field F] [Algebra O F] [IsFractionRing O F] (X U : Scheme.{0}) (s : X ⟶ Sp O) (c : U ⟶ Sp F) (f : U ⟶ X) (W : (pullback s (spMap (algebraMap O F))).Opens) (fW : U ⟶ W.toScheme), IsProjOver s → Geo.Tor.IsNormalScheme U → IsFinite fW → fW ≫ W.ι ≫ pullback.fst _ _ = f → fW ≫ W.ι ≫ pullback.snd _ _ = c → ∃ (Y : Scheme.{0}) (π : Y ⟶ X) (jQ : U ⟶ pullback (π ≫ s) (spMap (algebraMap O F))), IsFinite π ∧ Geo.Tor.IsNormalScheme Y ∧ IsProjOver (π ≫ s) ∧ Flat (π ≫ s) ∧ jQ ≫ pullback.snd _ _ = c ∧ jQ ≫ pullback.fst _ _ ≫ π = f ∧ IsOpenImmersion jQ ∧ Dense (Set.range jQ) ∧ ∀ y : ↥(pullback (π ≫ s) (spMap (algebraMap O F))), y ∈ Set.range jQ ↔ π (pullback.fst (π ≫ s) (spMap (algebraMap O F)) y) ∈ Set.range (W.ι ≫ pullback.fst s (spMap (algebraMap O F))) := by
  intro O F _ _ _ _ _ _ X U s c f W fW hs hU hfW hf hc
  have hprop : IsProper s := (isProjOver_iff_isProper_and_exists_isAmpleLB s).mp hs |>.1
  have hN : GlobalTheory.IsNormalScheme U := .of_pred hU
  have hb : IsPullback (pullback.fst s (spMap (algebraMap O F))) (pullback.snd _ _) s
      (spMap (algebraMap O F)) := .of_hasPullback _ _
  have : IsLocallyNoetherian (pullback s (spMap (algebraMap O F))) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd s (spMap (algebraMap O F)))
  have : QuasiCompact f := by rw [← hf]; infer_instance
  have : QuasiSeparated f := by rw [← hf]; infer_instance
  have : LocallyOfFiniteType c := by rw [← hc]; infer_instance
  have : IsLocallyNoetherian U := LocallyOfFiniteType.isLocallyNoetherian c
  have w : f ≫ s = c ≫ spMap (algebraMap O F) := by
    rw [← hf, ← hc]; simp only [Category.assoc, pullback.condition]
  have hfin : IsFinite f.fromNormalization :=
    isFinite_fromNormalization_of_over_fractionRing (o := .of O) f s F c w
  have h := isPullback_toNormalization_of_isLocalization (M := nonZeroDivisors O) hb fW W.ι f hf.symm
  have hb' : IsPullback (pullback.fst (f.fromNormalization ≫ s) (spMap (algebraMap O F)))
      (pullback.snd _ _) (f.fromNormalization ≫ s) (spMap (algebraMap O F)) := .of_hasPullback _ _
  have hpre := isPreimmersion_of_isPullback_localization (nonZeroDivisors O) hb
  have hpre' := isPreimmersion_of_isPullback_localization (nonZeroDivisors O) hb'
  let q : pullback (f.fromNormalization ≫ s) (spMap (algebraMap O F)) ⟶
      pullback s (spMap (algebraMap O F)) :=
    pullback.lift (pullback.fst _ _ ≫ f.fromNormalization) (pullback.snd _ _)
      (by simpa using pullback.condition)
  have hq₁ : q ≫ pullback.fst _ _ = pullback.fst _ _ ≫ f.fromNormalization := pullback.lift_fst ..
  have hq₂ : q ≫ pullback.snd _ _ = pullback.snd _ _ := pullback.lift_snd ..
  have hq : IsPullback (pullback.fst (f.fromNormalization ≫ s) (spMap (algebraMap O F))) q
      f.fromNormalization (pullback.fst s (spMap (algebraMap O F))) :=
    IsPullback.of_bot (by rw [hq₂]; exact hb') hq₁.symm hb
  let j : U ⟶ pullback (f.fromNormalization ≫ s) (spMap (algebraMap O F)) :=
    pullback.lift f.toNormalization c (by simpa using w)
  have hj₁ : j ≫ pullback.fst _ _ = f.toNormalization := pullback.lift_fst ..
  have hj₂ : j ≫ pullback.snd _ _ = c := pullback.lift_snd ..
  have hjq : j ≫ q = fW ≫ W.ι := by
    apply pullback.hom_ext
    · rw [Category.assoc, hq₁, reassoc_of% hj₁, Category.assoc, hf]
      simp
    · rw [Category.assoc, hq₂, hj₂, Category.assoc, hc]
  have hj : IsPullback j fW q W.ι := IsPullback.of_right (by rw [hj₁]; exact h) hjq hq
  refine ⟨f.normalization, f.fromNormalization, j, hfin, IsNormalScheme.pred _,
    isProjOver_comp_of_isFinite _ hs, flat_fromNormalization_comp f F s c w, hj₂,
    by rw [reassoc_of% hj₁]; simp,
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) hj.flip inferInstance, ?_, fun y ↦ ?_⟩
  · rw [hpre'.isEmbedding.isInducing.dense_iff]
    intro y
    have hd : DenseRange f.toNormalization := f.toNormalization.denseRange
    rw [← Set.range_comp, ← TopCat.coe_comp, ← Scheme.Hom.comp_base, hj₁]
    exact hd _
  · rw [← Scheme.Hom.comp_apply, ← hq₁, Scheme.Hom.comp_apply]
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨fW u, by rw [Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply fW, ← hjq]; simp⟩
    · rintro ⟨v, hv⟩
      rw [Scheme.Hom.comp_apply] at hv
      obtain ⟨u, hu, -⟩ := Scheme.exists_preimage_of_isPullback hj y v
        (hpre.isEmbedding.injective hv).symm
      exact ⟨u, hu⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionSectionExtendsAbLocus
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory

theorem exists_section_of_pow_eq_one {T V : Scheme.{0}} [IsLocallyNoetherian T] (hT : Geo.Tor.IsNormalScheme T)
    (j : V ⟶ T) [IsPreimmersion j] [Flat j] [IsDominant j] [QuasiCompact j]
    (G : Over T) [GrpObj G] [IsCommMonObj G] [IsProper G.hom] (n : ℕ) (hn : IsUnit (n : Γ(T, ⊤)))
    (P : Over T) (x : P ⟶ G) (hx : x ^ n = 1) (k : V ⟶ P.left) (hk : k ≫ P.hom = j) :
    ∃ σ : T ⟶ G.left, σ ≫ G.hom = 𝟙 T ∧ j ≫ σ = k ≫ x.left := by
  have hw : (Out.mulA G n).left ≫ G.hom = G.hom := Over.w _
  have h₁ : FormallyUnramified (Out.mulA G n).left := formallyUnramified_mulA T G n hn
  have h₂ : IsProper ((Out.mulA G n).left ≫ G.hom) := by rw [hw]; infer_instance
  have h₃ : IsProper (Out.mulA G n).left := IsProper.of_comp _ G.hom
  have h₄ : LocallyQuasiFinite (Out.mulA G n).left := by
    refine ⟨fun {U} hU {W} hW e => ?_⟩
    have a₁ := (Out.mulA G n).left.formallyUnramified_appLE hU hW e
    have a₂ := (Out.mulA G n).left.finiteType_appLE hU hW e
    algebraize [((Out.mulA G n).left.appLE U W e).hom]
    exact inferInstanceAs (Algebra.QuasiFinite _ _)
  have h₅ : IsFinite (Out.mulA G n).left := .of_isProper_of_locallyQuasiFinite _
  have e₁ : x ≫ Out.mulA G n = toUnit P ≫ η[G] := by
    rw [Out.mulA, MonObj.comp_pow, Category.comp_id, hx, Hom.one_def]
  have e₂ : x.left ≫ (Out.mulA G n).left = P.hom ≫ (η[G]).left := by
    rw [← Over.comp_left, e₁]; simp
  obtain ⟨σ, ⟨a, b⟩, -⟩ := existsUnique_lift_of_densePart T V G.left G.left j hT ‹_› ‹_› ‹_› ‹_›
    (Out.mulA G n).left (η[G]).left (k ≫ x.left) inferInstance
    (by rw [Category.assoc, e₂, ← hk, Category.assoc])
  refine ⟨σ, ?_, a⟩
  rw [← hw, reassoc_of% b]
  exact Over.w η[G]

theorem torsion_section_extends_abLocus : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β), IsDedFrac β → AbOpen Y.t.G → ∃ U : Y.X.Opens, (U : Set Y.X) = abLocus Y.t.G ∧ ∀ (σ : 𝟙_ (Over (Xo.XF c)) ⟶ Y.oF.t.G) (n : ℕ), IsUnit (n : O) → σ ^ n = 1 → Y.Extends U σ := by
  intro E _ _ _ H D l Xo c O _ β Y ⟨⟨_, hD⟩, _, hF⟩ ⟨U, hU, hP⟩
  refine ⟨U, hU, fun σ n hn hσ => ?_⟩
  letI : Algebra O c.F := β.toAlgebra
  obtain ⟨hN, -, -, j₁, j₂, j₃, j₄⟩ := genericPart_dense_proOpen O c.F Y.X (Xo.XF c) Y.s Y.jQ Y.flat Y.proj
    Y.jQ_open Y.jQ_dense
  replace j₁ : IsPreimmersion Y.j := j₁
  replace j₂ : Flat Y.j := j₂
  replace j₃ : IsDominant Y.j := j₃
  replace j₄ : QuasiCompact Y.j := j₄
  have hr : Set.range Y.j ⊆ Set.range U.ι := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι, hU]
    have : Y.jQ x ∈ pullback.fst Y.s (spMap β) ⁻¹' abLocus Y.t.G := by
      rw [Y.ab_gen]; exact ⟨_, rfl⟩
    exact this
  let j : Xo.XF c ⟶ U.toScheme := IsOpenImmersion.lift U.ι Y.j hr
  have hj : j ≫ U.ι = Y.j := IsOpenImmersion.lift_fac _ _ _
  have sq : IsPullback (𝟙 _) j Y.j U.ι := IsPullback.of_horiz_isIso_mono ⟨by simp [hj]⟩
  have k₁ : IsPreimmersion j := MorphismProperty.of_isPullback (P := @IsPreimmersion) sq j₁
  have k₂ : Flat j := MorphismProperty.of_isPullback (P := @Flat) sq j₂
  have k₄ : QuasiCompact j := MorphismProperty.of_isPullback (P := @QuasiCompact) sq j₄
  have k₃ : IsDominant j := by
    constructor
    have hd := Dense.preimage j₃.denseRange U.ι.isOpenEmbedding.isOpenMap
    refine hd.mono ?_
    rintro y ⟨x, hx⟩
    refine ⟨x, U.ι.isOpenEmbedding.injective ?_⟩
    rw [← hx, ← hj]; rfl
  have hT : Geo.Tor.IsNormalScheme U.toScheme := fun x => by
    obtain ⟨_, _⟩ := Y.normal (U.ι x)
    let e := (asIso (U.ι.stalkMap x)).commRingCatIsoToRingEquiv
    exact ⟨e.symm.toMulEquiv.isDomain _, IsIntegrallyClosed.of_equiv e⟩
  have hn' : IsUnit (n : Γ(U.toScheme, ⊤)) := by
    simpa using hn.map ((U.ι ≫ Y.s).appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom)
  let G : Over U.toScheme := (Over.pullback U.ι).obj Y.t.G
  have hG : IsProper G.hom := by
    have : IsProper ((pullbackRestrictIsoRestrict Y.t.G.hom U).inv ≫ pullback.snd Y.t.G.hom U.ι) := hP
    exact (MorphismProperty.cancel_left_of_respectsIso @IsProper _ _).mp this
  have gp := isGrpPullback_pullback Y.t.G U.ι
  have hc := Y.m.cart
  let ψ : Y.oF.t.G.left ⟶ G.left := gp.1.lift Y.m.φ (Y.oF.t.G.hom ≫ j)
    (by rw [Category.assoc, hj]; exact hc.1.w)
  have hψ : ψ ≫ pullback.fst Y.t.G.hom U.ι = Y.m.φ := gp.1.lift_fst _ _ _
  have gq : IsGrpPullback Y.oF.t.G G j ψ :=
    gp.cancel (by rw [hψ, hj]; exact hc) (gp.1.lift_snd _ _ _)
  obtain ⟨s, hs₁, hs₂⟩ := exists_section_of_pow_eq_one hT j G n hn' _ (pushHom gq _ σ)
    (by rw [← map_pow, hσ, map_one]) (𝟙 _) ((Category.id_comp _).trans (Category.id_comp _))
  refine ⟨s ≫ pullback.fst Y.t.G.hom U.ι, ?_, fun j' hj' => ?_⟩
  · rw [Category.assoc, gp.1.w, reassoc_of% hs₁]
  · obtain rfl : j' = j := by rw [← cancel_mono U.ι, hj, hj']
    rw [reassoc_of% hs₂, ← hψ]
    exact Category.assoc _ _ _

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.LbIsoCubeLBOfWeilIsAdjoint
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.AdjointOfPairing

open ReciprocityTheory.ChartRestriction.G.Out CommutatorPairing DescentPairing

theorem lbIso_of_gen {X Y : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
    (t : LB.Gen (LB.LinComb L (Sum.elim φ' φ) (Sum.elim ε' (fun k => - ε k)))) (ht : t.IsGen) :
    LBIso (LB.LinComb L φ ε) (LB.LinComb L φ' ε') := by
  have le : ∀ p : (K' → L.ι) × (K → L.ι), LB.wchart L φ' p.1 ⊓ LB.wchart L φ p.2 ≤
      LB.wchart L (Sum.elim φ' φ) (Sum.elim p.1 p.2) := fun p y hy => Set.mem_iInter.2 fun k => by
    rcases k with k | k
    exacts [Set.mem_iInter.1 hy.1 k, Set.mem_iInter.1 hy.2 k]
  refine gen_chartPull (A' := LB.div (LB.LinComb L φ' ε') (LB.LinComb L φ ε)) (h := 𝟙 Y)
    (A := LB.LinComb L (Sum.elim φ' φ) (Sum.elim ε' (fun k => - ε k)))
    ⟨fun p => Sum.elim p.1 p.2, le, fun y p q hp hq => ?_⟩ t ht
  refine (gm_div (LB.LinComb L φ ε) (LB.LinComb L φ' ε') (𝟙 Y) y p q ⟨hp, hq⟩).trans
    (Eq.trans ?_ (gm_linComb L _ _ (𝟙 Y) y _ _ (le p hp) (le q hq)).symm)
  refine (congrArg₂ (fun a b => a * b⁻¹) (gm_linComb L φ' ε' (𝟙 Y) y _ _ hp.1 hq.1)
    (gm_linComb L φ ε (𝟙 Y) y _ _ hp.2 hq.2)).trans (Eq.trans ?_ (Fintype.prod_sum_type _).symm)
  simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib]
  rfl

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A]

theorem exists_gen_pairing (hG : GlobalFnsSt) (hA : IsAbelianScheme A) {L : RigLB A} (cb : CubicalStr A L)
    {T : Over S} (p₀ : T.left) (hT : ∀ p : T.left, p = p₀) (n : ℕ) (x : T ⟶ A) (hx : x ^ n = 1) :
    ∃ u : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(mulT A T n ≫ translPt A x).left, (snd T A ^ n).left] ![1, -1]),
      u.IsGen ∧ ∀ (y : T ⟶ A) (c : Γ(T.left, ⊤)ˣ), y ^ n = 1 → WeilIs A L.L n x y c →
        ∀ (Z : Over S) (t : Z ⟶ T) (w : Z ⟶ A) (z : Z.left) (J), Good L.L z J →
          val u (lift t ((t ≫ y) * w)).left z J = val u (lift t w).left z J * gm t.left z ⊤ c := by
  obtain ⟨θx, rfl, -⟩ := exists_theta cb p₀ hT n x hx
  obtain ⟨u, hu, vu⟩ := exists_triv cb p₀ hT n θx
  refine ⟨u, hu, fun y c hy hc Z t w z J hJ => ?_⟩
  obtain ⟨θy, rfl, vy⟩ := exists_theta cb p₀ hT n y hy
  have hcm := (commIsOf_iff L.isLB θx θy c).1 ((GlobalLift.weilIs_iff_commIsOf hG hA L.isLB θx θy c).1 hc)
  obtain ⟨s, hs⟩ := vu _ t z J hJ
  obtain ⟨s', hs'⟩ := vy _ t z J hJ
  have k₁ := hcm _ t w z J hJ
  have k₂ := cubN_transl (isCub_cubV cb hJ) n (t ≫ θy.pt) w (t ≫ θx.pt)
    ((map_pow (preHom t) θy.pt n).symm.trans (by rw [hy]; exact map_one _))
  refine (hs _).trans (Eq.trans ?_ (congrArg₂ (· * ·) (hs _) k₁.symm).symm)
  have t₁ := hs' w
  have t₂ := hs' ((t ≫ θx.pt) * w)
  apply Additive.ofMul.injective
  have E := fun {p q : (Z.left.presheaf.stalk z)ˣ} (e : p = q) => congrArg Additive.ofMul e
  have a₁ := E t₁; have a₂ := E t₂; have a₃ := E k₂
  simp only [commVal, ofMul_mul, ofMul_inv] at a₁ a₂ a₃ ⊢
  linear_combination (norm := abel) a₃ + a₁ - a₂


omit [IsCommMonObj A] in
theorem prod_mulT {T Z : Over S} (n : ℕ) (x : T ⟶ A) (t : Z ⟶ T) (w : Z ⟶ A) {U : Type} [CommGroup U]
    (h : (Z.left ⟶ A.left) → U) :
    ∏ i : Fin 2, h ((lift t w).left ≫ ![(mulT A T n ≫ translPt A x).left, (snd T A ^ n).left] i) ^ ![(1 : ℤ), -1] i =
      h ((t ≫ x) * w ^ n).left * (h (w ^ n).left)⁻¹ := by
  rw [Fin.prod_univ_two]
  show h (lift t w ≫ mulT A T n ≫ translPt A x).left ^ (1 : ℤ) * h (lift t w ≫ snd T A ^ n).left ^ (-1 : ℤ) = _
  rw [mulT, comp_lift_assoc, lift_fst, lift_translPt, MonObj.comp_pow, lift_snd, zpow_one, zpow_neg_one]

theorem exists_gen_of_formEq_zero {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K]
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} (h : ∀ (U : Type) [CommGroup U] (h : (Y ⟶ X) → U), ∏ k, h (φ k) ^ ε k = 1) :
    ∃ t : LB.Gen (LB.LinComb L φ ε), t.IsGen := by
  obtain ⟨t, ht, -⟩ := exists_gen hL (φ' := φ) (ε' := ε) (fun U _ g => (Fintype.prod_empty _).trans (h U g).symm)
    (LB.oneGen L (Y := Y)) (fun i j => (map_one _).trans
      ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm)
  exact ⟨t, ht⟩

theorem exists_gen_fibre (hl : Laws) {k : Type} [Field k] [IsAlgClosed k] (P : PolAV (Sp k)) (a a' : P.A ⟶ P.A)
    [IsMonHom a] [IsMonHom a'] (n : ℕ) (hn : (n : k) ≠ 0) (x : 𝟙_ (Over (Sp k)) ⟶ P.A) (hx : x ^ n = 1)
    (H : ∀ (y : 𝟙_ (Over (Sp k)) ⟶ P.A) (c : Γ((𝟙_ (Over (Sp k))).left, ⊤)ˣ), y ^ n = 1 →
      WeilIs P.A P.L n (x ≫ a) y c → WeilIs P.A P.L n x (y ≫ a') c) :
    ∃ t : LB.Gen (LB.LinComb P.L
      (fun i => (lift (toUnit P.A ≫ x) (𝟙 P.A)).left ≫ rosatiφ P.A a a' i) rosatiε), t.IsGen := by
  have := P.isAb.comm
  obtain ⟨rig, hrig⟩ := P.rigid
  let L : RigLB P.A := ⟨P.L, rig, P.isLB, hrig⟩
  obtain ⟨⟨cb⟩, -⟩ := hl.cube _ P L rfl
  let p₀ : (𝟙_ (Over (Sp k))).left := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum k)
  have hT : ∀ p : (𝟙_ (Over (Sp k))).left, p = p₀ := fun p => Subsingleton.elim (α := PrimeSpectrum k) p p₀
  have hxa : (x ≫ a) ^ n = 1 := by rw [← MonObj.pow_comp, hx, MonObj.one_comp]
  obtain ⟨u₁, hu₁, v₁⟩ := exists_gen_pairing hl.globalFns P.isAb cb p₀ hT n (x ≫ a) hxa
  obtain ⟨u₂, hu₂, v₂⟩ := exists_gen_pairing hl.globalFns P.isAb cb p₀ hT n x hx
  obtain ⟨σ, hσ⟩ := exists_frame P.isLB (K := Fin 2) ![(x ≫ a).left, x.left] ![-1, 1] p₀ hT
  obtain ⟨u, hu, vu⟩ := exists_gen P.isLB
    (φ' := fun i => (mulA P.A n).left ≫ (lift (toUnit P.A ≫ x) (𝟙 P.A)).left ≫ rosatiφ P.A a a' i) (ε' := rosatiε)
    (fun U _ h => by
      have e : ∀ i, (mulA P.A n).left ≫ (lift (toUnit P.A ≫ x) (𝟙 P.A)).left ≫ rosatiφ P.A a a' i =
          (lift (toUnit P.A ≫ x) (𝟙 P.A ^ n)).left ≫ rosatiφ P.A a a' i := fun i => by
        rw [← Category.assoc, ← Over.comp_left, comp_lift, comp_toUnit_assoc, Category.comp_id]
      have e' : (𝟙 P.A ^ n) ≫ a' = a' ^ n := by rw [MonObj.pow_comp, Category.id_comp]
      have f : ∏ i : Fin 2, h ((toUnit P.A).left ≫ ![(x ≫ a).left, x.left] i) ^ ![(-1 : ℤ), 1] i =
          (h (toUnit P.A ≫ x ≫ a).left)⁻¹ * h (toUnit P.A ≫ x).left := by
        rw [Fin.prod_univ_two]
        exact congrArg₂ (· * ·) (zpow_neg_one _) (zpow_one _)
      refine (DVR.prod_sum₂ (K := Fin 2 ⊕ Fin 2) (K' := Fin 2) (U := U) _
        (DVR.prod_sum₂ (K := Fin 2) (K' := Fin 2) (U := U) _ (prod_mulT n (x ≫ a) (toUnit P.A) (𝟙 P.A) h)
        (DVR.prod_neg _ _ (prod_mulT n x (toUnit P.A) a' h))) f).trans ?_
      simp only [e]
      rw [prod_ros, e', Category.assoc]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel)
    (LB.mulGen P.L _ _ _ _ (LB.mulGen P.L _ _ _ _ (LB.pullGen P.L _ _ u₁ (lift (toUnit P.A) (𝟙 P.A)).left)
      (LB.invGen P.L _ _ (LB.pullGen P.L _ _ u₂ (lift (toUnit P.A) a').left))) (LB.pullGen P.L _ _ σ (toUnit P.A).left))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hu₁ _)
      (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hu₂ _))) (DVR.pullGen_isGen _ _ _ _ hσ _))
  have vw : ∀ (w : P.A ⟶ P.A) (z : P.A.left) (J), Good P.L z J → val u w.left z J =
      val u₁ (lift (toUnit P.A) w).left z J * (val u₂ (lift (toUnit P.A) (w ≫ a')).left z J)⁻¹ *
        val σ (toUnit P.A).left z J := fun w z J hJ => by
    refine (vu _ _ z J hJ).trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) ((val_pull hJ _ _ _).trans ?_) ((val_inv _ _).trans (congrArg (·⁻¹)
        ((val_pull hJ _ _ _).trans ?_))))) ((val_pull hJ _ _ _).trans ?_)))
    · rw [← Over.comp_left, comp_lift, comp_toUnit, Category.comp_id]
    · rw [← Over.comp_left, comp_lift, comp_toUnit]
    · rw [← Over.comp_left, comp_toUnit]
  refine exists_isGen_of_invariant P.isLB _ _ (mulA P.A n).left
    (I := {y : 𝟙_ (Over (Sp k)) ⟶ P.A // y ^ n = 1}) (fun y => ((toUnit P.A ≫ y.1) * 𝟙 P.A).left)
    (fun y => by
      rw [← Over.comp_left, GoodPoint.comp_mulA, mul_pow, ← MonObj.comp_pow, y.2, MonObj.comp_one, _root_.one_mul])
    (fun U f hf => torsion_invariant_descends (fun S _ Q m hm =>
      ⟨(hl.mulN S Q m hm).1, (hl.mulN S Q m hm).2.1, (hl.mulN S Q m hm).2.2.1, (hl.mulN S Q m hm).2.2.2.1⟩)
      k P n hn U f fun y hy => hf ⟨y, hy⟩) _ (fun _ => rfl) u hu fun y z J hJ => ?_
  obtain ⟨c, hc, -⟩ := (hl.weil _ P n _).1 (x ≫ a) y.1 hxa y.2
  have hya : (y.1 ≫ a') ^ n = 1 := by rw [← MonObj.pow_comp, y.2, MonObj.one_comp]
  refine (vw _ z J hJ).trans (Eq.trans ?_ (vw (𝟙 P.A) z J hJ).symm)
  rw [v₁ y.1 c y.2 hc _ _ _ z J hJ, MonObj.mul_comp, Category.assoc, v₂ _ c hya (H y.1 c y.2 hc) _ _ _ z J hJ,
    mul_inv, _root_.mul_mul_mul_comm, mul_inv_cancel, _root_.mul_one]

end GlobalTheory.AdjointOfPairing

namespace GlobalTheory

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfCommonGenericFibre
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory

theorem isAbelianScheme_of_common_generic_fibre
    {V K : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K]
    (B G : Over (Sp V)) [GrpObj B] [GrpObj G] (hB : IsAbelianScheme B) (hG : IsSemiAbelian G)
    (hext : ∀ f : (Over.pullback (spMap (algebraMap V K))).obj B ⟶ (Over.pullback (spMap (algebraMap V K))).obj G,
      IsMonHom f → ∃ F : B ⟶ G, (Over.pullback (spMap (algebraMap V K))).map F = f)
    (A : Over (Sp K)) [GrpObj A] {φ₁ : A.left ⟶ B.left} {φ₂ : A.left ⟶ G.left}
    (h₁ : IsGrpPullback A B (spMap (algebraMap V K)) φ₁) (h₂ : IsGrpPullback A G (spMap (algebraMap V K)) φ₂) :
    IsAbelianScheme G := by
  obtain ⟨e, he, -⟩ := grpPullback_iso (isGrpPullback_pullback B (spMap (algebraMap V K))) h₁
  obtain ⟨e', he', -⟩ := grpPullback_iso h₂ (isGrpPullback_pullback G (spMap (algebraMap V K)))
  obtain ⟨F, hF⟩ := hext (e.hom ≫ e'.hom) inferInstance
  refine isAbelianScheme_of_generically_surjective V K B G hB hG F ?_
  rintro x ⟨k, hk⟩
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback x k hk.symm
  have hsq : ((Over.pullback (spMap (algebraMap V K))).map F).left ≫ pullback.fst G.hom (spMap (algebraMap V K)) =
      pullback.fst B.hom (spMap (algebraMap V K)) ≫ F.left := by
    simp
  rw [hF] at hsq
  have hid : (e ≪≫ e').inv.left ≫ (e.hom ≫ e'.hom).left = 𝟙 _ := by
    rw [← Over.comp_left, ← Iso.trans_hom, Iso.inv_hom_id, Over.id_left]
  refine ⟨pullback.fst B.hom (spMap (algebraMap V K)) ((e ≪≫ e').inv.left z), ?_⟩
  calc F.left (pullback.fst B.hom (spMap (algebraMap V K)) ((e ≪≫ e').inv.left z))
      = ((e ≪≫ e').inv.left ≫ pullback.fst B.hom (spMap (algebraMap V K)) ≫ F.left) z := rfl
    _ = ((e ≪≫ e').inv.left ≫ (e.hom ≫ e'.hom).left ≫ pullback.fst G.hom (spMap (algebraMap V K))) z := by rw [hsq]
    _ = pullback.fst G.hom (spMap (algebraMap V K)) z := by rw [← Category.assoc, hid, Category.id_comp]
    _ = x := hz

theorem goodRedExt_of_isDiscreteValuationRing :
    (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K], Y.GoodRedExt V K := by
  intro hext E _ _ _ H D l Xo c O _ β Y V K _ _ _ _ _ _ b y hy hex
  obtain ⟨𝒜, _, 𝓛, A, _, φ₁, φ₂, h𝒜, -, -, hp1, hp2, -⟩ := hex
  obtain ⟨y', t, m, hy's, hy'j, hab⟩ := GlobalTheory.model_point_extends E H D l Xo c O β Y V K b y hy
  refine ⟨y', hy's, hy'j, hab ?_⟩
  have hm := m.cart
  have hc := IsGrpPullback.comp hp2 Y.m.cart
  have hw : (φ₂ ≫ Y.m.cm.F) ≫ Y.t.G.hom = (A.hom ≫ spMap (algebraMap V K)) ≫ y' := by
    rw [hc.1.w, Category.assoc, hy'j]; rfl
  have h2 : IsGrpPullback A t.G (spMap (algebraMap V K)) (hm.1.lift _ _ hw) :=
    IsGrpPullback.cancel hm (hc.congr (by rw [hy'j]; rfl) (hm.1.lift_fst _ _ hw).symm) (hm.1.lift_snd _ _ hw)
  exact isAbelianScheme_of_common_generic_fibre 𝒜 t.G h𝒜 t.semi
    (fun f hf => (hext V K 𝒜 t.G (isSemiAbelian_of_isAbelianScheme 𝒜 h𝒜) t.semi f hf).exists.imp fun _ h => h.2)
    A hp1 h2

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleOfCubeDivGeneratedField
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleOfCubeDivGeneratedField
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem IsAmpleLB.of_pow_div_generated {X : Scheme.{0}} {L N : LB X} (hL : IsAmpleLB L) (hN : N.IsLB) {m : ℕ}
    (hm : 1 ≤ m) {J : Type} (u : J → (lbPow (LB.div N L) m).Sec) (hu : ⨆ i, Out.nonzeroLocus (u i) = ⊤) :
    IsAmpleLB N := by
  refine ⟨hN, hL.compactSpace, fun x => ?_⟩
  obtain ⟨n, hn, s, hs, ha⟩ := hL.exists_affine x
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hu.ge (Set.mem_univ x))
  have hD := LB.isLB_div hN hL.isLB
  obtain ⟨v, hv⟩ := exists_sec_pow_nonzeroLocus_eq_inf hL.isLB hD hN (lbIso_refl hD) (secPow s m)
    (secCast (Nat.mul_comm m n) (secPow (u i) n))
  rw [nonzeroLocus_secCast, nonzeroLocus_secPow _ hn, nonzeroLocus_secPow _ hm] at hv
  exact ⟨n * m, Nat.mul_pos hn hm, v, hv.ge ⟨hi, hs⟩,
    hv ▸ isAffineOpen_nonzeroLocus_inf (isLB_lbPow hD m) (u i) ha⟩

theorem relAmple_of_cube_div_generated : ∀ (K : Type) [Field K] (A : Over (Sp K)) (L M : LB A.left) (a r : ℕ) (u : Fin r → (lbPow (LB.div (lbPow M a) L) 3).Sec), IsProper A.hom → L.IsLB → M.IsLB → 1 ≤ a → Out.RelAmple A L → ⨆ i, Out.nonzeroLocus (u i) = ⊤ → Out.RelAmple A M := by
  intro K _ A L M a r u hA hL hM ha hamp hu
  have h₁ := (relAmple_iff_isAmpleLB_of_isAffine A hL).1 hamp
  exact (relAmple_iff_isAmpleLB_of_isAffine A hM).2 ((isAmpleLB_pow_iff hM ha).1
    (h₁.of_pow_div_generated (isLB_lbPow hM a) (by norm_num) u hu))

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleOfCubeDivGeneratedFieldStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
theorem _root_.GlobalTheory.T.relAmple_of_cube_div_generated_field : ∀ (K : Type) [Field K] (A : Over (Sp K)) (L M : LB A.left) (a r : ℕ) (u : Fin r → (lbPow (LB.div (lbPow M a) L) 3).Sec), IsProper A.hom → L.IsLB → M.IsLB → 1 ≤ a → Out.RelAmple A L → ⨆ i, Out.nonzeroLocus (u i) = ⊤ → Out.RelAmple A M := by
  first | exact @GlobalTheory.relAmple_of_cube_div_generated | exact GlobalTheory.relAmple_of_cube_div_generated | (intros; apply GlobalTheory.relAmple_of_cube_div_generated <;> assumption)
end
end
