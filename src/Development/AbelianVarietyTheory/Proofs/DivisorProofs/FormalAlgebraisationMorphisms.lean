module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsProjectiveAlgebraisationFormalEmbeddingCom
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChowLemmaProjectiveModification
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraisationOfProperModificationNoetherianStep
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoOfProperIsIsoOnReductions

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsReductionClosedSubschemeIffIdealEq
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsReductionClosedSubschemeIffIdealEq
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

namespace GlobalTheory.FormalAlg

theorem baseIdeal_comp_eq_comap (R : Type) [CommRing R] (J : Ideal R) {W T : Scheme.{0}}
    (f : W ⟶ Spec (CommRingCat.of R)) (i : T ⟶ W) :
    baseIdeal (i ≫ f) J = (baseIdeal f J).comap i := by
  set m := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))
  obtain ⟨h0c, h0k, -⟩ := GlobalTheory.T.baseChange_quotient_closedImmersion_idealSheaf R J W _ f (pullback.fst f m) (pullback.snd f m)
    (IsPullback.of_hasPullback f m)
  obtain ⟨-, h1k, -⟩ := GlobalTheory.T.baseChange_quotient_closedImmersion_idealSheaf R J T _ (i ≫ f) (pullback.fst (i ≫ f) m) (pullback.snd (i ≫ f) m)
    (IsPullback.of_hasPullback (i ≫ f) m)
  haveI := h0c
  rw [← h1k, ← h0k, ← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion,
    ← pullbackRightPullbackFstIso_hom_fst f m i, Scheme.Hom.ker_comp_of_isIso]

theorem map_baseIdeal_comp (R : Type) [CommRing R] (J : Ideal R) {W T : Scheme.{0}}
    (f : W ⟶ Spec (CommRingCat.of R)) (i : T ⟶ W) (hi : IsClosedImmersion i) :
    (baseIdeal (i ≫ f) J).map i = i.ker ⊔ baseIdeal f J := by
  have h := (GlobalTheory.T.idealSheafData_map_sup_comap_closedImmersion T W i hi ⊥ (baseIdeal f J)).1
  rw [bot_sup_eq, Scheme.IdealSheafData.map_bot] at h
  rw [baseIdeal_comp_eq_comap, h]

theorem reduces_iff_ker_eq : ∀ (R : Type) [CommRing R] (J : Ideal R) (W T Y : Scheme.{0}) (f : W ⟶ Spec (CommRingCat.of R)) (i : T ⟶ W) (j : Y ⟶ W) (q : Y ⟶ Spec (CommRingCat.of (R ⧸ J))), IsClosedImmersion i → IsClosedImmersion j → j ≫ f = q ≫ (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) → ((∃ b : Y ⟶ T, b ≫ i = j ∧ IsPullback b q (i ≫ f) (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))) ↔ i.ker ⊔ baseIdeal f J = j.ker) := by
  intro R _ J W T Y f i j q hi hj hq
  haveI := hi
  haveI := hj
  constructor
  · rintro ⟨b, hb, hpb⟩
    obtain ⟨-, hbk, -⟩ := GlobalTheory.T.baseChange_quotient_closedImmersion_idealSheaf R J T Y (i ≫ f) b q hpb
    rw [← hb, Scheme.Hom.ker_comp, hbk, map_baseIdeal_comp R J f i hi]
  · intro hk
    set m := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))
    obtain ⟨h1c, h1k, -⟩ := GlobalTheory.T.baseChange_quotient_closedImmersion_idealSheaf R J T _ (i ≫ f) (pullback.fst (i ≫ f) m)
      (pullback.snd (i ≫ f) m) (IsPullback.of_hasPullback (i ≫ f) m)
    haveI := h1c
    have hker : (pullback.fst (i ≫ f) m ≫ i).ker = j.ker := by
      rw [Scheme.Hom.ker_comp, h1k, map_baseIdeal_comp R J f i hi, hk]
    let e := IsClosedImmersion.lift (pullback.fst (i ≫ f) m ≫ i) j hker.le
    have he : e ≫ pullback.fst (i ≫ f) m ≫ i = j := IsClosedImmersion.lift_fac _ _ _
    haveI : IsIso e := IsClosedImmersion.isIso_of_ker_eq j _ e he hker.symm
    haveI : IsClosedImmersion m := IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    have hmono : Mono m := inferInstance
    have hqe : e ≫ pullback.snd (i ≫ f) m = q := by
      rw [← cancel_mono m, ← hq, Category.assoc, ← pullback.condition, ← he]
      simp only [Category.assoc]
    refine ⟨e ≫ pullback.fst (i ≫ f) m, by rw [Category.assoc, he], ?_⟩
    rw [← hqe]
    exact IsPullback.of_iso (IsPullback.of_hasPullback (i ≫ f) m) (asIso e).symm (Iso.refl _)
      (Iso.refl _) (Iso.refl _) (by simp) (by simp) (by simp) (by simp)

end GlobalTheory.FormalAlg
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsReductionClosedSubschemeIffIdealEqStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isReduction_closedSubscheme_iff_ideal_eq : ∀ (R : Type) [CommRing R] (J : Ideal R) (W T Y : Scheme.{0}) (f : W ⟶ Spec (CommRingCat.of R)) (i : T ⟶ W) (j : Y ⟶ W) (q : Y ⟶ Spec (CommRingCat.of (R ⧸ J))), IsClosedImmersion i → IsClosedImmersion j → j ≫ f = q ≫ (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) → ((∃ b : Y ⟶ T, b ≫ i = j ∧ IsPullback b q (i ≫ f) (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))) ↔ i.ker ⊔ baseIdeal f J = j.ker) := by
  first | exact @GlobalTheory.FormalAlg.reduces_iff_ker_eq | exact GlobalTheory.FormalAlg.reduces_iff_ker_eq | (intros; apply GlobalTheory.FormalAlg.reduces_iff_ker_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompatibleReductionSystemMapImmersion
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompatibleReductionSystemMapImmersion
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FormalAlg

theorem isClosedImmersion_subschemeι_comp {R : Type} [CommRing R] {W W' : Scheme.{0}}
    (f : W ⟶ Spec (CommRingCat.of R)) (π : W' ⟶ W) [IsSeparated f] [IsImmersion π]
    (T : W'.IdealSheafData) [IsProper (T.subschemeι ≫ π ≫ f)] :
    IsClosedImmersion (T.subschemeι ≫ π) := by
  haveI : IsProper ((T.subschemeι ≫ π) ≫ f) := by rw [Category.assoc]; infer_instance
  haveI : IsProper (T.subschemeι ≫ π) := IsProper.of_comp _ f
  exact IsClosedImmersion.of_isPreimmersion _ (T.subschemeι ≫ π).isClosedMap.isClosed_range

theorem isProper_ker_subschemeι_comp {X Y S : Scheme.{0}} (g : X ⟶ Y) [IsClosedImmersion g]
    (f : Y ⟶ S) [IsProper (g ≫ f)] : IsProper (g.ker.subschemeι ≫ f) := by
  change IsProper (g.imageι ≫ f)
  have hg : g.imageι = inv g.toImage ≫ g := (IsIso.eq_inv_comp _).2 g.toImage_imageι
  rw [hg, Category.assoc]
  infer_instance

theorem mapSystem : ∀ (R : Type) [CommRing R] (I : Ideal R) (W W' : Scheme.{0})
    (f : W ⟶ Spec (CommRingCat.of R)) (π : W' ⟶ W), IsSeparated f → IsImmersion π →
    ∀ t : ℕ → W'.IdealSheafData, IsSystem (π ≫ f) I t → (∀ e, IsProper ((t e).subschemeι ≫ π ≫ f)) →
    IsSystem f I (fun e => (t e).map π) ∧ (∀ e, IsProper (((t e).map π).subschemeι ≫ f)) ∧
      ∀ e, ((t e).map π).comap π = t e := by
  intro R _ I W W' f π hf hπ t ht hp
  have hci : ∀ e, IsClosedImmersion ((t e).subschemeι ≫ π) := fun e =>
    haveI := hp e; isClosedImmersion_subschemeι_comp f π (t e)
  refine ⟨fun e => ?_, fun e => ?_, fun e => ?_⟩
  ·
    show (t e).map π = (t (e + 1)).map π ⊔ baseIdeal f (I ^ (e + 1))
    have hle : t (e + 1) ≤ t e := by rw [ht e]; exact le_sup_left
    have hι : IsClosedImmersion (t (e + 1)).subschemeι := inferInstance
    have h1 : ((t e).comap (t (e + 1)).subschemeι).map (t (e + 1)).subschemeι = t e := by
      have := (GlobalTheory.T.idealSheafData_map_sup_comap_closedImmersion _ _ _ hι ⊥ (t e)).1
      rw [bot_sup_eq, Scheme.IdealSheafData.map_bot, Scheme.IdealSheafData.ker_subschemeι,
        sup_eq_right.2 hle] at this
      exact this
    have hbot : (t (e + 1)).comap (t (e + 1)).subschemeι = ⊥ := by
      have := (GlobalTheory.T.idealSheafData_map_sup_comap_closedImmersion _ _ _ hι ⊥ ⊥).2
      rwa [Scheme.IdealSheafData.map_bot, Scheme.IdealSheafData.ker_subschemeι] at this
    have h2 : (t e).comap (t (e + 1)).subschemeι =
        (baseIdeal f (I ^ (e + 1))).comap ((t (e + 1)).subschemeι ≫ π) := by
      conv_lhs => rw [ht e]
      rw [Scheme.IdealSheafData.comap_sup, hbot, bot_sup_eq, GlobalTheory.T.baseIdealSheafOfIdeal_comap_specMap_support.1, GlobalTheory.T.baseIdealSheafOfIdeal_comap_specMap_support.1,
        Category.assoc]
    have h3 := (GlobalTheory.T.idealSheafData_map_sup_comap_closedImmersion _ _ _ (hci (e + 1)) ⊥ (baseIdeal f (I ^ (e + 1)))).1
    rw [bot_sup_eq, Scheme.IdealSheafData.map_bot] at h3
    calc (t e).map π = (((t e).comap (t (e + 1)).subschemeι).map (t (e + 1)).subschemeι).map π := by
          rw [h1]
      _ = ((t e).comap (t (e + 1)).subschemeι).map ((t (e + 1)).subschemeι ≫ π) := by
          rw [Scheme.IdealSheafData.map_comp]
      _ = ((t (e + 1)).subschemeι ≫ π).ker ⊔ baseIdeal f (I ^ (e + 1)) := by rw [h2, h3]
      _ = (t (e + 1)).map π ⊔ baseIdeal f (I ^ (e + 1)) := rfl
  ·
    haveI := hci e
    haveI : IsProper (((t e).subschemeι ≫ π) ≫ f) := by rw [Category.assoc]; exact hp e
    exact isProper_ker_subschemeι_comp ((t e).subschemeι ≫ π) f
  ·
    haveI := hci e
    refine le_antisymm (Scheme.IdealSheafData.comap_map_le _ _) ?_
    show t e ≤ (((t e).subschemeι ≫ π).ker).comap π
    rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]
    have h : pullback.fst π ((t e).subschemeι ≫ π) = pullback.snd _ _ ≫ (t e).subschemeι := by
      rw [← cancel_mono π, pullback.condition, Category.assoc]
    rw [h]
    conv_lhs => rw [← (t e).ker_subschemeι]
    exact Scheme.Hom.le_ker_comp _ _

end GlobalTheory.FormalAlg
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompatibleReductionSystemMapImmersionStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compatibleReductionSystem_map_immersion : ∀ (R : Type) [CommRing R] (I : Ideal R) (W W' : Scheme.{0}) (f : W ⟶ Spec (CommRingCat.of R)) (π : W' ⟶ W), IsSeparated f → IsImmersion π → ∀ t : ℕ → W'.IdealSheafData, IsSystem (π ≫ f) I t → (∀ e, IsProper ((t e).subschemeι ≫ π ≫ f)) → IsSystem f I (fun e => (t e).map π) ∧ (∀ e, IsProper (((t e).map π).subschemeι ≫ f)) ∧ ∀ e, ((t e).map π).comap π = t e := by
  first | exact @GlobalTheory.FormalAlg.mapSystem | exact GlobalTheory.FormalAlg.mapSystem | (intros; apply GlobalTheory.FormalAlg.mapSystem <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrothendieckExistenceClosedSubschemesSeparated
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraiseOfIsImmersionProjectiveCompleteNoeth
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalClosedSubschemesAlgebraiseOfProjective
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompatibleReductionSystemGivesThickeningTower
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompatibleReductionSystemGivesThickeningTower
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

namespace GlobalTheory.FormalAlg

theorem isSystem_tower : ∀ (R : Type) [CommRing R] (I : Ideal R) (W : Scheme.{0}) (f : W ⟶ Spec (CommRingCat.of R))
    (t : ℕ → W.IdealSheafData), IsSystem f I t →
    ∃ (q : ∀ e, (t e).subscheme ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))
      (β : ∀ e, (t e).subscheme ⟶ (t (e + 1)).subscheme),
      (∀ e, (t e).subschemeι ≫ f = q e ≫ thick R I e) ∧
      (∀ e, β e ≫ (t (e + 1)).subschemeι = (t e).subschemeι) ∧
      ∀ e, IsPullback (β e) (q e) (q (e + 1)) (thickTrans R I e) := by
  intro R _ I W f t ht
  have hci : ∀ e, IsClosedImmersion (thick R I e) := fun e =>
    IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (e + 1))))
      Ideal.Quotient.mk_surjective
  have hmono : ∀ e, Mono (thick R I e) := fun e => by haveI := hci e; infer_instance
  have hfst : ∀ e, (pullback.fst f (thick R I e)).ker = baseIdeal f (I ^ (e + 1)) := by
    intro e
    haveI := hci e
    have h := (GlobalTheory.T.isReduction_closedSubscheme_iff_ideal_eq R (I ^ (e + 1)) W W (pullback f (thick R I e)) f (𝟙 W)
      (pullback.fst f (thick R I e)) (pullback.snd f (thick R I e)) inferInstance inferInstance
      pullback.condition).1
      ⟨pullback.fst f (thick R I e), Category.comp_id _, by
        simpa using IsPullback.of_hasPullback f (thick R I e)⟩
    simpa using h.symm
  have hle : ∀ e, (pullback.fst f (thick R I e)).ker ≤ (t e).subschemeι.ker := fun e => by
    rw [hfst, Scheme.IdealSheafData.ker_subschemeι]
    exact ht.baseIdeal_le e
  let q : ∀ e, (t e).subscheme ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1))) := fun e =>
    haveI := hci e
    IsClosedImmersion.lift (pullback.fst f (thick R I e)) (t e).subschemeι (hle e) ≫ pullback.snd _ _
  have hq : ∀ e, (t e).subschemeι ≫ f = q e ≫ thick R I e := fun e => by
    haveI := hci e
    simp only [q, Category.assoc, ← pullback.condition]
    rw [← Category.assoc, IsClosedImmersion.lift_fac]
  clear_value q
  have hb : ∀ e, ∃ b : (t e).subscheme ⟶ (t (e + 1)).subscheme, b ≫ (t (e + 1)).subschemeι = (t e).subschemeι ∧
      IsPullback b (q e) ((t (e + 1)).subschemeι ≫ f) (thick R I e) := fun e =>
    (GlobalTheory.T.isReduction_closedSubscheme_iff_ideal_eq R (I ^ (e + 1)) W _ _ f (t (e + 1)).subschemeι (t e).subschemeι (q e)
      inferInstance inferInstance (hq e)).2
      (by rw [Scheme.IdealSheafData.ker_subschemeι, Scheme.IdealSheafData.ker_subschemeι]; exact (ht e).symm)
  choose β hβ using hb
  refine ⟨q, β, hq, fun e => (hβ e).1, fun e => ?_⟩
  have hbot : IsPullback (thickTrans R I e) (𝟙 _) (thick R I (e + 1)) (thick R I e) := by
    haveI := hmono (e + 1)
    refine IsPullback.of_isLimit' ⟨by simp [thickTrans_comp]⟩ ?_
    refine PullbackCone.IsLimit.mk _ (fun s => s.snd) (fun s => ?_) (fun s => by simp)
      (fun s m _ h2 => by simpa using h2)
    rw [← cancel_mono (thick R I (e + 1)), Category.assoc, thickTrans_comp]
    exact s.condition.symm
  have hcomm : β e ≫ q (e + 1) = q e ≫ thickTrans R I e := by
    haveI := hmono (e + 1)
    rw [← cancel_mono (thick R I (e + 1))]
    calc (β e ≫ q (e + 1)) ≫ thick R I (e + 1) = β e ≫ (t (e + 1)).subschemeι ≫ f := by
          rw [Category.assoc, hq]
      _ = (t e).subschemeι ≫ f := by rw [← Category.assoc, (hβ e).1]
      _ = q e ≫ thick R I e := hq e
      _ = (q e ≫ thickTrans R I e) ≫ thick R I (e + 1) := by rw [Category.assoc, thickTrans_comp]
  refine IsPullback.of_bot ?_ hcomm hbot
  rw [Category.comp_id, ← hq]
  exact (hβ e).2

end GlobalTheory.FormalAlg
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompatibleReductionSystemGivesThickeningTowerStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compatibleReductionSystem_gives_thickening_tower : ∀ (R : Type) [CommRing R] (I : Ideal R) (W : Scheme.{0}) (f : W ⟶ Spec (CommRingCat.of R)) (t : ℕ → W.IdealSheafData), IsSystem f I t → ∃ (q : ∀ e, (t e).subscheme ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) (β : ∀ e, (t e).subscheme ⟶ (t (e + 1)).subscheme), (∀ e, (t e).subschemeι ≫ f = q e ≫ thick R I e) ∧ (∀ e, β e ≫ (t (e + 1)).subschemeι = (t e).subschemeι) ∧ ∀ e, IsPullback (β e) (q e) (q (e + 1)) (thickTrans R I e) := by
  first | exact @GlobalTheory.FormalAlg.isSystem_tower | exact GlobalTheory.FormalAlg.isSystem_tower | (intros; apply GlobalTheory.FormalAlg.isSystem_tower <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedImmersionOfVeryAmpleSectionsCompatible
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedImmersionOfVeryAmpleSectionsCompatible
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw

namespace GlobalTheory.Div

theorem resG_eq_inv_mul_appLE {X X' : Scheme.{0}} {H : LB X} {H' : LB X'} {φ : X' ⟶ X}
    (w : LB.Iso H' (H.pull φ)) (k : H.ι) (k' : H'.ι) (a : Γ(X, H.U k)) (b : Γ(X', H'.U k'))
    (h : ∀ z, φ z ∈ H.U k → z ∈ H'.U k' →
      gs φ z _ a = (Geo.Tor.gw w (𝟙 _) z k k').val * gs (𝟙 _) z _ b) :
    resG X' (inf_le_right : (H.pull φ).U (fun _ => k) ⊓ H'.U k' ≤ H'.U k') b =
      ((@id (Γ(X', (H.pull φ).U (fun _ => k) ⊓ H'.U k')ˣ) (w.s (fun _ => k, k')))⁻¹).val *
        (φ.appLE (H.U k) ((H.pull φ).U (fun _ => k) ⊓ H'.U k')
          (inf_le_left.trans (GlobalTheory.Cartier.pull_U H φ _).le)).hom a := by
  apply fn_ext
  intro x hx
  have hk : φ x ∈ H.U k := (GlobalTheory.Cartier.pull_U H φ _).le hx.1
  have hx' : x ∈ H'.U k' := hx.2
  have e := h x hk hx'
  have h1 : gs (𝟙 X') x _ (resG X' (inf_le_right : (H.pull φ).U (fun _ => k) ⊓ H'.U k' ≤ H'.U k') b) =
      gs (𝟙 X') x _ b := gs_res (𝟙 X') x inf_le_right hx b
  have h2 : gs (𝟙 X') x _ ((φ.appLE (H.U k) ((H.pull φ).U (fun _ => k) ⊓ H'.U k')
      (inf_le_left.trans (GlobalTheory.Cartier.pull_U H φ _).le)).hom a) = gs φ x _ a := by
    have := gs_res (𝟙 X') x (inf_le_left.trans (GlobalTheory.Cartier.pull_U H φ _).le) hx ((φ.app (H.U k)).hom a)
    refine Eq.trans ?_ (this.trans ((gs_pull (𝟙 X') φ x (H.U k) hk a).trans (by rw [Category.id_comp])))
    rfl
  have h3 : gs (𝟙 X') x _ (((@id (Γ(X', (H.pull φ).U (fun _ => k) ⊓ H'.U k')ˣ) (w.s (fun _ => k, k')))⁻¹).val) =
      ((Geo.Tor.gw w (𝟙 _) x k k')⁻¹).val := by
    rw [gs_unit (𝟙 X') x _ hx, map_inv]
    rfl
  rw [h1, gs_mul (𝟙 X') x _ hx, h2, h3, e, ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]

theorem isClosedImmersion_of_veryAmpleBy_compat : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) (H : LB X) (n : ℕ) (s : Fin (n + 1) → LB.Sec H), H.IsLB → VeryAmpleBy f H s → ∀ (X' : Scheme.{0}) (f' : X' ⟶ Spec (CommRingCat.of R)) (H' : LB X') (s' : Fin (n + 1) → LB.Sec H') (φ : X' ⟶ X) (w : LB.Iso H' (H.pull φ)), H'.IsLB → VeryAmpleBy f' H' s' → φ ≫ f = f' → w.IsGen → (∀ j, (∀ z (k : (H).ι) (k' : (H').ι), (φ) z ∈ (H).U k → z ∈ (H').U k' → gs (φ) z _ ((s j).f k) = (Geo.Tor.gw (w) (𝟙 _) z k k').val * gs (𝟙 _) z _ ((s' j).f k'))) → IsClosedImmersion φ := by
  intro R _ X f H n s hH hs X' f' H' s' φ w hH' hs' hf _ hrel
  subst hf
  obtain ⟨hc, hci⟩ := (GlobalTheory.ProjSpace.veryAmpleBy_iff f s).1 hs
  obtain ⟨hc', hci'⟩ := (GlobalTheory.ProjSpace.veryAmpleBy_iff (φ ≫ f) s').1 hs'
  have heq : GlobalTheory.ProjSpace.toProj (φ ≫ f) s' hc' = φ ≫ GlobalTheory.ProjSpace.toProj f s hc := by
    refine GlobalTheory.ProjSpace.toProj_eq_comp_of_locally hc φ hc' fun z => ?_
    obtain ⟨k, hk⟩ := exists_chart hH (φ z)
    obtain ⟨k', hk'⟩ := exists_chart hH' z
    exact ⟨(H.pull φ).U (fun _ => k) ⊓ H'.U k', ⟨(GlobalTheory.Cartier.pull_U H φ _).ge hk, hk'⟩, k,
      inf_le_left.trans (GlobalTheory.Cartier.pull_U H φ _).le, k', inf_le_right, _,
      fun j => resG_eq_inv_mul_appLE w k k' _ _ fun y hy hy' => hrel j y k k' hy hy'⟩
  have : IsClosedImmersion (φ ≫ GlobalTheory.ProjSpace.toProj f s hc) := heq ▸ hci'
  exact IsClosedImmersion.of_comp_isClosedImmersion φ (GlobalTheory.ProjSpace.toProj f s hc)

end GlobalTheory.Div
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedImmersionOfVeryAmpleSectionsCompatibleStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isClosedImmersion_of_veryAmpleSections_compatible : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) (H : LB X) (n : ℕ) (s : Fin (n + 1) → LB.Sec H), H.IsLB → VeryAmpleBy f H s → ∀ (X' : Scheme.{0}) (f' : X' ⟶ Spec (CommRingCat.of R)) (H' : LB X') (s' : Fin (n + 1) → LB.Sec H') (φ : X' ⟶ X) (w : LB.Iso H' (H.pull φ)), H'.IsLB → VeryAmpleBy f' H' s' → φ ≫ f = f' → w.IsGen → (∀ j, (∀ z (k : (H).ι) (k' : (H').ι), (φ) z ∈ (H).U k → z ∈ (H').U k' → gs (φ) z _ ((s j).f k) = (Geo.Tor.gw (w) (𝟙 _) z k k').val * gs (𝟙 _) z _ ((s' j).f k'))) → IsClosedImmersion φ := by
  first | exact @GlobalTheory.Div.isClosedImmersion_of_veryAmpleBy_compat | exact GlobalTheory.Div.isClosedImmersion_of_veryAmpleBy_compat | (intros; apply GlobalTheory.Div.isClosedImmersion_of_veryAmpleBy_compat <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalClosedSubschemesAlgebraiseOfProjective
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

theorem GlobalTheory.FormalAlg.alg_of_isProjBy : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R → ∀ (W : Scheme.{0}) (f : W ⟶ Spec (CommRingCat.of R)), IsProjBy f → Alg f I := by
  intro R _ _ I hc W f hP t ht hp
  obtain ⟨q, β, hq, hβ, hpb⟩ := GlobalTheory.T.compatibleReductionSystem_gives_thickening_tower R I W f t ht
  let Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) := fun e => Over.mk (q e)
  let j : ∀ e, (Y e).left ⟶ W := fun e => (t e).subschemeι
  obtain ⟨H, hH, n, s, hs⟩ := hP
  have hL : ∀ e, (H.pull (j e)).IsLB := fun e => LB.isLB_pull hH _
  let t' := fun e => Classical.choose (GlobalTheory.MorAlg.exists_isPull (j e) hH s)
  have ht' : ∀ e, GlobalTheory.MorAlg.IsPull (j e) s (t' e) :=
    fun e => Classical.choose_spec (GlobalTheory.MorAlg.exists_isPull (j e) hH s)
  have hv : ∀ e, GlobalTheory.MorAlg.IsPull (β e) (t' (e + 1)) (t' e) := fun e =>
    GlobalTheory.MorAlg.IsPull.cancel hH (hL _) (hL _) (ht' (e + 1)) (by
      have h1 : β e ≫ j (e + 1) = j e := hβ e
      rw [h1]; exact ht' e)
  choose v hv cv using hv
  have hjR : ∀ e, j e ≫ f = (Y e).hom ≫ thick R I e := hq
  have hva : VeryAmpleBy (Y 0).hom (H.pull (j 0)) (t' 0) := by
    obtain ⟨w, hw, c⟩ := ht' 0
    refine GlobalTheory.AbLaw.VeryAmplePull.veryAmpleBy_pull R W f H n s hH hs _ (Ideal.Quotient.mk (I ^ (0 + 1))) _ _ (j 0) (hjR 0) ?_ _ w _ (hL 0) hw c
    have h₃ : IsClosedImmersion (pullback.lift (j 0) (Y 0).hom (hjR 0) ≫ pullback.fst f (thick R I 0)) := by
      rw [pullback.lift_fst]
      exact inferInstanceAs (IsClosedImmersion (t 0).subschemeι)
    exact IsClosedImmersion.of_comp _ (pullback.fst f (thick R I 0))
  obtain ⟨B, H', s', b, w, hH', hs', hb, -, hw, heq⟩ := GlobalTheory.T.exists_projective_algebraisation_formalEmbedding_complete R I hc Y β hpb (fun e => H.pull (j e)) v
    (fun e => ⟨hL e, hv e⟩) n t' cv hva
  obtain ⟨φ, u, hφ, hu, cu⟩ := GlobalTheory.exists_hom_of_veryAmpleBy R W f H n s hH hs B.left B.hom H' s' hH' hs'.1
    fun d F hF h0 => (mem_vanIdeal _ _ _).1 (heq d F hF fun e => (mem_vanIdeal _ _ _).2 fun k => by
      rw [← hjR]
      exact (ht' e).eqn f hH hF h0 k)
  have hbφ : ∀ e, b e ≫ φ = j e := fun e => by
    obtain ⟨w₁, hw₁, c₁⟩ := GlobalTheory.MorAlg.IsPull.comp hH hH' (hL e) ⟨u, hu, cu⟩ ⟨w e, (hw e).1, (hw e).2⟩
    obtain ⟨w₂, hw₂, c₂⟩ := ht' e
    refine GlobalTheory.MapUniq.hom_eq_of_pull_sections R W f H n s hH hs _ _ (t' e) _ _ w₁ w₂ (hL e) ?_ hw₁ hw₂ c₁ c₂
    rw [Category.assoc, hφ, hjR]
    exact (hb e).w
  haveI hci : IsClosedImmersion φ := GlobalTheory.T.isClosedImmersion_of_veryAmpleSections_compatible R W f H n s hH hs B.left B.hom H' s' φ u hH' hs' hφ hu cu
  haveI hBp : IsProper (φ ≫ f) := by
    rw [hφ]; exact GlobalTheory.AbLaw.isProper_of_isProjBy R _ _ ⟨H', hH', n, s', hs'⟩
  refine ⟨φ.ker, ?_, fun e => ?_⟩
  · change IsProper (φ.imageι ≫ f)
    have hg : φ.imageι = inv φ.toImage ≫ φ := (IsIso.eq_inv_comp _).2 φ.toImage_imageι
    rw [hg, Category.assoc]
    infer_instance
  · have key := (GlobalTheory.T.isReduction_closedSubscheme_iff_ideal_eq R (I ^ (e + 1)) W B.left (Y e).left f φ (j e) (q e) hci
      (inferInstanceAs (IsClosedImmersion (t e).subschemeι)) (hq e)).1
      ⟨b e, hbφ e, by rw [hφ]; exact hb e⟩
    rw [key]
    exact Scheme.IdealSheafData.ker_subschemeι (t e)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalClosedSubschemesAlgebraiseOfProjectiveStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formalClosedSubschemes_algebraise_of_projective : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R → ∀ (W : Scheme.{0}) (f : W ⟶ Spec (CommRingCat.of R)), IsProjBy f → Alg f I := by
  first | exact @GlobalTheory.FormalAlg.alg_of_isProjBy | exact GlobalTheory.FormalAlg.alg_of_isProjBy | (intros; apply GlobalTheory.FormalAlg.alg_of_isProjBy <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalClosedSubschemesAlgebraiseOpenImmersion
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalClosedSubschemesAlgebraiseOpenImmersion
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

namespace GlobalTheory.FormalAlg

theorem alg_comp_of_isOpenImmersion : ∀ (R : Type) [CommRing R] (I : Ideal R), I ≤ Ideal.jacobson ⊥ →
    ∀ (W W' : Scheme.{0}) (f : W ⟶ Spec (CommRingCat.of R)) (j : W' ⟶ W), IsSeparated f →
      IsOpenImmersion j → Alg f I → Alg (j ≫ f) I := by
  intro R _ I hI W W' f j hf hj hA t ht hp
  obtain ⟨hs, hsp, hsc⟩ := GlobalTheory.T.compatibleReductionSystem_map_immersion R I W W' f j hf inferInstance t ht hp
  obtain ⟨T, hTp, hTr⟩ := hA _ hs hsp

  have hs0 : ((((t 0).map j).support : Set W)) ⊆ Set.range j := by
    haveI : IsProper ((t 0).subschemeι ≫ j ≫ f) := hp 0
    haveI : IsProper (((t 0).subschemeι ≫ j) ≫ f) := by rw [Category.assoc]; infer_instance
    haveI : UniversallyClosed ((t 0).subschemeι ≫ j) := UniversallyClosed.of_comp_of_isSeparated _ f
    haveI : QuasiCompact ((t 0).subschemeι ≫ j) := QuasiCompact.of_comp _ f
    have hker : (t 0).map j = Scheme.Hom.ker ((t 0).subschemeι ≫ j) := by
      rw [← Scheme.IdealSheafData.map_ker, Scheme.IdealSheafData.ker_subschemeι]
    rw [hker, Scheme.Hom.support_ker,
      (((t 0).subschemeι ≫ j).isClosedMap.isClosed_range).closure_eq]
    rintro _ ⟨x, rfl⟩
    exact ⟨(t 0).subschemeι x, by simp⟩

  have hT : ((T.support : Set W)) ⊆ Set.range j := by
    haveI : UniversallyClosed (T.subschemeι ≫ f) := inferInstance
    have hZ : IsClosed (T.subschemeι.base ⁻¹' (Set.range j)ᶜ) :=
      (j.isOpenEmbedding.isOpen_range.isClosed_compl).preimage T.subschemeι.continuous
    have hE := GlobalTheory.T.eq_empty_of_isClosed_of_universallyClosed_of_le_jacobson R I hI T.subscheme (T.subschemeι ≫ f) inferInstance _ hZ (by
      intro x hx hIx
      apply hx
      apply hs0
      have h0 : T ⊔ baseIdeal f (I ^ (0 + 1)) = (t 0).map j := hTr 0
      rw [← h0, Scheme.IdealSheafData.support_sup]
      refine ⟨?_, ?_⟩
      · rw [← Scheme.IdealSheafData.range_subschemeι]; exact ⟨x, rfl⟩
      · refine ((GlobalTheory.T.baseIdealSheafOfIdeal_comap_specMap_support).2.2 R W f (I ^ (0 + 1)) (T.subschemeι x)).2 ?_
        rw [zero_add, pow_one]
        simpa using hIx)
    intro y hy
    rw [← Scheme.IdealSheafData.range_subschemeι] at hy
    obtain ⟨x, rfl⟩ := hy
    by_contra hc
    have : x ∈ (T.subschemeι.base ⁻¹' (Set.range j)ᶜ) := hc
    rw [hE] at this
    exact this
  refine ⟨T.comap j, ?_, fun e => ?_⟩
  · have hsurj : Function.Surjective (pullback.snd j T.subschemeι) := by
      intro x
      obtain ⟨w, hw⟩ := hT (by
        rw [← Scheme.IdealSheafData.range_subschemeι]; exact ⟨x, rfl⟩)
      obtain ⟨z, -, hz⟩ := Scheme.Pullback.exists_preimage_pullback w x hw
      exact ⟨z, hz⟩
    haveI : IsIso (pullback.snd j T.subschemeι) :=
      (isIso_iff_isOpenImmersion_and_surjective _).2 ⟨inferInstance, ⟨hsurj⟩⟩
    have he : (T.comap j).subschemeι ≫ j ≫ f =
        (T.comapIso j).hom ≫ pullback.snd j T.subschemeι ≫ T.subschemeι ≫ f := by
      rw [← Scheme.IdealSheafData.comapIso_hom_fst, Category.assoc, pullback.condition_assoc]
    rw [he]
    infer_instance
  · rw [← (GlobalTheory.T.baseIdealSheafOfIdeal_comap_specMap_support).1 R W W' f j, ← Scheme.IdealSheafData.comap_sup, show T ⊔ baseIdeal f (I ^ (e + 1)) = (t e).map j from hTr e, hsc e]

end GlobalTheory.FormalAlg
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalClosedSubschemesAlgebraiseOpenImmersionStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formalClosedSubschemesAlgebraise_openImmersion : ∀ (R : Type) [CommRing R] (I : Ideal R), I ≤ Ideal.jacobson ⊥ → ∀ (W W' : Scheme.{0}) (f : W ⟶ Spec (CommRingCat.of R)) (j : W' ⟶ W), IsSeparated f → IsOpenImmersion j → Alg f I → Alg (j ≫ f) I := by
  first | exact @GlobalTheory.FormalAlg.alg_comp_of_isOpenImmersion | exact GlobalTheory.FormalAlg.alg_comp_of_isOpenImmersion | (intros; apply GlobalTheory.FormalAlg.alg_comp_of_isOpenImmersion <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalClosedSubschemesAlgebraiseClosedImmersion
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalClosedSubschemesAlgebraiseClosedImmersion
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FormalAlg

theorem alg_of_isClosedImmersion : ∀ (R : Type) [CommRing R] (I : Ideal R) (W W' : Scheme.{0})
    (f : W ⟶ Spec (CommRingCat.of R)) (i : W' ⟶ W), IsSeparated f → IsClosedImmersion i → Alg f I →
    Alg (i ≫ f) I := by
  intro R _ I W W' f i hf hi hA t ht hp
  obtain ⟨hs, hsp, hc⟩ := GlobalTheory.T.compatibleReductionSystem_map_immersion R I W W' f i hf inferInstance t ht hp
  obtain ⟨T, hT, hred⟩ := hA _ hs hsp
  refine ⟨T.comap i, ?_, fun e => ?_⟩
  · have h1 : (T.comap i).subschemeι ≫ i ≫ f =
        (T.comapIso i).hom ≫ pullback.snd i T.subschemeι ≫ T.subschemeι ≫ f := by
      rw [← T.comapIso_hom_fst_assoc i, pullback.condition_assoc]
    rw [h1]
    infer_instance
  · rw [← (GlobalTheory.T.baseIdealSheafOfIdeal_comap_specMap_support).1 R W W' f i, ← Scheme.IdealSheafData.comap_sup, hred e]
    exact hc e

end GlobalTheory.FormalAlg
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalClosedSubschemesAlgebraiseClosedImmersionStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formalClosedSubschemesAlgebraise_closedImmersion : ∀ (R : Type) [CommRing R] (I : Ideal R) (W W' : Scheme.{0}) (f : W ⟶ Spec (CommRingCat.of R)) (i : W' ⟶ W), IsSeparated f → IsClosedImmersion i → Alg f I → Alg (i ≫ f) I := by
  first | exact @GlobalTheory.FormalAlg.alg_of_isClosedImmersion | exact GlobalTheory.FormalAlg.alg_of_isClosedImmersion | (intros; apply GlobalTheory.FormalAlg.alg_of_isClosedImmersion <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraiseOfIsImmersionProjectiveCompleteNoeth
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

namespace GlobalTheory.FormalAlg

theorem alg_of_isImmersion_isProjOver :
    ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R →
      ∀ (W P : Scheme.{0}) (j : W ⟶ P) (p : P ⟶ Spec (CommRingCat.of R)),
        ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsProjOver p → IsImmersion j → Alg (j ≫ p) I := by
  intro R _ _ I hI W P j p hp hj
  have hpb : IsProjBy p := (GlobalTheory.ProjSpace.isProjBy_iff_isProjOver p).2 hp
  have hprop : IsProper p := GlobalTheory.AbLaw.isProper_of_isProjBy R P p hpb
  have hA : Alg p I := GlobalTheory.T.formalClosedSubschemes_algebraise_of_projective R I hI P p hpb
  have hjac : I ≤ Ideal.jacobson ⊥ := IsAdicComplete.le_jacobson_bot I
  have hsep : IsSeparated p := inferInstance
  have hU : Alg (j.coborderRange.ι ≫ p) I :=
    GlobalTheory.T.formalClosedSubschemesAlgebraise_openImmersion R I hjac P _ p j.coborderRange.ι hsep inferInstance hA
  have hsepU : IsSeparated (j.coborderRange.ι ≫ p) := inferInstance
  have hW := GlobalTheory.T.formalClosedSubschemesAlgebraise_closedImmersion R I _ W (j.coborderRange.ι ≫ p) j.liftCoborder hsepU inferInstance hU
  rwa [← Category.assoc, Scheme.Hom.liftCoborder_ι] at hW

end GlobalTheory.FormalAlg
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraiseOfIsImmersionProjectiveCompleteNoethStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraise_of_isImmersion_projective_completeNoeth : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R → ∀ (W P : Scheme.{0}) (j : W ⟶ P) (p : P ⟶ Spec (CommRingCat.of R)), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsProjOver p → IsImmersion j → Alg (j ≫ p) I := by
  first | exact @GlobalTheory.FormalAlg.alg_of_isImmersion_isProjOver | exact GlobalTheory.FormalAlg.alg_of_isImmersion_isProjOver | (intros; apply GlobalTheory.FormalAlg.alg_of_isImmersion_isProjOver <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrothendieckExistenceClosedSubschemesSeparated
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FormalAlg

theorem subsingleton_idealSheafData_of_isEmpty (W : Scheme.{0}) [IsEmpty W] :
    Subsingleton W.IdealSheafData := by
  constructor
  intro a b
  apply Scheme.IdealSheafData.ext
  funext U
  exact Subsingleton.elim _ _

theorem alg_of_isEmpty {R : Type} [CommRing R] {W : Scheme.{0}} [IsEmpty W]
    (f : W ⟶ Spec (CommRingCat.of R)) (I : Ideal R) : Alg f I := by
  have := subsingleton_idealSheafData_of_isEmpty W
  intro t _ hp
  exact ⟨t 0, hp 0, fun _ => Subsingleton.elim _ _⟩

theorem alg_of_isSeparated : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R →
    ∀ (W : Scheme.{0}) (f : W ⟶ Spec (CommRingCat.of R)), IsSeparated f → LocallyOfFiniteType f →
      QuasiCompact f → Alg f I := by
  intro R _ _ I hI W₀ f₀ hsep hlft hqc
  have : IsLocallyNoetherian W₀ := LocallyOfFiniteType.isLocallyNoetherian f₀
  have : CompactSpace W₀ := QuasiCompact.compactSpace_of_compactSpace f₀
  have : AlgebraicGeometry.IsNoetherian W₀ := {}
  suffices H : ∀ Z : TopologicalSpace.Closeds W₀, ∀ (W : Scheme.{0}) (i : W ⟶ W₀), IsClosedImmersion i →
      Set.range i ⊆ (Z : Set W₀) → Alg (i ≫ f₀) I by
    simpa using H ⊤ W₀ (𝟙 _) inferInstance (by simp)
  intro Z
  induction Z using WellFoundedLT.induction with
  | _ Z ih =>
  intro W i hi hZ
  have hsep' : IsSeparated (i ≫ f₀) := inferInstance
  have hlft' : LocallyOfFiniteType (i ≫ f₀) := inferInstance
  have hqc' : QuasiCompact (i ≫ f₀) := inferInstance
  by_cases hW : Nonempty W
  · obtain ⟨W', P, π, q, s, U, hπ, hU, hiso, hs, hq, hcomm⟩ :=
      GlobalTheory.T.chow_lemma_projective_modification R W (i ≫ f₀) hsep' hlft' hqc' hW
    have hA : Alg (π ≫ i ≫ f₀) I := by
      rw [← hcomm]
      exact GlobalTheory.T.algebraise_of_isImmersion_projective_completeNoeth R I hI W' P q s hs hq
    let K := Scheme.IdealSheafData.vanishingIdeal
      (⟨(U : Set W)ᶜ, U.isOpen.isClosed_compl⟩ : TopologicalSpace.Closeds W)
    have hK : ((K.support : Set W)) = (U : Set W)ᶜ := Scheme.IdealSheafData.coe_support_vanishingIdeal _
    refine GlobalTheory.T.algebraisation_of_proper_modification_noetherian_step R I W (i ≫ f₀) hsep' hlft' hqc' W' π U hπ hiso K ?_ hA ?_
    · intro x hx
      by_contra hxU
      apply hx
      rw [← SetLike.mem_coe, hK]
      exact hxU
    · intro k
      let Z' : TopologicalSpace.Closeds W₀ :=
        ⟨i '' (U : Set W)ᶜ, i.isClosedEmbedding.isClosedMap _ U.isOpen.isClosed_compl⟩
      have hlt : Z' < Z := by
        refine lt_of_le_of_ne ?_ ?_
        · rintro y ⟨x, _, rfl⟩
          exact hZ ⟨x, rfl⟩
        · intro heq
          obtain ⟨u, hu⟩ := hU
          have h1 : i u ∈ (Z : Set W₀) := hZ ⟨u, rfl⟩
          rw [← heq] at h1
          obtain ⟨x, hx, hxu⟩ := h1
          exact hx (i.isClosedEmbedding.injective hxu ▸ hu)
      have h2 := ih Z' hlt _ ((K ^ k).subschemeι ≫ i) inferInstance (by
        rintro _ ⟨x, rfl⟩
        refine ⟨(K ^ k).subschemeι x, ?_, rfl⟩
        have hsub : ((K ^ k).support : Set W) ⊆ (U : Set W)ᶜ := by
          rcases Nat.eq_zero_or_pos k with rfl | hk
          · rw [pow_zero, Scheme.IdealSheafData.one_eq_top, Scheme.IdealSheafData.support_top]
            intro y hy
            exact hy.elim
          · rw [Scheme.IdealSheafData.support_pow _ _ hk.ne', hK]
        apply hsub
        rw [← Scheme.IdealSheafData.range_subschemeι]
        exact ⟨x, rfl⟩)
      rwa [Category.assoc] at h2
  · have : IsEmpty W := not_nonempty_iff.1 hW
    exact alg_of_isEmpty _ I

end GlobalTheory.FormalAlg
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrothendieckExistenceClosedSubschemesSeparatedStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.grothendieck_existence_closedSubschemes_separated : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R → ∀ (W : Scheme.{0}) (f : W ⟶ Spec (CommRingCat.of R)), IsSeparated f → LocallyOfFiniteType f → QuasiCompact f → Alg f I := by
  first | exact @GlobalTheory.FormalAlg.alg_of_isSeparated | exact GlobalTheory.FormalAlg.alg_of_isSeparated | (intros; apply GlobalTheory.FormalAlg.alg_of_isSeparated <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalAlgebraisationTower
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalAlgebraisationTower
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

theorem GlobalTheory.FormalAlg.alg_tower : ∀ (R : Type) [CommRing R] (I : Ideal R) (W : Scheme.{0}) (f : W ⟶ Spec (CommRingCat.of R)), Alg f I → ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → (∀ e, IsProper (Y e).hom) → ∀ j : ∀ e, (Y e).left ⟶ W, (∀ e, IsClosedImmersion (j e)) → (∀ e, j e ≫ f = (Y e).hom ≫ thick R I e) → (∀ e, β e ≫ j (e + 1) = j e) → ∃ (T : Scheme.{0}) (i : T ⟶ W) (c : ∀ e, (Y e).left ⟶ T), IsClosedImmersion i ∧ IsProper (i ≫ f) ∧ (∀ e, c e ≫ i = j e) ∧ ∀ e, IsPullback (c e) (Y e).hom (i ≫ f) (thick R I e) := by
  intro R _ I W f hA Y β hβ hY j hj hjf hβj
  have hP := (GlobalTheory.T.isPullback_thick_tower_squares R I Y β hβ).1
  have key : ∀ e (T : Scheme.{0}) (i : T ⟶ W), IsClosedImmersion i →
      ((∃ b : (Y e).left ⟶ T, b ≫ i = j e ∧ IsPullback b (Y e).hom (i ≫ f) (thick R I e)) ↔
        i.ker ⊔ baseIdeal f (I ^ (e + 1)) = (j e).ker) :=
    fun e T i hi => GlobalTheory.T.isReduction_closedSubscheme_iff_ideal_eq R (I ^ (e + 1)) W T (Y e).left f i (j e) (Y e).hom hi (hj e) (hjf e)
  have hsys : IsSystem f I (fun e => (j e).ker) := by
    intro e
    exact ((key e _ (j (e + 1)) (hj (e + 1))).1 ⟨β e, hβj e, by rw [hjf (e + 1)]; exact hP e⟩).symm
  have hprop : ∀ e, IsProper ((j e).ker.subschemeι ≫ f) := by
    intro e
    have h0 : (j e).toImage ≫ ((j e).ker.subschemeι ≫ f) = (Y e).hom ≫ thick R I e := by
      rw [← hjf e, ← Category.assoc]
      exact congrArg (· ≫ f) (Scheme.Hom.toImage_imageι (j e))
    have h1 : (j e).ker.subschemeι ≫ f = inv (j e).toImage ≫ (Y e).hom ≫ thick R I e := by
      rw [← h0, IsIso.inv_hom_id_assoc]
    have : IsClosedImmersion (thick R I e) :=
      IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    rw [h1]
    infer_instance
  obtain ⟨T, hTp, hTr⟩ := hA _ hsys hprop
  have hc : ∀ e, ∃ b : (Y e).left ⟶ T.subscheme, b ≫ T.subschemeι = j e ∧
      IsPullback b (Y e).hom (T.subschemeι ≫ f) (thick R I e) := fun e =>
    (key e _ T.subschemeι inferInstance).2 (by rw [Scheme.IdealSheafData.ker_subschemeι]; exact hTr e)
  choose c hc1 hc2 using hc
  exact ⟨T.subscheme, T.subschemeι, c, inferInstance, hTp, hc1, hc2⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalAlgebraisationTowerStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formal_algebraisation_tower : ∀ (R : Type) [CommRing R] (I : Ideal R) (W : Scheme.{0}) (f : W ⟶ Spec (CommRingCat.of R)), Alg f I → ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → (∀ e, IsProper (Y e).hom) → ∀ j : ∀ e, (Y e).left ⟶ W, (∀ e, IsClosedImmersion (j e)) → (∀ e, j e ≫ f = (Y e).hom ≫ thick R I e) → (∀ e, β e ≫ j (e + 1) = j e) → ∃ (T : Scheme.{0}) (i : T ⟶ W) (c : ∀ e, (Y e).left ⟶ T), IsClosedImmersion i ∧ IsProper (i ≫ f) ∧ (∀ e, c e ≫ i = j e) ∧ ∀ e, IsPullback (c e) (Y e).hom (i ≫ f) (thick R I e) := by
  first | exact @GlobalTheory.FormalAlg.alg_tower | exact GlobalTheory.FormalAlg.alg_tower | (intros; apply GlobalTheory.FormalAlg.alg_tower <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MorphismEqOfEqOnThickenings
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MorphismEqOfEqOnThickenings
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

namespace GlobalTheory.FormalAlg

theorem hom_eq_of_reductions_eq : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), I ≤ Ideal.jacobson ⊥ → ∀ (X Z : Over (Spec (CommRingCat.of R))), IsProper X.hom → IsSeparated Z.hom → ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (b : ∀ e, (Y e).left ⟶ X.left), (∀ e, IsPullback (b e) (Y e).hom X.hom (thick R I e)) → ∀ g g' : X ⟶ Z, (∀ e, b e ≫ g.left = b e ≫ g'.left) → g = g' := by
  intro R _ _ I hI X Z hX hZ Y b hb g g' hg
  have hι : IsClosedImmersion (equalizer.ι g g').left := isClosedImmersion_equalizer_ι_left g g'
  have hN : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have hle : ∀ e : ℕ, (equalizer.ι g g').left.ker ≤ baseIdeal X.hom (I ^ (e + 1)) := by
    intro e
    rw [← (GlobalTheory.T.baseChange_quotient_closedImmersion_idealSheaf R (I ^ (e + 1)) X.left (Y e).left X.hom (b e) (Y e).hom (hb e)).2.1]
    let c : Over.mk (b e ≫ X.hom) ⟶ X := Over.homMk (b e) rfl
    have hc : c ≫ g = c ≫ g' := by
      ext
      exact hg e
    have h1 : (equalizer.lift c hc).left ≫ (equalizer.ι g g').left = b e := by
      rw [← Over.comp_left, equalizer.lift_ι]
      rfl
    rw [← h1]
    exact Scheme.Hom.le_ker_comp _ _
  have hbot : (equalizer.ι g g').left.ker ≤ ⊥ :=
    GlobalTheory.T.idealSheaf_le_of_le_on_reductions_jacobson R I hI X.left X.hom _ ⊥ inferInstance fun e => (hle e).trans le_sup_right
  have hiso : IsIso (equalizer.ι g g').left :=
    IsClosedImmersion.isIso_iff_ker_eq_bot.2 (le_bot_iff.1 hbot)
  ext
  rw [← cancel_epi (equalizer.ι g g').left, ← Over.comp_left, ← Over.comp_left, equalizer.condition]

end GlobalTheory.FormalAlg
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MorphismEqOfEqOnThickeningsStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.morphism_eq_of_eq_on_thickenings : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), I ≤ Ideal.jacobson ⊥ → ∀ (X Z : Over (Spec (CommRingCat.of R))), IsProper X.hom → IsSeparated Z.hom → ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (b : ∀ e, (Y e).left ⟶ X.left), (∀ e, IsPullback (b e) (Y e).hom X.hom (thick R I e)) → ∀ g g' : X ⟶ Z, (∀ e, b e ≫ g.left = b e ≫ g'.left) → g = g' := by
  first | exact @GlobalTheory.FormalAlg.hom_eq_of_reductions_eq | exact GlobalTheory.FormalAlg.hom_eq_of_reductions_eq | (intros; apply GlobalTheory.FormalAlg.hom_eq_of_reductions_eq <;> assumption)
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.FormalAlg

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FormalAlgMorphisms

variable {R : Type} [CommRing R]

instance isClosedImmersion_thick (I : Ideal R) (e : ℕ) : IsClosedImmersion (thick R I e) :=
  IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

theorem isPullback_trans {I : Ideal R} (X : Over (Spec (CommRingCat.of R)))
    (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))))
    (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (b : ∀ e, (Y e).left ⟶ X.left)
    (hb : ∀ e, IsPullback (b e) (Y e).hom X.hom (thick R I e)) (hβ : ∀ e, β e ≫ b (e + 1) = b e)
    (e : ℕ) : IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e) := by
  have hw : β e ≫ (Y (e + 1)).hom = (Y e).hom ≫ thickTrans R I e := by
    rw [← cancel_mono (thick R I (e + 1)), Category.assoc, ← (hb (e + 1)).w, ← Category.assoc,
      hβ, (hb e).w, Category.assoc, thickTrans_comp]
  refine IsPullback.of_right ?_ hw (hb (e + 1))
  rw [hβ, thickTrans_comp]
  exact hb e

theorem formalAlgebraisation_morphisms : GlobalTheory.Published.FormalAlgebraisation.Morphisms := by
  intro R _ _ I hI X Z hX hZs hZl hZq Y β b hb hβ f hf hfβ
  have hIj : I ≤ Ideal.jacobson ⊥ := by
    haveI := hI
    exact IsAdicComplete.le_jacobson_bot I

  let fW : pullback X.hom Z.hom ⟶ Spec (CommRingCat.of R) := pullback.fst X.hom Z.hom ≫ X.hom
  haveI : IsSeparated (pullback.fst X.hom Z.hom) :=
    MorphismProperty.of_isPullback (P := @IsSeparated) (IsPullback.of_hasPullback X.hom Z.hom).flip hZs
  haveI : LocallyOfFiniteType (pullback.fst X.hom Z.hom) :=
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) (IsPullback.of_hasPullback X.hom Z.hom).flip hZl
  haveI : QuasiCompact (pullback.fst X.hom Z.hom) :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) (IsPullback.of_hasPullback X.hom Z.hom).flip hZq
  have hAlg : Alg fW I := GlobalTheory.T.grothendieck_existence_closedSubschemes_separated R I hI _ fW inferInstance inferInstance inferInstance

  have hcomm : ∀ e, b e ≫ X.hom = f e ≫ Z.hom := fun e => by rw [(hb e).w, hf e]
  let j : ∀ e, (Y e).left ⟶ pullback X.hom Z.hom := fun e => pullback.lift (b e) (f e) (hcomm e)
  have hj₁ : ∀ e, j e ≫ pullback.fst X.hom Z.hom = b e := fun e => pullback.lift_fst _ _ _
  have hj₂ : ∀ e, j e ≫ pullback.snd X.hom Z.hom = f e := fun e => pullback.lift_snd _ _ _
  have hbci : ∀ e, IsClosedImmersion (b e) := fun e =>
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) (hb e).flip inferInstance
  have hjci : ∀ e, IsClosedImmersion (j e) := fun e => by
    haveI : IsClosedImmersion (j e ≫ pullback.fst X.hom Z.hom) := by rw [hj₁]; exact hbci e
    exact IsClosedImmersion.of_comp (j e) (pullback.fst X.hom Z.hom)
  have hjf : ∀ e, j e ≫ fW = (Y e).hom ≫ thick R I e := fun e => by
    simp only [fW]
    rw [← Category.assoc, hj₁, (hb e).w]
  have hjβ : ∀ e, β e ≫ j (e + 1) = j e := fun e => by
    apply pullback.hom_ext
    · rw [Category.assoc, hj₁, hj₁, hβ]
    · rw [Category.assoc, hj₂, hj₂, hfβ]
  have hYp : ∀ e, IsProper (Y e).hom := fun e =>
    MorphismProperty.of_isPullback (P := @IsProper) (hb e) hX
  obtain ⟨T, i, c, hi, hip, hci, hcpb⟩ := GlobalTheory.T.formal_algebraisation_tower R I _ fW hAlg Y β
    (isPullback_trans X Y β b hb hβ) hYp j hjci hjf hjβ

  let φ : T ⟶ X.left := i ≫ pullback.fst X.hom Z.hom
  have hφX : φ ≫ X.hom = i ≫ fW := Category.assoc _ _ _
  haveI : IsProper (φ ≫ X.hom) := by rw [hφX]; exact hip
  haveI : IsProper φ := IsProper.of_comp φ X.hom
  have hcφ : ∀ e, c e ≫ φ = b e := fun e => by
    simp only [φ]
    rw [← Category.assoc, hci, hj₁]
  haveI hφiso : IsIso φ := GlobalTheory.T.isIso_of_proper_isIso_on_reductions R I hIj T X.left φ X.hom inferInstance hX Y c
    (fun e => by rw [hφX]; exact hcpb e) (fun e => by rw [hcφ]; exact hb e)

  let gl : X.left ⟶ Z.left := inv φ ≫ i ≫ pullback.snd X.hom Z.hom
  have hgw : gl ≫ Z.hom = X.hom := by
    simp only [gl, Category.assoc]
    rw [← pullback.condition, ← Category.assoc i, ← Category.assoc (inv φ)]
    exact IsIso.inv_hom_id_assoc φ X.hom
  refine ⟨Over.homMk gl hgw, fun e => ?_, fun g' hg' => ?_⟩
  · show b e ≫ gl = f e
    simp only [gl]
    rw [← hcφ e, Category.assoc, IsIso.hom_inv_id_assoc, ← Category.assoc, hci, hj₂]
  · refine GlobalTheory.T.morphism_eq_of_eq_on_thickenings R I hIj X Z hX hZs Y b hb g' _ fun e => ?_
    rw [hg' e]
    show f e = b e ≫ gl
    simp only [gl]
    rw [← hcφ e, Category.assoc, IsIso.hom_inv_id_assoc, ← Category.assoc, hci, hj₂]

end GlobalTheory.FormalAlgMorphisms
