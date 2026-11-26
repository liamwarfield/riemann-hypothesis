module

public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SemiAbelianModelDeterminedByGenericFibre

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmplePrincipalDescendedBundleNoetherian
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmplePrincipalDescendedBundleNoetherian
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

namespace GlobalTheory.DescentFamily

open GlobalTheory.CechPic

theorem card_ker_pullback {S S' : Scheme.{0}} (t : S' ⟶ S) {A B : Over S} [GrpObj A] [GrpObj B] (ψ : A ⟶ B) :
    Nat.card {x : 𝟙_ (Over S') ⟶ (Over.pullback t).obj A // x ≫ (Over.pullback t).map ψ = 1} =
      Nat.card {x : Over.mk ((𝟙_ (Over S')).hom ≫ t) ⟶ A // x ≫ ψ = 1} := by
  have hA := isGrpPullback_pullback A t
  have hB := isGrpPullback_pullback B t
  have inj : ∀ {G : Over S} [GrpObj G] (h : IsGrpPullback ((Over.pullback t).obj G) G t (pullback.fst G.hom t)),
      Function.Injective (pushHom h (𝟙_ (Over S'))) := fun h x y e =>
    Over.OverMorphism.ext (h.1.hom_ext (congrArg (fun z => z.left) e) (by rw [Over.w, Over.w]))
  have surj : Function.Surjective (pushHom hA (𝟙_ (Over S'))) := fun x =>
    ⟨Over.homMk (hA.1.lift x.left (𝟙_ (Over S')).hom (Over.w x)) (hA.1.lift_snd _ _ _),
      Over.OverMorphism.ext (hA.1.lift_fst _ _ _)⟩
  refine Nat.card_congr (Equiv.subtypeEquiv (Equiv.ofBijective _ ⟨inj hA, surj⟩) fun x => ?_)
  have e : pushHom hB (𝟙_ (Over S')) (x ≫ (Over.pullback t).map ψ) = pushHom hA (𝟙_ (Over S')) x ≫ ψ := by
    refine Over.OverMorphism.ext ?_
    show (x.left ≫ ((Over.pullback t).map ψ).left) ≫ pullback.fst B.hom t = (x.left ≫ pullback.fst A.hom t) ≫ ψ.left
    rw [Category.assoc, Category.assoc]
    exact congrArg (x.left ≫ ·) (pullback.lift_fst _ _ _)
  exact (map_eq_one_iff _ (inj hB)).symm.trans (Eq.congr_left e)

theorem kTriv_fibre {S : Scheme.{0}} (P : Out.PolAV S) {n : ℕ} (B : Over S) [GrpObj B] (ψ : P.A ⟶ B) (M : LB B.left)
    (hn : 0 < n) (hB : IsAbelianScheme B) (hM : M.IsLB) [IsMonHom ψ] [IsFinite ψ.left] [Etale ψ.left]
    [Surjective ψ.left] (hiso : LBIso (lbPow P.L n) (M.pull ψ.left)) (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    (t : Sp k ⟶ S) (hc : Nat.card {x : Over.mk (𝟙 _ ≫ t) ⟶ P.A // x ≫ ψ = 1} = n ^ P.g) :
    Out.KTriv ((Over.pullback t).obj B) (M.pull (pullback.fst B.hom t)) := by
  have hw : ((Over.pullback t).map ψ).left ≫ pullback.fst B.hom t = pullback.fst P.A.hom t ≫ ψ.left :=
    pullback.lift_fst _ _ _
  have hp : IsPullback (pullback.fst P.A.hom t) ((Over.pullback t).map ψ).left ψ.left (pullback.fst B.hom t) := by
    refine IsPullback.of_bot ?_ hw.symm (IsPullback.of_hasPullback B.hom t)
    have e : ((Over.pullback t).map ψ).left ≫ pullback.snd B.hom t = pullback.snd P.A.hom t :=
      Over.w ((Over.pullback t).map ψ)
    rw [e, Over.w ψ]
    exact IsPullback.of_hasPullback _ _
  have hL' := pull_isLB P.isLB (pullback.fst P.A.hom t)
  have hM' := pull_isLB hM (pullback.fst B.hom t)
  have h₁ : (lbPow (P.L.pull (pullback.fst P.A.hom t)) n).IsLB := LB.isLB_linComb hL' _ _
  have h₂ := pull_isLB hM' ((Over.pullback t).map ψ).left
  have h₀ := (cls_eq_iff (LB.isLB_linComb P.isLB _ _) (pull_isLB hM _)).2 hiso
  rw [cls_lbPow P.isLB, cls_pull hM] at h₀
  have he : cls _ h₁ = cls _ h₂ := by
    rw [cls_lbPow hL', cls_pull hM', cls_pull P.isLB, cls_pull hM, ← pull_comp, hw, pull_comp, ← h₀, map_nsmul]
  have hmon : IsMonHom ((Over.pullback t).map ψ) := inferInstance
  have H := pol_pull _ _ P.A ((Over.pullback t).obj P.A) t (pullback.fst P.A.hom t)
    P.L _ P.isLB hL' P.isAb (isGrpPullback_pullback P.A t) (PolBaseChange.lbIso_refl hL')
  let Q : Out.PolAV (Sp k) :=
    { A := (Over.pullback t).obj P.A, isAb := H.1, g := P.g
      smoothDim := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback
        (isGrpPullback_pullback P.A t).1 P.smoothDim
      L := P.L.pull (pullback.fst P.A.hom t), isLB := hL'
      rigid := PolBaseChange.rigidified_pull (isGrpPullback_pullback P.A t) P.rigid
      sym := PolBaseChange.sym_pull (isGrpPullback_pullback P.A t) P.sym
      ample := H.2.1 P.ample, ktriv := H.2.2 P.ktriv }
  refine kTriv_of_descent firstFiveLaws.1 k Q n _ ((Over.pullback t).map ψ) _ hn
    (PolPull.isAbelianScheme_of_isGrpPullback hB (isGrpPullback_pullback B t)) hM' hmon
    (MorphismProperty.of_isPullback (P := @IsFinite) hp inferInstance)
    (MorphismProperty.of_isPullback (P := @Etale) hp inferInstance)
    (MorphismProperty.of_isPullback (P := @Surjective) hp inferInstance)
    ((card_ker_pullback t ψ).trans hc) ?_
  refine (cls_eq_iff (LB.isLB_linComb h₁ _ _) (LB.isLB_linComb h₂ _ _)).1 ?_
  refine (cls_cube_two (G := (Over.pullback t).obj P.A) h₁ _ _ _).trans
    (Eq.trans ?_ (cls_cube_two (G := (Over.pullback t).obj P.A) h₂ _ _ _).symm)
  exact congrArg (fun c => lam (G := (Over.pullback t).obj P.A) c _ _) he

end GlobalTheory.DescentFamily

namespace GlobalTheory

open GlobalTheory.CechPic

theorem relAmple_kTriv_of_descent_family : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (P : Out.PolAV (Sp R)) (n : ℕ) (B : Over (Sp R)) [GrpObj B] (ψ : P.A ⟶ B) (M : LB B.left), (∀ m : ℕ, 0 < m → IsUnit (m : R)) → 0 < n → IsAbelianScheme B → M.IsLB → IsMonHom ψ → IsFinite ψ.left → Etale ψ.left → Surjective ψ.left → (∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R), Nat.card {x : Over.mk t ⟶ P.A // x ≫ ψ = 1} = n ^ P.g) → LBIso (lbPow P.L n) (M.pull ψ.left) → Out.RelAmple B M ∧ Out.KTriv B M := by
  intro R _ _ P n B _ ψ M hu hn hB hM hψ hf he hs hc hiso
  have hA := P.isAb
  have hn' : (lbPow P.L n).IsLB := LB.isLB_linComb P.isLB _ _
  have hid : IsFinite (𝟙 P.A : P.A ⟶ P.A).left := by rw [Over.id_left]; infer_instance
  have a₁ : Out.RelAmple P.A (lbPow P.L n) :=
    (relAmple_finite_pow_iso _ P.A P.A (𝟙 _) P.L n hn hA hA P.isLB hid).2.1.2 P.ample
  have a₂ : Out.RelAmple P.A (M.pull ψ.left) :=
    (relAmple_finite_pow_iso _ P.A P.A (𝟙 _) _ 1 one_pos hA hA hn' hid).2.2.2 _ (pull_isLB hM _) hiso a₁
  have a₃ : Out.RelAmple B M :=
    (relAmple_finite_pow_iso _ P.A B ψ M 1 one_pos hA hB hM hf).2.2.1 inferInstance hs a₂
  refine ⟨a₃, ?_⟩
  have loc : ∀ q : PrimeSpectrum R, ∃ f : R, f ∉ q.asIdeal ∧
      Out.KTriv ((Over.pullback (spMap (algebraMap R (Localization.Away f)))).obj B)
        (M.pull (pullback.fst B.hom (spMap (algebraMap R (Localization.Away f))))) := by
    intro q
    let k := AlgebraicClosure q.asIdeal.ResidueField
    let x : R →+* k := (algebraMap q.asIdeal.ResidueField k).comp (algebraMap R q.asIdeal.ResidueField)
    have : CharZero k := charZero_of_inj_zero fun m hm => by
      by_contra h
      have := (hu m (Nat.pos_of_ne_zero h)).map x
      rw [map_natCast, hm] at this
      exact not_isUnit_zero this
    obtain ⟨f, hf, H⟩ := kTriv_away_of_kTriv_fibre firstFiveLaws.1.globalFns R B M k x hB hM a₃
      (DescentFamily.kTriv_fibre P B ψ M hn hB hM hiso k (spMap x) (hc k _))
    refine ⟨f, fun h => hf ?_, H⟩
    show algebraMap q.asIdeal.ResidueField k (algebraMap R q.asIdeal.ResidueField f) = 0
    rw [Ideal.algebraMap_residueField_eq_zero.2 h, map_zero]
  choose f hf H using loc
  let j : ∀ q, Sp (Localization.Away (f q)) ⟶ Sp R := fun q => spMap (algebraMap R (Localization.Away (f q)))
  have hj : ∀ q, IsOpenImmersion (j q) := fun q => IsOpenImmersion.of_isLocalization (f q)
  let G := fun q => (Over.pullback (j q).isoOpensRange.inv).obj ((Over.pullback (j q)).obj B)
  have gp : ∀ q, IsGrpPullback (G q) ((Over.pullback (j q)).obj B) (j q).isoOpensRange.inv (pullback.fst _ _) :=
    fun q => isGrpPullback_pullback _ _
  have hM₁ := fun q => pull_isLB hM (pullback.fst B.hom (j q))
  have hB₁ := fun q => PolPull.isAbelianScheme_of_isGrpPullback hB (isGrpPullback_pullback B (j q))
  have key := fun q => pol_pull _ _ _ (G q) _ _ _ _ (hM₁ q) (pull_isLB (hM₁ q) _) (hB₁ q) (gp q)
    ((cls_eq_iff (pull_isLB (hM₁ q) _) (pull_isLB (hM₁ q) _)).1 rfl)
  refine CoverGlue.kTriv_of_cover (Sp R) (PrimeSpectrum R) (fun q => (j q).opensRange) B G
    (fun q => pullback.fst _ (j q).isoOpensRange.inv ≫ pullback.fst B.hom (j q)) ?_
    (fun q => ((gp q).comp (isGrpPullback_pullback B (j q))).congr (Scheme.Hom.isoOpensRange_inv_comp _) rfl)
    M _ hM (fun q => pull_isLB (hM₁ q) _) (fun q => ?_) hB (fun q => (key q).1) (fun q => (key q).2.2 (H q))
  · refine top_le_iff.1 fun q _ => TopologicalSpace.Opens.mem_iSup.2 ⟨q, ?_⟩
    have : q ∈ Set.range (PrimeSpectrum.comap (algebraMap R (Localization.Away (f q)))) := by
      rw [PrimeSpectrum.localization_away_comap_range (Localization.Away (f q)) (f q)]
      exact hf q
    exact this
  · rw [← cls_eq_iff (pull_isLB (hM₁ q) _) (pull_isLB hM _), cls_pull (hM₁ q), cls_pull hM, cls_pull hM, pull_comp]

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmplePrincipalDescendedBundleNoetherianStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relAmple_principal_descendedBundle_noetherian : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (P : Out.PolAV (Sp R)) (n : ℕ) (B : Over (Sp R)) [GrpObj B] (ψ : P.A ⟶ B) (M : LB B.left), (∀ m : ℕ, 0 < m → IsUnit (m : R)) → 0 < n → IsAbelianScheme B → M.IsLB → IsMonHom ψ → IsFinite ψ.left → Etale ψ.left → Surjective ψ.left → (∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R), Nat.card {x : Over.mk t ⟶ P.A // x ≫ ψ = 1} = n ^ P.g) → LBIso (lbPow P.L n) (M.pull ψ.left) → Out.RelAmple B M ∧ Out.KTriv B M := by
  first | exact @GlobalTheory.relAmple_kTriv_of_descent_family | exact GlobalTheory.relAmple_kTriv_of_descent_family | (intros; apply GlobalTheory.relAmple_kTriv_of_descent_family <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsOActDescendOfEtaleIsogeny
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

namespace GlobalTheory

theorem exists_oAct_descend_of_etale_isogeny :
    ∀ (O : Type) [CommRing O] (S : Scheme.{0}) [IsReduced S] (A B : Over S) [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B] (ψ : A ⟶ B) (a : OAct O A), IsAbelianScheme A → IsAbelianScheme B → IsMonHom ψ → IsFinite ψ.left → Etale ψ.left → Surjective ψ.left → (∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ S) (x : Over.mk t ⟶ A) (c : O), x ≫ ψ = 1 → (x ≫ a.act c) ≫ ψ = 1) → ∃ b : OAct O B, ∀ c, a.act c ≫ ψ = ψ ≫ b.act c := by
  intro O _ S _ A B _ _ _ _ ψ a hA hB hψ hf he hs hker
  have hsep : IsSeparated B.hom := by
    have := hB.proper
    infer_instance
  have key : ∀ c : O, ∃ g' : B ⟶ B, IsMonHom g' ∧ ψ ≫ g' = a.act c ≫ ψ ∧
      ∀ g'' : B ⟶ B, ψ ≫ g'' = a.act c ≫ ψ → g'' = g' := by
    intro c
    have := a.hom c
    refine GlobalTheory.T.exists_unique_factor_through_etale_isogeny_reduced S A B B ψ (a.act c ≫ ψ) hA hB hsep hψ hf he hs inferInstance ?_
    intro k _ _ t x hx
    rw [← Category.assoc]
    exact hker k t x c hx
  choose f hf1 hf2 hf3 using key
  refine ⟨⟨f, hf1, ?_, ?_, ?_⟩, fun c => (hf2 c).symm⟩
  · refine (hf3 1 _ ?_).symm
    rw [a.one, Category.id_comp, Category.comp_id]
  · intro x y
    refine (hf3 _ _ ?_).symm
    rw [← Category.assoc, hf2, Category.assoc, hf2, a.mul, Category.assoc]
  · intro x y
    refine (hf3 _ _ ?_).symm
    rw [MonObj.comp_mul, hf2, hf2, a.add]
    exact (map_mul (IsMonHom.monoidHom ψ A) _ _).symm

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsQuotientTripleFamilyReducedNoetherian
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

namespace GlobalTheory.HkFam

open CechPic

theorem exists_quotient_triple_family : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsNoetherianRing R] [IsReduced R] (t : SAB H (Sp R)) (g p : ℕ) (B : Over (Sp R)) [GrpObj B] (ψ : t.G ⟶ B) (M : LB B.left), (∀ m : ℕ, 0 < m → IsUnit (m : R)) → 0 < p → IsProper t.G.hom → SmoothOfRelativeDimension g t.G.hom → Out.RelAmple t.G t.PP.L → Out.KTriv t.G t.PP.L → IsAbelianScheme B → M.IsLB → IsMonHom ψ → IsFinite ψ.left → Etale ψ.left → Surjective ψ.left → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Sp R), Nat.card {z : Over.mk x ⟶ t.G // z ≫ ψ = 1} = p ^ (2 * g) ∧ ∀ z : Over.mk x ⟶ t.G, z ≫ ψ = 1 → z ^ p ^ 2 = 1 ∧ ∀ a, (z ≫ t.act.act a) ≫ ψ = 1) → LBIso (lbPow t.PP.L (p ^ 2)) (M.pull ψ.left) → ∃ (t' : SAB H (Sp R)) (ψ' : t.G ⟶ t'.G), IsProper t'.G.hom ∧ Out.RelAmple t'.G t'.PP.L ∧ Out.KTriv t'.G t'.PP.L ∧ IsIsogT t t' p ψ' ∧ ∀ (T : Over (Sp R)) (z : T ⟶ t.G), z ≫ ψ' = 1 ↔ z ≫ ψ = 1 := by
  intro E _ _ _ H R _ _ _ t g p B _ ψ M hR hp hprop hsm hamp hK hB hM hψ hf he hs hker hiso
  have laws : Out.Laws := GlobalTheory.firstFiveLaws.1
  have hA : IsAbelianScheme t.G := AbelianSchemeGerms.isAbelianScheme_of_proper t.G t.semi
  have hL := t.PP.isLB
  let P : Out.PolAV (Sp R) :=
    { A := t.G, isAb := hA, g := g, smoothDim := hsm, L := t.PP.L, isLB := hL,
      rigid := ⟨t.PP.rig, t.PP.rigGen⟩, sym := sym_of_isSymmetric t.PP t.sym, ample := hamp, ktriv := hK }
  have hn : 0 < p ^ 2 := pow_pos hp 2
  have := hB.comm
  have hred : IsReduced (Sp R) := inferInstance
  have hc : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Sp R),
      Nat.card {z : Over.mk x ⟶ t.G // z ≫ ψ = 1} = (p ^ 2) ^ g := fun k _ _ x => by
    rw [← pow_mul]; exact (hker k x).1
  have hMamp : Out.RelAmple B M := (GlobalTheory.T.relAmple_principal_descendedBundle_noetherian R P (p ^ 2) B ψ M hR hn hB hM hψ hf he hs hc hiso).1
  have hΘ : ∃ s : LB.Gen (Theta B M), s.IsGen := cube_of_relAmple _ B M hB hM hMamp
  obtain ⟨act, hact⟩ := GlobalTheory.exists_oAct_descend_of_etale_isogeny (𝓞 E) (Sp R) t.G B ψ t.act hA hB hψ hf he hs
    fun k _ _ x z c hz => ((hker k x).2 z hz).2 c
  have hα : ∀ a, ψ ≫ act.act a = t.act.act a ≫ ψ := fun a => (hact a).symm
  have hunit : IsUnit ((p ^ 2 : ℕ) : Γ(Sp R, ⊤)) := by
    have h := (hR _ hn).map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
    rwa [map_natCast] at h
  set l := cls t.PP.L hL with hl
  set m := cls M hM with hm
  have hψm : pull ψ.left m = (p ^ 2) • l := by
    rw [← cls_lbPow hL (p ^ 2) (LB.isLB_linComb hL _ _)]
    exact ((cls_eq_iff _ (pull_isLB hM _)).2 hiso).symm
  have lamψ : ∀ {T : Over (Sp R)} (u v : T ⟶ t.G), lam m (u ≫ ψ) (v ≫ ψ) = (p ^ 2) • lam l u v := fun u v => by
    rw [← lam_pull, hψm, lam_nsmul]
  have adj : ∀ a, LBIso (cubeLB B ![fst B B ≫ act.act a, snd B B] M)
      (cubeLB B ![fst B B, snd B B ≫ act.act (H.bar a)] M) := by
    intro a
    have := act.hom a
    have := act.hom (H.bar a)
    have adjA : ∀ {T : Over (Sp R)} (u v : T ⟶ t.G), lam l (u ≫ t.act.act a) v = lam l u (v ≫ t.act.act (H.bar a)) := by
      intro T u v
      have h := (cls_eq_iff (LB.isLB_linComb hL _ _) (LB.isLB_linComb hL _ _)).2 (t.adj a)
      have h' := congrArg (pull (lift u v).left)
        ((cls_cube_two hL _ _ _).symm.trans (h.trans (cls_cube_two hL _ _ _)))
      simpa only [pull_lam, lift_fst, lift_snd, lift_fst_assoc, lift_snd_assoc] using h'
    have adjψ : ∀ {T : Over (Sp R)} (u v : T ⟶ t.G),
        lam m ((u ≫ ψ) ≫ act.act a) (v ≫ ψ) = lam m (u ≫ ψ) ((v ≫ ψ) ≫ act.act (H.bar a)) := by
      intro T u v
      rw [Category.assoc, Category.assoc, hα, hα, ← Category.assoc, ← Category.assoc, lamψ, lamψ, adjA]
    have h₁ : (cubeLB B ![fst B B ≫ act.act a, snd B B] M).IsLB := LB.isLB_linComb hM _ _
    have h₂ : (cubeLB B ![fst B B, snd B B ≫ act.act (H.bar a)] M).IsLB := LB.isLB_linComb hM _ _
    have hN := LB.isLB_div h₂ h₁
    have val : ∀ {T : Over (Sp R)} (x y : T ⟶ B), lam m (x ≫ act.act a) y = lam m x (y ≫ act.act (H.bar a)) →
        ∃ s : ((LB.div (cubeLB B ![fst B B, snd B B ≫ act.act (H.bar a)] M)
          (cubeLB B ![fst B B ≫ act.act a, snd B B] M)).pull (lift x y).left).Gen, s.IsGen := by
      intro T x y h
      refine (cls_eq_zero_iff (pull_isLB hN _)).1 ?_
      rw [cls_pull hN, cls_div h₂ h₁, cls_cube_two hM, cls_cube_two hM, map_sub, pull_lam, pull_lam, lift_fst,
        lift_snd, lift_fst_assoc, lift_snd_assoc, ← hm, h, sub_self]
    refine GlobalTheory.T.triv_of_axes_triv_pullback_etale_isogeny (Sp R) t.G B ψ M _ (p ^ 2) hA hB hM hMamp hN hψ hf he hs hn hunit
      (fun k _ _ x z hz => ((hker k x).2 z hz).1) (val _ _ ?_) (val _ _ ?_) ?_
    · rw [MonObj.one_comp, lam_one_left, lam_one_left]
    · rw [MonObj.one_comp, lam_one_right, lam_one_right]
    · have e : ψ ⊗ₘ ψ = lift (fst t.G t.G ≫ ψ) (snd t.G t.G ≫ ψ) := by ext <;> simp
      rw [e]
      exact val _ _ (adjψ _ _)
  obtain ⟨PP, cub, hsym, hPP, -, hprim, hadj⟩ :=
    GlobalTheory.PrimNorm.exists_primitive_normalisation laws.globalFns E H _ B act M hB hM hΘ adj
  have hP' := PP.isLB
  have hpull : pull ψ.left (cls PP.L hP') = (p ^ 2) • l := by
    have h := (cls_eq_iff hL (LB.isLB_linComb hL _ _)).2 t.prim
    have h' := (cls_eq_iff hP' (LB.isLB_linComb hM _ _)).2 hPP
    have e : l = lam l (𝟙 _) (t.act.act H.w0) := h.trans (cls_cube_two hL _ _ _)
    have e' : cls PP.L hP' = lam m (𝟙 _) (act.act H.w0) := h'.trans (cls_cube_two hM _ _ _)
    rw [e', pull_lam, hα, Category.comp_id, ← Category.id_comp ψ, ← Category.assoc, Category.comp_id, lamψ, ← e]
  have hn' : (lbPow t.PP.L (p ^ 2)).IsLB := LB.isLB_linComb hL _ _
  have hfinal : LBIso (lbPow t.PP.L (p ^ 2)) (PP.L.pull ψ.left) := by
    rw [← cls_eq_iff hn' (pull_isLB hP' _), cls_lbPow hL, cls_pull hP', hpull]
  obtain ⟨a₃, a₄⟩ := GlobalTheory.T.relAmple_principal_descendedBundle_noetherian R P (p ^ 2) B ψ PP.L hR hn hB hP' hψ hf he hs hc hfinal
  exact ⟨{ G := B, semi := isSemiAbelian_of_isAbelianScheme B hB, act := act, PP := PP, cub := cub, sym := hsym,
           adj := hadj, prim := hprim }, ψ, hB.proper, a₃, a₄, ⟨hψ, hf, he, hs, hact, hfinal⟩, fun _ _ => Iff.rfl⟩

end GlobalTheory.HkFam
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsQuotientTripleFamilyReducedNoetherianStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_quotient_triple_family_reduced_noetherian : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsNoetherianRing R] [IsReduced R] (t : SAB H (Sp R)) (g p : ℕ) (B : Over (Sp R)) [GrpObj B] (ψ : t.G ⟶ B) (M : LB B.left), (∀ m : ℕ, 0 < m → IsUnit (m : R)) → 0 < p → IsProper t.G.hom → SmoothOfRelativeDimension g t.G.hom → Out.RelAmple t.G t.PP.L → Out.KTriv t.G t.PP.L → IsAbelianScheme B → M.IsLB → IsMonHom ψ → IsFinite ψ.left → Etale ψ.left → Surjective ψ.left → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Sp R), Nat.card {z : Over.mk x ⟶ t.G // z ≫ ψ = 1} = p ^ (2 * g) ∧ ∀ z : Over.mk x ⟶ t.G, z ≫ ψ = 1 → z ^ p ^ 2 = 1 ∧ ∀ a, (z ≫ t.act.act a) ≫ ψ = 1) → LBIso (lbPow t.PP.L (p ^ 2)) (M.pull ψ.left) → ∃ (t' : SAB H (Sp R)) (ψ' : t.G ⟶ t'.G), IsProper t'.G.hom ∧ Out.RelAmple t'.G t'.PP.L ∧ Out.KTriv t'.G t'.PP.L ∧ IsIsogT t t' p ψ' ∧ ∀ (T : Over (Sp R)) (z : T ⟶ t.G), z ≫ ψ' = 1 ↔ z ≫ ψ = 1 := by
  first | exact @GlobalTheory.HkFam.exists_quotient_triple_family | exact GlobalTheory.HkFam.exists_quotient_triple_family | (intros; apply GlobalTheory.HkFam.exists_quotient_triple_family <;> assumption)
end
