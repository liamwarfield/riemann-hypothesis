module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.OrdReadOf

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MCotanOne
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

private theorem tangent_of_form {κ B : Type} [Field κ] [CommRing B] [Algebra κ B] (ε : B →ₐ[κ] κ)
    (d : B →ₗ[κ] κ) (h1 : d 1 = 0) (h2 : ∀ x ∈ RingHom.ker ε.toRingHom ^ 2, d x = 0) :
    ∃ v : B →ₐ[κ] DualNumber κ, (TrivSqZeroExt.fstHom κ κ κ).comp v = ε ∧ ∀ x, (v x).snd = d x := by
  have hmem : ∀ x, x - algebraMap κ B (ε x) ∈ RingHom.ker ε.toRingHom := by
    intro x
    rw [RingHom.mem_ker]
    change ε (x - algebraMap κ B (ε x)) = 0
    rw [map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self]
  have key : ∀ x y, d (x * y) = ε x * d y + ε y * d x := by
    intro x y
    have hm : (x - algebraMap κ B (ε x)) * (y - algebraMap κ B (ε y)) ∈
        RingHom.ker ε.toRingHom ^ 2 := by
      rw [pow_two]
      exact Ideal.mul_mem_mul (hmem x) (hmem y)
    have hz := h2 _ hm
    have e : x * y = (x - algebraMap κ B (ε x)) * (y - algebraMap κ B (ε y)) + ε y • x
        + ε x • y - (ε x * ε y) • (1 : B) := by
      simp only [Algebra.smul_def, map_mul, mul_one]
      ring
    rw [e, map_sub, map_add (f := _), map_add (f := _), hz, map_smul, map_smul, map_smul, h1]
    simp only [smul_eq_mul]
    ring
  let f : B →ₗ[κ] DualNumber κ :=
    { toFun := fun x => TrivSqZeroExt.inl (ε x) + TrivSqZeroExt.inr (d x)
      map_add' := by
        intro x y
        ext <;> simp <;> ring
      map_smul' := by
        intro a x
        ext <;> simp }
  have hf : ∀ x, f x = TrivSqZeroExt.inl (ε x) + TrivSqZeroExt.inr (d x) := fun _ => rfl
  refine ⟨AlgHom.ofLinearMap f ?_ ?_, ?_, ?_⟩
  · rw [hf]
    ext <;> simp [h1]
  · intro x y
    rw [hf, hf, hf]
    ext <;> simp [key] <;> ring
  · ext x
    simp [hf]
  · intro x
    simp [hf]

theorem UpperTheory.Gal.crystallineComparison.Mod.cotanOne_of :
    CotanOne := by
  intro κ B _ _ _ ε v₀ hall
  classical
  let m := RingHom.ker ε.toRingHom
  let s : B → κ := fun x => (v₀ x).snd
  have hs_sub : ∀ x y, s (x - y) = s x - s y := by
    intro x y
    simp [s]
  have hs_smul : ∀ (a : κ) x, s (a • x) = a * s x := by
    intro a x
    simp [s]
  have hkill : ∀ y ∈ m, s y = 0 → y ∈ m ^ 2 := by
    intro y hy hsy
    by_contra hy2
    let P : Submodule κ B := (m ^ 2).restrictScalars κ ⊔ Submodule.span κ {(1 : B)}
    have hyP : y ∉ P := by
      intro hyP
      obtain ⟨z, hz, w, hw, hzw⟩ := Submodule.mem_sup.1 hyP
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hw
      have hz' : z ∈ m ^ 2 := hz
      have hzm : z ∈ m := Ideal.pow_le_self two_ne_zero hz'
      have e1 : ε y = ε z + a * ε 1 := by
        rw [← hzw, map_add (f := _), map_smul, smul_eq_mul]
      have hεy : ε y = 0 := hy
      have hεz : ε z = 0 := hzm
      simp only [hεy, hεz, _root_.map_one, zero_add] at e1
      have ha : a = 0 := by simpa using e1.symm
      apply hy2
      rw [← hzw, ha, zero_smul, add_zero]
      exact hz'
    obtain ⟨d, hdy, hdP⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hyP inferInstance
    have hdP' : ∀ p ∈ P, d p = 0 := by
      intro p hp
      have h3 : d p ∈ Submodule.map d P := ⟨p, hp, rfl⟩
      rw [hdP, Submodule.mem_bot] at h3
      exact h3
    have hd1 : d 1 = 0 := hdP' 1 (Submodule.mem_sup_right (Submodule.mem_span_singleton_self 1))
    have hd2 : ∀ x ∈ m ^ 2, d x = 0 := fun x hx => hdP' x (Submodule.mem_sup_left hx)
    obtain ⟨v, hv, hvd⟩ := tangent_of_form ε d hd1 hd2
    obtain ⟨c, hc⟩ := hall v hv
    apply hdy
    rw [← hvd, hc]
    change c * s y = 0
    rw [hsy, mul_zero]
  by_cases hex : ∃ t ∈ m, s t ≠ 0
  · obtain ⟨t, ht, hst⟩ := hex
    refine ⟨t, ht, ?_⟩
    intro x hx
    have hy : x - (s x / s t) • t ∈ m := by
      refine m.sub_mem hx ?_
      rw [Algebra.smul_def]
      exact m.mul_mem_left _ ht
    have hsy : s (x - (s x / s t) • t) = 0 := by
      rw [hs_sub, hs_smul, div_mul_cancel₀ _ hst, sub_self]
    have h2 := hkill _ hy hsy
    have e : x = (s x / s t) • t + (x - (s x / s t) • t) := by abel
    rw [e]
    refine Ideal.add_mem _ (Ideal.mem_sup_left ?_) (Ideal.mem_sup_right h2)
    rw [Algebra.smul_def]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self t)
  · push_neg at hex
    refine ⟨0, m.zero_mem, ?_⟩
    intro x hx
    exact Ideal.mem_sup_right (hkill x hx (hex x hx))
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MKillLocal
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

namespace UpperTheory.Gal.crystallineComparison.Mod

private theorem away_local {B : Type} [CommRing B] (f : B) (p : PrimeSpectrum B)
    (hp : p ∈ PrimeSpectrum.basicOpen f) (hs : (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum B)) ⊆ {p}) :
    IsLocalRing (Localization.Away f) := by
  have hrange := PrimeSpectrum.localization_away_comap_range (Localization.Away f) f
  have hinj := PrimeSpectrum.localization_comap_injective (Localization.Away f) (Submonoid.powers f)
  have key : ∀ q : PrimeSpectrum (Localization.Away f),
      PrimeSpectrum.comap (algebraMap B (Localization.Away f)) q = p := by
    intro q
    have hq : PrimeSpectrum.comap (algebraMap B (Localization.Away f)) q ∈
        (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum B)) := by
      rw [← hrange]
      exact ⟨q, rfl⟩
    exact hs hq
  obtain ⟨q, -⟩ : p ∈ Set.range (PrimeSpectrum.comap (algebraMap B (Localization.Away f))) := by
    rw [hrange]
    exact hp
  obtain ⟨M, hM, -⟩ := Ideal.exists_le_maximal q.asIdeal q.2.ne_top
  refine IsLocalRing.of_unique_max_ideal ⟨M, hM, fun N hN => ?_⟩
  have h := hinj ((key ⟨N, hN.isPrime⟩).trans (key ⟨M, hM.isPrime⟩).symm)
  exact congrArg PrimeSpectrum.asIdeal h

private theorem exists_eps (κ B : Type) [Field κ] [IsAlgClosed κ] [CommRing B] [Algebra κ B] [Module.Finite κ B]
    (f : B) (m : Ideal B) [hm : m.IsMaximal] (hf : f ∉ m) :
    Nonempty (Localization.Away f →ₐ[κ] κ) := by
  haveI : Module.Finite κ (B ⧸ m) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ κ m).toLinearMap Ideal.Quotient.mk_surjective
  haveI : Algebra.IsAlgebraic κ (B ⧸ m) := Algebra.IsAlgebraic.of_finite κ (B ⧸ m)
  let φ : B ⧸ m →ₐ[κ] κ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  let ψ : B →ₐ[κ] κ := φ.comp (Ideal.Quotient.mkₐ κ m)
  refine ⟨IsLocalization.liftAlgHom (M := Submonoid.powers f) (f := ψ) ?_⟩
  rintro ⟨y, n, rfl⟩
  simp only [map_pow]
  refine IsUnit.pow _ (isUnit_iff_ne_zero.mpr ?_)
  intro h
  apply hf
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  apply φ.toRingHom.injective
  rw [map_zero]
  exact h

private theorem local_kill (κ : Type) [Field κ] (A A' : Over (Sp κ)) [GrpObj A] [GrpObj A'] (χ : A ⟶ A') [IsMonHom χ]
    (P : ∀ T : Over (Sp κ), (T ⟶ A) → Prop) (hsub : IsSub A P)
    (h1 : ∀ g : 𝟙_ (Over (Sp κ)) ⟶ A, P _ g → g ≫ χ = 1)
    (Λ : Type) [CommRing Λ] [Algebra κ Λ] (ε : Λ →ₐ[κ] κ)
    (h2 : ∀ g : algPt κ Λ ⟶ A, P _ g → Inf ε g → g ≫ χ = 1)
    (g : algPt κ Λ ⟶ A) (hP : ∀ (T : Over (Sp κ)) (y : T ⟶ algPt κ Λ), P T (y ≫ g)) : g ≫ χ = 1 := by
  let s : 𝟙_ (Over (Sp κ)) ⟶ algPt κ Λ := Over.homMk (spMap ε.toRingHom) (by
    show Spec.map _ ≫ Spec.map _ = 𝟙 _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← Spec.map_id]
    congr 1
    ext x
    simp)
  let π : algPt κ Λ ⟶ 𝟙_ (Over (Sp κ)) := toUnit _
  have hsπ : s ≫ π = 𝟙 _ := toUnit_unique _ _
  let g0 : algPt κ Λ ⟶ A := π ≫ s ≫ g
  have hg : P _ g := by simpa using hP _ (𝟙 _)
  have hg0 : P _ g0 := by simpa [g0] using hP _ (π ≫ s)
  have hsg : P _ (s ≫ g) := hP _ s
  have hh : P _ (g * g0⁻¹) := ((hsub _).2 _ _ hg hg0)
  have hs1 : s ≫ (g * g0⁻¹) = 1 := by
    rw [MonObj.comp_mul, GrpObj.comp_inv]
    simp only [g0, ← Category.assoc, hsπ, Category.id_comp, mul_inv_cancel]
  have hinf : Inf ε (g * g0⁻¹) := by
    have := congrArg Over.Hom.left hs1
    simpa [Inf, s] using this
  have e1 : (g * g0⁻¹) ≫ χ = 1 := h2 _ hh hinf
  have e2 : g0 ≫ χ = 1 := by
    simp only [g0, Category.assoc, h1 _ hsg, MonObj.comp_one]
  have : g = (g * g0⁻¹) * g0 := by rw [inv_mul_cancel_right]
  rw [this, MonObj.mul_comp, e1, e2]
  exact _root_.mul_one _

theorem killLocal_of : KillLocal := by
  intro κ _ _ A A' _ _ χ hχ P d hrep hsub h1 h2 T g hg
  obtain ⟨B, _, _, hfin, hfree, -, i, hmono, hi⟩ := hrep
  obtain ⟨y, rfl⟩ := (hi T g).2 hg
  suffices hmain : i ≫ χ = 1 by rw [Category.assoc, hmain, comp_one]
  haveI : IsArtinianRing B := IsArtinianRing.of_finite κ B
  have hpt : ∀ p : PrimeSpectrum B, ∃ f : B, p ∈ PrimeSpectrum.basicOpen f ∧
      (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum B)) ⊆ {p} := by
    intro p
    obtain ⟨_, ⟨f, rfl⟩, hp, hs⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
      (Set.mem_singleton p) (isOpen_discrete _)
    exact ⟨f, hp, hs⟩
  choose s hs hs' using hpt
  have hspan : Ideal.span (Set.range s) = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    exact hs ⟨m, hm.isPrime⟩ (hle (Ideal.subset_span ⟨_, rfl⟩))
  apply Over.OverMorphism.ext
  refine Scheme.Cover.hom_ext (Scheme.affineOpenCoverOfSpanRangeEqTop (R := .of B) s hspan).openCover _ _ fun p => ?_
  change spMap (algebraMap B (Localization.Away (s p))) ≫ _ = spMap (algebraMap B (Localization.Away (s p))) ≫ _
  haveI := away_local (s p) p (hs p) (hs' p)
  haveI hmax : p.asIdeal.IsMaximal := p.2.isMaximal'
  obtain ⟨ε⟩ := exists_eps κ B (s p) p.asIdeal (hs p)
  let j : algPt κ (Localization.Away (s p)) ⟶ algPt κ B := Over.homMk (spMap (algebraMap B (Localization.Away (s p)))) (by
    change spMap (algebraMap B (Localization.Away (s p))) ≫ spMap (algebraMap κ B) = spMap (algebraMap κ (Localization.Away (s p)))
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq])
  have hk : (j ≫ i) ≫ χ = 1 := local_kill κ A A' χ P hsub h1 _ ε (fun g hg hI => h2 _ ε g hg hI) (j ≫ i)
    (fun T y => (hi T _).1 ⟨y ≫ j, by simp⟩)
  have hk' : j ≫ i ≫ χ = j ≫ 1 := by rw [comp_one, ← Category.assoc, hk]
  exact congrArg (fun t => t.left) hk'

end UpperTheory.Gal.crystallineComparison.Mod
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MFFRead
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

namespace UpperTheory.Gal.crystallineComparison.Mod

private theorem count_eq (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (hab : IsAbelianScheme A)
    (K : Over S) (i : K ⟶ A) (hm : Mono i) (hfin : IsFinite K.hom) (hfl : Flat K.hom) (c : ℕ) (hi : i ^ c = 1)
    (P : ∀ T : Over S, (T ⟶ A) → Prop) (hP : ∀ (T : Over S) (g : T ⟶ A), InSub i g ↔ P T g)
    (V : Type) [CommRing V] [IsDomain V] [ValuationRing V] [IsAlgClosed (FractionRing V)] (hc : (c : V) ≠ 0)
    (z : Sp V ⟶ S) (B : Type) [CommRing B] [Algebra V B] [Module.Finite V B] [Module.Free V B] (k : Sp B ⟶ K.left)
    (hk : IsPullback k (spMap (algebraMap V B)) K.hom z) :
    Module.finrank V B = Nat.card {g : Over.mk (spMap (algebraMap V (FractionRing V)) ≫ z) ⟶ A // P _ g} := by
  haveI := hfin
  haveI := hfl
  have hcF : ((c : FractionRing V)) ≠ 0 := by
    intro h
    apply hc
    apply IsFractionRing.injective V (FractionRing V)
    simpa using h
  let pt : Sp (FractionRing V) := (⊥ : PrimeSpectrum (FractionRing V))
  have h1 := GlobalTheory.T.finrank_finiteFlat_torsion_subscheme_eq_card_points S A hab K i c hm hfin hfl hi (FractionRing V) hcF
    (spMap (algebraMap V (FractionRing V)) ≫ z) pt
  have h2 := Scheme.Hom.finrank_of_isPullback k (spMap (algebraMap V B)) K.hom z hk
    (spMap (algebraMap V (FractionRing V)) pt)
  have h3 := Scheme.Hom.finrank_SpecMap_algebraMap V B (spMap (algebraMap V (FractionRing V)) pt)
  rw [Scheme.Hom.comp_apply] at h1
  have h4 : Nat.card {g : Over.mk (spMap (algebraMap V (FractionRing V)) ≫ z) ⟶ A // P _ g} =
      Nat.card (Over.mk (spMap (algebraMap V (FractionRing V)) ≫ z) ⟶ K) := by
    refine Nat.card_congr (Equiv.ofBijective (fun g => ⟨g ≫ i, (hP _ _).1 ⟨g, rfl⟩⟩) ⟨?_, ?_⟩).symm
    · intro a b hab'
      exact (cancel_mono i).1 (congrArg Subtype.val hab')
    · rintro ⟨g, hg⟩
      obtain ⟨y, hy⟩ := (hP _ _).2 hg
      exact ⟨y, Subtype.ext hy⟩
  rw [h4, ← h1, ← h2]
  unfold spMap at h3 ⊢
  rw [h3, Module.rankAtStalk_eq_finrank_of_free]
  rfl

theorem fFRead_of : AlgOf → FFRead := by
  intro hAlg S A _ _ hab P hRep c hc V _ _ _ _ hcV z A' φ hpb P' hP'
  obtain ⟨K, i, hm, hfin, hfl, hiP⟩ := hRep
  haveI := hfin
  haveI := hfl
  have hi : i ^ c = 1 := hc K i ((hiP K i).1 ⟨𝟙 _, by simp⟩)
  obtain ⟨BV, _, _, kV, _, _, hkV⟩ := hAlg S K.left K.hom hfin hfl V z
  have hcount := count_eq S A hab K i hm hfin hfl c hi P hiP V hcV z BV kV hkV
  obtain ⟨Bk, _, _, kk, _, _, hkk⟩ :=
    hAlg S K.left K.hom hfin hfl (IsLocalRing.ResidueField V) (resPt V ≫ z)
  have hr : Module.finrank (IsLocalRing.ResidueField V) Bk = Module.finrank V BV := by
    let q : Sp (IsLocalRing.ResidueField V) := (⊥ : PrimeSpectrum (IsLocalRing.ResidueField V))
    have e1 := Scheme.Hom.finrank_of_isPullback kk _ K.hom (resPt V ≫ z) hkk q
    have e2 := Scheme.Hom.finrank_of_isPullback kV _ K.hom z hkV (resPt V q)
    have e3 := Scheme.Hom.finrank_SpecMap_algebraMap (IsLocalRing.ResidueField V) Bk q
    have e4 := Scheme.Hom.finrank_SpecMap_algebraMap V BV (resPt V q)
    rw [Scheme.Hom.comp_apply] at e1
    unfold spMap at e1 e2
    rw [e3, Module.rankAtStalk_eq_finrank_of_free] at e1
    rw [e4, Module.rankAtStalk_eq_finrank_of_free] at e2
    exact e1.trans e2.symm
  have wsq : (kk ≫ i.left) ≫ A.hom = spMap (algebraMap (IsLocalRing.ResidueField V) Bk) ≫ (resPt V ≫ z) := by
    rw [Category.assoc, Over.w i]
    exact hkk.w
  have hlf : hpb.lift _ _ wsq ≫ φ = kk ≫ i.left := hpb.lift_fst _ _ wsq
  have hls : hpb.lift _ _ wsq ≫ A'.hom = spMap (algebraMap (IsLocalRing.ResidueField V) Bk) :=
    hpb.lift_snd _ _ wsq
  have hlm : Mono (hpb.lift _ _ wsq) := by
    constructor
    intro X a b hab'
    apply hkk.hom_ext
    · haveI := Over.mono_left_of_mono i
      have h1 := congrArg (· ≫ φ) hab'
      simp only [Category.assoc, hlf] at h1
      simpa only [Category.assoc] using (cancel_mono i.left).1 (by simpa only [Category.assoc] using h1)
    · have h1 := congrArg (· ≫ A'.hom) hab'
      simpa only [Category.assoc, hls] using h1
  refine ⟨Bk, inferInstance, inferInstance, inferInstance, inferInstance, hr.trans hcount,
    Over.homMk (U := Over.mk (spMap (algebraMap (IsLocalRing.ResidueField V) Bk))) (hpb.lift _ _ wsq) hls,
    ?_, ?_⟩
  · constructor
    intro X a b hab'
    ext
    exact (cancel_mono (hpb.lift _ _ wsq)).1 (by simpa using congrArg Over.Hom.left hab')
  · intro T g
    have hw : (g.left ≫ φ) ≫ A.hom = (Over.mk (T.hom ≫ resPt V ≫ z)).hom := by
      rw [Category.assoc, hpb.w, ← Category.assoc, Over.w g]
      rfl
    rw [hP' T g (Over.homMk (g.left ≫ φ) hw) rfl, ← hiP]
    constructor
    · rintro ⟨y, hy⟩
      have hyl := congrArg Over.Hom.left hy
      simp only [Over.comp_left, Over.homMk_left] at hyl
      have hw2 : (y.left ≫ kk) ≫ K.hom = (Over.mk (T.hom ≫ resPt V ≫ z)).hom := by
        rw [Category.assoc, hkk.w]
        simpa using congrArg (· ≫ resPt V ≫ z) (Over.w y)
      refine ⟨Over.homMk (y.left ≫ kk) hw2, ?_⟩
      ext
      simp only [Over.comp_left, Over.homMk_left, Category.assoc]
      rw [← hyl, Category.assoc, hlf]
    · rintro ⟨y, hy⟩
      have hyl := congrArg Over.Hom.left hy
      simp only [Over.comp_left, Over.homMk_left] at hyl
      have hw3 : y.left ≫ K.hom = T.hom ≫ resPt V ≫ z := by
        simpa using Over.w y
      refine ⟨Over.homMk (hkk.lift y.left T.hom hw3) (by simpa using hkk.lift_snd _ _ hw3), ?_⟩
      ext
      simp only [Over.comp_left, Over.homMk_left]
      apply hpb.hom_ext
      · rw [Category.assoc, hlf, ← Category.assoc, hkk.lift_fst, hyl]
      · rw [Category.assoc, hls, hkk.lift_snd]
        simpa using (Over.w g).symm

end UpperTheory.Gal.crystallineComparison.Mod
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MRepHomog
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

namespace UpperTheory.Gal.crystallineComparison.Mod

private lemma spMap_comp' {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  dsimp only [spMap]
  rw [← Spec.map_comp]
  rfl

private lemma spMap_id' (R : Type) [CommRing R] : spMap (RingHom.id R) = 𝟙 (Sp R) := by
  simp [spMap]

private lemma spMap_inj {R S : Type} [CommRing R] [CommRing S] {f g : R →+* S} (h : spMap f = spMap g) : f = g := by
  have h' : CommRingCat.ofHom f = CommRingCat.ofHom g := Spec.map_injective h
  exact congrArg CommRingCat.Hom.hom h'

private lemma exists_algHom {κ B C : Type} [Field κ] [CommRing B] [CommRing C] [Algebra κ B] [Algebra κ C]
    (f : Sp C ⟶ Sp B) (hf : f ≫ spMap (algebraMap κ B) = spMap (algebraMap κ C)) :
    ∃ φ : B →ₐ[κ] C, spMap φ.toRingHom = f := by
  obtain ⟨φ, rfl⟩ : ∃ φ, f = Spec.map φ := ⟨Spec.preimage f, (Spec.map_preimage f).symm⟩
  have hφ : φ.hom.comp (algebraMap κ B) = algebraMap κ C := by
    apply spMap_inj
    rw [← spMap_comp']
    exact hf
  exact ⟨{ toRingHom := φ.hom, commutes' := fun r => RingHom.congr_fun hφ r }, rfl⟩

private noncomputable def ptOf {κ B : Type} [Field κ] [CommRing B] [Algebra κ B] (ε : B →ₐ[κ] κ) :
    𝟙_ (Over (Sp κ)) ⟶ algPt κ B :=
  Over.homMk (spMap ε.toRingHom) (by
    show spMap ε.toRingHom ≫ spMap (algebraMap κ B) = 𝟙 _
    rw [spMap_comp', ← spMap_id']
    congr 1
    ext r
    simp)

private lemma ptOf_surj {κ B : Type} [Field κ] [CommRing B] [Algebra κ B] (y : 𝟙_ (Over (Sp κ)) ⟶ algPt κ B) :
    ∃ ε : B →ₐ[κ] κ, ptOf ε = y := by
  obtain ⟨ε, hε⟩ := exists_algHom (C := κ) y.left (by
    rw [Algebra.algebraMap_self, spMap_id']
    exact Over.w y)
  refine ⟨ε, Over.OverMorphism.ext ?_⟩
  rw [← hε]
  rfl

private lemma ptOf_inj {κ B : Type} [Field κ] [CommRing B] [Algebra κ B] {ε ε' : B →ₐ[κ] κ}
    (h : ptOf ε = ptOf ε') : ε = ε' := by
  have h1 : spMap ε.toRingHom = spMap ε'.toRingHom := congrArg CommaMorphism.left h
  have h2 := spMap_inj h1
  ext x
  exact RingHom.congr_fun h2 x

end UpperTheory.Gal.crystallineComparison.Mod

theorem UpperTheory.Gal.crystallineComparison.Mod.repHomog_of :
    RepHomog := by
  intro κ _ A _ P hSub B _ _ i hmono hiff
  haveI : Mono i := hmono
  refine ⟨?_, ?_⟩
  · refine Nat.card_congr (Equiv.ofBijective
      (fun ε => (⟨ptOf ε ≫ i, (hiff _ _).1 ⟨_, rfl⟩⟩ : { g // P (𝟙_ (Over (Sp κ))) g })) ⟨?_, ?_⟩)
    · intro a b h
      apply ptOf_inj
      exact (cancel_mono i).1 (congrArg Subtype.val h)
    · rintro ⟨g, hg⟩
      obtain ⟨y, hy⟩ := (hiff _ _).2 hg
      obtain ⟨ε, rfl⟩ := ptOf_surj y
      exact ⟨ε, Subtype.ext hy⟩
  · obtain ⟨y, hy⟩ := (hiff _ _).2 (hSub (𝟙_ (Over (Sp κ)))).1
    obtain ⟨ε₀, rfl⟩ := ptOf_surj y
    refine ⟨ε₀, ?_, fun ε => ?_⟩
    · show spMap ε₀.toRingHom ≫ i.left = (1 : 𝟙_ (Over (Sp κ)) ⟶ A).left
      rw [← hy]
      rfl
    · let c : algPt κ B ⟶ A := toUnit (algPt κ B) ≫ ptOf ε ≫ i
      have hc : c = toUnit (algPt κ B) ≫ ptOf ε ≫ i := rfl
      have hcP : P _ c := (hiff _ _).1 ⟨toUnit _ ≫ ptOf ε, by rw [hc, Category.assoc]⟩
      have hiP : P _ i := (hiff _ _).1 ⟨𝟙 _, Category.id_comp _⟩
      have hcinvP : P _ c⁻¹ := by
        have h' := (hSub (algPt κ B)).2 1 c (hSub _).1 hcP
        simpa using h'
      have hm : P _ (i * c) := by
        have h' := (hSub (algPt κ B)).2 i c⁻¹ hiP hcinvP
        simpa using h'
      have hm' : P _ (i * c⁻¹) := (hSub _).2 i c hiP hcP
      obtain ⟨s, hs⟩ := (hiff _ _).2 hm
      obtain ⟨s', hs'⟩ := (hiff _ _).2 hm'
      have hsc : ∀ t : algPt κ B ⟶ algPt κ B, t ≫ c = c := by
        intro t
        rw [hc, ← Category.assoc, comp_toUnit]
      have h1 : s ≫ s' = 𝟙 _ := by
        apply (cancel_mono i).1
        rw [Category.assoc, hs', comp_mul, hs, GrpObj.comp_inv, hsc, Category.id_comp,
          mul_inv_cancel_right]
      have h2 : s' ≫ s = 𝟙 _ := by
        apply (cancel_mono i).1
        rw [Category.assoc, hs, comp_mul, hs', hsc, Category.id_comp, inv_mul_cancel_right]
      have hpt : ptOf ε₀ ≫ s = ptOf ε := by
        apply (cancel_mono i).1
        rw [Category.assoc, hs, comp_mul, hy, _root_.one_mul, hc, ← Category.assoc,
          toUnit_unique (ptOf ε₀ ≫ toUnit _) (𝟙 _), Category.id_comp]
      obtain ⟨τ, hτ⟩ := exists_algHom (C := B) s.left (Over.w s)
      obtain ⟨τ', hτ'⟩ := exists_algHom (C := B) s'.left (Over.w s')
      have e1 : τ.comp τ' = AlgHom.id κ B := by
        have h' : spMap (τ.comp τ').toRingHom = spMap (RingHom.id B) := by
          rw [spMap_id']
          show spMap (τ.toRingHom.comp τ'.toRingHom) = _
          rw [← spMap_comp', hτ, hτ']
          exact congrArg CommaMorphism.left h1
        exact AlgHom.ext fun x => RingHom.congr_fun (spMap_inj h') x
      have e2 : τ'.comp τ = AlgHom.id κ B := by
        have h' : spMap (τ'.comp τ).toRingHom = spMap (RingHom.id B) := by
          rw [spMap_id']
          show spMap (τ'.toRingHom.comp τ.toRingHom) = _
          rw [← spMap_comp', hτ, hτ']
          exact congrArg CommaMorphism.left h2
        exact AlgHom.ext fun x => RingHom.congr_fun (spMap_inj h') x
      refine ⟨AlgEquiv.ofAlgHom τ τ' e1 e2, ?_⟩
      rw [AlgEquiv.coe_algHom_ofAlgHom]
      apply ptOf_inj
      apply Over.OverMorphism.ext
      show spMap (ε₀.toRingHom.comp τ.toRingHom) = (ptOf ε).left
      rw [← hpt]
      show _ = spMap ε₀.toRingHom ≫ s.left
      rw [← hτ, spMap_comp']
end
