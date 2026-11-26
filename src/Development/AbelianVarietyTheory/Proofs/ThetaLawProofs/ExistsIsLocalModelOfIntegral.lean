module

public import Development.AbelianVarietyTheory.Statements.FundamentalDomains.KeyFormulaPowOfKeyFormula
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsMulPullSec
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKeyPBRing
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeQuotientTriple
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.BasisPowerSectionsLocalBaseChange
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRootOfKeyFormula

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsIsLocalModelOfIntegral
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.KeyPow

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem exists_sec_fibre_ne_zero (hT : Out.SecTwistSt) {S X : Scheme.{0}} (P : Out.PolAV S) {R : Type} [CommRing R]
    [IsLocalRing R] {t : Sp R ⟶ S} {φ : X ⟶ P.A.left} {q : X ⟶ Sp R} (hp : IsPullback φ q P.A.hom t) :
    ∃ th : (P.L.pull φ).Sec, ∀ s : Sp R, ∃ z : X, q z = s ∧ z ∈ Out.nonzeroLocus th := by
  have := P.isAb.comm
  have := P.isAb.smooth
  let k := IsLocalRing.ResidueField R
  let T : Over S := Over.mk t
  let T' : Over S := Over.mk (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)) ≫ t)
  let ν : T' ⟶ T := Over.homMk (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) rfl
  have e : ∀ T : Over S, Out.translPt P.A (1 : T ⟶ P.A) = snd T P.A := fun T => by
    show (fst T P.A ≫ 1) * snd T P.A = _
    rw [MonObj.comp_one, _root_.one_mul]
  obtain ⟨⟨b, hb⟩, -⟩ := hT _ P 1 le_rfl k (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)) ≫ t) 1
  obtain ⟨-, hl⟩ := hT _ P 1 le_rfl R t 1
  have i₀ : Fin (1 ^ P.g) := ⟨0, by simp⟩
  have su : ∀ {M : Type} [AddCommMonoid M] (q : Fin (1 ^ P.g) → M), ∑ i, q i = q i₀ := fun q =>
    Finset.sum_eq_single i₀ (fun a _ h => absurd (Fin.ext (by have := a.2; have := i₀.2; simp at *; omega)) h) (by simp)
  have nz : ∃ j, (b i₀).f j ≠ 0 := by
    by_contra b0
    push Not at b0
    obtain ⟨r, -, hu⟩ := hb (b i₀)
    have := (hu (fun _ => 0) fun k => (b0 k).trans ((su _).trans
      ((congrArg (_ * ·) (b0 k)).trans (mul_zero _))).symm).trans (hu (fun _ => 1) fun k => (b0 k).trans
      ((su _).trans ((congrArg (_ * ·) (b0 k)).trans (mul_zero _))).symm).symm
    exact zero_ne_one ((Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.symm.injective
      ((map_zero _).trans ((congrFun this i₀).trans (map_one _).symm)))
  have : Smooth (fst T' P.A).left := inferInstanceAs (Smooth (pullback.fst T'.hom P.A.hom))
  have : IsReduced (T' ⊗ P.A).left := isReduced_scheme_of_smooth_of_isIntegrallyClosed k (fst T' P.A).left
  obtain ⟨j, hj⟩ := nz
  obtain ⟨z, hz⟩ : ∃ z, z ∈ (T' ⊗ P.A).left.basicOpen ((b i₀).f j) := by
    by_contra hn
    exact hj ((basicOpen_eq_bot_iff _).1 (eq_bot_iff.2 fun z hz => hn ⟨z, hz⟩))
  have hν : (ν ▷ P.A).left ≫ (snd T P.A).left = (snd T' P.A).left := congrArg (fun q => q.left) (whiskerRight_snd ν P.A)
  have hν' : (ν ▷ P.A).left ≫ (fst T P.A).left = (fst T' P.A).left ≫ ν.left :=
    congrArg (fun q => q.left) (whiskerRight_fst ν P.A)
  obtain ⟨sb, hsb⟩ := exists_sec P.isLB (K' := Fin 2)
    (φ' := fun k => (ν ▷ P.A).left ≫ ![(snd T P.A).left, (Out.translPt P.A (1 : T ⟶ P.A)).left] k)
    (ε' := ![((1 : ℕ) : ℤ) - 1, 1]) (fun U _ k => by
      rw [e, e, Fin.prod_univ_two, Fin.prod_univ_two]
      exact congrArg₂ (· * ·) (congrArg (fun f => k f ^ _) hν.symm) (congrArg (fun f => k f ^ _) hν.symm)) (b i₀)
  obtain ⟨s, hs⟩ := hl sb
  have hz' : (ν ▷ P.A).left z ∈ Out.nonzeroLocus s := by
    choose J hJ using fun χ : (T' ⊗ P.A).left ⟶ P.A.left => exists_chart P.isLB (χ z)
    have u := (MulPullSec.mem_nonzeroLocus_iff (b i₀) (𝟙 _) z hJ).1 (Opens.mem_iSup.2 ⟨j, hz⟩)
    rw [← hsb _ _ z J hJ] at u
    have hm := Good.mem hJ (fun k => (ν ▷ P.A).left ≫ ![(snd T P.A).left, (Out.translPt P.A (1 : T ⟶ P.A)).left] k) (𝟙 _)
    have hm' := Out.wchart_comp_le P.L _ _ _ hm
    have u' := (congrArg IsUnit ((congrArg (gs _ z _) (hs _)).trans
      ((gs_res _ z _ hm _).trans (gs_pull (𝟙 _) (ν ▷ P.A).left z _ hm' _)))).mp u
    exact Opens.mem_iSup.2 ⟨_, (MulPullSec.isUnit_gs_iff (𝟙 _ ≫ (ν ▷ P.A).left) z _ hm' _).1 u'⟩
  let ρ : X ⟶ (T ⊗ P.A).left := pullback.lift q φ hp.w.symm
  have ρ₂ : ρ ≫ (snd T P.A).left = φ := pullback.lift_snd _ _ _
  have ρ₁ : ρ ≫ (fst T P.A).left = q := pullback.lift_fst _ _ _
  let σ : (T ⊗ P.A).left ⟶ X := hp.lift (snd T P.A).left (fst T P.A).left pullback.condition.symm
  have σ₂ : σ ≫ φ = (snd T P.A).left := hp.lift_fst _ _ _
  have σ₁ : σ ≫ q = (fst T P.A).left := hp.lift_snd _ _ _
  have σρ : σ ≫ ρ = 𝟙 _ := by
    apply pullback.hom_ext
    · exact (Category.assoc _ _ _).trans ((congrArg (σ ≫ ·) ρ₁).trans (σ₁.trans (Category.id_comp _).symm))
    · exact (Category.assoc _ _ _).trans ((congrArg (σ ≫ ·) ρ₂).trans (σ₂.trans (Category.id_comp _).symm))
  have h1 : (LB.oneGen P.L (Y := X)).IsGen := fun i j =>
    (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm
  obtain ⟨th, hth⟩ := exists_sec P.isLB (K' := PUnit) (φ' := fun _ => φ) (ε' := fun _ => 1) (fun U _ k => by
      rw [e, Fintype.prod_sum_type, Fin.prod_univ_two, Fintype.prod_empty, Fintype.prod_unique]
      show k (ρ ≫ (snd T P.A).left) ^ (((1 : ℕ) : ℤ) - 1) * k (ρ ≫ (snd T P.A).left) ^ (1 : ℤ) * 1 = k φ ^ (1 : ℤ)
      rw [ρ₂]; simp) (pullMulSec s ρ _ h1)
  have hy : σ ((ν ▷ P.A).left z) ∈ Out.nonzeroLocus th := by
    choose J hJ using fun χ : (T ⊗ P.A).left ⟶ P.A.left => exists_chart P.isLB (χ ((ν ▷ P.A).left z))
    refine (MulPullSec.mem_nonzeroLocus_iff th σ _ hJ).2 ?_
    rw [hth _ _ _ J hJ, sval_pullMulSec s ρ _ _ _ _ hJ, Units.isUnit_mul_units, σρ]
    exact (MulPullSec.mem_nonzeroLocus_iff s (𝟙 _) _ hJ).1 hz'
  have hc : q (σ ((ν ▷ P.A).left z)) = IsLocalRing.closedPoint R := by
    refine (congrArg (fun f => f z) ((congrArg ((ν ▷ P.A).left ≫ ·) σ₁).trans hν')).trans ?_
    refine Eq.trans ?_ (IsLocalRing.comap_closedPoint (IsLocalRing.residue R))
    exact congrArg (PrimeSpectrum.comap (IsLocalRing.residue R)) (Subsingleton.elim (α := PrimeSpectrum k) _ _)
  have : Smooth q := MorphismProperty.of_isPullback (P := @Smooth) hp ‹_›
  have ht := (IsLocalRing.closedPoint_mem_iff (R := R) ⟨_, q.isOpenMap _ (Out.nonzeroLocus th).isOpen⟩).1 ⟨_, hy, hc⟩
  refine ⟨th, fun s => ?_⟩
  obtain ⟨y, h₁, h₂⟩ := (congrArg (fun U => s ∈ U) ht).mpr trivial
  exact ⟨y, h₂, h₁⟩

theorem exists_rescale {X X' Y Y' : Scheme.{0}} {L : LB X} {L' : LB X'} (hL : L.IsLB) (hL' : L'.IsLB) {F : X' ⟶ X}
    {w : LB.Iso L' (L.pull F)} (hw : PGen w) {e : Y ⟶ X} {e' : Y' ⟶ X'} {p : X' ⟶ Y'} (hp : e' ≫ p = 𝟙 _) {h : Y' ⟶ Y}
    (he : e' ≫ F = h ≫ e) {a : LB.Gen (L'.pull e')} (ha : a.IsGen) {t : LB.Gen (L.pull e)} (ht : t.IsGen) :
    ∃ w' : LB.Iso L' (L.pull F), PGen w' ∧
      PMaps w' (K := PUnit) (fun _ => e') (fun _ => e) (fun _ => 1) a t h := by
  have m : ∀ (y : Y') j, F (e' y) ∈ L.U j → h y ∈ LB.wchart L (fun _ : PUnit => e) (fun _ => j) := fun y j hj =>
    Set.mem_iInter.2 fun _ => (congrArg (fun f => f y ∈ L.U j) he).mp hj
  let W : L.ι × L'.ι → Y'.Opens := fun i => e' ⁻¹ᵁ (F ⁻¹ᵁ L.U i.1 ⊓ L'.U i.2)
  have l₁ : ∀ i, W i ≤ h ⁻¹ᵁ LB.wchart L (fun _ : PUnit => e) (fun _ => i.1) := fun i y hy => m y _ hy.1
  have l₂ : ∀ i, W i ≤ e' ⁻¹ᵁ ((L.pull F).U (fun _ => i.1) ⊓ L'.U i.2) := fun i y hy => ⟨mem_pull.2 hy.1, hy.2⟩
  have l₃ : ∀ i, W i ≤ LB.wchart L' (fun _ : PUnit => e') (fun _ => i.2) := fun i y hy => Set.mem_iInter.2 fun _ => hy.2
  obtain ⟨u, hu⟩ : ∃ u : ∀ i, Γ(Y', W i)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) i, r z ∈ W i →
      gm r z (W i) (u i) = gm (r ≫ h) z (LB.wchart L (fun _ : PUnit => e) (fun _ => i.1)) (t.s fun _ => i.1) *
        (gw w (r ≫ e') z i.1 i.2 * gm r z (LB.wchart L' (fun _ : PUnit => e') (fun _ => i.2)) (a.s fun _ => i.2))⁻¹ :=
    ⟨fun i => res (l₁ i) (pullU h _ (t.s fun _ => i.1)) *
        (res (l₂ i) (pullU e' _ (w.s (fun _ => i.1, i.2))) * res (l₃ i) (a.s fun _ => i.2))⁻¹, fun Z r z i hz =>
      (map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_res r z (l₁ i) hz _).trans (gm_pull r h z _ (l₁ i hz) _))
        ((map_inv _ _).trans (congrArg (·⁻¹) ((map_mul _ _ _).trans (congrArg₂ (· * ·)
          ((gm_res r z (l₂ i) hz _).trans (gm_pull r e' z _ (l₂ i hz) _)) (gm_res r z (l₃ i) hz _))))))⟩
  obtain ⟨c, hc⟩ := glue_unit ⊤ W (fun _ => le_top) (fun y _ => by
      obtain ⟨j, hj⟩ := exists_chart hL (F (e' y))
      obtain ⟨k, hk⟩ := exists_chart hL' (e' y)
      exact Opens.mem_iSup.2 ⟨(j, k), hj, hk⟩) u (fun i i' y hy => by
      rw [hu _ _ y i hy.1, hu _ _ y i' hy.2, gen_trans ht (𝟙 Y' ≫ h) y (l₁ i hy.1) (l₁ i' hy.2),
        gen_trans ha (𝟙 Y') y (l₃ i hy.1) (l₃ i' hy.2),
        hw _ (𝟙 Y' ≫ e') y i.1 i'.1 i.2 i'.2 hy.1.1 hy.2.1 hy.1.2 hy.2.2]
      simp only [trF, Fintype.prod_unique, zpow_one, Category.assoc, he]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel)
  let w' : LB.Iso L' (L.pull F) := ⟨fun i => res (le_top : _ ≤ p ⁻¹ᵁ ⊤) (pullU p ⊤ c) * w.s i⟩
  have v : ∀ (Z : Scheme.{0}) (r : Z ⟶ X') (z : Z) j k, F (r z) ∈ L.U j → r z ∈ L'.U k →
      gw w' r z j k = gm (r ≫ p) z ⊤ c * gw w r z j k := fun Z r z j k hj hk =>
    (map_mul _ _ _).trans (congrArg (· * _) ((gm_res r z _ (⟨mem_pull.2 hj, hk⟩ : r z ∈ (L.pull F).U (fun _ => j) ⊓ L'.U k)
      _).trans (gm_pull r p z ⊤ trivial c)))
  refine ⟨w', fun Z r z j j' k k' hj hj' hk hk' => ?_, fun Z r z j k hj hk => ?_⟩
  · rw [v Z r z j k hj hk, v Z r z j' k' hj' hk', hw Z r z j j' k k' hj hj' hk hk', mul_left_comm]
  · have hz : r z ∈ W (j PUnit.unit, k PUnit.unit) := ⟨hj _, hk _⟩
    rw [Fintype.prod_unique, zpow_one, v Z (r ≫ e') z _ _ (hj _) (hk _), Category.assoc, hp, Category.comp_id,
      ← gm_res r z le_top hz c, hc, hu Z r z _ hz, _root_.mul_assoc]
    exact (inv_mul_cancel_right _ _).symm

theorem exists_keyPB_of_isGrpPullback {R R' : Type} [CommRing R] [IsLocalRing R] [CommRing R'] (f : R →+* R')
    (x : KeyIn R') (y : KeyIn R) {φ : x.P.A.left ⟶ y.P.A.left} (h : IsGrpPullback x.P.A y.P.A (spMap f) φ)
    {w : LB.Iso x.P.L (y.P.L.pull φ)} (hw : PGen w) (hg : x.P.g = y.P.g) :
    ∃ th' hth' v' hv', KeyPB ⟨x.P, x.g_pos, x.rig, x.rig_gen, th', hth', v', hv'⟩ y f := by
  have he : eSec x.P.A ≫ φ = spMap f ≫ eSec y.P.A := PolBaseChange.eSec_comm h
  have := x.P.isAb.comm
  have := y.P.isAb.comm
  have := y.P.isAb.smooth
  obtain ⟨w', g', m'⟩ := exists_rescale y.P.isLB x.P.isLB hw (p := x.P.A.hom) (Over.w η[x.P.A]) he x.rig_gen y.rig_gen
  obtain ⟨th', hth'⟩ := sec_pull_down g' y.P.isLB x.P.isLB y.th
  have sq : ∀ i, (spMap (Chart.dualMapR f) ≫ (y.v i).left) ≫ y.P.A.hom = (epsR R').hom ≫ spMap f := fun i => by
    rw [Category.assoc, Over.w]
    show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext a <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  let v' : Fin y.P.g → (epsR R' ⟶ x.P.A) := fun i => Over.homMk (h.1.lift _ _ (sq i)) (h.1.lift_snd _ _ _)
  have hv' : ∀ i, (v' i).left ≫ φ = spMap (Chart.dualMapR f) ≫ (y.v i).left := fun i => h.1.lift_fst _ _ _
  have hb : ∀ {n : ℕ} (e : n = y.P.g), IsLieBasis fun i : Fin n => v' (i.cast e) := fun e => by
    subst e
    exact Chart.isLieBasis_baseChange f h y.basis hv'
  refine ⟨th', SectionBaseChange.fibre_nonzero_of_pull x.P.isLB hth' h.1 y.th_ne, _, hb hg, φ, he, w', hg,
    Chart.dualMapR f, h, (isGen_iff _).2 g',
    (maps_iff w' _ (fun _ => eSec y.P.A) _ x.rig y.rig _ _ (rigPull_le φ _ he y.P.L) (fun _ => rfl)).2 m',
    appLE_eq_of_stalk _ y.th th' (hth' _ (𝟙 _)), fun a => ?_, ?_, fun i => hv' _⟩
  · ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  · ext <;> simp [Chart.dualMapR]

theorem exists_keyIn_pullback (hT : Out.SecTwistSt) {O R : Type} [CommRing O] [CommRing R] [IsLocalRing R] (f : O →+* R)
    (P : Out.PolAV (Sp O)) (hg : 1 ≤ P.g) : ∃ (y : KeyIn R) (ψ : y.P.A.left ⟶ P.A.left) (w : LB.Iso y.P.L (P.L.pull ψ)),
      y.P.g = P.g ∧ IsGrpPullback y.P.A P.A (spMap f) ψ ∧ PGen w := by
  have h := isGrpPullback_pullback P.A (spMap f)
  let φ : ((Over.pullback (spMap f)).obj P.A).left ⟶ P.A.left := pullback.fst P.A.hom (spMap f)
  change IsGrpPullback _ _ _ φ at h
  have hL' := LB.isLB_pull P.isLB φ
  have hw := (isGen_iff _).1 (idIso_isGen hL')
  let P' : Out.PolAV (Sp R) :=
    { A := (Over.pullback (spMap f)).obj P.A
      isAb := Out.TLinPf.isAb_pullback (spMap f) P.A P.isAb
      g := P.g
      smoothDim := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback h.1 P.smoothDim
      L := P.L.pull φ
      isLB := hL'
      rigid := PolBaseChange.rigidified_pull h P.rigid
      sym := PolBaseChange.sym_pull h P.sym
      ample := relAmple_pull h.1 P.isLB hL' hw ⊤ (isAffineOpen_top _) (fun _ => trivial) P.ample
      ktriv := kTriv_pull h P.isLB hL' hw P.ktriv }
  obtain ⟨rig, hr⟩ := P'.rigid
  obtain ⟨th, hth⟩ := exists_sec_fibre_ne_zero hT P h.1
  obtain ⟨v, hv⟩ := exists_isLieBasis P'.A P'.smoothDim
  exact ⟨⟨P', hg, rig, hr, th, hth, v, hv⟩, φ, _, rfl, h, hw⟩

theorem exists_isLocalModel_of_integral : Out.SecTwistSt → ∀ (K : Type) [Field K] [NumberField K]
    (P₀ : Out.PolAV (Sp (𝓞 K))) (x : KeyIn K) (φ : x.P.A.left ⟶ P₀.A.left) (w : LB.Iso x.P.L (P₀.L.pull φ)),
    x.P.g = P₀.g → IsGrpPullback x.P.A P₀.A (spMap (algebraMap (𝓞 K) K)) φ → w.IsGen →
    ∃ oa od : HeightOneSpectrum (𝓞 K) → ℤ, ∀ 𝔭, ∃ (a : K) (M : Matrix (Fin x.P.g) (Fin x.P.g) K),
      GlobalTheory.KeyPow.IsLocalModel x 𝔭 a M ∧ 𝔭.valuation K a = WithZero.exp (-oa 𝔭) ∧
        𝔭.valuation K M.det = WithZero.exp (-od 𝔭) := by
  intro hT K _ _ P₀ x φ w hg hφ hw
  have key : ∀ 𝔭 : HeightOneSpectrum (𝓞 K), ∃ (a : K) (M : Matrix (Fin x.P.g) (Fin x.P.g) K),
      IsLocalModel x 𝔭 a M ∧ a ≠ 0 ∧ M.det ≠ 0 := fun 𝔭 => by
    let R := (𝔭.valuation K).integer
    let f : 𝓞 K →+* R := (algebraMap (𝓞 K) K).codRestrict R fun r => 𝔭.valuation_le_one r
    have hf : spMap (algebraMap R K) ≫ spMap f = spMap (algebraMap (𝓞 K) K) := (Spec.map_comp _ _).symm
    obtain ⟨y, ψ, w₀, hg₀, hψ, hw₀⟩ := exists_keyIn_pullback hT f P₀ (hg ▸ x.g_pos)
    have sq : φ ≫ P₀.A.hom = (x.P.A.hom ≫ spMap (algebraMap R K)) ≫ spMap f := by rw [Category.assoc, hf, hφ.1.w]
    obtain ⟨φ', rfl, h₂⟩ : ∃ φ' : x.P.A.left ⟶ y.P.A.left, φ' ≫ ψ = φ ∧
        φ' ≫ y.P.A.hom = x.P.A.hom ≫ spMap (algebraMap R K) := ⟨hψ.1.lift _ _ sq, hψ.1.lift_fst _ _ _, hψ.1.lift_snd _ _ _⟩
    obtain ⟨w', T⟩ := exists_cancel P₀.isLB w₀ w hw₀ ((isGen_iff _).1 hw) y.P.isLB x.P.isLB
    obtain ⟨th', hth', v', hv', hPB⟩ := exists_keyPB_of_isGrpPullback (algebraMap R K) x y
      (hψ.cancel (hφ.congr hf.symm rfl) h₂) (T.pgen_cancel P₀.isLB hw₀ ((isGen_iff _).1 hw)) (hg.trans hg₀.symm)
    obtain ⟨a, M, ha, hM⟩ := exists_scalar_matrix hT x.P x.th th' x.th_ne x.basis hv'
    have := x.P.isAb.comm
    refine ⟨a, M, ⟨R, _, inferInstance, inferInstance, _,
      inferInstanceAs (IsFractionRing (𝔭.valuation K).valuationSubring K), y, th', hth', v', hv', fun r => r.2, ha, hM, hPB⟩,
      ?_, (((LieComb.lieComb_algebra K x.P.A _ x.v x.basis.1).2.2.2.2 M v' x.basis hM).1 hv').ne_zero⟩
    rintro rfl
    obtain ⟨z, -, hz⟩ := hth' (default : PrimeSpectrum K)
    obtain ⟨i, hi⟩ := Opens.mem_iSup.1 hz
    rw [ha i, constFn, map_zero, map_zero, zero_mul, Scheme.basicOpen_zero] at hi
    exact hi
  choose a M h ha hM using key
  refine ⟨fun 𝔭 => -WithZero.log (𝔭.valuation K (a 𝔭)), fun 𝔭 => -WithZero.log (𝔭.valuation K (M 𝔭).det),
    fun 𝔭 => ⟨a 𝔭, M 𝔭, h 𝔭, ?_, ?_⟩⟩
  · rw [neg_neg, WithZero.exp_log (by simpa using ha 𝔭)]
  · rw [neg_neg, WithZero.exp_log (by simpa using hM 𝔭)]

end GlobalTheory.KeyPow
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.MemNonzeroLocusPullOn
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.KeyNear

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

section Pull

variable {X Y : Scheme.{0}} {L : LB X}

theorem res_appLE (φ : Y ⟶ X) {U : X.Opens} {V V' : Y.Opens} (e : V ≤ φ ⁻¹ᵁ U) (h : V' ≤ V) (s : Γ(X, U)) :
    resG Y h ((φ.appLE U V e).hom s) = (φ.appLE U V' (h.trans e)).hom s := by
  rw [← Scheme.Hom.appLE_map φ e (homOfLE h).op]; rfl

theorem appLE_res (φ : Y ⟶ X) {U U' : X.Opens} {V : Y.Opens} (h : U' ≤ U) (e : V ≤ φ ⁻¹ᵁ U') (s : Γ(X, U)) :
    (φ.appLE U' V e).hom (resG X h s) = (φ.appLE U V (e.trans (φ.preimage_mono h))).hom s := by
  rw [← Scheme.Hom.map_appLE φ e (homOfLE h).op]; rfl

def pullOn (φ : Y ⟶ X) {W : X.Opens} (hW : ∀ y, φ y ∈ W) (θ : ∀ i, Γ(X, W ⊓ L.U i)) (hθ : θ ∈ secOn L W) :
    (L.pull φ).Sec where
  f j := (φ.appLE (W ⊓ L.U (j PUnit.unit)) ((L.pull φ).U j)
    (fun y hy => ⟨hW y, LB.wchart_le L (fun _ : PUnit => φ) j PUnit.unit hy⟩)).hom (θ _)
  compat i j := by
    have e : (L.pull φ).U i ⊓ (L.pull φ).U j ≤ φ ⁻¹ᵁ (W ⊓ L.U (i PUnit.unit) ⊓ L.U (j PUnit.unit)) :=
      fun y hy => ⟨⟨hW y, LB.wchart_le L (fun _ : PUnit => φ) i PUnit.unit hy.1⟩,
        LB.wchart_le L (fun _ : PUnit => φ) j PUnit.unit hy.2⟩
    have h := congrArg (φ.appLE _ _ e).hom (hθ (i PUnit.unit) (j PUnit.unit))
    rw [map_mul, appLE_res, appLE_res, appLE_res] at h
    refine (res_appLE φ _ _ _).trans (h.trans ?_)
    refine congrArg₂ (· * ·) ?_ (res_appLE φ _ _ _).symm
    have e₁ : ∀ {G : Type} [CommGroup G] (a : G), a = ∏ _k : PUnit.{1}, a ^ (1 : ℤ) := fun a => by simp
    exact congrArg Units.val (e₁ (res (e.trans (φ.preimage_mono (le_inf (inf_le_left.trans inf_le_right) inf_le_right)))
      (pullU φ _ (L.g (i PUnit.unit) (j PUnit.unit)))))

theorem mem_nonzeroLocus_pullOn (φ : Y ⟶ X) {W : X.Opens} (hW : ∀ y, φ y ∈ W) (θ : ∀ i, Γ(X, W ⊓ L.U i))
    (hθ : θ ∈ secOn L W) {y : Y} {i : L.ι} (hy : φ y ∈ X.basicOpen (θ i)) :
    y ∈ Out.nonzeroLocus (pullOn φ hW θ hθ) := by
  refine TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => i, ?_⟩
  exact (Scheme.basicOpen_appLE φ _ _ _ (θ i)).ge ⟨mem_pull.2 (X.basicOpen_le _ hy).2, hy⟩

end Pull

open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa

theorem main : Out.Laws → ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (P : Out.PolAV (Sp R)), 1 ≤ P.g → ∀ p : PrimeSpectrum R, ∃ r : R, r ∉ p.asIdeal ∧ ∀ (R' : Type) [CommRing R'] (ρ : R →+* R'), IsUnit (ρ r) → ∃ (y : KeyIn R') (π : y.P.A.left ⟶ P.A.left), y.P.g = P.g ∧ IsGrpPullback y.P.A P.A (spMap ρ) π ∧ LBIso y.P.L (P.L.pull π) := by
  intro hL R _ _ P hg p
  obtain ⟨V, θ, hpV, hθ, hne⟩ := SecFamily.exists_secOn_nonvanishing hL (Sp R) P p
  have c₁ : IsCommMonObj P.A := P.isAb.comm
  obtain ⟨r₁, hr₁, v, hv⟩ := LieLoc.lie_locally_free R P.A P.g P.smoothDim p
  obtain ⟨_, ⟨r₂, rfl⟩, hr₂, hsub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open (a := p) (u := V.1) hpV V.2
  refine ⟨r₁ * r₂, fun h => (p.2.mem_or_mem h).elim hr₁ hr₂, fun R' _ f hf => ?_⟩
  rw [map_mul] at hf
  have u₁ := isUnit_of_mul_isUnit_left hf
  have u₂ := isUnit_of_mul_isUnit_right hf
  have hV : ∀ s : Sp R', spMap f s ∈ V := fun s => hsub (show f r₂ ∉ s.asIdeal from fun h =>
    s.2.ne_top (Ideal.eq_top_of_isUnit_mem _ h u₂))
  have h := isGrpPullback_pullback P.A (spMap f)
  let φ : ((Over.pullback (spMap f)).obj P.A).left ⟶ P.A.left := pullback.fst P.A.hom (spMap f)
  change IsGrpPullback _ _ _ φ at h
  have hL' := LB.isLB_pull P.isLB φ
  have hw := (isGen_iff _).1 (idIso_isGen hL')
  let P' : Out.PolAV (Sp R') :=
    { A := (Over.pullback (spMap f)).obj P.A
      isAb := Out.TLinPf.isAb_pullback (spMap f) P.A P.isAb
      g := P.g
      smoothDim := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback h.1 P.smoothDim
      L := P.L.pull φ
      isLB := hL'
      rigid := PolBaseChange.rigidified_pull h P.rigid
      sym := PolBaseChange.sym_pull h P.sym
      ample := relAmple_pull h.1 P.isLB hL' hw ⊤ (isAffineOpen_top _) (fun _ => trivial) P.ample
      ktriv := kTriv_pull h P.isLB hL' hw P.ktriv }
  obtain ⟨rig, hrig⟩ := P'.rigid
  have hW : ∀ y, φ y ∈ P.A.hom ⁻¹ᵁ V := fun y => by
    have e : P.A.hom (φ y) = spMap f (P'.A.hom y) := congrArg (fun g => g y) h.1.w
    change P.A.hom (φ y) ∈ V
    rw [e]
    exact hV _
  let f' : Localization.Away r₁ →+* R' := IsLocalization.Away.lift r₁ u₁
  have hf' : spMap f' ≫ spMap (algebraMap R (Localization.Away r₁)) = spMap f := by
    rw [← IsLocalization.Away.lift_comp (S := Localization.Away r₁) r₁ u₁]
    exact (Spec.map_comp _ _).symm
  have h₁ := isGrpPullback_pullback P.A (spMap (algebraMap R (Localization.Away r₁)))
  have w₁ : φ ≫ P.A.hom = (P'.A.hom ≫ spMap f') ≫ spMap (algebraMap R (Localization.Away r₁)) := by
    rw [Category.assoc, hf']; exact h.1.w
  have h₂ := IsGrpPullback.cancel h₁ (h.congr hf'.symm (h₁.1.lift_fst _ _ w₁).symm) (h₁.1.lift_snd _ _ w₁)
  have a₁ := Out.TLinPf.isAb_pullback (spMap (algebraMap R (Localization.Away r₁))) P.A P.isAb
  have c₂ : IsCommMonObj P'.A := P'.isAb.comm
  have c₃ := a₁.comm
  obtain ⟨v', hb', -⟩ := exists_isLieBasis_baseChange _ R' f' _ P'.A _ h₂ a₁.smooth P.g v hv
  refine ⟨⟨P', hg, rig, hrig, pullOn φ hW θ hθ, fun s => ?_, v', hb'⟩, φ, rfl, h, idIso _, idIso_isGen hL'⟩
  obtain ⟨z, i, hz, hz'⟩ := hne _ (hV s)
  obtain ⟨y, rfl, hy⟩ := Scheme.exists_preimage_of_isPullback h.1 z s hz
  exact ⟨y, hy, mem_nonzeroLocus_pullOn φ hW θ hθ hz'⟩

end GlobalTheory.KeyNear
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKeyDataBaseChangeSectionsMatrices
section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.FinitePreimageOfIsPullbackOfFiniteBase
open AlgebraicGeometry CategoryTheory Limits

namespace GlobalTheory.KeyFin

theorem finite_preimage_of_isPullback_of_finite_base :
    ∀ (X X' S S' : Scheme.{0}) (h : X ⟶ S) (h' : X' ⟶ S') (φ : X' ⟶ X) (f : S' ⟶ S) (Z : Set X),
      LocallyOfFiniteType h → QuasiCompact h → IsPullback φ h' h f → Finite S' → IsClosed Z →
      Z.Finite → (φ ⁻¹' Z).Finite := by
  intro X X' S S' h h' φ f Z _ _ H _ hZ hfin
  let I := Scheme.IdealSheafData.vanishingIdeal (X := X) ⟨Z, hZ⟩
  have hr : Set.range I.subschemeι = Z := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]; rfl
  have hf : Finite I.subscheme := by
    have : Finite (Set.range I.subschemeι) := by rw [hr]; exact hfin.to_subtype
    exact Finite.of_injective_finite_range I.subschemeι.isClosedEmbedding.injective
  have hq : LocallyQuasiFinite (I.subschemeι ≫ h) :=
    .of_finite_preimage_singleton _ fun _ => Set.toFinite _
  have P := (IsPullback.of_hasPullback I.subschemeι φ).paste_vert H
  have h1 : LocallyQuasiFinite (pullback.snd I.subschemeι φ ≫ h') :=
    MorphismProperty.of_isPullback (P := @LocallyQuasiFinite) P hq
  have h2 : QuasiCompact (pullback.snd I.subschemeι φ ≫ h') :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) P inferInstance
  have h3 : (Set.univ : Set ↑(pullback I.subschemeι φ)).Finite := by
    have := (Set.toFinite (Set.univ : Set S')).preimage'
      (f := (pullback.snd I.subschemeι φ ≫ h')) fun _ _ =>
        (pullback.snd I.subschemeι φ ≫ h').finite_preimage_singleton _
    simpa using this
  rw [← hr, ← Scheme.Pullback.range_snd, ← Set.image_univ]
  exact h3.image _

end GlobalTheory.KeyFin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKeyDataBaseChangeSectionsMatrices
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

noncomputable section
namespace GlobalTheory.KeyBaseChangeData

theorem via_mul {X Y : Scheme.{0}} {L : LB X} {L' : LB Y} {φ : Y ⟶ X} {w : LB.Iso L' (L.pull φ)} {l l' k : ℕ}
    (hk : l + l' = k) {a' b' : ∀ i, Γ(Y, L'.U i)} {a b : ∀ j, Γ(X, L.U j)} (ha : KeyVia.Via w l a' a)
    (hb : KeyVia.Via w l' b' b) : KeyVia.Via w k (fun i => a' i * b' i) (fun j => a j * b j) := by
  intro j i h
  rw [map_mul, map_mul, ha j i h, hb j i h, ← hk, pow_add, _root_.mul_mul_mul_comm]

theorem coords_mul {R R' : Type} [CommRing R] [CommRing R'] {x : KeyIn R} {x' : KeyIn R'} {f : R →+* R'} {φ w}
    (hx : KeyVia x' x f φ w) {n l k N : ℕ} (hk : n + l = k) {s : RR x n} {s' : RR x' n} {e : RR x l} {e' : RR x' l}
    {b : Fin N → RR x k} {b' : Fin N → RR x' k} {c : Fin N → R} (hs : SecVia x' x φ w s' s)
    (he : SecVia x' x φ w e' e) (hb : ∀ i, SecVia x' x φ w (b' i) (b i))
    (hc : Coords x b c (fun i => (show Γ(x.P.A.left, x.P.L.U i) from s.f i) * (show Γ(x.P.A.left, x.P.L.U i) from e.f i))) :
    Coords x' b' (fun i => f (c i))
      (fun i => (show Γ(x'.P.A.left, x'.P.L.U i) from s'.f i) * (show Γ(x'.P.A.left, x'.P.L.U i) from e'.f i)) := by
  obtain ⟨-, -, -, ⟨hP, -⟩, -⟩ := hx
  have H := KeyVia.Via.comb (w := w) (l := k) (b' := fun i => (b' i).f) (b := fun i => (b i).f) f x.P.A.hom
    x'.P.A.hom hP.w hb c
  have H' := via_mul (w := w) hk (a' := s'.f) (b' := e'.f) (a := s.f) (b := e.f) hs he
  have H'' := (congrArg (KeyVia.Via w k _) (funext hc)).mp H'
  exact fun i => congrFun (KeyVia.Via.unique x.P.isLB H'' H) i

theorem exists_baseChange_data : Out.Laws → ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] (R' : Type) [CommRing R'] (f : O →+* R') (x : KeyIn O) (n l : ℕ) (s : Fin x.P.g → RR x n) (b : ∀ j, Fin ((l - j * n) ^ x.P.g) → RR x (l - j * n)) (m), x.P.g * n < l → (∀ j ≤ x.P.g, IsBasis x (b j)) → IsMul x l s b m → ∃ (x' : KeyIn R') (φ : x'.P.A.left ⟶ x.P.A.left) (w : LB.Iso x'.P.L (x.P.L.pull φ)) (hg : x'.P.g = x.P.g) (s' : Fin x'.P.g → RR x' n) (b' : ∀ j, Fin ((l - j * n) ^ x'.P.g) → RR x' (l - j * n)) (m' : _), KeyVia x' x f φ w ∧ (∀ i, SecVia x' x φ w (s' i) (s (i.cast hg))) ∧ (∀ j k, SecVia x' x φ w (b' j k) (b j (k.cast (congrArg (fun r => (l - j * n) ^ r) hg)))) ∧ (∀ j ≤ x'.P.g, IsBasis x' (b' j)) ∧ IsMul x' l s' b' m' ∧ (∀ i j j' k k', m' i j j' k k' = f (m (i.cast hg) j j' (k.cast (congrArg (fun r => (l - j * n) ^ r) hg)) (k'.cast (congrArg (fun r => (l - j' * n) ^ r) hg)))) ∧ (Finite (Sp R') → FinZ x s → FinZ x' s') := by
  intro laws O _ _ _ R' _ f x n l s b m hl hb hm
  obtain ⟨x', hx'⟩ := KeyPow.exists_keyPB_ring x f
  obtain ⟨φ, w, hx⟩ := (KeyVia.main O R' x x' f).1.1 hx'
  have hg : x'.P.g = x.P.g := by
    obtain ⟨-, hg, -⟩ := hx
    exact hg
  obtain ⟨⟨A', ab, g', sm, L', hL', p₁, p₂, p₃, p₄⟩, q₁, q₂, q₃, q₄, q₅, q₆, q₇⟩ := x'
  obtain rfl : g' = x.P.g := hg
  let x' : KeyIn R' := ⟨⟨A', ab, x.P.g, sm, L', hL', p₁, p₂, p₃, p₄⟩, q₁, q₂, q₃, q₄, q₅, q₆, q₇⟩
  have hex := ((KeyVia.main O R' x x' f).2 φ w hx).1
  choose s' hs' using fun i => (hex _ (s i)).exists
  choose b' hb' using fun j k => (hex _ (b j k)).exists
  refine ⟨x', φ, w, rfl, s', b', fun i j j' => (m i j j').map f, hx, hs', hb', fun j hj => ?_,
    fun i j hj k => ?_, fun _ _ _ _ _ => rfl, fun hfin hz => ?_⟩
  · have h₁ : j * n ≤ x.P.g * n := Nat.mul_le_mul_right n hj
    exact (KeyBasis.main laws O x (l - j * n) (by omega)).2 (b j) (hb j hj) R' f x' φ w (b' j) hx (hb' j)
  · have h₁ : (j + 1) * n ≤ x.P.g * n := Nat.mul_le_mul_right n hj
    have h₂ : n + (l - (j + 1) * n) = l - j * n := by
      rw [Nat.add_mul, Nat.one_mul] at h₁ ⊢
      omega
    exact coords_mul hx h₂ (hs' i) (hb' (j + 1) k) (hb' j) (hm i j hj k)
  · obtain ⟨-, -, -, ⟨hP, -⟩, -⟩ := hx
    have hc : IsClosed {y : x.P.A.left | ∀ i, y ∉ Out.nonzeroLocus (s i)} := by
      rw [Set.setOf_forall]
      exact isClosed_iInter fun i => (Out.nonzeroLocus (s i)).isOpen.isClosed_compl
    haveI : IsProper x.P.A.hom := x.P.isAb.proper
    refine (KeyFin.finite_preimage_of_isPullback_of_finite_base _ _ _ _ _ _ _ _ _ inferInstance inferInstance
      hP hfin hc hz).subset fun y hy i h => hy i ?_
    exact EtBaseChange.mem_nonzeroLocus_via (hs' i) y h

end GlobalTheory.KeyBaseChangeData
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKeyDataBaseChangeSectionsMatricesStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_keyData_baseChange_sections_matrices : Out.Laws → ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] (R' : Type) [CommRing R'] (f : O →+* R') (x : KeyIn O) (n l : ℕ) (s : Fin x.P.g → RR x n) (b : ∀ j, Fin ((l - j * n) ^ x.P.g) → RR x (l - j * n)) (m), x.P.g * n < l → (∀ j ≤ x.P.g, IsBasis x (b j)) → IsMul x l s b m → ∃ (x' : KeyIn R') (φ : x'.P.A.left ⟶ x.P.A.left) (w : LB.Iso x'.P.L (x.P.L.pull φ)) (hg : x'.P.g = x.P.g) (s' : Fin x'.P.g → RR x' n) (b' : ∀ j, Fin ((l - j * n) ^ x'.P.g) → RR x' (l - j * n)) (m' : _), KeyVia x' x f φ w ∧ (∀ i, SecVia x' x φ w (s' i) (s (i.cast hg))) ∧ (∀ j k, SecVia x' x φ w (b' j k) (b j (k.cast (congrArg (fun r => (l - j * n) ^ r) hg)))) ∧ (∀ j ≤ x'.P.g, IsBasis x' (b' j)) ∧ IsMul x' l s' b' m' ∧ (∀ i j j' k k', m' i j j' k k' = f (m (i.cast hg) j j' (k.cast (congrArg (fun r => (l - j * n) ^ r) hg)) (k'.cast (congrArg (fun r => (l - j' * n) ^ r) hg)))) ∧ (Finite (Sp R') → FinZ x s → FinZ x' s') := by
  first | exact @GlobalTheory.KeyBaseChangeData.exists_baseChange_data | exact GlobalTheory.KeyBaseChangeData.exists_baseChange_data | (intros; apply GlobalTheory.KeyBaseChangeData.exists_baseChange_data <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ThetaKeyRuleValuationUnitOfFunctorial
section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ValueMemValuationSubring
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.KeyGenInt

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.KeyCl

theorem value_mem_valuationSubring (κ : Rule) (hU : UnitSp κ) (S K : Type) [CommRing S] [Field K] [CharZero K] [Algebra S K]
    (y : KeyIn S) (x : KeyIn K) (h : KeyPB x y (algebraMap S K)) (V : ValuationSubring K) (hV : IsDiscreteValuationRing V)
    (hS : ∀ s : S, algebraMap S K s ∈ V) : (κ K x : K) ∈ V ∧ (κ K x : K)⁻¹ ∈ V := by
  let j : S →+* V := (algebraMap S K).codRestrict V.toSubring hS
  obtain ⟨yV, hyV⟩ := GlobalTheory.KeyPow.exists_keyPB_ring y j
  have hc : (algebraMap V K).comp j = algebraMap S K := RingHom.ext fun _ => rfl
  have hx : KeyPB x yV (algebraMap V K) :=
    GlobalTheory.KeyCancel.keyPB_cancel S V K y yV x j (algebraMap V K) hyV (by rw [hc]; exact h)
  obtain ⟨u, hu, -⟩ := hU V K yV x hx
  refine ⟨?_, ?_⟩
  · rw [hu]; exact (u : V).2
  · have : (κ K x : K)⁻¹ = algebraMap V K (u⁻¹ : Vˣ) := by
      rw [hu]
      refine inv_eq_of_mul_eq_one_right ?_
      rw [← map_mul, Units.mul_inv, map_one]
    rw [this]; exact ((u⁻¹ : Vˣ) : V).2

theorem isIntegral_value : ∀ κ : Rule, UnitSp κ → ∀ (S K : Type) [CommRing S] [IsDomain S] [IsNoetherianRing S] [Field K]
    [CharZero K] [Algebra S K] [IsFractionRing S K] (y : KeyIn S) (x : KeyIn K), KeyPB x y (algebraMap S K) →
    IsIntegral S (κ K x : K) ∧ IsIntegral S ((κ K x : K)⁻¹) := by
  intro κ hU S K _ _ _ _ _ _ _ y x h
  exact ⟨GlobalTheory.isIntegral_of_forall_mem_discreteValuationSubring S K _ fun V hV hS => (value_mem_valuationSubring κ hU S K y x h V hV hS).1,
    GlobalTheory.isIntegral_of_forall_mem_discreteValuationSubring S K _ fun V hV hS => (value_mem_valuationSubring κ hU S K y x h V hV hS).2⟩

end GlobalTheory.KeyGenInt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ThetaKeyRuleValuationUnitOfFunctorial
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.KeyCl

namespace GlobalTheory.KeyValUnit

theorem valUnit : ∀ κ : Rule, Funct κ → UnitSp κ → ValUnit κ := by
  intro κ hF hU S V K _ _ _ _ _ _ _ _ _ g y x hx
  have := RingHom.ker_isPrime g
  let S₀ := S ⧸ RingHom.ker g
  let K₀ := FractionRing S₀
  let g₀ : S₀ →+* V := RingHom.kerLift g
  let f₀ : S₀ →+* K := (algebraMap V K).comp g₀
  have hf₀ : Function.Injective f₀ := (IsFractionRing.injective V K).comp (RingHom.kerLift_injective g)
  let j : K₀ →+* K := IsFractionRing.lift hf₀
  have hj : j.comp (algebraMap S₀ K₀) = (algebraMap V K).comp g₀ :=
    RingHom.ext fun a => IsFractionRing.lift_algebraMap hf₀ a
  have : CharZero K₀ := j.charZero
  obtain ⟨y₀, hy₀⟩ := GlobalTheory.KeyPow.exists_keyPB_ring y (Ideal.Quotient.mk (RingHom.ker g))
  obtain ⟨x₀, hx₀⟩ := GlobalTheory.KeyPow.exists_keyPB_ring y₀ (algebraMap S₀ K₀)
  have e : j.comp ((algebraMap S₀ K₀).comp (Ideal.Quotient.mk (RingHom.ker g))) = (algebraMap V K).comp g := by
    rw [← RingHom.comp_assoc, hj]
    exact RingHom.ext fun a => congrArg (algebraMap V K) (RingHom.kerLift_mk g a)
  have hxj : KeyPB x x₀ j := GlobalTheory.KeyCancel.keyPB_cancel _ _ _ y x₀ x _ _
    (GlobalTheory.keyPB_trans _ _ _ y y₀ x₀ _ _ hy₀ hx₀) (e.symm ▸ hx)
  have hval := hF K₀ K j x₀ x hxj
  obtain ⟨h₁, h₂⟩ := GlobalTheory.KeyGenInt.isIntegral_value κ hU S₀ K₀ y₀ x₀ hx₀
  have h₁' : IsIntegral V (κ K x : K) := hval ▸ h₁.map_of_comp_eq g₀ j hj.symm
  have h₂' : IsIntegral V ((κ K x : K)⁻¹) := by
    rw [hval, ← map_inv₀]
    exact h₂.map_of_comp_eq g₀ j hj.symm
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.1 h₁'
  obtain ⟨b, hb⟩ := IsIntegrallyClosed.isIntegral_iff.1 h₂'
  have hab : a * b = 1 := IsFractionRing.injective V K (by
    rw [map_mul, ha, hb, map_one, mul_inv_cancel₀ (κ K x).ne_zero])
  exact ⟨Units.mkOfMulEqOne a b hab, ha.symm⟩

end GlobalTheory.KeyValUnit
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ThetaKeyRuleValuationUnitOfFunctorialStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.KeyCl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaKeyRule_valuationUnit_of_functorial : ∀ κ : Rule, Funct κ → UnitSp κ → ValUnit κ := by
  first | exact @GlobalTheory.KeyValUnit.valUnit | exact GlobalTheory.KeyValUnit.valUnit | (intros; apply GlobalTheory.KeyValUnit.valUnit <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SimilitudeIsoThetaProductBaseChange
section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SimilitudeIsoThetaProductBaseChange
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

noncomputable section
namespace GlobalTheory.KeyRow

theorem comb_push {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {T : Over S} {T' : Over S'} (ψ : T'.left ⟶ T.left)
    (hψ : ψ ≫ T.hom = T'.hom ≫ f) {n : ℕ} (p : Fin n → (T ⟶ G)) (p' : Fin n → (T' ⟶ G'))
    (hp : ∀ c, (p' c).left ≫ φ = ψ ≫ (p c).left) (a : Fin n → ℤ) (ξ : 𝟙_ (Over S) ⟶ G) (ξ' : 𝟙_ (Over S') ⟶ G')
    (hξ : ξ'.left ≫ φ = f ≫ ξ.left) :
    ((List.ofFn fun c => p' c ^ a c).prod * (toUnit _ ≫ ξ')).left ≫ φ =
      ψ ≫ ((List.ofFn fun c => p c ^ a c).prod * (toUnit _ ≫ ξ)).left := by
  let U : Over.mk (T'.hom ≫ f) ⟶ T := Over.homMk ψ hψ
  have e₁ : ∀ c, pushHom h T' (p' c) = preHom U (p c) := fun c => Over.OverMorphism.ext (hp c)
  have t : ∀ {B : Scheme.{0}} (V : Over B), (toUnit V).left = V.hom := fun V =>
    (Category.comp_id _).symm.trans (Over.w (toUnit V))
  have e₂ : pushHom h T' (toUnit _ ≫ ξ') = preHom U (toUnit _ ≫ ξ) := Over.OverMorphism.ext (by
    show ((toUnit T').left ≫ ξ'.left) ≫ φ = ψ ≫ (toUnit T).left ≫ ξ.left
    rw [Category.assoc, hξ, t, t]
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ ξ.left) hψ.symm).trans (Category.assoc _ _ _)))
  have e : pushHom h T' ((List.ofFn fun c => p' c ^ a c).prod * (toUnit _ ≫ ξ')) =
      preHom U ((List.ofFn fun c => p c ^ a c).prod * (toUnit _ ≫ ξ)) := by
    rw [map_mul, map_mul, map_list_prod, map_list_prod, List.map_ofFn, List.map_ofFn, e₂]
    congr 3
    funext c
    simp only [Function.comp_apply, map_zpow, e₁]
  exact congrArg (fun z => z.left) e

theorem cancel_units {A K κ : Type} [CommRing A] [Fintype K] [Fintype κ] [DecidableEq κ] {N m : ℕ} (s : K → Aˣ)
    (t : κ → Aˣ) (v : Aˣ) (x : K → A) (c : (κ → Fin N) → A) (y : κ → Fin N → A)
    (h : ∏ r, (s r ^ 1).val * x r = (((∏ r, s r ^ (1 : ℤ)) * ∏ k, t k ^ (-(m : ℤ))) * v).val *
      ∑ I, c I * ∏ k, (t k ^ m).val * y k (I k)) :
    ∏ r, x r = v.val * ∑ I, c I * ∏ k, y k (I k) := by
  simp only [pow_one, zpow_one, zpow_neg, zpow_natCast, Finset.prod_mul_distrib, Finset.prod_inv_distrib,
    ← Units.coe_prod, mul_left_comm _ (∏ k, t k ^ m).val, ← Finset.mul_sum] at h
  refine (Units.mul_right_inj (∏ r, s r)).1 (h.trans ?_)
  rw [← _root_.mul_assoc, ← _root_.mul_assoc, ← Units.val_mul, ← Units.val_mul]
  congr 2
  rw [mul_comm (∏ k, t k ^ m), mul_right_comm, inv_mul_cancel_right]

theorem main : ∀ (R R' : Type) [CommRing R] [CommRing R'] (x : KeyIn R) (x' : KeyIn R') (f : R →+* R') φ u (m N : ℕ) (al : Matrix (Fin 4) (Fin 4) ℤ) (b : Fin N → RR x m) (b' : Fin N → RR x' m) (ξ : Fin 4 → Pt x) (ξ' : Fin 4 → Pt x') (w : LB.Gen (LB.LinComb x.P.L (K := Fin 4 ⊕ Fin 4) (Sum.elim (fun r => (alMap x al r (ξ r)).left) (fun c => (Out.powPr x.P.A c).left)) (Sum.elim (fun _ => 1) (fun _ => -(m : ℤ))))) (q : (Fin 4 → Fin N) → R), KeyVia x' x f φ u → (∀ k, SecVia x' x φ u (b' k) (b k)) → (∀ r, (ξ' r).left ≫ φ = spMap f ≫ (ξ r).left) → w.IsGen → (∀ (Z : Scheme.{0}) (ρ : Z ⟶ (Out.powObj x.P.A 4).left) (z : Z) J, Good x.P.L z J → ∏ r, gs (ρ ≫ (alMap x al r (ξ r)).left) z (x.P.L.U (J (ρ ≫ (alMap x al r (ξ r)).left))) (x.th.f (J (ρ ≫ (alMap x al r (ξ r)).left))) = (val w ρ z J).val * ∑ I' : Fin 4 → Fin N, gs ρ z ⊤ (cst (Out.powObj x.P.A 4).hom ⊤ (q I')) * ∏ c, gs (ρ ≫ (Out.powPr x.P.A c).left) z (x.P.L.U (J (ρ ≫ (Out.powPr x.P.A c).left))) ((b (I' c)).f (J (ρ ≫ (Out.powPr x.P.A c).left)))) → ∃ w' : LB.Gen (LB.LinComb x'.P.L (K := Fin 4 ⊕ Fin 4) (Sum.elim (fun r => (alMap x' al r (ξ' r)).left) (fun c => (Out.powPr x'.P.A c).left)) (Sum.elim (fun _ => 1) (fun _ => -(m : ℤ)))), w'.IsGen ∧ ∀ (Z : Scheme.{0}) (ρ : Z ⟶ (Out.powObj x'.P.A 4).left) (z : Z) J, Good x'.P.L z J → ∏ r, gs (ρ ≫ (alMap x' al r (ξ' r)).left) z (x'.P.L.U (J (ρ ≫ (alMap x' al r (ξ' r)).left))) (x'.th.f (J (ρ ≫ (alMap x' al r (ξ' r)).left))) = (val w' ρ z J).val * ∑ I' : Fin 4 → Fin N, gs ρ z ⊤ (cst (Out.powObj x'.P.A 4).hom ⊤ (f (q I'))) * ∏ c, gs (ρ ≫ (Out.powPr x'.P.A c).left) z (x'.P.L.U (J (ρ ≫ (Out.powPr x'.P.A c).left))) ((b' (I' c)).f (J (ρ ≫ (Out.powPr x'.P.A c).left))) := by
  rintro R R' _ _ x x' f φ u m N al b b' ξ ξ' w q ⟨he, hg, F, hφ, hu, -, hth, -⟩ hb hξ hw H
  obtain ⟨ψ, hψ, hc⟩ := KeyPow.exists_isGrpPullback_pow hφ (Out.powIsPowGrp x.P.A 4) (Out.powIsPowGrp x'.P.A 4)
  have hc' : ∀ c : Fin 4, (Out.powPr x'.P.A c).left ≫ φ = ψ ≫ (Out.powPr x.P.A c).left := hc
  have ha : ∀ r, (alMap x' al r (ξ' r)).left ≫ φ = ψ ≫ (alMap x al r (ξ r)).left := fun r =>
    comb_push hφ ψ hψ.1.w _ _ hc' (al r) (ξ r) (ξ' r) (hξ r)
  obtain ⟨w', hw', P⟩ := H1.exists_gen_move x.P.isLB x'.P.isLB u ((isGen_iff u).1 hu) _
    (Sum.elim (fun r => (alMap x' al r (ξ' r)).left) (fun c => (Out.powPr x'.P.A c).left)) _ ψ
    (by rintro (r | c); exacts [ha r, hc' c]) w hw
  refine ⟨w', hw', fun Z ρ z J' hJ' => ?_⟩
  choose J hJ using fun χ : Z ⟶ x.P.A.left => exists_chart x.P.isLB (χ z)
  have ha' : ∀ r, (ρ ≫ ψ) ≫ (alMap x al r (ξ r)).left = (ρ ≫ (alMap x' al r (ξ' r)).left) ≫ φ := fun r => by
    rw [Category.assoc, Category.assoc, ha]
  have hc'' : ∀ c : Fin 4, (ρ ≫ ψ) ≫ (Out.powPr x.P.A c).left = (ρ ≫ (Out.powPr x'.P.A c).left) ≫ φ := fun r => by
    rw [Category.assoc, Category.assoc, hc']
  have E := H Z (ρ ≫ ψ) z J hJ
  have hv := (val_of w (ρ ≫ ψ) z J (fun k => J ((ρ ≫ Sum.elim (fun r => (alMap x' al r (ξ' r)).left)
    (fun c => (Out.powPr x'.P.A c).left) k) ≫ φ)) (by rintro (r | c); exacts [congrArg J (ha' r), congrArg J (hc'' c)])).trans
    (P Z ρ z _ (fun k => J' (ρ ≫ Sum.elim (fun r => (alMap x' al r (ξ' r)).left)
    (fun c => (Out.powPr x'.P.A c).left) k)) (fun k => hJ _) (fun k => hJ' _))
  rw [Fintype.prod_sum_type] at hv
  have hth' : KeyVia.Via u 1 x'.th.f x.th.f := fun j i h => (hth j i h).trans (by rw [pow_one])
  have hq : ∀ a : R, gs (ρ ≫ ψ) z ⊤ (cst (Out.powObj x.P.A 4).hom ⊤ a) =
      gs ρ z ⊤ (cst (Out.powObj x'.P.A 4).hom ⊤ (f a)) := fun a =>
    (gs_appLE ψ ⊤ ⊤ le_top ρ z trivial _).symm.trans
      (congrArg (gs ρ z ⊤) (KeyVia.appLE_cst f _ _ hψ.1.w le_top a))
  rw [hv] at E
  refine cancel_units (m := m)
    (fun r => gw u (ρ ≫ (alMap x' al r (ξ' r)).left) z (J ((ρ ≫ (alMap x' al r (ξ' r)).left) ≫ φ))
      (J' (ρ ≫ (alMap x' al r (ξ' r)).left)))
    (fun c => gw u (ρ ≫ (Out.powPr x'.P.A c).left) z (J ((ρ ≫ (Out.powPr x'.P.A c).left) ≫ φ))
      (J' (ρ ≫ (Out.powPr x'.P.A c).left))) _ _ _
    (fun c k => gs (ρ ≫ (Out.powPr x'.P.A c).left) z (x'.P.L.U (J' (ρ ≫ (Out.powPr x'.P.A c).left)))
      ((b' k).f (J' (ρ ≫ (Out.powPr x'.P.A c).left)))) ?_
  refine Eq.trans (Finset.prod_congr rfl fun r _ => ?_) (E.trans (congrArg₂ (· * ·) rfl
    (Finset.sum_congr rfl fun I _ => congrArg₂ (· * ·) (hq _) (Finset.prod_congr rfl fun c _ => ?_))))
  · rw [ha']
    exact (KeyBasis.via_val hth' _ z (hJ _) (hJ' _)).symm
  · rw [hc'']
    exact KeyBasis.via_val (w := u) (hb (I c)) _ z (hJ _) (hJ' _)

end GlobalTheory.KeyRow
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SimilitudeIsoThetaProductBaseChangeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.similitudeIso_thetaProduct_baseChange : ∀ (R R' : Type) [CommRing R] [CommRing R'] (x : KeyIn R) (x' : KeyIn R') (f : R →+* R') φ u (m N : ℕ) (al : Matrix (Fin 4) (Fin 4) ℤ) (b : Fin N → RR x m) (b' : Fin N → RR x' m) (ξ : Fin 4 → Pt x) (ξ' : Fin 4 → Pt x') (w : LB.Gen (LB.LinComb x.P.L (K := Fin 4 ⊕ Fin 4) (Sum.elim (fun r => (alMap x al r (ξ r)).left) (fun c => (Out.powPr x.P.A c).left)) (Sum.elim (fun _ => 1) (fun _ => -(m : ℤ))))) (q : (Fin 4 → Fin N) → R), KeyVia x' x f φ u → (∀ k, SecVia x' x φ u (b' k) (b k)) → (∀ r, (ξ' r).left ≫ φ = spMap f ≫ (ξ r).left) → w.IsGen → (∀ (Z : Scheme.{0}) (ρ : Z ⟶ (Out.powObj x.P.A 4).left) (z : Z) J, Good x.P.L z J → ∏ r, gs (ρ ≫ (alMap x al r (ξ r)).left) z (x.P.L.U (J (ρ ≫ (alMap x al r (ξ r)).left))) (x.th.f (J (ρ ≫ (alMap x al r (ξ r)).left))) = (val w ρ z J).val * ∑ I' : Fin 4 → Fin N, gs ρ z ⊤ (cst (Out.powObj x.P.A 4).hom ⊤ (q I')) * ∏ c, gs (ρ ≫ (Out.powPr x.P.A c).left) z (x.P.L.U (J (ρ ≫ (Out.powPr x.P.A c).left))) ((b (I' c)).f (J (ρ ≫ (Out.powPr x.P.A c).left)))) → ∃ w' : LB.Gen (LB.LinComb x'.P.L (K := Fin 4 ⊕ Fin 4) (Sum.elim (fun r => (alMap x' al r (ξ' r)).left) (fun c => (Out.powPr x'.P.A c).left)) (Sum.elim (fun _ => 1) (fun _ => -(m : ℤ)))), w'.IsGen ∧ ∀ (Z : Scheme.{0}) (ρ : Z ⟶ (Out.powObj x'.P.A 4).left) (z : Z) J, Good x'.P.L z J → ∏ r, gs (ρ ≫ (alMap x' al r (ξ' r)).left) z (x'.P.L.U (J (ρ ≫ (alMap x' al r (ξ' r)).left))) (x'.th.f (J (ρ ≫ (alMap x' al r (ξ' r)).left))) = (val w' ρ z J).val * ∑ I' : Fin 4 → Fin N, gs ρ z ⊤ (cst (Out.powObj x'.P.A 4).hom ⊤ (f (q I'))) * ∏ c, gs (ρ ≫ (Out.powPr x'.P.A c).left) z (x'.P.L.U (J (ρ ≫ (Out.powPr x'.P.A c).left))) ((b' (I' c)).f (J (ρ ≫ (Out.powPr x'.P.A c).left))) := by
  first | exact @GlobalTheory.KeyRow.main | exact GlobalTheory.KeyRow.main | (intros; apply GlobalTheory.KeyRow.main <;> assumption)
end
end
