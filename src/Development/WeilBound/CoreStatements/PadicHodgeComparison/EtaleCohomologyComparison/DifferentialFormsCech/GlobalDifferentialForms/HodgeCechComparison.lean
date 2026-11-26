module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechHodgeToCohomologyIso
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.GlobalDifferentialForms.AffineOpenCaps.GlobTerm

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechHodgeDegenerationNatural
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoverIntersectionGradedVanish
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoverIntersectionGradedIsoStatement
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoverIntersectionGradedIso
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Glob

namespace GlobalTheory.CompanionTheory.CapKC

variable {K : Type} [CommRing K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))

theorem inU_capO {O : Type} [CommRing O] {R : Type} [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ}
    {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} {ι : Type} (U : ι → X.Opens) {n : ℕ}
    (i : Fin n → ι) (T : Thick (nlFun γ p X q κ)) : InU (capO U i) T ↔ ∀ a, InU (U (i a)) T := by
  constructor
  · intro h a x hx
    exact capO_le U i a (h hx)
  · intro h x hx
    let W : X.Opens := ⟨⋂ a, (U (i a) : Set X), isOpen_iInter_of_finite fun a => (U (i a)).isOpen⟩
    have hW : W ≤ capO U i := le_iInf fun a y hy => Set.mem_iInter.1 hy a
    exact hW (Set.mem_iInter.2 fun a => h a hx)

variable (U : Cov q) (a n : ℕ) (i : Fin (n + 1) → U.ι)

def toCap : (KS q (a + 1) {capO U.U i}).FullSubcategory ⥤ (capT (Vk q U a) i).FullSubcategory :=
  (capT (Vk q U a) i).lift ((KC q U a).lift (KS q (a + 1) {capO U.U i}).ι fun T =>
      ⟨T.property.1, U.U (i 0), ⟨i 0, rfl⟩, by
        obtain ⟨_, V, rfl, hV⟩ := T.property
        exact (inU_capO U.U i T.obj).1 hV 0⟩) fun T k => by
    obtain ⟨_, V, rfl, hV⟩ := T.property
    exact (inU_capO U.U i T.obj).1 hV k

def ofCap : (capT (Vk q U a) i).FullSubcategory ⥤ (KS q (a + 1) {capO U.U i}).FullSubcategory :=
  (KS q (a + 1) {capO U.U i}).lift ((capT (Vk q U a) i).ι ⋙ (KC q U a).ι) fun T =>
    ⟨T.obj.property.1, capO U.U i, rfl, (inU_capO U.U i T.obj.obj).2 T.property⟩

def capAdj : toCap q U a n i ⊣ ofCap q U a n i := Adjunction.mkOfHomEquiv
  { homEquiv := fun A B =>
      { toFun := fun g => ObjectProperty.homMk g.hom.hom
        invFun := fun g => ObjectProperty.homMk (ObjectProperty.homMk g.hom)
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    homEquiv_naturality_left_symm := fun _ _ => rfl
    homEquiv_naturality_right := fun _ _ => rfl }

theorem cap_kc : ∀ {K : Type} [CommRing K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (U : Cov q) (a n : ℕ)
    (i : Fin (n + 1) → U.ι) (r : ℕ), Nonempty (HU (Fk q U a) (capT (Vk q U a) i) r ≃+ HQ (KS q (a + 1) {capO U.U i}) (a : ℤ) ((a : ℤ) + 1) r) := by
  intro K _ X q U a n i r
  have hb := CrystallineSemistableComparison.P.adj ((capT (Vk q U a) i).ι ⋙ Fk q U a) (toCap q U a n i) (ofCap q U a n i) (capAdj q U a n i) r
  exact ⟨(LinearEquiv.ofBijective _ hb).toAddEquiv⟩

end GlobalTheory.CompanionTheory.CapKC
end
end

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Glob GlobalTheory.CompanionTheory.CechSerre
universe w
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cover_intersection_graded_iso : ∀ {K : Type} [CommRing K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (U : Cov q) (a n : ℕ)
    (i : Fin (n + 1) → U.ι) (r : ℕ), Nonempty (HU (Fk q U a) (capT (Vk q U a) i) r ≃+ HQ (KS q (a + 1) {capO U.U i}) (a : ℤ) ((a : ℤ) + 1) r) := by
  first | exact @GlobalTheory.CompanionTheory.CapKC.cap_kc | exact GlobalTheory.CompanionTheory.CapKC.cap_kc | (intros; apply GlobalTheory.CompanionTheory.CapKC.cap_kc <;> assumption)
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoverIntersectionGradedVanish
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Glob GlobalTheory.CompanionTheory.CechSerre
universe w

namespace GlobalTheory.CompanionTheory.CapVan

theorem capO_eq_iInf_image {X : Scheme.{0}} {ι : Type} [DecidableEq ι] [Fintype ι] (V : ι → X.Opens) {m : ℕ}
    (i : Fin m → ι) : capO V i = ⨅ α ∈ Finset.image i Finset.univ, V α := by
  show (⨅ a, V (i a)) = _
  apply le_antisymm
  · refine le_iInf₂ fun α hα => ?_
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hα
    exact iInf_le _ a
  · exact le_iInf fun a => iInf₂_le (i a) (Finset.mem_image_of_mem i (Finset.mem_univ a))

theorem van {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) [Smooth q]
    (U : Cov q) (a n : ℕ) (i : Fin (n + 1) → U.ι) (r : ℕ) (hr : r ≠ a) :
    Subsingleton (HU (Fk q U a) (capT (Vk q U a) i) r) := by
  classical
  obtain ⟨e⟩ := GlobalTheory.T.cover_intersection_graded_iso q U a n i r
  have hV : IsAffineOpen (capO U.U i) := by
    rw [capO_eq_iInf_image]
    exact U.inter _ ⟨i 0, Finset.mem_image_of_mem i (Finset.mem_univ 0)⟩
  haveI := CrystallineSemistableComparison.Pb.gr_aff q (capO U.U i) hV (a + 1) a r (Nat.lt_succ_self a) hr
  exact e.injective.subsingleton

end GlobalTheory.CompanionTheory.CapVan
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoverIntersectionGradedVanishStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Glob GlobalTheory.CompanionTheory.CechSerre
universe w
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cover_intersection_graded_vanish : ∀ {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) [Smooth q]
    (U : Cov q) (a n : ℕ) (i : Fin (n + 1) → U.ι) (r : ℕ), r ≠ a → Subsingleton (HU (Fk q U a) (capT (Vk q U a) i) r) := by
  first | exact @GlobalTheory.CompanionTheory.CapVan.van | exact GlobalTheory.CompanionTheory.CapVan.van | (intros; apply GlobalTheory.CompanionTheory.CapVan.van <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoverStarIsCosieve
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoverStarIsCosieve
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Glob GlobalTheory.CompanionTheory.CechSerre
universe w

namespace GlobalTheory.CompanionTheory.OmGlob

theorem vk_cosieve {K : Type} [CommRing K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (U : Cov q) (a : ℕ) (α : U.ι) :
    Cosieve (Vk q U a α) :=
  fun _ _ φ h => Site.inU_hom φ.hom h

end GlobalTheory.CompanionTheory.OmGlob
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoverStarIsCosieveStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Glob GlobalTheory.CompanionTheory.CechSerre
universe w
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cover_star_isCosieve : ∀ {K : Type} [CommRing K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (U : Cov q) (a : ℕ) (α : U.ι),
    Cosieve (Vk q U a α) := by
  first | exact @GlobalTheory.CompanionTheory.OmGlob.vk_cosieve | exact GlobalTheory.CompanionTheory.OmGlob.vk_cosieve | (intros; apply GlobalTheory.CompanionTheory.OmGlob.vk_cosieve <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechHodgeDegenerationNatural
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Glob GlobalTheory.CompanionTheory.CechSerre
universe w

noncomputable section
namespace GlobalTheory.CompanionTheory.OmGlobSite

variable {K : Type} [Field K]

theorem vk_cover {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (U : Cov q) (a : ℕ) (T : (KC q U a).FullSubcategory) :
    ∃ α, Vk q U a α T := by
  obtain ⟨-, V, ⟨α, rfl⟩, h⟩ := T.property
  exact ⟨α, h⟩

theorem cov_sSup {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (U : Cov q) : sSup (Set.range U.U) = ⊤ := by
  rw [sSup_range]
  exact U.cover

def rho {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (U : Cov q) (a n : ℕ) :
    HT.Hdg q a n ≃ₗ[K] CH.H (Fk q U a) n :=
  LinearEquiv.ofBijective ((CH.Mor.restrict (HT.grT (smFun X q) a) (KC q U a).ι).pull n)
    (GlobalTheory.CompanionTheory.OmLoc.grT_restrict_bijective q _ (cov_sSup q U) a (a + 1) (Nat.lt_succ_self a) n)

theorem rho_pull {X Y : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (p : Y ⟶ Spec (CommRingCat.of K))
    (u : X ⟶ Y) (hu : u ≫ p = q) (U : Cov q) (W : Cov p) (a n : ℕ)
    (hG : ∀ T, KC q U a T → KC p W a ((pullM u hu a).G.obj T)) (x : HT.Hdg p a n) :
    rho q U a n (HT.pullH u hu a n x) =
      (morU (pullM u hu a) (U := KC p W a) (U' := KC q U a) hG).pull n (rho p W a n x) := by
  have h1 := (CrystallineSemistableComparison.P.pull_comp (σ'' := RingHom.id K) (pullM u hu a)
    (CH.Mor.restrict (HT.grT (smFun X q) a) (KC q U a).ι) n x).1
  have h2 := (CrystallineSemistableComparison.P.pull_comp (σ'' := RingHom.id K)
    (CH.Mor.restrict (HT.grT (smFun Y p) a) (KC p W a).ι)
    (morU (pullM u hu a) (U := KC p W a) (U' := KC q U a) hG) n x).1
  change (CH.Mor.restrict (HT.grT (smFun X q) a) (KC q U a).ι).pull n ((pullM u hu a).pull n x) =
    (morU (pullM u hu a) (U := KC p W a) (U' := KC q U a) hG).pull n
      ((CH.Mor.restrict (HT.grT (smFun Y p) a) (KC p W a).ι).pull n x)
  rw [← h1, ← h2]
  rfl

theorem glob_site : ∀ (K : Type) [Field K] [CharZero K],
    ∃ e : ∀ {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) [Smooth q] (U : Cov q) (a j : ℕ),
      HT.Hdg q a (a + j) ≃ₗ[K] (CrystallineSemistableComparison.Pb.cechH (Fk q U a) (Vk q U a) a).cx.H j,
    ∀ {X Y : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (p : Y ⟶ Spec (CommRingCat.of K)) [Smooth q] [Smooth p]
      (u : X ⟶ Y) (hu : u ≫ p = q) (U : Cov q) (W : Cov p) (τ : U.ι → W.ι) (a : ℕ)
      (hG : ∀ T, KC q U a T → KC p W a ((pullM u hu a).G.obj T))
      (hτ : ∀ α T, Vk q U a α T → Vk p W a (τ α) ((morU (pullM u hu a) (U := KC p W a) (U' := KC q U a) hG).G.obj T))
      (j : ℕ) (c : (CrystallineSemistableComparison.Pb.cechH (Fk p W a) (Vk p W a) a).X j) (h0 : (CrystallineSemistableComparison.Pb.cechH (Fk p W a) (Vk p W a) a).cx.d j c = 0)
      (h1 : (CrystallineSemistableComparison.Pb.cechH (Fk q U a) (Vk q U a) a).cx.d j (fun i =>
        (morU (morU (pullM u hu a) (U := KC p W a) (U' := KC q U a) hG) (U := capT (Vk p W a) (τ ∘ i))
          (U' := capT (Vk q U a) i) fun T hT k => hτ (i k) T (hT k)).pull a (c (τ ∘ i))) = 0),
      HT.pullH u hu a (a + j) ((e p W a j).symm ((CrystallineSemistableComparison.Pb.cechH (Fk p W a) (Vk p W a) a).cx.cls c h0)) =
        (e q U a j).symm ((CrystallineSemistableComparison.Pb.cechH (Fk q U a) (Vk q U a) a).cx.cls _ h1) := by
  intro K _ _
  obtain ⟨E, hE⟩ := GlobalTheory.T.cech_hodge_to_cohomology_iso K
  refine ⟨fun q _ U a j => (rho q U a (a + j)).trans
      (E (Fk q U a) (Vk q U a) (GlobalTheory.T.cover_star_isCosieve q U a) (vk_cover q U a) a
        (fun n i r hr => GlobalTheory.T.cover_intersection_graded_vanish q U a n i r hr) j), ?_⟩
  intro X Y q p _ _ u hu U W τ a hG hτ j c h0 h1
  dsimp only
  rw [LinearEquiv.symm_trans_apply, LinearEquiv.symm_trans_apply]
  apply (rho q U a (a + j)).injective
  rw [LinearEquiv.apply_symm_apply, rho_pull q p u hu U W a (a + j) hG, LinearEquiv.apply_symm_apply]
  exact hE _ _ _ _ (GlobalTheory.T.cover_star_isCosieve p W a) (vk_cover p W a) (GlobalTheory.T.cover_star_isCosieve q U a) (vk_cover q U a) a
    (fun n i r hr => GlobalTheory.T.cover_intersection_graded_vanish p W a n i r hr) (fun n i r hr => GlobalTheory.T.cover_intersection_graded_vanish q U a n i r hr)
    (morU (pullM u hu a) hG) τ hτ j c h0 h1

end GlobalTheory.CompanionTheory.OmGlobSite
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechHodgeDegenerationNaturalStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Glob GlobalTheory.CompanionTheory.CechSerre
universe w
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cech_hodge_degeneration_natural : ∀ (K : Type) [Field K] [CharZero K],
    ∃ e : ∀ {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) [Smooth q] (U : Cov q) (a j : ℕ),
      HT.Hdg q a (a + j) ≃ₗ[K] (cechH (Fk q U a) (Vk q U a) a).cx.H j,
    ∀ {X Y : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (p : Y ⟶ Spec (CommRingCat.of K)) [Smooth q] [Smooth p]
      (u : X ⟶ Y) (hu : u ≫ p = q) (U : Cov q) (W : Cov p) (τ : U.ι → W.ι) (a : ℕ)
      (hG : ∀ T, KC q U a T → KC p W a ((pullM u hu a).G.obj T))
      (hτ : ∀ α T, Vk q U a α T → Vk p W a (τ α) ((morU (pullM u hu a) (U := KC p W a) (U' := KC q U a) hG).G.obj T))
      (j : ℕ) (c : (cechH (Fk p W a) (Vk p W a) a).X j) (h0 : (cechH (Fk p W a) (Vk p W a) a).cx.d j c = 0)
      (h1 : (cechH (Fk q U a) (Vk q U a) a).cx.d j (fun i =>
        (morU (morU (pullM u hu a) (U := KC p W a) (U' := KC q U a) hG) (U := capT (Vk p W a) (τ ∘ i))
          (U' := capT (Vk q U a) i) fun T hT k => hτ (i k) T (hT k)).pull a (c (τ ∘ i))) = 0),
      HT.pullH u hu a (a + j) ((e p W a j).symm ((cechH (Fk p W a) (Vk p W a) a).cx.cls c h0)) =
        (e q U a j).symm ((cechH (Fk q U a) (Vk q U a) a).cx.cls _ h1) := by
  first | exact @GlobalTheory.CompanionTheory.OmGlobSite.glob_site | exact GlobalTheory.CompanionTheory.OmGlobSite.glob_site | (intros; apply GlobalTheory.CompanionTheory.OmGlobSite.glob_site <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PullbackCoverStarCompat
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PullbackCoverStarCompat
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Glob GlobalTheory.CompanionTheory.CechSerre
universe w

noncomputable section

namespace GlobalTheory.CompanionTheory.OmGlobPush

theorem push_kc : ∀ {K : Type} [CommRing K] {X Y : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (p : Y ⟶ Spec (CommRingCat.of K))
    (u : X ⟶ Y) (hu : u ≫ p = q) (U : Cov q) (W : Cov p) (τ : U.ι → W.ι)
    (hτ : ∀ n (i : Fin (n + 1) → U.ι), capO U.U i ≤ u ⁻¹ᵁ capO W.U (τ ∘ i)) (a : ℕ),
    ∃ hG : ∀ T, KC q U a T → KC p W a ((pullM u hu a).G.obj T),
      ∀ α T, Vk q U a α T → Vk p W a (τ α) ((morU (pullM u hu a) (U := KC p W a) (U' := KC q U a) hG).G.obj T) := by
  intro K _ X Y q p u hu U W τ hτ a
  have key : ∀ (T : GlobalTheory.LogCris.Thick (CrystallineSemistableComparison.smFun X q)) (α : U.ι),
      CrystallineSemistableComparison.Pb.InU (U.U α) T → CrystallineSemistableComparison.Pb.InU (W.U (τ α)) ((pullM u hu a).G.obj T) := by
    intro T α h
    have h0 : U.U α ≤ u ⁻¹ᵁ W.U (τ α) := by
      have h1 := hτ 0 (fun _ => α)
      simpa [CrystallineSemistableComparison.Pb.capO] using h1
    unfold CrystallineSemistableComparison.Pb.InU at h ⊢
    change ⊤ ≤ (TopologicalSpace.Opens.map (pt T ≫ u).base).obj (W.U (τ α))
    exact h.trans ((TopologicalSpace.Opens.map (pt T).base).monotone h0)
  have ktf : ∀ (T : GlobalTheory.LogCris.Thick (CrystallineSemistableComparison.smFun X q)),
      CrystallineSemistableComparison.Pb.TF 1 (a + 1) T → CrystallineSemistableComparison.Pb.TF 1 (a + 1) ((pullM u hu a).G.obj T) := by
    intro T h
    exact h
  refine ⟨fun T hT => ?_, fun α T hT => ?_⟩
  · obtain ⟨hTF, V, ⟨α, rfl⟩, hV⟩ := hT
    exact ⟨ktf T hTF, W.U (τ α), ⟨τ α, rfl⟩, key T α hV⟩
  · exact key T.obj α hT

end GlobalTheory.CompanionTheory.OmGlobPush
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PullbackCoverStarCompatStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Glob GlobalTheory.CompanionTheory.CechSerre
universe w
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullback_cover_star_compat : ∀ {K : Type} [CommRing K] {X Y : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (p : Y ⟶ Spec (CommRingCat.of K))
    (u : X ⟶ Y) (hu : u ≫ p = q) (U : Cov q) (W : Cov p) (τ : U.ι → W.ι)
    (hτ : ∀ n (i : Fin (n + 1) → U.ι), capO U.U i ≤ u ⁻¹ᵁ capO W.U (τ ∘ i)) (a : ℕ),
    ∃ hG : ∀ T, KC q U a T → KC p W a ((pullM u hu a).G.obj T),
      ∀ α T, Vk q U a α T → Vk p W a (τ α) ((morU (pullM u hu a) (U := KC p W a) (U' := KC q U a) hG).G.obj T) := by
  first | exact @GlobalTheory.CompanionTheory.OmGlobPush.push_kc | exact GlobalTheory.CompanionTheory.OmGlobPush.push_kc | (intros; apply GlobalTheory.CompanionTheory.OmGlobPush.push_kc <;> assumption)
end
end

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Glob

namespace CrystallineSemistableComparison.Om.GlobPf2

section
variable {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (U : Cov q) (a : ℕ)
  (t : ∀ n (i : Fin (n + 1) → U.ι), HU (Fk q U a) (capT (Vk q U a) i) a ≃ₗ[K] OmU q (capO U.U i) a)

def tH (ht : ∀ m n (i : Fin (n + 1) → U.ι) (θ : Fin (m + 1) → Fin (n + 1)) (x : HU (Fk q U a) (capT (Vk q U a) (i ∘ θ)) a),
      t n i ((resU (Fk q U a) (U := capT (Vk q U a) (i ∘ θ)) (V := capT (Vk q U a) i) fun T hT k => hT (θ k)).pull a x) =
        formRes q (capO_comp U.U i θ) a (t m (i ∘ θ) x)) :
    Cx.Hom (cechH (Fk q U a) (Vk q U a) a).cx (formCos q U.U a).cx (RingHom.id K) where
  f n := LinearMap.pi fun i => (t n i).toLinearMap.comp (LinearMap.proj i)
  comm n x := by
    funext i
    let e := (t (n + 1) i).toAddEquiv.toAddMonoidHom
    have key : ∀ k : Fin (n + 2), (formCos q U.U a).δ n k (fun i' => t n i' (x i')) i =
        e ((cechH (Fk q U a) (Vk q U a) a).δ n k x i) := fun k =>
      (ht n (n + 1) i k.succAbove (x (i ∘ k.succAbove))).symm
    change (formCos q U.U a).d n (fun i' => t n i' (x i')) i =
      e ((cechH (Fk q U a) (Vk q U a) a).d n x i)
    rw [Cos.d_apply, Cos.d_apply, Finset.sum_apply, Finset.sum_apply, map_sum e]
    exact Finset.sum_congr rfl fun k _ => by
      rw [Pi.smul_apply, Pi.smul_apply, e.map_zsmul, key k]

theorem tH_bij (ht) (n : ℕ) : Function.Bijective ((tH q U a t ht).f n) := by
  refine ⟨fun x y h => funext fun i => (t n i).injective (congrFun h i), fun y => ⟨fun i => (t n i).symm (y i), ?_⟩⟩
  funext i
  exact (t n i).apply_symm_apply (y i)

end

theorem cls_congr0 {R : Type} [CommRing R] (L : Cx.{0} R) (n : ℕ) (x y : L.X n) (hx : L.d n x = 0) (hy : L.d n y = 0)
    (h : x = y) : L.cls x hx = L.cls y hy := by
  subst h; rfl

theorem glob_iso : ∀ (K : Type) [Field K] [CharZero K],
    ∃ e : ∀ {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) [Smooth q] (U : Cov q) (a j : ℕ),
      HT.Hdg q a (a + j) ≃ₗ[K] (formCos q U.U a).cx.H j,
    ∀ {X Y : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (p : Y ⟶ Spec (CommRingCat.of K)) [Smooth q] [Smooth p]
      (u : X ⟶ Y) (hu : u ≫ p = q) (U : Cov q) (W : Cov p) (τ : U.ι → W.ι)
      (hτ : ∀ n (i : Fin (n + 1) → U.ι), capO U.U i ≤ u ⁻¹ᵁ capO W.U (τ ∘ i)) (a j : ℕ) (c : (formCos p W.U a).X j)
      (h0 : (formCos p W.U a).cx.d j c = 0)
      (h1 : (formCos q U.U a).cx.d j (fun i => formRes q (hτ j i) a (formPull hu (capO W.U (τ ∘ i)) a (c (τ ∘ i)))) = 0),
      HT.pullH u hu a (a + j) ((e p W a j).symm ((formCos p W.U a).cx.cls c h0)) =
        (e q U a j).symm ((formCos q U.U a).cx.cls _ h1) := by
  intro K _ _
  obtain ⟨e1, he1⟩ := GlobalTheory.T.cech_hodge_degeneration_natural K
  obtain ⟨t, htr, htp⟩ := GlobalTheory.CompanionTheory.OmGlobTerm.AssemblyHe1.term K
  let φ : ∀ {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) [Smooth q] (U : Cov q) (a : ℕ),
      Cx.Hom (cechH (Fk q U a) (Vk q U a) a).cx (formCos q U.U a).cx (RingHom.id K) := fun q _ U a =>
    tH q U a (t q U a) fun m n i θ x => htr q U a m n i θ x
  refine ⟨fun q _ U a j => (e1 q U a j).trans
    (LinearEquiv.ofBijective ((φ q U a).mapH j) (P.mapH_bij (φ q U a) (fun n => tH_bij q U a (t q U a) (fun m n i θ x => htr q U a m n i θ x) n) j)), ?_⟩
  intro X Y q p _ _ u hu U W τ hτ a j c h0 h1
  obtain ⟨hG, hτ'⟩ := GlobalTheory.T.pullback_cover_star_compat q p u hu U W τ hτ a

  let c₀ : (cechH (Fk p W a) (Vk p W a) a).X j := fun i => (t p W a j i).symm (c i)
  have hc₀ : (φ p W a).f j c₀ = c := funext fun i => (t p W a j i).apply_symm_apply (c i)
  have h0' : (cechH (Fk p W a) (Vk p W a) a).cx.d j c₀ = 0 := by
    refine (tH_bij p W a (t p W a) (fun m n i θ x => htr p W a m n i θ x) (j + 1)).1 ?_
    rw [map_zero, ← (φ p W a).comm, hc₀, h0]

  let c₁ : (cechH (Fk q U a) (Vk q U a) a).X j := fun i =>
    (morU (morU (pullM u hu a) (U := KC p W a) (U' := KC q U a) hG) (U := capT (Vk p W a) (τ ∘ i))
      (U' := capT (Vk q U a) i) fun T hT k => hτ' (i k) T (hT k)).pull a (c₀ (τ ∘ i))
  have hc₁ : (φ q U a).f j c₁ = fun i => formRes q (hτ j i) a (formPull hu (capO W.U (τ ∘ i)) a (c (τ ∘ i))) := by
    funext i
    refine (htp q p u hu U W τ hτ a hG j i (fun T hT k => hτ' (i k) T (hT k)) (c₀ (τ ∘ i))).trans ?_
    exact congrArg _ (congrArg _ ((t p W a j (τ ∘ i)).apply_symm_apply (c (τ ∘ i))))
  have h1' : (cechH (Fk q U a) (Vk q U a) a).cx.d j c₁ = 0 := by
    refine (tH_bij q U a (t q U a) (fun m n i θ x => htr q U a m n i θ x) (j + 1)).1 ?_
    rw [map_zero, ← (φ q U a).comm, hc₁, h1]
  have key := he1 q p u hu U W τ a hG hτ' j c₀ h0' h1'
  have eY : (LinearEquiv.ofBijective ((φ p W a).mapH j) (P.mapH_bij (φ p W a) (fun n => tH_bij p W a (t p W a) (fun m n i θ x => htr p W a m n i θ x) n) j)).symm
      ((formCos p W.U a).cx.cls c h0) = (cechH (Fk p W a) (Vk p W a) a).cx.cls c₀ h0' := by
    rw [LinearEquiv.symm_apply_eq, LinearEquiv.ofBijective_apply, P.mapH_cls (φ p W a) j c₀ h0' (by rw [hc₀]; exact h0)]
    exact cls_congr0 _ j _ _ _ _ hc₀.symm
  have eX : (LinearEquiv.ofBijective ((φ q U a).mapH j) (P.mapH_bij (φ q U a) (fun n => tH_bij q U a (t q U a) (fun m n i θ x => htr q U a m n i θ x) n) j)).symm
      ((formCos q U.U a).cx.cls _ h1) = (cechH (Fk q U a) (Vk q U a) a).cx.cls c₁ h1' := by
    rw [LinearEquiv.symm_apply_eq, LinearEquiv.ofBijective_apply, P.mapH_cls (φ q U a) j c₁ h1' (by rw [hc₁]; exact h1)]
    exact cls_congr0 _ j _ _ _ _ hc₁.symm
  rw [LinearEquiv.symm_trans_apply, LinearEquiv.symm_trans_apply, eY, eX]
  exact key

end CrystallineSemistableComparison.Om.GlobPf2
