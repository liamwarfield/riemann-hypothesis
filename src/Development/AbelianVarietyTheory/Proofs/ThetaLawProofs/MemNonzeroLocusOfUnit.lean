module

public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsIsLocalModelOfIntegral
public import Development.AbelianVarietyTheory.Statements.FundamentalDomains.IsLocalModelOfIntegral
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.SameObj
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsUnitThetaKeyRuleSmoothBase
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.MorphismDescendsToSubring
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKeyPBPair
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KeyRuleCharHalfOfCharZero

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.MemNonzeroLocusOfUnit
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.KeyOnPol

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

section Generator

variable {R : Type} [CommRing R]

theorem cst_mul₀ {Z : Scheme.{0}} (q : Z ⟶ Sp R) (z : Z) (a b : R) : cst q z (a * b) = cst q z a * cst q z b := by
  simp only [cst, gs_eq q z ⊤ trivial, map_mul]

theorem cst_one₀ {Z : Scheme.{0}} (q : Z ⟶ Sp R) (z : Z) : cst q z 1 = 1 := by
  simp only [cst, gs_eq q z ⊤ trivial, map_one]

def toPow {X : Scheme.{0}} {L : LB X} (s : L.Sec) : LB.Sec (AbLaw.pw L ((1 : ℕ) : ℤ)) :=
  ⟨s.f, fun i j => (s.compat i j).trans (congrArg (· * _) (congrArg Units.val (zpow_one (L.g i j)).symm))⟩

def ofPow {X : Scheme.{0}} {L : LB X} (s : LB.Sec (AbLaw.pw L ((1 : ℕ) : ℤ))) : L.Sec :=
  ⟨s.f, fun i j => (s.compat i j).trans (congrArg (· * _) (congrArg Units.val (zpow_one (L.g i j))))⟩

theorem exists_generator (hS : Out.SecBaseChangeSt) [IsLocalRing R] [IsNoetherianRing R] (P : Out.PolAV (Sp R)) :
    ∃ b : P.L.Sec, (∀ s : Sp R, ∃ z : P.A.left, P.A.hom z = s ∧ z ∈ Out.nonzeroLocus b) ∧
      ∀ s : P.L.Sec, ∃ a : R, ∀ i, s.f i = constFn P.A.hom _ a * b.f i := by
  obtain ⟨β, hβ⟩ := KeyBasis.exists_universal_basis hS R P 1 le_rfl
  have i₀ : Fin (1 ^ P.g) := ⟨0, by simp⟩
  have su : ∀ {M : Type} [AddCommMonoid M] (q : Fin (1 ^ P.g) → M), ∑ i, q i = q i₀ := fun q =>
    Finset.sum_eq_single i₀ (fun a _ h => absurd (Fin.ext (by have := a.2; have := i₀.2; simp at *; omega)) h) (by simp)
  have exists_pw_local (β : Out.H0 P.L 1) : ∃ b : LB.Sec (AbLaw.pw P.L ((1 : ℕ) : ℤ)),
      ∀ (Z : Scheme.{0}) (q : Z ⟶ P.A.left) (z : Z) (j : P.L.ι), q z ∈ P.L.U j →
        gs q z (LB.wchart P.L (fun _ : Fin 1 => 𝟙 _) (fun _ => j)) (β.f fun _ => j) = gs q z (P.L.U j) (b.f j) := by
    have le : ∀ j, P.L.U j ≤ LB.wchart P.L (fun _ : Fin 1 => 𝟙 _) (fun _ => j) := fun j y hy => Set.mem_iInter.2 fun _ => hy
    refine ⟨⟨fun j => resG _ (le j) (β.f fun _ => j), fun j i => fn_ext fun y hy => ?_⟩,
      fun Z q z j hj => (gs_res q z (le j) hj _).symm⟩
    refine ((gs_res (𝟙 _) y _ hy _).trans (gs_res (𝟙 _) y (le j) hy.1 _)).trans
      ((sec_trans β (𝟙 _) y (le j hy.1) (le i hy.2)).trans (Eq.trans ?_ (gs_mul (𝟙 _) y _ hy _ _).symm))
    refine congrArg₂ (· * ·) ?_ ((gs_res (𝟙 _) y _ hy _).trans (gs_res (𝟙 _) y (le i) hy.2 _)).symm
    refine Eq.trans ?_ ((gs_unit (𝟙 _) y _ hy _).trans (congrArg Units.val (map_zpow _ _ _))).symm
    refine congrArg Units.val ((Fin.prod_univ_one _).trans ?_)
    rw [Category.comp_id]
    rfl
  obtain ⟨b, hb⟩ := exists_pw_local (β i₀)
  have hv : ∀ (Z : Scheme.{0}) (q : Z ⟶ P.A.left) (z : Z) (J : (Z ⟶ P.A.left) → P.L.ι), Good P.L z J →
      sval (β i₀) q z J = gs q z (P.L.U (J q)) ((ofPow b).f (J q)) := fun Z q z J hJ =>
    (sval_of (β i₀) q z J (fun _ => J q) fun _ => by rw [Category.comp_id]).trans (hb Z q z _ (hJ q))
  have := P.isAb.smooth
  refine ⟨ofPow b, ?_, fun s => ?_⟩
  · let k := IsLocalRing.ResidueField R
    let t : Sp k ⟶ Sp R := spMap (IsLocalRing.residue R)
    let f := pullback.fst t P.A.hom
    let π := pullback.snd t P.A.hom
    have hp : IsPullback f π t P.A.hom := IsPullback.of_hasPullback _ _
    have : IsReduced (pullback t P.A.hom) := isReduced_scheme_of_smooth_of_isIntegrallyClosed k f
    obtain ⟨z, hz⟩ : ∃ z, π z ∈ Out.nonzeroLocus (ofPow b) := by
      by_contra hn
      have h0 : ∀ j, (π.app _).hom ((ofPow b).f j) = 0 := fun j => by
        refine (basicOpen_eq_bot_iff _).1 (eq_bot_iff.2 fun z hz => hn ⟨z, ?_⟩)
        rw [← Scheme.preimage_basicOpen] at hz
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨j, hz⟩
      obtain ⟨c, -, hu⟩ := hβ k t _ π f hp ⟨fun _ => 0, fun _ _ => by rw [map_zero, map_zero, mul_zero]⟩
      have hc : ∀ c, SectionLimit.Rep π f β ⟨fun _ => 0, fun _ _ => by rw [map_zero, map_zero, mul_zero]⟩ c := by
        intro c Z r z J hJ
        rw [su, hv Z _ z J hJ, ← gs_pull r π z _ (hJ (r ≫ π)), h0, gs_eq r z _ (hJ (r ≫ π)), map_zero, map_zero, mul_zero]
        exact (gs_eq r z _ (hJ.mem (fun _ : Fin 1 => π) r) _).trans ((congrArg _ (map_zero _)).trans (map_zero _))
      exact zero_ne_one (congrFun ((hu (fun _ => 0) (hc _)).trans (hu (fun _ => 1) (hc _)).symm) i₀)
    have hc : P.A.hom (π z) = IsLocalRing.closedPoint R := by
      refine (congrArg (fun g => g z) hp.w.symm).trans ?_
      refine Eq.trans ?_ (IsLocalRing.comap_closedPoint (IsLocalRing.residue R))
      exact congrArg (PrimeSpectrum.comap (IsLocalRing.residue R)) (Subsingleton.elim (α := PrimeSpectrum k) _ _)
    have ht := (IsLocalRing.closedPoint_mem_iff (R := R)
      ⟨_, P.A.hom.isOpenMap _ (Out.nonzeroLocus (ofPow b)).isOpen⟩).1 ⟨_, hz, hc⟩
    intro s
    obtain ⟨y, h₁, h₂⟩ := (congrArg (fun U => s ∈ U) ht).mpr trivial
    exact ⟨y, h₂, h₁⟩
  · have hpow (s : P.L.Sec) :
        ∃ t : Out.H0 P.L 1, ∀ (Z : Scheme.{0}) (r : Z ⟶ P.A.left) (z : Z) (k : P.L.ι), r z ∈ P.L.U k →
          gs r z (LB.wchart P.L (fun _ : Fin 1 => 𝟙 _) (fun _ => k)) (t.f fun _ => k) = gs r z (P.L.U k) (s.f k) := by
      have le : ∀ j : Fin 1 → P.L.ι, LB.wchart P.L (fun _ : Fin 1 => 𝟙 _) j ≤ P.L.U (j 0) := fun j y hy => Set.mem_iInter.1 hy 0
      refine ⟨⟨fun j => resG _ (le j) (s.f (j 0)), fun i j => fn_ext fun y hy => ?_⟩,
        fun Z r z k h => gs_res r z (le fun _ => k) (Set.mem_iInter.2 fun _ => h) _⟩
      refine ((gs_res (𝟙 _) y _ hy _).trans (gs_res (𝟙 _) y (le i) hy.1 _)).trans
        ((gs_compat s (𝟙 _) y (le i hy.1) (le j hy.2)).trans (Eq.symm ((gs_mul (𝟙 _) y _ hy _ _).trans
          (congrArg₂ (· * ·) ((gs_unit (𝟙 _) y _ hy _).trans (congrArg Units.val ?_))
            ((gs_res (𝟙 _) y _ hy _).trans (gs_res (𝟙 _) y (le j) hy.2 _))))))
      refine (gm_linComb P.L _ _ (𝟙 _) y i j hy.1 hy.2).trans ?_
      simp [Geo.Tor.trF]
    obtain ⟨σ, hσ⟩ := hpow s
    obtain ⟨c, hc, -⟩ := hβ R (𝟙 _) _ (𝟙 _) P.A.hom (IsPullback.of_vert_isIso ⟨by simp⟩) σ
    refine ⟨c i₀, (sec_eq_iff _ _ _ _).2 fun i y hy => ?_⟩
    obtain ⟨J, hJ, hi⟩ := exists_good P.L P.isLB y (fun _ : PUnit => 𝟙 P.A.left) (fun _ => i) (fun _ _ _ => rfl) fun _ => hy
    have e := hc _ (𝟙 _) y J hJ
    rw [su, Category.id_comp, Category.id_comp, hv _ _ y J hJ, hi PUnit.unit,
      sval_of σ (𝟙 _) y J (fun _ => i) (fun _ => by rw [Category.comp_id]; exact hi PUnit.unit), hσ _ _ y i hy] at e
    exact e

end Generator

section Units

variable {R : Type} [CommRing R] {X : Scheme.{0}} {L : LB X}

def scale (p : X ⟶ Sp R) (a : R) (s : L.Sec) : L.Sec :=
  ⟨fun i => constFn p _ a * s.f i, fun i j => fn_ext fun y hy => by
    rw [gs_res _ y _ hy, gs_mul _ y _ hy.1, gs_mul _ y _ hy, gs_res _ y _ hy, gs_mul _ y _ hy.2, gs_constFn p _ _ y hy.1,
      gs_constFn p _ _ y hy.2, gs_unit _ y _ hy, gs_compat s (𝟙 X) y hy.1 hy.2, mul_left_comm]⟩

theorem isUnit_cst {Z : Scheme.{0}} (q : Z ⟶ Sp R) (z : Z) (a : Rˣ) : IsUnit (cst q z (a : R)) :=
  IsUnit.of_mul_eq_one (cst q z (a⁻¹ : Rˣ)) (by rw [← cst_mul₀, Units.mul_inv, cst_one₀])

theorem mem_nonzeroLocus_of_unit (p : X ⟶ Sp R) (a : Rˣ) {s t : L.Sec} (h : ∀ i, t.f i = constFn p _ (a : R) * s.f i)
    {y : X} (hy : y ∈ Out.nonzeroLocus s) : y ∈ Out.nonzeroLocus t := by
  obtain ⟨k, hk, u⟩ := (mem_nonzeroLocus _ _).1 hy
  refine (mem_nonzeroLocus _ _).2 ⟨k, hk, ?_⟩
  rw [(sec_eq_iff _ _ _ _).1 h k y hk]
  exact (isUnit_cst p y a).mul u

theorem exists_unit (hS : Out.SecBaseChangeSt) [IsLocalRing R] [IsNoetherianRing R] (P : Out.PolAV (Sp R))
    (s t : P.L.Sec) (hs : ∀ y : Sp R, ∃ z : P.A.left, P.A.hom z = y ∧ z ∈ Out.nonzeroLocus s)
    (ht : ∀ y : Sp R, ∃ z : P.A.left, P.A.hom z = y ∧ z ∈ Out.nonzeroLocus t) :
    ∃ a : Rˣ, ∀ i, t.f i = constFn P.A.hom _ (a : R) * s.f i := by
  obtain ⟨b, -, hb⟩ := exists_generator hS P
  have key : ∀ s : P.L.Sec, (∀ y : Sp R, ∃ z : P.A.left, P.A.hom z = y ∧ z ∈ Out.nonzeroLocus s) →
      ∃ a : Rˣ, ∀ i, ∀ y ∈ P.L.U i, gs (𝟙 _) y _ (s.f i) = cst P.A.hom y (a : R) * gs (𝟙 _) y _ (b.f i) := fun s hs => by
    obtain ⟨a, ha⟩ := hb s
    have ha' := (sec_eq_iff _ _ _ _).1 ha
    obtain ⟨z, hz, hz'⟩ := hs (IsLocalRing.closedPoint R)
    obtain ⟨k, hk, u⟩ := (mem_nonzeroLocus _ _).1 hz'
    rw [ha' k z hk] at u
    have hu : IsUnit a := by
      by_contra hn
      exact cst_not_isUnit P.A.hom z hz ((IsLocalRing.mem_maximalIdeal a).2 hn) (isUnit_of_mul_isUnit_left u)
    obtain ⟨a, rfl⟩ := hu
    exact ⟨a, ha'⟩
  obtain ⟨a, ha⟩ := key s hs
  obtain ⟨c, hc⟩ := key t ht
  refine ⟨c * a⁻¹, (sec_eq_iff _ _ _ _).2 fun i y hy => ?_⟩
  rw [ha i y hy, hc i y hy, ← _root_.mul_assoc, ← cst_mul₀, ← Units.val_mul, inv_mul_cancel_right]

end Units

open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

theorem main : Out.Laws → ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R], (∀ P : Out.PolAV (Sp R), 1 ≤ P.g → ∃ x : KeyIn R, x.P = P) ∧ ∀ (x : KeyIn R) (rig' hr' th' hth' v' hv'), ∃ (a : Rˣ) (t : x.P.L.Sec) (ht : _), (∀ i, t.f i = constFn x.P.A.hom _ (a : R) * x.th.f i) ∧ KeyPB ⟨x.P, x.g_pos, rig', hr', th', hth', v', hv'⟩ ⟨x.P, x.g_pos, x.rig, x.rig_gen, t, ht, v', hv'⟩ (RingHom.id R) := by
  intro hL R _ _ _
  refine ⟨fun P hg => ?_, fun x rig' hr' th' hth' v' hv' => ?_⟩
  · obtain ⟨rig, hr⟩ := P.rigid
    obtain ⟨th, hth, -⟩ := exists_generator hL.secBaseChange P
    obtain ⟨v, hv⟩ := KeyPow.exists_isLieBasis P.A P.smoothDim
    exact ⟨⟨P, hg, rig, hr, th, hth, v, hv⟩, rfl⟩
  · have e : spMap (RingHom.id R) = 𝟙 (Sp R) := Spec.map_id _
    have e' : spMap (RingHom.id (DualNumber R)) = 𝟙 (Sp (DualNumber R)) := Spec.map_id _
    have : IsMonHom (Iso.refl x.P.A).hom := inferInstanceAs (IsMonHom (𝟙 _))
    have h : IsGrpPullback x.P.A x.P.A (spMap (RingHom.id R)) (𝟙 _) :=
      (isGrpPullback_of_iso (Iso.refl x.P.A)).congr e.symm rfl
    have he : eSec x.P.A ≫ 𝟙 _ = spMap (RingHom.id R) ≫ eSec x.P.A := PolBaseChange.eSec_comm h
    have := x.P.isAb.comm
    have hgen : PGen (isoPullId (idIso x.P.L) (rfl : 𝟙 x.P.A.left = 𝟙 x.P.A.left)) := by
      intro Y f y j j' k k' hj hj' hk hk'
      have heval (j : x.P.L.ι) (k : x.P.L.ι) (hj : f y ∈ x.P.L.U j) (hk : f y ∈ x.P.L.U k) :
          gw (isoPullId (idIso x.P.L) (rfl : 𝟙 x.P.A.left = 𝟙 x.P.A.left)) f y j k = gm f y _ ((idIso x.P.L).s (j, k)) := by
        have hmem : f y ∈ (x.P.L.pull (𝟙 _)).U (fun _ => j) ⊓ x.P.L.U k := ⟨mem_pull.2 hj, hk⟩
        exact gm_res f y _ hmem ((idIso x.P.L).s (j, k))
      rw [heval j k hj hk, heval j' k' hj' hk', Category.comp_id]
      have hV : f y ∈ (x.P.L.U j ⊓ x.P.L.U k) ⊓ (x.P.L.U j' ⊓ x.P.L.U k') := ⟨⟨hj, hk⟩, ⟨hj', hk'⟩⟩
      have hw := idIso_isGen x.P.isLB
      have hw' : res (inf_le_left : (x.P.L.U j ⊓ x.P.L.U k) ⊓ (x.P.L.U j' ⊓ x.P.L.U k') ≤ x.P.L.U j ⊓ x.P.L.U k) ((idIso x.P.L).s (j, k)) =
          res (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left)) (x.P.L.g j j') *
          (res (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)) (x.P.L.g k k'))⁻¹ *
          res (inf_le_right : (x.P.L.U j ⊓ x.P.L.U k) ⊓ (x.P.L.U j' ⊓ x.P.L.U k') ≤ x.P.L.U j' ⊓ x.P.L.U k') ((idIso x.P.L).s (j', k')) := hw (j, k) (j', k')
      have key := congrArg (gm f y ((x.P.L.U j ⊓ x.P.L.U k) ⊓ (x.P.L.U j' ⊓ x.P.L.U k'))) hw'
      simp only [map_mul, map_inv, gm_res f y _ hV] at key
      rw [gm_res f y (U := x.P.L.U j ⊓ x.P.L.U k) _ hV ((idIso x.P.L).s (j, k)),
        gm_res f y (U := x.P.L.U j' ⊓ x.P.L.U k') _ hV ((idIso x.P.L).s (j', k'))] at key
      exact key
    obtain ⟨w, hw, hm⟩ := KeyPow.exists_rescale x.P.isLB x.P.isLB hgen
      (p := x.P.A.hom) (Over.w η[x.P.A]) he hr' x.rig_gen
    obtain ⟨s, hs⟩ := sec_pull_down hw x.P.isLB x.P.isLB x.th
    obtain ⟨a, ha⟩ := exists_unit hL.secBaseChange x.P s th'
      (SectionBaseChange.fibre_nonzero_of_pull x.P.isLB hs h.1 x.th_ne) hth'
    refine ⟨a, scale x.P.A.hom a x.th, fun y => ?_, fun _ => rfl, 𝟙 _, he, w, rfl, RingHom.id _, h, (isGen_iff _).2 hw,
      (maps_iff w _ (fun _ => eSec x.P.A) _ rig' x.rig _ _ (rigPull_le _ _ he x.P.L) (fun _ => rfl)).2 hm,
      KeyPow.appLE_eq_of_stalk w _ th' fun z j k hj hk => ?_, fun _ => rfl, rfl,
      fun i => by rw [e']; exact (Category.comp_id _).trans (Category.id_comp _).symm⟩
    · obtain ⟨z, hz, hz'⟩ := x.th_ne y
      exact ⟨z, hz, mem_nonzeroLocus_of_unit x.P.A.hom a (fun _ => rfl) hz'⟩
    · have e₁ := hs _ (𝟙 _) z j k hj hk
      rw [Category.id_comp] at e₁ ⊢
      rw [(sec_eq_iff x.P.A.hom (scale x.P.A.hom a x.th) x.th a).1 (fun _ => rfl) j z hj, e₁,
        (sec_eq_iff _ _ _ _).1 ha k z hk, mul_left_comm]

end GlobalTheory.KeyOnPol
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKeyInNormalAt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa

namespace GlobalTheory.KeyOfPeriod

theorem exists_keyIn_normalAt :
    ThetaUnifAV → GlobalTheory.TorusAlgebraic → ∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ), 1 ≤ g → τ.IsSymm → (τ.map Complex.im).PosDef → charHalf g a b → ∃ (x : KeyIn ℂ) (h : x.P.g = g), NormalAt x (τ.submatrix (Fin.cast h) (Fin.cast h)) 1 (fun i => a (i.cast h)) (fun i => b (i.cast h)) 1 := by
  intro _ H g τ a b hg hs hp hab
  obtain ⟨P, u, th, e, hΛ, ⟨h₁, h₂⟩, hth, -⟩ := H g τ a b hs hp hab.1 hab.2
  subst e
  obtain ⟨rig, hr, hR⟩ := Test.exists_isRig u
  choose v hv using fun i : Fin P.g => (h₂ (Pi.single i (2 * Real.pi * Complex.I)⁻¹)).exists
  have hb := Test.isLieBasis_of_isDiff P u h₁ h₂ (inv_ne_zero Complex.two_pi_I_ne_zero) v
    (fun i => (hv i).1) fun i => (hv i).2
  obtain ⟨z, hz⟩ := Function.ne_iff.1 (TorusAlg.thetaChar_level hs hp hab.1 hab.2).1
  obtain ⟨i, hi⟩ := exists_chart P.isLB ((u.ex z).left (default : PrimeSpectrum ℂ))
  have hi' := (top_le_preimage_iff_mem _ _).2 hi
  have hne : th.f i ≠ 0 := fun h => by
    have := hth i z hi'
    rw [h, valAt'_zero] at this
    exact mul_ne_zero hz (u.fr_ne i z hi') this.symm
  exact ⟨⟨P, hg, rig, hr, th, exists_mem_nonzeroLocus P th ⟨i, hne⟩, v, hb⟩, rfl,
    (normalAt_one_iff _ _ _ _).2 ⟨u, hs, hp, hΛ, hR, hth, fun i => (hv i).2⟩⟩

end GlobalTheory.KeyOfPeriod
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.NormalFormsEqOfKeyDataIsoComplex
section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.NormalFormsEqOfKeyDataIsoComplex
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyKa
open GlobalTheory.KeyEq

noncomputable section
namespace GlobalTheory.KeyIsoNormal

abbrev pt : Sp ℂ := (default : PrimeSpectrum ℂ)

def toStalk : ℂ →+* (Sp ℂ).presheaf.stalk pt :=
  ((Sp ℂ).presheaf.germ ⊤ pt trivial).hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom

theorem gs_eq_toStalk {X : Scheme.{0}} (x : Sp ℂ ⟶ X) (U : X.Opens) (h : x pt ∈ U) (f : Γ(X, U)) :
    gs x pt U f = toStalk (valAt' x U f) := by
  have h' := (top_le_preimage_iff_mem x U).2 h
  rw [gs_eq x pt U h, valAt', dite_eq_left h', valAt, toStalk, RingHom.comp_apply]
  erw [(Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom_inv_id_apply]
  exact (TopCat.Presheaf.germ_res_apply (Sp ℂ).presheaf (homOfLE h') pt trivial _).symm

theorem gm_eq_toStalk {X : Scheme.{0}} (x : Sp ℂ ⟶ X) (U : X.Opens) (h : x pt ∈ U) (f : Γ(X, U)ˣ) :
    (gm x pt U f).val = toStalk (valAt' x U f.val) :=
  (gs_unit x pt U h f).symm.trans (gs_eq_toStalk x U h _)

section Unit

variable {X X' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X}

def wv (w : LB.Iso L' (L.pull F)) (y : Sp ℂ ⟶ X') (j : L.ι) (k : L'.ι) : ℂ :=
  valAt' y ((L.pull F).U (fun _ => j) ⊓ L'.U k) (w.s (fun _ => j, k)).val

theorem gw_eq_toStalk (w : LB.Iso L' (L.pull F)) (y : Sp ℂ ⟶ X') {j : L.ι} {k : L'.ι} (hj : F (y pt) ∈ L.U j)
    (hk : y pt ∈ L'.U k) : (gw w y pt j k).val = toStalk (wv w y j k) :=
  gm_eq_toStalk y ((L.pull F).U (fun _ => j) ⊓ L'.U k) ⟨mem_pull.2 hj, hk⟩ _

theorem wv_ne_zero (w : LB.Iso L' (L.pull F)) (y : Sp ℂ ⟶ X') {j : L.ι} {k : L'.ι} (hj : F (y pt) ∈ L.U j)
    (hk : y pt ∈ L'.U k) : wv w y j k ≠ 0 := fun h =>
  (gw w y pt j k).ne_zero (by rw [gw_eq_toStalk w y hj hk, h, map_zero])

theorem wv_compat {w : LB.Iso L' (L.pull F)} (hw : PGen w) (y : Sp ℂ ⟶ X') {j j' : L.ι} {k k' : L'.ι}
    (hj : F (y pt) ∈ L.U j) (hj' : F (y pt) ∈ L.U j') (hk : y pt ∈ L'.U k) (hk' : y pt ∈ L'.U k') :
    wv w y j k * valAt' y (L'.U k ⊓ L'.U k') (L'.g k k').val =
      valAt' (y ≫ F) (L.U j ⊓ L.U j') (L.g j j').val * wv w y j' k' := by
  apply toStalk.injective
  rw [map_mul, map_mul, ← gw_eq_toStalk w y hj hk, ← gw_eq_toStalk w y hj' hk',
    ← gm_eq_toStalk y (L'.U k ⊓ L'.U k') ⟨hk, hk'⟩, ← gm_eq_toStalk (y ≫ F) (L.U j ⊓ L.U j') ⟨hj, hj'⟩,
    hw _ y pt j j' k k' hj hj' hk hk', ← Units.val_mul, ← Units.val_mul, mul_right_comm, inv_mul_cancel_right]

end Unit

theorem comp_mul_of_isGrpPullback {S : Scheme.{0}} {A A' : Over S} [GrpObj A] [GrpObj A'] (ψ : A' ⟶ A)
    (h : IsGrpPullback A' A (𝟙 S) ψ.left) {T : Over S} (x y : T ⟶ A') : (x * y) ≫ ψ = (x ≫ ψ) * (y ≫ ψ) := by
  let e : T ⟶ Over.mk (T.hom ≫ 𝟙 S) := Over.homMk (𝟙 T.left) (by simp)
  let l : (T ⟶ A') → (Over.mk (T.hom ≫ 𝟙 S) ⟶ A) := fun x => Over.homMk (x ≫ ψ).left (by simp)
  have hl : ∀ x, e ≫ l x = x ≫ ψ := fun x => by ext; simp [e, l]
  have := h.2 T x y (l x) (l y) rfl rfl
  rw [← hl x, ← hl y, ← MonObj.comp_mul]
  ext
  rw [Over.comp_left, Over.comp_left, this]
  simp [e]

theorem exists_push {A A' : Over (Sp ℂ)} [GrpObj A] [GrpObj A'] {L : LB A.left} {L' : LB A'.left} (hL : L.IsLB)
    (hL' : L'.IsLB) (ψ : A' ⟶ A) (h : IsGrpPullback A' A (𝟙 _) ψ.left) (w : LB.Iso L' (L.pull ψ.left)) (hw : PGen w)
    {g : ℕ} (u' : HolUnif A' L' g) :
    ∃ u : HolUnif A L g, (∀ z, (u.ex z).left = (u'.ex z).left ≫ ψ.left) ∧ u.Λ = u'.Λ ∧
      ∀ j k z, ψ.left ((u'.ex z).left pt) ∈ L.U j → (u'.ex z).left pt ∈ L'.U k →
        u.fr j z = wv w (u'.ex z).left j k * u'.fr k z := by
  have : IsIso ψ.left := h.1.isIso_fst_of_isIso
  have : IsIso ((Over.forget _).map ψ) := this
  have : IsIso ψ := isIso_of_reflects_iso ψ (Over.forget _)
  have hm := fun x y : 𝟙_ (Over (Sp ℂ)) ⟶ A' => comp_mul_of_isGrpPullback ψ h x y
  have h1 : (1 : 𝟙_ (Over (Sp ℂ)) ⟶ A') ≫ ψ = 1 := by
    have := hm 1 1
    rw [_root_.mul_one] at this
    exact mul_eq_left.1 this.symm
  choose K hK using fun z => exists_chart hL' ((u'.ex z).left pt)
  have key : ∀ j k z, ψ.left ((u'.ex z).left pt) ∈ L.U j → (u'.ex z).left pt ∈ L'.U k →
      wv w (u'.ex z).left j (K z) * u'.fr (K z) z = wv w (u'.ex z).left j k * u'.fr k z := fun j k z hj hk => by
    have e := wv_compat hw (u'.ex z).left hj hj (hK z) hk
    have e' : valAt' ((u'.ex z).left ≫ ψ.left) (L.U j ⊓ L.U j) (L.g j j).val = 1 := by
      apply toStalk.injective
      rw [← gm_eq_toStalk _ (L.U j ⊓ L.U j) ⟨hj, hj⟩, gm_self hL ((u'.ex z).left ≫ ψ.left) pt hj, map_one, Units.val_one]
    rw [e', _root_.one_mul] at e
    rw [u'.fr_compat (K z) k z ((top_le_preimage_iff_mem _ _).2 ⟨hK z, hk⟩), ← _root_.mul_assoc, e]
  have mem : ∀ (U : A.left.Opens) z, ⊤ ≤ (u'.ex z ≫ ψ).left ⁻¹ᵁ U → ψ.left ((u'.ex z).left pt) ∈ U :=
    fun U z hz => (top_le_preimage_iff_mem _ _).1 hz
  refine ⟨
    { ex := fun z => u'.ex z ≫ ψ
      ex_add := fun z z' => by rw [u'.ex_add, hm]
      ex_onto := fun p => (u'.ex_onto (p ≫ inv ψ)).imp fun z hz => by simp [hz]
      Λ := u'.Λ
      ker := fun z => by rw [← u'.ker, ← h1, cancel_mono]
      discrete := u'.discrete
      full := u'.full
      hol := fun U f => by
        have := u'.hol (ψ.left ⁻¹ᵁ U) ((ψ.left.app U).hom f)
        simp only [valAt'_comp] at this
        exact this
      fr := fun j z => wv w (u'.ex z).left j (K z) * u'.fr (K z) z
      fr_hol := fun j z hz => ?_
      fr_ne := fun j z hz => mul_ne_zero (wv_ne_zero w _ (mem _ _ hz) (hK z))
        (u'.fr_ne _ _ ((top_le_preimage_iff_mem _ _).2 (hK z)))
      fr_compat := fun j j' z hz => ?_ }, fun _ => rfl, rfl, key⟩
  · obtain ⟨ho, hd⟩ := u'.hol ((L.pull ψ.left).U (fun _ => j) ⊓ L'.U (K z)) (w.s (fun _ => j, K z)).val
    have hn := ho.mem_nhds ((top_le_preimage_iff_mem _ _).2 ⟨mem_pull.2 (mem _ _ hz), hK z⟩)
    have hn' := (u'.hol (L'.U (K z)) 0).1.mem_nhds ((top_le_preimage_iff_mem _ _).2 (hK z))
    refine (((hd.differentiableAt hn).mul ((u'.fr_hol (K z)).differentiableAt hn')).congr_of_eventuallyEq
      ?_).differentiableWithinAt
    filter_upwards [hn] with y hy
    have hy' := (top_le_preimage_iff_mem _ _).1 hy
    exact key j (K z) y (mem_pull.1 hy'.1) hy'.2
  · have hz' := mem _ _ hz
    have e := wv_compat hw (u'.ex z).left hz'.1 hz'.2 (hK z) (hK z)
    rw [u'.fr_compat (K z) (K z) z ((top_le_preimage_iff_mem _ _).2 ⟨hK z, hK z⟩), ← _root_.mul_assoc, e,
      _root_.mul_assoc, ← u'.fr_compat (K z) (K z) z ((top_le_preimage_iff_mem _ _).2 ⟨hK z, hK z⟩)]
    rfl

def NormalIn (x : KeyIn ℂ) {g : ℕ} (h : x.P.g = g) (τ M : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (c : ℂ) : Prop :=
  ∃ u : HolUnif x.P.A x.P.L g,
    τ.IsSymm ∧ (τ.map Complex.im).PosDef ∧
    (∀ z, z ∈ u.Λ ↔ ∃ m n : Fin g → ℤ, z = (fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ))) ∧
    u.IsRig x.rig ∧ u.IsFn x.th (fun z => c * thetaChar τ a b z) ∧
    ∀ i, u.IsDiff ((2 * Real.pi * Complex.I)⁻¹ • M i) (x.v (i.cast h.symm))

theorem val_iff (x : KeyIn ℂ) {g : ℕ} (h : x.P.g = g) (t : ℂ) :
    Val x t ↔ ∃ (τ M : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (c : ℂ),
      charHalf _ a b ∧ c ≠ 0 ∧ NormalIn x h τ M a b c ∧ t = M.det ^ 4 / c ^ 8 := by
  subst h
  rfl

theorem nrm_iff (x : KeyIn ℂ) {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) :
    Nrm x τ a b ↔ ∃ (h : x.P.g = g) (M : Matrix (Fin g) (Fin g) ℂ) (c : ℂ), c ≠ 0 ∧ NormalIn x h τ M a b c := by
  refine exists_congr fun h => ?_
  subst h
  rfl

theorem NormalIn.push {x x' : KeyIn ℂ} (H : KeyPB x' x (RingHom.id ℂ)) {g : ℕ} (h : x.P.g = g) (h' : x'.P.g = g)
    {τ M : Matrix (Fin g) (Fin g) ℂ} {a b : Fin g → ℂ} {c : ℂ} (hN : NormalIn x' h' τ M a b c) :
    NormalIn x h τ M a b c := by
  obtain ⟨φ, he, w, hg, F, hc, hw, hr, hs, hF, hFe, hv⟩ := H
  obtain ⟨u', h₁, h₂, h₃, h₄, h₅, h₆⟩ := hN
  have hid : spMap (RingHom.id ℂ) = 𝟙 (Sp ℂ) := Spec.map_id _
  have hFid : spMap F = 𝟙 _ := by
    rw [KeyCancel.dualNumber_ringHom_ext (F := F) (G := RingHom.id _) hF hFe]
    exact Spec.map_id _
  have r := (maps_iff w _ (fun _ => eSec x.P.A) _ x'.rig x.rig (spMap (RingHom.id ℂ)) _
    (rigPull_le φ (spMap (RingHom.id ℂ)) he x.P.L) (fun _ => rfl)).1 hr
  rw [hid] at r he
  rw [Category.id_comp] at he
  have hc' := hc.congr hid rfl
  obtain ⟨u, hex, hΛ, hfr⟩ := exists_push x.P.isLB x'.P.isLB (Over.homMk φ (hc'.1.w.trans (Category.comp_id _))) hc' w
    ((isGen_iff w).1 hw) u'
  replace hex : ∀ z, (u.ex z).left = (u'.ex z).left ≫ φ := hex
  replace hfr : ∀ j k z, φ ((u'.ex z).left pt) ∈ x.P.L.U j → (u'.ex z).left pt ∈ x'.P.L.U k →
    u.fr j z = wv w (u'.ex z).left j k * u'.fr k z := hfr
  refine ⟨u, h₁, h₂, hΛ ▸ h₃, fun j hj => ?_, fun j z hz => ?_, fun i U hU f => ?_⟩
  · have h0 : (u'.ex 0).left = eSec x'.P.A := by
      rw [(u'.ker 0).2 u'.Λ.zero_mem]
      change (toUnit _ ≫ η[x'.P.A]).left = η[x'.P.A].left
      rw [toUnit_unit, Category.id_comp]
    obtain ⟨k, hk⟩ := exists_chart x'.P.isLB (eSec x'.P.A pt)
    have hj' : φ (eSec x'.P.A pt) ∈ x.P.L.U (j PUnit.unit) := by
      have := mem_pull.1 (hj (Set.mem_univ pt))
      rw [← he] at this
      exact this
    have hk' : (𝟙 (Sp ℂ) : Sp ℂ ⟶ Sp ℂ) pt ∈ (x'.P.L.pull (eSec x'.P.A)).U (fun _ => k) := mem_pull.2 hk
    have e := congrArg Units.val (r _ (𝟙 (Sp ℂ)) pt j (fun _ => k) (fun _ => hj') (fun _ => hk))
    rw [Fintype.prod_unique, zpow_one, Category.id_comp, Category.id_comp, Units.val_mul] at e
    rw [hfr _ k 0 (h0 ▸ hj') (h0 ▸ hk), h0, h₄ (fun _ => k) ((top_le_preimage_iff_mem (𝟙 _) _).2 hk')]
    apply toStalk.injective
    rw [map_mul]
    exact (congrArg₂ (· * ·) (gw_eq_toStalk w _ hj' hk).symm (gm_eq_toStalk _ _ hk' _).symm).trans
      (e.symm.trans (gm_eq_toStalk _ _ (hj (Set.mem_univ pt)) _))
  · rw [hex] at hz ⊢
    have hj : φ ((u'.ex z).left pt) ∈ x.P.L.U j := (top_le_preimage_iff_mem _ _).1 hz
    obtain ⟨k, hk⟩ := exists_chart x'.P.isLB ((u'.ex z).left pt)
    have e := (KeyCancel.appLE_eq_iff_stalk w x.th x'.th).1 hs _ (u'.ex z).left pt j k hj hk
    rw [gs_eq_toStalk _ _ hj, gs_eq_toStalk _ _ hk, gw_eq_toStalk w _ hj hk, ← map_mul] at e
    rw [toStalk.injective e, hfr j k z hj hk, h₅ k z ((top_le_preimage_iff_mem _ _).2 hk)]
    ring
  · have e : (x.v (i.cast h.symm)).left = (x'.v (i.cast h'.symm)).left ≫ φ := by
      rw [hv, hFid, Category.id_comp]
      rfl
    have := h₆ i (φ ⁻¹ᵁ U) (by rw [e] at hU; exact hU) ((φ.app U).hom f)
    simp only [valAt'_comp, ← hex] at this
    rw [← this]
    congr 2
    generalize (x.v (i.cast h.symm)).left = q at e hU
    subst e
    rw [Scheme.Hom.comp_appLE]
    rfl

theorem val_iff_and_nrm_iff : ∀ x x' : KeyIn ℂ, KeyPB x' x (RingHom.id ℂ) → (∀ t, Val x t ↔ Val x' t) ∧ ∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ), Nrm x τ a b ↔ Nrm x' τ a b := by
  intro x x' H
  have H' : KeyPB x x' (RingHom.id ℂ) :=
    KeyCancel.keyPB_cancel ℂ ℂ ℂ x x' x (RingHom.id ℂ) (RingHom.id ℂ) H (keyPB_id ℂ x)
  have hg : x'.P.g = x.P.g := by
    obtain ⟨-, -, -, hg, -⟩ := H
    exact hg
  refine ⟨fun t => ?_, fun g τ a b => ?_⟩
  · rw [val_iff x rfl, val_iff x' hg]
    exact ⟨fun ⟨τ, M, a, b, c, h₁, h₂, h₃, h₄⟩ => ⟨τ, M, a, b, c, h₁, h₂, h₃.push H' hg rfl, h₄⟩,
      fun ⟨τ, M, a, b, c, h₁, h₂, h₃, h₄⟩ => ⟨τ, M, a, b, c, h₁, h₂, h₃.push H rfl hg, h₄⟩⟩
  · rw [nrm_iff, nrm_iff]
    exact ⟨fun ⟨h, M, c, h₁, h₂⟩ => ⟨hg.trans h, M, c, h₁, h₂.push H' _ h⟩,
      fun ⟨h, M, c, h₁, h₂⟩ => ⟨hg.symm.trans h, M, c, h₁, h₂.push H _ h⟩⟩

end GlobalTheory.KeyIsoNormal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.NormalFormsEqOfKeyDataIsoComplexStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyKa
open GlobalTheory.KeyEq
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalForms_eq_of_keyDataIso_complex : ∀ x x' : KeyIn ℂ, KeyPB x' x (RingHom.id ℂ) → (∀ t, Val x t ↔ Val x' t) ∧ ∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ), Nrm x τ a b ↔ Nrm x' τ a b := by
  first | exact @GlobalTheory.KeyIsoNormal.val_iff_and_nrm_iff | exact GlobalTheory.KeyIsoNormal.val_iff_and_nrm_iff | (intros; apply GlobalTheory.KeyIsoNormal.val_iff_and_nrm_iff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.FamUnit
section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsValueOfGeneric
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.KeyCl GlobalTheory.KeyPow GlobalTheory.KeySmoothBase

noncomputable section
namespace GlobalTheory.KeySpec

theorem valueAt_of_point {κ : Rule} (hF : Funct κ) {S k : Type} [CommRing S] [Field k] [CharZero k] {y : KeyIn S} {u : S}
    (r : S →+* k) {xk : KeyIn k} (hk : KeyPB xk y r) (h : (κ k xk : k) = r u) : ValueAt κ y u (RingHom.ker r) := by
  intro K _ _ f x hf hx
  haveI := RingHom.ker_isPrime r
  haveI : CharZero (S ⧸ RingHom.ker r) := (RingHom.kerLift r).charZero
  obtain ⟨y', hy⟩ := exists_keyPB_ring y (Ideal.Quotient.mk (RingHom.ker r))
  let F := FractionRing (S ⧸ RingHom.ker r)
  obtain ⟨xF, hxF⟩ := exists_keyPB_ring y' (algebraMap _ F)
  have hr := RingHom.kerLift_injective r
  have er : (RingHom.kerLift r).comp (Ideal.Quotient.mk (RingHom.ker r)) = r :=
    RingHom.ext fun a => RingHom.kerLift_mk r a
  have e : (IsFractionRing.lift (K := F) hr).comp (algebraMap _ F) = RingHom.kerLift r :=
    RingHom.ext fun a => IsFractionRing.lift_algebraMap hr a
  have h1 := hF F k (IsFractionRing.lift hr) xF xk
    (GlobalTheory.KeyCancel.keyPB_cancel _ _ _ y' xF xk _ _ hxF
      (e.symm ▸ GlobalTheory.KeyCancel.keyPB_cancel _ _ _ y y' xk _ _ hy (er.symm ▸ hk)))
  have h2 : (κ F xF : F) = algebraMap _ F (Ideal.Quotient.mk (RingHom.ker r) u) := by
    apply (IsFractionRing.lift (K := F) hr).injective
    rw [← h1, h, IsFractionRing.lift_algebraMap, RingHom.kerLift_mk]
  have hz : ∀ a ∈ RingHom.ker r, f a = 0 := fun a ha => (show a ∈ RingHom.ker f from hf ▸ ha)
  let g := Ideal.Quotient.lift (RingHom.ker r) f hz
  have eg : g.comp (Ideal.Quotient.mk _) = f := RingHom.ext fun a => Ideal.Quotient.lift_mk (RingHom.ker r) f hz
  have hg : RingHom.ker g = ⊥ := by
    refine le_antisymm (fun a ha => ?_) bot_le
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    have : a ∈ RingHom.ker f := ha
    exact Ideal.Quotient.eq_zero_iff_mem.2 (hf ▸ this)
  exact valueAt_bot hF hxF h2 K g x hg (GlobalTheory.KeyCancel.keyPB_cancel _ _ _ y y' x _ _ hy (eg.symm ▸ hx))

theorem isValue_of_generic : ∀ κ : Rule, Funct κ → UnitSp κ → ∀ (S : Type) [CommRing S] [IsDomain S] [IsNoetherianRing S] [CharZero S] (y : KeyIn S) (u : S), (∀ (K : Type) [Field K] [CharZero K] (f : S →+* K) (x : KeyIn K), Function.Injective f → KeyPB x y f → (κ K x : K) = f u) → IsValue κ y u := by
  intro κ hF hU S _ _ _ _ y u h K _ _ f x hx
  have h0 : ValueAt κ y u ⊥ := fun K _ _ f x hf hx => h K f x ((RingHom.injective_iff_ker_eq_bot f).2 hf) hx
  by_cases hp : RingHom.ker f = ⊥
  · exact h0 K f x hp hx
  haveI := RingHom.ker_isPrime f
  obtain ⟨O, _, _, _, _, φ, hφ, hm⟩ :=
    GlobalTheory.exists_complete_discreteValuationRing_of_prime_lt (⊥ : Ideal S) (RingHom.ker f) (bot_lt_iff_ne_bot.2 hp)
  haveI : CharZero O := charZero_of_injective_ringHom ((RingHom.injective_iff_ker_eq_bot φ).2 hφ)
  obtain ⟨yO, hy⟩ := exists_keyPB_ring y φ
  obtain ⟨u', hu'⟩ := exists_unit_dvr hF hU O yO
  have e : φ u = u' := (h0.map_bot φ hφ hy).unique (hu' ⊥)
  have hk : RingHom.ker ((IsLocalRing.residue O).comp φ) = RingHom.ker f := by
    rw [← RingHom.comap_ker, IsLocalRing.ker_residue, hm]
  haveI : CharZero (IsLocalRing.ResidueField O) := charZero_of_inj_zero fun n hn => by
    have : (n : S) ∈ RingHom.ker ((IsLocalRing.residue O).comp φ) := by
      rw [RingHom.mem_ker, map_natCast, hn]
    rw [hk, RingHom.mem_ker, map_natCast] at this
    exact_mod_cast this
  obtain ⟨xk, hxk⟩ := exists_keyPB_ring yO (IsLocalRing.residue O)
  refine valueAt_of_point hF ((IsLocalRing.residue O).comp φ) (GlobalTheory.keyPB_trans _ _ _ y yO xk _ _ hy hxk) ?_ K f x hk.symm hx
  rw [hu' _ _ _ xk rfl hxk, RingHom.comp_apply, e]

end GlobalTheory.KeySpec
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.KeyCl

namespace GlobalTheory.KeyFamUnit

theorem famUnit : ∀ κ : Rule, Funct κ → UnitSp κ → FamUnit κ := by
  intro κ hF hU S _ _ _ _ _ y
  obtain ⟨u, hu⟩ := GlobalTheory.KeySmoothBase.exists_unit_normal (κ := κ) hF hU S y
  exact ⟨u, GlobalTheory.KeySpec.isValue_of_generic κ hF hU S y u fun K _ _ f x hf hx =>
    hu K f x ((RingHom.injective_iff_ker_eq_bot f).1 hf) hx⟩

end GlobalTheory.KeyFamUnit
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsProjOverDescendsToSubring
section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsProjOverDescendsToSubring
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa

namespace GlobalTheory

theorem locallyOfFinitePresentation_pspace_str (R : Type) [CommRing R] (N : ℕ) :
    LocallyOfFinitePresentation (PSpace.str R N) := by
  have hloc : IsZariskiLocalAtSource @LocallyOfFinitePresentation :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @LocallyOfFinitePresentation)
  refine IsZariskiLocalAtSource.of_openCover (ProjSpace.chartCover R N) fun (i : Fin (N + 1)) => ?_
  change LocallyOfFinitePresentation (ProjSpace.chartι R N i ≫ PSpace.str R N)
  rw [ProjSpace.chartι_str]
  change LocallyOfFinitePresentation
    (Spec.map (CommRingCat.ofHom (MvPolynomial.C : R →+* MvPolynomial {j // j ≠ i} R)))
  rw [LocallyOfFinitePresentation.SpecMap_iff, CommRingCat.hom_ofHom, ← MvPolynomial.algebraMap_eq,
    RingHom.finitePresentation_algebraMap]
  infer_instance

theorem isProjOver_descends_to_subring :
    ∀ (S : Type) [CommRing S] (R₀ : Subring S) (X X₀ : Scheme.{0}) (f : X ⟶ Sp S) (f₀ : X₀ ⟶ Sp R₀) (π : X ⟶ X₀) [QuasiCompact f₀] [QuasiSeparated f₀] [LocallyOfFiniteType f₀], IsPullback π f f₀ (spMap R₀.subtype) → IsProjOver f → ∃ F : Finset S, ∀ (R₁ : Subring S) (h : R₀ ≤ R₁), (F : Set S) ⊆ R₁ → ∀ (X₁ : Scheme.{0}) (f₁ : X₁ ⟶ Sp R₁) (π₁ : X₁ ⟶ X₀), IsPullback π₁ f₁ f₀ (spMap (Subring.inclusion h)) → IsProjOver f₁ := by
  intro S _ R₀ X X₀ f f₀ π _ _ _ hX hP
  classical
  have hsub : ∀ {A B : Subring S} (hAB : A ≤ B), B.subtype.comp (Subring.inclusion hAB) = A.subtype :=
    fun _ => RingHom.ext fun _ => rfl
  have hincl : ∀ {A B C : Subring S} (hAB : A ≤ B) (hBC : B ≤ C) (hAC : A ≤ C),
      (Subring.inclusion hBC).comp (Subring.inclusion hAB) = Subring.inclusion hAC :=
    fun _ _ _ => RingHom.ext fun _ => rfl
  have hsp : ∀ {A B : Subring S} (hAB : A ≤ B),
      spMap B.subtype ≫ spMap (Subring.inclusion hAB) = spMap A.subtype := by
    intro A B hAB
    rw [← spMap_comp, hsub]
  have hsp2 : ∀ {A B C : Subring S} (hAB : A ≤ B) (hBC : B ≤ C) (hAC : A ≤ C),
      spMap (Subring.inclusion hBC) ≫ spMap (Subring.inclusion hAB) = spMap (Subring.inclusion hAC) := by
    intro A B C hAB hBC hAC
    rw [← spMap_comp, hincl]
  obtain ⟨M, i, hci, hif⟩ := hP
  have : LocallyOfFinitePresentation (PSpace.str R₀ M) := locallyOfFinitePresentation_pspace_str R₀ M
  have hφ : (i ≫ ProjSpace.baseChange M R₀.subtype) ≫ PSpace.str R₀ M = π ≫ f₀ := by
    rw [Category.assoc, ProjSpace.baseChange_str, ← Category.assoc, hif, hX.w]
  obtain ⟨F₁, hF₁⟩ := morphism_descends_to_subring S R₀ X X₀ (PSpace R₀ M) f f₀ (PSpace.str R₀ M) π
    (i ≫ ProjSpace.baseChange M R₀.subtype) hX hφ
  set R₀' : Subring S := R₀ ⊔ Subring.closure (F₁ : Set S) with hR₀'
  have h₀ : R₀ ≤ R₀' := le_sup_left
  have hF₁' : (F₁ : Set S) ⊆ R₀' := fun x hx =>
    (le_sup_right : Subring.closure (F₁ : Set S) ≤ R₀') (Subring.subset_closure hx)
  obtain ⟨X₀', π₀', f₀', hX₀'⟩ : ∃ (X₀' : Scheme.{0}) (π₀' : X₀' ⟶ X₀) (f₀' : X₀' ⟶ Sp R₀'),
      IsPullback π₀' f₀' f₀ (spMap (Subring.inclusion h₀)) :=
    ⟨_, _, _, IsPullback.of_hasPullback _ _⟩
  obtain ⟨j, hjπ, hjf⟩ : ∃ j : X ⟶ X₀', j ≫ π₀' = π ∧ j ≫ f₀' = f ≫ spMap R₀'.subtype :=
    ⟨hX₀'.lift π (f ≫ spMap R₀'.subtype) (by rw [Category.assoc, hsp h₀, hX.w]),
      hX₀'.lift_fst _ _ _, hX₀'.lift_snd _ _ _⟩
  obtain ⟨ψ, hjψ, hψq⟩ := hF₁ R₀' h₀ hF₁' X₀' f₀' π₀' j hX₀' hjπ hjf
  have hbc₀ := ProjSpace.isPullback_baseChange M (Subring.inclusion h₀)
  obtain ⟨g₀, hg₀b, hg₀q⟩ : ∃ g₀ : X₀' ⟶ PSpace R₀' M,
      g₀ ≫ ProjSpace.baseChange M (Subring.inclusion h₀) = ψ ∧ g₀ ≫ PSpace.str R₀' M = f₀' :=
    ⟨hbc₀.lift ψ f₀' (by rw [hψq, hX₀'.w]), hbc₀.lift_fst _ _ _, hbc₀.lift_snd _ _ _⟩
  have : IsProper (PSpace.str R₀' M) := isProper_str R₀' M
  have : QuasiCompact f₀' := MorphismProperty.of_isPullback (P := @QuasiCompact) hX₀' inferInstance
  have : QuasiSeparated f₀' := MorphismProperty.of_isPullback (P := @QuasiSeparated) hX₀' inferInstance
  have : LocallyOfFiniteType f₀' :=
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) hX₀' inferInstance
  have : LocallyOfFiniteType (g₀ ≫ PSpace.str R₀' M) := by rw [hg₀q]; infer_instance
  have : QuasiSeparated (g₀ ≫ PSpace.str R₀' M) := by rw [hg₀q]; infer_instance
  have : QuasiCompact (g₀ ≫ PSpace.str R₀' M) := by rw [hg₀q]; infer_instance
  have : LocallyOfFiniteType g₀ := locallyOfFiniteType_of_comp g₀ (PSpace.str R₀' M)
  have : QuasiSeparated g₀ := QuasiSeparated.of_comp g₀ (PSpace.str R₀' M)
  have : QuasiCompact g₀ := QuasiCompact.of_comp g₀ (PSpace.str R₀' M)
  have hY := ProjSpace.isPullback_baseChange M R₀'.subtype
  have hbc : ProjSpace.baseChange M R₀'.subtype ≫ ProjSpace.baseChange M (Subring.inclusion h₀) =
      ProjSpace.baseChange M R₀.subtype := by
    rw [← ProjSpace.baseChange_comp, hsub]
  have hleft : IsPullback j f f₀' (spMap R₀'.subtype) := by
    refine IsPullback.of_right ?_ hjf hX₀'
    rw [hjπ, hsp h₀]
    exact hX
  have hsq : IsPullback j i g₀ (ProjSpace.baseChange M R₀'.subtype) := by
    refine IsPullback.of_bot ?_ ?_ hY
    · rw [hif, hg₀q]
      exact hleft
    · apply hbc₀.hom_ext
      · rw [Category.assoc, hg₀b, hjψ, Category.assoc, hbc]
      · rw [Category.assoc, hg₀q, hjf, Category.assoc, ProjSpace.baseChange_str, ← Category.assoc, hif]
  obtain ⟨F₂, hF₂⟩ := GlobalTheory.T.isClosedImmersion_descends_to_subring' S R₀' X₀' (PSpace R₀' M) X (PSpace S M) g₀ (PSpace.str R₀' M)
    i j (ProjSpace.baseChange M R₀'.subtype) (PSpace.str S M) hY hsq hci
  refine ⟨F₁ ∪ F₂, fun R₁ h hF X₁ f₁ π₁ hX₁ => ?_⟩
  have h' : R₀' ≤ R₁ := sup_le h (Subring.closure_le.2 fun x hx =>
    hF (Finset.mem_coe.2 (Finset.mem_union_left _ (Finset.mem_coe.1 hx))))
  have hF₂' : (F₂ : Set S) ⊆ R₁ := fun x hx =>
    hF (Finset.mem_coe.2 (Finset.mem_union_right _ (Finset.mem_coe.1 hx)))
  obtain ⟨πX₁, hπ₁, hf₁⟩ : ∃ πX₁ : X₁ ⟶ X₀',
      πX₁ ≫ π₀' = π₁ ∧ πX₁ ≫ f₀' = f₁ ≫ spMap (Subring.inclusion h') :=
    ⟨hX₀'.lift π₁ (f₁ ≫ spMap (Subring.inclusion h')) (by rw [Category.assoc, hsp2 h₀ h' h, hX₁.w]),
      hX₀'.lift_fst _ _ _, hX₀'.lift_snd _ _ _⟩
  have hleft₁ : IsPullback πX₁ f₁ f₀' (spMap (Subring.inclusion h')) := by
    refine IsPullback.of_right ?_ hf₁ hX₀'
    rw [hπ₁, hsp2 h₀ h' h]
    exact hX₁
  have hY₁ := ProjSpace.isPullback_baseChange M (Subring.inclusion h')
  obtain ⟨g₁, hg₁b, hg₁q⟩ : ∃ g₁ : X₁ ⟶ PSpace R₁ M,
      g₁ ≫ ProjSpace.baseChange M (Subring.inclusion h') = πX₁ ≫ g₀ ∧ g₁ ≫ PSpace.str R₁ M = f₁ :=
    ⟨hY₁.lift (πX₁ ≫ g₀) f₁ (by rw [Category.assoc, hg₀q, hf₁]), hY₁.lift_fst _ _ _,
      hY₁.lift_snd _ _ _⟩
  have hsq₁ : IsPullback πX₁ g₁ g₀ (ProjSpace.baseChange M (Subring.inclusion h')) := by
    refine IsPullback.of_bot ?_ hg₁b.symm hY₁
    rw [hg₁q, hg₀q]
    exact hleft₁
  have := hF₂ R₁ h' hF₂' X₁ (PSpace R₁ M) g₁ πX₁ (ProjSpace.baseChange M (Subring.inclusion h'))
    (PSpace.str R₁ M) hY₁ hsq₁
  rw [← hg₁q]
  exact ProjSpace.isProjOver_comp_of_isClosedImmersion g₁ (ProjSpace.isProjOver_pspace_str R₁ M)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsProjOverDescendsToSubringStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isProjOver_descends_to_subring' : ∀ (S : Type) [CommRing S] (R₀ : Subring S) (X X₀ : Scheme.{0}) (f : X ⟶ Sp S) (f₀ : X₀ ⟶ Sp R₀) (π : X ⟶ X₀) [QuasiCompact f₀] [QuasiSeparated f₀] [LocallyOfFiniteType f₀], IsPullback π f f₀ (spMap R₀.subtype) → IsProjOver f → ∃ F : Finset S, ∀ (R₁ : Subring S) (h : R₀ ≤ R₁), (F : Set S) ⊆ R₁ → ∀ (X₁ : Scheme.{0}) (f₁ : X₁ ⟶ Sp R₁) (π₁ : X₁ ⟶ X₀), IsPullback π₁ f₁ f₀ (spMap (Subring.inclusion h)) → IsProjOver f₁ := by
  first | exact @GlobalTheory.isProjOver_descends_to_subring | exact GlobalTheory.isProjOver_descends_to_subring | (intros; apply GlobalTheory.isProjOver_descends_to_subring <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.FamHomogOfHomog
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.KeyFamHomog

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.KeyCl

theorem famHomog_of_homog : ∀ (N : ℕ → ℕ) (κ : Rule), Homog N κ → FamHomog N κ := by
  intro N κ hH S _ _ _ P hg rig hr th hth v hv th' hth' v' hv' a M u u' ha hM hu hu'
  obtain ⟨Q, hg₁, rig₁, hr₁, th₁, hth₁, v₁, hv₁, th₁', hth₁', v₁', hv₁', M₁, h₁, h₂, ha₁, hN, hd⟩ :=
    KeyGalDesc.exists_keyPB_pair (algebraMap S (FractionRing S)) P hg rig hr th hth v hv th' hth' v' hv' a M ha hM
  have e := hH _ Q hg₁ rig₁ hr₁ th₁ hth₁ v₁ hv₁ th₁' hth₁' v₁' hv₁' _ M₁ ha₁ hN
  have hgQ : Q.g = P.g := KeyGalDesc.g_eq h₁
  rw [hu _ _ _ h₁, hu' _ _ _ h₂, hd] at e
  have hn : N Q.g = N P.g := congrArg N hgQ
  rw [hn] at e
  apply IsFractionRing.injective S (FractionRing S)
  simpa only [map_mul, map_pow] using e

end GlobalTheory.KeyFamHomog
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KeyFormulaPowOfKeyRuleCharZero
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.KeyPow

theorem keyFormulaPow_of_keyRule :
    ThetaUnifAV → ∀ N : ℕ → ℕ, (∀ g, 1 ≤ N g) → GlobalTheory.KeyPow.KeyRule N 1 GlobalTheory.KeyPow.charHalf → GlobalTheory.KeyFormulaPow := by
  rintro hT N hN ⟨κ, hH, hF, hU, hK⟩
  refine ⟨N, hN, κ, fun K _ _ P hg rig hr th hth v hv th' hth' v' hv' a M =>
      hH K P hg rig hr th hth v hv th' hth' v' hv' a M hg,
    fun K K' _ _ _ _ f x x' => hF K K' f x x' x.g_pos,
    fun R K _ _ _ _ _ _ _ x xK => hU R K x xK x.g_pos,
    fun x u τ a b h₁ h₂ ha hb h₃ h₄ h₅ h₆ =>
      hK x τ a b x.g_pos ⟨ha, hb⟩ ((normalAt_one_iff x τ a b).2 ⟨u, h₁, h₂, h₃, h₄, h₅, h₆⟩), ?_⟩
  intro x u Hm W χ θ Fd nth nη h₁ h₂ h₃ h₄ h₅ h₆ h₇
  obtain ⟨u', τ, M, a, b, c, k₁, k₂, ha, hb, k₃, k₄, hc, k₅, hM, k₆, hn⟩ :=
    keyIn_normal_form_and_archimedean_constant hT x u Hm W χ θ Fd nth nη h₁ h₂ h₃ h₄ h₅ h₆ h₇
  have hv := value_at_normalForm N 1 (κ ℂ) x.P.g a b x.g_pos (hH ℂ)
    (fun y h τ' hy => hK y τ' _ _ y.g_pos ⟨fun i => ha _, fun i => hb _⟩ hy) x rfl τ M c hc hM
    ⟨u', k₁, k₂, k₃, k₄, k₅, k₆⟩
  rw [hv, norm_pow, pow_mul nth, pow_mul nη, ← mul_pow, ← mul_pow, hn, ← pow_mul]

end GlobalTheory.KeyPow
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.NormalAtScale
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyKa
open GlobalTheory.KeyEq

noncomputable section
namespace GlobalTheory.KeyEq

theorem normalAt_scale :
    ∀ (P : Out.PolAV (Sp ℂ)) (hg rig hr th hth v hv th' hth' v' hv') (a : ℂ) (N : Matrix (Fin P.g) (Fin P.g) ℂ), (∀ i, LB.Sec.f th' i = constFn P.A.hom _ a * LB.Sec.f th i) → (∀ i, IsLieComb (N i) v (v' i)) → a ≠ 0 ∧ N.det ≠ 0 ∧ ∀ (τ M : Matrix (Fin P.g) (Fin P.g) ℂ) (α β : Fin P.g → ℂ) (c : ℂ), NormalAt ⟨P, hg, rig, hr, th, hth, v, hv⟩ τ M α β c → NormalAt ⟨P, hg, rig, hr, th', hth', v', hv'⟩ τ (N * M) α β (a * c) := by
  intro P hg rig hr th hth v hv th' hth' v' hv' a N ha hN
  haveI := P.isAb.comm
  obtain ⟨-, -, -, -, bas⟩ := GlobalTheory.LieComb.lieComb_algebra ℂ P.A P.g v hv.1
  refine ⟨?_, ((bas N v' hv hN).1 hv').ne_zero, ?_⟩
  · rintro rfl
    obtain ⟨y, -, hy⟩ := hth' (IsLocalRing.closedPoint ℂ)
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
    rw [ha i, constFn, map_zero, map_zero, zero_mul, Scheme.basicOpen_zero] at hi
    exact hi
  · rintro τ M α β c ⟨u, h₁, h₂, h₃, h₄, h₅, h₆⟩
    refine ⟨u, h₁, h₂, h₃, h₄, ?_, ?_⟩
    · intro i z hz
      have e := h₅ i z hz
      refine ((congrArg (valAt' _ _) (ha i)).trans (valAt'_mul _ _ _ _)).trans ?_
      rw [valAt'_constFn _ _ (Over.w (u.ex z)) _ _ hz]
      refine (congrArg (a * ·) e).trans ?_
      beta_reduce
      simp only [_root_.mul_assoc]
    · intro i
      have h1 := GlobalTheory.UnifDifferential.isDiff_of_isLieComb P.A P.L P.g P.g u _ v _ _ hv.1 h₆ (hN i)
      have e : ∑ j, N i j • ((2 * Real.pi * Complex.I : ℂ)⁻¹ • M j) =
          (2 * Real.pi * Complex.I : ℂ)⁻¹ • (N * M) i := by
        simp only [smul_comm (N i _) (2 * Real.pi * Complex.I : ℂ)⁻¹]
        rw [← Finset.smul_sum, ← Matrix.vecMul_eq_sum]
        rfl
      rwa [e] at h1

end GlobalTheory.KeyEq
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.DetNeZeroOfNormalAt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyKa
open GlobalTheory.KeyEq

noncomputable section
namespace GlobalTheory.KeyEq

theorem det_ne_zero_of_normalAt (hU : ThetaUnifAV) (x : KeyIn ℂ) {τ M : Matrix (Fin x.P.g) (Fin x.P.g) ℂ}
    {a b : Fin x.P.g → ℂ} {c : ℂ} (h : NormalAt x τ M a b c) : M.det ≠ 0 := by
  obtain ⟨u, -, -, -, -, -, h₆⟩ := h
  obtain ⟨u₀, -, -, -, -, -, -, hd, -⟩ := hU x.P x.rig x.rig_gen
  have := x.P.isAb.comm
  obtain ⟨hex, htan, -⟩ := LieComb.lieComb_algebra ℂ x.P.A x.P.g x.v x.basis.1
  intro h0
  obtain ⟨d, hd0, hdM⟩ := Matrix.exists_vecMul_eq_zero_iff.2 h0
  have key : ∀ (e : Fin x.P.g → ℂ) (w), Matrix.vecMul e M = 0 → IsLieComb e x.v w → u₀.IsDiff 0 w := by
    intro e w he hw
    have h1 := UnifDifferential.isDiff_of_isLieComb _ _ _ _ u _ x.v e w x.basis.1 h₆ hw
    have e1 : ∑ j, e j • (2 * Real.pi * Complex.I : ℂ)⁻¹ • M j =
        (2 * Real.pi * Complex.I : ℂ)⁻¹ • Matrix.vecMul e M := by
      rw [Matrix.vecMul_eq_sum, Finset.smul_sum]
      exact Finset.sum_congr rfl fun j _ => smul_comm _ _ _
    rw [e1, he, smul_zero] at h1
    intro U hU' f
    rw [h1 U hU' f, map_zero, map_zero]
  obtain ⟨w, hw⟩ := (hex d).exists
  obtain ⟨w', hw'⟩ := (hex 0).exists
  have hww : w = w' := (hd 0).unique ⟨htan _ _ hw, key _ _ hdM hw⟩
    ⟨htan _ _ hw', key _ _ (Matrix.zero_vecMul M) hw'⟩
  subst hww
  exact hd0 ((x.basis.2 w (htan _ _ hw)).unique hw hw')

end GlobalTheory.KeyEq
end
end
