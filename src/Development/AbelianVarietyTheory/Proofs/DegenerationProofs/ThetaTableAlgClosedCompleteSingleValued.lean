module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ReframeSt
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.WithISelf
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.MemNonzeroLocusOfUnit
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SectionFramesMoveToCoverAndRingExtension
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGenOfFrames

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaTableAlgClosedCompleteSingleValued
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaTableAlgClosedCompleteSingleValued
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis

noncomputable section

namespace GlobalTheory.OneBasis

variable {R : Type} [CommRing R] [IsDomain R] (A : PolAV (Sp (FractionRing R))) (F : Type) [Field F]
  [Algebra (FractionRing R) F]

theorem exists_isTorsFrame_closed [CharZero R] [IsAlgClosed F] (hLaw : Laws) {ρ : LB.Gen (A.L.pull (eSec A.A))}
    (hρ : ρ.IsGen) {n : ℕ} (hn : Odd n) (x : TFK (R := R) F ⟶ A.A) (hx : x ^ n = 1) :
    ∃ e, IsTorsFrame A ρ n x e := by
  let T := TFK (R := R) F
  have : Subsingleton T.left := inferInstanceAs (Subsingleton (PrimeSpectrum F))
  obtain ⟨p⟩ : Nonempty T.left := inferInstanceAs (Nonempty (PrimeSpectrum F))
  have hu : IsUnit ((n ^ 2 : ℕ) : Γ(Spec (CommRingCat.of (FractionRing R)), ⊤)) := by
    let e := (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).commRingCatIsoToRingEquiv.symm
    rw [← map_natCast e]
    refine (IsUnit.mk0 _ ?_).map e
    rw [← map_natCast (algebraMap R (FractionRing R))]
    exact (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2
      (Nat.cast_ne_zero.2 (pow_ne_zero 2 hn.pos.ne'))
  obtain ⟨y, hy⟩ : ∃ y : T ⟶ A.A, y ^ n = x :=
    TorusExt.exists_pow_eq_of_noetherian (S := Sp (FractionRing R)) (k := F) T.hom hLaw.mulN A hn.pos.ne' x
  have hy' : y ^ (n ^ 2) = 1 := by rw [sq, pow_mul, hy, hx]
  obtain ⟨hex, -⟩ := hLaw.symLift _ A (n ^ 2) hn.pow hu T y hy'
  obtain ⟨V, hV, θ₀, hθ₀⟩ := hex p
  obtain ⟨h, hh⟩ := GlobalLift.exists_section (T := T) hV
  obtain ⟨θ, hθ⟩ := GlobalLift.exists_symLift_pull A.isLB h hθ₀
  rw [← Category.assoc, hh, Category.id_comp] at hθ
  exact exists_isTorsFrame_of_symLift hLaw _ A ρ hρ n hn T y x hy' hy θ hθ


omit [IsDomain R] in
theorem exists_valAt (hLaw : Laws) {k : ℕ} (t : SecA A F k) (x : TFK (R := R) F ⟶ A.A) {e} (he : LB.Gen.IsGen e) :
    ∃ c, ValAt t x e c := by
  obtain ⟨v, hv, -⟩ := hLaw.evVal _ A k x e he t
  obtain ⟨c, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of F)).inv).2 v
  refine ⟨c, fun z J hJ => ?_⟩
  have := FrameMove.sval_valueAt hv (𝟙 _) hJ
  rw [Category.id_comp] at this
  exact this

end GlobalTheory.OneBasis

namespace GlobalTheory

theorem tab_full_uniq : LL → ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (A : PolAV (Sp (FractionRing R))) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (ρ : LB.Gen (A.L.pull (eSec A.A))), ρ.IsGen → ∀ (m n r : ℕ), Odd m → Odd n → ∀ (th : SecA A F 1) (τ : Fin r → SecA A F (m ^ 2)), (∀ t, ∃! a, Cmb τ a t) → (tab ρ m th τ).Full (m ^ 2) n ∧ (tab ρ m th τ).Uniq (m ^ 2) n := by
  intro hLL R _ _ _ A F _ _ _ ρ hρ m n r hm hn th τ hτ
  have H := existsUnique_thetaConst hLL R A F ρ hρ
  refine ⟨⟨fun x hx => ?_, fun j x hx => ?_, fun j x hx => ?_⟩, fun x a ha => ?_, fun j x c hc => ?_⟩
  · obtain ⟨q, hq, -⟩ := H m hm th x hx
    obtain ⟨a, ha, -⟩ := hτ q.1
    exact ⟨a, hx, q.1, q.2, hq, ha⟩
  · obtain ⟨q, hq, -⟩ := H (n ^ j) hn.pow th x hx
    exact ⟨q.2, hx, q.1, hq⟩
  · obtain ⟨e, he⟩ := exists_isTorsFrame_closed A F hLL.1 hρ (hn.pow (n := j)) x hx
    choose l hl using fun i => exists_valAt A F hLL.1 (τ i) x he.2.1
    exact ⟨l, e, he, hl⟩
  · obtain ⟨hx, t, c, ht, ha⟩ := ha
    refine ⟨hx, ?_⟩
    rintro a' ⟨-, t', c', ht', ha'⟩
    have e : t' = t := congrArg Prod.fst ((H m hm th x hx).unique (y₁ := (t', c')) (y₂ := (t, c)) ht' ht)
    subst e
    exact (hτ t').unique ha' ha
  · obtain ⟨hx, t, ht⟩ := hc
    refine ⟨hx, ?_⟩
    rintro c' ⟨-, t', ht'⟩
    exact congrArg Prod.snd ((H (n ^ j) hn.pow th x hx).unique (y₁ := (t', c')) (y₂ := (t, c)) ht' ht)

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaTableAlgClosedCompleteSingleValuedStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaTable_algClosed_complete_singleValued : LL → ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (A : PolAV (Sp (FractionRing R))) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (ρ : LB.Gen (A.L.pull (eSec A.A))), ρ.IsGen → ∀ (m n r : ℕ), Odd m → Odd n → ∀ (th : SecA A F 1) (τ : Fin r → SecA A F (m ^ 2)), (∀ t, ∃! a, Cmb τ a t) → (tab ρ m th τ).Full (m ^ 2) n ∧ (tab ρ m th τ).Uniq (m ^ 2) n := by
  first | exact @GlobalTheory.tab_full_uniq | exact GlobalTheory.tab_full_uniq | (intros; apply GlobalTheory.tab_full_uniq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PolarisationGeneratingSectionPullbackLocalBase
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PolarisationGeneratingSectionPullbackLocalBase
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
open GlobalTheory.ModelData

namespace GlobalTheory.GeneratorPull

theorem exists_down {X : Scheme.{0}} {L : LB X} (s : H0 L 1) : ∃ t : L.Sec, ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z)
    (J : (Z ⟶ X) → L.ι), Good L z J → sval s r z J = gs r z (L.U (J r)) (t.f (J r)) := by
  have exists_pw_local : ∃ b : LB.Sec (AbLaw.pw L ((1 : ℕ) : ℤ)),
      ∀ (Z : Scheme.{0}) (q : Z ⟶ X) (z : Z) (j : L.ι), q z ∈ L.U j →
        gs q z (LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => j)) (s.f fun _ => j) = gs q z (L.U j) (b.f j) := by
    have le : ∀ j, L.U j ≤ LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => j) := fun j y hy => Set.mem_iInter.2 fun _ => hy
    refine ⟨⟨fun j => resG _ (le j) (s.f fun _ => j), fun j i => fn_ext fun y hy => ?_⟩,
      fun Z q z j hj => (gs_res q z (le j) hj _).symm⟩
    refine ((gs_res (𝟙 _) y _ hy _).trans (gs_res (𝟙 _) y (le j) hy.1 _)).trans
      ((sec_trans s (𝟙 _) y (le j hy.1) (le i hy.2)).trans (Eq.trans ?_ (gs_mul (𝟙 _) y _ hy _ _).symm))
    refine congrArg₂ (· * ·) ?_ ((gs_res (𝟙 _) y _ hy _).trans (gs_res (𝟙 _) y (le i) hy.2 _)).symm
    refine Eq.trans ?_ ((gs_unit (𝟙 _) y _ hy _).trans (congrArg Units.val (map_zpow _ _ _))).symm
    refine congrArg Units.val ((Fin.prod_univ_one _).trans ?_)
    rw [Category.comp_id]
    rfl
  obtain ⟨b, hb⟩ := exists_pw_local
  exact ⟨KeyOnPol.ofPow b, fun Z r z J hJ =>
    (sval_of s r z J (fun _ => J r) fun _ => by rw [Category.comp_id]).trans (hb Z r z _ (hJ r))⟩

theorem exists_up {X : Scheme.{0}} {L : LB X} (t : L.Sec) : ∃ s : H0 L 1, ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z)
    (J : (Z ⟶ X) → L.ι), Good L z J → sval s r z J = gs r z (L.U (J r)) (t.f (J r)) := by
  have exists_up_local : ∃ s : H0 L 1,
      ∀ (Z : Scheme.{0}) (q : Z ⟶ X) (z : Z) (j : L.ι), q z ∈ L.U j →
        gs q z (LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => j)) (s.f fun _ => j) = gs q z (L.U j) (t.f j) := by
    have le : ∀ j : Fin 1 → L.ι, LB.wchart L (fun _ : Fin 1 => 𝟙 X) j ≤ L.U (j 0) := fun j y hy => Set.mem_iInter.1 hy 0
    refine ⟨⟨fun j => resG X (le j) (t.f (j 0)), fun j i => fn_ext fun y hy => ?_⟩,
      fun Z q z j hj => gs_res q z (le _) (Set.mem_iInter.2 fun _ => hj) _⟩
    refine ((gs_res (𝟙 X) y _ hy _).trans (gs_res (𝟙 X) y (le j) hy.1 _)).trans (Eq.trans ?_ ((gs_mul (𝟙 X) y _ hy _ _).trans
      (congrArg₂ (· * ·) ((gs_unit (𝟙 X) y _ hy _).trans (congrArg Units.val (gm_linComb L _ _ (𝟙 X) y j i hy.1 hy.2)))
        ((gs_res (𝟙 X) y _ hy _).trans (gs_res (𝟙 X) y (le i) hy.2 _)))).symm)
    have hm : (𝟙 X) y ∈ L.U (j 0) ⊓ L.U (i 0) := ⟨le j hy.1, le i hy.2⟩
    have ht : gs (𝟙 X) y _ (t.f (j 0)) = (gm (𝟙 X) y _ (L.g (j 0) (i 0))).val * gs (𝟙 X) y _ (t.f (i 0)) :=
      (gs_res (𝟙 X) y _ hm _).symm.trans ((congrArg (gs (𝟙 X) y _) (t.compat (j 0) (i 0))).trans
        ((gs_mul (𝟙 X) y _ hm _ _).trans (congrArg₂ (· * ·) (gs_unit (𝟙 X) y _ hm _) (gs_res (𝟙 X) y _ hm _))))
    rw [ht, Fin.prod_univ_one, Nat.cast_one, zpow_one, Category.id_comp]
  obtain ⟨s, hs⟩ := exists_up_local
  exact ⟨s, fun Z r z J hJ =>
    (sval_of s r z J (fun _ => J r) fun _ => by rw [Category.comp_id]).trans (hs Z r z _ (hJ r))⟩

theorem exists_generator_pull : Laws → ∀ (R R' : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [CommRing R'] (f : R →+* R') (P : PolAV (Sp R)) (P' : PolAV (Sp R')) (Φ : P'.A.left ⟶ P.A.left) (w : LB.Iso P'.L (P.L.pull Φ)), IsGrpPullback P'.A P.A (spMap f) Φ → w.IsGen → ∀ th : H0 P.L 1, (∀ s : H0 P.L 1, ∃ r : R, ∀ j, s.f j = resTop _ (scal P.A.hom r) * th.f j) → ∃ th' : H0 P'.L 1, (∀ s : H0 P'.L 1, ∃ r : R', ∀ j, s.f j = resTop _ (scal P'.A.hom r) * th'.f j) ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ P'.A.left) (z : Z) (J : (Z ⟶ P.A.left) → P.L.ι) (J' : (Z ⟶ P'.A.left) → P'.L.ι), Good P.L z J → Good P'.L z J' → sval th (r ≫ Φ) z J = (gw w r z (J (r ≫ Φ)) (J' r)).val * sval th' r z J' := by
  intro hL R R' _ _ _ _ f P P' Φ w hΦ hw th hth
  obtain ⟨b, hb, -⟩ := KeyOnPol.exists_generator hL.secBaseChange P
  obtain ⟨t, ht⟩ := exists_down th
  obtain ⟨β, hβ⟩ := exists_up b
  obtain ⟨a, ha⟩ := hth β
  have nz : ∀ y : Sp R, ∃ x : P.A.left, P.A.hom x = y ∧ x ∈ nonzeroLocus t := fun y => by
    obtain ⟨x, hx, hn⟩ := hb y
    obtain ⟨k, hk, u⟩ := (mem_nonzeroLocus _ _).1 hn
    obtain ⟨J, hJ, e⟩ := exists_good P.L P.isLB x (fun _ : PUnit => 𝟙 P.A.left) (fun _ => k) (fun _ _ _ => rfl)
      fun _ => hk
    obtain rfl : J (𝟙 _) = k := e PUnit.unit
    have h := IndivisibleSection.sval_of_secIsMul (p := P.A.hom) (a := a) (s := β) (t := th) ha (𝟙 _) x hJ
    rw [hβ _ _ x J hJ, ht _ _ x J hJ] at h
    exact ⟨x, hx, (mem_nonzeroLocus _ _).2 ⟨_, hk, isUnit_of_mul_isUnit_right (h ▸ u)⟩⟩
  obtain ⟨t', ht'⟩ := sec_pull_down ((isGen_iff w).1 hw) P.isLB P'.isLB t
  have nz' := SectionBaseChange.fibre_nonzero_of_pull P'.isLB ht' hΦ.1 nz
  obtain ⟨th', hth'⟩ := exists_up t'
  refine ⟨th', fun s => ?_, fun Z r z J J' hJ hJ' => ?_⟩
  · obtain ⟨σ, hσ⟩ := exists_down s
    obtain ⟨c, hc, -⟩ := SectionBaseChange.generates hL.secBaseChange P hΦ.1 P'.isLB ⟨w, hw⟩ t' nz' σ
    refine ⟨c, IndivisibleSection.secIsMul_of_sval P'.isLB fun y J hJ => ?_⟩
    rw [hσ _ _ y J hJ, hth' _ _ y J hJ]
    exact (sec_eq_iff _ _ _ _).1 hc _ y (hJ (𝟙 _))
  · rw [ht _ _ z J hJ, hth' _ _ z J' hJ']
    exact ht' Z r z _ _ (hJ (r ≫ Φ)) (hJ' r)

end GlobalTheory.GeneratorPull
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PolarisationGeneratingSectionPullbackLocalBaseStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
open GlobalTheory.ModelData
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarisation_generating_section_pullback_local_base : Laws → ∀ (R R' : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [CommRing R'] (f : R →+* R') (P : PolAV (Sp R)) (P' : PolAV (Sp R')) (Φ : P'.A.left ⟶ P.A.left) (w : LB.Iso P'.L (P.L.pull Φ)), IsGrpPullback P'.A P.A (spMap f) Φ → w.IsGen → ∀ th : H0 P.L 1, (∀ s : H0 P.L 1, ∃ r : R, ∀ j, s.f j = resTop _ (scal P.A.hom r) * th.f j) → ∃ th' : H0 P'.L 1, (∀ s : H0 P'.L 1, ∃ r : R', ∀ j, s.f j = resTop _ (scal P'.A.hom r) * th'.f j) ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ P'.A.left) (z : Z) (J : (Z ⟶ P.A.left) → P.L.ι) (J' : (Z ⟶ P'.A.left) → P'.L.ι), Good P.L z J → Good P'.L z J' → sval th (r ≫ Φ) z J = (gw w r z (J (r ≫ Φ)) (J' r)).val * sval th' r z J' := by
  first | exact @GlobalTheory.GeneratorPull.exists_generator_pull | exact GlobalTheory.GeneratorPull.exists_generator_pull | (intros; apply GlobalTheory.GeneratorPull.exists_generator_pull <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsRigidifiedPolarisedFibreAtFieldPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsRigidifiedPolarisedFibreAtFieldPoint
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis

theorem GlobalTheory.OneBasis.exists_rigPull_of_polAt : Laws → Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Z : Scheme.{0}) (t : SAB H Z) (K : Type) [Field K] (x : Sp K ⟶ Z), PolAt t x → ∃ (A : PolAV (Sp K)) (φ : A.A.left ⟶ t.G.left) (w : LB.Iso A.L (t.PP.L.pull φ)) (ρ : LB.Gen (A.L.pull (eSec A.A))), RigPull A.A t.G x φ w ρ t.PP.rig := by
  intro _ _ E _ _ _ H Z t K _ x ⟨hp, hA, hK⟩
  have hsemi : IsSemiAbelian ((Over.pullback x).obj t.G) := by
    refine { comm := ?_, smooth := ?_, separated := ?_, quasiCompact := ?_, geomConnected := ?_, fibres := ?_ }
    · have := t.semi.comm
      infer_instance
    · have := t.semi.smooth
      change Smooth (pullback.snd t.G.hom x)
      infer_instance
    · have := t.semi.separated
      change IsSeparated (pullback.snd t.G.hom x)
      infer_instance
    · have := t.semi.quasiCompact
      change QuasiCompact (pullback.snd t.G.hom x)
      infer_instance
    · have := t.semi.geomConnected
      change GeometricallyConnected (pullback.snd t.G.hom x)
      infer_instance
    · intro Ω _ _ q
      obtain ⟨A⟩ := t.semi.fibres Ω (q ≫ x)
      exact ⟨torusExtOfIso (pullCompIso q x t.G) A⟩
  have hpull : ∃ (PP' : RigLB ((Over.pullback x).obj t.G)) (cub : CubicalStr _ PP') (sym : PP'.IsSymmetric) (adj : _) (prim : _)
      (m : SABMap ⟨(Over.pullback x).obj t.G, hsemi,
        Geo.Tor.OAct.pullback x t.G t.act, PP', cub, sym, adj, prim⟩ t x),
      m.φ = pullback.fst t.G.hom x := by
    have h := isGrpPullback_pullback t.G x
    obtain ⟨hL, hr, ⟨c', hc'⟩, hs⟩ := CubePf.cubePull _ _ t.G _ (cubeMapOf h) t.PP t.cub
    have hact : ∀ a, ((Geo.Tor.OAct.pullback x t.G t.act).act a).left ≫ pullback.fst t.G.hom x =
        pullback.fst t.G.hom x ≫ (t.act.act a).left := fun a => pullback.lift_fst _ _ _
    have pa : ∀ {T : Over _} (y : T ⟶ (Over.pullback x).obj t.G) a,
        pushPt h.1.w (y ≫ (Geo.Tor.OAct.pullback x t.G t.act).act a) = pushPt h.1.w y ≫ t.act.act a := fun y a =>
      Over.OverMorphism.ext (by
        show (y.left ≫ _) ≫ _ = (y.left ≫ _) ≫ _
        rw [Category.assoc, hact, Category.assoc])
    refine ⟨(cubeMapOf h).rigLB t.PP hL hr, c', hs t.sym, fun a => ?_, ?_, ⟨cubeMapOf h, h, rfl, hact, hc'⟩, rfl⟩
    · let U := lift (pushPt h.1.w (fst ((Over.pullback x).obj t.G) ((Over.pullback x).obj t.G)))
        (pushPt h.1.w (snd ((Over.pullback x).obj t.G) ((Over.pullback x).obj t.G)))
      refine LBIso.chartPull (chartPullLinComb t.PP.L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down)
        (chartPullLinComb t.PP.L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down) (t.adj a)
      · fin_cases i
        · exact (pa _ a).trans (by simp [U])
        · simp [U]
      · fin_cases i
        · simp [U]
        · exact (pa _ _).trans (by simp [U])
    · let U := pushPt h.1.w (𝟙 ((Over.pullback x).obj t.G))
      refine LBIso.chartPull (chartPullPull t.PP.L _)
        (chartPullLinComb t.PP.L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down) t.prim
      fin_cases i
      · simp [U]
      · exact (congrArg (pushPt h.1.w) (Category.id_comp _).symm).trans (pa _ _)
  obtain ⟨PP', cub, sym, adj, prim, m₁, hm₁⟩ := hpull
  let t' : SAB H (Spec (CommRingCat.of K)) :=
    ⟨(Over.pullback x).obj t.G, hsemi,
      Geo.Tor.OAct.pullback _ t.G t.act, PP', cub, sym, adj, prim⟩
  let m₀ : SABMap t' t x := m₁
  have hm₀ : m₀.cm.F = pullback.fst t.G.hom x := hm₁
  obtain ⟨w, hw, hr, -⟩ := m₀.lin
  have hL : LBIso t'.PP.L (t.PP.L.pull (pullback.fst t.G.hom x)) := hm₀ ▸ ⟨w, hw⟩
  have hM := LB.isLB_pull t.PP.isLB (pullback.fst t.G.hom x)
  have hL' : LBIso t'.PP.L ((t.PP.L.pull (pullback.fst t.G.hom x)).pull (𝟙 t'.G.left)) :=
    LBIso.chartPull (Geo.Tor.chartPullId _) (Geo.Tor.chartPullPull _ (𝟙 _) (𝟙 _) rfl) hL
  obtain ⟨v, hv⟩ := hL'
  have : IsMonHom (Iso.refl t'.G).hom := inferInstanceAs (IsMonHom (𝟙 t'.G))
  have hid : IsGrpPullback t'.G t'.G (𝟙 _) (𝟙 t'.G.left) := isGrpPullback_of_iso (Iso.refl t'.G)
  have hA' : RelAmple t'.G t'.PP.L :=
    relAmple_pull hid.1 hM t'.PP.isLB ((isGen_iff v).1 hv) ⊤ (isAffineOpen_top _) (fun _ => trivial) hA
  have hK' : KTriv t'.G t'.PP.L := kTriv_pull hid hM t'.PP.isLB ((isGen_iff v).1 hv) hK
  have := t'.semi.smooth
  have := t'.semi.geomConnected
  have : ConnectedSpace ↥t'.G.left :=
    GeometricallyConnected.geometrically_connectedSpace (f := t'.G.hom) (𝟙 _) (𝟙 _) t'.G.hom
      (IsPullback.of_horiz_isIso ⟨by simp⟩)
  obtain ⟨g, hg⟩ := exists_dim_of_preconnected t'.G.hom (Classical.arbitrary _)
  have hP : PMaps w (K := PUnit) (fun _ => eSec t'.G) (fun _ => eSec t.G) (fun _ => 1) t'.PP.rig t.PP.rig m₀.cm.e :=
    (maps_iff w _ (fun _ => eSec t.G) _ t'.PP.rig t.PP.rig m₀.cm.e _
      (rigPull_le m₀.cm.F m₀.cm.e m₀.cm.e_comm t.PP.L) (fun _ => rfl)).1 hr
  rw [m₀.base] at hP
  exact ⟨GlobalTheory.GenericPol.toPolAV t' g hg hp hA' hK', m₀.cm.F, w, t'.PP.rig, m₀.cart, hw, t'.PP.rigGen, hP⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsRigidifiedPolarisedFibreAtFieldPointStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rigidified_polarised_fibre_at_field_point : Laws → Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Z : Scheme.{0}) (t : SAB H Z) (K : Type) [Field K] (x : Sp K ⟶ Z), PolAt t x → ∃ (A : PolAV (Sp K)) (φ : A.A.left ⟶ t.G.left) (w : LB.Iso A.L (t.PP.L.pull φ)) (ρ : LB.Gen (A.L.pull (eSec A.A))), RigPull A.A t.G x φ w ρ t.PP.rig := by
  first | exact @GlobalTheory.OneBasis.exists_rigPull_of_polAt | exact GlobalTheory.OneBasis.exists_rigPull_of_polAt | (intros; apply GlobalTheory.OneBasis.exists_rigPull_of_polAt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsThetaBasisAfterEveryFieldExtension
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsThetaBasisAfterEveryFieldExtension
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis

noncomputable section

namespace GlobalTheory.OneBasis.AllExt

open GlobalTheory.FramePull GlobalTheory.ConstFam

variable {S Z : Scheme.{0}} {G₀ : Over S} {G : Over Z} {L₀ : LB G₀.left} {L : LB G.left} {F : G.left ⟶ G₀.left}
  {π : Z ⟶ S} {N : ℕ} {w : LB.Iso L (L₀.pull F)}

theorem exists_cmp_inv (hF : IsPullback F G.hom G₀.hom π) {T : Over Z} {T₀ : Over S} {u : T.left ⟶ T₀.left}
    {v : T₀.left ⟶ T.left} (huv : u ≫ v = 𝟙 _) (hvu : v ≫ u = 𝟙 _) (hu : u ≫ T₀.hom = T.hom ≫ π)
    {Φ : (T ⊗ G).left ⟶ (T₀ ⊗ G₀).left} (a₁ : Φ ≫ (fst T₀ G₀).left = (fst T G).left ≫ u)
    (a₂ : Φ ≫ (snd T₀ G₀).left = (snd T G).left ≫ F) : ∃ Ψ : (T₀ ⊗ G₀).left ⟶ (T ⊗ G).left,
      Ψ ≫ (fst T G).left = (fst T₀ G₀).left ≫ v ∧ Ψ ≫ (snd T G).left ≫ F = (snd T₀ G₀).left ∧
        Ψ ≫ Φ = 𝟙 _ ∧ Φ ≫ Ψ = 𝟙 _ := by
  have w₀ : (snd T₀ G₀).left ≫ G₀.hom = (((fst T₀ G₀).left ≫ v) ≫ T.hom) ≫ π := by
    rw [Category.assoc, Category.assoc, ← hu, reassoc_of% hvu, Over.w, Over.w]
  obtain ⟨Ψ, c₁, c₂⟩ : ∃ Ψ : (T₀ ⊗ G₀).left ⟶ (T ⊗ G).left,
      Ψ ≫ (fst T G).left = (fst T₀ G₀).left ≫ v ∧ Ψ ≫ (snd T G).left = hF.lift _ _ w₀ :=
    ⟨pullback.lift ((fst T₀ G₀).left ≫ v) (hF.lift _ _ w₀) (hF.lift_snd _ _ w₀).symm,
      pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have c₃ : Ψ ≫ (snd T G).left ≫ F = (snd T₀ G₀).left := by
    rw [reassoc_of% c₂, hF.lift_fst]
  refine ⟨Ψ, c₁, c₃, FramePull.prod_ext ?_ ?_, FramePull.prod_ext ?_ ?_⟩
  · rw [Category.assoc, a₁, reassoc_of% c₁, hvu, Category.id_comp, Category.comp_id]
  · rw [Category.assoc, a₂, c₃, Category.id_comp]
  · rw [Category.assoc, c₁, reassoc_of% a₁, huv, Category.id_comp, Category.comp_id]
  · rw [Category.id_comp]
    apply hF.hom_ext
    · rw [Category.assoc, Category.assoc, c₃, a₂]
    · rw [Category.assoc, Category.assoc, reassoc_of% c₂, hF.lift_snd, reassoc_of% a₁,
        reassoc_of% huv, Over.w, Over.w]

theorem basis_up (hF : IsPullback F G.hom G₀.hom π) (hw : w.IsGen) (hL₀ : L₀.IsLB) (hL : L.IsLB) {V : Scheme.{0}}
    {χ : V ⟶ Z} {χ₀ : V ⟶ S} (hχ : χ₀ = χ ≫ π) {T : Over Z} {T₀ : Over S} {h : Over.mk χ ⟶ T} {h₀ : Over.mk χ₀ ⟶ T₀}
    {u : T.left ⟶ T₀.left} (e : h₀.left = h.left ≫ u)
    {Φ : (T ⊗ G).left ⟶ (T₀ ⊗ G₀).left} (a₁ : Φ ≫ (fst T₀ G₀).left = (fst T G).left ≫ u)
    (a₂ : Φ ≫ (snd T₀ G₀).left = (snd T G).left ≫ F) {n : ℕ}
    {b : Fin n → LB.Sec (LPow G L (N : ℤ) T)} {b₀ : Fin n → LB.Sec (LPow G₀ L₀ (N : ℤ) T₀)}
    (hb : ∀ i, TransportedAlt w Φ (b i) (b₀ i)) (H : BasisAlong G L N h b) : BasisAlong G₀ L₀ N h₀ b₀ := by
  have hu : 𝟙 V ≫ (Over.mk χ₀).hom = (Over.mk χ).hom ≫ π := (Category.id_comp _).trans hχ
  obtain ⟨Φ', b₁, b₂⟩ := exists_cmp hF (T := Over.mk χ) (T₀ := Over.mk χ₀) (𝟙 V) hu
  obtain ⟨Ψ, c₁, c₃, i₁, i₂⟩ := exists_cmp_inv hF (T := Over.mk χ) (T₀ := Over.mk χ₀) (u := 𝟙 V) (v := 𝟙 V)
    (Category.id_comp _) (Category.id_comp _) hu b₁ b₂
  have hc := cmp_comm (h := h) (h₀ := h₀) a₁ a₂ b₁ b₂ ((Category.id_comp _).trans e)
  replace b₁ : Φ' ≫ (fst (Over.mk χ₀) G₀).left = (fst (Over.mk χ) G).left := b₁.trans (Category.comp_id _)
  replace c₁ : Ψ ≫ (fst (Over.mk χ) G).left = (fst (Over.mk χ₀) G₀).left := c₁.trans (Category.comp_id _)
  intro s₀
  obtain ⟨s, hs⟩ := exists_thr_down hw hL₀ hL b₂ s₀
  refine (existsUnique_congr fun c => ?_).2 (H s)
  rw [FramePull.lin_iff, FramePull.lin_iff]
  constructor
  · intro H W r z J hJ
    obtain ⟨J₀, hJ₀⟩ := exists_good' hL₀ z
    have := H W (r ≫ Φ') z J₀ hJ₀
    rw [Category.assoc r Φ' (fst (Over.mk χ₀) G₀).left, b₁] at this
    exact (lin_at_iff hc hb hs r z hJ₀ hJ _).1 this
  · intro H W r z J₀ hJ₀
    obtain ⟨J, hJ⟩ := exists_good' hL z
    have := (lin_at_iff hc hb hs (r ≫ Ψ) z hJ₀ hJ _).2 (H W (r ≫ Ψ) z J hJ)
    rw [Category.assoc r Ψ Φ', i₁, Category.comp_id, Category.assoc r Ψ, c₁] at this
    exact this

theorem exists_allBasis : Laws → Laws2 → ∀ (Z : Scheme.{0}) (G₀ : Over Z) [GrpObj G₀] (L₀ : LB G₀.left), L₀.IsLB → ∀ (K : Type) [Field K] (x : Sp K ⟶ Z) (A : PolAV (Sp K)) (φ : A.A.left ⟶ G₀.left) (w : LB.Iso A.L (L₀.pull φ)), IsGrpPullback A.A G₀ x φ → w.IsGen → ∀ k : ℕ, 1 ≤ k → ∃ (r : ℕ) (τ : Fin r → LB.Sec (LPow G₀ L₀ (k : ℤ) (Over.mk x))), AllBasis G₀ L₀ k x τ := by
  intro hL _ Z G₀ _ L₀ hL₀ K _ x A φ w gp hw k hk
  obtain ⟨U, hU, b, hb⟩ := PolFrames.exists_local_basisAlong k hL.secBaseChange A hk (IsLocalRing.closedPoint K)
  obtain rfl : U = ⊤ := eq_top_of_closedPoint_mem U hU
  have huv : (⊤ : (Sp K).Opens).ι ≫ (Sp K).topIso.inv = 𝟙 _ := (Sp K).topIso.hom_inv_id
  have hvu : (Sp K).topIso.inv ≫ (⊤ : (Sp K).Opens).ι = 𝟙 _ := (Sp K).topIso.inv_hom_id
  obtain ⟨Φ, a₁, a₂⟩ := exists_cmp gp.1 (T := Over.mk (⊤ : (Sp K).Opens).ι) (T₀ := Over.mk x)
    (⊤ : (Sp K).Opens).ι rfl
  obtain ⟨Ψ, -, c₃, -, i₂⟩ := exists_cmp_inv gp.1 (T := Over.mk (⊤ : (Sp K).Opens).ι) (T₀ := Over.mk x)
    huv hvu rfl a₁ a₂
  choose τ hτ using fun i => exists_thr_up hw hL₀ A.isLB c₃ i₂ (b i)
  refine ⟨_, τ, fun K' _ ga x' h => ?_⟩
  have e : spMap ga = (spMap ga ≫ (Sp K).topIso.inv) ≫ (⊤ : (Sp K).Opens).ι := by
    rw [Category.assoc, hvu, Category.comp_id]
  exact basis_up gp.1 hw hL₀ A.isLB (h.symm.trans (congrArg (· ≫ x) e)) e a₁ a₂ hτ
    (hb K' (spMap ga ≫ (Sp K).topIso.inv))

end GlobalTheory.OneBasis.AllExt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsThetaBasisAfterEveryFieldExtensionStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_thetaBasis_after_every_field_extension : Laws → Laws2 → ∀ (Z : Scheme.{0}) (G₀ : Over Z) [GrpObj G₀] (L₀ : LB G₀.left), L₀.IsLB → ∀ (K : Type) [Field K] (x : Sp K ⟶ Z) (A : PolAV (Sp K)) (φ : A.A.left ⟶ G₀.left) (w : LB.Iso A.L (L₀.pull φ)), IsGrpPullback A.A G₀ x φ → w.IsGen → ∀ k : ℕ, 1 ≤ k → ∃ (r : ℕ) (τ : Fin r → LB.Sec (LPow G₀ L₀ (k : ℤ) (Over.mk x))), AllBasis G₀ L₀ k x τ := by
  first | exact @GlobalTheory.OneBasis.AllExt.exists_allBasis | exact GlobalTheory.OneBasis.AllExt.exists_allBasis | (intros; apply GlobalTheory.OneBasis.AllExt.exists_allBasis <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsBasisRecombinationInvertibleMatrixTrait
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsBasisRecombinationInvertibleMatrixTrait
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis

noncomputable section
namespace GlobalTheory.Recombine
open GlobalTheory.FrameGen

variable {Z : Scheme.{0}} {G : Over Z} {L : LB G.left} {N : ℕ}

theorem exists_lin (hL : L.IsLB) {T T' : Over Z} (h : T' ⟶ T) {n : ℕ} (b : Fin n → LB.Sec (LPow G L (N : ℤ) T))
    (c : Fin n → Γ(T'.left, ⊤)) : ∃ s, Lin G L N h b c s := by
  choose b' hb' using fun i => exists_pull hL h (b i)
  refine ⟨SectionLimit.linSec (fun i => (fst T' G).left.appTop.hom (c i)) b', fun z J hJ => ?_⟩
  refine (SectionScalarValuation.sval_lin (s := SectionLimit.linSec (fun i => (fst T' G).left.appTop.hom (c i)) b')
    (fun i => (fst T' G).left.appTop.hom (c i)) b' (fun _ => rfl) (𝟙 _) z hJ).trans
    (Finset.sum_congr rfl fun i _ => congrArg₂ (· * ·) ?_ ?_)
  · exact (gs_pull (𝟙 _) (fst T' G).left z ⊤ trivial (c i)).trans (by rw [Category.id_comp])
  · exact (hb' i _ (𝟙 _) z J hJ).trans (by rw [Category.id_comp]; rfl)

section
variable {T T₁ T₂ T₃ : Over Z} {m n l : ℕ} {h₁ : T ⟶ T₁} {a : Fin m → LB.Sec (LPow G L (N : ℤ) T₁)} {h₂ : T ⟶ T₂}
  {b : Fin n → LB.Sec (LPow G L (N : ℤ) T₂)} {h₃ : T ⟶ T₃} {c : Fin l → LB.Sec (LPow G L (N : ℤ) T₃)}

theorem rel_id_iff (hL : L.IsLB) {a : Fin m → LB.Sec (LPow G L (N : ℤ) T)} {M : Matrix (Fin m) (Fin n) Γ(T.left, ⊤)} :
    Rel G L N (𝟙 _) a h₂ b M ↔ ∀ k, Lin G L N h₂ b (M k) (a k) := by
  constructor
  · intro H k z J hJ
    have := H k _ (𝟙 _) z J hJ
    simp only [Category.id_comp, ← gs_top, id_whiskerRight, Over.id_left] at this
    exact this
  · intro H k Y r z J hJ
    rw [id_whiskerRight, Over.id_left, Category.comp_id]
    exact lin_all hL (H k) r z hJ

theorem rel_inv {M : Matrix (Fin m) (Fin n) Γ(T.left, ⊤)} {V : Matrix (Fin n) (Fin m) Γ(T.left, ⊤)}
    (H : Rel G L N h₁ a h₂ b M) (e : V * M = (1 : Matrix (Fin n) (Fin n) Γ(T.left, ⊤))) : Rel G L N h₂ b h₁ a V := by
  intro k Y r z J hJ
  rw [Rel.refl (h₁ := h₂) (a := b) k Y r z J hJ, ← e]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [H _ Y r z J hJ, Matrix.mul_apply, map_sum, map_mul, Finset.mul_sum, Finset.sum_mul, _root_.mul_assoc]
  exact Finset.sum_comm

theorem basisAlong_of_rel (hL : L.IsLB) {a : Fin n → LB.Sec (LPow G L (N : ℤ) T₁)} {M V : Matrix (Fin n) (Fin n) Γ(T.left, ⊤)}
    (hb : BasisAlong G L N h₂ b)
    (H : Rel G L N h₁ a h₂ b M) (e : V * M = 1) (e' : M * V = 1) : BasisAlong G L N h₁ a := by
  intro s
  obtain ⟨P, hP⟩ := exists_rel hL hb (𝟙 _) (fun _ : Fin 1 => s)
  have key : ∀ c, Lin G L N h₁ a c s → Matrix.of (fun _ : Fin 1 => c) = P * V := fun c hc => by
    have r : Rel G L N (𝟙 _) (fun _ : Fin 1 => s) h₁ a (Matrix.of fun _ : Fin 1 => c) := (rel_id_iff hL).2 fun _ => hc
    rw [hP.unique hL hb (r.trans H), Matrix.mul_assoc, e', Matrix.mul_one]
  exact ⟨(P * V) 0, (rel_id_iff hL).1 (hP.trans (rel_inv H e)) 0, fun c hc => congrFun (key c hc) 0⟩

theorem exists_common (hL : L.IsLB) {b : Fin m → LB.Sec (LPow G L (N : ℤ) T₂)} {M} (H : Rel G L N h₁ a h₃ c M)
    (H' : Rel G L N h₂ b h₃ c M) (k : Fin m) :
    ∃ s, Lin G L N h₁ (fun _ : Fin 1 => a k) (fun _ => 1) s ∧ Lin G L N h₂ (fun _ : Fin 1 => b k) (fun _ => 1) s := by
  obtain ⟨s, hs⟩ := exists_lin hL h₁ (fun _ : Fin 1 => a k) (fun _ => 1)
  refine ⟨s, hs, fun z J hJ => (hs z J hJ).trans ?_⟩
  rw [Fin.sum_univ_one, Fin.sum_univ_one]
  have := (H k _ (𝟙 _) z J hJ).trans (H' k _ (𝟙 _) z J hJ).symm
  rw [Category.id_comp, Category.id_comp] at this
  exact congrArg _ this

theorem exists_common_pull (hL : L.IsLB) {b : Fin n → LB.Sec (LPow G L (N : ℤ) T₂)} {b' : Fin m → LB.Sec (LPow G L (N : ℤ) T₂)}
    {p : T₁ ⟶ T₃} {P : Matrix (Fin m) (Fin l) Γ(T₁.left, ⊤)} {U : Matrix (Fin m) (Fin n) Γ(T₂.left, ⊤)}
    {B : Matrix (Fin n) (Fin l) Γ(T.left, ⊤)} (r₁ : Rel G L N (𝟙 _) a p c P) (r₂ : Rel G L N (𝟙 _) b' (𝟙 _) b U)
    (r₃ : Rel G L N h₂ b h₃ c B) (e₁ : h₁ ≫ p = h₃) (e₂ : P.map h₁.left.appTop.hom = U.map h₂.left.appTop.hom * B)
    (k : Fin m) :
    ∃ s, Lin G L N h₁ (fun _ : Fin 1 => a k) (fun _ => 1) s ∧ Lin G L N h₂ (fun _ : Fin 1 => b' k) (fun _ => 1) s := by
  have r₄ := r₁.pull h₁
  have r₅ := r₂.pull h₂
  rw [Category.comp_id] at r₄ r₅
  rw [e₁, e₂] at r₄
  exact exists_common hL r₄ (r₅.trans r₃) k

end

abbrev fnHom (R : Type) [CommRing R] : R →+* Γ(Sp R, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom

theorem map_fnHom {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') {m n : ℕ} (M : Matrix (Fin m) (Fin n) R) :
    (M.map (fnHom R)).map (spMap f).appTop.hom = (M.map f).map (fnHom R') := by
  ext1 i j
  exact (congrArg (fun q => q.hom (M i j)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))).symm

theorem exists_rel_id (hL : L.IsLB) {T T' : Over Z} (h : T' ⟶ T) {m n : ℕ} (b : Fin n → LB.Sec (LPow G L (N : ℤ) T))
    (M : Matrix (Fin m) (Fin n) Γ(T'.left, ⊤)) : ∃ a, Rel G L N (𝟙 _) a h b M := by
  choose a ha using fun i => exists_lin hL h b (M i)
  exact ⟨a, (rel_id_iff hL).2 ha⟩

theorem map_inv_mul {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') {n : ℕ} {U : Matrix (Fin n) (Fin n) R}
    (hU : IsUnit U.det) : U⁻¹.map f * U.map f = 1 ∧ U.map f * U⁻¹.map f = 1 :=
  ⟨Matrix.map_mul.symm.trans (by rw [Matrix.nonsing_inv_mul _ hU, Matrix.map_one _ (map_zero _) (map_one _)]),
    Matrix.map_mul.symm.trans (by rw [Matrix.mul_nonsing_inv _ hU, Matrix.map_one _ (map_zero _) (map_one _)])⟩

theorem map_fnHom_mul {R W F : Type} [CommRing R] [CommRing W] [CommRing F] (f : R →+* F) (g : W →+* F) {n : ℕ}
    {P : Matrix (Fin n) (Fin n) R} {U : Matrix (Fin n) (Fin n) W} {B : Matrix (Fin n) (Fin n) F}
    (e : P.map f = U.map g * B) : (P.map (fnHom R)).map (spMap f).appTop.hom =
      (U.map (fnHom W)).map (spMap g).appTop.hom * B.map (fnHom F) := by
  rw [map_fnHom, map_fnHom, e, Matrix.map_mul]

theorem exists_recombination : ∀ (Z : Scheme.{0}) (G : Over Z) (L : LB G.left), L.IsLB → ∀ (N : ℕ) (K K₂ : Type) [Field K] [Field K₂] (x : Sp K ⟶ Z) (ie : K →+* K₂) (x₂ : Sp K₂ ⟶ Z), spMap ie ≫ x = x₂ → ∀ (n : ℕ) (τ : Fin n → LB.Sec (LPow G L (N : ℤ) (Over.mk x))) (Φ : Matrix (Fin n) (Fin n) K₂), ∃ f : Fin n → LB.Sec (LPow G L (N : ℤ) (Over.mk x₂)), ∀ (W : Type) [CommRing W] [IsDomain W] (gam : K₂ →+* FractionRing W) (χ : Sp W ⟶ Z) (h : spMap (gam.comp ie) ≫ x = jK W ≫ χ) (h₂ : spMap gam ≫ x₂ = jK W ≫ χ) (B : Matrix (Fin n) (Fin n) (FractionRing W)) (U : Matrix (Fin n) (Fin n) W), BasisBy G L N x (gam.comp ie) χ h τ B → IsUnit U.det → Φ.map gam = U.map (algebraMap W (FractionRing W)) * B → FrameAt G L N x₂ gam χ h₂ f := by
  intro Z G L hL N K K₂ _ _ x ie x₂ hx n τ Φ
  obtain ⟨f, r₁⟩ := exists_rel_id hL (Over.homMk (spMap ie) hx : Over.mk x₂ ⟶ Over.mk x) τ (Φ.map (fnHom K₂))
  refine ⟨f, fun W _ _ gam χ h h₂ B U H hU e => ?_⟩
  obtain ⟨b, hb, hB⟩ := H
  obtain ⟨b', r₂⟩ := exists_rel_id hL (𝟙 (Over.mk χ)) b (U.map (fnHom W))
  have r₃ : Rel G L N (Over.homMk (jK W) rfl : Over.mk (jK W ≫ χ) ⟶ Over.mk χ) b
      (Over.homMk (spMap (gam.comp ie)) h : Over.mk (jK W ≫ χ) ⟶ Over.mk x) τ (B.map (fnHom (FractionRing W))) :=
    rel_of_lin hL fun k => (hB k).imp fun _ H => H.symm
  exact ⟨b', basisAlong_of_rel hL hb r₂ (map_inv_mul (fnHom W) hU).1 (map_inv_mul (fnHom W) hU).2,
    exists_common_pull hL r₁ r₂ r₃ (Over.OverMorphism.ext (spMap_comp' ie gam).symm) (map_fnHom_mul gam _ e)⟩

end GlobalTheory.Recombine
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsBasisRecombinationInvertibleMatrixTraitStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_basis_recombination_invertible_matrix_trait : ∀ (Z : Scheme.{0}) (G : Over Z) (L : LB G.left), L.IsLB → ∀ (N : ℕ) (K K₂ : Type) [Field K] [Field K₂] (x : Sp K ⟶ Z) (ie : K →+* K₂) (x₂ : Sp K₂ ⟶ Z), spMap ie ≫ x = x₂ → ∀ (n : ℕ) (τ : Fin n → LB.Sec (LPow G L (N : ℤ) (Over.mk x))) (Φ : Matrix (Fin n) (Fin n) K₂), ∃ f : Fin n → LB.Sec (LPow G L (N : ℤ) (Over.mk x₂)), ∀ (W : Type) [CommRing W] [IsDomain W] (gam : K₂ →+* FractionRing W) (χ : Sp W ⟶ Z) (h : spMap (gam.comp ie) ≫ x = jK W ≫ χ) (h₂ : spMap gam ≫ x₂ = jK W ≫ χ) (B : Matrix (Fin n) (Fin n) (FractionRing W)) (U : Matrix (Fin n) (Fin n) W), BasisBy G L N x (gam.comp ie) χ h τ B → IsUnit U.det → Φ.map gam = U.map (algebraMap W (FractionRing W)) * B → FrameAt G L N x₂ gam χ h₂ f := by
  first | exact @GlobalTheory.Recombine.exists_recombination | exact GlobalTheory.Recombine.exists_recombination | (intros; apply GlobalTheory.Recombine.exists_recombination <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LineBundleIsoValuesConstantOfSameCubeTheta
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LineBundleIsoValuesConstantOfSameCubeTheta
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Relabel

noncomputable section
namespace GlobalTheory.IsoValConst
open GlobalTheory.TorusExt GlobalTheory.ArcTransport

theorem const_of_cube {A U : Type} [CommGroup A] [CommGroup U] (Ω : A → U)
    (hc : ∀ a b c, Ω (a * b * c) * (Ω (a * b))⁻¹ * (Ω (a * c))⁻¹ * (Ω (b * c))⁻¹ * Ω a * Ω b * Ω c * (Ω 1)⁻¹ = 1)
    (P : A → Prop) (hP : ∀ a b, P a → P b → Ω a = Ω b) (n : ℕ) (hd : ∀ x : A, ∃ y, y ^ n = x)
    (hg : ∀ a : A, ∃ t, t ^ n = 1 ∧ P (a * t)) (x : A) : Ω x = Ω 1 := by
  obtain ⟨h, hh⟩ : ∃ h : A → U, ∀ x, h x = Ω x / Ω 1 := ⟨_, fun _ => rfl⟩
  have h1 : h 1 = 1 := by rw [hh, div_self']
  let B : A → A →* U := fun z => MonoidHom.mk' (fun x => h (x * z) / (h x * h z)) fun x y => by
    have e := congrArg Additive.ofMul (hc x y z)
    apply Additive.ofMul.injective
    simp only [hh, ofMul_mul, ofMul_div, ofMul_inv, ofMul_one] at e ⊢
    linear_combination (norm := abel) e
  have hB : ∀ z x, B z x = h (x * z) / (h x * h z) := fun _ _ => rfl
  have sy : ∀ z x, B z x = B x z := fun z x => by rw [hB, hB, mul_comm x, mul_comm (h x)]
  have tors : ∀ t, t ^ n = 1 → ∀ a, h (a * t) = h a * h t := fun t ht a => by
    obtain ⟨b, rfl⟩ := hd a
    rw [← div_eq_one, ← hB, map_pow, sy, ← map_pow, ht, map_one]
  have pw : ∀ t, (∀ a, h (a * t) = h a * h t) → ∀ k : ℕ, h (t ^ k) = h t ^ k := fun t ht k => by
    induction k with
    | zero => rw [pow_zero, pow_zero, h1]
    | succ k ih => rw [pow_succ, pow_succ, ht, ih]
  have key : ∀ a t, t ^ n = 1 → h (a * t) ^ n = h a ^ n := fun a t ht => by
    rw [tors t ht, mul_pow, ← pw t (tors t ht), ht, h1, _root_.mul_one]
  have kill : ∀ a, h a ^ n = 1 := fun a => by
    obtain ⟨t, ht, p⟩ := hg a
    obtain ⟨s, hs, q⟩ := hg 1
    rw [← key a t ht, hh, hP _ _ p q, ← hh, key 1 s hs, h1, one_pow]
  have mul : ∀ t a, h (a * t) = h a * h t := fun t a => by
    obtain ⟨b, rfl⟩ := hd a
    rw [← div_eq_one, ← hB, map_pow, hB, div_pow, mul_pow, kill, kill, kill, _root_.mul_one, div_one]
  obtain ⟨y, rfl⟩ := hd x
  rw [← div_eq_one, ← hh, pw y (mul y), kill]

section Val
variable {F : Type} [Field F] {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}

theorem const_vF (t : LB.Gen (LB.LinComb L φ ε)) (r : Sp F ⟶ Y) {z : Sp F} {J : (Sp F ⟶ X) → L.ι} (hJ : Good L z J) :
    stalkConst z (vF t r J) = (val t r z J).val :=
  ((gs_unit r z _ (hJ.mem φ r) _).symm.trans (gs_eq_stalkConst r z
    (fun w _ => (Subsingleton.elim (α := PrimeSpectrum F) z w) ▸ hJ.mem φ r) _)).symm

theorem const_sF (s : LB.Sec (LB.LinComb L φ ε)) (r : Sp F ⟶ Y) {z : Sp F} {J : (Sp F ⟶ X) → L.ι} (hJ : Good L z J) :
    stalkConst z (sF s r J) = sval s r z J :=
  (gs_eq_stalkConst r z (fun w _ => (Subsingleton.elim (α := PrimeSpectrum F) z w) ▸ hJ.mem φ r) _).symm
end Val

theorem exists_iso_pull {X X' Y : Scheme.{0}} {L : LB X} {L' : LB X'} {Φ : X' ⟶ X} {w : LB.Iso L' (L.pull Φ)}
    (hw : w.IsGen) (h : Y ⟶ X') : ∃ w' : LB.Iso (L'.pull h) (L.pull (h ≫ Φ)), w'.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) j k, Φ (h (r z)) ∈ L.U j → h (r z) ∈ L'.U k →
        gw w' r z j (fun _ => k) = gw w (r ≫ h) z j k := by
  have le : ∀ p : (PUnit → L.ι) × (PUnit → L'.ι), (L.pull (h ≫ Φ)).U p.1 ⊓ (L'.pull h).U p.2 ≤
      h ⁻¹ᵁ ((L.pull Φ).U p.1 ⊓ L'.U (p.2 PUnit.unit)) := fun p y hy =>
    ⟨mem_pull.2 (mem_pull.1 (show y ∈ (L.pull (h ≫ Φ)).U p.1 from hy.1) :), mem_pull.1 hy.2⟩
  let w' : LB.Iso (L'.pull h) (L.pull (h ≫ Φ)) := ⟨fun p => res (le p) (pullU h _ (w.s (p.1, p.2 PUnit.unit)))⟩
  have v : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) j (k : PUnit → L'.ι), Φ (h (r z)) ∈ L.U j → h (r z) ∈ L'.U (k PUnit.unit) →
      gw w' r z j k = gw w (r ≫ h) z j (k PUnit.unit) := fun Z r z j k hj hk =>
    have m : r z ∈ (L.pull (h ≫ Φ)).U (fun _ => j) ⊓ (L'.pull h).U k := ⟨mem_pull.2 hj, mem_pull.2 hk⟩
    (gm_res r z (le (fun _ => j, k)) m _).trans (gm_pull r h z _ (le (fun _ => j, k) m) _)
  refine ⟨w', (isGen_iff _).2 fun Z r z j j' k k' hj hj' hk hk' => ?_, fun Z r z j k => v Z r z j fun _ => k⟩
  rw [v Z r z j k hj (mem_pull.1 hk), v Z r z j' k' hj' (mem_pull.1 hk'), gm_pull_g L' h r z k k' hk hk',
    ← Category.assoc]
  exact (isGen_iff _).1 hw Z (r ≫ h) z j j' _ _ hj hj' (mem_pull.1 hk :) (mem_pull.1 hk' :)

section Num
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
  {N : NumD F} (ν : NumOf D F N) (z : Sp F)

theorem good : Good D.P.L z ν.J := fun ψ => ν.good ψ trivial

theorem stalk_θ (x y u : N.A) : stalkUnits z (N.θ x y u) = thS D z ν.J (ν.eA x) (ν.eA y) (ν.eA u) :=
  Units.ext ((congrArg (stalkConst z) (ν.θ_eq x y u)).trans (const_vF _ _ (good ν z)))

theorem stalk_th : ∃ ρ : ((Sp F).presheaf.stalk z)ˣ, ∀ x : N.A,
    stalkConst z (N.th x) * ρ.val = sval (Z := Sp F) ν.th (ν.eA x).left z ν.J :=
  ⟨_, fun x => (congrArg _ (const_vF _ _ (good ν z)).symm).trans ((map_mul _ _ _).symm.trans
    ((congrArg (stalkConst z) (ν.th_eq x)).trans (const_sF _ _ (good ν z))))⟩

theorem sval_eq (s : H0 D.P.L 1) : ∃ κ : (Sp F).presheaf.stalk z, ∀ x : TF (R := R) F ⟶ D.P.A,
    sval (Z := Sp F) s x.left z ν.J = κ * sval (Z := Sp F) ν.th x.left z ν.J := by
  obtain ⟨r, hr⟩ := ν.th_gen s
  refine ⟨gs (Y := Sp F) (TF (R := R) F).hom z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r), fun x => ?_⟩
  have m := (good ν z).mem (fun _ : Fin 1 => 𝟙 D.P.A.left) (show Sp F ⟶ _ from x.left)
  refine (congrArg (gs _ z _) (hr _)).trans ((gs_mul _ z _ m _ _).trans (congrArg₂ (· * ·) ?_ rfl))
  refine (gs_res _ z le_top m _).trans ?_
  rw [← Over.w x]
  exact gs_pull (show Sp F ⟶ _ from x.left) D.P.A.hom z ⊤ trivial _
end Num

theorem exists_iso_val_const : Laws → ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (f : R' →+* R) (D : DegPre R) (D' : DegPre R') (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing R') F] (N : NumD F) (k : ℕ) (β : N.Form k) (u : Fˣ) (ν : NumOf D F (N.twist β u)) (ν' : NumOf D' F N) (φ : D.P.A.left ⟶ D'.P.A.left) (w : LB.Iso D.P.L (D'.P.L.pull φ)), IsGrpPullback D.P.A D'.P.A (spMap f) φ → w.IsGen → (∀ x, (ν.eA x).left ≫ φ = (ν'.eA x).left) → ∀ n : ℕ, (∀ x : N.A, ∃ y, y ^ n = x) → (∀ a : N.A, ∃ t, t ^ n = 1 ∧ N.th (a * t) ≠ 0) → ∃ (w' : LB.Iso (D.P.L.pull (snd (TF (R := R) F) D.P.A).left) (D'.P.L.pull ((snd (TF (R := R) F) D.P.A).left ≫ φ))) (c : Fˣ), w'.IsGen ∧ ∀ x, valF (lift (𝟙 (TF (R := R) F)) (ν.eA x)).left _ (w'.s (fun _ => ν'.J (ν'.eA x).left, fun _ => ν.J (ν.eA x).left)).val = c := by
  intro hL R R' _ _ _ _ f D D' F _ _ _ N k β u ν ν' φ w gp hw he n hd hg
  let z : Sp F := IsLocalRing.closedPoint F
  have hJ := good ν z
  have hJ' := good ν' z
  have hT : (TF (R := R) F).hom ≫ spMap f = (TF (R := R') F).hom := by
    rw [← Over.w (ν.eA 1), ← Over.w (ν'.eA 1), Category.assoc]
    exact (congrArg _ gp.1.w.symm).trans ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ D'.P.A.hom) (he 1)))
  have hp : ∀ x : N.A, pushF gp hT (ν.eA x) = ν'.eA x := fun x => Over.OverMorphism.ext (he x)
  let Ω : N.A → ((Sp F).presheaf.stalk z)ˣ := fun x => wVal w z ν'.J ν.J (ν.eA x)
  have em : ∀ a b : N.A, ν.eA (a * b) = ν.eA a * ν.eA b := fun a b => map_mul ν.eA a b
  have e1 : ν.eA (1 : N.A) = 1 := map_one ν.eA
  have hΩ : ∀ x, Ω x = Ω 1 := by
    refine const_of_cube Ω (fun a b c => ?_) (fun a => N.th a ≠ 0) ?_ n hd hg
    · have e := thS_push gp hT ((isGen_iff _).1 hw) hL.globalFns hJ' hJ (ν.eA a) (ν.eA b) (ν.eA c)
      rw [hp, hp, hp, ← em, ← em, ← em, ← em, ← e1] at e
      exact mul_eq_right.1 (e.symm.trans ((stalk_θ ν' z a b c).symm.trans (stalk_θ ν z a b c)))
    · obtain ⟨s, hs⟩ := ConstFam.exists_secThrough (φ' := fun _ : Fin 1 => 𝟙 D.P.A.left)
        (φ := fun _ : Fin 1 => 𝟙 D'.P.A.left) (h := φ) hw D'.P.isLB D.P.isLB
        (fun _ => (Category.id_comp _).trans (Category.comp_id _).symm) ν'.th
      obtain ⟨κ, hκ⟩ := sval_eq ν z s
      obtain ⟨ρ, hρ⟩ := stalk_th ν z
      obtain ⟨ρ', hρ'⟩ := stalk_th ν' z
      have key : ∀ a : N.A, N.th a ≠ 0 → ρ'.val = (Ω a).val * (κ * ρ.val) := fun a ha => by
        have e := hs.sval (fun _ => (Category.id_comp _).trans (Category.comp_id _).symm)
          (show Sp F ⟶ _ from (ν.eA a).left) hJ' hJ
        rw [Fin.prod_univ_one, Category.comp_id] at e
        replace e := e.trans (congrArg (fun q : ((Sp F).presheaf.stalk z)ˣ => q.val * _) (zpow_one _))
        have e' : stalkConst z (N.th a) * ρ'.val = (Ω a).val * (κ * (stalkConst z (N.th a) * ρ.val)) :=
          (hρ' a).trans ((congrArg (fun q => sval (Z := Sp F) ν'.th q z ν'.J) (he a).symm).trans (e.trans
            (congrArg _ ((hκ _).trans (congrArg _ (hρ a).symm)))))
        refine ((IsUnit.mk0 _ ha).map (stalkConst z)).mul_left_cancel (e'.trans ?_)
        ring
      intro a b ha hb
      have hu : IsUnit (κ * ρ.val) := isUnit_of_mul_isUnit_right (key a ha ▸ ρ'.isUnit)
      exact Units.ext (hu.mul_right_cancel ((key a ha).symm.trans (key b hb)))
  obtain ⟨w', hw', hv⟩ := exists_iso_pull hw (snd (TF (R := R) F) D.P.A).left
  refine ⟨w', (stalkUnits z).symm (Ω 1), hw', fun x => (stalkConst z).injective ?_⟩
  have l : (lift (𝟙 (TF (R := R) F)) (ν.eA x)).left ≫ (snd (TF (R := R) F) D.P.A).left = (ν.eA x).left := by
    rw [← Over.comp_left, lift_snd]
  have m₁ : ((lift (𝟙 (TF (R := R) F)) (ν.eA x)).left ≫ (snd (TF (R := R) F) D.P.A).left) z ∈
      D.P.L.U (ν.J (ν.eA x).left) := by rw [l]; exact hJ _
  have m₂ : (((lift (𝟙 (TF (R := R) F)) (ν.eA x)).left ≫ (snd (TF (R := R) F) D.P.A).left) ≫ φ) z ∈
      D'.P.L.U (ν'.J (ν'.eA x).left) := by rw [l, he]; exact hJ' _
  refine (toStk_valF (lift (𝟙 (TF (R := R) F)) (ν.eA x)).left
    ((D'.P.L.pull ((snd (TF (R := R) F) D.P.A).left ≫ φ)).U (fun _ => ν'.J (ν'.eA x).left) ⊓
      (D.P.L.pull (snd (TF (R := R) F) D.P.A).left).U fun _ => ν.J (ν.eA x).left) z ⟨mem_pull.2 m₂, mem_pull.2 m₁⟩ _).trans ?_
  rw [← stalkUnits_val, MulEquiv.apply_symm_apply, ← hΩ x]
  refine congrArg Units.val ((hv (Sp F) _ z _ _ m₂ m₁).trans ?_)
  rw [l, ← he]
  rfl

end GlobalTheory.IsoValConst
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LineBundleIsoValuesConstantOfSameCubeThetaStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Relabel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineBundleIso_values_constant_of_same_cube_theta : Laws → ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (f : R' →+* R) (D : DegPre R) (D' : DegPre R') (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing R') F] (N : NumD F) (k : ℕ) (β : N.Form k) (u : Fˣ) (ν : NumOf D F (N.twist β u)) (ν' : NumOf D' F N) (φ : D.P.A.left ⟶ D'.P.A.left) (w : LB.Iso D.P.L (D'.P.L.pull φ)), IsGrpPullback D.P.A D'.P.A (spMap f) φ → w.IsGen → (∀ x, (ν.eA x).left ≫ φ = (ν'.eA x).left) → ∀ n : ℕ, (∀ x : N.A, ∃ y, y ^ n = x) → (∀ a : N.A, ∃ t, t ^ n = 1 ∧ N.th (a * t) ≠ 0) → ∃ (w' : LB.Iso (D.P.L.pull (snd (TF (R := R) F) D.P.A).left) (D'.P.L.pull ((snd (TF (R := R) F) D.P.A).left ≫ φ))) (c : Fˣ), w'.IsGen ∧ ∀ x, valF (lift (𝟙 (TF (R := R) F)) (ν.eA x)).left _ (w'.s (fun _ => ν'.J (ν'.eA x).left, fun _ => ν.J (ν.eA x).left)).val = c := by
  first | exact @GlobalTheory.IsoValConst.exists_iso_val_const | exact GlobalTheory.IsoValConst.exists_iso_val_const | (intros; apply GlobalTheory.IsoValConst.exists_iso_val_const <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NonemptyUniformisationTraitInAbelianLocus
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NonemptyUniformisationTraitInAbelianLocus
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.ThetaPtMove GlobalTheory.ConstFam
open GlobalTheory.Ex.OneGen GlobalTheory.UT

namespace GlobalTheory.AbelianTrait

theorem isProper_snd_of_mem_abLocus {S : Scheme.{0}} (G : Over S) [IsSeparated G.hom] [LocallyOfFiniteType G.hom]
    {K : Type} [Field K] (t : Sp K ⟶ S) (p : Sp K) (hp : t p ∈ abLocus G) : IsProper (pullback.snd G.hom t) := by
  let K' := AlgebraicClosure K
  let u : Sp K' ⟶ Sp K := spMap (algebraMap K K')
  have : Subsingleton (Sp K) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  have q : Sp K' := (default : PrimeSpectrum K')
  have e : (u ≫ t) q = t p := congrArg (fun z => t z) (Subsingleton.elim (u q) p)
  have h₁ := hp K' (u ≫ t) ⟨q, e⟩
  have P := (IsPullback.of_hasPullback (pullback.snd G.hom t) u).paste_horiz (IsPullback.of_hasPullback G.hom t)
  have h₃ : UniversallyClosed (pullback.snd (pullback.snd G.hom t) u) := by
    rw [← P.isoPullback_hom_snd]
    infer_instance
  have : Nonempty (Sp K') := ⟨q⟩
  have hu : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}) u :=
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  have : UniversallyClosed (pullback.snd G.hom t) :=
    MorphismProperty.of_pullback_snd_of_descendsAlong (P := @UniversallyClosed) hu h₃
  exact ⟨⟩

theorem nonempty_pelUnif_of_abLocus : GlobalTheory.LN.UDvrSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t : SAB H S) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (χ : Sp W ⟶ S) (t' : SAB H (Sp W)) (_ : SABMap t' t χ), GlobalTheory.LN.PolAt t' (jK W) → Set.range χ ⊆ abLocus t.G → Nonempty (PELUnif (maximalIdeal W) t') := by
  intro hU E _ _ _ H S t W _ _ _ hW χ t' m hpol hr
  have hG := t'.semi
  have := hG.smooth
  have := hG.separated
  let r : Sp (W ⧸ maximalIdeal W) ⟶ Sp W := spMap (Ideal.Quotient.mk (maximalIdeal W))
  have p : Sp (W ⧸ maximalIdeal W) := (default : PrimeSpectrum (ResidueField W))
  have h₀ : r p ∈ abLocus t'.G := (abLocus_pullback abLocusOne t.semi m.cart.1 (r p)).1 (hr ⟨_, rfl⟩)
  have h₁ : IsProper (pullback.snd t'.G.hom r) := isProper_snd_of_mem_abLocus t'.G (K := ResidueField W) r p h₀
  have := hG.comm
  have := hG.geomConnected
  obtain ⟨P, -⟩ := hU E H W hW t' hpol
    ⟨_, ZJ.isGt_splitExtOfAbelian _ ⟨inferInstance, by
      change Smooth (pullback.snd t'.G.hom r)
      infer_instance, h₁, by
      change GeometricallyConnected (pullback.snd t'.G.hom r)
      infer_instance⟩⟩
  exact ⟨P⟩

end GlobalTheory.AbelianTrait
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NonemptyUniformisationTraitInAbelianLocusStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.ThetaPtMove GlobalTheory.ConstFam
open GlobalTheory.Ex.OneGen GlobalTheory.UT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_uniformisation_trait_in_abelianLocus : GlobalTheory.LN.UDvrSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t : SAB H S) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (χ : Sp W ⟶ S) (t' : SAB H (Sp W)) (_ : SABMap t' t χ), GlobalTheory.LN.PolAt t' (jK W) → Set.range χ ⊆ abLocus t.G → Nonempty (PELUnif (maximalIdeal W) t') := by
  first | exact @GlobalTheory.AbelianTrait.nonempty_pelUnif_of_abLocus | exact GlobalTheory.AbelianTrait.nonempty_pelUnif_of_abLocus | (intros; apply GlobalTheory.AbelianTrait.nonempty_pelUnif_of_abLocus <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ValIso
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Arch

noncomputable section
namespace GlobalTheory.Ex.Arch.FibEx
open GlobalTheory.CubeValues GlobalTheory.SymmetricSemicharacter GlobalTheory.EigenNorm GlobalTheory.FrameValue

theorem val_iso {X : Scheme.{0}} (x : Sp ℂ ⟶ X) {L M : LB X} (hM : M.IsLB) {w : LB.Iso L M} (hw : w.IsGen)
    (m : M.ι) (i j : L.ι) (hm : ⊤ ≤ x ⁻¹ᵁ M.U m) (hi : ⊤ ≤ x ⁻¹ᵁ L.U i) (hj : ⊤ ≤ x ⁻¹ᵁ L.U j) :
    valAt' x _ (w.s (m, i)).val * valAt' x (L.U i ⊓ L.U j) (L.g i j).val = valAt' x _ (w.s (m, j)).val := by
  have h : ⊤ ≤ x ⁻¹ᵁ (M.U m ⊓ L.U i ⊓ (M.U m ⊓ L.U j)) :=
    (le_preimage_inf x _ _).2 ⟨(le_preimage_inf x _ _).2 ⟨hm, hi⟩, (le_preimage_inf x _ _).2 ⟨hm, hj⟩⟩
  have l₁ : M.U m ⊓ L.U i ⊓ (M.U m ⊓ L.U j) ≤ M.U m ⊓ M.U m :=
    le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left)
  have l₂ : M.U m ⊓ L.U i ⊓ (M.U m ⊓ L.U j) ≤ L.U i ⊓ L.U j :=
    le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)
  suffices H : ∀ (a : Γ(X, M.U m ⊓ L.U i)ˣ) (b : Γ(X, M.U m ⊓ L.U j)ˣ), res inf_le_left a =
      res l₁ (M.g m m) * (res l₂ (L.g i j))⁻¹ * res inf_le_right b →
      valAt' x _ a.val * valAt' x (L.U i ⊓ L.U j) (L.g i j).val = valAt' x _ b.val from
    H (w.s (m, i)) (w.s (m, j)) (hw (m, i) (m, j))
  intro a b e
  have e' : res inf_le_left a * res l₂ (L.g i j) = res l₁ (M.g m m) * res inf_le_right b := by
    rw [e, mul_right_comm, inv_mul_cancel_right]
  have o : valAt' x (M.U m ⊓ M.U m) (M.g m m).val = 1 := by
    obtain ⟨ev, hev⟩ := (valueRules X x).2.1 _ hm
    rw [← val_res x valueRules (le_inf le_rfl le_rfl) hm, hM.g_self, hev, Units.val_one, map_one]
  have v := congrArg (fun q : Γ(X, _)ˣ => valAt' x _ q.val) e'
  obtain ⟨ev, hev⟩ := (valueRules X x).2.1 _ h
  simp only [hev, Units.val_mul, map_mul] at v
  simp only [← hev] at v
  rw [val_res x valueRules _ h, val_res x valueRules _ h, val_res x valueRules _ h, val_res x valueRules _ h, o,
    _root_.one_mul] at v
  exact v

theorem fibEx : Laws → ThetaUnifAV → FibExSt := by
  intro hL hT R _ _ _ P J hJ
  obtain ⟨P', φ, hφ, -, hmul, t, ht⟩ := hL.polBaseChange _ _ (TF (R := R) ℂ).hom P
  have gp : IsGrpPullback P'.A P.A (TF (R := R) ℂ).hom φ := ⟨hφ, fun T x y x₀ y₀ hx hy => by
    have ex : x₀ = toBase hφ.w x := Over.OverMorphism.ext hx
    have ey : y₀ = toBase hφ.w y := Over.OverMorphism.ext hy
    rw [ex, ey, ← hmul]; rfl⟩
  obtain ⟨w, hw⟩ := LBIso.symm ⟨t, ht⟩
  obtain ⟨rig, hrig⟩ := P'.rigid
  obtain ⟨u, Hm, χ, Ef, hAH, -, h₁, h₂, h₃, -, hE, hB, -⟩ := hT P' rig hrig
  let ex : (Fin P'.g → ℂ) → (TF (R := R) ℂ ⟶ P.A) := fun z => Over.homMk ((u.ex z).left ≫ φ) (by
    show ((u.ex z).left ≫ φ) ≫ P.A.hom = _
    rw [Category.assoc, hφ.w, ← Category.assoc, Over.w]
    exact Category.id_comp _)
  have hm : ∀ z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ (P.L.pull φ).U (fun _ => J (ex z).left) := fun z =>
    (le_preimage_wchart _ P.L _ _).2 fun _ => hJ _
  have hc := fun z => le_chartAt P'.isLB (u.ex z).left
  refine ⟨P'.g, u.Λ, Hm, χ, Ef, ex, fun z => Units.mk0
    (valAt' (u.ex z).left _ (w.s (fun _ => J (ex z).left, chartAt P'.isLB (u.ex z).left)).val *
      u.fr (chartAt P'.isLB (u.ex z).left) z)
    (mul_ne_zero (val_unit_ne_zero _ valueRules ((le_preimage_inf _ _ _).2 ⟨hm z, hc z⟩) _) (u.fr_ne _ _ (hc z))),
    ⟨hJ, P', φ, w, u, rfl, gp, hw, hAH, h₁, h₂, h₃, fun _ => rfl, fun z i hi => ?_⟩, hE, hB⟩
  rw [Units.val_mk0, u.fr_compat _ i z ((le_preimage_inf _ _ _).2 ⟨hc z, hi⟩), ← _root_.mul_assoc]
  exact congrArg (· * u.fr i z) (val_iso _ (pull_isLB P.isLB φ) hw _ _ _ (hm z) (hc z) hi)

end GlobalTheory.Ex.Arch.FibEx
end
end
