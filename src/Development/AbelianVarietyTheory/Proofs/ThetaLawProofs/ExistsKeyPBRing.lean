module

public import Development.AbelianVarietyTheory.Statements.FundamentalDomains.ExistsIsAddFundamentalDomain
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UnitOnInjectiveOfCommRing
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KeyInNormalFormAndArchimedeanConstant
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.MemSpanOfCardLe
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.LbIsoDescendsToSubfieldContainingFinset
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsNormalisedIsoPullbackMulByM
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.PowObjSmoothOfRelativeDimensionMul
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.RelAmplePowObjBoxLB

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKeyPBRing
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.KeyPow

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem exists_keyPB_ring {R R' : Type} [CommRing R] [CommRing R'] (x : KeyIn R) (f : R →+* R') :
    ∃ x' : KeyIn R', KeyPB x' x f := by
  have h := isGrpPullback_pullback x.P.A (spMap f)
  let φ : ((Over.pullback (spMap f)).obj x.P.A).left ⟶ x.P.A.left := pullback.fst x.P.A.hom (spMap f)
  change IsGrpPullback _ _ _ φ at h
  have hL' := LB.isLB_pull x.P.isLB φ
  have hw := (isGen_iff _).1 (idIso_isGen hL')
  let P' : Out.PolAV (Sp R') :=
    { A := (Over.pullback (spMap f)).obj x.P.A
      isAb := Out.TLinPf.isAb_pullback (spMap f) x.P.A x.P.isAb
      g := x.P.g
      smoothDim := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback h.1 x.P.smoothDim
      L := x.P.L.pull φ
      isLB := hL'
      rigid := PolBaseChange.rigidified_pull h x.P.rigid
      sym := PolBaseChange.sym_pull h x.P.sym
      ample := relAmple_pull h.1 x.P.isLB hL' hw ⊤ (isAffineOpen_top _) (fun _ => trivial) x.P.ample
      ktriv := kTriv_pull h x.P.isLB hL' hw x.P.ktriv }
  have he : eSec P'.A ≫ φ = spMap f ≫ eSec x.P.A := PolBaseChange.eSec_comm h
  have hr : (rigPullOf φ (spMap f) he x.P.L x.rig).IsGen :=
    Out.LBxP.isGen_pullAlong x.P.L φ (spMap f) (fun _ : PUnit => eSec x.P.A) (fun _ => 1) (fun _ => eSec P'.A)
      (fun _ => he) x.rig x.rig_gen
  obtain ⟨th', hth'⟩ := sec_pull_down hw x.P.isLB hL' x.th
  have c₁ : IsCommMonObj x.P.A := x.P.isAb.comm
  have c₂ : IsCommMonObj P'.A := P'.isAb.comm
  obtain ⟨v', hb', hv'⟩ := exists_isLieBasis_baseChange R R' f x.P.A P'.A φ h x.P.isAb.smooth x.P.g x.v x.basis
  refine ⟨⟨P', x.g_pos, _, hr, th', fun s => ?_, v', hb'⟩,
    φ, he, idIso _, rfl, Chart.dualMapR f, h, idIso_isGen hL', fun p => hr p.1 p.2,
    appLE_eq_of_stalk _ x.th th' (hth' _ (𝟙 _)), fun a => ?_, ?_, hv'⟩
  · obtain ⟨z, hz, hz'⟩ := x.th_ne (spMap f s)
    obtain ⟨y, rfl, hy⟩ := Scheme.exists_preimage_of_isPullback h.1 z s hz
    obtain ⟨k, hk, u⟩ := (mem_nonzeroLocus _ _).1 hz'
    refine ⟨y, hy, (mem_nonzeroLocus _ _).2 ⟨fun _ => k, mem_pull.2 hk, ?_⟩⟩
    have u₁ : IsUnit (gs φ y _ (x.th.f k)) := by rw [gs_stalkMap φ y _ hk]; exact u.map _
    have e := hth' _ (𝟙 _) y k (fun _ => k) hk (mem_pull.2 hk)
    rw [Category.id_comp] at e
    exact isUnit_of_mul_isUnit_right (e ▸ u₁)
  · ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  · ext <;> simp [Chart.dualMapR]

theorem keyIn_baseChange : Out.PolBaseChangeSt → ∀ (R R' : Type) [CommRing R] [CommRing R'] (x : KeyIn R) (f : R →+* R'),
    ∃ x' : KeyIn R', KeyPB x' x f :=
  fun _ _ _ _ _ x f => exists_keyPB_ring x f

end GlobalTheory.KeyPow
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.StalkOfAppLEEq
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KeyComp

theorem stalk_of_appLE_eq {X X' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} (w : LB.Iso L' (L.pull F)) (s : L.Sec)
    (s' : L'.Sec) (h : ∀ (j : (L.pull F).ι) (i : L'.ι) (hle : (L.pull F).U j ⊓ L'.U i ≤ F ⁻¹ᵁ L.U (j PUnit.unit)),
      (F.appLE _ _ hle).hom (s.f (j PUnit.unit)) =
        (show Γ(X', (L.pull F).U j ⊓ L'.U i) from (w.s (j, i)).val) * resG _ inf_le_right (s'.f i))
    {Z : Scheme.{0}} (r : Z ⟶ X') (z : Z) (j : L.ι) (k : L'.ι) (hj : F (r z) ∈ L.U j) (hk : r z ∈ L'.U k) :
    gs (r ≫ F) z _ (s.f j) = (gw w r z j k).val * gs r z _ (s'.f k) := by
  have hle : (L.pull F).U (fun _ => j) ⊓ L'.U k ≤ F ⁻¹ᵁ L.U j := fun _ hy => mem_pull.1 hy.1
  have hy : r z ∈ (L.pull F).U (fun _ => j) ⊓ L'.U k := ⟨mem_pull.2 hj, hk⟩
  have e := congrArg (gs r z _) (h (fun _ => j) k hle)
  refine (gs_appLE F _ _ hle r z hy _).symm.trans (e.trans ?_)
  rw [gs_mul _ z _ hy, gs_res _ z _ hy]
  exact congrArg (· * _) (gs_unit _ z _ hy _)

end GlobalTheory.KeyComp

namespace GlobalTheory

theorem keyPB_trans : ∀ (R R' R'' : Type) [CommRing R] [CommRing R'] [CommRing R''] (x : KeyIn R) (x' : KeyIn R') (x'' : KeyIn R'') (f : R →+* R') (f' : R' →+* R''), KeyPB x' x f → KeyPB x'' x' f' → KeyPB x'' x (f'.comp f) := by
  intro R R' R'' _ _ _ x x' x'' f f' H H'
  obtain ⟨φ, he, w, hg, F, hp, hw, hr, hs, hF, hε, hv⟩ := H
  obtain ⟨φ', he', w', hg', F', hp', hw', hr', hs', hF', hε', hv'⟩ := H'
  have g := (isGen_iff w).1 hw
  have g' := (isGen_iff w').1 hw'
  obtain ⟨w'', T⟩ := exists_comp x'.P.isLB w w' g g' x.P.isLB x''.P.isLB
  have he'' : eSec x''.P.A ≫ φ' ≫ φ = spMap (f'.comp f) ≫ eSec x.P.A := by
    rw [← Category.assoc, he', Category.assoc, he, spMap_comp, Category.assoc]
  refine ⟨φ' ≫ φ, he'', w'', hg'.trans hg, F'.comp F, (hp'.comp hp).congr (spMap_comp f f').symm rfl,
    (isGen_iff w'').2 (T.pgen_comp x'.P.isLB g g'), ?_, ?_, fun a => ?_, ?_, fun i => ?_⟩
  · have r₀ := (maps_iff w _ (fun _ => eSec x.P.A) _ x'.rig x.rig (spMap f) _
      (rigPull_le φ (spMap f) he x.P.L) (fun _ => rfl)).1 hr
    have r₁ := (maps_iff w' _ (fun _ => eSec x'.P.A) _ x''.rig x'.rig (spMap f') _
      (rigPull_le φ' (spMap f') he' x'.P.L) (fun _ => rfl)).1 hr'
    have r₂ := T.pmaps_comp x'.P.isLB (fun _ => he') r₀ r₁
    rw [← spMap_comp] at r₂
    exact (maps_iff w'' _ (fun _ => eSec x.P.A) _ x''.rig x.rig (spMap (f'.comp f)) _
      (rigPull_le (φ' ≫ φ) (spMap (f'.comp f)) he'' x.P.L) (fun _ => rfl)).2 r₂
  · refine KeyPow.appLE_eq_of_stalk w'' x.th x''.th fun z j k hj hk => ?_
    obtain ⟨i, hi⟩ := exists_chart x'.P.isLB (φ' z)
    have a := KeyComp.stalk_of_appLE_eq w x.th x'.th hs (𝟙 _ ≫ φ') z j i hj hi
    have b := KeyComp.stalk_of_appLE_eq w' x'.th x''.th hs' (𝟙 _) z i k hi hk
    rw [T _ (𝟙 _) z j i k hj hi hk, ← Category.assoc, a, b, Units.val_mul, _root_.mul_assoc]
  · rw [RingHom.comp_apply, hF, hF', RingHom.comp_apply]
  · rw [RingHom.comp_apply, hε, hε']
  · rw [← Category.assoc, hv', Category.assoc, hv, spMap_comp, Category.assoc]
    rfl

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.MemNonzeroLocusConstMul
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KeyNormalExists

def constMul {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) {L : LB X} (a : R) (s : L.Sec) : L.Sec where
  f j := constFn p _ a * s.f j
  compat j k := by
    rw [map_mul, map_mul, ThetaOnto.res_constFn, ThetaOnto.res_constFn, s.compat j k]
    ring

theorem mem_nonzeroLocus_constMul {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) {L : LB X} {a : R}
    (ha : IsUnit a) (s : L.Sec) {z : X} (hz : z ∈ Out.nonzeroLocus s) : z ∈ Out.nonzeroLocus (constMul p a s) := by
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hz
  refine TopologicalSpace.Opens.mem_iSup.2 ⟨i, ?_⟩
  have hu : IsUnit (constFn p (L.U i) a) := (ha.map _).map _
  change z ∈ X.basicOpen (constFn p (L.U i) a * s.f i)
  rw [Scheme.basicOpen_mul, Scheme.basicOpen_of_isUnit _ hu]
  exact ⟨X.basicOpen_le _ hi, hi⟩

theorem isFn_constMul {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g) (a : ℂ) {s : L.Sec}
    {θ : (Fin g → ℂ) → ℂ} (h : u.IsFn s θ) : u.IsFn (constMul A.hom a s) (fun z => a * θ z) := by
  intro i z hz
  change valAt' _ _ (constFn A.hom (L.U i) a * s.f i) = _
  rw [valAt'_mul, valAt'_constFn _ _ (Over.w (u.ex z)) _ _ hz, h i z hz, _root_.mul_assoc]

theorem exists_normalAt_one (x : KeyIn ℂ) {τ M : Matrix (Fin x.P.g) (Fin x.P.g) ℂ} {a b : Fin x.P.g → ℂ} {c : ℂ}
    (hc : c ≠ 0) (hM : M.det ≠ 0) (h : KeyPow.NormalAt x τ M a b c) :
    ∃ th hth v hv, KeyPow.NormalAt ⟨x.P, x.g_pos, x.rig, x.rig_gen, th, hth, v, hv⟩ τ 1 a b 1 := by
  obtain ⟨u, h₁, h₂, h₃, h₄, h₅, h₆⟩ := h
  have := x.P.isAb.comm
  obtain ⟨hex, -, -, -, hb⟩ := LieComb.lieComb_algebra ℂ x.P.A x.P.g x.v x.basis.1
  choose v hv using fun i => (hex (M⁻¹ i)).exists
  refine ⟨constMul x.P.A.hom c⁻¹ x.th, fun s => ?_, v,
    (hb M⁻¹ v x.basis hv).2 (Matrix.isUnit_nonsing_inv_det M hM.isUnit), u, h₁, h₂, h₃, h₄, ?_, fun i => ?_⟩
  · obtain ⟨z, hz, hz'⟩ := x.th_ne s
    exact ⟨z, hz, mem_nonzeroLocus_constMul _ (inv_ne_zero hc).isUnit _ hz'⟩
  · have := isFn_constMul u c⁻¹ h₅
    simpa only [inv_mul_cancel_left₀ hc, _root_.one_mul] using this
  · have := UnifDifferential.isDiff_of_isLieComb _ _ _ _ u _ x.v (M⁻¹ i) (v i) x.basis.1 h₆ (hv i)
    have e : ∑ j, M⁻¹ i j • (2 * Real.pi * Complex.I : ℂ)⁻¹ • M j =
        (2 * Real.pi * Complex.I : ℂ)⁻¹ • (1 : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) i := by
      rw [← Matrix.nonsing_inv_mul M hM.isUnit]
      funext k
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.mul_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [e] at this
    exact this

theorem exists_normalAt :
    ThetaUnifAV → ∀ x : KeyIn ℂ, (∃ (τ M : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (a b : Fin x.P.g → ℂ) (c : ℂ), GlobalTheory.KeyPow.charHalf x.P.g a b ∧ c ≠ 0 ∧ M.det ≠ 0 ∧ GlobalTheory.KeyPow.NormalAt x τ M a b c) ∧ ∃ (th : x.P.L.Sec) (hth : _) (v : _) (hv : _) (τ : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (a b : Fin x.P.g → ℂ), GlobalTheory.KeyPow.charHalf x.P.g a b ∧ GlobalTheory.KeyPow.NormalAt ⟨x.P, x.g_pos, x.rig, x.rig_gen, th, hth, v, hv⟩ τ 1 a b 1 := by
  intro hU x
  obtain ⟨u, Hm, χ, -, hA, hR, hd, -⟩ := hU x.P x.rig x.rig_gen
  choose W hW using fun i => (hd _ (x.basis.1 i)).exists
  obtain ⟨θ, hθ⟩ := KeyPow.exists_isFn x.P.isLB u x.th
  obtain ⟨Fd, hF⟩ := KeyPow.exists_isAddFundamentalDomain u
  obtain ⟨u', τ, M, a, b, c, h₁, h₂, ha, hb, h₃, h₄, hc, h₅, hM, h₆, -⟩ :=
    keyIn_normal_form_and_archimedean_constant hU x u Hm W χ θ Fd _ _ hA hR hθ hW hF rfl rfl
  have hN : KeyPow.NormalAt x τ M a b c := ⟨u', h₁, h₂, h₃, h₄, h₅, h₆⟩
  obtain ⟨th, hth, v, hv, h⟩ := exists_normalAt_one x hc hM hN
  exact ⟨⟨τ, M, a, b, c, ⟨ha, hb⟩, hc, hM, hN⟩, th, hth, v, hv, τ, a, b, ⟨ha, hb⟩, h⟩

end GlobalTheory.KeyNormalExists
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.RigidifiedSymDescendToSubring
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa

noncomputable section

namespace GlobalTheory.RigSymSubring

open GlobalTheory.CechPic

theorem pic_descends (S : Type) [CommRing S] (R₀ : Subring S) (X X₀ : Scheme.{0}) (f : X ⟶ Sp S)
    (f₀ : X₀ ⟶ Sp R₀) (π : X ⟶ X₀) [QuasiCompact f₀] [QuasiSeparated f₀] (c d : Pic X₀)
    (H : IsPullback π f f₀ (spMap R₀.subtype)) (e : pull π c = pull π d) :
    ∃ F : Finset S, ∀ (R₁ : Subring S) (h : R₀ ≤ R₁), (F : Set S) ⊆ R₁ →
      ∀ (X₁ : Scheme.{0}) (f₁ : X₁ ⟶ Sp R₁) (π₁ : X₁ ⟶ X₀),
        IsPullback π₁ f₁ f₀ (spMap (Subring.inclusion h)) → pull π₁ c = pull π₁ d := by
  obtain ⟨M, hM, rfl⟩ := cls_surj c
  obtain ⟨N, hN, rfl⟩ := cls_surj d
  obtain ⟨F, hF⟩ := GlobalTheory.T.lineBundleIso_descends_to_subring_of_finset S R₀ X X₀ f f₀ π M N H hM hN
    ((cls_eq_iff (pull_isLB hM π) (pull_isLB hN π)).1 e)
  exact ⟨F, fun R₁ h hR X₁ f₁ π₁ H₁ =>
    (cls_eq_iff (pull_isLB hM π₁) (pull_isLB hN π₁)).2 (hF R₁ h hR X₁ f₁ π₁ H₁)⟩

variable {T : Scheme.{0}} {A : Over T} [GrpObj A] {L : LB A.left}

theorem rigidified_iff (hL : L.IsLB) : Out.Rigidified A L ↔ pull (eSec A) (cls L hL) = 0 :=
  (cls_eq_zero_iff (pull_isLB hL _)).symm

theorem gen_iff (hL : L.IsLB) {Y : Scheme.{0}} (r : Y ⟶ A.left) :
    (∃ t : LB.Gen (LB.LinComb L (K := Fin 2) ![r ≫ (GrpObj.inv : A ⟶ A).left, r] ![1, -1]), t.IsGen) ↔
      pull r (pull (GrpObj.inv : A ⟶ A).left (cls L hL)) = pull r (cls L hL) := by
  rw [← cls_eq_zero_iff (LB.isLB_linComb hL _ _), cls_linComb hL, Fin.sum_univ_two, ← pull_comp]
  simp [← sub_eq_add_neg, sub_eq_zero]

theorem sym_of_cls (hL : L.IsLB) (e : pull (GrpObj.inv : A ⟶ A).left (cls L hL) = cls L hL) : Out.Sym A L :=
  fun _ => ⟨⊤, trivial, (gen_iff hL _).2 (by rw [e])⟩

theorem cls_of_sym {S : Type} [CommRing S] [IsLocalRing S] {A : Over (Sp S)} [GrpObj A] {L : LB A.left}
    (hL : L.IsLB) (hs : Out.Sym A L) : pull (GrpObj.inv : A ⟶ A).left (cls L hL) = cls L hL := by
  obtain ⟨U, hU, ht⟩ := hs (IsLocalRing.closedPoint S)
  obtain rfl : U = ⊤ := (IsLocalRing.closedPoint_mem_iff U).1 hU
  have i : ∀ c : Pic A.left, pull (inv (A.hom ⁻¹ᵁ ⊤).ι (I := inferInstanceAs (IsIso A.left.topIso.hom)))
      (pull (A.hom ⁻¹ᵁ ⊤).ι c) = c := fun c => by rw [← pull_comp, IsIso.inv_hom_id, pull_id]
  exact (i _).symm.trans ((congrArg _ ((gen_iff hL _).1 ht)).trans (i _))

end GlobalTheory.RigSymSubring

namespace GlobalTheory

open GlobalTheory.CechPic GlobalTheory.RigSymSubring

theorem rigidified_sym_descend_to_subring : ∀ (S : Type) [CommRing S] [IsLocalRing S] (R₀ : Subring S) (P : Out.PolAV (Sp S)) (A₀ : Over (Sp R₀)) [GrpObj A₀] (φ : P.A.left ⟶ A₀.left) (L₀ : LB A₀.left), IsAbelianScheme A₀ → L₀.IsLB → IsGrpPullback P.A A₀ (spMap R₀.subtype) φ → LBIso P.L (L₀.pull φ) → ∃ F : Finset S, ∀ (R₁ : Subring S) (h : R₀ ≤ R₁), (F : Set S) ⊆ R₁ → ∀ (A₁ : Over (Sp R₁)) [GrpObj A₁] (π : A₁.left ⟶ A₀.left), IsGrpPullback A₁ A₀ (spMap (Subring.inclusion h)) π → Out.Rigidified A₁ (L₀.pull π) ∧ Out.Sym A₁ (L₀.pull π) := by
  classical
  intro S _ _ R₀ P A₀ _ φ L₀ hA hL H hw
  have := hA.proper
  have hc : cls P.L P.isLB = pull φ (cls L₀ hL) := (cls_eq_iff P.isLB (pull_isLB hL φ)).2 hw
  have e₁ : pull (spMap R₀.subtype) (pull (X := A₀.left) (Y := Sp R₀) (eSec A₀) (cls L₀ hL)) =
      pull (spMap R₀.subtype) 0 := by
    have h₁ := (rigidified_iff P.isLB).1 P.rigid
    rw [hc, ← pull_comp, PolBaseChange.eSec_comm H] at h₁
    exact (pull_comp _ _ _).symm.trans (h₁.trans (map_zero _).symm)
  have e₂ : pull φ (pull (GrpObj.inv : A₀ ⟶ A₀).left (cls L₀ hL)) = pull φ (cls L₀ hL) := by
    have h₂ := cls_of_sym P.isLB P.sym
    rwa [hc, ← pull_comp, PolBaseChange.inv_comm H, pull_comp] at h₂
  obtain ⟨F₁, h₁⟩ := pic_descends S R₀ (Sp S) (Sp R₀) (𝟙 _) (𝟙 _) (spMap R₀.subtype) _ _
    (IsPullback.of_vert_isIso ⟨by simp⟩) e₁
  obtain ⟨F₂, h₂⟩ := pic_descends S R₀ _ _ P.A.hom A₀.hom φ _ _ H.1 e₂
  refine ⟨F₁ ∪ F₂, fun R₁ h hF A₁ _ π H₁ => ?_⟩
  rw [Finset.coe_union, Set.union_subset_iff] at hF
  have a := h₁ R₁ h hF.1 (Sp R₁) (𝟙 _) (spMap (Subring.inclusion h)) (IsPullback.of_vert_isIso ⟨by simp⟩)
  have b := h₂ R₁ h hF.2 _ A₁.hom π H₁.1
  refine ⟨(rigidified_iff (pull_isLB hL π)).2 ?_, sym_of_cls (pull_isLB hL π) ?_⟩
  · rw [cls_pull hL, ← pull_comp, PolBaseChange.eSec_comm H₁]
    exact (pull_comp _ _ _).trans (a.trans (map_zero _))
  · rw [cls_pull hL, ← pull_comp, PolBaseChange.inv_comm H₁, pull_comp, b]

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KeyPBId
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem keyPB_id : ∀ (R : Type) [CommRing R] (x : KeyIn R), KeyPB x x (RingHom.id R) :=
  fun _ _ x => GlobalTheory.KeyPow.keyPB_refl x

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsIsGrpPullbackPow
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.KeyPow

section Grp

variable {S S' : Scheme.{0}} {G H : Over S} {G' H' : Over S'} [GrpObj G] [GrpObj H] [GrpObj G'] [GrpObj H'] {j : ℕ}

theorem pow_left_ext (p : Out.IsPowGrp H G j) {T : Scheme.{0}} {a b : T ⟶ H.left} (h₀ : a ≫ H.hom = b ≫ H.hom)
    (h : ∀ i, a ≫ (p.pr i).left = b ≫ (p.pr i).left) : a = b := by
  let a' : Over.mk (a ≫ H.hom) ⟶ H := Over.homMk a rfl
  let b' : Over.mk (a ≫ H.hom) ⟶ H := Over.homMk b h₀.symm
  have : a' = b' := p.lim.hom_ext fun ⟨i⟩ => Over.OverMorphism.ext (h i)
  exact congrArg (fun z => z.left) this

theorem pow_left_lift (p : Out.IsPowGrp H G j) {T : Scheme.{0}} (s : T ⟶ S) (c : Fin j → (T ⟶ G.left))
    (hc : ∀ i, c i ≫ G.hom = s) : ∃ a : T ⟶ H.left, a ≫ H.hom = s ∧ ∀ i, a ≫ (p.pr i).left = c i := by
  let c' : Fin j → (Over.mk s ⟶ G) := fun i => Over.homMk (c i) (hc i)
  let a := p.lim.lift (Fan.mk (Over.mk s) c')
  exact ⟨a.left, Over.w a, fun i => congrArg (fun z => z.left) (p.lim.fac (Fan.mk (Over.mk s) c') ⟨i⟩)⟩

theorem exists_isGrpPullback_pow {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ)
    (p : Out.IsPowGrp H G j) (p' : Out.IsPowGrp H' G' j) :
    ∃ ψ : H'.left ⟶ H.left, IsGrpPullback H' H f ψ ∧ ∀ i, (p'.pr i).left ≫ φ = ψ ≫ (p.pr i).left := by
  obtain ⟨ψ, hψ₀, hψ⟩ := pow_left_lift p (H'.hom ≫ f) (fun i => (p'.pr i).left ≫ φ) fun i => by
    rw [Category.assoc, h.1.w, ← Category.assoc, Over.w]
  have key : ∀ (T : Scheme.{0}) (a : T ⟶ H.left) (b : T ⟶ S'), a ≫ H.hom = b ≫ f →
      ∃ m : T ⟶ H'.left, m ≫ ψ = a ∧ m ≫ H'.hom = b := fun T a b hab => by
    have sq : ∀ i, (a ≫ (p.pr i).left) ≫ G.hom = b ≫ f := fun i => by rw [Category.assoc, Over.w, hab]
    obtain ⟨m, hm₀, hm⟩ := pow_left_lift p' b (fun i => h.1.lift _ _ (sq i)) fun i => h.1.lift_snd _ _ _
    refine ⟨m, pow_left_ext p ?_ fun i => ?_, hm₀⟩
    · rw [Category.assoc, hψ₀, ← Category.assoc, hm₀, hab]
    · rw [Category.assoc, hψ, ← Category.assoc, hm, h.1.lift_fst]
  have ext : ∀ (T : Scheme.{0}) (m m' : T ⟶ H'.left), m ≫ ψ = m' ≫ ψ → m ≫ H'.hom = m' ≫ H'.hom → m = m' :=
    fun T m m' e₁ e₂ => pow_left_ext p' e₂ fun i => h.1.hom_ext
      (by rw [Category.assoc, Category.assoc, ← hψ, ← Category.assoc, e₁, Category.assoc])
      (by rw [Category.assoc, Category.assoc, Over.w, e₂])
  choose l hl₁ hl₂ using key
  refine ⟨ψ, ⟨⟨⟨hψ₀⟩, ⟨PullbackCone.IsLimit.mk _ (fun s => l _ s.fst s.snd s.condition) (fun s => hl₁ _ _ _ _)
    (fun s => hl₂ _ _ _ _) fun s m h₁ h₂ => ext _ _ _ (h₁.trans (hl₁ _ _ _ _).symm) (h₂.trans (hl₂ _ _ _ _).symm)⟩⟩,
    fun T x y x₀ y₀ hx hy => pow_left_ext p ?_ fun i => ?_⟩, fun i => (hψ i).symm⟩
  · rw [Over.w (x₀ * y₀), Category.assoc, hψ₀, ← Category.assoc, Over.w (x * y)]; rfl
  · have := p.hom i
    have := p'.hom i
    rw [Category.assoc, hψ, ← Category.assoc, ← Over.comp_left, ← Over.comp_left, MonObj.mul_comp, MonObj.mul_comp]
    refine h.2 T _ _ _ _ ?_ ?_
    · rw [Over.comp_left, Over.comp_left, hx, Category.assoc, hψ, Category.assoc]
    · rw [Over.comp_left, Over.comp_left, hy, Category.assoc, hψ, Category.assoc]

end Grp

section Bundle

variable {X X' Y Y' : Scheme.{0}} {J : Type} [Fintype J] {L : LB X} {L' : LB X'} {φ : X' ⟶ X} {ψ : Y' ⟶ Y}
  {p : J → (Y ⟶ X)} {p' : J → (Y' ⟶ X')}

theorem mem_wchart_iff {y : Y} {jj : J → L.ι} : y ∈ LB.wchart L p jj ↔ ∀ i, p i y ∈ L.U (jj i) := Set.mem_iInter

theorem exists_boxIso (hc : ∀ i, p' i ≫ φ = ψ ≫ p i) (w : LB.Iso L' (L.pull φ)) (hw : PGen w) :
    ∃ u : LB.Iso (LB.LinComb L' p' (fun _ => 1)) ((LB.LinComb L p (fun _ => 1)).pull ψ), PGen u ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (jj : J → L.ι) (jj' : J → L'.ι), ψ (r z) ∈ LB.wchart L p jj →
        r z ∈ LB.wchart L' p' jj' → gw u r z jj jj' = ∏ i, gw w (r ≫ p' i) z (jj i) (jj' i) := by
  have le : ∀ (q : (PUnit → J → L.ι) × (J → L'.ι)) (i : J),
      ((LB.LinComb L p (fun _ => 1)).pull ψ).U q.1 ⊓ LB.wchart L' p' q.2 ≤
        p' i ⁻¹ᵁ ((L.pull φ).U (fun _ => q.1 PUnit.unit i) ⊓ L'.U (q.2 i)) := fun q i y hy =>
    ⟨mem_pull.2 (by
      have := mem_wchart_iff.1 (mem_pull.1 hy.1) i
      rw [pt_eq hc] at this; exact this), mem_wchart_iff.1 hy.2 i⟩
  let u : LB.Iso (LB.LinComb L' p' (fun _ => 1)) ((LB.LinComb L p (fun _ => 1)).pull ψ) :=
    ⟨fun q => ∏ i, res (le q i) (pullU (p' i) _ (w.s (fun _ => q.1 PUnit.unit i, q.2 i)))⟩
  have hu : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (jj : J → L.ι) (jj' : J → L'.ι), ψ (r z) ∈ LB.wchart L p jj →
      r z ∈ LB.wchart L' p' jj' → gw u r z jj jj' = ∏ i, gw w (r ≫ p' i) z (jj i) (jj' i) := by
    intro Z r z jj jj' h₁ h₂
    have hm : r z ∈ ((LB.LinComb L p (fun _ => 1)).pull ψ).U (fun _ => jj) ⊓ LB.wchart L' p' jj' := ⟨mem_pull.2 h₁, h₂⟩
    exact (map_prod _ _ _).trans (Finset.prod_congr rfl fun i _ =>
      (gm_res r z (le (fun _ => jj, jj') i) hm _).trans (gm_pull r (p' i) z _ (le (fun _ => jj, jj') i hm) _))
  refine ⟨u, fun Z r z a a' b b' ha ha' hb hb' => ?_, hu⟩
  have m : ∀ (c : J → L.ι), ψ (r z) ∈ LB.wchart L p c → ∀ i, φ ((r ≫ p' i) z) ∈ L.U (c i) := fun c h i => by
    have := mem_wchart_iff.1 h i
    rw [pt_eq hc] at this; exact this
  rw [hu Z r z a b ha hb, hu Z r z a' b' ha' hb']
  refine Eq.trans ?_ (congrArg₂ (fun s t => s * t⁻¹ * _) (gm_linComb L p _ (r ≫ ψ) z a a' ha ha')
    (gm_linComb L' p' _ r z b b' hb hb')).symm
  rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [hw Z (r ≫ p' i) z (a i) (a' i) (b i) (b' i) (m a ha i) (m a' ha' i) (mem_wchart_iff.1 hb i)
    (mem_wchart_iff.1 hb' i), zpow_one, zpow_one, Category.assoc, Category.assoc, hc]

theorem exists_conjIso {B M : LB Y} {B' M' : LB Y'} (hB : B.IsLB) (hM : M.IsLB) (hB' : B'.IsLB) (hM' : M'.IsLB)
    (u : LB.Iso B' (B.pull ψ)) (hu : PGen u) (a : LB.Iso M B) (ha : a.IsGen) (a' : LB.Iso M' B') (ha' : a'.IsGen) :
    ∃ W : LB.Iso M' (M.pull ψ), PGen W ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) c c' b b', ψ (r z) ∈ B.U c →
      r z ∈ B'.U c' → ψ (r z) ∈ M.U b → r z ∈ M'.U b' →
      gv a (r ≫ ψ) z c b * gw W r z b b' = gw u r z c c' * gv a' r z c' b' := by
  have H : ∀ χ : Y' ⟶ Y, 𝟙 Y' ≫ ψ = χ → ∃ v : LB.Iso M' (B.pull χ), PGen v ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) c c' b', ψ (r z) ∈ B.U c → r z ∈ B'.U c' → r z ∈ M'.U b' →
        gw v r z c b' = gw u r z c c' * gv a' r z c' b' := by
    rintro _ rfl
    obtain ⟨v, T⟩ := exists_comp hB' u (isoPullId a' rfl) hu (isoPullId_pgen ha' rfl) hB hM'
    refine ⟨v, T.pgen_comp hB' hu (isoPullId_pgen ha' rfl), fun Z r z c c' b' h₁ h₂ h₃ => ?_⟩
    rw [T Z r z c c' b' h₁ h₂ h₃, Category.comp_id, gw_isoPullId a' rfl r z c' b' h₂ h₃]
  obtain ⟨v, hv, hv'⟩ := H (ψ ≫ 𝟙 Y) ((Category.id_comp _).trans (Category.comp_id _).symm)
  obtain ⟨W, T⟩ := exists_cancel hB (isoPullId a rfl) v (isoPullId_pgen ha rfl) hv hM hM'
  refine ⟨W, T.pgen_cancel hB (isoPullId_pgen ha rfl) hv, fun Z r z c c' b b' h₁ h₂ h₃ h₄ => ?_⟩
  rw [← hv' Z r z c c' b' h₁ h₂ h₄, T Z r z c b b' h₁ h₃ h₄, gw_isoPullId a rfl (r ≫ ψ) z c b h₁ h₃]

end Bundle

section Stalk

variable {S : Scheme.{0}} {G H : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj H] [IsCommMonObj H] {j : ℕ}

omit [IsCommMonObj G] [IsCommMonObj H] in
theorem eSec_pr (p : Out.IsPowGrp H G j) (i : Fin j) : eSec H ≫ (p.pr i).left = eSec G := by
  have := p.hom i
  rw [eSec, eSec, ← Over.comp_left, IsMonHom.one_hom]

theorem gm_boxRig (p : Out.IsPowGrp H G j) (L : LB G.left) (r : LB.Gen (L.pull (eSec G))) {Z : Scheme.{0}}
    (t : Z ⟶ (𝟙_ (Over S)).left) (z : Z) (c : L.ι) (hc : eSec G (t z) ∈ L.U c) :
    gm t z _ ((Out.boxRig p L r).s (fun _ _ => c)) =
      ∏ _i : Fin j, gm t z (LB.wchart L (fun _ : PUnit => eSec G) (fun _ => c)) (r.s (fun _ => c)) := by
  have h₁ : ∀ i, (p.pr i).left (eSec H (t z)) ∈ L.U c := fun i =>
    (congrArg (fun q => q (t z) ∈ L.U c) (eSec_pr p i)).mpr hc
  have hm : t z ∈ ((Out.boxLB L p.pr).pull (eSec H)).U (fun _ _ => c) := mem_pull.2 (mem_wchart_iff.2 h₁)
  refine (map_prod _ _ (Finset.univ : Finset (Fin j))).trans (Finset.prod_congr rfl fun i _ => ?_)
  refine (gm_res t z _ hm _).trans ?_
  have hm' : t z ∈ ((L.pull (p.pr i).left).pull (eSec H)).U (fun _ _ => c) := mem_pull.2 (mem_pull.2 (h₁ i))
  refine (gm_res t z _ hm' _).trans ((gm_pull t (𝟙 _) z _ (mem_pull.2 hc) _).trans ?_)
  rw [Category.comp_id]
  rfl

theorem gs_box_of_appLE {X Y : Scheme.{0}} {J : Type} [Fintype J] {L : LB X} {M : LB Y} {p : J → (Y ⟶ X)}
    (a : LB.Iso M (LB.LinComb L p (fun _ => 1))) (s : L.Sec) (σ : M.Sec)
    (H : ∀ (jj : J → L.ι) (b : M.ι) (h : ∀ i, (LB.LinComb L p (fun _ => 1)).U jj ⊓ M.U b ≤ p i ⁻¹ᵁ L.U (jj i)),
      ∏ i, ((p i).appLE _ _ (h i)).hom (s.f (jj i)) =
        (show Γ(Y, (LB.LinComb L p (fun _ => 1)).U jj ⊓ M.U b) from (a.s (jj, b)).val) * resG _ inf_le_right (σ.f b))
    {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (jj : J → L.ι) (b : M.ι) (h₁ : r z ∈ LB.wchart L p jj) (h₂ : r z ∈ M.U b) :
    ∏ i, gs (r ≫ p i) z _ (s.f (jj i)) = (gv a r z jj b).val * gs r z _ (σ.f b) := by
  have hm : r z ∈ (LB.LinComb L p (fun _ => 1)).U jj ⊓ M.U b := ⟨h₁, h₂⟩
  have e := congrArg (gs r z _) (H jj b fun i => inf_le_left.trans (LB.wchart_le L p jj i))
  rw [DVR.gs_prod r z _ hm, gs_mul r z _ hm, gs_res r z _ hm] at e
  exact (Finset.prod_congr rfl fun i _ => (gs_appLE _ _ _ _ r z hm _).symm).trans
    (e.trans (congrArg (· * _) (gs_unit r z _ hm _)))

theorem gs_pull_of_appLE {X X' : Scheme.{0}} {L : LB X} {L' : LB X'} {φ : X' ⟶ X} (w : LB.Iso L' (L.pull φ)) (s : L.Sec)
    (s' : L'.Sec) (H : ∀ (c : (L.pull φ).ι) (i : L'.ι) (h : (L.pull φ).U c ⊓ L'.U i ≤ φ ⁻¹ᵁ L.U (c PUnit.unit)),
      (φ.appLE _ _ h).hom (s.f (c PUnit.unit)) =
        (show Γ(X', (L.pull φ).U c ⊓ L'.U i) from (w.s (c, i)).val) * resG _ inf_le_right (s'.f i))
    {Z : Scheme.{0}} (r : Z ⟶ X') (z : Z) (c : L.ι) (i : L'.ι) (h₁ : φ (r z) ∈ L.U c) (h₂ : r z ∈ L'.U i) :
    gs (r ≫ φ) z _ (s.f c) = (gw w r z c i).val * gs r z _ (s'.f i) := by
  have hm : r z ∈ (L.pull φ).U (fun _ => c) ⊓ L'.U i := ⟨mem_pull.2 h₁, h₂⟩
  have e := congrArg (gs r z _) (H (fun _ => c) i fun y hy => mem_pull.1 hy.1)
  rw [gs_mul r z _ hm, gs_res r z _ hm] at e
  exact (gs_appLE _ _ _ _ r z hm _).symm.trans (e.trans (congrArg (· * _) (gs_unit r z _ hm _)))

end Stalk

theorem keyPB_of_isKeyPow : ∀ (R R' : Type) [CommRing R] [CommRing R'] (f : R →+* R') (x y : KeyIn R) (x' y' : KeyIn R')
    (j : ℕ), KeyPB x' x f → GlobalTheory.KeyPow.IsKeyPow y x j → GlobalTheory.KeyPow.IsKeyPow y' x' j → KeyPB y' y f := by
  rintro R R' _ _ f x y x' y' j ⟨φ, he, w, hg, F, hφ, hw, hr, hth, hF₁, hF₂, hv⟩ ⟨p, hp, pr, pth, pv⟩
    ⟨p', hp', pr', pth', pv'⟩
  have := x.P.isAb.comm
  have := y.P.isAb.comm
  have := x'.P.isAb.comm
  have := y'.P.isAb.comm
  obtain ⟨ψ, hψ, hc⟩ := exists_isGrpPullback_pow hφ p.toIsPowGrp p'.toIsPowGrp
  obtain ⟨u, hu, hu'⟩ := exists_boxIso hc w ((isGen_iff w).1 hw)
  obtain ⟨W, hW, hW'⟩ := exists_conjIso (DVR.linComb_isLB _ x.P.isLB _ _) y.P.isLB (DVR.linComb_isLB _ x'.P.isLB _ _)
    y'.P.isLB u hu p.w p.w_gen p'.w p'.w_gen
  have heψ : eSec y'.P.A ≫ ψ = spMap f ≫ eSec y.P.A := PolBaseChange.eSec_comm hψ
  have hgy : y'.P.g = y.P.g := by rw [← hp, ← hp', hg]
  have hFe : spMap F ≫ (epsR R).hom = (epsR R').hom ≫ spMap f := by
    show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext hF₁
  refine ⟨ψ, heψ, W, hgy, F, hψ, (isGen_iff W).2 hW, ?_, appLE_eq_of_stalk W y.th y'.th fun z b b' hb hb' => ?_,
    hF₁, hF₂, fun n => ?_⟩
  · refine (maps_iff W _ (fun _ => eSec y.P.A) _ y'.rig y.rig (spMap f) _ (rigPull_le ψ _ heψ y.P.L) (fun _ => rfl)).2 ?_
    have hx := (maps_iff w _ (fun _ => eSec x.P.A) _ x'.rig x.rig (spMap f) _ (rigPull_le φ _ he x.P.L)
      (fun _ => rfl)).1 hr
    intro Z r z b b' hb hb'
    obtain ⟨c, hcx⟩ := exists_chart x.P.isLB (φ (eSec x'.P.A (r z)))
    obtain ⟨c', hcx'⟩ := exists_chart x'.P.isLB (eSec x'.P.A (r z))
    have hc₁ : eSec x.P.A ((r ≫ spMap f) z) ∈ x.P.L.U c := (congrArg (fun q => q (r z) ∈ x.P.L.U c) he).mp hcx
    have hb₁ : eSec y.P.A ((r ≫ spMap f) z) ∈ y.P.L.U (b PUnit.unit) :=
      (congrArg (fun q => q (r z) ∈ y.P.L.U (b PUnit.unit)) heψ).mp (hb PUnit.unit)
    have m₁ : eSec y.P.A ((r ≫ spMap f) z) ∈ (Out.boxLB x.P.L p.pr).U (fun _ => c) := mem_wchart_iff.2 fun i =>
      (congrArg (fun q => q ((r ≫ spMap f) z) ∈ x.P.L.U c) (eSec_pr p.toIsPowGrp i)).mpr hc₁
    have m₂ : eSec y'.P.A (r z) ∈ (Out.boxLB x'.P.L p'.pr).U (fun _ => c') := mem_wchart_iff.2 fun i =>
      (congrArg (fun q => q (r z) ∈ x'.P.L.U c') (eSec_pr p'.toIsPowGrp i)).mpr hcx'
    have m₃ : ψ ((r ≫ eSec y'.P.A) z) ∈ (Out.boxLB x.P.L p.pr).U (fun _ => c) :=
      (congrArg (fun q => q (r z) ∈ (Out.boxLB x.P.L p.pr).U (fun _ => c)) heψ).mpr m₁
    have e₁ := (gm_boxRig p.toIsPowGrp x.P.L x.rig (r ≫ spMap f) z c hc₁).symm.trans
      (gm_maps_pt pr (r ≫ spMap f) z (fun _ => c) (b PUnit.unit) m₁ hb₁)
    have e₂ := (gm_boxRig p'.toIsPowGrp x'.P.L x'.rig r z c' hcx').symm.trans
      (gm_maps_pt pr' r z (fun _ => c') (b' PUnit.unit) m₂ (hb' PUnit.unit))
    have e₃ := hx Z r z (fun _ => c) (fun _ => c') (fun _ => hcx) (fun _ => hcx')
    have e₄ := hW' Z (r ≫ eSec y'.P.A) z (fun _ => c) (fun _ => c') (b PUnit.unit) (b' PUnit.unit) m₃ m₂
      (hb PUnit.unit) (hb' PUnit.unit)
    rw [hu' Z (r ≫ eSec y'.P.A) z _ _ m₃ m₂, Category.assoc, heψ, ← Category.assoc] at e₄
    simp only [Category.assoc, eSec_pr p'.toIsPowGrp] at e₄
    rw [Fintype.prod_unique, zpow_one] at e₃ ⊢
    rw [e₃, Finset.prod_mul_distrib, e₂, ← _root_.mul_assoc, Category.assoc] at e₁
    exact (mul_left_cancel (e₁.symm.trans ((congrArg (· * _) e₄.symm).trans (_root_.mul_assoc _ _ _))))
  · choose c hcx using fun i => exists_chart x.P.isLB (φ ((p'.pr i).left z))
    choose c' hcx' using fun i => exists_chart x'.P.isLB ((p'.pr i).left z)
    have m₁ : ψ z ∈ LB.wchart x.P.L (fun i => (p.pr i).left) c := mem_wchart_iff.2 fun i =>
      (congrArg (fun q => q z ∈ x.P.L.U (c i)) (hc i)).mp (hcx i)
    have m₂ : z ∈ LB.wchart x'.P.L (fun i => (p'.pr i).left) c' := mem_wchart_iff.2 hcx'
    have e₁ := gs_box_of_appLE p.w x.th y.th pth (𝟙 _ ≫ ψ) z c b m₁ hb
    have e₂ := gs_box_of_appLE p'.w x'.th y'.th pth' (𝟙 _) z c' b' m₂ hb'
    have e₃ := fun i => gs_pull_of_appLE w x.th x'.th hth (𝟙 _ ≫ (p'.pr i).left) z (c i) (c' i) (hcx i) (hcx' i)
    have e₄ := hW' _ (𝟙 _) z c c' b b' m₁ m₂ hb hb'
    rw [hu' _ (𝟙 _) z c c' m₁ m₂] at e₄
    have e₅ : ∀ i, (𝟙 _ ≫ ψ) ≫ (p.pr i).left = (𝟙 _ ≫ (p'.pr i).left) ≫ φ := fun i => by
      rw [Category.assoc, Category.assoc, hc]
    simp only [e₅, e₃] at e₁
    rw [Finset.prod_mul_distrib, e₂, ← Units.coe_prod, ← _root_.mul_assoc, ← Units.val_mul, ← e₄, Units.val_mul,
      _root_.mul_assoc] at e₁
    exact ((Units.mul_right_inj _).1 e₁).symm
  · obtain ⟨⟨i, k⟩, rfl⟩ : ∃ q : Fin j × Fin x'.P.g, (finProdFinEquiv q).cast hp' = n :=
      ⟨finProdFinEquiv.symm (n.cast hp'.symm), by rw [Equiv.apply_symm_apply]; rfl⟩
    have hn : ((finProdFinEquiv (i, k)).cast hp').cast hgy = (finProdFinEquiv (i, k.cast hg)).cast hp :=
      Fin.ext (by simp only [Fin.val_cast, finProdFinEquiv_apply_val, hg])
    rw [hn]
    refine pow_left_ext p.toIsPowGrp ?_ fun i' => ?_
    · rw [Category.assoc, hψ.1.w, ← Category.assoc, Over.w, Category.assoc, Over.w, hFe]
    · rw [Category.assoc, ← hc, ← Category.assoc, Category.assoc (spMap F), ← Over.comp_left, ← Over.comp_left, pv, pv']
      split_ifs
      · exact hv k
      · show ((epsR R').hom ≫ eSec x'.P.A) ≫ φ = spMap F ≫ (epsR R).hom ≫ eSec x.P.A
        rw [Category.assoc, he, ← Category.assoc, ← hFe, Category.assoc]

end GlobalTheory.KeyPow
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKeyPBOn
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa

namespace GlobalTheory.KeyTf

theorem isLieBasis_cast {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] {m n : ℕ} (e : m = n)
    {v : Fin n → (epsR R ⟶ G)} (hv : IsLieBasis v) : IsLieBasis (fun i : Fin m => v (i.cast e)) := by
  subst e
  exact hv

theorem exists_keyPB_on : ∀ (R R' : Type) [CommRing R] [CommRing R'] (f : R →+* R') (y : KeyIn R) (P' : Out.PolAV (Sp R')) (φ : P'.A.left ⟶ y.P.A.left) (hg : 1 ≤ P'.g), P'.g = y.P.g → IsGrpPullback P'.A y.P.A (spMap f) φ → LBIso P'.L (y.P.L.pull φ) → ∃ rig hr th hth v hv, KeyPB ⟨P', hg, rig, hr, th, hth, v, hv⟩ y f := by
  intro R R' _ _ f x P' φ hg e h ⟨w, hw₀⟩
  have hL' := P'.isLB
  have hw := (isGen_iff _).1 hw₀
  have he : eSec P'.A ≫ φ = spMap f ≫ eSec x.P.A := PolBaseChange.eSec_comm h
  have hr₀ : (rigPullOf φ (spMap f) he x.P.L x.rig).IsGen :=
    Out.LBxP.isGen_pullAlong x.P.L φ (spMap f) (fun _ : PUnit => eSec x.P.A) (fun _ => 1) (fun _ => eSec P'.A)
      (fun _ => he) x.rig x.rig_gen
  obtain ⟨rig, hr, hm⟩ := Transport.exists_transport (LB.isLB_pull hL' (eSec P'.A))
    (LB.isLB_pull (LB.isLB_pull x.P.isLB φ) (eSec P'.A))
    (LB.linCombIso w (K := PUnit) (fun _ => eSec P'.A) (fun _ => 1)) (DVR.linCombIso_isGen w hw₀ _ _) _ hr₀
  obtain ⟨th', hth'⟩ := sec_pull_down hw x.P.isLB hL' x.th
  have c₁ : IsCommMonObj x.P.A := x.P.isAb.comm
  have c₂ : IsCommMonObj P'.A := P'.isAb.comm
  obtain ⟨v', hb', hv'⟩ := exists_isLieBasis_baseChange R R' f x.P.A P'.A φ h x.P.isAb.smooth x.P.g x.v x.basis
  refine ⟨rig, hr, th', fun s => ?_, fun i => v' (i.cast e), isLieBasis_cast e hb',
    φ, he, w, e, Chart.dualMapR f, h, hw₀, hm,
    appLE_eq_of_stalk _ x.th th' (hth' _ (𝟙 _)), fun a => ?_, ?_, fun i => hv' _⟩
  · obtain ⟨z, hz, hz'⟩ := x.th_ne (spMap f s)
    obtain ⟨y, rfl, hy⟩ := Scheme.exists_preimage_of_isPullback h.1 z s hz
    obtain ⟨k, hk, u⟩ := (mem_nonzeroLocus _ _).1 hz'
    obtain ⟨k', hk'⟩ := exists_chart hL' y
    refine ⟨y, hy, (mem_nonzeroLocus _ _).2 ⟨k', hk', ?_⟩⟩
    have u₁ : IsUnit (gs φ y _ (x.th.f k)) := by rw [gs_stalkMap φ y _ hk]; exact u.map _
    have e' := hth' _ (𝟙 _) y k k' hk hk'
    rw [Category.id_comp] at e'
    exact isUnit_of_mul_isUnit_right (e' ▸ u₁)
  · ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  · ext <;> simp [Chart.dualMapR]

end GlobalTheory.KeyTf
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsIsKeyPow
section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KTrivBoxLBPowObj
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem kTriv_boxLB_powObj : ∀ (R : Type) [CommRing R] (P : Out.PolAV (Sp R)) (j : ℕ),
    Out.KTriv (Out.powObj P.A j) (Out.boxLB P.L (Out.powPr P.A (n := j))) := by
  intro R _ P j
  have : IsCommMonObj P.A := P.isAb.comm
  exact T.kTriv_external_tensor_power_lineBundle _ (Out.powObj P.A j) P.A j (Out.powIsPowGrp P.A j) P.L P.isLB P.ktriv

end GlobalTheory
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KeyPow

theorem exists_isKeyPow : ∀ (R : Type) [CommRing R] (x : KeyIn R) (j : ℕ), 1 ≤ j → ∃ y, GlobalTheory.KeyPow.IsKeyPow y x j := by
  intro R _ x j hj
  have := x.P.isAb.comm
  obtain ⟨hL, hS, hr⟩ := BoxPower.boxPower_basic R x.P j
  have hr' := hr x.rig x.rig_gen
  have hA : IsAbelianScheme (Out.powObj x.P.A j) := by
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hj
    exact AbelianSchemeGerms.isAbelianScheme_powObj x.P.A x.P.isAb n
  let P' : Out.PolAV (Sp R) :=
    { A := Out.powObj x.P.A j
      isAb := hA
      g := j * x.P.g
      smoothDim := powObj_smoothOfRelativeDimension_mul _ _ _ j x.P.smoothDim
      L := Out.boxLB x.P.L (Out.powPr x.P.A (n := j))
      isLB := hL
      rigid := ⟨_, hr'⟩
      sym := hS
      ample := relAmple_powObj_boxLB R x.P j
      ktriv := kTriv_boxLB_powObj R x.P j }
  obtain ⟨th, hth, hne⟩ := BoxSection.exists_boxSec _ _ _ j (Out.powIsPowGrp x.P.A j) x.P.L (fun _ => x.th) x.P.isLB
  obtain ⟨v, hv, hvp⟩ := PowLie.isLieBasis_pow R _ _ j x.P.g (Out.powIsPowGrp x.P.A j) x.v x.basis
  refine ⟨⟨P', Nat.mul_pos hj x.g_pos, _, hr', th, fun s => hne s fun _ => x.th_ne s, v, hv⟩,
    ⟨Out.powIsPowGrp x.P.A j, idIso _, idIso_isGen hL⟩, rfl, fun p => hr' p.1 p.2, fun jj b h => ?_, hvp⟩
  refine Eq.trans ?_ (th.compat jj b)
  rw [hth jj fun i => LB.wchart_le x.P.L _ jj i, map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  exact (congrArg (fun f => f.hom (x.th.f (jj i))) (Scheme.Hom.appLE_map (Out.powPr x.P.A i).left
    (LB.wchart_le x.P.L (fun i => (Out.powPr x.P.A i).left) jj i) (homOfLE (inf_le_left (b := P'.L.U b))).op)).symm

end GlobalTheory.KeyPow
end
