module

public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowEqOfBaseChange
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnivBasis
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicHomDetermined
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSemiAbelianModelSplitSpecialFibre
public import Development.AbelianVarietyTheory.Definitions.Degenerations.IsBasisB

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLabelMapTorsionCharacters
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLabelMapTorsionCharacters
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ZH.LabelMap

theorem exists_lift_points {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (T : Over S') {Γ : Type} [AddCommGroup Γ]
    (pt : Γ → (baseOver S ⟶ G)) (hadd : ∀ a b, pt (a + b) = pt a * pt b) :
    ∃ xx : Multiplicative Γ →* (T ⟶ G'),
      (∀ a x, x.left ≫ φ = (T.hom ≫ f) ≫ (pt a).left ↔ x = xx (Multiplicative.ofAdd a)) ∧
      ∀ (k : ℕ), (∀ z : Over.mk (T.hom ≫ f) ⟶ G, z ^ k = 1 → ∃ a, (T.hom ≫ f) ≫ (pt a).left = z.left) →
        ∀ x : T ⟶ G', x ^ k = 1 → ∃ a, xx (Multiplicative.ofAdd a) = x := by
  let Φ : (T ⟶ G') →* (Over.mk (T.hom ≫ f) ⟶ G) :=
    MonoidHom.mk' (fun x => toBase h.1.w x) fun x y => Over.OverMorphism.ext (h.2 T x y _ _ rfl rfl).symm
  have hΦ : ∀ x, (Φ x).left = x.left ≫ φ := fun _ => rfl
  have inj : Function.Injective Φ := fun x y e => Over.OverMorphism.ext (h.1.hom_ext
    ((hΦ x).symm.trans ((congrArg (fun z => z.left) e).trans (hΦ y))) ((Over.w x).trans (Over.w y).symm))
  have surj : Function.Surjective Φ := fun z =>
    ⟨Over.homMk (h.1.lift z.left T.hom (Over.w z)) (h.1.lift_snd _ _ _), Over.OverMorphism.ext (h.1.lift_fst _ _ _)⟩
  let e := MulEquiv.ofBijective Φ ⟨inj, surj⟩
  let U : Over.mk (T.hom ≫ f) ⟶ baseOver S := Over.homMk (T.hom ≫ f) (Category.comp_id _)
  let q : Multiplicative Γ →* (Over.mk (T.hom ≫ f) ⟶ G) :=
    MonoidHom.mk' (fun a => U ≫ pt a.toAdd) fun a b =>
      (congrArg (U ≫ ·) (hadd a.toAdd b.toAdd)).trans (MonObj.comp_mul U _ _)
  have key : ∀ a x, x.left ≫ φ = (T.hom ≫ f) ≫ (pt a).left ↔ x = e.symm (q (Multiplicative.ofAdd a)) := fun a x =>
    ⟨fun H => e.eq_symm_apply.2 (Over.OverMorphism.ext H),
      fun H => congrArg (fun z => z.left) (e.eq_symm_apply.1 H)⟩
  refine ⟨e.symm.toMonoidHom.comp q, key, fun k hk x hx => ?_⟩
  obtain ⟨a, ha⟩ := hk (Φ x) (by rw [← map_pow, hx, map_one])
  exact ⟨a, ((key a x).1 ha.symm).symm⟩

attribute [local instance] TorusExt.gtGroup in

theorem pow_eq_one_of_qkAdd {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F]
    [Algebra (FractionRing R) F] (hB : D.TauBimult) {k : ℕ} {M : Type} [Group M] (f : QkPt D F k → M)
    (heq : ∀ q q', QkPt.Equiv D F q q' → f q = f q') (hadd : ∀ q q' q'', QkAdd q q' q'' → f q'' = f q * f q')
    (q : QkPt D F k) : f q ^ k = 1 := by
  letI := TorusExt.gtGroup D F
  let iota : D.X →+ GtPtF D F := AddMonoidHom.mk' (fun x => (TorusExt.exists_iota hB x).choose) fun x x' => by
    obtain ⟨b, v⟩ := (TorusExt.isIota_iff_val _ _).1 (TorusExt.exists_iota (F := F) hB x).choose_spec
    obtain ⟨b', v'⟩ := (TorusExt.isIota_iff_val _ _).1 (TorusExt.exists_iota (F := F) hB x').choose_spec
    obtain ⟨b'', v''⟩ := (TorusExt.isIota_iff_val _ _).1 (TorusExt.exists_iota (F := F) hB (x + x')).choose_spec
    refine (TorusExt.isAdd_iff_eq _ _ _).1 ((TorusExt.isAdd_iff_val _ _ _).2 ⟨by rw [b, b', b'', ReciprocityTheory.ChartRestriction.G.DVR.cPoint_add], fun χ y J hJ => ?_⟩)
    have C : IsCub (ReciprocityTheory.ChartRestriction.G.DVR.th D (T := TF (R := R) F) y J) := isCub_cubV D.cub hJ
    rw [v χ y J hJ, v' χ y J hJ, v'' χ y J hJ, b, b', C.s01, C.s12]
    exact ReciprocityTheory.ChartRestriction.G.DVR.tau_mul (𝟙 (TF (R := R) F)) hJ hB x x' χ
  have isIota_iff_eq (x : D.X) (g : GtPtF D F) : GtPtF.IsIota x g ↔ g = iota x :=
    ⟨fun h => TorusExt.isIota_unique h (TorusExt.exists_iota hB x).choose_spec,
      fun h => h ▸ (TorusExt.exists_iota hB x).choose_spec⟩
  have qk_nsmul (q : QkPt D F k) : k • q.g = iota q.y := by
    obtain ⟨h, h₁, h₂⟩ := q.eq
    exact ((TorusExt.isNsmul_iff_eq _ _ _).1 h₁).symm.trans ((isIota_iff_eq _ _).1 h₂)
  let qkMk (y : D.X) (g : GtPtF D F) (h : k • g = iota y) : QkPt D F k :=
    ⟨y, g, k • g, (TorusExt.isNsmul_iff_eq _ _ _).2 rfl, (isIota_iff_eq _ _).2 h⟩
  let qkZero : QkPt D F k := qkMk 0 0 (by rw [nsmul_zero, map_zero])
  let qkAdd (p p' : QkPt D F k) : QkPt D F k :=
    qkMk (p.y + p'.y) (p.g + p'.g) (by rw [nsmul_add, qk_nsmul, qk_nsmul, map_add (f := _)])
  have qkAdd_rel (p p' : QkPt D F k) : QkAdd p p' (qkAdd p p') :=
    ⟨_, rfl, (TorusExt.isAdd_iff_eq _ _ _).2 rfl, qk_equiv_refl hB _⟩
  have fz : f qkZero = 1 := by
    have e := hadd _ _ _ (qkAdd_rel (qkZero) (qkZero))
    rw [show qkAdd (qkZero) (qkZero) = qkZero from
      TorusExt.qk_ext (add_zero _) (add_zero _)] at e
    exact mul_eq_left.1 e.symm
  let m : ℕ → QkPt D F k := fun n => qkMk (n • q.y) (n • q.g) (by
    rw [smul_comm, qk_nsmul, map_nsmul])
  have hm : ∀ n, f (m n) = f q ^ n := fun n => by
    induction n with
    | zero => exact (congrArg f (TorusExt.qk_ext (zero_nsmul _) (zero_nsmul _))).trans (fz.trans (pow_zero _).symm)
    | succ n ih =>
      rw [pow_succ, ← ih, ← hadd _ _ _ (qkAdd_rel _ _)]
      exact congrArg f (TorusExt.qk_ext (succ_nsmul _ _) (succ_nsmul _ _))
  rw [← hm, ← fz]
  exact (heq _ _ ⟨q.y, (zero_add _).symm, iota q.y, (isIota_iff_eq _ _).2 rfl, (TorusExt.isAdd_iff_eq _ _ _).2 ((qk_nsmul q).trans (zero_add _).symm)⟩).symm

theorem exists_labelMap : Laws → Laws2 → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀), ∃ yy : S.Gam →+ u.D.toPre.X ⧸ (nsmulAddMonoidHom (S.r * S.N) : u.D.toPre.X →+ u.D.toPre.X).range, Function.Surjective yy ∧ (∀ (a : S.Gam) (pk : QkPt u.D.toPre (PadicAlgCl p) (S.r * S.N)) (x : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A), QkToAkU u.U.toUnifPre (PadicAlgCl p) (S.r * S.N) pk x → x.left ≫ u.φ = spMap y₀ ≫ (ρ.pt a).left → yy a = QuotientAddGroup.mk pk.y) := by
  intro L _ hU o Ω _ _ _ _ S ρ p _ y₀ u
  haveI : CharZero u.V := ((algebraMap (FractionRing u.V) (PadicAlgCl p)).comp (algebraMap u.V _)).charZero
  have hk : 1 ≤ S.r * S.N := Nat.mul_pos S.r_pos (by have := S.N_ge; omega)
  obtain ⟨f, hrel, honto, heq, hadd, -⟩ := hU u.V u.complete u.A u.G u.D u.U (PadicAlgCl p) (S.r * S.N) hk
  obtain ⟨xx, hxx, hsurj⟩ := exists_lift_points u.cart (TFK (R := u.V) (PadicAlgCl p)) ρ.pt ρ.pt_add
  have hy : (TFK (R := u.V) (PadicAlgCl p)).hom ≫ spMap u.yK = spMap y₀ := by
    exact (Spec.map_comp (CommRingCat.ofHom u.yK) (CommRingCat.ofHom (algebraMap _ _))).symm.trans
      (congrArg spMap u.fac)
  have hsurj' := hsurj (S.r * S.N) fun z hz =>
    (ρ.pt_bij (PadicAlgCl p) _ z hz).exists.imp fun a ha => congrArg (fun w => w.left) ha
  have htors : ∀ a : S.Gam, xx (Multiplicative.ofAdd a) ^ (S.r * S.N) = 1 := fun a => by
    have : (S.r * S.N) • a = 0 := funext fun i => by
      rw [Pi.smul_apply, nsmul_eq_mul, ZMod.natCast_self, zero_mul]; rfl
    rw [← map_pow, ← ofAdd_nsmul, this, ofAdd_zero, map_one]
  choose P hP using fun a => honto _ (htors a)
  have hB := u.D.tau_bimult
  have wd : ∀ q q' : QkPt u.D.toPre (PadicAlgCl p) (S.r * S.N), f q = f q' →
      (QuotientAddGroup.mk q.y : u.D.toPre.X ⧸ (nsmulAddMonoidHom (S.r * S.N) : u.D.toPre.X →+ u.D.toPre.X).range) =
        QuotientAddGroup.mk q'.y := fun q q' e => by
    obtain ⟨z, hz, -⟩ := (heq q q').1 e
    exact QuotientAddGroup.eq.2 ⟨z, by rw [hz, neg_add_cancel_left]; rfl⟩
  have ftors : ∀ q, f q ^ (S.r * S.N) = 1 := pow_eq_one_of_qkAdd hB f (fun q q' e => (heq q q').2 e) hadd
  let D := u.D.toPre
  let F := PadicAlgCl p
  let R := u.V
  let k := S.r * S.N
  letI := TorusExt.gtGroup D F
  let iota : D.X →+ GtPtF D F := AddMonoidHom.mk' (fun x => (TorusExt.exists_iota hB x).choose) fun x x' => by
    obtain ⟨b, v⟩ := (TorusExt.isIota_iff_val _ _).1 (TorusExt.exists_iota (F := F) hB x).choose_spec
    obtain ⟨b', v'⟩ := (TorusExt.isIota_iff_val _ _).1 (TorusExt.exists_iota (F := F) hB x').choose_spec
    obtain ⟨b'', v''⟩ := (TorusExt.isIota_iff_val _ _).1 (TorusExt.exists_iota (F := F) hB (x + x')).choose_spec
    refine (TorusExt.isAdd_iff_eq _ _ _).1 ((TorusExt.isAdd_iff_val _ _ _).2 ⟨by rw [b, b', b'', ReciprocityTheory.ChartRestriction.G.DVR.cPoint_add], fun χ y J hJ => ?_⟩)
    have C : IsCub (ReciprocityTheory.ChartRestriction.G.DVR.th D (T := TF (R := R) F) y J) := isCub_cubV D.cub hJ
    rw [v χ y J hJ, v' χ y J hJ, v'' χ y J hJ, b, b', C.s01, C.s12]
    exact ReciprocityTheory.ChartRestriction.G.DVR.tau_mul (𝟙 (TF (R := R) F)) hJ hB x x' χ
  have isIota_iff_eq (x : D.X) (g : GtPtF D F) : GtPtF.IsIota x g ↔ g = iota x :=
    ⟨fun h => TorusExt.isIota_unique h (TorusExt.exists_iota hB x).choose_spec,
      fun h => h ▸ (TorusExt.exists_iota hB x).choose_spec⟩
  have qk_nsmul (q : QkPt D F k) : k • q.g = iota q.y := by
    obtain ⟨h, h₁, h₂⟩ := q.eq
    exact ((TorusExt.isNsmul_iff_eq _ _ _).1 h₁).symm.trans ((isIota_iff_eq _ _).1 h₂)
  let qkAdd (v v' : QkPt u.D.toPre (PadicAlgCl p) (S.r * S.N)) : QkPt u.D.toPre (PadicAlgCl p) (S.r * S.N) :=
    ⟨v.y + v'.y, v.g + v'.g, (S.r * S.N) • (v.g + v'.g),
      (TorusExt.isNsmul_iff_eq _ _ _).2 rfl,
      (isIota_iff_eq _ _).2 (by rw [nsmul_add, qk_nsmul, qk_nsmul, map_add (f := _)])⟩
  have qkAdd_rel (v v' : QkPt u.D.toPre (PadicAlgCl p) (S.r * S.N)) : QkAdd v v' (qkAdd v v') :=
    ⟨_, rfl, (TorusExt.isAdd_iff_eq _ _ _).2 rfl, qk_equiv_refl hB _⟩
  refine ⟨AddMonoidHom.mk' (fun a => QuotientAddGroup.mk (P a).y) fun a b => ?_, fun c => ?_, fun a pk x hx hφ => ?_⟩
  · exact wd _ (qkAdd (P a) (P b)) (by
      rw [hadd _ _ _ (qkAdd_rel _ _), hP, hP, hP, ofAdd_add, map_mul])
  · obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective c
    obtain ⟨q, rfl⟩ := TorusExt.exists_qkPt (F := PadicAlgCl p) L.mulN (Or.inr L.polBaseChange) hB (Nat.pos_iff_ne_zero.1 hk) y
    obtain ⟨a, ha⟩ := hsurj' _ (ftors q)
    exact ⟨a, wd _ _ ((hP a).trans ha)⟩
  · exact wd _ _ ((hP a).trans (((hxx a x).1 (hφ.trans (by rw [hy]))).symm.trans ((hrel pk x).1 hx)))

end GlobalTheory.ZH.LabelMap
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLabelMapTorsionCharactersStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_labelMap_torsion_characters : Laws → Laws2 → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀), ∃ yy : S.Gam →+ u.D.toPre.X ⧸ (nsmulAddMonoidHom (S.r * S.N) : u.D.toPre.X →+ u.D.toPre.X).range, Function.Surjective yy ∧ (∀ (a : S.Gam) (pk : QkPt u.D.toPre (PadicAlgCl p) (S.r * S.N)) (x : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A), QkToAkU u.U.toUnifPre (PadicAlgCl p) (S.r * S.N) pk x → x.left ≫ u.φ = spMap y₀ ≫ (ρ.pt a).left → yy a = QuotientAddGroup.mk pk.y) := by
  first | exact @GlobalTheory.ZH.LabelMap.exists_labelMap | exact GlobalTheory.ZH.LabelMap.exists_labelMap | (intros; apply GlobalTheory.ZH.LabelMap.exists_labelMap <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniqueOfBasis
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.ThetaReal

open CommPairing GlobalLift VVRank ThetaCoord

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {T : Over S}

theorem exists_symLift_one (hL : L.IsLB) {k : ℤ} {ν : LB.Gen (negLB A L k T)} (hν : ν.IsGen) :
    ∃ θ : ThetaGrp A L k T, SymLift A L k 1 1 θ ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) (J), Good L z J → tval θ r z J = 1 := by
  have h1 : (LB.oneGen L (Y := (T ⊗ A).left)).IsGen := SymLiftOdd.isGen_of_gm fun y j j' _ _ => by
    rw [trF, Fintype.prod_empty, _root_.one_mul]
    exact (map_one _).trans (map_one _).symm
  obtain ⟨t, ht, hv⟩ := exists_gen hL (φ' := ![(snd T A).left, (translPt A (1 : T ⟶ A)).left]) (ε' := ![k, -k])
    (fun U _ f => by
      rw [Fintype.prod_empty, Fin.prod_univ_two, ThetaAct.translPt_one]
      simp) (LB.oneGen L) h1
  have hv' : ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) (J), Good L z J →
      tval (⟨1, t, ht⟩ : ThetaGrp A L k T) r z J = 1 := fun Z r z J hJ => (hv Z r z J hJ).trans (val_one _)
  refine ⟨⟨1, t, ht⟩, symLift_of_tval hL rfl hν (fun T' π z J hJ p => ?_) (fun T' π z J hJ p => ?_), hv'⟩
  · exact Finset.prod_eq_one fun _ _ => hv' _ _ _ _ hJ
  · rw [hv' _ _ _ _ hJ, hv' _ _ _ _ hJ, MonObj.comp_one, inv_one, _root_.one_mul, _root_.one_mul, _root_.one_mul,
      mul_inv_cancel]

theorem isActOf_self (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB)
    {ν : LB.Gen (negLB A L 1 T)} (hν : ν.IsGen) {a : ℤ} {m q : ℕ} (hq : Odd q)
    {α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, (snd T A ^ m).left] ![a, -1])} (hα : α.IsGen)
    {th : LB.Sec (LPow A L 1 T)} {s : LB.Sec (LPow A L a T)}
    (hs : IsTwistPull A L (mulT A T m) (snd T A ^ m) (lift_snd _ _) a 1 α th s)
    {y : T ⟶ A} (hm : y ^ m = 1) (hy : y ^ q = 1) {θ : ThetaGrp A L a T} (H : SymLift A L a q y θ) :
    IsActOf A L a θ s s := by
  have := hA.comm
  obtain ⟨θ₁, h₁, v₁⟩ := exists_symLift_one hL hν
  obtain ⟨θ', h', v'⟩ := exists_symLift_mulPull hA hL (one_dvd q) hα hy (hm.symm ▸ h₁)
  have hc := SymLiftOdd.symLift_unique hG hA hL hq θ θ' H h'
  refine isTwistPull_of_sv A hL θ.isGen fun z J hJ => ?_
  have e : tval θ (𝟙 _) z J = tval θ' (𝟙 _) z J := val_corr hJ hc _
  have e₁ := sv_mulPull hs (fst T A) hJ (snd T A)
  have e₂ := sv_mulPull hs (fst T A) hJ ((fst T A ≫ y) * snd T A)
  have e₃ := v' _ (fst T A) z J hJ (snd T A)
  rw [v₁ _ _ _ _ hJ, _root_.mul_one] at e₃
  rw [mul_pow, ← MonObj.comp_pow, hm, MonObj.comp_one, _root_.one_mul] at e₂
  change _ = (tval θ (𝟙 _) z J).val * _
  rw [e, SymLiftOdd.id_eq_lift, ThetaCoord.lift_translT, H.pt_eq, e₃, e₁, e₂, Units.val_mul, _root_.mul_assoc,
    Units.inv_mul_cancel_left]

theorem act_act (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB) {k : ℤ} {q : ℕ} (hq : Odd q) {x y : T ⟶ A}
    (hy : y ^ q = 1) {θx θy θ : ThetaGrp A L k T} (Hx : SymLift A L k q x θx) (Hy : SymLift A L k q y θy)
    (H : SymLift A L k q (y * x) θ) {c : Γ(T.left, ⊤)ˣ} (hc : WeilIs A L k x y c)
    {s s' s'' t : LB.Sec (LPow A L k T)} (h₁ : IsActOf A L k θy s s') (h₂ : IsActOf A L k θx s' s'')
    (h₃ : IsActOf A L k θ s t) :
    (SecM.ofSec A s'' : SecM A L k T) = ((c ^ ((q + 1) / 2) : Γ(T.left, ⊤)ˣ) : Γ(T.left, ⊤)) • SecM.ofSec A t := by
  refine ThetaAct.sv_ext hL fun z J hJ => ?_
  have e₁ := sv_act Hx.pt_eq h₂ (fst T A) hJ (snd T A)
  have e₂ := sv_act Hy.pt_eq h₁ (fst T A) hJ ((fst T A ≫ x) * snd T A)
  have e₃ := sv_act H.pt_eq h₃ (fst T A) hJ (snd T A)
  have e₄ := tval_mul hG hA hL hq hy Hx Hy H hc (fst T A) hJ (snd T A)
  rw [← _root_.mul_assoc, ← MonObj.comp_mul] at e₂
  rw [ThetaAct.sv_smul _ _ _ _ hJ, Category.id_comp, gs_unit _ _ ⊤ trivial, map_pow, SymLiftOdd.id_eq_lift]
  refine e₁.trans ?_
  rw [e₂, ← _root_.mul_assoc, ← Units.val_mul, e₄, Units.val_mul, _root_.mul_assoc, ← e₃]
  rfl

theorem sum_iff {k : ℤ} {κ : Type} [Fintype κ] (σ : LB.Sec (LPow A L k T)) (s : κ → SecM A L k T)
    (c : κ → Γ(T.left, ⊤)) :
    (∀ j, σ.f j = ∑ i, liftFun A _ (c i) * (SecM.toSec A (s i)).f j) ↔ SecM.ofSec A σ = ∑ i, c i • s i := by
  have e : ∀ j, (∑ i, c i • s i : SecM A L k T).1 j = ∑ i, liftFun A _ (c i) * (SecM.toSec A (s i)).f j := fun j => by
    rw [Submodule.coe_sum, Finset.sum_apply]
    rfl
  exact ⟨fun h => Subtype.ext (funext fun j => (h j).trans (e j).symm),
    fun h j => (congrArg (fun q => q.1 j) h).trans (e j)⟩

theorem existsUnique_of_basis {k : ℤ} {κ : Type} [Fintype κ] (s : Module.Basis κ Γ(T.left, ⊤) (SecM A L k T))
    (σ : LB.Sec (LPow A L k T)) :
    ∃! c : κ → Γ(T.left, ⊤), ∀ j, σ.f j = ∑ i, liftFun A _ (c i) * (SecM.toSec A (s i)).f j := by
  simp only [sum_iff]
  exact ⟨s.equivFun (SecM.ofSec A σ), (s.sum_equivFun _).symm, fun c hc => by
    rw [hc, ← s.equivFun_symm_apply, LinearEquiv.apply_symm_apply]⟩

theorem UnivBasis.exists_basis {P : PolAV S} [IsAffine T.left] {n : ℤ} {κ : Type} {b : κ → SecM P.A P.L n T}
    (h : UnivBasis P n b) : ∃ c : Module.Basis κ Γ(T.left, ⊤) (SecM P.A P.L n T), ∀ i, c i = b i := by
  obtain ⟨c, hc⟩ := h T (𝟙 T)
  exact ⟨c, fun i => (hc i).trans (pullM_id P.A P.isLB n _)⟩

theorem UnivBasis.unique {P : PolAV S} {n : ℤ} {κ : Type} [Unique κ] {b : κ → SecM P.A P.L n T}
    (h : UnivBasis P n b) : UnivBasis P n (fun _ : Fin 1 => b default) := fun T' _ u => by
  obtain ⟨c, hc⟩ := h T' u
  refine ⟨c.reindex (Equiv.ofUnique κ (Fin 1)), fun i => ?_⟩
  rw [Module.Basis.reindex_apply, hc, Subsingleton.elim ((Equiv.ofUnique κ (Fin 1)).symm i) default]

end GlobalTheory.ThetaReal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPrimitiveScaling
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPrimitiveScaling
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PrimScale

open TopologicalSpace GlobalTheory.HolHom

theorem chart_one_le {X : Scheme.{0}} (L : LB X) (j : Fin 1 → L.ι) :
    LB.wchart L (fun _ : Fin 1 => 𝟙 X) j ≤ L.U (j 0) := fun _ hy => Set.mem_iInter.1 hy 0

theorem exists_section_firstPower_restrict {X : Scheme.{0}} {L : LB X} (s : L.Sec) : ∃ t : H0 L 1, ∀ j,
    t.f j = (X.presheaf.map (homOfLE (chart_one_le L j)).op).hom (s.f (j 0)) := by
  have le := chart_one_le L
  refine ⟨⟨fun j => (X.presheaf.map (homOfLE (le j)).op).hom (s.f (j 0)),
    fun (i j : Fin 1 → L.ι) => fn_ext fun y hy => ?_⟩, fun _ => rfl⟩
  refine ((gs_res (𝟙 X) y _ hy _).trans (gs_res (𝟙 X) y (le i) hy.1 _)).trans
    ((SecPullIso.gs_sec_trans s (𝟙 X) y (le i hy.1) (le j hy.2)).trans (Eq.symm ((gs_mul (𝟙 X) y _ hy _ _).trans
      (congrArg₂ (· * ·) ((gs_unit (𝟙 X) y _ hy _).trans (congrArg Units.val ?_))
        ((gs_res (𝟙 X) y _ hy _).trans (gs_res (𝟙 X) y (le j) hy.2 _))))))
  refine (gm_linComb L _ _ (𝟙 X) y i j hy.1 hy.2).trans ?_
  simp

theorem valR_mul' {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U)
    (a b : Γ(X, U)) : valR x U (a * b) = valR x U a * valR x U b := by
  simp only [valR_eq _ _ h, map_mul]

theorem valR_const {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) (p : X ⟶ Sp A) (h : x ≫ p = 𝟙 _) (a : A) :
    valR x ⊤ (p.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a)) = a := by
  refine (valR_comp x p ⊤ _).symm.trans ?_
  rw [h, valR, dite_eq_left (show ⊤ ≤ 𝟙 (Sp A) ⁻¹ᵁ ⊤ from le_top)]
  have : Scheme.Hom.appLE (𝟙 (Sp A)) ⊤ ⊤ le_top = 𝟙 _ := (Category.id_comp _).trans ((Sp A).presheaf.map_id _)
  rw [this]
  exact Iso.inv_hom_id_apply _ _

theorem exists_primitive_scaling : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (G : Over (Sp V)) [GrpObj G], IsSemiAbelian G → ∀ (M : LB G.left), M.IsLB → ∀ (Y : Scheme.{0}) (L : LB Y), L.IsLB → ∀ (ψ : pullback G.hom (jK V) ⟶ Y) (w : LB.Iso (M.pull (pullback.fst G.hom (jK V))) (L.pull ψ)), w.IsGen → ∀ θ : LB.Sec L, (∃ z, ψ z ∈ nonzeroLocus θ) → ∃ (ϑ : H0 M 1) (c : FractionRing V), c ≠ 0 ∧ (∃ z ∈ nonzeroLocus ϑ, G.hom z = IsLocalRing.closedPoint V) ∧ ∀ x : Sp (FractionRing V) ⟶ pullback G.hom (jK V), x ≫ pullback.snd G.hom (jK V) = 𝟙 _ → ∀ (i : M.ι) (k : L.ι), ⊤ ≤ (x ≫ pullback.fst G.hom (jK V)) ⁻¹ᵁ M.U i → ⊤ ≤ (x ≫ ψ) ⁻¹ᵁ L.U k → valR x _ (w.s (fun _ => k, fun _ => i)).val * valR (x ≫ pullback.fst G.hom (jK V)) _ (ϑ.f (fun _ => i)) = c * valR (x ≫ ψ) _ (θ.f k) := by
  intro V _ _ _ G _ hG M hM Y L hL ψ w hw θ hθ
  have := hG.smooth
  have := hG.separated
  have := hG.quasiCompact
  have := hG.geomConnected
  have := grpObj_geometricallyIntegral_of_smooth _ G
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  have hK := IsPullback.of_hasPullback G.hom (jK V)
  have hs := IsPullback.of_hasPullback G.hom (Spec.map (CommRingCat.ofHom (IsLocalRing.residue V)))
  have := DvrModel.isIntegral_of_geometricallyIntegral hK
  have := DvrModel.isIntegral_of_geometricallyIntegral hs
  obtain ⟨r, hr⟩ := SecPullIso.exists_pull ψ L (M.pull (pullback.fst G.hom (jK V))) w hL (LB.isLB_linComb hM _ _) hw θ
  obtain ⟨n, ⟨σ, hσ, b, x₀, hx₀, hb⟩, -⟩ := DvrModel.existsUnique_zpow_mul_sec hK hs hϖ hM r (by
    obtain ⟨x, hx⟩ := hθ
    obtain ⟨k, hk⟩ := Opens.mem_iSup.1 hx
    obtain ⟨a, ha⟩ := exists_chart (L := M.pull (pullback.fst G.hom (jK V))) (LB.isLB_linComb hM _ _) x
    have hk' := Y.basicOpen_le _ hk
    have u := (SecPullIso.isUnit_gs_iff ψ x hk' _).2 hk
    rw [hr x k a hk' ha] at u
    have u' := (SecPullIso.isUnit_gs_iff (𝟙 _) x ha _).1 (isUnit_of_mul_isUnit_right u)
    exact ⟨a, fun h => by rw [h, Scheme.basicOpen_zero] at u'; exact u'⟩)
  have h0 : algebraMap V (FractionRing V) ϖ ^ n ≠ 0 :=
    zpow_ne_zero _ ((map_ne_zero_iff _ (IsFractionRing.injective V _)).2 hϖ.ne_zero)
  obtain ⟨ϑ, hϑ⟩ := exists_section_firstPower_restrict σ
  refine ⟨ϑ, _, h0, ⟨x₀, Opens.mem_iSup.2 ⟨fun _ => b, ?_⟩, hx₀⟩, fun x hx i k hi hk => ?_⟩
  · refine (congrArg G.left.basicOpen (hϑ fun _ => b)).ge ?_
    exact (Scheme.basicOpen_res _ _ _).ge ⟨Set.mem_iInter.2 fun _ => G.left.basicOpen_le _ hb, hb⟩
  · have hi₁ : ⊤ ≤ (x ≫ pullback.fst G.hom (jK V)) ⁻¹ᵁ LB.wchart M (fun _ : Fin 1 => 𝟙 G.left) (fun _ => i) :=
      fun z hz => Set.mem_iInter.2 fun _ => hi hz
    have hi₂ : ⊤ ≤ x ⁻¹ᵁ (M.pull (pullback.fst G.hom (jK V))).U (fun _ => i) := fun z hz => mem_pull.2 (hi hz)
    have hW : ⊤ ≤ x ⁻¹ᵁ ((L.pull ψ).U (fun _ => k) ⊓ (M.pull (pullback.fst G.hom (jK V))).U (fun _ => i)) :=
      fun z hz => ⟨mem_pull.2 (hk hz), hi₂ hz⟩
    have l₁ : (L.pull ψ).U (fun _ => k) ⊓ (M.pull (pullback.fst G.hom (jK V))).U (fun _ => i) ≤ ψ ⁻¹ᵁ L.U k :=
      fun y hy => mem_pull.1 hy.1
    have e₁ : valR (x ≫ pullback.fst G.hom (jK V)) _ (ϑ.f (fun _ => i)) =
        algebraMap V (FractionRing V) ϖ ^ n * valR x _ (r.f fun _ => i) := by
      refine (congrArg (valR _ _) (hϑ fun _ => i)).trans ?_
      refine (valR_res _ _ _ hi₁).trans ((valR_appLE x _ _ _ _ _ hi₂).symm.trans
        ((congrArg (valR x _) (hσ fun _ => i)).trans ((valR_mul' x _ hi₂ _ _).trans (congrArg (· * _) ?_))))
      exact (valR_res x le_top _ hi₂).trans (valR_const x _ hx _)
    have e₂ : (ψ.appLE _ _ l₁).hom (θ.f k) = (show Γ(pullback G.hom (jK V), (L.pull ψ).U (fun _ => k) ⊓
        (M.pull (pullback.fst G.hom (jK V))).U (fun _ => i))ˣ from w.s (fun _ => k, fun _ => i)).val *
          ((pullback G.hom (jK V)).presheaf.map (homOfLE inf_le_right).op).hom (r.f fun _ => i) :=
      fn_ext fun y hy => by
        refine (gs_appLE _ _ _ _ (𝟙 _) y hy _).trans ?_
        rw [Category.id_comp, hr y k _ (l₁ hy) hy.2]
        exact ((gs_mul (𝟙 _) y _ hy _ _).trans (congrArg₂ (· * ·) (gs_unit (𝟙 _) y _ hy _)
          (gs_res (𝟙 _) y _ hy _))).symm
    have e₃ := (valR_appLE x ψ _ _ l₁ _ hW).symm.trans ((congrArg (valR x _) e₂).trans
      ((valR_mul' x _ hW _ _).trans (congrArg (_ * ·) (valR_res x _ _ hW))))
    rw [e₁, e₃]
    exact mul_left_comm _ _ _

end GlobalTheory.PrimScale
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPrimitiveScalingStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.exists_primitive_scaling_alt : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (G : Over (Sp V)) [GrpObj G], IsSemiAbelian G → ∀ (M : LB G.left), M.IsLB → ∀ (Y : Scheme.{0}) (L : LB Y), L.IsLB → ∀ (ψ : pullback G.hom (jK V) ⟶ Y) (w : LB.Iso (M.pull (pullback.fst G.hom (jK V))) (L.pull ψ)), w.IsGen → ∀ θ : LB.Sec L, (∃ z, ψ z ∈ nonzeroLocus θ) → ∃ (ϑ : H0 M 1) (c : FractionRing V), c ≠ 0 ∧ (∃ z ∈ nonzeroLocus ϑ, G.hom z = IsLocalRing.closedPoint V) ∧ ∀ x : Sp (FractionRing V) ⟶ pullback G.hom (jK V), x ≫ pullback.snd G.hom (jK V) = 𝟙 _ → ∀ (i : M.ι) (k : L.ι), ⊤ ≤ (x ≫ pullback.fst G.hom (jK V)) ⁻¹ᵁ M.U i → ⊤ ≤ (x ≫ ψ) ⁻¹ᵁ L.U k → valR x _ (w.s (fun _ => k, fun _ => i)).val * valR (x ≫ pullback.fst G.hom (jK V)) _ (ϑ.f (fun _ => i)) = c * valR (x ≫ ψ) _ (θ.f k) := by
  first | exact @GlobalTheory.PrimScale.exists_primitive_scaling | exact GlobalTheory.PrimScale.exists_primitive_scaling | (intros; apply GlobalTheory.PrimScale.exists_primitive_scaling <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsDenseClosedPointsChartSplitting
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsDenseClosedPointsChartSplitting
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

noncomputable section
namespace GlobalTheory.ZJ.DenseSplit

theorem exists_ringHom_kb (F : Type) [Field F] [Finite F] :
    ∃ (p : ℕ) (_ : Fact p.Prime), Nonempty (F →+* kb p) := by
  obtain ⟨p, hp⟩ := CharP.exists F
  have hpp : Fact p.Prime := ⟨CharP.char_is_prime F p⟩
  have : CharP (kb p) p := (CharP.charP_iff_prime_eq_zero hpp.out).mpr
    (GlobalTheory.natCast_self_residueField_padicAlgCl_eq_zero p)
  have := (kb_isAlgClosed_and_conj p).1
  letI : Algebra (ZMod p) F := ZMod.algebra F p
  letI : Algebra (ZMod p) (kb p) := ZMod.algebra _ p
  have : Module.Finite (ZMod p) F := Module.Finite.of_finite
  exact ⟨p, hpp, ⟨(IsAlgClosed.lift (R := ZMod p) (S := F) (M := kb p)).toRingHom⟩⟩

theorem isNoetherianRing_of_lft (R : Type) [CommRing R] (π : Sp R ⟶ Sp ℤ) [LocallyOfFiniteType π] :
    IsNoetherianRing R := by
  have : IsLocallyNoetherian (Sp R) := LocallyOfFiniteType.isLocallyNoetherian π
  exact isLocallyNoetherian_Spec.mp this

theorem exists_dense_splitOn : ∀ (C : Core) (L : C.Law), C.HasTests → C.HasCharts → letI := L.grp; letI := L.comm; ∀ z : C.Z, ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : IsNoetherianRing R) (t : Sp R ⟶ C.Z) (_ : IsImmersion t), t (⊥ : PrimeSpectrum R) = z ∧ ∃ (Ch : Charts ((Over.pullback t).obj C.GG).left) (d : ℕ) (c : Fin d → Ch.Cl) (Sg : Set (Sp R)), Dense Sg ∧ Ch.SplitOn c Sg ∧ ∀ x ∈ Sg, IsClosed ({t x} : Set C.Z) := by
  intro C L hT hC z
  letI := L.grp; letI := L.comm
  obtain ⟨R, _, _, t, _, htz, Ch, hCh⟩ := hC z
  have := C.lft
  have := C.flat
  obtain ⟨-, hfin, -, -, hdense⟩ := GlobalTheory.jacobson_closedPoints_tools_int (Sp R) (t ≫ C.π)
  refine ⟨R, inferInstance, inferInstance, isNoetherianRing_of_lft R (t ≫ C.π), t, inferInstance, htz, Ch, ?_⟩
  let κ := Σ d : Fin (C.g + 1), (Fin d → Ch.Cl)
  let Sg : κ → Set (Sp R) := fun k => {x | Charts.SplitOn (G := (Over.pullback t).obj C.GG) Ch k.2 {x} ∧
    IsClosed ({t x} : Set C.Z)}
  obtain ⟨k, hk⟩ := hdense κ Sg inferInstance (by
    intro x hx
    have := hfin x hx
    obtain ⟨p, hp, ⟨r⟩⟩ := exists_ringHom_kb ((Sp R).residueField x)
    let xb : Sp (kb p) ⟶ Sp R := Spec.map (CommRingCat.ofHom r) ≫ (Sp R).fromSpecResidueField x
    have hxb : ∀ s, xb s = x := fun s => by
      have : xb s ∈ Set.range ((Sp R).fromSpecResidueField x) := ⟨_, (Scheme.Hom.comp_apply _ _ _).symm⟩
      rwa [Scheme.range_fromSpecResidueField] at this
    have hrange : Set.range xb = {x} := by
      ext w
      exact ⟨fun ⟨s, hs⟩ => hs ▸ hxb s, fun hw => ⟨IsLocalRing.closedPoint (kb p), (hxb _).trans hw.symm⟩⟩
    obtain ⟨hlift, hcl⟩ := GlobalTheory.exists_integral_point_lifting_residue_point C.Z C.π C.U C.ne p
    obtain ⟨y, hy, hyU⟩ := hlift (xb ≫ t)
    obtain ⟨τ⟩ := hT p y hyU
    have e : (rPt p ≫ spMap τ.j) ≫ τ.y₀ = xb ≫ t := by rw [Category.assoc, τ.fac, hy]
    have g1 : IsGrpPullback ((Over.pullback (rPt p ≫ spMap τ.j)).obj τ.H) C.GG (xb ≫ t)
        (pullback.fst τ.H.hom (rPt p ≫ spMap τ.j) ≫ τ.f) :=
      ((isGrpPullback_pullback _ _).comp (L.test p y τ)).congr e rfl
    have g2 : IsGrpPullback ((Over.pullback t).obj C.GG) C.GG t (pullback.fst C.GG.hom t) :=
      isGrpPullback_pullback _ _
    have g3 : IsGrpPullback ((Over.pullback xb).obj ((Over.pullback t).obj C.GG)) ((Over.pullback t).obj C.GG) xb
        (pullback.fst ((Over.pullback t).obj C.GG).hom xb) :=
      isGrpPullback_pullback _ _
    let h : pullback τ.H.hom (rPt p ≫ spMap τ.j) ⟶ pullback C.GG.hom t :=
      pullback.lift (pullback.fst _ _ ≫ τ.f) (pullback.snd _ _ ≫ xb) (g1.1.w.trans (Category.assoc _ _ _).symm)
    have h1 : h ≫ pullback.fst _ _ = pullback.fst _ _ ≫ τ.f := pullback.lift_fst _ _ _
    have h2 : h ≫ pullback.snd _ _ = pullback.snd _ _ ≫ xb := pullback.lift_snd _ _ _
    have g4 : IsGrpPullback ((Over.pullback (rPt p ≫ spMap τ.j)).obj τ.H) ((Over.pullback t).obj C.GG) xb h :=
      g2.cancel (g1.congr rfl h1.symm) h2
    have ha : IsAffineHom h := MorphismProperty.of_isPullback (P := @IsAffineHom) g4.1.flip inferInstance
    have ha' : IsAffineHom (pullback.fst ((Over.pullback t).obj C.GG).hom xb) :=
      MorphismProperty.of_isPullback (P := @IsAffineHom) g3.1.flip inferInstance
    obtain ⟨d, hd, c, hs⟩ := hCh p y τ xb hy.symm h h1 h2
    have w : pullback.fst ((Over.pullback t).obj C.GG).hom xb ≫ ((Over.pullback t).obj C.GG).hom =
      ((Over.pullback xb).obj ((Over.pullback t).obj C.GG)).hom ≫ xb := g3.1.w
    let φ := g4.1.lift _ _ w
    have f1 : φ ≫ h = _ := g4.1.lift_fst _ _ w
    have f2 : φ ≫ _ = _ := g4.1.lift_snd _ _ w
    have g5 : IsGrpPullback ((Over.pullback xb).obj ((Over.pullback t).obj C.GG))
        ((Over.pullback (rPt p ≫ spMap τ.j)).obj τ.H) (𝟙 _) φ :=
      g4.cancel (g3.congr (Category.id_comp _).symm f1.symm) (f2.trans (Category.comp_id _).symm)
    have hφ : IsAffineHom φ := MorphismProperty.of_isPullback (P := @IsAffineHom) g5.1.flip inferInstance
    have hs' := @SplitPull.pull_pull_and_split_pull.2 (kb p) (kb p) _ _
      ((Over.pullback (rPt p ≫ spMap τ.j)).obj τ.H) _ ((Over.pullback xb).obj ((Over.pullback t).obj C.GG)) _
      (𝟙 _) φ hφ g5 (Ch.pull h) d c hs
    refine ⟨⟨⟨d, Nat.lt_succ_of_le hd⟩, c⟩, ?_, ?_⟩
    · rintro _ rfl
      refine ⟨kb p, inferInstance, xb, ha', hrange, ?_⟩
      have key : ∀ (ψ : ((Over.pullback xb).obj ((Over.pullback t).obj C.GG)).left ⟶ pullback C.GG.hom t)
          [IsAffineHom ψ], φ ≫ h = ψ →
          Charts.Split (H := (Over.pullback xb).obj ((Over.pullback t).obj C.GG)) (Ch.pull ψ) c := by
        intro ψ _ hψ
        subst hψ
        exact hs'
      exact @key _ ha' f1
    · have := hcl (xb ≫ t) (IsLocalRing.closedPoint (kb p))
      exact ((Scheme.Hom.comp_apply xb t _).trans (congrArg t (hxb _))) ▸ this)
  exact ⟨k.1, k.2, Sg k, hk, fun x hx => hx.1 x rfl, fun x hx => hx.2⟩

end GlobalTheory.ZJ.DenseSplit
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsDenseClosedPointsChartSplittingStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ
theorem _root_.GlobalTheory.T.exists_dense_closedPoints_chartSplitting : ∀ (C : Core) (L : C.Law), C.HasTests → C.HasCharts → letI := L.grp; letI := L.comm; ∀ z : C.Z, ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : IsNoetherianRing R) (t : Sp R ⟶ C.Z) (_ : IsImmersion t), t (⊥ : PrimeSpectrum R) = z ∧ ∃ (Ch : Charts ((Over.pullback t).obj C.GG).left) (d : ℕ) (c : Fin d → Ch.Cl) (Sg : Set (Sp R)), Dense Sg ∧ Ch.SplitOn c Sg ∧ ∀ x ∈ Sg, IsClosed ({t x} : Set C.Z) := by
  first | exact @GlobalTheory.ZJ.DenseSplit.exists_dense_splitOn | exact GlobalTheory.ZJ.DenseSplit.exists_dense_splitOn | (intros; apply GlobalTheory.ZJ.DenseSplit.exists_dense_splitOn <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsMonomialMatricesProjectiveRep
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsMonomialMatricesProjectiveRep
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ThetaReal

namespace GlobalTheory.ThetaReal

attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.ThetaReal.exists_monomial_matrices : ∀ (o A M : Type) [CommRing o] [CommRing A] [Nontrivial A] [AddCommGroup M] [Module A M] (f : o →+* A), Function.Injective f → ∀ (g m r N : ℕ), N = m ^ 2 → 1 ≤ m → 1 ≤ r → ∀ (ζ : o) (q : ℕ), 1 ≤ q → ζ ^ q = 1 → ∀ (_ : Module.Basis (Fin (N ^ g)) A M) (u : (Fin g ⊕ Fin g → ZMod (r * N)) → M →ₗ[A] M) (s₀ : M), (∀ a, r • a = 0 → ∀ v, u a v = v) → (∀ a b, ∃ e : ℕ, ∀ v, u a (u b v) = f (ζ ^ e) • u (a + b) v) → (∀ a b, r • _root_.GlobalTheory.ZH.eStd g _ a b = 0 → ∀ v, u a (u b v) = u (a + b) v) → (∀ a, (r * m) • a = 0 → u a s₀ = s₀) → Submodule.span A (Set.range fun a => u a s₀) = ⊤ → ∃ (J : Type) (_ : Fintype J) (ρ : (Fin g ⊕ Fin g → ZMod (r * N)) → Matrix J J o) (s : Module.Basis J A M) (i₀ : J), Fintype.card J = N ^ g ∧ s i₀ = s₀ ∧ (∀ a, r • a = 0 → ρ a = 1) ∧ (∀ a b, ∃ k : ℕ, ρ a * ρ b = ζ ^ k • ρ (a + b)) ∧ (∀ a b, r • _root_.GlobalTheory.ZH.eStd g _ a b = 0 → ρ a * ρ b = ρ (a + b)) ∧ (∀ a i, u a (s i) = ∑ l, f (ρ a l i) • s l) ∧ ∀ i, ∃ a, ∃ e : ℕ, ∀ l, ρ a l i₀ = if l = i then ζ ^ e else 0 := by
  intro o A M _ _ _ _ _ f hf g m r N hN hm hr ζ q hq hζ b u s₀ hker hmul hcomm hfix hspan
  subst hN
  obtain ⟨q, rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩

  let rep : (Fin g ⊕ Fin g → Fin m) → (Fin g ⊕ Fin g → ZMod (r * m ^ 2)) :=
    fun j k => ((j k : ℕ) : ZMod (r * m ^ 2))
  let cls : (Fin g ⊕ Fin g → ZMod (r * m ^ 2)) → (Fin g ⊕ Fin g → Fin m) :=
    fun a k => ⟨(a k).val % m, Nat.mod_lt _ hm⟩
  haveI : NeZero (r * m ^ 2) := ⟨(Nat.mul_pos (by omega) (pow_pos (by omega) 2)).ne'⟩
  have hzero : ((r : ZMod (r * m ^ 2)) * (m : ZMod (r * m ^ 2)) ^ 2) = 0 := by
    exact_mod_cast ZMod.natCast_self (r * m ^ 2)
  have hcls : ∀ a, (r * m) • (a - rep (cls a)) = 0 := fun a => by
    funext k
    simp only [Pi.smul_apply, Pi.sub_apply, Pi.zero_apply, nsmul_eq_mul, rep, cls]
    have hx : a k - (((a k).val % m : ℕ) : ZMod (r * m ^ 2)) = (((m * ((a k).val / m) : ℕ) : ZMod (r * m ^ 2))) := by
      rw [sub_eq_iff_eq_add, ← Nat.cast_add, Nat.div_add_mod, ZMod.natCast_zmod_val]
    rw [hx]
    push_cast
    linear_combination (((a k).val / m : ℕ) : ZMod (r * m ^ 2)) * hzero
  have hrep : ∀ j, cls (rep j) = j := fun j => by
    funext k
    apply Fin.ext
    have hlt : (j k : ℕ) < r * m ^ 2 :=
      lt_of_lt_of_le (j k).isLt (by nlinarith)
    simp only [rep, cls, ZMod.val_natCast_of_lt hlt, Nat.mod_eq_of_lt (j k).isLt]
  have hrep0 : rep (cls 0) = 0 := by
    funext k
    simp [rep, cls]
  let s : (Fin g ⊕ Fin g → Fin m) → M := fun j => u (rep j) s₀
  have hA : ∀ a, ∃ c : ℕ, u a s₀ = f (ζ ^ c) • s (cls a) := fun a => by
    obtain ⟨e, he⟩ := hmul (rep (cls a)) (a - rep (cls a))
    have h1 := he s₀
    rw [hfix _ (hcls a), add_sub_cancel] at h1
    refine ⟨e * q, ?_⟩
    show u a s₀ = f (ζ ^ (e * q)) • u (rep (cls a)) s₀
    rw [h1, smul_smul, ← map_mul, ← pow_add]
    have : e * q + e = e * (q + 1) := by ring
    rw [this, pow_mul', hζ, one_pow, map_one, one_smul]
  have hB : ∀ a j, ∃ c : ℕ, u a (s j) = f (ζ ^ c) • s (cls (a + rep j)) := fun a j => by
    obtain ⟨e, he⟩ := hmul a (rep j)
    obtain ⟨c, hc⟩ := hA (a + rep j)
    refine ⟨e + c, ?_⟩
    show u a (u (rep j) s₀) = _
    rw [he, hc, smul_smul, ← map_mul, ← pow_add]
  have hcard : Fintype.card (Fin g ⊕ Fin g → Fin m) = (m ^ 2) ^ g := by
    simp only [Fintype.card_fun, Fintype.card_sum, Fintype.card_fin]
    ring
  have hspan' : ⊤ ≤ Submodule.span A (Set.range s) := by
    rw [← hspan, Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    obtain ⟨c, hc⟩ := hA a
    show u a s₀ ∈ Submodule.span A (Set.range s)
    rw [hc]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨cls a, rfl⟩)
  let sB : Module.Basis (Fin g ⊕ Fin g → Fin m) A M := basisOfTopLeSpanOfCardEqFinrank s hspan'
    (by rw [hcard, Module.finrank_eq_card_basis b, Fintype.card_fin])
  have hsB : ⇑sB = s := coe_basisOfTopLeSpanOfCardEqFinrank s hspan' _
  choose c hc using hB
  let ρ : (Fin g ⊕ Fin g → ZMod (r * m ^ 2)) → Matrix (Fin g ⊕ Fin g → Fin m) (Fin g ⊕ Fin g → Fin m) o :=
    fun a => Matrix.of fun l i => if l = cls (a + rep i) then ζ ^ c a i else 0
  have hsum : ∀ a i, u a (sB i) = ∑ l, f (ρ a l i) • sB l := fun a i => by
    rw [hsB, hc a i]
    simp [ρ, apply_ite f, ite_smul]
  have hmat : ∀ a, LinearMap.toMatrix sB sB (u a) = (ρ a).map f := fun a => by
    ext l i
    rw [LinearMap.toMatrix_apply, hsum a i, Module.Basis.repr_sum_self, Matrix.map_apply]
  have hinj : Function.Injective (fun P : Matrix (Fin g ⊕ Fin g → Fin m) (Fin g ⊕ Fin g → Fin m) o => P.map f) :=
    Matrix.map_injective hf
  refine ⟨Fin g ⊕ Fin g → Fin m, inferInstance, ρ, sB, cls 0, hcard, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hsB]
    show u (rep (cls 0)) s₀ = s₀
    rw [hrep0]
    exact hker 0 (smul_zero r) s₀
  · intro a ha
    have hid : u a = LinearMap.id := LinearMap.ext (hker a ha)
    apply hinj
    dsimp only
    rw [← hmat, hid, LinearMap.toMatrix_id]
    convert (Matrix.map_one f (map_zero f) (map_one f)).symm
    all_goals first
      | rfl
      | exact Subsingleton.elim _ _
      | (funext x y; exact Subsingleton.elim _ _)
  · intro a a'
    obtain ⟨e, he⟩ := hmul a a'
    refine ⟨e, hinj ?_⟩
    have hcomp : u a ∘ₗ u a' = f (ζ ^ e) • u (a + a') := LinearMap.ext he
    dsimp only
    rw [Matrix.map_mul, ← hmat, ← hmat, ← LinearMap.toMatrix_comp, hcomp, map_smul, hmat]
    ext l i
    simp [Matrix.map_apply, Matrix.smul_apply]
  · intro a a' ha
    apply hinj
    have hcomp : u a ∘ₗ u a' = u (a + a') := LinearMap.ext (hcomm a a' ha)
    dsimp only
    rw [Matrix.map_mul, ← hmat, ← hmat, ← LinearMap.toMatrix_comp, hcomp, hmat]
  · exact hsum
  · intro i
    refine ⟨rep i, c (rep i) (cls 0), fun l => ?_⟩
    simp only [ρ, Matrix.of_apply]
    rw [hrep0, add_zero, hrep]
    split_ifs <;> rfl

end GlobalTheory.ThetaReal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsMonomialMatricesProjectiveRepStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ThetaReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_monomial_matrices_projectiveRep : ∀ (o A M : Type) [CommRing o] [CommRing A] [Nontrivial A] [AddCommGroup M] [Module A M] (f : o →+* A), Function.Injective f → ∀ (g m r N : ℕ), N = m ^ 2 → 1 ≤ m → 1 ≤ r → ∀ (ζ : o) (q : ℕ), 1 ≤ q → ζ ^ q = 1 → ∀ (_ : Module.Basis (Fin (N ^ g)) A M) (u : (Fin g ⊕ Fin g → ZMod (r * N)) → M →ₗ[A] M) (s₀ : M), (∀ a, r • a = 0 → ∀ v, u a v = v) → (∀ a b, ∃ e : ℕ, ∀ v, u a (u b v) = f (ζ ^ e) • u (a + b) v) → (∀ a b, r • eStd g _ a b = 0 → ∀ v, u a (u b v) = u (a + b) v) → (∀ a, (r * m) • a = 0 → u a s₀ = s₀) → Submodule.span A (Set.range fun a => u a s₀) = ⊤ → ∃ (J : Type) (_ : Fintype J) (ρ : (Fin g ⊕ Fin g → ZMod (r * N)) → Matrix J J o) (s : Module.Basis J A M) (i₀ : J), Fintype.card J = N ^ g ∧ s i₀ = s₀ ∧ (∀ a, r • a = 0 → ρ a = 1) ∧ (∀ a b, ∃ k : ℕ, ρ a * ρ b = ζ ^ k • ρ (a + b)) ∧ (∀ a b, r • eStd g _ a b = 0 → ρ a * ρ b = ρ (a + b)) ∧ (∀ a i, u a (s i) = ∑ l, f (ρ a l i) • s l) ∧ ∀ i, ∃ a, ∃ e : ℕ, ∀ l, ρ a l i₀ = if l = i then ζ ^ e else 0 := by
  first | exact @GlobalTheory.ThetaReal.exists_monomial_matrices | exact GlobalTheory.ThetaReal.exists_monomial_matrices | (intros; apply GlobalTheory.ThetaReal.exists_monomial_matrices <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ValUnitNeZero
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace GlobalTheory.ZH.FrameNorm
open CrdCalc

section Reg
variable {K C : Type} [Field K] [Field C] {Y : Scheme.{0}} {q : Y ⟶ Sp K} {σ : K →+* C}

variable (q σ) in
def Reg (W : Y.Opens) (F : (Sp C ⟶ Y) → C) : Prop :=
  ∃ r : Γ(Y, W), ∀ x : Sp C ⟶ Y, x ≫ q = spMap σ → ⊤ ≤ x ⁻¹ᵁ W → F x = valR x W r

variable {W : Y.Opens} {F G : (Sp C ⟶ Y) → C}

theorem Reg.mul (hF : Reg q σ W F) (hG : Reg q σ W G) : Reg q σ W fun x => F x * G x := by
  obtain ⟨r, hr⟩ := hF
  obtain ⟨s, hs⟩ := hG
  exact ⟨r * s, fun x hx hW => by rw [valR_mul x W hW, ← hr x hx hW, ← hs x hx hW]⟩

theorem Reg.pow (hF : Reg q σ W F) (n : ℕ) : Reg q σ W fun x => F x ^ n := by
  obtain ⟨r, hr⟩ := hF
  exact ⟨r ^ n, fun x hx hW => by
    beta_reduce
    rw [hr x hx hW, valR_eq x W hW, valR_eq x W hW, map_pow]⟩

theorem Reg.sum {I : Type} [Fintype I] {F : I → (Sp C ⟶ Y) → C} (hF : ∀ i, Reg q σ W (F i)) :
    Reg q σ W fun x => ∑ i, F i x := by
  choose r hr using hF
  refine ⟨∑ i, r i, fun x hx hW => ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [valR_eq x W hW, map_sum]
  exact Finset.sum_congr rfl fun i _ => (hr i x hx hW).trans (valR_eq x W hW _)

theorem Reg.const (a : K) : Reg q σ W fun _ => σ a :=
  ⟨constFn q W a, fun x hx hW => (GlobalTheory.Points.valR_constFn_of_over q σ x hx W hW a).symm⟩

theorem Reg.pull {X : Scheme.{0}} (g : Y ⟶ X) {U : X.Opens} (h : W ≤ g ⁻¹ᵁ U) (s : Γ(X, U)) :
    Reg q σ W fun x => valR (x ≫ g) U s :=
  ⟨(g.appLE U W h).hom s, fun x _ hW => (GlobalTheory.Points.valR_appLE x g h hW s).symm⟩

theorem Reg.inv_unit {X : Scheme.{0}} (g : Y ⟶ X) {U : X.Opens} (h : W ≤ g ⁻¹ᵁ U) (s : Γ(X, U)ˣ) :
    Reg q σ W fun x => (valR (x ≫ g) U s.val)⁻¹ := by
  refine ⟨(g.appLE U W h).hom (s⁻¹).val, fun x _ hW => ?_⟩
  have hU : ⊤ ≤ (x ≫ g) ⁻¹ᵁ U := fun _ hz => h (hW hz)
  rw [GlobalTheory.Points.valR_appLE x g h hW]
  refine inv_eq_of_mul_eq_one_right ?_
  rw [← valR_mul _ U hU, Units.mul_inv, valR_eq _ U hU, map_one]

theorem Reg.inv_basicOpen {X : Scheme.{0}} (g : Y ⟶ X) {U : X.Opens} (s : Γ(X, U))
    (h : W ≤ g ⁻¹ᵁ X.basicOpen s) : Reg q σ W fun x => (valR (x ≫ g) U s)⁻¹ := by
  obtain ⟨r, hr⟩ := Reg.inv_unit (q := q) (σ := σ) g h (X.toRingedSpace.isUnit_res_basicOpen s).unit
  refine ⟨r, fun x hx hW => ?_⟩
  rw [← hr x hx hW]
  exact congrArg _ (valR_res (x ≫ g) (X.basicOpen_le s) (fun _ hz => h (hW hz)) s).symm

end Reg

section Val
variable {C : Type} [Field C] {X Y : Scheme.{0}}

theorem val_unit_ne_zero (x : Sp C ⟶ X) {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (s : Γ(X, U)ˣ) :
    valR x U s.val ≠ 0 := by
  rw [valR_eq x U h]
  exact (s.isUnit.map _).ne_zero

theorem val_zpow (x : Sp C ⟶ X) {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (s : Γ(X, U)ˣ) (n : ℤ) :
    valR x U (s ^ n).val = valR x U s.val ^ n := by
  rw [valR_eq x U h, valR_eq x U h, ← MonoidHom.coe_coe, ← Units.coe_map, map_zpow, Units.val_zpow_eq_zpow_val]
  rfl

theorem val_res_pull (x : Sp C ⟶ Y) (g : Y ⟶ X) {U : X.Opens} {W : Y.Opens} (e : W ≤ g ⁻¹ᵁ U)
    (h : ⊤ ≤ x ⁻¹ᵁ W) (s : Γ(X, U)ˣ) : valR x W (res e (pullU g U s)).val = valR (x ≫ g) U s.val :=
  GlobalTheory.Points.valR_appLE x g e h s.val

def tv (L : LB X) (x : Sp C ⟶ X) (i j : L.ι) : C := valR x (L.U i ⊓ L.U j) (L.g i j).val

theorem tv_ne_zero (L : LB X) {x : Sp C ⟶ X} {i j : L.ι} (hi : ⊤ ≤ x ⁻¹ᵁ L.U i) (hj : ⊤ ≤ x ⁻¹ᵁ L.U j) :
    tv L x i j ≠ 0 := val_unit_ne_zero x (U := L.U i ⊓ L.U j) (fun _ hz => ⟨hi hz, hj hz⟩) _

theorem tv_self {L : LB X} (hL : L.IsLB) {x : Sp C ⟶ X} {i : L.ι} (hi : ⊤ ≤ x ⁻¹ᵁ L.U i) :
    tv L x i i = 1 := by
  have e := congrArg (fun u : Γ(X, L.U i)ˣ => valR x (L.U i) u.val) (hL.g_self i)
  refine (valR_res x (le_inf le_rfl le_rfl) hi _).symm.trans (e.trans ?_)
  rw [valR_eq x _ hi, Units.val_one, map_one]

theorem le_wchart {L : LB X} {I : Type} [Fintype I] {φ : I → (Y ⟶ X)} {x : Sp C ⟶ Y} {j : I → L.ι}
    (h : ∀ k, ⊤ ≤ (x ≫ φ k) ⁻¹ᵁ L.U (j k)) : ⊤ ≤ x ⁻¹ᵁ LB.wchart L φ j :=
  fun _ hz => Set.mem_iInter.2 fun k => h k hz

theorem tv_linComb (L : LB X) {I : Type} [Fintype I] (φ : I → (Y ⟶ X)) (ε : I → ℤ) {x : Sp C ⟶ Y}
    {j j' : I → L.ι} (h : ∀ k, ⊤ ≤ (x ≫ φ k) ⁻¹ᵁ L.U (j k)) (h' : ∀ k, ⊤ ≤ (x ≫ φ k) ⁻¹ᵁ L.U (j' k)) :
    tv (LB.LinComb L φ ε) x j j' = ∏ k, tv L (x ≫ φ k) (j k) (j' k) ^ ε k := by
  have hh : ⊤ ≤ x ⁻¹ᵁ (LB.wchart L φ j ⊓ LB.wchart L φ j') := fun _ hz => ⟨le_wchart h hz, le_wchart h' hz⟩
  have A : ∀ u : I → Γ(Y, LB.wchart L φ j ⊓ LB.wchart L φ j')ˣ,
      valR x _ (∏ k, u k ^ ε k).val = ∏ k, valR x _ (u k).val ^ ε k := fun u => by
    rw [valR_eq x _ hh, Units.coe_prod, map_prod]
    exact Finset.prod_congr rfl fun k _ => (valR_eq x _ hh _).symm.trans (val_zpow x hh _ _)
  refine (A _).trans (Finset.prod_congr rfl fun k _ => ?_)
  exact congrArg (· ^ ε k) (val_res_pull x (φ k) (U := L.U (j k) ⊓ L.U (j' k)) _ hh (L.g (j k) (j' k)))

theorem sec_val {L : LB X} (s : L.Sec) {x : Sp C ⟶ X} {i j : L.ι} (hi : ⊤ ≤ x ⁻¹ᵁ L.U i)
    (hj : ⊤ ≤ x ⁻¹ᵁ L.U j) : valR x (L.U i) (s.f i) = tv L x i j * valR x (L.U j) (s.f j) := by
  have hh : ⊤ ≤ x ⁻¹ᵁ (L.U i ⊓ L.U j) := fun y hy => ⟨hi hy, hj hy⟩
  have e := congrArg (valR x (L.U i ⊓ L.U j)) (s.compat i j)
  rw [valR_mul x _ hh] at e
  exact (valR_res x inf_le_left hh _).symm.trans (e.trans (congrArg _ (valR_res x inf_le_right hh _)))

theorem gen_val {L : LB X} {t : L.Gen} (ht : t.IsGen) {x : Sp C ⟶ X} {i j : L.ι} (hi : ⊤ ≤ x ⁻¹ᵁ L.U i)
    (hj : ⊤ ≤ x ⁻¹ᵁ L.U j) : valR x (L.U i) (t.s i).val = tv L x i j * valR x (L.U j) (t.s j).val :=
  sec_val ⟨fun i => (t.s i).val, fun i j => congrArg Units.val (ht i j)⟩ hi hj

end Val

structure IsoVal {K C : Type} [Field K] [Field C] {X H Y : Scheme.{0}} (q : Y ⟶ Sp K) (σ : K →+* C)
    (L : LB X) (M : LB H) (ψ : Y ⟶ X) (j : Y ⟶ H) (ω : (Sp C ⟶ Y) → M.ι → L.ι → C) : Prop where
  ne : ∀ x l m, ⊤ ≤ (x ≫ j) ⁻¹ᵁ M.U l → ⊤ ≤ (x ≫ ψ) ⁻¹ᵁ L.U m → ω x l m ≠ 0
  left : ∀ x l l' m, ⊤ ≤ (x ≫ j) ⁻¹ᵁ M.U l → ⊤ ≤ (x ≫ j) ⁻¹ᵁ M.U l' → ⊤ ≤ (x ≫ ψ) ⁻¹ᵁ L.U m →
    ω x l m = tv M (x ≫ j) l l' * ω x l' m
  right : ∀ x l m m', ⊤ ≤ (x ≫ j) ⁻¹ᵁ M.U l → ⊤ ≤ (x ≫ ψ) ⁻¹ᵁ L.U m → ⊤ ≤ (x ≫ ψ) ⁻¹ᵁ L.U m' →
    ω x l m * tv L (x ≫ ψ) m m' = ω x l m'
  reg : ∀ (g : Y ⟶ Y) (W : Y.Opens) l m, W ≤ (g ≫ j) ⁻¹ᵁ M.U l → W ≤ (g ≫ ψ) ⁻¹ᵁ L.U m →
    Reg q σ W (fun x => ω (x ≫ g) l m) ∧ Reg q σ W (fun x => (ω (x ≫ g) l m)⁻¹)

theorem exists_isoVal {K C : Type} [Field K] [Field C] {X H Y : Scheme.{0}} (q : Y ⟶ Sp K) (σ : K →+* C)
    {L : LB X} {M : LB H} (hL : L.IsLB) (hM : M.IsLB) {ψ : Y ⟶ X} {j : Y ⟶ H}
    (h : LBIso (L.pull ψ) (M.pull j)) : ∃ ω, IsoVal q σ L M ψ j ω := by
  obtain ⟨w, hw⟩ := h
  have mem : ∀ {x : Sp C ⟶ Y} {l m}, ⊤ ≤ (x ≫ j) ⁻¹ᵁ M.U l → ⊤ ≤ (x ≫ ψ) ⁻¹ᵁ L.U m →
      ⊤ ≤ x ⁻¹ᵁ (LB.div (M.pull j) (L.pull ψ)).U (fun _ => l, fun _ => m) := fun hl hm _ hz =>
    ⟨Set.mem_iInter.2 fun _ => hl hz, Set.mem_iInter.2 fun _ => hm hz⟩
  have key : ∀ (x : Sp C ⟶ Y) l l' m m', ⊤ ≤ (x ≫ j) ⁻¹ᵁ M.U l → ⊤ ≤ (x ≫ j) ⁻¹ᵁ M.U l' →
      ⊤ ≤ (x ≫ ψ) ⁻¹ᵁ L.U m → ⊤ ≤ (x ≫ ψ) ⁻¹ᵁ L.U m' →
      valR x _ (w.s (fun _ => l, fun _ => m)).val =
        tv M (x ≫ j) l l' * (tv L (x ≫ ψ) m m')⁻¹ * valR x _ (w.s (fun _ => l', fun _ => m')).val := by
    intro x l l' m m' hl hl' hm hm'
    refine (gen_val hw (mem hl hm) (mem hl' hm')).trans (congrArg (· * _) ?_)
    have hh : ⊤ ≤ x ⁻¹ᵁ ((LB.div (M.pull j) (L.pull ψ)).U (fun _ => l, fun _ => m) ⊓
        (LB.div (M.pull j) (L.pull ψ)).U (fun _ => l', fun _ => m')) :=
      fun _ hz => ⟨mem hl hm hz, mem hl' hm' hz⟩
    refine (valR_mul x _ hh _ _).trans (congrArg₂ (· * ·) ?_ ?_)
    · refine (valR_res x _ hh _).trans ((tv_linComb M _ _ (fun _ => hl) (fun _ => hl')).trans ?_)
      simp
    · rw [← zpow_neg_one, ← zpow_neg_one]
      refine (val_zpow x hh _ _).trans (congrArg (· ^ (-1 : ℤ)) ?_)
      refine (valR_res x _ hh _).trans ((tv_linComb L _ _ (fun _ => hm) (fun _ => hm')).trans ?_)
      simp
  refine ⟨fun x l m => valR x _ (w.s (fun _ => l, fun _ => m)).val,
    fun x l m hl hm => val_unit_ne_zero x (mem hl hm) _, fun x l l' m hl hl' hm => ?_,
    fun x l m m' hl hm hm' => ?_, fun g W l m hl hm => ?_⟩
  · rw [key x l l' m m hl hl' hm hm, tv_self hL hm, inv_one, _root_.mul_one]
  · rw [key x l l m m' hl hl hm hm', tv_self hM hl, _root_.one_mul, mul_right_comm,
      inv_mul_cancel₀ (tv_ne_zero L hm hm'), _root_.one_mul]
  · have e : W ≤ g ⁻¹ᵁ (LB.div (M.pull j) (L.pull ψ)).U (fun _ => l, fun _ => m) := fun _ hz =>
      ⟨Set.mem_iInter.2 fun _ => hl hz, Set.mem_iInter.2 fun _ => hm hz⟩
    exact ⟨Reg.pull g e _, Reg.inv_unit g e _⟩

end GlobalTheory.ZH.FrameNorm
end
end
