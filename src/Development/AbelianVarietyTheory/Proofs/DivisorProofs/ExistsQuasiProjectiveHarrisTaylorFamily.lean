module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelKernelBoundedRepresentableOfCoprime
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRepAdjointActionLevelSiegelPullback
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLieTateLociClosedSiegelPullback
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRepresentingFamilyOfAuxiliaryRepresentatio

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorAuxiliarySymplecticLevelRepresentabl
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorStructuresRepresentableSiegelBaseCha
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorStructuresRelativelyRepresentable
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarrisTaylorObjectOverLieTateLocus
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarrisTaylorObjectOverLieTateLocus
noncomputable section

namespace GlobalTheory.HTMkObj

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor
open GlobalTheory.SiegelPull ReciprocityTheory.ChartRestriction.G.Pdiv

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {S : Scheme.{0}}

theorem lieAt_of_lieHer (b : Base D R) {A : Over S} [GrpObj A] {act : OActN D.O A} {R' : Type} [CommRing R']
    {β : R →+* R'} {x : Sp R' ⟶ S} (h : LieHer b act β x) : LieAt b act β x := by
  have H := (h R' (RingHom.id R')).1
  have e : spMap (RingHom.id R') = 𝟙 _ := Spec.map_id _
  simp only [e, Category.id_comp, RingHom.id_comp] at H
  exact H

theorem lieMult_of_lieHer (b : Base D R) {A : Over S} [GrpObj A] {act : OActN D.O A} (k : Type) [Field k]
    [IsAlgClosed k] {β : R →+* k} {x : Sp k ⟶ S} (h : LieHer b act β x) (i : Fin D.a) :
    LieMult (act.toF D) x (β.comp (b.t i)) D.m := by
  have H := (h k (RingHom.id k)).2 k (RingHom.id k) i
  have e : spMap (RingHom.id k) = 𝟙 _ := Spec.map_id _
  simp only [e, Category.id_comp, RingHom.id_comp] at H
  exact H

end GlobalTheory.HTMkObj

namespace GlobalTheory.HTMkObj

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor
open GlobalTheory.SiegelPull ReciprocityTheory.ChartRestriction.G.Pdiv
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj

theorem exists_obj_of_locus : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (h M : ℕ) (B : Type) [CommRing B] (ζ : B) (S : Scheme.{0}) (s₁ : S ⟶ Sp B) (t : S ⟶ Sp R) (c : SiegPre h M ζ s₁) (e : ℕ), e.Coprime p → SiegKerBy c e → ∀ (X : Scheme.{0}) (πX : X ⟶ S) (AX : Over X) [GrpObj AX] [IsCommMonObj AX] (φX : AX.left ⟶ c.A.left) (φ₂X : (G2 AX).left ⟶ (G2 c.A).left) (actX : OActN D.O AX) (ηX : D.La → (𝟙_ (Over X) ⟶ AX)), IsGrpPullback AX c.A πX φX → IsSquare φX φ₂X → RosatiFor D actX (c.P.pull φ₂X) → EtaOK D N actX ηX → ∀ (Z : Scheme.{0}) (j : Z ⟶ X), (∀ (R' : Type) [CommRing R'] (β : R →+* R') (x : Sp R' ⟶ Z), x ≫ j ≫ πX ≫ t = spMap β → LieHer b actX β (x ≫ j)) → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Z) (β : R →+* k), x ≫ j ≫ πX ≫ t = spMap β → GeomAt D N actX (c.P.pull φ₂X) ηX k (x ≫ j)) → ∃ (u : Obj b N ((j ≫ πX) ≫ t)) (ψ : u.A.left ⟶ AX.left) (ψ₂ : (G2 u.A).left ⟶ (G2 c.A).left), IsGrpPullback u.A AX j ψ ∧ IsSquare (ψ ≫ φX) ψ₂ ∧ LBIso u.P (c.P.pull ψ₂) ∧ (∀ a : D.O, (u.act.act a).left ≫ ψ = ψ ≫ (actX.act a).left) ∧ ∀ y, (u.eta y).left ≫ ψ = j ≫ (ηX y).left := by
  intro p _ D R _ b N _ _ h M B _ ζ S s₁ t c e he hc X πX AX _ _ φX φ₂X actX ηX hX sqX hRos hEta Z j hLie hGeom
  let A' := (Over.pullback (j ≫ πX)).obj c.A
  let φ := PullbackComparison.pφ (j ≫ πX) c.A
  let φ₂ := PullbackComparison.pφ₂ (j ≫ πX) c.A
  have pb : IsGrpPullback A' c.A (j ≫ πX) φ := PullbackComparison.isGrpPullback (j ≫ πX) c.A
  have sq : IsSquare φ φ₂ := PullbackComparison.isSquare (j ≫ πX) c.A
  have wψ : φ ≫ c.A.hom = (A'.hom ≫ j) ≫ πX := by
    rw [Category.assoc]; exact pb.1.w
  let ψ : A'.left ⟶ AX.left := hX.1.lift φ (A'.hom ≫ j) wψ
  have hψ : ψ ≫ φX = φ := hX.1.lift_fst _ _ _
  have hψh : ψ ≫ AX.hom = A'.hom ≫ j := hX.1.lift_snd _ _ _
  have pbj : IsGrpPullback A' AX j ψ := IsGrpPullback.cancel hX (by rw [hψ]; exact pb) hψh
  let ψ₂ : (G2 A').left ⟶ (G2 AX).left :=
    pullback.lift ((fst A' A').left ≫ ψ) ((snd A' A').left ≫ ψ) (by
      rw [Category.assoc, Category.assoc, hψh, ← Category.assoc, ← Category.assoc, Over.w (fst A' A'),
        Over.w (snd A' A')])
  have sqψ : IsSquare ψ ψ₂ := ⟨pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have hψ₂ : ψ₂ ≫ φ₂X = φ₂ := by
    refine pullback.hom_ext (f := c.A.hom) (g := c.A.hom) ?_ ?_
    · show (ψ₂ ≫ φ₂X) ≫ (fst c.A c.A).left = φ₂ ≫ (fst c.A c.A).left
      rw [Category.assoc, sqX.1, ← Category.assoc, sqψ.1, Category.assoc, hψ, sq.1]
    · show (ψ₂ ≫ φ₂X) ≫ (snd c.A c.A).left = φ₂ ≫ (snd c.A c.A).left
      rw [Category.assoc, sqX.2, ← Category.assoc, sqψ.2, Category.assoc, hψ, sq.2]
  have hab : IsAbelianScheme A' :=
    { comm := by have := c.ab.comm; infer_instance
      smooth := by have := c.ab.smooth; show Smooth (Limits.pullback.snd _ _); infer_instance
      proper := by have := c.ab.proper; show IsProper (Limits.pullback.snd _ _); infer_instance
      geomConnected := by
        have := c.ab.geomConnected
        show GeometricallyConnected (Limits.pullback.snd _ _); infer_instance }
  obtain ⟨act', ⟨hhom, hone, hmul, hadd⟩, hact'⟩ := GlobalTheory.ActPull.exists_act_pull X Z j AX A' ψ pbj D.Oᵐᵒᵖ
    (fun a => actX.act a.unop) (fun a => actX.hom _) (by simpa using actX.one)
    (fun a b => by simpa using actX.mul b.unop a.unop) (fun a b => by simpa using actX.add a.unop b.unop)
  let actN : OActN D.O A' :=
    { act := fun c => act' (MulOpposite.op c)
      hom := fun c => hhom _
      one := by simpa using hone
      mul := fun c d => by rw [MulOpposite.op_mul]; exact hmul _ _
      add := fun c d => by rw [MulOpposite.op_add]; exact hadd _ _ }
  have hact : ∀ c, (actN.act c).left ≫ ψ = ψ ≫ (actX.act c).left := fun c => hact' (MulOpposite.op c)
  let P' : LB (G2 A').left := c.P.pull φ₂
  have hP' : P'.IsLB := pull_isLB c.isLB φ₂
  have iso : LBIso P' (c.P.pull φ₂) := PullbackComparison.gen_refl _ hP'
  have dg := SiegelPull.diag_iso sq iso
  have hPX : (c.P.pull φ₂X).IsLB := pull_isLB c.isLB φ₂X
  have H : LBIso P' ((c.P.pull φ₂X).pull ψ₂) :=
    LBIso.chartPull (chartPullSame c.P (fun _ : PUnit => φ₂) (fun _ => 𝟙 _) (fun _ => 1) φ₂
        (fun _ => (Category.comp_id _).symm))
      (chartPullLinComb c.P φ₂X (fun _ : PUnit => ψ₂) (fun _ => 𝟙 _) (fun _ => 1) φ₂
        (fun _ => by rw [hψ₂, Category.comp_id]))
      (PullbackComparison.gen_refl _ (pull_isLB c.isLB _))
  have dgX := SiegelPull.diag_iso sqψ H
  have sqL : ∀ (x' y' : G2 A' ⟶ A') (x y : G2 AX ⟶ AX), x'.left ≫ ψ = ψ₂ ≫ x.left → y'.left ≫ ψ = ψ₂ ≫ y.left →
      (lift x' y').left ≫ ψ₂ = ψ₂ ≫ (lift x y).left := fun x' y' x y hx hy =>
    (Category.id_comp _).symm.trans (SiegelPull.lift_sq sqψ (T := Over.mk (ψ₂ ≫ (G2 AX).hom)) (T' := G2 A') (𝟙 _)
      x' y' (Z := G2 AX) ψ₂ x y (by rw [Category.id_comp]; exact hx) (by rw [Category.id_comp]; exact hy))
  have rosP : RosatiFor D actN ((c.P.pull φ₂X).pull ψ₂) := fun a => LBIso.chartPull
    (chartPullLinComb (c.P.pull φ₂X) _ _ _ _ ψ₂ (fun _ => sqL _ _ _ _ (by
      rw [Over.comp_left, Over.comp_left, Category.assoc, hact, ← Category.assoc, ← sqψ.1, Category.assoc])
      (by rw [sqψ.2])))
    (chartPullLinComb (c.P.pull φ₂X) _ _ _ _ ψ₂ (fun _ => sqL _ _ _ _ (by rw [sqψ.1]) (by
      rw [Over.comp_left, Over.comp_left, Category.assoc, hact, ← Category.assoc, ← sqψ.2, Category.assoc])))
    (hRos a)
  obtain ⟨t₁, ht₁⟩ := c.rig₁
  obtain ⟨t₂, ht₂⟩ := c.rig₂
  let u : Obj b N ((j ≫ πX) ≫ t) :=
    { A := A'
      ab := hab
      act := actN
      P := P'
      isLB := hP'
      rig₁ := gen_chartPull (chartPullLinComb c.P _ _ _ _ φ (fun _ => PullbackComparison.lift_one_id (j ≫ πX) c.A)) t₁ ht₁
      rig₂ := gen_chartPull (chartPullLinComb c.P _ _ _ _ φ (fun _ => PullbackComparison.lift_id_one (j ≫ πX) c.A)) t₂ ht₂
      symm := LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull c.P _ _ rfl)
        (chartPullLinComb c.P _ _ _ _ φ₂ (fun _ => PullbackComparison.lift_swap (j ≫ πX) c.A)) c.symm
      ample := (pol_pull S Z c.A A' (j ≫ πX) φ _ _ (pull_isLB c.isLB _) (pull_isLB hP' _) c.ab pb dg).2.1 hc.1
      kerP := ⟨e, he, fun T x hx => kerBy_pull pb sq c.isLB hP' iso e hc.2 T x hx⟩
      rosati := RosatiFor.of_iso (pull_isLB hPX _) hP' (LBIso.symm H) rosP
      lie := fun R' _ β x hx v hv => by
        have hx' : x ≫ j ≫ πX ≫ t = spMap β := by simpa only [Category.assoc] using hx
        obtain ⟨e, he⟩ := GlobalTheory.LiePull.exists_pushEquiv pbj (epsPtR x) (spMap (algebraMap R' (DualNumber R')) ≫ x ≫ j)
          (Category.assoc _ _ _).symm
        obtain ⟨w, hw, hvw⟩ := lieAt_of_lieHer b (hLie R' β x hx') (e v)
          ((HTPull.isTanScal_iff pbj actX actN hact x e he _ _ v).1 hv)
        refine ⟨fun i => e.symm (w i), fun i c => (HTPull.isTanScal_iff pbj actX actN hact x e he _ _ _).2
          (by rw [e.apply_symm_apply]; exact hw i c), e.injective ?_⟩
        rw [hvw, map_list_prod, List.map_ofFn]
        simp [Function.comp_def]
      lieRank := fun k _ _ x β hx i => by
        have hx' : x ≫ j ≫ πX ≫ t = spMap β := by simpa only [Category.assoc] using hx
        exact (GlobalTheory.LiePull.lieMult_pull (𝓞 D.F) X Z AX A' j ψ (actX.toF D) (actN.toF D) pbj
          (fun c => hact _) k x (β.comp (b.t i)) D.m).2 (lieMult_of_lieHer b k (hLie k β x hx') i)
      eta := fun y => SiegelPull.secPull pbj (ηX y)
      eta_add := fun y z => SiegelPull.push_injective pbj _ (by
        rw [map_mul, push_secPull', push_secPull', push_secPull', hEta.1, MonObj.comp_mul])
      eta_lin := fun c y => SiegelPull.push_injective pbj _ (by
        rw [HTPull.push_comp pbj (hact c), push_secPull', push_secPull', hEta.2.1, Category.assoc])
      eta_ker := fun y => SiegelPull.push_injective pbj _ (by
        rw [push_secPull', hEta.2.2, map_one, MonObj.comp_one])
      geom := fun k _ _ x β hx => by
        have hx' : x ≫ j ≫ πX ≫ t = spMap β := by simpa only [Category.assoc] using hx
        obtain ⟨I, hI⟩ := hGeom k x β hx'
        let e : (Over.mk x ⟶ A') ≃* (Over.mk (x ≫ j) ⟶ AX) := MulEquiv.ofBijective (pushHom pbj (Over.mk x))
          ⟨SiegelPull.push_injective pbj _, SiegelPull.push_surjective pbj _⟩
        have ea : ∀ c g, e (g ≫ actN.act c) = e g ≫ actX.act c := fun c g => HTPull.push_comp pbj (hact c) _ g
        have ex : ∀ z, z.left = (e.symm z).left ≫ ψ := fun z =>
          (congrArg (fun q => q.left) (e.apply_symm_apply z)).symm
        refine ⟨{ ζ := I.ζ, ζ_prim := I.ζ_prim, ζ_pow := I.ζ_pow, ev := fun n y => e.symm (I.ev n y)
                  add := fun n y z => by rw [I.add, map_mul]
                  lin := fun n c y => e.injective (by rw [ea, e.apply_symm_apply, e.apply_symm_apply, I.lin])
                  ker := fun n hn hp y => by rw [map_eq_one_iff _ e.symm.injective]; exact I.ker n hn hp y
                  onto := fun n hn hp q => by
                    rw [← map_eq_one_iff e e.injective, map_pow, I.onto n hn hp (e q)]
                    exact exists_congr fun y => e.symm_apply_eq.symm
                  tower := fun n m hn hm hp y => by rw [← map_pow, I.tower n m hn hm hp]
                  isom := fun n hn hp y z => (weilIs_grpPullback_of_comm X Z AX A' j ψ _ _ (pull_isLB hPX _)
                    (pull_isLB hP' _) pbj dgX (Over.mk x) n _ _ (I.ev n y) (I.ev n z) _ (ex _) (ex _)).2
                    (I.isom n hn hp y z) }, fun y => ?_⟩
        show toUnit _ ≫ SiegelPull.secPull pbj (ηX y) = e.symm (I.ev N y)
        rw [eq_comm, e.symm_apply_eq, ← hI y]
        exact (SiegelPull.push_secPull pbj (ηX y) (Over.mk x)).symm }
  exact ⟨u, ψ, φ₂, pbj, by rw [hψ]; exact sq, iso, hact, fun y => SiegelPull.secPull_left pbj _⟩

end GlobalTheory.HTMkObj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarrisTaylorObjectOverLieTateLocusStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_harrisTaylorObject_over_lieTate_locus : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (h M : ℕ) (B : Type) [CommRing B] (ζ : B) (S : Scheme.{0}) (s₁ : S ⟶ Sp B) (t : S ⟶ Sp R) (c : SiegPre h M ζ s₁) (e : ℕ), e.Coprime p → SiegKerBy c e → ∀ (X : Scheme.{0}) (πX : X ⟶ S) (AX : Over X) [GrpObj AX] [IsCommMonObj AX] (φX : AX.left ⟶ c.A.left) (φ₂X : (G2 AX).left ⟶ (G2 c.A).left) (actX : OActN D.O AX) (ηX : D.La → (𝟙_ (Over X) ⟶ AX)), IsGrpPullback AX c.A πX φX → IsSquare φX φ₂X → RosatiFor D actX (c.P.pull φ₂X) → EtaOK D N actX ηX → ∀ (Z : Scheme.{0}) (j : Z ⟶ X), (∀ (R' : Type) [CommRing R'] (β : R →+* R') (x : Sp R' ⟶ Z), x ≫ j ≫ πX ≫ t = spMap β → LieHer b actX β (x ≫ j)) → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Z) (β : R →+* k), x ≫ j ≫ πX ≫ t = spMap β → GeomAt D N actX (c.P.pull φ₂X) ηX k (x ≫ j)) → ∃ (u : Obj b N ((j ≫ πX) ≫ t)) (ψ : u.A.left ⟶ AX.left) (ψ₂ : (G2 u.A).left ⟶ (G2 c.A).left), IsGrpPullback u.A AX j ψ ∧ IsSquare (ψ ≫ φX) ψ₂ ∧ LBIso u.P (c.P.pull ψ₂) ∧ (∀ a : D.O, (u.act.act a).left ≫ ψ = ψ ≫ (actX.act a).left) ∧ ∀ y, (u.eta y).left ≫ ψ = j ≫ (ηX y).left := by
  first | (exact @GlobalTheory.HTMkObj.exists_obj_of_locus) | (exact GlobalTheory.HTMkObj.exists_obj_of_locus) | (intros; apply GlobalTheory.HTMkObj.exists_obj_of_locus <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLieTateConditionsIffPullbacks
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLieTateConditionsIffPullbacks
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor

noncomputable section

namespace GlobalTheory.HTTransport

open ReciprocityTheory.ChartRestriction.G.Pdiv

variable {p : ℕ} [Fact p.Prime] {D : Datum p}

def tateTransport {k : Type} [Field k] {Q Q' : Type} [Group Q] [Group Q'] {act : D.O → Q → Q}
    {act' : D.O → Q' → Q'} {E : ℕ → Q → Q → kˣ → Prop} {E' : ℕ → Q' → Q' → kˣ → Prop}
    (I : TateIsoO D k Q act E) (e : Q ≃* Q') (ha : ∀ c g, e (act c g) = act' c (e g))
    (hE : ∀ n g g' u, E n g g' u → E' n (e g) (e g') u) : TateIsoO D k Q' act' E' where
  ζ := I.ζ
  ζ_prim := I.ζ_prim
  ζ_pow := I.ζ_pow
  ev n y := e (I.ev n y)
  add n x y := by rw [I.add, map_mul]
  lin n c x := by rw [I.lin, ha]
  ker n hn hp x := by rw [map_eq_one_iff _ e.injective]; exact I.ker n hn hp x
  onto n hn hp q := by
    rw [← map_eq_one_iff e.symm e.symm.injective, map_pow, I.onto n hn hp]
    exact exists_congr fun y => ⟨fun h => by rw [h, e.apply_symm_apply], fun h => by rw [← h, e.symm_apply_apply]⟩
  tower n m hn hm hp x := by rw [← map_pow, I.tower n m hn hm hp]
  isom n hn hp x y := hE _ _ _ _ (I.isom n hn hp x y)

theorem exists_tate_iff {k : Type} [Field k] {Q Q' : Type} [Group Q] [Group Q'] {act : D.O → Q → Q}
    {act' : D.O → Q' → Q'} {E : ℕ → Q → Q → kˣ → Prop} {E' : ℕ → Q' → Q' → kˣ → Prop}
    (e : Q ≃* Q') (ha : ∀ c g, e (act c g) = act' c (e g))
    (hE : ∀ n g g' u, E n g g' u ↔ E' n (e g) (e g') u) (N : ℕ) (l : D.La → Q) (l' : D.La → Q')
    (hl : ∀ y, e (l y) = l' y) :
    (∃ I : TateIsoO D k Q act E, ∀ y, l y = I.ev N y) ↔ (∃ I : TateIsoO D k Q' act' E', ∀ y, l' y = I.ev N y) := by
  constructor
  · rintro ⟨I, hI⟩
    exact ⟨tateTransport I e ha fun n g g' u => (hE n g g' u).1, fun y => by rw [← hl, hI]; rfl⟩
  · rintro ⟨I, hI⟩
    refine ⟨tateTransport I e.symm (fun c g => e.injective (by rw [e.apply_symm_apply, ha, e.apply_symm_apply]))
      (fun n g g' u h => (hE n _ _ u).2 (by rw [e.apply_symm_apply, e.apply_symm_apply]; exact h)), fun y => ?_⟩
    show l y = e.symm (I.ev N y)
    rw [← hI y, ← hl y, e.symm_apply_apply]

variable {R : Type} [CommRing R] (b : Base D R) {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} [GrpObj A]
  [GrpObj A'] {f : S' ⟶ S} {φ : A'.left ⟶ A.left}

theorem lieAt_iff (pb : IsGrpPullback A' A f φ) (act : OActN D.O A) (act' : OActN D.O A')
    (hact : ∀ c, (act'.act c).left ≫ φ = φ ≫ (act.act c).left) {R' : Type} [CommRing R'] (β : R →+* R')
    (x : Sp R' ⟶ S') : LieAt b act' β x ↔ LieAt b act β (x ≫ f) := by
  obtain ⟨e, he⟩ := GlobalTheory.LiePull.exists_pushEquiv pb (epsPtR x) (spMap (algebraMap R' (DualNumber R')) ≫ x ≫ f)
    (Category.assoc _ _ _).symm
  have key := fun c r v => GlobalTheory.HTPull.isTanScal_iff pb act act' hact x e he c r v
  constructor
  · intro H v hv
    obtain ⟨w, hw, hvw⟩ := H (e.symm v) ((key _ _ _).2 (by rw [e.apply_symm_apply]; exact hv))
    refine ⟨fun i => e (w i), fun i c => (key _ _ _).1 (hw i c), ?_⟩
    rw [← e.apply_symm_apply v, hvw, map_list_prod, List.map_ofFn]
    rfl
  · intro H v hv
    obtain ⟨w, hw, hvw⟩ := H (e v) ((key _ _ _).1 hv)
    refine ⟨fun i => e.symm (w i), fun i c => (key _ _ _).2 (by rw [e.apply_symm_apply]; exact hw i c),
      e.injective ?_⟩
    rw [hvw, map_list_prod, List.map_ofFn]
    simp [Function.comp_def]

theorem lieRankAt_iff (pb : IsGrpPullback A' A f φ) (act : OActN D.O A) (act' : OActN D.O A')
    (hact : ∀ c, (act'.act c).left ≫ φ = φ ≫ (act.act c).left) {R' : Type} [CommRing R'] (β : R →+* R')
    (x : Sp R' ⟶ S') : LieRankAt b act' β x ↔ LieRankAt b act β (x ≫ f) := by
  refine forall_congr' fun k => forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun g =>
    forall_congr' fun i => ?_
  have h := GlobalTheory.LiePull.lieMult_pull (𝓞 D.F) S S' A A' f φ (act.toF D) (act'.toF D) pb (fun c => hact _) k
    (spMap g ≫ x) ((g.comp β).comp (b.t i)) D.m
  rwa [Category.assoc] at h

theorem lieHer_iff (pb : IsGrpPullback A' A f φ) (act : OActN D.O A) (act' : OActN D.O A')
    (hact : ∀ c, (act'.act c).left ≫ φ = φ ≫ (act.act c).left) {R' : Type} [CommRing R'] (β : R →+* R')
    (x : Sp R' ⟶ S') : LieHer b act' β x ↔ LieHer b act β (x ≫ f) := by
  refine forall_congr' fun R'' => forall_congr' fun _ => forall_congr' fun g => ?_
  have h1 := lieAt_iff b pb act act' hact (g.comp β) (spMap g ≫ x)
  have h2 := lieRankAt_iff b pb act act' hact (g.comp β) (spMap g ≫ x)
  rw [Category.assoc] at h1 h2
  exact and_congr h1 h2

theorem geomAt_iff [IsCommMonObj A] (pb : IsGrpPullback A' A f φ) (act : OActN D.O A) (act' : OActN D.O A')
    (hact : ∀ c, (act'.act c).left ≫ φ = φ ≫ (act.act c).left) (P : LB (G2 A).left) (P' : LB (G2 A').left)
    (hP : P.IsLB) (hP' : P'.IsLB) (φ₂ : (G2 A').left ⟶ (G2 A).left) (sq : IsSquare φ φ₂)
    (H : LBIso P' (P.pull φ₂)) (eta : D.La → (𝟙_ (Over S) ⟶ A)) (eta' : D.La → (𝟙_ (Over S') ⟶ A'))
    (heta : ∀ y, (eta' y).left ≫ φ = f ≫ (eta y).left) (N : ℕ) (k : Type) [Field k] (x : Sp k ⟶ S') :
    GeomAt D N act' P' eta' k x ↔ GeomAt D N act P eta k (x ≫ f) := by
  have dg := SiegelPull.diag_iso sq H
  let e : (Over.mk x ⟶ A') ≃* (Over.mk (x ≫ f) ⟶ A) := MulEquiv.ofBijective (pushHom pb (Over.mk x))
    ⟨SiegelPull.push_injective pb _, SiegelPull.push_surjective pb _⟩
  have hel : ∀ g, (e g).left = g.left ≫ φ := fun g => rfl
  refine exists_tate_iff e (fun c g => GlobalTheory.HTPull.push_comp pb (hact c) _ g) (fun n g g' u => ?_) N _ _
    (fun y => ?_)
  · exact weilIs_grpPullback_of_comm S S' A A' f φ _ _ (pull_isLB hP _) (pull_isLB hP' _) pb dg (Over.mk x) n
      g g' (e g) (e g') _ (hel g) (hel g')
  · apply Over.OverMorphism.ext
    show ((toUnit (Over.mk x)).left ≫ (eta' y).left) ≫ φ = (toUnit (Over.mk (x ≫ f))).left ≫ (eta y).left
    rw [Category.assoc, heta, Over.toUnit_left, Over.toUnit_left, ← Category.assoc]
    rfl

end GlobalTheory.HTTransport

namespace GlobalTheory.HTTransport

open ReciprocityTheory.ChartRestriction.G.Pdiv

theorem lieHer_geomAt_iff : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (S₀ : Scheme.{0}) (A₀ : Over S₀) [GrpObj A₀] [IsCommMonObj A₀] (P₀ : LB (G2 A₀).left), P₀.IsLB → ∀ (X T : Scheme.{0}) (πX : X ⟶ S₀) (z : T ⟶ X) (AX : Over X) [GrpObj AX] [IsCommMonObj AX] (AT : Over T) [GrpObj AT] [IsCommMonObj AT] (φX : AX.left ⟶ A₀.left) (φ₂X : (G2 AX).left ⟶ (G2 A₀).left) (φT : AT.left ⟶ A₀.left) (φ₂T : (G2 AT).left ⟶ (G2 A₀).left) (ψ : AT.left ⟶ AX.left) (actX : OActN D.O AX) (actT : OActN D.O AT) (ηX : D.La → (𝟙_ (Over X) ⟶ AX)) (ηT : D.La → (𝟙_ (Over T) ⟶ AT)) (PT : LB (G2 AT).left), PT.IsLB → IsGrpPullback AX A₀ πX φX → IsSquare φX φ₂X → IsGrpPullback AT A₀ (z ≫ πX) φT → IsSquare φT φ₂T → IsGrpPullback AT AX z ψ → ψ ≫ φX = φT → LBIso PT (P₀.pull φ₂T) → (∀ a : D.O, (actT.act a).left ≫ ψ = ψ ≫ (actX.act a).left) → (∀ y, (ηT y).left ≫ ψ = z ≫ (ηX y).left) → (∀ (R' : Type) [CommRing R'] (β : R →+* R') (x : Sp R' ⟶ T), LieHer b actT β x ↔ LieHer b actX β (x ≫ z)) ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ T), GeomAt D N actT PT ηT k x ↔ GeomAt D N actX (P₀.pull φ₂X) ηX k (x ≫ z) := by
  intro p _ D R _ b N S₀ A₀ _ _ P₀ hP₀ X T πX z AX _ _ AT _ _ φX φ₂X φT φ₂T ψ actX actT ηX ηT PT hPT _ sqX _ sqT
    pbψ hψ H hact hη
  have w : ((fst AT AT).left ≫ ψ) ≫ AX.hom = ((snd AT AT).left ≫ ψ) ≫ AX.hom := by
    rw [Category.assoc, Category.assoc, pbψ.1.w, ← Category.assoc, ← Category.assoc, Over.w, Over.w]
  let ψ₂ : (G2 AT).left ⟶ (G2 AX).left := pullback.lift _ _ w
  have sqψ : IsSquare ψ ψ₂ := ⟨pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have hcomp : ψ₂ ≫ φ₂X = φ₂T := by
    have h1 : (ψ₂ ≫ φ₂X) ≫ (fst A₀ A₀).left = φ₂T ≫ (fst A₀ A₀).left := by
      rw [Category.assoc, sqX.1, ← Category.assoc, sqψ.1, Category.assoc, hψ, sqT.1]
    have h2 : (ψ₂ ≫ φ₂X) ≫ (snd A₀ A₀).left = φ₂T ≫ (snd A₀ A₀).left := by
      rw [Category.assoc, sqX.2, ← Category.assoc, sqψ.2, Category.assoc, hψ, sqT.2]
    exact Over.tensorObj_ext _ _ h1 h2
  have hB : ((P₀.pull φ₂X).pull ψ₂).IsLB := pull_isLB (pull_isLB hP₀ _) _
  have iso : LBIso PT ((P₀.pull φ₂X).pull ψ₂) :=
    LBIso.trans hPT (pull_isLB hP₀ _) hB H
      (LBIso.chartPull (GlobalTheory.RigidBundleGlue.chartPullComp P₀ φ₂X ψ₂ φ₂T hcomp.symm) (chartPullId _)
        (PullbackComparison.gen_refl _ hB))
  exact ⟨fun R' _ β x => lieHer_iff b pbψ actX actT hact β x,
    fun k _ _ x => geomAt_iff pbψ actX actT hact (P₀.pull φ₂X) PT (pull_isLB hP₀ _) hPT ψ₂ sqψ iso ηX ηT hη N k x⟩

end GlobalTheory.HTTransport
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLieTateConditionsIffPullbacksStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylorLie_tate_conditions_iff_pullbacks : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (S₀ : Scheme.{0}) (A₀ : Over S₀) [GrpObj A₀] [IsCommMonObj A₀] (P₀ : LB (G2 A₀).left), P₀.IsLB → ∀ (X T : Scheme.{0}) (πX : X ⟶ S₀) (z : T ⟶ X) (AX : Over X) [GrpObj AX] [IsCommMonObj AX] (AT : Over T) [GrpObj AT] [IsCommMonObj AT] (φX : AX.left ⟶ A₀.left) (φ₂X : (G2 AX).left ⟶ (G2 A₀).left) (φT : AT.left ⟶ A₀.left) (φ₂T : (G2 AT).left ⟶ (G2 A₀).left) (ψ : AT.left ⟶ AX.left) (actX : OActN D.O AX) (actT : OActN D.O AT) (ηX : D.La → (𝟙_ (Over X) ⟶ AX)) (ηT : D.La → (𝟙_ (Over T) ⟶ AT)) (PT : LB (G2 AT).left), PT.IsLB → IsGrpPullback AX A₀ πX φX → IsSquare φX φ₂X → IsGrpPullback AT A₀ (z ≫ πX) φT → IsSquare φT φ₂T → IsGrpPullback AT AX z ψ → ψ ≫ φX = φT → LBIso PT (P₀.pull φ₂T) → (∀ a : D.O, (actT.act a).left ≫ ψ = ψ ≫ (actX.act a).left) → (∀ y, (ηT y).left ≫ ψ = z ≫ (ηX y).left) → (∀ (R' : Type) [CommRing R'] (β : R →+* R') (x : Sp R' ⟶ T), LieHer b actT β x ↔ LieHer b actX β (x ≫ z)) ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ T), GeomAt D N actT PT ηT k x ↔ GeomAt D N actX (P₀.pull φ₂X) ηX k (x ≫ z) := by
  first | (exact @GlobalTheory.HTTransport.lieHer_geomAt_iff) | (exact GlobalTheory.HTTransport.lieHer_geomAt_iff) | (intros; apply GlobalTheory.HTTransport.lieHer_geomAt_iff  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarrisTaylorObjectMapOfCommonPullback
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarrisTaylorObjectMapOfCommonPullback
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor

noncomputable section

namespace GlobalTheory.HTObjMap

theorem exists_objMap_of_common_pullback : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (S₀ : Scheme.{0}) (A₀ : Over S₀) [GrpObj A₀] (P₀ : LB (G2 A₀).left), P₀.IsLB → ∀ (T Z : Scheme.{0}) (t₁ : T ⟶ Sp R) (t₂ : Z ⟶ Sp R) (o : Obj b N t₁) (u : Obj b N t₂) (g : T ⟶ S₀) (πZ : Z ⟶ S₀) (z : T ⟶ Z) (φo : o.A.left ⟶ A₀.left) (φ₂o : (G2 o.A).left ⟶ (G2 A₀).left) (φu : u.A.left ⟶ A₀.left) (φ₂u : (G2 u.A).left ⟶ (G2 A₀).left) (ψ : o.A.left ⟶ u.A.left), IsGrpPullback o.A A₀ g φo → IsSquare φo φ₂o → LBIso o.P (P₀.pull φ₂o) → IsGrpPullback u.A A₀ πZ φu → IsSquare φu φ₂u → LBIso u.P (P₀.pull φ₂u) → z ≫ πZ = g → ψ ≫ φu = φo → ψ ≫ u.A.hom = o.A.hom ≫ z → (∀ a : D.O, (o.act.act a).left ≫ ψ = ψ ≫ (u.act.act a).left) → (∀ y, (o.eta y).left ≫ ψ = z ≫ (u.eta y).left) → ∃ m : ObjMap o u z, m.φ = ψ := by
  intro p _ D R _ b N S₀ A₀ _ P₀ hP₀ T Z t₁ t₂ o u g πZ z φo φ₂o φu φ₂u ψ ho sqo io hu squ iu hz hψ hw hact heta
  have cart : IsGrpPullback o.A u.A z ψ := IsGrpPullback.cancel hu (by rw [hz, hψ]; exact ho) hw
  have wc : ((fst o.A o.A).left ≫ ψ) ≫ u.A.hom = ((snd o.A o.A).left ≫ ψ) ≫ u.A.hom := by
    rw [Category.assoc, Category.assoc, hw, ← Category.assoc, ← Category.assoc, Over.w (fst o.A o.A), Over.w (snd o.A o.A)]
  let φ₂ : (G2 o.A).left ⟶ (G2 u.A).left := pullback.lift ((fst o.A o.A).left ≫ ψ) ((snd o.A o.A).left ≫ ψ) wc
  have s₁ : φ₂ ≫ (fst u.A u.A).left = (fst o.A o.A).left ≫ ψ := pullback.lift_fst _ _ _
  have s₂ : φ₂ ≫ (snd u.A u.A).left = (snd o.A o.A).left ≫ ψ := pullback.lift_snd _ _ _
  have sq : IsSquare ψ φ₂ := ⟨s₁, s₂⟩
  have a₁ : (φ₂ ≫ φ₂u) ≫ (fst A₀ A₀).left = φ₂o ≫ (fst A₀ A₀).left := by
    rw [Category.assoc, squ.1, ← Category.assoc, s₁, Category.assoc, hψ, sqo.1]
  have a₂ : (φ₂ ≫ φ₂u) ≫ (snd A₀ A₀).left = φ₂o ≫ (snd A₀ A₀).left := by
    rw [Category.assoc, squ.2, ← Category.assoc, s₂, Category.assoc, hψ, sqo.2]
  have e₂ : φ₂ ≫ φ₂u = φ₂o := Over.tensorObj_ext _ _ a₁ a₂
  have i₂ : LBIso (P₀.pull φ₂o) (u.P.pull φ₂) :=
    LBIso.chartPull (chartPullSame P₀ _ _ _ φ₂ (fun _ => e₂.symm)) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull u.P φ₂ φ₂ rfl) (LBIso.symm iu)
  have pol : LBIso o.P (u.P.pull φ₂) :=
    LBIso.trans o.isLB (pull_isLB hP₀ _) (pull_isLB u.isLB _) io i₂
  exact ⟨{ φ := ψ, φ₂ := φ₂, cart := cart, sq := sq, act := hact, pol := pol, eta := heta }, rfl⟩

end GlobalTheory.HTObjMap
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarrisTaylorObjectMapOfCommonPullbackStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_harrisTaylorObjectMap_of_common_pullback : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (S₀ : Scheme.{0}) (A₀ : Over S₀) [GrpObj A₀] (P₀ : LB (G2 A₀).left), P₀.IsLB → ∀ (T Z : Scheme.{0}) (t₁ : T ⟶ Sp R) (t₂ : Z ⟶ Sp R) (o : Obj b N t₁) (u : Obj b N t₂) (g : T ⟶ S₀) (πZ : Z ⟶ S₀) (z : T ⟶ Z) (φo : o.A.left ⟶ A₀.left) (φ₂o : (G2 o.A).left ⟶ (G2 A₀).left) (φu : u.A.left ⟶ A₀.left) (φ₂u : (G2 u.A).left ⟶ (G2 A₀).left) (ψ : o.A.left ⟶ u.A.left), IsGrpPullback o.A A₀ g φo → IsSquare φo φ₂o → LBIso o.P (P₀.pull φ₂o) → IsGrpPullback u.A A₀ πZ φu → IsSquare φu φ₂u → LBIso u.P (P₀.pull φ₂u) → z ≫ πZ = g → ψ ≫ φu = φo → ψ ≫ u.A.hom = o.A.hom ≫ z → (∀ a : D.O, (o.act.act a).left ≫ ψ = ψ ≫ (u.act.act a).left) → (∀ y, (o.eta y).left ≫ ψ = z ≫ (u.eta y).left) → ∃ m : ObjMap o u z, m.φ = ψ := by
  first | (exact @GlobalTheory.HTObjMap.exists_objMap_of_common_pullback) | (exact GlobalTheory.HTObjMap.exists_objMap_of_common_pullback) | (intros; apply GlobalTheory.HTObjMap.exists_objMap_of_common_pullback  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorStructuresRelativelyRepresentable
noncomputable section

namespace GlobalTheory.UPel.HT

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor

theorem relRep_htPull : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (h M : ℕ) (B : Type) [CommRing B] (ζ : B) (S : Scheme.{0}) [IsLocallyNoetherian S] (s₁ : S ⟶ Sp B) (t : S ⟶ Sp R) (c : SiegPre h M ζ s₁) (e : ℕ), e.Coprime p → SiegKerBy c e → ∃ (Z : Scheme.{0}) (π : Z ⟶ S) (u : Obj b N (π ≫ t)) (φu : u.A.left ⟶ c.A.left) (φ₂u : (G2 u.A).left ⟶ (G2 c.A).left), IsGrpPullback u.A c.A π φu ∧ IsSquare φu φ₂u ∧ LBIso u.P (c.P.pull φ₂u) ∧ IsFinite π ∧ ∀ (T : Scheme.{0}) (g : T ⟶ S) (t' : T ⟶ Sp R) (o : Obj b N t') (φ : o.A.left ⟶ c.A.left) (φ₂ : (G2 o.A).left ⟶ (G2 c.A).left), g ≫ t = t' → IsGrpPullback o.A c.A g φ → IsSquare φ φ₂ → LBIso o.P (c.P.pull φ₂) → ∃! z : T ⟶ Z, z ≫ π = g ∧ ∃ m : ObjMap o u z, m.φ ≫ φu = φ := by
  intro p _ D R _ b N hN hNp h M B _ ζ S _ s₁ t c e he hc
  obtain ⟨E, πE, AE, _, _, φE, φ₂E, actE, ηE, hEn, hEf, pbE, sqE, rosE, etaE, univE⟩ :=
    GlobalTheory.T.exists_rep_adjointAction_level_siegelPullback p D R b N hNp h M B ζ S s₁ t c e he hc
  obtain ⟨Z, j, hj, hZ⟩ := GlobalTheory.T.harrisTaylor_lie_tate_loci_closed_siegelPullback p D R b N hN hNp h M B ζ S s₁ t c e he hc E πE AE φE φ₂E actE ηE
    pbE sqE rosE etaE
  have hZj := (hZ Z j).1 ⟨𝟙 Z, Category.id_comp _⟩
  obtain ⟨u, ψ, ψ₂, pbu, squ, isou, actu, etau⟩ := GlobalTheory.T.exists_harrisTaylorObject_over_lieTate_locus p D R b N hN hNp h M B ζ S s₁ t c e he hc E πE AE
    φE φ₂E actE ηE pbE sqE rosE etaE Z j hZj.1 hZj.2
  haveI : IsFinite πE := hEf
  haveI : Mono j := inferInstance
  refine ⟨Z, j ≫ πE, u, ψ ≫ φE, ψ₂, pbu.comp pbE, squ, isou, inferInstance, ?_⟩
  intro T g t' o φ φ₂ hgt pbo sqo isoo
  have rosO : RosatiFor D o.act (c.P.pull φ₂) :=
    RosatiFor.of_iso o.isLB (pull_isLB c.isLB _) isoo o.rosatiFor
  obtain ⟨z₀, ⟨hz₀, ψ₀, pb₀, hψ₀, act₀, eta₀⟩, uniq₀⟩ := univE T g o.A φ φ₂ o.act o.eta pbo sqo rosO o.etaOK
  have pbo' : IsGrpPullback o.A c.A (z₀ ≫ πE) φ := by rw [hz₀]; exact pbo
  have tr := GlobalTheory.T.harrisTaylorLie_tate_conditions_iff_pullbacks p D R b N S c.A c.P c.isLB E T πE z₀ AE o.A φE φ₂E φ φ₂ ψ₀ actE o.act ηE o.eta o.P
    o.isLB pbE sqE pbo' sqo pb₀ hψ₀ isoo act₀ eta₀
  have hpt : ∀ {R' : Type} [CommRing R'] (β : R →+* R') (x : Sp R' ⟶ T), x ≫ z₀ ≫ πE ≫ t = spMap β →
      x ≫ t' = spMap β := fun β x hx => by
    rw [← hgt, ← hz₀]; simpa [Category.assoc] using hx
  obtain ⟨z, hz⟩ := (hZ T z₀).2 ⟨fun R' _ β x hx => (tr.1 R' β x).1 (o.lieHer R' β x (hpt β x hx)),
    fun k _ _ x β hx => (tr.2 k x).1 (o.geomAt k x β (hpt β x hx))⟩
  have w : ψ₀ ≫ AE.hom = (o.A.hom ≫ z) ≫ j := by rw [pb₀.1.w, Category.assoc, hz]
  let ψ' := pbu.1.lift ψ₀ (o.A.hom ≫ z) w
  have h1 : ψ' ≫ ψ = ψ₀ := pbu.1.lift_fst _ _ _
  have h2 : ψ' ≫ u.A.hom = o.A.hom ≫ z := pbu.1.lift_snd _ _ _
  have hact : ∀ a : D.O, (o.act.act a).left ≫ ψ' = ψ' ≫ (u.act.act a).left := fun a => by
    apply pbu.1.hom_ext
    · rw [Category.assoc, h1, act₀, Category.assoc, actu, ← Category.assoc, h1]
    · rw [Category.assoc, h2, Category.assoc, Over.w (u.act.act a), h2, ← Category.assoc,
        Over.w (o.act.act a)]
  have heta : ∀ y, (o.eta y).left ≫ ψ' = z ≫ (u.eta y).left := fun y => by
    apply pbu.1.hom_ext
    · rw [Category.assoc, h1, eta₀, Category.assoc, etau, ← Category.assoc, hz]
    · rw [Category.assoc, h2, Category.assoc, Over.w (u.eta y), ← Category.assoc, Over.w (o.eta y)]
      simp
  obtain ⟨m, hm⟩ := GlobalTheory.T.exists_harrisTaylorObjectMap_of_common_pullback p D R b N S c.A c.P c.isLB T Z t' ((j ≫ πE) ≫ t) o u g (j ≫ πE) z φ φ₂
    (ψ ≫ φE) ψ₂ ψ' pbo sqo isoo (pbu.comp pbE) squ isou (by rw [← Category.assoc, hz, hz₀])
    (by rw [← Category.assoc, h1, hψ₀]) h2 hact heta
  refine ⟨z, ⟨by rw [← Category.assoc, hz, hz₀], m, by rw [hm, ← Category.assoc, h1, hψ₀]⟩, ?_⟩
  rintro z' ⟨hz', m', hm'⟩
  have e₀ : z' ≫ j = z₀ := uniq₀ (z' ≫ j) ⟨by rw [Category.assoc]; exact hz', m'.φ ≫ ψ, m'.cart.comp pbu,
    by rw [Category.assoc]; exact hm',
    fun a => by rw [← Category.assoc, m'.act a, Category.assoc, actu]; exact (Category.assoc _ _ _).symm,
    fun y => by rw [← Category.assoc, m'.eta y, Category.assoc, etau]; exact (Category.assoc _ _ _).symm⟩
  exact (cancel_mono j).1 (e₀.trans hz.symm)

end GlobalTheory.UPel.HT
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorStructuresRelativelyRepresentableStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylor_structures_relatively_representable : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (h M : ℕ) (B : Type) [CommRing B] (ζ : B) (S : Scheme.{0}) [IsLocallyNoetherian S] (s₁ : S ⟶ Sp B) (t : S ⟶ Sp R) (c : SiegPre h M ζ s₁) (e : ℕ), e.Coprime p → SiegKerBy c e → ∃ (Z : Scheme.{0}) (π : Z ⟶ S) (u : Obj b N (π ≫ t)) (φu : u.A.left ⟶ c.A.left) (φ₂u : (G2 u.A).left ⟶ (G2 c.A).left), IsGrpPullback u.A c.A π φu ∧ IsSquare φu φ₂u ∧ LBIso u.P (c.P.pull φ₂u) ∧ IsFinite π ∧ ∀ (T : Scheme.{0}) (g : T ⟶ S) (t' : T ⟶ Sp R) (o : Obj b N t') (φ : o.A.left ⟶ c.A.left) (φ₂ : (G2 o.A).left ⟶ (G2 c.A).left), g ≫ t = t' → IsGrpPullback o.A c.A g φ → IsSquare φ φ₂ → LBIso o.P (c.P.pull φ₂) → ∃! z : T ⟶ Z, z ≫ π = g ∧ ∃ m : ObjMap o u z, m.φ ≫ φu = φ := by
  first | (exact @GlobalTheory.UPel.HT.relRep_htPull) | (exact GlobalTheory.UPel.HT.relRep_htPull) | (intros; apply GlobalTheory.UPel.HT.relRep_htPull  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelObjectRigidityIdentificationsEq
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelObjectRigidityIdentificationsEq
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory.SiegRigidCyc

open GlobalTheory.CechPic GlobalTheory.AmpleRigid GlobalTheory.SiegRigid

theorem eq_of_pullback : ∀ (h M : ℕ), 3 ≤ M → ∀ (S S' : Scheme.{0}) (s : S ⟶ Sp (cycAway M)) (s' : S' ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) s) (o : SiegPre h M (zetaAway M) s') (f : S' ⟶ S), Out.RelAmple c.A c.diag → ∀ (φ ψ : o.A.left ⟶ c.A.left) (φ₂ ψ₂ : (G2 o.A).left ⟶ (G2 c.A).left), IsGrpPullback o.A c.A f φ → IsSquare φ φ₂ → LBIso o.P (c.P.pull φ₂) → (∀ a, (o.lev a).left ≫ φ = f ≫ (c.lev a).left) → IsGrpPullback o.A c.A f ψ → IsSquare ψ ψ₂ → LBIso o.P (c.P.pull ψ₂) → (∀ a, (o.lev a).left ≫ ψ = f ≫ (c.lev a).left) → φ = ψ := by
  intro h M hM S S' s s' c o f hamp φ ψ φ₂ ψ₂ g q w l g' q' w' l'
  obtain ⟨σ, hσ, e⟩ := exists_aut g g'
  have hMu : IsUnit ((M : ℕ) : cycAway M) := isUnit_natCast (show M ≠ 0 by omega)
  have key : σ.hom = 𝟙 _ := by
    refine eq_id_of_forall_geometric_fibre laws_without_cohomology.1 o.A o.ab σ.hom (IsMonHom.one_hom σ.hom)
      fun t => ?_
    let K : Type := AlgebraicClosure (S'.residueField t)
    let j : Sp K ⟶ S' := Spec.map (CommRingCat.ofHom (algebraMap (S'.residueField t) K)) ≫ S'.fromSpecResidueField t
    have hp := isGrpPullback_pullback o.A j
    have := o.ab.smooth
    have := o.ab.proper
    have := o.ab.geomConnected
    have hab : IsAbelianScheme ((Over.pullback j).obj o.A) :=
      { comm := Functor.isCommMonObj_obj
        smooth := by change Smooth (pullback.snd o.A.hom j); infer_instance
        proper := by change IsProper (pullback.snd o.A.hom j); infer_instance
        geomConnected := by change GeometricallyConnected (pullback.snd o.A.hom j); infer_instance }
    have hNK : (M : K) ≠ 0 := by
      have hu := hMu.map (Spec.preimage ((j ≫ f) ≫ s)).hom
      rw [map_natCast] at hu
      exact hu.ne_zero
    have e' := eq_of_field (pull_isLB c.isLB _) hamp hab (hp.comp g) (hp.comp g')
      (by rw [pull_comp, pull_comp]; exact congrArg _ ((pull_cls_diag q w).trans (pull_cls_diag q' w').symm)) hM hNK
      fun Ω _ _ x y hy => by
        have hy₁ : pushHom hp (Over.mk x) y ^ M = 1 := by rw [← map_pow, hy, map_one]
        have e₁ := eq_on_torsion (GlobalTheory.LowChart.isUnit_zetaAway M hM) c g _ l l' Ω (x ≫ j) _ hy₁
        rw [← Category.assoc, ← Category.assoc]
        exact e₁
    refine ⟨_, _, j, _, _, (default : PrimeSpectrum K), ?_, hp.1, ?_⟩
    · exact (Scheme.Hom.comp_apply _ _ _).trans (Scheme.fromSpecResidueField_apply t _)
    · apply g'.1.hom_ext
      · rw [Category.assoc, e]
        exact e'
      · rw [Category.assoc, Over.w]
  rw [← e, key, Over.id_left, Category.id_comp]

end GlobalTheory.SiegRigidCyc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelObjectRigidityIdentificationsEqStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelObject_rigidity_identifications_eq : ∀ (h M : ℕ), 3 ≤ M → ∀ (S S' : Scheme.{0}) (s : S ⟶ Sp (cycAway M)) (s' : S' ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) s) (o : SiegPre h M (zetaAway M) s') (f : S' ⟶ S), Out.RelAmple c.A c.diag → ∀ (φ ψ : o.A.left ⟶ c.A.left) (φ₂ ψ₂ : (G2 o.A).left ⟶ (G2 c.A).left), IsGrpPullback o.A c.A f φ → IsSquare φ φ₂ → LBIso o.P (c.P.pull φ₂) → (∀ a, (o.lev a).left ≫ φ = f ≫ (c.lev a).left) → IsGrpPullback o.A c.A f ψ → IsSquare ψ ψ₂ → LBIso o.P (c.P.pull ψ₂) → (∀ a, (o.lev a).left ≫ ψ = f ≫ (c.lev a).left) → φ = ψ := by
  first | (exact @GlobalTheory.SiegRigidCyc.eq_of_pullback) | (exact GlobalTheory.SiegRigidCyc.eq_of_pullback) | (intros; apply GlobalTheory.SiegRigidCyc.eq_of_pullback  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorStructuresRepresentableSiegelBaseCha
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor

noncomputable section

namespace GlobalTheory.UPel.HT

open GlobalTheory.SiegelPull GlobalTheory.SiegelPullComp

theorem relRep_siegel : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N h M e : ℕ), 3 ≤ N → N.Coprime p → 3 ≤ M → Odd M → M.Coprime p → e.Coprime p → ∀ (Y : Scheme.{0}) (s : Y ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) s), SiegKerBy c e → IsLocallyNoetherian (pullback (s ≫ spMap (Int.castRingHom (cycAway M))) (spMap (Int.castRingHom R))) → ∃ (Z : Scheme.{0}) (π : Z ⟶ pullback (s ≫ spMap (Int.castRingHom (cycAway M))) (spMap (Int.castRingHom R))) (u : Obj b N (π ≫ pullback.snd _ _)) (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over Z) ⟶ u.A)), IsSympLev u.P h M (zetaAway M) (π ≫ pullback.fst _ _ ≫ s) lev ∧ IsFinite π ∧ (∀ (T : Scheme.{0}) (g : T ⟶ Z) (t : T ⟶ Sp R) (t₁ : T ⟶ Sp (cycAway M)) (o : Obj b N t) (l : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over T) ⟶ o.A)) (hl : IsSympLev o.P h M (zetaAway M) t₁ l), (∃ m : ObjMap o u g, ∀ a, (l a).left ≫ m.φ = g ≫ (lev a).left) → SiegPB (o.toSieg hl) c (g ≫ π ≫ pullback.fst _ _)) ∧ ∀ (T : Scheme.{0}) (t₀ : T ⟶ Y) (t : T ⟶ Sp R) (t₁ : T ⟶ Sp (cycAway M)) (o : Obj b N t) (l : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over T) ⟶ o.A)) (hl : IsSympLev o.P h M (zetaAway M) t₁ l), SiegPB (o.toSieg hl) c t₀ → ∃! g : T ⟶ Z, g ≫ π ≫ pullback.fst _ _ = t₀ ∧ g ≫ π ≫ pullback.snd _ _ = t ∧ ∃ m : ObjMap o u g, ∀ a, (l a).left ≫ m.φ = g ≫ (lev a).left := by
  intro p _ D R _ b N h M e hN hNp hM hMo hMp hep Y s c hker hY
  haveI := hY
  obtain ⟨⟨c', hc'⟩, -⟩ := GlobalTheory.siegPre_pullback h M (cycAway M) (zetaAway M) Y _ s
    (pullback.fst (s ≫ spMap (Int.castRingHom (cycAway M))) (spMap (Int.castRingHom R)) ≫ s) (pullback.fst _ _) c rfl
  have hker' : SiegKerBy c' e := siegKerBy_pull hc' hker
  obtain ⟨Z, π, u, φu, φ₂u, hpb, hsq, hiso, hfin, hrep⟩ :=
    GlobalTheory.T.harrisTaylor_structures_relatively_representable p D R b N hN hNp h M (cycAway M) (zetaAway M) _ _ (pullback.snd _ _) c' e hep hker'
  let lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over Z) ⟶ u.A) := fun a => GlobalTheory.SiegelPull.secPull hpb (c'.lev a)
  have hlev : ∀ a, (lev a).left ≫ φu = π ≫ (c'.lev a).left := fun a => GlobalTheory.SiegelPull.secPull_left hpb _
  have hsl : IsSympLev u.P h M (zetaAway M) (π ≫ pullback.fst _ _ ≫ s) lev :=
    isSympLev_pull hpb hsq c'.isLB u.isLB hiso hlev (GlobalTheory.UPel.HT.SiegPre.isSympLev c')
  have hlevw : ∀ a, (lev a).left ≫ u.A.hom = 𝟙 Z := fun a => Over.w (lev a)
  refine ⟨Z, π, u, lev, hsl, hfin, ?_, ?_⟩
  · rintro T g t t₁ o l hl ⟨m, hm⟩
    have h1 : SiegPB (o.toSieg hl) (u.toSieg hsl) g := ⟨m.φ, m.φ₂, m.cart, m.sq, m.pol, hm⟩
    have h2 : SiegPB (u.toSieg hsl) c' π := ⟨φu, φ₂u, hpb, hsq, hiso, hlev⟩
    exact pb_comp (pb_comp hc' h2) h1
  · intro T t₀ t t₁ o l hl hS
    have hw : t₀ ≫ s ≫ spMap (Int.castRingHom (cycAway M)) = t ≫ spMap (Int.castRingHom R) :=
      specZIsTerminal.hom_ext _ _
    let g₀ : T ⟶ pullback (s ≫ spMap (Int.castRingHom (cycAway M))) (spMap (Int.castRingHom R)) :=
      pullback.lift t₀ t hw
    have hg₁ : g₀ ≫ pullback.fst _ _ = t₀ := pullback.lift_fst _ _ _
    have hg₂ : g₀ ≫ pullback.snd _ _ = t := pullback.lift_snd _ _ _
    have hS' : SiegPB (o.toSieg hl) c' g₀ := pb_cancel hc' (by rw [hg₁]; exact hS)
    obtain ⟨φ, φ₂, hφ, hsqφ, hisoφ, hlφ⟩ := hS'
    obtain ⟨z, ⟨hz, m, hm⟩, huniq⟩ := hrep T g₀ t o φ φ₂ hg₂ hφ hsqφ hisoφ
    have hlw : ∀ a, (l a).left ≫ o.A.hom = 𝟙 T := fun a => Over.w (l a)
    refine ⟨z, ⟨by rw [← Category.assoc, hz, hg₁], by rw [← Category.assoc, hz, hg₂], m, fun a => ?_⟩, ?_⟩
    · apply hpb.1.hom_ext
      · rw [Category.assoc, hm, Category.assoc, hlev, ← Category.assoc, hz]
        exact hlφ a
      · rw [Category.assoc, m.cart.1.w, ← Category.assoc, hlw, Category.assoc, hlevw]
        simp
    · rintro z' ⟨h1', h2', m', hm'⟩
      have hzπ : z' ≫ π = g₀ := pullback.hom_ext (by rw [Category.assoc, h1', hg₁])
        (by rw [Category.assoc, h2', hg₂])
      refine huniq z' ⟨hzπ, m', ?_⟩
      refine GlobalTheory.T.siegelObject_rigidity_identifications_eq h M hM _ T _ t₁ c' (o.toSieg hl) g₀ hker'.1 (m'.φ ≫ φu) φ (m'.φ₂ ≫ φ₂u) φ₂
        (by rw [← hzπ]; exact m'.cart.comp hpb) ⟨?_, ?_⟩ ?_ (fun a => ?_) hφ hsqφ hisoφ hlφ
      · exact (Category.assoc _ _ _).trans ((congrArg (m'.φ₂ ≫ ·) hsq.1).trans ((Category.assoc _ _ _).symm.trans
          ((congrArg (· ≫ φu) m'.sq.1).trans (Category.assoc _ _ _))))
      · exact (Category.assoc _ _ _).trans ((congrArg (m'.φ₂ ≫ ·) hsq.2).trans ((Category.assoc _ _ _).symm.trans
          ((congrArg (· ≫ φu) m'.sq.2).trans (Category.assoc _ _ _))))
      · exact (m'.pol.trans o.isLB (pull_isLB u.isLB _) (pull_isLB (pull_isLB c'.isLB _) _)
          (iso_pull m'.φ₂ hiso)).trans o.isLB (pull_isLB (pull_isLB c'.isLB _) _) (pull_isLB c'.isLB _)
          (iso_pull_pull c'.isLB φ₂u m'.φ₂)
      · show (l a).left ≫ m'.φ ≫ φu = g₀ ≫ (c'.lev a).left
        rw [← Category.assoc, hm' a, Category.assoc, hlev, ← Category.assoc, hzπ]

end GlobalTheory.UPel.HT
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorStructuresRepresentableSiegelBaseChaStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylor_structures_representable_siegel_baseChange : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N h M e : ℕ), 3 ≤ N → N.Coprime p → 3 ≤ M → Odd M → M.Coprime p → e.Coprime p → ∀ (Y : Scheme.{0}) (s : Y ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) s), SiegKerBy c e → IsLocallyNoetherian (pullback (s ≫ spMap (Int.castRingHom (cycAway M))) (spMap (Int.castRingHom R))) → ∃ (Z : Scheme.{0}) (π : Z ⟶ pullback (s ≫ spMap (Int.castRingHom (cycAway M))) (spMap (Int.castRingHom R))) (u : Obj b N (π ≫ pullback.snd _ _)) (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over Z) ⟶ u.A)), IsSympLev u.P h M (zetaAway M) (π ≫ pullback.fst _ _ ≫ s) lev ∧ IsFinite π ∧ (∀ (T : Scheme.{0}) (g : T ⟶ Z) (t : T ⟶ Sp R) (t₁ : T ⟶ Sp (cycAway M)) (o : Obj b N t) (l : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over T) ⟶ o.A)) (hl : IsSympLev o.P h M (zetaAway M) t₁ l), (∃ m : ObjMap o u g, ∀ a, (l a).left ≫ m.φ = g ≫ (lev a).left) → SiegPB (o.toSieg hl) c (g ≫ π ≫ pullback.fst _ _)) ∧ ∀ (T : Scheme.{0}) (t₀ : T ⟶ Y) (t : T ⟶ Sp R) (t₁ : T ⟶ Sp (cycAway M)) (o : Obj b N t) (l : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over T) ⟶ o.A)) (hl : IsSympLev o.P h M (zetaAway M) t₁ l), SiegPB (o.toSieg hl) c t₀ → ∃! g : T ⟶ Z, g ≫ π ≫ pullback.fst _ _ = t₀ ∧ g ≫ π ≫ pullback.snd _ _ = t ∧ ∃ m : ObjMap o u g, ∀ a, (l a).left ≫ m.φ = g ≫ (lev a).left := by
  first | (exact @GlobalTheory.UPel.HT.relRep_siegel) | (exact GlobalTheory.UPel.HT.relRep_siegel) | (intros; apply GlobalTheory.UPel.HT.relRep_siegel  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsQuasiProjectiveOfFiniteOverCyclotomicAwayPullb
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsQuasiProjectiveOfFiniteOverCyclotomicAwayPullb
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor

namespace GlobalTheory.CycAwayQProj

theorem finiteType_closure {K : Type} [CommRing K] {s : Set K} (hs : s.Finite) :
    (Int.castRingHom (Subring.closure s)).FiniteType := by
  have h : Algebra.FiniteType ℤ (Algebra.adjoin ℤ s) :=
    (Subalgebra.fg_iff_finiteType _).1 (Subalgebra.fg_def.2 ⟨s, hs, rfl⟩)
  have e : Algebra.adjoin ℤ s ≃+* Subring.closure s :=
    RingEquiv.subringCongr (s := (Algebra.adjoin ℤ s).toSubring) (by rw [Algebra.adjoin_int]; rfl)
  have h' : Algebra.FiniteType ℤ (Subring.closure s) := h.equiv (AlgEquiv.ofRingEquiv (f := e) fun x => by simp)
  have := RingHom.finiteType_algebraMap.2 h'
  rwa [RingHom.eq_intCast' (algebraMap ℤ (Subring.closure s))] at this

theorem finiteType_cycAway (M : ℕ) : (Int.castRingHom (cycAway M)).FiniteType :=
  finiteType_closure (Set.toFinite _)

theorem isQProjOver_comp_spMap {A B : Type} [CommRing A] [CommRing B] {f : A →+* B} (hf : f.FiniteType)
    {Y : Scheme.{0}} {s : Y ⟶ Sp B} (h : IsQProjOver s) : IsQProjOver (s ≫ spMap f) := by
  obtain ⟨_, hL⟩ := (isQProjOver_iff_locallyOfFiniteType_and_exists_isAmpleLB s).1 h
  have : LocallyOfFiniteType (spMap f) := (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).2 hf
  exact (isQProjOver_iff_locallyOfFiniteType_and_exists_isAmpleLB _).2 ⟨inferInstance, hL⟩

theorem isQProjOver_of_isFinite_pullback : ∀ (M : ℕ) (R : Type) [CommRing R] [IsNoetherianRing R], IsUnit ((M : ℕ) : R) → ∀ (Y : Scheme.{0}) (s : Y ⟶ Sp (cycAway M)), IsQProjOver s → ∀ (Z : Scheme.{0}) (π : Z ⟶ pullback (s ≫ spMap (Int.castRingHom (cycAway M))) (spMap (Int.castRingHom R))), IsFinite π → IsQProjOver (π ≫ pullback.snd _ _) :=
  fun M _ _ _ _ _ _ hs _ π _ =>
    isQProjOver_comp_of_isFinite π
      (isQProjOver_of_isPullback (IsPullback.of_hasPullback _ _) (isQProjOver_comp_spMap (finiteType_cycAway M) hs))

end GlobalTheory.CycAwayQProj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsQuasiProjectiveOfFiniteOverCyclotomicAwayPullbStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isQuasiProjective_of_finite_over_cyclotomicAway_pullback : ∀ (M : ℕ) (R : Type) [CommRing R] [IsNoetherianRing R], IsUnit ((M : ℕ) : R) → ∀ (Y : Scheme.{0}) (s : Y ⟶ Sp (cycAway M)), IsQProjOver s → ∀ (Z : Scheme.{0}) (π : Z ⟶ pullback (s ≫ spMap (Int.castRingHom (cycAway M))) (spMap (Int.castRingHom R))), IsFinite π → IsQProjOver (π ≫ pullback.snd _ _) := by
  first | (exact @GlobalTheory.CycAwayQProj.isQProjOver_of_isFinite_pullback) | (exact GlobalTheory.CycAwayQProj.isQProjOver_of_isFinite_pullback) | (intros; apply GlobalTheory.CycAwayQProj.isQProjOver_of_isFinite_pullback  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorAuxiliarySymplecticLevelRepresentabl
noncomputable section

namespace GlobalTheory.UPel.HT

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.SiegelTor

theorem harrisTaylorModuli_symplecticLevel_representable : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsNoetherianRing R] (b : Base D R) (N M e : ℕ), 3 ≤ N → N.Coprime p → 3 ≤ M → Odd M → M.Coprime p → e.Coprime p → M.Coprime e → (∀ f : D.La →ₗ[ℤ] ℤ, ∃ x, D.EF x = e • f) → SDRep (Module.finrank ℤ D.La / 2) M e → HasLevelStructureOfLevel b N (Module.finrank ℤ D.La / 2) M := by
  intro p _ D R _ _ b N M e hN hNp hM hMo hMp hep _ hdual hSD
  obtain ⟨X, s, u, hku, -, hqs, huniv⟩ := hSD
  have hMR : IsUnit ((M : ℕ) : R) := b.unit M hMp
  have hqP : IsQProjOver (𝟙 _ ≫ pullback.snd (s ≫ spMap (Int.castRingHom (cycAway M)))
      (spMap (Int.castRingHom R))) :=
    GlobalTheory.T.isQuasiProjective_of_finite_over_cyclotomicAway_pullback M R hMR X s hqs _ (𝟙 _) inferInstance
  rw [Category.id_comp] at hqP
  have hLN := GlobalTheory.T.isLocallyNoetherian_of_isQProjOver_noetherian R _ _ hqP
  obtain ⟨Z, π, v, lev, hlev, hfin, hfwd, hback⟩ :=
    GlobalTheory.T.harrisTaylor_structures_representable_siegel_baseChange p D R b N (Module.finrank ℤ D.La / 2) M e hN hNp hM hMo hMp hep X s u hku hLN
  refine ⟨Z, π ≫ pullback.snd _ _, π ≫ pullback.fst _ _ ≫ s, v, lev, hlev,
    GlobalTheory.T.isQuasiProjective_of_finite_over_cyclotomicAway_pullback M R hMR X s hqs Z π hfin, ?_⟩
  intro S t t₁ o l hl
  have heS : IsUnit ((e : ℕ) : Γ(S, ⊤)) := by
    have h := (b.unit e hep).map ((t.appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
    simpa using h
  obtain ⟨f₀, ⟨hf₀s, hf₀pb⟩, hf₀u⟩ :=
    huniv S t₁ (o.toSieg hl) heS (GlobalTheory.T.harrisTaylor_siegelObject_polarisationKernel_killed p D R b N S t o _ M t₁ l hl e hep hdual)
  obtain ⟨g, ⟨hg₁, hg₂, hgm⟩, hgu⟩ := hback S f₀ t t₁ o l hl hf₀pb
  refine ⟨g, ⟨hg₂, ?_, hgm⟩, ?_⟩
  · rw [← hf₀s, ← hg₁]
    simp only [Category.assoc]
  · rintro g' ⟨hg's, hg's₁, hg'm⟩
    have hfst : g' ≫ π ≫ pullback.fst _ _ = f₀ :=
      hf₀u _ ⟨by simpa only [Category.assoc] using hg's₁, hfwd S g' t t₁ o l hl hg'm⟩
    exact hgu g' ⟨hfst, hg's, hg'm⟩

end GlobalTheory.UPel.HT
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorAuxiliarySymplecticLevelRepresentablStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylor_auxiliary_symplectic_level_representable : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsNoetherianRing R] (b : Base D R) (N M e : ℕ), 3 ≤ N → N.Coprime p → 3 ≤ M → Odd M → M.Coprime p → e.Coprime p → M.Coprime e → (∀ f : D.La →ₗ[ℤ] ℤ, ∃ x, D.EF x = e • f) → SDRep (Module.finrank ℤ D.La / 2) M e → HasLevelStructureOfLevel b N (Module.finrank ℤ D.La / 2) M := by
  first | (exact @GlobalTheory.UPel.HT.harrisTaylorModuli_symplecticLevel_representable) | (exact GlobalTheory.UPel.HT.harrisTaylorModuli_symplecticLevel_representable) | (intros; apply GlobalTheory.UPel.HT.harrisTaylorModuli_symplecticLevel_representable  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuasiProjectiveHarrisTaylorFamily
noncomputable section

namespace GlobalTheory.UPel.HT

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.SiegelTor

theorem exists_repFam_qproj : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R]
    [IsNoetherianRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∃ F : RepFam b N, IsQProjOver F.s := by
  intro p _ D R _ _ b N hN hNp
  obtain ⟨e, hep, he⟩ := D.perfP
  have hp := (Fact.out : p.Prime)
  have he0 : 0 < e := by
    rcases Nat.eq_zero_or_pos e with h | h
    · subst h
      rw [Nat.coprime_zero_left] at hep
      exact absurd hep hp.one_lt.ne'
    · exact h
  obtain ⟨M, hMge, hMp⟩ := Nat.exists_infinite_primes (p + e + 3)
  have hM3 : 3 ≤ M := by omega
  have hModd : Odd M := hMp.odd_of_ne_two (by omega)
  have hMcp : M.Coprime p := (Nat.coprime_primes hMp hp).2 (by omega)
  have hMe : M.Coprime e := (Nat.Prime.coprime_iff_not_dvd hMp).2 fun h => by
    have := Nat.le_of_dvd he0 h
    omega
  have hg : 1 ≤ Module.finrank ℤ D.La / 2 := by
    have := D.two_le_finrank_La
    omega
  exact GlobalTheory.T.exists_representingFamily_of_auxiliaryRepresentation p D R b N M e hN hNp hM3 hModd hMcp hep hMe he
    (GlobalTheory.T.harrisTaylor_auxiliary_symplectic_level_representable p D R b N M e hN hNp hM3 hModd hMcp hep hMe he
      (GlobalTheory.T.siegelKernelBoundedRepresentable_of_coprime _ M e hg hM3 hModd he0 hMe))

end GlobalTheory.UPel.HT
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuasiProjectiveHarrisTaylorFamilyStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_quasiProjective_harrisTaylor_family : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] [IsNoetherianRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∃ F : RepFam b N, IsQProjOver F.s := by
  first | (exact @GlobalTheory.UPel.HT.exists_repFam_qproj) | (exact GlobalTheory.UPel.HT.exists_repFam_qproj) | (intros; apply GlobalTheory.UPel.HT.exists_repFam_qproj  <;> assumption)
end
