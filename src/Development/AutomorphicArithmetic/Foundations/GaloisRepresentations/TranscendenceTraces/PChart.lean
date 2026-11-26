module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PChart
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.chart_of :
    Chart := by
  intro Z S p _ A _ u
  haveI : IsAffine (pullback p u) := isAffine_of_isAffineHom (pullback.snd p u)
  let V := pullback p u
  let e : Spec Γ(V, ⊤) ≅ V := V.isoSpec.symm
  let φ : CommRingCat.of A ⟶ Γ(V, ⊤) := Spec.preimage (e.hom ≫ pullback.snd p u)
  have hφ : Spec.map φ = e.hom ≫ pullback.snd p u := Spec.map_preimage _
  letI alg : Algebra A Γ(V, ⊤) := φ.hom.toAlgebra
  have hφ' : Spec.map (CommRingCat.ofHom (algebraMap A Γ(V, ⊤))) = e.hom ≫ pullback.snd p u := hφ
  refine ⟨Γ(V, ⊤), inferInstance, alg, e.hom ≫ pullback.fst p u, ?_, ?_⟩
  · have hfin : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap A Γ(V, ⊤)))) := by
      rw [hφ']; infer_instance
    have h2 := (IsFinite.SpecMap_iff _).1 hfin
    exact RingHom.finite_algebraMap.1 h2
  · rw [hφ']
    exact IsPullback.of_iso (IsPullback.of_hasPullback p u) e.symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by simp) (by simp) (by simp) (by simp)
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PFibFin
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

private theorem fib_spec_finite (Ω B : Type) [Field Ω] [CommRing B] [Algebra Ω B] [Module.Finite Ω B] :
    (fib (Ω := Ω) (Spec.map (CommRingCat.ofHom (algebraMap Ω B))) (𝟙 (gp Ω))).Finite := by
  apply (Set.finite_range (fun g : B →ₐ[Ω] Ω => Spec.map (CommRingCat.ofHom (g : B →+* Ω)))).subset
  intro z hz
  have hz' : z ≫ Spec.map (CommRingCat.ofHom (algebraMap Ω B)) = 𝟙 _ := hz
  obtain ⟨φ, rfl⟩ : ∃ φ, Spec.map φ = z := ⟨Spec.preimage z, Spec.map_preimage z⟩
  rw [← Spec.map_comp, ← Spec.map_id] at hz'
  have h2 := Spec.map_injective hz'
  refine ⟨{ φ.hom with commutes' := fun c => ?_ }, ?_⟩
  · have := congrArg (fun g => g.hom c) h2
    simpa using this
  · rfl

theorem UpperTheory.Gal.TranscendenceTraces.fibFin_of :
    Chart → FibFin := by
  intro hC
  unfold Chart at hC
  unfold FibFin
  intro V U r _ Ω _ x
  obtain ⟨B, iB, iAB, v, hfin, hpb⟩ := hC r Ω x
  haveI := hfin
  have h := (fib_bijOn hpb (𝟙 (gp Ω))).image_eq
  rw [Category.id_comp] at h
  rw [← h]
  exact (fib_spec_finite Ω B).image _
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PPtLift
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

private theorem pt_map_ideal {Ω : Type} [Field Ω] {B : CommRingCat.{0}} (s : B ⟶ CommRingCat.of Ω) :
    (show PrimeSpectrum B from pt (Spec.map s)).asIdeal = RingHom.ker s.hom := by
  have h : (pt (Spec.map s) : Spec B) = PrimeSpectrum.comap s.hom (IsLocalRing.closedPoint Ω) := rfl
  change (pt (Spec.map s) : Spec B).asIdeal = _
  rw [h, RingHom.ker_eq_comap_bot]
  change Ideal.comap s.hom (IsLocalRing.maximalIdeal Ω) = _
  rw [IsLocalRing.maximalIdeal_eq_bot]

private theorem exists_retract {Ω : Type} [Field Ω] [IsAlgClosed Ω] {B : CommRingCat.{0}} (φ : CommRingCat.of Ω ⟶ B)
    (hφ : φ.hom.IsIntegral) (q : Ideal B) [q.IsPrime] :
    ∃ s : B ⟶ CommRingCat.of Ω, φ ≫ s = 𝟙 _ ∧ RingHom.ker s.hom = q := by
  letI : Algebra Ω B := φ.hom.toAlgebra
  haveI : Algebra.IsIntegral Ω B := ⟨hφ⟩
  have hb : Function.Bijective (algebraMap Ω (B ⧸ q)) := IsAlgClosed.algebraMap_bijective_of_isIntegral
  let e : Ω ≃+* B ⧸ q := RingEquiv.ofBijective (algebraMap Ω (B ⧸ q)) hb
  refine ⟨CommRingCat.ofHom (e.symm.toRingHom.comp (Ideal.Quotient.mk q)), ?_, ?_⟩
  · ext a
    change e.symm (Ideal.Quotient.mk q (φ.hom a)) = a
    exact e.symm_apply_apply a
  · ext b
    change e.symm (Ideal.Quotient.mk q b) = 0 ↔ b ∈ q
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    simp

theorem UpperTheory.Gal.TranscendenceTraces.ptLift_of :
    PtLift := by
  intro V U r _ Ω _ _ x v hv
  obtain ⟨t, ht1, ht2⟩ := Scheme.Pullback.exists_preimage_pullback (f := r) (g := x) v
    (IsLocalRing.closedPoint Ω) hv
  let P := pullback r x
  haveI : IsIntegralHom (pullback.snd r x) := inferInstance
  haveI : IsAffine P := isAffine_of_isAffineHom (pullback.snd r x)
  let φ : CommRingCat.of Ω ⟶ Γ(P, ⊤) := Spec.preimage (P.isoSpec.inv ≫ pullback.snd r x)
  have hφ' : Spec.map φ = P.isoSpec.inv ≫ pullback.snd r x := Spec.map_preimage _
  have hφ : φ.hom.IsIntegral := by
    rw [← IsIntegralHom.SpecMap_iff, hφ']
    infer_instance
  let y : Spec Γ(P, ⊤) := P.isoSpec.hom t
  haveI : y.asIdeal.IsPrime := PrimeSpectrum.isPrime y
  obtain ⟨s, hs, hk⟩ := exists_retract φ hφ y.asIdeal
  refine ⟨Spec.map s ≫ P.isoSpec.inv ≫ pullback.fst r x, ?_, ?_⟩
  · have h1 : Spec.map s ≫ Spec.map φ = 𝟙 _ := by
      rw [← Spec.map_comp, hs, Spec.map_id]
    rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc P.isoSpec.inv,
      ← hφ', ← Category.assoc, h1, Category.id_comp]
  · have hy : (pt (Spec.map s) : Spec Γ(P, ⊤)) = y :=
      PrimeSpectrum.ext ((pt_map_ideal s).trans hk)
    rw [← Category.assoc, pt_comp, pt_comp, hy]
    change (pullback.fst r x) (P.isoSpec.inv (P.isoSpec.hom t)) = v
    have h2 : P.isoSpec.inv (P.isoSpec.hom t) = t := by
      rw [← Scheme.Hom.comp_apply, Iso.hom_inv_id]
      rfl
    rw [h2, ht1]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PhiExact
section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PhiSecRes
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped DirectSum Classical

namespace UpperTheory.Gal.TranscendenceTraces

variable {R : Type} [CommRing R] {Z S : Scheme.{0}} (p : Z ⟶ S)

def pbm {U' U : Scheme.{0}} (g : U' ⟶ U) (u : U ⟶ S) (u' : U' ⟶ S) (h : g ≫ u = u') : pullback p u' ⟶ pullback p u :=
  pullback.lift (pullback.fst p u') (pullback.snd p u' ≫ g) (by rw [Category.assoc, h, pullback.condition])

theorem pbm_fst {U' U : Scheme.{0}} (g : U' ⟶ U) (u : U ⟶ S) (u' : U' ⟶ S) (h : g ≫ u = u') :
    pbm p g u u' h ≫ pullback.fst p u = pullback.fst p u' := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem pbm_snd {U' U : Scheme.{0}} (g : U' ⟶ U) (u : U ⟶ S) (u' : U' ⟶ S) (h : g ≫ u = u') :
    pbm p g u u' h ≫ pullback.snd p u = pullback.snd p u' ≫ g := pullback.lift_snd _ _ _

abbrev DS (G : Shv R) (U : Scheme.{0}) : Type 1 := ⨁ u : (U ⟶ S), Sec G (pullback p u)

def inc (G : Shv R) {U : Scheme.{0}} (u : U ⟶ S) : Sec G (pullback p u) →ₗ[ULift.{1} R] DS p G U :=
  DirectSum.lof (ULift.{1} R) (U ⟶ S) (fun u => Sec G (pullback p u)) u

theorem DS.hom_ext {G : Shv R} {U : Scheme.{0}} {M : Type 1} [AddCommGroup M] [Module (ULift.{1} R) M]
    {f f' : DS p G U →ₗ[ULift.{1} R] M} (h : ∀ u a, f (inc p G u a) = f' (inc p G u a)) : f = f' :=
  DirectSum.linearMap_ext _ fun u => LinearMap.ext fun a => h u a

theorem inc_congr (G : Shv R) {U : Scheme.{0}} {u u' : U ⟶ S} (h : u' = u) (k : pullback p u' ⟶ pullback p u)
    (h1 : k ≫ pullback.fst p u = pullback.fst p u') (h2 : k ≫ pullback.snd p u = pullback.snd p u')
    (a : Sec G (pullback p u)) : inc p G u' (Sec.res k a) = inc p G u a := by
  subst h
  have : k = 𝟙 _ := pullback.hom_ext (by simpa using h1) (by simpa using h2)
  rw [this, res_id]

def DS.res (G : Shv R) {U' U : Scheme.{0}} (g : U' ⟶ U) : DS p G U →ₗ[ULift.{1} R] DS p G U' :=
  DirectSum.toModule _ _ _ fun u => inc p G (g ≫ u) ∘ₗ (G.obj.map (pbm p g u _ rfl).op).hom

theorem DS.res_inc (G : Shv R) {U' U : Scheme.{0}} (g : U' ⟶ U) (u : U ⟶ S) (u' : U' ⟶ S) (h : g ≫ u = u')
    (a : Sec G (pullback p u)) : DS.res p G g (inc p G u a) = inc p G u' (Sec.res (pbm p g u u' h) a) := by
  subst h
  exact DirectSum.toModule_lof _ _ _

def DS.map {G G' : Shv R} (f : G ⟶ G') (U : Scheme.{0}) : DS p G U →ₗ[ULift.{1} R] DS p G' U :=
  DirectSum.toModule _ _ _ fun u => inc p G' u ∘ₗ (f.hom.app (op (pullback p u))).hom

theorem DS.map_inc {G G' : Shv R} (f : G ⟶ G') {U : Scheme.{0}} (u : U ⟶ S) (a : Sec G (pullback p u)) :
    DS.map p f U (inc p G u a) = inc p G' u (Sec.map f a) := DirectSum.toModule_lof _ _ _

def phiP (G : Shv R) : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R) where
  obj U := ModuleCat.of _ (DS p G U.unop)
  map g := ModuleCat.ofHom (DS.res p G g.unop)
  map_id U := ModuleCat.hom_ext (DS.hom_ext p fun u a => by
    change DS.res p G (𝟙 _) (inc p G u a) = inc p G u a
    rw [DS.res_inc p G _ u _ rfl]
    exact inc_congr p G (Category.id_comp u) _ (pbm_fst p _ _ _ _) (by simp) a)
  map_comp f g := ModuleCat.hom_ext (DS.hom_ext p fun u a => by
    change DS.res p G (g.unop ≫ f.unop) (inc p G u a) = DS.res p G g.unop (DS.res p G f.unop (inc p G u a))
    rw [DS.res_inc p G _ u _ (Category.assoc _ _ _), DS.res_inc p G f.unop u _ rfl, DS.res_inc p G g.unop _ _ rfl, res_res]
    congr 2
    exact pullback.hom_ext (by simp only [Category.assoc, pbm_fst]) (by simp))

def phiPF (R : Type) [CommRing R] : Shv R ⥤ (Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)) where
  obj G := phiP p G
  map {G G'} f :=
    { app := fun U => ModuleCat.ofHom (DS.map p f U.unop)
      naturality := fun U V g => ModuleCat.hom_ext (DS.hom_ext p fun u a => by
        change DS.map p f _ (DS.res p G g.unop (inc p G u a)) = DS.res p G' g.unop (DS.map p f _ (inc p G u a))
        rw [DS.res_inc p G _ u _ rfl, DS.map_inc, DS.map_inc, DS.res_inc p G' _ u _ rfl, map_res]) }
  map_id G := NatTrans.ext (funext fun U => ModuleCat.hom_ext (DS.hom_ext p fun u a => DS.map_inc p (𝟙 G) u a))
  map_comp {G G' G''} f g := NatTrans.ext (funext fun U => ModuleCat.hom_ext (DS.hom_ext p fun u a => by
    change DS.map p (f ≫ g) _ (inc p G u a) = DS.map p g _ (DS.map p f _ (inc p G u a))
    rw [DS.map_inc, DS.map_inc, DS.map_inc]
    rfl))

instance (R : Type) [CommRing R] : (phiPF p R).Additive where
  map_add {G G' f g} := NatTrans.ext (funext fun U => ModuleCat.hom_ext (DS.hom_ext p fun u a => by
    change DS.map p (f + g) _ (inc p G u a) = DS.map p f _ (inc p G u a) + DS.map p g _ (inc p G u a)
    rw [DS.map_inc, DS.map_inc, DS.map_inc, ← map_add (f := _)]
    rfl))

def phi (R : Type) [CommRing R] : Shv R ⥤ Shv R := phiPF p R ⋙ presheafToSheaf _ _

instance (R : Type) [CommRing R] : (phi p R).Additive := by
  unfold phi
  infer_instance

def phiSec (G : Shv R) (U : Scheme.{0}) : DS p G U →ₗ[ULift.{1} R] Sec ((phi p R).obj G) U :=
  ((toSheafify Scheme.etaleTopology (phiP p G)).app (op U)).hom

theorem phiSec_res (G : Shv R) {V U : Scheme.{0}} (g : V ⟶ U) (x : DS p G U) :
    Sec.res g (phiSec p G U x) = phiSec p G V (DS.res p G g x) :=
  (congrArg (fun h => h.hom x) ((toSheafify Scheme.etaleTopology (phiP p G)).naturality g.op)).symm

theorem phiSec_map {G G' : Shv R} (f : G ⟶ G') (U : Scheme.{0}) (x : DS p G U) :
    Sec.map ((phi p R).map f) (phiSec p G U x) = phiSec p G' U (DS.map p f U x) :=
  (congrArg (fun h => (h.app (op U)).hom x) (toSheafify_naturality Scheme.etaleTopology ((phiPF p R).map f))).symm

def Sq.cmp {p : Z ⟶ S} (A : Sq p) : pullback p A.u ⟶ A.V :=
  A.pb.lift (pullback.fst p A.u) (pullback.snd p A.u) pullback.condition

theorem Sq.cmp_v {p : Z ⟶ S} (A : Sq p) : A.cmp ≫ A.v = pullback.fst p A.u := A.pb.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem Sq.cmp_r {p : Z ⟶ S} (A : Sq p) : A.cmp ≫ A.r = pullback.snd p A.u := A.pb.lift_snd _ _ _

def phiE (G : Shv R) : Fam0 p G ((phi p R).obj G) where
  app A := (phiSec p G A.U ∘ₗ inc p G A.u ∘ₗ (G.obj.map A.cmp.op).hom).toAddMonoidHom
  nat {A B} t a := by
    change Sec.res t.g (phiSec p G B.U (inc p G B.u (Sec.res B.cmp a))) =
      phiSec p G A.U (inc p G A.u (Sec.res A.cmp (Sec.res t.k a)))
    rw [phiSec_res, DS.res_inc p G t.g B.u A.u t.hu, res_res, res_res]
    congr 3
    exact B.pb.hom_ext (by simp only [Category.assoc, Sq.cmp_v, pbm_fst, t.hv])
      (by simp [t.hr])

theorem phiE_app (G : Shv R) (A : Sq p) (a : Sec G A.V) :
    (phiE p G).app A a = phiSec p G A.U (inc p G A.u (Sec.res A.cmp a)) := rfl

theorem phiE_of (G : Shv R) {U : Scheme.{0}} (u : U ⟶ S) (a : Sec G (pullback p u)) :
    (phiE p G).app (Sq.of p u) a = phiSec p G U (inc p G u a) := by
  refine (phiE_app p G (Sq.of p u) a).trans ?_
  exact congrArg _ (inc_congr p G rfl _ (Sq.cmp_v (Sq.of p u)) (Sq.cmp_r (Sq.of p u)) a)

end UpperTheory.Gal.TranscendenceTraces

end
end

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC

namespace UpperTheory.Gal.TranscendenceTraces

def PhiUniv : Prop := ∀ (Q : ℕ) {Z S : Scheme.{0}} (p : Z ⟶ S) (G J : Shv (ZMod Q)) (t : Fam0 p G J),
  ∃! m : (phi p (ZMod Q)).obj G ⟶ J, ∀ A a, Sec.map m ((phiE p G).app A a) = t.app A a

def DSOne : Prop := ∀ (R : Type) [CommRing R] {Z S : Scheme.{0}} (p : Z ⟶ S) [IsFinite p] (T : ShortComplex (Shv R)), T.Exact →
  ∀ (U : Scheme.{0}) (u : U ⟶ S) (b : Sec T.X₂ (pullback p u)), Sec.map T.g b = 0 →
  Loc U fun V g => ∃ a : DS p T.X₁ V, DS.map p T.f V a = DS.res p T.X₂ g (inc p T.X₂ u b)

def DSLoc : Prop := ∀ (R : Type) [CommRing R] {Z S : Scheme.{0}} (p : Z ⟶ S) [IsFinite p] (T : ShortComplex (Shv R)), T.Exact →
  ∀ (U : Scheme.{0}) (x : DS p T.X₂ U), DS.map p T.g U x = 0 →
  Loc U fun V g => ∃ a : DS p T.X₁ V, DS.map p T.f V a = DS.res p T.X₂ g x

def PhiExact : Prop := ∀ (R : Type) [CommRing R] {Z S : Scheme.{0}} (p : Z ⟶ S) [IsFinite p] (T : ShortComplex (Shv R)),
  T.Exact → (T.map (phi p R)).Exact

def PhiQis : Prop := ∀ (R : Type) [CommRing R] (Φ : Shv R ⥤ Shv R) [Φ.Additive],
  (∀ T : ShortComplex (Shv R), T.Exact → (T.map Φ).Exact) → ∀ F : Shv R,
  ∃ ε : sgl (Φ.obj F) ⟶ (Φ.mapHomologicalComplex (ComplexShape.up ℤ)).obj (res R F), QuasiIso ε ∧
    sglι (Φ.obj F) ≫ ε.f 0 = Φ.map (resι R F)

def ExtRes : Prop := ∀ (R : Type) [CommRing R] (F G : Shv R) (T : Cx R) (ε : sgl F ⟶ T) [QuasiIso ε],
  (∀ a : F ⟶ G, ∃ m : T ⟶ res R G, sglι F ≫ ε.f 0 ≫ m.f 0 = a ≫ resι R G) ∧
  ∀ m m' : T ⟶ res R G, sglι F ≫ ε.f 0 ≫ m.f 0 = sglι F ≫ ε.f 0 ≫ m'.f 0 → ∀ (U : Scheme.{0}) (i n k : ℤ), i + 1 = n → n + 1 = k →
    ∀ y : Sec (T.X n) U, Sec.map (T.d n k) y = 0 → ∃ c, Sec.map ((res R G).d i n) c = Sec.map (m.f n) y - Sec.map (m'.f n) y

def FamHom : Prop := ∀ (Q : ℕ) {Z S : Scheme.{0}} (p : Z ⟶ S) (Φ : Shv (ZMod Q) ⥤ Shv (ZMod Q)) [Φ.Additive]
  (e : ∀ G, Fam0 p G (Φ.obj G)), Rep0 p Q Φ e → ∀ I J : Cx (ZMod Q),
  (∀ m : (Φ.mapHomologicalComplex (ComplexShape.up ℤ)).obj I ⟶ J, ∃ τ : Fam p I J,
    ∀ n A a, (τ.deg n).app A a = Sec.map (F := Φ.obj (I.X n)) (m.f n) ((e (I.X n)).app A a)) ∧
  ∀ τ : Fam p I J, ∃ m : (Φ.mapHomologicalComplex (ComplexShape.up ℤ)).obj I ⟶ J,
    ∀ n A a, (τ.deg n).app A a = Sec.map (F := Φ.obj (I.X n)) (m.f n) ((e (I.X n)).app A a)

end UpperTheory.Gal.TranscendenceTraces

end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PGenBasic
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

private theorem genPt_exists_spec {S : Scheme.{0}} (s : S) : ∃ t : S, t ⤳ s ∧ GenPt t := by
  have hC : IsIrreducible (irreducibleComponent s) := isIrreducible_irreducibleComponent
  have hcl : IsClosed (irreducibleComponent s) := isClosed_irreducibleComponent
  have ht : IsGenericPoint hC.genericPoint (irreducibleComponent s) :=
    hC.isGenericPoint_genericPoint hcl
  refine ⟨hC.genericPoint, ht.specializes mem_irreducibleComponent, ?_⟩
  intro t' h'
  have hsub : irreducibleComponent s ⊆ closure {t'} := by
    rw [← ht.def]
    exact h'.closure_subset
  have heq : closure ({t'} : Set S) = irreducibleComponent s :=
    eq_irreducibleComponent isIrreducible_singleton.closure.isPreirreducible hsub
  have ht' : IsGenericPoint t' (irreducibleComponent s) := heq
  exact ht'.eq ht

private theorem genPt_open {U S : Scheme.{0}} (j : U ⟶ S) [IsOpenImmersion j] (s : U) :
    GenPt (j s) ↔ GenPt s := by
  have he := j.isOpenEmbedding
  constructor
  · intro h t hts
    exact he.injective (h _ (hts.map he.continuous))
  · intro h t hts
    have hmem : t ∈ Set.range j := hts.mem_open he.isOpen_range ⟨s, rfl⟩
    obtain ⟨t', rfl⟩ := hmem
    have : t' ⤳ s := he.isInducing.specializes_iff.1 hts
    rw [h t' this]

private theorem genPt_integral (S : Scheme.{0}) [IsIntegral S] (s : S) :
    GenPt s ↔ s = genericPoint S := by
  constructor
  · intro h
    exact (h _ (genericPoint_specializes s)).symm
  · rintro rfl t ht
    exact (ht.antisymm (genericPoint_specializes t)).eq

theorem UpperTheory.Gal.TranscendenceTraces.genBasic_of :
    GenBasic := by
  refine ⟨fun S => ?_, fun j _ s => genPt_open j s, fun S _ s => genPt_integral S s⟩
  rw [dense_iff_inter_open]
  rintro N hN ⟨s, hs⟩
  obtain ⟨t, hts, ht⟩ := genPt_exists_spec s
  exact ⟨t, hts.mem_open hN hs, ht⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PPtOne
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

private lemma ring_eq {Ω B L : Type} [Field Ω] [IsAlgClosed Ω] [CommRing B] [Algebra Ω B] [Module.Finite Ω B] [Field L]
    (f f' : B →+* L) (h : f.comp (algebraMap Ω B) = f'.comp (algebraMap Ω B))
    (hk : RingHom.ker f = RingHom.ker f') : f = f' := by
  haveI : (RingHom.ker f).IsPrime := RingHom.ker_isPrime f
  haveI : IsDomain (B ⧸ RingHom.ker f) := Ideal.Quotient.isDomain _
  have hb := IsAlgClosed.algebraMap_bijective_of_isIntegral (k := Ω) (K := B ⧸ RingHom.ker f)
  ext b
  obtain ⟨c, hc⟩ := hb.2 (Ideal.Quotient.mk _ b)
  have hm : b - algebraMap Ω B c ∈ RingHom.ker f := by
    rw [← Ideal.Quotient.eq]
    rw [← hc]
    rfl
  have h1 : f b = f (algebraMap Ω B c) := by
    have := RingHom.mem_ker.mp hm
    rw [map_sub, sub_eq_zero] at this
    exact this
  have h2 : f' b = f' (algebraMap Ω B c) := by
    have := RingHom.mem_ker.mp (hk ▸ hm)
    rw [map_sub, sub_eq_zero] at this
    exact this
  rw [h1, h2]
  exact congrArg (fun g : Ω →+* L => g c) h

private lemma pt_spec {B L : Type} [CommRing B] [Field L] (f : CommRingCat.of B ⟶ CommRingCat.of L) :
    (pt (Spec.map f) : Spec (CommRingCat.of B)).asIdeal = RingHom.ker f.hom := by
  ext b
  change f.hom b ∈ (IsLocalRing.closedPoint L).asIdeal ↔ _
  simp [RingHom.mem_ker, IsLocalRing.closedPoint]

theorem UpperTheory.Gal.TranscendenceTraces.ptOne_of :
    Chart → PtOne := by
  intro hC V Ω _ _ r _ L _ a z z' hz hz' hp
  obtain ⟨B, _, _, v, hfin, hpb⟩ := hC r Ω (𝟙 _)
  haveI : IsIso v := hpb.isIso_fst_of_isIso
  have hs : inv v ≫ Spec.map (CommRingCat.ofHom (algebraMap Ω B)) = r := by
    have := hpb.w
    rw [Category.comp_id] at this
    rw [← this, IsIso.inv_hom_id_assoc]
  obtain ⟨f, hf⟩ := Spec.map_surjective (z ≫ inv v)
  obtain ⟨f', hf'⟩ := Spec.map_surjective (z' ≫ inv v)
  have e1 : Spec.map f ≫ Spec.map (CommRingCat.ofHom (algebraMap Ω B)) = a := by
    rw [hf, Category.assoc, hs, hz]
  have e2 : Spec.map f' ≫ Spec.map (CommRingCat.ofHom (algebraMap Ω B)) = a := by
    rw [hf', Category.assoc, hs, hz']
  have e3 : CommRingCat.ofHom (algebraMap Ω B) ≫ f = CommRingCat.ofHom (algebraMap Ω B) ≫ f' := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_comp, e1, e2]
  have e4 : pt (Spec.map f) = pt (Spec.map f') := by
    rw [hf, hf', pt_comp, pt_comp, hp]
  have e5 : RingHom.ker f.hom = RingHom.ker f'.hom := by
    rw [← pt_spec f, ← pt_spec f', e4]
  have e6 : f.hom = f'.hom := ring_eq f.hom f'.hom (congrArg CommRingCat.Hom.hom e3) e5
  have e7 : f = f' := CommRingCat.hom_ext e6
  have e8 : z ≫ inv v = z' ≫ inv v := by rw [← hf, ← hf', e7]
  exact (cancel_mono (inv v)).mp e8
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PtExOf
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.ptEx_of :
    PtEx := by
  intro X s
  let Ω : Type := AlgebraicClosure (X.residueField s)
  let y : gp Ω ⟶ Spec (X.residueField s) :=
    Spec.map (CommRingCat.ofHom (algebraMap (X.residueField s) Ω))
  refine ⟨Ω, inferInstance, inferInstance, y ≫ X.fromSpecResidueField s, ?_⟩
  rw [pt_comp]
  exact Scheme.fromSpecResidueField_apply s (pt y)
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PTrPush
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.trPush_of :
    TrChar → FamPush → WtPush → RpBasic → RpOp → TrPush := by
  intro hTr hFam hWt hRp hOp q _ n i Z Z' S h p _ _ w hw hq x
  obtain ⟨σ, hσ, hσd⟩ := hFam q i h p w (trFam (h ≫ p) w q i) (hTr q i (h ≫ p) w hw hq).2.1
  have hw' := hWt h p w hw
  have e2 : tr p (Wt.push h w) q n i = σ.op n := by
    ext y
    exact (hTr q i p (Wt.push h w) hw' hq).2.2 σ hσ n ▸ rfl
  rw [e2]
  obtain ⟨a, ha⟩ := (hRp (ZMod q) (res (ZMod q) (tw q i)) Z' n).1 x
  have h1 := hOp (ZMod q) (ZMod q) σ n x a ha
  have h2 := hOp (ZMod q) (ZMod q) (trFam (h ≫ p) w q i) n _ _
    ((hRp (ZMod q) (res (ZMod q) (tw q i)) Z' n).2.2.2.1 Z h x a ha)
  exact ((hRp (ZMod q) (res (ZMod q) (tw q i)) S n).2.2.1 _ _ _ _ h2 h1).2.1 (hσd n a).symm
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PTrComp
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.trComp_of :
    TrChar → FamComp → WtComp → RpBasic → RpOp → TrComp := by
  intro hChar hFam hWc hRp hOp q _ n i W Z S r p _ _ w' w hr hp hq x
  have hrp : IsWt (r ≫ p) (Wt.mul r w' w) := hWc r p w' w hr hp
  have hqZ : IsUnit ((q : ℕ) : Γ(Z, ⊤)) := by
    have := hq.map p.appTop.hom
    rwa [map_natCast] at this
  obtain ⟨_, hsr, _⟩ := hChar q i r w' hr hqZ
  obtain ⟨_, hsp, _⟩ := hChar q i p w hp hq
  obtain ⟨σ, hσ, hσeq⟩ := hFam q i r p w' w (trFam r w' q i) (trFam p w q i) hsr hsp
  rw [(hChar q i (r ≫ p) _ hrp hq).2.2 σ hσ n, (hChar q i p w hp hq).2.2 _ hsp n,
    (hChar q i r w' hr hqZ).2.2 _ hsr n]
  obtain ⟨a, ha⟩ := (hRp (ZMod q) (res (ZMod q) (tw q i)) W n).1 x
  have h1 := hOp _ _ (trFam r w' q i) n x a ha
  have h2 := hOp _ _ (trFam p w q i) n _ _ h1
  have h3 := hOp _ _ σ n x a ha
  rw [hσeq n a] at h3
  exact ((hRp (ZMod q) (res (ZMod q) (tw q i)) S n).2.2.1 _ _ _ _ h3 h2).2.1 rfl
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PTrCompQ
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.trCompQ_of :
    TrHl → TrComp → WtComp → TrCompQ := by
  intro hHl hC hWC l _ n i W Z S r p _ _ w' w hr hp hl
  have hlZ : IsUnit ((l : ℕ) : Γ(Z, ⊤)) := by
    simpa using hl.map p.appTop.hom
  have hcomp : trHl l (r ≫ p) (Wt.mul r w' w) n i = trHl l p w n i ∘ₗ trHl l r w' n i := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    funext k
    haveI : NeZero (l ^ k) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
    have hlk : IsUnit ((l ^ k : ℕ) : Γ(S, ⊤)) := by
      rw [Nat.cast_pow]
      exact hl.pow k
    rw [LinearMap.comp_apply, hHl l n i p w hp hl, hHl l n i r w' hr hlZ,
      hHl l n i (r ≫ p) _ (hWC r p w' w hr hp) hl]
    exact hC (l ^ k) n i r p w' w hr hp hlk _
  unfold trHQ
  rw [hcomp, LinearMap.baseChange_comp]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.TrBCOf
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.trBC_of :
    TrChar → FamBC → WtBC → RpBasic → RpOp → TrBC := by
  intro hChar hFam hWbc hRp hOp q _ n i Z' S' Z S v p' p g _ w hpb hw hq x
  haveI : IsFinite p' := MorphismProperty.of_isPullback (P := @IsFinite) hpb inferInstance
  have hw' : IsWt p' (Wt.comap v w) := hWbc v p' p g w hpb hw
  have hq' : IsUnit ((q : ℕ) : Γ(S', ⊤)) := by
    have := hq.map g.appTop.hom
    rwa [map_natCast] at this
  obtain ⟨_, hs, _⟩ := hChar q i p w hw hq
  obtain ⟨τ', hτ', hτeq⟩ := hFam q i v p' p g w hpb (trFam p w q i) hs
  rw [(hChar q i p w hw hq).2.2 _ hs n, (hChar q i p' _ hw' hq').2.2 τ' hτ' n]
  obtain ⟨a, ha⟩ := (hRp (ZMod q) _ Z n).1 x
  have h1 := hOp _ _ (trFam p w q i) n x a ha
  have h2 := (hRp (ZMod q) _ S n).2.2.2.1 S' g _ _ h1
  have h3 := (hRp (ZMod q) _ Z n).2.2.2.1 Z' v x a ha
  have h4 := hOp _ _ τ' n _ _ h3
  have h5 : Rp ((τ'.op n) ((cpull ((chains (ZMod q)).map (sch.map v)) (res (ZMod q) (tw q i)) n) x))
      (Sec.res g ((((trFam p w q i).deg n).app (Sq.self p)) a)) := by
    have e := hτeq n a
    exact e ▸ h4
  exact ((hRp (ZMod q) _ S' n).2.2.1 _ _ _ _ h2 h5).2.1 rfl
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PMultSec
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

private theorem length_self_eq_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S) :
    Module.length R R = Module.length S S := by
  have : RingHomSurjective (e : R →+* S) := ⟨e.surjective⟩
  let f : R →ₛₗ[(e : R →+* S)] S :=
    { toFun := e, map_add' := e.map_add, map_smul' := fun a b => by simp [smul_eq_mul] }
  rw [Module.length, Module.length, WithBot.unbot_inj,
    Order.krullDim_eq_of_orderIso (Submodule.orderIsoMapComapOfBijective f e.bijective)]

private theorem length_stalk_eq_of_isIso {X Y : Scheme.{0}} (f : X ⟶ Y) [IsIso f] (x : X) (y : Y) (h : f x = y) :
    Module.length (X.presheaf.stalk x) (X.presheaf.stalk x) = Module.length (Y.presheaf.stalk y) (Y.presheaf.stalk y) := by
  subst h
  have : IsIso (f.stalkMap x) := inferInstance
  exact (length_self_eq_of_ringEquiv (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv).symm

theorem UpperTheory.Gal.TranscendenceTraces.multSec_of :
    MultSec := by
  intro V Ω _ _ r z hz
  haveI : IsIso (z ≫ r) := by rw [hz]; infer_instance
  haveI : IsIso (pullback.fst r (z ≫ r)) := inferInstance
  unfold mult
  rw [length_stalk_eq_of_isIso (pullback.fst r (z ≫ r)) _ (pt z)
    (by rw [← pt_comp, pullback.lift_fst])]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PMultSumPt
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.multSumPt_of :
    StalkSum → MultSec → PtLift → PtOne → FibFin → MultSumPt := by
  intro hS hM hL hO hF V Ω _ _ r _
  have hI : IsIntegralHom r := inferInstance
  have hbij : Set.BijOn (fun z : gp Ω ⟶ V => pt z) (fib r (𝟙 (gp Ω))) Set.univ := by
    refine ⟨fun _ _ => Set.mem_univ _, ?_, ?_⟩
    · intro z hz z' hz' h
      exact hO Ω r Ω (𝟙 (gp Ω)) z z' hz hz' h
    · intro v _
      have hv : r v = pt (𝟙 (gp Ω)) := by
        have h1 := pt_eq (𝟙 (gp Ω)) (r v)
        simpa using h1
      obtain ⟨z, hz, hzv⟩ := hL r Ω (𝟙 (gp Ω)) v hv
      exact ⟨z, hz, hzv⟩
  have hfin : Finite V := by
    have hu : (Set.univ : Set V).Finite := by
      rw [← hbij.image_eq]
      exact (hF r Ω (𝟙 (gp Ω))).image _
    exact Set.finite_univ_iff.mp hu
  show (∑ᶠ (z : gp Ω ⟶ V) (_ : z ∈ fib r (𝟙 (gp Ω))), mult r Ω z) = _
  rw [finsum_mem_eq_of_bijOn (fun z : gp Ω ⟶ V => pt z) hbij
    (g := fun v : V => ((Module.length (V.presheaf.stalk v) (V.presheaf.stalk v)).toNat : ℤ))
    (fun z hz => hM Ω r z hz), finsum_mem_univ, ← Nat.cast_finsum, hS Ω r]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PCorrCompQ
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.corrCompQ_of :
    CycComp → WtBC → WtComp → TrBCQ → TrCompQ → CorrCompQ := by
  intro hC hBC hWC hTB hTC S Y X c d
  haveI := c.fin
  haveI := d.fin
  have pb := IsPullback.of_hasPullback d.p c.f
  have hbw := hBC _ _ d.p c.f d.w pb d.wt
  have hw := hWC (pullback.snd d.p c.f) c.p (Wt.comap (pullback.fst d.p c.f) d.w) c.w hbw c.wt
  let e : Corr S X := ⟨pullback d.p c.f, pullback.snd d.p c.f ≫ c.p, pullback.fst d.p c.f ≫ d.f,
    Wt.mul (pullback.snd d.p c.f) (Wt.comap (pullback.fst d.p c.f) d.w) c.w, inferInstance, hw⟩
  refine ⟨e, pullback.fst d.p c.f, pullback.snd d.p c.f, pb, rfl, rfl, rfl, ?_, ?_⟩
  · exact hC c d e _ _ pb rfl rfl rfl
  · intro l _ n i hl hl2
    have hpull : pullHQ l (sch.map (pullback.fst d.p c.f ≫ d.f)) n i =
        pullHQ l (sch.map (pullback.fst d.p c.f)) n i ∘ₗ pullHQ l (sch.map d.f) n i := by
      simp only [pullHQ, Functor.map_comp, pullHl_comp, LinearMap.baseChange_comp]
    have key := hTB l n i _ _ d.p c.f d.w pb d.wt hl2
    show trHQ l (pullback.snd d.p c.f ≫ c.p) _ n i ∘ₗ pullHQ l (sch.map (pullback.fst d.p c.f ≫ d.f)) n i =
      (trHQ l c.p c.w n i ∘ₗ pullHQ l (sch.map c.f) n i) ∘ₗ (trHQ l d.p d.w n i ∘ₗ pullHQ l (sch.map d.f) n i)
    rw [hTC l n i _ _ _ _ hbw c.wt hl, hpull]
    refine LinearMap.ext fun v => ?_
    simp only [LinearMap.comp_apply]
    exact congrArg (trHQ l c.p c.w n i) (LinearMap.congr_fun key _).symm
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PTrBCQ
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.trBCQ_of :
    TrHl → TrBC → WtBC → TrBCQ := by
  intro hHl hBC hWt l _ n i Z' S' Z S v p' p g _ w hpb hw hl
  haveI : IsFinite p' := MorphismProperty.of_isPullback (P := @IsFinite) hpb inferInstance
  have hw' : IsWt p' (Wt.comap v w) := hWt v p' p g w hpb hw
  have hl' : IsUnit ((l : ℕ) : Γ(S', ⊤)) := by
    have := hl.map g.appTop.hom
    rwa [map_natCast] at this
  have key : pullHl l (sch.map g) n i ∘ₗ trHl l p w n i =
      trHl l p' (Wt.comap v w) n i ∘ₗ pullHl l (sch.map v) n i := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    funext k
    have hk : IsUnit ((↑(l ^ k) : ℕ) : Γ(S, ⊤)) := by
      rw [Nat.cast_pow]
      exact hl.pow k
    show (pull (ZMod (l ^ k)) (sch.map g) (tw (l ^ k) i) n) ((trHl l p w n i x).1 k) =
      (trHl l p' (Wt.comap v w) n i (pullHl l (sch.map v) n i x)).1 k
    rw [hHl l n i p w hw hl x k, hHl l n i p' (Wt.comap v w) hw' hl' _ k]
    exact hBC (l ^ k) n i v p' p g w hpb hw hk (x.1 k)
  unfold trHQ pullHQ
  rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp, key]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PTrSum
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.trSum_of :
    SumEx → SumNat → PtInj → FibFin → TrSum := by
  intro hEx hNat hInj hFin q _ i Z S p _ w hw hq
  have uniq : ∀ (A : Sq p) (a : Sec (tw q i) A.V) (b b' : Sec (tw q i) A.U),
      IsSum w A a b → IsSum w A a b' → b = b' := by
    intro A a b b' hb hb'
    apply hInj q i A.U b b'
    intro Ω _ _ x
    rw [hb Ω x, hb' Ω x]
  have ex : ∃ t : Fam0 p (tw q i) (tw q i),
      ∀ (A : Sq p) (a : Sec (tw q i) A.V), IsSum w A a (t.app A a) := by
    choose f hf using fun (A : Sq p) (a : Sec (tw q i) A.V) => hEx q i p w hw hq A a
    refine ⟨⟨fun A => { toFun := f A, map_zero' := ?_, map_add' := ?_ }, ?_⟩, ?_⟩
    · refine uniq A 0 _ _ (hf A 0) ?_
      intro Ω _ _ x
      simp [Sec.res]
    · intro a a'
      refine uniq A (a + a') _ _ (hf A (a + a')) ?_
      intro Ω _ _ x
      have hfin : (fib A.r x).Finite := by
        haveI := Sq.finite A
        exact hFin A.r Ω x
      rw [show Sec.res x (f A a + f A a') = Sec.res x (f A a) + Sec.res x (f A a') by simp [Sec.res],
        hf A a Ω x, hf A a' Ω x, ← finsum_mem_add_distrib hfin]
      apply finsum_mem_congr rfl
      intro z _
      simp [Sec.res, smul_add]
    · intro A B t a
      exact uniq A (Sec.res t.k a) _ _ (hNat _ (tw q i) w t a (f B a) (hf B a)) (hf A _)
    · intro A a
      exact hf A a
  exact pick_spec ex
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PMultBC
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

private lemma length_self_eq {R R' : Type} [CommRing R] [CommRing R'] (e : R ≃+* R') :
    Module.length R R = Module.length R' R' := by
  have h : ((Module.length R R : ℕ∞) : WithBot ℕ∞) = (Module.length R' R' : ℕ∞) := by
    rw [Module.coe_length, Module.coe_length]
    exact Order.krullDim_eq_of_orderIso e.idealComapOrderIso.symm
  exact_mod_cast h

private lemma length_stalk_eq {X Y : Scheme.{0}} (f : X ⟶ Y) [IsIso f] (x : X) (y : Y) (hy : f x = y) :
    Module.length (Y.presheaf.stalk y) (Y.presheaf.stalk y) =
      Module.length (X.presheaf.stalk x) (X.presheaf.stalk x) := by
  subst hy
  exact length_self_eq (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv

theorem UpperTheory.Gal.TranscendenceTraces.multBC_of :
    MultBC := by
  intro Z' S' Z S v p' p g h
  funext Ω _ _ z
  have hw : (z ≫ p') ≫ g = (z ≫ v) ≫ p := by
    simp only [Category.assoc, h.w]
  have hP : IsPullback (pullback.fst p' (z ≫ p') ≫ v) (pullback.snd p' (z ≫ p')) p ((z ≫ v) ≫ p) := by
    rw [← hw]
    exact (IsPullback.of_hasPullback p' (z ≫ p')).paste_horiz h
  have hl : (pullback.lift z (𝟙 _) (Category.id_comp _).symm : gp Ω ⟶ pullback p' (z ≫ p')) ≫ hP.isoPullback.hom =
      pullback.lift (z ≫ v) (𝟙 _) (Category.id_comp _).symm := by
    apply pullback.hom_ext
    · rw [Category.assoc, hP.isoPullback_hom_fst, pullback.lift_fst_assoc, pullback.lift_fst]
    · rw [Category.assoc, hP.isoPullback_hom_snd, pullback.lift_snd, pullback.lift_snd]
  have hpt : hP.isoPullback.hom (pt (pullback.lift z (𝟙 _) (Category.id_comp _).symm : gp Ω ⟶ pullback p' (z ≫ p'))) =
      pt (pullback.lift (z ≫ v) (𝟙 _) (Category.id_comp _).symm : gp Ω ⟶ pullback p ((z ≫ v) ≫ p)) := by
    rw [← pt_comp, hl]
  simp only [Wt.comap, mult]
  rw [length_stalk_eq hP.isoPullback.hom _ _ hpt]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PMultPt
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

private theorem exists_fac {Ω : Type} [Field Ω] {S : Scheme.{0}} (x : gp Ω ⟶ S) (s : S) (h : pt x = s) :
    ∃ a : gp Ω ⟶ Spec (S.residueField s), a ≫ S.fromSpecResidueField s = x := by
  obtain ⟨⟨t, a⟩, rfl⟩ := (Scheme.SpecToEquivOfField Ω S).symm.surjective x
  have hx : (Scheme.SpecToEquivOfField Ω S).symm ⟨t, a⟩ = Spec.map a ≫ S.fromSpecResidueField t := by
    simp [Scheme.SpecToEquivOfField]
  rw [hx] at h ⊢
  have hs : s ∈ Set.range (S.fromSpecResidueField t) := ⟨pt (Spec.map a), by rw [← pt_comp, h]⟩
  rw [Scheme.range_fromSpecResidueField, Set.mem_singleton_iff] at hs
  subst hs
  exact ⟨Spec.map a, rfl⟩

theorem UpperTheory.Gal.TranscendenceTraces.multPt_of :
    WtFlat → WtPt → MultBC → MultPt := by
  intro hflat hpt hbc Z S p _ Ω Ω' _ _ _ _ z z' hzz
  obtain ⟨s, hs⟩ : ∃ s, p (pt z) = s := ⟨_, rfl⟩
  have hpb := IsPullback.of_hasPullback p (S.fromSpecResidueField s)
  have hw := hpt (pullback.snd p (S.fromSpecResidueField s))
    (mult (pullback.snd p (S.fromSpecResidueField s))) (hflat _)
  have hm := hbc _ _ _ _ hpb
  obtain ⟨a, ha⟩ := exists_fac (z ≫ p) s (by rw [pt_comp, hs])
  obtain ⟨a', ha'⟩ := exists_fac (z' ≫ p) s (by rw [pt_comp, ← hzz, hs])
  obtain ⟨z1, e1⟩ : ∃ z1 : gp Ω ⟶ pullback p (S.fromSpecResidueField s),
      z1 ≫ pullback.fst _ _ = z := ⟨pullback.lift z a ha.symm, pullback.lift_fst _ _ _⟩
  obtain ⟨z1', e1'⟩ : ∃ z1' : gp Ω' ⟶ pullback p (S.fromSpecResidueField s),
      z1' ≫ pullback.fst _ _ = z' := ⟨pullback.lift z' a' ha'.symm, pullback.lift_fst _ _ _⟩
  have hp1 : pt z1 = pt z1' := by
    apply (IsPreimmersion.isEmbedding (pullback.fst p (S.fromSpecResidueField s))).injective
    rw [← pt_comp z1, ← pt_comp z1', e1, e1']
    exact hzz
  have key := hw Ω Ω' z1 z1' hp1
  rw [hm] at key
  simpa [Wt.comap, e1, e1'] using key
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PNwtDeg
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.nwtDeg_of :
    WtNormal → WtDegConst → MultSum → MultBC → GenBasic → NwtDeg := by
  intro hN hD hMS hBC hG Z' Z S K _ v p' p g _ _ hpb hLoc hg
  obtain ⟨hW, hgen⟩ := hN p hLoc
  obtain ⟨d, hd⟩ := hD p (nwt p) hW
  rw [hd]
  haveI : IsFinite p' := MorphismProperty.of_isPullback (P := @IsFinite) hpb inferInstance
  let Ω := AlgebraicClosure K
  let y : gp Ω ⟶ gp K := Spec.map (CommRingCat.ofHom (algebraMap K Ω))
  have hval := congrArg (fun w : Wt S => w Ω (y ≫ g)) hd
  simp only [Wt.const] at hval
  have h1 : Wt.push p (nwt p) Ω (y ≫ g) = Wt.push p (mult p) Ω (y ≫ g) := by
    simp only [Wt.push]
    apply finsum_congr
    intro z
    apply finsum_congr
    intro hz
    apply hgen
    have hz' : z ≫ p = y ≫ g := hz
    rw [hz', pt_comp, Subsingleton.elim (pt y) (IsLocalRing.closedPoint K)]
    exact (hG.2.2 S _).mpr hg
  have h2 : Wt.push p (mult p) Ω (y ≫ g) = Wt.push p' (mult p') Ω y := by
    simp only [Wt.push]
    symm
    rw [finsum_mem_eq_of_bijOn (fun z => z ≫ v) (fib_bijOn hpb y)
      (g := fun z => mult p Ω z)]
    intro z _
    rw [hBC v p' p g hpb]
    rfl
  have h3 := hMS p' Ω y
  have h4 : pt y = IsLocalRing.closedPoint K := Subsingleton.elim _ _
  rw [h1, h2, h3, h4] at hval
  rw [hval]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PCorrEq
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.corrEq_of :
    ImageFin → TrRel → TrPush → WtPush → CorrEq := by
  intro hIF hTR hTP hWP q _ n i S Y B bS bY _ _ ι _ c m hc hq D hD hcyc y
  obtain ⟨G, pG, fG, h, hpG, hh, hp, hf, hmono⟩ :=
    hIF bS bY ι (fun a => (c a).Z) (fun a => (c a).p) (fun a => (c a).f) (fun a => (c a).fin) hc
  haveI := hpG
  have hwt : ∀ a, IsWt (h a ≫ pG) (c a).w := by
    intro a
    rw [hp a]
    exact (c a).wt
  have key : ∀ a, (c a).op q n i y =
      tr pG (Wt.push (h a) (c a).w) q n i (pull (ZMod q) (sch.map fG) (tw q i) n y) := by
    intro a
    haveI := hh a
    rw [← hTP q n i (h a) pG (c a).w (hwt a) hq, ← pull_comp, ← Functor.map_comp, hf a]
    simp only [Corr.op, AddMonoidHom.comp_apply]
    rw [hp a]
  simp only [key]
  refine hTR q n i pG ι (fun a => Wt.push (h a) (c a).w) m
    (fun a => by haveI := hh a; exact hWP (h a) pG (c a).w (hwt a)) hq D hD ?_ _
  intro Ω _ _ z hz
  rw [← hcyc Ω (z ≫ pG) (z ≫ fG) hz]
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  have hs : fib (h a) z = {z' | z' ≫ (c a).p = z ≫ pG ∧ z' ≫ (c a).f = z ≫ fG} := by
    ext z'
    simp only [fib, Set.mem_setOf_eq]
    constructor
    · rintro rfl
      exact ⟨by rw [Category.assoc, hp a], by rw [Category.assoc, hf a]⟩
    · rintro ⟨h1, h2⟩
      apply hmono
      · rw [Category.assoc, hp a, h1]
      · rw [Category.assoc, hf a, h2]
  simp only [Wt.push, Corr.cyc]
  rw [hs]
end
