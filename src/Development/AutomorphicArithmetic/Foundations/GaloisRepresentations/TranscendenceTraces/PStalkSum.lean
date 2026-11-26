module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechLevelRepresentable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchClsCocycleSec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigOfOmegaInjectiveOfEqZero
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteMaximalSpectrumOfFiniteOfIsLocalRing

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PStalkSum
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

private theorem length_congr {R S : Type} [CommRing R] [CommRing S] (e : R ≃+* S) :
    Module.length R R = Module.length S S := by
  have : RingHomSurjective (e : R →+* S) := ⟨e.surjective⟩
  let f : R →ₛₗ[(e : R →+* S)] S :=
    { toFun := e
      map_add' := e.map_add
      map_smul' := fun a b => by simp [smul_eq_mul] }
  rw [Module.length, Module.length, WithBot.unbot_inj]
  exact Order.krullDim_eq_of_orderIso (Submodule.orderIsoMapComapOfBijective f e.bijective)

theorem UpperTheory.Gal.TranscendenceTraces.stalkSum_of :
    Chart → ArtSum → StalkSum := by
  intro hC hA V Ω _ _ r _
  obtain ⟨B, _, _, v, hfin, hpb⟩ := hC r Ω (𝟙 (gp Ω))
  have hv : IsIso v := hpb.isIso_fst_of_isIso
  have hr : r = inv v ≫ Spec.map (CommRingCat.ofHom (algebraMap Ω B)) := by
    rw [IsIso.eq_inv_comp, hpb.w, Category.comp_id]
  have hfl : Flat (Spec.map (CommRingCat.ofHom (algebraMap Ω B))) := by
    rw [Flat.SpecMap_iff]
    simpa [RingHom.flat_algebraMap_iff] using (inferInstance : Module.Flat Ω B)
  have hfi : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap Ω B))) := by
    rw [IsFinite.SpecMap_iff]
    simpa [RingHom.finite_algebraMap] using hfin
  have hR : Scheme.Hom.finrank r (IsLocalRing.closedPoint Ω) = Module.finrank Ω B := by
    rw [hr, Scheme.Hom.finrank_comp_left_of_isIso, Scheme.Hom.finrank_SpecMap_algebraMap,
      Module.rankAtStalk_eq_finrank_of_free]
    rfl
  have hs : ∀ P : PrimeSpectrum B, IsIso (v.stalkMap P) :=
    (IsOpenImmersion.iff_isIso_stalkMap (f := v)).mp inferInstance |>.2
  have e2 : ∀ P : PrimeSpectrum B,
      V.presheaf.stalk (v P) ≃+* Localization.AtPrime P.asIdeal := fun P =>
    ((asIso (v.stalkMap P)) ≪≫ Spec.stalkIso (CommRingCat.of B) P).commRingCatIsoToRingEquiv
  rw [hR, ← hA Ω B, ← finsum_comp_equiv v.homeomorph.toEquiv]
  refine finsum_congr fun P => ?_
  change (Module.length (V.presheaf.stalk (v P)) (V.presheaf.stalk (v P))).toNat = _
  rw [length_congr (e2 P)]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PWtFlat
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.wtFlat_of :
    WtClopen → MultSum → MultBC → MultOpen → WtFlat := by
  intro hC hS hB hO Z S p _ _ _
  refine hC p (mult p) fun A W hW => ?_
  have : IsFinite A.r := A.finite
  have : Flat A.r := MorphismProperty.of_isPullback A.pb ‹_›
  have : LocallyOfFinitePresentation A.r := MorphismProperty.of_isPullback A.pb ‹_›
  let O : A.V.Opens := ⟨W, hW.isOpen⟩
  have : IsClosedImmersion O.ι :=
    IsClosedImmersion.of_isPreimmersion O.ι (by rw [O.range_ι]; exact hW.isClosed)
  have hm : mult (O.ι ≫ A.r) = (mult A.r).comap O.ι := hO O.ι A.r
  have hm' : mult A.r = (mult p).comap A.v := hB A.v A.r p A.u A.pb
  refine ⟨fun u => (((O.ι ≫ A.r).finrank u : ℕ) : ℤ), ?_, ?_⟩
  · exact (Scheme.Hom.isLocallyConstant_finrank (O.ι ≫ A.r)).comp _
  · intro Ω _ _ x
    have h1 := hS (O.ι ≫ A.r) Ω x
    refine h1.symm.trans ?_
    change ∑ᶠ z ∈ fib (O.ι ≫ A.r) x, mult (O.ι ≫ A.r) Ω z = _
    refine finsum_mem_eq_of_bijOn (fun z => z ≫ O.ι) ⟨?_, ?_, ?_⟩ ?_
    · intro z hz
      refine ⟨?_, ?_⟩
      · change (z ≫ O.ι) ≫ A.r = x
        rw [Category.assoc]; exact hz
      · change pt (z ≫ O.ι) ∈ W
        rw [pt_comp]; exact (pt z).2
    · intro z _ z' _ e
      exact (cancel_mono O.ι).1 e
    · rintro z ⟨hz, hzW⟩
      have hr : Set.range z ⊆ Set.range O.ι := by
        rw [O.range_ι]
        rintro _ ⟨t, rfl⟩
        rw [pt_eq]; exact hzW
      refine ⟨IsOpenImmersion.lift O.ι z hr, ?_, IsOpenImmersion.lift_fac _ _ _⟩
      change _ ≫ O.ι ≫ A.r = x
      rw [← Category.assoc, IsOpenImmersion.lift_fac]; exact hz
    · intro z _
      rw [hm, hm']
      simp [Wt.comap]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PNwtGlue
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

private theorem lift_ex {Z S : Scheme.{0}} {p : Z ⟶ S} (A : Sq p) [IsOpenImmersion A.u] {Ω : Type} [Field Ω]
    (z : gp Ω ⟶ Z) (hz : pt (z ≫ p) ∈ Set.range A.u) : ∃ l : gp Ω ⟶ A.V, l ≫ A.v = z := by
  have hr : Set.range (z ≫ p) ⊆ Set.range A.u := by
    rintro _ ⟨t, rfl⟩
    rw [pt_eq]
    exact hz
  exact ⟨A.pb.lift z (IsOpenImmersion.lift A.u (z ≫ p) hr) (IsOpenImmersion.lift_fac _ _ _).symm,
    A.pb.lift_fst _ _ _⟩

theorem UpperTheory.Gal.TranscendenceTraces.nwtGlue_of :
    NwtAgree → WtLocal → MultBC → GenBasic → NwtGlue := by
  intro hAg hLoc hBC hGen Z S p _ h
  choose A w hopen hmem hw using h
  have hl : ∀ (Ω : Type) [Field Ω] (z : gp Ω ⟶ Z), ∃ l : gp Ω ⟶ (A (pt (z ≫ p))).V, l ≫ (A (pt (z ≫ p))).v = z := by
    intro Ω _ z
    haveI := hopen (pt (z ≫ p))
    exact lift_ex _ z (hmem _)
  choose l hlv using hl
  let W : Wt Z := fun Ω _ _ z => w (pt (z ≫ p)) Ω (l Ω z)
  have hcomap : ∀ t, W.comap (A t).v = w t := by
    intro t
    funext Ω _ _ z
    haveI := hopen t
    haveI := hopen (pt ((z ≫ (A t).v) ≫ p))
    exact hAg p (A _) (A t) (w _) (w t) (hw _) (hw t) Ω (l Ω (z ≫ (A t).v)) z (hlv Ω _)
  refine ⟨W, hLoc p W fun s => ⟨A s, hopen s, hmem s, ?_⟩, ?_⟩
  · rw [hcomap s]
    exact (hw s).1
  · intro Ω _ _ z hz
    set s := pt (z ≫ p) with hs
    haveI := hopen s
    have hz' : GenPt (pt (l Ω z ≫ (A s).r)) := by
      rw [← hGen.2.1 (A s).u, ← pt_comp, Category.assoc, ← (A s).pb.w, ← Category.assoc, hlv Ω z]
      exact hz
    have h1 := (hw s).2 Ω (l Ω z) hz'
    have h2 := hBC (A s).v (A s).r p (A s).u (A s).pb
    change w s Ω (l Ω z) = _
    rw [h1, h2]
    change mult p Ω (l Ω z ≫ (A s).v) = _
    rw [hlv Ω z]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PMultEt
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

private theorem isOpenImmersion_of_section {X Y : Scheme.{0}} (f : X ⟶ Y) (s : Y ⟶ X) [Etale f] (h : s ≫ f = 𝟙 Y) :
    IsOpenImmersion s := by
  have hpb := pullback_lift_diagonal_isPullback s f
  have hgr := MorphismProperty.of_isPullback (P := @IsOpenImmersion) hpb
    (inferInstance : IsOpenImmersion (pullback.diagonal f))
  have hsnd : IsOpenImmersion (pullback.snd (s ≫ f) f) := by
    have : IsIso (s ≫ f) := by rw [h]; infer_instance
    infer_instance
  have hs : s = pullback.lift (𝟙 Y) s (by simp [h]) ≫ pullback.snd (s ≫ f) f :=
    (pullback.lift_snd _ _ _).symm
  rw [hs]
  exact IsOpenImmersion.comp _ _

private theorem length_self_of_isField (R : Type) [CommRing R] (h : IsField R) : Module.length R R = 1 := by
  rw [Module.length_eq_one_iff, isSimpleModule_self_iff_isUnit]
  obtain ⟨a, b, hab⟩ := h.exists_pair_ne
  refine ⟨⟨a, b, hab⟩, fun x hx => ?_⟩
  obtain ⟨y, hy⟩ := h.mul_inv_cancel hx
  exact ⟨⟨x, y, hy, by rw [mul_comm]; exact hy⟩, rfl⟩

private theorem length_stalk_pt {V : Scheme.{0}} {Ω : Type} [Field Ω] (s : gp Ω ⟶ V) [IsOpenImmersion s] :
    Module.length (V.presheaf.stalk (pt s)) (V.presheaf.stalk (pt s)) = 1 := by
  have hK : IsField ((Spec (CommRingCat.of Ω)).presheaf.stalk (IsLocalRing.closedPoint Ω)) := by
    have e : (IsLocalRing.closedPoint Ω : Spec (CommRingCat.of Ω)) = genericPoint _ :=
      Subsingleton.elim _ _
    rw [e]
    exact (inferInstance : Field (Spec (CommRingCat.of Ω)).functionField).toIsField
  haveI := (IsOpenImmersion.iff_isIso_stalkMap.mp ‹IsOpenImmersion s›).2 (IsLocalRing.closedPoint Ω)
  have hV : IsField (V.presheaf.stalk (pt s)) :=
    MulEquiv.isField hK (asIso (s.stalkMap (IsLocalRing.closedPoint Ω))).commRingCatIsoToRingEquiv.toMulEquiv
  exact length_self_of_isField _ hV

theorem UpperTheory.Gal.TranscendenceTraces.multEt_of :
    MultEt := by
  intro Z S p _
  funext Ω _ _ z
  change mult p Ω z = (1 : ℤ)
  have hσ : IsOpenImmersion (pullback.lift z (𝟙 (gp Ω)) (Category.id_comp _).symm : gp Ω ⟶ pullback p (z ≫ p)) :=
    isOpenImmersion_of_section (pullback.snd p (z ≫ p)) _ (pullback.lift_snd _ _ _)
  have hl := length_stalk_pt (pullback.lift z (𝟙 (gp Ω)) (Category.id_comp _).symm : gp Ω ⟶ pullback p (z ≫ p))
  simp only [mult]
  rw [hl]
  rfl
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PNormSpec
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.normSpec_of :
    SplitCover → CountEx → CountWt → MultPt → PtEx → PtLift → GenBasic → NormSpec := by
  intro hS hCE hCW hMP hPE hPL _
  unfold NormSpec
  intro A B _ _ _ _ _ _
  set p := Spec.map (CommRingCat.ofHom (algebraMap A B)) with hp
  haveI : IsFinite p := by
    rw [hp, IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.mpr inferInstance
  obtain ⟨T, π, ι, σ, c, hπi, hπs, hι, hσ, hsym, hgen⟩ := hS A B
  haveI := hπi
  haveI := hπs
  haveI := hι
  have hk : ∀ s : ↥(Spec (CommRingCat.of B)), ∃ (Ω : Type) (_ : Field Ω) (_ : IsAlgClosed Ω)
      (y : gp Ω ⟶ Spec (CommRingCat.of B)), pt y = s := fun s => hPE _ s
  choose Ωk fk ak yk hyk using hk
  let key : ↥(Spec (CommRingCat.of B)) → ℤ := fun s => letI := fk s; letI := ak s; mult p (Ωk s) (yk s)
  let m : ι → ℤ := fun j => key (c j)
  have hm : ∀ j (Ω : Type) [Field Ω] [IsAlgClosed Ω] (z : gp Ω ⟶ Spec (CommRingCat.of B)),
      c j = pt z → m j = mult p Ω z := by
    intro j Ω _ _ z hz
    letI := fk (c j)
    letI := ak (c j)
    exact hMP p (Ωk (c j)) Ω (yk (c j)) z ((hyk (c j)).trans hz)
  have hSy : UpperTheory.Gal.TranscendenceTraces.Sym π σ m := by
    unfold UpperTheory.Gal.TranscendenceTraces.Sym
    intro Ω _ _ x x' hxx'
    obtain ⟨e, he⟩ := hsym Ω x x' hxx'
    exact ⟨e, fun j => ⟨(he j).1, congrArg key (he j).2⟩⟩
  obtain ⟨w, hw⟩ := hCE p π σ m hSy
  refine ⟨w, hCW p π σ m w hσ hw, ?_⟩
  intro Ω _ _ z hz
  obtain ⟨v, hv⟩ := π.surjective (pt (z ≫ p))
  obtain ⟨x, hx, -⟩ := hPL π Ω (z ≫ p) v hv
  have hcount := hw Ω x z hx.symm
  have hbot : (pt (x ≫ π)).asIdeal = ⊥ := by
    rw [hx]
    unfold GenPt at hz
    have h0 := hz (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum A) ((PrimeSpectrum.le_iff_specializes _ _).mp bot_le)
    rw [← h0]
  obtain ⟨⟨j0, hj0, huniq⟩, hcj⟩ := hgen Ω x z hx.symm hbot
  have hset : {j | x ≫ σ j = z} = {j0} := by
    ext j
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · exact huniq j
    · rintro rfl
      exact hj0
  rw [hcount, hset, finsum_mem_singleton]
  exact hm j0 Ω z (hcj j0 hj0)
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PFunSec
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

private theorem res_zsmul {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (c : ℤ) (x : Sec F U) :
    Sec.res g (c • x) = c • Sec.res g x := by
  simp

private theorem sec_eq_of_isEmpty {R : Type} [CommRing R] {F : Shv R} (W : Scheme.{0}) [IsEmpty W] (a b : Sec F W) : a = b :=
  (GlobalTheory.T.etaleSheafSections_ext_and_glue R F W).1 a b (GlobalTheory.T.etaleLocal_property_calculus_rules.2.2.2.2.2.2 W _)

theorem UpperTheory.Gal.TranscendenceTraces.funSec_of :
    FunSec := by
  intro q _ i U ζ φ hφ
  let V : ℤ → U.Opens := fun n => ⟨{x | φ x = n}, hφ.isOpen_fiber n⟩
  have hmem : ∀ (n : ℤ) (v : (V n : Scheme)), φ ((V n).ι v) = n := by
    intro n v
    have h1 : (V n).ι v ∈ Set.range (V n).ι := ⟨v, rfl⟩
    rw [Scheme.Opens.range_ι] at h1
    exact h1
  have hcov : ∀ u : U, ∃ n, ∃ v, (V n).ι v = u := by
    intro u
    refine ⟨φ u, ?_⟩
    have h1 : u ∈ Set.range (V (φ u)).ι := by
      rw [Scheme.Opens.range_ι]
      exact rfl
    exact h1
  obtain ⟨y, hy⟩ := (GlobalTheory.T.etaleSheafSections_sep_glue_of_surjective_family (ZMod q) (tw q i) U ℤ (fun n => (V n : Scheme)) (fun n => (V n).ι)
    (fun n => inferInstance) hcov).2 (fun n => n • Sec.res (V n).ι (twGen i ζ)) (by
      intro n m
      by_cases h : n = m
      · subst h
        rw [res_zsmul, res_zsmul, res_res, res_res, pullback.condition]
      · haveI : IsEmpty ↥(pullback (V n).ι (V m).ι) := by
          refine ⟨fun p => h ?_⟩
          have e1 := hmem n (pullback.fst (V n).ι (V m).ι p)
          have e2 := hmem m (pullback.snd (V n).ι (V m).ι p)
          have hc : (V n).ι (pullback.fst (V n).ι (V m).ι p) =
              (V m).ι (pullback.snd (V n).ι (V m).ι p) :=
            congrArg (fun f : pullback (V n).ι (V m).ι ⟶ U => f p) pullback.condition
          rw [hc] at e1
          exact e1.symm.trans e2
        exact sec_eq_of_isEmpty _ _ _)
  refine ⟨y, ?_⟩
  intro Ω _ _ x
  have hr : Set.range x ⊆ Set.range (V (φ (pt x))).ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨s, rfl⟩
    show φ (x s) = φ (pt x)
    rw [pt_eq]
  obtain ⟨k, hk⟩ : ∃ k, k ≫ (V (φ (pt x))).ι = x := ⟨_, IsOpenImmersion.lift_fac _ _ hr⟩
  calc Sec.res x y = Sec.res (k ≫ (V (φ (pt x))).ι) y := by rw [hk]
    _ = Sec.res k ((φ (pt x)) • Sec.res (V (φ (pt x))).ι (twGen i ζ)) := by
        rw [← res_res, hy]
    _ = φ (pt x) • Sec.res x (twGen i ζ) := by rw [res_zsmul, res_res, hk]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PRpBasic
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

private theorem cohomologyClass_mk_zsmul {R : Type} [CommRing R] {K L : Cx R} {n : ℤ} (d : ℤ) (a : Cocycle K L n) :
    CohomologyClass.mk (d • a) = d • CohomologyClass.mk a :=
  map_zsmul (CohomologyClass.mkAddMonoidHom K L n) d a

private theorem ev_cocycle_add {R : Type} [CommRing R] (I : Cx R) (X : Scheme) (n : ℤ) (h0 : -((0 : ℕ) : ℤ) + n = n)
    (α β : Cocycle ((chains R).obj (sch.obj X)) I n) :
    ev ((α + β : Cocycle ((chains R).obj (sch.obj X)) I n) : Cochain ((chains R).obj (sch.obj X)) I n) 0 n h0 X (𝟙 X) =
      ev (α : Cochain ((chains R).obj (sch.obj X)) I n) 0 n h0 X (𝟙 X) +
        ev (β : Cochain ((chains R).obj (sch.obj X)) I n) 0 n h0 X (𝟙 X) := by
  rw [Cocycle.coe_add]
  exact ((GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := sch.obj X) (I := I) (n := n)).1 _ _ 0 n h0 X (𝟙 X)).1

private theorem ev_cocycle_zsmul {R : Type} [CommRing R] (I : Cx R) (X : Scheme) (n : ℤ) (h0 : -((0 : ℕ) : ℤ) + n = n)
    (d : ℤ) (α : Cocycle ((chains R).obj (sch.obj X)) I n) :
    ev ((d • α : Cocycle ((chains R).obj (sch.obj X)) I n) : Cochain ((chains R).obj (sch.obj X)) I n) 0 n h0 X (𝟙 X) =
      d • ev (α : Cochain ((chains R).obj (sch.obj X)) I n) 0 n h0 X (𝟙 X) := by
  rw [Cocycle.coe_smul]
  exact ((GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := sch.obj X) (I := I) (n := n)).1 _ 0 0 n h0 X (𝟙 X)).2.2.2 d

theorem UpperTheory.Gal.TranscendenceTraces.rpBasic_of :
    RpBasic := by
  intro R _ I X n
  have ev_lin := GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := sch.obj X) (I := I) (n := n)
  have key := fun (α : Cocycle ((chains R).obj (sch.obj X)) I n) =>
    (GlobalTheory.T.cocycle_ev_d_eq_zero_and_mk_eq_zero_iff R X I (n - 1) n (n + 1) (by ring) rfl).2 α
  have h0 : -((0 : ℕ) : ℤ) + n = n := by simp
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x
    obtain ⟨α, rfl⟩ := CohomologyClass.mk_surjective x
    exact ⟨_, α, rfl, rfl⟩
  · rintro x a ⟨α, -, rfl⟩
    exact (key α).1
  · rintro x x' a a' ⟨α, rfl, ha⟩ ⟨β, rfl, hb⟩
    subst ha hb
    have hiff : CohomologyClass.mk α = CohomologyClass.mk β ↔
        ∃ y, Sec.map (I.d (n - 1) n) y =
          ev (α : Cochain ((chains R).obj (sch.obj X)) I n) 0 n h0 X (𝟙 X) -
            ev (β : Cochain ((chains R).obj (sch.obj X)) I n) 0 n h0 X (𝟙 X) := by
      rw [← sub_eq_zero, ← CohomologyClass.mk_sub, (key (α - β)).2, Cocycle.coe_sub,
        (ev_lin.1 (α : Cochain _ I n) β 0 n h0 X (𝟙 X)).2.1]
    refine ⟨hiff, fun h => hiff.2 ⟨0, ?_⟩, ⟨α + β, CohomologyClass.mk_add α β, ev_cocycle_add I X n h0 α β⟩,
      fun d => ⟨d • α, cohomologyClass_mk_zsmul d α, ev_cocycle_zsmul I X n h0 d α⟩⟩
    rw [h, sub_self]
    exact map_zero _
  · rintro Y f x a ⟨α, rfl, rfl⟩
    refine ⟨zcomp (Cocycle.ofHom ((chains R).map (sch.map f))) α (zero_add n), rfl, ?_⟩
    have h1 := ev_lin.2.2.2.1 (sch.map f) (α : Cochain _ I n) 0 n h0 Y (𝟙 Y)
    have h2 := ev_lin.2.1 (α : Cochain _ I n) 0 n h0 Y X f (𝟙 X)
    exact h1.trans h2.symm
  · rintro R' _ J ρ x a ⟨α, rfl, rfl⟩
    obtain ⟨β, hβ⟩ := SemiMap.image_exists ρ (sch.obj X) n α
    exact ⟨β, (SemiMap.op_spec ρ (sch.obj X) n α β hβ).symm, hβ 0 n h0 X (𝟙 X)⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PTrLin
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

private theorem op_add_of (hRp : RpBasic) (hOp : RpOp) {q : ℕ} {i n : ℤ} {Z S : Scheme.{0}} {p : Z ⟶ S}
    (τ τ' σ : Fam p (res (ZMod q) (tw q i)) (res (ZMod q) (tw q i)))
    (h : ∀ a, (σ.deg n).app (Sq.self p) a = (τ.deg n).app (Sq.self p) a + (τ'.deg n).app (Sq.self p) a)
    (x : CohomologyClass ((chains (ZMod q)).obj (sch.obj Z)) (res (ZMod q) (tw q i)) n) :
    σ.op n x = τ.op n x + τ'.op n x := by
  obtain ⟨a, ha⟩ := ((hRp (ZMod q) (res (ZMod q) (tw q i)) Z n).1) x
  have h1 := hOp (ZMod q) (ZMod q) τ n x a ha
  have h2 := hOp (ZMod q) (ZMod q) τ' n x a ha
  have h3 := hOp (ZMod q) (ZMod q) σ n x a ha
  have hS := (hRp (ZMod q) (res (ZMod q) (tw q i)) S n).2.2.1
  have h4 := (hS _ _ _ _ h1 h2).2.2.1
  exact (hS _ _ _ _ h3 h4).2.1 (h a)

private theorem op_smul_of (hRp : RpBasic) (hOp : RpOp) {q : ℕ} {i n : ℤ} {Z S : Scheme.{0}} {p : Z ⟶ S} (d : ℤ)
    (τ σ : Fam p (res (ZMod q) (tw q i)) (res (ZMod q) (tw q i)))
    (h : ∀ a, (σ.deg n).app (Sq.self p) a = d • (τ.deg n).app (Sq.self p) a)
    (x : CohomologyClass ((chains (ZMod q)).obj (sch.obj Z)) (res (ZMod q) (tw q i)) n) :
    σ.op n x = d • τ.op n x := by
  obtain ⟨a, ha⟩ := ((hRp (ZMod q) (res (ZMod q) (tw q i)) Z n).1) x
  have h1 := hOp (ZMod q) (ZMod q) τ n x a ha
  have h3 := hOp (ZMod q) (ZMod q) σ n x a ha
  have hS := (hRp (ZMod q) (res (ZMod q) (tw q i)) S n).2.2.1
  have h4 := (hS _ _ _ _ h1 h1).2.2.2 d
  exact (hS _ _ _ _ h3 h4).2.1 (h a)

private theorem op_id_of (hRp : RpBasic) (hOp : RpOp) {q : ℕ} {i n : ℤ} {S : Scheme.{0}} (d : ℤ)
    (σ : Fam (𝟙 S) (res (ZMod q) (tw q i)) (res (ZMod q) (tw q i)))
    (h : ∀ a, (σ.deg n).app (Sq.self (𝟙 S)) a = d • a)
    (x : CohomologyClass ((chains (ZMod q)).obj (sch.obj S)) (res (ZMod q) (tw q i)) n) :
    σ.op n x = d • x := by
  obtain ⟨a, ha⟩ := ((hRp (ZMod q) (res (ZMod q) (tw q i)) S n).1) x
  have h3 := hOp (ZMod q) (ZMod q) σ n x a ha
  have hS := (hRp (ZMod q) (res (ZMod q) (tw q i)) S n).2.2.1
  have h4 := (hS _ _ _ _ ha ha).2.2.2 d
  exact (hS _ _ _ _ h3 h4).2.1 (h a)

theorem UpperTheory.Gal.TranscendenceTraces.trLin_of :
    TrChar → FamLin → WtLin → RpBasic → RpOp → TrLin := by
  intro hChar hFam hWt hRp hOp q _ n i
  refine ⟨?_, ?_, ?_⟩
  · intro Z S p _ w w' hw hw' hq x
    obtain ⟨σ, hσ, hσd⟩ := (hFam q i).1 p w w' (trFam p w q i) (trFam p w' q i)
      (hChar q i p w hw hq).2.1 (hChar q i p w' hw' hq).2.1
    rw [(hChar q i p (w.add w') (hWt.1 p w w' hw hw') hq).2.2 σ hσ n]
    exact op_add_of hRp hOp _ _ σ (fun a => hσd n _ a) x
  · intro Z S p _ d w hw hq x
    obtain ⟨σ, hσ, hσd⟩ := (hFam q i).2.1 p d w (trFam p w q i) (hChar q i p w hw hq).2.1
    rw [(hChar q i p (w.smul d) (hWt.2.1 p d w hw) hq).2.2 σ hσ n]
    exact op_smul_of hRp hOp d _ σ (fun a => hσd n _ a) x
  · intro S d hq x
    obtain ⟨σ, hσ, hσd⟩ := (hFam q i).2.2 S d
    rw [(hChar q i (𝟙 S) (Wt.const S d) (hWt.2.2 (𝟙 S) d) hq).2.2 σ hσ n]
    exact op_id_of hRp hOp d σ (fun a => hσd n a) x
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PNwtAgree
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.nwtAgree_of :
    NwtOpen → WtUnique → GenBasic → MultBC → NwtAgree := by
  intro hOpen hUniq hGen _ Z S p _ A B _ _ w w' hw hw' Ω _ _ z z' hz
  have hc : pullback.fst A.u B.u ≫ A.u = pullback.snd A.u B.u ≫ B.u := pullback.condition
  have hP : IsPullback (pullback.fst p (pullback.fst A.u B.u ≫ A.u))
      (pullback.snd p (pullback.fst A.u B.u ≫ A.u)) p (pullback.fst A.u B.u ≫ A.u) :=
    IsPullback.of_hasPullback _ _
  have hP' : IsPullback (pullback.fst p (pullback.fst A.u B.u ≫ A.u))
      (pullback.snd p (pullback.fst A.u B.u ≫ A.u)) p (pullback.snd A.u B.u ≫ B.u) := by
    rw [← hc]
    exact hP
  have eA : pullback.fst p (pullback.fst A.u B.u ≫ A.u) ≫ p =
      (pullback.snd p (pullback.fst A.u B.u ≫ A.u) ≫ pullback.fst A.u B.u) ≫ A.u := by
    rw [Category.assoc]
    exact hP.w
  have eB : pullback.fst p (pullback.fst A.u B.u ≫ A.u) ≫ p =
      (pullback.snd p (pullback.fst A.u B.u ≫ A.u) ≫ pullback.snd A.u B.u) ≫ B.u := by
    rw [Category.assoc]
    exact hP'.w
  let C : Sq A.r := ⟨pullback A.u B.u, pullback p (pullback.fst A.u B.u ≫ A.u), pullback.fst A.u B.u,
    A.pb.lift _ _ eA, pullback.snd p (pullback.fst A.u B.u ≫ A.u),
    IsPullback.of_right (by rw [A.pb.lift_fst]; exact hP) (A.pb.lift_snd _ _ _) A.pb⟩
  let C' : Sq B.r := ⟨pullback A.u B.u, pullback p (pullback.fst A.u B.u ≫ A.u), pullback.snd A.u B.u,
    B.pb.lift _ _ eB, pullback.snd p (pullback.fst A.u B.u ≫ A.u),
    IsPullback.of_right (by rw [B.pb.lift_fst]; exact hP') (B.pb.lift_snd _ _ _) B.pb⟩
  haveI : IsOpenImmersion C.u := inferInstanceAs (IsOpenImmersion (pullback.fst A.u B.u))
  haveI : IsOpenImmersion C'.u := inferInstanceAs (IsOpenImmersion (pullback.snd A.u B.u))
  have h1 : IsNwt (pullback.snd p (pullback.fst A.u B.u ≫ A.u)) (w.comap C.v) := hOpen A.r w C hw
  have h2 : IsNwt (pullback.snd p (pullback.fst A.u B.u ≫ A.u)) (w'.comap C'.v) := hOpen B.r w' C' hw'
  haveI : IsFinite (pullback.snd p (pullback.fst A.u B.u ≫ A.u)) := MorphismProperty.of_isPullback hP ‹_›
  have hE : w.comap C.v = w'.comap C'.v :=
    hUniq _ _ _ h1.1 h2.1 {s | GenPt s} (hGen.1 _) fun Ω _ _ y hy => by
      rw [h1.2 Ω y hy, h2.2 Ω y hy]
  have e1 : (z ≫ A.r) ≫ A.u = (z' ≫ B.r) ≫ B.u := by
    rw [Category.assoc, Category.assoc, ← A.pb.w, ← B.pb.w, ← Category.assoc, ← Category.assoc, hz]
  have e2 : (z ≫ A.v) ≫ p = pullback.lift (z ≫ A.r) (z' ≫ B.r) e1 ≫ pullback.fst A.u B.u ≫ A.u := by
    rw [pullback.lift_fst_assoc, Category.assoc, Category.assoc, A.pb.w]
  let z0 : gp Ω ⟶ pullback p (pullback.fst A.u B.u ≫ A.u) :=
    pullback.lift (z ≫ A.v) (pullback.lift (z ≫ A.r) (z' ≫ B.r) e1) e2
  have hz0 : z0 ≫ C.v = z := by
    apply A.pb.hom_ext
    · change (z0 ≫ A.pb.lift _ _ eA) ≫ A.v = _
      rw [Category.assoc, A.pb.lift_fst]
      exact pullback.lift_fst _ _ _
    · change (z0 ≫ A.pb.lift _ _ eA) ≫ A.r = _
      rw [Category.assoc, A.pb.lift_snd, pullback.lift_snd_assoc, pullback.lift_fst]
  have hz0' : z0 ≫ C'.v = z' := by
    apply B.pb.hom_ext
    · change (z0 ≫ B.pb.lift _ _ eB) ≫ B.v = _
      rw [Category.assoc, B.pb.lift_fst, ← hz]
      exact pullback.lift_fst _ _ _
    · change (z0 ≫ B.pb.lift _ _ eB) ≫ B.r = _
      rw [Category.assoc, B.pb.lift_snd, pullback.lift_snd_assoc, pullback.lift_snd]
  have := congrFun (congrFun (congrFun (congrFun hE Ω) ‹_›) ‹_›) z0
  simpa only [Wt.comap, hz0, hz0'] using this
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PFinSec
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces
open scoped TensorProduct

namespace UpperTheory.Gal.TranscendenceTraces.FiniteSectionsSeparable

private theorem sepClosed_of_isAlgebraic (K L : Type) [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L] [IsSepClosed K] : IsSepClosed L := by
  refine IsSepClosed.of_exists_root _ fun p hm hirr hsep => ?_
  have hdeg : p.degree ≠ 0 := fun h => hirr.not_isUnit (Polynomial.isUnit_iff_degree_eq_zero.2 h)
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_aeval_eq_zero (AlgebraicClosure L) p hdeg
  haveI : Algebra.IsAlgebraic K (AlgebraicClosure L) := Algebra.IsAlgebraic.trans K L _
  haveI : IsPurelyInseparable L (AlgebraicClosure L) :=
    IsPurelyInseparable.tower_top K L (AlgebraicClosure L)
  have hs : IsSeparable L r := Polynomial.Separable.of_dvd hsep (minpoly.dvd L r hr)
  obtain ⟨x, rfl⟩ := IsPurelyInseparable.inseparable' r hs
  refine ⟨x, (algebraMap L (AlgebraicClosure L)).injective ?_⟩
  rw [map_zero, ← hr, Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval]

private theorem sh_of_finite (O T : Type) [CommRing O] [CommRing T] [Algebra O T]
    [Module.Finite O T] (hO : SH O) (hT : HenselianLocalRing T) : SH T := by
  obtain ⟨hH, hS⟩ := hO
  haveI := hH
  haveI := hT
  refine ⟨hT, ?_⟩
  haveI : IsLocalHom (algebraMap O T) := ⟨fun a ha => by
    by_contra h
    have h1 : a ∈ IsLocalRing.maximalIdeal O := h
    rw [← GlobalTheory.comap_eq_maximalIdeal_of_finite (IsLocalRing.maximalIdeal T)] at h1
    exact (Ideal.mem_comap.1 h1) ha⟩
  letI : Algebra (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField T) :=
    (IsLocalRing.ResidueField.map (algebraMap O T)).toAlgebra
  haveI : Algebra.IsAlgebraic (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField T) := by
    refine ⟨fun x => ?_⟩
    obtain ⟨t, rfl⟩ := IsLocalRing.residue_surjective x
    obtain ⟨p, hp, h0⟩ := Algebra.IsIntegral.isIntegral (R := O) t
    refine IsIntegral.isAlgebraic ⟨p.map (IsLocalRing.residue O), hp.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    have h2 : (algebraMap (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField T)).comp
        (IsLocalRing.residue O) = (IsLocalRing.residue T).comp (algebraMap O T) := rfl
    rw [h2, ← Polynomial.hom_eval₂, h0, map_zero]
  exact sepClosed_of_isAlgebraic (IsLocalRing.ResidueField O) _

private theorem exists_ringHom (hS : SHSec) (B C T : Type) [CommRing B] [CommRing C] [CommRing T]
    [Algebra B C] [Algebra.Etale B C] [Module.FaithfullyFlat B C] [Algebra B T] (hT : SH T) :
    ∃ f : C →+* T, ∀ b, f (algebraMap B C b) = algebraMap B T b := by
  obtain ⟨s⟩ := hS T (T ⊗[B] C) hT
  refine ⟨s.toRingHom.comp (Algebra.TensorProduct.includeRight : C →ₐ[B] T ⊗[B] C).toRingHom, fun b => ?_⟩
  have h1 : (Algebra.TensorProduct.includeRight : C →ₐ[B] T ⊗[B] C) (algebraMap B C b) =
      algebraMap T (T ⊗[B] C) (algebraMap B T b) := by
    rw [AlgHom.commutes, IsScalarTower.algebraMap_apply B T (T ⊗[B] C)]
  change s ((Algebra.TensorProduct.includeRight : C →ₐ[B] T ⊗[B] C) (algebraMap B C b)) = _
  rw [h1]
  exact s.commutes _

end UpperTheory.Gal.TranscendenceTraces.FiniteSectionsSeparable

open UpperTheory.Gal.TranscendenceTraces.FiniteSectionsSeparable in
theorem UpperTheory.Gal.TranscendenceTraces.finSec_of :
    SHSec → FinSec := by
  intro hS O B C _ _ _ _ _ _ _ _ hO
  obtain ⟨hH, -⟩ := id hO
  haveI := hH
  obtain ⟨ι, _, T, _, _, e, hT⟩ := GlobalTheory.exists_algEquiv_pi_henselianLocalRing O B
  have key : ∀ i, ∃ f : C →+* T i, ∀ b, f (algebraMap B C b) = e b i := by
    intro i
    haveI := (hT i).2
    have hs := sh_of_finite O (T i) hO (hT i).1
    letI : Algebra B (T i) := ((Pi.evalRingHom T i).comp (e : B →+* Π i, T i)).toAlgebra
    exact exists_ringHom hS B C (T i) hs
  choose f hf using key
  refine ⟨{ toRingHom := (e.symm : (Π i, T i) →+* B).comp (Pi.ringHom f), commutes' := fun b => ?_ }⟩
  have h : Pi.ringHom f (algebraMap B C b) = e b := funext fun i => hf i b
  change e.symm (Pi.ringHom f (algebraMap B C b)) = b
  rw [h]
  exact e.symm_apply_apply b
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PGalTrans
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

private lemma exists_pow_mem_of_fixed (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [Normal K L] (q : ℕ) [ExpChar K q] (x : L) (hx : ∀ σ : L ≃ₐ[K] L, σ x = x) :
    ∃ n, x ^ q ^ n ∈ (algebraMap K L).range := by
  classical
  rw [← mem_perfectClosure_iff_pow_mem q, mem_perfectClosure_iff_natSepDegree_eq_one]
  have hint : IsIntegral K x := Algebra.IsIntegral.isIntegral x
  have hspl : ((minpoly K x).map (algebraMap K L)).Splits := Normal.splits inferInstance x
  rw [Polynomial.natSepDegree_eq_of_splits _ hspl, Finset.card_eq_one]
  refine ⟨x, ?_⟩
  ext y
  simp only [Multiset.mem_toFinset, Polynomial.mem_aroots, Finset.mem_singleton]
  constructor
  · rintro ⟨-, hy⟩
    obtain ⟨σ, hσ⟩ := minpoly.exists_algEquiv_of_root' hint.isAlgebraic hy
    rw [← hσ, hx σ]
  · intro h
    rw [h]
    exact ⟨minpoly.ne_zero hint, minpoly.aeval K x⟩

private lemma fixed_pow_mem (A L : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [Field L] [Algebra A L]
    [Algebra (FractionRing A) L] [IsScalarTower A (FractionRing A) L] [FiniteDimensional (FractionRing A) L]
    [Normal (FractionRing A) L] (q : ℕ) [ExpChar (FractionRing A) q] (b : integralClosure A L)
    (hb : ∀ g : integralClosure A L ≃ₐ[A] integralClosure A L, g b = b) :
    ∃ (n : ℕ) (a : A), b ^ q ^ n = algebraMap A (integralClosure A L) a := by
  have hx : ∀ σ : L ≃ₐ[FractionRing A] L, σ (b : L) = b := fun σ => by
    have h := algebraMap_galRestrict_apply A (K := FractionRing A) (L := L)
      (B := integralClosure A L) σ b
    rw [hb] at h
    exact h.symm
  obtain ⟨n, k, hk⟩ := exists_pow_mem_of_fixed (FractionRing A) L q (b : L) hx
  have hint : IsIntegral A (algebraMap (FractionRing A) L k) := by
    rw [hk]
    exact (b ^ q ^ n).2
  have hk' : IsIntegral A k :=
    (isIntegral_algHom_iff (IsScalarTower.toAlgHom A (FractionRing A) L)
      (algebraMap (FractionRing A) L).injective).mp hint
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp hk'
  refine ⟨n, a, Subtype.ext ?_⟩
  rw [SubmonoidClass.coe_pow, ← hk, ← ha, ← IsScalarTower.algebraMap_apply]
  rfl

private lemma eq_of_fixed (A L Ω : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [Field L] [Algebra A L]
    [Algebra (FractionRing A) L] [IsScalarTower A (FractionRing A) L] [FiniteDimensional (FractionRing A) L]
    [Normal (FractionRing A) L] [Field Ω] (φ φ' : integralClosure A L →+* Ω)
    (h : φ.comp (algebraMap A _) = φ'.comp (algebraMap A _)) (b : integralClosure A L)
    (hb : ∀ g : integralClosure A L ≃ₐ[A] integralClosure A L, g b = b) : φ b = φ' b := by
  obtain ⟨q, hq⟩ := ExpChar.exists (FractionRing A)
  obtain ⟨n, a, ha⟩ := fixed_pow_mem A L q b hb
  have h1 : φ b ^ q ^ n = φ' b ^ q ^ n := by
    rw [← map_pow, ← map_pow, ha]
    exact congrArg (fun f : A →+* Ω => f a) h
  cases hq with
  | zero => simpa using h1
  | prime hp =>
    have hA : (q : A) = 0 := by
      apply IsFractionRing.injective A (FractionRing A)
      rw [map_natCast, map_zero, CharP.cast_eq_zero]
    have hΩ : (q : Ω) = 0 := by
      have := congrArg (fun f : A →+* Ω => f q) h
      simp only [RingHom.comp_apply, map_natCast] at this
      rw [← map_natCast (φ.comp (algebraMap A _)) q, hA, map_zero]
    haveI : CharP Ω q := (CharP.charP_iff_prime_eq_zero hp).mpr hΩ
    haveI : ExpChar Ω q := ExpChar.prime hp
    exact iterateFrobenius_inj Ω q n h1

theorem UpperTheory.Gal.TranscendenceTraces.galTrans_of : InvTrans → GalTrans := by
  intro hInv A L Ω _ _ _ _ _ _ _ _ _ _ φ φ' h
  let G := integralClosure A L ≃ₐ[A] integralClosure A L
  haveI : Finite G :=
    Finite.of_equiv _ (galRestrict A (FractionRing A) L (integralClosure A L)).toEquiv
  let A' := FixedPoints.subring (integralClosure A L) G
  haveI : SMulCommClass G A' (integralClosure A L) := ⟨fun g a b => by
    change g • ((a : integralClosure A L) * b) = (a : integralClosure A L) * (g • b)
    rw [smul_mul', show g • (a : integralClosure A L) = a from a.2 g]⟩
  haveI : Algebra.IsInvariant A' (integralClosure A L) G := ⟨fun b hb => ⟨⟨b, hb⟩, rfl⟩⟩
  obtain ⟨g, hg⟩ := hInv A' (integralClosure A L) G Ω φ φ' (by
    ext a
    exact eq_of_fixed A L Ω φ φ' h a fun g => a.2 g)
  exact ⟨g, hg⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PWtVanish
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.wtVanish_of :
    Isolate → WtPt → PtEx → PtLift → FibFin → WtVanish := by
  intro hIso hPt hEx hLift hFin Z S p _ w hw D hD hzero
  funext Ω _ _ z
  show w Ω z = 0
  obtain ⟨A, W, v, hEt, hW, hvW, hvz, huniq⟩ := hIso p (pt z)
  haveI : IsFinite A.r := A.finite
  classical
  let φ : A.V → ℤ := fun y => if y ∈ W then 1 else 0
  have hφ : IsLocallyConstant φ := by
    refine IsLocallyConstant.iff_isOpen_fiber.2 ?_
    intro n
    by_cases h1 : n = 1
    · subst h1
      convert hW.isOpen using 1
      ext y
      by_cases hy : y ∈ W <;> simp [φ, hy]
    · by_cases h0 : n = 0
      · subst h0
        convert hW.compl.isOpen using 1
        ext y
        by_cases hy : y ∈ W <;> simp [φ, hy]
      · convert isOpen_empty using 1
        ext y
        by_cases hy : y ∈ W <;> simp [φ, hy] <;> omega
  obtain ⟨ψ, hψ, hψeq⟩ := hw A φ hφ
  have hsum : ∀ (Ω1 : Type) [Field Ω1] [IsAlgClosed Ω1] (x1 : gp Ω1 ⟶ A.U), pt x1 = A.r v →
      ψ (A.r v) = w Ω z * ∑ᶠ z' ∈ fib A.r x1, φ (pt z') := by
    intro Ω1 _ _ x1 hx1
    rw [← hx1, hψeq Ω1 x1, mul_finsum_mem]
    apply finsum_mem_congr rfl
    intro z' hz'
    have hz'' : z' ≫ A.r = x1 := hz'
    by_cases hW' : pt z' ∈ W
    · have hr : A.r (pt z') = A.r v := by
        rw [← pt_comp, hz'']
        exact hx1
      have hv : pt z' = v := huniq _ hW' hr
      have hwz : w Ω1 (z' ≫ A.v) = w Ω z :=
        hPt p w hw Ω1 Ω (z' ≫ A.v) z (by rw [pt_comp, hv, hvz])
      simp [φ, hW', hwz]
    · simp [φ, hW']
  have hpos : ∀ (Ω1 : Type) [Field Ω1] [IsAlgClosed Ω1] (x1 : gp Ω1 ⟶ A.U), pt x1 = A.r v →
      0 < ∑ᶠ z' ∈ fib A.r x1, φ (pt z') := by
    intro Ω1 _ _ x1 hx1
    obtain ⟨z1, hz1, hpz1⟩ := hLift A.r Ω1 x1 v hx1.symm
    have hf := hFin A.r Ω1 x1
    rw [finsum_mem_eq_finite_toFinset_sum _ hf]
    have hmem : z1 ∈ hf.toFinset := by
      rw [Set.Finite.mem_toFinset]
      exact hz1
    calc (0:ℤ) < φ (pt z1) := by simp [φ, hpz1, hvW]
      _ ≤ _ := Finset.single_le_sum (f := fun z' => φ (pt z'))
          (fun i _ => by by_cases hi : pt i ∈ W <;> simp [φ, hi]) hmem
  obtain ⟨Ω0, _, _, x0, hx0⟩ := hEx A.U (A.r v)
  have hO : IsOpen (ψ ⁻¹' {ψ (A.r v)}) := hψ.isOpen_fiber _
  have hopen := A.u.isOpenMap _ hO
  obtain ⟨y, ⟨u1, hu1, rfl⟩, hyD⟩ :=
    hD.inter_open_nonempty _ hopen ⟨A.u (A.r v), A.r v, rfl, rfl⟩
  obtain ⟨Ω2, _, _, x2, hx2⟩ := hEx A.U u1
  have hψ1 : ψ u1 = 0 := by
    rw [← hx2, hψeq Ω2 x2]
    apply finsum_mem_of_eqOn_zero
    intro z' hz'
    have hz'' : z' ≫ A.r = x2 := hz'
    have hw0 : w Ω2 (z' ≫ A.v) = 0 := by
      apply hzero Ω2
      have hc : (z' ≫ A.v) ≫ p = x2 ≫ A.u := by
        rw [Category.assoc, A.pb.w, ← Category.assoc, hz'']
      rw [hc, pt_comp, hx2]
      exact hyD
    simp [hw0]
  have hu1' : ψ u1 = ψ (A.r v) := hu1
  have h1 := hsum Ω0 x0 hx0
  have h2 := hpos Ω0 x0 hx0
  rw [← hu1', hψ1] at h1
  rcases mul_eq_zero.mp h1.symm with h | h
  · exact h
  · exact absurd h h2.ne'
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PFamComp
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

noncomputable section

namespace UpperTheory.Gal.TranscendenceTraces.FamilyComposition

variable {W Z S : Scheme.{0}} (r : W ⟶ Z) (p : Z ⟶ S)

private def cr (A : Sq (r ≫ p)) : A.V ⟶ pullback p A.u :=
  pullback.lift (A.v ≫ r) A.r (by rw [Category.assoc]; exact A.pb.w)

private lemma cr_fst (A : Sq (r ≫ p)) : cr r p A ≫ pullback.fst p A.u = A.v ≫ r := pullback.lift_fst _ _ _

private lemma cr_snd (A : Sq (r ≫ p)) : cr r p A ≫ pullback.snd p A.u = A.r := pullback.lift_snd _ _ _

private abbrev sqB (A : Sq (r ≫ p)) : Sq p := Sq.of p A.u

private def sqC (A : Sq (r ≫ p)) : Sq r :=
  ⟨pullback p A.u, A.V, pullback.fst p A.u, A.v, cr r p A,
    IsPullback.of_bot (by rw [cr_snd]; exact A.pb) (cr_fst r p A).symm (IsPullback.of_hasPullback p A.u)⟩

variable {r p}

private def mid {A A' : Sq (r ≫ p)} (t : A.To A') : pullback p A.u ⟶ pullback p A'.u :=
  pullback.lift (pullback.fst p A.u) (pullback.snd p A.u ≫ t.g)
    (by rw [Category.assoc, t.hu]; exact pullback.condition)

private lemma mid_fst {A A' : Sq (r ≫ p)} (t : A.To A') : mid t ≫ pullback.fst p A'.u = pullback.fst p A.u :=
  pullback.lift_fst _ _ _

private lemma mid_snd {A A' : Sq (r ≫ p)} (t : A.To A') :
    mid t ≫ pullback.snd p A'.u = pullback.snd p A.u ≫ t.g := pullback.lift_snd _ _ _

private def toB {A A' : Sq (r ≫ p)} (t : A.To A') : (sqB r p A).To (sqB r p A') :=
  ⟨t.g, mid t, t.hu, mid_fst t, mid_snd t⟩

private def toC {A A' : Sq (r ≫ p)} (t : A.To A') : (sqC r p A).To (sqC r p A') :=
  ⟨mid t, t.k, mid_fst t, by
      have := t.hv
      exact this, by
      change t.k ≫ cr r p A' = cr r p A ≫ mid t
      apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc, cr_fst, mid_fst, cr_fst, ← Category.assoc, t.hv]
      · rw [Category.assoc, Category.assoc, cr_snd, mid_snd, ← Category.assoc, cr_snd, t.hr]⟩

variable (r p)

private def comp0 {R₁ R₂ R₃ : Type} [CommRing R₁] [CommRing R₂] [CommRing R₃] {F : Shv R₁} {G : Shv R₂} {H : Shv R₃}
    (a : Fam0 r F G) (b : Fam0 p G H) : Fam0 (r ≫ p) F H where
  app A := (b.app (sqB r p A)).comp (a.app (sqC r p A))
  nat {A A'} t x := by
    have h1 := b.nat (toB t) (a.app (sqC r p A') x)
    have h2 := a.nat (toC t) x
    exact h1.trans (congrArg (b.app (sqB r p A)) h2)

private lemma zsmul_finsum_mem {ι M : Type*} [AddCommGroup M] (d : ℤ) {s : Set ι} (f : ι → M) (hs : s.Finite) :
    d • ∑ᶠ i ∈ s, f i = ∑ᶠ i ∈ s, d • f i :=
  (zsmulAddGroupHom d).map_finsum_mem f hs

end UpperTheory.Gal.TranscendenceTraces.FamilyComposition

open UpperTheory.Gal.TranscendenceTraces.FamilyComposition in
theorem UpperTheory.Gal.TranscendenceTraces.famComp_of :
    SumComp → FibFin → FamComp := by
  intro hS hF q i W Z S r p _ _ w' w τ' τ h' h
  refine ⟨⟨fun s => comp0 r p (τ'.deg s) (τ.deg s), fun A s t a => ?_⟩, fun A a => ?_, fun n a => ?_⟩
  · exact ((τ.comm (sqB r p A) s t _).trans
      (congrArg ((τ.deg t).app (sqB r p A)) (τ'.comm (sqC r p A) s t a)))
  · obtain ⟨b1, e1, s1⟩ := h' (sqC r p A) a
    obtain ⟨b2, e2, s2⟩ := h (sqB r p A) b1
    refine ⟨b2, (congrArg ((τ.deg 0).app (sqB r p A)) e1).trans e2, ?_⟩
    intro Ω _ _ x
    haveI fB : IsFinite (pullback.snd p A.u) := Sq.finite (sqB r p A)
    haveI fC : IsFinite (cr r p A) := Sq.finite (sqC r p A)
    have key := hS (cr r p A) (pullback.snd p A.u) Ω x (Sec (tw q i) (gp Ω))
      (fun z => (Wt.mul r w' w) Ω (z ≫ A.v) • Sec.res z a)
    rw [cr_snd] at key
    refine (s2 Ω x).trans (Eq.trans ?_ key.symm)
    refine finsum_mem_congr rfl fun (y : gp Ω ⟶ pullback p A.u) _ => ?_
    have e : (Sec.res y b1 : Sec (tw q i) (gp Ω)) = ∑ᶠ z ∈ fib (cr r p A) y, w' Ω (z ≫ A.v) • Sec.res z a := s1 Ω y
    refine (congrArg (fun m => w Ω (y ≫ pullback.fst p A.u) • m) e).trans ?_
    refine (zsmul_finsum_mem _ _ (hF (cr r p A) Ω y)).trans ?_
    refine finsum_mem_congr rfl fun z hz => ?_
    have hy : (z ≫ A.v) ≫ r = y ≫ pullback.fst p A.u := by
      have hz' : z ≫ cr r p A = y := hz
      rw [← hz', Category.assoc, Category.assoc, cr_fst]
    change _ = (w' Ω (z ≫ A.v) * w Ω ((z ≫ A.v) ≫ r)) • Sec.res z a
    rw [hy, mul_comm, mul_smul]
  · let t1 : (sqB r p (Sq.self (r ≫ p))).To (Sq.self p) :=
      ⟨𝟙 S, pullback.fst p (𝟙 S), Category.comp_id _, Category.comp_id _,
        pullback.condition⟩
    let t2 : (sqC r p (Sq.self (r ≫ p))).To (Sq.self r) :=
      ⟨pullback.fst p (𝟙 S), 𝟙 W, Category.comp_id _, Category.comp_id _, by
        have := cr_fst r p (Sq.self (r ≫ p))
        exact (Eq.trans this.symm rfl : _)⟩
    have n1 := (τ.deg n).nat t1 ((τ'.deg n).app (Sq.self r) a)
    have n2 := (τ'.deg n).nat t2 a
    have e1 : (τ.deg n).app (Sq.self p) ((τ'.deg n).app (Sq.self r) a) =
        (τ.deg n).app (sqB r p (Sq.self (r ≫ p))) (Sec.res (pullback.fst p (𝟙 S)) ((τ'.deg n).app (Sq.self r) a)) :=
      (res_id _).symm.trans n1
    have e2 : Sec.res (pullback.fst p (𝟙 S)) ((τ'.deg n).app (Sq.self r) a) =
        (τ'.deg n).app (sqC r p (Sq.self (r ≫ p))) a :=
      n2.trans (congrArg _ (res_id a))
    exact (e1.trans (congrArg _ e2)).symm
end
end
