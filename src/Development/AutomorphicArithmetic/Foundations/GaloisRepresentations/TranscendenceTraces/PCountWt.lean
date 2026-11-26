module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigOfOmegaInjectiveOfEqZero

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PCountWt
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

private theorem isLC_sum {X ι : Type*} [TopologicalSpace X] (s : Finset ι) (f : ι → X → ℤ)
    (h : ∀ j, IsLocallyConstant (f j)) : IsLocallyConstant (fun t => ∑ j ∈ s, f j t) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact IsLocallyConstant.const 0
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a).add ih

private theorem key {T Z S : Scheme.{0}} {p : Z ⟶ S} {π : T ⟶ S} {ι : Type} [Fintype ι] [IsFinite p]
    (hFib : FibFin) (σ : ι → (T ⟶ Z)) (m : ι → ℤ) (w : Wt Z) (hC : Counts p π σ m w) (A : Sq p)
    (φ : A.V → ℤ) (Ω : Type) [Field Ω] [IsAlgClosed Ω] {U1 : Scheme.{0}} (f : U1 ⟶ T) (g : U1 ⟶ A.U)
    (hfg : f ≫ π = g ≫ A.u) (τ : ι → (U1 ⟶ A.V)) (hτv : ∀ j, τ j ≫ A.v = f ≫ σ j)
    (hτr : ∀ j, τ j ≫ A.r = g) (x1 : gp Ω ⟶ U1) :
    ∑ j, m j * φ (τ j (pt x1)) = ∑ᶠ z ∈ fib A.r (x1 ≫ g), w Ω (z ≫ A.v) * φ (pt z) := by
  classical
  haveI : IsFinite A.r := A.finite
  have hfin := hFib A.r Ω (x1 ≫ g)
  have hmem : ∀ j, x1 ≫ τ j ∈ fib A.r (x1 ≫ g) := fun j => by
    show (x1 ≫ τ j) ≫ A.r = x1 ≫ g
    rw [Category.assoc, hτr]
  have hiff : ∀ z ∈ fib A.r (x1 ≫ g), ∀ j, (x1 ≫ f) ≫ σ j = z ≫ A.v ↔ x1 ≫ τ j = z := by
    intro z hz j
    have hz' : z ≫ A.r = x1 ≫ g := hz
    constructor
    · intro h
      apply A.pb.hom_ext
      · rw [Category.assoc, hτv, ← Category.assoc, h]
      · rw [Category.assoc, hτr, hz']
    · intro h
      rw [← h, Category.assoc, Category.assoc, hτv]
  have hw : ∀ z ∈ fib A.r (x1 ≫ g),
      w Ω (z ≫ A.v) = ∑ j, if x1 ≫ τ j = z then m j else 0 := by
    intro z hz
    have hz' : z ≫ A.r = x1 ≫ g := hz
    have hsq : (z ≫ A.v) ≫ p = (x1 ≫ f) ≫ π := by
      rw [Category.assoc, A.pb.w, ← Category.assoc, hz', Category.assoc, ← hfg, Category.assoc]
    rw [hC Ω (x1 ≫ f) (z ≫ A.v) hsq, finsum_mem_def, finsum_eq_sum_of_fintype]
    apply Finset.sum_congr rfl
    intro j _
    by_cases h : x1 ≫ τ j = z
    · rw [Set.indicator_of_mem
        (show j ∈ {j | (x1 ≫ f) ≫ σ j = z ≫ A.v} from (hiff z hz j).mpr h) m, if_pos h]
    · rw [Set.indicator_of_notMem
        (show j ∉ {j | (x1 ≫ f) ≫ σ j = z ≫ A.v} from fun h' => h ((hiff z hz j).mp h')) m,
        if_neg h]
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
  rw [Finset.sum_congr rfl
    (g := fun z => (∑ j, if x1 ≫ τ j = z then m j else 0) * φ (pt z))
    (fun z hz => by rw [hw z (hfin.mem_toFinset.mp hz)])]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simp only [ite_mul, zero_mul]
  rw [Finset.sum_ite_eq, if_pos (hfin.mem_toFinset.mpr (hmem j)), pt_comp]

theorem UpperTheory.Gal.TranscendenceTraces.countWt_of :
    PtEx → PtLift → FibFin → CountWt := by
  intro hPE hPL hFib T Z S p π _ _ _ ι _ σ m w hσ hC
  classical
  haveI := Fintype.ofFinite ι
  intro A φ hφ
  let f : pullback π A.u ⟶ T := pullback.fst π A.u
  let g : pullback π A.u ⟶ A.U := pullback.snd π A.u
  have hfg : f ≫ π = g ≫ A.u := pullback.condition
  have hpb1 : IsPullback f g π A.u := IsPullback.of_hasPullback π A.u
  haveI : Surjective g := MorphismProperty.of_isPullback (P := @Surjective) hpb1 inferInstance
  haveI : IsIntegralHom g :=
    MorphismProperty.of_isPullback (P := @IsIntegralHom) hpb1 inferInstance
  let τ : ι → (pullback π A.u ⟶ A.V) := fun j =>
    A.pb.lift (f ≫ σ j) g (by rw [Category.assoc, hσ j, hfg])
  have hτv : ∀ j, τ j ≫ A.v = f ≫ σ j := fun j => A.pb.lift_fst _ _ _
  have hτr : ∀ j, τ j ≫ A.r = g := fun j => A.pb.lift_snd _ _ _
  let χ : ↥(pullback π A.u) → ℤ := fun t => ∑ j, m j * φ (τ j t)
  have hχ : IsLocallyConstant χ :=
    isLC_sum Finset.univ (fun j t => m j * φ (τ j t))
      (fun j => (hφ.comp_continuous (τ j).continuous).comp (fun a => m j * a))
  have hconst : ∀ t1 t2, g t1 = g t2 → χ t1 = χ t2 := by
    intro t1 t2 h
    obtain ⟨Ω, hF, hA, x1, hx1⟩ := hPE _ t1
    letI := hF
    haveI := hA
    obtain ⟨z, hz, hzt⟩ := hPL g Ω (x1 ≫ g) t2 (by rw [pt_comp, hx1, h])
    have k1 := key hFib σ m w hC A φ Ω f g hfg τ hτv hτr x1
    have k2 := key hFib σ m w hC A φ Ω f g hfg τ hτv hτr z
    rw [hz] at k2
    show ∑ j, m j * φ (τ j t1) = ∑ j, m j * φ (τ j t2)
    rw [← hx1, ← hzt, k1, k2]
  have hsurj : Function.Surjective g := g.surjective
  let ψ : A.U → ℤ := fun s => χ (Function.surjInv hsurj s)
  have hψg : ∀ t, ψ (g t) = χ t := fun t => hconst _ _ (Function.surjInv_eq hsurj _)
  refine ⟨ψ, ?_, ?_⟩
  · have hq : Topology.IsQuotientMap g := g.isClosedMap.isQuotientMap g.continuous hsurj
    intro s
    rw [← hq.isOpen_preimage]
    have hpre : g ⁻¹' (ψ ⁻¹' s) = χ ⁻¹' s := by
      ext t
      simp only [Set.mem_preimage, hψg]
    rw [hpre]
    exact hχ s
  · intro Ω _ _ x
    obtain ⟨t, ht⟩ := hsurj (pt x)
    obtain ⟨z, hz, _⟩ := hPL g Ω x t ht
    rw [← hz, pt_comp, hψg]
    exact key hFib σ m w hC A φ Ω f g hfg τ hτv hτr z
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PSumEx
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.RingSec
theorem UpperTheory.Reformulated.B.Qh66.ring_sec :
    ∀ (Ω C : Type) [inst : Field Ω] [IsAlgClosed Ω]
    [inst_2 : CommRing C] [Nontrivial C] (φ : Ω →+* C), φ.FiniteType → ∃ (ρ : C →+* Ω), ρ.comp φ = RingHom.id Ω := by
  intro Ω C _ _ _ _ φ hφ
  letI : Algebra Ω C := φ.toAlgebra
  haveI : Algebra.FiniteType Ω C := hφ
  obtain ⟨m, hm⟩ := Ideal.exists_maximal C
  letI : Field (C ⧸ m) := Ideal.Quotient.field m
  haveI : Module.Finite Ω (C ⧸ m) := finite_of_finite_type_of_isJacobsonRing Ω (C ⧸ m)
  let f : (C ⧸ m) →ₐ[Ω] Ω := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨(f.comp (Ideal.Quotient.mkₐ Ω m)).toRingHom, ?_⟩
  ext x
  exact (f.comp (Ideal.Quotient.mkₐ Ω m)).commutes x
end

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

private theorem ring_sec (Ω C : Type) [Field Ω] [IsAlgClosed Ω] [CommRing C] [Nontrivial C] (φ : Ω →+* C)
    (h : φ.FiniteType) : ∃ ρ : C →+* Ω, ρ.comp φ = RingHom.id Ω :=
  _root_.UpperTheory.Reformulated.B.Qh66.ring_sec Ω C φ h

private theorem etale_sec (Ω : Type) [Field Ω] [IsAlgClosed Ω] {V : Scheme.{0}} [IsAffine V] (g : V ⟶ gp Ω) [Etale g]
    [Nonempty V] : ∃ σ : gp Ω ⟶ V, σ ≫ g = 𝟙 _ := by
  have hl : LocallyOfFiniteType g := inferInstance
  have hft : g.appTop.hom.FiniteType := (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)).mp hl
  let e := Scheme.ΓSpecIso (CommRingCat.of Ω)
  haveI : Nontrivial Γ(V, ⊤) := by
    haveI : Nonempty (⊤ : V.Opens) := ⟨⟨Classical.arbitrary V, trivial⟩⟩
    exact Scheme.component_nontrivial V ⊤
  have hft' : (e.inv ≫ g.appTop).hom.FiniteType := by
    rw [CommRingCat.hom_comp]
    exact RingHom.FiniteType.comp hft (RingHom.FiniteType.of_surjective _ (ConcreteCategory.bijective_of_isIso e.inv).2)
  obtain ⟨ρ, hρ⟩ := ring_sec Ω Γ(V, ⊤) (e.inv ≫ g.appTop).hom hft'
  refine ⟨Spec.map (CommRingCat.ofHom ρ) ≫ V.isoSpec.inv, ?_⟩
  have he : (gp Ω).isoSpec.hom ≫ Spec.map e.inv = 𝟙 _ := by
    rw [Scheme.isoSpec_Spec_hom, ← Spec.map_comp]
    simp [e]
  have h1 : g = V.isoSpec.hom ≫ Spec.map (e.inv ≫ g.appTop) := by
    rw [Spec.map_comp, ← Category.assoc, Scheme.isoSpec_hom_naturality, Category.assoc, he, Category.comp_id]
  have h2 : (e.inv ≫ g.appTop) ≫ CommRingCat.ofHom ρ = 𝟙 _ := CommRingCat.hom_ext hρ
  calc (Spec.map (CommRingCat.ofHom ρ) ≫ V.isoSpec.inv) ≫ g
      = (Spec.map (CommRingCat.ofHom ρ) ≫ V.isoSpec.inv) ≫ V.isoSpec.hom ≫ Spec.map (e.inv ≫ g.appTop) := by rw [← h1]
    _ = Spec.map (CommRingCat.ofHom ρ) ≫ Spec.map (e.inv ≫ g.appTop) := by simp
    _ = Spec.map ((e.inv ≫ g.appTop) ≫ CommRingCat.ofHom ρ) := (Spec.map_comp _ _).symm
    _ = 𝟙 _ := by rw [h2, Spec.map_id]

private theorem loc_gp (Ω : Type) [Field Ω] [IsAlgClosed Ω] (P : ∀ V : Scheme.{0}, (V ⟶ gp Ω) → Prop)
    (hP : ∀ (V W : Scheme.{0}) (g : V ⟶ gp Ω) (k : W ⟶ V), P V g → P W (k ≫ g)) (h : Loc (gp Ω) P) : P (gp Ω) (𝟙 _) := by
  obtain ⟨V, g, hV, hg, ⟨v, -⟩, hPg⟩ := (GlobalTheory.T.etaleLocally_iff_affine_etale_point_cover (gp Ω) P hP).1 h (IsLocalRing.closedPoint Ω)
  haveI : Nonempty V := ⟨v⟩
  obtain ⟨σ, hσ⟩ := etale_sec Ω g
  simpa [hσ] using hP _ _ g σ hPg

@[reducible] private noncomputable def bcSq {Z S : Scheme.{0}} {p : Z ⟶ S} (A : Sq p) {V : Scheme.{0}} (g : V ⟶ A.U) : Sq p :=
  ⟨V, pullback A.r g, g ≫ A.u, pullback.fst A.r g ≫ A.v, pullback.snd A.r g,
    (IsPullback.of_hasPullback A.r g).paste_horiz A.pb⟩

theorem UpperTheory.Gal.TranscendenceTraces.sumEx_of :
    SumExLoc → SumNat → PtInj → SumEx := by
  intro hLoc hNat hInj q _ i Z S p _ w hw hq A a
  have hqU : IsUnit (q : Γ(A.U, ⊤)) := by
    simpa using hq.map A.u.appTop.hom
  obtain ⟨T, hT, hTp⟩ := (GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity q A.U).1 hqU
  have hex : ∀ (V : Scheme.{0}) (g : V ⟶ A.U), T.arrows g →
      ∃ b : Sec (tw q i) V, IsSum w (bcSq A g) (Sec.res (pullback.fst A.r g) a) b :=
    fun V g hg => hLoc q i p w hw (bcSq A g) (hTp V g hg) _
  have huniq : ∀ (B : Sq p) (a' : Sec (tw q i) B.V) (b b' : Sec (tw q i) B.U), IsSum w B a' b → IsSum w B a' b' → b = b' :=
    fun B a' b b' h h' => hInj q i B.U b b' fun Ω _ _ x => (h Ω x).trans (h' Ω x).symm
  let s : ∀ (V : Scheme.{0}) (g : V ⟶ A.U), T.arrows g → Sec (tw q i) V := fun V g hg => (hex V g hg).choose
  have hs : ∀ (V : Scheme.{0}) (g : V ⟶ A.U) (hg : T.arrows g),
      IsSum w (bcSq A g) (Sec.res (pullback.fst A.r g) a) (s V g hg) := fun V g hg => (hex V g hg).choose_spec
  have hcomp : ∀ (V W : Scheme.{0}) (g : V ⟶ A.U) (k : W ⟶ V) (hg : T.arrows g),
      Sec.res k (s V g hg) = s W (k ≫ g) (T.downward_closed hg k) := by
    intro V W g k hg
    obtain ⟨L, hLf, hLs⟩ : ∃ L : pullback A.r (k ≫ g) ⟶ pullback A.r g,
        L ≫ pullback.fst A.r g = pullback.fst A.r (k ≫ g) ∧ L ≫ pullback.snd A.r g = pullback.snd A.r (k ≫ g) ≫ k :=
      ⟨pullback.lift (pullback.fst A.r (k ≫ g)) (pullback.snd A.r (k ≫ g) ≫ k)
        (by rw [pullback.condition, Category.assoc]), pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
    let t : (bcSq A (k ≫ g)).To (bcSq A g) :=
      { g := k
        k := L
        hu := by simp
        hv := by
          change L ≫ pullback.fst A.r g ≫ A.v = pullback.fst A.r (k ≫ g) ≫ A.v
          rw [← Category.assoc, hLf]
        hr := hLs }
    have h1 := hNat (ZMod q) (tw q i) w t _ _ (hs V g hg)
    have h2 : Sec.res t.k (Sec.res (pullback.fst A.r g) a) = Sec.res (pullback.fst A.r (k ≫ g)) a := by
      rw [res_res]
      change Sec.res (L ≫ pullback.fst A.r g) a = _
      rw [hLf]
    rw [h2] at h1
    exact huniq _ _ _ _ h1 (hs W (k ≫ g) (T.downward_closed hg k))
  obtain ⟨b, hb⟩ := (GlobalTheory.T.etaleSheafSections_ext_and_glue (ZMod q) (tw q i) A.U).2 T hT s hcomp
  refine ⟨b, fun Ω _ _ x => ?_⟩
  have hx : T.arrows x := by
    have hl : Loc (gp Ω) fun V g => T.arrows (g ≫ x) :=
      GlobalTheory.T.etaleLocal_property_calculus_rules.2.2.2.1 A.U (gp Ω) x (fun V g => T.arrows g) ⟨T, hT, fun _ _ h => h⟩
    have h0 := loc_gp Ω (fun V g => T.arrows (g ≫ x))
      (fun V W g k h => by simpa using T.downward_closed h k) hl
    simpa using h0
  have h1 := (res_id _).symm.trans (hs _ x hx Ω (𝟙 _))
  rw [hb _ x hx, h1]
  have hbij := fib_bijOn (IsPullback.of_hasPullback A.r x) (𝟙 (gp Ω))
  rw [Category.id_comp] at hbij
  refine finsum_mem_eq_of_bijOn _ hbij fun z hz => ?_
  change w Ω (z ≫ pullback.fst A.r x ≫ A.v) • Sec.res z (Sec.res (pullback.fst A.r x) a) =
    w Ω ((z ≫ pullback.fst A.r x) ≫ A.v) • Sec.res (z ≫ pullback.fst A.r x) a
  rw [res_res, Category.assoc]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PInvTrans
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.RootOrbit
theorem UpperTheory.Reformulated.B.Qi49.root_orbit :
    ∀ {A B G Ω : Type} [inst : CommRing A]
    [inst_1 : CommRing B] [inst_2 : Algebra A B] [inst_3 : Group G] [Finite G] [inst_5 : MulSemiringAction G B]
    [SMulCommClass G A B] [Algebra.IsInvariant A B G] [inst_8 : Field Ω] (φ ψ : B →+* Ω),
    φ.comp (Algebra.algebraMap A B) = ψ.comp (Algebra.algebraMap A B) →
      ∀ (b : B), ∃ (g : G), (ψ : B → Ω) b = (φ : B → Ω) (g • b) := by
  intro A B G Ω _ _ _ _ _ _ _ _ _ φ ψ h b
  classical
  cases nonempty_fintype G
  obtain ⟨p, hp⟩ := (Polynomial.mem_lifts _).1 (Algebra.IsInvariant.charpoly_mem_lifts A B G b)
  have hmap : (MulSemiringAction.charpoly G b).map φ = (MulSemiringAction.charpoly G b).map ψ := by
    rw [← hp, Polynomial.map_map, Polynomial.map_map, h]
  have hroot : ((MulSemiringAction.charpoly G b).map ψ).eval (ψ b) = 0 := by
    rw [Polynomial.eval_map, Polynomial.eval₂_at_apply, MulSemiringAction.eval_charpoly, map_zero]
  rw [← hmap, MulSemiringAction.charpoly_eq, Polynomial.map_prod, Polynomial.eval_prod,
    Finset.prod_eq_zero_iff] at hroot
  obtain ⟨g, -, hg⟩ := hroot
  refine ⟨g, ?_⟩
  simpa [sub_eq_zero] using hg
end

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

namespace UpperTheory.Gal.TranscendenceTraces

private theorem root_orbit {A B G Ω : Type} [CommRing A] [CommRing B] [Algebra A B] [Group G] [Finite G]
    [MulSemiringAction G B] [SMulCommClass G A B] [Algebra.IsInvariant A B G] [Field Ω] (φ ψ : B →+* Ω)
    (h : φ.comp (algebraMap A B) = ψ.comp (algebraMap A B)) (b : B) : ∃ g : G, ψ b = φ (g • b) :=
  _root_.UpperTheory.Reformulated.B.Qi49.root_orbit φ ψ h b

private theorem same_ker {A B G Ω : Type} [CommRing A] [CommRing B] [Algebra A B] [Group G] [Finite G]
    [MulSemiringAction G B] [SMulCommClass G A B] [Algebra.IsInvariant A B G] [Field Ω] (φ ψ : B →+* Ω)
    (h : φ.comp (algebraMap A B) = ψ.comp (algebraMap A B)) (hk : RingHom.ker φ = RingHom.ker ψ) :
    ∃ g : G, ∀ b, ψ b = φ (g • b) := by
  let Q : Ideal B := RingHom.ker φ
  haveI : Q.IsPrime := RingHom.ker_isPrime φ
  let P : Ideal A := Q.under A
  haveI : Q.LiesOver P := ⟨rfl⟩
  let φb : B ⧸ Q →+* Ω := Ideal.Quotient.lift Q φ (fun a ha => ha)
  let ψb : B ⧸ Q →+* Ω := Ideal.Quotient.lift Q ψ (fun a ha => by
    have : a ∈ RingHom.ker ψ := hk ▸ ha
    exact this)
  have φm : ∀ b, φb (Ideal.Quotient.mk Q b) = φ b := fun b => Ideal.Quotient.lift_mk _ _ _
  have ψm : ∀ b, ψb (Ideal.Quotient.mk Q b) = ψ b := fun b => Ideal.Quotient.lift_mk _ _ _
  have inj : ∀ f : B ⧸ Q →+* Ω, (∀ b, f (Ideal.Quotient.mk Q b) = 0 → b ∈ Q) → Function.Injective f := by
    intro f hf
    refine (injective_iff_map_eq_zero f).2 fun x hx => ?_
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact Ideal.Quotient.eq_zero_iff_mem.2 (hf b hx)
  have φi : Function.Injective φb := inj φb fun b hb => by
    rw [φm] at hb
    exact hb
  have ψi : Function.Injective ψb := inj ψb fun b hb => by
    rw [ψm] at hb
    have h' : b ∈ RingHom.ker ψ := hb
    rw [← hk] at h'
    exact h'
  have hr : ψb.range = φb.range := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨g, hg⟩ := root_orbit (G := G) φ ψ h b
      exact ⟨Ideal.Quotient.mk Q (g • b), by rw [φm, ψm, hg]⟩
    · rintro ⟨x, rfl⟩
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨g, hg⟩ := root_orbit (G := G) ψ φ h.symm b
      exact ⟨Ideal.Quotient.mk Q (g • b), by rw [φm, ψm, hg]⟩
  let eφ : B ⧸ Q ≃+* φb.range := RingEquiv.ofBijective φb.rangeRestrict
    ⟨fun x y e => φi (congrArg Subtype.val e), φb.rangeRestrict_surjective⟩
  let eψ : B ⧸ Q ≃+* ψb.range := RingEquiv.ofBijective ψb.rangeRestrict
    ⟨fun x y e => ψi (congrArg Subtype.val e), ψb.rangeRestrict_surjective⟩
  let τ0 : B ⧸ Q ≃+* B ⧸ Q := (eψ.trans (RingEquiv.subringCongr hr)).trans eφ.symm
  have hτ : ∀ x, φb (τ0 x) = ψb x := by
    intro x
    have e : eφ (τ0 x) = RingEquiv.subringCongr hr (eψ x) := eφ.apply_symm_apply _
    exact congrArg Subtype.val e
  let τ : (B ⧸ Q) ≃ₐ[A ⧸ P] (B ⧸ Q) := AlgEquiv.ofRingEquiv (f := τ0) (fun a => by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    apply φi
    rw [hτ]
    change ψb (Ideal.Quotient.mk Q (algebraMap A B a)) = φb (Ideal.Quotient.mk Q (algebraMap A B a))
    rw [φm, ψm]
    exact (congrArg (fun f => f a) h).symm)
  obtain ⟨g, hg⟩ := Ideal.Quotient.stabilizerHom_surjective G P Q τ
  refine ⟨g.1, fun b => ?_⟩
  have e1 : Ideal.Quotient.stabilizerHom Q P G g (Ideal.Quotient.mk Q b) = Ideal.Quotient.mk Q (g.1 • b) :=
    Ideal.Quotient.stabilizerHom_apply Q P G g b
  rw [hg] at e1
  have e2 := hτ (Ideal.Quotient.mk Q b)
  rw [ψm] at e2
  rw [← e2, ← φm]
  exact congrArg φb e1

end UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.invTrans_of :
    InvTrans := by
  intro A B G Ω _ _ _ _ _ _ _ _ _ φ φ' h
  haveI : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
  haveI : (RingHom.ker φ').IsPrime := RingHom.ker_isPrime φ'
  have hu : (RingHom.ker φ).under A = (RingHom.ker φ').under A := by
    ext a
    change φ (algebraMap A B a) = 0 ↔ φ' (algebraMap A B a) = 0
    rw [show φ (algebraMap A B a) = φ' (algebraMap A B a) from congrArg (fun f => f a) h]
  obtain ⟨g0, hg0⟩ := Algebra.IsInvariant.exists_smul_of_under_eq A B G _ _ hu
  let ψ : B →+* Ω := φ'.comp (MulSemiringAction.toRingHom G B g0)
  have hψ : ∀ b, ψ b = φ' (g0 • b) := fun _ => rfl
  have hk : RingHom.ker φ = RingHom.ker ψ := by
    ext b
    have e : g0 • b ∈ RingHom.ker φ' ↔ b ∈ RingHom.ker φ := by
      rw [hg0]
      exact Ideal.smul_mem_pointwise_smul_iff
    rw [← e, RingHom.mem_ker, RingHom.mem_ker, hψ]
  have hA : φ.comp (algebraMap A B) = ψ.comp (algebraMap A B) := by
    ext a
    have e : φ (algebraMap A B a) = φ' (algebraMap A B a) := congrArg (fun f => f a) h
    simp [hψ, e, smul_algebraMap]
  obtain ⟨g, hg⟩ := same_ker (G := G) φ ψ hA hk
  refine ⟨g * g0⁻¹, fun b => ?_⟩
  have e := hg (g0⁻¹ • b)
  rw [hψ, smul_inv_smul, ← mul_smul] at e
  exact e
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PSplitField
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SplittingFieldConstruction
open Polynomial

noncomputable def UpperTheory.Reformulated.B.SplittingFieldConstruction.SplitField :
    Prop :=
    ∀ (A B : Type) [inst : CommRing A] [inst_1 : IsDomain A] [inst_2 : CommRing B] [inst_3 : Algebra A B]
      [Module.Finite A B],
      ∃ (L : Type) (x : Field L) (x_1 : Algebra A L) (x_2 : Algebra (FractionRing A) L) (_ :
        IsScalarTower A (FractionRing A) L),
        FiniteDimensional (FractionRing A) L ∧
          Normal (FractionRing A) L ∧
            Finite (B →ₐ[A] ↥(integralClosure A L)) ∧
              ∀ (Ω : Type) [inst_5 : Field Ω] (φ : ↥(integralClosure A L) →+* Ω) (z : B →+* Ω),
                Function.Injective (⇑(φ.comp (Algebra.algebraMap A ↥(integralClosure A L))) : A → Ω) →
                  z.comp (Algebra.algebraMap A B) = φ.comp (Algebra.algebraMap A ↥(integralClosure A L)) →
                    ∃! σ : B →ₐ[A] ↥(integralClosure A L), φ.comp (↑σ : B →+* ↥(integralClosure A L)) = z

private theorem UpperTheory.Reformulated.B.SplittingFieldConstruction.exists_monic {A B : Type} [CommRing A] [CommRing B]
    [Algebra A B] [Module.Finite A B] (s : Finset B) :
    ∃ p : A[X], p.Monic ∧ ∀ b ∈ s, aeval b p = 0 := by
  have h : ∀ b : B, ∃ q : A[X], q.Monic ∧ aeval b q = 0 := fun b =>
    (Algebra.IsIntegral.isIntegral (R := A) b)
  choose q hq hq0 using h
  refine ⟨∏ b ∈ s, q b, monic_prod_of_monic _ _ fun b _ => hq b, fun b hb => ?_⟩
  rw [map_prod]
  exact Finset.prod_eq_zero hb (hq0 b)

private theorem UpperTheory.Reformulated.B.SplittingFieldConstruction.finite_algHom {A B C : Type} [CommRing A] [CommRing B]
    [CommRing C] [IsDomain C] [Algebra A B] [Algebra A C] (s : Finset B)
    (hs : Submodule.span A (s : Set B) = ⊤) (p : A[X]) (hp : p.Monic)
    (h0 : ∀ b ∈ s, aeval b p = 0) : Finite (B →ₐ[A] C) := by
  let f : (B →ₐ[A] C) → (s → p.rootSet C) := fun σ b =>
    ⟨σ b, by
      rw [hp.mem_rootSet, aeval_algHom_apply, h0 b b.2, map_zero]⟩
  refine Finite.of_injective f fun σ τ h => ?_
  apply AlgHom.toLinearMap_injective
  refine LinearMap.ext_on hs fun b hb => ?_
  exact congrArg Subtype.val (congrFun h ⟨b, hb⟩)

private theorem UpperTheory.Reformulated.B.SplittingFieldConstruction.factor {A B C Ω : Type} [CommRing A] [Nontrivial A] [CommRing B]
    [CommRing C] [IsDomain C] [Algebra A B] [Algebra A C] [Algebra.IsIntegral A C] [Field Ω]
    (s : Finset B) (hs : Submodule.span A (s : Set B) = ⊤) (p : A[X]) (hp : p.Monic)
    (h0 : ∀ b ∈ s, aeval b p = 0) (hsp : (p.map (algebraMap A C)).Splits)
    (φ : C →+* Ω) (z : B →+* Ω) (hinj : Function.Injective (φ.comp (algebraMap A C)))
    (hz : z.comp (algebraMap A B) = φ.comp (algebraMap A C)) :
    ∃! σ : B →ₐ[A] C, φ.comp (σ : B →+* C) = z := by
  have hφ : Function.Injective φ := by
    rw [RingHom.injective_iff_ker_eq_bot]
    apply Ideal.eq_bot_of_comap_eq_bot (R := A)
    rw [Ideal.under_def, RingHom.comap_ker]
    exact (RingHom.injective_iff_ker_eq_bot _).1 hinj
  have hzA : ∀ a : A, z (algebraMap A B a) = φ (algebraMap A C a) := fun a =>
    DFunLike.congr_fun hz a
  have hgen : ∀ b ∈ s, z b ∈ φ.range := by
    intro b hb
    have h1 : eval (z b) ((p.map (algebraMap A C)).map φ) = 0 := by
      rw [Polynomial.map_map, ← hz, eval_map, ← hom_eval₂, ← aeval_def, h0 b hb, map_zero]
    rw [hsp.eq_prod_roots_of_monic (hp.map _), Polynomial.map_multiset_prod,
      eval_multiset_prod, Multiset.prod_eq_zero_iff] at h1
    simp only [Multiset.map_map, Multiset.mem_map, Function.comp_apply, Polynomial.map_sub,
      map_X, map_C, eval_sub, eval_X, eval_C] at h1
    obtain ⟨c, -, hc⟩ := h1
    exact ⟨c, (sub_eq_zero.1 hc).symm⟩
  have hall : ∀ b : B, z b ∈ φ.range := by
    intro b
    have hb : b ∈ Submodule.span A (s : Set B) := hs ▸ Submodule.mem_top
    induction hb using Submodule.span_induction with
    | mem x hx => exact hgen x hx
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a x _ hx =>
      rw [Algebra.smul_def, map_mul, hzA]
      exact mul_mem ⟨_, rfl⟩ hx
  choose g hg using hall
  let σ : B →ₐ[A] C :=
    { toFun := g
      map_one' := hφ (by rw [hg, map_one, map_one])
      map_mul' := fun x y => hφ (by rw [map_mul φ, hg, hg, hg, map_mul])
      map_zero' := hφ (by rw [hg, map_zero, map_zero])
      map_add' := fun x y => hφ (by rw [map_add φ, hg, hg, hg, map_add (f := _)])
      commutes' := fun a => hφ (by rw [hg, hzA]) }
  refine ⟨σ, RingHom.ext fun b => hg b, fun τ hτ => AlgHom.ext fun b => hφ ?_⟩
  exact (DFunLike.congr_fun hτ b).trans (hg b).symm

private theorem UpperTheory.Reformulated.B.SplittingFieldConstruction.splits_closure {A L : Type} [CommRing A] [Field L]
    [Algebra A L] (p : A[X]) (hp : p.Monic) (hsp : (p.map (algebraMap A L)).Splits) :
    (p.map (algebraMap A (integralClosure A L))).Splits := by
  have hm : (p.map (algebraMap A (integralClosure A L))).map
      (algebraMap (integralClosure A L) L) = p.map (algebraMap A L) := by
    rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq]
  refine Splits.of_splits_map_of_injective (i := algebraMap (integralClosure A L) L)
    Subtype.val_injective (hm ▸ hsp) fun a ha => ?_
  rw [hm] at ha
  have h1 := isRoot_of_mem_roots ha
  rw [IsRoot.def, eval_map] at h1
  exact ⟨⟨a, p, hp, h1⟩, rfl⟩

theorem UpperTheory.Reformulated.B.SplittingFieldConstruction.splitField_of :
    UpperTheory.Reformulated.B.SplittingFieldConstruction.SplitField := by
  intro A B _ _ _ _ _
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := A) (M := B)
  obtain ⟨p, hp, h0⟩ := UpperTheory.Reformulated.B.SplittingFieldConstruction.exists_monic (A := A) s
  let q : (FractionRing A)[X] := p.map (algebraMap A (FractionRing A))
  let L : Type := q.SplittingField
  letI iK : Algebra (FractionRing A) L := inferInstance
  letI iA : Algebra A L :=
    ((algebraMap (FractionRing A) L).comp (algebraMap A (FractionRing A))).toAlgebra
  haveI iT : @IsScalarTower A (FractionRing A) L Algebra.toSMul iK.toSMul iA.toSMul :=
    IsScalarTower.of_algebraMap_eq' rfl
  have hsp : (p.map (algebraMap A L)).Splits := by
    rw [IsScalarTower.algebraMap_eq A (FractionRing A) L, ← Polynomial.map_map]
    exact SplittingField.splits q
  refine ⟨L, inferInstance, iA, iK, iT, inferInstance, inferInstance,
    UpperTheory.Reformulated.B.SplittingFieldConstruction.finite_algHom s hs p hp h0, ?_⟩
  intro Ω _ φ z hinj hz
  exact UpperTheory.Reformulated.B.SplittingFieldConstruction.factor s hs p hp h0
    (UpperTheory.Reformulated.B.SplittingFieldConstruction.splits_closure p hp hsp) φ z hinj hz
end

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.splitField_of :
    SplitField :=
  _root_.UpperTheory.Reformulated.B.SplittingFieldConstruction.splitField_of
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PTrSplitQ
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

private theorem pullHQ_id' (l : ℕ) [Fact l.Prime] (E : Spc) (n i : ℤ) :
    pullHQ l (𝟙 E) n i = LinearMap.id := by
  unfold pullHQ
  rw [pullHl_id, LinearMap.baseChange_id]

private theorem pullHQ_comp' (l : ℕ) [Fact l.Prime] {E E' E'' : Spc} (f : E ⟶ E') (g : E' ⟶ E'') (n i : ℤ) :
    pullHQ l (f ≫ g) n i = (pullHQ l f n i) ∘ₗ (pullHQ l g n i) := by
  unfold pullHQ
  rw [pullHl_comp, LinearMap.baseChange_comp]

private theorem existsUnique_sec {U P : Scheme.{0}} (p' : P ⟶ U) {m : ℕ} (s' : Fin m → (U ⟶ P))
    (hs : ∀ j, s' j ≫ p' = 𝟙 U) (hiso : IsIso (Sigma.desc s' : ∐ (fun _ : Fin m => U) ⟶ P))
    {Ω : Type} [Field Ω] (x0 : gp Ω ⟶ U) (y : gp Ω ⟶ P) (hy : y ≫ p' = x0) :
    ∃! j, x0 ≫ s' j = y := by
  have hι : ∀ j, Sigma.ι (fun _ : Fin m => U) j ≫ Sigma.desc s' = s' j := fun j => Sigma.ι_desc _ _
  let t : gp Ω ⟶ ∐ (fun _ : Fin m => U) := y ≫ inv (Sigma.desc s')
  obtain ⟨⟨j, u⟩, hu⟩ := (sigmaMk (fun _ : Fin m => U)).surjective (pt t)
  rw [sigmaMk_mk] at hu
  have hr : Set.range t ⊆ Set.range (Sigma.ι (fun _ : Fin m => U) j) := by
    rintro _ ⟨a, rfl⟩
    exact ⟨u, by rw [hu, pt_eq]⟩
  let t' := IsOpenImmersion.lift (Sigma.ι (fun _ : Fin m => U) j) t hr
  have ht' : t' ≫ Sigma.ι (fun _ : Fin m => U) j = t := IsOpenImmersion.lift_fac _ _ _
  have h1 : t' ≫ s' j = y := by
    rw [← hι j, ← Category.assoc, ht']
    simp [t]
  have h2 : t' = x0 := by
    rw [← hy, ← h1, Category.assoc, hs j, Category.comp_id]
  refine ⟨j, by rw [← h2]; exact h1, fun k hk => ?_⟩
  have h3 : (x0 ≫ Sigma.ι (fun _ : Fin m => U) k) ≫ Sigma.desc s' =
      (x0 ≫ Sigma.ι (fun _ : Fin m => U) j) ≫ Sigma.desc s' := by
    rw [Category.assoc, Category.assoc, hι, hι, hk, ← h2, h1]
  have h4 := (cancel_mono (Sigma.desc s')).1 h3
  have h5 : Sigma.ι (fun _ : Fin m => U) k (pt x0) = Sigma.ι (fun _ : Fin m => U) j (pt x0) := by
    rw [← pt_comp, ← pt_comp, h4]
  exact congrArg Sigma.fst ((sigmaι_eq_iff _ k j _ _).1 h5)

private theorem finsum_one_singleton {T : Type*} (A : Set T) (a : T) (h : A = {a}) :
    ∑ᶠ z ∈ A, (1 : ℤ) = 1 := by
  subst h
  simp

private theorem finsum_one_empty {T : Type*} (A : Set T) (h : A = ∅) :
    ∑ᶠ z ∈ A, (1 : ℤ) = 0 := by
  subst h
  simp

private theorem tr_split (hCorr : CorrEqQ) (hId : TrIdQ) (l : ℕ) [Fact l.Prime] (n i : ℤ) {U P : Scheme.{0}}
    (p' : P ⟶ U) [IsFinite p'] (wt : IsWt p' (Wt.const P 1)) (wt1 : IsWt (𝟙 U) (Wt.const U 1))
    (hl : IsUnit (l : Γ(U, ⊤))) {m : ℕ} (s' : Fin m → (U ⟶ P)) (hs : ∀ j, s' j ≫ p' = 𝟙 U)
    (hiso : IsIso (Sigma.desc s' : ∐ (fun _ : Fin m => U) ⟶ P)) :
    trHQ l p' (Wt.const P 1) n i = ∑ j, pullHQ l (sch.map (s' j)) n i := by
  classical
  let c : Option (Fin m) → Corr U P := fun o => match o with
    | none => ⟨P, p', 𝟙 P, Wt.const P 1, inferInstance, wt⟩
    | some j => ⟨U, 𝟙 U, s' j, Wt.const U 1, inferInstance, wt1⟩
  let mm : Option (Fin m) → ℤ := fun o => match o with
    | none => 1
    | some _ => -1
  have hcn : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x0 : gp Ω ⟶ U) (y : gp Ω ⟶ P),
      (c none).cyc Ω x0 y = if y ≫ p' = x0 then 1 else 0 := by
    intro Ω _ _ x0 y
    split_ifs with h
    · refine finsum_one_singleton _ y ?_
      ext z
      simp only [c, Set.mem_setOf_eq, Set.mem_singleton_iff, Category.comp_id]
      exact ⟨fun hz => hz.2, fun hz => ⟨hz ▸ h, hz⟩⟩
    · refine finsum_one_empty _ ?_
      ext z
      simp only [c, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, Category.comp_id]
      rintro ⟨h1, rfl⟩
      exact h h1
  have hcs : ∀ (j : Fin m) (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x0 : gp Ω ⟶ U) (y : gp Ω ⟶ P),
      (c (some j)).cyc Ω x0 y = if x0 ≫ s' j = y then 1 else 0 := by
    intro j Ω _ _ x0 y
    split_ifs with h
    · refine finsum_one_singleton _ x0 ?_
      ext z
      simp only [c, Set.mem_setOf_eq, Set.mem_singleton_iff, Category.comp_id]
      exact ⟨fun hz => hz.1, fun hz => ⟨hz, hz ▸ h⟩⟩
    · refine finsum_one_empty _ ?_
      ext z
      simp only [c, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, Category.comp_id]
      rintro ⟨rfl, h1⟩
      exact h h1
  have key := hCorr l n i (𝟙 U) p' (Option (Fin m)) c mm
    (fun a => by cases a with
      | none => simp [c]
      | some j => simp [c, hs j]) hl Set.univ dense_univ
    (fun Ω _ _ x0 y _ => by
      rw [Fintype.sum_option]
      simp only [hcn, hcs, mm]
      by_cases hy : y ≫ p' = x0
      · obtain ⟨j, hj, hu⟩ := existsUnique_sec p' s' hs hiso x0 y hy
        rw [if_pos hy, Finset.sum_eq_single j]
        · simp [hj]
        · intro k _ hk
          rw [if_neg (fun e => hk (hu k e))]
          simp
        · simp
      · rw [if_neg hy]
        simp only [mul_zero, zero_add]
        refine Finset.sum_eq_zero fun j _ => ?_
        rw [if_neg]
        · simp
        · intro e
          apply hy
          rw [← e, Category.assoc, hs j, Category.comp_id])
  rw [Fintype.sum_option] at key
  have e0 : (c none).opQ l n i = trHQ l p' (Wt.const P 1) n i := by
    change trHQ l p' (Wt.const P 1) n i ∘ₗ pullHQ l (sch.map (𝟙 P)) n i = _
    rw [CategoryTheory.Functor.map_id, pullHQ_id', LinearMap.comp_id]
  have e1 : ∀ j, (c (some j)).opQ l n i = pullHQ l (sch.map (s' j)) n i := by
    intro j
    change trHQ l (𝟙 U) (Wt.const U 1) n i ∘ₗ pullHQ l (sch.map (s' j)) n i = _
    rw [hId l n i U 1 hl]
    simp
  simp only [mm, e0, e1] at key
  simp only [Int.cast_one, one_smul, Int.cast_neg, neg_smul, Finset.sum_neg_distrib] at key
  exact add_neg_eq_zero.1 key

theorem UpperTheory.Gal.TranscendenceTraces.trSplitQ_of :
    TrBCQ → CorrEqQ → TrIdQ → WtLin → WtFlat → MultBasic → TrSplitQ := by
  intro hBC hCorr hId hLin hFlat hMult l _ n i Z S p _ _ hl U x m s hs hiso
  have wtp : IsWt p (Wt.const Z 1) := by
    rw [← hMult.2.2 p]
    exact hFlat p
  have wtp' : IsWt (pullback.snd p x) (Wt.const (pullback p x) 1) := by
    rw [← hMult.2.2 (pullback.snd p x)]
    exact hFlat _
  have hlU : IsUnit (l : Γ(U, ⊤)) := by
    simpa using hl.map x.appTop.hom
  have h1 := hBC l n i (pullback.fst p x) (pullback.snd p x) p x (Wt.const Z 1)
    (IsPullback.of_hasPullback p x) wtp hl
  have h2 := tr_split hCorr hId l n i (pullback.snd p x) wtp' (hLin.2.2 (𝟙 U) 1) hlU
    (fun j => pullback.lift (s j) (𝟙 U) (by rw [hs j, Category.id_comp]))
    (fun j => pullback.lift_snd _ _ _) hiso
  rw [h1]
  change trHQ l (pullback.snd p x) (Wt.const _ 1) n i ∘ₗ _ = _
  rw [h2]
  refine LinearMap.ext fun a => ?_
  simp only [LinearMap.comp_apply, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← LinearMap.comp_apply, ← pullHQ_comp', ← CategoryTheory.Functor.map_comp, pullback.lift_fst]
end
