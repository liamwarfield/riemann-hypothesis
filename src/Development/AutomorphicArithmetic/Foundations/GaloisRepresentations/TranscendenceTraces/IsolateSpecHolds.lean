module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PStalkSum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AcycFOfPiSh
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PCountWt
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PTrRed
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PPhiQis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCochainEvEqOfNaturalStatement
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PCorrBCQ
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PSecFun
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PChart
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlueMeasUnivNeTopOfCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafSectionsExtAndGlue
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupChernKummerPullbackNaturality
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OmegaBaseChangeFiniteProjectiveReflexive
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChosenInjectiveResolutionEtaleSheafSectionsExact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistSectionsLocallyGenerated
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FontaineAinfLocalDomainXiAdicOrder

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PIndDesc
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces
open scoped TensorProduct

namespace UpperTheory.Gal.TranscendenceTraces

private noncomputable def pushIso (A B O : Type) [CommRing A] [CommRing B] [CommRing O] [Algebra A B] [Algebra A O] :
    (Under.pushout (CommRingCat.ofHom (algebraMap A B))).obj (Under.mk (CommRingCat.ofHom (algebraMap A O))) ≅
      Under.mk (CommRingCat.ofHom (algebraMap B (B ⊗[A] O))) :=
  Under.isoMk (CommRingCat.isPushout_tensorProduct A B O).flip.isoPushout.symm
    ((CommRingCat.isPushout_tensorProduct A B O).flip.inr_isoPushout_inv)

private def algOf {B C T : Type} [CommRing B] [CommRing C] [CommRing T] [Algebra B C] [Algebra B T]
    (f : Under.mk (CommRingCat.ofHom (algebraMap B C)) ⟶ Under.mk (CommRingCat.ofHom (algebraMap B T))) : C →ₐ[B] T :=
  { f.right.hom with
    commutes' := fun b => by
      have := congr($(Under.w f).hom b)
      simpa using this }

private def underOf {B C T : Type} [CommRing B] [CommRing C] [CommRing T] [Algebra B C] [Algebra B T]
    (f : C →ₐ[B] T) : Under.mk (CommRingCat.ofHom (algebraMap B C)) ⟶ Under.mk (CommRingCat.ofHom (algebraMap B T)) :=
  Under.homMk (CommRingCat.ofHom f.toRingHom) (by ext b; exact f.commutes b)

end UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.indDesc_of :
    IndDesc := by
  intro A O B C _ _ _ _ _ _ _ _ hO ⟨g⟩
  obtain ⟨J, _, _, D, ι, ⟨hc⟩, hD⟩ := GlobalTheory.T.exists_filtered_colimit_of_etale_of_indEt A O hO
  let F := Under.pushout (CommRingCat.ofHom (algebraMap A B))
  have hFc := isColimitOfPreserves F hc
  have : IsFinitelyPresentable.{0} (Under.mk (CommRingCat.ofHom (algebraMap B C))) :=
    CommRingCat.isFinitelyPresentable_under _ _
      (show (algebraMap B C).FinitePresentation from
        (RingHom.finitePresentation_algebraMap (A := B) (B := C)).mpr inferInstance)
  obtain ⟨j, q, -⟩ := IsFinitelyPresentable.exists_hom_of_isColimit hFc
    (underOf g ≫ (pushIso A B O).inv)
  let E : Type := (D.obj j).right
  letI : Algebra A E := (D.obj j).hom.hom.toAlgebra
  refine ⟨E, inferInstance, inferInstance, ?_, ?_, ?_⟩
  · exact RingHom.etale_algebraMap.mp (hD j)
  · refine ⟨{ (ι.app j).right.hom with commutes' := fun a => ?_ }⟩
    have := congr($(Under.w (ι.app j)).hom a)
    exact this
  · exact ⟨algOf (q ≫ (pushIso A B E).hom)⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PWtPush
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

private theorem sum_up {α : Type*} {s : Set α} (hs : s.Finite) (f : α → ℤ) :
    ∑ᶠ a ∈ s, (ULift.up.{1} (f a)) = ULift.up.{1} (∑ᶠ a ∈ s, f a) :=
  ((AddEquiv.ulift (α := ℤ)).symm.map_finsum_mem f hs).symm

theorem UpperTheory.Gal.TranscendenceTraces.wtPush_of :
    SumComp → FibFin → WtPush := by
  intro hS hF Z Z' S h p _ _ w hw A φ hφ
  let B : Sq (h ≫ p) :=
    ⟨A.U, pullback h A.v, A.u, pullback.fst h A.v, pullback.snd h A.v ≫ A.r,
      IsPullback.paste_vert (IsPullback.of_hasPullback h A.v) A.pb⟩
  haveI : IsFinite A.r := Sq.finite A
  have hφ' : IsLocallyConstant (φ ∘ (pullback.snd h A.v)) :=
    hφ.comp_continuous (Scheme.Hom.continuous _)
  obtain ⟨ψ, hψ, hψeq⟩ := hw B (φ ∘ (pullback.snd h A.v)) hφ'
  refine ⟨ψ, hψ, ?_⟩
  intro Ω _ _ x
  rw [hψeq Ω x]
  apply (ULift.up_injective : Function.Injective (ULift.up.{1, 0} : ℤ → ULift.{1} ℤ))
  have step1 : ∀ q : gp Ω ⟶ pullback h A.v,
      w Ω (q ≫ B.v) * (φ ∘ (pullback.snd h A.v)) (pt q)
        = w Ω (q ≫ pullback.fst h A.v) * φ (pt (q ≫ pullback.snd h A.v)) := by
    intro q
    simp only [Function.comp_apply, pt_comp]
    rfl
  change ULift.up (∑ᶠ (q : gp Ω ⟶ pullback h A.v) (_ : q ∈ fib (pullback.snd h A.v ≫ A.r) x),
      w Ω (q ≫ B.v) * (φ ∘ (pullback.snd h A.v)) (pt q)) = _
  simp only [step1]
  rw [← sum_up (hF _ Ω x)]
  rw [hS (pullback.snd h A.v) A.r Ω x (ULift.{1} ℤ)
    (fun q => ULift.up (w Ω (q ≫ pullback.fst h A.v) * φ (pt (q ≫ pullback.snd h A.v))))]
  rw [← sum_up (hF A.r Ω x)]
  apply finsum_mem_congr rfl
  intro y hy
  rw [sum_up (hF _ Ω y)]
  congr 1
  unfold Wt.push
  rw [finsum_mem_mul]
  apply finsum_mem_eq_of_bijOn (fun q => q ≫ pullback.fst h A.v)
    (fib_bijOn (IsPullback.of_hasPullback h A.v) y)
  intro q hq
  simp only [fib, Set.mem_setOf_eq] at hq
  rw [hq]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PSplitCover
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

private lemma exists_hom {R Ω : Type} [CommRing R] [Field Ω] (x : gp Ω ⟶ Spec (CommRingCat.of R)) :
    ∃ φ : R →+* Ω, x = Spec.map (CommRingCat.ofHom φ) := by
  refine ⟨(Spec.preimage x).hom, ?_⟩
  simp [Spec.map_preimage]

private lemma map_comp' {R S Ω : Type} [CommRing R] [CommRing S] [CommRing Ω] (a : R →+* S) (φ : S →+* Ω) :
    Spec.map (CommRingCat.ofHom φ) ≫ Spec.map (CommRingCat.ofHom a) =
      Spec.map (CommRingCat.ofHom (φ.comp a)) := by
  rw [← Spec.map_comp]
  rfl

private lemma map_inj' {R S : Type} [CommRing R] [CommRing S] {f g : R →+* S}
    (h : Spec.map (CommRingCat.ofHom f) = Spec.map (CommRingCat.ofHom g)) : f = g := by
  have := Spec.map_injective h
  simpa using congrArg CommRingCat.Hom.hom this

private lemma pt_map {R Ω : Type} [CommRing R] [Field Ω] (f : R →+* Ω) :
    (pt (Spec.map (CommRingCat.ofHom f))).asIdeal = RingHom.ker f := by
  ext a
  simp only [pt]
  show a ∈ (Ideal.comap f (IsLocalRing.closedPoint Ω).asIdeal) ↔ _
  simp [IsLocalRing.closedPoint, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]

theorem UpperTheory.Gal.TranscendenceTraces.splitCover_of :
    SplitField → GalTrans → SplitCover := by
  intro hsf hgt A B _ _ _ _ _ _
  obtain ⟨L, _, _, _, _, _, _, hfin, hsp⟩ := hsf A B
  set C := integralClosure A L
  have hinj : Function.Injective (algebraMap A C) := by
    intro a b hab
    have h1 : algebraMap A L a = algebraMap A L b := by
      have := congrArg (fun c : C => (c : L)) hab
      simpa using this
    rw [IsScalarTower.algebraMap_apply A (FractionRing A) L a,
      IsScalarTower.algebraMap_apply A (FractionRing A) L b] at h1
    exact IsFractionRing.injective A (FractionRing A) ((algebraMap (FractionRing A) L).injective h1)
  have key : ∀ {Ω : Type} [Field Ω] (φ : C →+* Ω),
      RingHom.ker (φ.comp (algebraMap A C)) = ⊥ → RingHom.ker φ = ⊥ := by
    intro Ω _ φ h
    apply Ideal.eq_bot_of_comap_eq_bot (R := A)
    change Ideal.comap (algebraMap A C) (RingHom.ker φ) = ⊥
    rw [RingHom.comap_ker]
    exact h
  refine ⟨Spec (CommRingCat.of C), Spec.map (CommRingCat.ofHom (algebraMap A C)), (B →ₐ[A] C),
    fun j => Spec.map (CommRingCat.ofHom (j : B →+* C)),
    fun j => (⟨RingHom.ker (j : B →+* C), RingHom.ker_isPrime _⟩ : PrimeSpectrum B),
    ?_, ?_, hfin, ?_, ?_, ?_⟩
  · exact IsIntegralHom.SpecMap_iff.mpr (fun x => Algebra.IsIntegral.isIntegral x)
  · refine ⟨fun p => ?_⟩
    have hp : p.asIdeal.IsPrime := p.isPrime
    obtain ⟨Q, -, hQ, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := C) p.asIdeal ⊥ (by
      rw [(show Ideal.under _ ⊥ = ⊥ from Ideal.comap_bot_of_injective _ hinj)]
      exact bot_le)
    exact ⟨⟨Q, hQ⟩, PrimeSpectrum.ext hQc⟩
  · intro j
    rw [map_comp']
    congr 2
    exact j.comp_algebraMap
  · intro Ω _ x x' hxx
    obtain ⟨φ, rfl⟩ := exists_hom x
    obtain ⟨φ', rfl⟩ := exists_hom x'
    simp only [map_comp'] at hxx
    obtain ⟨g, hg⟩ := hgt A L Ω φ φ' (map_inj' hxx)
    let e : (B →ₐ[A] C) ≃ (B →ₐ[A] C) :=
      { toFun := fun j => (g.symm : C →ₐ[A] C).comp j
        invFun := fun j => (g : C →ₐ[A] C).comp j
        left_inv := fun j => by
          ext b
          simp
        right_inv := fun j => by
          ext b
          simp }
    refine ⟨e, fun j => ⟨?_, ?_⟩⟩
    · simp only [map_comp']
      congr 2
      ext b
      simp [e, hg]
    · apply PrimeSpectrum.ext
      ext b
      simp [e]
  · intro Ω _ x z hz hbot
    obtain ⟨φ, rfl⟩ := exists_hom x
    obtain ⟨ζ, rfl⟩ := exists_hom z
    simp only [map_comp'] at hz
    rw [map_comp', pt_map] at hbot
    have hφ : Function.Injective φ := (RingHom.injective_iff_ker_eq_bot φ).mpr (key φ hbot)
    have hiff : ∀ j : B →ₐ[A] C, Spec.map (CommRingCat.ofHom φ) ≫
        Spec.map (CommRingCat.ofHom (j : B →+* C)) = Spec.map (CommRingCat.ofHom ζ) ↔
        φ.comp (j : B →+* C) = ζ := by
      intro j
      rw [map_comp']
      exact ⟨map_inj', fun h => by rw [h]⟩
    obtain ⟨j0, hj0, hu⟩ := hsp Ω φ ζ ((RingHom.injective_iff_ker_eq_bot _).mpr hbot) (map_inj' hz)
    refine ⟨⟨j0, (hiff j0).2 hj0, fun j hj => hu j ((hiff j).1 hj)⟩, fun j hj => ?_⟩
    rw [hiff] at hj
    apply PrimeSpectrum.ext
    rw [pt_map, ← hj]
    ext b
    simp [map_eq_zero_iff _ hφ]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PImgBasic
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

namespace UpperTheory.Gal.TranscendenceTraces

private noncomputable def toOf {Z S : Scheme.{0}} {p : Z ⟶ S} (A : Sq p) : A.To (Sq.of p A.u) :=
  ⟨𝟙 _, pullback.lift A.v A.r A.pb.w, Category.id_comp _, pullback.lift_fst _ _ _,
    (pullback.lift_snd _ _ _).trans (Category.comp_id _).symm⟩

private noncomputable def ofTo {Z S V U : Scheme.{0}} (p : Z ⟶ S) (g : V ⟶ U) (u : U ⟶ S) :
    (Sq.of p (g ≫ u)).To (Sq.of p u) :=
  ⟨g, pullback.lift (pullback.fst p (g ≫ u)) (pullback.snd p (g ≫ u) ≫ g)
      (pullback.condition.trans (Category.assoc _ _ _).symm),
    rfl, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩

private noncomputable def imgVal {Z S : Scheme.{0}} {p : Z ⟶ S} {R' R : Type} [CommRing R'] [CommRing R] {I : Cx R'} {J : Cx R}
    (τ : Fam p I J) {n : ℤ} (α : Cochain ((chains R').obj (sch.obj Z)) I n) (k : ℕ) (s : ℤ) (h : -(k : ℤ) + n = s)
    (U : Scheme.{0}) (u : U ⟶ S) : Sec (J.X s) U :=
  (τ.deg s).app (Sq.of p u) (ev (R := R') α k s h (pullback p u) (pullback.fst p u))

end UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.imgBasic_of :
    ImgBasic := by
  intro Z S p R' R _ _ I J τ n
  have ev_def {T : Type} [CommRing T] {E : Spc} {K : Cx T} {j : ℤ}
      (α : Cochain ((chains T).obj E) K j) (k : ℕ) (s : ℤ) (h : -(k : ℤ) + j = s)
      (U : Scheme.{0}) (x : Sx E k U) : ev (R := T) α k s h U x =
        Sec.map ((chainsXIso T E k).inv ≫ α.v _ _ h) (freeGen T _ U x) := rfl
  refine ⟨fun α => ?_, fun m hm α β hαβ => ?_⟩
  · have ev_res (k : ℕ) (s : ℤ) (h : -(k : ℤ) + n = s) {V U : Scheme.{0}}
        (g : V ⟶ U) (x : Sx (sch.obj Z) k U) :
        Sec.res g (ev (R := R') α k s h U x) = ev (R := R') α k s h V (Sx.res g x) := by
      rw [ev_def, CupSpec.map_res, CupSpec.freeGen_res]
      rfl
    have ev_ext (β' β : Cochain ((chains R).obj (sch.obj S)) J n)
        (he : ∀ k s h U x, ev (R := R) β' k s h U x = ev (R := R) β k s h U x) : β' = β := by
      ext i s hs : 1
      by_cases hi : i ≤ 0
      · obtain ⟨k, rfl⟩ : ∃ k : ℕ, i = -(k : ℤ) := ⟨(-i).toNat, by omega⟩
        rw [← cancel_epi (chainsXIso R (sch.obj S) k).inv]
        exact CupSpec.free_ext _ _ (fun U x => he k s hs U x)
      · exact (CupSpec.isZero_chains (sch.obj S) i (by omega)).eq_of_src _ _
    have hnat : ∀ (k : ℕ) (s : ℤ) (h : -(k : ℤ) + n = s) (V U : Scheme) (g : V ⟶ U) (u : Sx (sch.obj S) k U),
        Sec.res g (imgVal τ α k s h U u) = imgVal τ α k s h V (Sx.res g u) := by
      intro k s h V U g u
      have e1 : Sec.res g ((τ.deg s).app (Sq.of p u) (ev (R := R') α k s h (pullback p u) (pullback.fst p u))) =
          (τ.deg s).app (Sq.of p (g ≫ u)) (Sec.res (ofTo p g u).k (ev (R := R') α k s h (pullback p u) (pullback.fst p u))) :=
        (τ.deg s).nat (ofTo p g u) _
      have e2 : Sec.res (ofTo p g u).k (ev (R := R') α k s h (pullback p u) (pullback.fst p u)) =
          ev (R := R') α k s h (pullback p (g ≫ u)) (pullback.fst p (g ≫ u)) := by
        refine (ev_res k s h (ofTo p g u).k (pullback.fst p u)).trans ?_
        congr 1
        show (ofTo p g u).k ≫ pullback.fst p u = pullback.fst p (g ≫ u)
        exact pullback.lift_fst _ _ _
      exact e1.trans (congrArg _ e2)
    have hex := exists_cochain_ev_eq_of_natural R (E := sch.obj S) (I := J) (n := n)
      (imgVal τ α) hnat
    obtain ⟨β, hβ⟩ := hex
    have hIm : τ.IsImage α β := by
      intro k s h A
      have e1 : Sec.res (toOf A).g ((τ.deg s).app (Sq.of p A.u) (ev (R := R') α k s h (pullback p A.u) (pullback.fst p A.u))) =
          (τ.deg s).app A (Sec.res (toOf A).k (ev (R := R') α k s h (pullback p A.u) (pullback.fst p A.u))) :=
        (τ.deg s).nat (toOf A) _
      have e2 : Sec.res (toOf A).k (ev (R := R') α k s h (pullback p A.u) (pullback.fst p A.u)) =
          ev (R := R') α k s h A.V A.v := by
        refine (ev_res k s h (toOf A).k (pullback.fst p A.u)).trans ?_
        congr 1
        show (toOf A).k ≫ pullback.fst p A.u = A.v
        exact pullback.lift_fst _ _ _
      exact (hβ k s h A.U A.u).trans (((res_id _).symm.trans e1).trans (congrArg _ e2))
    refine ⟨β, hIm, fun β' h' => ev_ext β' β (fun k s h U u => ?_)⟩
    exact (h' k s h (Sq.of p u)).trans (hIm k s h (Sq.of p u)).symm
  · have ev_delta_zero {T : Type} [CommRing T] {E : Spc} {K : Cx T}
        (γ : Cochain ((chains T).obj E) K n) (U : Scheme.{0}) (x : Sx E 0 U) :
        ev (R := T) (δ n m γ) 0 m (by simp) U x =
          Sec.map (K.d n m) (ev (R := T) γ 0 n (by simp) U x) := by
      rw [ev_def, δ_v n m hm γ _ m (by simp) n 1 (by omega) (by simp),
        (CupSpec.isZero_chains E 1 one_pos).eq_of_tgt (((chains T).obj E).d _ 1) 0,
        zero_comp, smul_zero, add_zero]
      rfl
    have ev_delta_succ {T : Type} [CommRing T] {E : Spc} {K : Cx T}
        (γ : Cochain ((chains T).obj E) K n) (U : Scheme.{0}) (q : ℕ) (s t : ℤ)
        (hs : -((q + 1 : ℕ) : ℤ) + n = s) (ht : -((q + 1 : ℕ) : ℤ) + m = t)
        (x : Sx E (q + 1) U) :
        ev (R := T) (δ n m γ) (q + 1) t ht U x =
          Sec.map (K.d s t) (ev (R := T) γ (q + 1) s hs U x) +
            m.negOnePow • ∑ i : Fin (q + 2), (-1 : ℤ) ^ (i : ℕ) •
              ev (R := T) γ q t (by omega) U (x.face i) := by
      rw [ev_def, δ_v n m hm γ _ t ht s (-(q : ℤ)) (by omega) (by omega), Preadditive.comp_add,
        Units.smul_def, Preadditive.comp_zsmul, ← Category.assoc _ (((chains T).obj E).d _ _),
        CupSpec.chains_d, Category.assoc, Preadditive.sum_comp]
      refine (map_add (CupSpec.mapHom _ _ (freeGen T _ U x)) _ _).trans ?_
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_zsmul, map_sum, Units.smul_def]
      refine congrArg₂ (· + ·) rfl (congrArg _ (Finset.sum_congr rfl fun i _ => ?_))
      rw [Preadditive.zsmul_comp, map_zsmul]
      congr 1
      change Sec.map ((chainsXIso T E q).inv ≫ γ.v _ _ _)
        (Sec.map ((free T).map _) (freeGen T _ U x)) = _
      rw [CupSpec.freeGen_map]
      rfl
    intro k s h A
    cases k with
    | zero =>
      have hs : s = m := by simpa using h.symm
      subst hs
      have eβ := ev_delta_zero (E := sch.obj S) β A.U A.u
      have eα := ev_delta_zero (E := sch.obj Z) α A.V A.v
      refine eβ.trans ?_
      refine Eq.trans ?_ (congrArg _ eα.symm)
      refine (congrArg _ (hαβ 0 n (by simp) A)).trans ?_
      exact τ.comm A n s _
    | succ q =>
      have eβ := ev_delta_succ (E := sch.obj S) β A.U q (-((q + 1 : ℕ) : ℤ) + n) s rfl h A.u
      have eα := ev_delta_succ (E := sch.obj Z) α A.V q (-((q + 1 : ℕ) : ℤ) + n) s rfl h A.v
      refine eβ.trans ?_
      refine Eq.trans ?_ (congrArg _ eα.symm)
      rw [map_add (f := _)]
      congr 1
      · exact (congrArg _ (hαβ _ _ rfl A)).trans (τ.comm A _ s _)
      · set_option synthInstance.maxHeartbeats 100000 in
          rw [Units.smul_def, Units.smul_def, map_zsmul, map_sum]
        congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_zsmul]
        congr 1
        exact hαβ q s _ A
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.ImgcSpec
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

namespace UpperTheory.Gal.TranscendenceTraces.RepresentationImage

variable {Z S : Scheme.{0}} {p : Z ⟶ S} {R' R : Type} [CommRing R'] [CommRing R] {I : Cx R'} {J : Cx R}

private theorem img_zero (τ : Fam p I J) (n : ℤ) :
    τ.IsImage (0 : Cochain ((chains R').obj (sch.obj Z)) I n) (0 : Cochain ((chains R).obj (sch.obj S)) J n) := by
  intro k s h A
  have h1 := ((GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := sch.obj S) (I := J) (n := n)).1 0 0 k s h A.U A.u).2.2.1
  have h2 := ((GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R' (E := sch.obj Z) (I := I) (n := n)).1 0 0 k s h A.V A.v).2.2.1
  exact h1.trans ((map_zero ((τ.deg s).app A)).symm.trans (congrArg ((τ.deg s).app A) h2.symm))

private theorem img_add (τ : Fam p I J) {n : ℤ} {a a' : Cochain ((chains R').obj (sch.obj Z)) I n}
    {b b' : Cochain ((chains R).obj (sch.obj S)) J n} (h : τ.IsImage a b) (h' : τ.IsImage a' b') :
    τ.IsImage (a + a') (b + b') := by
  intro k s hs A
  rw [((GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R).1 b b' k s hs A.U A.u).1, ((GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R').1 a a' k s hs A.V A.v).1, map_add (f := _),
    h k s hs A, h' k s hs A]

private noncomputable def imgc (hI : ImgBasic) (τ : Fam p I J) {n : ℤ}
    (α : Cocycle ((chains R').obj (sch.obj Z)) I n) : Cocycle ((chains R).obj (sch.obj S)) J n :=
  Cocycle.mk ((hI R' R τ n).1 α.1).exists.choose (n + 1) rfl (by
    have h := (hI R' R τ n).2 (n + 1) rfl _ _ ((hI R' R τ n).1 α.1).exists.choose_spec
    rw [Cocycle.δ_eq_zero] at h
    exact ((hI R' R τ (n + 1)).1 0).unique h (img_zero τ (n + 1)))

private theorem imgc_spec (hI : ImgBasic) (τ : Fam p I J) {n : ℤ}
    (α : Cocycle ((chains R').obj (sch.obj Z)) I n) : τ.IsImage α.1 (imgc hI τ α).1 :=
  ((hI R' R τ n).1 α.1).exists.choose_spec

private theorem imgc_eq (hI : ImgBasic) (τ : Fam p I J) {n : ℤ}
    (α : Cocycle ((chains R').obj (sch.obj Z)) I n) (β : Cocycle ((chains R).obj (sch.obj S)) J n)
    (h : τ.IsImage α.1 β.1) : imgc hI τ α = β :=
  Cocycle.ext (((hI R' R τ n).1 α.1).unique (imgc_spec hI τ α) h)

private noncomputable def opMap (hI : ImgBasic) (τ : Fam p I J) (n : ℤ) :
    CohomologyClass ((chains R').obj (sch.obj Z)) I n →+ CohomologyClass ((chains R).obj (sch.obj S)) J n :=
  CohomologyClass.descAddMonoidHom
    (AddMonoidHom.mk' (fun α => CohomologyClass.mk (imgc hI τ α)) (fun α α' => by
      rw [← CohomologyClass.mk_add]; congr 1
      exact imgc_eq hI τ _ _ (img_add τ (imgc_spec hI τ α) (imgc_spec hI τ α'))))
    (by
      rintro ⟨a, ha⟩ ⟨n', hn', a', rfl⟩
      change CohomologyClass.mk _ = 0
      rw [CohomologyClass.mk_eq_zero_iff]
      obtain ⟨b, hb, -⟩ := (hI R' R τ n').1 a'
      exact ⟨n', hn', b, ((hI R' R τ n).1 _).unique ((hI R' R τ n').2 n hn' _ _ hb) (imgc_spec hI τ ⟨_, ha⟩)⟩)

private theorem op_spec (hI : ImgBasic) (τ : Fam p I J) (n : ℤ)
    (α : Cocycle ((chains R').obj (sch.obj Z)) I n) (β : Cocycle ((chains R).obj (sch.obj S)) J n)
    (h : τ.IsImage α.1 β.1) : τ.op n (CohomologyClass.mk α) = CohomologyClass.mk β :=
  pick_spec (P := fun c : CohomologyClass ((chains R').obj (sch.obj Z)) I n →+
      CohomologyClass ((chains R).obj (sch.obj S)) J n =>
    ∀ (α : Cocycle _ I n) (β : Cocycle _ J n), τ.IsImage α.1 β.1 →
      c (CohomologyClass.mk α) = CohomologyClass.mk β)
    ⟨opMap hI τ n, fun α β h => congrArg CohomologyClass.mk (imgc_eq hI τ α β h)⟩ α β h

end UpperTheory.Gal.TranscendenceTraces.RepresentationImage

open UpperTheory.Gal.TranscendenceTraces.RepresentationImage in
theorem UpperTheory.Gal.TranscendenceTraces.rpOp_of :
    ImgBasic → RpOp := by
  intro hI Z S p R' R _ _ I J τ n x a hx
  obtain ⟨α, rfl, rfl⟩ := hx
  exact ⟨imgc hI τ α, (op_spec hI τ n α _ (imgc_spec hI τ α)).symm, imgc_spec hI τ α 0 n (by simp) (Sq.self p)⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PNwtFlat
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.nwtFlat_of :
    WtBC → WtFlat → WtUnique → MultBC → NwtFlat := by
  intro hBC hFlat hUniq hMBC Z' S' Z S v p' p g _ _ _ pb hN hD
  haveI : IsFinite p' := MorphismProperty.of_isPullback pb ‹_›
  refine hUniq p' _ _ (hBC v p' p g _ pb hN.1) (hFlat p') _ hD ?_
  intro Ω _ _ z hz
  rw [hMBC v p' p g pb]
  refine hN.2 Ω (z ≫ v) ?_
  have e : (z ≫ v) ≫ p = (z ≫ p') ≫ g := by
    rw [Category.assoc, pb.w, Category.assoc]
  rw [e, pt_comp]
  exact hz
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PNmlInt
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

private theorem normal_affineOpen_integrallyClosed (S : Scheme.{0}) (hN : Nml S) (U : S.Opens) (hU : IsAffineOpen U)
    [IsDomain Γ(S, U)] : IsIntegrallyClosed Γ(S, U) := by
  refine IsIntegrallyClosed.of_localization_maximal ?_
  intro p _ _
  let y : PrimeSpectrum Γ(S, U) := ⟨p, inferInstance⟩
  have hmem : hU.fromSpec y ∈ U := by
    rw [← SetLike.mem_coe, ← hU.range_fromSpec]
    exact ⟨_, rfl⟩
  letI := TopCat.Presheaf.algebra_section_stalk S.presheaf ⟨hU.fromSpec y, hmem⟩
  haveI : IsLocalization.AtPrime (S.presheaf.stalk (hU.fromSpec y)) p := hU.isLocalization_stalk' y hmem
  obtain ⟨_, hint⟩ := hN (hU.fromSpec y)
  haveI := hint
  exact IsIntegrallyClosed.of_equiv
    (IsLocalization.algEquiv p.primeCompl (S.presheaf.stalk (hU.fromSpec y)) (Localization.AtPrime p)).toRingEquiv

theorem UpperTheory.Gal.TranscendenceTraces.nmlInt_of :
    NmlInt := by
  intro S _ hN s
  obtain ⟨U, hU, hs, -⟩ := exists_isAffineOpen_mem_and_subset (x := s) (U := ⊤) trivial
  haveI : Nonempty U := ⟨⟨s, hs⟩⟩
  haveI : IsDomain Γ(S, U) := IsIntegral.component_integral U
  exact ⟨U, hU, hs, inferInstance, normal_affineOpen_integrallyClosed S hN U hU⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PMultOpen
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

private theorem length_self_eq_of_ringEquiv {R R' : Type*} [CommRing R] [CommRing R'] (f : R ≃+* R') :
    Module.length R R = Module.length R' R' := by
  haveI : RingHomInvPair (f : R →+* R') (f.symm : R' →+* R) := RingHomInvPair.of_ringEquiv f
  haveI : RingHomInvPair (f.symm : R' →+* R) (f : R →+* R') := RingHomInvPair.symm _ _
  apply WithBot.coe_injective
  rw [Module.coe_length, Module.coe_length]
  exact Order.krullDim_eq_of_orderIso (Submodule.orderIsoMapComap f.toSemilinearEquiv)

private theorem length_stalk_eq {X Y : Scheme.{0}} (e : X ⟶ Y) [IsOpenImmersion e] (x : X) :
    Module.length (X.presheaf.stalk x) (X.presheaf.stalk x) =
      Module.length (Y.presheaf.stalk (e x)) (Y.presheaf.stalk (e x)) := by
  exact (length_self_eq_of_ringEquiv (asIso (e.stalkMap x)).commRingCatIsoToRingEquiv).symm

theorem UpperTheory.Gal.TranscendenceTraces.multOpen_of :
    MultOpen := by
  intro W Z S j _ p
  funext Ω _ _ z
  have e1 : (j ≫ p) ≫ 𝟙 S = j ≫ p := by simp
  have e2 : (z ≫ j ≫ p) ≫ 𝟙 S = 𝟙 (gp Ω) ≫ (z ≫ j) ≫ p := by simp
  let m := pullback.map (j ≫ p) (z ≫ j ≫ p) p ((z ≫ j) ≫ p) j (𝟙 _) (𝟙 S) e1 e2
  have hm : IsOpenImmersion m := by infer_instance
  have hx : pullback.lift z (𝟙 (gp Ω)) (by simp) ≫ m =
      pullback.lift (z ≫ j) (𝟙 (gp Ω)) (by simp) := by
    apply pullback.hom_ext
    · rw [Category.assoc (pullback.lift z (𝟙 (gp Ω)) _)]
      simp only [m, pullback.map, pullback.lift_fst, pullback.lift_fst_assoc]
    · rw [Category.assoc (pullback.lift z (𝟙 (gp Ω)) _)]
      simp only [m, pullback.map, pullback.lift_snd, pullback.lift_snd_assoc, Category.comp_id]
  have hl := length_stalk_eq m (pt (pullback.lift z (𝟙 (gp Ω)) (by simp)))
  rw [← pt_comp, hx] at hl
  simp only [mult, Wt.comap]
  rw [hl]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PFamLin
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

noncomputable section

private def famAdd {Z S : Scheme.{0}} {p : Z ⟶ S} {R' R : Type} [CommRing R'] [CommRing R] {I : Cx R'} {J : Cx R}
    (τ τ' : Fam p I J) : Fam p I J where
  deg s := ⟨fun A => (τ.deg s).app A + (τ'.deg s).app A, fun t a => by
    simp only [AddMonoidHom.add_apply]
    rw [← (τ.deg s).nat t a, ← (τ'.deg s).nat t a]
    exact map_add _ _ _⟩
  comm A s t a := by
    simp only [AddMonoidHom.add_apply]
    rw [← τ.comm, ← τ'.comm]
    exact map_add _ _ _

private def famSmul {Z S : Scheme.{0}} {p : Z ⟶ S} {R' R : Type} [CommRing R'] [CommRing R] {I : Cx R'} {J : Cx R}
    (d : ℤ) (τ : Fam p I J) : Fam p I J where
  deg s := ⟨fun A => d • (τ.deg s).app A, fun t a => by
    simp only [AddMonoidHom.smul_apply]
    rw [← (τ.deg s).nat t a]
    exact map_zsmul _ _ _⟩
  comm A s t a := by
    simp only [AddMonoidHom.smul_apply]
    rw [← τ.comm]
    exact map_zsmul _ _ _

private theorem isIso_r {S : Scheme.{0}} (A : Sq (𝟙 S)) : IsIso A.r := A.pb.isIso_snd_of_isIso

private def resInv {S : Scheme.{0}} {R : Type} [CommRing R] (F : Shv R) (A : Sq (𝟙 S)) : Sec F A.V →+ Sec F A.U :=
  haveI := isIso_r A
  AddMonoidHom.mk' (fun a => Sec.res (inv A.r) a) (fun a b => map_add _ _ _)

private theorem resInv_apply {S : Scheme.{0}} {R : Type} [CommRing R] (F : Shv R) (A : Sq (𝟙 S)) [IsIso A.r] (a : Sec F A.V) :
    resInv F A a = Sec.res (inv A.r) a := rfl

private def famId (S : Scheme.{0}) {R : Type} [CommRing R] (I : Cx R) (d : ℤ) : Fam (𝟙 S) I I where
  deg s := ⟨fun A => d • resInv (I.X s) A, fun {A B} t a => by
    haveI := isIso_r A
    haveI := isIso_r B
    simp only [AddMonoidHom.smul_apply, resInv_apply]
    have e : t.g ≫ inv B.r = inv A.r ≫ t.k := by
      rw [IsIso.comp_inv_eq, Category.assoc, t.hr, IsIso.inv_hom_id_assoc]
    rw [show Sec.res t.g (d • Sec.res (inv B.r) a) = d • Sec.res t.g (Sec.res (inv B.r) a) from map_zsmul _ _ _,
      res_res, res_res, e]⟩
  comm A s t a := by
    haveI := isIso_r A
    simp only [AddMonoidHom.smul_apply, resInv_apply]
    rw [show Sec.map (I.d s t) (d • Sec.res (inv A.r) a) = d • Sec.map (I.d s t) (Sec.res (inv A.r) a) from map_zsmul _ _ _,
      map_res]

theorem UpperTheory.Gal.TranscendenceTraces.famLin_of :
    FibFin → FamLin := by
  intro hF q i
  refine ⟨?_, ?_, ?_⟩
  · intro Z S p _ w w' τ τ' hτ hτ'
    refine ⟨famAdd τ τ', fun A a => ?_, fun n A a => rfl⟩
    obtain ⟨b, hb, hs⟩ := hτ A a
    obtain ⟨b', hb', hs'⟩ := hτ' A a
    refine ⟨b + b', ?_, fun Ω _ _ x => ?_⟩
    · change (τ.deg 0).app A _ + (τ'.deg 0).app A _ = _
      rw [hb, hb']
      exact (map_add _ _ _).symm
    · haveI := Sq.finite A
      have hfin := hF A.r Ω x
      rw [show Sec.res x (b + b') = Sec.res x b + Sec.res x b' from map_add _ _ _, hs Ω x, hs' Ω x,
        ← finsum_mem_add_distrib hfin]
      refine finsum_mem_congr rfl fun z _ => ?_
      simp only [Wt.add, add_smul]
  · intro Z S p _ d w τ hτ
    refine ⟨famSmul d τ, fun A a => ?_, fun n A a => rfl⟩
    obtain ⟨b, hb, hs⟩ := hτ A a
    refine ⟨d • b, ?_, fun Ω _ _ x => ?_⟩
    · change d • (τ.deg 0).app A _ = _
      rw [hb]
      exact (map_zsmul _ _ _).symm
    · haveI := Sq.finite A
      have hfin := hF A.r Ω x
      rw [show Sec.res x (d • b) = d • Sec.res x b from map_zsmul _ _ _, hs Ω x]
      have := (zsmulAddGroupHom (α := Sec (tw q i) (gp Ω)) d).map_finsum_mem
        (fun z => w Ω (z ≫ A.v) • Sec.res z a) hfin
      refine this.trans ?_
      refine finsum_mem_congr rfl fun z _ => ?_
      simp only [Wt.smul, mul_smul, zsmulAddGroupHom_apply]
  · intro S d
    refine ⟨famId S _ d, fun A a => ?_, fun n a => ?_⟩
    · haveI := isIso_r A
      refine ⟨d • Sec.res (inv A.r) a, ?_, fun Ω _ _ x => ?_⟩
      · change d • resInv ((res _ (tw q i)).X 0) A (Sec.map (resι _ (tw q i)) a) = _
        rw [resInv_apply, ← map_res]
        exact (map_zsmul _ _ _).symm
      · have hf : fib A.r x = {x ≫ inv A.r} := by
          ext z
          simp only [fib, Set.mem_setOf_eq, Set.mem_singleton_iff]
          rw [IsIso.eq_comp_inv]
        rw [hf, finsum_mem_singleton]
        rw [show Sec.res x (d • Sec.res (inv A.r) a) = d • Sec.res x (Sec.res (inv A.r) a) from map_zsmul _ _ _, res_res]
        rfl
    · change d • resInv ((res _ (tw q i)).X n) (Sq.self (𝟙 S)) a = _
      haveI := isIso_r (Sq.self (𝟙 S))
      rw [resInv_apply]
      have e : inv (Sq.self (𝟙 S)).r = 𝟙 _ := IsIso.inv_id
      rw [e]
      exact congrArg (d • ·) (res_id a)

end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PFamPush
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

private noncomputable def sqPush {Z Z' S : Scheme.{0}} (h : Z ⟶ Z') (p : Z' ⟶ S) (A : Sq p) : Sq (h ≫ p) :=
  ⟨A.U, pullback h A.v, A.u, pullback.fst h A.v, pullback.snd h A.v ≫ A.r,
    (IsPullback.of_hasPullback h A.v).paste_vert A.pb⟩

private def resHom {R : Type} [CommRing R] (F : Shv R) {V U : Scheme.{0}} (g : V ⟶ U) : Sec F U →+ Sec F V :=
  (F.obj.map g.op).hom.toAddMonoidHom

private theorem pushK_w {Z Z' S : Scheme.{0}} (h : Z ⟶ Z') {p : Z' ⟶ S} {A B : Sq p} (t : A.To B) :
    pullback.fst h A.v ≫ h = (pullback.snd h A.v ≫ t.k) ≫ B.v := by
  rw [Category.assoc, t.hv]
  exact pullback.condition

private noncomputable def pushK {Z Z' S : Scheme.{0}} (h : Z ⟶ Z') {p : Z' ⟶ S} {A B : Sq p} (t : A.To B) :
    pullback h A.v ⟶ pullback h B.v :=
  pullback.lift (pullback.fst h A.v) (pullback.snd h A.v ≫ t.k) (pushK_w h t)

private theorem pushK_fst {Z Z' S : Scheme.{0}} (h : Z ⟶ Z') {p : Z' ⟶ S} {A B : Sq p} (t : A.To B) :
    pushK h t ≫ pullback.fst h B.v = pullback.fst h A.v := pullback.lift_fst _ _ _

private theorem pushK_snd {Z Z' S : Scheme.{0}} (h : Z ⟶ Z') {p : Z' ⟶ S} {A B : Sq p} (t : A.To B) :
    pushK h t ≫ pullback.snd h B.v = pullback.snd h A.v ≫ t.k := pullback.lift_snd _ _ _

private theorem pushK_r {Z Z' S : Scheme.{0}} (h : Z ⟶ Z') {p : Z' ⟶ S} {A B : Sq p} (t : A.To B) :
    pushK h t ≫ pullback.snd h B.v ≫ B.r = (pullback.snd h A.v ≫ A.r) ≫ t.g := by
  rw [← Category.assoc, pushK_snd, Category.assoc, t.hr, Category.assoc]

private noncomputable def toPush {Z Z' S : Scheme.{0}} (h : Z ⟶ Z') (p : Z' ⟶ S) {A B : Sq p} (t : A.To B) :
    (sqPush h p A).To (sqPush h p B) :=
  ⟨t.g, pushK h t, t.hu, pushK_fst h t, pushK_r h t⟩

private theorem res_pushK {R : Type} [CommRing R] {F : Shv R} {Z Z' S : Scheme.{0}} (h : Z ⟶ Z') {p : Z' ⟶ S}
    {A B : Sq p} (t : A.To B) (a : Sec F B.V) :
    Sec.res (pushK h t) (Sec.res (pullback.snd h B.v) a) = Sec.res (pullback.snd h A.v) (Sec.res t.k a) := by
  rw [res_res, res_res, pushK_snd]

private noncomputable def familyPushforward {Z Z' S : Scheme.{0}} (h : Z ⟶ Z') (p : Z' ⟶ S) {R' R : Type} [CommRing R']
    [CommRing R] {F : Shv R'} {G : Shv R} (τ : Fam0 (h ≫ p) F G) : Fam0 p F G where
  app A := (τ.app (sqPush h p A)).comp (resHom F (pullback.snd h A.v))
  nat {A B} t a := (τ.nat (toPush h p t) (Sec.res (pullback.snd h B.v) a)).trans
    (congrArg (τ.app (sqPush h p A)) (res_pushK h t a))

private noncomputable def famPush {Z Z' S : Scheme.{0}} (h : Z ⟶ Z') (p : Z' ⟶ S) {R' R : Type} [CommRing R']
    [CommRing R] {I : Cx R'} {J : Cx R} (τ : Fam (h ≫ p) I J) : Fam p I J where
  deg s := familyPushforward h p (τ.deg s)
  comm A s t a := (τ.comm (sqPush h p A) s t (Sec.res (pullback.snd h A.v) a)).trans
    (congrArg ((τ.deg t).app (sqPush h p A)) (map_res (I.d s t) (pullback.snd h A.v) a))

private theorem sum_push (hS : SumComp) (hF : FibFin) {q : ℕ} {i : ℤ} {Z Z' S : Scheme.{0}} (h : Z ⟶ Z') (p : Z' ⟶ S)
    [IsFinite h] [IsFinite p] (w : Wt Z) (A : Sq p) (a : Sec (tw q i) A.V) (b : Sec (tw q i) A.U)
    (hb : IsSum w (sqPush h p A) (Sec.res (pullback.snd h A.v) a) b) : IsSum (w.push h) A a b := by
  intro Ω _ _ x
  haveI := A.finite
  refine (hb Ω x).trans ((hS (pullback.snd h A.v) A.r Ω x _
    (fun z => w Ω (z ≫ pullback.fst h A.v) • Sec.res z (Sec.res (pullback.snd h A.v) a))).trans ?_)
  refine finsum_congr fun y => finsum_congr fun hy => ?_
  have hfin := hF (pullback.snd h A.v) Ω y
  have hbij := fib_bijOn (IsPullback.of_hasPullback h A.v) (Ω := Ω) y
  have hsum := finsum_mem_eq_of_bijOn (f := fun z => w Ω (z ≫ pullback.fst h A.v))
    (g := fun z' => w Ω z') _ hbij (fun _ _ => rfl)
  show _ = (∑ᶠ (z' : gp Ω ⟶ Z) (_ : z' ∈ fib h (y ≫ A.v)), w Ω z') • Sec.res y a
  rw [← hsum, finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin,
    Finset.sum_smul]
  refine Finset.sum_congr rfl fun z hz => ?_
  rw [Set.Finite.mem_toFinset] at hz
  rw [res_res]
  congr 2

private theorem self_r {Z Z' S : Scheme.{0}} (h : Z ⟶ Z') (p : Z' ⟶ S) :
    pullback.fst h (𝟙 Z') ≫ h ≫ p = (pullback.snd h (𝟙 Z') ≫ p) ≫ 𝟙 S := by
  rw [Category.comp_id, ← Category.assoc, pullback.condition, Category.comp_id]

private theorem res_self {R : Type} [CommRing R] {F : Shv R} {Z Z' : Scheme.{0}} (h : Z ⟶ Z') (a : Sec F Z') :
    Sec.res (pullback.fst h (𝟙 Z')) (Sec.res h a) = Sec.res (pullback.snd h (𝟙 Z')) a := by
  rw [res_res, pullback.condition, Category.comp_id]

theorem UpperTheory.Gal.TranscendenceTraces.famPush_of :
    SumComp → FibFin → FamPush := by
  intro hS hF q i Z Z' S h p _ _ w τ hτ
  refine ⟨famPush h p τ, ?_, ?_⟩
  · intro A a
    obtain ⟨b, hb, hbs⟩ := hτ (sqPush h p A) (Sec.res (pullback.snd h A.v) a)
    refine ⟨b, ?_, sum_push hS hF h p w A a b hbs⟩
    show (τ.deg 0).app (sqPush h p A)
      (Sec.res (pullback.snd h A.v) (Sec.map (resι (ZMod q) (tw q i)) a)) = _
    exact (congrArg ((τ.deg 0).app (sqPush h p A)) (map_res _ _ a)).symm.trans hb
  · intro n a
    let t : (sqPush h p (Sq.self p)).To (Sq.self (h ≫ p)) :=
      ⟨𝟙 S, pullback.fst h (𝟙 Z'), Category.id_comp _, Category.comp_id _, self_r h p⟩
    have hn : Sec.res (𝟙 S) ((τ.deg n).app (Sq.self (h ≫ p)) (Sec.res h a)) =
        (τ.deg n).app (sqPush h p (Sq.self p)) (Sec.res (pullback.fst h (𝟙 Z')) (Sec.res h a)) :=
      (τ.deg n).nat t (Sec.res h a)
    show (τ.deg n).app (sqPush h p (Sq.self p)) (Sec.res (pullback.snd h (𝟙 Z')) a) = _
    exact (congrArg ((τ.deg n).app (sqPush h p (Sq.self p))) (res_self h a).symm).trans
      (hn.symm.trans (res_id _))
end

section -- restored from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PExtRes
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.extRes_of :
    ExtRes := by
  intro R _ F G T ε _
  obtain ⟨hKI, -, hGE, -, hι, -⟩ := GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties R G
  haveI := hKI
  haveI := hGE
  have key := GlobalTheory.T.extend_chainMap_along_quasiIso_kInjective R F T (res R G) ε
  refine ⟨fun a => ?_, fun m m' h U i n k hin hnk y hy => ?_⟩
  · obtain ⟨m, hm⟩ := key.1 ((CochainComplex.singleFunctor (Shv R) 0).map a ≫ resAug G)
    refine ⟨m, ?_⟩
    have h0 : ε.f 0 ≫ m.f 0 = ((CochainComplex.singleFunctor (Shv R) 0).map a).f 0 ≫ (resAug G).f 0 := by
      rw [← HomologicalComplex.comp_f, hm, HomologicalComplex.comp_f]
    rw [h0, ← hι]
    change (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).inv ≫
        ((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).map a).f 0 ≫ (resAug G).f 0 =
      a ≫ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 G).inv ≫ (resAug G).f 0
    rw [HomologicalComplex.single_map_f_self]
    exact (congrArg (_ ≫ ·) (Category.assoc _ _ _)).trans
      ((Iso.inv_hom_id_assoc _ _).trans (Category.assoc _ _ _))
  · have hε : ε ≫ m = ε ≫ m' := by
      refine HomologicalComplex.from_single_hom_ext (j := 0) ?_
      rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f]
      exact (Iso.cancel_iso_inv_left (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F) _ _).1 h
    obtain ⟨H⟩ := key.2 m m' hε
    have hc := H.comm n
    rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel n k from hnk),
      prevD_eq _ (show (ComplexShape.up ℤ).Rel i n from hin)] at hc
    have e1 : Sec.map (T.d n k ≫ H.hom k n) y = 0 := by
      change Sec.map (H.hom k n) (Sec.map (T.d n k) y) = 0
      rw [hy]
      exact map_zero _
    have e2 : Sec.map (H.hom n i ≫ (res R G).d i n) y = Sec.map ((res R G).d i n) (Sec.map (H.hom n i) y) := rfl
    have e3 : ∀ {A B : Shv R} (f g : A ⟶ B) (x : Sec A U), Sec.map (f + g) x = Sec.map f x + Sec.map g x :=
      fun _ _ _ => rfl
    refine ⟨Sec.map (H.hom n i) y, ?_⟩
    rw [hc, e3, e3, e1, e2, zero_add, add_sub_cancel_right]
end

section -- restored from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PFamHom
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

private noncomputable def postFam {Z S : Scheme.{0}} {p : Z ⟶ S} {R : Type} [CommRing R] {G K J : Shv R}
    (t : Fam0 p G K) (m : K ⟶ J) : Fam0 p G J where
  app A := ((m.hom.app (op A.U)).hom.toAddMonoidHom).comp (t.app A)
  nat {A B} s a := by
    change Sec.res s.g (Sec.map m (t.app B a)) = Sec.map m (t.app A (Sec.res s.k a))
    rw [← t.nat s a, map_res]

theorem UpperTheory.Gal.TranscendenceTraces.famHom_of :
    FamHom := by
  intro Q Z S p Φ _ e hrep I J
  constructor
  · intro m
    refine ⟨⟨fun n => postFam (e (I.X n)) (m.f n), fun A s t a => ?_⟩, fun n A a => rfl⟩
    have hc := congrArg (fun φ => Sec.map φ ((e (I.X s)).app A a)) (m.comm s t)
    exact hc.trans (congrArg (Sec.map (m.f t)) (hrep.nat (I.d s t) A a))
  · intro τ
    choose mm hmm _ using fun n => hrep.univ (I.X n) (J.X n) (τ.deg n)
    refine ⟨⟨mm, fun i j _ => ?_⟩, fun n A a => (hmm n A a).symm⟩
    apply (hrep.univ (I.X i) (J.X j) (postFam (τ.deg i) (J.d i j))).unique
    · intro A a
      exact congrArg (Sec.map (J.d i j)) (hmm i A a)
    · intro A a
      exact ((congrArg (Sec.map (mm j)) (hrep.nat (I.d i j) A a)).trans (hmm j A _)).trans
        (τ.comm A i j a).symm
end

section -- restored from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PhiAsm
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

namespace UpperTheory.Gal.TranscendenceTraces

theorem phiEx_of_parts (hU : PhiUniv) (hE : PhiExact) : PhiEx := by
  intro Q Z S p _
  refine ⟨phi p (ZMod Q), inferInstance, fun G => phiE p G, ⟨fun f A a => ?_, fun G J t => hU Q p G J t⟩,
    fun T hT => hE _ p T hT⟩
  rw [phiE_app, phiE_app, phiSec_map, DS.map_inc, map_res]

theorem fL_of_parts (hQ : PhiQis) (hX : ExtRes) (hH : FamHom) (hP : PhiEx) : FL := by
  intro Q Z S p _ F G t
  obtain ⟨Φ, _, e, hr, hex⟩ := hP Q p
  obtain ⟨ε, hq, hε⟩ := hQ _ Φ hex F
  obtain ⟨h1, h2⟩ := hX _ (Φ.obj F) G _ ε
  obtain ⟨k1, k2⟩ := hH Q p Φ e hr (res _ F) (res _ G)
  obtain ⟨a0, ha0, -⟩ := hr.univ F G t
  have key : ∀ (m : (Φ.mapHomologicalComplex (ComplexShape.up ℤ)).obj (res _ F) ⟶ res _ G) (A : Sq p) (a : Sec F A.V),
      Sec.map (sglι (Φ.obj F) ≫ ε.f 0 ≫ m.f 0) ((e F).app A a) =
        Sec.map (F := Φ.obj ((res _ F).X 0)) (m.f 0) ((e _).app A (Sec.map (resι _ F) a)) := by
    intro m A a
    rw [← hr.nat, ← hε]
    rfl
  refine ⟨?_, fun τ τ' hτ hτ' A m n k hm hn a ha => ?_⟩
  · obtain ⟨m, hm⟩ := h1 a0
    obtain ⟨τ, hτ⟩ := k1 m
    refine ⟨τ, fun A a => ?_⟩
    rw [hτ, ← key, hm, ← ha0]
    rfl
  · obtain ⟨u, hu⟩ := k2 τ
    obtain ⟨u', hu'⟩ := k2 τ'
    let t' : Fam0 p F ((res _ G).X 0) :=
      { app := fun A => ((resι _ G).hom.app (op A.U)).hom.toAddMonoidHom.comp (t.app A)
        nat := fun s a => (map_res (resι _ G) s.g _).symm.trans (congrArg _ (t.nat s a)) }
    have e0 : sglι (Φ.obj F) ≫ ε.f 0 ≫ u.f 0 = sglι (Φ.obj F) ≫ ε.f 0 ≫ u'.f 0 :=
      (hr.univ F _ t').unique (fun A a => by rw [key, ← hu]; exact hτ A a) (fun A a => by rw [key, ← hu']; exact hτ' A a)
    have hy : Sec.map (((Φ.mapHomologicalComplex (ComplexShape.up ℤ)).obj (res _ F)).d n k) ((e _).app A a) = 0 := by
      refine (hr.nat ((res _ F).d n k) A a).trans ?_
      rw [ha]
      exact map_zero _
    obtain ⟨c, hc⟩ := h2 u u' e0 A.U m n k hm hn _ hy
    exact ⟨c, by rw [hu, hu']; exact hc⟩

end UpperTheory.Gal.TranscendenceTraces
end

section -- restored from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.FLOf
namespace UpperTheory.Gal.TranscendenceTraces

theorem fL_of : PhiEx → FL := fL_of_parts phiQis_of extRes_of famHom_of

end UpperTheory.Gal.TranscendenceTraces
end

section -- restored from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.OpEqOf
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.opEq_of :
    FL → RpBasic → RpOp → OpEq := by
  intro hFL hB hOp Q Z S p _ F G t τ τ' hτ hτ' n
  ext x
  obtain ⟨a, ha⟩ := (hB (ZMod Q) (res (ZMod Q) F) Z n).1 x
  have hd := (hB (ZMod Q) (res (ZMod Q) F) Z n).2.1 x a ha
  have h1 := hOp _ _ τ n x a ha
  have h2 := hOp _ _ τ' n x a ha
  obtain ⟨y, hy⟩ := (hFL Q p F G t).2 τ τ' hτ hτ' (Sq.self p) (n - 1) n (n + 1)
    (sub_add_cancel n 1) rfl a hd
  exact ((hB (ZMod Q) (res (ZMod Q) G) S n).2.2.1 _ _ _ _ h1 h2).1.mpr ⟨y, hy⟩
end

section -- restored from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PArtSum
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

private theorem length_local (Ω R : Type) [Field Ω] [IsAlgClosed Ω] [CommRing R] [Algebra Ω R]
    [Module.Finite Ω R] [IsLocalRing R] : Module.length R R = Module.finrank Ω R := by
  have h1 := IsLocalRing.length_restrictScalars Ω R R
  have h2 : Module.length (IsLocalRing.ResidueField Ω) (IsLocalRing.ResidueField R) = 1 := by
    rw [← Module.length_eq_of_surjective (S := Ω) (M := IsLocalRing.ResidueField R)
      IsLocalRing.residue_surjective]
    haveI : Module.Finite Ω (IsLocalRing.ResidueField R) :=
      Module.Finite.of_surjective (IsScalarTower.toAlgHom Ω R (IsLocalRing.ResidueField R)).toLinearMap
        IsLocalRing.residue_surjective
    rw [Module.length_eq_finrank,
      Module.finrank_of_bijective_algebraMap IsAlgClosed.algebraMap_bijective_of_isIntegral]
    rfl
  rw [h2, mul_one, Module.length_eq_finrank] at h1
  exact h1.symm

theorem UpperTheory.Gal.TranscendenceTraces.artSum_of : ArtSum := by
  intro Ω B _ _ _ _ _
  classical
  haveI : IsArtinianRing B := IsArtinianRing.of_finite Ω B
  haveI : Fintype (PrimeSpectrum B) := Fintype.ofFinite _
  have hbij := PrimeSpectrum.discreteTopology_iff_toPiLocalization_bijective.mp
    (inferInstance : DiscreteTopology (PrimeSpectrum B))
  let e : B ≃ₗ[Ω] PrimeSpectrum.PiLocalization B :=
    LinearEquiv.ofBijective
      ((PrimeSpectrum.toPiLocalization B).restrictScalars Ω).toLinearMap hbij
  haveI : Module.Finite Ω (PrimeSpectrum.PiLocalization B) := Module.Finite.equiv e
  haveI : ∀ P : PrimeSpectrum B, Module.Finite Ω (Localization.AtPrime P.asIdeal) := fun P =>
    Module.Finite.of_surjective
      (LinearMap.proj (R := Ω) (φ := fun P : PrimeSpectrum B => Localization.AtPrime P.asIdeal) P)
      (fun x => ⟨Pi.single P x, by simp⟩)
  rw [finsum_eq_sum_of_fintype, e.finrank_eq, Module.finrank_pi_fintype]
  refine Finset.sum_congr rfl fun P _ => ?_
  rw [length_local Ω (Localization.AtPrime P.asIdeal)]
  rfl
end

section -- restored from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PCorrEqQ
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

private theorem hl_rel (hTr : TrHl) (hC : CorrEq) (l : ℕ) [Fact l.Prime] (n i : ℤ) {S Y B : Scheme.{0}} (bS : S ⟶ B) (bY : Y ⟶ B)
    [IsSeparated bY] [LocallyOfFiniteType bY] (ι : Type) [Fintype ι] (c : ι → Corr S Y) (m : ι → ℤ)
    (hb : ∀ a, (c a).f ≫ bY = (c a).p ≫ bS) (hl : IsUnit (l : Γ(S, ⊤))) (D : Set S) (hD : Dense D)
    (hz : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : gp Ω ⟶ S) (y : gp Ω ⟶ Y), pt x ∈ D →
      ∑ a, m a * (c a).cyc Ω x y = 0) :
    ∑ a, m a • (trHl l (c a).p (c a).w n i ∘ₗ pullHl l (sch.map (c a).f) n i) = 0 := by
  refine LinearMap.ext fun x => Subtype.ext (funext fun k => ?_)
  haveI : NeZero (l ^ k) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have hq : IsUnit ((l ^ k : ℕ) : Γ(S, ⊤)) := by
    rw [Nat.cast_pow]
    exact hl.pow k
  have h := hC (l ^ k) n i bS bY ι c m hb hq D hD hz (x.1 k)
  have e : ∀ a, ((trHl l (c a).p (c a).w n i ∘ₗ pullHl l (sch.map (c a).f) n i) x).1 k =
      (c a).op (l ^ k) n i (x.1 k) := fun a => by
    haveI := (c a).fin
    exact hTr l n i (c a).p (c a).w (c a).wt hl _ k
  rw [LinearMap.sum_apply, Submodule.coe_sum, Finset.sum_apply]
  refine Eq.trans (Finset.sum_congr rfl fun a _ => ?_) h
  change m a • ((trHl l (c a).p (c a).w n i ∘ₗ pullHl l (sch.map (c a).f) n i) x).1 k = _
  rw [e a]
  rfl

theorem UpperTheory.Gal.TranscendenceTraces.corrEqQ_of :
    TrHl → CorrEq → CorrEqQ := by
  intro hTr hC l _ n i S Y B bS bY _ _ ι _ c m hb hl D hD hz
  have h := hl_rel hTr hC l n i bS bY ι c m hb hl D hD hz
  have e : ∀ a, Corr.opQ l (c a) n i = LinearMap.baseChangeHom ℤ_[l] ℚ_[l] _ _
      (trHl l (c a).p (c a).w n i ∘ₗ pullHl l (sch.map (c a).f) n i) := by
    intro a
    rw [LinearMap.baseChangeHom_apply, LinearMap.baseChange_comp]
    rfl
  simp only [e, Int.cast_smul_eq_zsmul]
  simp_rw [← map_zsmul]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← map_sum, h, map_zero]
end

section -- restored from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PCorrGraphQ
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.corrGraphQ_of :
    TrIdQ → WtLin → CorrGraphQ := by
  intro hT hW S Y f d
  refine ⟨⟨S, 𝟙 S, f, Wt.const S d, inferInstance, hW.2.2 (𝟙 S) d⟩, ?_, ?_, ?_⟩
  · intro B bY
    simp
  · intro Ω _ _ x y
    constructor
    · intro h
      have hs : {z : gp Ω ⟶ S | z ≫ 𝟙 S = x ∧ z ≫ f = y} = {x} := by
        ext z
        simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, Category.comp_id]
        constructor
        · exact fun hz => hz.1
        · rintro rfl
          exact ⟨rfl, h⟩
      change ∑ᶠ z ∈ {z : gp Ω ⟶ S | z ≫ 𝟙 S = x ∧ z ≫ f = y}, Wt.const S d Ω z = d
      rw [hs, finsum_mem_singleton]
      rfl
    · intro h
      have hs : {z : gp Ω ⟶ S | z ≫ 𝟙 S = x ∧ z ≫ f = y} = ∅ := by
        ext z
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, Category.comp_id]
        rintro ⟨rfl, h'⟩
        exact h h'
      change ∑ᶠ z ∈ {z : gp Ω ⟶ S | z ≫ 𝟙 S = x ∧ z ≫ f = y}, Wt.const S d Ω z = 0
      rw [hs, finsum_mem_empty]
  · intro l _ n i hl
    change (trHQ l (𝟙 S) (Wt.const S d) n i).comp (pullHQ l (sch.map f) n i) = _
    rw [hT l n i S d hl, LinearMap.smul_comp, LinearMap.id_comp]
end

section -- restored from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PCountEx
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.countEx_of :
    CountEx := by
  classical
  intro T Z S p π ι σ m hsym
  refine ⟨fun Ω _ _ z => if h : ∃ x : gp Ω ⟶ T, z ≫ p = x ≫ π then
      ∑ᶠ (j : ι) (_ : j ∈ {j | h.choose ≫ σ j = z}), m j else 0, ?_⟩
  intro Ω _ _ x z hz
  have hex : ∃ x : gp Ω ⟶ T, z ≫ p = x ≫ π := ⟨x, hz⟩
  simp only [dif_pos hex]
  set x₀ := hex.choose with hx₀
  have h₀ : z ≫ p = x₀ ≫ π := hex.choose_spec
  obtain ⟨e, he⟩ := hsym Ω x x₀ (hz.symm.trans h₀)
  symm
  apply finsum_mem_eq_of_bijOn e
  · refine ⟨?_, ?_, ?_⟩
    · intro j hj
      simp only [Set.mem_setOf_eq] at hj ⊢
      rw [← (he j).1, hj]
    · intro a _ b _ hab
      exact e.injective hab
    · intro k hk
      simp only [Set.mem_setOf_eq] at hk
      refine ⟨e.symm k, ?_, by simp⟩
      simp only [Set.mem_setOf_eq]
      rw [(he (e.symm k)).1, Equiv.apply_symm_apply, hk]
  · intro j _
    exact ((he j).2).symm
end

section -- restored from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PCoverOne
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.coverOne_of :
    CoverOne := by
  intro R _ F G f V b h
  have hd : ∀ (V' W : Scheme.{0}) (g : V' ⟶ V) (k : W ⟶ V'),
      (∃ a : Sec F V', Sec.map f a = Sec.res g b) → ∃ a : Sec F W, Sec.map f a = Sec.res (k ≫ g) b := by
    rintro V' W g k ⟨a, ha⟩
    exact ⟨Sec.res k a, by rw [map_res, ha, res_res]⟩
  have h2 := (GlobalTheory.T.etaleLocally_iff_affine_etale_point_cover V (fun W k => ∃ a : Sec F W, Sec.map f a = Sec.res k b) hd).1 h
  choose Wf k _ het hx a ha using h2
  obtain ⟨a', ha'⟩ := (GlobalTheory.T.sec_sigma_res_bijective R F Wf).2 a
  refine ⟨∐ Wf, Sigma.desc k, a', ?_, ?_, ?_⟩
  · have : IsZariskiLocalAtSource @Etale := HasRingHomProperty.instIsZariskiLocalAtSource
    exact IsZariskiLocalAtSource.sigmaDesc (P := @Etale) fun i => het i
  · refine ⟨fun x => ?_⟩
    obtain ⟨y, hy⟩ := hx x
    refine ⟨Sigma.ι Wf x y, ?_⟩
    rw [← Scheme.Hom.comp_apply, Sigma.ι_desc, hy]
  · refine (GlobalTheory.T.sec_sigma_res_bijective R G Wf).1 (funext fun i => ?_)
    show Sec.res (Sigma.ι Wf i) (Sec.map f a') = Sec.res (Sigma.ι Wf i) (Sec.res (Sigma.desc k) b)
    have e : Sec.res (Sigma.ι Wf i) a' = a i := congrFun ha' i
    rw [← map_res, e, ha, res_res, Sigma.ι_desc]
end

section -- restored from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PCycComp
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

open Classical in
private lemma cyc_eq_sum {S Y : Scheme.{0}} (c : Corr S Y) (Ω : Type) [Field Ω] [IsAlgClosed Ω]
    (x : gp Ω ⟶ S) (y : gp Ω ⟶ Y) (AF : Finset (gp Ω ⟶ c.Z)) (hAF : ∀ s, s ∈ AF ↔ s ≫ c.p = x) :
    c.cyc Ω x y = ∑ s ∈ AF with s ≫ c.f = y, c.w Ω s := by
  have hs : {z : gp Ω ⟶ c.Z | z ≫ c.p = x ∧ z ≫ c.f = y} = ↑(AF.filter (fun s => s ≫ c.f = y)) := by
    ext z
    simp [hAF]
  show (∑ᶠ (z : gp Ω ⟶ c.Z) (_ : z ∈ {z : gp Ω ⟶ c.Z | z ≫ c.p = x ∧ z ≫ c.f = y}), c.w Ω z) = _
  rw [hs, finsum_mem_coe_finset]

theorem UpperTheory.Gal.TranscendenceTraces.cycComp_of :
    FibFin → CycComp := by
  classical
  intro hF S Y X c d e a b pb hp hf hw Ω _ _ x y
  haveI := c.fin
  haveI := d.fin
  haveI := e.fin
  let A := (hF c.p Ω x).toFinset
  have hAm : ∀ s, s ∈ A ↔ s ≫ c.p = x := fun s => by simp [A, fib]
  let B : (gp Ω ⟶ Y) → Finset (gp Ω ⟶ d.Z) := fun t => (hF d.p Ω t).toFinset
  have hBm : ∀ t u, u ∈ B t ↔ u ≫ d.p = t := fun t u => by simp [B, fib]
  let E := (hF e.p Ω x).toFinset
  have hEm : ∀ z, z ∈ E ↔ z ≫ e.p = x := fun z => by simp [E, fib]
  have hR : (∑ᶠ t : gp Ω ⟶ Y, c.cyc Ω x t * d.cyc Ω t y) =
      ∑ s ∈ A, c.w Ω s * d.cyc Ω (s ≫ c.f) y := by
    rw [finsum_eq_sum_of_support_subset (s := A.image (· ≫ c.f))]
    · rw [← Finset.sum_fiberwise_of_maps_to (s := A) (t := A.image (· ≫ c.f)) (g := (· ≫ c.f))
          (fun s hs => Finset.mem_image_of_mem _ hs)]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [cyc_eq_sum c Ω x t A hAm, Finset.sum_mul]
      refine Finset.sum_congr rfl fun s hs => ?_
      rw [(Finset.mem_filter.1 hs).2]
    · intro t ht
      rw [Function.mem_support] at ht
      by_contra hn
      apply ht
      rw [cyc_eq_sum c Ω x t A hAm, Finset.sum_eq_zero, zero_mul]
      intro s hs
      exact absurd (Finset.mem_coe.2 (Finset.mem_image.2
        ⟨s, (Finset.mem_filter.1 hs).1, (Finset.mem_filter.1 hs).2⟩)) hn
  have hmaps : ∀ z ∈ E.filter (fun z => z ≫ e.f = y), z ≫ b ∈ A := by
    intro z hz
    rw [hAm, Category.assoc, ← hp]
    exact (hEm z).1 (Finset.mem_filter.1 hz).1
  rw [hR, cyc_eq_sum e Ω x y E hEm, ← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [cyc_eq_sum d Ω (s ≫ c.f) y (B (s ≫ c.f)) (hBm _), Finset.mul_sum]
  refine Finset.sum_bij' (fun z _ => z ≫ a)
    (fun u hu => pb.lift u s ((hBm _ u).1 (Finset.mem_filter.1 hu).1)) ?_ ?_ ?_ ?_ ?_
  · intro z hz
    simp only [Finset.mem_filter, hEm, hBm] at hz ⊢
    refine ⟨?_, ?_⟩
    · rw [Category.assoc, pb.w, ← Category.assoc, hz.2]
    · rw [Category.assoc, ← hf, hz.1.2]
  · intro u hu
    have hu' := Finset.mem_filter.1 hu
    simp only [Finset.mem_filter, hEm]
    refine ⟨⟨?_, ?_⟩, pb.lift_snd _ _ _⟩
    · rw [hp, ← Category.assoc, pb.lift_snd]
      exact (hAm s).1 hs
    · rw [hf, ← Category.assoc, pb.lift_fst]
      exact hu'.2
  · intro z hz
    have hz' := Finset.mem_filter.1 hz
    apply pb.hom_ext
    · rw [pb.lift_fst]
    · rw [pb.lift_snd, hz'.2]
  · intro u hu
    exact pb.lift_fst _ _ _
  · intro z hz
    have hz' := Finset.mem_filter.1 hz
    rw [hw]
    show d.w Ω (z ≫ a) * c.w Ω (z ≫ b) = c.w Ω s * d.w Ω (z ≫ a)
    rw [hz'.2, mul_comm]
end

section -- restored from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PDSLoc
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

private theorem DS_map_apply {R : Type} [CommRing R] {Z S : Scheme.{0}} (p : Z ⟶ S) {G G' : Shv R} (f : G ⟶ G')
    (U : Scheme.{0}) (x : DS p G U) (u : U ⟶ S) :
    (DS.map p f U x) u = Sec.map f (x u) := by
  classical
  induction x using DirectSum.induction_on with
  | zero => simp [Sec.map]
  | of v a =>
    have h := DS.map_inc p f v a
    simp only [inc, DirectSum.lof_eq_of] at h
    rw [h]
    by_cases hv : v = u
    · subst hv
      simp [DirectSum.of_eq_same]
    · rw [DirectSum.of_eq_of_ne _ _ _ (Ne.symm hv), DirectSum.of_eq_of_ne _ _ _ (Ne.symm hv)]
      simp [Sec.map]
  | add x y hx hy => simp [map_add (f := _), hx, hy, Sec.map]

theorem UpperTheory.Gal.TranscendenceTraces.dSLoc_of :
    DSOne → DSLoc := by
  intro h1 R _ Z S p _ T hT U x hx
  classical
  have hz : ∀ u, Sec.map T.g (x u) = 0 := by
    intro u
    rw [← DS_map_apply, hx]
    rfl
  have hL := (GlobalTheory.T.etaleLocal_property_calculus_rules).2.2.2.2.2.1 U x.support
    (fun i V g => ∃ a, DS.map p T.f V a = DS.res p T.X₂ g (inc p T.X₂ i.1 (x i.1)))
    (fun i => h1 R p T hT U i.1 (x i.1) (hz i.1))
  refine (GlobalTheory.T.etaleLocal_property_calculus_rules).2.1 U _ _ hL ?_
  intro V g hg
  choose a ha using hg
  refine ⟨∑ i : x.support, a i, ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  simp only [ha]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← map_sum]
  congr 1
  conv_rhs => rw [← DirectSum.sum_support_of x]
  simp only [inc, DirectSum.lof_eq_of]
  exact Finset.sum_coe_sort x.support (fun i => DirectSum.of (fun i => Sec T.X₂ (pullback p i)) i (x i))
end

section -- restored from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PDSOne
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.dSOne_of :
    LocFinSec → DSOne := by
  intro hL R _ Z S p _ T hT U u b hb
  obtain ⟨-, hmono, -, -, -, -, -⟩ := GlobalTheory.T.etaleLocal_property_calculus_rules
  have h1 := (GlobalTheory.T.etaleSheaf_shortComplex_exact_iff_locally R T).1 hT (pullback p u) b hb
  have h2 := hL R T.f (pullback.snd p u) b h1
  apply hmono _ _ _ h2
  intro U' g hg
  obtain ⟨a, ha⟩ := hg (pullback p (g ≫ u)) (pbm p g u (g ≫ u) rfl) (pullback.snd p (g ≫ u))
    (pbm_snd p g u (g ≫ u) rfl)
  refine ⟨inc p T.X₁ (g ≫ u) a, ?_⟩
  rw [DS.map_inc, ha, DS.res_inc p T.X₂ g u (g ≫ u) rfl]
end

section -- restored from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PFamBC
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.famBC_of :
    FamBC := by
  intro q i Z' S' Z S v p' p g w h τ hτ
  let push : Sq p' → Sq p := fun A =>
    { U := A.U, V := A.V, u := A.u ≫ g, v := A.v ≫ v, r := A.r,
      pb := A.pb.paste_horiz h }
  let pushTo : ∀ {A B : Sq p'}, A.To B → (push A).To (push B) := fun {A B} t =>
    { g := t.g, k := t.k,
      hu := by simp only [push, ← Category.assoc, t.hu],
      hv := by simp only [push, ← Category.assoc, t.hv],
      hr := t.hr }
  let τ' : Fam p' (res (ZMod q) (tw q i)) (res (ZMod q) (tw q i)) :=
    { deg := fun s =>
        { app := fun A => (τ.deg s).app (push A),
          nat := fun {A B} t a => (τ.deg s).nat (pushTo t) a },
      comm := fun A s t a => τ.comm (push A) s t a }
  refine ⟨τ', ?_, ?_⟩
  · intro A a
    obtain ⟨b, hb1, hb2⟩ := hτ (push A) a
    refine ⟨b, hb1, ?_⟩
    intro Ω _ _ x
    have := hb2 Ω x
    simpa only [IsSum, Wt.comap, push, Category.assoc] using this
  · intro n a
    let t : (push (Sq.self p')).To (Sq.self p) :=
      { g := g, k := v,
        hu := by simp [push, Sq.self],
        hv := by simp [push, Sq.self],
        hr := by simpa [push, Sq.self] using h.w }
    exact ((τ.deg n).nat t a).symm
end

section -- restored from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PFamSemi
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.famSemi_of :
    FamSemi := by
  intro Z S p R₁ R₂ R₃ _ _ _ I J K
  refine ⟨fun τ ρ => ?_, fun ρ τ => ?_⟩
  · refine ⟨⟨fun s => ⟨fun A => (ρ.app A.U s).comp ((τ.deg s).app A), ?_⟩, ?_⟩, fun _ _ _ => rfl⟩
    · intro A B t a
      change Sec.res t.g (ρ.app B.U s ((τ.deg s).app B a)) = ρ.app A.U s ((τ.deg s).app A (Sec.res t.k a))
      rw [ρ.nat t.g s, (τ.deg s).nat t a]
    · intro A s t a
      change Sec.map (K.d s t) (ρ.app A.U s ((τ.deg s).app A a)) =
        ρ.app A.U t ((τ.deg t).app A (Sec.map (I.d s t) a))
      rw [ρ.comm A.U s t, τ.comm A s t a]
  · refine ⟨⟨fun s => ⟨fun A => ((τ.deg s).app A).comp (ρ.app A.V s), ?_⟩, ?_⟩, fun _ _ _ => rfl⟩
    · intro A B t a
      change Sec.res t.g ((τ.deg s).app B (ρ.app B.V s a)) = (τ.deg s).app A (ρ.app A.V s (Sec.res t.k a))
      rw [(τ.deg s).nat t, ρ.nat t.k s]
    · intro A s t a
      change Sec.map (K.d s t) ((τ.deg s).app A (ρ.app A.V s a)) =
        (τ.deg t).app A (ρ.app A.V t (Sec.map (I.d s t) a))
      rw [τ.comm A s t, ρ.comm A.V s t]
end

section -- restored from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PImageFin
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

set_option backward.isDefEq.respectTransparency false in
private theorem isFinite_sigma_desc_of_finite (ι : Type) [Finite ι] :
    ∀ {S : Scheme.{0}} (Z : ι → Scheme.{0}) (p : ∀ a, Z a ⟶ S), (∀ a, IsFinite (p a)) →
      IsFinite (Sigma.desc p) := by
  induction ι using Finite.induction_empty_option with
  | of_equiv e ih =>
    intro S Z p hp
    have := ih (fun a => Z (e a)) (fun a => p (e a)) (fun a => hp _)
    let i : (∐ fun a => Z (e a)) ≅ ∐ Z := Sigma.whiskerEquiv e (fun _ => Iso.refl _)
    have h : i.hom ≫ Sigma.desc p = Sigma.desc (fun a => p (e a)) := by
      apply Sigma.hom_ext
      intro a
      simp [i]
    have h' : Sigma.desc p = i.inv ≫ Sigma.desc (fun a => p (e a)) := by
      rw [← h, Iso.inv_hom_id_assoc]
    rw [h']
    infer_instance
  | h_empty =>
    intro S Z p hp
    have : IsEmpty (∐ Z : Scheme.{0}) := ⟨fun x => by
      obtain ⟨i, _, _⟩ := (sigmaOpenCover Z).exists_eq x
      exact i.elim⟩
    infer_instance
  | h_option ih =>
    intro S Z p hp
    have h1 := ih (fun a => Z (some a)) (fun a => p (some a)) (fun a => hp _)
    have h0 := hp none
    let i : (Z none ⨿ ∐ fun a => Z (some a)) ≅ ∐ Z :=
      { hom := coprod.desc (Sigma.ι Z none) (Sigma.desc fun a => Sigma.ι Z (some a))
        inv := Sigma.desc fun o => match o with
          | none => coprod.inl
          | some a => Sigma.ι (fun a => Z (some a)) a ≫ coprod.inr
        hom_inv_id := by
          apply coprod.hom_ext
          · simp
          · apply Sigma.hom_ext
            intro a
            simp
        inv_hom_id := by
          apply Sigma.hom_ext
          rintro (_ | a) <;> simp }
    have h : i.hom ≫ Sigma.desc p = coprod.desc (p none) (Sigma.desc fun a => p (some a)) := by
      apply coprod.hom_ext
      · simp [i]
      · apply Sigma.hom_ext
        intro a
        simp [i]
    have h' : Sigma.desc p = i.inv ≫ coprod.desc (p none) (Sigma.desc fun a => p (some a)) := by
      rw [← h, Iso.inv_hom_id_assoc]
    have c : IsFinite (coprod.desc (p none) (Sigma.desc fun a => p (some a))) := inferInstance
    have d0 : IsIso i.inv := ⟨i.hom, i.inv_hom_id, i.hom_inv_id⟩
    have d : IsFinite i.inv := inferInstance
    rw [h']
    infer_instance

set_option backward.isDefEq.respectTransparency false in
theorem UpperTheory.Gal.TranscendenceTraces.imageFin_of :
    ImageOne → ImageFin := by
  intro hOne S Y B bS bY _ _ ι _ Z p f hp hf
  have hk : (Sigma.desc fun a => pullback.lift (f a) (p a) (hf a)) ≫ pullback.snd bY bS = Sigma.desc p := by
    apply Sigma.hom_ext
    intro a
    simp
  obtain ⟨k, hkdef⟩ : ∃ k : ∐ Z ⟶ pullback bY bS, k = Sigma.desc fun a => pullback.lift (f a) (p a) (hf a) := ⟨_, rfl⟩
  rw [← hkdef] at hk
  have hι : ∀ a, Sigma.ι Z a ≫ k = pullback.lift (f a) (p a) (hf a) := by
    intro a
    simp [hkdef]
  have hfin : IsFinite (k ≫ pullback.snd bY bS) := by
    rw [hk]
    exact isFinite_sigma_desc_of_finite ι Z p hp
  obtain ⟨h1, h2⟩ := hOne k (pullback.snd bY bS)
  have hh : ∀ a, (Sigma.ι Z a ≫ k.toImage) ≫ k.imageι = pullback.lift (f a) (p a) (hf a) := by
    intro a
    rw [Category.assoc, Scheme.Hom.toImage_imageι, hι]
  have hpa : ∀ a, (Sigma.ι Z a ≫ k.toImage) ≫ k.imageι ≫ pullback.snd bY bS = p a := by
    intro a
    rw [← Category.assoc, hh, pullback.lift_snd]
  have hfa : ∀ a, (Sigma.ι Z a ≫ k.toImage) ≫ k.imageι ≫ pullback.fst bY bS = f a := by
    intro a
    rw [← Category.assoc, hh, pullback.lift_fst]
  refine ⟨k.image, k.imageι ≫ pullback.snd bY bS, k.imageι ≫ pullback.fst bY bS,
    fun a => Sigma.ι Z a ≫ k.toImage, h1, fun a => ?_, hpa, hfa, ?_⟩
  · have : IsFinite ((Sigma.ι Z a ≫ k.toImage) ≫ k.imageι ≫ pullback.snd bY bS) := by
      rw [hpa]
      exact hp a
    exact IsFinite.of_comp _ (k.imageι ≫ pullback.snd bY bS)
  · intro T x y hs hf'
    rw [← cancel_mono k.imageι]
    apply pullback.hom_ext
    · simpa using hf'
    · simpa using hs
end

section -- restored from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PImageOne
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.imageOne_of :
    ImageOne := by
  intro Z P S k b _ _ _
  have hk : IsFinite k := IsFinite.of_comp k b
  have ht : IsFinite k.toImage := by
    have : IsFinite (k.toImage ≫ k.imageι) := by rw [k.toImage_imageι]; exact hk
    exact IsFinite.of_comp k.toImage k.imageι
  have hs : Surjective k.toImage :=
     surjective_of_isDominant_of_isClosed_range k.toImage k.toImage.isClosedMap.isClosed_range
  have e : k.toImage ≫ (k.imageι ≫ b) = k ≫ b := k.toImage_imageι_assoc b
  have huc : UniversallyClosed (k.imageι ≫ b) := by
    have : UniversallyClosed (k.toImage ≫ (k.imageι ≫ b)) := by rw [e]; infer_instance
    exact UniversallyClosed.of_comp_surjective k.toImage _
  have hqf : LocallyQuasiFinite (k.imageι ≫ b) := by
    refine .of_finite_preimage_singleton _ fun s => ?_
    refine (((k ≫ b).finite_preimage_singleton s).image k.toImage).subset ?_
    intro y hy
    obtain ⟨x, rfl⟩ := k.toImage.surjective y
    refine ⟨x, ?_, rfl⟩
    have : (k ≫ b) x = (k.imageι ≫ b) (k.toImage x) := by
      rw [← e, Scheme.Hom.comp_apply]
    exact this.trans hy
  have : IsProper (k.imageι ≫ b) := ⟨⟩
  exact ⟨IsFinite.of_isProper_of_locallyQuasiFinite _, ht⟩
end

section -- restored from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PIsolate
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.isolate_of :
    Chart → IsolateSpec → Isolate := by
  intro hC hI Z S p _ z
  have hmem : p z ∈ (⊤ : S.Opens) := trivial
  obtain ⟨U, hU0, hzU, -⟩ :=
    (TopologicalSpace.Opens.isBasis_iff_nbhd.mp S.isBasis_affineOpens) hmem
  have hU : IsAffineOpen U := hU0
  let u0 : Spec (CommRingCat.of Γ(S, U)) ⟶ S := hU.isoSpec.inv ≫ Scheme.Opens.ι U
  obtain ⟨B, iB, iAB, v0, hfin, hpb⟩ := hC p Γ(S, U) u0
  haveI := hfin
  obtain ⟨y, hy⟩ : ∃ y : (U : Scheme), Scheme.Opens.ι U y = p z := ⟨⟨p z, hzU⟩, rfl⟩
  have ha : u0 (hU.isoSpec.hom y) = p z := by
    show (hU.isoSpec.hom ≫ hU.isoSpec.inv ≫ Scheme.Opens.ι U) y = p z
    rw [Iso.hom_inv_id_assoc, hy]
  obtain ⟨w0, hw1, hw2⟩ := Scheme.Pullback.exists_preimage_pullback (f := p) (g := u0) z _ ha.symm
  have hw : v0 (hpb.isoPullback.inv w0) = z := by
    rw [← Scheme.Hom.comp_apply, hpb.isoPullback_inv_fst, hw1]
  obtain ⟨A', W, v, hEt, hW, hvW, hvv, hiso⟩ := hI Γ(S, U) B (hpb.isoPullback.inv w0)
  haveI := hEt
  refine ⟨⟨A'.U, A'.V, A'.u ≫ u0, A'.v ≫ v0, A'.r, A'.pb.paste_horiz hpb⟩, W, v, ?_, hW, hvW, ?_, hiso⟩
  · show Etale (A'.u ≫ u0)
    infer_instance
  · show (A'.v ≫ v0) v = z
    rw [Scheme.Hom.comp_apply, hvv, hw]
end

section -- restored from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PIsolateSpec
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.isolateSpec_of :
    IsolateSpec := by
  intro R B _ _ _ _ z
  let z' : PrimeSpectrum B := z
  haveI : z'.asIdeal.IsPrime := z'.isPrime
  haveI : Algebra.QuasiFiniteAt R z'.asIdeal := inferInstance
  obtain ⟨R', _, _, hEt, P, _, _, e, he, P', hP', hlo, hq, heP, -, -, huniq⟩ :=
    Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq (z'.asIdeal.under R) z'.asIdeal
  have pb := (isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_tensorProduct R R' B)).flip
  refine ⟨⟨Spec (CommRingCat.of R'), Spec (CommRingCat.of (TensorProduct R R' B)), _, _, _, pb⟩,
    ((PrimeSpectrum.basicOpen e : TopologicalSpace.Opens (PrimeSpectrum (TensorProduct R R' B))) :
      Set (PrimeSpectrum (TensorProduct R R' B))),
    (⟨P', hP'⟩ : PrimeSpectrum (TensorProduct R R' B)), ?_, ?_, ?_, ?_, ?_⟩
  · exact HasRingHomProperty.Spec_iff.mpr (RingHom.etale_algebraMap.mpr hEt)
  · exact PrimeSpectrum.isClopen_iff.mpr ⟨e, he, rfl⟩
  · exact heP
  · apply PrimeSpectrum.ext
    exact hq
  · intro v' hv' hr
    have h1 : (v' : PrimeSpectrum (TensorProduct R R' B)).asIdeal.LiesOver P := by
      constructor
      have h2 : Ideal.comap (algebraMap R' (TensorProduct R R' B))
          (v' : PrimeSpectrum (TensorProduct R R' B)).asIdeal =
          Ideal.comap (algebraMap R' (TensorProduct R R' B)) P' :=
        congrArg PrimeSpectrum.asIdeal hr
      rw [Ideal.under, h2]
      exact hlo.over
    apply PrimeSpectrum.ext
    exact huniq _ (PrimeSpectrum.isPrime _) h1 hv'
end

section -- restored from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PLocFinAff
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces
open scoped TensorProduct

theorem UpperTheory.Gal.TranscendenceTraces.locFinAff_of :
    Chart → RingSplit → LocFinAff := by
  intro hC hR W V U _ π r _ _ _ x
  let A := Γ(U, ⊤)
  let u : Spec (CommRingCat.of A) ⟶ U := U.isoSpec.inv
  obtain ⟨B, _, _, v, _, hpb⟩ := hC r A u
  haveI : IsIso v := hpb.isIso_fst_of_isIso
  let f : W ⟶ Spec (CommRingCat.of B) := π ≫ inv v
  obtain ⟨C, g, h, hg, hh⟩ := GlobalTheory.T.exists_etaleFaithfullyFlat_refining_etale_surjection (CommRingCat.of B) W f inferInstance inferInstance
  letI : Algebra B C := g.hom.toAlgebra
  haveI : Algebra.Etale B C := hg.1
  haveI : Module.FaithfullyFlat B C := hg.2
  let P : PrimeSpectrum A := U.isoSpec.hom x
  obtain ⟨E, _, _, hE, ⟨Q, hQ⟩, ⟨φ⟩⟩ := hR A B C P
  let gE : Spec (CommRingCat.of E) ⟶ U := Spec.map (CommRingCat.ofHom (algebraMap A E)) ≫ u
  haveI : Etale (Spec.map (CommRingCat.ofHom (algebraMap A E))) :=
    HasRingHomProperty.Spec_iff.mpr (RingHom.etale_algebraMap.mpr hE)
  have big := (isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct A B E)).paste_horiz hpb
  have hhπ : h ≫ π = Spec.map g ≫ v := by
    rw [← hh]
    simp [f]
  refine ⟨Spec (CommRingCat.of E), gE, inferInstance, inferInstance, ⟨Q, ?_⟩, ?_⟩
  · change u (Spec.map (CommRingCat.ofHom (algebraMap A E)) Q) = x
    have e : Spec.map (CommRingCat.ofHom (algebraMap A E)) Q = P := hQ
    rw [e]
    show U.isoSpec.inv (U.isoSpec.hom x) = x
    rw [← Scheme.Hom.comp_apply, Iso.hom_inv_id]
    rfl
  · refine ⟨big.lift (pullback.fst r gE) (pullback.snd r gE) pullback.condition ≫
      Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ h, ?_⟩
    have eφ : g ≫ CommRingCat.ofHom φ.toRingHom = CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom := by
      ext b
      exact φ.commutes b
    rw [Category.assoc, Category.assoc, hhπ, ← Category.assoc (Spec.map _) (Spec.map g) v, ← Spec.map_comp, eφ]
    exact big.lift_fst _ _ _
end

section -- restored from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PLocFinGeo
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.locFinGeo_of :
    LocFinAff → LocFinGeo := by
  intro hA W V U π r _ _ _
  rw [GlobalTheory.T.etaleLocally_iff_affine_etale_point_cover U (fun V' g ↦ ∃ s, s ≫ π = pullback.fst r g)]
  swap
  · rintro V' W' g k ⟨s, hs⟩
    refine ⟨pullback.lift (pullback.fst r (k ≫ g)) (pullback.snd r (k ≫ g) ≫ k)
      (by simp [pullback.condition]) ≫ s, ?_⟩
    rw [Category.assoc, hs, pullback.lift_fst]
  intro x
  obtain ⟨y, hy⟩ := U.affineCover.covers x
  set ι := U.affineCover.f (U.affineCover.idx x) with hι
  obtain ⟨U', g, hU', hg, ⟨z, hz⟩, s, hs⟩ :=
    hA (pullback.snd π (pullback.fst r ι)) (pullback.snd r ι) y
  refine ⟨U', g ≫ ι, hU', inferInstance, ⟨z, by simp [hz, hy]⟩, ?_⟩
  let φ : pullback r (g ≫ ι) ⟶ pullback (pullback.snd r ι) g :=
    pullback.lift (pullback.lift (pullback.fst r (g ≫ ι)) (pullback.snd r (g ≫ ι) ≫ g)
      (by rw [Category.assoc, ← pullback.condition]))
      (pullback.snd r (g ≫ ι)) (pullback.lift_snd _ _ _)
  refine ⟨φ ≫ s ≫ pullback.fst π (pullback.fst r ι), ?_⟩
  rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc s, hs]
  dsimp only [φ]
  rw [← Category.assoc, pullback.lift_fst, pullback.lift_fst]
end

section -- restored from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PLocFinSec
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.locFinSec_of :
    CoverOne → LocFinGeo → LocFinSec := by
  intro hC hG R _ F G f V U r _ b hb
  obtain ⟨W, π, a, hE, hS, ha⟩ := hC R f V b hb
  haveI := hE
  haveI := hS
  refine (GlobalTheory.T.etaleLocal_property_calculus_rules).2.1 U _ _ (hG π r) ?_
  rintro U' g ⟨s, hs⟩ V' k r' hk
  refine ⟨Sec.res (pullback.lift k r' hk ≫ s) a, ?_⟩
  rw [map_res, ha, res_res]
  congr 1
  rw [Category.assoc, hs, pullback.lift_fst]
end

section -- restored from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PMultBasic
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.multBasic_of :
    MultBC → MultOpen → MultEt → MultBasic := by
  intro h1 h2 h3
  exact ⟨h1, h2, h3⟩
end

section -- restored from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PMultSum
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.multSum_of :
    MultSumPt → MultBC → MultSum := by
  intro hPt hBC Z S p _ _ Ω _ _ x
  have hpb : IsPullback (pullback.fst p x) (pullback.snd p x) p x := IsPullback.of_hasPullback p x
  have hfin := Scheme.Hom.finrank_of_isPullback _ _ _ _ hpb (IsLocalRing.closedPoint Ω)
  have h1 := hPt Ω (pullback.snd p x)
  rw [hBC _ _ _ _ hpb] at h1
  rw [show pt x = x (IsLocalRing.closedPoint Ω) from rfl, ← hfin, ← h1]
  simp only [Wt.push, Wt.comap]
  have hb := fib_bijOn hpb (Ω := Ω) (𝟙 _)
  rw [Category.id_comp] at hb
  exact (finsum_mem_eq_of_bijOn _ hb (fun _ _ => rfl)).symm
end

section -- restored from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PNmlLoc
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.nmlLoc_of :
    NmlInt → NmlNoeth → NmlLoc := by
  intro hI hN S hS h
  rcases h with h | h
  · haveI := h
    exact hI S hS
  · haveI := h
    exact hN S hS
end

section -- restored from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PNmlNoeth
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

private theorem exists_open_irreducible_nhds_of_generizations {Y : Type*} [TopologicalSpace Y] [QuasiSober Y]
    [TopologicalSpace.NoetherianSpace Y] (y : Y) (hG : IsIrreducible {z | z ⤳ y}) :
    ∃ U : Set Y, IsOpen U ∧ y ∈ U ∧ IsIrreducible U := by
  have key : ∀ W ∈ irreducibleComponents Y, y ∈ W → W = closure {z | z ⤳ y} := by
    intro W hW hyW
    have hWc : IsClosed W := isClosed_of_mem_irreducibleComponents W hW
    have hgen := hW.1.isGenericPoint_genericPoint_closure
    rw [hWc.closure_eq] at hgen
    have hcl : closure {hW.1.genericPoint} = W := hgen
    have hsub : W ⊆ closure {z | z ⤳ y} := by
      rw [← hcl]
      exact closure_mono (Set.singleton_subset_iff.mpr (hgen.specializes hyW))
    exact le_antisymm hsub (hW.2 hG.closure hsub)
  let C := irreducibleComponent y
  refine ⟨(⋃₀ (irreducibleComponents Y \ {C}))ᶜ, ?_, ?_, ?_⟩
  · rw [Set.sUnion_eq_biUnion, isOpen_compl_iff]
    exact TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.sdiff.isClosed_biUnion
      fun W hW ↦ isClosed_of_mem_irreducibleComponents W hW.1
  · simp only [Set.mem_compl_iff, Set.mem_sUnion, Set.mem_diff, Set.mem_singleton_iff,
      not_exists, not_and, and_imp]
    intro W hW hne hyW
    exact hne ((key W hW hyW).trans (key C (irreducibleComponent_mem_irreducibleComponents y)
      mem_irreducibleComponent).symm)
  · apply isIrreducible_iff_closure.mp
    rw [closure_sUnion_irreducibleComponents_sdiff_singleton
      TopologicalSpace.NoetherianSpace.finite_irreducibleComponents _
      (irreducibleComponent_mem_irreducibleComponents y)]
    exact isIrreducible_irreducibleComponent

private theorem isIntegrallyClosed_affine_of_stalks {X : Scheme} {U : X.Opens} (hU : IsAffineOpen U)
    [IsDomain Γ(X, U)] (h : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) :
    IsIntegrallyClosed Γ(X, U) := by
  refine IsIntegrallyClosed.of_localization_maximal fun p _ hp => ?_
  let y : PrimeSpectrum Γ(X, U) := ⟨p, hp.isPrime⟩
  have hy : hU.fromSpec y ∈ U := hU.range_fromSpec.le ⟨y, rfl⟩
  letI : Algebra Γ(X, U) (X.presheaf.stalk (hU.fromSpec y)) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨hU.fromSpec y, hy⟩
  haveI : IsLocalization y.asIdeal.primeCompl (X.presheaf.stalk (hU.fromSpec y)) :=
    hU.isLocalization_stalk' y hy
  change IsIntegrallyClosed (Localization.AtPrime y.asIdeal)
  exact (h _).of_equiv (IsLocalization.algEquiv y.asIdeal.primeCompl
    (X.presheaf.stalk (hU.fromSpec y)) (Localization.AtPrime y.asIdeal)).toRingEquiv

theorem UpperTheory.Gal.TranscendenceTraces.nmlNoeth_of :
    NmlNoeth := by
  intro S _ hN x
  haveI : ∀ z : S, IsDomain (S.presheaf.stalk z) := fun z => (hN z).1
  obtain ⟨_, ⟨V : S.Opens, hV, rfl⟩, hxV, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  haveI : CompactSpace V.toScheme := isCompact_iff_compactSpace.mp hV.isCompact
  haveI : IsNoetherian V.toScheme := {}
  have hns : TopologicalSpace.NoetherianSpace V.toScheme := inferInstance
  have hqs : QuasiSober V.toScheme := inferInstance
  have hG : IsIrreducible {z | z ⤳ x} := by
    rw [← Scheme.range_fromSpecStalk]
    haveI : IrreducibleSpace (Spec (S.presheaf.stalk x)) := PrimeSpectrum.irreducibleSpace
    rw [← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ _).image _
      (S.fromSpecStalk x).continuous.continuousOn
  have hGV : {z | z ⤳ x} ⊆ (V : Set S) := fun z hz => hz.mem_open V.isOpen hxV
  have hG' : IsIrreducible {z : V | z ⤳ ⟨x, hxV⟩} := by
    have he : {z : V | z ⤳ ⟨x, hxV⟩} =
        Set.range (fun z : {z | z ⤳ x} => (⟨z.1, hGV z.2⟩ : V)) := by
      ext z
      constructor
      · intro hz
        exact ⟨⟨z.1, (Topology.IsInducing.subtypeVal.specializes_iff).mpr hz⟩, rfl⟩
      · rintro ⟨w, rfl⟩
        exact (Topology.IsInducing.subtypeVal.specializes_iff).mp w.2
    rw [he, ← Set.image_univ]
    haveI : IrreducibleSpace {z | z ⤳ x} := isIrreducible_iff_irreducibleSpace.mp hG
    exact (IrreducibleSpace.isIrreducible_univ _).image _
      (by fun_prop : Continuous _).continuousOn
  obtain ⟨W, hWo, hxW, hWi⟩ := @exists_open_irreducible_nhds_of_generizations V.toScheme _ hqs hns ⟨x, hxV⟩ hG'
  have hW'o : IsOpen (Subtype.val '' W : Set S) := V.isOpen.isOpenMap_subtype_val W hWo
  obtain ⟨_, ⟨U : S.Opens, hU, rfl⟩, hxU, hUW⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (⟨_, hxW, rfl⟩ : x ∈ Subtype.val '' W) hW'o
  have hUi : IsIrreducible (U : Set S) :=
    ⟨⟨x, hxU⟩, (hWi.image _ continuous_subtype_val.continuousOn).2.open_subset U.isOpen hUW⟩
  haveI : IrreducibleSpace U := isIrreducible_iff_irreducibleSpace.mp hUi
  haveI : IsReduced S := isReduced_of_isReduced_stalk S
  haveI : IsIntegral U.toScheme := isIntegral_of_irreducibleSpace_of_isReduced _
  haveI : Nonempty (⊤ : U.toScheme.Opens) := ⟨⟨⟨x, hxU⟩, trivial⟩⟩
  haveI : IsDomain Γ(S, U) :=
    MulEquiv.isDomain Γ(U.toScheme, ⊤) (U.topIso).commRingCatIsoToRingEquiv.symm.toMulEquiv
  exact ⟨U, hU, hxU, inferInstance, isIntegrallyClosed_affine_of_stalks hU fun z => (hN z).2⟩
end

section -- restored from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PNormAff
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.normAff_of :
    Chart → NormSpec → NormAff := by
  intro hC hN Z S p _ U hU hD hI
  obtain ⟨B, _, _, v, hfin, hpb⟩ := hC p Γ(S, U) hU.fromSpec
  obtain ⟨w, hw⟩ := hN Γ(S, U) B
  exact ⟨⟨_, _, hU.fromSpec, v, _, hpb⟩, w, inferInstance, hU.range_fromSpec, hw⟩
end

section -- restored from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PNwtOfFlat
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.nwtOfFlat_of :
    WtFlat → WtUnique → GenBasic → NwtOfFlat := by
  intro hW hU hG Z S p _ _ _
  have hm : IsNwt p (mult p) := ⟨hW p, fun _ _ _ _ _ => rfl⟩
  have hex : ∃ w, IsNwt p w := ⟨mult p, hm⟩
  have hspec : IsNwt p hex.choose := hex.choose_spec
  have hval : nwt p = hex.choose := by
    unfold nwt
    rw [dite_eq_left hex]
  rw [hval]
  refine hU p _ _ hspec.1 hm.1 {s | GenPt s} (hG.1 S) ?_
  intro Ω _ _ z hz
  exact hspec.2 Ω z hz
end

section -- restored from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PNwtOpen
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.nwtOpen_of :
    WtBC → MultBC → GenBasic → NwtOpen := by
  intro hw hm hg Z S p w A _ hp
  obtain ⟨hwt, hgen⟩ := hp
  refine ⟨hw A.v A.r p A.u w A.pb hwt, ?_⟩
  intro Ω _ _ z hz
  have hsq : (z ≫ A.v) ≫ p = (z ≫ A.r) ≫ A.u := by
    rw [Category.assoc, Category.assoc, A.pb.w]
  have hz' : GenPt (pt ((z ≫ A.v) ≫ p)) := by
    rw [hsq, pt_comp]
    exact (hg.2.1 A.u (pt (z ≫ A.r))).mpr hz
  rw [hm A.v A.r p A.u A.pb]
  exact hgen Ω (z ≫ A.v) hz'
end

section -- restored from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PPhiExact
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

private theorem ds_res_map_comm {R : Type} [CommRing R] {Z S : Scheme} (p : Z ⟶ S) {G G' : Shv R}
    (f : G ⟶ G') {W V : Scheme} (k : W ⟶ V) (x : DS p G V) :
    DS.res p G' k (DS.map p f V x) = DS.map p f W (DS.res p G k x) := by
  have h := congrArg (fun φ => ModuleCat.Hom.hom φ x) (((phiPF p R).map f).naturality k.op)
  simp only [phiPF, phiP, ModuleCat.hom_comp, ModuleCat.hom_ofHom] at h
  exact h.symm

theorem UpperTheory.Gal.TranscendenceTraces.phiExact_of :
    DSLoc → PhiExact := by
  intro hD R _ Z S p _ T hT
  obtain ⟨-, hmono, -, -, hloc, -, -⟩ := GlobalTheory.T.etaleLocal_property_calculus_rules
  rw [GlobalTheory.T.etaleSheaf_shortComplex_exact_iff_locally]
  intro U b hb
  change Sec ((phi p R).obj T.X₂) U at b
  change Sec.map ((phi p R).map T.g) b = 0 at hb
  have h1 := (GlobalTheory.T.etaleToSheafify_locally_bijective_and_lift R (phiP p T.X₂)).1 U b
  apply hloc
  apply hmono _ _ _ h1
  rintro V g ⟨x0, hx0⟩
  obtain ⟨x, hx⟩ : ∃ x : DS p T.X₂ V, phiSec p T.X₂ V x = Sec.res g b := ⟨x0, hx0⟩
  have hz : phiSec p T.X₃ V (DS.map p T.g V x) = 0 := by
    rw [← phiSec_map, hx, map_res, hb]
    exact map_zero _
  have h2 := (GlobalTheory.T.etaleToSheafify_locally_bijective_and_lift R (phiP p T.X₃)).2.1 V _ hz
  apply hloc
  apply hmono _ _ _ h2
  intro W k hk
  have hk' : DS.res p T.X₃ k (DS.map p T.g V x) = 0 := hk
  have h0 : DS.map p T.g W (DS.res p T.X₂ k x) = 0 := by
    rw [← ds_res_map_comm]
    exact hk'
  apply hmono _ _ _ (hD R p T hT W (DS.res p T.X₂ k x) h0)
  rintro W' k' ⟨a, ha⟩
  refine ⟨phiSec p T.X₁ W' a, ?_⟩
  change Sec.map ((phi p R).map T.f) (phiSec p T.X₁ W' a) = Sec.res ((k' ≫ k) ≫ g) b
  rw [phiSec_map, ha, ← phiSec_res, ← phiSec_res, hx]
  exact (res_res k' k (Sec.res g b)).trans (res_res (k' ≫ k) g b)
end

section -- restored from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PPhiEx
namespace UpperTheory.Gal.TranscendenceTraces

theorem phiEx_of : LocFinSec → PhiEx := fun h => phiEx_of_parts phiUniv_of (phiExact_of (dSLoc_of (dSOne_of h)))

end UpperTheory.Gal.TranscendenceTraces
end

section -- restored from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PPtCommon
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.ptCommon_of :
    PtCommon := by
  intro X Ω Ω' _ _ z z' h
  have key : ∀ (K : Type) [Field K] (w : gp K ⟶ X) (y : X), pt w = y →
      ∃ ψ : X.residueField y ⟶ CommRingCat.of K, w = Spec.map ψ ≫ X.fromSpecResidueField y := by
    intro K _ w y hy
    subst hy
    exact ⟨_, (Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K X w).symm⟩
  obtain ⟨x, hx⟩ : ∃ x, pt z = x := ⟨_, rfl⟩
  obtain ⟨φ, hφ⟩ := key Ω z x hx
  obtain ⟨φ', hφ'⟩ := key Ω' z' x (h.symm.trans hx)
  have i1 : Function.Injective φ.hom := φ.hom.injective
  have i2 : Function.Injective φ'.hom := φ'.hom.injective
  letI := φ.hom.toAlgebra
  letI := φ'.hom.toAlgebra
  haveI : Nontrivial (TensorProduct (X.residueField x) Ω Ω') :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain _ _ _ i1 i2
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (TensorProduct (X.residueField x) Ω Ω')
  letI := Ideal.Quotient.field M
  let ψ : TensorProduct (X.residueField x) Ω Ω' →+* AlgebraicClosure (TensorProduct (X.residueField x) Ω Ω' ⧸ M) :=
    (algebraMap _ _).comp (Ideal.Quotient.mk M)
  have e1 : ∀ c, (φ.hom c ⊗ₜ[X.residueField x] (1 : Ω') : TensorProduct (X.residueField x) Ω Ω') =
      (1 : Ω) ⊗ₜ (φ'.hom c) := by
    intro c
    change algebraMap _ Ω c ⊗ₜ _ = _ ⊗ₜ algebraMap _ Ω' c
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  refine ⟨AlgebraicClosure (TensorProduct (X.residueField x) Ω Ω' ⧸ M), inferInstance, inferInstance,
    Spec.map (CommRingCat.ofHom (ψ.comp Algebra.TensorProduct.includeLeftRingHom)),
    Spec.map (CommRingCat.ofHom (ψ.comp (Algebra.TensorProduct.includeRight :
      Ω' →ₐ[X.residueField x] TensorProduct (X.residueField x) Ω Ω').toRingHom)), ?_⟩
  rw [hφ, hφ', ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
  congr 2
  ext c
  simp [e1]
end

section -- restored from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PRedZero
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.redZero_of :
    RedZero := by
  intro Q q _ _ hqQ i
  obtain ⟨f, hf_nat, hf_gen⟩ := GlobalTheory.EtC.RedExists.twRed_sec Q q hqQ i
  refine ⟨f, hf_nat, ?_⟩
  intro U a
  apply (GlobalTheory.T.etaleSheafSections_ext_and_glue (ZMod q) _ U).1
  refine GlobalTheory.T.etaleLocal_property_calculus_rules.2.1 U _ _ ((GlobalTheory.T.tateTwist_sections_locally_generated Q i).1 U a) ?_
  intro V g h
  rw [SemiMap.nat, ← map_res, ← map_res, hf_nat]
  rcases h with h | ⟨ζ, c, h⟩
  · rw [h]
    simp only [Sec.map, map_zero]
  · rw [h]
    have key := GlobalTheory.T.tateTwistReductionResolutionMap_generator Q q hqQ i V ζ (GlobalTheory.EtC.RedExists.powPrim hqQ ζ) rfl
    simp only [GlobalTheory.EtC.resGen] at key
    simp only [Sec.map, map_nsmul, map_zsmul] at key ⊢
    rw [key, hf_gen V ζ (GlobalTheory.EtC.RedExists.powPrim hqQ ζ) rfl]
end

section -- restored from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PRingSplit
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces
open scoped TensorProduct

theorem UpperTheory.Gal.TranscendenceTraces.ringSplit_of :
    FinSec → IndDesc → RingSplit := by
  intro hF hI A B C _ _ _ _ _ _ _ _ P
  obtain ⟨O, _, _, _, hSH, hInd, hP⟩ := GlobalTheory.StrictHensPrime.exists_sh_indEt A P.asIdeal
  letI : Algebra B (O ⊗[A] B) := (Algebra.TensorProduct.includeRight : B →ₐ[A] O ⊗[A] B).toRingHom.toAlgebra
  obtain ⟨s⟩ := hF O (O ⊗[A] B) ((O ⊗[A] B) ⊗[B] C) hSH
  have t0 : C →ₐ[B] O ⊗[A] B :=
    (s.restrictScalars B).comp (Algebra.TensorProduct.includeRight : C →ₐ[B] (O ⊗[A] B) ⊗[B] C)
  let c : O ⊗[A] B →ₐ[B] B ⊗[A] O :=
    { (Algebra.TensorProduct.comm A O B).toAlgHom.toRingHom with
      commutes' := fun b => by
        show Algebra.TensorProduct.comm A O B ((1 : O) ⊗ₜ[A] b) = b ⊗ₜ[A] (1 : O)
        simp }
  obtain ⟨E, _, _, hE, ⟨φ⟩, hC⟩ := hI A O B C hInd ⟨c.comp t0⟩
  refine ⟨E, inferInstance, inferInstance, hE, ?_, hC⟩
  haveI : (Ideal.comap (φ : E →+* O) (IsLocalRing.maximalIdeal O)).IsPrime := Ideal.comap_isPrime _ _
  refine ⟨⟨Ideal.comap (φ : E →+* O) (IsLocalRing.maximalIdeal O), inferInstance⟩, ?_⟩
  ext1
  show Ideal.comap (algebraMap A E) (Ideal.comap (φ : E →+* O) (IsLocalRing.maximalIdeal O)) = P.asIdeal
  rw [Ideal.comap_comap, ← hP]
  congr 1
  exact φ.comp_algebraMap
end

section -- restored from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PSHSec
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.sHSec_of :
    SHSec := by
  intro T C _ _ _ _ _ hSH
  obtain ⟨hH, hS⟩ := hSH
  obtain ⟨q, hq⟩ := PrimeSpectrum.comap_surjective_of_faithfullyFlat (B := C)
    (⟨IsLocalRing.maximalIdeal T, inferInstance⟩ : PrimeSpectrum T)
  have hq' : (PrimeSpectrum.asIdeal q).comap (algebraMap T C) = IsLocalRing.maximalIdeal T :=
    congrArg PrimeSpectrum.asIdeal hq
  haveI : (PrimeSpectrum.asIdeal q).IsPrime := PrimeSpectrum.isPrime q
  obtain ⟨s, -⟩ := (GlobalTheory.StrictHensel.strictlyHenselian_iff T).2 ⟨inferInstance, inferInstance⟩
    C (PrimeSpectrum.asIdeal q) hq'
  exact ⟨s⟩
end

section -- restored from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PSumComp
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.sumComp_of :
    FibFin → SumComp := by
  intro hF W V U r p _ _ Ω _ x M _ c
  have hset : fib (r ≫ p) x = ⋃ y ∈ fib p x, fib r y := by
    ext z
    simp only [fib, Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
    constructor
    · intro hz
      exact ⟨z ≫ r, by rw [Category.assoc]; exact hz, rfl⟩
    · rintro ⟨y, hy, hz⟩
      rw [← Category.assoc, hz, hy]
  have hdisj : (fib p x).PairwiseDisjoint (fun y => fib r y) := by
    intro y₁ _ y₂ _ hne
    refine Set.disjoint_left.mpr ?_
    intro z h₁ h₂
    apply hne
    simp only [fib, Set.mem_setOf_eq] at h₁ h₂
    rw [← h₁, ← h₂]
  change ∑ᶠ z ∈ fib (r ≫ p) x, c z = ∑ᶠ y ∈ fib p x, ∑ᶠ z ∈ fib r y, c z
  rw [hset]
  exact finsum_mem_biUnion hdisj (hF p Ω x) (fun y _ => hF r Ω y)
end

section -- restored from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PSumExLoc
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.sumExLoc_of :
    SecFun → FunSec → FibFin → SumExLoc := by
  intro hSF hFS hFF q _ i Z S p _ w hw A hζ a
  obtain ⟨ζ⟩ := hζ
  haveI : IsFinite A.r := Sq.finite A
  have hgen : twGen i (ζ.map A.r.appTop.hom) = Sec.res A.r (twGen i ζ) :=
    ((GlobalTheory.T.tateTwist_sections_locally_generated q i).2.2.2.1 A.V A.U A.r ζ).symm
  obtain ⟨φ, hφ, hv⟩ := hSF q i A.V (ζ.map A.r.appTop.hom) a
  obtain ⟨ψ, hψ, hs⟩ := hw A φ hφ
  obtain ⟨b, hb⟩ := hFS q i A.U ζ ψ hψ
  refine ⟨b, fun Ω _ _ x => ?_⟩
  have hfin : (fib A.r x).Finite := hFF A.r Ω x
  have hz : ∀ z ∈ fib A.r x, Sec.res z a = φ (pt z) • Sec.res x (twGen i ζ) := by
    intro z hz
    have hz' : z ≫ A.r = x := hz
    rw [hv Ω z, hgen, res_res, hz']
  rw [hb Ω x, hs Ω x, finsum_mem_eq_finite_toFinset_sum _ hfin,
    finsum_mem_eq_finite_toFinset_sum _ hfin, Finset.sum_smul]
  refine Finset.sum_congr rfl fun z hzm => ?_
  rw [hz z (hfin.mem_toFinset.mp hzm), mul_smul]
end

section -- restored from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PSumNat
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.sumNat_of :
    SumNat := by
  intro R _ F Z S p w A B t a b hB Ω _ _ x
  rw [res_res, hB Ω (x ≫ t.g)]
  symm
  refine finsum_mem_eq_of_bijOn (fun z => z ≫ t.k) (fib_bijOn t.isPullback x) ?_
  intro z _
  simp only [res_res, Category.assoc, t.hv]
end

section -- restored from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PTrChar
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.trChar_of :
    FL → OpEq → TrSum → PtInj → TrChar := by
  intro hFL hOp hTS hPI q _ i Z S p _ w hw hq
  have hOver : (trFam p w q i).Over (tr0 p w q i) := by
    unfold trFam
    exact GlobalTheory.EtC.pick_spec (hFL q p (tw q i) (tw q i) (tr0 p w q i)).1
  refine ⟨hOver, ?_, ?_⟩
  · intro A a
    exact ⟨(tr0 p w q i).app A a, hOver A a, hTS q i p w hw hq A a⟩
  · intro τ hτ n
    have hτo : τ.Over (tr0 p w q i) := by
      intro A a
      obtain ⟨b, hb, hs⟩ := hτ A a
      have hbe : b = (tr0 p w q i).app A a := by
        apply hPI q i A.U
        intro Ω _ _ x
        rw [hs Ω x, hTS q i p w hw hq A a Ω x]
      rw [hb, hbe]
    exact hOp q p (tw q i) (tw q i) (tr0 p w q i) (trFam p w q i) τ hOver hτo n
end

section -- restored from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PTrDeg
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.trDeg_of :
    TrPush → TrLin → TrDeg := by
  intro hP hL q _ n i Z S p _ w d hw hq hpush x
  have h1 := hP q n i p (𝟙 S) w (by simpa using hw) hq x
  simp only [Category.comp_id] at h1
  rw [h1, hpush]
  exact (hL q n i).2.2 S d hq x
end

section -- restored from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PTrDegQ
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

private theorem trHl_pullHl (hHl : TrHl) (hDeg : TrDeg) (l : ℕ) [Fact l.Prime] (n i : ℤ) {Z S : Scheme.{0}} (p : Z ⟶ S)
    [IsFinite p] (w : Wt Z) (d : ℤ) (hw : IsWt p w) (hl : IsUnit (l : Γ(S, ⊤))) (hd : w.push p = Wt.const S d)
    (x : Hl l (sch.obj S) n i) :
    trHl l p w n i (pullHl l (sch.map p) n i x) = d • x := by
  apply Subtype.ext
  funext k
  have hk : IsUnit ((↑(l ^ k) : ℕ) : Γ(S, ⊤)) := by
    rw [Nat.cast_pow]
    exact hl.pow k
  show (trHl l p w n i (pullHl l (sch.map p) n i x)).1 k = (d • x).1 k
  rw [hHl l n i p w hw hl _ k]
  exact hDeg (l ^ k) n i p w d hw hk hd (x.1 k)

theorem UpperTheory.Gal.TranscendenceTraces.trDegQ_of :
    TrHl → TrDeg → TrDegQ := by
  intro hHl hDeg l _ n i Z S p _ w d hw hl hd
  apply LinearMap.ext
  intro z
  unfold trHQ pullHQ
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a y =>
    rw [LinearMap.comp_apply, LinearMap.baseChange_tmul, LinearMap.baseChange_tmul,
      trHl_pullHl hHl hDeg l n i p w d hw hl hd y]
    simp only [TensorProduct.tmul_smul, LinearMap.smul_apply, LinearMap.id_apply]
    exact (Int.cast_smul_eq_zsmul ℚ_[l] d _).symm
  | add u v hu hv =>
    simp only [map_add (f := _)] at hu hv ⊢
    rw [hu, hv]
end

section -- restored from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PTrIdQ
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

private theorem trHl_id_apply (hHl : TrHl) (hL : TrLin) (hW : WtLin) (l : ℕ) [Fact l.Prime] (n i : ℤ) (S : Scheme.{0})
    (d : ℤ) (hu : IsUnit (l : Γ(S, ⊤))) (x : Hl l (sch.obj S) n i) :
    trHl l (𝟙 S) (Wt.const S d) n i x = d • x := by
  have hw : IsWt (𝟙 S) (Wt.const S d) := hW.2.2 (𝟙 S) d
  refine Subtype.ext (funext fun k => ?_)
  haveI : NeZero (l ^ k) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have hq : IsUnit ((l ^ k : ℕ) : Γ(S, ⊤)) := by
    rw [Nat.cast_pow]
    exact hu.pow k
  refine (hHl l n i (𝟙 S) _ hw hu x k).trans ?_
  exact (hL (l ^ k) n i).2.2 S d hq (x.1 k)

theorem UpperTheory.Gal.TranscendenceTraces.trIdQ_of :
    TrHl → TrLin → WtLin → TrIdQ := by
  intro hHl hL hW l _ n i S d hu
  unfold trHQ
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a m =>
    rw [LinearMap.baseChange_tmul, trHl_id_apply hHl hL hW l n i S d hu m]
    simp only [LinearMap.smul_apply, LinearMap.id_apply, TensorProduct.tmul_smul]
    rw [Int.cast_smul_eq_zsmul]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
end

section -- restored from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PTrRel
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

private noncomputable def wSum {Z : Scheme.{0}} {ι : Type} (w : ι → Wt Z) (m : ι → ℤ) (s : Finset ι) : Wt Z :=
  fun Ω _ _ z => ∑ a ∈ s, m a * w a Ω z

theorem UpperTheory.Gal.TranscendenceTraces.trRel_of :
    TrLin → WtLin → WtVanish → TrRel := by
  intro hT hW hV q _ n i Z S p _ ι _ w m hw hq D hD hz x
  classical
  obtain ⟨hTa, hTs, -⟩ := hT q n i
  obtain ⟨hWa, hWs, -⟩ := hW
  have h0 : wSum w m ∅ = Wt.const Z 0 := by
    funext Ω _ _ z
    simp [wSum, Wt.const]
  have hc : ∀ y : Ht q (sch.obj Z) n i, tr p (Wt.const Z 0) q n i y = 0 := by
    intro y
    have hs : Wt.smul 0 (Wt.const Z 0) = Wt.const Z 0 := by
      funext Ω _ _ z
      simp [Wt.smul, Wt.const]
    rw [← hs, hTs p 0 _ (isWt_zero p) hq y, zero_smul]
  have hins : ∀ (a : ι) (s : Finset ι), a ∉ s →
      wSum w m (insert a s) = (Wt.smul (m a) (w a)).add (wSum w m s) := by
    intro a s ha
    funext Ω _ _ z
    simp [wSum, Wt.add, Wt.smul, Finset.sum_insert ha]
  have key : ∀ s : Finset ι, IsWt p (wSum w m s) ∧
      ∀ y, tr p (wSum w m s) q n i y = ∑ a ∈ s, m a • tr p (w a) q n i y := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      rw [h0]
      exact ⟨isWt_zero p, fun y => by rw [hc y, Finset.sum_empty]⟩
    | insert a s ha ih =>
      rw [hins a s ha]
      have h1 := hWs p (m a) (w a) (hw a)
      refine ⟨hWa p _ _ h1 ih.1, fun y => ?_⟩
      rw [hTa p _ _ h1 ih.1 hq y, hTs p _ _ (hw a) hq y, ih.2 y, Finset.sum_insert ha]
  have hzero : wSum w m Finset.univ = Wt.const Z 0 :=
    hV p _ (key Finset.univ).1 D hD fun Ω _ _ z hz' => hz Ω z hz'
  rw [← (key Finset.univ).2 x, hzero, hc x]
end

section -- restored from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PWtClopen
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

private theorem isLocallyConstant_weighted_sum {X : Type*} [TopologicalSpace X] (T : Finset ℤ) (f : ℤ → X → ℤ)
    (hf : ∀ c, IsLocallyConstant (f c)) : IsLocallyConstant (fun y => ∑ c ∈ T, c * f c y) := by
  have h : ∀ c, Continuous (f c) := fun c => (IsLocallyConstant.iff_continuous _).1 (hf c)
  exact (IsLocallyConstant.iff_continuous _).2
    (continuous_finsetSum _ fun c _ => continuous_const.mul (h c))

theorem UpperTheory.Gal.TranscendenceTraces.wtClopen_of :
    WtCrit → FibFin → WtClopen := by
  intro hcrit hfin Z S p _ w hcl
  apply hcrit p w
  intro A φ hφ u
  have hφc : Continuous φ := (IsLocallyConstant.iff_continuous φ).1 hφ
  haveI := A.finite
  obtain ⟨U0, hU0, hu, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1 A.U.isBasis_affineOpens)
    (show u ∈ (⊤ : A.U.Opens) from trivial)
  have hK : IsCompact (A.r ⁻¹' (U0 : Set A.U)) :=
    QuasiCompact.isCompact_preimage _ U0.isOpen (IsAffineOpen.isCompact hU0)
  let T : Finset ℤ := ((hK.image hφc).finite_of_discrete).toFinset
  choose ψ hψ hψs using fun c : ℤ => hcl A (φ ⁻¹' {c}) (hφ.isClopen_fiber c)
  let Ψ : A.U → ℤ := fun y => ∑ c ∈ T, c * ψ c y
  have hΨ : IsLocallyConstant Ψ := isLocallyConstant_weighted_sum T ψ hψ
  refine ⟨(U0 : Set A.U) ∩ {y | Ψ y = Ψ u}, Ψ u, U0.isOpen.inter (hΨ.isOpen_fiber _),
    ⟨hu, rfl⟩, ?_⟩
  rintro Ω _ _ x ⟨hx0, hxΨ⟩
  rw [← show Ψ (pt x) = Ψ u from hxΨ]
  have hF := hfin A.r Ω x
  classical
  have key : ∀ c, ψ c (pt x) =
      ∑ z ∈ hF.toFinset, if φ (pt z) = c then w Ω (z ≫ A.v) else 0 := by
    intro c
    rw [hψs c Ω x, finsum_mem_eq_finite_toFinset_sum _ (hF.inter_of_left _), ← Finset.sum_filter]
    congr 1
    ext z
    simp
  simp only [Ψ, key, Finset.mul_sum]
  rw [finsum_mem_eq_finite_toFinset_sum _ hF, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z hz
  have hzf : z ≫ A.r = x := (Set.Finite.mem_toFinset hF).1 hz
  have hmem : φ (pt z) ∈ T := by
    rw [Set.Finite.mem_toFinset]
    refine ⟨pt z, ?_, rfl⟩
    show A.r (pt z) ∈ (U0 : Set A.U)
    rw [← pt_comp, hzf]
    exact hx0
  simp_rw [mul_ite, mul_zero]
  rw [Finset.sum_ite_eq, if_pos hmem, mul_comm]
end

section -- restored from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PWtComp
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.wtComp_of :
    SumComp → FibFin → WtComp := by
  intro hsum hfin W Z S r p _ _ w' w hr hp A φ hφ
  obtain ⟨m, hm1, hm2⟩ : ∃ m : A.V ⟶ pullback p A.u,
      m ≫ pullback.fst p A.u = A.v ≫ r ∧ m ≫ pullback.snd p A.u = A.r :=
    ⟨pullback.lift (A.v ≫ r) A.r (by rw [Category.assoc]; exact A.pb.w),
      pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have hsq : IsPullback A.v m r (pullback.fst p A.u) := by
    refine IsPullback.of_bot ?_ hm1.symm (IsPullback.of_hasPullback p A.u)
    rw [hm2]
    exact A.pb
  let C : Sq r := ⟨pullback p A.u, A.V, pullback.fst p A.u, A.v, m, hsq⟩
  haveI : IsFinite m := C.finite
  haveI : IsFinite (pullback.snd p A.u) := (Sq.of p A.u).finite
  obtain ⟨ψ1, hψ1, hψ1s⟩ := hr C φ hφ
  obtain ⟨ψ2, hψ2, hψ2s⟩ := hp (Sq.of p A.u) ψ1 hψ1
  refine ⟨ψ2, hψ2, ?_⟩
  intro Ω _ _ x
  have hsc : ∀ c : (gp Ω ⟶ A.V) → ℤ, ∑ᶠ z ∈ fib (m ≫ pullback.snd p A.u) x, c z =
      ∑ᶠ y ∈ fib (pullback.snd p A.u) x, ∑ᶠ z ∈ fib m y, c z := by
    intro c
    have h := congrArg (AddEquiv.ulift : ULift.{1} ℤ ≃+ ℤ)
      (hsum m (pullback.snd p A.u) Ω x (ULift.{1} ℤ) (fun z => ULift.up (c z)))
    simp only [AddEquiv.map_finsum] at h
    exact h
  refine (hψ2s Ω x).trans ?_
  rw [← hm2, hsc]
  refine finsum_mem_congr rfl ?_
  intro y _
  refine (congrArg (fun t => w Ω (y ≫ pullback.fst p A.u) * t) (hψ1s Ω y)).trans ?_
  rw [mul_finsum_mem]
  refine finsum_mem_congr rfl ?_
  intro z hz
  have hz' : z ≫ m = y := hz
  show w Ω (y ≫ pullback.fst p A.u) * (w' Ω (z ≫ A.v) * φ (pt z)) =
    w' Ω (z ≫ A.v) * w Ω ((z ≫ A.v) ≫ r) * φ (pt z)
  rw [Category.assoc, ← hm1, ← Category.assoc, hz']
  exact (mul_left_comm _ _ _).trans (mul_assoc _ _ _).symm
end

section -- restored from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PWtCrit
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.wtCrit_of :
    PtEx → WtCrit := by
  intro hPt Z S p w h A φ hφ
  choose N c hN hu hc using h A φ hφ
  refine ⟨c, ?_, fun Ω _ _ x => (hc (pt x) Ω x (hu (pt x))).symm⟩
  rw [IsLocallyConstant.iff_exists_open]
  intro u
  refine ⟨N u, hN u, hu u, fun u' hu' => ?_⟩
  obtain ⟨Ω, _, _, x, rfl⟩ := hPt A.U u'
  rw [← hc (pt x) Ω x (hu (pt x)), hc u Ω x hu']
end

section -- restored from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PWtDegConst
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.wtDegConst_of :
    PtEx → WtDegConst := by
  intro _ Z S p _ _ w hw
  obtain ⟨ψ, hψ, hsum⟩ := hw (Sq.self p) (fun _ => 1) (IsLocallyConstant.const 1)
  have hψ' : IsLocallyConstant (fun s : S => ψ s) := hψ
  by_cases hS : Nonempty S
  · obtain ⟨s₀⟩ := hS
    refine ⟨ψ s₀, ?_⟩
    funext Ω _ _ x
    have h : ψ (pt x) = ∑ᶠ (z : gp Ω ⟶ Z) (_ : z ∈ fib p x), w Ω (z ≫ 𝟙 Z) * 1 := hsum Ω x
    simp only [Category.comp_id, mul_one] at h
    show (∑ᶠ (z : gp Ω ⟶ Z) (_ : z ∈ fib p x), w Ω z) = ψ s₀
    have hc : ψ (pt x) = ψ s₀ := hψ'.apply_eq_of_preconnectedSpace (pt x) s₀
    rw [← hc]
    exact h.symm
  · refine ⟨0, ?_⟩
    funext Ω _ _ x
    exact (hS ⟨pt x⟩).elim
end

section -- restored from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PWtExt
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

private theorem fsum_single {α : Type*} (s : Set α) (f : α → ℤ) (a : α) (ha : a ∈ s)
    (h : ∀ x ∈ s, f x ≠ 0 → x = a) : ∑ᶠ x ∈ s, f x = f a := by
  classical
  rw [finsum_eq_single (fun x => ∑ᶠ (_ : x ∈ s), f x) a]
  · simp [ha]
  · intro x hx
    by_cases hs : x ∈ s
    · have h0 : f x = 0 := by
        by_contra h0
        exact hx (h x hs h0)
      simp [h0]
    · simp [hs]

private theorem discrete_of_chart (hChart : Chart) {V : Scheme.{0}} (Ω : Type) [Field Ω] (r : V ⟶ gp Ω) [IsFinite r] :
    DiscreteTopology V := by
  obtain ⟨B, _, _, v, hfin, hpb⟩ := hChart r Ω (𝟙 _)
  haveI : IsIso v := hpb.isIso_fst_of_isIso
  haveI : IsArtinianRing B := IsArtinianRing.of_finite Ω B
  haveI : DiscreteTopology (Spec (CommRingCat.of B)) := inferInstanceAs (DiscreteTopology (PrimeSpectrum B))
  exact (Scheme.homeoOfIso (asIso v)).symm.isEmbedding.discreteTopology

theorem UpperTheory.Gal.TranscendenceTraces.wtExt_of :
    PtOne → Chart → WtExt := by
  intro hOne hChart Z S p _ w hw Ω L _ _ _ _ z a
  classical
  haveI hr : IsFinite (pullback.snd p (z ≫ p)) := Sq.finite (Sq.of p (z ≫ p))
  haveI := discrete_of_chart hChart Ω (pullback.snd p (z ≫ p))
  let z0 : gp Ω ⟶ pullback p (z ≫ p) := pullback.lift z (𝟙 _) (by simp)
  have hf : z0 ≫ pullback.fst p (z ≫ p) = z := pullback.lift_fst _ _ _
  have hs : z0 ≫ pullback.snd p (z ≫ p) = 𝟙 _ := pullback.lift_snd _ _ _
  let φ : (pullback p (z ≫ p) : Scheme.{0}) → ℤ := fun y => if y = pt z0 then 1 else 0
  obtain ⟨ψ, -, hψ⟩ := hw (Sq.of p (z ≫ p)) φ (IsLocallyConstant.of_discrete φ)
  have h1 : ψ (pt (𝟙 (gp Ω))) = ∑ᶠ y ∈ fib (pullback.snd p (z ≫ p)) (𝟙 (gp Ω)),
      w Ω (y ≫ pullback.fst p (z ≫ p)) * φ (pt y) := hψ Ω (𝟙 _)
  have h2 : ψ (pt a) = ∑ᶠ y ∈ fib (pullback.snd p (z ≫ p)) a,
      w L (y ≫ pullback.fst p (z ≫ p)) * φ (pt y) := hψ L a
  have hpt : pt (a ≫ z0) = pt z0 := by rw [pt_comp, pt_eq]
  have hφ : φ (pt z0) = 1 := if_pos rfl
  have hne : ∀ y : (pullback p (z ≫ p) : Scheme.{0}), φ y ≠ 0 → y = pt z0 := by
    intro y hy
    by_contra h
    exact hy (if_neg h)
  have e1 : ∑ᶠ y ∈ fib (pullback.snd p (z ≫ p)) (𝟙 (gp Ω)),
      w Ω (y ≫ pullback.fst p (z ≫ p)) * φ (pt y) = w Ω z := by
    rw [fsum_single _ _ z0 hs, hf, hφ, mul_one]
    intro y hy h0
    exact hOne Ω (pullback.snd p (z ≫ p)) Ω (𝟙 _) y z0 hy hs (hne _ (right_ne_zero_of_mul h0))
  have hs' : (a ≫ z0) ≫ pullback.snd p (z ≫ p) = a := by
    rw [Category.assoc, hs, Category.comp_id]
  have e2 : ∑ᶠ y ∈ fib (pullback.snd p (z ≫ p)) a,
      w L (y ≫ pullback.fst p (z ≫ p)) * φ (pt y) = w L (a ≫ z) := by
    rw [fsum_single _ _ (a ≫ z0) hs', Category.assoc, hf, hpt, hφ, mul_one]
    intro y hy h0
    exact hOne Ω (pullback.snd p (z ≫ p)) L a y (a ≫ z0) hy hs'
      ((hne _ (right_ne_zero_of_mul h0)).trans hpt.symm)
  have hU : pt a = pt (𝟙 (gp Ω)) := Subsingleton.elim (α := PrimeSpectrum Ω) _ _
  rw [← e2, ← e1, ← h2, ← h1]
  exact congrArg ψ hU
end

section -- restored from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PWtLin
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.wtLin_of :
    FibFin → WtLin := by
  intro hF
  refine ⟨?_, ?_, ?_⟩
  · intro Z S p _ w w' h1 h2
    unfold IsWt at *
    intro A φ hφ
    obtain ⟨ψ1, hψ1, e1⟩ := h1 A φ hφ
    obtain ⟨ψ2, hψ2, e2⟩ := h2 A φ hφ
    refine ⟨ψ1 + ψ2, hψ1.add hψ2, ?_⟩
    intro Ω _ _ x
    haveI := A.finite
    have hfin := hF A.r Ω x
    rw [Pi.add_apply, e1, e2, ← finsum_mem_add_distrib hfin]
    refine finsum_congr fun z => finsum_congr fun _ => ?_
    show _ = (w Ω _ + w' Ω _) * _
    ring
  · intro Z S p _ d w h1
    unfold IsWt at *
    intro A φ hφ
    obtain ⟨ψ1, hψ1, e1⟩ := h1 A φ hφ
    refine ⟨(fun t => d * t) ∘ ψ1, hψ1.comp _, ?_⟩
    intro Ω _ _ x
    rw [Function.comp_apply, e1, mul_finsum_mem]
    refine finsum_congr fun z => finsum_congr fun _ => ?_
    show _ = d * w Ω _ * _
    ring
  · intro Z S p _ d
    unfold IsWt
    intro A φ hφ
    haveI : IsIso A.r := by
      rw [← A.pb.isoPullback_hom_snd]
      infer_instance
    refine ⟨(fun t => d * t) ∘ φ ∘ ⇑(inv A.r), (hφ.comp_continuous (inv A.r).continuous).comp _, ?_⟩
    intro Ω _ _ x
    have hs : fib A.r x = {x ≫ inv A.r} := by
      ext z
      show z ≫ A.r = x ↔ z = x ≫ inv A.r
      constructor
      · rintro rfl
        simp
      · rintro rfl
        simp
    rw [hs, finsum_mem_singleton, pt_comp]
    rfl
end

section -- restored from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PWtLocal
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.wtLocal_of :
    WtCrit → WtLocal := by
  intro hcrit Z S p w hloc
  apply hcrit p w
  intro B φ hφ b
  obtain ⟨A, hAo, ⟨a, ha⟩, hA⟩ := hloc (B.u b)
  obtain ⟨W, f1, f2, hW, hf1, c0, hc0⟩ : ∃ (W : Scheme) (f1 : W ⟶ B.U) (f2 : W ⟶ A.U),
      IsPullback f1 f2 B.u A.u ∧ IsOpenImmersion f1 ∧ ∃ c0, f1 c0 = b := by
    obtain ⟨c0, hc0, -⟩ :=
      Scheme.Pullback.exists_preimage_pullback (f := B.u) (g := A.u) b a ha.symm
    exact ⟨_, _, _, IsPullback.of_hasPullback B.u A.u, inferInstance, c0, hc0⟩
  obtain ⟨V', q1, q2, hq⟩ : ∃ (V' : Scheme) (q1 : V' ⟶ A.V) (q2 : V' ⟶ W),
      IsPullback q1 q2 A.r f2 :=
    ⟨_, _, _, IsPullback.of_hasPullback A.r f2⟩
  have hcomm : (q1 ≫ A.v) ≫ p = (q2 ≫ f1) ≫ B.u := by
    simp only [Category.assoc]
    rw [A.pb.w, ← Category.assoc, hq.w, Category.assoc, hW.w]
  obtain ⟨g, hg1, hg2⟩ : ∃ g : V' ⟶ B.V, g ≫ B.v = q1 ≫ A.v ∧ g ≫ B.r = q2 ≫ f1 :=
    ⟨B.pb.lift _ _ hcomm, B.pb.lift_fst _ _ _, B.pb.lift_snd _ _ _⟩
  have hsq : IsPullback g q2 B.r f1 := by
    refine IsPullback.of_right ?_ hg2 B.pb
    rw [hg1, hW.w]
    exact hq.paste_horiz A.pb
  obtain ⟨ψ, hψ, hψs⟩ :=
    hA ⟨W, V', f2, q1, q2, hq⟩ (fun y => φ (g y)) (hφ.comp_continuous g.continuous)
  refine ⟨f1 '' {y | ψ y = ψ c0}, ψ c0, f1.isOpenEmbedding.isOpenMap _ (hψ.isOpen_fiber _),
    ⟨c0, rfl, hc0⟩, ?_⟩
  rintro Ω _ _ x ⟨y, hy, hyx⟩
  have hr : Set.range x ⊆ Set.range f1 := by
    rintro _ ⟨t, rfl⟩
    exact ⟨y, hyx.trans (pt_eq x t).symm⟩
  have hx' : IsOpenImmersion.lift f1 x hr ≫ f1 = x := IsOpenImmersion.lift_fac _ _ _
  have hpt : pt (IsOpenImmersion.lift f1 x hr) = y := by
    apply f1.isOpenEmbedding.injective
    rw [← pt_comp, hx', hyx]
  have hs := hψs Ω (IsOpenImmersion.lift f1 x hr)
  rw [hpt, show ψ y = ψ c0 from hy] at hs
  rw [hs]
  symm
  have hb := fib_bijOn hsq (IsOpenImmersion.lift f1 x hr)
  rw [hx'] at hb
  refine finsum_mem_eq_of_bijOn (fun z => z ≫ g) hb ?_
  intro z _
  simp only [Wt.comap, pt_comp, Category.assoc, hg1]
end

section -- restored from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PWtNormal
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.wtNormal_of :
    NormAff → NwtGlue → WtNormal := by
  intro hAff hGlue Z S p _ hS
  have h : ∃ w, IsNwt p w := by
    refine hGlue p (fun s => ?_)
    obtain ⟨U, hU, hs, hd, hi⟩ := hS s
    obtain ⟨A, w, ho, hr, hw⟩ := hAff p U hU hd hi
    exact ⟨A, w, ho, by rw [hr]; exact hs, hw⟩
  unfold nwt
  rw [dite_eq_left h]
  exact h.choose_spec
end

section -- restored from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PWtUnique
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.wtUnique_of :
    WtVanish → WtLin → WtUnique := by
  intro hV hL Z S p _ w w' hw hw' D hD hagree
  have hdiff : IsWt p (w.add (Wt.smul (-1) w')) := hL.1 p w _ hw (hL.2.1 p (-1) w' hw')
  have h0 := hV p _ hdiff D hD (by
    intro Ω _ _ z hz
    show w Ω z + (-1) * w' Ω z = 0
    rw [hagree Ω z hz]
    ring)
  funext Ω _ _ z
  have h := congrFun (congrFun (congrFun (congrFun h0 Ω) ‹_›) ‹_›) z
  change w Ω z + (-1) * w' Ω z = 0 at h
  linarith
end

section -- restored from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.TrHlOf
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.trHl_of :
    TrRed → TrHl := by
  intro hR l _ n i Z S p _ w hw hl x k
  have hne : ∀ k : ℕ, NeZero (l ^ k) := fun k => ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have hu : ∀ k : ℕ, IsUnit ((l ^ k : ℕ) : Γ(S, ⊤)) := fun k => by
    rw [Nat.cast_pow]
    exact hl.pow _
  have hT : ∃ T : Hl l (sch.obj Z) n i →ₗ[ℤ_[l]] Hl l (sch.obj S) n i,
      ∀ (x : Hl l (sch.obj Z) n i) (k : ℕ), (T x).1 k = tr p w (l ^ k) n i (x.1 k) := by
    refine ⟨{ toFun := fun x => ⟨fun k => tr p w (l ^ k) n i (x.1 k), fun k => ?_⟩
              map_add' := fun x y => Subtype.ext (funext fun k => map_add (tr p w (l ^ k) n i) (x.1 k) (y.1 k))
              map_smul' := fun r x => Subtype.ext (funext fun k => ?_) }, fun _ _ => rfl⟩
    · haveI := hne (k + 1)
      haveI := hne k
      exact (hR (l ^ (k + 1)) (l ^ k) (pow_dvd_pow l (Nat.le_succ k)) n i p w hw (hu (k + 1)) (x.1 (k + 1))).trans
        (congrArg _ (x.2 k))
    · let f : HtL l k (sch.obj Z) n i →+ HtL l k (sch.obj S) n i := tr p w (l ^ k) n i
      change f (r • x.1 k) = r • f (x.1 k)
      rw [HtL.smul_eq l k k le_rfl, HtL.smul_eq l k k le_rfl]
      exact map_nsmul f _ _
  exact pick_spec (P := fun T : Hl l (sch.obj Z) n i →ₗ[ℤ_[l]] Hl l (sch.obj S) n i =>
    ∀ (x : Hl l (sch.obj Z) n i) (k : ℕ), (T x).1 k = tr p w (l ^ k) n i (x.1 k)) hT x k
end

section -- restored from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.WtBCOf
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.wtBC_of :
    WtBC := by
  intro Z' S' Z S v p' p g w h hw
  unfold IsWt at *
  intro A φ hφ
  obtain ⟨ψ, hψ, e⟩ := hw ⟨A.U, A.V, A.u ≫ g, A.v ≫ v, A.r, A.pb.paste_horiz h⟩ φ hφ
  refine ⟨ψ, hψ, ?_⟩
  intro Ω _ _ x
  rw [e]
  refine finsum_congr fun z => finsum_congr fun _ => ?_
  show w Ω (z ≫ A.v ≫ v) * _ = w Ω ((z ≫ A.v) ≫ v) * _
  rw [Category.assoc]
end

section -- restored from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.WtPtOf
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.wtPt_of :
    WtExt → PtCommon → WtPt := by
  intro hE hC Z S p _ w hw Ω Ω' _ _ _ _ z z' h
  obtain ⟨L, _, _, a, a', ha⟩ := hC Z Ω Ω' z z' h
  rw [← hE p w hw Ω L z a, ← hE p w hw Ω' L z' a', ha]
end

namespace UpperTheory.Gal.TranscendenceTraces

theorem ptEx_holds : PtEx := @ptEx_of

theorem chart_holds : Chart := @chart_of

theorem fibFin_holds : FibFin := @fibFin_of @chart_holds

theorem ptCommon_holds : PtCommon := @ptCommon_of

theorem ptOne_holds : PtOne := @ptOne_of @chart_holds

theorem wtExt_holds : WtExt := @wtExt_of @ptOne_holds @chart_holds

theorem wtPt_holds : WtPt := @wtPt_of @wtExt_holds @ptCommon_holds

theorem ptLift_holds : PtLift := @ptLift_of

theorem isolateSpec_holds : IsolateSpec := @isolateSpec_of

theorem isolate_holds : Isolate := @isolate_of @chart_holds @isolateSpec_holds

theorem imageOne_holds : ImageOne := @imageOne_of

theorem genBasic_holds : GenBasic := @genBasic_of

theorem indDesc_holds : IndDesc := @indDesc_of

theorem sHSec_holds : SHSec := @sHSec_of

theorem finSec_holds : FinSec := @finSec_of @sHSec_holds

theorem imageFin_holds : ImageFin := @imageFin_of @imageOne_holds

theorem ringSplit_holds : RingSplit := @ringSplit_of @finSec_holds @indDesc_holds

theorem locFinAff_holds : LocFinAff := @locFinAff_of @chart_holds @ringSplit_holds

theorem locFinGeo_holds : LocFinGeo := @locFinGeo_of @locFinAff_holds

theorem coverOne_holds : CoverOne := @coverOne_of

theorem locFinSec_holds : LocFinSec := @locFinSec_of @coverOne_holds @locFinGeo_holds

theorem wtBC_holds : WtBC := @wtBC_of

theorem invTrans_holds : InvTrans := @invTrans_of

theorem galTrans_holds : GalTrans := @galTrans_of @invTrans_holds

theorem splitField_holds : SplitField := @splitField_of

theorem sumComp_holds : SumComp := @sumComp_of @fibFin_holds

theorem wtComp_holds : WtComp := @wtComp_of @sumComp_holds @fibFin_holds

theorem splitCover_holds : SplitCover := @splitCover_of @splitField_holds @galTrans_holds

theorem wtLin_holds : WtLin := @wtLin_of @fibFin_holds

theorem countEx_holds : CountEx := @countEx_of

theorem countWt_holds : CountWt := @countWt_of @ptEx_holds @ptLift_holds @fibFin_holds

theorem wtCrit_holds : WtCrit := @wtCrit_of @ptEx_holds

theorem wtClopen_holds : WtClopen := @wtClopen_of @wtCrit_holds @fibFin_holds

theorem artSum_holds : ArtSum := @artSum_of

theorem stalkSum_holds : StalkSum := @stalkSum_of @chart_holds @artSum_holds

theorem multSec_holds : MultSec := @multSec_of

theorem multSumPt_holds : MultSumPt := multSumPt_of stalkSum_holds multSec_holds ptLift_holds ptOne_holds fibFin_holds

theorem multBC_holds : MultBC := @multBC_of

theorem multSum_holds : MultSum := @multSum_of @multSumPt_holds @multBC_holds

theorem multOpen_holds : MultOpen := @multOpen_of

theorem wtFlat_holds : WtFlat := wtFlat_of wtClopen_holds multSum_holds multBC_holds multOpen_holds

theorem multPt_holds : MultPt := @multPt_of @wtFlat_holds @wtPt_holds @multBC_holds

theorem normSpec_holds : NormSpec := normSpec_of splitCover_holds countEx_holds countWt_holds multPt_holds ptEx_holds ptLift_holds genBasic_holds

theorem wtPush_holds : WtPush := @wtPush_of @sumComp_holds @fibFin_holds

theorem wtLocal_holds : WtLocal := @wtLocal_of @wtCrit_holds

theorem normAff_holds : NormAff := @normAff_of @chart_holds @normSpec_holds

theorem nwtOpen_holds : NwtOpen := @nwtOpen_of @wtBC_holds @multBC_holds @genBasic_holds

theorem wtVanish_holds : WtVanish := wtVanish_of isolate_holds wtPt_holds ptEx_holds ptLift_holds fibFin_holds

theorem wtUnique_holds : WtUnique := @wtUnique_of @wtVanish_holds @wtLin_holds

theorem nwtAgree_holds : NwtAgree := nwtAgree_of nwtOpen_holds wtUnique_holds genBasic_holds multBC_holds

theorem nwtGlue_holds : NwtGlue := nwtGlue_of nwtAgree_holds wtLocal_holds multBC_holds genBasic_holds

theorem wtNormal_holds : WtNormal := @wtNormal_of @normAff_holds @nwtGlue_holds

theorem wtDegConst_holds : WtDegConst := @wtDegConst_of @ptEx_holds

theorem nmlInt_holds : NmlInt := @nmlInt_of

theorem nmlNoeth_holds : NmlNoeth := @nmlNoeth_of

theorem nmlLoc_holds : NmlLoc := @nmlLoc_of @nmlInt_holds @nmlNoeth_holds

theorem nwtFlat_holds : NwtFlat := nwtFlat_of wtBC_holds wtFlat_holds wtUnique_holds multBC_holds

theorem multEt_holds : MultEt := @multEt_of

theorem multBasic_holds : MultBasic := @multBasic_of @multBC_holds @multOpen_holds @multEt_holds

theorem nwtOfFlat_holds : NwtOfFlat := @nwtOfFlat_of @wtFlat_holds @wtUnique_holds @genBasic_holds

theorem nwtDeg_holds : NwtDeg := nwtDeg_of wtNormal_holds wtDegConst_holds multSum_holds multBC_holds genBasic_holds

theorem funSec_holds : FunSec := @funSec_of

theorem phiEx_holds : PhiEx := @phiEx_of @locFinSec_holds

theorem fL_holds : FL := @fL_of @phiEx_holds

theorem rpBasic_holds : RpBasic := @rpBasic_of

theorem imgBasic_holds : ImgBasic := @imgBasic_of

theorem rpOp_holds : RpOp := @rpOp_of @imgBasic_holds

theorem opEq_holds : OpEq := @opEq_of @fL_holds @rpBasic_holds @rpOp_holds

theorem secFun_holds : SecFun := @secFun_of @ptEx_holds

theorem sumExLoc_holds : SumExLoc := @sumExLoc_of @secFun_holds @funSec_holds @fibFin_holds

theorem sumNat_holds : SumNat := @sumNat_of

theorem ptInj_holds : PtInj := @ptInj_of @ptEx_holds

theorem sumEx_holds : SumEx := @sumEx_of @sumExLoc_holds @sumNat_holds @ptInj_holds

theorem trSum_holds : TrSum := trSum_of sumEx_holds sumNat_holds ptInj_holds fibFin_holds

theorem trChar_holds : TrChar := @trChar_of @fL_holds @opEq_holds @trSum_holds @ptInj_holds

theorem famSemi_holds : FamSemi := @famSemi_of

theorem redZero_holds : RedZero := @redZero_of

theorem trRed_holds (h : GlobalTheory.EtC.A8) : TrRed := trRed_of h trChar_holds trSum_holds opEq_holds famSemi_holds redZero_holds rpBasic_holds rpOp_holds ptInj_holds fibFin_holds

theorem trHl_holds (h : GlobalTheory.EtC.A8) : TrHl := @trHl_of (@trRed_holds h)

theorem famLin_holds : FamLin := @famLin_of @fibFin_holds

theorem trLin_holds : TrLin := trLin_of trChar_holds famLin_holds wtLin_holds rpBasic_holds rpOp_holds

theorem trIdQ_holds (h : GlobalTheory.EtC.A8) : TrIdQ := @trIdQ_of (@trHl_holds h) @trLin_holds @wtLin_holds

theorem famPush_holds : FamPush := @famPush_of @sumComp_holds @fibFin_holds

theorem trPush_holds : TrPush := trPush_of trChar_holds famPush_holds wtPush_holds rpBasic_holds rpOp_holds

theorem trDeg_holds : TrDeg := @trDeg_of @trPush_holds @trLin_holds

theorem trDegQ_holds (h : GlobalTheory.EtC.A8) : TrDegQ := @trDegQ_of (@trHl_holds h) @trDeg_holds

theorem famComp_holds : FamComp := @famComp_of @sumComp_holds @fibFin_holds

theorem trComp_holds : TrComp := trComp_of trChar_holds famComp_holds wtComp_holds rpBasic_holds rpOp_holds

theorem trCompQ_holds (h : GlobalTheory.EtC.A8) : TrCompQ := trCompQ_of (trHl_holds h) trComp_holds wtComp_holds

theorem famBC_holds : FamBC := @famBC_of

theorem trBC_holds : TrBC := trBC_of trChar_holds famBC_holds wtBC_holds rpBasic_holds rpOp_holds

theorem trBCQ_holds (h : GlobalTheory.EtC.A8) : TrBCQ := trBCQ_of (trHl_holds h) trBC_holds wtBC_holds

theorem trRel_holds : TrRel := @trRel_of @trLin_holds @wtLin_holds @wtVanish_holds

theorem corrEq_holds : CorrEq := corrEq_of imageFin_holds trRel_holds trPush_holds wtPush_holds

theorem corrEqQ_holds (h : GlobalTheory.EtC.A8) : CorrEqQ := @corrEqQ_of (@trHl_holds h) @corrEq_holds

theorem cycComp_holds : CycComp := @cycComp_of @fibFin_holds

theorem corrBCQ_holds (h : GlobalTheory.EtC.A8) : CorrBCQ := @corrBCQ_of (@trBCQ_holds h)

theorem corrCompQ_holds (h : GlobalTheory.EtC.A8) : CorrCompQ := corrCompQ_of cycComp_holds wtBC_holds wtComp_holds (trBCQ_holds h) (trCompQ_holds h)

theorem trSplitQ_holds (h : GlobalTheory.EtC.A8) : TrSplitQ := trSplitQ_of (trBCQ_holds h) (corrEqQ_holds h) (trIdQ_holds h) wtLin_holds wtFlat_holds multBasic_holds

theorem corrGraphQ_holds (h : GlobalTheory.EtC.A8) : CorrGraphQ := @corrGraphQ_of (@trIdQ_holds h) @wtLin_holds

theorem weights_holds : Weights := ⟨wtBC_holds, wtComp_holds, wtLin_holds, wtPush_holds, wtPt_holds, wtUnique_holds, wtDegConst_holds,
    multBasic_holds, multSum_holds, wtFlat_holds, wtNormal_holds, nmlLoc_holds, nwtFlat_holds, nwtOfFlat_holds,
    nwtDeg_holds⟩

theorem torsion_holds : Torsion :=
  ⟨@trSum_holds, @trBC_holds, @trComp_holds, @trLin_holds, @trPush_holds, @trDeg_holds, @corrEq_holds⟩

theorem adic_holds (h : GlobalTheory.EtC.A8) : Adic := ⟨trRed_holds h, trHl_holds h, trBCQ_holds h, trCompQ_holds h, trDegQ_holds h, corrEqQ_holds h, corrBCQ_holds h,
    corrCompQ_holds h, corrGraphQ_holds h, trSplitQ_holds h⟩

end UpperTheory.Gal.TranscendenceTraces
