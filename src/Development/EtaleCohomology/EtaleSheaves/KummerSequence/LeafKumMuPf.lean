module

public import Development.EtaleCohomology.EtaleSheaves.LeafKillCut

@[expose] public section

section -- merged from Development.EtaleCohomology.EtaleSheaves.KummerSequence.LeafKumSeqPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.E4

namespace LateralTheory.E.H2CurveOrder.LeafKumSeqPf

def powNat (q : ℕ) : unitsF ⟶ unitsF where
  app A := ModuleCat.ofHom
    { toFun := fun g => ⟨q • g.down⟩
      map_add' := fun x y => congrArg ULift.up (smul_add q x.down y.down)
      map_smul' := fun c x => congrArg ULift.up (smul_comm q c.down x.down) }
  naturality A B f := by
    ext x
    exact congrArg ULift.up (map_nsmul _ q x.down).symm

def powGm (q : ℕ) : Gm ⟶ Gm := (presheafToSheaf _ _).map (Functor.whiskerLeft Scheme.Γ (powNat q))

def kumSC (q : ℕ) : ShortComplex (Shv ℤ) :=
  ShortComplex.mk (kernel.ι (powGm q)) (cokernel.π (kernel.ι (powGm q))) (cokernel.condition _)

theorem kumSC_shortExact (q : ℕ) : (kumSC q).ShortExact := by
  have hex : (kumSC q).Exact :=
    ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel (kernel.ι (powGm q)))
  exact { exact := hex, mono_f := by dsimp [kumSC]; infer_instance, epi_g := by dsimp [kumSC]; infer_instance }

def LeafKumMu : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (B : Type) [CommRing B], IsUnit (q : B) →
  Nonempty (H ℤ (sp B) (kernel (powGm q)) 1 ≃+ Ht q (sp B) 1 1)

def KummerUnitsSurjectH0 : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (B : Type) [CommRing B], IsUnit (q : B) →
  ∃ c : Additive Bˣ →+ H ℤ (sp B) (kumSC q).X₃ 0, Function.Surjective c ∧
    ∀ u : Additive Bˣ, c (q • u) ∈ (HK.post ℤ ((chains ℤ).obj (sp B)) (kumSC q).g 0).range

theorem LeafKumSeq_of (hM : LeafKumMu) (hH : KummerUnitsSurjectH0) : LateralTheory.E.LeafKumCut.LeafKumSeq := by
  intro hy q _ B _ hq
  have hA7 : A7 := hy.2.2.2.2.2.1
  obtain ⟨z, hz⟩ := hA7 ℤ (kumSC q) (kumSC_shortExact q)
  obtain ⟨h1, h2, h3⟩ := hz ((chains ℤ).obj (sp B)) 0
  obtain ⟨e1⟩ := hM hy q B hq
  obtain ⟨c, hcs, hcq⟩ := hH hy q B hq
  let δ : H ℤ (sp B) (kumSC q).X₃ 0 →+ H ℤ (sp B) (kernel (powGm q)) 1 :=
    HK.ext ℤ ((chains ℤ).obj (sp B)) z 0 (0 + 1) rfl
  have h2 : Function.Exact (HK.post ℤ ((chains ℤ).obj (sp B)) (kumSC q).g 0) δ := h2
  have h3 : Function.Exact δ (HK.post ℤ ((chains ℤ).obj (sp B)) (kumSC q).f 1) := h3
  let g : Additive Bˣ →+ Ht q (sp B) 1 1 := e1.toAddMonoidHom.comp (δ.comp c)
  let φ : Bˣ →* Multiplicative (Ht q (sp B) 1 1) :=
    { toFun := fun u => Multiplicative.ofAdd (g (Additive.ofMul u))
      map_one' := by simp
      map_mul' := fun x y => by simp only [ofMul_mul, map_add (f := _), ofAdd_add] }
  have hφ : (powMonoidHom q : Bˣ →* Bˣ).range ≤ φ.ker := by
    rintro _ ⟨u, rfl⟩
    rw [MonoidHom.mem_ker]
    have hz0 : δ (c (q • Additive.ofMul u)) = 0 := (h2 _).mpr (hcq _)
    show Multiplicative.ofAdd (e1 (δ (c (Additive.ofMul (u ^ q))))) = 1
    rw [ofMul_pow, hz0, map_zero]
    rfl
  let ψ := QuotientGroup.lift _ φ hφ
  let a : Additive (Bˣ ⧸ (powMonoidHom q : Bˣ →* Bˣ).range) →+ Ht q (sp B) 1 1 :=
    { toFun := fun x => Multiplicative.toAdd (ψ (Additive.toMul x))
      map_zero' := by simp
      map_add' := fun x y => by simp only [toMul_add, map_mul, toAdd_mul] }
  refine ⟨a,
    (HK.post ℤ ((chains ℤ).obj (sp B)) (kumSC q).f 1).comp e1.symm.toAddMonoidHom, ?_⟩
  intro y
  constructor
  · intro hb
    obtain ⟨w, hw⟩ := (h3 (e1.symm y)).mp hb
    obtain ⟨v, rfl⟩ := hcs w
    refine ⟨Additive.ofMul (QuotientGroup.mk (Additive.toMul v)), ?_⟩
    show e1 (δ (c (Additive.ofMul (Additive.toMul v)))) = y
    rw [ofMul_toMul]
    rw [hw]; simp
  · rintro ⟨x, rfl⟩
    obtain ⟨u, hu⟩ := QuotientGroup.mk_surjective (Additive.toMul x)
    have hx : x = Additive.ofMul (QuotientGroup.mk u) := by rw [hu]; rfl
    subst hx
    show HK.post ℤ _ (kumSC q).f 1 (e1.symm (e1 (δ (c (Additive.ofMul u))))) = 0
    rw [AddEquiv.symm_apply_apply]
    exact (h3 _).mpr ⟨_, rfl⟩

end LateralTheory.E.H2CurveOrder.LeafKumSeqPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.KummerSequence.LeafKumMuPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.E4

namespace LateralTheory.E.H2CurveOrder.LeafKumMuPf

variable {R : Type} [CommRing R]

abbrev evU (U : Scheme.{0}) : Shv R ⥤ ModuleCat.{1} (ULift.{1} R) :=
  sheafToPresheaf _ _ ⋙ (evaluation _ _).obj (op U)

theorem kerSec_inj {F G : Shv R} (φ : F ⟶ G) (U : Scheme.{0}) :
    Function.Injective (Sec.map (kernel.ι φ) (U := U)) := by
  have hm : Mono ((evU U).map (kernel.ι φ)) := inferInstance
  exact (ModuleCat.mono_iff_injective _).1 hm

theorem secMap_comp {F G K : Shv R} (f : F ⟶ G) (g : G ⟶ K) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (f ≫ g) x = Sec.map g (Sec.map f x) := rfl

theorem secMap_zero {F G : Shv R} {U : Scheme.{0}} (x : Sec F U) : Sec.map (0 : F ⟶ G) x = 0 := rfl

def LeafKumMuUnits : Prop := ∀ (q : ℕ) [NeZero q] (B : Type) [CommRing B], IsUnit (q : B) →
  ∃ κ : (restr (Int.castRingHom (ZMod q))).obj (tw q 1) ⟶ Gm, κ ≫ LateralTheory.E.H2CurveOrder.LeafKumSeqPf.powGm q = 0 ∧
    ∀ U : Scheme.{0}, Nonempty (Sx (sp B) 0 U) → Function.Injective (Sec.map κ (U := U)) ∧
      ∀ s : Sec Gm U, Sec.map (LateralTheory.E.H2CurveOrder.LeafKumSeqPf.powGm q) s = 0 → ∃ t, Sec.map κ t = s

def LeafKumMuSec : Prop := ∀ (q : ℕ) [NeZero q] (B : Type) [CommRing B], IsUnit (q : B) →
  ∃ κ : (restr (Int.castRingHom (ZMod q))).obj (tw q 1) ⟶ kernel (LateralTheory.E.H2CurveOrder.LeafKumSeqPf.powGm q),
    ∀ U : Scheme.{0}, Nonempty (Sx (sp B) 0 U) → Function.Bijective (Sec.map κ (U := U))

theorem LeafKumMuSec_of (hU : LeafKumMuUnits) : LeafKumMuSec := by
  intro q _ B _ hq
  obtain ⟨κ, h0, hκ⟩ := hU q B hq
  refine ⟨kernel.lift _ κ h0, fun U hUB => ?_⟩
  obtain ⟨hi, hs⟩ := hκ U hUB
  have hc : ∀ t : Sec ((restr (Int.castRingHom (ZMod q))).obj (tw q 1)) U, Sec.map (kernel.ι _) (Sec.map (kernel.lift _ κ h0) t) = Sec.map κ t := by
    intro t; rw [← secMap_comp, kernel.lift_ι]
  refine ⟨fun a b hab => hi ?_, fun y => ?_⟩
  · rw [← hc, ← hc, hab]
  · obtain ⟨t, ht⟩ := hs (Sec.map (kernel.ι _) y) (by rw [← secMap_comp, kernel.condition, secMap_zero])
    exact ⟨t, kerSec_inj _ U (by rw [hc, ht])⟩

theorem LeafKumMu_of (h8 : A8) (h10 : A10) (hU : LeafKumMuUnits) : LateralTheory.E.H2CurveOrder.LeafKumSeqPf.LeafKumMu := by
  intro _ q _ B _ hq
  obtain ⟨κ, hκ⟩ := LeafKumMuSec_of hU q B hq
  have b1 := h8 ℤ (ZMod q) (Int.castRingHom (ZMod q)) (sp B) (tw q 1) 1
  have b2 := h10 ℤ (sp B) κ hκ 1
  exact ⟨((AddEquiv.ofBijective _ b1).trans (AddEquiv.ofBijective _ b2)).symm⟩

end LateralTheory.E.H2CurveOrder.LeafKumMuPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.KummerSequence.KummerH0Surjection
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.E4 LateralTheory.E.H2CurveOrder.LeafKumSeqPf
open CochainComplex CochainComplex.HomComplex

namespace LateralTheory.E.H2CurveOrder.KummerH0Surjection

theorem resMap_comp_homotopy (R : Type) [CommRing R] {F G L : Shv R} (f : F ⟶ G) (g : G ⟶ L) :
    Nonempty (Homotopy (resMap R (f ≫ g)) (resMap R f ≫ resMap R g)) := by
  refine ⟨?_⟩
  have H : Homotopy (InjectiveResolution.desc (f ≫ g) (injectiveResolution L) (injectiveResolution F))
      (InjectiveResolution.desc f (injectiveResolution G) (injectiveResolution F) ≫
        InjectiveResolution.desc g (injectiveResolution L) (injectiveResolution G)) :=
    InjectiveResolution.descHomotopy (f ≫ g) _ _ (by simp) (by simp)
  exact (H.extend ComplexShape.embeddingUpNat).trans
    (Homotopy.ofEq (HomologicalComplex.extendMap_comp _ _ _))

theorem post_comp (R : Type) [CommRing R] (K : Cx R) {F G L : Shv R} (f : F ⟶ G) (g : G ⟶ L) (n : ℤ)
    (x : HK R K F n) : HK.post R K (f ≫ g) n x = HK.post R K g n (HK.post R K f n x) := by
  obtain ⟨H⟩ := resMap_comp_homotopy R f g
  obtain ⟨a, rfl⟩ := CohomologyClass.mk_surjective x
  show CohomologyClass.mk _ = CohomologyClass.mk _
  rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff,
    mem_coboundaries_iff _ (n - 1) (by omega)]
  refine ⟨a.1.comp (Cochain.ofHomotopy H) (by omega), ?_⟩
  rw [δ_comp _ _ _ (n + 1) 0 n (by omega) rfl (by omega), δ_ofHomotopy, Cocycle.δ_eq_zero]
  simp [zcomp, Cochain.comp_sub, Cochain.ofHom_comp]

def kumM (q : ℕ) : (kumSC q).X₃ ⟶ Gm := cokernel.desc (kernel.ι (powGm q)) (powGm q) (kernel.condition _)

instance kumM_mono (q : ℕ) : Mono (kumM q) :=
  inferInstanceAs (Mono (Abelian.factorThruCoimage (powGm q)))

theorem sec_injective {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) [Mono φ] (U : Scheme.{0}) :
    Function.Injective (Sec.map φ (U := U)) := by
  have h1 : Mono φ.hom := (sheafToPresheaf _ _).map_mono φ
  have h2 : Mono (φ.hom.app (op U)) := (NatTrans.mono_iff_mono_app _).mp h1 (op U)
  exact (ModuleCat.mono_iff_injective _).mp h2

def LeafKumSecSurj : Prop := ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) →
  Function.Surjective (Sec.map (kumM q) (U := U))

def LeafKumBij : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (B : Type) [CommRing B], IsUnit (q : B) →
  Function.Bijective (HK.post ℤ ((chains ℤ).obj (sp B)) (kumM q) 0)

theorem LeafKumBij_of (hS : LeafKumSecSurj) : LeafKumBij := by
  intro hy q _ B _ hq
  have hA10 : A10 := hy.2.2.2.2.2.2.2.2.1
  refine hA10 ℤ (sp B) (kumM q) ?_ 0
  intro U ⟨x⟩
  refine ⟨sec_injective _ U, hS q U ?_⟩
  have x' : U ⟶ Spec (CommRingCat.of B) := x
  have h1 : IsUnit ((q : ℕ) : Γ(Spec (CommRingCat.of B), ⊤)) := by
    have := hq.map (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom
    simpa using this
  simpa using h1.map x'.appTop.hom

def unitsToSec (U : Scheme.{0}) : Additive (Γ(U, ⊤))ˣ →+ Sec Gm U where
  toFun x := ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ unitsF)).app (op U)).hom ⟨x⟩
  map_zero' := by
    have := map_zero ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ unitsF)).app (op U)).hom
    exact this
  map_add' x y := by
    have := map_add ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ unitsF)).app (op U)).hom
      (⟨x⟩ : ULift (Additive (Γ(U, ⊤))ˣ)) ⟨y⟩
    exact this

theorem pow_unitsToSec (q : ℕ) (U : Scheme.{0}) (x : Additive (Γ(U, ⊤))ˣ) :
    Sec.map (powGm q) (unitsToSec U x) = unitsToSec U (q • x) := by
  have h := toSheafify_naturality Scheme.etaleTopology (Functor.whiskerLeft Scheme.Γ (powNat q))
  have h2 := congrArg (fun η => (η.app (op U)).hom (⟨x⟩ : ULift (Additive (Γ(U, ⊤))ˣ))) h
  exact h2.symm

def EtaleDegreeZeroCohomologyNaturallyIsoToSections : Prop := Hyps → ∃ e : ∀ (F : Shv ℤ) (X : Scheme.{0}), Sec F X ≃+ H ℤ (sch.obj X) F 0,
  ∀ {F G : Shv ℤ} (φ : F ⟶ G) (X : Scheme.{0}) (s : Sec F X),
    HK.post ℤ ((chains ℤ).obj (sch.obj X)) φ 0 (e F X s) = e G X (Sec.map φ s)

def LeafGmSecSurj : Prop := ∀ (B : Type) [CommRing B],
  Function.Surjective (unitsToSec (Spec (CommRingCat.of B)))

def EtaleUnitsDegreeZeroCohomologySurjectiveFromRingUnits : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (B : Type) [CommRing B],
  ∃ u : Additive Bˣ →+ H ℤ (sp B) Gm 0, Function.Surjective u ∧
    ∀ x : Additive Bˣ, HK.post ℤ ((chains ℤ).obj (sp B)) (powGm q) 0 (u x) = u (q • x)

theorem etale_units_degree_zero_cohomology_of_natural_iso_and_surjective (hN : EtaleDegreeZeroCohomologyNaturallyIsoToSections) (hS : LeafGmSecSurj) : EtaleUnitsDegreeZeroCohomologySurjectiveFromRingUnits := by
  intro hy q _ B _
  obtain ⟨e, he⟩ := hN hy
  let ψ : Bˣ →* (Γ(Spec (CommRingCat.of B), ⊤))ˣ :=
    Units.map (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom.toMonoidHom
  have hψ : Function.Surjective ψ := by
    intro v
    refine ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom.toMonoidHom v, ?_⟩
    ext
    simp [ψ]
  let u : Additive Bˣ →+ H ℤ (sp B) Gm 0 :=
    ((e Gm (Spec (CommRingCat.of B))).toAddMonoidHom.comp (unitsToSec _)).comp (MonoidHom.toAdditive ψ)
  refine ⟨u, ?_, ?_⟩
  · intro y
    obtain ⟨s, rfl⟩ := (e Gm (Spec (CommRingCat.of B))).surjective y
    obtain ⟨v, rfl⟩ := hS B s
    obtain ⟨w, hw⟩ := hψ (Additive.toMul v)
    exact ⟨Additive.ofMul w, by simp [u, hw]⟩
  · intro x
    simp only [u, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom]
    rw [he, pow_unitsToSec, ← map_nsmul (MonoidHom.toAdditive ψ)]

theorem kumSC_g_kumM (q : ℕ) : (kumSC q).g ≫ kumM q = powGm q := cokernel.π_desc _ _ _

theorem etale_kummer_degree_zero_cohomology_of_sections_and_units_surjective (hS : LeafKumSecSurj) (hN : EtaleDegreeZeroCohomologyNaturallyIsoToSections) (hG : LeafGmSecSurj) :
    LateralTheory.E.H2CurveOrder.LeafKumSeqPf.KummerUnitsSurjectH0 := by
  intro hy q _ B _ hq
  obtain ⟨u, hus, hu⟩ := etale_units_degree_zero_cohomology_of_natural_iso_and_surjective hN hG hy q B
  let e := AddEquiv.ofBijective (HK.post ℤ ((chains ℤ).obj (sp B)) (kumM q) 0) (LeafKumBij_of hS hy q B hq)
  refine ⟨e.symm.toAddMonoidHom.comp u, e.symm.surjective.comp hus, ?_⟩
  intro x
  refine ⟨u x, ?_⟩
  apply e.injective
  show HK.post ℤ ((chains ℤ).obj (sp B)) (kumM q) 0 (HK.post ℤ ((chains ℤ).obj (sp B)) (kumSC q).g 0 (u x)) =
    e (e.symm (u (q • x)))
  rw [AddEquiv.apply_symm_apply, ← hu]
  have h := post_comp ℤ ((chains ℤ).obj (sp B)) (kumSC q).g (kumM q) 0 (u x)
  have h2 : HK.post ℤ ((chains ℤ).obj (sp B)) ((kumSC q).g ≫ kumM q) 0 (u x) =
      HK.post ℤ ((chains ℤ).obj (sp B)) (powGm q) 0 (u x) := by
    erw [kumSC_g_kumM]; rfl
  exact h.symm.trans h2

end LateralTheory.E.H2CurveOrder.KummerH0Surjection
end
end
