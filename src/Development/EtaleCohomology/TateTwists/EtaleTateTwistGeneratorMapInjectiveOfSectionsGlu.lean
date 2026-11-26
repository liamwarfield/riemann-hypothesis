module

public import Development.EtaleCohomology.TateTwists.EtaleLocallyExistsPrimitiveRootOfUnityOfInvertib
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.SelmerDuality.ZModInj
public import Development.EtaleCohomology.TateTwists.EtaleChainCochainEvalBasicPropertiesHold
public import Development.EtaleCohomology.TateTwists.EtaleSimplicialCochainExistsFromNaturalSections
public import Development.EtaleCohomology.TateTwists.ExistsEtaleKummerChernClassCochainOfDegreeValues

@[expose] public section

section -- merged from Development.EtaleCohomology.TateTwists.EtaleTateTwistGeneratorMapInjectiveOfSectionsGlu
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped TensorProduct DirectSum

noncomputable section
namespace LateralTheory.EtaleFoundations.GenIsoInj

theorem ulift_smul_eq {q : ℕ} [NeZero q] {M : Type*} [AddCommGroup M] [Module (ULift.{1} (ZMod q)) M]
    (r : ULift.{1} (ZMod q)) (x : M) : r • x = r.down.val • x := by
  have : r = ((r.down.val : ℕ) : ULift.{1} (ZMod q)) := by
    apply ULift.ext; simp only [ULift.down_natCast, ZMod.natCast_zmod_val]
  conv_lhs => rw [this]
  rw [Nat.cast_smul_eq_nsmul]

theorem q_smul {q : ℕ} [NeZero q] {M : Type*} [AddCommGroup M] [Module (ULift.{1} (ZMod q)) M]
    (c : ℕ) (hc : q ∣ c) (x : M) : c • x = 0 := by
  rw [← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q))]
  have : ((c : ℕ) : ULift.{1} (ZMod q)) = 0 := by
    ext; simpa using (ZMod.natCast_eq_zero_iff c q).2 hc
  rw [this, zero_smul]

theorem exists_functional {q : ℕ} [NeZero q] {M : Type 1} [AddCommGroup M] [Module (ULift.{1} (ZMod q)) M]
    (g : M) (hg : ∀ c : ℕ, c • g = 0 → q ∣ c) :
    ∃ F : M →ₗ[ULift.{1} (ZMod q)] ULift.{1} (ZMod q), F g = 1 := by
  letI : Module (ZMod q) M :=
    Module.compHom M (ULift.ringEquiv.symm : ZMod q ≃+* ULift.{1} (ZMod q)).toRingHom
  have hsm : ∀ (r : ZMod q) (x : M), r • x = (ULift.up r : ULift.{1} (ZMod q)) • x := fun r x => rfl
  let f : ZMod q →ₗ[ZMod q] M := LinearMap.toSpanSingleton (ZMod q) M g
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro r hr
    have h1 : r.val • g = 0 := by
      have h2 : (ULift.up r : ULift.{1} (ZMod q)) • g = 0 := hr
      have h4 := ulift_smul_eq (M := M) (ULift.up r : ULift.{1} (ZMod q)) g
      exact h4.symm.trans h2
    have h3 := hg _ h1
    rw [← ZMod.natCast_zmod_val r]
    exact (ZMod.natCast_eq_zero_iff _ _).2 h3
  obtain ⟨h, hh⟩ := (KStar.Selmer.zmod_baer (N := q)).extension_property f hf LinearMap.id
  refine ⟨{ toFun := fun x => ULift.up (h x), map_add' := fun x y => by ext; simp,
             map_smul' := fun r x => ?_ }, ?_⟩
  · change ULift.up (h (r.down • x)) = r • ULift.up (h x)
    rw [h.map_smul]
    ext; simp [smul_eq_mul]
  · have := LinearMap.congr_fun hh 1
    simp only [LinearMap.comp_apply, f, LinearMap.toSpanSingleton_apply, one_smul, LinearMap.id_apply] at this
    ext; simpa using this

theorem dvd_of_tmul {q : ℕ} [NeZero q] {M N : Type 1} [AddCommGroup M] [Module (ULift.{1} (ZMod q)) M]
    [AddCommGroup N] [Module (ULift.{1} (ZMod q)) N] (g : M) (g' : N)
    (hg : ∀ c : ℕ, c • g = 0 → q ∣ c) (hg' : ∀ c : ℕ, c • g' = 0 → q ∣ c) (c : ℕ)
    (h : c • (g ⊗ₜ[ULift.{1} (ZMod q)] g') = 0) : q ∣ c := by
  obtain ⟨F, hF⟩ := exists_functional g hg
  obtain ⟨F', hF'⟩ := exists_functional g' hg'
  let L := TensorProduct.lift ((LinearMap.mul (ULift.{1} (ZMod q)) (ULift.{1} (ZMod q))).compl₂ F' ∘ₗ F)
  have := congrArg L h
  simp only [map_nsmul, L, TensorProduct.lift.tmul, LinearMap.comp_apply, LinearMap.compl₂_apply,
    LinearMap.mul_apply', hF, hF', mul_one, map_zero, nsmul_eq_mul] at this
  have h2 := congrArg ULift.down this
  simp at h2
  exact (ZMod.natCast_eq_zero_iff _ _).1 h2

end LateralTheory.EtaleFoundations.GenIsoInj

namespace LateralTheory.EtaleFoundations.GenIsoInj

theorem res_comp {R : Type} [CommRing R] {F : Shv R} {W V U : Scheme.{0}} (h : W ⟶ V) (g : V ⟶ U)
    (x : Sec F U) : Sec.res (h ≫ g) x = Sec.res h (Sec.res g x) := by
  simp [Sec.res]

theorem sm_nsmul {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (c : ℕ) (x : Sec F U) :
    Sec.map φ (c • x) = c • Sec.map φ x := map_nsmul _ _ _
theorem sm_zero {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} :
    Sec.map φ (0 : Sec F U) = 0 := map_zero _
theorem sr_nsmul {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (c : ℕ) (x : Sec F U) :
    Sec.res g (c • x) = c • Sec.res g x := map_nsmul _ _ _
theorem sr_zero {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) :
    Sec.res g (0 : Sec F U) = 0 := map_zero _

theorem sgl_smul_eq_zero {q : ℕ} {F : Shv (ZMod q)} {U : Scheme.{0}} (c : ℕ) (x : Sec F U)
    (h : c • Sec.map (sglι F) x = 0) : c • x = 0 := by
  let ψ : (sgl F).X 0 ⟶ F := (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).hom
  have hψ : sglι F ≫ ψ = 𝟙 F := (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).inv_hom_id
  have e : ∀ y : Sec F U, Sec.map ψ (Sec.map (sglι F) y) = y := fun y => by
    rw [TwMulPf.sec_map_comp, hψ, TwMulPf.sec_map_id]
  have h' : Sec.map (sglι F) (c • x) = Sec.map (sglι F) 0 := by
    rw [show Sec.map (sglι F) (c • x) = c • Sec.map (sglι F) x from map_nsmul _ c x, h]
    exact (map_zero _).symm
  have := congrArg (Sec.map ψ) h'
  rwa [e, e] at this

end LateralTheory.EtaleFoundations.GenIsoInj


open LateralTheory.EtaleFoundations.GenIsoInj LateralTheory.EtaleFoundations.TwMulPf in
theorem LateralTheory.EtaleFoundations.etale_tate_twist_generator_map_injective_of_sections_glue (hts : LateralTheory.EtaleFoundations.EtaleTateTwistSectionsLocallyGenerated)
    (hlb : LateralTheory.EtaleFoundations.EtaleLocalPropertyBasicClosure) (hsg : LateralTheory.EtaleFoundations.EtaleSheafSectionsSeparatedAndGlue) :
    LateralTheory.EtaleFoundations.EtaleTateTwistGeneratorMapSectionsInjective := by
  classical
  intro q _ i j k T μ hμ hk φ hφ U a ha
  have nt : ∀ (l : ℤ) (W : Scheme.{0}) [Nonempty W] (ζ : Prim q Γ(W, ⊤)) (c : ℕ),
      c • Sec.map (sglι (tw q l)) (twGen l ζ) = 0 → q ∣ c :=
    fun l W _ ζ c h => (hts q l).2.2.1 W ζ c (LateralTheory.EtaleFoundations.GenIsoInj.sgl_smul_eq_zero c _ h)
  refine hlb.2.2.2.2.1 U _ (hlb.2.1 U _ _ ((hts q k).1 U a) ?_)
  rintro V g (h0 | ⟨ζ, c, hc⟩)
  · exact hlb.1 V _ fun W h => by rw [LateralTheory.EtaleFoundations.GenIsoInj.res_comp, h0, LateralTheory.EtaleFoundations.GenIsoInj.sr_zero]
  · have h1 : c • μ.mul V 0 0 0 (add_zero 0) (Sec.map (sglι _) (twGen i ζ))
        (Sec.map (sglι _) (twGen j ζ)) = 0 := by
      rw [← hφ V ζ, ← LateralTheory.EtaleFoundations.GenIsoInj.sm_nsmul, ← LateralTheory.EtaleFoundations.GenIsoInj.sm_nsmul, ← hc, ← LateralTheory.EtaleFoundations.TwMulPf.sec_res_map, ha, LateralTheory.EtaleFoundations.GenIsoInj.sr_zero, LateralTheory.EtaleFoundations.GenIsoInj.sm_zero]
    let x : Tens (sgl (tw q i)) (sgl (tw q j)) V 0 :=
      DirectSum.lof (ULift.{1} (ZMod q)) {p : ℤ × ℤ // p.1 + p.2 = 0}
        (fun p => Sec ((sgl (tw q i)).X p.1.1) V ⊗[ULift.{1} (ZMod q)] Sec ((sgl (tw q j)).X p.1.2) V)
        ⟨(0, 0), rfl⟩ (c • (Sec.map (sglι _) (twGen i ζ) ⊗ₜ Sec.map (sglι _) (twGen j ζ)))
    have hx : μ.lift V 0 x = 0 := by
      simp only [x, Pair.lift, DirectSum.toModule_lof, map_nsmul, TensorProduct.lift.tmul]
      exact h1
    refine hlb.2.1 V _ _ (hμ.2 V 0 x hx) fun W h hW => ?_
    have hW' : c • (Sec.res h (Sec.map (sglι _) (twGen i ζ)) ⊗ₜ[ULift.{1} (ZMod q)]
        Sec.res h (Sec.map (sglι _) (twGen j ζ))) = 0 := by
      have := congrArg (DirectSum.component (ULift.{1} (ZMod q)) {p : ℤ × ℤ // p.1 + p.2 = 0}
        (fun p => Sec ((sgl (tw q i)).X p.1.1) W ⊗[ULift.{1} (ZMod q)] Sec ((sgl (tw q j)).X p.1.2) W)
        ⟨(0, 0), rfl⟩) hW
      simpa [x, Tens.res, DirectSum.component.lof_self] using this
    show Sec.res (h ≫ g) a = 0
    rw [LateralTheory.EtaleFoundations.GenIsoInj.res_comp, hc, LateralTheory.EtaleFoundations.GenIsoInj.sr_nsmul]
    by_cases hne : Nonempty W
    · rw [LateralTheory.EtaleFoundations.TwMulPf.sec_res_map, LateralTheory.EtaleFoundations.TwMulPf.sec_res_map, (hts q i).2.2.2.1, (hts q j).2.2.2.1] at hW'
      exact LateralTheory.EtaleFoundations.GenIsoInj.q_smul c (LateralTheory.EtaleFoundations.GenIsoInj.dvd_of_tmul _ _ (nt i W _) (nt j W _) c hW') _
    · have : IsEmpty W := not_nonempty_iff.1 hne
      exact (hsg (ZMod q) (tw q k) W).1 _ _ (hlb.2.2.2.2.2.2 W _)
end
end

section -- merged from Development.EtaleCohomology.TateTwists.EtaleTensorPairingSectionsLocallyFiniteSums
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

def LateralTheory.EtaleFoundations.EtaleTensorPairingSectionsLocallyFiniteSums : Prop :=
  ∀ (R : Type) [CommRing R] (F G T : Shv R) (μ : Pair (sgl F) (sgl G) (sgl T)), μ.IsTensor →
    ∀ (U : Scheme.{0}) (y : Sec ((sgl T).X 0) U), Loc U fun V g => ∃ (n : ℕ) (a : Fin n → Sec F V) (b : Fin n → Sec G V),
      Sec.res g y = ∑ m, μ.mul V 0 0 0 (add_zero 0) (Sec.map (sglι F) (a m)) (Sec.map (sglι G) (b m))

def LateralTheory.EtaleFoundations.EtaleTateTwistGeneratorMapHitsProductsLocally : Prop :=
  ∀ (q : ℕ) [NeZero q] (i j k : ℤ) (T : Shv (ZMod q)) (μ : Pair (sgl (tw q i)) (sgl (tw q j)) (sgl T)),
    i + j = k → ∀ φ : tw q k ⟶ T, (∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)),
      Sec.map (sglι T) (Sec.map φ (twGen k ζ)) =
        μ.mul U 0 0 0 (add_zero 0) (Sec.map (sglι _) (twGen i ζ)) (Sec.map (sglι _) (twGen j ζ))) →
    ∀ (U : Scheme.{0}) (a : Sec (tw q i) U) (b : Sec (tw q j) U), Loc U fun V g => ∃ c : Sec (tw q k) V,
      Sec.map (sglι T) (Sec.map φ c) =
        μ.mul V 0 0 0 (add_zero 0) (Sec.map (sglι _) (Sec.res g a)) (Sec.map (sglι _) (Sec.res g b))

namespace LateralTheory.EtaleFoundations.GenIsoSurjPf

variable {R : Type} [CommRing R]

theorem loc_mono' {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (hP : Loc U P)
    (h : ∀ V g, P V g → Q V g) : Loc U Q := by
  obtain ⟨S, hS, h'⟩ := hP
  exact ⟨S, hS, fun V g hg => h V g (h' V g hg)⟩

theorem loc_top' {U : Scheme.{0}} {P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : ∀ V g, P V g) : Loc U P :=
  ⟨⊤, Scheme.etaleTopology.top_mem U, fun V g _ => h V g⟩

theorem loc_and' {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (hP : Loc U P) (hQ : Loc U Q) :
    Loc U fun V g => P V g ∧ Q V g := by
  obtain ⟨S, hS, h⟩ := hP
  obtain ⟨T, hT, h'⟩ := hQ
  exact ⟨S ⊓ T, Scheme.etaleTopology.intersection_covering hS hT, fun V g hg => ⟨h V g hg.1, h' V g hg.2⟩⟩

theorem loc_bind' {U : Scheme.{0}} {P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop}
    (h : Loc U fun V g => Loc V fun W k => P W (k ≫ g)) : Loc U P := by
  obtain ⟨S, hS, h'⟩ := h
  choose T hT hP using h'
  refine ⟨Sieve.bind S.arrows fun V g hg => T V g hg, Scheme.etaleTopology.bind_covering hS hT, ?_⟩
  rintro W f ⟨V, k, g, hg, hk, rfl⟩
  exact hP V g hg W k hk

theorem loc_fin {U : Scheme.{0}} : ∀ (n : ℕ) (P : Fin n → ∀ V : Scheme.{0}, (V ⟶ U) → Prop),
    (∀ m, Loc U (P m)) → Loc U fun V g => ∀ m, P m V g
  | 0, _, _ => loc_top' fun _ _ m => m.elim0
  | n + 1, P, h => loc_mono' (loc_and' (h 0) (loc_fin n (fun m => P m.succ) fun m => h m.succ))
      fun _ _ hv m => Fin.cases hv.1 hv.2 m

theorem res_res {F : Shv R} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (x : Sec F U) :
    Sec.res k (Sec.res g x) = Sec.res (k ≫ g) x := by
  simp [Sec.res]

theorem res_map {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.res g (Sec.map φ x) = Sec.map φ (Sec.res g x) := by
  have := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (φ.hom.naturality g.op)) x
  simpa using this.symm

theorem map_id' {F : Shv R} {U : Scheme.{0}} (x : Sec F U) : Sec.map (𝟙 F) x = x := by
  simp [Sec.map]

theorem sglι_inj (F : Shv R) {U : Scheme.{0}} {x y : Sec F U}
    (h : Sec.map (sglι F) x = Sec.map (sglι F) y) : x = y := by
  have e : ∀ z : Sec F U, Sec.map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).hom
      (Sec.map (sglι F) z) = z := by
    intro z
    change Sec.map (sglι F ≫ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).hom) z = z
    rw [sglι]
    erw [Iso.inv_hom_id]
    exact map_id' z
  rw [← e x, ← e y, h]

end LateralTheory.EtaleFoundations.GenIsoSurjPf

namespace LateralTheory.EtaleFoundations.GenIsoSurjPf

variable {R : Type} [CommRing R]

theorem sec_zero_of_isZero {F : Shv R} (hF : IsZero F) {U : Scheme.{0}} (x : Sec F U) : x = 0 := by
  have h1 : Sec.map (𝟙 F) x = Sec.map (0 : F ⟶ F) x := by rw [hF.eq_of_src (𝟙 F) 0]
  rw [map_id'] at h1
  rw [h1]
  simp [Sec.map]

theorem sglι_surj (F : Shv R) {U : Scheme.{0}} (y : Sec ((sgl F).X 0) U) : ∃ a : Sec F U, Sec.map (sglι F) a = y := by
  refine ⟨Sec.map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).hom y, ?_⟩
  change Sec.map ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).hom ≫ sglι F) y = y
  rw [sglι]
  erw [Iso.hom_inv_id]
  exact map_id' y

def IsSum {F G T : Shv R} (μ : Pair (sgl F) (sgl G) (sgl T)) (V : Scheme.{0}) (z : Sec ((sgl T).X 0) V) : Prop :=
  ∃ (n : ℕ) (a : Fin n → Sec F V) (b : Fin n → Sec G V),
    z = ∑ m, μ.mul V 0 0 0 (add_zero 0) (Sec.map (sglι F) (a m)) (Sec.map (sglι G) (b m))

theorem isSum_zero {F G T : Shv R} (μ : Pair (sgl F) (sgl G) (sgl T)) (V : Scheme.{0}) : IsSum μ V 0 :=
  ⟨0, Fin.elim0, Fin.elim0, by simp⟩

theorem isSum_add {F G T : Shv R} (μ : Pair (sgl F) (sgl G) (sgl T)) (V : Scheme.{0}) {z w : Sec ((sgl T).X 0) V}
    (hz : IsSum μ V z) (hw : IsSum μ V w) : IsSum μ V (z + w) := by
  obtain ⟨n, a, b, rfl⟩ := hz
  obtain ⟨n', a', b', rfl⟩ := hw
  refine ⟨n + n', Fin.append a a', Fin.append b b', ?_⟩
  rw [Fin.sum_univ_add]
  simp [Fin.append_left, Fin.append_right]

theorem isSum_lift {F G T : Shv R} (μ : Pair (sgl F) (sgl G) (sgl T)) (V : Scheme.{0})
    (x : Tens (sgl F) (sgl G) V 0) : IsSum μ V (μ.lift V 0 x) := by
  classical
  induction x using DirectSum.induction_on with
  | zero => simpa using isSum_zero μ V
  | add x y hx hy => simpa using isSum_add μ V hx hy
  | of p t =>
    obtain ⟨⟨s, u⟩, hsu⟩ := p
    have hl : μ.lift V 0 (DirectSum.of _ ⟨⟨s, u⟩, hsu⟩ t) = TensorProduct.lift (μ.mul V s u 0 hsu) t := by
      simp [Pair.lift, ← DirectSum.lof_eq_of (ULift.{1} R)]
    rw [hl]
    clear hl
    induction t using TensorProduct.induction_on with
    | zero => simpa using isSum_zero μ V
    | add x y hx hy => simpa using isSum_add μ V hx hy
    | tmul a b =>
      simp only [TensorProduct.lift.tmul]
      by_cases hs : s = 0
      · subst hs
        have hu : u = 0 := by simpa using hsu
        subst hu
        obtain ⟨a', rfl⟩ := sglι_surj F a
        obtain ⟨b', rfl⟩ := sglι_surj G b
        exact ⟨1, fun _ => a', fun _ => b', by simp⟩
      · have ha : a = 0 := sec_zero_of_isZero
          (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 F s hs) a
        rw [ha]
        simpa using isSum_zero μ V

theorem etale_tensor_pairing_sections_locally_finite_sums : LateralTheory.EtaleFoundations.EtaleTensorPairingSectionsLocallyFiniteSums := by
  intro R _ F G T μ hμ U y
  refine loc_mono' (hμ.1 U 0 y) fun V g ⟨x, hx⟩ => ?_
  obtain ⟨n, a, b, h⟩ := isSum_lift μ V x
  exact ⟨n, a, b, hx ▸ h⟩

end LateralTheory.EtaleFoundations.GenIsoSurjPf

open LateralTheory.EtaleFoundations.GenIsoSurjPf in
theorem LateralTheory.EtaleFoundations.etale_tate_twist_generator_map_locally_surjective_of_pairs (hp : LateralTheory.EtaleFoundations.EtaleTateTwistGeneratorMapHitsProductsLocally) : LateralTheory.EtaleFoundations.EtaleTateTwistGeneratorMapLocallySurjective := by
  intro q _ i j k T μ hμ hk φ hφ U b
  refine loc_bind' (loc_mono' (etale_tensor_pairing_sections_locally_finite_sums (ZMod q) _ _ _ μ hμ U (Sec.map (sglι T) b)) fun V g ⟨n, a, c, hy⟩ => ?_)
  refine loc_mono' (loc_fin n _ fun m => hp q i j k T μ hk φ hφ V (a m) (c m)) fun W h hW => ?_
  choose e he using hW
  refine ⟨∑ m, e m, sglι_inj T ?_⟩
  rw [← res_map, ← res_res, hy]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, he, μ.nat, res_map]
end
end

section -- merged from Development.EtaleCohomology.TateTwists.EtaleTwistedResolutionExistsOfFlatSections
section -- merged from Development.EtaleCohomology.TateTwists.EtaleInjectiveSheafSectionsInjectiveHolds
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.TwResSecInj

theorem sigma_map_mono (R : Type) [CommRing R] (ι : Type) {X Y : ModuleCat.{1} (ULift.{1} R)} (f : X ⟶ Y) [Mono f] :
    Mono (Limits.Sigma.map (fun (_ : ι) => f)) := by
  let α : Discrete.functor (fun (_ : ι) => X) ⟶ Discrete.functor (fun _ => Y) := Discrete.natTrans (fun _ => f)
  have : ∀ j, Mono (α.app j) := fun j => by
    change Mono f; infer_instance
  have h1 : Mono α := NatTrans.mono_of_mono_app _
  exact (colim : (Discrete ι ⥤ ModuleCat.{1} (ULift.{1} R)) ⥤ _).map_mono α

instance evLA_mono (R : Type) [CommRing R] (U : Scheme.{0}) :
    (evaluationLeftAdjoint (ModuleCat.{1} (ULift.{1} R)) (op U)).PreservesMonomorphisms where
  preserves {X Y} f _ := by
    have hm : ∀ c, Mono (((evaluationLeftAdjoint (ModuleCat.{1} (ULift.{1} R)) (op U)).map f).app c) := by
      intro c
      rw [evaluationLeftAdjoint_map_app]
      have e : (Limits.Sigma.desc fun h => f ≫ Sigma.ι (fun _ => Y) h) = Limits.Sigma.map (fun (_ : op U ⟶ c) => f) := by
        ext; simp
      rw [e]; exact sigma_map_mono R _ f
    exact NatTrans.mono_of_mono_app _

end LateralTheory.EtaleFoundations.TwResSecInj

open LateralTheory.EtaleFoundations.TwResSecInj in
theorem LateralTheory.EtaleFoundations.etale_injective_sheaf_sections_injective_holds : LateralTheory.EtaleFoundations.EtaleInjectiveSheafSectionsInjective := by
  intro R _ M _ U
  have adj := (evaluationAdjunctionRight (ModuleCat.{1} (ULift.{1} R)) (op U)).comp
    (sheafificationAdjunction Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R)))
  have hI := Injective.injective_of_adjoint adj M
  exact Module.injective_module_of_injective_object (inj := hI) _ _
end

section -- merged from Development.EtaleCohomology.TateTwists.ZmodInjectiveModuleFlatHolds
namespace LateralTheory.EtaleFoundations.QFFlat

universe u v

open TensorProduct

theorem zmod_P (q : ℕ) [NeZero q] (a : ZMod q) :
    ∃ b : ZMod q, b * a = 0 ∧ ∀ r : ZMod q, r * b = 0 → ∃ c, c * a = r := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  set n := a.val with hn
  set g := Nat.gcd n q with hg
  have hgq : g ∣ q := Nat.gcd_dvd_right n q
  have hgn : g ∣ n := Nat.gcd_dvd_left n q
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_right n hq
  have ha : (n : ZMod q) = a := ZMod.natCast_zmod_val a
  refine ⟨((q / g : ℕ) : ZMod q), ?_, fun r hr => ?_⟩
  · rw [← ha, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff]
    obtain ⟨t, ht⟩ := hgn
    refine ⟨t, ?_⟩
    rw [ht, ← mul_assoc, Nat.div_mul_cancel hgq]
  · have hr' : (r.val : ZMod q) = r := ZMod.natCast_zmod_val r
    rw [← hr', ← Nat.cast_mul, ZMod.natCast_eq_zero_iff] at hr
    have hqg : 0 < q / g := Nat.div_pos (Nat.le_of_dvd hq hgq) hgpos
    have hdiv : g ∣ r.val := by
      have h1 : g * (q / g) ∣ r.val * (q / g) := by rwa [Nat.mul_div_cancel' hgq]
      exact Nat.dvd_of_mul_dvd_mul_right hqg h1
    obtain ⟨j, hj⟩ := hdiv
    have hbez : ((g : ℤ) : ZMod q) = (n : ZMod q) * ((Nat.gcdA n q : ℤ) : ZMod q) := by
      rw [hg, Nat.gcd_eq_gcd_ab n q]
      push_cast
      simp
    refine ⟨((Nat.gcdA n q : ℤ) : ZMod q) * (j : ZMod q), ?_⟩
    rw [← hr', hj, ← ha]
    push_cast at hbez ⊢
    rw [hbez]
    ring

theorem ulift_P (q : ℕ) [NeZero q] (a : ULift.{1} (ZMod q)) :
    ∃ b : ULift.{1} (ZMod q), b * a = 0 ∧ ∀ r : ULift.{1} (ZMod q), r * b = 0 → ∃ c, c * a = r := by
  obtain ⟨b, hb, h⟩ := zmod_P q a.down
  refine ⟨ULift.up b, ULift.ext hb, fun r hr => ?_⟩
  obtain ⟨c, hc⟩ := h r.down (congrArg ULift.down hr)
  exact ⟨ULift.up c, ULift.ext hc⟩

theorem key {R : Type u} {M : Type v} [CommRing R] [Small.{v} R] [AddCommGroup M] [Module R M] (hM : Module.Injective R M)
    (hP : ∀ a : R, ∃ b : R, b * a = 0 ∧ ∀ r : R, r * b = 0 → ∃ c, c * a = r)
    (a : R) (m : M) (h : a • m = 0) : ∃ (b : R) (m' : M), b * a = 0 ∧ m = b • m' := by
  obtain ⟨b, hba, hb⟩ := hP a
  have wd : ∀ c c' : R, c * b = c' * b → c • m = c' • m := by
    intro c c' hcc
    obtain ⟨e, he⟩ := hb (c - c') (by rw [sub_mul, hcc, sub_self])
    rw [← sub_eq_zero, ← sub_smul, ← he, mul_smul, h, smul_zero]
  have hc : ∀ x : Ideal.span {b}, (Ideal.mem_span_singleton'.1 x.2).choose * b = x :=
    fun x => (Ideal.mem_span_singleton'.1 x.2).choose_spec
  let g : Ideal.span {b} →ₗ[R] M :=
    { toFun := fun x => (Ideal.mem_span_singleton'.1 x.2).choose • m
      map_add' := fun x y => by
        rw [← add_smul]
        apply wd
        rw [add_mul, hc, hc, hc, Submodule.coe_add]
      map_smul' := fun r x => by
        rw [RingHom.id_apply, ← mul_smul]
        apply wd
        rw [mul_assoc, hc, hc, Submodule.coe_smul, smul_eq_mul] }
  obtain ⟨G, hG⟩ := Module.Baer.of_injective hM (Ideal.span {b}) g
  refine ⟨b, G 1, hba, ?_⟩
  have hbm : b ∈ Ideal.span {b} := Ideal.subset_span rfl
  rw [← map_smul, smul_eq_mul, mul_one, hG b hbm]
  change m = (Ideal.mem_span_singleton'.1 hbm).choose • m
  conv_lhs => rw [← one_smul R m]
  apply wd
  rw [hc ⟨b, hbm⟩, one_mul]

theorem flat_of {R : Type u} {M : Type v} [CommRing R] [Small.{v} R] [IsPrincipalIdealRing R] [AddCommGroup M] [Module R M]
    (hM : Module.Injective R M)
    (hP : ∀ a : R, ∃ b : R, b * a = 0 ∧ ∀ r : R, r * b = 0 → ∃ c, c * a = r) : Module.Flat R M := by
  rw [Module.Flat.iff_lift_lsmul_comp_subtype_injective]
  intro I _
  obtain ⟨a, ha⟩ := Submodule.IsPrincipal.principal I
  have mem : a ∈ I := by rw [ha]; exact Submodule.mem_span_singleton_self a
  have hrep : ∀ t : I ⊗[R] M, ∃ m : M, t = (⟨a, mem⟩ : I) ⊗ₜ m := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul x n =>
      have hx : (x : R) ∈ Submodule.span R {a} := ha ▸ x.2
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hx
      refine ⟨c • n, ?_⟩
      rw [← smul_tmul]
      congr 1
      ext
      simp
      rw [← hc, smul_eq_mul]
    | add x y hx hy =>
      obtain ⟨mx, rfl⟩ := hx
      obtain ⟨my, rfl⟩ := hy
      exact ⟨mx + my, by rw [tmul_add]⟩
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro t ht
  obtain ⟨m, rfl⟩ := hrep t
  have ham : a • m = 0 := by simpa using ht
  obtain ⟨b, m', hba, rfl⟩ := key hM hP a m ham
  rw [← smul_tmul]
  have h0 : b • (⟨a, mem⟩ : I) = 0 := Subtype.ext (by simp [hba])
  rw [h0, zero_tmul]

end LateralTheory.EtaleFoundations.QFFlat

theorem LateralTheory.EtaleFoundations.zmod_injective_module_flat_holds : LateralTheory.EtaleFoundations.ZModInjectiveModuleFlat := by
  intro q _ N _ _ hN
  have : IsPrincipalIdealRing (ZMod q) :=
    IsPrincipalIdealRing.of_surjective (Int.castRingHom (ZMod q)) ZMod.intCast_surjective
  have : IsPrincipalIdealRing (ULift.{1} (ZMod q)) :=
    IsPrincipalIdealRing.of_surjective (ULift.ringEquiv (R := ZMod q)).symm
      (ULift.ringEquiv (R := ZMod q)).symm.surjective
  exact LateralTheory.EtaleFoundations.QFFlat.flat_of hN (LateralTheory.EtaleFoundations.QFFlat.ulift_P q)
end

namespace LateralTheory.Fin.EtaleTwistResolutionUniversalExtension
theorem etale_twisted_resolution_sections_injective : LateralTheory.EtaleFoundations.EtaleInjectiveSheafSectionsInjective := by
  apply LateralTheory.EtaleFoundations.etale_injective_sheaf_sections_injective_holds
theorem etale_twisted_resolution_quasiIso_flat : LateralTheory.EtaleFoundations.ZModInjectiveModuleFlat := by
  apply LateralTheory.EtaleFoundations.zmod_injective_module_flat_holds
theorem etale_twisted_resolution_exists_of_flat_sections : LateralTheory.EtaleFoundations.EtaleTwistResolutionUniversalExtension := by
  apply LateralTheory.EtaleFoundations.etale_tate_twist_resolution_universal_of_injective_sections_and_zmod_f <;> first | exact etale_twisted_resolution_sections_injective | exact etale_twisted_resolution_quasiIso_flat
theorem intersectionNumber_baseChange : LateralTheory.EtaleFoundations.EtaleTwistResolutionUniversalExtension := etale_twisted_resolution_exists_of_flat_sections
end LateralTheory.Fin.EtaleTwistResolutionUniversalExtension
end

section -- merged from Development.EtaleCohomology.TateTwists.TtTwistSidePf
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped TensorProduct

namespace LateralTheory.EtaleFoundations.TwSide

def tw_mul : Prop := ∀ (q : ℕ) [NeZero q] (i j k : ℤ), i + j = k → ∃ μ : Pair (sgl (tw q i)) (sgl (tw q j)) (sgl (tw q k)), μ.IsTensor ∧ ∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)), μ.mul U 0 0 0 (add_zero 0) (Sec.map (sglι _) (twGen i ζ)) (Sec.map (sglι _) (twGen j ζ)) = Sec.map (sglι _) (twGen k ζ)

def tw_flat : Prop := ∀ (q : ℕ) [NeZero q] (i : ℤ), FlatS (tw q i)

def flip_ex : Prop := ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K), ∃ ν : Pair J I K, μ.IsFlip ν ∧ ν.IsFlip μ ∧ (μ.IsTensor → ν.IsTensor)

def tens_qis : Prop := ∀ (R : Type) [CommRing R] {I I' J T T' : Cx R} [I.IsStrictlyGE 0] [I'.IsStrictlyGE 0] [J.IsStrictlyGE 0] (τ : Pair I J T) (τ' : Pair I' J T'), τ.IsTensor → τ'.IsTensor → (∀ t, FlatS (J.X t)) → ∀ (f : I ⟶ I') [QuasiIso f] (u : T ⟶ T'), τ.Compat τ' f (𝟙 J) u → QuasiIso u

variable {R : Type} [CommRing R]

theorem sec_sub {F : Shv R} (h : IsZero F) (U : Scheme.{0}) : Subsingleton (Sec F U) := by
  constructor; intro a b
  have : 𝟙 F = 0 := h.eq_of_src _ _
  have ha : a = Sec.map (𝟙 F) a := rfl
  have hb : b = Sec.map (𝟙 F) b := rfl
  rw [ha, hb, this]; rfl

theorem flat_zero {F : Shv R} (h : IsZero F) : FlatS F := by
  refine ⟨F.obj, 𝟙 _, fun U y => LateralTheory.EtaleFoundations.TensFam.loc_top fun V g => ⟨Sec.res g y, rfl⟩,
    fun U x _ => LateralTheory.EtaleFoundations.TensFam.loc_top fun V g => @Subsingleton.elim _ (sec_sub h V) _ _, fun U _ => ?_⟩
  haveI := sec_sub h U
  infer_instance

open ZeroObject in
theorem flat_sgl {F : Shv R} (hF : FlatS F) (t : ℤ) : FlatS ((sgl F).X t) := by
  by_cases ht : t = 0
  · subst ht
    exact (show FlatS (if (0:ℤ) = 0 then F else 0) by rw [if_pos rfl]; exact hF)
  · exact flat_zero (HomologicalComplex.isZero_single_obj_X _ _ _ _ ht)

theorem sgl_sub (F : Shv R) {t : ℤ} (ht : t ≠ 0) (U : Scheme.{0}) : Subsingleton (Sec ((sgl F).X t) U) :=
  sec_sub (HomologicalComplex.isZero_single_obj_X _ _ _ _ ht) U

theorem map_res {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.res g (Sec.map φ x) = Sec.map φ (Sec.res g x) :=
  (congrArg (fun f => ModuleCat.Hom.hom f x) (φ.hom.naturality g.op)).symm

theorem map_comp' {F G H : Shv R} (f : F ⟶ G) (g : G ⟶ H) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (f ≫ g) x = Sec.map g (Sec.map f x) := rfl

theorem map_zero' {F G : Shv R} {U : Scheme.{0}} (x : Sec F U) : Sec.map (0 : F ⟶ G) x = 0 := rfl

theorem tens_ind {I J : Cx R} {U : Scheme.{0}} {w : ℤ} (P : Tens I J U w → Prop) (h0 : P 0)
    (hadd : ∀ x y, P x → P y → P (x + y))
    (ht : ∀ p a b, P (DirectSum.lof (ULift.{1} R) _ _ p (a ⊗ₜ b))) (x : Tens I J U w) : P x := by
  induction x using DirectSum.induction_on with
  | zero => exact h0
  | add x y hx hy => exact hadd _ _ hx hy
  | of p z =>
    induction z using TensorProduct.induction_on with
    | zero => simpa using h0
    | tmul a b => simpa [DirectSum.lof_eq_of] using ht p a b
    | add z1 z2 h1 h2 => rw [map_add (f := _)]; exact hadd _ _ h1 h2

theorem lift_lof {I J K : Cx R} (τ : Pair I J K) (U : Scheme.{0}) (w : ℤ) p a b :
    τ.lift U w (DirectSum.lof (ULift.{1} R) _ _ p (a ⊗ₜ b)) = τ.mul U p.1.1 p.1.2 w p.2 a b := by
  simp [Pair.lift, DirectSum.toModule_lof]

theorem shv_isZero {F : Shv R} (h : ∀ U : Scheme.{0}, ∀ y : Sec F U, y = 0) : IsZero F := by
  rw [IsZero.iff_id_eq_zero]
  ext U y
  exact h _ y

end LateralTheory.EtaleFoundations.TwSide

namespace LateralTheory.EtaleFoundations.TwSide
variable {q : ℕ} [NeZero q]

noncomputable def T {A B J : Cx (ZMod q)} (ε : B ⟶ J) (U : Scheme.{0}) (w : ℤ) :
    Tens A B U w →ₗ[ULift.{1} (ZMod q)] Tens A J U w :=
  DirectSum.toModule _ _ _ fun p => (DirectSum.lof (ULift.{1} (ZMod q)) {p : ℤ × ℤ // p.1 + p.2 = w}
      (fun p => Sec (A.X p.1.1) U ⊗[ULift.{1} (ZMod q)] Sec (J.X p.1.2) U) p).comp
    (TensorProduct.map LinearMap.id ((ε.f p.1.2).hom.app (op U)).hom)

theorem T_lof {A B J : Cx (ZMod q)} (ε : B ⟶ J) (U : Scheme.{0}) (w : ℤ) (p : {p : ℤ × ℤ // p.1 + p.2 = w})
    (a : Sec (A.X p.1.1) U) (b : Sec (B.X p.1.2) U) :
    T ε U w (DirectSum.lof (ULift.{1} (ZMod q)) _ _ p (a ⊗ₜ b)) =
      DirectSum.lof (ULift.{1} (ZMod q)) _ _ p (a ⊗ₜ Sec.map (ε.f p.1.2) b) := by
  simp [T, DirectSum.toModule_lof]

theorem smul_eq (c : ULift.{1} (ZMod q)) : c = ((c.down.val : ℕ) : ULift.{1} (ZMod q)) := by
  apply ULift.ext; rw [ULift.down_natCast, ZMod.natCast_zmod_val]

noncomputable def ofFam {F G : Shv (ZMod q)} (φ : ∀ U : Scheme.{0}, Sec F U →+ Sec G U)
    (hφ : ∀ (V U : Scheme.{0}) (g : V ⟶ U) y, Sec.res g (φ U y) = φ V (Sec.res g y)) : F ⟶ G :=
  ObjectProperty.homMk
    { app := fun U => ModuleCat.ofHom
        { toFun := φ U.unop
          map_add' := map_add _
          map_smul' := fun c y => by
            rw [smul_eq c]
            simp only [Nat.cast_smul_eq_nsmul, map_nsmul, RingHom.id_apply] }
      naturality := fun U V g => by
        ext y
        exact (hφ V.unop U.unop g.unop y).symm }

theorem twist_side (htm : tw_mul) (htf : tw_flat) (hfl : flip_ex) (hqis : tens_qis) (i j k : ℤ) (hk : i + j = k)
    {J M : Cx (ZMod q)} (e' : ∀ U : Scheme.{0}, Prim q Γ(U, ⊤) → Sec (J.X 0) U) (hJ : IsTwRes q j J e')
    (hflat : ∀ t, FlatS (J.X t)) (σ : Pair (sgl (tw q i)) J M) (hσ : σ.IsTensor) :
    IsTwRes q k M fun U ζ => σ.mul U 0 0 0 (add_zero 0) (Sec.map (sglι (tw q i)) (twGen i ζ)) (e' U ζ) := by
  obtain ⟨μ, hμ, hgen⟩ := htm q i j k hk
  obtain ⟨hJge, ε', hε', hε'gen⟩ := hJ

  have hMge : M.IsStrictlyGE 0 := by
    refine (CochainComplex.isStrictlyGE_iff M 0).2 fun w hw => shv_isZero fun U y => ?_
    apply LateralTheory.EtaleFoundations.TensFam.sep
    obtain ⟨S, hS, h1⟩ := hσ.1 U w y
    refine ⟨S, hS, fun V g hg => ?_⟩
    obtain ⟨x, hx⟩ := h1 V g hg
    rw [← hx, show Sec.res g (0 : Sec (M.X w) U) = 0 from map_zero _]
    refine tens_ind (fun x => σ.lift V w x = 0) (map_zero _) (fun x y hx hy => by rw [map_add (f := _), hx, hy, add_zero])
      (fun p a b => ?_) x
    rw [lift_lof]
    rcases p with ⟨⟨s, t⟩, hst⟩
    by_cases hs : s = 0
    · have ht : t < 0 := by simp only at hst; omega
      haveI := sec_sub (CochainComplex.isZero_of_isStrictlyGE J 0 t (by omega)) V
      rw [Subsingleton.elim b 0, map_zero]
    · haveI := sgl_sub (tw q i) hs V
      rw [Subsingleton.elim a 0, map_zero, LinearMap.zero_apply]
  let b : ∀ U : Scheme.{0}, Tens (sgl (tw q i)) (sgl (tw q j)) U 0 →+ Sec (M.X 0) U :=
    fun U => ((σ.lift U 0).comp (T ε' U 0)).toAddMonoidHom
  have hbv : ∀ U p a c, b U (DirectSum.lof (ULift.{1} (ZMod q)) _ _ p (a ⊗ₜ c)) =
      σ.mul U p.1.1 p.1.2 0 p.2 a (Sec.map (ε'.f p.1.2) c) := by
    intro U p a c
    simp only [b, LinearMap.toAddMonoidHom_coe, LinearMap.comp_apply, T_lof, lift_lof]
  have hb : ∀ (V U : Scheme.{0}) (g : V ⟶ U) x, Sec.res g (b U x) = b V (Tens.res g 0 x) := by
    intro V U g x
    refine tens_ind (fun x => Sec.res g (b U x) = b V (Tens.res g 0 x)) (by simp)
      (fun x y hx hy => by simp only [map_add (f := _), hx, hy]) (fun p a c => ?_) x
    rw [hbv, σ.nat, map_res]
    simp only [Tens.res, DirectSum.lmap_lof, TensorProduct.map_tmul]
    rw [hbv]
  obtain ⟨φ, hφnat, hφlift⟩ := LateralTheory.EtaleFoundations.etale_tensor_hom_descends_along_tensor_pairing (ZMod q) (ZMod q) μ hμ 0 (M.X 0) b hb
  have hd : ∀ U (y : Sec ((sgl (tw q k)).X 0) U), Sec.map (M.d 0 (0 + 1)) (φ U y) = 0 := by
    intro U y
    apply LateralTheory.EtaleFoundations.TensFam.sep
    obtain ⟨S, hS, h1⟩ := hμ.1 U 0 y
    refine ⟨S, hS, fun V g hg => ?_⟩
    obtain ⟨x, hx⟩ := h1 V g hg
    rw [show Sec.res g (0 : Sec (M.X (0 + 1)) U) = 0 from map_zero _, map_res, hφnat, ← hx, hφlift]
    refine tens_ind (fun x => Sec.map (M.d 0 (0 + 1)) (b V x) = 0) (by simp)
      (fun x y hx hy => by simp only [map_add (f := _), hx, hy, add_zero]) (fun p a c => ?_) x
    rcases p with ⟨⟨s, t⟩, hst⟩
    rw [hbv]
    have hl := σ.leibniz V s t 0 hst a (Sec.map (ε'.f t) c)
    have hz : ∀ (F : Shv (ZMod q)) (m n : ℤ), (sgl F).d m n = 0 := fun F m n => HomologicalComplex.single_obj_d _ _ _ _ _
    rw [hl, ← map_comp', ε'.comm, map_comp', hz, hz]
    simp only [map_zero', map_zero, LinearMap.zero_apply, smul_zero, add_zero]
  let u : sgl (tw q k) ⟶ M := HomologicalComplex.mkHomFromSingle (sglι (tw q k) ≫ ofFam φ hφnat) (by
    intro l hl
    obtain rfl : l = 0 + 1 := by simp at hl; omega
    ext U y
    exact hd _ _)
  have hu0 : ∀ U (z : Sec ((sgl (tw q k)).X 0) U), Sec.map (u.f 0) z = φ U z := by
    intro U z
    rw [HomologicalComplex.mkHomFromSingle_f, ← Category.assoc]
    show Sec.map (ofFam φ hφnat) (Sec.map ((HomologicalComplex.singleObjXSelf _ 0 (tw q k)).hom ≫ (HomologicalComplex.singleObjXSelf _ 0 (tw q k)).inv) z) = _
    rw [Iso.hom_inv_id]; rfl
  have cmp : ∀ (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w) (a : Sec ((sgl (tw q i)).X s) U) (c : Sec ((sgl (tw q j)).X t) U),
      Sec.map (u.f w) (μ.mul U s t w h a c) = σ.mul U s t w h a (Sec.map (ε'.f t) c) := by
    intro U s t w h a c
    by_cases hs : s = 0
    · by_cases ht : t = 0
      · subst hs ht
        obtain rfl : w = 0 := by omega
        rw [hu0]
        have := hφlift U (DirectSum.lof (ULift.{1} (ZMod q)) _ _ ⟨(0,0), h⟩ (a ⊗ₜ c))
        rw [lift_lof] at this
        rw [this, hbv]
      · haveI := sgl_sub (tw q j) ht U
        rw [Subsingleton.elim c 0]
        simp only [map_zero]
    · haveI := sgl_sub (tw q i) hs U
      rw [Subsingleton.elim a 0]
      simp only [map_zero, LinearMap.zero_apply]
  obtain ⟨μf, hμf, -, hμfT⟩ := hfl (ZMod q) μ
  obtain ⟨σf, hσf, -, hσfT⟩ := hfl (ZMod q) σ
  haveI := hJge
  haveI := hε'
  have hcomp : μf.Compat σf ε' (𝟙 _) u := by
    intro U s t w h a c
    rw [HomologicalComplex.id_f]
    show _ = σf.mul U s t w h (Sec.map (ε'.f s) a) c
    rw [hμf U t s w (by omega) c a, hσf U t s w (by omega) c _, Units.smul_def, Units.smul_def, ← cmp]
    exact map_zsmul ((u.f w).hom.app (op U)).hom _ _
  have hu : QuasiIso u := hqis (ZMod q) μf σf (hμfT hμ) (hσfT hσ) (flat_sgl (htf q i)) ε' u hcomp
  refine ⟨hMge, u, hu, fun U ζ => ?_⟩
  rw [← hgen U ζ, cmp, hε'gen]

end LateralTheory.EtaleFoundations.TwSide

theorem LateralTheory.EtaleFoundations.tt_twist_side_of (htm : LateralTheory.EtaleFoundations.TwSide.tw_mul) (htf : LateralTheory.EtaleFoundations.TwSide.tw_flat)
    (hfl : LateralTheory.EtaleFoundations.TwSide.flip_ex) (hqis : LateralTheory.EtaleFoundations.TwSide.tens_qis) : LateralTheory.EtaleFoundations.tt_twist_side := by
  intro q _ i j k hk J M e' hJ hflat σ hσ
  exact LateralTheory.EtaleFoundations.TwSide.twist_side htm htf hfl hqis i j k hk e' hJ hflat σ hσ
end

section -- merged from Development.EtaleCohomology.TateTwists.EtaleFirstChernCochainCoboundaryVanishesSimplexD
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

def EvDelta : Prop := ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n m : ℤ}
  (hm : n + 1 = m) (α : Cochain ((chains R).obj E) I n) (U : Scheme.{0}),
  (∀ (x : Sx E 0 U), ev (R := R) (δ n m α) 0 m (by simp) U x =
    Sec.map (I.d n m) (ev (R := R) α 0 n (by simp) U x)) ∧
  ∀ (p : ℕ) (s t : ℤ) (hs : -((p + 1 : ℕ) : ℤ) + n = s)
    (ht : -((p + 1 : ℕ) : ℤ) + m = t) (x : Sx E (p + 1) U),
    ev (R := R) (δ n m α) (p + 1) t ht U x =
      Sec.map (I.d s t) (ev (R := R) α (p + 1) s hs U x) +
        m.negOnePow • ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) •
          ev (R := R) α p t (by omega) U (x.face i)

def cx_ext : Prop := ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ} (α : Cochain ((chains R).obj E) I n),
  (∀ p s h U x, ev (R := R) α p s h U x = 0) → α = 0

def res_neg : Prop := ∀ (q : ℕ) (s : ℤ), s < 0 → ∀ (U : Scheme.{0}) (a : Sec ((res _ (tw q 1)).X s) U), a = 0

def EtaleFirstChernCochainCoboundaryVanishesSimplexDegreeOne : Prop := ∀ (q : ℕ) [NeZero q] {E : Spc} (L : E ⟶ ofCat (glCat 1)), Inv q E →
  ∀ α : Cochain ((chains (ZMod q)).obj E) (res _ (tw q 1)) 2, IsEtaleKummerChernClassCochainOfLineBundle q L α →
  ∀ (U : Scheme.{0}) (x : Sx E 1 U), ev (R := ZMod q) (δ 2 3 α) 1 2 (by simp) U x = 0

def EtaleFirstChernCochainCoboundaryVanishesSimplexDegreeTwo : Prop := ∀ (q : ℕ) [NeZero q] {E : Spc} (L : E ⟶ ofCat (glCat 1)), Inv q E →
  ∀ α : Cochain ((chains (ZMod q)).obj E) (res _ (tw q 1)) 2, IsEtaleKummerChernClassCochainOfLineBundle q L α →
  ∀ (U : Scheme.{0}) (x : Sx E 2 U), ev (R := ZMod q) (δ 2 3 α) 2 1 (by simp) U x = 0

def EtaleFirstChernCochainCoboundaryVanishesSimplexDegreeThree : Prop := ∀ (q : ℕ) [NeZero q] {E : Spc} (L : E ⟶ ofCat (glCat 1)), Inv q E →
  ∀ α : Cochain ((chains (ZMod q)).obj E) (res _ (tw q 1)) 2, IsEtaleKummerChernClassCochainOfLineBundle q L α →
  ∀ (U : Scheme.{0}) (x : Sx E 3 U), ev (R := ZMod q) (δ 2 3 α) 3 0 (by simp) U x = 0

theorem etale_first_chern_cochain_closed_of_degree_parts (hd : EvDelta) (hx : cx_ext) (hr : res_neg) (h1 : EtaleFirstChernCochainCoboundaryVanishesSimplexDegreeOne) (h2 : EtaleFirstChernCochainCoboundaryVanishesSimplexDegreeTwo) (h3 : EtaleFirstChernCochainCoboundaryVanishesSimplexDegreeThree) :
    EtaleKummerChernClassCochainIsCocycle := by
  intro q _ E L hi α hα
  apply hx
  intro p s h U x
  match p, x with
  | 0, x =>
    obtain rfl : s = 3 := by omega
    rw [(hd (ZMod q) (show (2:ℤ) + 1 = 3 by norm_num) α U).1 x, hα.1 U x]
    exact map_zero ((((res (ZMod q) (tw q 1)).d 2 3).hom.app (op U)).hom)
  | 1, x =>
    obtain rfl : s = 2 := by omega
    exact h1 q L hi α hα U x
  | 2, x =>
    obtain rfl : s = 1 := by omega
    exact h2 q L hi α hα U x
  | 3, x =>
    obtain rfl : s = 0 := by omega
    exact h3 q L hi α hα U x
  | k + 4, x =>
    exact hr q s (by push_cast at h; omega) U _

end LateralTheory.EtaleFoundations

open LateralTheory.EtaleFoundations in
theorem LateralTheory.EtaleFoundations.etale_first_chern_cochain_closed_of_components (hd : EvDelta) (hx : cx_ext) (hr : res_neg) (h1 : EtaleFirstChernCochainCoboundaryVanishesSimplexDegreeOne) (h2 : EtaleFirstChernCochainCoboundaryVanishesSimplexDegreeTwo) (h3 : EtaleFirstChernCochainCoboundaryVanishesSimplexDegreeThree) :
    LateralTheory.EtaleFoundations.EtaleKummerChernClassCochainIsCocycle := etale_first_chern_cochain_closed_of_degree_parts hd hx hr h1 h2 h3
end

section -- merged from Development.EtaleCohomology.TateTwists.TAwAssoc0Of
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

lemma aw_diag {M : Type*} [AddCommMonoid M] (N : ℕ) (Φ : ℕ → ℕ → M) :
    ∑ q ∈ Finset.range (N + 1), ∑ p ∈ Finset.range (q + 1), Φ p (q - p) =
      ∑ p ∈ Finset.range (N + 1), ∑ r ∈ Finset.range (N - p + 1), Φ p r := by
  rw [Finset.sum_range_diag_flip]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.mem_range] at hp
  rw [show N + 1 - p = N - p + 1 by omega]

lemma bil_zsmul_left {S A B C : Type*} [CommRing S] [AddCommGroup A] [Module S A] [AddCommGroup B] [Module S B]
    [AddCommGroup C] [Module S C] (f : A →ₗ[S] B →ₗ[S] C) (c : ℤ) (a : A) (b : B) :
    f (c • a) b = c • f a b := by
  have := map_zsmul (f.flip b) c a
  simpa using this

lemma bil_sum_left {S A B C ι : Type*} [CommRing S] [AddCommGroup A] [Module S A] [AddCommGroup B] [Module S B]
    [AddCommGroup C] [Module S C] (f : A →ₗ[S] B →ₗ[S] C) (s : Finset ι) (a : ι → A) (b : B) :
    f (∑ i ∈ s, a i) b = ∑ i ∈ s, f (a i) b := by
  have := map_sum (f.flip b) a s
  simpa using this

variable {R : Type} [CommRing R]

lemma mul_ev_right {A B C : Cx R} (P : Pair A B C) {E : Spc} {N : ℕ} {U : Scheme.{0}} (x : Sx E N U) {s k w : ℤ}
    (a : Sec (A.X s) U) (γ : Cochain ((chains R).obj E) B k) (t t' j j' : ℕ) (ht : t = t') (hj : j = j')
    (h : s + (-(t : ℤ) + k) = w) (h' : s + (-(t' : ℤ) + k) = w) (hl : j + t ≤ N) (hl' : j' + t' ≤ N) :
    P.mul U s (-(t : ℤ) + k) w h a (ev γ t _ rfl U (x.sub j t hl)) =
      P.mul U s (-(t' : ℤ) + k) w h' a (ev γ t' _ rfl U (x.sub j' t' hl')) := by
  subst ht hj; rfl

theorem t_aw_assoc0_of (hev : EtaleCochainEvaluationLinear) (hsub : EtaleSimplexSubfaceComposition) : t_aw_assoc0 := by
  intro R _ I J K M M' L μ ν μ' ν' hass E n m k nm mk w h1 h2 h3 h4 α β γ ab bc x y hab hx hbc hy
  refine (hev R).2.2.1 x y fun N s hs U z => ?_
  rw [hx N s hs U z, hy N s hs U z]
  let Φ : ℕ → ℕ → Sec (L.X s) U := fun p r => if h : p + r ≤ N then
    (((m * (p : ℤ) + k * ((p : ℤ) + r)).negOnePow : ℤˣ) : ℤ) •
      ν'.mul U (-(p : ℤ) + n) (-((N - p : ℕ) : ℤ) + mk) s (by omega) (ev α p _ rfl U (z.sub 0 p (by omega)))
        (μ'.mul U (-(r : ℤ) + m) (-((N - p - r : ℕ) : ℤ) + k) (-((N - p : ℕ) : ℤ) + mk) (by omega)
          (ev β r _ rfl U (z.sub p r (by omega))) (ev γ (N - p - r) _ rfl U (z.sub (p + r) (N - p - r) (by omega))))
    else 0
  have hsg : ∀ a b c : ℤ, a + b = c → ((a.negOnePow : ℤˣ) : ℤ) * ((b.negOnePow : ℤˣ) : ℤ) = ((c.negOnePow : ℤˣ) : ℤ) := by
    intro a b c h; rw [← Units.val_mul, ← Int.negOnePow_add, h]
  calc _ = ∑ q : Fin (N + 1), ∑ p : Fin ((q : ℕ) + 1), Φ p ((q : ℕ) - p) := by
          refine Finset.sum_congr rfl fun q _ => ?_
          rw [hab, bil_sum_left, Finset.smul_sum]
          refine Finset.sum_congr rfl fun p _ => ?_
          have hp := p.is_lt
          have hq := q.is_lt
          simp only [Φ]
          rw [dite_eq_left (by omega), Units.smul_def, Units.smul_def, bil_zsmul_left, smul_smul,
            hsg _ _ (m * ((p : ℕ) : ℤ) + k * (((p : ℕ) : ℤ) + (((q : ℕ) - (p : ℕ) : ℕ) : ℤ)))
              (by push_cast [Nat.cast_sub (show (p : ℕ) ≤ q by omega)]; ring)]
          congr 1
          rw [hass U _ _ _ _ (-((N - p : ℕ) : ℤ) + mk) s _ _ (by omega) (by omega)]
          rw [(hsub z).1 0 q 0 p, (hsub z).1 0 q p (q - p)]
          simp only [Nat.zero_add]
          congr 1
          exact mul_ev_right _ z _ γ (N - q) (N - p - (q - p)) q (p + (q - p)) (by omega) (by omega) _ _ _ _
    _ = ∑ q ∈ Finset.range (N + 1), ∑ p ∈ Finset.range (q + 1), Φ p (q - p) := by
          rw [← Fin.sum_univ_eq_sum_range (fun q => ∑ p ∈ Finset.range (q + 1), Φ p (q - p))]
          exact Finset.sum_congr rfl fun q _ => Fin.sum_univ_eq_sum_range (fun p => Φ p (q - p)) _
    _ = ∑ p ∈ Finset.range (N + 1), ∑ r ∈ Finset.range (N - p + 1), Φ p r := aw_diag N Φ
    _ = ∑ p : Fin (N + 1), ∑ r : Fin (N - (p : ℕ) + 1), Φ p r := by
          rw [← Fin.sum_univ_eq_sum_range (fun p => ∑ r ∈ Finset.range (N - p + 1), Φ p r)]
          exact Finset.sum_congr rfl fun p _ => (Fin.sum_univ_eq_sum_range (fun r => Φ p r) _).symm
    _ = _ := by
          refine Finset.sum_congr rfl fun p _ => ?_
          set_option synthInstance.maxHeartbeats 100000 in
            rw [hbc, map_sum, Finset.smul_sum]
          refine Finset.sum_congr rfl fun r _ => ?_
          have hp := p.is_lt
          have hr := r.is_lt
          simp only [Φ]
          rw [dite_eq_left (by omega), Units.smul_def, Units.smul_def, map_zsmul, smul_smul,
            hsg _ _ (m * ((p : ℕ) : ℤ) + k * (((p : ℕ) : ℤ) + ((r : ℕ) : ℤ))) (by subst h3; ring)]
          rw [(hsub z).1 p (N - p) 0 r, (hsub z).1 p (N - p) r (N - p - r)]
          simp only [Nat.add_zero]

end LateralTheory.EtaleFoundations
end
