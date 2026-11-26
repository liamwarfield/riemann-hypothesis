module

public import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.AppellHumbertUnifTangentWeilPairing
public import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsConstOfSqMulTendstoZero
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsWeierstrassCoordinatesOnLine

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.NonemptyPolAVGenericFibreWithLieBasis
section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.NonemptyPolAVGenericFibreWithLieBasis
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM

theorem GenFib.nonempty_of_baseChange :
    Out.PolBaseChangeSt → ∀ (K : Type) [Field K] [NumberField K] (P : Out.PolAV (Sp (𝓞 K))), Nonempty (GenFib P) := by
  intro hB K _ _ P
  obtain ⟨P₀, φ, h⟩ := exists_isPolFibre hB (algebraMap (𝓞 K) K) P
  obtain ⟨v, hv⟩ := GlobalTheory.KeyPow.exists_isLieBasis P₀.A P₀.smoothDim
  exact ⟨⟨P₀, φ, h, v, hv⟩⟩

end GlobalTheory.CM
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.NonemptyPolAVGenericFibreWithLieBasisStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_polAVGenericFibreWithLieBasis : Out.PolBaseChangeSt → ∀ (K : Type) [Field K] [NumberField K] (P : Out.PolAV (Sp (𝓞 K))), Nonempty (GenFib P) := by
  first | exact @GlobalTheory.CM.GenFib.nonempty_of_baseChange | exact GlobalTheory.CM.GenFib.nonempty_of_baseChange | (intros; apply GlobalTheory.CM.GenFib.nonempty_of_baseChange <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUniqueExtendRingOfIntegersHom
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM

section
variable {E K K' : Type} [Field E] [NumberField E] [Field K] [NumberField K] [Field K'] [NumberField K']

theorem ringOfIntegers_hom_injective (τ : 𝓞 E →+* 𝓞 K) : Function.Injective τ := by
  rw [RingHom.injective_iff_ker_eq_bot]
  have : (RingHom.ker τ).IsPrime := RingHom.ker_isPrime τ
  apply Ideal.eq_bot_of_comap_eq_bot (R := ℤ)
  rw [eq_bot_iff]
  intro n hn
  rw [Ideal.mem_comap, RingHom.mem_ker] at hn
  simpa using hn

theorem existsUnique_extend_ringOfIntegers_hom (τ : 𝓞 E →+* 𝓞 K) :
    ∃! τ' : E →+* K, ∀ a : 𝓞 E, τ' a = τ a := by
  have hi : Function.Injective ((algebraMap (𝓞 K) K).comp τ) :=
    (RingOfIntegers.coe_injective).comp (ringOfIntegers_hom_injective τ)
  have hl : ∀ a : 𝓞 E, (IsFractionRing.lift hi : E →+* K) (algebraMap (𝓞 E) E a) = algebraMap (𝓞 K) K (τ a) :=
    fun a => IsFractionRing.lift_algebraMap (A := 𝓞 E) (K := E) hi a
  generalize (IsFractionRing.lift hi : E →+* K) = σ₀ at hl
  refine ⟨σ₀, hl, fun σ hσ => ?_⟩
  refine IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext fun a => ?_)
  exact (hσ a).trans (hl a).symm

theorem mapRingHom_bijective :
    Function.Bijective fun σ : E →+* K => (RingOfIntegers.mapRingHom σ : 𝓞 E →+* 𝓞 K) := by
  constructor
  · intro σ σ' h
    refine (existsUnique_extend_ringOfIntegers_hom (RingOfIntegers.mapRingHom σ)).unique (fun a => rfl) fun a => ?_
    have h' : RingOfIntegers.mapRingHom σ = RingOfIntegers.mapRingHom σ' := h
    rw [h']
    rfl
  · intro τ
    obtain ⟨σ, hσ⟩ := (existsUnique_extend_ringOfIntegers_hom τ).exists
    exact ⟨σ, RingHom.ext fun a => RingOfIntegers.ext (hσ a)⟩

theorem splits_iff_card : Splits E K ↔ Nat.card (E →+* K) = Module.finrank ℚ E := by
  rw [Splits, ← Nat.card_eq_of_bijective _ (mapRingHom_bijective (E := E) (K := K))]

theorem card_ringHom_le_finrank : Nat.card (E →+* K) ≤ Module.finrank ℚ E := by
  rw [Nat.card_congr (RingHom.equivRatAlgHom E K)]
  exact card_algHom_le_finrank ℚ E K

theorem comp_bijective_of_splits (j : K →+* K') (h : Splits E K) :
    Function.Bijective fun σ : E →+* K => j.comp σ := by
  have : Finite (E →+* K') := Finite.of_equiv _ (RingHom.equivRatAlgHom E K').symm
  have hi : Function.Injective fun σ : E →+* K => j.comp σ := fun σ σ' e =>
    RingHom.ext fun a => j.injective (DFunLike.congr_fun e a)
  refine hi.bijective_of_nat_card_le ?_
  rw [splits_iff_card.1 h]
  exact card_ringHom_le_finrank

end

theorem splits_basic : ∀ (E : Type) [Field E] [NumberField E], (∃ k : IntermediateField ℚ ℂ, FiniteDimensional ℚ k ∧ ∀ (τ : E →+* ℂ) a, τ a ∈ k) ∧ (∀ (k : IntermediateField ℚ ℂ) [NumberField k], (∀ (τ : E →+* ℂ) a, τ a ∈ k) → Splits E k) ∧ ∀ (K : Type) [Field K] [NumberField K], (Splits E K ↔ Nat.card (E →+* K) = Module.finrank ℚ E) ∧ (∀ τ : 𝓞 E →+* 𝓞 K, ∃! τ' : E →+* K, ∀ a : 𝓞 E, τ' a = τ a) ∧ ∀ (K' : Type) [Field K'] [NumberField K'] (j : K →+* K'), Splits E K → Splits E K' ∧ Function.Bijective fun τ : 𝓞 E →+* 𝓞 K => (RingOfIntegers.mapRingHom j).comp τ := by
  intro E _ _
  refine ⟨⟨IntermediateField.normalClosure ℚ E ℂ, inferInstance, fun τ a => ?_⟩, fun k _ hk => ?_,
    fun K _ _ => ⟨splits_iff_card, existsUnique_extend_ringOfIntegers_hom, fun K' _ _ j h => ⟨?_, ?_⟩⟩⟩
  · exact AlgHom.fieldRange_le_normalClosure τ.toRatAlgHom ⟨a, rfl⟩
  · rw [splits_iff_card, ← Embeddings.card E ℂ, ← Nat.card_eq_fintype_card]
    refine Nat.card_eq_of_bijective (fun σ => (algebraMap k ℂ).comp σ) ⟨fun σ σ' e => ?_, fun τ => ?_⟩
    · exact RingHom.ext fun a => (algebraMap k ℂ).injective (DFunLike.congr_fun e a)
    · exact ⟨τ.codRestrict k (hk τ), RingHom.ext fun a => rfl⟩
  · rw [splits_iff_card, ← Nat.card_eq_of_bijective _ (comp_bijective_of_splits j h)]
    exact splits_iff_card.1 h
  · have e : ((fun τ : 𝓞 E →+* 𝓞 K => (RingOfIntegers.mapRingHom j).comp τ) ∘
        fun σ : E →+* K => (RingOfIntegers.mapRingHom σ : 𝓞 E →+* 𝓞 K)) =
        (fun σ : E →+* K' => (RingOfIntegers.mapRingHom σ : 𝓞 E →+* 𝓞 K')) ∘ fun σ : E →+* K => j.comp σ := by
      funext σ
      exact RingHom.ext fun a => rfl
    rw [← Function.Bijective.of_comp_iff _ (mapRingHom_bijective (E := E) (K := K)), e]
    exact mapRingHom_bijective.comp (comp_bijective_of_splits j h)

end GlobalTheory.CM
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.EllPullExistsOAct
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section

namespace GlobalTheory.CM

theorem ellPull_exists_oAct {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {g : G'.left ⟶ G.left} (hg : IsGrpPullback G' G f g) {O : Type} [CommRing O] (o : OAct O G) :
    ∃ o' : OAct O G', ∀ a, (o'.act a).left ≫ g = g ≫ (o.act a).left := by
  have inj : ∀ {T : Over S'} {x y : T ⟶ G'}, pushPt hg.1.w x = pushPt hg.1.w y → x = y := fun {T x y} h =>
    Over.OverMorphism.ext (hg.1.hom_ext (congrArg (fun q => q.left) h) (by rw [Over.w, Over.w]))
  let act : O → (G' ⟶ G') := fun a => Over.homMk (hg.1.lift (g ≫ (o.act a).left) G'.hom
    (by rw [Category.assoc, Over.w, hg.1.w])) (hg.1.lift_snd _ _ _)
  have ha : ∀ a, (act a).left ≫ g = g ≫ (o.act a).left := fun a => hg.1.lift_fst _ _ _
  have pa : ∀ {T : Over S'} (x : T ⟶ G') a, pushPt hg.1.w (x ≫ act a) = pushPt hg.1.w x ≫ o.act a := fun x a =>
    Over.OverMorphism.ext (by
      show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
      rw [Category.assoc, ha, Category.assoc])
  have pm : ∀ {T : Over S'} (x y : T ⟶ G'), pushPt hg.1.w (x * y) = pushPt hg.1.w x * pushPt hg.1.w y := fun x y =>
    map_mul (pushHom hg _) x y
  refine ⟨⟨act, fun a => isMonHom_of_mul _ fun T x y => inj ?_, inj ?_, fun a b => inj ?_, fun a b => inj ?_⟩, ha⟩
  · have := o.hom a
    rw [pa, pm, pm, pa, pa, MonObj.mul_comp]
  · rw [← Category.id_comp (act 1), pa, o.one, Category.comp_id]
  · rw [← Category.id_comp (act (a * b)), pa, pa, ← Category.id_comp (act a), pa, o.mul, Category.assoc]
  · refine Eq.trans ?_ (pm (act a) (act b)).symm
    rw [← Category.id_comp (act (a + b)), ← Category.id_comp (act a), ← Category.id_comp (act b), pa, pa, pa, o.add]
    exact MonObj.comp_mul _ _ _

theorem ellPull_prim {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {g : G'.left ⟶ G.left} (hg : IsGrpPullback G' G f g) {L : LB G.left} {L' : LB G'.left} (hL : L.IsLB)
    (hL' : L'.IsLB) (i : LBIso (L.pull g) L') {w : G ⟶ G} {w' : G' ⟶ G'} (hw : w'.left ≫ g = g ≫ w.left)
    (h : LBIso L (cubeLB G ![𝟙 G, w] L)) : LBIso L' (cubeLB G' ![𝟙 G', w'] L') := by
  let U : Over.mk (G'.hom ≫ f) ⟶ G := Over.homMk g hg.1.w
  have H₁ : LBIso (L.pull g) (cubeLB G' ![𝟙 G', w'] (L.pull g)) := by
    refine LBIso.chartPull (Geo.Tor.chartPullPull L g U.left rfl)
      (chartPullLinComb L g _ _ _ U.left fun I => lamBC_psum_push hg _ _ U (fun k => ?_) I.down) h
    fin_cases k
    · refine Over.OverMorphism.ext ?_
      show 𝟙 _ ≫ g = g ≫ 𝟙 _
      rw [Category.id_comp, Category.comp_id]
    · exact Over.OverMorphism.ext hw
  have hLg : (L.pull g).IsLB := DVR.linComb_isLB _ hL _ _
  exact LBIso.trans hL' hLg (DVR.linComb_isLB _ hL' _ _) i.symm
    (LBIso.trans hLg (DVR.linComb_isLB _ hLg _ _) (DVR.linComb_isLB _ hL' _ _) H₁
      (PowPrimitive.lbIso_linComb i _ _))

theorem exists_ellMap : Out.PolBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] (ω : R) (C : Ell H R ω) (R' : Type) [CommRing R'] (f : R →+* R'), ∃ (C' : Ell H R' (f ω)) (φ : C'.P.A.left ⟶ C.P.A.left), EllMap C' C f φ := by
  intro hB E _ _ _ H R _ ω C R' _ f
  obtain ⟨P', φ, hP⟩ := exists_isPolFibre hB f C.P
  obtain ⟨hdim, hg, hi⟩ := id hP
  obtain ⟨o', ho⟩ := ellPull_exists_oAct hg C.act
  have : IsCommMonObj P'.A := P'.isAb.comm
  have := C.P.smoothDim
  obtain ⟨v', hv', hv⟩ := exists_isLieBasis_baseChange R R' f C.P.A P'.A φ hg
    (SmoothOfRelativeDimension.smooth C.P.g C.P.A.hom) 1 ![C.v] C.basis
  have ev : ![v' 0] = v' := by
    funext i
    fin_cases i
    rfl
  have hv0 : (v' 0).left ≫ φ = spMap (Chart.dualMapR f) ≫ C.v.left := hv 0
  refine ⟨⟨P', hdim.trans C.dim, o', v' 0, ev ▸ hv', ?_, fun a b hab => ?_,
    ellPull_prim hg C.P.isLB P'.isLB hi (ho _) C.prim⟩, φ, rfl, hP, hv0, ho⟩
  · have e : (fun i => f (![ω] i)) = ![f ω] := by
      funext i
      fin_cases i
      rfl
    rw [ev, ← e]
    refine (lieComb_baseChange R R' f C.P.A P'.A φ hg 1 ![C.v] _ ![ω] v' _ hv C.eig).1 ?_
    show ((v' 0).left ≫ (o'.act (wK H)).left) ≫ φ = _ ≫ C.v.left ≫ (C.act.act (wK H)).left
    rw [Category.assoc, ho, ← Category.assoc, hv0, Category.assoc]
  · have e1 : (𝟙 P'.A : P'.A ⟶ P'.A).left ≫ φ = φ ≫ (𝟙 C.P.A : C.P.A ⟶ C.P.A).left := by
      show 𝟙 _ ≫ φ = φ ≫ 𝟙 _
      rw [Category.id_comp, Category.comp_id]
    exact lamEq_baseChange _ _ (spMap f) _ _ _ _ _ _ _ _ φ φ φ φ hg.1.w hg.1.w hg hg _ _ _ _ C.P.isLB C.P.isLB
      P'.isLB P'.isLB hi hi _ _ _ _ _ _ _ _ (ho a) e1 e1 (ho b) (C.adj a b hab)

end GlobalTheory.CM

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmCurveLieCharacterOfAdjoinGenerator
section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmCurveLieCharacterOfAdjoinGenerator
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section
namespace GlobalTheory.CM.LieChar

variable {R : Type} [CommRing R] {G G' : Over (Sp R)} [GrpObj G] [GrpObj G']

theorem isLieComb_one_iff (c : R) (v w : epsR R ⟶ G) :
    IsLieComb ![c] ![v] w ↔ w.left = spMap (epsScaleR c) ≫ v.left := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    simpa using hu 0
  · intro h
    exact ⟨![w], fun i => by fin_cases i; exact h, by simp⟩

theorem isLieComb_comp {c : R} {v w : epsR R ⟶ G} (h : IsLieComb ![c] ![v] w) (f : G ⟶ G') :
    IsLieComb ![c] ![v ≫ f] (w ≫ f) := by
  rw [isLieComb_one_iff] at h ⊢
  simp [h]

theorem isTangent_comp {v : epsR R ⟶ G} (h : IsTangent v) (f : G ⟶ G') [IsMonHom f] :
    IsTangent (v ≫ f) := by
  unfold IsTangent at h ⊢
  rw [Over.comp_left, ← Category.assoc, h, ← Over.comp_left, IsMonHom.one_hom]

theorem spMap_epsScaleR_one : spMap (epsScaleR (1 : R)) = 𝟙 _ := by
  have : epsScaleR (1 : R) = RingHom.id _ := by
    ext x <;> simp [epsScaleR]
  rw [this]
  exact Spec.map_id _

theorem isLieComb_mul (x y : epsR R ⟶ G) : IsLieComb ![(1 : R), 1] ![x, y] (x * y) :=
  ⟨![x, y], fun i => by fin_cases i <;> simp [spMap_epsScaleR_one], by simp⟩

theorem exists_char [IsCommMonObj G] {O : Type} [CommRing O] (act : OAct O G) {v : epsR R ⟶ G}
    (hv : IsLieBasis ![v]) :
    ∃ τ : O →+* R, (∀ c, IsLieComb ![τ c] ![v] (v ≫ act.act c)) ∧
      ∀ c r, IsLieComb ![r] ![v] (v ≫ act.act c) → τ c = r := by
  have ht : ∀ c, IsTangent (v ≫ act.act c) := fun c => by
    haveI := act.hom c
    exact isTangent_comp (hv.1 0) _
  have e1 : ∀ d : Fin 1 → R, d = ![d 0] := fun d => by
    funext i; fin_cases i; rfl
  choose d hd hu using fun c => hv.2 _ (ht c)
  have hτ : ∀ c, IsLieComb ![d c 0] ![v] (v ≫ act.act c) := fun c => by
    rw [← e1]; exact hd c
  have huq : ∀ c r, IsLieComb ![r] ![v] (v ≫ act.act c) → d c 0 = r := fun c r h => by
    rw [← hu c _ h]; rfl
  obtain ⟨-, -, hcomp, -, -⟩ := GlobalTheory.LieComb.lieComb_algebra R G 1 ![v] hv.1
  have hone : d 1 0 = 1 := huq _ _ (by
    rw [isLieComb_one_iff, act.one, spMap_epsScaleR_one]; simp)
  have hmul : ∀ a b, d (a * b) 0 = d a 0 * d b 0 := fun a b => huq _ _ (by
    have := hcomp 1 ![![d b 0]] ![v ≫ act.act b] ![d a 0] _
      (fun i => by fin_cases i; exact hτ b) (isLieComb_comp (hτ a) (act.act b))
    rw [act.mul, ← Category.assoc]
    convert this using 1
    funext i; fin_cases i; simp)
  have hadd : ∀ a b, d (a + b) 0 = d a 0 + d b 0 := fun a b => huq _ _ (by
    have := hcomp 2 ![![d a 0], ![d b 0]] ![v ≫ act.act a, v ≫ act.act b] ![1, 1] _
      (fun i => by
        fin_cases i
        · exact hτ a
        · exact hτ b) (isLieComb_mul _ _)
    rw [act.add, MonObj.comp_mul]
    convert this using 1
    funext i; fin_cases i; simp)
  exact ⟨RingHom.mk' ⟨⟨fun c => d c 0, hone⟩, hmul⟩ hadd, hτ, huq⟩

theorem ell_char : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] (ω : R)
    (C : Ell H R ω), ∃ τ₀ : OK H →+* R, τ₀ (wK H) = ω ∧ ∀ c, IsLieComb ![τ₀ c] ![C.v] (C.v ≫ C.act.act c) := by
  intro E _ _ _ H R _ ω C
  obtain ⟨τ, h, hu⟩ := exists_char C.act C.basis
  exact ⟨τ, hu _ _ C.eig, h⟩

end GlobalTheory.CM.LieChar
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmCurveLieCharacterOfAdjoinGeneratorStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

theorem _root_.GlobalTheory.T.cmCurve_lie_character_of_adjoinGenerator : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] (ω : R) (C : Ell H R ω), ∃ τ₀ : OK H →+* R, τ₀ (wK H) = ω ∧ ∀ c, IsLieComb ![τ₀ c] ![C.v] (C.v ≫ C.act.act c) := by
  first | exact @GlobalTheory.CM.LieChar.ell_char | exact GlobalTheory.CM.LieChar.ell_char | (intros; apply GlobalTheory.CM.LieChar.ell_char <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HasTypeBaseChange
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM

theorem hasType_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R R' : Type) [CommRing R] [CommRing R'] (f : R →+* R') (t : SAB H (Sp R)) (t' : SAB H (Sp R')) (_ : SABMap t' t (spMap f)) (ρ : R) (p q : ℕ), (Function.Injective f → HasType H t.act ρ p q → HasType H t'.act (f ρ) p q) ∧ ((∀ (k : Type) [Field k] (β : R →+* k), Function.Injective β → ∃ β' : R' →+* k, β'.comp f = β ∧ Function.Injective β') → HasType H t'.act (f ρ) p q → HasType H t.act ρ p q) := by
  intro E _ _ _ H R R' _ _ f t t' m ρ p q
  have key : ∀ (k : Type) [Field k] (β' : R' →+* k) (τ : 𝓞 E →+* k) (n : ℕ),
      LieMult t'.act (spMap β') τ n ↔ LieMult t.act (spMap (β'.comp f)) τ n := fun k _ β' τ n => by
    have e : spMap β' ≫ spMap f = spMap (β'.comp f) := (Spec.map_comp _ _).symm
    rw [← e]
    exact LiePull.lieMult_pull _ _ _ t.G t'.G (spMap f) m.cm.F t.act t'.act m.cart m.act k _ τ n
  refine ⟨fun hf h k _ _ β' hβ' τ => ?_, fun hext h k _ _ β hβ τ => ?_⟩
  · rw [key, key]
    exact h k (β'.comp f) (hβ'.comp hf) τ
  · obtain ⟨β', rfl, hβ'⟩ := hext k β hβ
    rw [← key, ← key]
    exact h k β' hβ' τ

end GlobalTheory.CM
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RosatiAdjIffLamEq
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.RosLam

theorem form_rosati {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] (f g : G ⟶ G)
    {V : Type} [CommGroup V] (k : ((G ⊗ G).left ⟶ G.left) → V) :
    (∏ I : ULift.{0} (Finset (Fin 2)),
        k (psum G ![fst G G ≫ f, snd G G] I.down).left ^ ((-1 : ℤ) ^ (2 - I.down.card))) /
      (∏ I : ULift.{0} (Finset (Fin 2)),
        k (psum G ![fst G G, snd G G ≫ g] I.down).left ^ ((-1 : ℤ) ^ (2 - I.down.card))) =
      ∏ i, k (Out.rosatiφ G f g i) ^ Out.rosatiε i := by
  have p := prod_ros f g (fst G G) (snd G G) k
  rw [lift_fst_snd] at p
  simp only [Over.id_left, Category.id_comp] at p
  rw [p, GlobalTheory.NormRos.prod_square, GlobalTheory.NormRos.prod_square]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_div]
  abel

theorem lbIso_of_gen {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {L : LB G.left} (hL : L.IsLB)
    (f g : G ⟶ G) (t : LB.Gen (LB.LinComb L (Out.rosatiφ G f g) Out.rosatiε)) (ht : t.IsGen) :
    LBIso (cubeLB G ![fst G G ≫ f, snd G G] L) (cubeLB G ![fst G G, snd G G ≫ g] L) := by
  obtain ⟨Pic, _, cl, pl, h₁, h₂, -, -, h₅, -⟩ := GlobalTheory.CechPicMul.exists_picardGroup
  obtain ⟨a, a'⟩ := h₅ _ _ L hL _ (Out.rosatiφ G f g) Out.rosatiε
  obtain ⟨b, b'⟩ : (cubeLB G ![fst G G ≫ f, snd G G] L).IsLB ∧ cl (cubeLB G ![fst G G ≫ f, snd G G] L) = _ :=
    h₅ _ _ L hL _ _ _
  obtain ⟨c, c'⟩ : (cubeLB G ![fst G G, snd G G ≫ g] L).IsLB ∧ cl (cubeLB G ![fst G G, snd G G ≫ g] L) = _ :=
    h₅ _ _ L hL _ _ _
  refine (h₁ _ _ _ b c).1 ?_
  have e := ((h₂ _ _ a).2 ⟨t, ht⟩).symm.trans a'
  rw [b', c', ← div_eq_one, e]
  have key := form_rosati f g (V := Multiplicative (FreeAbelianGroup ((G ⊗ G).left ⟶ G.left)))
    (fun ψ => Multiplicative.ofAdd (FreeAbelianGroup.of ψ))
  have k := congrArg (AddMonoidHom.toMultiplicativeLeft
    (FreeAbelianGroup.lift fun ψ : (G ⊗ G).left ⟶ G.left => Additive.ofMul (pl ψ (cl L)))) key
  simpa only [map_div, map_prod, map_zpow, AddMonoidHom.coe_toMultiplicativeLeft, Function.comp_apply, toAdd_ofAdd,
    FreeAbelianGroup.lift_apply_of, toMul_ofMul] using k

theorem rosatiAdj_iff_lamEq : Out.GlobalFnsSt → ∀ (S : Scheme.{0}) (P : Out.PolAV S) (f g : P.A ⟶ P.A), IsMonHom f → IsMonHom g → (Out.RosatiAdj P.A P.L f g ↔ LamEq P.L f (𝟙 P.A) P.L (𝟙 P.A) g) := by
  intro hG S P f g hf hg
  have := P.isAb.comm
  unfold LamEq
  rw [Category.comp_id, Category.comp_id]
  constructor
  · intro h
    obtain ⟨u, hu, -⟩ := exists_ros hG P.isAb P.isLB f g h
    exact lbIso_of_gen P.isLB f g u hu
  · intro h s
    obtain ⟨t, ht⟩ := GlobalTheory.NormRos.exists_gen_rosati P.isLB f g h
    exact ⟨⊤, trivial, LB.pullGen P.L _ _ t _, DVR.pullGen_isGen _ _ _ _ ht _⟩

end GlobalTheory.RosLam
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsPolarisedAbelianSchemeLieBasisInvariants
section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsUnimodularSolZeroNeg
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.WeierstrassCurve
open scoped CategoryTheory.Obj UpperHalfPlane

noncomputable section

namespace GlobalTheory.WeierstrassCurve.OriginTangent

variable {R : Type} [CommRing R] (W : WeierstrassCurve R) {A : Type} [CommRing A]

theorem ptHom_origin_inj {ρ ρ' : R →+* A} {z w z' w' : A}
    (h : IsUnimodularSol (W.map ρ) ![z, -1, w]) (h' : IsUnimodularSol (W.map ρ') ![z', -1, w'])
    (e : ptHom W ρ ![z, -1, w] h = ptHom W ρ' ![z', -1, w'] h') : z = z' ∧ w = w' := by
  have e₁ := (SpecMap_originEval_chartY W ρ z w h.equation).trans
    (e.trans (SpecMap_originEval_chartY W ρ' z' w' h'.equation).symm)
  rw [cancel_mono] at e₁
  have e' : originEval W ρ z w h.equation = originEval W ρ' z' w' h'.equation :=
    congrArg (·.hom) (Spec.map_injective e₁)
  exact ⟨(originEval_originZ ..).symm.trans
      ((RingHom.congr_fun e' (originZ W)).trans (originEval_originZ ..)),
    (originEval_originW ..).symm.trans
      ((RingHom.congr_fun e' (originW W)).trans (originEval_originW ..))⟩

theorem exists_eq_ptHom_origin (ρ : R →+* A) (g : Spec (.of A) ⟶ scheme W)
    (hY : ∀ p, g p ∈ coordOpen W 1) (hg : g ≫ toSpec W = Spec.map (CommRingCat.ofHom ρ)) :
    ∃ (z w : A) (h : IsUnimodularSol (W.map ρ) ![z, -1, w]), g = ptHom W ρ ![z, -1, w] h := by
  have hr : Set.range g ⊆ Set.range (chartY W) := by
    rintro _ ⟨p, rfl⟩
    rw [← Scheme.Hom.coe_opensRange, opensRange_chartY]
    exact hY p
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (IsOpenImmersion.lift _ _ hr)
  have hl : Spec.map ψ ≫ chartY W = g := hψ ▸ IsOpenImmersion.lift_fac _ _ hr
  have hc : ψ.hom.comp (algebraMap R (OriginRing W)) = ρ := by
    rw [← hl, Category.assoc, chartY_toSpec, ← Spec.map_comp] at hg
    exact congrArg (·.hom) (Spec.map_injective hg)
  have hP : (ψ.hom ∘ ![originZ W, -1, originW W]) =
      ![ψ.hom (originZ W), -1, ψ.hom (originW W)] := by
    ext1 j; fin_cases j <;> simp
  have h₀ : IsUnimodularSol (W.map (algebraMap R (OriginRing W))) ![originZ W, -1, originW W] :=
    isUnimodularSol_origin (equation_originZ_originW W)
  have h₁ := h₀.map_comp ψ.hom
  have h₂ : IsUnimodularSol (W.map ρ) ![ψ.hom (originZ W), -1, ψ.hom (originW W)] := by
    rw [← hc, ← hP]; exact h₁
  refine ⟨_, _, h₂, ?_⟩
  rw [← hl]
  exact (SpecMap_ptHom W _ _ h₀ ψ.hom).trans (ptHom_congr W _ _ _ hc hP _)

theorem SpecMap_zero_origin (ρ : R →+* A) (h : IsUnimodularSol (W.map ρ) ![0, -1, 0]) :
    Spec.map (CommRingCat.ofHom ρ) ≫ zero W = ptHom W ρ ![0, -1, 0] h := by
  rw [SpecMap_zero, ← ptHom_smul W ρ _ _ isUnit_one.neg]
  exact ptHom_congr W _ _ _ rfl (by ext1 j; fin_cases j <;> simp) _

theorem isUnimodularSol_zero_neg (V : WeierstrassCurve A) : IsUnimodularSol V ![0, -1, 0] :=
  isUnimodularSol_origin (by rw [equation_origin_iff]; simp)

theorem exists_eq_ptHom_eps (f : R →+* A) (g : Spec (.of (DualNumber A)) ⟶ scheme W)
    (hg : g ≫ toSpec W =
      Spec.map (CommRingCat.ofHom ((algebraMap A (DualNumber A)).comp f)))
    (h0 : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom A A A).toRingHom) ≫ g =
      Spec.map (CommRingCat.ofHom f) ≫ zero W) :
    ∃ (c : A) (h : IsUnimodularSol (W.map ((algebraMap A (DualNumber A)).comp f))
      ![TrivSqZeroExt.inr c, -1, 0]),
      g = ptHom W ((algebraMap A (DualNumber A)).comp f) ![TrivSqZeroExt.inr c, -1, 0] h := by
  have hY : ∀ p, g p ∈ coordOpen W 1 := by
    intro p
    have hs : Function.Surjective (PrimeSpectrum.comap (TrivSqZeroExt.fstHom A A A).toRingHom) := by
      rw [← Set.range_eq_univ, range_comap_of_surjective _ _ TrivSqZeroExt.fst_surjective,
        PrimeSpectrum.zeroLocus_eq_univ_iff]
      intro x hx
      have hx' : x.fst = 0 := hx
      refine ⟨2, ?_⟩
      ext <;> simp [pow_two, hx']
    obtain ⟨q, rfl⟩ := hs p
    have e : g (PrimeSpectrum.comap (TrivSqZeroExt.fstHom A A A).toRingHom q) =
        zero W (Spec.map (CommRingCat.ofHom f) q) := by
      exact (Scheme.Hom.comp_apply
        (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom A A A).toRingHom)) g q).symm.trans
        ((congrArg (fun t => t q) h0).trans
          (Scheme.Hom.comp_apply (Spec.map (CommRingCat.ofHom f)) (zero W) q))
    rw [e]
    exact (zero_preimage_coordOpen_one W).ge (Set.mem_univ _)
  obtain ⟨z, w, h, rfl⟩ := exists_eq_ptHom_origin W _ g hY hg
  have hP : ((TrivSqZeroExt.fstHom A A A).toRingHom ∘ ![z, -1, w]) = ![z.fst, -1, w.fst] := by
    ext1 j; fin_cases j <;> simp
  have h₁ := h.map_comp (TrivSqZeroExt.fstHom A A A).toRingHom
  have h₂ := h₁
  rw [hP] at h₂
  rw [SpecMap_ptHom, SpecMap_zero_origin W f (isUnimodularSol_zero_neg _),
    ptHom_congr W _ _ h₁ rfl hP h₂] at h0
  obtain ⟨hz, hw⟩ := ptHom_origin_inj W _ _ h0
  have he := (equation_origin_iff _ _ _).mp h.equation
  have hzz : z * z = 0 := by ext <;> simp [hz]
  have hzw : z * w = 0 := by ext <;> simp [hz, hw]
  have hww : w * w = 0 := by ext <;> simp [hw]
  have hw0 : w = 0 := by
    set V := W.map ((algebraMap A (DualNumber A)).comp f)
    linear_combination he + z * hzz + (V.a₁ + V.a₂ * z + V.a₄ * w) * hzw + (V.a₃ + V.a₆ * w) * hww
  have hz0 : z = TrivSqZeroExt.inr z.snd := by ext <;> simp [hz]
  have hQ : ![z, -1, w] = ![TrivSqZeroExt.inr z.snd, -1, 0] := by rw [hw0, ← hz0]
  exact ⟨z.snd, hQ ▸ h, ptHom_congr W _ _ _ rfl hQ _⟩

theorem epsScale_ptHom (f : R →+* A) (c : A)
    (h : IsUnimodularSol (W.map ((algebraMap A (DualNumber A)).comp f)) ![DualNumber.eps, -1, 0]) :
    ∃ h', spMap (epsScaleR c) ≫
        ptHom W ((algebraMap A (DualNumber A)).comp f) ![DualNumber.eps, -1, 0] h =
      ptHom W ((algebraMap A (DualNumber A)).comp f) ![TrivSqZeroExt.inr c, -1, 0] h' := by
  have hρ : (epsScaleR c).comp ((algebraMap A (DualNumber A)).comp f) =
      (algebraMap A (DualNumber A)).comp f := by
    ext a <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]
  have hP : (epsScaleR c ∘ ![DualNumber.eps, -1, 0]) = ![TrivSqZeroExt.inr c, -1, 0] := by
    ext1 j; fin_cases j
    · ext <;> simp [epsScaleR]
    · simp
    · simp
  have h₁ := h.map_comp (epsScaleR c)
  rw [hρ, hP] at h₁
  exact ⟨h₁, (SpecMap_ptHom W _ _ h _).trans (ptHom_congr W _ _ _ hρ hP _)⟩

theorem isLieComb_one_iff {G : Over (Sp A)} [GrpObj G] (c : Fin 1 → A) (v w : epsR A ⟶ G) :
    IsLieComb c ![v] w ↔ w.left = spMap (epsScaleR (c 0)) ≫ v.left := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    simpa using hu 0
  · intro hw
    refine ⟨![w], fun i => ?_, by simp⟩
    fin_cases i
    exact hw

theorem isLieBasis_eps : ∀ (R : Type) [CommRing R] (W : WeierstrassCurve R) (R' : Type) [CommRing R'] (f : R →+* R') (A : Over (Sp R')) [GrpObj A] (φ : A.left ⟶ scheme W) (v : epsR R' ⟶ A) (h : IsUnimodularSol (W.map ((algebraMap R' (DualNumber R')).comp f)) ![DualNumber.eps, -1, 0]), IsPullback φ A.hom (toSpec W) (spMap f) → eSec A ≫ φ = spMap f ≫ zero W → v.left ≫ φ = ptHom W ((algebraMap R' (DualNumber R')).comp f) ![DualNumber.eps, -1, 0] h → IsLieBasis ![v] := by
  intro R _ W R' _ f A _ φ v h hpb he hv
  have hover : ∀ w : epsR R' ⟶ A, w.left ≫ A.hom = spMap (algebraMap R' (DualNumber R')) :=
    fun w => Over.w w
  have hη : η[A].left ≫ A.hom = 𝟙 (Sp R') := Over.w η[A]
  have he' : η[A].left ≫ φ = spMap f ≫ zero W := he
  constructor
  · intro i
    fin_cases i
    change spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ v.left = η[A].left
    refine hpb.hom_ext ?_ ?_
    · rw [Category.assoc, hv, he', SpecMap_zero_origin W f (isUnimodularSol_zero_neg _)]
      refine (SpecMap_ptHom W _ _ h _).trans (ptHom_congr W _ _ _ ?_ ?_ _)
      · ext a; simp [TrivSqZeroExt.algebraMap_eq_inl]
      · ext1 j; fin_cases j <;> simp
    · rw [Category.assoc, hover, hη, ← Spec.map_comp, ← Spec.map_id]
      congr 1
  · intro w hw
    have hw' : spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ w.left = η[A].left := hw
    obtain ⟨c, hc, hwc⟩ := exists_eq_ptHom_eps W f (w.left ≫ φ)
      (by rw [Category.assoc, hpb.w, ← Category.assoc, hover, ← Spec.map_comp]; rfl)
      (by rw [← Category.assoc, hw', he'])
    have key : ∀ a : R', w.left = spMap (epsScaleR a) ≫ v.left ↔ a = c := by
      intro a
      obtain ⟨ha, hea⟩ := epsScale_ptHom W f a h
      constructor
      · intro e
        rw [e, Category.assoc, hv, hea] at hwc
        exact TrivSqZeroExt.inr_injective (ptHom_origin_inj W _ _ hwc).1
      · rintro rfl
        refine hpb.hom_ext ?_ ?_
        · rw [Category.assoc, hv, hea, hwc]
        · rw [Category.assoc, hover, hover, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
          congr 2
          ext b <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]
    refine ⟨fun _ => c, (isLieComb_one_iff _ _ _).mpr ((key c).mpr rfl), fun c' hc' => ?_⟩
    funext i
    fin_cases i
    exact (key _).mp ((isLieComb_one_iff _ _ _).mp hc')

end GlobalTheory.WeierstrassCurve.OriginTangent
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsPolarisedAbelianSchemeLieBasisInvariants
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.WeierstrassCurve
open scoped CategoryTheory.Obj UpperHalfPlane

noncomputable section

namespace GlobalTheory.WeierstrassCurve

theorem fibre_over_scheme {R R' : Type} [CommRing R] [CommRing R'] (W : WeierstrassCurve R) (f : R →+* R')
    {A : Over (Sp R)} {A' : Over (Sp R')} [GrpObj A] [GrpObj A'] {ψ : A.left ⟶ scheme W} [IsIso ψ]
    (hψ : ψ ≫ toSpec W = A.hom) (he : eSec A ≫ ψ = zero W) {v : epsR R ⟶ A}
    {h : IsUnimodularSol (W.map (algebraMap R (DualNumber R))) ![DualNumber.eps, -1, 0]}
    (hv : v.left ≫ ψ = ptHom W (algebraMap R (DualNumber R)) ![DualNumber.eps, -1, 0] h)
    {φ : A'.left ⟶ A.left} (hφ : IsGrpPullback A' A (spMap f) φ) {v' : epsR R' ⟶ A'} (hv' : IsVecOver f φ v v') :
    ∃ h' : IsUnimodularSol (W.map ((algebraMap R' (DualNumber R')).comp f)) ![DualNumber.eps, -1, 0],
      IsPullback (φ ≫ ψ) A'.hom (toSpec W) (spMap f) ∧ eSec A' ≫ φ ≫ ψ = spMap f ≫ zero W ∧
      v'.left ≫ φ ≫ ψ = ptHom W ((algebraMap R' (DualNumber R')).comp f) ![DualNumber.eps, -1, 0] h' := by
  have hρ : (Chart.dualMapR f).comp (algebraMap R (DualNumber R)) = (algebraMap R' (DualNumber R')).comp f := by
    ext a <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  have hP : (Chart.dualMapR f ∘ ![DualNumber.eps, -1, 0]) = ![DualNumber.eps, -1, 0] := by
    ext1 j; fin_cases j
    · ext <;> simp [Chart.dualMapR]
    · simp
    · simp
  have h₁ := h.map_comp (Chart.dualMapR f)
  rw [hρ, hP] at h₁
  refine ⟨h₁, ?_, ?_, ?_⟩
  · exact hφ.1.of_iso (Iso.refl _) (asIso ψ) (Iso.refl _) (Iso.refl _) (by simp) (by simp) (by simp [hψ]) (by simp)
  · rw [← Category.assoc, PolBaseChange.eSec_comm hφ, Category.assoc, he]
  · rw [← Category.assoc, hv', Category.assoc, hv]
    exact (SpecMap_ptHom W _ _ h _).trans (ptHom_congr W _ _ _ hρ hP _)

theorem exists_polAV_invariants : ∀ (R : Type) [CommRing R] (W : WeierstrassCurve R), IsUnit W.Δ → ∃ (P : Out.PolAV (Sp R)) (v : epsR R ⟶ P.A), P.g = 1 ∧ IsLieBasis ![v] ∧ (∀ (R' : Type) [CommRing R'] (f' : R →+* R') (P' : Out.PolAV (Sp R')) (φ' : P'.A.left ⟶ P.A.left) (v' : epsR R' ⟶ P'.A), IsPolFibre f' P P' φ' → IsVecOver f' φ' v v' → IsLieBasis ![v']) ∧ (∀ (s' : R →+* ℂ) (P' : Out.PolAV (Sp ℂ)) (φ' : P'.A.left ⟶ P.A.left) (v' : epsR ℂ ⟶ P'.A) (u' : HolUnif P'.A P'.L P'.g) (w' : Fin P'.g → ℂ), IsPolFibre s' P P' φ' → IsVecOver s' φ' v v' → u'.IsDiff w' v' → w' ≠ 0 ∧ ∃ L : PeriodPair, (∀ z : ℂ, z ∈ L.lattice ↔ z • w' ∈ u'.Λ) ∧ s' W.c₄ = 12 * L.g₂ ∧ s' W.c₆ = 216 * L.g₃ ∧ s' W.Δ = L.g₂ ^ 3 - 27 * L.g₃ ^ 2) := by
  intro R _ W hΔ
  obtain ⟨P, ψ, v, hg, hiso, hψ, he, ⟨h, hv⟩, hb⟩ := GlobalTheory.WeierstrassCurve.exists_polAV R W hΔ
  refine ⟨P, v, hg, hb, fun R' _ f P' φ v' hP hv' => ?_, fun s P' φ v' u w hP hv' hd => ?_⟩
  · obtain ⟨h', h1, h2, h3⟩ := fibre_over_scheme W f hψ he hv hP.2.1 hv'
    exact OriginTangent.isLieBasis_eps R W R' f P'.A (φ ≫ ψ) v' h' h1 h2 h3
  · obtain ⟨h', h1, h2, h3⟩ := fibre_over_scheme W s hψ he hv hP.2.1 hv'
    obtain ⟨hw, x, y, t, hx, hy, hper, heq, ht, ht0, ht1, hty, hlim⟩ :=
      GlobalTheory.T.exists_weierstrass_coordinates_on_line R W s P'.A (φ ≫ ψ) v' h' h1 h2 h3 P'.L P'.g u w hd
    obtain ⟨L, hL⟩ := GlobalTheory.exists_periodPair_of_lattice_in_line P'.g u.Λ w (hP.1.trans hg) hw u.discrete u.full
    have hset : (L.lattice : Set ℂ) = {z | z • w ∈ u.Λ} := Set.ext hL
    have key := GlobalTheory.invariants_eq_of_periodic_solution L (W.map s) x y t 1 one_ne_zero (hset ▸ hx) (hset ▸ hy)
      (fun l hl => hper l ((hL l).1 hl)) (fun z hz => heq z fun e => hz ((hL z).2 e)) ht ht0 ht1 hty hlim
    simp only [one_pow, _root_.one_mul, WeierstrassCurve.map_c₄, WeierstrassCurve.map_c₆, WeierstrassCurve.map_Δ] at key
    exact ⟨hw, L, hL, key⟩

end GlobalTheory.WeierstrassCurve
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsPolarisedAbelianSchemeLieBasisInvariantsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.WeierstrassCurve
open scoped CategoryTheory.Obj UpperHalfPlane
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_polarisedAbelianScheme_lieBasis_invariants : ∀ (R : Type) [CommRing R] (W : WeierstrassCurve R), IsUnit W.Δ → ∃ (P : Out.PolAV (Sp R)) (v : epsR R ⟶ P.A), P.g = 1 ∧ IsLieBasis ![v] ∧ (∀ (R' : Type) [CommRing R'] (f' : R →+* R') (P' : Out.PolAV (Sp R')) (φ' : P'.A.left ⟶ P.A.left) (v' : epsR R' ⟶ P'.A), IsPolFibre f' P P' φ' → IsVecOver f' φ' v v' → IsLieBasis ![v']) ∧ (∀ (s' : R →+* ℂ) (P' : Out.PolAV (Sp ℂ)) (φ' : P'.A.left ⟶ P.A.left) (v' : epsR ℂ ⟶ P'.A) (u' : HolUnif P'.A P'.L P'.g) (w' : Fin P'.g → ℂ), IsPolFibre s' P P' φ' → IsVecOver s' φ' v v' → u'.IsDiff w' v' → w' ≠ 0 ∧ ∃ L : PeriodPair, (∀ z : ℂ, z ∈ L.lattice ↔ z • w' ∈ u'.Λ) ∧ s' W.c₄ = 12 * L.g₂ ∧ s' W.c₆ = 216 * L.g₃ ∧ s' W.Δ = L.g₂ ^ 3 - 27 * L.g₃ ^ 2) := by
  first | exact @GlobalTheory.WeierstrassCurve.exists_polAV_invariants | exact GlobalTheory.WeierstrassCurve.exists_polAV_invariants | (intros; apply GlobalTheory.WeierstrassCurve.exists_polAV_invariants <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsIsPolFibreOfKeyPB
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.KeyFibre

theorem eq_dualMapR_of_algebraMap {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R')
    (F : DualNumber R →+* DualNumber R') (h : ∀ a, F (algebraMap R _ a) = algebraMap R' _ (f a))
    (he : F DualNumber.eps = DualNumber.eps) : F = Chart.dualMapR f := by
  refine RingHom.ext fun x => ?_
  have e : x = algebraMap R _ x.fst + algebraMap R _ x.snd * DualNumber.eps := by
    ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
  rw [e, map_add (f := _), map_mul, h, h, he]
  ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]

theorem exists_isPolFibre_of_keyPB : ∀ (R R' : Type) [CommRing R] [CommRing R'] (f : R →+* R') (x : KeyIn R) (x' : KeyIn R'), KeyPB x' x f → ∃ (φ : x'.P.A.left ⟶ x.P.A.left) (hg : x'.P.g = x.P.g), IsPolFibre f x.P x'.P φ ∧ ∀ i, IsVecOver f φ (x.v (i.cast hg)) (x'.v i) := by
  intro R R' _ _ f x x' h
  obtain ⟨φ, he, w, hg, F, hφ, hw, h1, h2, hF, hε, hv⟩ := h
  refine ⟨φ, hg, ⟨hg, hφ, LBIso.symm ⟨w, hw⟩⟩, fun i => ?_⟩
  have := hv i
  rw [eq_dualMapR_of_algebraMap f F hF hε] at this
  exact this

end GlobalTheory.KeyFibre
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsMulEquivPointsOfIsGrpPullback
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.LamF

theorem _root_.GlobalTheory.LamF.exists_mulEquiv_points_of_isGrpPullback :
    ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (G : Over S) (G' : Over S') [GrpObj G] [GrpObj G'] (φ : G'.left ⟶ G.left), _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback G' G f φ → ∀ T : Over S', ∃ Φ : (T ⟶ G') ≃* (Over.mk (T.hom ≫ f) ⟶ G), ∀ x, (Φ x).left = x.left ≫ φ := by
  intro S S' f G G' _ _ φ hφ T
  obtain ⟨hpb, hmul⟩ := hφ
  let toFun : (T ⟶ G') → (Over.mk (T.hom ≫ f) ⟶ G) := fun x =>
    Over.homMk (x.left ≫ φ) (by
      show (x.left ≫ φ) ≫ G.hom = T.hom ≫ f
      rw [Category.assoc, hpb.w, ← Category.assoc, Over.w])
  let invFun : (Over.mk (T.hom ≫ f) ⟶ G) → (T ⟶ G') := fun y =>
    Over.homMk (hpb.lift y.left T.hom (by simpa using Over.w y)) (hpb.lift_snd _ _ _)
  have hto : ∀ x, (toFun x).left = x.left ≫ φ := fun x => rfl
  refine ⟨{ toFun := toFun, invFun := invFun, left_inv := ?_, right_inv := ?_, map_mul' := ?_ }, hto⟩
  · intro x
    ext1
    refine hpb.hom_ext ?_ ?_
    · exact hpb.lift_fst _ _ _
    · exact (hpb.lift_snd _ _ _).trans (Over.w x).symm
  · intro y
    ext1
    exact hpb.lift_fst _ _ _
  · intro x y
    ext1
    exact (hmul T x y (toFun x) (toFun y) (hto x) (hto y)).symm

end GlobalTheory.LamF
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ValuationLeIffExistsSmulMem
open NumberField IsDedekindDomain Formalism.L2.LamCM WithZero
open scoped nonZeroDivisors

namespace GlobalTheory.LamF

variable {K : Type} [Field K] [NumberField K]

theorem isLocGen_iff_valuation_eq (p : HeightOneSpectrum (𝓞 K)) (c : K) (I : FractionalIdeal (𝓞 K)⁰ K) :
    IsLocGen p c I ↔ p.valuation K c = exp (-FractionalIdeal.count K p I) := by
  constructor
  · rintro ⟨h0, h⟩
    rw [GlobalTheory.Idele.valuation_eq_exp_neg_count p h0, h]
  · intro h
    have h0 : c ≠ 0 := by
      rintro rfl
      rw [map_zero] at h
      exact exp_ne_zero h.symm
    refine ⟨h0, ?_⟩
    rw [GlobalTheory.Idele.valuation_eq_exp_neg_count p h0, exp_inj] at h
    exact neg_injective h

theorem valuation_le_iff_exists_smul_mem (p : HeightOneSpectrum (𝓞 K)) {I : FractionalIdeal (𝓞 K)⁰ K}
    (hI : I ≠ 0) (c : K) :
    p.valuation K c ≤ exp (-FractionalIdeal.count K p I) ↔ ∃ s : 𝓞 K, s ∉ p.asIdeal ∧ s • c ∈ I := by
  constructor
  · intro h
    obtain ⟨y, hy, hv⟩ := GlobalTheory.Idele.exists_mem_valuation_eq hI p
    have hvy : p.valuation K y ≠ 0 := by rw [hv]; exact exp_ne_zero
    have hy0 : y ≠ 0 := by rintro rfl; simp at hvy
    have h1 : p.valuation K (c / y) ≤ 1 := by
      rw [map_div₀, div_le_one₀ (zero_lt_iff.2 hvy), hv]; exact h
    obtain ⟨a, s, hs⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer p (c / y) h1
    refine ⟨s.1, s.2, ?_⟩
    have : (s.1 : 𝓞 K) • c = a • y := by
      rw [Algebra.smul_def, Algebra.smul_def, ← hs]
      field_simp
    rw [this]
    exact Submodule.smul_mem (I : Submodule (𝓞 K) K) a hy
  · rintro ⟨s, hs, hc⟩
    have h := (GlobalTheory.Idele.mem_iff_valuation_le hI _).1 hc p
    have h1 : p.valuation K (algebraMap (𝓞 K) K s) = 1 := by
      refine le_antisymm (p.valuation_le_one s) (not_lt.1 fun hlt => hs ?_)
      exact (p.valuation_lt_one_iff_mem s).1 hlt
    rwa [Algebra.smul_def, map_mul, h1, one_mul] at h

theorem mem_iff_forall_exists_smul_mem {V : Type} [AddCommGroup V] [Module (𝓞 K) V]
    (Λ : Submodule (𝓞 K) V) (z : V) :
    z ∈ Λ ↔ ∀ p : HeightOneSpectrum (𝓞 K), ∃ s : 𝓞 K, s ∉ p.asIdeal ∧ s • z ∈ Λ := by
  constructor
  · intro hz p
    exact ⟨1, fun h => p.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), by simpa using hz⟩
  · intro h
    let A : Ideal (𝓞 K) := Λ.comap (LinearMap.toSpanSingleton (𝓞 K) V z)
    have hA : A = ⊤ := by
      by_contra hne
      obtain ⟨m, hm, hAm⟩ := Ideal.exists_le_maximal A hne
      have hm0 : m ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hm (RingOfIntegers.not_isField K)
      obtain ⟨s, hs, hsz⟩ := h ⟨m, hm.isPrime, hm0⟩
      exact hs (hAm (by simpa [A] using hsz))
    have : (1 : 𝓞 K) ∈ A := hA ▸ Submodule.mem_top
    simpa [A] using this

theorem local_global_ideal_lattice : ∀ (K : Type) [Field K] [NumberField K],
    (∀ (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) (cl : HeightOneSpectrum (𝓞 K) → K), I ≠ 0 →
      (∀ p, IsLocGen p (cl p) I) → ∀ c : K,
        c ∈ I ↔ ∀ p : HeightOneSpectrum (𝓞 K), p.valuation K c ≤ p.valuation K (cl p)) ∧
    (∀ (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) (p : HeightOneSpectrum (𝓞 K)), I ≠ 0 →
      (∃ cl ∈ I, IsLocGen p cl I) ∧ ∀ cl, IsLocGen p cl I ↔ cl ≠ 0 ∧ ∀ c : K,
        p.valuation K c ≤ p.valuation K cl ↔ ∃ s : 𝓞 K, s ∉ p.asIdeal ∧ s • c ∈ I) ∧
    ∀ (V : Type) [AddCommGroup V] [Module (𝓞 K) V] (Λ : Submodule (𝓞 K) V) (z : V),
      z ∈ Λ ↔ ∀ p : HeightOneSpectrum (𝓞 K), ∃ s : 𝓞 K, s ∉ p.asIdeal ∧ s • z ∈ Λ := by
  intro K _ _
  refine ⟨fun I cl hI hcl c => ?_, fun I p hI => ⟨?_, fun cl => ?_⟩,
    fun V _ _ Λ z => mem_iff_forall_exists_smul_mem Λ z⟩
  · rw [GlobalTheory.Idele.mem_iff_valuation_le hI]
    refine forall_congr' fun p => ?_
    rw [(isLocGen_iff_valuation_eq p _ I).1 (hcl p)]
  · obtain ⟨y, hy, hv⟩ := GlobalTheory.Idele.exists_mem_valuation_eq hI p
    exact ⟨y, hy, (isLocGen_iff_valuation_eq p y I).2 hv⟩
  · constructor
    · intro h
      refine ⟨h.1, fun c => ?_⟩
      rw [(isLocGen_iff_valuation_eq p _ I).1 h]
      exact valuation_le_iff_exists_smul_mem p hI c
    · rintro ⟨-, h⟩
      obtain ⟨y, hy, hv⟩ := GlobalTheory.Idele.exists_mem_valuation_eq hI p
      refine (isLocGen_iff_valuation_eq p cl I).2 (le_antisymm ?_ ?_)
      · exact (valuation_le_iff_exists_smul_mem p hI cl).2 ((h cl).1 le_rfl)
      · rw [← hv]
        exact (h y).2 ((valuation_le_iff_exists_smul_mem p hI y).1 hv.le)

end GlobalTheory.LamF
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RingActIffOAct
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.LamF

theorem _root_.GlobalTheory.LamF.ringAct_iff_oAct :
    ∀ (O : Type) [CommRing O] (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G],
      (∀ a : _root_.ReciprocityTheory.ChartRestriction.G.Out.RingAct G O, ∃ b : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.OAct O G, b.act = a.act) ∧
        ∀ b : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.OAct O G, ∃ a : _root_.ReciprocityTheory.ChartRestriction.G.Out.RingAct G O, a.act = b.act := by
  intro O _ S G _ _
  exact ⟨fun a => ⟨_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.ofRingAct a, rfl⟩, fun b => ⟨b.toRingAct, rfl⟩⟩

end GlobalTheory.LamF
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsOActExtendDedekind
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM

theorem exists_oAct_extend_dedekind : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → ∀ (R K : Type) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K] (O : Type) [CommRing O] (G : Over (Sp R)) [GrpObj G] (G₀ : Over (Sp K)) [GrpObj G₀] (φ : G₀.left ⟶ G.left), IsAbelianScheme G → IsGrpPullback G₀ G (spMap (algebraMap R K)) φ → ∀ a₀ : OAct O G₀, ∃ a : OAct O G, ∀ c, (a₀.act c).left ≫ φ = φ ≫ (a.act c).left := by
  intro H R K _ _ _ _ _ O _ G _ G₀ _ φ hG hφ a₀
  have key := fun c => GlobalTheory.T.abelianScheme_hom_extends_dedekind_of_isGrpPullback_alt H R K G G G₀ G₀ φ φ hG hG hφ hφ (a₀.act c) (a₀.hom c)
  choose F hF hc hu using key
  refine ⟨⟨F, hF, ?_, ?_, ?_⟩, hc⟩
  · refine (hu 1 (𝟙 G) ?_).symm
    rw [a₀.one]
    simp
  · intro a b
    refine (hu (a * b) (F a ≫ F b) ?_).symm
    rw [a₀.mul, Over.comp_left, Over.comp_left, Category.assoc, hc b, ← Category.assoc, hc a, Category.assoc]
  · intro a b
    refine (hu (a + b) (F a * F b) ?_).symm
    let ψ : Over.mk (G₀.hom ≫ spMap (algebraMap R K)) ⟶ G := Over.homMk φ hφ.1.w
    have h := hφ.2 G₀ (a₀.act a) (a₀.act b) (ψ ≫ F a) (ψ ≫ F b) (hc a).symm (hc b).symm
    rw [a₀.add, ← h, ← MonObj.comp_mul]
    rfl

end GlobalTheory.CM
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.AbelianSchemeSurjectiveOfOntoComplexPointsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

theorem _root_.GlobalTheory.T.abelianScheme_surjective_of_onto_complex_points : ∀ (R : Type) [CommRing R] [IsDomain R] (σ : R →+* ℂ), Function.Injective σ → ∀ (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (Φ : B ⟶ A), IsAbelianScheme A → IsAbelianScheme B → (∀ y : Over.mk (spMap σ) ⟶ A, ∃ x : Over.mk (spMap σ) ⟶ B, y = x ≫ Φ) → Surjective Φ.left ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (y : Over.mk t ⟶ A), ∃ x : Over.mk t ⟶ B, y = x ≫ Φ := by
  first | exact @GlobalTheory.OntoSurj.surjective_of_onto_complex_points | exact GlobalTheory.OntoSurj.surjective_of_onto_complex_points | (intros; apply GlobalTheory.OntoSurj.surjective_of_onto_complex_points <;> assumption)
end
