module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSumTaylorCoordinateSpaceEntire
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTranslationIntertwinerUnitary
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.InverseBundleGeneratorPointOfChartUnitsSections
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsDivOfExpandsAt
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.RosIdSt
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.VeryAmpleByPull
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExpansionOfIntegralSectionIsIntegral

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpSeriesCoeffNormBoundedRingLaws
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpSeriesCoeffNormBoundedRingLaws
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne

theorem sup_norm_laws : ∀ (q : ℕ) [Fact q.Prime], (∀ (f g : ℂ_[q]⟦X⟧) (A B : ℝ), Bd A f → Bd B g → Bd (max A B) (f + g) ∧ Bd (A * B) (f * g)) ∧ (∀ (f h : ℂ_[q]⟦X⟧) (A : ℝ), Bd A f → Bd 1 h → constantCoeff h = 0 → Bd A (f.subst h)) ∧ (∀ (f g : ℂ_[q]⟦X⟧), Bd 1 f → ‖constantCoeff f‖ = 1 → f * g = 1 → Bd 1 g) ∧ (∀ (f g : ℂ_[q]⟦X⟧) (B : ℝ), Bdd f → Bdd g → Bd B (f * g) → ∀ i j, ‖coeff i f‖ * ‖coeff j g‖ ≤ B) ∧ (∀ (f g : ℂ_[q]⟦X⟧), Bdd f → Bdd g → f * g = 1 → constantCoeff f = 1 → Bd 1 f ∧ Bd 1 g) ∧ (∀ (f v : ℂ_[q]⟦X⟧) (k : ℕ) (B : ℝ), Bd 1 v → ‖constantCoeff v‖ = 1 → Bd B (X ^ k * v * f) → Bd B f) := by
  intro q _
  have R := GlobalTheory.EvenTheta.SerRing.series_ring_laws q
  have hmul : ∀ (f g : ℂ_[q]⟦X⟧) (A B : ℝ), Bd A f → Bd B g → Bd (A * B) (f * g) :=
    fun f g A B hf hg => R.2.2.2.2.2.2 f g A B hf hg
  have hinv : ∀ f : ℂ_[q]⟦X⟧, Bd 1 f → ‖constantCoeff f‖ = 1 → Bd 1 f⁻¹ :=
    fun f hf h0 => R.2.2.2.2.1 f hf h0
  have hinv' : ∀ (f g : ℂ_[q]⟦X⟧), Bd 1 f → ‖constantCoeff f‖ = 1 → f * g = 1 → Bd 1 g := by
    intro f g hf h0 hfg
    have hc : constantCoeff f ≠ 0 := by
      intro h
      rw [h, norm_zero] at h0
      exact zero_ne_one h0
    have hgf : g = f⁻¹ := by
      rw [PowerSeries.eq_inv_iff_mul_eq_one hc, mul_comm]
      exact hfg
    rw [hgf]
    exact hinv f hf h0
  have hgauss : ∀ (f g : ℂ_[q]⟦X⟧) (B : ℝ), Bdd f → Bdd g → Bd B (f * g) →
      ∀ i j, ‖coeff i f‖ * ‖coeff j g‖ ≤ B :=
    fun f g B hf hg hB => GlobalTheory.EvenTheta.sup_norm_mul_padicComplex q f g B hf hg hB
  refine ⟨fun f g A B hf hg => ⟨fun n => GlobalTheory.EvenTheta.SerRing.norm_coeff_add_le f g A B hf hg n,
    hmul f g A B hf hg⟩, fun f h A hf hh h0 => R.2.2.2.2.2.1 f h A hf hh h0, hinv', hgauss, ?_, ?_⟩
  · intro f g hf hg hfg h1
    have hg0 : constantCoeff g = 1 := by
      have hc := congrArg constantCoeff hfg
      rw [map_mul, h1, one_mul, map_one] at hc
      exact hc
    have hB : Bd 1 (f * g) := by
      rw [hfg]
      intro n
      rw [coeff_one]
      split_ifs <;> simp
    have H := hgauss f g 1 hf hg hB
    refine ⟨fun i => ?_, fun j => ?_⟩
    · have hi := H i 0
      rwa [coeff_zero_eq_constantCoeff_apply, hg0, norm_one, mul_one] at hi
    · have hj := H 0 j
      rwa [coeff_zero_eq_constantCoeff_apply, h1, norm_one, one_mul] at hj
  · intro f v k B hv h0 hB
    have hw : Bd B (v * f) := by
      intro m
      have hm := hB (m + k)
      rwa [mul_assoc, coeff_X_pow_mul] at hm
    have hc : constantCoeff v ≠ 0 := by
      intro h
      rw [h, norm_zero] at h0
      exact zero_ne_one h0
    have hvf := hmul v⁻¹ (v * f) 1 B (hinv v hv h0) hw
    rwa [← mul_assoc, PowerSeries.inv_mul_cancel _ hc, one_mul, one_mul] at hvf

end GlobalTheory.MomOne
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpSeriesCoeffNormBoundedRingLawsStatement
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cpSeriesCoeffNormBounded_ring_laws : ∀ (q : ℕ) [Fact q.Prime], (∀ (f g : ℂ_[q]⟦X⟧) (A B : ℝ), Bd A f → Bd B g → Bd (max A B) (f + g) ∧ Bd (A * B) (f * g)) ∧ (∀ (f h : ℂ_[q]⟦X⟧) (A : ℝ), Bd A f → Bd 1 h → constantCoeff h = 0 → Bd A (f.subst h)) ∧ (∀ (f g : ℂ_[q]⟦X⟧), Bd 1 f → ‖constantCoeff f‖ = 1 → f * g = 1 → Bd 1 g) ∧ (∀ (f g : ℂ_[q]⟦X⟧) (B : ℝ), Bdd f → Bdd g → Bd B (f * g) → ∀ i j, ‖coeff i f‖ * ‖coeff j g‖ ≤ B) ∧ (∀ (f g : ℂ_[q]⟦X⟧), Bdd f → Bdd g → f * g = 1 → constantCoeff f = 1 → Bd 1 f ∧ Bd 1 g) ∧ (∀ (f v : ℂ_[q]⟦X⟧) (k : ℕ) (B : ℝ), Bd 1 v → ‖constantCoeff v‖ = 1 → Bd B (X ^ k * v * f) → Bd B f) := by
  first | exact @GlobalTheory.MomOne.sup_norm_laws | exact GlobalTheory.MomOne.sup_norm_laws | (intros; apply GlobalTheory.MomOne.sup_norm_laws <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.TorusExtensionOverCompleteLocalDvr
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.TorusExtensionOverCompleteLocalDvr
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorusModel

open GlobalTheory.AdicColimit

section BaseChange

variable {S S' : Scheme.{0}} (f : S' ⟶ S)

theorem exists_isGt (hG : GlobalFnsSt) (E : SplitExt S) :
    ∃ (H : Over S) (_ : GrpObj H), IsCommMonObj H ∧ E.IsGt H := by
  letI := E.free
  letI := E.finite
  have hN : ∀ k, (E.O (E.basis k)).L.IsLB := fun k => (E.O (E.basis k)).isLB
  obtain ⟨G, q, u, hu⟩ := exists_generatorScheme E.B.left _ (fun k => (E.O (E.basis k)).L) hN
  obtain ⟨h₁, h₂, h₃, -, -⟩ :=
    generatorScheme_properties E.B.left _ (fun k => (E.O (E.basis k)).L) hN G q u hu
  obtain ⟨inst, hc, d, -⟩ := exists_grpObj_gtDatum_of_generators hG S E G q u hu h₁ inferInstance h₃
  exact ⟨Over.mk (q ≫ E.B.hom), inst, hc, ⟨d⟩⟩

def polPull [IsAffine S] (P : PolAV S) : PolAV S' :=
  have h := isGrpPullback_pullback P.A f
  have hL' := pull_isLB P.isLB (pullback.fst P.A.hom f)
  have hw := (isGen_iff _).1 (PolBaseChange.lbIso_refl hL').choose_spec
  { A := (Over.pullback f).obj P.A
    isAb := TLinPf.isAb_pullback f P.A P.isAb
    g := P.g
    smoothDim := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback h.1 P.smoothDim
    L := P.L.pull (pullback.fst P.A.hom f)
    isLB := hL'
    rigid := PolBaseChange.rigidified_pull h P.rigid
    sym := PolBaseChange.sym_pull h P.sym
    ample := relAmple_pull h.1 P.isLB hL' hw ⊤ (isAffineOpen_top S) (fun _ => trivial) P.ample
    ktriv := kTriv_pull h P.isLB hL' hw P.ktriv }

theorem torsion_pullback (B : Over S) [GrpObj B] (N : ℕ) (h₁ : IsFinite (𝟙 B ^ N).left) (h₂ : Flat (𝟙 B ^ N).left) :
    IsFinite (torsion ((Over.pullback f).obj B) N).hom ∧ Flat (torsion ((Over.pullback f).obj B) N).hom := by
  rw [← MulEtaleDvr.mulN_eq_pow] at h₁ h₂
  have H := MulEtaleDvr.isPullback_torsion ((Over.pullback f).obj B) N
  rw [← MulEtaleDvr.pullback_map_mulN] at H
  exact ⟨MorphismProperty.of_isPullback (P := @IsFinite) H
      (MorphismProperty.overPullbackMap (P := @IsFinite) f _ h₁),
    MorphismProperty.of_isPullback (P := @Flat) H (MorphismProperty.overPullbackMap (P := @Flat) f _ h₂)⟩

variable {H : Over S} [GrpObj H]

theorem exists_pushEquiv (T : Over S') (s : T.left ⟶ S) (hs : s = T.hom ≫ f) :
    ∃ π : (T ⟶ (Over.pullback f).obj H) ≃* (Over.mk s ⟶ H), ∀ x, (π x).left = x.left ≫ pullback.fst H.hom f := by
  subst hs
  have h := isGrpPullback_pullback H f
  refine ⟨MulEquiv.ofBijective (pushHom h T) ⟨fun x y e => Over.OverMorphism.ext
    (h.1.hom_ext (congrArg (fun q => q.left) e) (by rw [Over.w, Over.w])), fun y => ?_⟩, fun x => rfl⟩
  exact ⟨Over.homMk (h.1.lift y.left T.hom (Over.w y)) (h.1.lift_snd _ _ _),
    Over.OverMorphism.ext (h.1.lift_fst _ _ _)⟩

def actPull [IsCommMonObj H] {O : Type} [Ring O] (ρ : RingAct H O) : RingAct ((Over.pullback f).obj H) O where
  act a := (Over.pullback f).map (ρ.act a)
  hom a := by have := ρ.hom a; infer_instance
  map_one := by rw [ρ.map_one, CategoryTheory.Functor.map_id]
  map_mul a b := by rw [ρ.map_mul, CategoryTheory.Functor.map_comp]
  map_add a b := by
    rw [ρ.map_add a b]
    exact map_mul (Over.pullback f).homMonoidHom (ρ.act a) (ρ.act b)

end BaseChange

theorem exists_model (hG : GlobalFnsSt) {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
    [IsCommMonObj G] (U : UnifPre I D A G) {O : Type} [CommRing O] [StarRing O] [Module O D.toPre.X]
    {ιD : D.OAct O} {ιA : A.OAct O} {ιG : RingAct G O} (hO : U.OLinear O ιD ιA ιG)
    {S' : Scheme.{0}} (f : S' ⟶ Spec (CommRingCat.of R)) :
    ∃ (Gt : Over S') (_ : GrpObj Gt) (_ : IsCommMonObj Gt) (ρ : RingAct Gt O)
      (J : ∀ (T : Over S') (s : T.left ⟶ Spec (CommRingCat.of R)), s = T.hom ≫ f → IsAdicColimit I (Over.mk s) →
        ((T ⟶ Gt) ≃* (Over.mk s ⟶ G))),
      (GtBaseChange.extBC f (splitExt D.toPre)).IsGt Gt ∧
      (∀ T T' s s' hs hs' hT hT' (k : T' ⟶ T) (x : T ⟶ Gt),
        (J T' s' hs' hT' (k ≫ x)).left = k.left ≫ (J T s hs hT x).left) ∧
      ∀ T s hs hT (x : T ⟶ Gt) (a : O), J T s hs hT (x ≫ ρ.act a) = J T s hs hT x ≫ ιG.act a := by
  obtain ⟨H, _, _, hH⟩ := exists_isGt hG (splitExt D.toPre)
  obtain ⟨Φ, hΦ⟩ := exists_points hG hH
  obtain ⟨ρ, hρ⟩ := exists_ringAct hG ιD (Φ := Φ) hΦ
  obtain ⟨J, hJ⟩ := exists_mulEquiv U hG (Φ := Φ) hΦ
  choose π hπ using exists_pushEquiv f (H := H)
  obtain ⟨d⟩ := hH
  refine ⟨(Over.pullback f).obj H, inferInstance, inferInstance, actPull f ρ,
    fun T s hs hT => (π T s hs).trans (J _ hT), GtBaseChange.isGt_extBC f _ H d, ?_, ?_⟩
  · intro T T' s s' hs hs' hT hT' k x
    let k₀ : Over.mk s' ⟶ Over.mk s := Over.homMk k.left (by
      change k.left ≫ s = s'
      rw [hs, hs', Over.w_assoc])
    have e : π T' s' hs' (k ≫ x) = k₀ ≫ π T s hs x := Over.OverMorphism.ext (by
      rw [hπ, Over.comp_left, Over.comp_left, hπ, Category.assoc]; rfl)
    have := (hJ _ hT' (k₀ ≫ π T s hs x) _).2 (((hJ _ hT (π T s hs x) _).1 rfl).pull k₀ (hΦ.1 _ _ k₀ _))
    rw [← e] at this
    exact congrArg (·.left) this
  · intro T s hs hT x a
    have e : π T s hs (x ≫ (actPull f ρ).act a) = π T s hs x ≫ ρ.act a := Over.OverMorphism.ext (by
      rw [hπ, Over.comp_left, Over.comp_left, hπ, Category.assoc, Category.assoc]
      exact congrArg (x.left ≫ ·) (pullback.lift_fst _ _ _))
    have := (hJ _ hT (π T s hs x ≫ ρ.act a) _).2 (((hJ _ hT (π T s hs x) _).1 rfl).smul hG hO a (hρ a _ _))
    rw [← e] at this
    exact this

theorem isAdicColimit_of_pow {R A : Type} [CommRing R] [CommRing A] (I : Ideal R) (φ : R →+* A) (n : ℕ)
    (h : ∀ a ∈ I ^ n, φ a = 0) : IsAdicColimit I (Over.mk (Spec.map (CommRingCat.ofHom φ))) := by
  refine isAdicColimit_of_factor n (Spec.map (CommRingCat.ofHom (Ideal.Quotient.lift (I ^ (n + 1)) φ
    fun a ha => h a (Ideal.pow_le_pow_right (Nat.le_succ n) ha)))) ?_
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, Ideal.Quotient.lift_comp_mk]
  rfl

theorem isAdicColimit_of_finite_flat {R O : Type} [CommRing R] [CommRing O] [IsLocalRing O] (I : Ideal R)
    (f : R →+* O) (hO : IsAdicComplete (I.map f) O) (hm : ∀ a ∈ maximalIdeal O, ∃ n : ℕ, a ^ n ∈ I.map f)
    (A : Type) [CommRing A] [Algebra O A] [Module.Finite O A] [Module.Flat O A] :
    IsAdicColimit I (Over.mk (Spec.map (CommRingCat.ofHom ((algebraMap O A).comp f)))) := by
  have := henselianLocalRing_of_le_radical (I.map f) hm
  refine isAdicColimit_finite_henselian_of_local isAdicColimit_spec_of_isLocalRing isAdicColimit_of_disjoint_cover
    R I O A _ ?_
  rw [← Ideal.map_map]
  exact GlobalTheory.FlatComplete.isAdicComplete_of_finite_flat O _ hO A

theorem main : Laws → Laws4 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] (t : SAB H (Sp V)) (P : PELUnif (maximalIdeal V) t) (O : Type) [CommRing O] [IsLocalRing O] (f : V →+* O), IsLocalHom f → IsAdicComplete ((maximalIdeal V).map f) O → (∀ a ∈ maximalIdeal O, ∃ n : ℕ, a ^ n ∈ (maximalIdeal V).map f) → ∃ (Ex : SplitExt (Spec (CommRingCat.of O))) (B : PolAV (Spec (CommRingCat.of O))) (_ : B.A = Ex.B) (_ : HEq B.grp Ex.grpB) (Gt : Over (Spec (CommRingCat.of O))) (_ : GrpObj Gt) (_ : IsCommMonObj Gt) (ρ : RingAct Gt (𝓞 E)) (J : ∀ (A : Type) [CommRing A] [Algebra O A], ((Module.Finite O A ∧ Module.Free O A) ∨ ∃ n : ℕ, ∀ a ∈ maximalIdeal V ^ n, algebraMap O A (f a) = 0) → (specO O A ⟶ Gt) → (Over.mk (Spec.map (CommRingCat.ofHom ((algebraMap O A).comp f))) ⟶ t.G)), Ex.IsGt Gt ∧ (∀ N : ℕ, 1 ≤ N → IsFinite (torsion Ex.B N).hom ∧ Flat (torsion Ex.B N).hom) ∧ (∀ (A A' : Type) [CommRing A] [Algebra O A] [CommRing A'] [Algebra O A'] (hA : ((Module.Finite O A ∧ Module.Free O A) ∨ ∃ n : ℕ, ∀ a ∈ maximalIdeal V ^ n, algebraMap O A (f a) = 0)) (hA' : ((Module.Finite O A' ∧ Module.Free O A') ∨ ∃ n : ℕ, ∀ a ∈ maximalIdeal V ^ n, algebraMap O A' (f a) = 0)) (φ : A →ₐ[O] A') (x : specO O A ⟶ Gt), (J A' hA' (ptMap φ ≫ x)).left = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ (J A hA x).left) ∧ ∀ (A : Type) [CommRing A] [Algebra O A] (hA : ((Module.Finite O A ∧ Module.Free O A) ∨ ∃ n : ℕ, ∀ a ∈ maximalIdeal V ^ n, algebraMap O A (f a) = 0)), (∀ x x', J A hA (x * x') = J A hA x * J A hA x') ∧ (∀ x (a : 𝓞 E), J A hA (x ≫ ρ.act a) = J A hA x ≫ t.act.act a) ∧ Function.Injective (J A hA) ∧ ((∃ n : ℕ, ∀ a ∈ maximalIdeal V ^ n, algebraMap O A (f a) = 0) → Function.Surjective (J A hA)) ∧ ∀ (I : Ideal A) (g : Over.mk (Spec.map (CommRingCat.ofHom ((algebraMap O A).comp f))) ⟶ t.G), IsNilpotent I → Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ g.left = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ (1 : Over.mk (Spec.map (CommRingCat.ofHom ((algebraMap O A).comp f))) ⟶ t.G).left → ∃ x, J A hA x = g := by
  intro hL _ E _ _ _ H V _ _ _ _ t P O _ _ f _ hO hm
  letI := H.starRing
  obtain ⟨Gt, _, _, ρ, J, h₁, h₂, h₃⟩ := exists_model hL.globalFns P.U.toUnifPre P.lin (spMap f)
  have hs : ∀ (A : Type) [CommRing A] [Algebra O A],
      Spec.map (CommRingCat.ofHom ((algebraMap O A).comp f)) = (specO O A).hom ≫ spMap f := fun A _ _ => by
    rw [CommRingCat.ofHom_comp, Spec.map_comp]; rfl
  have hc : ∀ (A : Type) [CommRing A] [Algebra O A], ((Module.Finite O A ∧ Module.Free O A) ∨
      ∃ n : ℕ, ∀ a ∈ maximalIdeal V ^ n, algebraMap O A (f a) = 0) →
      IsAdicColimit (maximalIdeal V) (Over.mk (Spec.map (CommRingCat.ofHom ((algebraMap O A).comp f)))) := by
    rintro A _ _ (⟨_, _⟩ | ⟨n, hn⟩)
    exacts [isAdicColimit_of_finite_flat _ f hO hm A, isAdicColimit_of_pow _ _ n hn]
  refine ⟨GtBaseChange.extBC (spMap f) (splitExt P.D.toPre), polPull (spMap f) P.D.toPre.P, rfl, HEq.rfl,
    Gt, inferInstance, inferInstance, ρ, fun A _ _ hA => J (specO O A) _ (hs A) (hc A hA), h₁, fun N hN => ?_,
    fun A A' _ _ _ _ hA hA' φ x => h₂ _ _ _ _ _ _ _ _ (ptMap φ) x,
    fun A _ _ hA => ⟨map_mul _, h₃ _ _ _ _, MulEquiv.injective _, fun _ => MulEquiv.surjective _,
      fun _ g _ _ => MulEquiv.surjective _ g⟩⟩
  obtain ⟨a, b, -⟩ := hL.mulN _ P.D.toPre.P N hN
  exact torsion_pullback (spMap f) P.D.toPre.P.A N a b

end GlobalTheory.TorusModel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.TorusExtensionOverCompleteLocalDvrStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torusExtension_over_completeLocal_dvr : Laws → Laws4 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] (t : SAB H (Sp V)) (P : PELUnif (maximalIdeal V) t) (O : Type) [CommRing O] [IsLocalRing O] (f : V →+* O), IsLocalHom f → IsAdicComplete ((maximalIdeal V).map f) O → (∀ a ∈ maximalIdeal O, ∃ n : ℕ, a ^ n ∈ (maximalIdeal V).map f) → ∃ (Ex : SplitExt (Spec (CommRingCat.of O))) (B : PolAV (Spec (CommRingCat.of O))) (_ : B.A = Ex.B) (_ : HEq B.grp Ex.grpB) (Gt : Over (Spec (CommRingCat.of O))) (_ : GrpObj Gt) (_ : IsCommMonObj Gt) (ρ : RingAct Gt (𝓞 E)) (J : ∀ (A : Type) [CommRing A] [Algebra O A], ((Module.Finite O A ∧ Module.Free O A) ∨ ∃ n : ℕ, ∀ a ∈ maximalIdeal V ^ n, algebraMap O A (f a) = 0) → (specO O A ⟶ Gt) → (Over.mk (Spec.map (CommRingCat.ofHom ((algebraMap O A).comp f))) ⟶ t.G)), Ex.IsGt Gt ∧ (∀ N : ℕ, 1 ≤ N → IsFinite (torsion Ex.B N).hom ∧ Flat (torsion Ex.B N).hom) ∧ (∀ (A A' : Type) [CommRing A] [Algebra O A] [CommRing A'] [Algebra O A'] (hA : ((Module.Finite O A ∧ Module.Free O A) ∨ ∃ n : ℕ, ∀ a ∈ maximalIdeal V ^ n, algebraMap O A (f a) = 0)) (hA' : ((Module.Finite O A' ∧ Module.Free O A') ∨ ∃ n : ℕ, ∀ a ∈ maximalIdeal V ^ n, algebraMap O A' (f a) = 0)) (φ : A →ₐ[O] A') (x : specO O A ⟶ Gt), (J A' hA' (ptMap φ ≫ x)).left = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ (J A hA x).left) ∧ ∀ (A : Type) [CommRing A] [Algebra O A] (hA : ((Module.Finite O A ∧ Module.Free O A) ∨ ∃ n : ℕ, ∀ a ∈ maximalIdeal V ^ n, algebraMap O A (f a) = 0)), (∀ x x', J A hA (x * x') = J A hA x * J A hA x') ∧ (∀ x (a : 𝓞 E), J A hA (x ≫ ρ.act a) = J A hA x ≫ t.act.act a) ∧ Function.Injective (J A hA) ∧ ((∃ n : ℕ, ∀ a ∈ maximalIdeal V ^ n, algebraMap O A (f a) = 0) → Function.Surjective (J A hA)) ∧ ∀ (I : Ideal A) (g : Over.mk (Spec.map (CommRingCat.ofHom ((algebraMap O A).comp f))) ⟶ t.G), IsNilpotent I → Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ g.left = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ (1 : Over.mk (Spec.map (CommRingCat.ofHom ((algebraMap O A).comp f))) ⟶ t.G).left → ∃ x, J A hA x = g := by
  first | exact @GlobalTheory.TorusModel.main | exact GlobalTheory.TorusModel.main | (intros; apply GlobalTheory.TorusModel.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsIntegralExpansionsOfValuationGe
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsIntegralExpansionsOfValuationGe
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace IntComb

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
  {D : DegData V (maximalIdeal V)}

theorem exists_int_of_vge (hϖ : Irreducible ϖ) {k : ℕ} {α : D.toPre.X}
    {s : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre (FractionRing V) α) (DegPre.famε k))} {r : ℚ}
    (hr : 0 ≤ r) (hs : VGe D (FractionRing V) (FamInt.ordVal hϖ) k α s r) :
    ∃ f : D.toPre.SecB k α,
      GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing V) α) (DegPre.famε k) s
        (D.toPre.famφB α) (DegPre.famε k) f (DegPre.prB D.toPre (FractionRing V)).left 1 := by
  obtain ⟨n, a, σ, σF, hσ, hva, hsum⟩ := hs
  have hint : ∀ i, ∃ b : V, a i = algebraMap V (FractionRing V) b := fun i => by
    obtain ⟨b, hb⟩ := (FamInt.le_ordFn_iff hϖ (a i) 0).1 (le_trans (by exact_mod_cast hr) (hva i))
    exact ⟨b, by rw [hb, zpow_zero, _root_.one_mul]⟩
  choose b hb using hint
  refine ⟨FamInt.secLin (fun i => scal D.toPre.P.A.hom (b i)) σ,
    SectionScalarValuation.secScal_of_sval D.toPre.P.isLB fun y J hJ => ?_⟩
  rw [SectionScalarValuation.sval_lin (fun i => scal D.toPre.P.A.hom (b i)) σ (fun _ => rfl) _ y hJ,
    SectionScalarValuation.sval_lin (fun i => gF D.toPre (FractionRing V) (a i)) σF (fun j => hsum j) (𝟙 _) y hJ]
  refine Finset.sum_congr rfl fun i _ => congrArg₂ (· * ·) ?_ (SectionScalarValuation.secScal_sval (hσ i) _ y hJ)
  have e1 : gs (𝟙 _ ≫ (DegPre.prB D.toPre (FractionRing V)).left) y ⊤ (scal D.toPre.P.A.hom (b i)) =
      cst ((𝟙 _ ≫ (DegPre.prB D.toPre (FractionRing V)).left) ≫ D.toPre.P.A.hom) y (b i) :=
    gs_pull _ _ y ⊤ trivial _
  have e2 : gs (𝟙 _) y ⊤ (gF D.toPre (FractionRing V) (a i)) =
      cst (𝟙 _ ≫ (fst (TF (R := V) (FractionRing V)) D.toPre.P.A).left) y (a i) :=
    gs_pull _ (fst (TF (R := V) (FractionRing V)) D.toPre.P.A).left y ⊤ trivial _
  have e3 : (𝟙 _ ≫ (DegPre.prB D.toPre (FractionRing V)).left) ≫ D.toPre.P.A.hom =
      ((𝟙 _ ≫ (fst (TF (R := V) (FractionRing V)) D.toPre.P.A).left) ≫
        spMap (algebraMap (FractionRing V) (FractionRing V))) ≫ spMap (algebraMap V (FractionRing V)) := by
    rw [Category.id_comp, Category.id_comp, Category.assoc, Over.w]
    exact (Over.w (fst (TF (R := V) (FractionRing V)) D.toPre.P.A)).symm
  rw [e1, e2, e3, cst_comp, cst_comp, hb i]
  rfl

theorem integralFamily_of_min (hL : Laws) (hϖ : Irreducible ϖ) {Q : D.toPre.X → ℤ} (hQ : QForm.IsQ D.toPre ϖ Q)
    {q : ℕ} (hq : 1 ≤ q) (χ : D.toPre.X) (β : D.toPre.SecB q χ) (hmin : ∀ z, Q χ ≤ Q (χ + q • z)) :
    ∃ (Φ : Fam D.toPre (FractionRing V) q) (f : ∀ α, D.toPre.SecB q α),
      (∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing V) α) (DegPre.famε q) (Φ.s α)
        (D.toPre.famφB α) (DegPre.famε q) (f α) (DegPre.prB D.toPre (FractionRing V)).left 1) ∧
      f χ = β ∧ ∀ α, (∀ z, α ≠ χ + q • z) → ∀ j, (f α).f j = 0 := by
  classical
  obtain ⟨σ, hσ⟩ := FamInt.exists_pull (F := FractionRing V) β
  obtain ⟨Φ, hΦ, hΦ0⟩ := UUA.exists_fam_rep (F := FractionRing V) hL.globalFns D.tau_bimult q χ (fun a b h => by
    have h' : (q : ℤ) • a = (q : ℤ) • b := by
      rw [natCast_zsmul, natCast_zsmul]; exact add_left_cancel h
    exact smul_right_injective D.toPre.X (by omega : (q : ℤ) ≠ 0) h') σ
  have h0 : VGe D (FractionRing V) (FamInt.ordVal hϖ) q χ (Φ.s χ) 0 := by
    refine ⟨1, fun _ => 1, fun _ => β, fun _ => Φ.s χ, fun _ => hΦ ▸ hσ, fun _ => ?_, fun j => ?_⟩
    · simp
    · simp [DegPre.constBF]
  have key : ∀ α : D.toPre.X, ∃ f : D.toPre.SecB q α,
      GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing V) α) (DegPre.famε q) (Φ.s α)
        (D.toPre.famφB α) (DegPre.famε q) f (DegPre.prB D.toPre (FractionRing V)).left 1 ∧
      (∀ h : χ = α, f = h ▸ β) ∧ ((∀ z, α ≠ χ + q • z) → ∀ j, f.f j = 0) := by
    intro α
    by_cases hα : χ = α
    · subst hα
      exact ⟨β, hΦ ▸ hσ, fun _ => rfl, fun h => absurd (by simp) (h 0)⟩
    by_cases hc : ∃ z, α = χ + q • z
    · obtain ⟨z, rfl⟩ := hc
      have H := SectionScalarValuation.fe_move hϖ hQ (FamInt.valOver_ordVal hϖ) q z χ Φ h0
      have hle := hmin z
      rw [q_shift hϖ hQ, le_add_iff_nonneg_right] at hle
      have hpos : (0 : ℤ) ≤ q * Q z + QForm.bOf D.toPre Q z χ :=
        nonneg_of_mul_nonneg_right hle (by omega)
      obtain ⟨f, h1⟩ := exists_int_of_vge hϖ (by rw [zero_add]; exact_mod_cast hpos) H
      exact ⟨f, h1, fun h => absurd h hα, fun h => absurd rfl (h z)⟩
    · refine ⟨SecOps.secZero, SectionScalarValuation.secScal_of_sval D.toPre.P.isLB fun y J hJ => ?_, fun h => absurd h hα,
        fun _ _ => rfl⟩
      rw [UUA.sval_zero_of (s := SecOps.secZero) (fun _ => rfl) _ y J (hJ.mem _ _),
        UUA.sval_zero_of (hΦ0 α fun mu e => hc ⟨mu, e.symm⟩) _ y J (hJ.mem _ _)]
  choose f h1 h2 h3 using key
  exact ⟨Φ, f, h1, h2 χ rfl, h3⟩

theorem exists_min_reps (hϖ : Irreducible ϖ) {Q : D.toPre.X → ℤ} (hQ : QForm.IsQ D.toPre ϖ Q)
    {q : ℕ} (hq : 1 ≤ q) : ∃ (N : ℕ) (χ : Fin N → D.toPre.X), (∀ α, ∃ i m, α = χ i + q • m) ∧
      (∀ i i', i' ≠ i → ∀ z, χ i ≠ χ i' + q • z) ∧ ∀ i z, Q (χ i) ≤ Q (χ i + q • z) := by
  obtain ⟨-, e, he⟩ := exists_representatives_mod_nsmul D.toPre.X q hq
  have hnn : ∀ x, 0 ≤ Q x := fun x => by
    by_cases hx : x = 0
    · rw [hx, QForm.Q_zero hϖ D hQ]
    · exact le_trans zero_le_one (QForm.Q_pos hϖ D hQ hx)
  have hm : ∀ i, ∃ m : D.toPre.X, ∀ z, Q (e i + q • m) ≤ Q (e i + q • z) := fun i => by
    refine ⟨Function.argmin (fun z : D.toPre.X => (Q (e i + q • z)).toNat), fun z => ?_⟩
    have h := Function.argmin_le (fun z : D.toPre.X => (Q (e i + q • z)).toNat) z
    have h1 := hnn (e i + q • z)
    omega
  choose m hm using hm
  refine ⟨_, fun i => e i + q • m i, fun α => ?_, fun i i' hi z h => hi ?_, fun i z => ?_⟩
  · obtain ⟨i, ⟨z, hz⟩, -⟩ := he α
    exact ⟨i, z - m i, by rw [hz, smul_sub, add_assoc, add_sub_cancel]⟩
  · exact (he (e i + q • m i)).unique ⟨m i' + z, by rw [smul_add, ← add_assoc]; exact h⟩ ⟨m i, rfl⟩
  · have := hm i (m i + z)
    rwa [smul_add, ← add_assoc] at this

variable {F : Type} [Field F] [Algebra (FractionRing V) F] {k : ℕ}

theorem sum_f {n : ℕ} (S : Finset (Fin n)) (t : Fin n → Fam D.toPre F k) (α : D.toPre.X) (j) :
    ((∑ i ∈ S, t i).s α).f j = ∑ i ∈ S, ((t i).s α).f j := by
  classical
  induction S using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, zero_f]
  | insert a S ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, add_f, ih]

theorem sval_comb {n : ℕ} (c : Fin n → F) (t : Fin n → Fam D.toPre F k) (α : D.toPre.X) {Z : Scheme.{0}}
    (r : Z ⟶ (DegPre.BF D.toPre F).left) (z : Z) {J} (hJ : Good D.toPre.P.L z J) :
    sval ((∑ i, c i • t i).s α) r z J =
      ∑ i, gs r z ⊤ (scal (fst (TF (R := V) F) D.toPre.P.A).left (c i)) * sval ((t i).s α) r z J :=
  SectionScalarValuation.sval_lin (fun i => gF D.toPre F (c i)) (fun i => (t i).s α) (fun j => sum_f _ _ α j) r z hJ

end IntComb

theorem exists_integral_expansions_of_vge : Laws → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ → ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G] (U : Unif (maximalIdeal V) D A G) (Q : D.toPre.X → ℤ), QForm.IsQ D.toPre ϖ Q → ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v → ∀ (q : ℕ), 1 ≤ q → ∀ (s : Fam D.toPre F q) (r : ℚ), (∀ χ, VGe D F v q χ (s.s χ) r) → ∃ (l : ℕ) (c : Fin l → F) (σ : Fin l → H0 U.LG.L q) (f : Fin l → ∀ α, D.toPre.SecB q α), (∀ i, ((r : ℚ) : WithTop ℚ) ≤ v (c i)) ∧ (∀ i e, U.ExpandsAt e q (σ i) (f i)) ∧ ∀ α : D.toPre.X, GeneratorPullback.SecLin D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε q) (s.s α) (D.toPre.famφB α) (DegPre.famε q) (fun i => f i α) (DegPre.prB D.toPre F).left (fun i => scal (fst (TF (R := V) F) D.toPre.P.A).left (c i)) := by
  intro hL V _ _ _ ϖ hϖ D A G _ _ U Q hQ F _ _ v _ q hq s r hs
  classical
  obtain ⟨N, χ, hrep, hdis, hmin⟩ := IntComb.exists_min_reps hϖ hQ hq
  choose n a β βF hβ hva hsum using fun i => hs (χ i)
  choose Φ f hf hfβ hf0 using fun p : (Σ i : Fin N, Fin (n i)) =>
    IntComb.integralFamily_of_min hL hϖ hQ hq (χ p.1) (β p.1 p.2) (hmin p.1)
  choose σ hσ using fun p => IntegralExpansion.main hL V D A G U q hq (Φ p) (f p) (hf p)
  choose θ hθ using fun p => GlobalTheory.T.integralDegenerationFamily_baseChange_extensionField hL.globalFns V _ D q (Φ p) (f p) (hf p) F
  let E := (Fintype.equivFin (Σ i : Fin N, Fin (n i))).symm
  have hst : s = ∑ x, a (E x).1 (E x).2 • θ (E x) := by
    refine fam_ext fun α => ?_
    obtain ⟨i, m, rfl⟩ := hrep α
    refine fam_eq_on_class_of_eq hL.globalFns V D.toPre F q _ _ (χ i) ?_ m
    refine sec_ext_val D.toPre.P.isLB fun y J hJ => ?_
    rw [IntComb.sval_comb _ _ _ _ _ hJ,
      SectionScalarValuation.sval_lin (fun x => gF D.toPre F (a i x)) (βF i) (fun j => hsum i j) (𝟙 _) y hJ,
      E.sum_comp (fun p => gs (𝟙 _) y ⊤ (scal (fst (TF (R := V) F) D.toPre.P.A).left (a p.1 p.2)) *
        sval ((θ p).s (χ i)) (𝟙 _) y J), Fintype.sum_sigma, Finset.sum_eq_single i]
    · refine Finset.sum_congr rfl fun x _ => congrArg₂ (· * ·) rfl ?_
      rw [← SectionScalarValuation.secScal_sval (hβ i x) _ y hJ, ← SectionScalarValuation.secScal_sval (hθ ⟨i, x⟩ (χ i)) _ y hJ, hfβ ⟨i, x⟩]
    · refine fun i' _ hi => Finset.sum_eq_zero fun x _ => ?_
      rw [← SectionScalarValuation.secScal_sval (hθ ⟨i', x⟩ (χ i)) _ y hJ,
        UUA.sval_zero_of (hf0 ⟨i', x⟩ (χ i) (hdis i i' hi)) _ y J (hJ.mem _ _), mul_zero]
    · exact fun h => absurd (Finset.mem_univ i) h
  refine ⟨_, fun x => a (E x).1 (E x).2, fun x => σ (E x), fun x => f (E x), fun x => hva _ _,
    fun x e => hσ _ e, fun α => ?_⟩
  refine (FieldBaseChange.secLin_iff_val D.toPre.P.isLB _ _ _ _).2 fun y J hJ => ?_
  rw [hst, IntComb.sval_comb _ _ _ _ _ hJ]
  exact Finset.sum_congr rfl fun x _ => by rw [SectionScalarValuation.secScal_sval (hθ _ α) _ _ hJ]

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsIntegralExpansionsOfValuationGeStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integralExpansions_of_valuation_ge : Laws → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ → ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G] (U : Unif (maximalIdeal V) D A G) (Q : D.toPre.X → ℤ), QForm.IsQ D.toPre ϖ Q → ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v → ∀ (q : ℕ), 1 ≤ q → ∀ (s : Fam D.toPre F q) (r : ℚ), (∀ χ, VGe D F v q χ (s.s χ) r) → ∃ (l : ℕ) (c : Fin l → F) (σ : Fin l → H0 U.LG.L q) (f : Fin l → ∀ α, D.toPre.SecB q α), (∀ i, ((r : ℚ) : WithTop ℚ) ≤ v (c i)) ∧ (∀ i e, U.ExpandsAt e q (σ i) (f i)) ∧ ∀ α : D.toPre.X, GeneratorPullback.SecLin D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε q) (s.s α) (D.toPre.famφB α) (DegPre.famε q) (fun i => f i α) (DegPre.prB D.toPre F).left (fun i => scal (fst (TF (R := V) F) D.toPre.P.A).left (c i)) := by
  first | exact @GlobalTheory.exists_integral_expansions_of_vge | exact GlobalTheory.exists_integral_expansions_of_vge | (intros; apply GlobalTheory.exists_integral_expansions_of_vge <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsUniqueFrameSer
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS FB ev)
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.PtGermCompare

theorem surjective_cube {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
    [IsCommMonObj G] (U : UnifPre I D A G) : Function.Surjective (G ⊗ G ⊗ G).hom.appTop.hom := by
  have hG := GlobalTheory.globalFns_holds
  have := U.smooth
  have : IsDominant (jK R) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
    (((RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R (FractionRing R))).le.trans bot_le)⟩
  have := IsSchemeTheoreticallyDominant.of_isDominant (jK R)
  have hg : IsPullback (U.gen.inv.left ≫ pullback.fst G.hom (jK R)) A.A.hom G.hom (jK R) := by
    have : IsIso U.gen.inv.left := inferInstanceAs (IsIso ((Over.forget _).map U.gen.inv))
    have s : IsPullback U.gen.inv.left A.A.hom (pullback.snd G.hom (jK R)) (𝟙 _) :=
      IsPullback.of_horiz_isIso ⟨(Over.w U.gen.inv).trans (Category.comp_id _).symm⟩
    simpa using s.paste_horiz (IsPullback.of_hasPullback G.hom (jK R))
  have s₁ : Function.Surjective G.hom.appTop.hom :=
    RigidIsoCube.surjective_appTop_of_baseChange hg (eSec G) (Over.w η[G]) (hG _ _ A.isAb).2
  have : Flat (G ⊗ G).hom := by rw [Over.tensorObj_hom]; infer_instance
  have s₂ := surj_comp (RigidIsoCube.surjective_snd_of_generic hG (jK R) G A.isAb hg G) s₁
  rw [Over.w (snd G G)] at s₂
  have s₃ := surj_comp (RigidIsoCube.surjective_snd_of_generic hG (jK R) G A.isAb hg (G ⊗ G)) s₂
  rw [Over.w (snd G (G ⊗ G))] at s₃
  exact s₃

theorem cubical_unique {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G]
    (sj : Function.Surjective (G ⊗ G ⊗ G).hom.appTop.hom) {L : RigLB G} (c c' : CubicalStr G L) : c = c' := by
  let e : 𝟙_ (Over S) ⟶ G3 G := lift 1 (lift 1 1)
  have h : c.t.s = c'.t.s := JetSer.gen_ext_val L.isLB (φ := thφ G (x3 G)) (ε := thε) c.isGen c'.isGen fun y J hJ =>
    gen_unique L.isLB (φ := thφ G (x3 G)) (ε := thε) (G3 G).hom e.left (Over.w e) sj c.isGen c'.isGen
      (fun y J hJ => ((isCub_cubV c hJ).face 1 1).trans ((isCub_cubV c' hJ).face 1 1).symm) _ _ y J hJ
  obtain ⟨⟨t⟩, _⟩ := c
  obtain ⟨⟨t'⟩, _⟩ := c'
  obtain rfl : t = t' := h
  rfl

section Scale
variable {R : Type} [CommRing R] {G : Over (Spec (CommRingCat.of R))}

end Scale

section Bound
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
  {D : DegData V (maximalIdeal V)} {F : Type} [Field F] [Algebra (FractionRing V) F] {v : AddValuation F (WithTop ℚ)}

end Bound

section Cast
variable {R : Type} [CommRing R] {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] {L L' : RigLB G}

end Cast

open GlobalTheory.FamGerm

section Data
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {V : Type} [CommRing V] [IsDomain V]
  [IsDiscreteValuationRing V] {F : Type} [Field F] [Algebra (FractionRing V) F]

variable [CharZero F]

end Data

section Statements

end Statements

end GlobalTheory.PtGermCompare
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.GermExistsUniqueLinear
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS FB ev Dof pt)
open GlobalTheory GlobalTheory.FamGerm GlobalTheory.FieldBaseChange
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FamGermExist

theorem exists_linear_extension {R K F : Type} [CommRing R] [IsDomain R] [Field K] [Field F] [Algebra R K]
    [IsFractionRing R K] [Algebra K F] {M N P : Type} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module K N]
    [AddCommGroup P] [Module F P] (ρ : M →ₛₗ[algebraMap R K] N) (hρ : Function.Injective ρ)
    (a : N →ₛₗ[algebraMap K F] P) (ha : IsExtension a) {κ : Type} (g : M →ₗ[R] MvPowerSeries κ R) :
    ∃ Λ : P →ₗ[F] MvPowerSeries κ F, ∀ x, Λ (a (ρ x)) =
      MvPowerSeries.map ((algebraMap K F).comp (algebraMap R K)) (g x) := by
  classical
  let T₁ := Finsupp.linearCombination F fun x : M => a (ρ x)
  let T₂ := Finsupp.linearCombination F fun x : M =>
    MvPowerSeries.map ((algebraMap K F).comp (algebraMap R K)) (g x)
  have hk : LinearMap.ker T₁ ≤ LinearMap.ker T₂ := fun c hc => by
    rw [LinearMap.mem_ker, Finsupp.linearCombination_apply, Finsupp.sum] at hc ⊢
    ext mo
    refine (Module.forall_dual_apply_eq_zero_iff K _).1 fun ℓ => ?_
    obtain ⟨Λ, hΛ⟩ := ha.coord ℓ
    obtain ⟨r, hr⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors R) c.support (fun x => ℓ (c x))
    choose! m hm using hr
    have h₁ : ∑ x ∈ c.support, m x • x = 0 := hρ (by
      have := congrArg (fun z => (algebraMap R K r) • Λ z) hc
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_zero, smul_zero, Finset.smul_sum] at this
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_zero, ← this, map_sum]
      refine Finset.sum_congr rfl fun x hx => ?_
      rw [hΛ, map_smulₛₗ, hm x hx, smul_smul, Algebra.smul_def])
    have h₂ := congrArg (fun z => algebraMap R K (MvPowerSeries.coeff mo (g z))) h₁
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, map_zero, smul_eq_mul, map_mul] at h₂
    have hr0 : algebraMap R K r ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective R K)).2 (nonZeroDivisors.coe_ne_zero r)
    refine mul_left_cancel₀ hr0 ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [mul_zero, ← h₂, map_sum, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [hm x hx, map_smul, MvPowerSeries.coeff_map, smul_eq_mul, RingHom.comp_apply, mul_comm (c x),
      ← Algebra.smul_def (A := F), map_smul, Algebra.smul_def (r : R) (ℓ (c x)), smul_eq_mul]
    ring
  obtain ⟨Λ, hΛ⟩ := LinearMap.exists_extend
    ((LinearMap.ker T₁).liftQ T₂ hk ∘ₗ T₁.quotKerEquivRange.symm.toLinearMap)
  refine ⟨Λ, fun x => ?_⟩
  have e := LinearMap.congr_fun hΛ ⟨T₁ (Finsupp.single x 1), LinearMap.mem_range_self _ _⟩
  simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearEquiv.coe_coe,
    LinearMap.quotKerEquivRange_symm_apply_image, Submodule.mkQ_apply, Submodule.liftQ_apply] at e
  simpa only [T₁, T₂, Finsupp.linearCombination_single, one_smul] using e

theorem exists_serHom (halg : JetSer.JetAlgSt) (hrep : JetSer.RepSt) (hser : JetSer.SerSt) (hex : JetSer.SerExSt)
    {R : Type} [CommRing R] {G : Over (Spec (CommRingCat.of R))} [GrpObj G] {d : ℕ} {x : JetSer.Fam G (Fin d)}
    (hx : Chart.IsUnivChart G d x) {U : G.left.Opens} (hU : ⊤ ≤ η[G].left ⁻¹ᵁ U) :
    ∃ τ : FnOver G.hom U →ₐ[R] PS R 1 d, ∀ f g, JetSer.IsSer1 x U f g ↔ g = τ f := by
  obtain ⟨h1, -, h3, -⟩ := hrep R G d x hx (Fin 1 × Fin d)
  obtain ⟨y, hy, -⟩ := h1 (pt R (n := 1) d 0) (TB.WickVanishing.gp_pt 0)
  have hc := (h3 _ y hy).1
  have e : ∀ r : PS R 1 d, ev (n := 1) ![pt R (n := 1) d 0] r = r := fun r => by
    have : (![pt R d 0] : Fin 1 → Germ.Pt R 1 d) = fun j => pt R d j := by
      funext j; fin_cases j; rfl
    rw [this]
    unfold ev
    exact congrFun MvPowerSeries.subst_self r
  have hs : ∀ f g, JetSer.IsSer1 x U f g → JetSer.HasSer (fun m => (y m).left) U f g := fun f g h => by
    have := h 1 _ y hy
    rwa [e] at this
  have ex := (hex R G d x hx).1 U hU
  have hm : ∀ m, ⊤ ≤ (y m).left ⁻¹ᵁ U := fun m => (hs _ _ (ex 0).exists.choose_spec m).1
  obtain ⟨⟨τ, hτ⟩, -⟩ := hser R (Fin 1 × Fin d) G.left (fun m => (y m).left)
    (fun m => by rw [← Over.comp_left, hc m]) U (hm 0)
  refine ⟨⟨τ, fun c => Eq.symm ((hτ _ _).1 fun m => ⟨hm m, ?_⟩)⟩, fun f g => ⟨fun h => (hτ f g).1 (hs f g h), ?_⟩⟩
  · obtain ⟨t, ht, -⟩ := (halg R (Fin 1 × Fin d)).1 m
    rw [← ht, AlgHom.commutes]
    have h₁ := (JetSer.fnVal_comp (y m).left G.hom U ⊤ le_top (hm m)
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c)).2
    refine Eq.trans (Eq.symm h₁) ?_
    rw [Over.w (y m)]
    have h₂ := JetSer.fnVal_specMap (algebraMap R (Chart.JetR R (Fin 1 × Fin d) m)) (𝟙 _) ⊤ le_top
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c)
    rw [Category.comp_id] at h₂
    refine h₂.trans (congrArg _ ?_)
    rw [JetSer.fnVal_eq_fnValHom _ _ le_top]
    simp [JetSer.fnValHom, Scheme.Hom.appLE]
  · rintro rfl
    obtain ⟨g, hg⟩ := (ex f).exists
    exact (hτ f g).1 (hs f g hg) ▸ hg

section Group

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)

theorem genericSec_injective (k : ℕ) : Function.Injective (genericSec U k) := by
  have := U.smooth
  intro a b h
  refine SecOver.ext _ _ fun j => ExpInt.generic_app_injective G _ (fn_ext fun y hy => ?_)
  have hy' := (wchart_eq (L := U.LG.L) (φ := fun _ : Fin 1 => 𝟙 G.left) (p := pullback.fst G.hom (jK R))
    (φ' := fun _ => pullback.fst G.hom (jK R)) (fun _ => (Category.comp_id _).symm) j).ge hy
  have e := congrArg (fun s : LB.Sec (LB.LinComb U.LG.L (K := Fin 1) (fun _ => pullback.fst G.hom (jK R))
    (fun _ => (k : ℤ))) => gs (𝟙 _) y _ (s.f j)) h
  exact (gs_res (𝟙 _) y _ hy' _).symm.trans (e.trans (gs_res (𝟙 _) y _ hy' _))

variable (F : Type) [Field F] [Algebra (FractionRing R) F]

theorem expandsG_sum {k n : ℕ} (c : Fin n → F) (σ : Fin n → IntSec U k) (f : Fin n → ∀ α, D.toPre.SecB k α)
    {s : Fam D.toPre F k} (h₁ : ∀ i e, U.ExpandsAt e k (σ i) (f i))
    (h₂ : ∀ α : D.toPre.X, GeneratorPullback.SecLin D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k) (s.s α)
      (D.toPre.famφB α) (DegPre.famε k) (fun i => f i α) (DegPre.prB D.toPre F).left
      (fun i => scal (fst (TF (R := R) F) D.toPre.P.A).left (c i))) :
    U.ExpandsG F k (∑ i, c i • extendSec U F k (genericSec U k (σ i)) : GroupSec U F k) s :=
  ⟨n, c, σ, f, h₁, (secLin_iff U.LG.isLB _ σ
    (UnifPre.gFK (G := G) F) c (fun i => extendSec U F k (genericSec U k (σ i))) (fun i y J hJ =>
      (sval_pullOver _ _ _ _ hJ).trans ((sval_pullOver _ _ _ _ hJ).trans
        (congrArg (fun q => sval (σ i) q y J) (Category.assoc _ _ _))))).2 rfl, h₂⟩

theorem exists_linear_section (hG : GlobalFnsSt) {k : ℕ} (hk : 1 ≤ k) (h : U.ExpBij k) :
    ∃ e : Fam D.toPre F k →ₗ[F] GroupSec U F k, ∀ v s, U.ExpandsG F k v s ↔ v = e s := by
  obtain ⟨-, h₂⟩ := expandsG_bijective U F hG hk h
  choose f hf using fun s => (h₂ s).exists
  have iff : ∀ v s, U.ExpandsG F k v s ↔ v = f s := fun v s =>
    ⟨fun h => (h₂ s).unique h (hf s), fun h => h ▸ hf s⟩
  have lin : ∀ (c : F) s s', f (c • s + s') = c • f s + f s' := fun c s s' =>
    ((iff _ _).1 (expandsG_lin U F k c (hf s) (hf s'))).symm
  have f0 : f 0 = 0 := by
    have := lin 1 0 0
    rw [one_smul, one_smul, add_zero] at this
    exact left_eq_add.1 this
  exact ⟨{ toFun := f
           map_add' := fun t t' => by simpa only [one_smul] using lin 1 t t'
           map_smul' := fun c t => by simpa only [add_zero, f0, RingHom.id_apply] using lin c t 0 }, iff⟩

theorem exists_linear_series {k : ℕ} {κ : Type} (g : IntSec U k →ₗ[R] MvPowerSeries κ R) :
    ∃ Λ : GroupSec U F k →ₗ[F] MvPowerSeries κ F, ∀ (n : ℕ) (c : Fin n → F) (σ : Fin n → IntSec U k),
      Λ (∑ i, c i • extendSec U F k (genericSec U k (σ i))) = ∑ i, MvPowerSeries.C (c i) *
        MvPowerSeries.map ((algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R))) (g (σ i)) := by
  have : TopologicalSpace.NoetherianSpace ((Over.pullback (jK R)).obj G).left := noetherianSpace_generic U
  obtain ⟨Λ, hΛ⟩ := exists_linear_extension (genericSec U k) (genericSec_injective U k)
    (extendSec U F k) (isExtension_pullOver (isPullback_groupBase F) U.LG.isLB _ _) g
  refine ⟨Λ, fun n c σ => ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [map_smul, hΛ, MvPowerSeries.smul_eq_C_mul]

theorem exists_linear_germ (hG : GlobalFnsSt) {k : ℕ} (hk : 1 ≤ k) (h : U.ExpBij k) {κ : Type}
    (g : IntSec U k →ₗ[R] MvPowerSeries κ R) : ∃ gm : Fam D.toPre F k →ₗ[F] MvPowerSeries κ F,
    ∀ s f, (∃ (n : ℕ) (c : Fin n → F) (σ : Fin n → IntSec U k) (fi : Fin n → ∀ α, D.toPre.SecB k α),
      (∀ i e, U.ExpandsAt e k (σ i) (fi i)) ∧
      (∀ α : D.toPre.X, GeneratorPullback.SecLin D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k) (s.s α)
        (D.toPre.famφB α) (DegPre.famε k) (fun i => fi i α) (DegPre.prB D.toPre F).left
        (fun i => scal (fst (TF (R := R) F) D.toPre.P.A).left (c i))) ∧
      f = ∑ i, MvPowerSeries.C (c i) *
        MvPowerSeries.map ((algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R))) (g (σ i))) ↔
      f = gm s := by
  obtain ⟨e, he⟩ := exists_linear_section U F hG hk h
  obtain ⟨Λ, hΛ⟩ := exists_linear_series U F g
  refine ⟨Λ ∘ₗ e, fun s f => ⟨?_, ?_⟩⟩
  · rintro ⟨n, c, σ, fi, h₁, h₂, rfl⟩
    rw [LinearMap.comp_apply, ← (he _ s).1 (expandsG_sum U F c σ fi h₁ h₂), hΛ]
  · rintro rfl
    obtain ⟨n, c, σ, fi, h₁, -, h₂⟩ := (he _ s).2 rfl
    exact ⟨n, c, σ, fi, h₁, h₂,
      (congrArg Λ ((he _ s).1 (expandsG_sum U F c σ fi h₁ h₂)).symm).trans (hΛ n c σ)⟩

theorem exists_linear_quotient (halg : JetSer.JetAlgSt) (hrep : JetSer.RepSt) (hser : JetSer.SerSt)
    (hex : JetSer.SerExSt) {d : ℕ} {x : JetSer.Fam G (Fin d)} (hx : Chart.IsUnivChart G d x) {j : U.LG.L.ι}
    (hj : ⊤ ≤ η[G].left ⁻¹ᵁ U.LG.L.U j) (k : ℕ) {r : PS R 1 d} (hr : IsUnit r) :
    ∃ g : IntSec U k →ₗ[R] PS R 1 d, ∀ (σ : IntSec U k) f,
      (∃ S, JetSer.IsSer1 x _ (LB.Sec.f σ (fun _ => j)) S ∧ f * r = S) ↔ f = g σ := by
  obtain ⟨τ, hτ⟩ := exists_serHom halg hrep hser hex hx
    (U := LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => j))
    (GermExist.top_le_preimage_wchart _ _ j _ (fun _ => by rw [Category.comp_id]; exact hj))
  obtain ⟨u, rfl⟩ := hr
  refine ⟨LinearMap.mulRight R (u⁻¹).val ∘ₗ τ.toLinearMap ∘ₗ chartLin G.hom
    (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (k : ℤ))) (fun _ => j), fun σ f => ⟨?_, ?_⟩⟩
  · rintro ⟨S, hS, e⟩
    exact (Units.eq_mul_inv_iff_mul_eq u).2 (e.trans ((hτ _ _).1 hS))
  · intro e
    exact ⟨_, (hτ _ _).2 rfl, (Units.eq_mul_inv_iff_mul_eq u).1 e⟩

end Group

theorem germ_exists_unique_linear : Laws → Laws4 → TwistBCSpanStatement → JetSer.JetAlgSt → JetSer.RepSt →
    JetSer.SerSt → JetSer.SerExSt → FamGerm.GermExSt := by
  intro hL _ _ halg hrep hser hex E _ _ _ H V _ _ _ F _ _ _ _ _ _ y q hq
  let _ := H.starRing
  have := y.t.act.hom H.w0
  obtain ⟨r, hr, ur⟩ := (hex V y.t.G y.d y.x y.hx).1
    (LB.wchart y.P.U.LG.L (JetSer.primφ (y.t.act.act H.w0)) (fun _ => y.j))
    (GermExist.top_le_preimage_wchart _ _ y.j _ (fun k => by
      rw [GermExist.unit_comp_primφ _ (IsMonHom.one_hom _) k]; exact y.hj)) (y.ρ.s (fun _ => y.j)).val
  obtain ⟨g, hg⟩ := exists_linear_quotient y.P.U.toUnifPre halg hrep hser hex y.hx y.hj q
    ((GermExist.isUnit_of_isSer1 hrep hser y.hx (Units.isUnit _) hr).pow q)
  obtain ⟨gm, h⟩ := exists_linear_germ y.P.U.toUnifPre F hL.globalFns hq (y.P.U.expand q hq) g
  refine ⟨gm, fun s f => Iff.trans ⟨?_, ?_⟩ (h s f)⟩
  · rintro ⟨n, c, σ, fi, g', r', h₁, h₂, hr', h₃, e⟩
    obtain rfl := ur r' hr'
    obtain rfl : g' = fun i => g (σ i) := funext fun i => (hg _ _).1 (h₃ i)
    exact ⟨n, c, σ, fi, h₁, h₂, e⟩
  · rintro ⟨n, c, σ, fi, h₁, h₂, e⟩
    exact ⟨n, c, σ, fi, fun i => g (σ i), r, h₁, h₂, hr, fun i => (hg _ _).2 rfl, e⟩

end GlobalTheory.FamGermExist
end
end
