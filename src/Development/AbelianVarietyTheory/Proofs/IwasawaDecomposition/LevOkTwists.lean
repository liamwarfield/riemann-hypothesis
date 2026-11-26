module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ReferenceCharactersFactorTame
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeightEqOfFinitePartNeBot
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallySubsingletonCohAmplePsEff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsWeilOfFixes
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinitePartAtOwnWeightNeBot
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevOkTwists
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 ReciprocityTheory.Neutral.Bridge.HCFR Neutral.B1
open GlobalTheory.Mem.Chr hiding HChar atFin
open Formalism.L2.Host (HChar atFin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.LevTwist

theorem conjP_ne {R : Ranks} (H : Formalism.BasicNotions.Host R) {P : HeightOneSpectrum (𝓞 H.E)} (h : IsSplitPl H P) : conjPrime₂ P ≠ P := by
  intro e
  obtain ⟨x, hx, hy⟩ := h
  have hc : IsConjPl H P P := (isConjPl_iff H P P).2 e.symm
  have e1 : ((cO H.E x : 𝓞 H.E) : H.E) = H.conj (x : H.E) := bridge_star_holds R H x
  exact hy _ e1 ((hc x _ e1).1 hx)

variable {B : Base} {X : PreX B.toPre} {I : ColIn B X}

theorem under_sel (h : I.Ok) (v : HeightOneSpectrum (𝓞 B.host.F)) : (I.sel v).under (𝓞 B.host.F) = v :=
  HeightOneSpectrum.ext (h.sel_ok v)

theorem good_of_mem (h : I.Ok) {P : HeightOneSpectrum (𝓞 B.host.E)} (hP : P ∈ I.SQ) :
    I.sel (P.under (𝓞 B.host.F)) = P ∧ GoodPl B.host.E I.S (P.under (𝓞 B.host.F)) := by
  obtain ⟨a, ha⟩ := I.mem_SQ.1 hP
  obtain ⟨v, -, rfl, hg⟩ := I.exists_of_mem_Q ha
  rw [under_sel h]
  exact ⟨rfl, hg⟩

theorem plc_mem (h : I.Ok) {P : HeightOneSpectrum (𝓞 B.host.E)} (hP : P ∈ (B.primes X).vGs) :
    Formalism.EigenvalueLevelCeiling.plc (P.under (𝓞 B.host.F)) ∈ I.S := by
  classical
  have hPr := (GlobalTheory.BasePrimes.primes_ok B X).1
  have h0 : ∀ i, B.fields.conjO ((B.primes X).piG i) ≠ 0 := fun i h => by
    have := hPr.piG_norm i
    rw [h, mul_zero] at this
    exact (hPr.g_prime i).ne_zero (Nat.cast_eq_zero.1 this.symm)
  have hm : ∃ i, B.fields.conjO ((B.primes X).piG i) ∈ P.asIdeal := by
    unfold Primes.vGs Primes.vG at hP
    simpa only [Finset.mem_union, mem_divs (h0 _), Fin.exists_fin_two] using hP
  obtain ⟨i, hi⟩ := hm
  have h1 : ((B.primes X).g i : 𝓞 B.fields.E) ∈ P.asIdeal := by
    rw [← hPr.piG_norm i]; exact Ideal.mul_mem_left _ _ hi
  rw [(ReadTwist.plc_under_eq_iff (F := B.host.F) P (hPr.g_prime i)).2 h1]
  exact h.g_mem i

theorem levOk_twists : ∀ (B : Base) (X : PreX B.toPre) (I : ColIn B X), I.Ok → LevOk B.host (B.primes X).vGs I.SQ ∧ Disjoint (B.primes X).vGs I.SQ ∧ ∀ a, KDq B.host (I.Q a) ≤ ((I.xi a).1.comp (finPartI B.host.E)).ker ∧ (I.xi a).IsUnitary := by
  classical
  intro B X I h
  have hb := levOk_base B X
  have hu : ∀ P : HeightOneSpectrum (𝓞 B.host.E), (conjPrime₂ P).under (𝓞 B.host.F) = P.under (𝓞 B.host.F) := fun P =>
    (under_eq_iff B.host P _).2 (Or.inr rfl)
  refine ⟨⟨hb.cover, fun P hP hP' => ?_⟩, Finset.disjoint_left.2 fun P h1 h2 => (good_of_mem h h2).2.2.2 (plc_mem h h1),
    fun a => ?_⟩
  · simp only [Finset.mem_union] at hP hP'
    rcases hP with hP | hP <;> rcases hP' with hP' | hP'
    · exact hb.split P (by simpa using hP) (by simpa using hP')
    · refine (good_of_mem h hP').2.2.2 ?_
      rw [hu]
      exact plc_mem h hP
    · refine (good_of_mem h hP).2.2.2 ?_
      rw [← hu]
      exact plc_mem h hP'
    · have e := (good_of_mem h hP').1
      rw [hu, (good_of_mem h hP).1] at e
      exact conjP_ne B.host ((GoodPlace.goodPl_under_iff _ B.host _ P).1 (good_of_mem h hP).2).1 e.symm
  · obtain ⟨⟨⟨n, hn, ho⟩, hT, hta, -⟩, hq, -⟩ :=
      ReadTwist.isTwist_of_reads B.R B.host B.LL B.embLL I.S (I.tup a) (I.xi a) (h.xi_reads a)
    refine ⟨KDq_le_ker_of_tame _ hT hta fun w hw => by_contra fun hr => hw (Or.inr ?_), fun x => ?_⟩
    · have hfin : (Qprime (I.tup a : Chr B.fields.F B.fields.E B.fields.K)).Finite :=
        ((UnrAe.finite_ramified (I.xi a)).image (·.under (𝓞 B.host.F))).subset fun v hv => by
          obtain ⟨P, e, hP⟩ := (hq v).1 hv
          exact ⟨P, hP, e⟩
      have hmem : I.sel (w.under (𝓞 B.host.F)) ∈ I.Q a := by
        unfold ColIn.Q QE
        rw [dite_eq_left hfin]
        convert Finset.mem_image_of_mem I.sel (hfin.mem_toFinset.2 ((hq _).2 ⟨w, rfl, hr⟩))
      rcases (under_eq_iff B.host _ w).1 (under_sel h _).symm with e | e
      · exact Or.inl (e ▸ hmem)
      · exact Or.inr ⟨_, hmem, (isConjPl_iff B.host _ _).2 e⟩
    · have h1 : (I.xi a).1 x ^ n = 1 := congrArg (fun χ : HChar B.host.E => χ.1 x) ho
      have h2 : ‖(((I.xi a).1 x : ℂˣ) : ℂ)‖ ^ n = 1 := by
        rw [← norm_pow, ← Units.val_pow_eq_pow_val, h1, Units.val_one, norm_one]
      exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 h2

end GlobalTheory.Mem.LevTwist
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JGenSpecializes
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar

namespace GlobalTheory.TrueGeo.SmallSec

section Val

variable {K : Type} [Field K] {Z : Scheme.{0}} [IsIntegral Z] {y : Sp K ⟶ Z} {f g : Z.functionField}

theorem valAt_algebraMap (a : Z.presheaf.stalk (below y)) :
    valAt y (algebraMap _ Z.functionField a) = (Scheme.stalkClosedPointTo y).hom a := by
  have h : RegAt (below y) (algebraMap _ Z.functionField a) := ⟨a, rfl⟩
  rw [valAt, dif_pos h, IsFractionRing.injective _ Z.functionField h.choose_spec]

theorem valAt_mul (hf : RegAt (below y) f) (hg : RegAt (below y) g) :
    valAt y (f * g) = valAt y f * valAt y g := by
  obtain ⟨a, rfl⟩ := hf
  obtain ⟨b, rfl⟩ := hg
  rw [← map_mul, valAt_algebraMap, valAt_algebraMap, valAt_algebraMap, map_mul]

theorem regAt_pow {x : Z} (hf : RegAt x f) (n : ℕ) : RegAt x (f ^ n) := by
  obtain ⟨a, rfl⟩ := hf
  exact ⟨a ^ n, map_pow _ _ _⟩

theorem valAt_pow (hf : RegAt (below y) f) (n : ℕ) : valAt y (f ^ n) = valAt y f ^ n := by
  obtain ⟨a, rfl⟩ := hf
  rw [← map_pow, valAt_algebraMap, valAt_algebraMap, map_pow]

theorem valAt_ne_zero (hf : UnitAt (below y) f) : valAt y f ≠ 0 := by
  obtain ⟨a, ha, rfl⟩ := hf
  rw [valAt_algebraMap]
  exact (ha.map (Scheme.stalkClosedPointTo y).hom).ne_zero

theorem valAt_fnOf {U : Z.Opens} (hy : below y ∈ U) (h : genericPoint Z ∈ U) (a : Γ(Z, U)) :
    valAt y (fnOf U h a) = valR y U a := by
  have e : fnOf U h a = algebraMap _ Z.functionField (Z.presheaf.germ U (below y) hy a) :=
    (algebraMap_germ hy a).symm
  have ht : ⊤ ≤ y ⁻¹ᵁ U := (Scheme.preimage_eq_top_of_closedPoint_mem y hy).ge
  have H := congrArg (fun φ => φ.hom a) (Scheme.germ_stalkClosedPointTo y U hy)
  rw [e, valAt_algebraMap]
  first
  | rw [valR, dif_pos ht]
  | simp only [valR, dif_pos ht]
  | simp only [valR, ht, dite_true]
  refine H.trans ?_
  first
  | rfl
  | (simp only [Scheme.Hom.appLE, CommRingCat.hom_comp, RingHom.comp_apply, Iso.trans_hom,
      Functor.mapIso_hom, Iso.op_hom, eqToIso.hom]; done)
  | (simp only [Scheme.Hom.appLE, CommRingCat.hom_comp, RingHom.comp_apply, Iso.trans_hom,
      Functor.mapIso_hom, Iso.op_hom, eqToIso.hom]; rfl)
  | (simp [Scheme.Hom.appLE]; done)

theorem ratVal_eq_valAt {k : Type} [CommRing k] {q : Z ⟶ Sp k} {σ : k →+* ℂ} (y : CxPts q σ)
    (hf : RegAt (under y) f) : ratVal f y = valAt y.1 f := by
  rw [ratVal, dif_pos hf]
  have he := hf.exists_fnOf.choose_spec.choose_spec.choose_spec
  conv_rhs => rw [← he]
  exact (valAt_fnOf hf.exists_fnOf.choose_spec.choose _ _).symm

end Val

section Fn

variable {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (j : Y ⟶ X)
  (hη : j (genericPoint Y) ⤳ genericPoint X)

def fnMap : X.functionField →+* Y.functionField :=
  (X.presheaf.stalkSpecializes hη ≫ j.stalkMap (genericPoint Y)).hom

theorem fnMap_fnOf {U : X.Opens} (h : genericPoint X ∈ U) (h' : genericPoint Y ∈ j ⁻¹ᵁ U)
    (s : Γ(X, U)) : fnMap j hη (fnOf U h s) = fnOf (j ⁻¹ᵁ U) h' (j.app U s) := by
  show (X.presheaf.germ U _ h ≫ X.presheaf.stalkSpecializes hη ≫ j.stalkMap (genericPoint Y)).hom s =
    (j.app U ≫ Y.presheaf.germ (j ⁻¹ᵁ U) (genericPoint Y) h').hom s
  rw [TopCat.Presheaf.germ_stalkSpecializes_assoc, Scheme.Hom.germ_stalkMap]

private theorem fnMap_algebraMap_eq_algebraMap_stalkMap (y : Y) (b : X.presheaf.stalk (j y)) :
    fnMap j hη (algebraMap _ X.functionField b) = algebraMap _ Y.functionField (j.stalkMap y b) := by
  have e1 := Scheme.Hom.stalkSpecializes_stalkMap_apply j (genericPoint Y) y
    ((genericPoint_spec Y).specializes trivial) b
  simp only [RingHom.algebraMap_toAlgebra, fnMap]
  rw [← e1]
  simp only [CommRingCat.comp_apply, TopCat.Presheaf.stalkSpecializes_comp_apply]

theorem exists_fnMap_eq [IsPreimmersion j] {y : Y} {u : Y.functionField}
    (hu : RegAt y u) : ∃ t, RegAt (j y) t ∧ fnMap j hη t = u := by
  obtain ⟨a, rfl⟩ := hu
  obtain ⟨b, rfl⟩ := j.stalkMap_surjective y a
  exact ⟨algebraMap _ X.functionField b, ⟨b, rfl⟩, fnMap_algebraMap_eq_algebraMap_stalkMap j hη y b⟩

theorem fnMap_surjective [IsPreimmersion j] : Function.Surjective (fnMap j hη) := fun u =>
  let ⟨t, _, ht⟩ := exists_fnMap_eq j hη (regAt_genericPoint u)
  ⟨t, ht⟩

theorem regAt_fnMap_iff [IsPreimmersion j] {y : Y} {t : X.functionField} :
    RegAt y (fnMap j hη t) ↔ RegAt (j y) t := by
  constructor
  · intro h
    obtain ⟨t', ht', e⟩ := exists_fnMap_eq j hη h
    rwa [(fnMap j hη).injective e] at ht'
  · rintro ⟨b, rfl⟩
    exact ⟨_, (fnMap_algebraMap_eq_algebraMap_stalkMap j hη y b).symm⟩

theorem valAt_fnMap {K : Type} [Field K] (y : Sp K ⟶ Y) {t : X.functionField}
    (h : RegAt (j (below y)) t) : valAt y (fnMap j hη t) = valAt (y ≫ j) t := by
  obtain ⟨b, rfl⟩ := h
  rw [fnMap_algebraMap_eq_algebraMap_stalkMap, valAt_algebraMap]
  refine Eq.trans ?_ (valAt_algebraMap (y := y ≫ j) b).symm
  rw [Scheme.stalkClosedPointTo_comp]
  rfl

end Fn

section Model

variable {F : Type} [Field F] [NumberField F] {Y : Var F} (M : Model Y)

theorem isPreimmersion_j : IsPreimmersion M.j := by
  have : IsPreimmersion (spMap (algebraMap (𝓞 F) F)) :=
    IsPreimmersion.of_isLocalization (nonZeroDivisors (𝓞 F))
  exact MorphismProperty.of_isPullback (P := @IsPreimmersion) M.pb.flip this

private theorem asIdeal_spMap_algebraMap_eq_bot (s : Sp F) : (spMap (algebraMap (𝓞 F) F) s).asIdeal = ⊥ := by
  haveI := s.isPrime
  have hs : s.asIdeal = ⊥ := Ideal.eq_bot_of_prime _
  have e : (spMap (algebraMap (𝓞 F) F) s).asIdeal = Ideal.comap (algebraMap (𝓞 F) F) s.asIdeal := by
    first
    | rfl
    | simp [spMap]
    | simp [spMap, Spec.map_base]
  rw [e, hs]
  exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective (𝓞 F) F)

theorem mem_range_j {x : M.X} (hx : (M.p x).asIdeal = ⊥) : x ∈ Set.range M.j := by
  have e : M.p x = spMap (algebraMap (𝓞 F) F) (IsLocalRing.closedPoint F) :=
    PrimeSpectrum.ext (hx.trans (asIdeal_spMap_algebraMap_eq_bot _).symm)
  obtain ⟨z, hz1, -⟩ := Scheme.Pullback.exists_preimage_pullback x _ e
  refine ⟨M.pb.isoPullback.inv z, ?_⟩
  rw [← hz1, ← M.pb.isoPullback_inv_fst]
  first
  | rfl
  | exact (Scheme.comp_apply _ _ _).symm
  | simp

theorem asIdeal_p_j (y : Y.X) : (M.p (M.j y)).asIdeal = ⊥ := by
  have e : M.p (M.j y) = spMap (algebraMap (𝓞 F) F) (Y.str y) := by
    first
    | (show (M.j ≫ M.p) y = (Y.str ≫ spMap _) y
       rw [M.pb.w])
    | rw [← Scheme.comp_apply, M.pb.w, Scheme.comp_apply]
  rw [e, asIdeal_spMap_algebraMap_eq_bot]

theorem asIdeal_p_gen [IsIntegral M.X] : (M.p (genericPoint M.X)).asIdeal = ⊥ := by
  obtain ⟨y⟩ : Nonempty Y.X := inferInstance
  have hs : genericPoint M.X ⤳ M.j y := (genericPoint_spec M.X).specializes trivial
  have h3 : (M.p (genericPoint M.X)).asIdeal ≤ (M.p (M.j y)).asIdeal :=
    (PrimeSpectrum.le_iff_specializes _ _).2 (M.p.base.hom.map_specializes hs)
  rw [asIdeal_p_j] at h3
  exact le_bot_iff.1 h3

theorem j_gen_specializes [IsIntegral M.X] : M.j (genericPoint Y.X) ⤳ genericPoint M.X := by
  obtain ⟨y0, hy0⟩ := mem_range_j M (asIdeal_p_gen M)
  rw [← hy0]
  exact M.j.base.hom.map_specializes ((genericPoint_spec Y.X).specializes trivial)

end Model

end GlobalTheory.TrueGeo.SmallSec
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValAtAlgebraMap
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions

namespace GlobalTheory.TrueGeo.OfModel

section Values

variable {K : Type} [Field K] {Z : Scheme.{0}} [IsIntegral Z] (y : Sp K ⟶ Z)

theorem valAt_algebraMap (a : Z.presheaf.stalk (below y)) :
    valAt y (algebraMap _ Z.functionField a) = (Scheme.stalkClosedPointTo y).hom a := by
  have h : RegAt (below y) (algebraMap _ Z.functionField a) := ⟨a, rfl⟩
  rw [valAt, dif_pos h]
  exact congrArg _ (IsFractionRing.injective (Z.presheaf.stalk (below y)) Z.functionField h.choose_spec)

theorem valAt_mul {f g : Z.functionField} (hf : RegAt (below y) f) (hg : RegAt (below y) g) :
    valAt y (f * g) = valAt y f * valAt y g := by
  obtain ⟨a, rfl⟩ := hf
  obtain ⟨b, rfl⟩ := hg
  rw [← map_mul, valAt_algebraMap, valAt_algebraMap, valAt_algebraMap, map_mul]

theorem valAt_fnOf {U : Z.Opens} (hU : below y ∈ U) (h : ⊤ ≤ y ⁻¹ᵁ U) (a : Γ(Z, U)) :
    valAt y (fnOf U (gen_mem hU) a) =
      (y.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom).hom a := by
  have e : Z.presheaf.germ U _ hU ≫ Scheme.stalkClosedPointTo (R := CommRingCat.of K) y =
      y.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom := by
    rw [Scheme.germ_stalkClosedPointTo]
    simp [Iso.trans_hom, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map_assoc]
  rw [← algebraMap_germ hU, valAt_algebraMap, ← e]
  rfl

end Values

theorem eval_pull {K O : Type} [CommRing K] [CommRing O] (φ : O →+* K) {X Z : Scheme.{0}} (j : Z ⟶ X)
    (y : Sp K ⟶ Z) (yt : Sp O ⟶ X) (e : spMap φ ≫ yt = y ≫ j) {U : X.Opens} {W : Z.Opens}
    (hW : W ≤ j ⁻¹ᵁ U) (h : ⊤ ≤ y ⁻¹ᵁ W) (ht : ⊤ ≤ yt ⁻¹ᵁ U) (a : Γ(X, U)) :
    (y.appLE W ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom).hom ((j.appLE U W hW).hom a) =
      φ ((yt.appLE U ⊤ ht ≫ (Scheme.ΓSpecIso (CommRingCat.of O)).hom).hom a) := by
  have e1 : j.appLE U W hW ≫ y.appLE W ⊤ h = yt.appLE U ⊤ ht ≫ (spMap φ).appTop := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
    refine Eq.trans ?_ (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
    simp only [e]
  have e2 := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ)
  have e3 : j.appLE U W hW ≫ y.appLE W ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom =
      (yt.appLE U ⊤ ht ≫ (Scheme.ΓSpecIso (CommRingCat.of O)).hom) ≫ CommRingCat.ofHom φ := by
    rw [← Category.assoc, e1, Category.assoc, e2, Category.assoc]
  exact congrArg (fun ψ => ψ.hom a) e3

variable {F : Type} [Field F] [NumberField F]

variable {Y : Var F} (M : TrueGeo.Model Y) (B : LB M.X)

end GlobalTheory.TrueGeo.OfModel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasLab
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.Mem.R3.HasLabelling

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3} {X0 : BaseLevelRowSide D}

def HasLab (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (σ : D.what₂.FT) (p : A3.fam3.base3.Ix) : Prop :=
  (∀ i : Fin D.R.m, (D.what₂.isot ((i : ℕ) + 1) σ).map (Y.mj.eW i) ≤ R.Wp3 i p) ∧
  ∀ k, D.what₂.ft0 k = σ → ∃ x ∈ R.EEp3 p,
    ((Y.Iz.jE (D.what₂.onb0 k)).1 : (toChainReal R.toRealDat F.lv2 Y.tupT Y.hm Y.hTop).Amb 0) = PiTensorProduct.lift (R.HE.e x)

end GlobalTheory.Mem.R3.HasLabelling
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TensOfForallIsPsEff
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory

theorem IsAmpleLB.tens_of_forall_isPsEff : ∀ (k : Type) [Field k] (X : Scheme.{0}) (f : X ⟶ Sp k), IsProjOver f → ∀ A N : LB X, IsAmpleLB A → N.IsLB → (∀ Z : Closeds X, IsIrreducible (Z : Set X) → IsPsEff (N.pull (redι Z))) → IsAmpleLB (tens A N) := by
  intro k _ X f hf A N hA hN hpe
  haveI : AlgebraicGeometry.IsNoetherian X := isNoetherian_of_isProjOver hf
  have hT : (tens A N).IsLB := isLB_tens hA.isLB hN
  refine isAmpleLB_of_subsingleton_coh_one X (tens A N) hT fun F hF => ?_
  obtain ⟨j₀, hj⟩ := eventually_subsingleton_coh_ample_psEff k X f hf A N hA hN hpe F hF
  refine ⟨max j₀ 1, le_max_right _ _, ?_⟩
  have h1 := hj (max j₀ 1) (max j₀ 1) (le_max_left _ _) le_rfl 1 one_pos
  have hpow (L : LB X) (hL : L.IsLB) (n : ℕ) (h : (lbPow L n).IsLB) :
      cls _ h = n • cls L hL := by
    rw [cls_linComb hL, Fintype.sum_unique, pull_id, natCast_zsmul]
  obtain ⟨i⟩ := nonempty_twist_iso_of_cls_eq F
    (isLB_tens (isLB_lbPow hA.isLB (max j₀ 1)) (isLB_lbPow hN (max j₀ 1)))
    (isLB_lbPow hT (max j₀ 1)) (by
      rw [cls_tens (isLB_lbPow hA.isLB _) (isLB_lbPow hN _), hpow A hA.isLB, hpow N hN,
        hpow (tens A N) hT, cls_tens hA.isLB hN, smul_add])
  exact (cohOn.mapIso Γ(X, ⊤) ⊤ 1 i).symm.injective.subsingleton

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopologicalKrullDimEqSucc
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CechPic
open scoped TensorProduct

namespace GlobalTheory.IntModel

theorem ringKrullDim_adjoin_le {R S : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R] [CommRing S] [IsDomain S]
    [Algebra R S] [FaithfulSMul R S] [Algebra.IsAlgebraic R S] (s : Finset S) :
    ringKrullDim (Algebra.adjoin R (s : Set S)) ≤ ringKrullDim R := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.coe_empty, Algebra.adjoin_empty]
    exact (ringKrullDim_eq_of_ringEquiv (Algebra.botEquivOfInjective
      (FaithfulSMul.algebraMap_injective R S)).toRingEquiv).le
  | insert a s _ ih =>
    refine le_trans ?_ ih
    set T := Algebra.adjoin R (s : Set S)
    set T' := Algebra.adjoin R ((insert a s : Finset S) : Set S)
    have hle : T ≤ T' := Algebra.adjoin_mono (by simp)
    have ha : a ∈ T' := Algebra.subset_adjoin (by simp)
    have : Algebra.FiniteType R T := (Subalgebra.fg_iff_finiteType _).1 (Subalgebra.fg_adjoin_finset s)
    have : IsNoetherianRing T := Algebra.FiniteType.isNoetherianRing R T
    let f : T →+* T' := (Subalgebra.inclusion hle).toRingHom
    have hf : Function.Injective f := Subalgebra.inclusion_injective hle
    have hgen : Function.Surjective (Polynomial.eval₂RingHom f ⟨a, ha⟩) := by
      rintro ⟨y, hy⟩
      induction hy using Algebra.adjoin_induction with
      | mem x hx =>
        rcases Finset.mem_insert.1 (Finset.mem_coe.1 hx) with rfl | hx
        · exact ⟨Polynomial.X, by simp⟩
        · exact ⟨Polynomial.C ⟨x, Algebra.subset_adjoin hx⟩, by simp [f]⟩
      | algebraMap r => exact ⟨Polynomial.C (algebraMap R T r), by simp [f]; rfl⟩
      | add x y _ _ hx hy =>
        obtain ⟨p, hp⟩ := hx
        obtain ⟨q, hq⟩ := hy
        exact ⟨p + q, by rw [map_add (f := _), hp, hq]; rfl⟩
      | mul x y _ _ hx hy =>
        obtain ⟨p, hp⟩ := hx
        obtain ⟨q, hq⟩ := hy
        exact ⟨p * q, by rw [map_mul, hp, hq]; rfl⟩
    obtain ⟨g, hg0, hg⟩ := Algebra.IsAlgebraic.isAlgebraic (R := R) a
    have hinj : Function.Injective (algebraMap R T) := fun x y h =>
      FaithfulSMul.algebraMap_injective R S (congrArg Subtype.val h)
    have halg : ∃ g : Polynomial T, g ≠ 0 ∧ Polynomial.eval₂ f ⟨a, ha⟩ g = 0 := by
      refine ⟨g.map (algebraMap R T), (Polynomial.map_ne_zero_iff hinj).2 hg0, Subtype.ext ?_⟩
      rw [Polynomial.eval₂_map]
      refine (Polynomial.hom_eval₂ g _ T'.val.toRingHom _).trans ?_
      exact hg
    refine (ringKrullDim_le_iff_height_le _).2 fun q hq => ?_
    have h := ReciprocityTheory.CA.height_le_height_comap_of_eval₂_surjective f hf _ hgen halg q
    exact le_trans (by exact_mod_cast h) (Ideal.height_le_ringKrullDim_of_ne_top (Ideal.comap_isPrime f q).ne_top)

theorem ringKrullDim_le_add {O A : Type} (K : Type) [CommRing O] [IsDomain O] [IsNoetherianRing O] [CommRing A]
    [IsDomain A] [Algebra O A] [FaithfulSMul O A] [Algebra.FiniteType O A] [Field K] [Algebra O K] [IsFractionRing O K] :
    ringKrullDim A ≤ ringKrullDim O + ringKrullDim (K ⊗[O] A) := by
  obtain ⟨d, hd⟩ := exists_trdeg_eq_natCast O (A := A)
  rw [ringKrullDim_genericFibre_eq O K hd]
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis O A
  have hc : Cardinal.mk s = d := hs.cardinalMk_eq_trdeg.trans hd
  have : Finite s := Cardinal.lt_aleph0_iff_finite.1 (hc ▸ Cardinal.natCast_lt_aleph0)
  let R := Algebra.adjoin O (Set.range ((↑) : s → A))
  have e : MvPolynomial s O ≃+* R := hs.1.aevalEquiv.toRingEquiv
  have : IsNoetherianRing R := isNoetherianRing_of_ringEquiv _ e
  have : Algebra.IsAlgebraic R A := hs.isAlgebraic
  have : Algebra.FiniteType R A := .of_restrictScalars_finiteType O R A
  obtain ⟨t, ht⟩ := Algebra.FiniteType.out (R := R) (A := A)
  have h := ringKrullDim_adjoin_le (R := R) t
  rw [ht, ringKrullDim_eq_of_ringEquiv Subalgebra.topEquiv.toRingEquiv, ← ringKrullDim_eq_of_ringEquiv e,
    MvPolynomial.ringKrullDim_of_isNoetherianRing, ENat.card_eq_coe_natCard, ← Cardinal.toNat_mk, hc, Cardinal.toNat_natCast] at h
  exact h

theorem topologicalKrullDim_eq_succ {O K : Type} [CommRing O] [IsDedekindDomain O] (hO : ¬ IsField O) [Field K]
    [Algebra O K] [IsFractionRing O K] {X Y : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp O} [IsProper p] [Flat p]
    {j : Y ⟶ X} {q : Y ⟶ Sp K} (H : IsPullback j q p (spMap (algebraMap O K))) {d : ℕ}
    (hd : topologicalKrullDim Y = d) : topologicalKrullDim X = (d + 1 : ℕ) := by
  have hO1 : ringKrullDim O ≤ 1 := by exact_mod_cast Ring.krullDimLE_iff.mp (inferInstance : Ring.KrullDimLE 1 O)
  refine le_antisymm (topologicalKrullDim_le_of_forall_exists_isOpen fun x => ?_) ?_
  · obtain ⟨A, _, _, i, _, a, rfl, hi⟩ := exists_affine_chart_over p x
    obtain ⟨i₀, _, -⟩ := exists_affine_chart_of_isPullback H i hi
    refine ⟨Set.range i, i.isOpenEmbedding.isOpen_range, ⟨a, rfl⟩, ?_⟩
    rw [topologicalKrullDim_eq_of_isEmbedding i.isOpenEmbedding.isEmbedding rfl]
    have : Nonempty (Spec (.of A)) := ⟨a⟩
    have : IsIntegral (Spec (.of A)) := isIntegral_of_isOpenImmersion i
    have : IsDomain A := (affine_isIntegral_iff (.of A)).1 this
    have hft : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap O A))) := by rw [← hi]; infer_instance
    have hfl : Flat (Spec.map (CommRingCat.ofHom (algebraMap O A))) := by rw [← hi]; infer_instance
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at hft
    rw [HasRingHomProperty.Spec_iff (P := @Flat)] at hfl
    have : Algebra.FiniteType O A := RingHom.finiteType_algebraMap.mp hft
    have : Module.Flat O A := RingHom.flat_algebraMap_iff.mp hfl
    have : FaithfulSMul O A := inferInstance
    have h₁ : ringKrullDim (K ⊗[O] A) ≤ d :=
      (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _).ge.trans
        (i₀.isOpenEmbedding.isInducing.topologicalKrullDim_le.trans hd.le)
    refine (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim A).le.trans ((ringKrullDim_le_add (O := O) K).trans ?_)
    refine (add_le_add hO1 h₁).trans_eq ?_
    push_cast
    exact add_comm _ _
  · have := IsPreimmersion.of_isLocalization (R := O) (S := K) (nonZeroDivisors O)
    have : IsPreimmersion j := MorphismProperty.of_isPullback H.flip this
    have hj := j.isEmbedding
    have eX : topologicalKrullDim X = Order.krullDim X := Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X))
    have eY : topologicalKrullDim Y = Order.krullDim Y := Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := Y))
    rw [eY] at hd
    rw [eX]
    obtain ⟨l, hl⟩ := Order.le_krullDim_iff.1 hd.ge
    have hm : StrictMono (j : Y → X) := fun a b h =>
      ⟨hj.isInducing.specializes_iff.2 h.1, fun h' => h.2 (hj.isInducing.specializes_iff.1 h')⟩
    obtain ⟨m, hm0, hmp⟩ := Ring.not_isField_iff_exists_prime.1 hO
    have hp (y : Y) : (p (j y)).asIdeal = ⊥ := by
      rw [← Scheme.Hom.comp_apply, H.w, Scheme.Hom.comp_apply]
      change Ideal.comap (algebraMap O K) (q y).asIdeal = ⊥
      rw [(Ideal.eq_bot_or_top _).resolve_right (q y).2.ne_top]
      exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective O K)
    have hs : p (j l.head) ⤳ (⟨m, hmp⟩ : PrimeSpectrum O) :=
      (PrimeSpectrum.le_iff_specializes _ _).1 ((hp _).le.trans bot_le)
    obtain ⟨x, hx, hxm⟩ := p.isClosedMap.specializingMap hs
    have hlt : x < (l.map _ hm).head := by
      refine ⟨hx, fun h' => hm0 ?_⟩
      have h₁ : p x ⤳ p (j l.head) := Specializes.map h' p.continuous
      rw [hxm] at h₁
      have h₂ : m ≤ (p (j l.head)).asIdeal := (PrimeSpectrum.le_iff_specializes _ _).2 h₁
      exact le_bot_iff.1 (h₂.trans (hp _).le)
    refine Order.le_krullDim_iff.2 ⟨(l.map _ hm).cons x hlt, ?_⟩
    simp [hl]

theorem exists_flat_model {O K : Type} [CommRing O] [IsDedekindDomain O] [Field K] [Algebra O K] [IsFractionRing O K]
    {Y : Scheme.{0}} [IsIntegral Y] (q : Y ⟶ Sp K) (hq : IsProjOver q) {ι : Type} [Fintype ι]
    (P : ι → Scheme.{0}) (p : ∀ i, P i ⟶ Sp O) (f : ∀ i, Y ⟶ P i) (hp : ∀ i, IsProjOver (p i))
    (hf : ∀ i, f i ≫ p i = q ≫ spMap (algebraMap O K)) :
    ∃ (X : Scheme.{0}) (π : X ⟶ Sp O) (j : Y ⟶ X), IsIntegral X ∧ IsProjOver π ∧ Flat π ∧
      IsPullback j q π (spMap (algebraMap O K)) ∧ ∀ i, ∃ g : X ⟶ P i, j ≫ g = f i ∧ g ≫ p i = π := by
  obtain ⟨W₀, s₀, i₀, hs₀, H₀⟩ :=
    GlobalTheory.ProjClosure.exists_isProjOver_isPullback_of_isLocalization (nonZeroDivisors O) q hq
  obtain ⟨W, h, r, hW, hr, hg⟩ :=
    CommonModel.exists_common s₀ hs₀ i₀ P p f hp (fun i => (hf i).trans H₀.w.symm) Finset.univ
  have w : h ≫ r ≫ s₀ = q ≫ spMap (algebraMap O K) := by rw [← Category.assoc, hr, H₀.w]
  have hqp : IsProper q := CommonModel.isProper_of_isProjOver hq
  have hsp : IsProper (r ≫ s₀) := CommonModel.isProper_of_isProjOver hW
  have hb := IsPullback.of_hasPullback (r ≫ s₀) (spMap (algebraMap O K))
  let f' : Y ⟶ pullback (r ≫ s₀) (spMap (algebraMap O K)) := pullback.lift h q w
  have hf' : f' ≫ pullback.snd _ _ = q := pullback.lift_snd _ _ _
  let ρ : pullback (r ≫ s₀) (spMap (algebraMap O K)) ⟶ Y :=
    H₀.lift (pullback.fst _ _ ≫ r) (pullback.snd _ _) (by rw [Category.assoc, pullback.condition])
  have hρ : ρ ≫ q = pullback.snd _ _ := H₀.lift_snd _ _ _
  have hfρ : f' ≫ ρ = 𝟙 Y := by
    apply H₀.hom_ext
    · rw [Category.assoc, H₀.lift_fst, pullback.lift_fst_assoc, hr, Category.id_comp]
    · rw [Category.assoc, hρ, pullback.lift_snd, Category.id_comp]
  have : IsSeparated (ρ ≫ q) := by rw [hρ]; infer_instance
  have : IsSeparated ρ := IsSeparated.of_comp ρ q
  have : IsClosedImmersion (f' ≫ ρ) := by rw [hfρ]; infer_instance
  have : IsClosedImmersion f' := IsClosedImmersion.of_comp f' ρ
  have hh : f' ≫ pullback.fst _ _ = h := pullback.lift_fst _ _ _
  have : IsAffineHom (pullback.fst (r ≫ s₀) (spMap (algebraMap O K))) :=
    MorphismProperty.of_isPullback hb.flip (isAffineHom_of_isAffine _)
  have : QuasiCompact h := by rw [← hh]; infer_instance
  have : Flat (spMap (algebraMap O K)) := flat_specMap_localization (nonZeroDivisors O) K
  have : Mono (spMap (algebraMap O K)) := mono_specMap_localization (nonZeroDivisors O) K
  have hpb := isPullback_toImage_of_isClosedImmersion h f' _ hh
  refine ⟨h.image, h.imageι ≫ r ≫ s₀, h.toImage, inferInstance,
    ProjSpace.isProjOver_comp_of_isClosedImmersion _ hW, flat_image_of_over_fractionField h (r ≫ s₀) q w.symm, ?_,
    fun i => ?_⟩
  · have := hpb.flip.paste_vert hb
    rwa [hf'] at this
  · obtain ⟨g, h₁, h₂⟩ := hg i (Finset.mem_univ i)
    exact ⟨h.imageι ≫ g, by rw [← Category.assoc, h.toImage_imageι, h₁], by rw [Category.assoc, h₂]⟩

end GlobalTheory.IntModel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NontrivialOfNeBot
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

namespace GlobalTheory.DefU.Pairs

section Abstract

variable {H S F P P' : Type} [Group H] [AddCommGroup S] [Module ℂ S] [AddCommGroup F] [Module ℂ F]
  [AddCommGroup P] [Module ℂ P] [AddCommGroup P'] [Module ℂ P']

def img (j : P →ₗ[ℂ] S →ₗ[ℂ] F) : Submodule ℂ F := Submodule.span ℂ {φ | ∃ p v, j p v = φ}

theorem apply_mem_img (j : P →ₗ[ℂ] S →ₗ[ℂ] F) (p : P) (v : S) : j p v ∈ img j :=
  Submodule.subset_span ⟨p, v, rfl⟩

variable {ι : Type} [Fintype ι]

def total (b : ι → S) (j : P →ₗ[ℂ] S →ₗ[ℂ] F) : (ι → P) →ₗ[ℂ] F :=
  ∑ a, (LinearMap.applyₗ (b a)) ∘ₗ j ∘ₗ LinearMap.proj a

theorem total_apply (b : ι → S) (j : P →ₗ[ℂ] S →ₗ[ℂ] F) (c : ι → P) :
    total b j c = ∑ a, j (c a) (b a) := by
  simp [total, LinearMap.sum_apply]

theorem total_repr (b : Module.Basis ι ℂ S) (j : P →ₗ[ℂ] S →ₗ[ℂ] F) (p : P) (v : S) :
    total b j (fun a => b.repr v a • p) = j p v := by
  rw [total_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    conv_rhs => rw [← b.sum_repr v, map_sum]
  simp

theorem range_total (b : Module.Basis ι ℂ S) (j : P →ₗ[ℂ] S →ₗ[ℂ] F) :
    LinearMap.range (total b j) = img j := by
  refine le_antisymm ?_ (Submodule.span_le.2 ?_)
  · rintro _ ⟨c, rfl⟩
    rw [total_apply]
    exact Submodule.sum_mem _ fun a _ => apply_mem_img j _ _
  · rintro _ ⟨p, v, rfl⟩
    exact ⟨_, total_repr b j p v⟩

theorem coeff_mem {ρ : Representation ℂ H S} (hsp : Submodule.span ℂ (Set.range ρ) = ⊤) {R : H → Module.End ℂ F}
    {j : P →ₗ[ℂ] S →ₗ[ℂ] F} (hj : ∀ p x v, j p (ρ x v) = R x (j p v)) {U : Submodule ℂ F}
    (hU : ∀ x, ∀ u ∈ U, R x u ∈ U) (b : Module.Basis ι ℂ S) {c : ι → P} (h : total b j c ∈ U) (a : ι) (w : S) :
    j (c a) w ∈ U := by
  classical
  have key : ∀ T : Module.End ℂ S, ∑ a, j (c a) (T (b a)) ∈ U := fun T => by
    have hT : T ∈ Submodule.span ℂ (Set.range ρ) := hsp ▸ Submodule.mem_top
    induction hT using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      have e : ∑ a, j (c a) (ρ g (b a)) = R g (total b j c) := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [total_apply, map_sum]
        exact Finset.sum_congr rfl fun a _ => hj _ _ _
      rw [e]
      exact hU _ _ h
    | zero => simp
    | add x y _ _ hx hy => simpa [Finset.sum_add_distrib] using add_mem hx hy
    | smul r x _ hx => simpa [Finset.smul_sum] using U.smul_mem r hx
  have h1 := key ((b.coord a).smulRight w)
  rw [Finset.sum_eq_single a (fun a' _ h' => by simp [Module.Basis.coord_apply, Finsupp.single_apply, h'])
    (fun h' => absurd (Finset.mem_univ a) h')] at h1
  simpa [Module.Basis.coord_apply] using h1

theorem eq_bot_or_eq_img [FiniteDimensional ℂ S] {K : Type} {ρ : Representation ℂ H S}
    (hsp : Submodule.span ℂ (Set.range ρ) = ⊤) {R : H → Module.End ℂ F} {j : P →ₗ[ℂ] S →ₗ[ℂ] F}
    (hj : ∀ p x v, j p (ρ x v) = R x (j p v)) {Q : K → Module.End ℂ P}
    {T : K → Module.End ℂ F} (hQ : ∀ k p v, j (Q k p) v = T k (j p v))
    (hP : ∀ N : Submodule ℂ P, (∀ k, ∀ p ∈ N, Q k p ∈ N) → N = ⊥ ∨ N = ⊤) {U : Submodule ℂ F} (hle : U ≤ img j)
    (hU : ∀ x, ∀ u ∈ U, R x u ∈ U) (hT : ∀ k, ∀ u ∈ U, T k u ∈ U) : U = ⊥ ∨ U = img j := by
  let N : Submodule ℂ P := ⨅ v : S, U.comap ((LinearMap.applyₗ v) ∘ₗ j)
  have hN : ∀ p, p ∈ N ↔ ∀ v, j p v ∈ U := fun p => by simp [N, Submodule.mem_iInf]
  rcases hP N fun k p hp => (hN _).2 fun v => by
      rw [hQ]
      exact hT _ _ ((hN p).1 hp v) with h | h
  · left
    refine (Submodule.eq_bot_iff _).2 fun φ hφ => ?_
    let b := Module.finBasis ℂ S
    obtain ⟨c, rfl⟩ : φ ∈ LinearMap.range (total b j) := by
      rw [range_total]
      exact hle hφ
    have hc : ∀ a, c a = 0 := fun a => by
      have : c a ∈ N := (hN _).2 fun w => coeff_mem hsp hj hU b hφ a w
      rwa [h, Submodule.mem_bot] at this
    rw [total_apply]
    simp [hc]
  · right
    refine le_antisymm hle (Submodule.span_le.2 ?_)
    rintro _ ⟨p, v, rfl⟩
    exact (hN p).1 (h ▸ Submodule.mem_top) v

end Abstract

section Concrete

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem exists_inf_mul_fin (x : UA E n) : ∃ a ∈ infU E n, ∃ k ∈ finU (E := E) (n := n), x = a * k := by
  let y : GL (Fin n) (Cinf E) := cInf x
  have hx : cT (conjAd E) x.1.val * 1 * x.1.val = 1 := x.2
  have h1 : x.1.val.map (pInf E) = y.val := rfl
  have h3 : (cT (conjAd E) x.1.val).map (pInf E) = y.valᴴ := by
    ext1 i j
    rw [Matrix.conjTranspose_apply, ← h1]
    exact (infEq E).symm_apply_apply _
  have hy : y.valᴴ * y.val = 1 := by
    rw [mul_one] at hx
    rw [← h3, ← h1, ← Matrix.map_mul, hx]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  let a : UA E n := ⟨infGL E n y, infGL_mem_UA y hy⟩
  refine ⟨a, pFin_infGL y, a⁻¹ * x, ?_, (mul_inv_cancel_left a x).symm⟩
  have h4 : cInf a = y := pInf_infGL y
  refine MonoidHom.mem_ker.2 ?_
  rw [map_mul, map_inv, h4]
  exact inv_mul_cancel y

theorem stable_of {U : Submodule ℂ (UA E n → ℂ)} (h1 : ∀ x : infU E n, ∀ φ ∈ U, RU E n x.1 φ ∈ U)
    (h2 : ∀ k : finU (E := E) (n := n), ∀ φ ∈ U, RU E n k.1 φ ∈ U) (x : UA E n) (φ : UA E n → ℂ) (hφ : φ ∈ U) : RU E n x φ ∈ U := by
  obtain ⟨a, ha, k, hk, rfl⟩ := exists_inf_mul_fin x
  rw [← RU_RU]
  exact h1 ⟨a, ha⟩ _ (h2 ⟨k, hk⟩ _ hφ)

theorem exists_cAll (g : InfinitePlace E → GL (Fin n) ℂ)
    (hg : ∀ v, (g v : Matrix (Fin n) (Fin n) ℂ) ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    ∃ y : infU E n, cAll y.1 = g := by
  classical
  let J : Subgroup (InfinitePlace E → GL (Fin n) ℂ) := (cAll.comp (infU E n).subtype).range
  let Hs : InfinitePlace E → Subgroup (GL (Fin n) ℂ) := fun _ => (GlobalTheory.Branching.unitaryIncl n).range
  have hle : Subgroup.pi Set.univ Hs ≤ J := by
    rw [Subgroup.pi_le_iff]
    intro v
    rintro _ ⟨_, ⟨u, rfl⟩, rfl⟩
    obtain ⟨e, he⟩ := GlobalTheory.T.archimedeanUnitaryPoints_equiv_unitaryGroup E n v.embedding
    let x := e.symm u
    have hx := Subgroup.mem_inf.1 x.2
    refine ⟨⟨x.1, hx.1⟩, ?_⟩
    funext v'
    by_cases h : v' = v
    · subst h
      change cEmb v'.embedding x.1 = _
      rw [← he, e.apply_symm_apply]
      simp
    · have h5 : x.1 ∈ (cEmb (E := E) (n := n) v'.embedding).ker :=
        Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hx.2 v'.embedding) (by simpa using h)
      change cEmb v'.embedding x.1 = _
      rw [MonoidHom.mem_ker.1 h5]
      simp [h]
  obtain ⟨y, hy⟩ : g ∈ J := hle fun v _ => ⟨⟨(g v).val, hg v⟩, Units.ext rfl⟩
  exact ⟨y, hy⟩

theorem span_rep (W : Wt E n) [Nontrivial W.Sp] : Submodule.span ℂ (Set.range W.rep) = ⊤ :=
  GlobalTheory.ClassFin.span_range_eq_top_of_isIrreducible _ _ W.rep ((CuspRep.isIrreducible_iff _).2 ⟨inferInstance, fun U hU =>
    GlobalTheory.CoefIrred.vv_irreducible_unitary (InfinitePlace E) n W U fun g hg x hx => by
      obtain ⟨y, rfl⟩ := exists_cAll g hg
      exact hU y x hx⟩)

def jOf (W : Wt E n) (M : Submodule ℂ (algForms W)) : M →ₗ[ℂ] W.Sp →ₗ[ℂ] (UA E n → ℂ) :=
  (algForms W).subtype ∘ₗ M.subtype

theorem jOf_injective (W : Wt E n) (M : Submodule ℂ (algForms W)) : Function.Injective (jOf W M) :=
  Subtype.val_injective.comp Subtype.val_injective

theorem jOf_rep (W : Wt E n) (M : Submodule ℂ (algForms W)) (p : M) (x : infU E n) (v : W.Sp) :
    jOf W M p (W.rep x v) = RU E n x.1 (jOf W M p v) := p.1.2.2 x v

theorem nontrivial_of_ne_bot {W : Wt E n} {M : Submodule ℂ (algForms W)} (h : M ≠ ⊥) :
    Nontrivial W.Sp ∧ img (jOf W M) ≠ ⊥ := by
  obtain ⟨p, hp, h0⟩ := (Submodule.ne_bot_iff _).1 h
  have h1 : jOf W M ⟨p, hp⟩ ≠ 0 := fun e => h0 (congrArg Subtype.val (jOf_injective W M (e.trans (map_zero _).symm)))
  obtain ⟨v, hv⟩ := DFunLike.ne_iff.1 h1
  refine ⟨⟨v, 0, fun e => hv (by rw [e, map_zero]; rfl)⟩, fun e => hv ?_⟩
  have := apply_mem_img (jOf W M) ⟨p, hp⟩ v
  rw [e, Submodule.mem_bot] at this
  exact this

theorem img_stable {W : Wt E n} {M : Submodule ℂ (algForms W)} (hM : ∀ k, ∀ f ∈ M, algRep W k f ∈ M) (x : UA E n)
    (φ : UA E n → ℂ) (hφ : φ ∈ img (jOf W M)) : RU E n x φ ∈ img (jOf W M) := by
  refine stable_of (fun a => ?_) (fun k => ?_) x φ hφ
  · have h1 : img (jOf W M) ≤ (img (jOf W M)).comap (RU E n a.1) := Submodule.span_le.2 (by
      rintro _ ⟨p, v, rfl⟩
      change RU E n a.1 _ ∈ img (jOf W M)
      rw [← jOf_rep]
      exact apply_mem_img _ _ _)
    exact fun φ hφ => h1 hφ
  · have h1 : img (jOf W M) ≤ (img (jOf W M)).comap (RU E n k.1) := Submodule.span_le.2 (by
      rintro _ ⟨p, v, rfl⟩
      exact apply_mem_img (jOf W M) ⟨algRep W k p.1, hM k _ p.2⟩ v)
    exact fun φ hφ => h1 hφ

theorem V_eq_img (π : AutSub E n) {W : Wt E n} {M : Submodule ℂ (algForms W)} (hM : ∀ k, ∀ f ∈ M, algRep W k f ∈ M)
    (h0 : M ≠ ⊥) (hle : M ≤ π.finPart W) : π.V = img (jOf W M) := by
  have h1 : img (jOf W M) ≤ π.V := Submodule.span_le.2 (by
    rintro _ ⟨p, v, rfl⟩
    exact AutSub.mem_finPart.1 (hle p.2) v)
  exact ((π.isAut.irred _ h1 (img_stable hM)).resolve_left (nontrivial_of_ne_bot h0).2).symm

theorem finPart_stable (π : AutSub E n) (W : Wt E n) : ∀ k, ∀ f ∈ π.finPart W, algRep W k f ∈ π.finPart W :=
  fun k _ h => AutSub.mem_finPart.2 fun v => π.isAut.stable k _ (AutSub.mem_finPart.1 h v)

section Iso

variable {π π' : AutSub E n} {W : Wt E n} (e : π.finPart W ≃ₗ[ℂ] π'.finPart W) (T : π.V ≃ₗ[ℂ] π'.V)
  (hA : π.V = img (jOf W (π.finPart W)))
  (hT : ∀ p v (h : jOf W (π.finPart W) p v ∈ π.V), (T ⟨jOf W (π.finPart W) p v, h⟩ : UA E n → ℂ) = jOf W (π'.finPart W) (e p) v)

include hA hT

end Iso

end Concrete

end GlobalTheory.DefU.Pairs

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InducedMetricPullback
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions

namespace GlobalTheory.TrueGeo.InducedPull

variable {X X' Z : Scheme.{0}}

theorem val_pull_g (B : LB X) (a : Z ⟶ X) (i i' : (B.pull a).ι)
    (l : (B.pull a).U i ⊓ (B.pull a).U i' ≤ a ⁻¹ᵁ (B.U (i PUnit.unit) ⊓ B.U (i' PUnit.unit))) :
    ((B.pull a).g i i').val = (a.appLE _ _ l).hom (B.g (i PUnit.unit) (i' PUnit.unit)).val := by
  have : (B.pull a).g i i' = res l (pullU a _ (B.g (i PUnit.unit) (i' PUnit.unit))) := by
    change ∏ _k : PUnit, _ = _
    exact (Fintype.prod_unique _).trans (zpow_one _)
  rw [this]
  rfl

end GlobalTheory.TrueGeo.InducedPull
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ComplexPointsLiftModel
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions

namespace GlobalTheory

theorem ringOfIntegers_hom_complex_injective (F : Type) [Field F] [NumberField F] (τ : 𝓞 F →+* ℂ) :
    Function.Injective τ := by
  rw [RingHom.injective_iff_ker_eq_bot]
  apply Ideal.eq_bot_of_comap_eq_bot (R := ℤ)
  rw [Ideal.under_def, RingHom.comap_ker, ← RingHom.injective_iff_ker_eq_bot]
  exact RingHom.injective_int _

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CartierLocalEquationCommon
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions

namespace GlobalTheory.Cartier.CommonEqn

variable {X : Scheme.{0}} [IsIntegral X]

theorem generatesAt_add {D : CartierDiv X} {x : X} {f f' : X.functionField}
    (h : D.GeneratesAt x f) (h' : D.VanishesAt x f') : D.GeneratesAt x (f + f') := by
  obtain ⟨g, hg, a, ha, e⟩ := h
  obtain ⟨b, hb, e'⟩ := hg.vanishesAt_iff.1 h'
  refine ⟨g, hg, a + b, ?_, by rw [map_add (f := _), e, e', add_mul]⟩
  by_contra hu
  have : a + b ∈ IsLocalRing.maximalIdeal _ := hu
  exact (show a ∈ IsLocalRing.maximalIdeal _ from by simpa using sub_mem this hb) ha

end GlobalTheory.Cartier.CommonEqn
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CombPowIsometric
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions

namespace GlobalTheory.ArInt

theorem isometric_comb_unit_pow : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (L : HermLB p) (m : ℕ), (ArInt.comb (fun _ : Unit => L) (fun _ => (m : ℤ))).Isometric (L.pow m) := by
  intro k _ X _ p L m
  rw [← HermLB.icls_eq_iff, icls_comb, HermLB.icls_pow]
  simp

end GlobalTheory.ArInt
end
