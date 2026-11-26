module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentAndTwistData
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SideMultiplicityFamily
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NVNeZero
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BrgStdR
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLayerParametersAdmissible
public import Formalism.LocalToGlobal.Columns.MtHeckeSum
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CorrectionOfTransport
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemUnipSymBc
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitsLiftSpec

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistedLatticeFinitelyGeneratedSpanning
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistedLatticeFinitelyGeneratedSpanning
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.HeightCounting.FormsStep

variable (D : D7) (T : TwR D.LL0 D.nd) (S : RatDat D.ntw)

theorem readT_integral (i : T.Tw) (b : Bool) (x : ↥D.LL0) (hx : IsIntegral ℤ x) :
    ∃ o : T.O i, algebraMap (T.O i) (FractionRing (T.O i)) o = readT D T i b x := by
  have key : ∀ e : ↥D.LL0 →+* FractionRing (T.O0 i),
      ∃ y : T.O0 i, algebraMap (T.O0 i) (FractionRing (T.O0 i)) y = e x := by
    intro e
    have h1 : IsIntegral ℤ (e x) := by
      obtain ⟨p, hp, hpx⟩ := hx
      refine ⟨p, hp, ?_⟩
      have h3 := congrArg e hpx
      rw [map_zero, Polynomial.hom_eval₂] at h3
      rwa [RingHom.ext_int (e.comp (algebraMap ℤ _)) (algebraMap ℤ _)] at h3
    have h2 : IsIntegral (T.O0 i) (e x) := h1.tower_top
    exact IsIntegrallyClosed.isIntegral_iff.mp h2
  obtain ⟨y, hy⟩ := key (if b then T.emb0 i else T.emb0b i)
  refine ⟨algebraMap (T.O0 i) (T.O i) y, ?_⟩
  unfold readT
  rw [RingHom.comp_apply, ← hy]
  exact (IsLocalization.map_eq _ _).symm

theorem ksInt_mem (i : T.Tw) (b : Bool) (a : 𝓞 S.Ks) :
    ∃ o : T.O i, algebraMap (T.O i) (FractionRing (T.O i)) o = algebraMap S.Ks (KT D T i b) (a : S.Ks) :=
  readT_integral D T i b _ ((RingOfIntegers.isIntegral_coe a).map S.kKs.toIntAlgHom)

theorem one_tmul_smul (i : T.Tw) (j : ℕ) (b : Bool) (c : S.Ks) (m : ↥(WKr D S j)) :
    ((1 : KT D T i b) ⊗ₜ[S.Ks] (c • m) : KT D T i b ⊗[S.Ks] ↥(WKr D S j)) =
      algebraMap S.Ks (KT D T i b) c • ((1 : KT D T i b) ⊗ₜ[S.Ks] m) := by
  rw [← TensorProduct.smul_tmul, TensorProduct.smul_tmul', Algebra.smul_def, mul_one, smul_eq_mul, mul_one]

theorem fmT_eq_zero (i : T.Tw) (j : ℕ) (b : Bool) (h : ¬ (1 ≤ j ∧ j ≤ D.R.m)) (z : KT D T i b ⊗[S.Ks] ↥(WKr D S j)) : z = 0 := by
  induction z using TensorProduct.induction_on with
  | zero => rfl
  | tmul k m =>
    have hm : m = 0 := by
      exact Subtype.ext (Submodule.mem_bot _ |>.mp ((WKr_off D S h).le m.2))
    rw [hm, TensorProduct.tmul_zero]
  | add x y hx hy => rw [hx, hy, add_zero]

theorem bsupT_fg_span (In : RatIn D S) (i : T.Tw) (j : ℕ) (b : Bool) :
    (BsupT D T S i j b).FG ∧
      Submodule.span (FractionRing (T.O i)) (BsupT D T S i j b : Set (FmT D T S i j b)) = ⊤ := by
  by_cases h : 1 ≤ j ∧ j ≤ D.R.m
  swap
  · have hz := fmT_eq_zero D T S i j b h
    refine ⟨?_, ?_⟩
    · have : BsupT D T S i j b = ⊥ := (Submodule.eq_bot_iff _).mpr fun z _ => hz z
      rw [this]; exact Submodule.fg_bot
    · exact Submodule.eq_top_iff'.mpr fun z => by rw [hz z]; exact Submodule.zero_mem _
  obtain ⟨T0, hT, hMK, hWK⟩ := In.mk_fg j h.1 h.2
  have hmem : ∀ t ∈ T0, t ∈ WKr D S j := fun t ht => by
    rw [WKr_of D S h.1 h.2]; exact (hMK t (hT t ht)).1
  let g : ↥T0 → FmT D T S i j b := fun t =>
    ((1 : KT D T i b) ⊗ₜ[S.Ks] (⟨t.1, hmem t.1 t.2⟩ : ↥(WKr D S j)) : KT D T i b ⊗[S.Ks] ↥(WKr D S j))
  have hgB : Set.range g ⊆ BsupT D T S i j b := by
    rintro _ ⟨t, rfl⟩
    exact Submodule.subset_span ⟨⟨t.1, hmem t.1 t.2⟩, hT t.1 t.2, rfl⟩

  have hO : ∀ y ∈ Submodule.span (𝓞 S.Ks) (T0 : Set (S.WL j)), y ∈ WKr D S j ∧ ∀ hy : y ∈ WKr D S j,
      (((1 : KT D T i b) ⊗ₜ[S.Ks] (⟨y, hy⟩ : ↥(WKr D S j)) : KT D T i b ⊗[S.Ks] ↥(WKr D S j)) : FmT D T S i j b) ∈
        Submodule.span (T.O i) (Set.range g) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem t ht => exact ⟨hmem t ht, fun _ => Submodule.subset_span ⟨⟨t, ht⟩, rfl⟩⟩
    | zero =>
      refine ⟨Submodule.zero_mem _, fun hy => ?_⟩
      have : (⟨0, hy⟩ : ↥(WKr D S j)) = 0 := rfl
      rw [this, TensorProduct.tmul_zero]; exact Submodule.zero_mem _
    | add y z _ _ hy hz =>
      refine ⟨Submodule.add_mem _ hy.1 hz.1, fun hyz => ?_⟩
      have : (⟨y + z, hyz⟩ : ↥(WKr D S j)) = ⟨y, hy.1⟩ + ⟨z, hz.1⟩ := rfl
      rw [this, TensorProduct.tmul_add]
      exact Submodule.add_mem _ (hy.2 hy.1) (hz.2 hz.1)
    | smul a y _ hy =>
      have hay : a • y = (a : S.Ks) • y := (algebraMap_smul S.Ks a y).symm
      have hm : a • y ∈ WKr D S j := by rw [hay]; exact Submodule.smul_mem _ _ hy.1
      refine ⟨hm, fun hy' => ?_⟩
      have : (⟨a • y, hy'⟩ : ↥(WKr D S j)) = (a : S.Ks) • ⟨y, hy.1⟩ := Subtype.ext hay
      rw [this, one_tmul_smul]
      obtain ⟨o, ho⟩ := ksInt_mem D T S i b a
      rw [← ho]
      exact Submodule.smul_mem _ o (hy.2 hy.1)
  have hBeq : BsupT D T S i j b = Submodule.span (T.O i) (Set.range g) := by
    refine le_antisymm ?_ (Submodule.span_le.mpr hgB)
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨x, hx, rfl⟩
    exact (hO x.1 (hMK x.1 hx).2).2 x.2
  refine ⟨?_, ?_⟩
  · rw [hBeq]; exact Submodule.fg_span (Set.finite_range g)

  have hK : ∀ y ∈ Submodule.span S.Ks (T0 : Set (S.WL j)), y ∈ WKr D S j ∧ ∀ hy : y ∈ WKr D S j,
      (((1 : KT D T i b) ⊗ₜ[S.Ks] (⟨y, hy⟩ : ↥(WKr D S j)) : KT D T i b ⊗[S.Ks] ↥(WKr D S j)) : FmT D T S i j b) ∈
        Submodule.span (FractionRing (T.O i)) (BsupT D T S i j b : Set (FmT D T S i j b)) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem t ht => exact ⟨hmem t ht, fun _ => Submodule.subset_span (hgB ⟨⟨t, ht⟩, rfl⟩)⟩
    | zero =>
      refine ⟨Submodule.zero_mem _, fun hy => ?_⟩
      have : (⟨0, hy⟩ : ↥(WKr D S j)) = 0 := rfl
      rw [this, TensorProduct.tmul_zero]; exact Submodule.zero_mem _
    | add y z _ _ hy hz =>
      refine ⟨Submodule.add_mem _ hy.1 hz.1, fun hyz => ?_⟩
      have : (⟨y + z, hyz⟩ : ↥(WKr D S j)) = ⟨y, hy.1⟩ + ⟨z, hz.1⟩ := rfl
      rw [this, TensorProduct.tmul_add]
      exact Submodule.add_mem _ (hy.2 hy.1) (hz.2 hz.1)
    | smul c y _ hy =>
      have hm : c • y ∈ WKr D S j := Submodule.smul_mem _ _ hy.1
      refine ⟨hm, fun hy' => ?_⟩
      have : (⟨c • y, hy'⟩ : ↥(WKr D S j)) = c • ⟨y, hy.1⟩ := rfl
      rw [this, one_tmul_smul]
      exact Submodule.smul_mem _ _ (hy.2 hy.1)
  refine Submodule.eq_top_iff'.mpr fun z => ?_
  change KT D T i b ⊗[S.Ks] ↥(WKr D S j) at z
  induction z using TensorProduct.induction_on with
  | zero => exact Submodule.zero_mem _
  | tmul k m =>
    have hm : (m : S.WL j) ∈ Submodule.span S.Ks (T0 : Set (S.WL j)) := by
      exact hWK _ ((WKr_of D S h.1 h.2).le m.2)
    have h1 := (hK m.1 hm).2 m.2
    have h2 : (k ⊗ₜ[S.Ks] m : KT D T i b ⊗[S.Ks] ↥(WKr D S j)) = k • ((1 : KT D T i b) ⊗ₜ[S.Ks] m) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [h2]
    exact Submodule.smul_mem _ k h1
  | add x y hx hy => exact Submodule.add_mem _ hx hy

theorem bsupT_fg_span_all : ∀ (D : D7) (S : RatDat D.ntw) (In : RatIn D S) (T : TwR D.LL0 D.nd) (i : T.Tw) (j : ℕ) (b : Bool),
    (BsupT D T S i j b).FG ∧
      Submodule.span (FractionRing (T.O i)) (BsupT D T S i j b : Set (FmT D T S i j b)) = ⊤ :=
  fun D S In T i j b => bsupT_fg_span D T S In i j b

end GlobalTheory.HeightCounting.FormsStep
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistedLatticeFinitelyGeneratedSpanningStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_lattice_finitely_generated_spanning : ∀ (D : D7) (S : RatDat D.ntw) (In : RatIn D S) (T : TwR D.LL0 D.nd) (i : T.Tw) (j : ℕ) (b : Bool),
    (BsupT D T S i j b).FG ∧
      Submodule.span (FractionRing (T.O i)) (BsupT D T S i j b : Set (FmT D T S i j b)) = ⊤ := by
  first | exact @GlobalTheory.HeightCounting.FormsStep.bsupT_fg_span_all | exact GlobalTheory.HeightCounting.FormsStep.bsupT_fg_span_all | (intros; apply GlobalTheory.HeightCounting.FormsStep.bsupT_fg_span_all <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceCompactOpenMembership
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.LocLevel

theorem mem_placesOver_of_overPl' {D : D7} {p : ℕ} {w w' : PlE D.host}
    {v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E))} (hw : NG.OverPl w v) (hw' : NG.OverPl w' v)
    (h : w' ∈ placesOver D.host.E p) : w ∈ placesOver D.host.E p := by
  have h1 : ((p : ℕ) : 𝓞 (maximalRealSubfield D.host.E)) ∈ v.asIdeal := by
    rw [← hw', Ideal.mem_comap, map_natCast]; exact h
  rw [← hw, Ideal.mem_comap, map_natCast] at h1
  exact h1

theorem overPl_of_isConjPl {D : D7} {w : PlE D.host} {s : SplitPlace D.host.E} (hc : IsConjPl D.host w s.w) :
    NG.OverPl w s.v := by
  unfold NG.OverPl
  rw [← s.w_under]
  ext a
  rw [Ideal.mem_comap, Ideal.mem_comap]
  apply hc
  have hy := GlobalTheory.SplitConjPlace.cO_algebraMap a
  set y := algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E) a
  have e1 : (y : D.host.E) = IsCMField.complexConj D.host.E (y : D.host.E) := by
    conv_lhs => rw [← hy]
    rw [IsCMField.coe_ringOfIntegersComplexConj]
  rw [e1]
  conv_rhs => rw [← e1]
  exact D.host.φ₀.injective (by
    rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply])


end GlobalTheory.LocLevel
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RTupQEqOneIff
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

noncomputable section

namespace GlobalTheory.Mem.R3.RowAct

section Gen

variable {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)

theorem parLev_of_Q (q : (levEnv V β L).Q) :
    Formalism.UG.bc (swapAE D) ((q : Bridge.Gf V) : GL _ _) ∈ parLev D.sp.cm V.gram β L := q.2.1

def rTupQ : (levEnv V β L).Q →* G0 L.Pg L.r where
  toFun q := rTup β L (Formalism.UG.bc (swapAE D) ((q : Bridge.Gf V) : GL _ _))
  map_one' := by
    simp only [OneMemClass.coe_one, map_one]
    exact rTup_one
  map_mul' x y := by
    simp only [Subgroup.coe_mul, map_mul]
    exact rTup_mul (parLev_of_Q V β L x) (parLev_of_Q V β L y)

theorem rTupQ_eq_one_iff (q : (levEnv V β L).Q) :
    rTupQ V β L q = 1 ↔ ((q : Bridge.Gf V)) ∈ (levEnv V β L).J := by
  constructor
  · intro h
    exact ⟨parLev_of_Q V β L q, Subgroup.mem_bot.2 h⟩
  · intro h
    exact Subgroup.mem_bot.1 h.2

end Gen

end GlobalTheory.Mem.R3.RowAct
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdentityIntegralUnitaryFrameCoordinatesOfUnitGra
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdentityIntegralUnitaryFrameCoordinatesOfUnitGra
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 1000000

namespace GlobalTheory.Mem.R3.LiftBrg

theorem castGL_mem_UA_one {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (hc : CMData F E) {m n : ℕ} (h : m = n) (x : GL (Fin m) (E ⊗[F] Formalism.L2.Herm.Af F)) :
    castGL h x ∈ Formalism.L2.DIV.UA hc (1 : Matrix (Fin n) (Fin n) E) ↔
      x ∈ Formalism.L2.DIV.UA hc (1 : Matrix (Fin m) (Fin m) E) := by
  subst h
  have : castGL (rfl : m = m) x = x := by
    ext i j
    rfl
  rw [this]

theorem frameOK_one_of_gram_eq_one (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (U : Set I.ι)
    (i : Fin X.toD7.R.m) (t : TupU I U) (hg : (Vc X.toD7 i).gram = 1) : LiftBrg.FrameOK X I U i t 1 1 := by
  refine ⟨⟨1, (map_one _).symm⟩, one_mem _, fun x => ?_, one_mem _, one_mem _, fun PP _ => ?_⟩
  · rw [hg, one_mul, inv_one, mul_one]
    exact (castGL_mem_UA_one X.toD7.sp.cm (rkEq X i) x).symm
  · rw [one_mul]; exact one_mem _

end GlobalTheory.Mem.R3.LiftBrg
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdentityIntegralUnitaryFrameCoordinatesOfUnitGraStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.identity_integralUnitaryFrameCoordinates_of_unitGram : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (U : Set I.ι) (i : Fin X.toD7.R.m) (t : TupU I U), (Vc X.toD7 i).gram = 1 → LiftBrg.FrameOK X I U i t 1 1 := by
  first | exact @GlobalTheory.Mem.R3.LiftBrg.frameOK_one_of_gram_eq_one | exact GlobalTheory.Mem.R3.LiftBrg.frameOK_one_of_gram_eq_one | (intros; apply GlobalTheory.Mem.R3.LiftBrg.frameOK_one_of_gram_eq_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RecAtOfTwoPasses
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top NumberField IsDedekindDomain

namespace GlobalTheory.Mem.Top.V4.TwoPass

theorem large_of_sup {C : FC} {K K' : TransportedAlt} {CH : ℝ} (h : C.Large (K.sup K') CH) : C.Large K CH ∧ C.Large K' CH :=
  ⟨⟨fun c hc => (le_max_left _ _).trans (h.1 c hc), trivial, fun c hc => (le_max_left _ _).trans (h.2.2.1 c hc),
      fun c hc => (le_max_left _ _).trans (h.2.2.2 c hc)⟩,
    ⟨fun c hc => (le_max_right _ _).trans (h.1 c hc), trivial, fun c hc => (le_max_right _ _).trans (h.2.2.1 c hc),
      fun c hc => (le_max_right _ _).trans (h.2.2.2 c hc)⟩⟩

theorem ev_and {p q : Ctx → Prop} (hp : Ev p) (hq : Ev q) : Ev fun K => p K ∧ q K := by
  obtain ⟨a, ha, hp⟩ := hp
  obtain ⟨b, hb, hq⟩ := hq
  refine ⟨min a b, lt_min ha hb, fun e C8 he hle h52 h8 => ?_⟩
  obtain ⟨K, hK⟩ := hp e C8 he (hle.trans (min_le_left _ _)) h52 h8
  obtain ⟨K', hK'⟩ := hq e C8 he (hle.trans (min_le_right _ _)) h52 h8
  refine ⟨K.sup K', fun C hC hC8 hL => ?_⟩
  obtain ⟨a1, ha1⟩ := hK C hC hC8 (large_of_sup hL).1
  obtain ⟨b1, hb1⟩ := hK' C hC hC8 (large_of_sup hL).2
  refine ⟨max a1 b1, fun cD hcD => ?_⟩
  obtain ⟨a2, ha2⟩ := ha1 cD (le_trans (le_max_left _ _) hcD)
  obtain ⟨b2, hb2⟩ := hb1 cD (le_trans (le_max_right _ _) hcD)
  refine ⟨max a2 b2, fun ch hch => ?_⟩
  obtain ⟨a3, ha3⟩ := ha2 ch (le_trans (le_max_left _ _) hch)
  obtain ⟨b3, hb3⟩ := hb2 ch (le_trans (le_max_right _ _) hch)
  exact ⟨max a3 b3, fun X h1 h2 h3 h4 hx =>
    ⟨ha3 X h1 h2 h3 h4 (le_trans (le_max_left _ _) hx), hb3 X h1 h2 h3 h4 (le_trans (le_max_right _ _) hx)⟩⟩

theorem ev_mono {p q : Ctx → Prop} (h : ∀ K, p K → q K) (hp : Ev p) : Ev q := by
  obtain ⟨a, ha, hp⟩ := hp
  refine ⟨a, ha, fun e C8 he hle h52 h8 => ?_⟩
  obtain ⟨K, hK⟩ := hp e C8 he hle h52 h8
  refine ⟨K, fun C hC hC8 hL => ?_⟩
  obtain ⟨a1, ha1⟩ := hK C hC hC8 hL
  refine ⟨a1, fun cD hcD => ?_⟩
  obtain ⟨a2, ha2⟩ := ha1 cD hcD
  refine ⟨a2, fun ch hch => ?_⟩
  obtain ⟨a3, ha3⟩ := ha2 ch hch
  exact ⟨a3, fun X h1 h2 h3 h4 hx => h X (ha3 X h1 h2 h3 h4 hx)⟩

end GlobalTheory.Mem.Top.V4.TwoPass

namespace GlobalTheory.Mem.Top.V4

open TwoPass

end GlobalTheory.Mem.Top.V4
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPtOfMulK1Standard
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPtOfMulK1Standard
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TopCh.KStd

theorem K1_le_J0_empty {B : Base} (n : ℕ) [NeZero n] (ST SG : Finset (HeightOneSpectrum (𝓞 B.host.E))) :
    K1 B.sp.cm n ST SG ≤ J0 B.sp.cm n ∅ := by
  intro t ht
  have h1 := principal_le_congruence_subgroup B.sp.cm n ST SG ht
  unfold J0 at h1 ⊢
  simp only [Subgroup.mem_inf] at h1 ⊢
  refine ⟨h1.1, ?_⟩
  simp

theorem exists_ptOf_mul_K1 : ∀ {B : Base} (n : ℕ) [NeZero n] (ST SG : Finset (HeightOneSpectrum (𝓞 B.host.E))) (k t : GA B n), t ∈ K1 B.sp.cm n ST SG → (∃ p : DecoF B.fields.E n ∅ ∅ ∅, PtOf k p ∧ p.deco.1.N = stdLat B.fields.E n) → ∃ p : DecoF B.fields.E n ∅ ∅ ∅, PtOf (k * t) p ∧ p.deco.1.N = stdLat B.fields.E n := by
  intro B n _ ST SG k t ht ⟨p, hp, hN⟩
  have hz : t ∈ J0 B.sp.cm n ∅ := K1_le_J0_empty n ST SG ht
  refine ⟨p, ?_, hN⟩
  refine (GlobalTheory.Mem.Col2.PtDeco.isPtOf_iff_decoRaw B.host.F B.host.E B.sp.cm n ∅ ∅ ∅ (k * t) p rfl).2 ⟨?_, ?_⟩
  · exact mul_mem hp.uni (congruence_le_adelic_unitary B.sp.cm n ∅ hz)
  · have h := decoRaw_rawSm B.sp.cm ∅ ∅ 1 (⟨t, hz⟩⁻¹ : J0 B.sp.cm n ∅) k
    rw [map_one, map_inv] at h
    have e : Formalism.UG.bc (iA B.host.F B.host.E) ((1 : URat B.sp.cm n) : GL (Fin n) B.host.E) * k *
        (((⟨t, hz⟩⁻¹ : J0 B.sp.cm n ∅) : J0 B.sp.cm n ∅) : GL (Fin n) (AfE B.host.F B.host.E))⁻¹ = k * t := by
      simp
    rw [e] at h
    have hr : (redG B.sp.cm n ∅ ∅ ⟨t, hz⟩)⁻¹ = 1 := Subsingleton.elim _ _
    rw [hr] at h
    rw [(near_of_isPtOf hp 0).deco] at h
    simp only [map_one] at h
    change decoRaw ∅ ∅ (k * t) = Deco.act 1 1 p.deco.1 at h
    rw [Deco.act_one] at h
    exact h.symm

end GlobalTheory.Mem.Col2.TopCh.KStd

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPtOfMulK1StandardStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ptOf_mul_K1_standard : ∀ {B : Base} (n : ℕ) [NeZero n] (ST SG : Finset (HeightOneSpectrum (𝓞 B.host.E))) (k t : GA B n), t ∈ K1 B.sp.cm n ST SG → (∃ p : DecoF B.fields.E n ∅ ∅ ∅, PtOf k p ∧ p.deco.1.N = stdLat B.fields.E n) → ∃ p : DecoF B.fields.E n ∅ ∅ ∅, PtOf (k * t) p ∧ p.deco.1.N = stdLat B.fields.E n := by
  first | exact @GlobalTheory.Mem.Col2.TopCh.KStd.exists_ptOf_mul_K1 | exact GlobalTheory.Mem.Col2.TopCh.KStd.exists_ptOf_mul_K1 | (intros; apply GlobalTheory.Mem.Col2.TopCh.KStd.exists_ptOf_mul_K1 <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdelicPointFinitePartEqRealOne
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdelicPointFinitePartEqRealOne
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
open GlobalTheory.Mem.R3.LiftBrg

namespace GlobalTheory.Mem.FinPartLift

theorem exists_gfC_finHom_eq : ∀ {D : D7} (V : HSp D) (g : Bridge.Gf V), ∃ α ∈ GfC V, finHom V α = (g : GL (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) := by
  intro D V g
  obtain ⟨β, hβ⟩ := g.2
  obtain ⟨α, hα, e⟩ := GlobalTheory.AdIsomCorrection.exists_finE V (Formalism.IndefR.Lev.finE V β) (GlobalTheory.LevSplit.finE_mem_UA V β)
  refine ⟨α, hα, ?_⟩
  rw [← hβ]
  apply Units.ext
  ext i j
  have h := congrArg (fun x : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D) => x.val i j) e
  exact (Algebra.TensorProduct.comm D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.host.E).injective h

end GlobalTheory.Mem.FinPartLift
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdelicPointFinitePartEqRealOneStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
open GlobalTheory.Mem.R3.LiftBrg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adelicPoint_finitePart_eq_realOne : ∀ {D : D7} (V : HSp D) (g : Bridge.Gf V), ∃ α ∈ GfC V, finHom V α = (g : GL (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) := by
  exact @_root_.GlobalTheory.Mem.FinPartLift.exists_gfC_finHom_eq
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaloisFamilyIrreducible
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.AutUnr

section Fixed
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]

theorem exists_fixed_of_mem_biSup (ρ : Representation ℂ (GQ L n) W) (K : Set (GAf L n))
    (t : Finset (Submodule ℂ (GAf L n → W))) :
    (∀ S ∈ t, NG.IsIrrRep ρ S) → ∀ f ∈ ⨆ S ∈ t, S, f ≠ 0 → (∀ κ ∈ K, NG.rt L n κ f = f) →
      ∃ S ∈ t, ∃ g ∈ S, g ≠ 0 ∧ ∀ κ ∈ K, NG.rt L n κ g = g := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    intro _ f hf hf0 _
    simp only [Finset.notMem_empty, iSup_false, iSup_bot, Submodule.mem_bot] at hf
    exact absurd hf hf0
  | insert S t hS ih =>
    intro ht f hf hf0 hfix
    have ht' : ∀ S' ∈ t, NG.IsIrrRep ρ S' := fun S' h => ht S' (Finset.mem_insert_of_mem h)
    have hSi := ht S (Finset.mem_insert_self _ _)
    have hNst : ∀ h, ∀ g ∈ ⨆ S' ∈ t, S', NG.rt L n h g ∈ ⨆ S' ∈ t, S' := by
      intro h
      have hle : (⨆ S' ∈ t, S') ≤ (⨆ S' ∈ t, S').comap (NG.rt L n h) := by
        refine iSup₂_le fun S' hS' g hg => ?_
        exact (le_iSup₂ (f := fun (S'' : Submodule ℂ (GAf L n → W)) (_ : S'' ∈ t) => S'') S' hS')
          ((ht' S' hS').1.stable h g hg)
      exact fun g hg => hle hg
    rw [Finset.iSup_insert] at hf
    by_cases hd : S ⊓ (⨆ S' ∈ t, S') = ⊥
    · obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hf
      have hfa : ∀ κ ∈ K, NG.rt L n κ a = a ∧ NG.rt L n κ b = b := by
        intro κ hκ
        have e := hfix κ hκ
        rw [map_add (f := _)] at e
        have h1 : NG.rt L n κ a - a = b - NG.rt L n κ b := by
          rw [sub_eq_sub_iff_add_eq_add, e, add_comm]
        have hm : NG.rt L n κ a - a ∈ S ⊓ (⨆ S' ∈ t, S') :=
          ⟨S.sub_mem (hSi.1.stable κ a ha) ha, h1 ▸ Submodule.sub_mem _ hb (hNst κ b hb)⟩
        rw [hd, Submodule.mem_bot] at hm
        refine ⟨sub_eq_zero.1 hm, ?_⟩
        rw [hm] at h1
        exact (sub_eq_zero.1 h1.symm).symm
      by_cases ha0 : a = 0
      · subst ha0
        rw [zero_add] at hf0
        obtain ⟨S', hS', g, hg, hg0, hgf⟩ := ih ht' b hb hf0 fun κ hκ => (hfa κ hκ).2
        exact ⟨S', Finset.mem_insert_of_mem hS', g, hg, hg0, hgf⟩
      · exact ⟨S, Finset.mem_insert_self _ _, a, ha, ha0, fun κ hκ => (hfa κ hκ).1⟩
    · have hsub : NG.IsSubrep ρ (S ⊓ (⨆ S' ∈ t, S')) :=
        ⟨inf_le_left.trans hSi.1.le, fun h g hg => ⟨hSi.1.stable h g hg.1, hNst h g hg.2⟩⟩
      have heq : S ⊓ (⨆ S' ∈ t, S') = S := (hSi.2.2 _ hsub inf_le_left).resolve_left hd
      have hSN : S ≤ ⨆ S' ∈ t, S' := heq ▸ inf_le_right
      have hfN : f ∈ ⨆ S' ∈ t, S' := (sup_le hSN le_rfl) hf
      obtain ⟨S', hS', g, hg, hg0, hgf⟩ := ih ht' f hfN hf0 hfix
      exact ⟨S', Finset.mem_insert_of_mem hS', g, hg, hg0, hgf⟩

theorem exists_fixed_of_isoTyp (ρ : Representation ℂ (GQ L n) W) {S : Submodule ℂ (GAf L n → W)}
    (hS : ∀ h, ∀ f ∈ S, NG.rt L n h f ∈ S) (K : Set (GAf L n)) {f : GAf L n → W} (hf : f ∈ NG.isoTyp ρ S)
    (hf0 : f ≠ 0) (hfix : ∀ κ ∈ K, NG.rt L n κ f = f) : ∃ g ∈ S, g ≠ 0 ∧ ∀ κ ∈ K, NG.rt L n κ g = g := by
  unfold NG.isoTyp at hf
  obtain ⟨s, hs, hfs⟩ := Submodule.mem_sSup_iff_exists_finset.1 hf
  obtain ⟨S', hS', g, hg, hg0, hgf⟩ :=
    exists_fixed_of_mem_biSup ρ K s (fun S' h => (hs h).1) f hfs hf0 hfix
  obtain ⟨T, hT⟩ := (hs hS').2
  refine ⟨(T.symm ⟨g, hg⟩ : S), (T.symm ⟨g, hg⟩).2, ?_, fun κ hκ => ?_⟩
  · intro h0
    apply hg0
    have h1 : T.symm ⟨g, hg⟩ = 0 := Subtype.ext h0
    have h2 := congrArg T h1
    rw [LinearEquiv.apply_symm_apply, map_zero] at h2
    exact congrArg Subtype.val h2
  · set a := T.symm ⟨g, hg⟩
    have e := hT κ a ⟨NG.rt L n κ (a : GAf L n → W), hS κ _ a.2⟩ rfl
    have hTa : ((T a : _) : GAf L n → W) = g := by simp [a]
    rw [hTa, hgf κ hκ] at e
    have e2 : T ⟨NG.rt L n κ (a : GAf L n → W), hS κ _ a.2⟩ = T a := Subtype.ext (e.trans hTa.symm)
    exact congrArg Subtype.val (T.injective e2)

end Fixed

end GlobalTheory.AutUnr

namespace GlobalTheory.AutUnr

theorem mem_placesOver_of_overPl {D : D7} {p : ℕ} {w w' : PlE D.host}
    {v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E))} (hw : NG.OverPl w v) (hw' : NG.OverPl w' v)
    (h : w' ∈ placesOver D.host.E p) : w ∈ placesOver D.host.E p := by
  have h1 : ((p : ℕ) : 𝓞 (maximalRealSubfield D.host.E)) ∈ v.asIdeal := by
    rw [← hw', Ideal.mem_comap, map_natCast]; exact h
  rw [← hw, Ideal.mem_comap, map_natCast] at h1
  exact h1

theorem exists_splitPlace_eq (D : D7) (w : PlE D.host) (hw : IsSplitPl D.host w) :
    ∃ s : SplitPlace D.host.E, s.w = w := by
  obtain ⟨s, -, h, -⟩ := GlobalTheory.SplitConjPlace.splitEx_all D w hw
  refine ⟨GlobalTheory.SplitConjPlace.conjSP s, HeightOneSpectrum.ext (Ideal.ext fun x => ?_)⟩
  rw [GlobalTheory.SplitConjPlace.mem_conj_w]
  refine (h x _ ?_).symm
  rw [IsCMField.coe_ringOfIntegersComplexConj]
  exact D.host.φ₀.injective (by
    rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply])


end GlobalTheory.AutUnr
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelFrameCharacterMulMovedPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelFrameCharacterMulMovedPoint
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TopCh

theorem toGLm_entry {E : Type} [Field E] {n : ℕ} (f : Sp E n ≃ₗ[E] Sp E n) (i j : Fin n) :
    ((toGLm E n f : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i j = f (Pi.single j 1) i := by
  simp [toGLm, Matrix.GeneralLinearGroup.toLin, LinearMap.GeneralLinearGroup.generalLinearEquiv]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {n : ℕ}
  {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))}

theorem localComponent_eq_frame {hc : CMData F E} {g : GL (Fin n) (AfE F E)} {p : DecoF E n ST SG Q} (h : IsPtOf hc g p) (P : Q) :
    rhoP F P.1 g = Formalism.UG.bc (algebraMap E (P.1.adicCompletion E)) (toGLm E n (p.fr P)) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  show adAt F P.1 ((g : Matrix (Fin n) (Fin n) (AfE F E)) i j) = algebraMap E _ (((toGLm E n (p.fr P) : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i j)
  rw [h.fr P i j, toGLm_entry]

theorem rhoT_eq_iota {hc : CMData F E} {k t y x : GL (Fin n) (AfE F E)} {p : DecoF E n ST SG Q} (h : GLG (E := E) (n := n) (SG := SG)) (θ : GLQ E n Q)
    (hk : ∀ P : Q, rhoP F P.1 k = 1) (h1 : IsPtOf hc (y * (k * t)) p)
    (h2 : IsPtOf hc (y * x * (k * t)) (((1, h, θ) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) • p)) (P : Q) :
    rhoT F P.1 t x = iotaP P.1 ((θ P)⁻¹) := by
  have e0 : rhoT F P.1 t x = (rhoP F P.1 (y * (k * t)))⁻¹ * rhoP F P.1 (y * x * (k * t)) := by
    rw [← map_inv, ← map_mul, show (y * (k * t))⁻¹ * (y * x * (k * t)) = t⁻¹ * (k⁻¹ * (x * k)) * t by group,
      map_mul, map_mul, map_mul, map_mul, map_inv (rhoP F P.1) k, hk P, inv_one, one_mul, mul_one]
    simp [rhoT]
  rw [e0, localComponent_eq_frame h1 P, localComponent_eq_frame h2 P]
  show _ * Formalism.UG.bc _ (toGLm E n ((1 : Sp E n ≃ₗ[E] Sp E n) * p.fr P * ((θ P)⁻¹).1)) = _
  rw [one_mul, map_mul, map_mul, inv_mul_cancel_left]
  rfl

theorem topChi_eq {K : Type} [Field K] (σ : K →+* ℂ) (U : Subgroup (GL (Fin n) (AfE F E))) (t : GL (Fin n) (AfE F E))
    (Θ : LevQFam E K n Q) (d : Q → E) (hd : ∀ P, d P ≠ 0) (N : Q → ℕ)
    (hdN : ∀ P : Q, P.1.valuation E (d P) ≤ WithZero.exp (-(N P : ℤ)))
    (hΘ : ∀ (P : Q) (g : ↥(GLint E n P.1)), lqPrinc P.1 (N P) (g : Sp E n ≃ₗ[E] Sp E n) → ∃ h : g ∈ (Θ P).H, (Θ P).lam ⟨g, h⟩ = 1)
    (x : topU U t Θ d) (θ : Θ.grp) (hx : ∀ P : Q, rhoT F P.1 t x.1 = iotaP P.1 ((θ.1 P)⁻¹)) :
    topChi σ U t Θ d hd N hdN hΘ x = Units.map (σ : K →* ℂ) (Θ.chr θ) := by
  have hθ : ∀ P : Q, θ.1 P ∈ (Θ P).H := fun P => θ.2 P (Set.mem_univ P)
  have key : ∀ P : Q, locChr P.1 (Θ P) (d P) (hd P) (hdN P) (hΘ P) ⟨rhoT F P.1 t x.1, rhoT_mem x.2 P⟩ =
      ((Θ P).lam ⟨θ.1 P, hθ P⟩)⁻¹ := by
    intro P
    have mem : iotaP P.1 ((θ.1 P)⁻¹) ∈ locLev P.1 (Θ P) (d P) := hx P ▸ rhoT_mem x.2 P
    have e : (⟨rhoT F P.1 t x.1, rhoT_mem x.2 P⟩ : locLev P.1 (Θ P) (d P)) = ⟨iotaP P.1 ((θ.1 P)⁻¹), mem⟩ := Subtype.ext (hx P)
    rw [e, ← map_inv]
    exact qbChr_rat (F := E) P.1 (algebraMap E (P.1.adicCompletion E)) (phi_int P.1) (phi_lt P.1) (Θ P) (d P) (hd P) (hdN P) (hΘ P)
      ((θ.1 P)⁻¹) (inv_mem (hθ P)) mem
  have ec : Θ.chr θ = ∏ P : Q, (Θ P).lam ⟨θ.1 P, hθ P⟩ := by
    unfold LevQFam.chr piChar
    exact MonoidHom.finsetProd_apply (M := ↥(Subgroup.pi Set.univ fun P : Q => (Θ P).H)) _ _ _
  unfold topChi
  rw [MonoidHom.inv_apply, MonoidHom.finsetProd_apply, ec, map_prod, ← _root_.inv_inj, inv_inv, ← Finset.prod_inv_distrib]
  refine Finset.prod_congr rfl fun P _ => ?_
  show Units.map (σ : K →* ℂ) (locChr P.1 (Θ P) (d P) (hd P) (hdN P) (hΘ P) ⟨rhoT F P.1 t x.1, rhoT_mem x.2 P⟩) = _
  rw [key, map_inv]

theorem chi_eq_of_J0 {K : Type} [Field K] [NeZero n] {hc : CMData F E} (Λ : LevFam E K n SG) (σ : K →+* ℂ)
    {U : Subgroup (GL (Fin n) (AfE F E))} (χ : U →* ℂˣ) {k t : GL (Fin n) (AfE F E)} (ht : t ∈ K1 hc n ST SG)
    (hχ : ∀ (x : U) (z : J0 hc n ST) (h : Λ.grp), z.1 = k⁻¹ * x.1 * k → redG hc n ST SG z = h.1⁻¹ →
      χ x = Units.map (σ : K →* ℂ) (Λ.chr h))
    (x : U) (h : Λ.grp) (hz : (k * t)⁻¹ * x.1 * (k * t) ∈ J0 hc n ST) (hr : redG hc n ST SG ⟨_, hz⟩ = h.1⁻¹) :
    χ x = Units.map (σ : K →* ℂ) (Λ.chr h) := by
  obtain ⟨t', ht', rfl⟩ := Subgroup.mem_map.1 ht
  refine hχ x (t' * ⟨_, hz⟩ * t'⁻¹) h ?_ ?_
  · show t'.1 * ((k * t'.1)⁻¹ * x.1 * (k * t'.1)) * t'.1⁻¹ = _
    group
  · rw [map_mul, map_mul, map_inv, MonoidHom.mem_ker.1 ht', hr, one_mul, inv_one, mul_one]

theorem chr_of_J0 {K : Type} [Field K] [NeZero n] (hc : CMData F E) (Λ : LevFam E K n SG) (Θ : LevQFam E K n Q) (d : Q → E)
    (hd : ∀ P, d P ≠ 0) (N : Q → ℕ) (hdN : ∀ P : Q, P.1.valuation E (d P) ≤ WithZero.exp (-(N P : ℤ)))
    (hΘ : ∀ (P : Q) (g : ↥(GLint E n P.1)), lqPrinc P.1 (N P) (g : Sp E n ≃ₗ[E] Sp E n) → ∃ h : g ∈ (Θ P).H, (Θ P).lam ⟨g, h⟩ = 1)
    (σ : K →+* ℂ) (U : Subgroup (GL (Fin n) (AfE F E))) (χ : U →* ℂˣ) (k t y : GL (Fin n) (AfE F E)) (p : DecoF E n ST SG Q)
    (hk : ∀ P : Q, rhoP F P.1 k = 1) (ht : t ∈ K1 hc n ST SG)
    (hχ : ∀ (x : U) (z : J0 hc n ST) (h : Λ.grp), z.1 = k⁻¹ * x.1 * k → redG hc n ST SG z = h.1⁻¹ →
      χ x = Units.map (σ : K →* ℂ) (Λ.chr h))
    (x : topU U t Θ d) (h : Λ.grp) (θ : Θ.grp) (h1 : IsPtOf hc (y * (k * t)) p)
    (h2 : IsPtOf hc (y * x.1 * (k * t)) (((1, h.1, θ.1) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) • p))
    (hz : (k * t)⁻¹ * x.1 * (k * t) ∈ J0 hc n ST) (hr : redG hc n ST SG ⟨_, hz⟩ = h.1⁻¹) :
    χ ⟨x.1, topU_le _ _ _ _ x.2⟩ * topChi σ U t Θ d hd N hdN hΘ x = Units.map (σ : K →* ℂ) (Λ.chr h * Θ.chr θ) := by
  rw [chi_eq_of_J0 Λ σ χ ht hχ ⟨x.1, topU_le _ _ _ _ x.2⟩ h hz hr,
    topChi_eq σ U t Θ d hd N hdN hΘ x θ fun P => rhoT_eq_iota h.1 θ.1 hk h1 h2 P, map_mul]

theorem chi_mul_topChi_moved : ∀ (F E K : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] [Field K] (hc : CMData F E) (n : ℕ) [NeZero n] (ST SG Q : Finset (HeightOneSpectrum (𝓞 E))) (Λ : LevFam E K n SG) (Θ : LevQFam E K n Q) (d : Q → E) (hd : ∀ P, d P ≠ 0) (N : Q → ℕ) (hdN : ∀ P : Q, P.1.valuation E (d P) ≤ WithZero.exp (-(N P : ℤ))) (hΘ : ∀ (P : Q) (g : ↥(GLint E n P.1)), lqPrinc P.1 (N P) (g : Sp E n ≃ₗ[E] Sp E n) → ∃ h : g ∈ (Θ P).H, (Θ P).lam ⟨g, h⟩ = 1) (σ : K →+* ℂ) (U : Subgroup (GL (Fin n) (AfE F E))) (χ : U →* ℂˣ) (k t y : GL (Fin n) (AfE F E)) (p : DecoF E n ST SG Q), k ∈ UAd hc n → (∀ P : Q, rhoP F P.1 k = 1) → t ∈ K1 hc n ST SG → (∀ (x : U) (z : J0 hc n ST) (h : Λ.grp), z.1 = k⁻¹ * x.1 * k → redG hc n ST SG z = h.1⁻¹ → χ x = Units.map (σ : K →* ℂ) (Λ.chr h)) → ∀ (x : topU U t Θ d) (h : Λ.grp) (θ : Θ.grp), IsPtOf hc (y * (k * t)) p → IsPtOf hc (y * x.1 * (k * t)) (((1, h.1, θ.1) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) • p) → χ ⟨x.1, topU_le _ _ _ _ x.2⟩ * topChi σ U t Θ d hd N hdN hΘ x = Units.map (σ : K →* ℂ) (Λ.chr h * Θ.chr θ) := by
  intro F E K _ _ _ _ _ _ _ hc n _ ST SG Q Λ Θ d hd N hdN hΘ σ U χ k t y p _ hk ht hχ x h θ h1 h2
  have e : y * (k * t) * ((k * t)⁻¹ * x.1 * (k * t)) = y * x.1 * (k * t) := by group
  obtain ⟨hz, hr⟩ := ((isPtOf_mul_J0 F E hc n ST SG Q (y * (k * t)) ((k * t)⁻¹ * x.1 * (k * t)) p
    (((1, h.1, θ.1) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) • p) h.1).1 h1 (e ▸ h2)).2 rfl
  exact chr_of_J0 hc Λ Θ d hd N hdN hΘ σ U χ k t y p hk ht hχ x h θ h1 h2 hz hr

end GlobalTheory.Mem.Col2.TopCh

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelFrameCharacterMulMovedPointStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelFrameCharacter_mul_movedPoint : ∀ (F E K : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] [Field K] (hc : CMData F E) (n : ℕ) [NeZero n] (ST SG Q : Finset (HeightOneSpectrum (𝓞 E))) (Λ : LevFam E K n SG) (Θ : LevQFam E K n Q) (d : Q → E) (hd : ∀ P, d P ≠ 0) (N : Q → ℕ) (hdN : ∀ P : Q, P.1.valuation E (d P) ≤ WithZero.exp (-(N P : ℤ))) (hΘ : ∀ (P : Q) (g : ↥(GLint E n P.1)), lqPrinc P.1 (N P) (g : Sp E n ≃ₗ[E] Sp E n) → ∃ h : g ∈ (Θ P).H, (Θ P).lam ⟨g, h⟩ = 1) (σ : K →+* ℂ) (U : Subgroup (GL (Fin n) (AfE F E))) (χ : U →* ℂˣ) (k t y : GL (Fin n) (AfE F E)) (p : DecoF E n ST SG Q), k ∈ UAd hc n → (∀ P : Q, rhoP F P.1 k = 1) → t ∈ K1 hc n ST SG → (∀ (x : U) (z : J0 hc n ST) (h : Λ.grp), z.1 = k⁻¹ * x.1 * k → redG hc n ST SG z = h.1⁻¹ → χ x = Units.map (σ : K →* ℂ) (Λ.chr h)) → ∀ (x : topU U t Θ d) (h : Λ.grp) (θ : Θ.grp), IsPtOf hc (y * (k * t)) p → IsPtOf hc (y * x.1 * (k * t)) (((1, h.1, θ.1) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) • p) → χ ⟨x.1, topU_le _ _ _ _ x.2⟩ * topChi σ U t Θ d hd N hdN hΘ x = Units.map (σ : K →* ℂ) (Λ.chr h * Θ.chr θ) := by
  first | exact @GlobalTheory.Mem.Col2.TopCh.chi_mul_topChi_moved | exact GlobalTheory.Mem.Col2.TopCh.chi_mul_topChi_moved | (intros; apply GlobalTheory.Mem.Col2.TopCh.chi_mul_topChi_moved <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitarySatakeInvariantAntidiagTransport
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitarySatakeInvariantAntidiagTransport
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial Formalism.UG GlobalTheory.SatInd

noncomputable section

namespace GlobalTheory.SatInd

section Transport

variable {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))]

theorem bc_mem_range_intL_of (φ : K →+* K) (hφ : ∀ x ∈ intL K, φ x ∈ intL K) {n : ℕ}
    (x : GL (Fin n) K) (hx : x ∈ (bc (n := Fin n) (intL K).subtype).range) :
    bc (n := Fin n) φ x ∈ (bc (n := Fin n) (intL K).subtype).range := by
  obtain ⟨M, rfl⟩ := hx
  refine ⟨bc (φ.restrict (intL K) (intL K) hφ) M, ?_⟩
  apply Units.ext
  ext i j
  simp [bc]

theorem guMap_symm_comp (g : K ≃+* K) {σ σ' : K →+* K} (hg : ∀ x, g (σ x) = σ' (g x))
    (hg' : ∀ x, g.symm (σ' x) = σ (g.symm x)) {n : ℕ} (y : GU σ n) :
    guMap g.symm hg' n (guMap g hg n y) = y := by
  apply Subtype.ext
  apply Units.ext
  ext i j
  simp [guMap_val]

theorem mem_KU_iff_guMap (g : K ≃+* K) {σ σ' : K →+* K} (hg : ∀ x, g (σ x) = σ' (g x))
    (hint : ∀ x, x ∈ intL K ↔ g x ∈ intL K) {n : ℕ} (y : GU σ n) :
    y ∈ KU σ n ↔ guMap g hg n y ∈ KU σ' n := by
  have hs : ∀ x ∈ intL K, (g.symm : K →+* K) x ∈ intL K := by
    intro x hx
    rw [hint]
    simpa using hx
  simp only [KU, intPts, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  constructor
  · rintro ⟨-, h⟩
    exact ⟨(guMap g hg n y).2, bc_mem_range_intL_of (g : K →+* K) (fun x hx => (hint x).1 hx) _ h⟩
  · rintro ⟨-, h⟩
    refine ⟨y.2, ?_⟩
    have := bc_mem_range_intL_of (g.symm : K →+* K) hs _ h
    convert this using 1
    apply Units.ext
    ext i j
    simp [bc, guMap_val]

end Transport


open Classical in
theorem satU_guMap : ∀ {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))] (g : K ≃+* K) {σ σ' : K →+* K} (hg : ∀ x, g (σ x) = σ' (g x)), (∀ x, x ∈ intL K ↔ g x ∈ intL K) → ∀ (ϖ ϖ' : K) (q n m : ℕ) (h' : GU σ' n → ℂ), IsBiInv (KU σ' n) h' → (∀ (a : Fin m → ℤ) (y : GU σ n), (∃ u : GU σ n, IsUnipU u ∧ ∃ k ∈ KU σ n, ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = tMat ϖ n m a * ((u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * ((k : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) ↔ (∃ u : GU σ' n, IsUnipU u ∧ ∃ k ∈ KU σ' n, ((guMap g hg n y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = tMat ϖ' n m a * ((u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * ((k : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) → ∀ α : Fin m → ℂ, SatU ϖ q (fun y => h' (guMap g hg n y)) α = SatU ϖ' q h' α := by
  intro K _ _ g σ σ' hg hint ϖ ϖ' q n m h' hbi hcond α
  have hg' : ∀ x, g.symm (σ' x) = σ (g.symm x) := by
    intro x
    apply g.injective
    rw [hg]
    simp
  let e : GU σ n ≃* GU σ' n :=
    { toFun := guMap g hg n
      invFun := guMap g.symm hg' n
      left_inv := fun y => guMap_symm_comp g hg hg' y
      right_inv := fun y => by
        have := guMap_symm_comp g.symm hg' (by simpa using hg) y
        simpa using this
      map_mul' := map_mul _ }
  have he : ∀ y, e y = guMap g hg n y := fun _ => rfl
  let E : GU σ n ⧸ KU σ n ≃ GU σ' n ⧸ KU σ' n :=
    Quotient.congr e.toEquiv (fun a b => by
      rw [QuotientGroup.leftRel_apply, QuotientGroup.leftRel_apply]
      change a⁻¹ * b ∈ KU σ n ↔ (e a)⁻¹ * e b ∈ KU σ' n
      rw [← map_inv, ← map_mul, he]
      exact mem_KU_iff_guMap g hg hint _)
  unfold SatU
  refine finsum_congr (fun a => ?_)
  congr 1
  set F' : GU σ' n → ℂ := fun y => if ∃ u : GU σ' n, IsUnipU u ∧ ∃ k ∈ KU σ' n,
      ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        tMat ϖ' n m a * ((u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          ((k : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) then h' y else 0 with hF'
  have hinv : ∀ (y : GU σ' n) (k : KU σ' n), F' (y * k) = F' y := by
    intro y k
    simp only [hF']
    have hc : (∃ u : GU σ' n, IsUnipU u ∧ ∃ k' ∈ KU σ' n,
        (((y * k : GU σ' n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
          tMat ϖ' n m a * ((u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
            ((k' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) ↔
        (∃ u : GU σ' n, IsUnipU u ∧ ∃ k' ∈ KU σ' n,
        ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
          tMat ϖ' n m a * ((u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
            ((k' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
      constructor
      · rintro ⟨u, hu, k', hk', hy⟩
        refine ⟨u, hu, k' * (k : GU σ' n)⁻¹, (KU σ' n).mul_mem hk' ((KU σ' n).inv_mem k.2), ?_⟩
        have h1 : ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
            (((y * k : GU σ' n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
              ((((k : GU σ' n)⁻¹ : GU σ' n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
          simp [Matrix.mul_assoc]
        rw [h1, hy]
        simp [Matrix.mul_assoc]
      · rintro ⟨u, hu, k', hk', hy⟩
        refine ⟨u, hu, k' * (k : GU σ' n), (KU σ' n).mul_mem hk' k.2, ?_⟩
        simp only [Subgroup.coe_mul, Units.val_mul, hy, Matrix.mul_assoc]
    have hh : h' (y * k) = h' y := by
      have := hbi 1 k y
      simpa using this
    simp only [hc, hh]
  have hmk : ∀ x : GU σ n ⧸ KU σ n, F' (E x).out = F' (guMap g hg n x.out) := by
    intro x
    have hx : E x = QuotientGroup.mk (guMap g hg n x.out) := by
      conv_lhs => rw [← Quotient.out_eq x]
      rfl
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (KU σ' n) (guMap g hg n x.out)
    rw [hx, hk, hinv]
  calc (∑ᶠ x : GU σ n ⧸ KU σ n, if ∃ u : GU σ n, IsUnipU u ∧ ∃ k ∈ KU σ n,
          (((x.out : GU σ n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
            tMat ϖ n m a * (((u : GU σ n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
              (((k : GU σ n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
        then h' (guMap g hg n x.out) else 0)
      = ∑ᶠ x : GU σ n ⧸ KU σ n, F' (E x).out := by
        refine finsum_congr (fun x => ?_)
        rw [hmk, hF']
        simp only [hcond a x.out]
    _ = ∑ᶠ x' : GU σ' n ⧸ KU σ' n, F' x'.out := finsum_comp_equiv E (f := fun x' => F' x'.out)

end GlobalTheory.SatInd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitarySatakeInvariantAntidiagTransportStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial Formalism.UG GlobalTheory.SatInd
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitarySatake_invariant_antidiagTransport : ∀ {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))] (g : K ≃+* K) {σ σ' : K →+* K} (hg : ∀ x, g (σ x) = σ' (g x)), (∀ x, x ∈ intL K ↔ g x ∈ intL K) → ∀ (ϖ ϖ' : K) (q n m : ℕ) (h' : GU σ' n → ℂ), IsBiInv (KU σ' n) h' → (∀ (a : Fin m → ℤ) (y : GU σ n), (∃ u : GU σ n, IsUnipU u ∧ ∃ k ∈ KU σ n, ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = tMat ϖ n m a * ((u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * ((k : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) ↔ (∃ u : GU σ' n, IsUnipU u ∧ ∃ k ∈ KU σ' n, ((guMap g hg n y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = tMat ϖ' n m a * ((u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * ((k : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) → ∀ α : Fin m → ℂ, SatU ϖ q (fun y => h' (guMap g hg n y)) α = SatU ϖ' q h' α := by
  first | exact @GlobalTheory.SatInd.satU_guMap | exact GlobalTheory.SatInd.satU_guMap | (intros; apply GlobalTheory.SatInd.satU_guMap <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SymAllowed
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.GroupLoc

variable {D : D7}

def ModW (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) (S : Set (VA X.B.I)) (y : VA X.B.I) : Prop :=
  y ∈ Submodule.span (Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E) S ⊔ wLf X w

def CondAt (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) (x : X.B.I.Gf) : Prop :=
  (∀ a : Fin D.R.rS, ModW X w (X.e0 '' {b | b.1 < a.1}) ((X.B.I.fmat x - 1) *ᵥ X.e0 a)) ∧
    ModW X w (Set.range X.e0) ((X.B.I.fmat x - 1) *ᵥ X.z0) ∧
    ∀ i : Fin D.R.k, ModW X w (Set.range X.e0 ∪ X.bw '' {j | j.1 < i.1}) ((X.B.I.fmat x - 1) *ᵥ X.bw i)

def symAllowed (ρ k : ℕ) {r : ℕ} (i j : Fin r) : Prop :=
  j.1 < i.1 ∧ ¬ (ρ ≤ j.1 ∧ j.1 < ρ + k ∧ i.1 = ρ + k)

def ColCond (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) (x : X.B.I.Gf) : Prop :=
  ∀ i : Fin D.R.r, ModW X w (GlobalTheory.Mem.SymFrame.symVec X w '' {j | symAllowed D.R.rS D.R.k i j})
    ((X.B.I.fmat x - 1) *ᵥ GlobalTheory.Mem.SymFrame.symVec X w i)

end GlobalTheory.Mem.GroupLoc

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConjugateSplitPlaceAndUniformizer
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConjugateSplitPlaceAndUniformizer
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN

namespace GlobalTheory.SplitExConj

theorem exists_splitPlace_conj_unif : ∀ (D : D7), (∀ v : PlE D.host, IsSplitPl D.host v → ∃ (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), IsConjPl D.host v s.w ∧ IsUnif D.host.E s.v ϖ) :=
  fun D => GlobalTheory.SplitConjPlace.splitEx_all D

end GlobalTheory.SplitExConj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConjugateSplitPlaceAndUniformizerStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_conjugate_splitPlace_and_uniformizer : ∀ (D : D7), (∀ v : PlE D.host, IsSplitPl D.host v → ∃ (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), IsConjPl D.host v s.w ∧ IsUnif D.host.E s.v ϖ) := by
  first | exact @GlobalTheory.SplitExConj.exists_splitPlace_conj_unif | exact GlobalTheory.SplitExConj.exists_splitPlace_conj_unif | (intros; apply GlobalTheory.SplitExConj.exists_splitPlace_conj_unif <;> assumption)
end
end
