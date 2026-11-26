module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertOfUnramifiedIsometricInvolution
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NVNeZero
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MeanLogSupNormLowerBoundCmFrameNonvanishing

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftPRouteSmall
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section
namespace GlobalTheory.SmallRoute

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

def outer (W : G.Weil) (M : Vol G) {t : T} {i j : ℕ} (d : PureT G (routeSmall t i j)) (F : Fn G (.grid i (j + 1)))
    (g₁ : GA D (G.V (.grid (i + 1) j))) : Fn G (.grid i j) := fun u =>
  W.kerA (.right i j) d.2 u g₁ * ∫ g in M.fd (.grid i (j + 1)), W.kerA (.down t i j) d.1.2 g u * F g ∂M.ν (.grid i (j + 1))

theorem liftT_routeSmall (W : G.Weil) (M : Vol G) {t : T} {i j : ℕ} (τ : TotT G (routeSmall t i j))
    (F : Fn G (.grid i (j + 1))) (g₁ : GA D (G.V (.grid (i + 1) j))) :
    liftT W M (routeSmall t i j) τ F g₁ = τ.sum fun d c => c * ∫ u in M.fd (.grid i j), outer W M d F g₁ u ∂M.ν (.grid i j) := by
  simp only [liftT, Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rfl

end GlobalTheory.SmallRoute
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceConjugationPropertiesCmField
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceConjugationPropertiesCmField
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct

noncomputable section

namespace GlobalTheory.ConjAtPlace

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem tendsto_pow_of_lt_one {w : HeightOneSpectrum (𝓞 E)} (x : w.adicCompletion E) (h : Valued.v x < 1) :
    Tendsto (fun n : ℕ => x ^ n) atTop (nhds 0) := by
  rw [(Valued.hasBasis_nhds_zero _ _).tendsto_right_iff]
  intro γ _
  have hne : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 ≠ 0 := by simp
  obtain ⟨n, hn⟩ := exists_pow_lt₀ h (Units.mk0 _ hne)
  filter_upwards [eventually_ge_atTop n] with m hm
  rw [Valuation.restrict_lt_iff_lt_embedding, map_pow]
  exact lt_of_le_of_lt (pow_le_pow_right_of_le_one' h.le hm) hn

theorem lt_one_of_continuous {w : HeightOneSpectrum (𝓞 E)} (s : w.adicCompletion E →+* w.adicCompletion E)
    (hs : Continuous s) {z : w.adicCompletion E} (hz : Valued.v z < 1) : Valued.v (s z) < 1 := by
  have h1 : Tendsto (fun n : ℕ => s z ^ n) atTop (nhds 0) := by
    have := (hs.tendsto 0).comp (tendsto_pow_of_lt_one z hz)
    simpa [Function.comp_def, map_pow] using this
  have hU : {y : w.adicCompletion E | Valued.v y < 1} ∈ nhds (0 : w.adicCompletion E) :=
    Valued.mem_nhds_zero.2 ⟨1, fun y hy => by simpa using hy⟩
  obtain ⟨N, hN⟩ := (h1.eventually hU).exists
  by_contra hc
  rw [not_lt] at hc
  rw [map_pow] at hN
  exact absurd hN (not_lt.2 (one_le_pow₀ hc))

theorem conjSrc_eq_of_cont (w : HeightOneSpectrum (𝓞 E)) (s : w.adicCompletion E →+* w.adicCompletion E)
    (hs : Continuous s)
    (he : ∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x)) :
    conjSrc (GlobalTheory.SplitPts.conjE E) w = w := by
  have hval : ∀ a : 𝓞 E, Valued.v (algebraMap E (w.adicCompletion E) (a : E)) =
      w.valuation E (algebraMap (𝓞 E) E a) := fun a =>
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _
  have hmem : ∀ a : 𝓞 E, a ∈ w.asIdeal ↔ Valued.v (algebraMap E (w.adicCompletion E) (a : E)) < 1 := by
    intro a
    rw [hval, HeightOneSpectrum.valuation_lt_one_iff_mem]
  have hdir : ∀ x y : 𝓞 E, (y : E) = IsCMField.complexConj E (x : E) → x ∈ w.asIdeal → y ∈ w.asIdeal := by
    intro x y hxy hx
    rw [hmem] at hx ⊢
    rw [hxy, ← he]
    exact lt_one_of_continuous s hs hx
  have hc : GlobalTheory.Mem.Chr.ConjPl (GlobalTheory.SplitPts.conjE E) w w := by
    rw [GlobalTheory.Mem.Chr.conjPl_iff_mem]
    intro x y hxy
    refine ⟨hdir x y hxy, hdir y x ?_⟩
    rw [show (GlobalTheory.SplitPts.conjE E) (x : E) = IsCMField.complexConj E (x : E) from rfl] at hxy
    rw [hxy, IsCMField.complexConj_apply_apply]
  exact (eq_conjSrc hc).symm

theorem conjSrc_eq_iff (w : HeightOneSpectrum (𝓞 E)) :
    conjSrc (GlobalTheory.SplitPts.conjE E) w = w ↔ ¬ IsSplitAt w := by
  refine ⟨fun h hs => (GlobalTheory.SplitPts.over_split hs).1 h, fun h => ?_⟩
  by_contra hne
  apply h
  exact ⟨conjSrc (GlobalTheory.SplitPts.conjE E) w, hne,
    (GlobalTheory.Mem.Chr.under_eq_iff_conjPl (IsCMField.complexConj E)
      (Algebra.IsQuadraticExtension.finrank_eq_two _ _) (IsCMField.complexConj_ne_one E) w _).2
      (Or.inr (GlobalTheory.SplitPts.conjPl_self_conjSrc w))⟩

theorem ext_of_cont {v w : HeightOneSpectrum (𝓞 E)} (s t : v.adicCompletion E →+* w.adicCompletion E)
    (hs : Continuous s) (ht : Continuous t)
    (hse : ∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x))
    (hte : ∀ x : E, t (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x)) : s = t :=
  RingHom.ext fun y => congrFun ((HeightOneSpectrum.denseRange_algebraMap (K := E) v).equalizer hs ht
    (funext fun k => (hse k).trans (hte k).symm)) y

theorem cont_of_val {w : HeightOneSpectrum (𝓞 E)} (s : w.adicCompletion E →+* w.adicCompletion E)
    (hv : ∀ x, Valued.v (s x) = Valued.v x) : Continuous s :=
  GlobalTheory.Mem.Chr.continuous_of_valued_eq (HeightOneSpectrum.valuedAdicCompletion_surjective E w) s hv

theorem cj_spec (w : Pl E)
    (h : ∃ s : w.adicCompletion E →+* w.adicCompletion E, Continuous s ∧
      ∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x)) :
    Continuous (cj w) ∧ ∀ x : E, cj w (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x) := by
  unfold cj
  rw [dite_eq_left h]
  exact h.choose_spec

theorem cj_of_not (w : Pl E)
    (h : ¬ ∃ s : w.adicCompletion E →+* w.adicCompletion E, Continuous s ∧
      ∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x)) :
    cj w = RingHom.id _ := by
  unfold cj
  rw [dite_eq_right h]

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ w : Pl E, Continuous (cj w) ∧ (∀ x, cj w (cj w x) = x) ∧ (∀ x, Valued.v (cj w x) = Valued.v x) ∧ (¬ IsSplitAt w → (∀ x : E, cj w (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x)) ∧ (∃ ϖ q, IsUnramInv ϖ (cj w) q ∧ qV E w = q ^ 2) ∧ (∀ x : Af E, pLoc E w (conjFin (IsCMField.complexConj E).toRingEquiv x) = cj w (pLoc E w x)) ∧ ∀ (s : w.adicCompletion E →+* w.adicCompletion E), (∀ x, Valued.v (s x) = Valued.v x) → (∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x)) → s = cj w) ∧ ∀ (s : w.adicCompletion E →+* w.adicCompletion E), (∀ x, Valued.v (s x) = Valued.v x) → (∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x)) → ¬ IsSplitAt w := by
  intro E _ _ _ hU w
  by_cases hsp : IsSplitAt w
  · have hno : ¬ ∃ s : w.adicCompletion E →+* w.adicCompletion E, Continuous s ∧
        ∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x) := by
      rintro ⟨s, hs, he⟩
      exact (GlobalTheory.SplitPts.over_split hsp).1 (conjSrc_eq_of_cont w s hs he)
    have hid := cj_of_not w hno
    refine ⟨by rw [hid]; exact continuous_id, fun x => by rw [hid]; rfl, fun x => by rw [hid]; rfl,
      fun h => absurd hsp h, fun s hv he _ => hno ⟨s, cont_of_val s hv, he⟩⟩
  · obtain ⟨s0, ϖ, q, he0, hU0⟩ := GlobalTheory.InertPlaceConj.exists_conj_isUnramInv E w (hU w) hsp
    have hc0 : Continuous s0 := cont_of_val s0 hU0.2.1
    obtain ⟨hcj, hecj⟩ := cj_spec w ⟨s0, hc0, he0⟩
    have heq : cj w = s0 := ext_of_cont _ _ hcj hc0 hecj he0
    have hsrc : conjSrc (GlobalTheory.SplitPts.conjE E) w = w := (conjSrc_eq_iff w).2 hsp
    refine ⟨hcj, fun x => by rw [heq]; exact hU0.1 x, fun x => by rw [heq]; exact hU0.2.1 x,
      fun _ => ⟨hecj, ⟨ϖ, q, by rw [heq]; exact hU0, ?_⟩, fun x => ?_,
        fun s hv he => ext_of_cont _ _ (cont_of_val s hv) hcj he hecj⟩, fun _ _ _ => hsp⟩
    · exact (Formalism.UG.P.tjcosets_card_residue w).symm.trans hU0.2.2.2.2.2.2
    · rw [pLoc_conjFin]
      have key : ∀ (v : HeightOneSpectrum (𝓞 E)) (_ : v = w) (f : v.adicCompletion E →+* w.adicCompletion E),
          Continuous f → (∀ k : E, f (algebraMap E _ k) = algebraMap E _ (IsCMField.complexConj E k)) →
          f (pLoc E v x) = cj w (pLoc E w x) := by
        rintro v rfl f hf hfe
        rw [ext_of_cont f (cj v) hf hcj hfe hecj]
      exact key _ hsrc _ (conjLoc_spec _ w).1 (conjLoc_spec _ w).2.1

end GlobalTheory.ConjAtPlace
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceConjugationPropertiesCmFieldStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.placeConjugation_properties_cmField : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ w : Pl E, Continuous (cj w) ∧ (∀ x, cj w (cj w x) = x) ∧ (∀ x, Valued.v (cj w x) = Valued.v x) ∧ (¬ IsSplitAt w → (∀ x : E, cj w (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x)) ∧ (∃ ϖ q, IsUnramInv ϖ (cj w) q ∧ qV E w = q ^ 2) ∧ (∀ x : Af E, pLoc E w (conjFin (IsCMField.complexConj E).toRingEquiv x) = cj w (pLoc E w x)) ∧ ∀ (s : w.adicCompletion E →+* w.adicCompletion E), (∀ x, Valued.v (s x) = Valued.v x) → (∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x)) → s = cj w) ∧ ∀ (s : w.adicCompletion E →+* w.adicCompletion E), (∀ x, Valued.v (s x) = Valued.v x) → (∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x)) → ¬ IsSplitAt w := by
  first | exact @GlobalTheory.ConjAtPlace.main | exact GlobalTheory.ConjAtPlace.main | (intros; apply GlobalTheory.ConjAtPlace.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareStanding
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct

namespace GlobalTheory.FunObj

open GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

def SquareStanding (G : GridData L sc) (t : T) : Prop :=
  11 ≤ D.host.splitBound ∧
    ∀ w ∈ locPl G t, ((D.host.QS * D.host.q * D.host.d * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal

end GlobalTheory.FunObj

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetVecEq
noncomputable section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FunObj.SqNum

namespace GlobalTheory.FunObj.StdDatum

variable (D : D7)

def cosetV (δ : ℂ) (𝔪 : Ideal (𝓞 D.host.E)) (o a d : ℕ) (e0 : VC D a d → ℂ) : VC D a d → ℂ :=
  ((Real.sqrt ((Ideal.absNorm 𝔪 : ℝ) ^ (a * d)) : ℂ))⁻¹ •
    Wd D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ (unitBlock D o a d))
      (Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)) e0)

def congLev (𝔪 : Ideal (𝓞 D.host.E)) (N : ℕ) : Subgroup (GA D N) :=
  Subgroup.closure {k | k ∈ intG D N ∧ CongOne D 𝔪 k}

def blockLev (𝔪 : Ideal (𝓞 D.host.E)) (d a : ℕ) : Subgroup (GA D d) :=
  Subgroup.closure {h | h ∈ intG D d ∧ ∀ i j : Fin d, j.1 < a → a ≤ i.1 →
    ((h : GL (Fin d) (AE D)) : Matrix (Fin d) (Fin d) (AE D)) i j ∈ hatId D 𝔪}

variable {D}

def stdSum {δ : ℂ} {a d : ℕ} {e0 : VC D a d → ℂ} (W : WeilO D ⊤ δ a d e0) (𝔪 : Ideal (𝓞 D.host.E)) (o : ℕ)
    (R : Finset (GA D a)) : VC D a d → ℂ :=
  ∑ r ∈ R, W.Om r 1 (cosetV D δ 𝔪 o a d e0)

theorem congLev_le (𝔪 : Ideal (𝓞 D.host.E)) (N : ℕ) : congLev D 𝔪 N ≤ intG D N :=
  (Subgroup.closure_le _).2 fun _ h => h.1

theorem blockLev_le (𝔪 : Ideal (𝓞 D.host.E)) (d a : ℕ) : blockLev D 𝔪 d a ≤ intG D d :=
  (Subgroup.closure_le _).2 fun _ h => h.1

end GlobalTheory.FunObj.StdDatum

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StarMemAdelicSchwartzSpaceNumberField
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StarMemAdelicSchwartzSpaceNumberField
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.SchAConj

open GlobalTheory.WeilM
open scoped Classical

def conjSchwartz {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (f : SchwartzMap V ℂ) : SchwartzMap V ℂ where
  toFun x := star (f x)
  smooth' := Complex.conjLIE.toContinuousLinearEquiv.contDiff.comp f.smooth'
  decay' := by
    intro k n
    obtain ⟨C, hC⟩ := f.decay' k n
    refine ⟨C, fun x => ?_⟩
    have h := Complex.conjLIE.norm_iteratedFDeriv_comp_left (𝕜 := ℝ) (f : V → ℂ) x n
    have e : (fun x => star (f x)) = (Complex.conjLIE : ℂ → ℂ) ∘ (f : V → ℂ) := rfl
    show ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun x => star (f x)) x‖ ≤ C
    rw [e, h]
    exact hC x

theorem conjSchwartz_apply {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (f : SchwartzMap V ℂ) (x : V) :
    conjSchwartz f x = star (f x) := rfl

theorem star_mem_schA : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (Φ : (κ → AF F) → ℂ), Φ ∈ schA F κ → (fun x => star (Φ x)) ∈ schA F κ := by
  intro F _ _ κ _ Φ hΦ
  induction hΦ using Submodule.span_induction with
  | mem Ψ hΨ =>
    obtain ⟨f, g, hg, rfl⟩ := hΨ
    refine Submodule.subset_span ⟨conjSchwartz f, fun y => star (g y), ⟨hg.1.comp star, ?_⟩, ?_⟩
    · exact hg.2.comp_left (g := star) (star_zero ℂ)
    · funext x
      simp [pureA, conjSchwartz_apply, star_mul']
  | zero =>
    convert (schA F κ).zero_mem using 1
    funext x; simp
  | add Ψ Ψ' _ _ h h' =>
    have := (schA F κ).add_mem h h'
    convert this using 1
    funext x; simp [star_add]
  | smul c Ψ _ h =>
    have := (schA F κ).smul_mem (star c) h
    convert this using 1
    funext x; simp [star_mul']

end GlobalTheory.SchAConj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StarMemAdelicSchwartzSpaceNumberFieldStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.star_mem_adelicSchwartzSpaceNumberField : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (Φ : (κ → AF F) → ℂ), Φ ∈ schA F κ → (fun x => star (Φ x)) ∈ schA F κ := by
  first | exact @GlobalTheory.SchAConj.star_mem_schA | exact GlobalTheory.SchAConj.star_mem_schA | (intros; apply GlobalTheory.SchAConj.star_mem_schA <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalGLLocalComponentsEventuallySatake
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalGLLocalComponentsEventuallySatake
open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair

namespace GlobalTheory.CuspRep.UnrSat

theorem eventually_hasSatGL_locRep : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : CuspSub E a), ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∃ B, GlobalTheory.LFun.HasSatGL w (π.locRep w) B := by
  intro hF E _ _ _ a π
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 π.ne_bot
  filter_upwards [LocSph.eventually_mem ((π.cusp φ hφ).1.level.mem_nhds (by simp))] with w hw
  refine exists_hasSatGL_locRep hF E a π w
    ((Submodule.ne_bot_iff _).2 ⟨⟨φ, hφ⟩, ?_, fun e => h0 (congrArg Subtype.val e)⟩)
  refine GlobalTheory.LGrp.mem_fixed.2 fun k hk => Subtype.ext ?_
  obtain ⟨g, rfl⟩ := hk
  exact hw g

end GlobalTheory.CuspRep.UnrSat
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalGLLocalComponentsEventuallySatakeStatement
open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspidal_GL_local_components_eventually_satake : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : CuspSub E a), ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∃ B, GlobalTheory.LFun.HasSatGL w (π.locRep w) B := by
  first | exact @GlobalTheory.CuspRep.UnrSat.eventually_hasSatGL_locRep | exact GlobalTheory.CuspRep.UnrSat.eventually_hasSatGL_locRep | (intros; apply GlobalTheory.CuspRep.UnrSat.eventually_hasSatGL_locRep <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalCongruenceConjMemArithmeticGroup
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalCongruenceConjMemArithmeticGroup
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo
open scoped ENNReal
open IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RepConv

theorem hat_cong {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ} (L : Set (Fin n → E))
    (γ : Matrix (Fin n) (Fin n) E) (M : ℕ) (h : ∀ x ∈ L, ∃ y ∈ L, γ.mulVec x - x = M • y) :
    ∀ z ∈ GlobalTheory.AdLat.hat F L, ∃ y ∈ GlobalTheory.AdLat.hat F L,
      (γ.map (inclR (F := F) (FiniteAdeleRing (𝓞 F) F))).mulVec z - z = M • y := by
  intro z hz
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hz
    obtain ⟨y, hy, e⟩ := h x hx
    refine ⟨fun i => a ⊗ₜ y i, AddSubgroup.subset_closure ⟨a, ha, y, hy, rfl⟩, ?_⟩
    funext i
    have e1 := congrFun e i
    simp only [Pi.sub_apply, Pi.smul_apply] at e1 ⊢
    rw [← TensorProduct.tmul_smul, ← e1, TensorProduct.tmul_sub]
    congr 1
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [inclR]
  | zero => exact ⟨0, zero_mem _, by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨y, hy, e⟩ := ha
    obtain ⟨y', hy', e'⟩ := hb
    refine ⟨y + y', add_mem hy hy', ?_⟩
    rw [Matrix.mulVec_add, smul_add, ← e, ← e']
    abel
  | neg a _ ha =>
    obtain ⟨y, hy, e⟩ := ha
    refine ⟨-y, neg_mem hy, ?_⟩
    rw [Matrix.mulVec_neg, smul_neg, ← e]
    abel

theorem archM_mul' {D : D7} (V : HSp D) (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (a b : GA D V) :
    archM V θ (a * b) = archM V θ a * archM V θ b := by
  unfold archM
  rw [map_mul, Units.val_mul, Matrix.map_mul]

theorem archM_one' {D : D7} (V : HSp D) (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) :
    archM V θ 1 = 1 := by
  unfold archM
  rw [map_one]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem exists_rat {D : D7} (V : HSp D) (γ' : GL (Fin V.rank) D.host.E)
    (h : ∀ x y, herm (-(V.gram)ᵀ) (γ'.1.mulVec x) (γ'.1.mulVec y) =
      herm (-(V.gram)ᵀ) x y) :
    ∃ γ₀ ∈ GQ V, (finHom V γ₀).1 = γ'.1.map (inclR (Af D.host.F)) ∧
      ∀ (τ : D.host.E →+* ℂ) (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ), Formalism.MainNotions.StandardLattice.IsInfEmb τ θ →
        archM V θ γ₀ = γ'.1.map τ := by
  have hU : γ' ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram := by
    show Formalism.UG.cT _ γ'.1 * V.gram * γ'.1 = V.gram
    refine Matrix.ext fun a b => ?_
    have := h (Pi.single b 1) (Pi.single a 1)
    have hc : ∀ x, cc x = (D.sp.cm.sig : D.host.E →+* D.host.E) x := fun _ => rfl
    simp only [herm, Matrix.mulVec_single_one, hc, Matrix.neg_apply, Matrix.transpose_apply, Matrix.col_apply] at this
    have h2 : ∑ x, ∑ y, (Pi.single b 1 : Fin V.rank → D.host.E) x * -V.gram y x *
        (D.sp.cm.sig : D.host.E →+* D.host.E) ((Pi.single a 1 : Fin V.rank → D.host.E) y) = -V.gram a b := by
      rw [Finset.sum_eq_single b, Finset.sum_eq_single a]
      · simp
      · intro j _ hj; simp [hj]
      · simp
      · intro j _ hj; simp [hj]
      · simp
    rw [h2] at this
    rw [← neg_inj, ← this]
    simp only [Matrix.mul_apply, Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul,
      ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hR : Formalism.UG.bc (inclR (AF D.host.F)) γ' ∈ HR (AF D.host.F) D.sp.cm.sig V.gram := by
    have hU' : Formalism.UG.cT _ γ'.1 * V.gram * γ'.1 = V.gram := hU
    have := congrArg (fun m => Matrix.map m (inclR (F := D.host.F) (AF D.host.F))) hU'
    simp only [Matrix.map_mul] at this
    rw [GlobalTheory.UnitaryGlue.cT_map (inclR (F := D.host.F) (AF D.host.F)) (D.sp.cm.sig : D.host.E →+* D.host.E)
      (sigR (AF D.host.F) D.sp.cm.sig) (fun _ => rfl)] at this
    exact this
  let γ₀ : GA D V := ⟨_, hR⟩
  have h1 : (matHom V γ₀).1 = γ'.1.map (inclR (AF D.host.F)) := rfl
  refine ⟨γ₀, Subgroup.mem_subgroupOf.2 ⟨γ', hU, rfl⟩, ?_, fun τ θ hθ => ?_⟩
  · rw [← GlobalTheory.UnitaryGlue.map_map_inclR (sndA D.host.F), ← h1]; rfl
  · have hinc : (γ'.1.map (inclR (Ainf D.host.F))).map θ = γ'.1.map τ := by
      ext i j
      exact hθ.1 _
    rw [← hinc, ← GlobalTheory.UnitaryGlue.map_map_inclR (fstA D.host.F), ← h1]; rfl

theorem map_eq_of_frames {E : Type} [Field E] {Ψ : Finset (E →+* ℂ)} {r : ℕ} (γ1 γ2 γ3 : GL (Fin r) E)
    (x b : Frame Ψ r) (τ : Ψ) (u : Matrix (Fin r) (Fin r) ℂ) (hdet : (mat x τ).det ≠ 0)
    (hb : mat b τ = (mat x τ)⁻¹ * u * mat x τ) (e : lact γ1 x = lact γ2 (rmul (lact γ3 x) b)) :
    ((γ2 * γ3)⁻¹ * γ1).1.map τ.1 = u := by
  have hu : IsUnit (mat x τ).det := Ne.isUnit hdet
  have e5 : γ1.1.map τ.1 * mat x τ = γ2.1.map τ.1 * ((γ3.1.map τ.1 * mat x τ) * mat b τ) := congrFun e τ
  rw [hb] at e5
  have e6 : γ1.1.map τ.1 = (γ2 * γ3).1.map τ.1 * u := by
    have := congrArg (· * (mat x τ)⁻¹) e5
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one,
      Matrix.mul_nonsing_inv_cancel_left _ _ hu] at this
    rw [this, Units.val_mul, Matrix.map_mul, Matrix.mul_assoc]
  rw [Units.val_mul, Matrix.map_mul, e6, ← Matrix.mul_assoc, ← Matrix.map_mul, Units.inv_mul,
    Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]

theorem hat_cong_conj {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ} (L L' : Set (Fin n → E))
    (g : GL (Fin n) (GlobalTheory.AdLat.RA F E))
    (hhat : (GlobalTheory.AdLat.hat F L' : Set (Fin n → GlobalTheory.AdLat.RA F E)) = g.1.mulVec '' (GlobalTheory.AdLat.hat F L))
    (γ : Matrix (Fin n) (Fin n) E) (M : ℕ) (h : ∀ x ∈ L', ∃ y ∈ L', γ.mulVec x - x = M • y) :
    ∀ z ∈ GlobalTheory.AdLat.hat F L, ∃ y ∈ GlobalTheory.AdLat.hat F L,
      ((g⁻¹).1 * γ.map (inclR (F := F) (FiniteAdeleRing (𝓞 F) F)) * g.1).mulVec z - z = M • y := by
  intro z hz
  have hz1 : g.1.mulVec z ∈ (GlobalTheory.AdLat.hat F L' : Set (Fin n → GlobalTheory.AdLat.RA F E)) := by
    rw [hhat]; exact ⟨z, hz, rfl⟩
  obtain ⟨y, hy, e⟩ := hat_cong L' γ M h _ hz1
  have hy1 : y ∈ (GlobalTheory.AdLat.hat F L' : Set (Fin n → GlobalTheory.AdLat.RA F E)) := hy
  rw [hhat] at hy1
  obtain ⟨y', hy', rfl⟩ := hy1
  refine ⟨y', hy', ?_⟩
  have e2 := congrArg ((g⁻¹).1.mulVec) e
  simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at e2
  rw [← e2, Matrix.mul_assoc]


set_option maxHeartbeats 400000 in
theorem conj_mem_of_cong : ∀ (D : D7) (V : Formalism.BasicNotions.TH.HSp D) (Comp : Type) (X : Comp → Data D.host.E V.rank)
    (dict : GA D V → Σ k, Frame (X k).Ψ V.rank) (Kf : Subgroup (GA D V))
    (th : ∀ c, (X c).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (M : ℕ) (x0 : ∀ c, Frame (X c).Ψ V.rank),
    IsLevelK V M Kf → (∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) → DictIsUnif V dict Kf th rfl →
    (∀ c, x0 c ∈ (X c).dom) →
    (∀ g, ∀ h ∈ GinfC V, ∃ γ' ∈ (X (dict g).1).Γ,
      dict (g * h) = ⟨(dict g).1, lact γ' (rmul (dict g).2 (archMat V th rfl x0 h (dict g).1))⟩) →
    (∀ c, (X c).Gm = -(V.gram)ᵀ) →
    ∀ (k : Comp) (g : GA D V), dict g = ⟨k, x0 k⟩ →
    ∀ Λk : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E),
      (Λk : Set (Fin V.rank → D.host.E)) = GlobalTheory.AdLat.latOf (maximalRealSubfield D.host.E) (finHom V g).1
        (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)) →
      (GlobalTheory.AdLat.hat (maximalRealSubfield D.host.E) (Λk : Set (Fin V.rank → D.host.E)) :
                   Set (Fin V.rank → GlobalTheory.AdLat.RA (maximalRealSubfield D.host.E) D.host.E)) =
        ((finHom V g).1 : Matrix (Fin V.rank) (Fin V.rank) (GlobalTheory.AdLat.RA (maximalRealSubfield D.host.E) D.host.E)).mulVec ''
          (GlobalTheory.AdLat.hat (maximalRealSubfield D.host.E) (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E))) →
    ∀ γ' : GL (Fin V.rank) D.host.E,
      (IsUStab (-(V.gram)ᵀ) Λk γ' ∧ ∀ x ∈ Λk, ∃ y ∈ Λk, (γ' : Matrix (Fin V.rank) (Fin V.rank) D.host.E).mulVec x - x = M • y) →
      ∃ γ ∈ (X k).Γ, ∀ (τ : D.host.E →+* ℂ) (hτ : τ ∈ (X k).Ψ),
        archM V (th k ⟨τ, hτ⟩) g * (γ : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map τ =
          (γ' : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map τ * archM V (th k ⟨τ, hτ⟩) g := by
  intro D V Comp X dict Kf th M x0 hK hth hd hx0 hact _ k g hg Λk _ hhat γ' hγ'
  haveI : IsTotallyReal D.host.F := D.sp.cm.totReal
  obtain ⟨γ₀, hQ, hfin, harch⟩ := exists_rat V γ' hγ'.1.1
  obtain ⟨hinj, -, -, hsur⟩ := (GlobalTheory.T.adelicUnitary_exists_with_prescribed_parts D V).2 (X k).Ψ (th k) (X k).cmType (hth k)
  obtain ⟨h, hh, hhw⟩ := hsur (fun τ => archM V (th k τ) (g⁻¹ * γ₀ * g)) (fun τ =>
    GlobalTheory.MarkUnit.infMat_unitary D.sp.cm.sig V.gram τ.1
      (fun x => IsCMField.complexEmbedding_complexConj D.host.E τ.1 x) (th k τ) (hth k τ) _)
  have hκ1 : ∀ τ, archM V (th k τ) (g⁻¹ * γ₀ * g * h⁻¹) = 1 := fun τ => by
    rw [archM_mul', ← hhw, ← archM_mul', mul_inv_cancel, archM_one']
  have hh1 : finHom V h = 1 := hh
  have hκ : g⁻¹ * γ₀ * g * h⁻¹ ∈ Kf := by
    refine (hK _).2 ⟨hinj _ hκ1, ?_⟩
    have hf : (finHom V (g⁻¹ * γ₀ * g * h⁻¹)).1 =
        ((finHom V g)⁻¹).1 * γ'.1.map (inclR (Af D.host.F)) * (finHom V g).1 := by
      rw [← hfin]
      simp only [map_mul, map_inv, hh1, inv_one, mul_one, Units.val_mul]
    rw [(GlobalTheory.Member.latHat_eq_hat_and_gram D V).1, hf]
    exact hat_cong_conj (F := D.host.F) (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E))
      (Λk : Set (Fin V.rank → D.host.E)) (finHom V g) hhat γ'.1 M hγ'.2
  obtain ⟨γ1, hγ1, e1⟩ := hd.1 γ₀ hQ g
  obtain ⟨γ3, hγ3, e3⟩ := hd.2.1 _ hκ g
  obtain ⟨γ2, hγ2, e2⟩ := hact (g * (g⁻¹ * γ₀ * g * h⁻¹)) h hh
  have hgrp : g * (g⁻¹ * γ₀ * g * h⁻¹) * h = γ₀ * g := by group
  rw [hgrp, e1] at e2
  rw [e3] at e2 hγ2
  rw [hg] at e2 hγ1 hγ2 hγ3
  have e4 : lact γ1 (x0 k) = lact γ2 (rmul (lact γ3 (x0 k)) (archMat V th rfl x0 h k)) :=
    eq_of_heq (Sigma.mk.inj e2).2
  refine ⟨(γ2 * γ3)⁻¹ * γ1, mul_mem (inv_mem (mul_mem hγ2 hγ3)) hγ1, fun τ hτ => ?_⟩
  have hb : mat (archMat V th rfl x0 h k) ⟨τ, hτ⟩ =
      (mat (x0 k) ⟨τ, hτ⟩)⁻¹ * archM V (th k ⟨τ, hτ⟩) h * mat (x0 k) ⟨τ, hτ⟩ := by
    have hre : ∀ u : Matrix (Fin V.rank) (Fin V.rank) ℂ,
        Matrix.reindex (finCongr (rfl : V.rank = V.rank)) (finCongr (rfl : V.rank = V.rank)) u = u := fun u => by
      simp
    rw [← hre (archM V (th k ⟨τ, hτ⟩) h)]
    rfl
  have e6 := map_eq_of_frames γ1 γ2 γ3 (x0 k) _ ⟨τ, hτ⟩ _ (hx0 k ⟨τ, hτ⟩).1 hb e4
  rw [e6, hhw, ← harch τ _ (hth k ⟨τ, hτ⟩), ← archM_mul', ← archM_mul']
  congr 1
  group

end GlobalTheory.RepConv
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalCongruenceConjMemArithmeticGroupStatement
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo
open scoped ENNReal
open IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principalCongruence_conj_mem_arithmeticGroup : ∀ (D : D7) (V : Formalism.BasicNotions.TH.HSp D) (Comp : Type) (X : Comp → Data D.host.E V.rank)
    (dict : GA D V → Σ k, Frame (X k).Ψ V.rank) (Kf : Subgroup (GA D V))
    (th : ∀ c, (X c).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (M : ℕ) (x0 : ∀ c, Frame (X c).Ψ V.rank),
    IsLevelK V M Kf → (∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) → DictIsUnif V dict Kf th rfl →
    (∀ c, x0 c ∈ (X c).dom) →
    (∀ g, ∀ h ∈ GinfC V, ∃ γ' ∈ (X (dict g).1).Γ,
      dict (g * h) = ⟨(dict g).1, lact γ' (rmul (dict g).2 (archMat V th rfl x0 h (dict g).1))⟩) →
    (∀ c, (X c).Gm = -(V.gram)ᵀ) →
    ∀ (k : Comp) (g : GA D V), dict g = ⟨k, x0 k⟩ →
    ∀ Λk : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E),
      (Λk : Set (Fin V.rank → D.host.E)) = GlobalTheory.AdLat.latOf (maximalRealSubfield D.host.E) (finHom V g).1
        (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)) →
      (GlobalTheory.AdLat.hat (maximalRealSubfield D.host.E) (Λk : Set (Fin V.rank → D.host.E)) :
                   Set (Fin V.rank → GlobalTheory.AdLat.RA (maximalRealSubfield D.host.E) D.host.E)) =
        ((finHom V g).1 : Matrix (Fin V.rank) (Fin V.rank) (GlobalTheory.AdLat.RA (maximalRealSubfield D.host.E) D.host.E)).mulVec ''
          (GlobalTheory.AdLat.hat (maximalRealSubfield D.host.E) (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E))) →
    ∀ γ' : GL (Fin V.rank) D.host.E,
      (IsUStab (-(V.gram)ᵀ) Λk γ' ∧ ∀ x ∈ Λk, ∃ y ∈ Λk, (γ' : Matrix (Fin V.rank) (Fin V.rank) D.host.E).mulVec x - x = M • y) →
      ∃ γ ∈ (X k).Γ, ∀ (τ : D.host.E →+* ℂ) (hτ : τ ∈ (X k).Ψ),
        archM V (th k ⟨τ, hτ⟩) g * (γ : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map τ =
          (γ' : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map τ * archM V (th k ⟨τ, hτ⟩) g := by
  first | exact @GlobalTheory.RepConv.conj_mem_of_cong | exact GlobalTheory.RepConv.conj_mem_of_cong | (intros; apply GlobalTheory.RepConv.conj_mem_of_cong <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjSmulNeBot
noncomputable section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

namespace GlobalTheory.BotPairSmall

def cvec (D : D7) (δ : ℂ) (𝔪 : Ideal (𝓞 D.host.E)) (o a d : ℕ) (e0 : VC D a d → ℂ) : VC D a d → ℂ :=
  ((Real.sqrt ((Ideal.absNorm 𝔪 : ℝ) ^ (a * d)) : ℂ))⁻¹ •
    Wd D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ (unitBlock D o a d))
      (Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)) e0)

def blockSet (D : D7) (𝔪 : Ideal (𝓞 D.host.E)) (a N : ℕ) : Set (GA D N) :=
  {h | h ∈ intG D N ∧ ∀ i j : Fin N, j.1 < a → a ≤ i.1 →
    ((h : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j ∈ hatId D 𝔪}

def blockJ (D : D7) (𝔪 : Ideal (𝓞 D.host.E)) (a N : ℕ) : Subgroup (GA D N) := Subgroup.closure (blockSet D 𝔪 a N)

theorem blockJ_le (D : D7) (𝔪 : Ideal (𝓞 D.host.E)) (a N : ℕ) : blockJ D 𝔪 a N ≤ intG D N :=
  (Subgroup.closure_le _).2 fun _ h => h.1

theorem conj_smul_ne_bot (D : D7) {𝔪 : Ideal (𝓞 D.host.E)} (h : 𝔪 ≠ ⊥) : D.host.conj • 𝔪 ≠ ⊥ := by
  intro e
  apply h
  have := congrArg (fun I : Ideal (𝓞 D.host.E) => D.host.conj⁻¹ • I) e
  simpa [smul_smul] using this

end GlobalTheory.BotPairSmall
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacuumCharacterPositiveDefiniteSource
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacuumCharacterPositiveDefiniteSource
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct Kronecker ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.VacuumCharacter

variable {D : D7}

theorem vacuum_character : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → IsInfFam θ → S.SigOK → T.SigOK → ∀ (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ), (∀ τ, IsCartanInv (gramAt D S τ) 1) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) → ∀ (a b : D.what₂.Tau → ℚ), (∀ τ, HasInfExp D χS τ (a τ)) → (∀ τ, HasInfExp D χT τ (b τ)) → ∀ (x₁ x₂ x₃ : D.what₂.Tau → ℤ), (∀ τ, (x₁ τ : ℚ) = a τ + (S.rank : ℚ) / 2) → (∀ τ, (x₂ τ : ℚ) = a τ - (S.rank : ℚ) / 2) → (∀ τ, (x₃ τ : ℂ) = -((sT τ).trace / 2 + (b τ : ℂ))) → ∀ f, IsThetaFunO ψ S T f → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO 1 (sT τ)) f) → ∀ g ∈ GinfC S, ∀ h ∈ GinfC T, (∀ τ, sT τ * compAt θ τ (Formalism.L2.Theta.mt T h) = compAt θ τ (Formalism.L2.Theta.mt T h) * sT τ) → om (g, h) f = (∏ τ, ((1 / 2 : ℂ) • (1 + sT τ) * compAt θ τ (Formalism.L2.Theta.mt T h) + (1 / 2 : ℂ) • (1 - sT τ)).det ^ x₁ τ * ((1 / 2 : ℂ) • (1 - sT τ) * compAt θ τ (Formalism.L2.Theta.mt T h) + (1 / 2 : ℂ) • (1 + sT τ)).det ^ x₂ τ * (compAt θ τ (Formalism.L2.Theta.mt S g)).det ^ x₃ τ) • f := by
  intro D ψ θ S T χS χT om hW hθ _ _ sT hS hT a b ha hb x₁ x₂ x₃ h1 h2 h3 f hf hv g hg h hh hc
  obtain ⟨η, e1, e2, e3, e4⟩ := GlobalTheory.T.exists_unramifiedHeckeChar_halfExponent_restrict_quadratic D
  have hdet : ∀ {k : ℕ} {G s : Matrix (Fin k) (Fin k) ℂ}, IsCartanInv G s → G.det ≠ 0 := fun {k G s} hG => by
    have := hG.2.2.det_pos.ne'
    rw [Matrix.det_mul] at this
    exact left_ne_zero_of_mul this
  obtain ⟨x, hx, hxv⟩ := exists_root hθ S (fun τ => hdet (hS τ)) g hg
  obtain ⟨y, hy, hyv⟩ := exists_root hθ T (fun τ => hdet (hT τ)) h hh
  choose p hp hd using fun τ => detPlus_one (n := S.rank) (sT τ) (hT τ).1
  rw [GlobalTheory.T.weilDatum_realPlaces_fockVacuum_character D ψ hW.std S T θ hθ χS χT om η ⟨e1, e4, e3, e2⟩ hW (fun _ => 1) sT hS hT g hg h hh
    (fun τ => by rw [one_mul, mul_one]) hc x y hx hy f hf hv]
  congr 1
  have hb' : ∀ τ, ((-x₃ τ - p τ : ℤ) : ℚ) = b τ - T.rank / 2 := fun τ => by
    have := h3 τ
    rw [hp] at this
    apply Rat.cast_injective (α := ℂ)
    push_cast
    linear_combination -this
  rw [Circle.coe_mul, Circle.coe_inv,
    hxv _ (fun τ => -x₃ τ - p τ) (fun τ => by rw [hb']; exact hasInfExp_twist (hb τ) (e2 τ) _),
    hyv _ x₂ (fun τ => by rw [h2]; exact hasInfExp_twist (ha τ) (e2 τ) _),
    ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  obtain ⟨d1, d2⟩ := hd τ (compAt θ τ (Formalism.L2.Theta.mt S g⁻¹)) (compAt θ τ (Formalism.L2.Theta.mt T h)) (hc τ)
  have inv : ∀ (V : HSp D) (k : GA D V),
      (compAt θ τ (Formalism.L2.Theta.mt V k)).det * (compAt θ τ (Formalism.L2.Theta.mt V k⁻¹)).det = 1 := fun V k => by
    rw [det_compAt, det_compAt, ← map_mul, ← map_mul, ← Matrix.det_mul]
    unfold Formalism.L2.Theta.mt
    rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one, Matrix.det_one, map_one, map_one]
  have g0 := left_ne_zero_of_mul_eq_one (inv S g)
  have h0 := left_ne_zero_of_mul_eq_one (inv T h)
  rw [d2] at h0
  have h0' := left_ne_zero_of_mul h0
  have e : x₁ τ = x₂ τ + S.rank := by
    have : (x₁ τ : ℚ) = x₂ τ + S.rank := by rw [h1, h2]; ring
    exact_mod_cast this
  have alg : ∀ (A B G : ℂ) (u v : ℤ) (n k : ℕ), A ≠ 0 → G ≠ 0 →
      (G ^ (-v - k))⁻¹ * (A * B) ^ u * (A ^ n * G⁻¹ ^ k) = A ^ (u + n) * B ^ u * G ^ v := by
    intro A B G u v n k hA hG
    rw [mul_zpow, zpow_add₀ hA, zpow_sub₀ hG, _root_.zpow_neg, zpow_natCast, zpow_natCast, inv_pow]
    have := zpow_ne_zero v hG
    have := pow_ne_zero k hG
    field_simp
  rw [d1, d2, eq_inv_of_mul_eq_one_right (inv S g), e]
  exact alg _ _ _ _ _ _ _ h0' g0

end GlobalTheory.VacuumCharacter

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacuumCharacterPositiveDefiniteSourceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vacuum_character_positive_definite_source : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → IsInfFam θ → S.SigOK → T.SigOK → ∀ (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ), (∀ τ, IsCartanInv (gramAt D S τ) 1) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) → ∀ (a b : D.what₂.Tau → ℚ), (∀ τ, HasInfExp D χS τ (a τ)) → (∀ τ, HasInfExp D χT τ (b τ)) → ∀ (x₁ x₂ x₃ : D.what₂.Tau → ℤ), (∀ τ, (x₁ τ : ℚ) = a τ + (S.rank : ℚ) / 2) → (∀ τ, (x₂ τ : ℚ) = a τ - (S.rank : ℚ) / 2) → (∀ τ, (x₃ τ : ℂ) = -((sT τ).trace / 2 + (b τ : ℂ))) → ∀ f, IsThetaFunO ψ S T f → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO 1 (sT τ)) f) → ∀ g ∈ GinfC S, ∀ h ∈ GinfC T, (∀ τ, sT τ * compAt θ τ (mt T h) = compAt θ τ (mt T h) * sT τ) → om (g, h) f = (∏ τ, ((1 / 2 : ℂ) • (1 + sT τ) * compAt θ τ (mt T h) + (1 / 2 : ℂ) • (1 - sT τ)).det ^ x₁ τ * ((1 / 2 : ℂ) • (1 - sT τ) * compAt θ τ (mt T h) + (1 / 2 : ℂ) • (1 + sT τ)).det ^ x₂ τ * (compAt θ τ (mt S g)).det ^ x₃ τ) • f := by
  first | exact @GlobalTheory.VacuumCharacter.vacuum_character | exact GlobalTheory.VacuumCharacter.vacuum_character | (intros; apply GlobalTheory.VacuumCharacter.vacuum_character <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockOfMatrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.DblVac

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def diagonalBlockOfMatrix {σ : E →ₐ[F] E} {d : ℕ} {W : Spc F E d} (g : UD σ W) : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :=
  ⅟(2 : AF F) • ((matD g).toBlocks₁₁ + (matD g).toBlocks₁₂ + (matD g).toBlocks₂₁ + (matD g).toBlocks₂₂)

def BigCell {σ : E →ₐ[F] E} {d : ℕ} (W : Spc F E d) (v : Pl (F := F)) (g : UD σ W) : Prop :=
  ∃ M : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), M * diagonalBlockOfMatrix g = 1 ∧
    ∀ z ∈ GlobalTheory.InertSph.latAt W v, M *ᵥ z ∈ GlobalTheory.InertSph.latAt W v

end GlobalTheory.DblVac
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ApplyAt0Smul
noncomputable section

open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField Polynomial
open scoped Pointwise nonZeroDivisors
open Formalism.L2.Host (HChar embTau)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FunObj GlobalTheory.FunObj.SqNum

namespace GlobalTheory.FunObj.NormUniq

variable {D : D7}

theorem wd_smul (T : Tor D) {N N' : ℕ} (x : VC D N N') (c : ℂ) (G : VC D N N' → ℂ) :
    Wd D T x (c • G) = c • Wd D T x G := by
  funext z
  simp only [Wd, U, Pi.smul_apply, smul_eq_mul]
  ring

theorem wd_add (T : Tor D) {N N' : ℕ} (x : VC D N N') (G G' : VC D N N' → ℂ) :
    Wd D T x (G + G') = Wd D T x G + Wd D T x G' := by
  funext z
  simp only [Wd, U, Pi.add_apply]
  ring

theorem applyAt0_smul {N N' : ℕ} (P : MvPolynomial (GL3Theta.Idx D N N') ℂ) {c : ℂ} (hc : c ≠ 0)
    (G : VC D N N' → ℂ) : GL3Theta.applyAt0 D P (c • G) = c * GL3Theta.applyAt0 D P G := by
  simp only [GL3Theta.applyAt0, Finset.mul_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  have : TaylorLogMetric.taylor D (c • G) α = c * TaylorLogMetric.taylor D G α := by
    unfold TaylorLogMetric.taylor
    let g : ℂ ≃L[ℂ] ℂ := ContinuousLinearEquiv.smulLeft (R₁ := ℂ) (M₁ := ℂ) (G := ℂˣ) (Units.mk0 c hc)
    have e : c • G = ⇑g ∘ G := by
      funext z; simp [g, ContinuousLinearEquiv.smulLeft, Units.smul_def]
    rw [e, ContinuousLinearEquiv.iteratedFDeriv_comp_left]
    simp [g, ContinuousLinearEquiv.smulLeft, Units.smul_def]
    ring
  rw [this]; ring

theorem tt_zero (T : Tor D) {N N' : ℕ} : (0 : VC D N N' → ℂ) ∈ TT D T N N' :=
  ⟨differentiable_const 0, 1, one_pos, fun x _ => by funext z; simp [Wd, U]⟩

theorem tt_add {T : Tor D} {N N' : ℕ} {F F' : VC D N N' → ℂ} (hF : F ∈ TT D T N N') (hF' : F' ∈ TT D T N N') :
    F + F' ∈ TT D T N N' := by
  obtain ⟨h1, m, hm, h2⟩ := hF
  obtain ⟨h1', m', hm', h2'⟩ := hF'
  refine ⟨h1.add h1', m * m', Nat.mul_pos hm hm', fun x hx => ?_⟩
  have e1 := h2 (m' • x) (AddSubgroup.nsmul_mem _ hx _)
  have e2 := h2' (m • x) (AddSubgroup.nsmul_mem _ hx _)
  rw [smul_smul] at e1 e2
  rw [mul_comm m' m] at e2
  rw [wd_add, e1, e2]

theorem tt_smul {T : Tor D} {N N' : ℕ} {F : VC D N N' → ℂ} (hF : F ∈ TT D T N N') (c : ℂ) :
    c • F ∈ TT D T N N' := by
  obtain ⟨h1, m, hm, h2⟩ := hF
  exact ⟨h1.const_smul c, m, hm, fun x hx => by rw [wd_smul, h2 x hx]⟩

theorem tt_sum {T : Tor D} {N N' : ℕ} {ι : Type*} (s : Finset ι) {F : ι → VC D N N' → ℂ}
    (hF : ∀ i ∈ s, F i ∈ TT D T N N') : ∑ i ∈ s, F i ∈ TT D T N N' := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using tt_zero T
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact tt_add (hF a (Finset.mem_insert_self a s)) (ih fun i hi => hF i (Finset.mem_insert_of_mem hi))

end GlobalTheory.FunObj.NormUniq
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjMemAdelicSchwartzSpaceNumberFieldOfMem
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjMemAdelicSchwartzSpaceNumberFieldOfMem
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

namespace GlobalTheory.ConjSch

open scoped Classical

noncomputable def conjSch {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (f : SchwartzMap V ℂ) : SchwartzMap V ℂ where
  toFun x := star (f x)
  smooth' := (Complex.conjLIE.toContinuousLinearEquiv.contDiff).comp f.smooth'
  decay' := by
    intro k n
    obtain ⟨C, hC⟩ := f.decay' k n
    refine ⟨C, fun x => ?_⟩
    have e : (fun x => star (f x)) = Complex.conjLIE ∘ f := rfl
    rw [e, LinearIsometryEquiv.norm_iteratedFDeriv_comp_left]
    exact hC x

theorem conjSch_apply {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (f : SchwartzMap V ℂ) (x : V) :
    conjSch f x = star (f x) := rfl

theorem star_mem_schA {F : Type} [Field F] [NumberField F] (κ : Type) [Fintype κ] :
    ∀ Φ ∈ schA F κ, (fun x => star (Φ x)) ∈ schA F κ := by
  intro Φ hΦ
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, g, hg, rfl⟩ := hx
    refine Submodule.subset_span ⟨conjSch f, fun y => star (g y),
      ⟨hg.1.comp _, hg.2.comp_left (g := star) (star_zero _)⟩, ?_⟩
    funext y
    simp only [pureA, conjSch_apply, star_mul', mul_comm]
  | zero =>
    simp only [Pi.zero_apply, star_zero]
    exact (schA F κ).zero_mem
  | add x y _ _ hx hy =>
    have := (schA F κ).add_mem hx hy
    convert this using 1
    funext z; simp
  | smul c x _ hx =>
    have := (schA F κ).smul_mem (star c) hx
    convert this using 1
    funext z; simp [star_mul', mul_comm]

end GlobalTheory.ConjSch

theorem GlobalTheory.star_mem_schA_main : ∀ {F : Type} [Field F] [NumberField F] (κ : Type) [Fintype κ], ∀ Φ ∈ schA F κ, (fun x => star (Φ x)) ∈ schA F κ :=
  fun κ _ => GlobalTheory.ConjSch.star_mem_schA κ
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjMemAdelicSchwartzSpaceNumberFieldOfMemStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conj_mem_adelicSchwartzSpaceNumberField_of_mem : ∀ {F : Type} [Field F] [NumberField F] (κ : Type) [Fintype κ], ∀ Φ ∈ schA F κ, (fun x => star (Φ x)) ∈ schA F κ := by
  first | exact @GlobalTheory.star_mem_schA_main | exact GlobalTheory.star_mem_schA_main | (intros; apply GlobalTheory.star_mem_schA_main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualLatticeNegTransposeGram
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualLatticeNegTransposeGram
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo
open scoped ENNReal
open IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.Member.selfDualLat_neg_gram_transpose : ∀ (D : D7) (V : Formalism.BasicNotions.TH.HSp D), GlobalTheory.UCls.SelfDualLat (-(V.gram)ᵀ) (GlobalTheory.Member.latC V) := by
  intro D V
  obtain ⟨-, -, hfg, hsp, -, hcc, -, hG, hdet, -, hL⟩ := GlobalTheory.Member.latHat_eq_hat_and_gram D V
  have hint : ∀ z : D.host.E, IsIntegral ℤ z ↔
      z ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) := by
    intro z
    rw [FractionalIdeal.mem_one_iff, IsIntegralClosure.isIntegral_iff (A := 𝓞 D.host.E)]
  refine ⟨?_, ?_, hfg, hsp, ?_⟩
  · intro a b
    simp only [Matrix.neg_apply, map_neg, ← hcc, hG]
  · rw [Matrix.det_neg]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hdet
  · intro x
    rw [← hL x]
    refine forall_congr' fun y => imp_congr_right fun _ => ?_
    have he : herm (-(V.gram)ᵀ) x y = -(∑ a, ∑ b, x a * V.gramᵀ a b * cF D (y b)) := by
      simp only [herm, Matrix.neg_apply, mul_neg, neg_mul, Finset.sum_neg_distrib, hcc]
    rw [he, hint, ← hint, ← hint]
    exact ⟨fun h => by simpa using h.neg, fun h => h.neg⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualLatticeNegTransposeGramStatement
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo
open scoped ENNReal
open IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.selfDualLattice_neg_transpose_gram : ∀ (D : D7) (V : Formalism.BasicNotions.TH.HSp D), GlobalTheory.UCls.SelfDualLat (-(V.gram)ᵀ) (GlobalTheory.Member.latC V) := by
  first | exact @GlobalTheory.Member.selfDualLat_neg_gram_transpose | exact GlobalTheory.Member.selfDualLat_neg_gram_transpose | (intros; apply GlobalTheory.Member.selfDualLat_neg_gram_transpose <;> assumption)
end
end
