module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchurConstantsExistOnChainOfCuspRapidDecay
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.CuspLatticeAnyLevel
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTypesIdempotentCoefficients
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ContinuousIdeleCircle

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductOfLocalLevelsUnitaryIsOpenIsCompactIsLeve
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductOfLocalLevelsUnitaryIsOpenIsCompactIsLeve
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.GlobLev

open GlobalTheory.SplitPts GroundTheory.Automorphic

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}


omit [IsCMField E] in
theorem mem_KGL_iff_val (w : Pl E) (g : GLw n w) :
    g ∈ GlobalTheory.LFun.KGL w (n := n) ↔ (∀ i j, Valued.v (g.val i j) ≤ 1) ∧ ∀ i j, Valued.v ((g⁻¹).val i j) ≤ 1 := by
  have hO : GLnLocal.integralGL (w.adicCompletion E) n = GlobalTheory.LFun.KGL w (n := n) := by
    have h : (ValuativeRel.valuation (w.adicCompletion E)).integer = Formalism.UG.Ov E w :=
      Subring.ext fun x => GroundTheory.Global.mem_valuationInteger_iff w x
    rw [GlobalTheory.LFun.KGL, ← h]; rfl
  rw [← hO, GLnLocal.mem_integralGL_iff]
  simp only [GroundTheory.Global.mem_valuationInteger_iff]
  rfl

theorem eq_or_eq_conjSrc {w u : Pl E}
    (h : u.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E))) :
    u = w ∨ u = conjSrc (conjE E) w := by
  by_cases huw : u = w
  · exact Or.inl huw
  · exact (over_split ⟨u, huw, h⟩).2.2 u h

theorem conjSrc_eq_of_not_split {w : Pl E} (hw : ¬ IsSplitAt w) : conjSrc (conjE E) w = w := by
  by_contra hne
  exact hw ⟨_, hne, (GlobalTheory.Mem.Chr.under_eq_iff_conjPl (IsCMField.complexConj E)
    (Algebra.IsQuadraticExtension.finrank_eq_two _ _) (IsCMField.complexConj_ne_one E) w _).2
      (Or.inr (conjPl_self_conjSrc w))⟩

theorem conjLoc_eq_cj {w : Pl E} (hw : ¬ IsSplitAt w) (a : Af E) :
    conjLoc (conjE E) w (pLoc E (conjSrc (conjE E) w) a) = cj w (pLoc E w a) := by
  have key : ∀ (v : Pl E) (_ : v = w) (f : v.adicCompletion E →+* w.adicCompletion E), Continuous f →
      (∀ k : E, f (algebraMap E _ k) = algebraMap E _ (conjE E k)) → f (pLoc E v a) = cj w (pLoc E w a) := by
    rintro v rfl f hf h
    have hex : ∃ s : v.adicCompletion E →+* v.adicCompletion E, Continuous s ∧
      ∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x) := ⟨f, hf, h⟩
    rw [cj, dite_eq_left hex]
    exact congrFun ((HeightOneSpectrum.denseRange_algebraMap (K := E) v).equalizer hf hex.choose_spec.1
      (funext fun k => (h k).trans (hex.choose_spec.2 k).symm)) _
  exact key _ (conjSrc_eq_of_not_split hw) _ (conjLoc_spec (conjE E) _).1 (conjLoc_spec (conjE E) _).2.1

theorem cLoc_mem_UL (w : Pl E) (x : UA E n) : cLoc w x ∈ UL n w := by
  unfold UL
  split_ifs with hw
  · exact Subgroup.mem_top _
  · have h := comp_eq x w
    have e : (cLoc (conjSrc (conjE E) w) x).val.map (conjLoc (conjE E) w) = (cLoc w x).val.map (cj w) :=
      Matrix.ext fun i j => conjLoc_eq_cj hw _
    rw [e] at h
    change ((cLoc w x).val.map (cj w))ᵀ * 1 * (cLoc w x).val = 1
    rw [Matrix.mul_one]
    exact h

theorem val_inv_entry (x : UA E n) (u : Pl E) (i j : Fin n) :
    Valued.v (((cLoc u x)⁻¹).val i j) = Valued.v ((cLoc (conjSrc (conjE E) u) x).val j i) := by
  have h := comp_eq x u
  have e : ((cLoc u x)⁻¹).val = ((cLoc (conjSrc (conjE E) u) x).val.map (conjLoc (conjE E) u))ᵀ :=
    (Units.eq_inv_of_mul_eq_one_right h).symm
  rw [e]
  exact (conjLoc_spec (conjE E) u).2.2 _

theorem integral_conjSrc (x : UA E n) (u : Pl E) (h : cLoc u x ∈ GlobalTheory.LFun.KGL u (n := n)) :
    cLoc (conjSrc (conjE E) u) x ∈ GlobalTheory.LFun.KGL (conjSrc (conjE E) u) (n := n) := by
  rw [mem_KGL_iff_val] at h ⊢
  refine ⟨fun i j => (val_inv_entry x u j i) ▸ h.2 j i, fun i j => ?_⟩
  have h2 := val_inv_entry x⁻¹ u j i
  rw [map_inv, map_inv, inv_inv] at h2
  exact h2 ▸ h.1 j i

theorem mem_globLev (S : Set (Pl E)) (K' : ∀ w : Pl E, Subgroup (UL n w)) (k : finU (E := E) (n := n)) :
    k ∈ globLev S K' ↔ ∀ w ∈ S, (⟨cLoc w k.1, cLoc_mem_UL w k.1⟩ : UL n w) ∈ K' w := by
  simp only [globLev, Subgroup.mem_iInf, Subgroup.mem_comap]
  refine forall₂_congr fun w _ => ⟨?_, fun h => ⟨_, h, rfl⟩⟩
  rintro ⟨a, ha, e⟩
  have : a = ⟨cLoc w k.1, cLoc_mem_UL w k.1⟩ := Subtype.ext e
  exact this ▸ ha


variable (E n) in
def finPart : finU (E := E) (n := n) →* GL (Fin n) (Af E) :=
  (GeneralLinearGroup.map (pFin E)).comp ((UA E n).subtype.comp (finU (E := E) (n := n)).subtype)

theorem continuous_finPart : Continuous (finPart E n) :=
  (Continuous.units_map _ (continuous_id.matrix_map (continuous_snd : Continuous (pFin E)))).comp
    (continuous_subtype_val.comp continuous_subtype_val)

theorem globLev_KL_eq {S : Set (Pl E)} (hS : IsSection S) :
    globLev S (KL n) = (AdelicGLn.integralFiniteGL E n).comap (finPart E n) := by
  ext k
  have e : k ∈ (AdelicGLn.integralFiniteGL E n).comap (finPart E n) ↔ ∀ u, cLoc u k.1 ∈ GlobalTheory.LFun.KGL u (n := n) := by
    rw [Subgroup.mem_comap, AdelicGLn.mem_integralFiniteGL_iff, ← map_inv]
    simp only [mem_KGL_iff_val, ← map_inv, GroundTheory.Global.mem_integralFiniteAdeles]
    exact ⟨fun h u => ⟨fun i j => h.1 i j u, fun i j => h.2 i j u⟩,
      fun h => ⟨fun i j u => (h u).1 i j, fun i j u => (h u).2 i j⟩⟩
  rw [e, mem_globLev]
  refine ⟨fun h u => ?_, fun h w _ => h w⟩
  obtain ⟨w, ⟨hw, hwu⟩, -⟩ := hS u
  rcases eq_or_eq_conjSrc hwu.symm with rfl | rfl
  · exact h u hw
  · exact integral_conjSrc k.1 w (h w hw)

theorem continuous_pInf_ad : Continuous (pInf E) :=
  continuous_pi fun w =>
    ((InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
      (continuous_apply w)).comp continuous_fst

theorem continuous_conj_ad : Continuous (conjAd E) :=
  ((continuous_infEq E).comp (continuous_star.comp continuous_pInf_ad)).prodMk
    ((continuous_conjFin _).comp continuous_snd)

theorem isClosedEmbedding_finU : Topology.IsClosedEmbedding (fun x : finU (E := E) (n := n) => ((x : UA E n) : GA E n)) := by
  haveI : T2Space (FiniteAdeleRing (𝓞 E) E) :=
    inferInstanceAs (T2Space (RestrictedProduct (fun v : HeightOneSpectrum (𝓞 E) => v.adicCompletion E)
      (fun v => (v.adicCompletionIntegers E : Set (v.adicCompletion E))) Filter.cofinite))
  haveI : T2Space (InfiniteAdeleRing E) := inferInstanceAs (T2Space ((v : InfinitePlace E) → v.Completion))
  haveI : T2Space (Ad E) := inferInstanceAs (T2Space (InfiniteAdeleRing E × FiniteAdeleRing (𝓞 E) E))
  have h1 : IsClosed ((UA E n : Subgroup (GA E n)) : Set (GA E n)) := by
    show IsClosed {g : GA E n | ((g : Matrix (Fin n) (Fin n) (Ad E)).map (conjAd E))ᵀ * 1 *
      (g : Matrix (Fin n) (Fin n) (Ad E)) = 1}
    exact isClosed_eq (((Units.continuous_val.matrix_map continuous_conj_ad).matrix_transpose.matrix_mul
      continuous_const).matrix_mul Units.continuous_val) continuous_const
  have h2 : IsClosed ((finU (E := E) (n := n) : Subgroup (UA E n)) : Set (UA E n)) := by
    haveI : T2Space (GL (Fin n) (Cinf E)) := Units.isEmbedding_embedProduct.t2Space
    have hc : Continuous (cInf (E := E) (n := n)) :=
      (Continuous.units_map _ (continuous_id.matrix_map continuous_pInf_ad)).comp continuous_subtype_val
    exact isClosed_eq hc continuous_const
  exact h1.isClosedEmbedding_subtypeVal.comp h2.isClosedEmbedding_subtypeVal

theorem continuous_finGL_ad : Continuous (finGL E n) :=
  Continuous.units_map _ (continuous_const.add (continuous_id.matrix_map
    (continuous_const.prodMk continuous_id : Continuous fun x : Af E => ((0, x) : InfiniteAdeleRing E × Af E))))

theorem continuous_cLoc (w : Pl E) : Continuous (cLoc (n := n) w) :=
  (Continuous.units_map _ (continuous_id.matrix_map
    ((RestrictedProduct.continuous_eval w).comp continuous_snd))).comp continuous_subtype_val

theorem globLev_isOpen_isCompact_isLevel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n →
    ∀ (S : Set (Pl E)), IsSection S → ∀ (K' : ∀ w : Pl E, Subgroup (UL n w)),
    IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' →
    IsOpen (globLev S (KL n) : Set (finU (E := E) (n := n))) ∧ IsCompact (globLev S (KL n) : Set (finU (E := E) (n := n))) ∧
      IsLevel (MonoidHom.id _) (globLev S (KL n)) (globLev S K') := by
  intro E _ _ _ _ n _ S hS K' hK
  have hO : IsOpen (globLev S (KL n) : Set (finU (E := E) (n := n))) := by
    rw [globLev_KL_eq hS]
    exact (AdelicGLn.isOpen_integralFiniteGL E n).preimage continuous_finPart
  have hle : globLev S K' ≤ globLev S (KL n) := fun k hk =>
    (mem_globLev S _ k).2 fun w hw => (hK.1 w).2.1 ((mem_globLev S _ k).1 hk w hw)
  refine ⟨hO, ?_, ?_, hle, fun k hk => hk⟩
  · refine IsCompact.of_isClosed_subset (isClosedEmbedding_finU.isCompact_preimage
      ((AdelicGLn.isCompact_integralFiniteGL E n).image continuous_finGL_ad))
      (Subgroup.isClosed_of_isOpen _ hO) fun x hx => ⟨finPart E n x, ?_, ?_⟩
    · rw [globLev_KL_eq hS] at hx
      exact hx
    · have h1 : GeneralLinearGroup.map (pInf E) ((x : UA E n) : GA E n) = 1 := x.2
      exact ga_ext (by rw [pInf_finGL, h1]) (by rw [pFin_finGL]; rfl)
  · have hfin : {w | w ∈ S ∧ K' w ≠ KL n w}.Finite := (Filter.eventually_cofinite.1 hK.2).subset fun w hw => hw.2
    have e : (globLev S K' : Set (finU (E := E) (n := n))) = (globLev S (KL n) : Set (finU (E := E) (n := n))) ∩
        ⋂ w ∈ {w | w ∈ S ∧ K' w ≠ KL n w},
          (fun k : finU (E := E) (n := n) => (⟨cLoc w k.1, cLoc_mem_UL w k.1⟩ : UL n w)) ⁻¹' (K' w : Set (UL n w)) := by
      ext k
      simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]
      refine ⟨fun hk => ⟨hle hk, fun w hw => (mem_globLev S _ k).1 hk w hw.1⟩, fun hk => ?_⟩
      refine (mem_globLev S _ k).2 fun w hw => ?_
      by_cases h : K' w = KL n w
      · rw [h]; exact (mem_globLev S _ k).1 hk.1 w hw
      · exact hk.2 w ⟨hw, h⟩
    rw [e]
    exact hO.inter (hfin.isOpen_biInter fun w _ => (hK.1 w).1.preimage
      (Continuous.subtype_mk ((continuous_cLoc w).comp continuous_subtype_val) _))

end GlobalTheory.BCT.GlobLev
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductOfLocalLevelsUnitaryIsOpenIsCompactIsLeveStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.productOfLocalLevelsUnitary_isOpen_isCompact_isLevel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → IsOpen (globLev S (KL n) : Set (finU (E := E) (n := n))) ∧ IsCompact (globLev S (KL n) : Set (finU (E := E) (n := n))) ∧ IsLevel (MonoidHom.id _) (globLev S (KL n)) (globLev S K') := by
  first | exact @GlobalTheory.BCT.GlobLev.globLev_isOpen_isCompact_isLevel | exact GlobalTheory.BCT.GlobLev.globLev_isOpen_isCompact_isLevel | (intros; apply GlobalTheory.BCT.GlobLev.globLev_isOpen_isCompact_isLevel <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCuspOnRestrict
open MvPolynomial NumberField Module GlobalTheory.AllWt GlobalTheory.CompHt ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

namespace GlobalTheory.CompRestr

open GlobalTheory.FlatLine GlobalTheory.Reg

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}

theorem idem_mem_sec (Z : Comp Xo c) : idem Z ∈ sec Xo c 0 0 := by
  rw [← secZ_nat]
  have : (fun i => (ex Dw (0 : (E →+* ℂ) × ℕ → ℕ) 0 i : ℤ)) = 0 := by
    funext i
    rcases i with _ | ⟨τ, i⟩ <;> simp [ex]
  rw [this]
  exact idem_mem_secZ Z

theorem idem_mul_mem_cuspW {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ))
    (Z : Comp Xo c) {G : WTZ E} {f : Rul Xo c} (hf : f ∈ cuspW Xo c U G) : idem Z * f ∈ cuspW Xo c U G := by
  rw [mem_cuspW] at hf ⊢
  refine ⟨?_, fun σ hσ => ?_⟩
  · have := mul_mem_secZ (idem_mem_secZ Z) hf.1
    rwa [zero_add] at this
  · rw [AllWt.rdU_mul]
    refine IdemCusp.mul_mem_holSub (U σ).X (modelWt (U σ) G) (rdU (U σ) (idem Z)) (fun k => ?_) (hf.2 σ hσ)
    have hD : Dom (E := E) 0 0 := ⟨fun τ _ _ _ => le_rfl, Even.zero⟩
    have hs := (hU σ hσ).2.2.2.2.1 0 0 hD (idem Z) (idem_mem_sec Z) k
    have h0 : laU (U σ) 0 0 k = 0 := by
      funext τ j
      simp [laU]
    rw [h0] at hs
    refine IdemCusp.isIdemFn_of_isSec _ hs ?_
    have := congrFun (AllWt.rdU_mul (U σ) (idem Z) (idem Z)) k
    rw [idem_mul_idem] at this
    exact this.symm

theorem exists_cuspOn_restrict : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), (∀ σ, GoodEmb c σ → IsUnf (U σ)) → ∀ (Z : Comp Xo c) (G : WTZ E) (f : cuspW Xo c U G), ∃ g : cuspOn U Z G, (∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S), LiesOn Z y → evR Xo c g y = evR Xo c f y) ∧ (f ∈ latW U G → g ∈ latOn U Z G) := by
  intro E _ _ _ H Dw l Xo c r U hU Z G f
  have hs : idem Z * (f : Rul Xo c) ∈ suppOn Z := by
    rw [mul_comm]; exact mul_mem_suppOn _ (idem_mem_suppOn Z)
  refine ⟨⟨idem Z * (f : Rul Xo c), idem_mul_mem_cuspW hU Z f.2, hs⟩, fun S _ _ y hy => ?_, fun hf => ?_⟩
  · show evR Xo c (idem Z * (f : Rul Xo c)) y = evR Xo c f y
    by_cases ht : Tested y
    · have e : evR Xo c (idem Z * (f : Rul Xo c)) y = evR Xo c (idem Z) y * evR Xo c f y :=
        evalAt_mul (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (idem Z) f y
      rw [e, evR_idem hy ht, one_mul]
    · unfold evR evalAt
      rw [dite_eq_right ht, dite_eq_right ht]
  · refine (mem_supLat_iff (Z := Z) hs).2 fun la v hv => ?_
    show 0 ≤ v (idem Z * (f : Rul Xo c))
    rw [(isVal_valOn hv).mul, val_idem hv, zero_add]
    exact hf la v (valOn_subset Z la hv)

end GlobalTheory.CompRestr
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstRelIffTwistFactorAt
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TwistFactorCompare

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke
open scoped TensorProduct

theorem eq_one_of_chrEq_one {D : D7} {χ : (AE D)ˣ →* Circle} (h : ChrEq χ 1) (x : (AE D)ˣ) : χ x = 1 := by
  refine HeckeFinTrivial.eq_one_of_trivial_on_finite D χ h.1 (fun y hy => ?_) x
  obtain ⟨j, h1, h2, h3⟩ := HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨N, hN, hprod⟩ := CharLocProd.char_eq_prod_locK D j h1 h2 (PlaceIdem.exists_isPlIdem D j h1 h2 h3) χ 1 h
  obtain ⟨S, k, hS, hS'⟩ := finiteIdele_exists_local_approx D.host.E N hN
    (Units.map ((j : _ →+* _).comp (finPart D)).toMonoidHom y)
  exact Subtype.ext ((hprod y hy S k (fun P hP => ⟨(hS P hP).1, (hS P hP).2.1⟩) hS').trans
    (Finset.prod_eq_one fun P _ => rfl))

section Row

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)

variable {R i}

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l}
  {c : Coeff l} {σ : c.F →+* ℂ}
  {U : Unf Xo c σ D.R.r} {dict : GA D (Wc D i) → Σ k, Frame (U.X k).Ψ D.R.r}
  {ι : Dw.La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)} {g : ℕ}
  {e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ)}
  {F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)}
  {ik : U.Comp → Fin F.n} {φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ}
  {th : ∀ k, (U.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)}
  {x₀ : (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ}
  {dδ : T0 → DeltaDat Xo c (Vc D i).rank}
  {U₂ : ∀ t, Unf (dδ t).Xo₂ (dδ t).c₂ (σ.comp ((dδ t).eF.symm : (dδ t).c₂.F →+* c.F)) D.R.r}
  {dict₂ : ∀ t, GA D (Wc D i) → Σ k, Frame ((U₂ t).X k).Ψ D.R.r}
  {xi : T0 → (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ}

end Row

end GlobalTheory.TwistFactorCompare

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.T2SpaceFiniteAdeleRing
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.EulerTw

variable (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ)

def cPl (w : Pl E) : Pl E := conjSrc (IsCMField.complexConj E).toRingEquiv w

def orb (w : Pl E) : Finset (Pl E) := {w, cPl E w}

def idem (T : Finset (Pl E)) : FiniteAdeleRing (𝓞 E) E :=
  ⟨fun w => if w ∈ T then 1 else 0, by
    filter_upwards [T.finite_toSet.compl_mem_cofinite] with w hw
    rw [if_neg (by simpa using hw)]
    exact zero_mem _⟩

theorem idem_mul_self (T : Finset (Pl E)) : idem E T * idem E T = idem E T := by
  refine Subtype.ext (funext fun w => ?_)
  show (if w ∈ T then (1 : w.adicCompletion E) else 0) * (if w ∈ T then 1 else 0) = if w ∈ T then 1 else 0
  split_ifs <;> simp

def prjM (T : Finset (Pl E)) :
    Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E) →* Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E) where
  toFun M := idem E T • M + (1 - idem E T) • (1 : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E))
  map_one' := by rw [← add_smul, add_sub_cancel, one_smul]
  map_mul' M N := by
    have h1 : idem E T * (1 - idem E T) = 0 := by rw [mul_sub, mul_one, idem_mul_self, sub_self]
    have h2 : (1 - idem E T) * idem E T = 0 := by rw [sub_mul, one_mul, idem_mul_self, sub_self]
    have h3 : (1 - idem E T) * (1 - idem E T) = 1 - idem E T := by rw [sub_mul, one_mul, h1, sub_zero]
    simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, smul_smul,
      idem_mul_self, h1, h2, h3, zero_smul, add_zero, zero_add]

def prjG (T : Finset (Pl E)) : GL (Fin n) (FiniteAdeleRing (𝓞 E) E) →* GL (Fin n) (FiniteAdeleRing (𝓞 E) E) :=
  Units.map (prjM E n T)

def Kglob : Subgroup (GL (Fin n) (FiniteAdeleRing (𝓞 E) E)) :=
  ⨅ w : Pl E, (GlobalTheory.LFun.KGL w (n := n)).comap (GeneralLinearGroup.map (pLoc E w))

instance t2Space_finiteAdeleRing : T2Space (FiniteAdeleRing (𝓞 E) E) :=
  T2Space.of_injective_continuous (f := fun x : FiniteAdeleRing (𝓞 E) E => (x : ∀ v : Pl E, v.adicCompletion E))
    Subtype.val_injective RestrictedProduct.continuous_coe

end GlobalTheory.EulerTw
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorObjectMapsComposeCancel
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorObjectMapsComposeCancel
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

namespace GlobalTheory.UPel.HT.MapComp

theorem lbIso_pull_comp {X Y Z : Scheme.{0}} {L : LB X} {M : LB Y} {a : Y ⟶ X} (h : LBIso M (L.pull a)) (j : Z ⟶ Y)
    {a' : Z ⟶ X} (e : a' = j ≫ a) : LBIso (M.pull j) (L.pull a') :=
  LBIso.chartPull (Geo.Tor.chartPullPull M j j rfl) (Geo.Tor.chartPullSame L _ (fun _ => a) _ j fun _ => e) h

theorem isSquare_comp {S S' S'' : Scheme.{0}} {G : Over S} {G' : Over S'} {G'' : Over S''} {φ : G'.left ⟶ G.left}
    {φ₂ : (G' ⊗ G').left ⟶ (G ⊗ G).left} {ψ : G''.left ⟶ G'.left} {ψ₂ : (G'' ⊗ G'').left ⟶ (G' ⊗ G').left}
    (h' : IsSquare ψ ψ₂) (h : IsSquare φ φ₂) : IsSquare (ψ ≫ φ) (ψ₂ ≫ φ₂) :=
  ⟨by rw [Category.assoc, h.1, ← Category.assoc, h'.1, Category.assoc],
    by rw [Category.assoc, h.2, ← Category.assoc, h'.2, Category.assoc]⟩

theorem isSquare_unique {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} {φ : G'.left ⟶ G.left}
    {a b : (G' ⊗ G').left ⟶ (G ⊗ G).left} (ha : IsSquare φ a) (hb : IsSquare φ b) : a = b := by
  apply pullback.hom_ext
  · exact ha.1.trans hb.1.symm
  · exact ha.2.trans hb.2.symm

theorem exists_isSquare {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} {f : S' ⟶ S} {φ : G'.left ⟶ G.left}
    (w : φ ≫ G.hom = G'.hom ≫ f) : ∃ φ₂ : (G' ⊗ G').left ⟶ (G ⊗ G).left, IsSquare φ φ₂ :=
  ⟨_, congrArg (fun z => z.left) (lift_fst (pushPt w (fst G' G')) (pushPt w (snd G' G'))),
    congrArg (fun z => z.left) (lift_snd (pushPt w (fst G' G')) (pushPt w (snd G' G')))⟩

end GlobalTheory.UPel.HT.MapComp

namespace GlobalTheory.UPel.HT

open GlobalTheory.UPel.HT.MapComp

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}

def MapComp.comp {S₁ S₂ S₃ : Scheme.{0}} {s₁ : S₁ ⟶ Sp R} {s₂ : S₂ ⟶ Sp R} {s₃ : S₃ ⟶ Sp R}
    {o₁ : Obj b N s₁} {o₂ : Obj b N s₂} {o₃ : Obj b N s₃} {f : S₁ ⟶ S₂} {g : S₂ ⟶ S₃}
    (m₁ : ObjMap o₁ o₂ f) (m₂ : ObjMap o₂ o₃ g) : ObjMap o₁ o₃ (f ≫ g) where
  φ := m₁.φ ≫ m₂.φ
  φ₂ := m₁.φ₂ ≫ m₂.φ₂
  cart := m₁.cart.comp m₂.cart
  sq := isSquare_comp m₁.sq m₂.sq
  act c := by rw [← Category.assoc, m₁.act, Category.assoc, m₂.act, Category.assoc]
  pol := LBIso.trans o₁.isLB (pull_isLB o₂.isLB _) (pull_isLB o₃.isLB _) m₁.pol (lbIso_pull_comp m₂.pol m₁.φ₂ rfl)
  eta y := by rw [← Category.assoc, m₁.eta, Category.assoc, m₂.eta, Category.assoc]

theorem MapComp.cancel {S₁ S₂ S₃ : Scheme.{0}} {s₁ : S₁ ⟶ Sp R} {s₂ : S₂ ⟶ Sp R} {s₃ : S₃ ⟶ Sp R}
    {o₁ : Obj b N s₁} {o₂ : Obj b N s₂} {o₃ : Obj b N s₃} {f : S₁ ⟶ S₂} {g : S₂ ⟶ S₃}
    (m : ObjMap o₁ o₃ (f ≫ g)) (m₂ : ObjMap o₂ o₃ g) : Nonempty (ObjMap o₁ o₂ f) := by
  have w : m.φ ≫ o₃.A.hom = (o₁.A.hom ≫ f) ≫ g := by rw [m.cart.1.w, Category.assoc]
  set φ := m₂.cart.1.lift m.φ (o₁.A.hom ≫ f) w
  have hφ : φ ≫ m₂.φ = m.φ := m₂.cart.1.lift_fst _ _ _
  have hφ' : φ ≫ o₂.A.hom = o₁.A.hom ≫ f := m₂.cart.1.lift_snd _ _ _
  have n : IsGrpPullback o₁.A o₃.A (f ≫ g) (φ ≫ m₂.φ) := by rw [hφ]; exact m.cart
  obtain ⟨φ₂, sq⟩ := exists_isSquare hφ'
  have e : m.φ₂ = φ₂ ≫ m₂.φ₂ := isSquare_unique m.sq (hφ ▸ isSquare_comp sq m₂.sq)
  have hact : ∀ c, (o₁.act.act c).left ≫ φ = φ ≫ (o₂.act.act c).left := by
    intro c
    apply m₂.cart.1.hom_ext
    · rw [Category.assoc, hφ, m.act, Category.assoc, m₂.act, ← Category.assoc, hφ]
    · rw [Category.assoc, hφ', ← Category.assoc, Over.w, Category.assoc, Over.w, hφ']
  have heta : ∀ y, (o₁.eta y).left ≫ φ = f ≫ (o₂.eta y).left := by
    intro y
    apply m₂.cart.1.hom_ext
    · rw [Category.assoc, hφ, m.eta, Category.assoc, Category.assoc, m₂.eta]
    · rw [Category.assoc, hφ', ← Category.assoc, Over.w, Category.assoc, Over.w]
      show 𝟙 _ ≫ f = f ≫ 𝟙 _
      rw [Category.id_comp, Category.comp_id]
  exact ⟨{ φ := φ
           φ₂ := φ₂
           cart := m₂.cart.cancel n hφ'
           sq := sq
           act := hact
           pol := LBIso.trans o₁.isLB (pull_isLB o₃.isLB _) (pull_isLB o₂.isLB _) m.pol
             (LBIso.symm (lbIso_pull_comp m₂.pol φ₂ e))
           eta := heta }⟩

theorem objMap_comp_cancel (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ)
    (S₁ S₂ S₃ : Scheme.{0}) (s₁ : S₁ ⟶ Sp R) (s₂ : S₂ ⟶ Sp R) (s₃ : S₃ ⟶ Sp R) (o₁ : Obj b N s₁) (o₂ : Obj b N s₂)
    (o₃ : Obj b N s₃) (f : S₁ ⟶ S₂) (g : S₂ ⟶ S₃) :
    (Nonempty (ObjMap o₁ o₂ f) → Nonempty (ObjMap o₂ o₃ g) → Nonempty (ObjMap o₁ o₃ (f ≫ g))) ∧
      (Nonempty (ObjMap o₁ o₃ (f ≫ g)) → Nonempty (ObjMap o₂ o₃ g) → Nonempty (ObjMap o₁ o₂ f)) :=
  ⟨fun ⟨m₁⟩ ⟨m₂⟩ => ⟨MapComp.comp m₁ m₂⟩, fun ⟨m⟩ ⟨m₂⟩ => MapComp.cancel m m₂⟩

end GlobalTheory.UPel.HT
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorObjectMapsComposeCancelStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harris_taylor_object_maps_compose_cancel : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (S₁ S₂ S₃ : Scheme.{0}) (s₁ : S₁ ⟶ Sp R) (s₂ : S₂ ⟶ Sp R) (s₃ : S₃ ⟶ Sp R) (o₁ : GlobalTheory.UPel.HT.Obj b N s₁) (o₂ : GlobalTheory.UPel.HT.Obj b N s₂) (o₃ : GlobalTheory.UPel.HT.Obj b N s₃) (f : S₁ ⟶ S₂) (g : S₂ ⟶ S₃), (Nonempty (GlobalTheory.UPel.HT.ObjMap o₁ o₂ f) → Nonempty (GlobalTheory.UPel.HT.ObjMap o₂ o₃ g) → Nonempty (GlobalTheory.UPel.HT.ObjMap o₁ o₃ (f ≫ g))) ∧ (Nonempty (GlobalTheory.UPel.HT.ObjMap o₁ o₃ (f ≫ g)) → Nonempty (GlobalTheory.UPel.HT.ObjMap o₂ o₃ g) → Nonempty (GlobalTheory.UPel.HT.ObjMap o₁ o₂ f)) := by
  first | exact @GlobalTheory.UPel.HT.objMap_comp_cancel | exact GlobalTheory.UPel.HT.objMap_comp_cancel | (intros; apply GlobalTheory.UPel.HT.objMap_comp_cancel <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParP
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LeviDesc

def cavg {G : Type} [Group G] (K : Subgroup G) (f : G → ℂ) (x : G) : ℂ :=
  avg fun k : K => f ((k : G)⁻¹ * x * k)

def adL {k : Type} [Field k] {a b : ℕ} (A : GL (Fin a) k) (B : Matrix (Fin b) (Fin b) k) :
    Matrix (Fin a) (Fin b) k →ₗ[k] Matrix (Fin a) (Fin b) k where
  toFun X := X - (A⁻¹ : GL (Fin a) k).val * X * B
  map_add' X Y := by simp only [Matrix.mul_add, Matrix.add_mul]; abel
  map_smul' c X := by simp [Matrix.mul_smul, Matrix.smul_mul, smul_sub]

variable {E : Type} [Field E] [NumberField E]

def parP (a n : ℕ) (w : Pl E) : Subgroup (GLw n w) where
  carrier := {g | (g : Matrix (Fin n) (Fin n) (w.adicCompletion E)).BlockTriangular fun i : Fin n => decide (a ≤ (i : ℕ))}
  mul_mem' {g h} hg hh := by
    simp only [Set.mem_ofPred_eq, Units.val_mul] at *
    exact hg.mul hh
  one_mem' := by
    simp only [Set.mem_ofPred_eq, Units.val_one]
    exact Matrix.blockTriangular_one
  inv_mem' {g} hg := by
    let := g.invertible
    simp only [Set.mem_ofPred_eq, Matrix.coe_units_inv] at *
    exact Matrix.blockTriangular_inv_of_blockTriangular hg

def orbN {n a b : ℕ} (h : a + b = n) (w : Pl E) (f : GLw n w → ℂ) (m : GLw a w × GLw b w) : ℂ :=
  hint (intMat a b w) fun X => cavg (GlobalTheory.LFun.KGL w (n := n)) f
    ((blk h w 1 (Multiplicative.toAdd X))⁻¹ * blk h w m 0 * blk h w 1 (Multiplicative.toAdd X))

end GlobalTheory.LeviDesc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DgMatOne
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC
  Formalism.L2.Host GlobalTheory.BCT
open scoped Classical

namespace GlobalTheory.BCT.CtLevel

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

abbrev blkEq {a b n : ℕ} (h : a + b = n) : Fin a ⊕ Fin b ≃ Fin n := finSumFinEquiv.trans (finCongr h)

def dgMat {R : Type} [CommRing R] {a b n : ℕ} (h : a + b = n) (A : Matrix (Fin a) (Fin a) R)
    (D : Matrix (Fin b) (Fin b) R) : Matrix (Fin n) (Fin n) R :=
  reindex (blkEq h) (blkEq h) (fromBlocks A 0 0 D)

theorem dgMat_mul {R : Type} [CommRing R] {a b n : ℕ} (h : a + b = n) (A A' : Matrix (Fin a) (Fin a) R)
    (D D' : Matrix (Fin b) (Fin b) R) : dgMat h A D * dgMat h A' D' = dgMat h (A * A') (D * D') := by
  simp only [dgMat, reindex_apply, submatrix_mul_equiv, fromBlocks_multiply]
  simp

theorem dgMat_one {R : Type} [CommRing R] {a b n : ℕ} (h : a + b = n) :
    dgMat h (1 : Matrix (Fin a) (Fin a) R) (1 : Matrix (Fin b) (Fin b) R) = 1 := by
  rw [dgMat, fromBlocks_one, reindex_apply, submatrix_one_equiv]

def dgM {a b n : ℕ} (h : a + b = n) (w : Pl E) : GLw a w × GLw b w →* GLw n w where
  toFun k := ⟨dgMat h k.1.val k.2.val, dgMat h (k.1⁻¹).val (k.2⁻¹).val,
    by rw [dgMat_mul, Units.mul_inv, Units.mul_inv, dgMat_one],
    by rw [dgMat_mul, Units.inv_mul, Units.inv_mul, dgMat_one]⟩
  map_one' := Units.ext (by simp [dgMat_one])
  map_mul' x y := Units.ext (by simp [dgMat_mul])

theorem dgM_val {a b n : ℕ} (h : a + b = n) (w : Pl E) (k : GLw a w × GLw b w) :
    (dgM h w k).val = dgMat h k.1.val k.2.val := rfl

def lev₁ {a b n : ℕ} (h : a + b = n) (w : Pl E) (N : Subgroup (GLw n w)) (μ : (w.adicCompletion E)ˣ →* ℂˣ) :
    Subgroup (GLw a w) :=
  GlobalTheory.LFun.KGL w (n := a) ⊓ N.comap ((dgM h w).comp (MonoidHom.inl _ _)) ⊓ μ.ker.comap GeneralLinearGroup.det

def lev₂ {a b n : ℕ} (h : a + b = n) (w : Pl E) (N : Subgroup (GLw n w)) (μ : (w.adicCompletion E)ˣ →* ℂˣ) :
    Subgroup (GLw b w) :=
  GlobalTheory.LFun.KGL w (n := b) ⊓ N.comap ((dgM h w).comp (MonoidHom.inr _ _)) ⊓ μ.ker.comap GeneralLinearGroup.det

theorem blk_val {n a b : ℕ} (h : a + b = n) (w : Pl E) (m : GLw a w × GLw b w)
    (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)) :
    (blk h w m X).val = reindex (blkEq h) (blkEq h) (fromBlocks m.1.val (m.1.val * X) 0 m.2.val) := by
  have hu : IsUnit (reindex (blkEq h) (blkEq h) (fromBlocks m.1.val (m.1.val * X) 0 m.2.val)) := by
    rw [isUnit_iff_isUnit_det, det_reindex_self, det_fromBlocks_zero₂₁]
    exact (m.1.isUnit.map detMonoidHom).mul (m.2.isUnit.map detMonoidHom)
  unfold blk
  simp only
  rw [dite_eq_left hu]
  rfl

end GlobalTheory.BCT.CtLevel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlagDomainDataPrincipalCongruenceLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlagDomainDataPrincipalCongruenceLevel
open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.LevGeo
open scoped ENNReal

namespace GlobalTheory.PrincData

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem isIntegral_cc {x : E} (hx : IsIntegral ℤ x) : IsIntegral ℤ (cc x) :=
  hx.map ((IsCMField.complexConj E : E →+* E).toIntAlgHom)

theorem herm_add_left (G : Matrix (Fin r) (Fin r) E) (x x' y : Fin r → E) :
    herm G (x + x') y = herm G x y + herm G x' y := by
  simp only [herm, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem herm_add_right (G : Matrix (Fin r) (Fin r) E) (x y y' : Fin r → E) :
    herm G x (y + y') = herm G x y + herm G x y' := by
  simp only [herm, cc, Pi.add_apply, map_add (f := _), mul_add, Finset.sum_add_distrib]

theorem herm_smul_left (G : Matrix (Fin r) (Fin r) E) (c : 𝓞 E) (x y : Fin r → E) :
    herm G (c • x) y = (c : E) * herm G x y := by
  simp only [herm, Pi.smul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [Algebra.smul_def, show algebraMap (𝓞 E) E c = (c : E) from rfl]; ring

theorem herm_smul_right (G : Matrix (Fin r) (Fin r) E) (c : 𝓞 E) (x y : Fin r → E) :
    herm G x (c • y) = cc (c : E) * herm G x y := by
  simp only [herm, Pi.smul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [Algebra.smul_def]
  simp only [cc, map_mul]
  ring

theorem exists_nat_herm_int (G : Matrix (Fin r) (Fin r) E) (L : Submodule (𝓞 E) (Fin r → E)) (hL : L.FG) :
    ∃ n : ℕ, 0 < n ∧ ∀ x ∈ L, ∀ y ∈ L, IsIntegral ℤ ((n : E) * herm G x y) := by
  classical
  obtain ⟨s, rfl⟩ := hL
  obtain ⟨y0, hy0, hy⟩ := exists_integral_multiples ℤ ℚ ((s ×ˢ s).image fun p => herm G p.1 p.2)
  have hgen : ∀ a ∈ s, ∀ b ∈ s, IsIntegral ℤ ((y0 : E) * herm G a b) := fun a ha b hb => by
    have h := hy _ (Finset.mem_image.2 ⟨(a, b), Finset.mem_product.2 ⟨ha, hb⟩, rfl⟩)
    rwa [zsmul_eq_mul] at h
  have hright : ∀ a ∈ s, ∀ y ∈ Submodule.span (𝓞 E) (s : Set (Fin r → E)),
      IsIntegral ℤ ((y0 : E) * herm G a y) := by
    intro a ha y hy'
    induction hy' using Submodule.span_induction with
    | mem b hb => exact hgen a ha b hb
    | zero => simpa [herm, cc] using isIntegral_zero
    | add u v _ _ hu hv => rw [herm_add_right, mul_add]; exact hu.add hv
    | smul c u _ hu => rw [herm_smul_right, mul_left_comm]; exact (isIntegral_cc c.2).mul hu
  have hall : ∀ x ∈ Submodule.span (𝓞 E) (s : Set (Fin r → E)), ∀ y ∈ Submodule.span (𝓞 E) (s : Set (Fin r → E)),
      IsIntegral ℤ ((y0 : E) * herm G x y) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem a ha => exact hright a ha
    | zero => intro y _; simpa [herm] using isIntegral_zero
    | add u v _ _ hu hv => intro y hy'; rw [herm_add_left, mul_add]; exact (hu y hy').add (hv y hy')
    | smul c u _ hu => intro y hy'; rw [herm_smul_left, mul_left_comm]; exact c.2.mul (hu y hy')
  refine ⟨y0.natAbs, Int.natAbs_pos.2 hy0, fun x hx y hy' => ?_⟩
  have key := hall x hx y hy'
  rcases Int.natAbs_eq y0 with h | h
  · have e : ((y0.natAbs : ℕ) : E) = (y0 : E) := by
      have h' := congrArg (fun z : ℤ => (z : E)) h
      simp only [Int.cast_natCast] at h'
      exact h'.symm
    rw [e]; exact key
  · have e : ((y0.natAbs : ℕ) : E) = -(y0 : E) := by
      have h' := congrArg (fun z : ℤ => (z : E)) h
      simp only [Int.cast_neg, Int.cast_natCast] at h'
      rw [h', neg_neg]
    rw [e, neg_mul]; exact key.neg

theorem exists_nat_int (k : E) : ∃ n : ℕ, 0 < n ∧ IsIntegral ℤ ((n : E) * k) := by
  have halg : IsAlgebraic ℤ k := (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic _)
  obtain ⟨y, hy, hyi⟩ := halg.exists_integral_multiple
  refine ⟨y.natAbs, Int.natAbs_pos.2 hy, ?_⟩
  rw [zsmul_eq_mul] at hyi
  rcases Int.natAbs_eq y with h | h
  · have e : ((y.natAbs : ℕ) : E) = (y : E) := by
      have h' := congrArg (fun z : ℤ => (z : E)) h
      simp only [Int.cast_natCast] at h'
      exact h'.symm
    rw [e]; exact hyi
  · have e : ((y.natAbs : ℕ) : E) = -(y : E) := by
      have h' := congrArg (fun z : ℤ => (z : E)) h
      simp only [Int.cast_neg, Int.cast_natCast] at h'
      rw [h', neg_neg]
    rw [e, neg_mul]; exact hyi.neg

theorem exists_princ_data : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (M : ℕ) (X0 : Data E r) (Λ : Submodule (𝓞 E) (Fin r → E)), 3 ≤ M → Λ.FG → Submodule.span E (Λ : Set (Fin r → E)) = ⊤ → ∃ X : Data E r, X.Gm = X0.Gm ∧ X.Ψ = X0.Ψ ∧ X.p0 = X0.p0 ∧ X.Λ = Λ ∧ ∀ γ, γ ∈ X.Γ ↔ IsUStab X0.Gm Λ γ ∧ ∀ x ∈ Λ, ∃ y ∈ Λ, (γ : Matrix (Fin r) (Fin r) E).mulVec x - x = M • y := by
  intro E _ _ _ r M X0 Λ hM hfg hsp
  obtain ⟨n, hn, hnint⟩ := exists_nat_herm_int X0.Gm Λ hfg
  obtain ⟨k, hk, hkint⟩ := exists_nat_int X0.κ0
  have hM0 : (M : E) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hint : ∀ x ∈ Λ, ∀ y ∈ Λ,
      IsIntegral ℤ (((M * n * k : ℕ) : E) / (M : E) * X0.κ0 * herm X0.Gm x y) := by
    intro x hx y hy
    have e : ((M * n * k : ℕ) : E) / (M : E) * X0.κ0 * herm X0.Gm x y =
        ((k : E) * X0.κ0) * ((n : E) * herm X0.Gm x y) := by
      push_cast
      field_simp
    rw [e]
    exact hkint.mul (hnint x hx y hy)
  obtain ⟨X, hΨ, hG, hp, hΛ, -, -, -, hΓ, -⟩ := GlobalTheory.FlagData.exists_data GlobalTheory.latMinkowski E r X0.p0 M (M * n * k)
    X0.Ψ X0.Gm Λ X0.ξ0 X0.κ0 X0.cmType X0.Gm_herm X0.Gm_det X0.p0_le
    (fun τ hτ => X0.signature ⟨τ, hτ⟩) hfg hsp hM X0.ξ0_im X0.ξ0_ne X0.κ0_xi
    (fun τ hτ => X0.κ0_sign ⟨τ, hτ⟩) (by positivity) hint
  refine ⟨X, hG, hΨ, hp, hΛ, fun γ => ?_⟩
  rw [hΓ γ]
  refine and_congr Iff.rfl (forall₂_congr fun x _ => exists_congr fun y => and_congr Iff.rfl ?_)
  exact sub_eq_iff_eq_add'.symm

end GlobalTheory.PrincData
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlagDomainDataPrincipalCongruenceLevelStatement
open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.LevGeo
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_flagDomainData_principalCongruenceLevel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (M : ℕ) (X0 : Data E r) (Λ : Submodule (𝓞 E) (Fin r → E)), 3 ≤ M → Λ.FG → Submodule.span E (Λ : Set (Fin r → E)) = ⊤ → ∃ X : Data E r, X.Gm = X0.Gm ∧ X.Ψ = X0.Ψ ∧ X.p0 = X0.p0 ∧ X.Λ = Λ ∧ ∀ γ, γ ∈ X.Γ ↔ IsUStab X0.Gm Λ γ ∧ ∀ x ∈ Λ, ∃ y ∈ Λ, (γ : Matrix (Fin r) (Fin r) E).mulVec x - x = M • y := by
  first | exact @GlobalTheory.PrincData.exists_princ_data | exact GlobalTheory.PrincData.exists_princ_data | (intros; apply GlobalTheory.PrincData.exists_princ_data <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCentralIdempotentOfGoodSeriesIdempotent
section -- merged from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnipotentLatticeMembership
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.UnipotentLatticeMembership

open NumberField IsDedekindDomain Formalism.IndefR.Arith

section Clause

variable {LL Ks : Type} [Field LL] [NumberField LL] [Field Ks] [NumberField Ks] [Algebra Ks LL]
variable {WL : Type} [AddCommGroup WL] [Module LL WL] [Module Ks WL] [IsScalarTower Ks LL WL]
  [Module (𝓞 LL) WL] [IsScalarTower (𝓞 LL) LL WL] [Module (𝓞 Ks) WL] [IsScalarTower (𝓞 Ks) Ks WL]
variable {W : (LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)]
variable {G0 : Type} [Group G0] [Fintype G0]
variable (A : FormsL LL Ks WL W G0) (J0 : Subgroup G0) (lam0 : J0 →* LLˣ) (eC : G0 → LL)

variable {A J0 lam0 eC}

end Clause

section Level

open Formalism.BasicNotions Formalism.L2.DIV

variable (D : D7) {LL : Type} [Field LL]

abbrev TypePl : Type := Σ k : Fin 2, D.nd.PlG k

instance finiteLevelGroupFintype : Fintype (G0g D.nd) :=
  haveI : ∀ k, NeZero (D.host.g k) := fun k => ⟨(D.host.g_prime k).ne_zero⟩
  Fintype.ofFinite _

end Level

section Rec

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.MainNotions.DIV.Cons

variable {D : D7}

end Rec

end GlobalTheory.IndefiniteRowSideFullHecke.UnipotentLatticeMembership
end
end

noncomputable section

namespace GlobalTheory.GoodLatCompare

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.IndefR.Arith Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.GoodBasisCentralIdempotents GlobalTheory.IndefiniteRowSideFullHecke.UnipotentLatticeMembership

section Clause

variable {LL Ks : Type} [Field LL] [NumberField LL] [Field Ks] [NumberField Ks] [Algebra Ks LL]
variable {WL : Type} [AddCommGroup WL] [Module LL WL] [Module Ks WL] [IsScalarTower Ks LL WL]
  [Module (𝓞 LL) WL] [IsScalarTower (𝓞 LL) LL WL] [Module (𝓞 Ks) WL] [IsScalarTower (𝓞 Ks) Ks WL]
variable {W : (LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)]
variable {G G' : Type} [Group G] [Fintype G] [Group G'] [Fintype G']


end Clause

section Forms

variable {D : D7} (T : Core D) (j : ℕ) (w : WeightFamilies.Wt D j)
variable {LL : Type} [Field LL] [NumberField LL] [Algebra T.Q.c.F LL]
variable {WL : Type} [AddCommGroup WL] [Module LL WL] [Module T.Q.c.F WL] [IsScalarTower T.Q.c.F LL WL]
  [Module (𝓞 T.Q.c.F) WL] [IsScalarTower (𝓞 T.Q.c.F) T.Q.c.F WL]
variable {W : (LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)]
variable {G : Type} [Group G]

end Forms

section Local

variable {κ κ' : Type} [CommRing κ] [CommRing κ'] {r : ℕ}

end Local

structure PlaceIso (D : D7) (Pg : Finset (Pl D.host.E)) where
  pl : TypePl D ≃ ↥Pg
  iso : ∀ v : TypePl D, ZMod (D.host.g v.1) ≃+* kP (pl v).1

namespace PlaceIso

variable {D : D7} {Pg : Finset (Pl D.host.E)} (P : PlaceIso D Pg) {LL : Type} [Field LL]

end PlaceIso

section Places

open scoped Pointwise

variable {D : D7}

variable {T : Core D} (hb : ∀ k, ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ (T.pb k).asIdeal)
include hb

end Places


open GlobalTheory.MemN.TypesInhab in
theorem goodSeriesIdempotent_central_idempotent (D : D7) :
    D.ntypes.e0 ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd)) ∧ D.ntypes.e0 * D.ntypes.e0 = D.ntypes.e0 := by
  classical
  haveI : ∀ k, NeZero (D.host.g k) := fun k => ⟨(D.host.g_prime k).ne_zero⟩
  haveI : ∀ k, Fact (D.host.g k).Prime := fun k => ⟨D.host.g_prime k⟩
  obtain ⟨hc, hm⟩ := good_sum (I := TypePl D) (P := fun v => Fin D.R.r → ZMod (D.host.g v.1))
    (fun v p => D.ntypes.eSer v.1 (Formalism.CyclotomicNorms.monicOf p))
    (fun a => D.ntypes.goodTuple (fun k v => Formalism.CyclotomicNorms.monicOf (a ⟨k, v⟩))) D.ntypes.e0 (fun g => rfl)
    (fun _ _ => D.ntypes.eSer_idem _ _) (fun _ _ => D.ntypes.eSer_central _ _)
    (fun _ p q hpq => D.ntypes.eSer_orth _ _ _ fun h => hpq (funext fun i => by
      rw [← Formalism.CyclotomicNorms.Sqf.coeff_monicOf_lt p i, h, Formalism.CyclotomicNorms.Sqf.coeff_monicOf_lt]))
  refine ⟨hc, ?_⟩
  have h : D.ntypes.e0 = ∑ a : ∀ v : TypePl D, Fin D.R.r → ZMod (D.host.g v.1),
      if D.ntypes.goodTuple (fun k v => Formalism.CyclotomicNorms.monicOf (a ⟨k, v⟩)) then
        ten (fun v => D.ntypes.eSer v.1 (Formalism.CyclotomicNorms.monicOf (a v))) else 0 := by
    ext g
    rw [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
    refine (finsum_eq_sum_of_fintype _).trans (Finset.sum_congr rfl fun a _ => ?_)
    split_ifs <;> rfl
  conv_lhs => rhs; rw [h]
  rw [Finset.mul_sum]
  conv_rhs => rw [h]
  refine Finset.sum_congr rfl fun a _ => ?_
  split_ifs with ha
  · rw [hm, if_pos ha]
  · rw [mul_zero]

theorem isCentralIdempotent_of_goodSeriesIdempotent {D : D7} {LL : Type} [Field LL] (σ₀ : LL →+* ℂ) {eC : G0g D.nd → LL}
    (h : ∀ g, σ₀ (eC g) = D.ntypes.e0.coeff g) : IsCentralIdem eC := by
  obtain ⟨hc, hi⟩ := goodSeriesIdempotent_central_idempotent D
  refine ⟨fun g x => σ₀.injective ?_, fun g => σ₀.injective ?_⟩
  · have := congrArg (fun z => z.coeff (x * g))
      (Subalgebra.mem_center_iff.1 hc (MonoidAlgebra.single x (1 : ℂ)))
    simp only [MonoidAlgebra.coeff_single_mul_apply, MonoidAlgebra.coeff_mul_single_apply, inv_mul_cancel_left, one_mul, mul_one] at this
    rw [h, h, this]
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [map_sum, h, ← hi, GlobalTheory.MemN.TypesInhab.coeff_mul_sum]
      exact Finset.sum_congr rfl fun x _ => by rw [map_mul, h, h]

section Sides

variable {D : D7} (T : Core D) (j : ℕ) (w : WeightFamilies.Wt D j)
  (LL : Type) [Field LL] [NumberField LL] [Algebra T.Q.c.F LL]

end Sides

end GlobalTheory.GoodLatCompare
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HcfjHolds
namespace GlobalTheory.Laid

theorem hcfj_holds : GlobalTheory.Published.HilbertClassFieldJ := GlobalTheory.CompanionTheory.Hypotheses₂.hilbertClassFieldJ

end GlobalTheory.Laid
end
