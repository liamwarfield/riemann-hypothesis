module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvUAbsU
public import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.AbsGeneratorRatioEqOneOfUnitFrameMove
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateFreeOfCard
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuadraticHeckeCharCMEqIdeleInfiniteSignFiniteTri
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuadraticHeckeCharCMEqIdeleInfiniteSignFiniteTri
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.EtaInfSign

open GlobalTheory.QuadSymbol

variable (E : Type) [Field E] [NumberField E] [IsCMField E]

theorem mem_normGroup_of_pos (v : InfinitePlace (maximalRealSubfield E)) (y : (v.Completion)ˣ)
    (hy : 0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal (IsTotallyReal.isReal v) (y : v.Completion)) :
    y ∈ normGroup (maximalRealSubfield E) E v.Completion := by
  obtain ⟨δ, b, hδ, h0, h1⟩ := AlmostNorm.exists_basis_sq (maximalRealSubfield E) E
  rw [mem_normGroup_iff_form b h0 h1]
  let e := InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal v)
  have hy' : 0 < e y := hy
  refine ⟨e.symm (Real.sqrt (e y)), 0, e.injective ?_⟩
  simp only [map_sub, map_pow, map_mul, map_zero, RingEquiv.apply_symm_apply]
  rw [zero_pow two_ne_zero, mul_zero, sub_zero, Real.sq_sqrt hy'.le]

theorem not_mem_normGroup_of_neg (v : InfinitePlace (maximalRealSubfield E)) (y : (v.Completion)ˣ)
    (hy : InfinitePlace.Completion.extensionEmbeddingOfIsReal (IsTotallyReal.isReal v) (y : v.Completion) < 0) :
    y ∉ normGroup (maximalRealSubfield E) E v.Completion := by
  intro hmem
  have hneg : (-y) ∈ normGroup (maximalRealSubfield E) E v.Completion := by
    refine mem_normGroup_of_pos E v (-y) ?_
    rw [Units.val_neg, map_neg]
    exact neg_pos.2 hy
  have h1 : (-1 : (v.Completion)ˣ) ∈ normGroup (maximalRealSubfield E) E v.Completion := by
    have : (-1 : (v.Completion)ˣ) = y * (-y)⁻¹ := by
      rw [inv_neg, mul_neg, mul_inv_cancel]
    rw [this]
    exact mul_mem hmem (inv_mem hneg)
  exact eta_eq_neg_one_iff.1 (GlobalTheory.GalOfCusp.eta_neg_one E v) h1

theorem eta_real (v : InfinitePlace (maximalRealSubfield E)) (y : (v.Completion)ˣ) :
    eta (maximalRealSubfield E) E v.Completion y =
      if 0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal (IsTotallyReal.isReal v) (y : v.Completion)
      then 1 else -1 := by
  split_ifs with h
  · exact eta_eq_one_iff.2 (mem_normGroup_of_pos E v y h)
  · have h0 : InfinitePlace.Completion.extensionEmbeddingOfIsReal (IsTotallyReal.isReal v) (y : v.Completion) ≠ 0 :=
      fun h' => y.ne_zero ((InfinitePlace.Completion.extensionEmbeddingOfIsReal _).injective (h'.trans (map_zero _).symm))
    exact eta_eq_neg_one_iff.2 (not_mem_normGroup_of_neg E v y (lt_of_le_of_ne (not_lt.1 h) h0))

theorem embedding_comp_algebraMap (w : InfinitePlace E) :
    (w.comap (algebraMap (maximalRealSubfield E) E)).embedding =
      w.embedding.comp (algebraMap (maximalRealSubfield E) E) := by
  have hw : w.comap (algebraMap (maximalRealSubfield E) E) =
      InfinitePlace.mk (w.embedding.comp (algebraMap (maximalRealSubfield E) E)) := by
    conv_lhs => rw [← InfinitePlace.mk_embedding w]
    rw [InfinitePlace.comap_mk]
  rw [hw]
  rcases InfinitePlace.embedding_mk_eq (w.embedding.comp (algebraMap (maximalRealSubfield E) E)) with h | h
  · exact h
  · rw [h]
    exact ComplexEmbedding.isReal_iff.1 (IsTotallyReal.complexEmbedding_isReal _)

theorem extensionEmbedding_completionMap (w : InfinitePlace E)
    (x : (w.comap (algebraMap (maximalRealSubfield E) E)).Completion) :
    InfinitePlace.Completion.extensionEmbedding w
      (AbsoluteValue.Completion.map (w.comap (algebraMap (maximalRealSubfield E) E)).1 w.1 x) =
    ((InfinitePlace.Completion.extensionEmbeddingOfIsReal (IsTotallyReal.isReal _) x : ℝ) : ℂ) := by
  induction x using AbsoluteValue.Completion.induction_on with
  | hp =>
    exact isClosed_eq ((InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.comp
        (AbsoluteValue.Completion.continuous_map _ _))
      (Complex.continuous_ofReal.comp (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal _).continuous)
  | ih a =>
    rw [AbsoluteValue.Completion.map_coe, InfinitePlace.Completion.extensionEmbedding_coe,
      InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe, InfinitePlace.embedding_of_isReal_apply,
      embedding_comp_algebraMap]
    rfl

theorem unitDir_ofReal (r : ℝ) (hr : r ≠ 0) (u : ℂˣ) (hu : (u : ℂ) = r) :
    GlobalTheory.ConsEta.unitDir u = Units.map (Int.castRingHom ℂ).toMonoidHom (if 0 < r then 1 else -1) := by
  ext
  change (u : ℂ) / (‖(u : ℂ)‖ : ℂ) = _
  rw [hu, Complex.norm_real, Real.norm_eq_abs]
  split_ifs with h
  · rw [abs_of_pos h, div_self (Complex.ofReal_ne_zero.2 hr)]
    simp
  · rw [abs_of_neg (lt_of_le_of_ne (not_lt.1 h) hr), Complex.ofReal_neg, div_neg, div_self (Complex.ofReal_ne_zero.2 hr)]
    simp

end GlobalTheory.EtaInfSign


open GlobalTheory.QuadSymbol in
theorem GlobalTheory.EtaInfSign.quadChar_eq_infSign : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (b : Neutral.B1.Ideles (maximalRealSubfield E)),
    (∀ v, (b : AdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E)).2 v = 1) →
    (GlobalTheory.GalOfCusp.quadChar E).1 b = GlobalTheory.ConsEta.infSign E (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E b) := by
  intro E _ _ _ b hb
  have hfin : GlobalTheory.IdeleNormChar.finComp b = 1 := funext fun v => Units.ext (hb v)
  have hL : (GlobalTheory.GalOfCusp.quadChar E).1 b = Units.map (Int.castRingHom ℂ).toMonoidHom
      (∏ v : InfinitePlace (maximalRealSubfield E),
        eta (maximalRealSubfield E) E v.Completion (GlobalTheory.IdeleNormChar.infComp b v)) := by
    change Units.map _ (etaProd _ E (GlobalTheory.IdeleNormChar.finComp b) (GlobalTheory.IdeleNormChar.infComp b)) = _
    unfold etaProd
    rw [hfin]
    have h1 : (fun v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)) =>
        eta (maximalRealSubfield E) E (v.adicCompletion _) ((1 : FinFam (maximalRealSubfield E)) v)) = fun _ => 1 :=
      funext fun v => eta_eq_one_iff.2 (one_mem _)
    rw [h1, finprod_one, one_mul]
  rw [hL, map_prod, GlobalTheory.ConsEta.infSign, MonoidHom.finsetProd_apply]
  symm
  refine Fintype.prod_equiv (IsCMField.equivInfinitePlace E) _ _ fun w => ?_
  rw [IsCMField.equivInfinitePlace_apply, GlobalTheory.EtaInfSign.eta_real]
  have hv := IsTotallyReal.isReal (w.comap (algebraMap (maximalRealSubfield E) E))
  refine GlobalTheory.EtaInfSign.unitDir_ofReal _ ?_ _ ?_
  · intro h'
    exact (GlobalTheory.IdeleNormChar.infComp b _).ne_zero
      ((InfinitePlace.Completion.extensionEmbeddingOfIsReal hv).injective (by rw [map_zero]; exact h'))
  · exact GlobalTheory.EtaInfSign.extensionEmbedding_completionMap E w _
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuadraticHeckeCharCMEqIdeleInfiniteSignFiniteTriStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quadraticHeckeCharCM_eq_ideleInfiniteSign_finiteTrivial : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (b : Neutral.B1.Ideles (maximalRealSubfield E)),
    (∀ v, (b : AdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E)).2 v = 1) →
    (GlobalTheory.GalOfCusp.quadChar E).1 b = GlobalTheory.ConsEta.infSign E (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E b) := by
  first | exact @GlobalTheory.EtaInfSign.quadChar_eq_infSign | exact GlobalTheory.EtaInfSign.quadChar_eq_infSign | (intros; apply GlobalTheory.EtaInfSign.quadChar_eq_infSign <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntValuationPrimeBack
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo GlobalTheory.LevPull GlobalTheory.FieldBC
open scoped ENNReal
open IsDedekindDomain

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GalSup

section Prime

variable {K : Type} [Field K] [NumberField K]

abbrev primeBack (s : K ≃+* K) (la : HeightOneSpectrum (𝓞 K)) : HeightOneSpectrum (𝓞 K) :=
  HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv s).symm la

theorem count_equiv {R S : Type} [CommRing R] [IsDedekindDomain R] [CommRing S] [IsDedekindDomain S]
    [DecidableEq (Associates (Ideal R))] [∀ p : Associates (Ideal R), Decidable (Irreducible p)]
    [DecidableEq (Associates (Ideal S))] [∀ p : Associates (Ideal S), Decidable (Irreducible p)]
    (e : R ≃+* S) (p : HeightOneSpectrum R) {I : Ideal R} (hI : I ≠ ⊥) :
    (Associates.mk (HeightOneSpectrum.equivOfRingEquiv e p).asIdeal).count (Associates.mk (I.comap e.symm)).factors =
      (Associates.mk p.asIdeal).count (Associates.mk I).factors := by
  have hI' : I.comap e.symm ≠ ⊥ := by
    rw [← Ideal.map_comap_of_equiv]
    exact fun h => hI ((Ideal.map_eq_bot_iff_of_injective e.injective).1 h)
  refine eq_of_forall_le_iff fun k => ?_
  rw [← Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.2 hI') (HeightOneSpectrum.associates_irreducible _),
    ← Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.2 hI) (HeightOneSpectrum.associates_irreducible _),
    ← Associates.mk_pow, ← Associates.mk_pow, Associates.mk_le_mk_iff_dvd, Associates.mk_le_mk_iff_dvd,
    Ideal.dvd_iff_le, Ideal.dvd_iff_le]
  have : (HeightOneSpectrum.equivOfRingEquiv e p).asIdeal = p.asIdeal.map (e : R →+* S) := by
    rw [Ideal.map_comap_of_equiv]; rfl
  rw [this, ← Ideal.map_pow, Ideal.map_comap_of_equiv]
  exact Ideal.comap_le_comap_iff_of_surjective e.symm e.symm.surjective _ _

theorem intValuation_primeBack (s : K ≃+* K) (la : HeightOneSpectrum (𝓞 K)) (a : 𝓞 K) :
    (primeBack s la).intValuation a = la.intValuation (RingOfIntegers.mapRingEquiv s a) := by
  classical
  by_cases ha : a = 0
  · subst ha; simp
  have ha' : RingOfIntegers.mapRingEquiv s a ≠ 0 := by simpa using ha
  rw [HeightOneSpectrum.intValuation_if_neg _ ha, HeightOneSpectrum.intValuation_if_neg _ ha']
  have hc : (Ideal.span {RingOfIntegers.mapRingEquiv s a}).comap (RingOfIntegers.mapRingEquiv s).symm.symm =
      Ideal.span {a} := by
    rw [← Ideal.map_comap_of_equiv, Ideal.map_span, Set.image_singleton]
    simp
  have := count_equiv (RingOfIntegers.mapRingEquiv s).symm la
    (I := Ideal.span {RingOfIntegers.mapRingEquiv s a}) (by simpa using ha')
  rw [hc] at this
  rw [this]

theorem valuation_primeBack (s : K ≃+* K) (la : HeightOneSpectrum (𝓞 K)) (x : K) :
    (primeBack s la).valuation K x = la.valuation K (s x) := by
  obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) x
  have hs : ∀ z : 𝓞 K, s (algebraMap (𝓞 K) K z) = algebraMap (𝓞 K) K (RingOfIntegers.mapRingEquiv s z) :=
    fun _ => rfl
  rw [map_div₀, map_div₀, map_div₀, hs, hs, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.valuation_of_algebraMap, intValuation_primeBack, intValuation_primeBack]

theorem vLa_primeBack (s : K ≃+* K) (la : HeightOneSpectrum (𝓞 K)) (x : K) :
    vLa (primeBack s la) x = vLa la (s x) := by
  simp only [vLa, valuation_primeBack]

end Prime
end GlobalTheory.GalSup

namespace GlobalTheory.GalSup

section Pts

open ReciprocityTheory.ChartRestriction.G

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c c' : Coeff l} (hle : c.F ≤ c'.F)

def changeEmbedding {L : Type} [CommRing L] (ι₀ ι₁ : c'.F →+* L) (κ : c.F →+* L)
    (h₀ : ∀ a, ι₀ (incF c c' hle a) = κ a) (h₁ : ∀ a, ι₁ (incF c c' hle a) = κ a)
    (y : letI := ι₀.toAlgebra; FrPt Xo c' L) : letI := ι₁.toAlgebra; FrPt Xo c' L :=
  letI : Algebra c.F L := κ.toAlgebra
  let y₀ : FrPt Xo c L := (letI : Algebra c'.F L := ι₀.toAlgebra; y.res hle h₀)
  letI : Algebra c'.F L := ι₁.toAlgebra
  y₀.ext hle h₁

theorem evR_rulBC {L : Type} [CommRing L] (ι₀ : c'.F →+* L) (κ : c.F →+* L)
    (h₀ : ∀ a, ι₀ (incF c c' hle a) = κ a) {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {f : Rul Xo c} (hf : f ∈ sec Xo c a n)
    (y : letI := ι₀.toAlgebra; FrPt Xo c' L) :
    (letI := ι₀.toAlgebra; evR Xo c' (rulBC hle f) y) =
      (letI : Algebra c.F L := κ.toAlgebra; letI := ι₀.toAlgebra; evR Xo c f (y.res hle h₀)) := by
  letI : Algebra c.F L := κ.toAlgebra
  letI := ι₀.toAlgebra
  exact ((rulBC_sec_val_linear E H Dw l Xo c c' hle).1 a n f hf).2 L h₀ y

theorem integral_reread {T : CDVR} (ι₀ ι₁ : c'.F →+* T.Fr) (κ : c.F →+* T.Fr)
    (h₀ : ∀ a, ι₀ (incF c c' hle a) = κ a) (h₁ : ∀ a, ι₁ (incF c c' hle a) = κ a)
    (y : letI := ι₀.toAlgebra; FrPt Xo c' T.Fr) (hy : Integral T ι₀ y) :
    Integral T ι₁ (changeEmbedding hle ι₀ ι₁ κ h₀ h₁ y) := by
  have key : ∀ (τ : E →+* ℂ) (b : 𝓞 E), ι₁ (embK c' τ b) = ι₀ (embK c' τ b) := fun τ b => by
    rw [← embK_incF hle τ b, h₀, h₁]
  have eig : ∀ (G : SAB H (Sp T.V)) τ (w : epsOver T.V T.V ⟶ G.G),
      IsEigV c' ι₁ G τ w ↔ IsEigV c' ι₀ G τ w := fun G τ w => by
    unfold IsEigV
    simp only [key]
  obtain ⟨G, t', m1, m2, ⟨ub, h1, h2, h3, h4⟩, rest⟩ := hy
  exact ⟨G, t', m1, m2, ⟨ub, h1, fun τ i => (eig G τ _).2 (h2 τ i),
    fun τ w ht he => h3 τ w ht ((eig G τ w).1 he), h4⟩, rest⟩

end Pts
end GlobalTheory.GalSup

namespace GlobalTheory.GalSup

open ReciprocityTheory.ChartRestriction.G

theorem evI_sum {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {T : CDVR} {io : c.F →+* T.Fr} (y : IntFr Xo c T io) {m : ℕ}
    (b : Fin m → c.F) (g : Fin m → Rul Xo c) :
    evI y (∑ i, b i • g i) = ∑ i, io (b i) * evI y (g i) := by
  have h := map_sum (AddMonoidHom.mk' (evI y) (evI_add y)) (fun i => b i • g i) Finset.univ
  simp only [AddMonoidHom.mk'_apply] at h
  rw [h]
  simp only [evI_smul]

theorem intAt_galois : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c c' : Coeff l) (hle : c.F ≤ c'.F) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (s : c'.F ≃+* c'.F), (∀ x : c.F, s (incF c c' hle x) = incF c c' hle x) → ∀ (m : ℕ) (as : Fin m → c'.F) (fs : Fin m → Rul Xo c), (∀ i, fs i ∈ sec Xo c a n) → IntAt Xo c' (∑ i, as i • rulBC hle (fs i)) → IntAt Xo c' (∑ i, s (as i) • rulBC hle (fs i)) := by
  intro E _ _ _ H Dw l Xo c c' hle a n s hs m as fs hfs hint la v hv
  obtain ⟨⟨q, T, ι, e, ho, y, hy, eta, heta, hq⟩, rfl⟩ := hv
  subst hq
  show 0 ≤ nval T.V e (evI y _)
  let κ : c.F →+* T.Fr := ι.comp (incF c c' hle)
  let ι₁ : c'.F →+* T.Fr := ι.comp (s : c'.F →+* c'.F)
  have h₀ : ∀ x, ι (incF c c' hle x) = κ x := fun _ => rfl
  have h₁ : ∀ x, ι₁ (incF c c' hle x) = κ x := fun x => by
    show ι (s (incF c c' hle x)) = ι (incF c c' hle x)
    rw [hs x]
  let y₁ : IntFr Xo c' T ι₁ := ⟨changeEmbedding hle ι ι₁ κ h₀ h₁ y.1,
    (letI := ι₁.toAlgebra; GlobalTheory.FlagTan.fromTest_of_isLocalRing _), integral_reread hle ι ι₁ κ h₀ h₁ y.1 y.2.2⟩
  have ho₁ : OverLa (primeBack s la) T.V ι₁ e := ⟨ho.1, fun x => by
    rw [vLa_primeBack]; exact ho.2 (s x)⟩
  have key : 0 ≤ nval T.V e (evI y₁ (∑ i, as i • rulBC hle (fs i))) :=
    hint (primeBack s la) _ ⟨PtV.mk (primeBack s la) ho₁ y₁ hy () trivial, rfl⟩
  have e1 : evI y (∑ i, s (as i) • rulBC hle (fs i)) = evI y₁ (∑ i, as i • rulBC hle (fs i)) := by
    rw [evI_sum, evI_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    unfold evI
    rw [evR_rulBC hle ι κ h₀ (hfs i), evR_rulBC hle ι₁ κ h₁ (hfs i)]
    rfl
  rw [e1]
  exact key

end GlobalTheory.GalSup
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CabsGenEqOneOfNormPin
open NumberField AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.GeoLevel GlobalTheory.LevelCusp GlobalTheory.FrameUnif
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix
open GlobalTheory.UnitFrameGen MeasureTheory

noncomputable section

namespace GlobalTheory.GeoLevel


set_option maxHeartbeats 1600000 in
theorem cabs_gen_eq_one_of_normPin : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (σ' : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ' ty) (i i' : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ)) (P' : (F.Di i').La →+ (Fin g → ℂ)) (ρ : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ) (y z y' : FrPt Xo c (CAt σ)) (t : Ix Dw → (CAt σ)ˣ), IsPeriod (F.Di i) ty P → IsPeriod (F.Di i') ty P' → y.x = F.u i P → z.x = F.u i' P' → NormPin F i P y → NormPin F i' P' z → FrMove ρ ν y y' → FrBor t z y' → cabs (t none : CAt σ) = 1 := by
  intro E _ _ _ H Dw l Xo c σ σ' g ty F i i' P P' ρ ν y₀ z₀ y' t hp hp' hu hu' hx hx' hmv hb
  obtain ⟨Hm, χ, fr, θ, Fd, hH, -, him, hd, hn, hc, h0, ha, hv, hF, hI⟩ := hx
  obtain ⟨Hm', χ', fr', θ', Fd', hH', -, him', hd', hn', hc', h0', ha', hv', hF', hI'⟩ := hx'
  obtain ⟨O, ω, o1, o2, o3, o4, o5⟩ := GlobalTheory.MoveValues.frMove_values E H Dw l Xo c σ ρ ν _ _ hmv
  have hxρ : z₀.x = y₀.x ≫ ρ := hb.1.symm.trans hmv.1
  obtain ⟨hxx, -, hbc⟩ := hb
  clear hmv
  obtain ⟨gam, hl, hg1, hg4, hex0⟩ := exists_isometry_of_sabMap F ν hp hp'
    ((congrArg (· ≫ ρ) hu).symm.trans (hxρ.symm.trans hu'))
  obtain ⟨h, hdet, hh⟩ : ∃ h : Matrix (Fin g) (Fin g) ℂ, IsUnit h.det ∧ ∀ z, h *ᵥ z = hl z :=
    ⟨LinearMap.toMatrix' hl.toLinearMap, by
      rw [LinearMap.det_toMatrix']; exact LinearEquiv.isUnit_det' hl,
      fun a => by rw [LinearMap.toMatrix'_mulVec]; rfl⟩
  have hg : ∀ a, P' (gam a) = h *ᵥ P a := fun a => by rw [hh, hg4]
  have hex : ∀ z, (F.ex i' P' (h *ᵥ z)).left = (F.ex i P z).left ≫ ν.φ := fun z => by rw [hh, hex0]
  have hspan : Submodule.span ℝ (P.range : Set (Fin g → ℂ)) = ⊤ := by
    rw [AddMonoidHom.coe_range]; exact hp.2.2.2.1
  have hHH : ∀ z w, hermForm Hm' (h *ᵥ z) (h *ᵥ w) = hermForm Hm z w :=
    hermForm_eq_of_im _ hspan Hm Hm' h (by
      rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
      rw [← hg, ← hg, him, him', hg1])
  have hexp : ∀ a ∈ P.range, ∀ z, F.ex i P (z + a) = F.ex i P z := fun a ha z => by
    rw [F.ex_add i P hp, (F.ex_ker i P hp a).2 ha]
    exact @_root_.mul_one _ (CategoryTheory.Hom.monoid).toMulOneClass _
  have hcov : ∀ z, ∃ j, ⊤ ≤ (F.ex i P z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j := fun z =>
    GlobalTheory.ThetaPtChg.exists_chart_point Xo.univ.t.PP.isLB _
  have hcov2 : ∀ z, ∃ q : Xo.univ.t.PP.L.ι × Xo.univ.t.PP.L.ι, ⊤ ≤ (F.ex i P z).left ⁻¹ᵁ O q.1 q.2 := fun z => by
    obtain ⟨j, hj⟩ := hcov z
    obtain ⟨j', hj'⟩ := GlobalTheory.ThetaPtChg.exists_chart_point Xo.univ.t.PP.isLB ((F.ex i P z).left ≫ ν.φ)
    exact ⟨(j', j), (o1 _ _ _).2 ⟨hj', hj⟩⟩
  have tr : ∀ j j' z, ⊤ ≤ (F.ex i P z).left ⁻¹ᵁ O j j' →
      ⊤ ≤ (F.ex i' P' (h *ᵥ z)).left ⁻¹ᵁ Xo.univ.t.PP.L.U j := fun j j' z hz => by
    rw [hex]; exact ((o1 _ _ _).1 hz).1
  have tr2 : ∀ j j' z, ⊤ ≤ (F.ex i P z).left ⁻¹ᵁ O j j' →
      ⊤ ≤ (F.ex i P z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j' := fun j j' z hz => ((o1 _ _ _).1 hz).2
  have hm : ∀ j, ∀ a ∈ P.range, ∀ z, ⊤ ≤ (F.ex i P z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → ‖fr j z‖ =
      Real.exp (Real.pi * (hermForm Hm z a).re + Real.pi / 2 * (hermForm Hm a a).re) * ‖fr j (z + a)‖ := by
    rintro j _ ⟨a, rfl⟩ z hz
    exact norm_factor Hm _ _ _ _ _ (ha a j z).1 ((ha a j z).2 hz)
  have dl : Differentiable ℂ (fun z' : Fin g → ℂ => h *ᵥ z') :=
    (LinearMap.toContinuousLinearMap (Matrix.mulVecLin h)).differentiable
  have hw0 : ∀ z, (F.ex i P z).left ≫ Xo.univ.t.G.hom = (y₀.x : Sp ℂ ⟶ Xo.X) := fun z =>
    (Over.w (F.ex i P z)).trans hu.symm
  have hw0' : ∀ z, (F.ex i' P' z).left ≫ Xo.univ.t.G.hom = (z₀.x : Sp ℂ ⟶ Xo.X) := fun z =>
    (Over.w (F.ex i' P' z)).trans hu'.symm
  have hz0 : (F.ex i P 0).left = (y₀.x : Sp ℂ ⟶ Xo.X) ≫ eSec Xo.univ.t.G := by
    rw [(F.ex_ker i P hp 0).2 (zero_mem _), hu]
    rfl
  have hfr : ∀ q : Xo.univ.t.PP.L.ι × Xo.univ.t.PP.L.ι, ∀ z, ⊤ ≤ (F.ex i P z).left ⁻¹ᵁ O q.1 q.2 →
      fr' q.1 (h *ᵥ z) = valAt' (F.ex i P z).left (O q.1 q.2) (ω q.1 q.2) * fr q.2 z :=
    frames_eq P.range hspan (fun q : Xo.univ.t.PP.L.ι × Xo.univ.t.PP.L.ι => {z | ⊤ ≤ (F.ex i P z).left ⁻¹ᵁ O q.1 q.2})
      (fun j => GlobalTheory.FamilyUnif_isOpen_ex F i P hp _) hcov2
      (fun j a ha z hz => by rw [Set.mem_setOf_eq, hexp a ha]; exact hz)
      (fun q z => valAt' (F.ex i P z).left (O q.1 q.2) (ω q.1 q.2) * fr q.2 z) (fun q z => fr' q.1 (h *ᵥ z))
      (fun q q' z => valAt' ((F.ex i P z).left ≫ ν.φ) (Xo.univ.t.PP.L.U q.1 ⊓ Xo.univ.t.PP.L.U q'.1)
        (Xo.univ.t.PP.L.g q.1 q'.1).val)
      (fun a z => Real.exp (Real.pi * (hermForm Hm z a).re + Real.pi / 2 * (hermForm Hm a a).re))
      (fun q => (((GlobalTheory.ClassUniq.isHolTo_ex F i P hp) (O q.1 q.2) (ω q.1 q.2)).2.mono
        fun z hz => ⟨Set.mem_univ _, hz⟩).mul ((hd q.2).mono fun z hz => tr2 _ _ z hz))
      (fun q => (hd' q.1).comp dl.differentiableOn fun z hz => tr _ _ z hz)
      (fun q z hz => mul_ne_zero (o2 _ _ _ hz) (hn _ z (tr2 _ _ z hz)))
      (fun q q' z h1 h2 => by
        rw [hc q.2 q'.2 z ((top_le_preimage_inf _ _ _).2 ⟨tr2 _ _ z h1, tr2 _ _ z h2⟩), ← mul_assoc,
          o3 _ _ _ _ _ h1 h2, mul_assoc])
      (fun q q' z h1 h2 => by
        have e2 := hc' q.1 q'.1 (h *ᵥ z) ((top_le_preimage_inf _ _ _).2 ⟨tr _ _ _ h1, tr _ _ _ h2⟩)
        rw [hex] at e2
        exact e2)
      (fun q hz => by
        have t0 := tr _ _ 0 hz
        simp only [Matrix.mulVec_zero] at t0 ⊢
        rw [h0 _ (tr2 _ _ 0 hz), h0' _ t0, hxρ]
        exact o4 _ _ _ _ hz0 hz)
      (fun q a haa z hz => by
        rw [hexp a haa, norm_mul, norm_mul, hm _ a haa z (tr2 _ _ z hz)]
        ring)
      (by
        rintro q _ ⟨a, rfl⟩ z hz
        have := norm_factor Hm' _ _ _ _ _ (ha' (gam a) q.1 (h *ᵥ z)).1
          ((ha' (gam a) q.1 (h *ᵥ z)).2 (tr _ _ z hz))
        rw [hg, hHH, hHH, ← Matrix.mulVec_add] at this
        exact this)
  have hS : Out.SecTwistSt := GlobalTheory.abelianSchemeLaws_all.2.secTwist
  have hid : spMap (RingHom.id ℂ) = 𝟙 _ := by simp [spMap]
  have hbc' : GlobalTheory.Frames.SecBC (RingHom.id ℂ) (Formalism.L2.PjFree.toC (t none : CAt σ)) z₀.x y'.x
      z₀.s y'.s := by
    obtain ⟨pm, p1, p2, p3⟩ := hbc
    exact ⟨pm, p1, by rw [hid]; exact p2.trans (Category.comp_id _).symm, p3⟩
  have hθ : ∀ z, θ z = Formalism.L2.PjFree.toC (t none : CAt σ) * θ' (h *ᵥ z) := fun z => by
    obtain ⟨q, hq⟩ := hcov2 z
    let p : Over.mk (y₀.x : Sp ℂ ⟶ Xo.X) ⟶ Xo.univ.t.G := Over.homMk (F.ex i P z).left (hw0 z)
    have e1 := congrArg CommaMorphism.left (CartesianMonoidalCategory.lift_snd (𝟙 _) p)
    have e2 := congrArg CommaMorphism.left (CartesianMonoidalCategory.lift_fst (𝟙 _) p)
    have v1 := hv q.2 z _ e1 e2 (tr2 _ _ z hq)
    have hval := GlobalTheory.ThetaPtChg.val_of_secBC hS (Xo := Xo) _ _ hxx _ _ _ hbc'
      (Over.homMk (F.ex i' P' (h *ᵥ z)).left (hw0' _)) q.1 _ _
      (fun pt h1 h2 => hv' q.1 (h *ᵥ z) pt h1 h2 (tr _ _ z hq))
      (fun pt h1 h2 => o5 q.1 q.2 _ pt _ e1 e2 (h1.trans (hex z)) h2 hq)
    have hval2 : valAt' (F.ex i P z).left (O q.1 q.2) (ω q.1 q.2) * (θ z * fr q.2 z) =
        Formalism.L2.PjFree.toC (t none : CAt σ) * (θ' (h *ᵥ z) * fr' q.1 (h *ᵥ z)) :=
      (congrArg (valAt' (F.ex i P z).left (O q.1 q.2) (ω q.1 q.2) * ·) v1).symm.trans hval
    rw [hfr q z hq] at hval2
    apply mul_right_cancel₀ (mul_ne_zero (o2 _ _ _ hq) (hn _ z (tr2 _ _ z hq)))
    linear_combination hval2
  have ht0 : Formalism.L2.PjFree.toC (t none : CAt σ) ≠ 0 := Units.ne_zero (M₀ := ℂ) (t none)
  have hθp : ∀ a ∈ P.range, ∀ z, ‖θ (z + a)‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm (z + a) (z + a)).re) =
      ‖θ z‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm z z).re) := fun a ha z => by
    obtain ⟨j, hj⟩ := hcov z
    have hj' : ⊤ ≤ (F.ex i P (z + a)).left ⁻¹ᵁ Xo.univ.t.PP.L.U j := by rw [hexp a ha]; exact hj
    let p : Over.mk (y₀.x : Sp ℂ ⟶ Xo.X) ⟶ Xo.univ.t.G := Over.homMk (F.ex i P z).left (hw0 z)
    have e1 := congrArg CommaMorphism.left (CartesianMonoidalCategory.lift_snd (𝟙 _) p)
    have e2 := congrArg CommaMorphism.left (CartesianMonoidalCategory.lift_fst (𝟙 _) p)
    have v1 := hv j z _ e1 e2 hj
    have v2 := hv j (z + a) _ (by rw [hexp a ha]; exact e1) e2 hj'
    exact normSq_periodic hH _ _ _ _ z a (hn j _ hj') (v2.symm.trans v1) (hm j a ha z hj)
  haveI : Countable P.range := by
    haveI := hp.2.2.1
    exact TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  have hinj : Function.Injective (fun z : Fin g → ℂ => h *ᵥ z) :=
    Matrix.mulVec_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det h).2 hdet)
  have hn0 : ‖Formalism.L2.PjFree.toC (t none : CAt σ)‖ ≠ 0 := norm_ne_zero_iff.2 ht0
  have key : ∀ z, ‖θ' (h *ᵥ z)‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm' (h *ᵥ z) (h *ᵥ z)).re) =
      (‖Formalism.L2.PjFree.toC (t none : CAt σ)‖ ^ 2)⁻¹ *
        (‖θ z‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm z z).re)) :=
    fun z => by rw [hθ, hHH, norm_mul, mul_pow]; field_simp
  have hmean := mean_comp_eq P.range P'.range h hdet (fun z => ⟨?_, ?_⟩) Fd Fd' hF hF'
    (fun z => ‖θ' z‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm' z z).re))
    (fun a ha z => by simp only [key, hθp a ha z])
  · simp only [key] at hmean
    rw [hI', integral_const_mul, mul_div_assoc, hI, mul_one, inv_eq_one] at hmean
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 hmean
  · rintro ⟨a, ha⟩
    refine ⟨gam.symm a, hinj ?_⟩
    simp only
    rw [← hg, gam.apply_symm_apply, ha]
  · rintro ⟨a, rfl⟩
    exact ⟨gam a, hg a⟩

end GlobalTheory.GeoLevel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemCompactPartRestrictedProductIffForall
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemCompactPartRestrictedProductIffForall
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CptPartRestr

open Set
open scoped Pointwise

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]

def cptSub (T : Subgroup G) (hT : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a) : Subgroup G where
  carrier := {t | t ∈ T ∧ IsCompact (closure (Subgroup.zpowers t : Set G))}
  one_mem' := by
    refine ⟨T.one_mem, ?_⟩
    rw [Subgroup.zpowers_one_eq_bot, Subgroup.coe_bot, closure_singleton]
    exact isCompact_singleton
  mul_mem' := by
    rintro a b ⟨haT, ha⟩ ⟨hbT, hb⟩
    refine ⟨T.mul_mem haT hbT, ?_⟩
    have hc : Commute a b := hT a haT b hbT
    have hsub : closure (Subgroup.zpowers (a * b) : Set G) ⊆
        closure (Subgroup.zpowers a : Set G) * closure (Subgroup.zpowers b : Set G) := by
      refine closure_minimal ?_ (ha.mul hb).isClosed
      rintro _ ⟨n, rfl⟩
      simp only [hc.mul_zpow]
      exact Set.mul_mem_mul (subset_closure (Subgroup.zpow_mem_zpowers a n))
        (subset_closure (Subgroup.zpow_mem_zpowers b n))
    exact (ha.mul hb).of_isClosed_subset isClosed_closure hsub
  inv_mem' := by
    rintro a ⟨haT, ha⟩
    refine ⟨T.inv_mem haT, ?_⟩
    rw [Subgroup.zpowers_inv]
    exact ha

theorem mem_cptPart_iff (T : Subgroup G) (hT : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a) (x : G) :
    x ∈ cptPart T ↔ x ∈ T ∧ IsCompact (closure (Subgroup.zpowers x : Set G)) := by
  have : cptPart T = cptSub T hT := Subgroup.closure_eq (cptSub T hT)
  rw [this]
  rfl

section Restr

variable {X V : Type} {Y : V → Type} [Group X] [TopologicalSpace X] [IsTopologicalGroup X] [T2Space X]
  [∀ v, Group (Y v)] [∀ v, TopologicalSpace (Y v)] [∀ v, IsTopologicalGroup (Y v)] [∀ v, T2Space (Y v)]
  {pf : ∀ v, X →* Y v} {K : ∀ v, Subgroup (Y v)}

theorem isClosed_setOf_forall_mem (hX : GlobalTheory.RestrMeas.IsRestrGroup (GlobalTheory.RestrMeas.noArch X) pf K)
    (C : ∀ v, Set (Y v)) (hC : ∀ v, IsCompact (C v)) : IsClosed {z : X | ∀ v, pf v z ∈ C v} := by
  simp only [Set.setOf_forall]
  exact isClosed_iInter fun v => (hC v).isClosed.preimage (hX.continuous_pf v)

theorem isCompact_setOf_forall_mem (hX : GlobalTheory.RestrMeas.IsRestrGroup (GlobalTheory.RestrMeas.noArch X) pf K)
    (S : Finset V) : ∀ C : ∀ v, Set (Y v), (∀ v, IsCompact (C v)) → (∀ v ∉ S, C v ⊆ K v) →
      IsCompact {z : X | ∀ v, pf v z ∈ C v} := by
  induction S using Finset.induction_on with
  | empty =>
    intro C hC hCK
    have hKg := hX.isCompact_level (fun e => e.elim) (fun e => e.elim)
    exact hKg.of_isClosed_subset (isClosed_setOf_forall_mem hX C hC)
      fun z hz => ⟨fun e => e.elim, fun v => hCK v (Finset.notMem_empty v) (hz v)⟩
  | @insert v₀ S hv₀ ih =>
    intro C hC hCK
    obtain ⟨t, hcov⟩ := (hC v₀).elim_finite_subcover (fun c : C v₀ => (c : Y v₀) • (K v₀ : Set (Y v₀)))
      (fun c => (hX.isOpen_K v₀).smul _)
      (fun y hy => Set.mem_iUnion.2 ⟨⟨y, hy⟩, ⟨1, (K v₀).one_mem, by simp⟩⟩)
    set C' : ∀ v, Set (Y v) := Function.update C v₀ (K v₀ : Set (Y v₀)) with hC'def
    have hC' : ∀ v, IsCompact (C' v) := by
      intro v
      by_cases h : v = v₀
      · subst h; simp only [hC'def, Function.update_self]; exact hX.isCompact_K v
      · simp only [hC'def, Function.update_of_ne h]; exact hC v
    have hC'K : ∀ v ∉ S, C' v ⊆ K v := by
      intro v hv
      by_cases h : v = v₀
      · subst h; simp only [hC'def, Function.update_self]; exact subset_rfl
      · simp only [hC'def, Function.update_of_ne h]
        exact hCK v (by simp [h, hv])
    have hM' := ih C' hC' hC'K
    have hl : ∀ c : Y v₀, ∃ x : X, ∀ v, pf v x = Pi.mulSingle v₀ c v := by
      intro c
      have hev : ∀ᶠ v in cofinite, (Pi.mulSingle v₀ c : ∀ v, Y v) v ∈ K v := by
        rw [Filter.eventually_cofinite]
        refine (Set.finite_singleton v₀).subset fun v hv => ?_
        by_contra h
        exact hv (by rw [Pi.mulSingle_eq_of_ne h]; exact (K v).one_mem)
      obtain ⟨x, -, hx⟩ := hX.exists_eq (fun e => e.elim) _ hev
      exact ⟨x, hx⟩
    choose xc hxc using hl
    have hU : IsCompact (⋃ i ∈ t, xc (i : Y v₀) • {z : X | ∀ v, pf v z ∈ C' v}) :=
      t.isCompact_biUnion fun i _ => hM'.smul _
    refine hU.of_isClosed_subset (isClosed_setOf_forall_mem hX C hC) fun z hz => ?_
    obtain ⟨i, hi, hzi⟩ := Set.mem_iUnion₂.1 (hcov (hz v₀))
    obtain ⟨k, hk, hik⟩ := Set.mem_smul_set.1 hzi
    refine Set.mem_iUnion₂.2 ⟨i, hi, Set.mem_smul_set_iff_inv_smul_mem.2 fun v => ?_⟩
    rw [smul_eq_mul, map_mul, map_inv, hxc]
    by_cases h : v = v₀
    · subst h
      simp only [Pi.mulSingle_eq_same, hC'def, Function.update_self]
      rw [← hik, smul_eq_mul, inv_mul_cancel_left]
      exact hk
    · simp only [Pi.mulSingle_eq_of_ne h, inv_one, one_mul, hC'def, Function.update_of_ne h]
      exact hz v

theorem isCompact_closure_zpowers_iff (hX : GlobalTheory.RestrMeas.IsRestrGroup (GlobalTheory.RestrMeas.noArch X) pf K) (x : X) :
    IsCompact (closure (Subgroup.zpowers x : Set X)) ↔
      ∀ v, IsCompact (closure (Subgroup.zpowers (pf v x) : Set (Y v))) := by
  constructor
  · intro h v
    have hi := h.image (hX.continuous_pf v)
    refine hi.of_isClosed_subset isClosed_closure (closure_minimal ?_ hi.isClosed)
    rintro _ ⟨n, rfl⟩
    exact ⟨x ^ n, subset_closure (Subgroup.zpow_mem_zpowers x n), map_zpow _ _ _⟩
  · intro h
    have hfin := Filter.eventually_cofinite.1 (hX.eventually_mem x)
    have hCK : ∀ v ∉ hfin.toFinset, closure (Subgroup.zpowers (pf v x) : Set (Y v)) ⊆ K v := by
      intro v hv
      rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] at hv
      exact closure_minimal (fun y hy => Subgroup.zpowers_le.2 hv hy) (hX.isCompact_K v).isClosed
    have hM := isCompact_setOf_forall_mem hX hfin.toFinset _ h hCK
    refine hM.of_isClosed_subset isClosed_closure
      (closure_minimal ?_ (isClosed_setOf_forall_mem hX _ h))
    rintro _ ⟨n, rfl⟩ v
    rw [map_zpow]
    exact subset_closure (Subgroup.zpow_mem_zpowers _ n)

end Restr

theorem mem_cptPart_iff_forall : ∀ {X V : Type} {Y : V → Type} [Group X] [TopologicalSpace X] [IsTopologicalGroup X] [T2Space X] [∀ v, Group (Y v)] [∀ v, TopologicalSpace (Y v)] [∀ v, IsTopologicalGroup (Y v)] [∀ v, T2Space (Y v)] (pf : ∀ v, X →* Y v) (K : ∀ v, Subgroup (Y v)), GlobalTheory.RestrMeas.IsRestrGroup (GlobalTheory.RestrMeas.noArch X) pf K → ∀ (T : Subgroup X) (Tv : ∀ v, Subgroup (Y v)), (∀ x, x ∈ T ↔ ∀ v, pf v x ∈ Tv v) → (∀ v, ∀ a ∈ Tv v, ∀ b ∈ Tv v, a * b = b * a) → ∀ x, x ∈ cptPart T ↔ ∀ v, pf v x ∈ cptPart (Tv v) := by
  intro X V Y _ _ _ _ _ _ _ _ pf K hX T Tv hT hTv x
  have hTc : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a := fun a ha b hb =>
    hX.ext _ _ (fun e => e.elim) fun v => by
      rw [map_mul, map_mul]; exact hTv v _ ((hT a).1 ha v) _ ((hT b).1 hb v)
  rw [mem_cptPart_iff T hTc, hT, isCompact_closure_zpowers_iff hX]
  simp only [mem_cptPart_iff _ (hTv _)]
  exact ⟨fun h v => ⟨h.1 v, h.2 v⟩, fun h => ⟨fun v => (h v).1, fun v => (h v).2⟩⟩

end GlobalTheory.CptPartRestr
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemCompactPartRestrictedProductIffForallStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_compactPart_restrictedProduct_iff_forall : ∀ {X V : Type} {Y : V → Type} [Group X] [TopologicalSpace X] [IsTopologicalGroup X] [T2Space X] [∀ v, Group (Y v)] [∀ v, TopologicalSpace (Y v)] [∀ v, IsTopologicalGroup (Y v)] [∀ v, T2Space (Y v)] (pf : ∀ v, X →* Y v) (K : ∀ v, Subgroup (Y v)), GlobalTheory.RestrMeas.IsRestrGroup (GlobalTheory.RestrMeas.noArch X) pf K → ∀ (T : Subgroup X) (Tv : ∀ v, Subgroup (Y v)), (∀ x, x ∈ T ↔ ∀ v, pf v x ∈ Tv v) → (∀ v, ∀ a ∈ Tv v, ∀ b ∈ Tv v, a * b = b * a) → ∀ x, x ∈ cptPart T ↔ ∀ v, pf v x ∈ cptPart (Tv v) := by
  first | exact @GlobalTheory.CptPartRestr.mem_cptPart_iff_forall | exact GlobalTheory.CptPartRestr.mem_cptPart_iff_forall | (intros; apply GlobalTheory.CptPartRestr.mem_cptPart_iff_forall <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFubiniStudyOfTotallyOrderedRatFnFamily
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFubiniStudyOfTotallyOrderedRatFnFamily
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSNef.FSExist

variable {X : Scheme.{0}} [IsIntegral X] {J : Type} {f : J → X.functionField}

theorem regAt_nhds {x : X} {g : X.functionField} (h : RegAt x g) :
    ∃ U : X.Opens, x ∈ U ∧ ∀ y ∈ U, RegAt y g := by
  obtain ⟨U, hx, a, rfl⟩ := h.exists_fnOf
  exact ⟨U, hx, fun y hy => regAt_fnOf hy _ a⟩

theorem exists_min [Fintype J] [Nonempty J] (hf : Total f) (x : X) :
    ∃ j, ∀ l, RegAt x (f l / f j) := by
  have key : ∀ s : Finset J, s.Nonempty → ∃ j, ∀ l ∈ s, RegAt x (f l / f j) := by
    intro s hs
    induction hs using Finset.Nonempty.cons_induction with
    | singleton a =>
      refine ⟨a, fun l hl => ?_⟩
      rw [Finset.mem_singleton.1 hl, div_self (hf.1 a)]
      exact (unitAt_one x).regAt
    | cons a s ha hs ih =>
      obtain ⟨j, hj⟩ := ih
      rcases hf.2 x a j with h | h
      ·
        refine ⟨j, fun l hl => ?_⟩
        rcases Finset.mem_cons.1 hl with rfl | hl
        · exact h
        · exact hj l hl
      ·
        refine ⟨a, fun l hl => ?_⟩
        rcases Finset.mem_cons.1 hl with rfl | hl
        · rw [div_self (hf.1 l)]; exact (unitAt_one x).regAt
        · have e : f l / f a = f l / f j * (f j / f a) := by
            rw [div_mul_div_cancel₀ (hf.1 j)]
          rw [e]; exact (hj l hl).mul h
  obtain ⟨j, hj⟩ := key Finset.univ Finset.univ_nonempty
  exact ⟨j, fun l => hj l (Finset.mem_univ l)⟩

def inv (hf : Total f) (j : J) : X.functionFieldˣ := Units.mk0 (f j)⁻¹ (inv_ne_zero (hf.1 j))

theorem germOf_inv_eq (hf : Total f) {x : X} {j j' : J} (hj : ∀ l, RegAt x (f l / f j))
    (hj' : ∀ l, RegAt x (f l / f j')) : germOf x (inv hf j) = germOf x (inv hf j') := by
  rw [germOf_eq_iff]
  change UnitAt x ((f j')⁻¹ / (f j)⁻¹)
  rw [inv_div_inv]
  refine (unitAt_iff (div_ne_zero (hf.1 j) (hf.1 j'))).2 ⟨hj' j, ?_⟩
  rw [inv_div]
  exact hj j'

theorem isOpen_minSet [Finite J] (hf : Total f) (j : J) :
    IsOpen {y : X | ∀ l, RegAt y (f l / f j)} := by
  refine isOpen_iff_forall_mem_open.2 fun y hy => ?_
  choose V hV hV' using fun l => regAt_nhds (hy l)
  exact ⟨⋂ l, (V l : Set X), fun z hz l => hV' l z (Set.mem_iInter.1 hz l),
    isOpen_iInter_of_finite fun l => (V l).isOpen, Set.mem_iInter.2 hV⟩

variable [Fintype J] [Nonempty J]

def fsDiv (hf : Total f) : CartierDiv X :=
  show cartierGroup X from ⟨fun x => germOf x (inv hf (exists_min hf x).choose), fun x =>
    ⟨⟨_, isOpen_minSet hf (exists_min hf x).choose⟩, (exists_min hf x).choose_spec,
      inv hf (exists_min hf x).choose, fun y hy =>
        germOf_inv_eq hf (exists_min hf y).choose_spec hy⟩⟩

theorem isEqn_inv (hf : Total f) {x : X} {j : J} (hj : ∀ l, RegAt x (f l / f j)) :
    (fsDiv hf).IsEqn x (inv hf j) :=
  germOf_inv_eq hf (exists_min hf x).choose_spec hj

theorem mem_sections (hf : Total f) (l : J) : f l ∈ (fsDiv hf).sections :=
  CartierDiv.mem_sections.2 fun x =>
    ⟨_, isEqn_inv hf (exists_min hf x).choose_spec, by
      change RegAt x (f l * (f _)⁻¹)
      rw [← div_eq_mul_inv]
      exact (exists_min hf x).choose_spec l⟩

theorem generatesAt (hf : Total f) {x : X} {j : J} (hj : ∀ l, RegAt x (f l / f j)) :
    (fsDiv hf).GeneratesAt x (f j) :=
  ⟨_, isEqn_inv hf hj, by
    change UnitAt x (f j * (f j)⁻¹)
    rw [mul_inv_cancel₀ (hf.1 j)]
    exact unitAt_one x⟩

end GlobalTheory.HSNef.FSExist

namespace GlobalTheory.HSNef.FSExist

variable {X : Scheme.{0}} [IsIntegral X] {J : Type} [Fintype J] [Nonempty J] {f : J → X.functionField}
  [DecidableEq J]

def sec (hf : Total f) (l : J) : (toLB (fsDiv hf)).Sec :=
  ((presents_toLB (fsDiv hf)).exists_rat_eq (mem_sections hf l)).choose

theorem rat_sec (hf : Total f) (l : J) : (presents_toLB (fsDiv hf)).rat (sec hf l) = f l :=
  ((presents_toLB (fsDiv hf)).exists_rat_eq (mem_sections hf l)).choose_spec

theorem iSup_sec (hf : Total f) : ⨆ j, ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (sec hf j) = ⊤ :=
  eq_top_iff.2 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨(exists_min hf x).choose,
    ((presents_toLB (fsDiv hf)).generatesAt_rat_iff _).1 (by
      rw [rat_sec]; exact generatesAt hf (exists_min hf x).choose_spec)⟩

def expDiag (w : J → ℝ) : Matrix J J ℂ := Matrix.diagonal fun j => ((Real.exp (w j) : ℝ) : ℂ)

theorem det_expDiag (w : J → ℝ) : (expDiag w).det ≠ 0 := by
  classical
  rw [expDiag, Matrix.det_diagonal]
  exact Finset.prod_ne_zero_iff.2 fun j _ => Complex.ofReal_ne_zero.2 (Real.exp_pos _).ne'

theorem map_expDiag (w : J → ℝ) : (expDiag w).map (starRingEnd ℂ) = expDiag w := by
  ext i j
  by_cases h : i = j
  · subst h; rw [Matrix.map_apply, expDiag, Matrix.diagonal_apply_eq, Complex.conj_ofReal]
  · simp [expDiag, Matrix.diagonal_apply_ne _ h]

theorem sum_expDiag (w : J → ℝ) (v : J → ℂ) (a : J) :
    ∑ j, expDiag w j a * v j = ((Real.exp (w a) : ℝ) : ℂ) * v a := by
  classical
  rw [Finset.sum_eq_single a (fun j _ hj => by simp [expDiag, Matrix.diagonal_apply_ne _ hj])
    (fun h => (h (Finset.mem_univ a)).elim)]
  simp [expDiag]

end GlobalTheory.HSNef.FSExist


open GlobalTheory.HSNef.FSExist in
theorem GlobalTheory.HSNef.exists_isFS : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k),
    ∀ (J : Type) [Fintype J] [Nonempty J] (f : J → X.functionField) (w : J → ℝ), Total f →
      ∃ M : HermLB p, IsFS M f w := by
  intro k _ X _ p J _ _ f w hf
  classical
  let h := presents_toLB (fsDiv hf)
  refine ⟨HermLB.fs p (isLB_toLB (fsDiv hf)) (sec hf) (iSup_sec hf) (fun _ => expDiag w)
    (fun _ => det_expDiag w) (fun _ => ⟨1, one_mem _, by rw [mul_one, map_expDiag]⟩), ?_⟩
  refine ⟨fun i => i.1.2, h.isRatSec, fun x c hx => ⟨fun j => ?_, ?_⟩, fun σ y (c : (toLB (fsDiv hf)).ι) (hy : y ∈ ptsIn p σ ((toLB (fsDiv hf)).U c)) => ?_⟩
  · exact (c.2.2 x hx).regularAt_iff.1 (CartierDiv.mem_sections.1 (mem_sections hf j) x)
  · exact ⟨_, (c.2.2 x hx).generatesAt_iff.1 (generatesAt hf (exists_min hf x).choose_spec)⟩
  · refine (Weight.fsBasis_φ (p := p) (σ := σ) (isLB_toLB (fsDiv hf)) (sec hf) (iSup_sec hf) (expDiag w)
      (det_expDiag w) c y).trans ?_
    congr 1
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [sum_expDiag]
    have e : f a * (c.1.2 : X.functionField) = fnOf _ c.2.1 ((sec hf a).f c) := by
      rw [← rat_sec hf a]; exact h.rat_mul (sec hf a) c c.2.1
    have e2 : ratVal (f a * (c.1.2 : X.functionField)) y =
        valR y.1 ((toLB (fsDiv hf)).U c) ((sec hf a).f c) := by
      rw [e]; exact ratVal_fnOf (U := (toLB (fsDiv hf)).U c) hy c.2.1 _
    rw [e2]
    rw [norm_mul, mul_pow, mul_comm, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), ← Real.exp_nat_mul]
    norm_num
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFubiniStudyOfTotallyOrderedRatFnFamilyStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fubiniStudy_of_totallyOrdered_ratFnFamily : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k), ∀ (J : Type) [Fintype J] [Nonempty J] (f : J → X.functionField) (w : J → ℝ), Total f → ∃ M : HermLB p, IsFS M f w := by
  first | exact @GlobalTheory.HSNef.exists_isFS | exact GlobalTheory.HSNef.exists_isFS | (intros; apply GlobalTheory.HSNef.exists_isFS <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryBorelEqDiagonalMulUnipotent
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryBorelEqDiagonalMulUnipotent
open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.WeylCell Formalism.UG

namespace GlobalTheory.UnitaryBorel

theorem borel_eq_diag_mul_unip_sameDiag : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) (n : ℕ)
    (β : GU σ n), IsBorelU β →
    ∃ t ν : GU σ n, β = t * ν ∧ IsUnipU ν ∧
      (∀ i j, i ≠ j → ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j = 0) ∧
      ∀ i, ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i = ((β : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i := by
  intro L _ _ σ n b hb
  obtain ⟨d, hd, hd'⟩ := Formalism.UG.P.fSatake_diag_exists (σ := σ)
    (fun i => (((b : Formalism.UG.GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i)
    (Formalism.UG.P.fSatake_unit_diag hb)
  have hne : ∀ i, (((b : Formalism.UG.GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i ≠ 0 :=
    Formalism.UG.P.fSatake_ne_zero_of_borel hb
  have hu : (((d⁻¹ * b : Formalism.UG.GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
      Matrix.diagonal (fun i => ((((b : Formalism.UG.GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i)⁻¹) *
        (((b : Formalism.UG.GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := by
    rw [Subgroup.coe_mul, Units.val_mul, hd']
  refine ⟨d, d⁻¹ * b, by group, ⟨fun i j hji => ?_, fun i => ?_⟩,
    fun i j hij => by rw [hd, Matrix.diagonal_apply_ne _ hij], fun i => by rw [hd, Matrix.diagonal_apply_eq]⟩
  · rw [hu, Matrix.diagonal_mul, hb i j hji, mul_zero]
  · rw [hu, Matrix.diagonal_mul, inv_mul_cancel₀ (hne i)]

end GlobalTheory.UnitaryBorel
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryBorelEqDiagonalMulUnipotentStatement
open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.WeylCell Formalism.UG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryBorel_eq_diagonal_mul_unipotent : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) (n : ℕ)
    (β : GU σ n), IsBorelU β →
    ∃ t ν : GU σ n, β = t * ν ∧ IsUnipU ν ∧
      (∀ i j, i ≠ j → ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j = 0) ∧
      ∀ i, ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i = ((β : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i := by
  first | exact @GlobalTheory.UnitaryBorel.borel_eq_diag_mul_unip_sameDiag | exact GlobalTheory.UnitaryBorel.borel_eq_diag_mul_unip_sameDiag | (intros; apply GlobalTheory.UnitaryBorel.borel_eq_diag_mul_unip_sameDiag <;> assumption)
end
end
