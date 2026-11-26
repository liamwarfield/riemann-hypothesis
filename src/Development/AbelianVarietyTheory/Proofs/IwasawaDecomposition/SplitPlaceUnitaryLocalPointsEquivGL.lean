module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOneP
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassInvOfUnitTrivial
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PtYAndItYOfPair

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceUnitaryLocalPointsEquivGL
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceUnitaryLocalPointsEquivGL
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

noncomputable section

namespace GlobalTheory.SplitPts

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}


variable (E) in
abbrev conjE : E ≃+* E := (IsCMField.complexConj E).toRingEquiv

theorem conjSrc_conjSrc_cm (v : HeightOneSpectrum (𝓞 E)) : conjSrc (conjE E) (conjSrc (conjE E) v) = v :=
  (eq_conjSrc fun x => by
    rw [← conjPl_conjSrc (conjE E) v ((conjE E) x)]
    exact congrArg _ (IsCMField.complexConj_apply_apply E x)).symm

theorem conjPl_self_conjSrc (w : HeightOneSpectrum (𝓞 E)) : GlobalTheory.Mem.Chr.ConjPl (conjE E) w (conjSrc (conjE E) w) := by
  have h := conjPl_conjSrc (conjE E) (conjSrc (conjE E) w)
  rwa [conjSrc_conjSrc_cm] at h

theorem over_split {w : HeightOneSpectrum (𝓞 E)} (hw : IsSplitAt w) :
    conjSrc (conjE E) w ≠ w ∧
      (conjSrc (conjE E) w).under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E)) ∧
      ∀ u : HeightOneSpectrum (𝓞 E), u.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E)) →
        u = w ∨ u = conjSrc (conjE E) w := by
  have key := GlobalTheory.Mem.Chr.under_eq_iff_conjPl (IsCMField.complexConj E)
    (Algebra.IsQuadraticExtension.finrank_eq_two _ _) (IsCMField.complexConj_ne_one E) w
  have h2 : ∀ u, GlobalTheory.Mem.Chr.ConjPl (conjE E) w u → u = conjSrc (conjE E) w := fun u h => by
    rw [eq_conjSrc h, conjSrc_conjSrc_cm]
  obtain ⟨u, hu, hu'⟩ := hw
  refine ⟨?_, (key _).2 (Or.inr (conjPl_self_conjSrc w)), fun u' h => ((key u').1 h).imp_right (h2 u')⟩
  rcases (key u).1 hu' with h | h
  · exact absurd h hu
  · rw [← h2 u h]; exact hu

theorem comp_eq (x : UA E n) (u : HeightOneSpectrum (𝓞 E)) :
    ((cLoc (conjSrc (conjE E) u) x).val.map (conjLoc (conjE E) u))ᵀ * (cLoc u x).val = 1 := by
  have h : cT (conjAd E) (x.1 : Matrix (Fin n) (Fin n) (Ad E)) * 1 * x.1.val = 1 := x.2
  rw [Matrix.mul_one] at h
  have h2 := congrArg (RingHom.mapMatrix ((pLoc E u).comp (pFin E))) h
  rw [map_one, map_mul] at h2
  exact h2

theorem eq_one_of_cLoc {w : HeightOneSpectrum (𝓞 E)} (hw : IsSplitAt w) (z : locU n w) (h1 : cLoc w z.1 = 1) :
    z = 1 := by
  obtain ⟨-, -, hover⟩ := over_split hw
  have hw1 : ∀ v, v = w → cLoc v z.1 = 1 := by
    rintro v rfl
    exact h1
  have hall : ∀ u, cLoc u z.1 = 1 := by
    intro u
    by_cases hu : u.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E))
    · rcases hover u hu with rfl | rfl
      · exact h1
      · have hce := comp_eq z.1 (conjSrc (conjE E) w)
        rw [hw1 _ (conjSrc_conjSrc_cm w), Units.val_one, Matrix.map_one _ (map_zero _) (map_one _),
          Matrix.transpose_one, Matrix.one_mul] at hce
        exact Units.ext hce
    · have hz := (Subgroup.mem_inf.1 z.2).2
      exact MonoidHom.mem_ker.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hz u) hu)
  have hinf : cInf z.1 = 1 := MonoidHom.mem_ker.1 (Subgroup.mem_inf.1 z.2).1
  refine Subtype.ext (Subtype.ext (ga_ext ?_ ?_))
  · exact hinf.trans (map_one _).symm
  · rw [Subgroup.coe_one, Subgroup.coe_one, map_one]
    refine Units.ext (Matrix.ext fun i j => FiniteAdeleRing.ext (R := 𝓞 E) E fun u => ?_)
    have := congrArg (fun g : GL (Fin n) (u.adicCompletion E) => g.val i j) (hall u)
    simp only [Units.val_one, Matrix.one_apply] at this
    refine this.trans ?_
    split_ifs with hij <;> simp [hij] <;> rfl

def psi (w : HeightOneSpectrum (𝓞 E)) : w.adicCompletion E →+* (conjSrc (conjE E) w).adicCompletion E :=
  (GlobalTheory.Mem.Chr.exists_finCompl_map (conjE E) (conjPl_self_conjSrc w)).choose

theorem psi_spec (w : HeightOneSpectrum (𝓞 E)) : Continuous (psi w) ∧
    ∀ k : E, psi w (algebraMap E _ k) = algebraMap E _ (conjE E k) :=
  ⟨(GlobalTheory.Mem.Chr.exists_finCompl_map (conjE E) (conjPl_self_conjSrc w)).choose_spec.1,
    (GlobalTheory.Mem.Chr.exists_finCompl_map (conjE E) (conjPl_self_conjSrc w)).choose_spec.2.1⟩

theorem conjLoc_psi (w : HeightOneSpectrum (𝓞 E)) (y : w.adicCompletion E) : conjLoc (conjE E) w (psi w y) = y := by
  refine congrFun ((HeightOneSpectrum.denseRange_algebraMap (K := E) w).equalizer
    ((conjLoc_spec (conjE E) w).1.comp (psi_spec w).1) continuous_id (funext fun k => ?_)) y
  simp only [Function.comp_apply, id, (psi_spec w).2, (conjLoc_spec (conjE E) w).2.1]
  exact congrArg _ (IsCMField.complexConj_apply_apply E k)

theorem conjLoc_pLoc (w : HeightOneSpectrum (𝓞 E)) (a : Af E) :
    conjLoc (conjE E) (conjSrc (conjE E) w) (pLoc E (conjSrc (conjE E) (conjSrc (conjE E) w)) a) = psi w (pLoc E w a) := by
  have key : ∀ (v : HeightOneSpectrum (𝓞 E)) (_ : v = w)
      (f : v.adicCompletion E →+* (conjSrc (conjE E) w).adicCompletion E), Continuous f →
      (∀ k : E, f (algebraMap E _ k) = algebraMap E _ (conjE E k)) → f (pLoc E v a) = psi w (pLoc E w a) := by
    rintro v rfl f hf h
    exact congrFun ((HeightOneSpectrum.denseRange_algebraMap (K := E) v).equalizer hf (psi_spec v).1
      (funext fun k => (h k).trans ((psi_spec v).2 k).symm)) _
  exact key _ (conjSrc_conjSrc_cm w) _ (conjLoc_spec (conjE E) _).1 (conjLoc_spec (conjE E) _).2.1

theorem invT_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (g : GL (Fin n) R) :
    GeneralLinearGroup.map f (invT n R g) = invT n S (GeneralLinearGroup.map f g) := by
  apply Units.ext
  change ((g⁻¹ : GL (Fin n) R).val)ᵀ.map f = ((GeneralLinearGroup.map f g)⁻¹).valᵀ
  rw [← map_inv]
  rfl

def finPt (w : HeightOneSpectrum (𝓞 E)) (h : GL (Fin n) (w.adicCompletion E)) : GL (Fin n) (Af E) :=
  locGL E n w h * locGL E n (conjSrc (conjE E) w) (invT n _ (GeneralLinearGroup.map (psi w) h))

theorem finPt_w {w : HeightOneSpectrum (𝓞 E)} (hne : conjSrc (conjE E) w ≠ w) (h : GL (Fin n) (w.adicCompletion E)) :
    GeneralLinearGroup.map (pLoc E w) (finPt w h) = h := by
  rw [finPt, map_mul, pLoc_locGL, pLoc_locGL_of_ne (Ne.symm hne), mul_one]

theorem finPt_w' {w : HeightOneSpectrum (𝓞 E)} (hne : conjSrc (conjE E) w ≠ w) (h : GL (Fin n) (w.adicCompletion E)) :
    GeneralLinearGroup.map (pLoc E (conjSrc (conjE E) w)) (finPt w h) =
      invT n _ (GeneralLinearGroup.map (psi w) h) := by
  rw [finPt, map_mul, pLoc_locGL, pLoc_locGL_of_ne hne, one_mul]

theorem finPt_other {w u : HeightOneSpectrum (𝓞 E)} (h1 : u ≠ w) (h2 : u ≠ conjSrc (conjE E) w)
    (h : GL (Fin n) (w.adicCompletion E)) : GeneralLinearGroup.map (pLoc E u) (finPt w h) = 1 := by
  rw [finPt, map_mul, pLoc_locGL_of_ne h1, pLoc_locGL_of_ne h2, one_mul]

omit [IsCMField E] in
theorem matAf_ext {M N : Matrix (Fin n) (Fin n) (Af E)}
    (h : ∀ u, RingHom.mapMatrix (pLoc E u) M = RingHom.mapMatrix (pLoc E u) N) : M = N :=
  Matrix.ext fun i j => FiniteAdeleRing.ext (R := 𝓞 E) E fun u => congrFun (congrFun (h u) i) j

theorem matAd_ext {M N : Matrix (Fin n) (Fin n) (Ad E)} (h1 : RingHom.mapMatrix (pInf E) M = RingHom.mapMatrix (pInf E) N)
    (h2 : RingHom.mapMatrix (pFin E) M = RingHom.mapMatrix (pFin E) N) : M = N :=
  Matrix.ext fun i j => ad_ext (congrFun (congrFun h1 i) j) (congrFun (congrFun h2 i) j)

theorem finGL_mem_UA (k : GL (Fin n) (Af E))
    (hk : ∀ u, ((GeneralLinearGroup.map (pLoc E (conjSrc (conjE E) u)) k).val.map (conjLoc (conjE E) u))ᵀ *
      (GeneralLinearGroup.map (pLoc E u) k).val = 1) : finGL E n k ∈ UA E n := by
  show cT (conjAd E) (finGL E n k).val * 1 * (finGL E n k).val = 1
  rw [Matrix.mul_one]
  have hinf : (finGL E n k).val.map (pInf E) = 1 := congrArg Units.val (pInf_finGL k)
  have hfin : (finGL E n k).val.map (pFin E) = k.val := congrArg Units.val (pFin_finGL k)
  refine matAd_ext ?_ ?_
  · rw [map_mul, map_one]
    have e : RingHom.mapMatrix (pInf E) (cT (conjAd E) (finGL E n k).val) = 1 := by
      refine Matrix.ext fun i j => ?_
      have hji := congrFun (congrFun hinf j) i
      change pInf E (conjAd E ((finGL E n k).val j i)) = _
      rw [show pInf E (conjAd E ((finGL E n k).val j i)) = starRingEnd (Cinf E) (pInf E ((finGL E n k).val j i)) from
        (infEq E).symm_apply_apply _]
      change starRingEnd (Cinf E) (((finGL E n k).val.map (pInf E)) j i) = _
      rw [hinf]
      simp [Matrix.one_apply, eq_comm]
    rw [e, one_mul]
    exact hinf
  · rw [map_mul, map_one]
    have e : RingHom.mapMatrix (pFin E) (cT (conjAd E) (finGL E n k).val) = cT (conjFin (conjE E)) k.val := by
      rw [← hfin]; rfl
    change RingHom.mapMatrix (pFin E) (cT (conjAd E) (finGL E n k).val) * (finGL E n k).val.map (pFin E) = 1
    rw [e, hfin]
    refine matAf_ext fun u => ?_
    rw [map_mul, map_one]
    exact hk u

theorem finPt_cond {w : HeightOneSpectrum (𝓞 E)} (hw : IsSplitAt w) (h : GL (Fin n) (w.adicCompletion E))
    (u : HeightOneSpectrum (𝓞 E)) :
    ((GeneralLinearGroup.map (pLoc E (conjSrc (conjE E) u)) (finPt w h)).val.map (conjLoc (conjE E) u))ᵀ *
      (GeneralLinearGroup.map (pLoc E u) (finPt w h)).val = 1 := by
  obtain ⟨hne, -, -⟩ := over_split hw
  by_cases h1 : u = w
  · rw [h1, finPt_w' hne, finPt_w hne]
    change ((GeneralLinearGroup.map (conjLoc (conjE E) w) (invT n _ (GeneralLinearGroup.map (psi w) h))).val)ᵀ * h.val = 1
    rw [invT_map, show GeneralLinearGroup.map (conjLoc (conjE E) w) (GeneralLinearGroup.map (psi w) h) = h from
      Units.ext (Matrix.ext fun i j => conjLoc_psi w _)]
    change (((h⁻¹ : GL (Fin n) _).val)ᵀ)ᵀ * h.val = 1
    rw [Matrix.transpose_transpose, Units.inv_mul]
  · by_cases h2 : u = conjSrc (conjE E) w
    · rw [h2, finPt_w' hne]
      have e : (GeneralLinearGroup.map (pLoc E (conjSrc (conjE E) (conjSrc (conjE E) w))) (finPt w h)).val.map
          (conjLoc (conjE E) (conjSrc (conjE E) w)) = (GeneralLinearGroup.map (psi w) h).val := by
        refine Matrix.ext fun i j => ?_
        refine (conjLoc_pLoc w _).trans ?_
        have := congrArg (fun g : GL (Fin n) (w.adicCompletion E) => g.val i j) (finPt_w hne h)
        exact congrArg (psi w) this
      rw [e]
      change (GeneralLinearGroup.map (psi w) h).valᵀ * ((GeneralLinearGroup.map (psi w) h)⁻¹).valᵀ = 1
      rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]
    · have h3 : conjSrc (conjE E) u ≠ w := fun e => h2 (by rw [← e, conjSrc_conjSrc_cm])
      have h4 : conjSrc (conjE E) u ≠ conjSrc (conjE E) w := fun e => h1 (conjSrc_injective _ e)
      rw [finPt_other h3 h4, finPt_other h1 h2]
      simp

theorem cLoc_finGL (u : HeightOneSpectrum (𝓞 E)) (k : GL (Fin n) (Af E)) (hk : finGL E n k ∈ UA E n) :
    cLoc u (⟨finGL E n k, hk⟩ : UA E n) = GeneralLinearGroup.map (pLoc E u) k := by
  change GeneralLinearGroup.map ((pLoc E u).comp (pFin E)) (finGL E n k) = _
  have e : ∀ g : GA E n, GeneralLinearGroup.map ((pLoc E u).comp (pFin E)) g =
      GeneralLinearGroup.map (pLoc E u) (GeneralLinearGroup.map (pFin E) g) := fun g => Units.ext rfl
  rw [e, pFin_finGL]

def locPt {w : HeightOneSpectrum (𝓞 E)} (hw : IsSplitAt w) (h : GL (Fin n) (w.adicCompletion E)) : locU n w :=
  ⟨⟨finGL E n (finPt w h), finGL_mem_UA _ (finPt_cond hw h)⟩, by
    obtain ⟨-, hw', -⟩ := over_split hw
    refine Subgroup.mem_inf.2 ⟨MonoidHom.mem_ker.2 (pInf_finGL _), Subgroup.mem_iInf.2 fun u =>
      Subgroup.mem_iInf.2 fun hu => MonoidHom.mem_ker.2 ?_⟩
    rw [cLoc_finGL]
    exact finPt_other (fun e => hu (by rw [e])) (fun e => hu (by rw [e, hw'])) h⟩

theorem cLoc_locPt {w : HeightOneSpectrum (𝓞 E)} (hw : IsSplitAt w) (h : GL (Fin n) (w.adicCompletion E)) :
    cLoc w (locPt hw h).1 = h :=
  (cLoc_finGL w _ _).trans (finPt_w (over_split hw).1 h)

theorem continuous_invT (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] :
    Continuous (invT n R) :=
  Units.continuous_iff.2 ⟨Units.continuous_coe_inv.matrix_transpose, Units.continuous_val.matrix_transpose⟩

end GlobalTheory.SplitPts


open GlobalTheory.SplitPts in
theorem GlobalTheory.locU_equiv_GL : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ)
    (w : HeightOneSpectrum (𝓞 E)), IsSplitAt w →
      ∃ e : locU n w ≃ₜ* GL (Fin n) (w.adicCompletion E), ∀ x : locU n w, e x = cLoc w (x : UA E n) := by
  intro E _ _ _ n w hw
  have inj : ∀ a b : locU n w, cLoc w a.1 = cLoc w b.1 → a = b := fun a b hab => by
    have := eq_one_of_cLoc hw (a * b⁻¹)
      (by rw [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, hab, mul_inv_cancel])
    exact mul_inv_eq_one.1 this
  have hfin : Continuous (finGL E n) :=
    Continuous.units_map _ (continuous_const.add (continuous_id.matrix_map
      (continuous_const.prodMk continuous_id : Continuous fun x : Af E => ((0, x) : InfiniteAdeleRing E × Af E))))
  refine ⟨{ toFun := fun x => cLoc w x.1
            invFun := locPt hw
            left_inv := fun x => inj _ _ (cLoc_locPt hw _)
            right_inv := fun h => cLoc_locPt hw h
            map_mul' := fun x y => map_mul (cLoc w) x.1 y.1
            continuous_toFun := ?_
            continuous_invFun := ?_ }, fun x => rfl⟩
  · exact (Continuous.units_map _ (continuous_id.matrix_map
      ((RestrictedProduct.continuous_eval w).comp continuous_snd))).comp
      (continuous_subtype_val.comp continuous_subtype_val)
  · refine Continuous.subtype_mk (Continuous.subtype_mk (hfin.comp ?_) _) _
    exact (CuspSub.continuous_locGL w).mul ((CuspSub.continuous_locGL _).comp ((continuous_invT _).comp
      (Continuous.units_map _ (continuous_id.matrix_map (psi_spec w).1))))
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceUnitaryLocalPointsEquivGLStatement
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlace_unitaryLocalPoints_equiv_GL : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : HeightOneSpectrum (𝓞 E)), IsSplitAt w → ∃ e : locU n w ≃ₜ* GL (Fin n) (w.adicCompletion E), ∀ x : locU n w, e x = cLoc w (x : UA E n) := by
  first | exact @GlobalTheory.locU_equiv_GL | exact GlobalTheory.locU_equiv_GL | (intros; apply GlobalTheory.locU_equiv_GL <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousRetractionOntoUnitaryLocalPoints
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousRetractionOntoUnitaryLocalPoints
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

noncomputable section

namespace GlobalTheory.DefU.LocRet

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem under_conjSrc (v : HeightOneSpectrum (𝓞 E)) :
    (conjSrc (IsCMField.complexConj E).toRingEquiv v).under (𝓞 (maximalRealSubfield E)) =
      v.under (𝓞 (maximalRealSubfield E)) := by
  have h := conjPl_conjSrc (IsCMField.complexConj E).toRingEquiv v
  ext y
  change algebraMap _ (𝓞 E) y ∈ (conjSrc (IsCMField.complexConj E).toRingEquiv v).asIdeal ↔ algebraMap _ (𝓞 E) y ∈ v.asIdeal
  rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := E), ← HeightOneSpectrum.valuation_lt_one_iff_mem (K := E), ← h]
  have : (IsCMField.complexConj E).toRingEquiv ((algebraMap _ (𝓞 E) y : 𝓞 E) : E) = ((algebraMap _ (𝓞 E) y : 𝓞 E) : E) := by
    change (IsCMField.complexConj E) (algebraMap (maximalRealSubfield E) E (y : maximalRealSubfield E)) = _
    rw [AlgEquiv.commutes]
    rfl
  rw [this]

variable (w : HeightOneSpectrum (𝓞 E))


open Classical in
def idemF : Af E :=
  ⟨fun v => if v.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E)) then 1 else 0,
    Filter.Eventually.of_forall fun v => by
      dsimp only
      split_ifs
      · exact one_mem _
      · exact zero_mem _⟩

def idem : Ad E := sFin E (idemF w)

theorem idem_mul_idem : idem w * idem w = idem w := by
  refine Prod.ext (mul_zero _) (FiniteAdeleRing.ext E fun v => ?_)
  change (idemF w).1 v * (idemF w).1 v = (idemF w).1 v
  simp only [idemF]
  split_ifs <;> simp

def sIdem : Ad E →ₙ+* Ad E where
  toFun x := idem w * x
  map_mul' x y := by
    calc idem w * (x * y) = (idem w * idem w) * (x * y) := by rw [idem_mul_idem]
      _ = idem w * x * (idem w * y) := by ring
  map_zero' := mul_zero _
  map_add' x y := mul_add _ _ _

theorem pInf_sIdem (x : Ad E) : pInf E (sIdem w x) = 0 := by
  change pInf E (sFin E (idemF w) * x) = 0
  rw [map_mul]
  have : pInf E (sFin E (idemF w)) = 0 := map_zero (infEq E).symm
  rw [this, zero_mul]

theorem pLoc_sIdem_of_eq {v : HeightOneSpectrum (𝓞 E)}
    (hv : v.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E))) (x : Ad E) :
    ((pLoc E v).comp (pFin E)) (sIdem w x) = ((pLoc E v).comp (pFin E)) x := by
  change ((pLoc E v).comp (pFin E)) (idem w) * _ = _
  have : ((pLoc E v).comp (pFin E)) (idem w) = 1 := by
    change (idemF w).1 v = 1
    simp only [idemF, if_pos hv]
  rw [this, one_mul]
  rfl

theorem pLoc_sIdem_of_ne {v : HeightOneSpectrum (𝓞 E)}
    (hv : v.under (𝓞 (maximalRealSubfield E)) ≠ w.under (𝓞 (maximalRealSubfield E))) (x : Ad E) :
    ((pLoc E v).comp (pFin E)) (sIdem w x) = 0 := by
  change ((pLoc E v).comp (pFin E)) (idem w) * _ = _
  have : ((pLoc E v).comp (pFin E)) (idem w) = 0 := by
    change (idemF w).1 v = 0
    simp only [idemF, if_neg hv]
  rw [this, zero_mul]

theorem conjAd_idem : conjAd E (idem w) = idem w := by
  refine Prod.ext ?_ (FiniteAdeleRing.ext E fun v => ?_)
  · change (infEq E) ((starRingEnd (Cinf E)) ((infEq E).symm 0)) = 0
    simp
  change pLoc E v (conjFin (IsCMField.complexConj E).toRingEquiv (idemF w)) = (idemF w).1 v
  rw [pLoc_conjFin]
  change conjLoc _ v ((idemF w).1 _) = (idemF w).1 v
  have hc := under_conjSrc (E := E) v
  simp only [idemF]
  split_ifs with h1 h2 h2
  · simp
  · exact absurd (hc.symm.trans h1) h2
  · exact absurd (hc.trans h2) h1
  · simp

variable {w} {n : ℕ}

theorem ga_ext' {g h : GA E n} (h1 : GeneralLinearGroup.map (pInf E) g = GeneralLinearGroup.map (pInf E) h)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 E), GeneralLinearGroup.map ((pLoc E v).comp (pFin E)) g =
      GeneralLinearGroup.map ((pLoc E v).comp (pFin E)) h) : g = h := by
  refine ga_ext h1 (Units.ext (Matrix.ext fun i j => FiniteAdeleRing.ext E fun v => ?_))
  exact congrArg (fun x : GL (Fin n) (v.adicCompletion E) => x.val i j) (h2 v)

theorem cT_corner (M : Matrix (Fin n) (Fin n) (Ad E)) :
    cT (conjAd E) (corner (matN n (sIdem w)) M) = corner (matN n (sIdem w)) (cT (conjAd E) M) := by
  ext i j
  change conjAd E ((1 : Matrix (Fin n) (Fin n) (Ad E)) j i - idem w * (1 : Matrix (Fin n) (Fin n) (Ad E)) j i +
      idem w * M j i) = (1 : Matrix (Fin n) (Fin n) (Ad E)) i j - idem w * (1 : Matrix (Fin n) (Fin n) (Ad E)) i j +
      idem w * conjAd E (M j i)
  rw [map_add (f := _), map_sub, map_mul, map_mul, conjAd_idem, Matrix.one_apply, Matrix.one_apply]
  by_cases h : j = i
  · subst h; simp
  · simp [h, Ne.symm h]

theorem corner_mem (g : UA E n) : cornerGL n (sIdem w) g.1 ∈ UA E n := by
  have hg : cT (conjAd E) (g.1 : Matrix (Fin n) (Fin n) (Ad E)) * 1 * g.1 = 1 := g.2
  change cT (conjAd E) (corner (matN n (sIdem w)) g.1.1) * 1 * corner (matN n (sIdem w)) g.1.1 = 1
  rw [cT_corner, Matrix.mul_one, ← map_mul, ← Matrix.mul_one (cT (conjAd E) _), hg, map_one]


variable (n w) in
def ret0 : UA E n →* UA E n := ((cornerGL n (sIdem w)).comp (UA E n).subtype).codRestrict (UA E n) corner_mem

theorem infiniteProj_unitaryAdelicLocalRetractionEnd_eq_one (g : UA E n) : GeneralLinearGroup.map (pInf E) (ret0 w n g).1 = 1 :=
  map_cornerGL_of_zero _ _ (pInf_sIdem w) _

theorem localProj_unitaryAdelicLocalRetractionEnd_of_under_eq {v : HeightOneSpectrum (𝓞 E)}
    (hv : v.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E))) (g : UA E n) :
    GeneralLinearGroup.map ((pLoc E v).comp (pFin E)) (ret0 w n g).1 = GeneralLinearGroup.map ((pLoc E v).comp (pFin E)) g.1 :=
  map_cornerGL_of_hom _ _ _ (pLoc_sIdem_of_eq w hv) _

theorem localProj_unitaryAdelicLocalRetractionEnd_of_under_ne {v : HeightOneSpectrum (𝓞 E)}
    (hv : v.under (𝓞 (maximalRealSubfield E)) ≠ w.under (𝓞 (maximalRealSubfield E))) (g : UA E n) :
    GeneralLinearGroup.map ((pLoc E v).comp (pFin E)) (ret0 w n g).1 = 1 :=
  map_cornerGL_of_zero _ _ (pLoc_sIdem_of_ne w hv) _

theorem unitaryAdelicLocalRetractionEnd_mem_localPoints (g : UA E n) : ret0 w n g ∈ locU n w := by
  refine Subgroup.mem_inf.2 ⟨MonoidHom.mem_ker.2 (infiniteProj_unitaryAdelicLocalRetractionEnd_eq_one g), Subgroup.mem_iInf.2 fun u => Subgroup.mem_iInf.2 fun hu => ?_⟩
  exact MonoidHom.mem_ker.2 (localProj_unitaryAdelicLocalRetractionEnd_of_under_ne hu g)

theorem mem_locU_inf {x : UA E n} (hx : x ∈ locU n w) : GeneralLinearGroup.map (pInf E) x.1 = 1 :=
  MonoidHom.mem_ker.1 (Subgroup.mem_inf.1 hx).1

theorem mem_locU_ne {x : UA E n} (hx : x ∈ locU n w) {v : HeightOneSpectrum (𝓞 E)}
    (hv : v.under (𝓞 (maximalRealSubfield E)) ≠ w.under (𝓞 (maximalRealSubfield E))) :
    GeneralLinearGroup.map ((pLoc E v).comp (pFin E)) x.1 = 1 :=
  MonoidHom.mem_ker.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hx).2 v) hv)


variable (n w) in
def ret : UA E n →* locU n w := (ret0 w n).codRestrict (locU n w) unitaryAdelicLocalRetractionEnd_mem_localPoints

theorem continuous_ret : Continuous (ret w n) := by
  have hc : Continuous (corner (matN n (sIdem w))) := by
    change Continuous fun M : Matrix (Fin n) (Fin n) (Ad E) => 1 - (1 : Matrix (Fin n) (Fin n) (Ad E)).map (idem w * ·) +
      M.map (idem w * ·)
    exact continuous_const.add (continuous_id.matrix_map (continuous_const.mul continuous_id))
  exact Continuous.subtype_mk (Continuous.subtype_mk ((Continuous.units_map _ hc).comp continuous_subtype_val) _) _

theorem ret_of_mem (x : locU n w) : ret w n x = x := by
  refine Subtype.ext (Subtype.ext (ga_ext' ?_ fun v => ?_))
  · exact (infiniteProj_unitaryAdelicLocalRetractionEnd_eq_one x.1).trans (mem_locU_inf x.2).symm
  · by_cases hv : v.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E))
    · exact localProj_unitaryAdelicLocalRetractionEnd_of_under_eq hv x.1
    · exact (localProj_unitaryAdelicLocalRetractionEnd_of_under_ne hv x.1).trans (mem_locU_ne x.2 hv).symm

theorem commute_ret (g : UA E n) (y : locU n w) : Commute ((ret w n g : UA E n)⁻¹ * g) (y : UA E n) := by
  refine Subtype.ext (ga_ext' ?_ fun v => ?_)
  · simp only [Subgroup.coe_mul, map_mul, mem_locU_inf y.2, one_mul, mul_one]
  · by_cases hv : v.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E))
    · have h : GeneralLinearGroup.map ((pLoc E v).comp (pFin E)) (((ret w n g : UA E n)⁻¹ * g : UA E n) : GA E n) = 1 := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]
        change (GeneralLinearGroup.map ((pLoc E v).comp (pFin E)) (ret0 w n g).1)⁻¹ * _ = 1
        rw [localProj_unitaryAdelicLocalRetractionEnd_of_under_eq hv g, inv_mul_cancel]
      simp only [Subgroup.coe_mul, map_mul] at h ⊢
      rw [h, one_mul, mul_one]
    · simp only [Subgroup.coe_mul, map_mul, mem_locU_ne y.2 hv, one_mul, mul_one]

theorem exists_ret (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : HeightOneSpectrum (𝓞 E)) :
    ∃ r : UA E n →* locU n w, Continuous r ∧ (∀ x : locU n w, r x = x) ∧
      ∀ (g : UA E n) (y : locU n w), Commute ((r g : UA E n)⁻¹ * g) (y : UA E n) :=
  ⟨ret w n, continuous_ret, ret_of_mem, commute_ret⟩

end GlobalTheory.DefU.LocRet

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousRetractionOntoUnitaryLocalPointsStatement
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_continuous_retraction_onto_unitaryLocalPoints : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : HeightOneSpectrum (𝓞 E)), ∃ r : UA E n →* locU n w, Continuous r ∧ (∀ x : locU n w, r x = x) ∧ ∀ (g : UA E n) (y : locU n w), Commute ((r g : UA E n)⁻¹ * g) (y : UA E n) := by
  first | exact @GlobalTheory.DefU.LocRet.exists_ret | exact GlobalTheory.DefU.LocRet.exists_ret | (intros; apply GlobalTheory.DefU.LocRet.exists_ret <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IrreducibleRepIsotypicOfCentraliserFactor
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IrreducibleRepIsotypicOfCentraliserFactor
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

namespace GlobalTheory.CuspRep.CompUniq

theorem isotypic : ∀ (G H V W W' : Type) [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W'] (ρ : Representation ℂ G V) (s : H →* G) (σ : Representation ℂ H W) (σ' : Representation ℂ H W'), ρ.IsIrreducible → σ.IsIrreducible → σ'.IsIrreducible → (∀ g, ∃ u, ∀ y, Commute ((s u)⁻¹ * g) (s y)) → ∀ f : σ.IntertwiningMap (ρ.comp s), f ≠ 0 → (⨆ f : σ.IntertwiningMap (ρ.comp s), LinearMap.range f.toLinearMap) = ⊤ ∧ ∀ f' : σ'.IntertwiningMap (ρ.comp s), f' ≠ 0 → Nonempty (σ.Equiv σ') := by
  intro G H V W W' _ _ _ _ _ _ _ _ ρ s σ σ' hρ hσ hσ' hc f hf
  have hP : GlobalTheory.CuspRep.LocUniq.isoPart σ (ρ.comp s) = ⊤ := by
    rcases ((isIrreducible_iff ρ).1 hρ).2 (GlobalTheory.CuspRep.LocUniq.isoPart σ (ρ.comp s)) (fun g v hv => by
      obtain ⟨u, hu⟩ := hc g
      have h1 := GlobalTheory.CuspRep.LocUniq.isoPart_comm σ (ρ.comp s) (ρ ((s u)⁻¹ * g)) (fun y x => by
        simp only [MonoidHom.comp_apply]
        rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, (hu y).eq]) hv
      have h2 := GlobalTheory.CuspRep.LocUniq.isoPart_act σ (ρ.comp s) u h1
      rwa [MonoidHom.comp_apply, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left] at h2) with h | h
    · refine absurd ?_ hf
      apply Representation.IntertwiningMap.toLinearMap_injective
      refine LinearMap.ext fun v => ?_
      have h3 : f.toLinearMap v ∈ GlobalTheory.CuspRep.LocUniq.isoPart σ (ρ.comp s) :=
        Submodule.mem_iSup_of_mem f ⟨v, rfl⟩
      rw [h] at h3
      rw [(Submodule.mem_bot ℂ).1 h3]
      rfl
    · exact h
  refine ⟨hP, fun f' hf' => ?_⟩
  haveI := hσ
  haveI := hσ'
  exact GlobalTheory.CuspRep.LocUniq.equiv_of_isoPart σ σ' (ρ.comp s) hP f' hf'

end GlobalTheory.CuspRep.CompUniq
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IrreducibleRepIsotypicOfCentraliserFactorStatement
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.irreducibleRep_isotypic_of_centraliser_factor : ∀ (G H V W W' : Type) [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W'] (ρ : Representation ℂ G V) (s : H →* G) (σ : Representation ℂ H W) (σ' : Representation ℂ H W'), ρ.IsIrreducible → σ.IsIrreducible → σ'.IsIrreducible → (∀ g, ∃ u, ∀ y, Commute ((s u)⁻¹ * g) (s y)) → ∀ f : σ.IntertwiningMap (ρ.comp s), f ≠ 0 → (⨆ f : σ.IntertwiningMap (ρ.comp s), LinearMap.range f.toLinearMap) = ⊤ ∧ ∀ f' : σ'.IntertwiningMap (ρ.comp s), f' ≠ 0 → Nonempty (σ.Equiv σ') := by
  first | exact @GlobalTheory.CuspRep.CompUniq.isotypic | exact GlobalTheory.CuspRep.CompUniq.isotypic | (intros; apply GlobalTheory.CuspRep.CompUniq.isotypic <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaFunctionScalarProductPreservedIsometry
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaFunctionScalarProductPreservedIsometry
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.LiftPolar

theorem sesq_eq_of_diag {V : Type} [AddCommGroup V] [Module ℂ V] (B B' : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ)
    (h : ∀ v, B v v = B' v v) (f g : V) : B f g = B' f g := by
  have h1 := h (f + g)
  have h2 := h (f + Complex.I • g)
  simp only [map_add (f := _), LinearMap.add_apply, map_smul, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
    Complex.conj_I, h f, h g] at h1 h2
  linear_combination (1 / 2 : ℂ) * h1 + (Complex.I / 2) * h2 + (1 / 2 : ℂ) * (B f g - B' f g - B g f + B' g f) * Complex.I_mul_I

theorem integral_mul_star_eq {X : Type} [MeasurableSpace X] (ν : Measure X) [IsFiniteMeasure ν]
    (Θ : Submodule ℂ (X → ℂ)) (hm : ∀ f ∈ Θ, Measurable f) (hb : ∀ f ∈ Θ, ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C)
    (M : Module.End ℂ (X → ℂ)) (hM : ∀ f ∈ Θ, M f ∈ Θ)
    (hn : ∀ f ∈ Θ, ∫⁻ x, ‖M f x‖ₑ ^ 2 ∂ν = ∫⁻ x, ‖f x‖ₑ ^ 2 ∂ν) (f f' : X → ℂ) (hf : f ∈ Θ) (hf' : f' ∈ Θ) :
    ∫ x, M f x * star (M f' x) ∂ν = ∫ x, f x * star (f' x) ∂ν := by
  obtain ⟨B, hB, hN⟩ := GlobalTheory.ThetaMeanSquareForm.exists_form ν Θ hm hb
  have hr : ∀ v : Θ, ∃ r : ℝ, 0 ≤ r ∧ B v v = r := fun v =>
    ⟨∫ x, ‖(v : X → ℂ) x‖ ^ 2 ∂ν, integral_nonneg fun x => by positivity, by
      rw [hB]
      simp_rw [Complex.mul_conj', ← Complex.ofReal_pow]
      rw [integral_complex_ofReal]⟩
  let N : Θ →ₗ[ℂ] Θ := M.restrict hM
  let B' : Θ →ₗ[ℂ] Θ →ₗ⋆[ℂ] ℂ := LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun u v => B (N u) (N v))
    (fun _ _ _ => by simp only [map_add (f := _), LinearMap.add_apply])
    (fun _ _ _ => by simp only [map_smul, LinearMap.smul_apply, RingHom.id_apply])
    (fun _ _ _ => by simp only [map_add (f := _)])
    (fun _ _ _ => by simp only [map_smul, LinearMap.map_smulₛₗ])
  have hd : ∀ v : Θ, B' v v = B v v := fun v => by
    show B (N v) (N v) = B v v
    obtain ⟨r, hr0, e⟩ := hr v
    obtain ⟨s, hs0, e'⟩ := hr (N v)
    have h1 := hn v v.2
    have h2 := hN v
    have h3 := hN (N v)
    rw [e, Complex.ofReal_re] at h2
    rw [e', Complex.ofReal_re] at h3
    have h4 : ENNReal.ofReal s = ENNReal.ofReal r := h3.symm.trans (h1.trans h2)
    rw [e, e', (ENNReal.ofReal_eq_ofReal_iff hs0 hr0).1 h4]
  have key := sesq_eq_of_diag B' B hd ⟨f, hf⟩ ⟨f', hf'⟩
  exact (hB (N ⟨f, hf⟩) (N ⟨f', hf'⟩)).symm.trans (key.trans (hB ⟨f, hf⟩ ⟨f', hf'⟩))

theorem scalar_eq : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL T S) 𝓕 μ → ∀ M : Module.End ℂ (WO S T → ℂ), (∀ f, IsThetaFunO ψ S T f → IsThetaFunO ψ S T (M f)) → (∀ f, IsThetaFunO ψ S T f → ∫⁻ w in 𝓕, ‖M f w‖ₑ ^ 2 ∂μ = ∫⁻ w in 𝓕, ‖f w‖ₑ ^ 2 ∂μ) → ∀ f f', IsThetaFunO ψ S T f → IsThetaFunO ψ S T f' → ∫ x in 𝓕, M f x * star (M f' x) ∂μ = ∫ x in 𝓕, f x * star (f' x) ∂μ := by
  intro D ψ hψ S T μ 𝓕 hμ h𝓕 M hM hn f f' hf hf'
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  haveI : Countable (ratL T S) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact GlobalTheory.measure_addFundamentalDomain_lt_top_of_cocompact (G := WO S T) (ratL T S) hK hKc μ h𝓕⟩
  let Θ : Submodule ℂ (WO S T → ℂ) :=
    { carrier := {f | IsThetaFunO ψ S T f}
      add_mem' := GlobalTheory.WeilVacMove.isTheta_add
      zero_mem' := GlobalTheory.WeilVacMove.isTheta_zero
      smul_mem' := fun c _ h => GlobalTheory.WeilVacMove.isTheta_smul c h }
  have hb : ∀ g ∈ Θ, ∃ C : ℝ, ∀ w, ‖g w‖ ≤ C := fun g (hg : IsThetaFunO ψ S T g) => by
    have hp : ∀ γ ∈ ratL T S, ∀ w, ‖g (γ + w)‖ = ‖g w‖ := by
      rintro _ ⟨γ, rfl⟩ w
      exact (congrArg norm (hg.quasi γ w)).trans (by rw [norm_mul, hψ.1.2.1, one_mul])
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hg.cont.continuousOn
    refine ⟨C, fun w => ?_⟩
    obtain ⟨γ, hγ, h⟩ := hKc w
    rw [← hp γ hγ w]
    exact hC _ h
  exact integral_mul_star_eq (μ.restrict 𝓕) Θ (fun g (hg : IsThetaFunO ψ S T g) => hg.cont.measurable) hb M hM hn
    f f' hf hf'

end GlobalTheory.Mem.LiftPolar

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaFunctionScalarProductPreservedIsometryStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaFunction_scalarProduct_preserved_isometry : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL T S) 𝓕 μ → ∀ M : Module.End ℂ (WO S T → ℂ), (∀ f, IsThetaFunO ψ S T f → IsThetaFunO ψ S T (M f)) → (∀ f, IsThetaFunO ψ S T f → ∫⁻ w in 𝓕, ‖M f w‖ₑ ^ 2 ∂μ = ∫⁻ w in 𝓕, ‖f w‖ₑ ^ 2 ∂μ) → ∀ f f', IsThetaFunO ψ S T f → IsThetaFunO ψ S T f' → ∫ x in 𝓕, M f x * star (M f' x) ∂μ = ∫ x in 𝓕, f x * star (f' x) ∂μ := by
  first | exact @GlobalTheory.Mem.LiftPolar.scalar_eq | exact GlobalTheory.Mem.LiftPolar.scalar_eq | (intros; apply GlobalTheory.Mem.LiftPolar.scalar_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RationalSymplecticPointsSelfAnnihilator
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RationalSymplecticPointsSelfAnnihilator
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RatAnnih

section Scalar

variable {F : Type} [Field F] [NumberField F]

theorem inf_rat (L : Ainf F →+ ℂ) (hL : Continuous L)
    (hT : ∀ x : F, L (algebraMap F _ x) = ((Algebra.trace ℚ F x : ℚ) : ℂ)) (y : Ainf F)
    (h : ∀ c : 𝓞 F, ∃ n : ℤ, L (y * algebraMap F _ (c : F)) = n) : ∃ d : F, y = algebraMap F _ d := by
  classical
  have hb : ∀ i, ∃ n : ℤ, L (y * algebraMap F _ (integralBasis F i)) = n := fun i => by
    rw [integralBasis_apply]; exact h _
  choose n hn using hb
  refine ⟨∑ i, (n i : F) * (integralBasis F).traceDual i, funext fun v => ?_⟩
  let φ : Ainf F →+* ℂ := (InfinitePlace.Completion.extensionEmbedding v).comp (Pi.evalRingHom _ v)
  have hφ : Continuous φ :=
    (InfinitePlace.Completion.isometry_extensionEmbedding v).continuous.comp (continuous_apply v)
  have key : (fun w : Ainf F => φ w) = fun w => ∑ i, L (w * algebraMap F _ (integralBasis F i)) *
      φ (algebraMap F _ ((integralBasis F).traceDual i)) := by
    refine (InfiniteAdeleRing.denseRange_algebraMap F).equalizer hφ
      (continuous_finsetSum _ fun i _ => (hL.comp (continuous_id.mul continuous_const)).mul continuous_const) ?_
    funext x
    simp only [Function.comp_apply, ← map_mul, hT]
    conv_lhs => rw [← (integralBasis F).traceDual.sum_repr x]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, Module.Basis.traceDual_repr_apply, Algebra.traceForm_apply, Algebra.smul_def, map_mul,
      eq_ratCast]
    exact Finset.sum_congr rfl fun i _ => by
      rw [← RingHom.comp_apply φ (algebraMap F (Ainf F)), map_ratCast]
  apply (InfinitePlace.Completion.extensionEmbedding v).injective
  change φ y = φ (algebraMap F (Ainf F) _)
  rw [congrFun key y]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hn, map_sum, map_mul, map_intCast]

theorem fin_eq_zero {ψ : AddChar (AF F) ℂ} (hψ : Continuous ψ) (hv : ∀ v, ∃ y, psiV F ψ v y ≠ 1) (l : Af F)
    (h : ∀ c : F, ψ (pairA F 0 (l * algebraMap F _ c)) = 1) : l = 0 := by
  classical
  have hp : Continuous fun y : Af F => pairA F 0 (l * y) :=
    Continuous.prodMk continuous_const (continuous_const.mul continuous_id)
  have hall : ∀ z : Af F, ψ (pairA F 0 (l * z)) = 1 := by
    intro z
    obtain ⟨x, β, hβ, rfl⟩ := (GlobalTheory.AdLat.strong_approximation_mod_nat F 1 one_pos).1 z
    have h1 : ψ (pairA F 0 (l * β)) = 1 :=
      GlobalTheory.IntDense.mem_of_isClosed F (C := {y | ψ (pairA F 0 (l * y)) = 1})
        (isClosed_eq (hψ.comp hp) continuous_const) (fun a => h a) β hβ
    have e : pairA F 0 (l * (algebraMap F _ x + 1 • β)) =
        pairA F 0 (l * algebraMap F _ x) + pairA F 0 (l * β) := by
      rw [one_smul, mul_add]
      exact Prod.ext (add_zero _).symm rfl
    rw [e, ψ.map_add_eq_mul, h, h1, one_mul]
  have hext : ∀ a b : Af F, (∀ w, evalV F w a = evalV F w b) → a = b := fun a b hab =>
    Subtype.ext (funext hab)
  refine hext _ _ fun v => ?_
  by_contra hne
  rw [map_zero] at hne
  obtain ⟨y, hy⟩ := hv v
  have same : ∀ t, evalV F v (singleV F v t) = t := fun t => RestrictedProduct.single_eq_same
    (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) v t
  have diff : ∀ t w, w ≠ v → evalV F w (singleV F v t) = 0 := fun t w hw => RestrictedProduct.single_eq_of_ne
    (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) t hw
  refine hy ?_
  rw [psiV, ← hall (singleV F v ((evalV F v l)⁻¹ * y))]
  congr 2
  refine hext _ _ fun w => ?_
  by_cases hw : w = v
  · subst hw
    rw [map_mul, same, same, mul_inv_cancel_left₀ hne]
  · rw [map_mul, diff _ _ hw, diff _ _ hw, mul_zero]

theorem adele_rat {ψ : AddChar (AF F) ℂ} (hψ : IsCharAF F ψ) (hv : ∀ v, ∃ y, psiV F ψ v y ≠ 1)
    (L : Ainf F →+ ℂ) (hL : Continuous L)
    (hT : ∀ x : F, L (algebraMap F _ x) = ((Algebra.trace ℚ F x : ℚ) : ℂ))
    (hinf : ∀ x, psiInf F ψ x = Complex.exp (-(2 * Real.pi * Complex.I * L x))) (a : AF F)
    (h : ∀ c : F, ψ (a * algebraMap F _ c) = 1) : ∃ d : F, a = algebraMap F _ d := by
  have hsub : ∀ (b : AF F) (x : F), (∀ c : F, ψ (b * algebraMap F _ c) = 1) →
      ∀ c : F, ψ ((b - algebraMap F _ x) * algebraMap F _ c) = 1 := fun b x hb c => by
    rw [sub_mul, ← map_mul, AddChar.map_sub_eq_div, hb, hψ.2.2.1, div_one]
  obtain ⟨x, β, hβ, hx⟩ := (GlobalTheory.AdLat.strong_approximation_mod_nat F 1 one_pos).1 (sndA F a)
  have h1 := hsub a x h
  have hβ' : sndA F (a - algebraMap F _ x) = β := by
    rw [map_sub, AlgHom.commutes, hx, one_smul, add_sub_cancel_left]
  obtain ⟨d, hd⟩ := inf_rat L hL hT (fstA F (a - algebraMap F _ x)) fun c => by
    have h2 : ψ (pairA F 0 (β * algebraMap F _ (c : F))) = 1 := by
      refine GlobalTheory.IntDense.addChar_eq_one_of_integral F ψ hψ.1 c (fun r => ?_) β hβ
      have h3 := GlobalTheory.StdAdelicChar.ratChar_integer F (r * c)
      rw [GlobalTheory.StdRat.char_fin_rat ψ hψ, hinf, hT, map_neg, ← h3, GlobalTheory.StdAdelicChar.ratChar]
      congr 1
      push_cast
      ring
    have e : (a - algebraMap F _ x) * algebraMap F _ (c : F) =
        pairA F (fstA F (a - algebraMap F _ x) * algebraMap F _ (c : F)) 0 +
          pairA F 0 (β * algebraMap F _ (c : F)) := by
      rw [← hβ']
      exact Prod.ext (add_zero _).symm (zero_add _).symm
    have h4 := h1 c
    rw [e, ψ.map_add_eq_mul, h2, mul_one] at h4
    have h5 := (hinf _).symm.trans h4
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 h5
    refine ⟨-n, mul_left_cancel₀ Complex.two_pi_I_ne_zero ?_⟩
    push_cast
    linear_combination -hn
  have h6 := hsub _ d h1
  have h7 : fstA F (a - algebraMap F _ x - algebraMap F _ d) = 0 := by
    rw [map_sub, AlgHom.commutes, hd, sub_self]
  have h8 := fin_eq_zero hψ.1 hv (sndA F (a - algebraMap F _ x - algebraMap F _ d)) fun c => by
    rw [← h6 c]
    congr 1
    refine Prod.ext ?_ rfl
    change 0 = fstA F (a - algebraMap F _ x - algebraMap F _ d) * _
    rw [h7, zero_mul]
  refine ⟨x + d, ?_⟩
  rw [map_add (f := _), ← sub_eq_zero, ← sub_sub]
  exact Prod.ext h7 h8

end Scalar

theorem tensor_rat {F E : Type} [Field F] [CharZero F] [Field E] [Algebra F E] [FiniteDimensional F E]
    {R : Type} [CommRing R] [Algebra F R] (z : R ⊗[F] E)
    (h : ∀ e : E, ∃ d : F, Algebra.trace R (R ⊗[F] E) ((1 : R) ⊗ₜ[F] e * z) = algebraMap F R d) :
    ∃ e : E, z = (1 : R) ⊗ₜ[F] e := by
  classical
  let b := Module.finBasis F E
  have key : ∀ z : R ⊗[F] E,
      z = ∑ i, Algebra.trace R (R ⊗[F] E) ((1 : R) ⊗ₜ[F] b i * z) ⊗ₜ[F] b.traceDual i := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy =>
      simp only [mul_add, map_add (f := _), TensorProduct.add_tmul, Finset.sum_add_distrib]
      rw [← hx, ← hy]
    | tmul a e =>
      conv_lhs => rw [← b.traceDual.sum_repr e, TensorProduct.tmul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, GlobalTheory.LatVac.trace_tmul, Module.Basis.traceDual_repr_apply,
        Algebra.traceForm_apply, ← TensorProduct.smul_tmul, Algebra.smul_def, mul_comm, mul_comm e]
  choose d hd using h
  refine ⟨∑ i, d (b i) • b.traceDual i, ?_⟩
  rw [key z, TensorProduct.tmul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hd, ← TensorProduct.smul_tmul, Algebra.algebraMap_eq_smul_one]

theorem trace_mul_algebraMap {F E : Type} [Field F] [Field E] [Algebra F E]
    {R : Type} [CommRing R] [Algebra F R] (z : R ⊗[F] E) (e : E) (c : F) :
    Algebra.trace R (R ⊗[F] E) ((1 : R) ⊗ₜ[F] e * z) * algebraMap F R c =
      Algebra.trace R (R ⊗[F] E) ((1 : R) ⊗ₜ[F] (c • e) * z) := by
  rw [mul_comm, ← smul_eq_mul, ← map_smul, ← smul_mul_assoc, algebraMap_smul, ← TensorProduct.tmul_smul]

theorem sum_single {E A : Type} [Field E] [CommRing A] (ι : E →+* A) {m n : ℕ} (P : Matrix (Fin m) (Fin m) E)
    (Q : Matrix (Fin n) (Fin n) E) (hP : IsUnit P.det) (hQ : IsUnit Q.det) (a₀ : Fin m) (d₀ : Fin n) (e : E)
    (x : Fin n → Fin m → A) :
    ∑ a, ∑ b, ∑ c, ∑ d, ι (P⁻¹ a b) * ι ((P * Matrix.single a₀ d₀ e * Q⁻¹) b c) * ι (Q c d) * x d a =
      ι e * x d₀ a₀ := by
  have h1 : P⁻¹ * (P * Matrix.single a₀ d₀ e * Q⁻¹) * Q = Matrix.single a₀ d₀ e := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hQ, Matrix.mul_one,
      Matrix.nonsing_inv_mul_cancel_left _ _ hP]
  generalize P * Matrix.single a₀ d₀ e * Q⁻¹ = M at h1
  have h2 : ∀ a, ∑ b, ∑ c, ∑ d, ι (P⁻¹ a b) * ι (M b c) * ι (Q c d) * x d a =
      ∑ d, ι (Matrix.single a₀ d₀ e a d) * x d a := fun a => by
    rw [← h1]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mul_apply, map_sum, map_mul, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine (Finset.sum_congr rfl fun c _ => Finset.sum_comm).trans Finset.sum_comm
  simp only [h2]
  rw [Finset.sum_eq_single a₀, Finset.sum_eq_single d₀, Matrix.single_apply_same]
  · intro d _ hd
    rw [Matrix.single_apply_of_col_ne _ _ hd.symm, map_zero, zero_mul]
  · simp
  · intro a _ ha
    exact Finset.sum_eq_zero fun d _ => by rw [Matrix.single_apply_of_row_ne ha.symm, map_zero, zero_mul]
  · simp

theorem exists_symplO_eq {D : D7} (S T : HSp D) (x : WO S T) (i : Fin T.rank) (j : Fin S.rank) (e : D.host.E) :
    ∃ γ ∈ ratL T S, symplO S T x γ = Algebra.trace (AF D.host.F) (AE D) (incA D e * x i j) := by
  refine ⟨ratW T S fun c b => star ((S.gram * Matrix.single j i (D.host.xi0⁻¹ * e) * T.gram⁻¹) b c), ⟨_, rfl⟩, ?_⟩
  have h := sum_single (incA D) S.gram T.gram (GlobalTheory.LatVac.gram_det_isUnit S) (GlobalTheory.LatVac.gram_det_isUnit T) j i
    (D.host.xi0⁻¹ * e) x
  have h2 : hO S T x (ratW T S fun c b =>
      star ((S.gram * Matrix.single j i (D.host.xi0⁻¹ * e) * T.gram⁻¹) b c)) =
      incA D (D.host.xi0⁻¹ * e) * x i j := by
    rw [← h, hO]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ =>
      Finset.sum_congr rfl fun d _ => ?_
    exact congrArg (fun t => incA D (S.gram⁻¹ a b) * t * incA D (T.gram c d) * x d a)
      ((GlobalTheory.DualPairCheck.cA_incA _).trans (congrArg (incA D) (star_star _)))
  rw [symplO, h2, ← mul_assoc, ← RingHom.map_mul, mul_inv_cancel_left₀ (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D)]

theorem ratL_annihilator : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (x : WO S T), (∀ γ ∈ ratL T S, ψ (symplO S T x γ) = 1) ↔ x ∈ ratL T S := by
  intro D ψ hψ S T x
  haveI : Module.Finite D.host.F D.host.E := Module.finite_of_finrank_pos (by rw [D.sp.cm.deg2]; norm_num)
  constructor
  · intro h
    obtain ⟨θ, hθ⟩ := hψ.2.1
    let L : Ainf D.host.F →+ ℂ := AddMonoidHom.mk' (fun x => ∑ ρ, θ ρ (x ⊗ₜ[D.host.F] (1 : D.host.E))) fun a b => by
      simp only [map_add (f := _), TensorProduct.add_tmul, Finset.sum_add_distrib]
    have hrat := adele_rat hψ.1 (GlobalTheory.StdCharLocal.psiV_ne_one D ψ hψ) L
      (continuous_finsetSum _ fun ρ _ => (hθ ρ).2)
      (fun x => by
        show ∑ ρ, θ ρ (algebraMap D.host.F (Ainf D.host.F) x ⊗ₜ[D.host.F] (1 : D.host.E)) = _
        rw [GlobalTheory.StdRat.tmul_one_eq, Finset.sum_congr rfl fun ρ _ => (hθ ρ).1 _, GlobalTheory.StdRat.sum_tauE_eq_trace])
      (fun y => by
        rw [hψ.2.2 θ hθ]
        congr 1
        change _ = -(_ * ∑ ρ, θ ρ (y ⊗ₜ[D.host.F] (1 : D.host.E)))
        push_cast
        ring)
    have hent : ∀ i j, ∃ e : D.host.E, x i j = (1 : AF D.host.F) ⊗ₜ[D.host.F] e := fun i j =>
      tensor_rat (x i j) fun e => hrat _ fun c => by
        obtain ⟨γ, hγ, hγe⟩ := exists_symplO_eq S T x i j (c • e)
        exact (congrArg ψ ((trace_mul_algebraMap (x i j) e c).trans hγe.symm)).trans (h γ hγ)
    choose M hM using hent
    exact ⟨Matrix.of M, Matrix.ext fun i j => (hM i j).symm⟩
  · rintro ⟨γ, rfl⟩ _ ⟨γ', rfl⟩
    obtain ⟨a, ha⟩ := GlobalTheory.SymplecticOrthogonalSesquilinear.symplO_rat D S T γ γ'
    exact (congrArg ψ ha).trans (hψ.1.2.2.1 a)

end GlobalTheory.RatAnnih

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RationalSymplecticPointsSelfAnnihilatorStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalSymplecticPoints_self_annihilator : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (x : WO S T), (∀ γ ∈ ratL T S, ψ (symplO S T x γ) = 1) ↔ x ∈ ratL T S := by
  first | exact @GlobalTheory.RatAnnih.ratL_annihilator | exact GlobalTheory.RatAnnih.ratL_annihilator | (intros; apply GlobalTheory.RatAnnih.ratL_annihilator <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DualWeylModuleTensorCoefficientUniversalStatement
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

open Formalism.L2.DIV GlobalTheory.CoefIrred in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualWeylModule_tensor_coefficient_universal :
    ∀ (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n) (V : Type) [AddCommGroup V]
      [Module ℂ V] (F : (∀ v, nablaSq ℂ n (lam v)) →ₘₗ[ℂ] V),
      ∃! f : Formalism.L2.DIV.VV ℂ lam →ₗ[ℂ] V,
        ∀ u, f (GlobalTheory.CoefIrred.tenMul (K := ℂ) lam u) = F u := by
  intro ι _ n lam V _ _ F
  have hBasis : ∀ i, bVV ℂ lam i = tenMul lam (fun τ => ssBasis ℂ (lam τ) (i τ)) := by
    intro i
    apply Subtype.ext
    rw [bVV_coe, tenMul_coe, bVVfun]
    simp only [ssBasis_coe]
  let f := (bVV ℂ lam).constr ℂ (fun i => F (fun τ => ssBasis ℂ (lam τ) (i τ)))
  refine ⟨f, ?_, ?_⟩
  · have hComp : f.compMultilinearMap (tenMul lam) = F := by
      apply Module.Basis.ext_multilinear (fun τ => ssBasis ℂ (lam τ))
      intro i
      simp only [LinearMap.compMultilinearMap_apply, ← hBasis, f, Module.Basis.constr_basis]
    intro u
    exact congrArg (fun m => m u) hComp
  · intro g hg
    apply (bVV ℂ lam).ext
    intro i
    simp only [f, Module.Basis.constr_basis]
    rw [hBasis, hg]
end
