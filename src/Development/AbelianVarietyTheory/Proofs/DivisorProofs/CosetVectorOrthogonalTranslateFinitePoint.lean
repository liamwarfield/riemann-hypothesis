module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubsingletonSpDualNumber
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrincipallyPolarisedPowerUnimodularForm

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuedFiniteUnitaryLeOneOffOpenSubset
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuedFiniteUnitaryLeOneOffOpenSubset
open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop (modT)
open GlobalTheory.BottomIPData (sfB)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat IsFockVec IsSphOff volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip)
open GlobalTheory.Core.Rk.IP (openOff integrand wcoef)
open GlobalTheory.StdLoc (glVol blockIdx)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.NormRatio
open scoped nonZeroDivisors
open GlobalTheory.CosetOrth

noncomputable section

open scoped TensorProduct Matrix

namespace GlobalTheory.CosetOrth

section Local

open GlobalTheory.AdelicU GlobalTheory.LFun

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem valued_toCompl_le_one {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)} (h : w.under (𝓞 F) = v)
    {y : Fv F v ⊗[F] E} (hy : y ∈ intLoc F E v) : Valued.v (toCompl h y) ≤ 1 :=
  (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 <|
    intLoc_induction (p := fun y => toCompl h y ∈ w.adicCompletionIntegers E)
      (fun _ ha x => mul_mem (complMap_mem h ha) (GlobalTheory.AdeleBaseChange.algebraMap_int_mem x w))
      (by rw [map_zero]; exact zero_mem _) (fun _ _ h h' => by rw [map_add]; exact add_mem h h')
      (fun _ h => by rw [map_neg]; exact neg_mem h) hy

theorem map_evalV_map_sndA (v : HeightOneSpectrum (𝓞 F)) (z : AF F ⊗[F] E) :
    Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (AlgHom.id F E)
      (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) z) =
      Algebra.TensorProduct.map (evFin F v) (AlgHom.id F E) z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a e => rfl
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

end Local

variable {D : D7}

theorem valued_finMat_finStd_le_one (V : HSp D) (hG : V.gram = 1) (k : GA D V)
    (w : HeightOneSpectrum (𝓞 D.host.E))
    (hk : GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram (w.under (𝓞 D.host.F)) k ∈
      GlobalTheory.AdelicU.stabLoc D.sp.cm.sig V.gram (stdLat V) (w.under (𝓞 D.host.F))) (i j : Fin V.rank) :
    Valued.v (finMat (GlobalTheory.BotClassDict.finStd V hG k) i j w) ≤ 1 := by
  have hL : stdLat V = GlobalTheory.AdelicU.stdLattice D.host.E V.rank := by
    ext x
    exact ⟨fun h i _ => Submodule.mem_one.1 (h i trivial), fun h i _ => Submodule.mem_one.2 (h i trivial)⟩
  rw [hL] at hk
  have h1 := (GlobalTheory.AdelicU.mem_stabLoc_stdLattice_iff.1 hk).1 i j
  have e : finMat (GlobalTheory.BotClassDict.finStd V hG k) i j =
      GlobalTheory.LFun.finAdEquiv D.host.F D.host.E ((finHom V k).1 i j) := by
    rw [← GlobalTheory.BotClassDict.toAfE_finStd V hG, GlobalTheory.BotClassDict.finAdEquiv_toAfE]
    rfl
  rw [e, GlobalTheory.LFun.finAdEquiv_apply rfl]
  refine valued_toCompl_le_one rfl ?_
  have e2 := map_evalV_map_sndA (w.under (𝓞 D.host.F)) ((matHom V k).1 i j)
  exact e2 ▸ h1

end GlobalTheory.CosetOrth

theorem GlobalTheory.CosetOrth.valued_finMat_le_one_of_mem_openOff : ∀ {D : D7} (V : HSp D) (g : GA D V) (y : Formalism.MainNotions.StandardLatticesGL3.GA D V.rank) (Sf : Finset (FinPl D)), V.gram = 1 →
  GlobalTheory.BotFormula.IsFinPt V g y → g ∈ openOff V (stdLat V) Sf →
  ∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) ∉ Sf → ∀ i j,
    Valued.v (finMat y i j w) ≤ 1 ∧ Valued.v (finMat y⁻¹ i j w) ≤ 1 := by
  intro D V g y Sf hG hy hg w hw i j
  have hfy := GlobalTheory.BotClassDict.finStd_of_isFinPt V hG hy
  subst hfy
  have h := hg _ hw
  refine ⟨GlobalTheory.CosetOrth.valued_finMat_finStd_le_one V hG g w h i j, ?_⟩
  rw [← map_inv]
  refine GlobalTheory.CosetOrth.valued_finMat_finStd_le_one V hG g⁻¹ w ?_ i j
  have h' := inv_mem h
  rwa [← map_inv] at h'
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuedFiniteUnitaryLeOneOffOpenSubsetStatement
open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop (modT)
open GlobalTheory.BottomIPData (sfB)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat IsFockVec IsSphOff volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip)
open GlobalTheory.Core.Rk.IP (openOff integrand wcoef)
open GlobalTheory.StdLoc (glVol blockIdx)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.NormRatio
open scoped nonZeroDivisors
open GlobalTheory.CosetOrth

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valued_finiteUnitary_le_one_off_openSubset : ∀ {D : D7} (V : HSp D) (g : GA D V) (y : Formalism.MainNotions.StandardLatticesGL3.GA D V.rank) (Sf : Finset (FinPl D)), V.gram = 1 →
  GlobalTheory.BotFormula.IsFinPt V g y → g ∈ openOff V (stdLat V) Sf →
  ∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) ∉ Sf → ∀ i j,
    Valued.v (finMat y i j w) ≤ 1 ∧ Valued.v (finMat y⁻¹ i j w) ≤ 1 := by
  first | exact @GlobalTheory.CosetOrth.valued_finMat_le_one_of_mem_openOff | exact GlobalTheory.CosetOrth.valued_finMat_le_one_of_mem_openOff | (intros; apply GlobalTheory.CosetOrth.valued_finMat_le_one_of_mem_openOff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DenseRationalHomPointsIdealCompletion
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DenseRationalHomPointsIdealCompletion
open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop (modT)
open GlobalTheory.BottomIPData (sfB)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat IsFockVec IsSphOff volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip)
open GlobalTheory.Core.Rk.IP (openOff integrand wcoef)
open GlobalTheory.StdLoc (glVol blockIdx)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.NormRatio
open scoped nonZeroDivisors
open GlobalTheory.CosetOrth

noncomputable section

namespace GlobalTheory.CosetOrthDens

section General

variable {E : Type} [Field E] [NumberField E]

theorem inHat_algebraMap_iff {I : FractionalIdeal (𝓞 E)⁰ E} (hI : I ≠ 0) (x : E) :
    InHat I (algebraMap E (FiniteAdeleRing (𝓞 E) E) x) ↔ x ∈ I :=
  (GlobalTheory.Idele.mem_adelicIdeal_iff hI).symm.trans (GlobalTheory.Idele.algebraMap_mem_adelicIdeal hI x)

theorem isOpen_inHat_one : IsOpen {x : FiniteAdeleRing (𝓞 E) E | InHat 1 x} := by
  have h := RestrictedProduct.isOpen_forall_mem (R := fun v : HeightOneSpectrum (𝓞 E) => v.adicCompletion E)
    (A := fun v => (v.adicCompletionIntegers E : Set (v.adicCompletion E))) fun v => Valued.isOpen_valuationSubring _
  have e : {x : FiniteAdeleRing (𝓞 E) E | InHat 1 x} =
      {x : FiniteAdeleRing (𝓞 E) E | ∀ v, x v ∈ (v.adicCompletionIntegers E : Set (v.adicCompletion E))} := by
    ext x
    exact inHat_one_iff x
  rw [e]
  exact h

theorem isOpen_inHat {I : FractionalIdeal (𝓞 E)⁰ E} (hI : I ≠ 0) : IsOpen {x : FiniteAdeleRing (𝓞 E) E | InHat I x} := by
  obtain ⟨c, hc0, hc⟩ := FractionalIdeal.exists_ne_zero_mem_isInteger hI
  set a : E := algebraMap (𝓞 E) E c with ha
  have ha0 : a ≠ 0 := by simpa [ha] using hc0
  rw [isOpen_iff_mem_nhds]
  intro y hy
  have hcont : Continuous fun x : FiniteAdeleRing (𝓞 E) E => (x - y) * algebraMap E (FiniteAdeleRing (𝓞 E) E) a⁻¹ :=
    (continuous_id.sub continuous_const).mul continuous_const
  refine Filter.mem_of_superset ((isOpen_inHat_one.preimage hcont).mem_nhds ?_) fun x hx => ?_
  · show InHat 1 ((y - y) * _)
    rw [sub_self, zero_mul]
    exact inHat_zero 1
  · have h1 := InHat.mul_left hx ((inHat_algebraMap_iff hI a).2 hc)
    rw [mul_assoc, ← map_mul, inv_mul_cancel₀ ha0, map_one, mul_one] at h1
    have h2 := h1.add hy
    rwa [sub_add_cancel] at h2

end General

variable {D : D7}

def lift (D : D7) (s : FA D) : AE D :=
  GlobalTheory.LFun.extZero D.host.F D.host.E ((GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).symm s)

theorem continuous_lift : Continuous (lift D) :=
  GlobalTheory.LFun.continuous_extZero.comp GlobalTheory.LFun.continuous_finAdEquiv_symm

theorem infPart_lift (s : FA D) : infPart D (lift D s) = 0 := GlobalTheory.LFun.infTens_extZero _

theorem fe_lift (s : FA D) : fe D (lift D s) = s := by
  have : finPart D (lift D s) = (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).symm s := GlobalTheory.LFun.finTens_extZero _
  rw [fe_apply, this, RingEquiv.apply_symm_apply]

theorem lift_fe {x : AE D} (hx : infPart D x = 0) : lift D (fe D x) = x := by
  refine sub_eq_zero.1 (GlobalTheory.LatVac.eq_zero_of_parts _ ?_ ?_)
  · rw [RingHom.map_sub, infPart_lift, hx, sub_self]
  · apply (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).injective
    rw [map_zero, ← fe_apply, map_sub, fe_lift, sub_self]

theorem lift_algebraMap (γ : D.host.E) :
    lift D (algebraMap D.host.E (FA D) γ) = pairA D.host.F 0 1 ⊗ₜ[D.host.F] γ := by
  have h1 : infPart D (pairA D.host.F 0 1 ⊗ₜ[D.host.F] γ) = 0 := by
    show (0 : Ainf D.host.F) ⊗ₜ[D.host.F] γ = 0
    exact TensorProduct.zero_tmul _ _
  have h2 : fe D (pairA D.host.F 0 1 ⊗ₜ[D.host.F] γ) = algebraMap D.host.E (FA D) γ := by
    show GlobalTheory.LFun.toFinAd D.host.F D.host.E ((1 : Af D.host.F) ⊗ₜ[D.host.F] γ) = _
    rw [GlobalTheory.LFun.toFinAd_tmul, map_one, one_mul]
  rw [← h2, lift_fe h1]

theorem exists_finPt_sub_mem : ∀ {D : D7} (S T : HSp D) (r : D.host.E) (I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E), r ≠ 0 → I ≠ 0 →
  ∀ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) → ∀ u : WO S T, HatPt r I u →
  ∃ z : Matrix (Fin T.rank) (Fin S.rank) D.host.E, (∀ i j, z i j ∈ I) ∧ u - finPt (S := S) (T := T) rfl rfl r z ∈ U := by
  intro D S T r I hr hI U hU u hu
  haveI hg : IsTopologicalAddGroup (WO S T) := inferInstance
  haveI : ContinuousSub (WO S T) := IsTopologicalAddGroup.to_continuousSub
  let Φ : (Fin T.rank → Fin S.rank → FA D) → WO S T := fun y =>
    Matrix.of fun i j => lift D (algebraMap D.host.E (FA D) r⁻¹ * y i j)
  have hΦ : Continuous Φ := continuous_matrix fun i j =>
    continuous_lift.comp (continuous_const.mul ((continuous_apply j).comp (continuous_apply i)))
  have hd : DenseRange (Pi.map fun (_ : Fin T.rank) => Pi.map fun (_ : Fin S.rank) => algebraMap D.host.E (FA D)) :=
    DenseRange.piMap fun _ => DenseRange.piMap fun _ =>
      PI.UnipApproxD.IntegersDenseFiniteAdeles.denseRange (R := 𝓞 D.host.E) (K := D.host.E)
  have hO : IsOpen ({y | u - Φ y ∈ U} ∩ ⋂ i, ⋂ j, {y : Fin T.rank → Fin S.rank → FA D | InHat I (y i j)}) :=
    (hU.preimage (continuous_const.sub hΦ)).inter (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      (isOpen_inHat hI).preimage (f := fun y : Fin T.rank → Fin S.rank → FA D => y i j)
        ((continuous_apply j).comp (continuous_apply i)))
  have h0 : Φ (fun i j => algebraMap D.host.E (FA D) r * fe D (u i j)) = u := by
    funext i j
    show lift D (algebraMap D.host.E (FA D) r⁻¹ * (algebraMap D.host.E (FA D) r * fe D (u i j))) = u i j
    rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hr, map_one, one_mul]
    exact lift_fe (congrFun (congrFun hu.1 i) j)
  obtain ⟨z, hz1, hz2⟩ := hd.exists_mem_open hO ⟨fun i j => algebraMap D.host.E (FA D) r * fe D (u i j), by
    show u - Φ _ ∈ U
    rw [h0, sub_self]
    exact U.zero_mem, Set.mem_iInter.2 fun i => Set.mem_iInter.2 fun j => hu.2 i j⟩
  refine ⟨Matrix.of fun i j => -z i j, fun i j => ?_, ?_⟩
  · have : z i j ∈ I := (inHat_algebraMap_iff hI _).1 (Set.mem_iInter.1 (Set.mem_iInter.1 hz2 i) j)
    exact (I : Submodule (𝓞 D.host.E) D.host.E).neg_mem this
  · have e : finPt (S := S) (T := T) rfl rfl r (Matrix.of fun i j => -z i j) =
        Φ (Pi.map (fun (_ : Fin T.rank) => Pi.map fun (_ : Fin S.rank) => algebraMap D.host.E (FA D)) z) := by
      funext i j
      show pairA D.host.F 0 1 ⊗ₜ[D.host.F] (-(r⁻¹ * -z i j)) =
        lift D (algebraMap D.host.E (FA D) r⁻¹ * algebraMap D.host.E (FA D) (z i j))
      rw [← map_mul, lift_algebraMap, mul_neg, neg_neg]
    rw [e]
    exact hz1

end GlobalTheory.CosetOrthDens
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DenseRationalHomPointsIdealCompletionStatement
open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop (modT)
open GlobalTheory.BottomIPData (sfB)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat IsFockVec IsSphOff volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip)
open GlobalTheory.Core.Rk.IP (openOff integrand wcoef)
open GlobalTheory.StdLoc (glVol blockIdx)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.NormRatio
open scoped nonZeroDivisors
open GlobalTheory.CosetOrth

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dense_rationalHomPoints_idealCompletion : ∀ {D : D7} (S T : HSp D) (r : D.host.E) (I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E), r ≠ 0 → I ≠ 0 →
  ∀ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) → ∀ u : WO S T, HatPt r I u →
  ∃ z : Matrix (Fin T.rank) (Fin S.rank) D.host.E, (∀ i j, z i j ∈ I) ∧ u - finPt (S := S) (T := T) rfl rfl r z ∈ U := by
  first | exact @GlobalTheory.CosetOrthDens.exists_finPt_sub_mem | exact GlobalTheory.CosetOrthDens.exists_finPt_sub_mem | (intros; apply GlobalTheory.CosetOrthDens.exists_finPt_sub_mem <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugatePlaceValuationCountUnder
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugatePlaceValuationCountUnder
open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop (modT)
open GlobalTheory.BottomIPData (sfB)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat IsFockVec IsSphOff volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip)
open GlobalTheory.Core.Rk.IP (openOff integrand wcoef)
open GlobalTheory.StdLoc (glVol blockIdx)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.NormRatio
open scoped nonZeroDivisors
open GlobalTheory.CosetOrth

noncomputable section

namespace GlobalTheory.ConjPlace

open GlobalTheory.IdemSupport (cP cO mem_cP cO_cO cO_coe)

theorem conj_smul_eq (D : D7) (x : 𝓞 D.host.E) : D.host.conj • x = cO D x := by
  apply RingOfIntegers.ext
  rw [cO_coe, Formalism.BasicNotions.Examples₂.star_eq_conj]
  rfl

theorem mem_conj_smul (D : D7) (I : Ideal (𝓞 D.host.E)) (x : 𝓞 D.host.E) :
    x ∈ (D.host.conj • I : Ideal (𝓞 D.host.E)) ↔ cO D x ∈ I := by
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem]
  have : D.host.conj⁻¹ • x = cO D x := by
    rw [inv_smul_eq_iff, conj_smul_eq, cO_cO]
  rw [this]

theorem count_conj (D : D7) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : (cP w).asIdeal = D.host.conj • w.asIdeal)
    (𝔞 : Ideal (𝓞 D.host.E)) (h : 𝔞 ≠ ⊥) :
    FractionalIdeal.count D.host.E (cP w)
      ((D.host.conj • 𝔞 : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) =
      FractionalIdeal.count D.host.E w (𝔞 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) := by
  have h' : (D.host.conj • 𝔞 : Ideal (𝓞 D.host.E)) ≠ 0 := fun e => h (by
    have := congrArg (fun I : Ideal (𝓞 D.host.E) => D.host.conj⁻¹ • I) e
    simpa using this)
  rw [FractionalIdeal.count_coe _ _ h', FractionalIdeal.count_coe _ _ h]
  congr 1
  refine eq_of_forall_le_iff fun k => ?_
  rw [← Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.2 h') (cP w).associates_irreducible,
    ← Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.2 h) w.associates_irreducible,
    ← Associates.mk_pow, ← Associates.mk_pow, Associates.mk_le_mk_iff_dvd, Associates.mk_le_mk_iff_dvd,
    Ideal.dvd_iff_le, Ideal.dvd_iff_le, hw, ← smul_pow', Ideal.pointwise_smul_le_pointwise_smul_iff]

theorem exists_norm (D : D7) (x : 𝓞 D.host.E) :
    ∃ y : 𝓞 D.host.F, algebraMap (𝓞 D.host.F) (𝓞 D.host.E) y = x * cO D x := by
  have hm : ((x * cO D x : 𝓞 D.host.E) : D.host.E) ∈ maximalRealSubfield D.host.E := by
    rw [← IsCMField.complexConj_eq_self_iff]
    change star ((x * cO D x : 𝓞 D.host.E) : D.host.E) = _
    rw [← cO_coe, map_mul, cO_cO, mul_comm]
  refine ⟨⟨⟨_, hm⟩, ?_⟩, rfl⟩
  exact (isIntegral_algebraMap_iff ).1 (x * cO D x).isIntegral_coe

theorem cO_algebraMap (D : D7) (y : 𝓞 D.host.F) :
    cO D (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) y) = algebraMap (𝓞 D.host.F) (𝓞 D.host.E) y := by
  apply RingOfIntegers.ext
  rw [cO_coe]
  exact (IsCMField.complexConj_eq_self_iff D.host.E _).2 (y : D.host.F).2

theorem under_cP (D : D7) (w : HeightOneSpectrum (𝓞 D.host.E)) :
    (cP w).under (𝓞 D.host.F) = w.under (𝓞 D.host.F) := by
  ext y
  change algebraMap (𝓞 D.host.F) (𝓞 D.host.E) y ∈ (cP w).asIdeal ↔ algebraMap (𝓞 D.host.F) (𝓞 D.host.E) y ∈ w.asIdeal
  rw [mem_cP, cO_algebraMap]

theorem under_eq_iff (D : D7) (w w'' : HeightOneSpectrum (𝓞 D.host.E)) :
    w''.under (𝓞 D.host.F) = w.under (𝓞 D.host.F) ↔ w'' = w ∨ w'' = cP w := by
  refine ⟨fun h => ?_, ?_⟩
  · have hs : (w''.asIdeal : Set (𝓞 D.host.E)) ⊆ w.asIdeal ∪ (cP w).asIdeal := fun x hx => by
      obtain ⟨y, hy⟩ := exists_norm D x
      have h1 : y ∈ (w''.under (𝓞 D.host.F)).asIdeal := by
        change algebraMap (𝓞 D.host.F) (𝓞 D.host.E) y ∈ w''.asIdeal
        rw [hy]; exact Ideal.mul_mem_right _ _ hx
      rw [h] at h1
      change algebraMap (𝓞 D.host.F) (𝓞 D.host.E) y ∈ w.asIdeal at h1
      rw [hy] at h1
      exact w.isPrime.mem_or_mem h1
    exact (Ideal.subset_union.1 hs).imp GlobalTheory.IdemSupport.eq_of_le GlobalTheory.IdemSupport.eq_of_le
  · rintro (rfl | rfl)
    · rfl
    · exact under_cP D w

theorem conj_place : ∀ (D : D7), ∀ w : HeightOneSpectrum (𝓞 D.host.E), ∃ w' : HeightOneSpectrum (𝓞 D.host.E), w'.asIdeal = D.host.conj • w.asIdeal ∧
    (∀ x : Formalism.MainNotions.StandardLatticesGL3.AE D, Valued.v (GlobalTheory.BotFormula.toFinE D (Formalism.MainNotions.StandardLatticesGL3.sgA D x) w') = Valued.v (GlobalTheory.BotFormula.toFinE D x w)) ∧
    (∀ 𝔞 : Ideal (𝓞 D.host.E), 𝔞 ≠ ⊥ → FractionalIdeal.count D.host.E w' ((D.host.conj • 𝔞 : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) =
      FractionalIdeal.count D.host.E w (𝔞 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)) ∧
    ∀ w'' : HeightOneSpectrum (𝓞 D.host.E), w''.under (𝓞 D.host.F) = w.under (𝓞 D.host.F) ↔ w'' = w ∨ w'' = w' := by
  intro D w
  have hw : (cP w).asIdeal = D.host.conj • w.asIdeal := by
    ext x
    rw [mem_cP, mem_conj_smul]
  refine ⟨cP w, hw, fun x => ?_, count_conj D w hw, under_eq_iff D w⟩
  have hc : w = GlobalTheory.CuspRep.conjSrc (D.host.conj : D.host.E ≃+* D.host.E) (cP w) :=
    GlobalTheory.CuspRep.eq_conjSrc fun y => by
      have := GlobalTheory.ConjVal.valuation_cP w y
      rw [Formalism.BasicNotions.Examples₂.star_eq_conj] at this
      exact this
  rw [GlobalTheory.BotFormula.toFinE_sgA]
  refine ((GlobalTheory.CuspRep.conjLoc_spec (D.host.conj : D.host.E ≃+* D.host.E) (cP w)).2.2
    (GlobalTheory.BotFormula.toFinE D x (GlobalTheory.CuspRep.conjSrc (D.host.conj : D.host.E ≃+* D.host.E) (cP w)))).trans ?_
  rw [← hc]

end GlobalTheory.ConjPlace
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugatePlaceValuationCountUnderStatement
open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop (modT)
open GlobalTheory.BottomIPData (sfB)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat IsFockVec IsSphOff volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip)
open GlobalTheory.Core.Rk.IP (openOff integrand wcoef)
open GlobalTheory.StdLoc (glVol blockIdx)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.NormRatio
open scoped nonZeroDivisors
open GlobalTheory.CosetOrth

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugatePlace_valuation_count_under : ∀ (D : D7), ∀ w : HeightOneSpectrum (𝓞 D.host.E), ∃ w' : HeightOneSpectrum (𝓞 D.host.E), w'.asIdeal = D.host.conj • w.asIdeal ∧
    (∀ x : Formalism.MainNotions.StandardLatticesGL3.AE D, Valued.v (GlobalTheory.BotFormula.toFinE D (Formalism.MainNotions.StandardLatticesGL3.sgA D x) w') = Valued.v (GlobalTheory.BotFormula.toFinE D x w)) ∧
    (∀ 𝔞 : Ideal (𝓞 D.host.E), 𝔞 ≠ ⊥ → FractionalIdeal.count D.host.E w' ((D.host.conj • 𝔞 : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) =
      FractionalIdeal.count D.host.E w (𝔞 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)) ∧
    ∀ w'' : HeightOneSpectrum (𝓞 D.host.E), w''.under (𝓞 D.host.F) = w.under (𝓞 D.host.F) ↔ w'' = w ∨ w'' = w' := by
  first | exact @GlobalTheory.ConjPlace.conj_place | exact GlobalTheory.ConjPlace.conj_place | (intros; apply GlobalTheory.ConjPlace.conj_place <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuedOneSubLeOfMovesIdealCompletion
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuedOneSubLeOfMovesIdealCompletion
open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop (modT)
open GlobalTheory.BottomIPData (sfB)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat IsFockVec IsSphOff volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip)
open GlobalTheory.Core.Rk.IP (openOff integrand wcoef)
open GlobalTheory.StdLoc (glVol blockIdx)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.NormRatio
open scoped nonZeroDivisors
open GlobalTheory.CosetOrth

namespace GlobalTheory.CosetOrth

theorem exists_single_adele {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (x : w.adicCompletion E) :
    ∃ s : FiniteAdeleRing (𝓞 E) E, s w = x ∧ ∀ u, u ≠ w → s u = 0 := by
  refine ⟨⟨Pi.single w x, ?_⟩, ?_, ?_⟩
  · refine Filter.eventually_cofinite.2 ((Set.finite_singleton w).subset fun u hu => ?_)
    by_contra hne
    apply hu
    rw [Pi.single_eq_of_ne hne]
    exact zero_mem _
  · exact Pi.single_eq_same (M := fun u : HeightOneSpectrum (𝓞 E) => u.adicCompletion E) w x
  · intro u hu
    exact Pi.single_eq_of_ne (M := fun u : HeightOneSpectrum (𝓞 E) => u.adicCompletion E) hu x

theorem row_bound {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ)
    (hv : Function.Surjective v) {ι : Type} [Fintype ι] (δ h : ι → K) (hδ : ∀ k, v (δ k) ≤ 1) {C : Γ} (hC : 1 < C)
    (H : ∀ x, v x ≤ C → (∀ k, v (x * h k) ≤ C) → ∀ j, v (x * (δ j - h j)) ≤ 1) (j : ι) :
    v (δ j - h j) ≤ C⁻¹ := by
  have hC0 : 0 < C := zero_lt_one.trans hC
  have hint : ∀ k, v (h k) ≤ 1 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨k₀, hk₀⟩ := hcon
    obtain ⟨k, -, hk⟩ := Finset.exists_max_image Finset.univ (fun k => v (h k)) ⟨k₀, Finset.mem_univ _⟩
    have h1 : 1 < v (h k) := hk₀.trans_le (hk k₀ (Finset.mem_univ _))
    have h0 : 0 < v (h k) := zero_lt_one.trans h1
    obtain ⟨x, hx⟩ := hv (C * (v (h k))⁻¹)
    have hxk : v x * v (h k) = C := by rw [hx, mul_assoc, inv_mul_cancel₀ h0.ne', mul_one]
    have key := H x (by rw [← hxk]; exact le_mul_of_one_le_right' h1.le)
      (fun l => by rw [map_mul, ← hxk]; gcongr; exact hk l (Finset.mem_univ _)) k
    rw [map_mul, v.map_sub_eq_of_lt_right ((hδ k).trans_lt h1), hxk] at key
    exact absurd hC (not_lt.2 key)
  obtain ⟨x, hx⟩ := hv C
  have key := H x hx.le (fun l => by rw [map_mul, hx]; exact mul_le_of_le_one_right' (hint l)) j
  rw [map_mul, hx] at key
  calc v (δ j - h j) = C⁻¹ * (C * v (δ j - h j)) := by rw [← mul_assoc, inv_mul_cancel₀ hC0.ne', one_mul]
    _ ≤ C⁻¹ * 1 := by gcongr
    _ = C⁻¹ := mul_one _

theorem valued_one_sub_le_of_moves_integral : ∀ {E : Type} [Field E] [NumberField E] (I : FractionalIdeal (𝓞 E)⁰ E) (w : HeightOneSpectrum (𝓞 E)) (c : ℤ) (n : E)
  {a : ℕ} (H : Matrix (Fin a) (Fin a) (FiniteAdeleRing (𝓞 E) E)), w.valuation E n = 1 → FractionalIdeal.count E w I = -c → 1 ≤ c →
  (∀ (s : FiniteAdeleRing (𝓞 E) E) (i j : Fin a), InHat I s → (∀ k, InHat I (s * H i k)) →
    InHat 1 (algebraMap E (FiniteAdeleRing (𝓞 E) E) n * (s * (1 - H) i j))) →
  ∀ i j, Valued.v ((1 - H) i j w) ≤ WithZero.exp (-c) := by
  intro E _ _ I w c n a H hn hI hc hH i j
  have hsub : ∀ l, (1 - H) i l w = (1 : Matrix (Fin a) (Fin a) (FiniteAdeleRing (𝓞 E) E)) i l w - H i l w :=
    fun l => rfl
  rw [hsub, WithZero.exp_neg]
  refine row_bound Valued.v (w.valuedAdicCompletion_surjective E)
    (fun l => (1 : Matrix (Fin a) (Fin a) (FiniteAdeleRing (𝓞 E) E)) i l w) (fun l => H i l w) (fun k => ?_) ?_ ?_ j
  · by_cases hik : i = k
    · subst hik
      rw [Matrix.one_apply_eq]
      have : (1 : FiniteAdeleRing (𝓞 E) E) w = 1 := rfl
      rw [this, map_one]
    · rw [Matrix.one_apply_ne hik]
      have : (0 : FiniteAdeleRing (𝓞 E) E) w = 0 := rfl
      rw [this, map_zero]; exact zero_le
  · rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
  · intro x hx hxh l
    obtain ⟨s, hsw, hsu⟩ := exists_single_adele w x
    have h1 : InHat I s := fun u => by
      by_cases hu : u = w
      · subst hu; rw [hsw, hI, neg_neg]; exact hx
      · rw [hsu u hu, map_zero]; exact zero_le
    have h2 : ∀ k, InHat I (s * H i k) := fun k u => by
      have : (s * H i k) u = s u * H i k u := rfl
      rw [this]
      by_cases hu : u = w
      · subst hu; rw [hsw, hI, neg_neg]; exact hxh k
      · rw [hsu u hu, zero_mul, map_zero]; exact zero_le
    have key := (inHat_one_iff _).1 (hH s i l h1 h2) w
    have e : (algebraMap E (FiniteAdeleRing (𝓞 E) E) n * (s * (1 - H) i l)) w =
        (n : w.adicCompletion E) * (s w * (1 - H) i l w) := rfl
    rw [e, map_mul, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hn, one_mul, hsw, hsub] at key
    exact key

end GlobalTheory.CosetOrth
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuedOneSubLeOfMovesIdealCompletionStatement
open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop (modT)
open GlobalTheory.BottomIPData (sfB)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat IsFockVec IsSphOff volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip)
open GlobalTheory.Core.Rk.IP (openOff integrand wcoef)
open GlobalTheory.StdLoc (glVol blockIdx)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.NormRatio
open scoped nonZeroDivisors
open GlobalTheory.CosetOrth

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valued_one_sub_le_of_moves_idealCompletion : ∀ {E : Type} [Field E] [NumberField E] (I : FractionalIdeal (𝓞 E)⁰ E) (w : HeightOneSpectrum (𝓞 E)) (c : ℤ) (n : E)
  {a : ℕ} (H : Matrix (Fin a) (Fin a) (FiniteAdeleRing (𝓞 E) E)), w.valuation E n = 1 → FractionalIdeal.count E w I = -c → 1 ≤ c →
  (∀ (s : FiniteAdeleRing (𝓞 E) E) (i j : Fin a), InHat I s → (∀ k, InHat I (s * H i k)) →
    InHat 1 (algebraMap E (FiniteAdeleRing (𝓞 E) E) n * (s * (1 - H) i j))) →
  ∀ i j, Valued.v ((1 - H) i j w) ≤ WithZero.exp (-c) := by
  first | exact @GlobalTheory.CosetOrth.valued_one_sub_le_of_moves_integral | exact GlobalTheory.CosetOrth.valued_one_sub_le_of_moves_integral | (intros; apply GlobalTheory.CosetOrth.valued_one_sub_le_of_moves_integral <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetVectorOrthogonalTranslateFinitePoint
open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop (modT)
open GlobalTheory.BottomIPData (sfB)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat IsFockVec IsSphOff volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip)
open GlobalTheory.Core.Rk.IP (openOff integrand wcoef)
open GlobalTheory.StdLoc (glVol blockIdx)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.NormRatio
open scoped nonZeroDivisors
open Formalism.MainNotions.TaylorLogMetric (VC tor0 Th La Iop YYl U al)
open Formalism.MainNotions.StandardLatticesGL3 (stdL pt Wd wdPh La0)
open GlobalTheory.SplitScalar

noncomputable section

namespace GlobalTheory.CosetOrth

variable {D : D7}

section Read

variable {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} {a d : ℕ} {hS : S.rank = a} {hT : T.rank = d}
  {δ : ℂ} {r : D.host.E}

theorem symplOH_self (x : WO S T) : symplOH S T x x = 0 := by
  have h := symplOH_add_self S T x x
  have h2 := symplOH_skew S T x x
  have h3 : symplO S T x x = 0 := by rw [← h]; nth_rewrite 1 [h2]; exact neg_add_cancel _
  rw [symplOH, h3, mul_zero]

theorem finPt_neg (z : Matrix (Fin d) (Fin a) D.host.E) : finPt hS hT r (-z) = -finPt hS hT r z := by
  unfold finPt
  rw [← map_neg]
  congr 1
  ext i j
  simp

theorem u_neg_u (T : Formalism.MainNotions.TaylorLogMetric.Tor D) (x : VC D a d) (G : VC D a d → ℂ) : U D T (-x) (U D T x G) = G := by
  funext z
  have h1 : ∀ y, Formalism.MainNotions.TaylorLogMetric.Hf D T y (-x) = -Formalism.MainNotions.TaylorLogMetric.Hf D T y x := fun y => by
    simp [Formalism.MainNotions.TaylorLogMetric.Hf, neg_div]
  have h2 : Formalism.MainNotions.TaylorLogMetric.Hf D T (z + -x) x = Formalism.MainNotions.TaylorLogMetric.Hf D T z x - Formalism.MainNotions.TaylorLogMetric.Hf D T x x := by
    simp [Formalism.MainNotions.TaylorLogMetric.Hf, add_mul, Finset.sum_add_distrib, sub_eq_add_neg, add_div, neg_div]
  have h3 : Formalism.MainNotions.TaylorLogMetric.Hf D T (-x) x = -Formalism.MainNotions.TaylorLogMetric.Hf D T x x := by
    simp [Formalism.MainNotions.TaylorLogMetric.Hf, neg_div]
  simp only [U, h1, h2, h3, neg_add_cancel_right]
  rw [mul_assoc, ← Complex.exp_add]
  convert mul_one _
  rw [← Complex.exp_zero]
  congr 1
  ring

theorem exists_read_of_wd (h : Setup ψ θ S T ⊤ δ r) {G : VC D a d → ℂ} {φ : WO S T → ℂ} {c : ℂ} (hc : c ≠ 0)
    (z : Matrix (Fin d) (Fin a) D.host.E)
    (hφ : Reads ψ θ hS hT ⊤ δ r (c • Wd D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ z) G) φ) :
    ∃ (c' : ℂ) (φ₁ : WO S T → ℂ), Reads ψ θ hS hT ⊤ δ r G φ₁ ∧ φ = c' • heisO ψ S T (finPt hS hT r z) φ₁ := by
  set x := pt D (tor0 D ⊤ δ) δ z with hx
  have hw : wdPh D (tor0 D ⊤ δ) x ≠ 0 := by simp [wdPh, Formalism.MainNotions.StandardLatticesGL3.ee, Complex.exp_ne_zero]
  have hc' : c * wdPh D (tor0 D ⊤ δ) x ≠ 0 := mul_ne_zero hc hw
  have e : (c * wdPh D (tor0 D ⊤ δ) x)⁻¹ • c • Wd D (tor0 D ⊤ δ) x G = U D (tor0 D ⊤ δ) x G := by
    funext y
    simp only [Wd, Pi.smul_apply, smul_eq_mul]
    field_simp
  have h1 := hφ.smul (c * wdPh D (tor0 D ⊤ δ) x)⁻¹
  rw [e] at h1
  have h2 := GlobalTheory.T.heisenbergFinitePoint_reads_classicalTranslation ψ θ S T hS hT ⊤ δ r h _ _ h1 (-z)
  have e2 : pt D (tor0 D ⊤ δ) δ (-z) = -x := by
    funext τ i j
    simp [hx, pt, Formalism.MainNotions.TaylorLogMetric.embV, tor0]
  rw [e2, u_neg_u] at h2
  refine ⟨c * wdPh D (tor0 D ⊤ δ) x, _, h2, ?_⟩
  rw [heisO_heisO, finPt_neg, add_neg_cancel, heisO_zero, ← neg_neg (symplOH _ _ _ _), ← symplOH_skew]
  have : symplOH S T (-finPt hS hT r z) (finPt hS hT r z) = 0 := by
    have h3 := symplOH_add_left S T (-finPt hS hT r z) (finPt hS hT r z) (finPt hS hT r z)
    rw [neg_add_cancel, symplOH_self, add_zero, symplOH, symplO_zero_left, mul_zero] at h3
    exact h3.symm
  rw [this, neg_zero, AddChar.map_zero_eq_one, one_smul, smul_smul, mul_inv_cancel₀ hc', one_smul]

theorem heis_two_finPt (h : Setup ψ θ S T ⊤ δ r) {L L'} {G : VC D a d → ℂ} (hG : G ∈ Th D (tor0 D ⊤ δ) L L')
    {f : WO S T → ℂ} (hf : Reads ψ θ hS hT ⊤ δ r G f) {z : Matrix (Fin d) (Fin a) D.host.E} (hz : z ∈ YYl D L L') :
    heisO ψ S T (2 • finPt hS hT r z) f = f := by
  set x := pt D (tor0 D ⊤ δ) δ z with hx
  have hxm : x ∈ La D (tor0 D ⊤ δ) L L' :=
    AddSubgroup.subset_closure ⟨δ, AddSubgroup.subset_closure ⟨1, trivial, by simp⟩, z, hz, rfl⟩
  have h1 := (GlobalTheory.T.heisenbergFinitePoint_reads_classicalTranslation ψ θ S T hS hT ⊤ δ r h _ _ hf z).smul (al D (tor0 D ⊤ δ) x)
  have e : al D (tor0 D ⊤ δ) x • U D (tor0 D ⊤ δ) x G = G := funext fun y => hG.2 x hxm y
  rw [e] at h1
  have h2 := h1.unique hf
  have hal : al D (tor0 D ⊤ δ) x * al D (tor0 D ⊤ δ) x = 1 := by
    rw [al, ← mul_zpow]; simp
  have h3 : heisO ψ S T (finPt hS hT r z) f = al D (tor0 D ⊤ δ) x • f := by
    conv_rhs => rw [← h2]
    rw [smul_smul, hal, one_smul]
  have h4 := heisO_heisO ψ S T (finPt hS hT r z) (finPt hS hT r z) f
  rw [symplOH_self, AddChar.map_zero_eq_one, one_smul, ← two_nsmul, h3, heisO_smul, h3, smul_smul, hal, one_smul] at h4
  exact h4.symm

end Read

theorem heis_two_hatPt {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {r : D.host.E}
    {I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E} (hr : r ≠ 0) (hI : I ≠ 0) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    (h : ∀ z : Matrix (Fin T.rank) (Fin S.rank) D.host.E, (∀ i j, z i j ∈ I) →
      heisO ψ S T (2 • finPt (S := S) (T := T) rfl rfl r z) f = f) {u : WO S T} (hu : HatPt r I u) :
    heisO ψ S T (2 • u) f = f := by
  obtain ⟨U, hU, hUf⟩ := hf.level
  obtain ⟨z, hz, hk⟩ := GlobalTheory.T.dense_rationalHomPoints_idealCompletion S T r I hr hI U hU u hu
  set x := finPt (S := S) (T := T) rfl rfl r z with hx
  have hxi : x.map (infPart D) = 0 := GlobalTheory.VacUnique.finRat_inf S T _
  have hki : (u - x).map (infPart D) = 0 := by
    funext i j
    have a1 : infPart D (u i j) = 0 := congrFun (congrFun hu.1 i) j
    have a2 : infPart D (x i j) = 0 := congrFun (congrFun hxi i) j
    change infPart D (u i j - x i j) = 0
    rw [RingHom.map_sub, a1, a2, sub_self]
  have h1 := hUf _ hk hki
  have h2 : heisO ψ S T (2 • x) f = f := h z hz
  obtain ⟨k, rfl⟩ : ∃ k, u = x + k := ⟨u - x, (add_sub_cancel x u).symm⟩
  rw [add_sub_cancel_left] at h1
  have h3 := heisO_comm ψ S T (2 • x) k f
  rw [h1, h2, h1] at h3
  have h4 := heisO_heisO ψ S T k k f
  rw [h1, h1, symplOH_self, AddChar.map_zero_eq_one, one_smul] at h4
  have h5 := heisO_heisO ψ S T (2 • x) (k + k) f
  rw [← h4, h2, symplOH_add_right, symplOH_add_self, ← two_nsmul k, ← nsmul_add] at h5
  have h0 : ψ (symplO S T (2 • x) k) ≠ 0 := left_ne_zero_of_mul_eq_one (b := ψ (-symplO S T (2 • x) k))
    (by rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one])
  exact smul_right_injective _ h0 (h5.symm.trans h3)

theorem mem_YYl_skew {𝔪 : Ideal (𝓞 D.host.E)} {a d : ℕ} {z : Matrix (Fin d) (Fin a) D.host.E}
    (hz : ∀ i j, z i j ∈ skewId D 𝔪) : z ∈ YYl D (stdL D a) (skewLat D 𝔪 d) := by
  refine Submodule.subset_span ⟨1, ?_, _, Submodule.subset_span fun x hx i _ => ?_, (one_smul _ _).symm⟩
  · refine FractionalIdeal.one_mem_inv_coe_ideal fun h => ?_
    have h2 := D.host.𝔟_spec.2
    rw [h, Ideal.smul_bot, sup_bot_eq] at h2
    exact bot_ne_top h2
  · have : ∑ j, z i j * x j ∈ (skewId D 𝔪 : Submodule (𝓞 D.host.E) D.host.E) := sum_mem fun j _ => by
      obtain ⟨b, hb⟩ := Submodule.mem_one.1 (hx j trivial)
      rw [← hb, mul_comm, ← Algebra.smul_def]
      exact Submodule.smul_mem _ b (hz i j)
    exact this

theorem count_coe_eq_zero_iff {E : Type} [Field E] [NumberField E] {𝔞 : Ideal (𝓞 E)} (h : 𝔞 ≠ ⊥) (w : HeightOneSpectrum (𝓞 E)) :
    FractionalIdeal.count E w (𝔞 : FractionalIdeal (𝓞 E)⁰ E) = 0 ↔ ¬ 𝔞 ≤ w.asIdeal := by
  rw [FractionalIdeal.count_coe E w h, Nat.cast_eq_zero, ← Ideal.dvd_iff_le,
    ← Associates.count_ne_zero_iff_dvd h w.irreducible, not_not]

theorem place_facts {𝔪 : Ideal (𝓞 D.host.E)} {Sf : Finset (FinPl D)} (hG : GoodMod D 𝔪 Sf)
    {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : D.host.conj • 𝔪 ≤ w.asIdeal) (k : ℕ) :
    FractionalIdeal.count D.host.E w (skewId D 𝔪) = -FractionalIdeal.count D.host.E w
      ((D.host.conj • 𝔪 : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ∧
    1 ≤ FractionalIdeal.count D.host.E w ((D.host.conj • 𝔪 : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ∧
    w.valuation D.host.E (2 * (((D.host.QS * D.host.q) ^ k : ℕ) : D.host.E) * (((D.host.QS * D.host.q) ^ k : ℕ) : D.host.E)) = 1 := by
  have hc := GlobalTheory.FunObj.CosetTheta.conj_ne_bot hG.1
  have h0 : ¬ 𝔪 ≤ w.asIdeal := fun h => w.isPrime.ne_top (top_le_iff.1 (hG.2.1 ▸ sup_le h hw))
  refine ⟨?_, ?_, ?_⟩
  · rw [skewId, div_eq_mul_inv, FractionalIdeal.count_mul D.host.E w (FractionalIdeal.coeIdeal_ne_zero.2 hG.1)
      (inv_ne_zero (FractionalIdeal.coeIdeal_ne_zero.2 hc)), FractionalIdeal.count_inv,
      (count_coe_eq_zero_iff hG.1 w).2 h0, zero_add]
  · have h1 := FractionalIdeal.count_coe_nonneg D.host.E w (D.host.conj • 𝔪)
    have h2 := (count_coe_eq_zero_iff hc w).not.2 (not_not.2 hw)
    omega
  · have hq : ((D.host.QS * D.host.q : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal := by
      intro hq
      obtain ⟨x, hx, y, hy, e⟩ := Ideal.isCoprime_iff_exists.1 hG.2.2.1
      obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 hy
      have e2 := congrArg (MulSemiringAction.toRingHom _ (𝓞 D.host.E) D.host.conj) e
      rw [map_add (f := _), map_mul, map_natCast, map_one] at e2
      refine w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 ?_)
      rw [← e2]
      exact add_mem (hw (Ideal.smul_mem_pointwise_smul _ _ _ hx)) (Ideal.mul_mem_left _ _ hq)
    have h2 : ((2 : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal := fun h => hq (by
      obtain ⟨c, hc2⟩ := D.host.two_dvd_QS
      rw [hc2, mul_assoc, Nat.cast_mul]; exact Ideal.mul_mem_right _ _ h)
    have val : ∀ n : ℕ, (n : 𝓞 D.host.E) ∉ w.asIdeal → w.valuation D.host.E (n : D.host.E) = 1 := fun n hn => by
      rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := D.host.E), not_lt] at hn
      have := le_antisymm (w.valuation_le_one (K := D.host.E) (n : 𝓞 D.host.E)) hn
      simpa using this
    have v2 := val 2 h2
    rw [Nat.cast_ofNat] at v2
    rw [map_mul, map_mul, v2, Nat.cast_pow, map_pow, val _ hq, one_pow, one_mul, one_mul]

theorem stdLat_selfDual {V : HSp D} (hG : V.gram = 1) : IsSelfDualC V (stdLat V) := by
  have e : stdLat V = GlobalTheory.SW.stdL D.host.E V.rank := by
    ext x
    rw [GlobalTheory.SW.Base.mem_stdL]
    simp only [stdLat, Formalism.MainNotions.StandardLatticesGL3.stdL, Submodule.mem_pi, Set.mem_univ, true_imp_iff, Submodule.mem_one]
    exact forall_congr' fun i => ⟨fun ⟨y, hy⟩ => hy ▸ y.2, fun h => ⟨⟨x i, h⟩, rfl⟩⟩
  rw [e]; exact GlobalTheory.Ker.Base.selfDualC_stdL hG

theorem mem_of_char_eq {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {r : D.host.E} (hψ : IsStdChar D ψ (-1))
    (gS : S.gram = 1) (gT : T.gram = 1) (hr : r ≠ 0) {𝔪 : Ideal (𝓞 D.host.E)} {Sf : Finset (FinPl D)} (hG : GoodMod D 𝔪 Sf)
    {LB : Lat T} (hLB : IsSelfDualC T LB)
    (hY : ∀ z : Matrix (Fin T.rank) (Fin S.rank) D.host.E,
      finPt (S := S) (T := T) rfl rfl r z ∈ (latO S T (stdLat S) LB fun _ => True) → z ∈ YYl D (stdL D S.rank) (stdL D T.rank))
    {o : ℕ} (ho : o + S.rank ≤ T.rank) {g : GA D S} {y : Formalism.MainNotions.StandardLatticesGL3.GA D S.rank} (hg : GlobalTheory.BotFormula.IsFinPt S g y)
    (hg' : GlobalTheory.BotFormula.IsFinPt S g⁻¹ y⁻¹) (hy : g ∈ openOff S (stdLat S) Sf)
    (h : ∀ u : WO S T, HatPt r (skewId D 𝔪) u → HatPt r (skewId D 𝔪) (actO S T g 1 u) →
      ψ (symplO S T (2 • u) (finPt (S := S) (T := T) rfl rfl r (unitBlock D o S.rank T.rank))) =
        ψ (symplO S T (actO S T g 1 (2 • u)) (finPt (S := S) (T := T) rfl rfl r (unitBlock D o S.rank T.rank)))) :
    y ∈ intG D S.rank ∧ CongOne D 𝔪 y := by
  obtain ⟨k, hk⟩ := GlobalTheory.T.exists_pow_integral_completedHomLattice S T r LB hr hY
  have hH : ∀ i j, fe D (mt S g⁻¹ i j) = finMat y⁻¹ i j := fun i j => by
    obtain ⟨e, he⟩ := hg'.2
    exact he i j
  have hH1 : ∀ i j, fe D ((1 - mt S g⁻¹) i j) = (1 - finMat y⁻¹) i j := fun i j => by
    rw [Matrix.sub_apply, Matrix.sub_apply, RingHom.map_sub, hH, Matrix.one_apply, Matrix.one_apply]
    split_ifs
    · rw [RingHom.map_one]
    · rw [RingHom.map_zero]
  have key : ∀ (s : FA D) (i j : Fin S.rank), InHat (skewId D 𝔪) s → (∀ l, InHat (skewId D 𝔪) (s * finMat y⁻¹ i l)) →
      InHat 1 (algebraMap D.host.E (FA D)
        (2 * (((D.host.QS * D.host.q) ^ k : ℕ) : D.host.E) * (((D.host.QS * D.host.q) ^ k : ℕ) : D.host.E)) * (s * (1 - finMat y⁻¹) i j)) := by
    intro s i j hs hs'
    obtain ⟨σ, hσ, eσ⟩ := exists_fe (algebraMap D.host.E (FA D) r⁻¹ * s)
    have e1 : algebraMap D.host.E (FA D) r * fe D σ = s := by
      rw [eσ, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hr, map_one, one_mul]
    have h1 := GlobalTheory.T.integral_of_completedLattice_selfDual_rankOne ψ S T r LB _ hψ gS gT (stdLat_selfDual gS) hLB hr hk ⟨o + j, by omega⟩ j
      (2 * σ * (1 - mt S g⁻¹) i j) (by rw [RingHom.map_mul, RingHom.map_mul, hσ, mul_zero, zero_mul]) fun t ht ht' => by
        have e2 : algebraMap D.host.E (FA D) r * fe D (t * σ) = fe D t * s := by
          rw [RingHom.map_mul, mul_left_comm, e1]
        have h2 := GlobalTheory.T.addChar_trace_unitBlock_trivial_of_moves ψ S T r (skewId D 𝔪) o g gS gT ho h (t * σ) i j
          (by rw [RingHom.map_mul, ht, zero_mul]) (by rw [e2]; exact ht'.mul_left hs)
          fun l => by rw [e2, hH, mul_assoc]; exact ht'.mul_left (hs' l)
        rw [← h2]
        congr 4
        ring
    convert h1 using 1
    rw [(fe D).map_mul, (fe D).map_mul, hH1, ← e1, ← one_add_one_eq_two (R := AE D), (fe D).map_add, (fe D).map_one,
      ← one_add_one_eq_two (R := D.host.E)]
    simp only [RingHom.map_mul, RingHom.map_add, RingHom.map_one]
    ring
  have hc := GlobalTheory.T.unitaryFinitePoint_congr_one_of_inv_conj_congr (GlobalTheory.T.conjugatePlace_valuation_count_under D) 𝔪 Sf hG y (GlobalTheory.T.valued_finiteUnitary_le_one_off_openSubset S g y Sf gS hg hy) fun w hw => by
    obtain ⟨h1, h2, h3⟩ := place_facts hG hw k
    exact GlobalTheory.T.valued_one_sub_le_of_moves_idealCompletion (skewId D 𝔪) w _ _ (finMat y⁻¹) h3 h1 h2 key
  refine ⟨(GlobalTheory.NormSum.mem_intG y).2 fun i j => ⟨?_, ?_⟩, fun i j => GlobalTheory.T.mem_idealIntegralFiniteAdeles_of_memCompletion 𝔪 hG.1 _ ?_⟩
  · exact (GlobalTheory.ZeroAtPlaces.mem_OhE_iff _).2 fun w =>
      (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 ((inHat_one_iff _).1 (hc i j).1 w)
  · exact (GlobalTheory.ZeroAtPlaces.mem_OhE_iff _).2 fun w =>
      (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 ((inHat_one_iff _).1 (hc i j).2.1 w)
  · convert (hc i j).2.2 using 1
    rw [Matrix.sub_apply, Matrix.sub_apply, map_sub, Matrix.one_apply, Matrix.one_apply]
    split_ifs
    · rw [map_one]; rfl
    · rw [map_zero]; rfl

theorem actO_two {S T : HSp D} (g : GA D S) (h : GA D T) (u : WO S T) : actO S T g h (2 • u) = 2 • actO S T g h u := by
  simp only [actO, two_nsmul, Matrix.mul_add, Matrix.add_mul]

theorem ip_eq_zero {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d)
    {δ : ℂ} {r : D.host.E} (h : Setup ψ θ S T ⊤ δ r) {χS χT : (AE D)ˣ →* Circle} {om : GlobalTheory.Core.Rk.IP.WRep S T}
    (hω : IsWeilDatumO ψ S T χS χT om) {e0 : VC D a d → ℂ} (he0 : e0 ∈ Th D (tor0 D ⊤ δ) (stdL D a) (stdL D d))
    {𝔪 : Ideal (𝓞 D.host.E)} {Sf : Finset (FinPl D)} (hG : GoodMod D 𝔪 Sf) {LB : Lat T} (hLB : IsSelfDualC T LB)
    (hY : ∀ z : Matrix (Fin d) (Fin a) D.host.E,
      finPt hS hT r z ∈ (latO S T (stdLat S) LB fun _ => True) → z ∈ YYl D (stdL D a) (stdL D d))
    {o : ℕ} (ho : o + a ≤ d) {c : ℂ} (hc : c ≠ 0) {φ : WO S T → ℂ}
    (hφ : Reads ψ θ hS hT ⊤ δ r (c • Wd D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ (unitBlock D o a d))
      (Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)) e0)) φ)
    {ν : Measure (WO S T)} {𝓕 : Set (WO S T)} (hν : IsCovolOne (ratL T S) ν 𝓕)
    {g : GA D S} {y : Formalism.MainNotions.StandardLatticesGL3.GA D a} (hg : GlobalTheory.BotFormula.IsFinPt S g y)
    (hg' : GlobalTheory.BotFormula.IsFinPt S g⁻¹ y⁻¹) (hy : g ∈ openOff S (stdLat S) Sf) (hn : ¬ (y ∈ intG D a ∧ CongOne D 𝔪 y)) :
    ip S T ν 𝓕 (om (g, 1) φ) φ = 0 := by
  subst hS hT
  have hr : r ≠ 0 := h.scale.ne_zero top_ne_bot
  obtain ⟨c', φ₁, hφ₁, e⟩ := exists_read_of_wd h hc _ hφ
  have hI : skewId D 𝔪 ≠ 0 := div_ne_zero (FractionalIdeal.coeIdeal_ne_zero.2 hG.1)
    (FractionalIdeal.coeIdeal_ne_zero.2 (GlobalTheory.FunObj.CosetTheta.conj_ne_bot hG.1))
  have hth := GlobalTheory.SkewTheta.iop_mem_thSp D δ h.crv e0 he0 𝔪 (GlobalTheory.SkewLatSelfDual.skewLat_SD hG.1 _)
  have eig : ∀ u : WO S T, HatPt r (skewId D 𝔪) u → heisO ψ S T (2 • u) φ =
      ψ (symplO S T (2 • u) (finPt (S := S) (T := T) rfl rfl r (unitBlock D o S.rank T.rank))) • φ := fun u hu => by
    have h1 := heis_two_hatPt hr hI hφ₁.1 (fun z hz => heis_two_finPt h hth hφ₁ (mem_YYl_skew hz)) hu
    rw [e, heisO_smul, heisO_comm, h1, smul_comm]
  by_contra hne
  refine hn (mem_of_char_eq h.std h.gS h.gT hr hG hLB hY ho hg hg' hy fun u hu hu' => ?_)
  by_contra hd
  refine hne (ip_eq_zero_of_heis_eigen h.std hν (hω.om_pres _ _ hφ.1) hφ.1 (actO S T g 1 (2 • u)) ?_ ?_ (h.std.1.2.1 _) hd)
  · rw [← hω.om_heis _ _ _ _ hφ.1, eig u hu, map_smul]
  · rw [actO_two]; exact eig _ hu'

end GlobalTheory.CosetOrth

theorem GlobalTheory.NormRatio.ip_om_cosetVec_eq_zero : ∀ {D : D7} {δ t0 : ℂ} {Q : ℕ} (P : Pair D ⊤ δ t0 Q) (X : Data P) (r : D.host.E), IsExact P X r →
  ∀ (𝔪 : Ideal (𝓞 D.host.E)) (Sf : Finset (FinPl D)) (o : ℕ), GoodMod D 𝔪 Sf →
  ∀ LB : Lat X.B, IsSelfDualC X.B LB →
    (∀ z : Matrix (Fin P.d) (Fin P.a) D.host.E, z ∈ Formalism.MainNotions.TaylorLogMetric.YYl D (Formalism.MainNotions.StandardLatticesGL3.stdL D P.a) (Formalism.MainNotions.StandardLatticesGL3.stdL D P.d) ↔
      finPt X.rkA X.rkB r z ∈ latO X.A X.B (stdLat X.A) LB fun _ => True) →
  ∀ f₀ φ, Reads X.ψ X.θ X.rkA X.rkB ⊤ δ r P.e0 f₀ → IsSphOff X.ψ X.A X.B (stdLat X.A) LB ∅ f₀ →
    Reads X.ψ X.θ X.rkA X.rkB ⊤ δ r (cosetVec P 𝔪 o) φ →
  o + P.a ≤ P.d → ∀ (ν : Measure (WO X.A X.B)) (𝓕 : Set (WO X.A X.B)), IsCovolOne (ratL X.B X.A) ν 𝓕 →
  ∀ y, X.ιA y ∈ openOff X.A (stdLat X.A) Sf → ¬ (y ∈ intG D P.a ∧ CongOne D 𝔪 y) →
    ip X.A X.B ν 𝓕 (X.om (X.ιA y, 1) φ) φ = 0 := by
  intro D δ t0 Q P X r hX 𝔪 Sf o hG LB hLB hY f₀ φ _ _ hφ hoa ν 𝓕 hcov y hy hn
  have hc : ((Real.sqrt ((Ideal.absNorm 𝔪 : ℝ) ^ (P.a * P.d)) : ℂ))⁻¹ ≠ 0 := by
    have : (0 : ℝ) < Ideal.absNorm 𝔪 := by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.2 hG.1)
    exact inv_ne_zero (Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 (pow_pos this _)).ne')
  have hg' := hX.std.ptA y⁻¹
  rw [map_inv] at hg'
  exact GlobalTheory.CosetOrth.ip_eq_zero X.rkA X.rkB hX.setup hX.weil P.vac.1 hG hLB (fun z => (hY z).2) hoa hc hφ hcov
    (hX.std.ptA y) hg' hy hn
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetVectorOrthogonalTranslateFinitePointStatement
open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop (modT)
open GlobalTheory.BottomIPData (sfB)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat IsFockVec IsSphOff volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip)
open GlobalTheory.Core.Rk.IP (openOff integrand wcoef)
open GlobalTheory.StdLoc (glVol blockIdx)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.NormRatio

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cosetVector_orthogonal_translate_finite_point : ∀ {D : D7} {δ t0 : ℂ} {Q : ℕ} (P : Pair D ⊤ δ t0 Q) (X : Data P) (r : D.host.E), IsExact P X r →
  ∀ (𝔪 : Ideal (𝓞 D.host.E)) (Sf : Finset (FinPl D)) (o : ℕ), GoodMod D 𝔪 Sf →
  ∀ LB : Lat X.B, IsSelfDualC X.B LB →
    (∀ z : Matrix (Fin P.d) (Fin P.a) D.host.E, z ∈ Formalism.MainNotions.TaylorLogMetric.YYl D (Formalism.MainNotions.StandardLatticesGL3.stdL D P.a) (Formalism.MainNotions.StandardLatticesGL3.stdL D P.d) ↔
      finPt X.rkA X.rkB r z ∈ latO X.A X.B (stdLat X.A) LB fun _ => True) →
  ∀ f₀ φ, Reads X.ψ X.θ X.rkA X.rkB ⊤ δ r P.e0 f₀ → IsSphOff X.ψ X.A X.B (stdLat X.A) LB ∅ f₀ →
    Reads X.ψ X.θ X.rkA X.rkB ⊤ δ r (cosetVec P 𝔪 o) φ →
  o + P.a ≤ P.d → ∀ (ν : Measure (WO X.A X.B)) (𝓕 : Set (WO X.A X.B)), IsCovolOne (ratL X.B X.A) ν 𝓕 →
  ∀ y, X.ιA y ∈ openOff X.A (stdLat X.A) Sf → ¬ (y ∈ intG D P.a ∧ CongOne D 𝔪 y) →
    ip X.A X.B ν 𝓕 (X.om (X.ιA y, 1) φ) φ = 0 := by
  first | exact @GlobalTheory.NormRatio.ip_om_cosetVec_eq_zero | exact GlobalTheory.NormRatio.ip_om_cosetVec_eq_zero | (intros; apply GlobalTheory.NormRatio.ip_om_cosetVec_eq_zero <;> assumption)
end
