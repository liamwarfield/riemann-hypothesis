module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniformisationTorusMonoAndFactor
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClassifiedTorusTorsionPointEqUniformisationTorus

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenKerNormOneFiniteAdeleDetClass
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenKerNormOneFiniteAdeleDetClass
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.FullDt ReciprocityTheory.Neutral.Bridge.HCFR Neutral.B1
open scoped TensorProduct Topology

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.FullDt

attribute [local instance] rlt_top rlt_topRing adeles_t2Space

variable {R : Ranks} {H : Formalism.BasicNotions.Host R} {SG SQ : Finset (HeightOneSpectrum (𝓞 H.E))}

theorem lift_mem_KDq (hl : LevOk H SG SQ) (x : Formalism.L2.Herm.unitaryOneFiniteAdeles (host_cmData R H)) (b : GlobalTheory.Mem.Chr.Ideles H.E)
    (hb : IsDetLift (host_cmData R H) x.1 b) (c : 𝓞 H.E) (hc : ∀ P ∈ uSG SG SQ, c ∈ P.asIdeal) (s : AfE H.F H.E)
    (hs : s ∈ RInt H.F H.E)
    (hx : ((x.1 : GL (Fin 1) (AfE H.F H.E)) : Matrix (Fin 1) (Fin 1) (AfE H.F H.E)) 0 0 =
      1 + iA H.F H.E (algebraMap (𝓞 H.E) H.E c) * s) : b ∈ KDq H SQ := by
  have hd : ((x.1 : GL (Fin 1) (AfE H.F H.E)) : Matrix (Fin 1) (Fin 1) (AfE H.F H.E)).det =
      1 + iA H.F H.E (algebraMap (𝓞 H.E) H.E c) * s := by
    rw [Matrix.det_fin_one, hx]
  have hdd := DetLift.det_mul_conj_det _ _ x.2
  set d := ((x.1 : GL (Fin 1) (AfE H.F H.E)) : Matrix (Fin 1) (Fin 1) (AfE H.F H.E)).det with hdef
  have hci : ∀ w : HeightOneSpectrum (𝓞 H.E), adAt H.F w (iA H.F H.E (algebraMap (𝓞 H.E) H.E c)) =
      algebraMap H.E _ (algebraMap (𝓞 H.E) H.E c) := fun w => adAt_inclE H.F w _
  have hsv : ∀ w : HeightOneSpectrum (𝓞 H.E), Valued.v (adAt H.F w s) ≤ 1 := (mem_rInt_iff H.F H.E s).1 hs
  have hle : ∀ w : HeightOneSpectrum (𝓞 H.E), Valued.v (adAt H.F w d) ≤ 1 := fun w => by
    rw [hd, map_add (f := _), map_one, map_mul, hci]
    refine Valuation.map_add_le _ (by rw [map_one]) ?_
    rw [map_mul, valued_algebraMap]
    exact mul_le_one' (HeightOneSpectrum.valuation_le_one _ _) (hsv w)
  have hv1 : ∀ w : HeightOneSpectrum (𝓞 H.E), Valued.v (adAt H.F w d) = 1 := fun w => by
    have e := congrArg (fun z => Valued.v (adAt H.F w z)) hdd
    simp only [map_mul, map_one] at e
    refine le_antisymm (hle w) ?_
    have e' : Valued.v (adAt H.F w d) * Valued.v (adAt H.F (conjPrime₂ w) d) = 1 := by
      rw [← valued_sigR (host_cmData R H) w d]
      exact e
    calc (1 : _) = Valued.v (adAt H.F w d) * Valued.v (adAt H.F (conjPrime₂ w) d) := e'.symm
      _ ≤ _ := mul_le_of_le_one_right' (hle _)
  have hcomp := fun w => DetSpec.compAt_eq hb w
  refine mem_KDq_of_conj hl b (fun w => ?_) fun P hP => ?_
  · rw [hcomp w, map_mul, hv1 w, one_mul, valued_sigR, adAt_finAf]
  · have h0 : adAt H.F P (Formalism.UG.sigR (host_cmData R H).sig _ (finAf H.F H.E b : AfE H.F H.E)) ≠ 0 := by
      rw [← (Valued.v : Valuation (P.adicCompletion H.E) _).ne_zero_iff, valued_sigR, adAt_finAf]
      exact DetSpec.val_compAt_ne _ _
    rw [hcomp P, mul_div_cancel_right₀ _ h0]
    show Valued.v (adAt H.F P d - 1) < 1
    rw [hd, map_add (f := _), map_one, add_sub_cancel_left, map_mul, hci, map_mul,
      valued_algebraMap]
    have hlt : P.valuation H.E (algebraMap (𝓞 H.E) H.E c) < 1 :=
      (HeightOneSpectrum.valuation_lt_one_iff_mem P c).2 (hc P hP)
    exact (mul_le_of_le_one_right' (hsv P)).trans_lt hlt

theorem isOpen_ker_u1Dt : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (SG SQ : Finset (HeightOneSpectrum (𝓞 H.E))), LevOk H SG SQ → letI := Formalism.BasicNotions.tensTopL (F := H.F) (E := H.E) (Formalism.L2.Herm.Af H.F); IsOpen {x : Formalism.L2.Herm.unitaryOneFiniteAdeles (host_cmData R H) | u1Dt H SQ x = 1} := by
  intro R H SG SQ hl
  classical
  obtain ⟨a, ha0, ha⟩ := rlt_exists_a (uSG SG SQ)
  set c : AfE H.F H.E := iA H.F H.E (algebraMap (𝓞 H.E) H.E a)⁻¹ with hc'
  have hca : iA H.F H.E (algebraMap (𝓞 H.E) H.E a) * c = 1 := by
    rw [hc', ← map_mul, mul_inv_cancel₀ (by simpa using ha0), map_one]
  let W : Set (GL (Fin 1) (AfE H.F H.E)) :=
    {u | c * ((u : Matrix (Fin 1) (Fin 1) (AfE H.F H.E)) 0 0 - 1) ∈ Formalism.L2.Herm.intAf H.F H.E}
  have hWo : IsOpen W := by
    exact rlt_isOpen_intAf.preimage
      (continuous_const.mul ((Units.continuous_val.matrix_elem 0 0).sub continuous_const))
  have hW1 : (1 : GL (Fin 1) (AfE H.F H.E)) ∈ W := by
    show c * (((1 : GL (Fin 1) (AfE H.F H.E)) : Matrix (Fin 1) (Fin 1) (AfE H.F H.E)) 0 0 - 1) ∈ Formalism.L2.Herm.intAf H.F H.E
    simp
  have hsub : ∀ x : Formalism.L2.Herm.unitaryOneFiniteAdeles (host_cmData R H), x.1 ∈ W → x ∈ (u1Dt H SQ).ker := by
    intro x hx
    obtain ⟨b, hb⟩ := exists_lift H x
    rw [MonoidHom.mem_ker, normOneFiniteAdeleDetClass_of_isDetLift H SQ x b hb]
    refine (QuotientGroup.eq_one_iff b).2 (lift_mem_KDq hl x b hb a ha _ hx ?_)
    rw [← mul_assoc, hca, one_mul]
    ring
  have hnh : (((u1Dt H SQ).ker : Subgroup _) : Set (Formalism.L2.Herm.unitaryOneFiniteAdeles (host_cmData R H))) ∈ 𝓝 (1 : Formalism.L2.Herm.unitaryOneFiniteAdeles (host_cmData R H)) := by
    have hpre : (fun x : Formalism.L2.Herm.unitaryOneFiniteAdeles (host_cmData R H) => x.1) ⁻¹' W ∈ 𝓝 (1 : Formalism.L2.Herm.unitaryOneFiniteAdeles (host_cmData R H)) :=
      (hWo.preimage continuous_subtype_val).mem_nhds hW1
    exact Filter.mem_of_superset hpre fun x hx => hsub x hx
  exact Subgroup.isOpen_of_mem_nhds _ hnh

end GlobalTheory.Mem.Col2.FullDt

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenKerNormOneFiniteAdeleDetClassStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.FullDt ReciprocityTheory.Neutral.Bridge.HCFR Neutral.B1
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isOpen_ker_normOneFiniteAdeleDetClass : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (SG SQ : Finset (HeightOneSpectrum (𝓞 H.E))), LevOk H SG SQ → letI := Formalism.BasicNotions.tensTopL (F := H.F) (E := H.E) (Formalism.L2.Herm.Af H.F); IsOpen {x : Formalism.L2.Herm.unitaryOneFiniteAdeles (host_cmData R H) | u1Dt H SQ x = 1} := by
  first | exact @GlobalTheory.Mem.Col2.FullDt.isOpen_ker_u1Dt | exact GlobalTheory.Mem.Col2.FullDt.isOpen_ker_u1Dt | (intros; apply GlobalTheory.Mem.Col2.FullDt.isOpen_ker_u1Dt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RationalNormOneClassEqFiniteAdelicDetClass
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RationalNormOneClassEqFiniteAdelicDetClass
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.FullDt ReciprocityTheory.Neutral.Bridge.HCFR Neutral.B1
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.FullDt

theorem e1Q_eq_u1Dt_of_det_eq : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (SQ : Finset (HeightOneSpectrum (𝓞 H.E))) (z : unitary H.E) (x : Formalism.L2.Herm.unitaryOneFiniteAdeles (host_cmData R H)), Matrix.GeneralLinearGroup.det x.1 = Formalism.L2.Herm.unitaryOneRationalAdele H.F z → e1Q H SQ z = u1Dt H SQ x := by
  intro R H SQ z x hx
  obtain ⟨k, hk⟩ := exists_eq_div_conj H z
  rw [← isUnitaryPointsMap_unitaryRationalPointsFiner H SQ k z hk]
  symm
  apply normOneFiniteAdeleDetClass_of_isDetLift
  unfold IsDetLift
  rw [hx]
  have hf : finAf H.F H.E (Neutral.B1.diagUnits H.E k) = Units.map (Formalism.UG.inclE (F := H.F) (FiniteAdeleRing (𝓞 H.F) H.F)).toMonoidHom k := by
    apply Units.ext
    apply (afIso H.F H.E).injective
    rw [afIso_finAf]
    show _ = afIso H.F H.E ((k : H.E) ⊗ₜ[H.F] 1)
    rw [afIso_tmul_one]
    rfl
  rw [hf]
  have key : Formalism.L2.Herm.unitaryOneRationalAdele H.F z * conjId (host_cmData R H).sig
      (Units.map (Formalism.UG.inclE (F := H.F) (FiniteAdeleRing (𝓞 H.F) H.F)).toMonoidHom k) =
      Units.map (Formalism.UG.inclE (F := H.F) (FiniteAdeleRing (𝓞 H.F) H.F)).toMonoidHom k := by
    apply Units.ext
    show Formalism.UG.inclE (F := H.F) (FiniteAdeleRing (𝓞 H.F) H.F) (z : H.E) *
      Formalism.UG.sigR (host_cmData R H).sig _ (Formalism.UG.inclE (F := H.F) (FiniteAdeleRing (𝓞 H.F) H.F) (k : H.E)) =
      Formalism.UG.inclE (F := H.F) (FiniteAdeleRing (𝓞 H.F) H.F) (k : H.E)
    rw [sigR_inclE, ← map_mul, bridge_star_holds R H, hk]
  rw [h90, MonoidHom.div_apply, MonoidHom.id_apply, div_eq_iff_eq_mul]
  exact key.symm

end GlobalTheory.Mem.Col2.FullDt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RationalNormOneClassEqFiniteAdelicDetClassStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.FullDt ReciprocityTheory.Neutral.Bridge.HCFR Neutral.B1
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalNormOne_class_eq_finiteAdelic_det_class : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (SQ : Finset (HeightOneSpectrum (𝓞 H.E))) (z : unitary H.E) (x : Formalism.L2.Herm.unitaryOneFiniteAdeles (host_cmData R H)), Matrix.GeneralLinearGroup.det x.1 = Formalism.L2.Herm.unitaryOneRationalAdele H.F z → e1Q H SQ z = u1Dt H SQ x := by
  first | exact @GlobalTheory.Mem.Col2.FullDt.e1Q_eq_u1Dt_of_det_eq | exact GlobalTheory.Mem.Col2.FullDt.e1Q_eq_u1Dt_of_det_eq | (intros; apply GlobalTheory.Mem.Col2.FullDt.e1Q_eq_u1Dt_of_det_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemNormOneIntegralIffConjugateValuationsEq
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemNormOneIntegralIffConjugateValuationsEq
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.FullDt ReciprocityTheory.Neutral.Bridge.HCFR Neutral.B1
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.Mem.Col2.FullDt
section Gen
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
  (hc : Formalism.BasicNotions.CMData F E)

theorem mem_u1int_iff_entry (u : GL (Fin 1) (AfE F E)) :
    u ∈ Formalism.L2.Herm.IntegralUnitGroup hc ↔ u ∈ Formalism.L2.Herm.unitaryOneFiniteAdeles hc ∧ ∀ y : Fin 1 → AfE F E,
      (y 0 ∈ RInt F E ↔ (u : Matrix (Fin 1) (Fin 1) (AfE F E)) 0 0 * y 0 ∈ RInt F E) := by
  have hl : ∀ y : Fin 1 → AfE F E, y ∈ (Formalism.UG.stdLat (n := Fin 1) ↥(RInt F E) : Submodule ↥(RInt F E) (Fin 1 → AfE F E)) ↔
      y 0 ∈ RInt F E := by
    intro y
    simp only [Formalism.UG.stdLat, Submodule.mem_pi, Set.mem_univ, true_implies, Fin.forall_fin_one]
    exact ⟨fun ⟨r, hr⟩ => hr ▸ r.2, fun h => ⟨⟨_, h⟩, rfl⟩⟩
  show u ∈ Formalism.UG.UJ _ _ ⊓ Formalism.UG.stabGL _ ↔ _
  rw [Subgroup.mem_inf]
  refine and_congr Iff.rfl ?_
  show (∀ y, _ ↔ _) ↔ _
  refine forall_congr' fun y => ?_
  rw [hl, hl]
  simp [Matrix.mulVec, dotProduct]


omit [StarRing E] in
theorem rInt_mul_iff {c d : AfE F E} (hcd : c * d = 1) :
    (∀ y : AfE F E, y ∈ RInt F E ↔ c * y ∈ RInt F E) ↔ ∀ P : HeightOneSpectrum (𝓞 E), Valued.v (adAt F P c) = 1 := by
  constructor
  · intro h P
    have hc1 : c ∈ RInt F E := by simpa using (h 1).1 (one_mem _)
    have hd1 : d ∈ RInt F E := (h d).2 (by rw [hcd]; exact one_mem _)
    have a1 := (mem_rInt_iff F E c).1 hc1 P
    have a2 := (mem_rInt_iff F E d).1 hd1 P
    rw [← adAt_apply] at a1 a2
    have e : Valued.v (adAt F P c) * Valued.v (adAt F P d) = 1 := by rw [← map_mul, ← map_mul, hcd, map_one, map_one]
    refine le_antisymm a1 ?_
    rw [← e]
    exact mul_le_of_le_one_right' a2
  · intro h y
    rw [mem_rInt_iff, mem_rInt_iff]
    refine forall_congr' fun P => ?_
    rw [← adAt_apply, ← adAt_apply, map_mul, map_mul, h P, one_mul]
end Gen

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem mem_u1int_iff_val : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (x : Formalism.L2.Herm.unitaryOneFiniteAdeles (host_cmData R H)) (a : GlobalTheory.Mem.Chr.Ideles H.E),
    IsDetLift (host_cmData R H) x.1 a → ((x.1 ∈ Formalism.L2.Herm.IntegralUnitGroup (host_cmData R H)) ↔
      ∀ w : HeightOneSpectrum (𝓞 H.E), Valued.v (compAt w a) = Valued.v (compAt (conjPrime₂ w) a)) := by
  intro R H x a ha
  have hcd : ((x.1 : Matrix (Fin 1) (Fin 1) (AfE H.F H.E)) 0 0) * ((x.1⁻¹ : GL (Fin 1) (AfE H.F H.E)) : Matrix (Fin 1) (Fin 1) (AfE H.F H.E)) 0 0 = 1 := by
    have := congrArg (fun M : Matrix (Fin 1) (Fin 1) (AfE H.F H.E) => M 0 0) (Units.mul_inv x.1)
    simpa [Matrix.mul_apply] using this
  rw [mem_u1int_iff_entry, and_iff_right x.2]
  have e1 : (∀ y : Fin 1 → AfE H.F H.E, (y 0 ∈ RInt H.F H.E ↔ (x.1 : Matrix (Fin 1) (Fin 1) (AfE H.F H.E)) 0 0 * y 0 ∈ RInt H.F H.E)) ↔
      ∀ y : AfE H.F H.E, (y ∈ RInt H.F H.E ↔ (x.1 : Matrix (Fin 1) (Fin 1) (AfE H.F H.E)) 0 0 * y ∈ RInt H.F H.E) :=
    ⟨fun h y => h fun _ => y, fun h y => h (y 0)⟩
  rw [e1, rInt_mul_iff hcd]
  refine forall_congr' fun w => ?_
  have k := congrArg Valued.v (DetSpec.compAt_eq ha w)
  rw [map_mul, valued_sigR, adAt_finAf, Matrix.det_fin_one] at k
  rw [k]
  have h0 := DetSpec.val_compAt_ne (conjPrime₂ w) a
  constructor
  · intro h; rw [h, one_mul]
  · intro h
    exact (mul_eq_right₀ h0).1 h
end GlobalTheory.Mem.Col2.FullDt

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemNormOneIntegralIffConjugateValuationsEqStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.FullDt ReciprocityTheory.Neutral.Bridge.HCFR Neutral.B1
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_normOneIntegral_iff_conjugate_valuations_eq : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (x : Formalism.L2.Herm.unitaryOneFiniteAdeles (host_cmData R H)) (a : GlobalTheory.Mem.Chr.Ideles H.E), IsDetLift (host_cmData R H) x.1 a → ((x.1 ∈ Formalism.L2.Herm.IntegralUnitGroup (host_cmData R H)) ↔ ∀ w : HeightOneSpectrum (𝓞 H.E), Valued.v (compAt w a) = Valued.v (compAt (conjPrime₂ w) a)) := by
  first | exact @GlobalTheory.Mem.Col2.FullDt.mem_u1int_iff_val | exact GlobalTheory.Mem.Col2.FullDt.mem_u1int_iff_val | (intros; apply GlobalTheory.Mem.Col2.FullDt.mem_u1int_iff_val <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFullHermitianColumnsTrueColumns
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.FullDt ReciprocityTheory.Neutral.Bridge.HCFR Neutral.B1
open scoped TensorProduct

namespace GlobalTheory.Mem.Col2.FullDt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {R : Ranks} (H : Formalism.BasicNotions.Host R) (SQ : Finset (HeightOneSpectrum (𝓞 H.E)))

theorem mem_integralNormOne_of_normOneDetClass_eq_one (x : Formalism.L2.Herm.unitaryOneFiniteAdeles (host_cmData R H)) (h : u1Dt H SQ x = 1) :
    x.1 ∈ Formalism.L2.Herm.IntegralUnitGroup (host_cmData R H) := by
  obtain ⟨a, ha⟩ := exists_lift H x
  have e : (QuotientGroup.mk a : DtQ H SQ) = 1 := (normOneFiniteAdeleDetClass_of_isDetLift H SQ x a ha).symm.trans h
  have ha' : a ∈ KDq H SQ := (QuotientGroup.eq_one_iff a).1 e
  refine (GlobalTheory.T.mem_normOneIntegral_iff_conjugate_valuations_eq R H x a ha).2 fun w => ?_
  exact (GlobalTheory.Mem.Chr.mem_KD_sup_unitIdl_iff R H a).1 (Subgroup.mem_sup_left (KDq_le_KD H SQ ha')) w (conjPrime₂ w)
    ((isConjPl_iff H w _).2 rfl)

theorem unitIdeleImage_eq_map_integralNormOne : UOQ H SQ = ((Formalism.L2.Herm.IntegralUnitGroup (host_cmData R H)).subgroupOf (Formalism.L2.Herm.unitaryOneFiniteAdeles (host_cmData R H))).map (u1Dt H SQ) := by
  ext t
  constructor
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨x, hx⟩ := exists_of_idele H a
    refine ⟨x, ?_, normOneFiniteAdeleDetClass_of_isDetLift H SQ x a hx⟩
    refine (GlobalTheory.T.mem_normOneIntegral_iff_conjugate_valuations_eq R H x a hx).2 fun w => ?_
    exact (ha w).trans (ha (conjPrime₂ w)).symm
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨a, ha⟩ := exists_lift H x
    rw [normOneFiniteAdeleDetClass_of_isDetLift H SQ x a ha, mk_mem_UOQ, KDq_sup_unitIdl]
    refine (GlobalTheory.Mem.Chr.mem_KD_sup_unitIdl_iff R H a).2 fun w w' hw => ?_
    rw [(isConjPl_iff H w w').1 hw]
    exact (GlobalTheory.T.mem_normOneIntegral_iff_conjugate_valuations_eq R H x a ha).1 hx w

end Gen

section Main

open Formalism.UG Formalism.L2.Forms GlobalTheory.Mem.Col2.TC
attribute [local instance] GlobalTheory.Mem.Col2.starE

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X)

theorem detPt_of_reads (hI : I.Ok) (u : B.Word) (i : ℕ) {Ch : Type} {chOf : (I.stp u I.mu0 i).Cl → Ch}
    {Lb : Ch → Submodule (𝓞 B.host.E) (Fin (B.R.N i) → B.host.E)} {U : Ch → Subgroup (GA B (B.R.N i))} {chi : ∀ β, U β →* ℂˣ}
    {y : (I.stp u I.mu0 i).Cl → GA B (B.R.N i)} {st : ∀ c, (I.stp u I.mu0 i).Stab c → GL (Fin (B.R.N i)) B.host.E}
    {k : Ch → GA B (B.R.N i)} (hR : I.Reads u I.mu0 i chOf Lb U chi y st k) (c : (I.stp u I.mu0 i).Cl)
    (x : Formalism.L2.Herm.unitaryOneFiniteAdeles (host_cmData B.R B.host))
    (hx : Matrix.GeneralLinearGroup.det x.1 = Matrix.GeneralLinearGroup.det (y c)) :
    detPt B.host I.SQ ((I.stp u I.mu0 i).rep c).1.1 = u1Dt B.host I.SQ x := by
  obtain ⟨p, hp, hN⟩ := hR.k_std (chOf c)
  refine GlobalTheory.T.pointDeterminant_eq_normOneClass_of_level B.R B.host _ _ _ _ I.SQ _ (y c) (k (chOf c)) x (GlobalTheory.Mem.LevTwist.levOk_twists B X I hI).1 (hR.pt c) hp.uni
    (hN ▸ hp.lat) (fun P hP => ?_) hx
  refine hR.k_off _ _ (GlobalTheory.T.memberLevelPrime_not_mem_under_levelPrimes B X I hI u P hP) ?_ (Or.inl rfl)
  rintro ⟨Q, hQ, -⟩
  rw [GlobalTheory.T.q_mu0_eq_empty B X I] at hQ
  exact absurd hQ (Finset.notMem_empty Q)

theorem det_reGL {a b : ℕ} (h : a = b) {A : Type} [CommRing A] (g : GL (Fin a) A) :
    Matrix.GeneralLinearGroup.det (reGL h A g) = Matrix.GeneralLinearGroup.det g := by
  subst h
  refine Units.ext ?_
  simp [reGL, Matrix.GeneralLinearGroup.det]

variable (l : I.Laws) (Z : TC.Later B (I.cols l)) (C : ColsTiedSym (I.rec7 l Z))


include I in
theorem det_normOne_classStepZero_trueColumns (hI : I.Ok) (hS : I.StdC l Z C) (u : B.Word) (c : ((I.rec7 l Z).mem u).C.cls 0)
    (x : Formalism.L2.Herm.unitaryOneFiniteAdeles (host_cmData B.R B.host))
    (hx : Matrix.GeneralLinearGroup.det x.1 = Matrix.GeneralLinearGroup.det ((C.herm.base.lev0 u).y c).1) :
    (I.rec7 l Z).detCls u 0 c = u1Dt B.host I.SQ x := by
  obtain ⟨k, hk⟩ := (hS u).ends 0 (Nat.zero_le _) (Or.inl rfl)
  refine detPt_of_reads I hI u 0 hk c x ?_
  have e := (C.car0 u).y_eq c
  rw [hx]
  exact (e ▸ det_reGL _ _).symm


include I in
theorem detI_std (hI : I.Ok) (hS : I.StdC l Z C) (u : B.Word) (i : ℕ) (h1 : 1 ≤ i) (hm : i ≤ B.R.m)
    (c : ((I.rec7 l Z).mem u).C.cls i) (x : Formalism.L2.Herm.unitaryOneFiniteAdeles (host_cmData B.R B.host))
    (hx : Matrix.GeneralLinearGroup.det x.1 = Matrix.GeneralLinearGroup.det
      ((C.herm.base.cls u i h1 hm (C.herm.base.chOf u i c)).y ⟨c, rfl⟩).1) :
    (I.rec7 l Z).detCls u i c = u1Dt B.host I.SQ x := by
  by_cases h2 : i + 1 ≤ B.R.m
  · obtain ⟨k, hk⟩ := (hS u).mid i h1 h2
    refine detPt_of_reads I hI u i hk c x ?_
    have e := (C.carC u i h1 h2 (C.herm.base.chOf u i c)).y_eq ⟨c, rfl⟩
    rw [hx]
    exact (e ▸ det_reGL _ _).symm
  · obtain rfl : i = B.R.m := by omega
    obtain ⟨k, hk⟩ := (hS u).ends B.R.m le_rfl (Or.inr rfl)
    refine detPt_of_reads I hI u _ hk c x ?_
    have e := (C.carM u).y_eq c
    have key : ∀ (β : C.herm.base.Ch u B.R.m) (hb : C.herm.base.chOf u B.R.m c = β),
        Matrix.GeneralLinearGroup.det ((C.herm.base.cls u B.R.m h1 hm β).y ⟨c, hb⟩).1 =
          Matrix.GeneralLinearGroup.det ((C.herm.base.cls u B.R.m h1 hm (C.herm.base.chOf u B.R.m c)).y ⟨c, rfl⟩).1 := by
      rintro _ rfl
      rfl
    rw [hx, ← key _ (chOf_m C.herm.base u c)]
    exact (e ▸ det_reGL _ _).symm

def hermS (hI : I.Ok) (hS : I.StdC l Z C) : Formalism.L2.Herm.SymmetricHermitianColumns (I.rec7 l Z) :=
  { C.herm.base with
    dt := u1Dt B.host I.SQ
    dt_surj := normOneFiniteAdeleDetClass_surjective B.host I.SQ
    dt_ker := mem_integralNormOne_of_normOneDetClass_eq_one B.host I.SQ
    dt_open := GlobalTheory.T.isOpen_ker_normOneFiniteAdeleDetClass B.R B.host _ I.SQ (GlobalTheory.Mem.LevTwist.levOk_twists B X I hI).1
    dt_UO := unitIdeleImage_eq_map_integralNormOne B.host I.SQ
    dt_rat := fun z x h => GlobalTheory.T.rationalNormOne_class_eq_finiteAdelic_det_class B.R B.host I.SQ z x h
    det0 := fun u c x h => det_normOne_classStepZero_trueColumns I l Z C hI hS u c x h
    detI := fun u i h1 hm c x h => detI_std I l Z C hI hS u i h1 hm c x h }

theorem relDet_std (hI : I.Ok) (hS : I.StdC l Z C) : Formalism.L2.Herm.SymmetricRelativeDeterminant (I.rec7 l Z) (hermS I l Z C hI hS) := by
  intro N L L' g _ hg x hx
  obtain ⟨idl, hp⟩ := GlobalTheory.Mem.NormOneIdeal.pinned_of_finer (I.rec7 l Z) I.SQ (MulEquiv.refl _)
    (by ext t; exact ⟨fun h => ⟨t, h, rfl⟩, fun ⟨_, h, e⟩ => e ▸ h⟩) (fun _ => rfl)
    (fun N L L' t h => h)
  exact GlobalTheory.Mem.NormOneIdeal.relDet_eq_of_pinned (I.rec7 l Z) idl hp _ (hermS I l Z C hI hS).dt (hermS I l Z C hI hS).dt_ker
    (hermS I l Z C hI hS).dt_UO (hermS I l Z C hI hS).dt_rat L L' g x hg hx

theorem exists_colsFullS : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (C : ColsTiedSym (I.rec7 l Z)) (g : Formalism.L2.Herm.SymmetricGroupCompatibility (I.rec7 l Z) C.herm.base), I.StdC l Z C → Formalism.L2.Herm.VolumeCompatible (I.rec7 l Z) → ∃ Fu : ColsFullS C, HEq Fu.1.g g ∧ I.StdDt l Z Fu.1.base.dt := by
  intro B X I hI _ l Z C g hS hV
  let Fu : Formalism.L2.Herm.FullTiedS (I.rec7 l Z) :=
    { base := hermS I l Z C hI hS
      atT := C.herm.atT
      vol := hV
      levelZeroCompatibility := C.herm.levelZeroCompatibility
      g := g
      ad := C.herm.ad
      cof := C.herm.cof
      piG := C.herm.piG
      stabMap := C.herm.stabMap
      fvI := C.herm.fvI
      relDet := relDet_std I l Z C hI hS
      std := C.herm.std
      vpos := B.V_pos
      baseL := C.herm.baseL }
  refine ⟨⟨Fu, rfl⟩, HEq.rfl, ?_⟩
  intro x a ha
  exact normOneFiniteAdeleDetClass_of_isDetLift B.host I.SQ x a ha

end Main

end GlobalTheory.Mem.Col2.FullDt

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFullHermitianColumnsTrueColumnsStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fullHermitianColumns_trueColumns : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (C : ColsTiedSym (I.rec7 l Z)) (g : Formalism.L2.Herm.SymmetricGroupCompatibility (I.rec7 l Z) C.herm.base), I.StdC l Z C → Formalism.L2.Herm.VolumeCompatible (I.rec7 l Z) → ∃ Fu : ColsFullS C, HEq Fu.1.g g ∧ I.StdDt l Z Fu.1.base.dt := by
  first | exact @GlobalTheory.Mem.Col2.FullDt.exists_colsFullS | exact GlobalTheory.Mem.Col2.FullDt.exists_colsFullS | (intros; apply GlobalTheory.Mem.Col2.FullDt.exists_colsFullS <;> assumption)
end
