module

public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHasCentChar
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.TwoSplitIdem
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BesselDatumAuxiliaryVectorOrthogonalImage
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsSplitIdempotentsOfRelTraceOneModTwo
public import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsThetaFunOOfThetaAt
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ExponentSeparation
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HcParameterEAddHalfShiftLeBSucc

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOrEqOfPlaceIdem
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PlaceModelSum

open GlobalTheory.PlaceModel

theorem smul_tmul_one {F A E : Type} [Field F] [CommRing A] [CommRing E] [Algebra F A] [Algebra F E]
    (t : F) (a : A) : (t • a) ⊗ₜ[F] (1 : E) = a ⊗ₜ[F] algebraMap F E t := by
  rw [TensorProduct.smul_tmul, Algebra.algebraMap_eq_smul_one]

theorem trace_laws {R : Type} [CommRing R] {e c e' c' : R} (h1 : e * e = e) (c1 : c * c = c) (h2 : e * c = 0)
    (h1' : e' * e' = e') (c1' : c' * c' = c') (h2' : e' * c' = 0) :
    (e * e' + c * c') * (e * e' + c * c') = e * e' + c * c' ∧ (e + c) * (e * e' + c * c') = e * e' + c * c' ∧
      (e' + c') * (e * e' + c * c') = e * e' + c * c' ∧ (0 = e * e' + c * c' → e * e' = 0) ∧
      (e + c = e * e' + c * c' → e' + c' = e * e' + c * c' → e = e') :=
  ⟨by linear_combination (e' * e') * h1 + e * h1' + (c' * c') * c1 + c * c1' + (2 * e' * c') * h2,
    by linear_combination e' * h1 + c' * c1 + (e' + c') * h2,
    by linear_combination e * h1' + c * c1' + (e + c) * h2',
    fun ht => by linear_combination (-e) * ht - e' * h1 - c' * h2,
    fun b1 b2 => by
      linear_combination e * b1 - e' * b2 - h1 - h2 + h1' + h2' + e' * h1 + c' * h2 - e * h1' - c * h2'⟩

theorem eq_or_orth {A R : Type} [CommRing A] [CommRing R] (ι : A →+* R) (hinj : Function.Injective ι)
    {e c e' c' : R} {ε ε' t : A} (h1 : e * e = e) (c1 : c * c = c) (h2 : e * c = 0)
    (h1' : e' * e' = e') (c1' : c' * c' = c') (h2' : e' * c' = 0) (h3 : e + c = ι ε) (h3' : e' + c' = ι ε')
    (ht : ι t = e * e' + c * c') (p : t * t = t → ε * t = t → t = 0 ∨ t = ε)
    (p' : t * t = t → ε' * t = t → t = 0 ∨ t = ε') : e = e' ∨ e * e' = 0 := by
  obtain ⟨k1, k2, k3, k4, k5⟩ := trace_laws h1 c1 h2 h1' c1' h2'
  rw [← ht] at k1 k2 k3 k4 k5
  rw [h3] at k2 k5
  rw [h3'] at k3 k5
  have tt : t * t = t := hinj (by rw [map_mul]; exact k1)
  have t1 : ε * t = t := hinj (by rw [map_mul]; exact k2)
  have t2 : ε' * t = t := hinj (by rw [map_mul]; exact k3)
  by_cases h0 : t = 0
  · exact Or.inr (k4 (by rw [h0, map_zero]))
  · exact Or.inl (k5 (by rw [← (p tt t1).resolve_left h0]) (by rw [← (p' tt t2).resolve_left h0]))

variable {D : D7}

theorem exists_add_conj (a : AE D) : ∃ t : AF D.host.F, algebraMap (AF D.host.F) (AE D) t = a + cA D a := by
  induction a using TensorProduct.induction_on with
  | zero => exact ⟨0, by rw [RingHom.map_zero, RingHom.map_zero, add_zero]⟩
  | add x y hx hy =>
    obtain ⟨s, hs⟩ := hx
    obtain ⟨t, ht⟩ := hy
    exact ⟨s + t, by rw [RingHom.map_add (f := _), RingHom.map_add (f := _), hs, ht]; ring⟩
  | tmul a x =>
    have hσ : ∀ x, D.sp.cm.sig (D.sp.cm.sig x) = x := fun x => star_star x
    obtain ⟨t, ht⟩ : ∃ t : D.host.F, algebraMap _ _ t = x + D.sp.cm.sig x := by
      apply (D.sp.cm.fixed _).1
      change D.sp.cm.sig _ = _
      rw [map_add (f := _), hσ, add_comm]
    refine ⟨t • a, ?_⟩
    change (t • a) ⊗ₜ[D.host.F] (1 : D.host.E) = a ⊗ₜ[D.host.F] x + a ⊗ₜ[D.host.F] D.sp.cm.sig x
    rw [← TensorProduct.tmul_add, ← ht, smul_tmul_one]

theorem eq_zero_or_eq_of_placeIdem {v : HeightOneSpectrum (𝓞 D.host.F)} {ε t : AF D.host.F}
    (hε : IsPlaceIdem D v ε) (ht : t * t = t) (hεt : ε * t = t) : t = 0 ∨ t = ε := by
  obtain ⟨α, rfl, h1, h0⟩ := hε
  have e1 : t.1 = 0 := by
    have : (0 : Ainf D.host.F) * t.1 = t.1 := congrArg Prod.fst hεt
    rw [← this, zero_mul]
  have e2 : α * t.2 = t.2 := congrArg Prod.snd hεt
  have e3 : t.2 * t.2 = t.2 := congrArg Prod.snd ht
  have e4 : ∀ w, w ≠ v → evalV D.host.F w t.2 = 0 := fun w hw => by rw [← e2, map_mul, h0 w hw, zero_mul]
  have e5 : evalV D.host.F v t.2 * (evalV D.host.F v t.2 - 1) = 0 := by
    rw [mul_sub, ← map_mul, e3, mul_one, sub_self]
  have ext : ∀ β : Af D.host.F, (∀ w, evalV D.host.F w t.2 = evalV D.host.F w β) → t = pairA D.host.F 0 β :=
    fun β h => Prod.ext e1 (RestrictedProduct.ext _ _ h)
  rcases mul_eq_zero.1 e5 with h | h
  · refine Or.inl (ext 0 fun w => ?_)
    rw [map_zero]
    by_cases hw : w = v
    · rw [hw, h]
    · exact e4 w hw
  · refine Or.inr (ext α fun w => ?_)
    by_cases hw : w = v
    · rw [hw, h1, sub_eq_zero.1 h]
    · rw [e4 w hw, h0 w hw]

theorem eq_or_mul_eq_zero {e e' : AE D} (he : IsSplitIdem D e) (he' : IsSplitIdem D e') : e = e' ∨ e * e' = 0 := by
  obtain ⟨h1, h2, v, ε, hε, h3⟩ := he
  obtain ⟨h1', h2', v', ε', hε', h3'⟩ := he'
  have hinj : Function.Injective (algebraMap (AF D.host.F) (AE D)) :=
    Algebra.TensorProduct.includeLeft_injective (S := D.host.F) (algebraMap D.host.F D.host.E).injective
  have c1 : cA D e * cA D e = cA D e := by rw [← map_mul, h1]
  have c1' : cA D e' * cA D e' = cA D e' := by rw [← map_mul, h1']
  obtain ⟨t, ht⟩ := exists_add_conj (e * e')
  rw [RingHom.map_mul] at ht
  exact eq_or_orth _ hinj h1 c1 h2 h1' c1' h2' h3 h3' ht (eq_zero_or_eq_of_placeIdem hε)
    (eq_zero_or_eq_of_placeIdem hε')

theorem isSplitIdem_cA {e : AE D} (he : IsSplitIdem D e) : IsSplitIdem D (cA D e) := by
  obtain ⟨h1, h2, v, ε, hε, h3⟩ := he
  exact ⟨by rw [← map_mul, h1], by rw [cA_cA, mul_comm, h2], v, ε, hε, by rw [cA_cA, add_comm, h3]⟩

def IsOrthSum (e : AE D) : Prop :=
  ∃ (ι : Type) (P : Finset ι) (es : ι → AE D), (∀ i ∈ P, IsSplitIdem D (es i)) ∧
    (∀ i ∈ P, ∀ j ∈ P, j ≠ i → es i * es j = 0) ∧ e = ∑ i ∈ P, es i

theorem isOrthSum_of_isIdemSum {e : AE D} {P : Finset (Formalism.L2.DIV.Pl D.host.E)} (h : IsIdemSum e P) :
    IsOrthSum e := by
  obtain ⟨⟨es, h1, h2⟩, -⟩ := h
  refine ⟨_, P, es, fun i hi => (h1 i hi).1, fun i hi j hj hij => ?_, h2⟩
  refine (eq_or_mul_eq_zero (h1 i hi).1 (h1 j hj).1).resolve_left fun h => hij ?_
  refine HeightOneSpectrum.ext (Ideal.ext fun x => ?_)
  by_cases hx : x = 0
  · rw [hx]; exact iff_of_true (zero_mem _) (zero_mem _)
  · rw [(h1 i hi).2 x hx, (h1 j hj).2 x hx, h]

theorem IsOrthSum.conj {e : AE D} (h : IsOrthSum e) : IsOrthSum (cA D e) := by
  obtain ⟨ι, P, es, h1, h2, rfl⟩ := h
  exact ⟨ι, P, fun i => cA D (es i), fun i hi => isSplitIdem_cA (h1 i hi),
    fun i hi j hj hij => by rw [← map_mul, h2 i hi j hj hij, map_zero], map_sum _ _ _⟩

theorem mul_sum_orth {ι : Type} {P : Finset ι} {es : ι → AE D} (h1 : ∀ i ∈ P, IsSplitIdem D (es i))
    (h2 : ∀ i ∈ P, ∀ j ∈ P, j ≠ i → es i * es j = 0) {i : ι} (hi : i ∈ P) : es i * ∑ j ∈ P, es j = es i := by
  rw [Finset.mul_sum, Finset.sum_eq_single_of_mem i hi (h2 i hi), (h1 i hi).1]

theorem IsOrthSum.idem {e : AE D} (h : IsOrthSum e) : e * e = e := by
  obtain ⟨ι, P, es, h1, h2, rfl⟩ := h
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun i hi => mul_sum_orth h1 h2 hi

theorem infPart_split {e : AE D} (he : IsSplitIdem D e) : infPart D e = 0 := by
  obtain ⟨h1, h2, v, ε, ⟨β, rfl, -⟩, h3⟩ := he
  have h0 : infPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 β)) = 0 := TensorProduct.zero_tmul _ _
  have : e = (e + cA D e) * e := by linear_combination -h1 - h2
  rw [this, h3, map_mul, h0, zero_mul]

theorem IsOrthSum.infPart_eq {e : AE D} (h : IsOrthSum e) : infPart D e = 0 := by
  obtain ⟨ι, P, es, h1, -, rfl⟩ := h
  exact Finset.sum_induction _ (fun y => infPart D y = 0)
    (fun x y hx hy => by rw [RingHom.map_add (f := _), hx, hy, add_zero]) (RingHom.map_zero _) fun i hi => infPart_split (h1 i hi)

variable {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}

theorem idem_smul_latO {e : AE D} (he : e * e = e) {u : WO S T} (hu : u ∈ latO S T LS LT fun _ => True) :
    e • u ∈ latO S T LS LT fun _ => True :=
  GlobalTheory.LatticeStable.smul_mem_latO D S T LS LT _ e (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← map_mul, he])) u hu

theorem idem_smul_half {e : AE D} (he : e * e = e) {u : WO S T} (hu : u ∈ latO S T LS LT fun _ => True) :
    e • u ∈ (latO S T LS LT fun _ => True) ⊓ half S T e :=
  AddSubgroup.mem_inf.2 ⟨idem_smul_latO he hu, by rw [mem_half, smul_smul, he]⟩

theorem IsOrthSum.infPart_half {e : AE D} (h : IsOrthSum e) {u : WO S T} (hu : u ∈ half S T e) :
    u.map (infPart D) = 0 := by
  ext i j
  rw [Matrix.map_apply, ← (isHalf_iff S T).2 hu i j, map_mul, h.infPart_eq, zero_mul]
  rfl

theorem IsOrthSum.heisO_eq {ψ : AddChar (AF D.host.F) ℂ} {e : AE D} (h : IsOrthSum e) (hec : cA D e * e = 0)
    {f : WO S T → ℂ} (hf : IsLatVac (heisO ψ S T) (latO S T LS LT fun _ => True) f) (u : WO S T)
    (hu : u ∈ (latO S T LS LT fun _ => True) ⊓ half S T e) : heisO ψ S T u f = f := by
  obtain ⟨ι, P, es, h1, h2, he⟩ := h
  have e1 : u = ∑ i ∈ P, es i • u := by rw [← Finset.sum_smul, ← he, (mem_half S T).1 hu.2]
  have key : (∑ i ∈ P, es i • u) ∈ half S T e ∧ heisL S T ψ (∑ i ∈ P, es i • u) f = f := by
    refine Finset.sum_induction _ (fun y => y ∈ half S T e ∧ heisL S T ψ y f = f) (fun x y hx hy => ?_) ?_
      fun i hi => ?_
    · exact ⟨add_mem hx.1 hy.1, by rw [← heisL_half S T ψ hec x hx.1 y hy.1, hy.2, hx.2]⟩
    · exact ⟨zero_mem _, GlobalTheory.LatVac.heisO_zero ψ f⟩
    · have := idem_smul_half (h1 i hi).1 hu.1
      refine ⟨?_, hf.2 _ (h1 i hi) _ this.1 ((isHalf_iff S T).2 this.2)⟩
      rw [mem_half, smul_smul, mul_comm, he, mul_sum_orth h1 h2 hi]
  rw [← e1] at key
  exact key.2

theorem IsOrthSum.mem_of_dual {ψ : AddChar (AF D.host.F) ℂ}
    (hdual : ∀ u : WO S T, u.map (infPart D) = 0 → (u ∈ (latO S T LS LT fun _ => True) ↔
      ∀ u' ∈ (latO S T LS LT fun _ => True), ψ (symplO S T u u') = 1))
    {a : AE D} (ha : IsOrthSum a) (x : WO S T) (hx : x ∈ half S T a)
    (h : ∀ y ∈ (latO S T LS LT fun _ => True) ⊓ half S T (cA D a), ψ (symplO S T x y) = 1) :
    x ∈ (latO S T LS LT fun _ => True) ⊓ half S T a :=
  AddSubgroup.mem_inf.2 ⟨(hdual x (ha.infPart_half hx)).2 fun u hu => by
    have := h _ (idem_smul_half ha.conj.idem hu)
    rwa [← symplO_smul, (mem_half S T).1 hx] at this, hx⟩

theorem IsOrthSum.exists_model {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1))
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) {e : AE D} (he : IsOrthSum e) (hec : e * cA D e = 0)
    {f₀ : WO S T → ℂ} (hvac : IsLatVac (heisO ψ S T) (latO S T ΛS ΛT fun _ => True) f₀) :
    ∃ Tm, IsPlaceModel ψ (symplO S T) (heisO ψ S T) e (latO S T ΛS ΛT fun _ => True) 1 f₀ Tm := by
  have hdual := (GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T _ _ hψ hS hT).1
  have hfin := GlobalTheory.LatFinMod.latO_finite_mod D S T _ _ hS.1.fg hT.1.fg fun _ => True
  refine exists_placeModel ψ hec _ (fun u hu y hy => (hdual u (he.infPart_half hu.2)).1 hu.1 y hy.1)
    (he.mem_of_dual hdual) (fun y hy h => ?_) (fun k hk => ?_) one_ne_zero f₀
    (he.heisO_eq (by rw [mul_comm, hec]) hvac) (he.conj.heisO_eq (by rw [cA_cA, hec]) hvac)
  · refine he.conj.mem_of_dual hdual y hy fun u hu => ?_
    rw [cA_cA] at hu
    rw [symplO_skew, AddChar.map_neg_eq_inv, h u hu, inv_one]
  · obtain ⟨R, hR, h⟩ := hfin k hk
    refine ⟨(fun r => e • r) '' R, hR.image _, fun t ht => ?_⟩
    obtain ⟨r, hr, u, hu, htr⟩ := h t ht.1
    refine ⟨_, ⟨r, hr, rfl⟩, e • u, idem_smul_half he.idem hu, ?_⟩
    have := (mem_half S T).1 ht.2
    rw [← this, htr, smul_add, smul_comm e k u]

theorem placeModelExistsSum : ∀ D : D7, PlaceModelExistsSum D := by
  intro D ψ hψ S T ΛS ΛT hS hT P e he f₀ _ hvac
  have h := isOrthSum_of_isIdemSum he
  exact ⟨h.exists_model hψ hS hT he.2 hvac,
    h.conj.exists_model hψ hS hT (by rw [cA_cA, mul_comm, he.2]) hvac⟩

end GlobalTheory.PlaceModelSum

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsUnitaryOfIsCsd
noncomputable section

open NumberField IsDedekindDomain Topology Matrix Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host

namespace GlobalTheory.CuspRep.CsdUnitary

open Central

section

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}


omit [_root_.NumberField.IsTotallyComplex E] in
theorem norm_of_pow (χ : HChar E) (z : Ideles E) {n : ℕ} (hn : 0 < n) (h : ‖((χ.1 (z ^ n) : ℂˣ) : ℂ)‖ = 1) :
    ‖((χ.1 z : ℂˣ) : ℂ)‖ = 1 := by
  rw [map_pow, Units.val_pow_eq_pow_val, norm_pow] at h
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 h

theorem norm_int (χ : HChar E) (k : GL (Fin 1) (Af E))
    (hk : k ∈ GlobalTheory.GLIntegral.glSub (GlobalTheory.GLIntegral.intSubring E)) :
    ‖((χ.1 (finId E (GeneralLinearGroup.det k)) : ℂˣ) : ℂ)‖ = 1 := by
  let U : Subgroup (GL (Fin 1) (Af E)) := (χ.1.comp (finId E)).ker.comap GeneralLinearGroup.det
  have hU : IsOpen (U : Set (GL (Fin 1) (Af E))) :=
    (isOpen_ker_finIdele E (χ.1.comp (finId E)) (χ.2.1.comp (continuous_finId E))).preimage
      GeneralLinearGroup.continuous_det
  have : T2Space (Af E) :=
    inferInstanceAs (T2Space (RestrictedProduct (fun v : HeightOneSpectrum (𝓞 E) => v.adicCompletion E)
      (fun v => (v.adicCompletionIntegers E : Set (v.adicCompletion E))) Filter.cofinite))
  set K : Subgroup (GL (Fin 1) (Af E)) := GlobalTheory.GLIntegral.glSub (GlobalTheory.GLIntegral.intSubring E)
  have : CompactSpace K := isCompact_iff_compactSpace.1
    (GlobalTheory.GLIntegral.isCompact_glSub _ (GlobalTheory.AdeleCocompact.isCompact_integral E))
  have : Finite (K ⧸ U.subgroupOf K) := Subgroup.quotient_finite_of_isOpen _ (hU.preimage continuous_subtype_val)
  have hi := (Subgroup.finiteIndex_of_finite_quotient (H := U.subgroupOf K)).index_ne_zero
  obtain ⟨n, hn, -, h1⟩ := Subgroup.exists_pow_mem_of_index_ne_zero hi ⟨k, hk⟩
  refine norm_of_pow χ _ hn ?_
  have h2 : χ.1 (finId E (GeneralLinearGroup.det (k ^ n))) = 1 := h1
  rw [← map_pow, ← map_pow, h2, Units.val_one, norm_one]

theorem isUnitary_of_inf (χ : HChar E) (h : ∀ y, ‖((chiInf χ y : ℂˣ) : ℂ)‖ = 1) : χ.IsUnitary := by
  intro z
  change ‖((χ.1 z : ℂˣ) : ℂ)‖ = 1
  obtain ⟨n, hn, -, h1⟩ := Subgroup.exists_pow_mem_of_index_ne_zero
    (GlobalTheory.Mem.UnitIndex.finiteIndex_unitIdl_sup E).index_ne_zero z
  refine norm_of_pow χ z hn ?_
  obtain ⟨u, hu, _, ⟨γ, rfl⟩, e⟩ := Subgroup.mem_sup.1 h1
  have key : ∀ u ∈ GlobalTheory.Mem.Chr.unitIdl E, ∀ i j, (RankOne.obo _ (Units.map (pFin E).toMonoidHom u)).val i j ∈
      GlobalTheory.GLIntegral.intSubring E := fun u hu i j v => by
    rw [RankOne.obo_apply]
    exact (hu v).le
  have h2 := norm_int χ (RankOne.obo _ (Units.map (pFin E).toMonoidHom u))
    ⟨key u hu, by rw [← map_inv, ← map_inv]; exact key _ (inv_mem hu)⟩
  rw [show GeneralLinearGroup.det (RankOne.obo _ (Units.map (pFin E).toMonoidHom u)) = _ from CG.det_oneByOne _] at h2
  have h3 : ‖((χ.1 (infId E (Units.map (pInf E).toMonoidHom u)) : ℂˣ) : ℂ)‖ = 1 := h _
  have h4 : χ.1 (Mem.Chr.diagUnits E γ) = 1 := χ.2.2 γ
  rw [← e, map_mul, h4, mul_one, ← infId_mul_finId u, map_mul, Units.val_mul, norm_mul, h2, h3, one_mul]

theorem norm_chiInf (χ : HChar E) (h : ∀ z, star z = z → dchi χ z = 0) (y : (Cinf E)ˣ) :
    ‖((chiInf χ y : ℂˣ) : ℂ)‖ = 1 := by
  classical
  have h1 : ∀ w : InfinitePlace E, dchi χ (Pi.single w 1) = 0 := fun w => h _ (by
    funext v
    by_cases e : v = w
    · subst e; simp
    · simp [e])
  have h2 : ∀ w : InfinitePlace E, (dchi χ (Pi.single w Complex.I)).re = 0 := fun w => by
    have e : expU ((2 * Real.pi : ℝ) • (Pi.single w Complex.I : Cinf E)) = 1 := Units.ext (funext fun v => by
      change Complex.exp (((2 * Real.pi : ℝ) • (Pi.single w Complex.I : Cinf E)) v) = 1
      by_cases e : v = w
      · subst e; simp
      · simp [e])
    have h3 := congrArg norm (chiInf_expU χ ((2 * Real.pi : ℝ) • (Pi.single w Complex.I : Cinf E)))
    rw [e, map_one, Units.val_one, norm_one, Complex.norm_exp, map_smul, eq_comm, Real.exp_eq_one_iff,
      Complex.smul_re, smul_eq_mul] at h3
    exact (mul_eq_zero.1 h3).resolve_left (by positivity)
  have h3 : ∀ z : Cinf E, (dchi χ z).re = 0 := fun z => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← Finset.univ_sum_single z, map_sum, Complex.re_sum]
    refine Finset.sum_eq_zero fun w _ => ?_
    have e : (Pi.single w (z w) : Cinf E) =
        (z w).re • (Pi.single w 1 : Cinf E) + (z w).im • (Pi.single w Complex.I : Cinf E) := by
      rw [← Pi.single_smul, ← Pi.single_smul, ← Pi.single_add]
      simp
    rw [e, map_add (f := _), map_smul, map_smul, h1, smul_zero, zero_add, Complex.smul_re, h2, smul_zero]
  rw [← expU_log y, chiInf_expU, Complex.norm_exp, h3, Real.exp_zero]

theorem lie_scL {π : CuspSub E a} {ω : HChar E} (h : π.HasCentral ω) (z : Cinf E) {ψ : Sm E a} (hψ : ψ ∈ π.V) :
    lie E a (scL a z) ψ = dchi ω z • ψ := by
  refine Subtype.ext <| funext fun g => ?_
  have h1 := hasDerivAt_scalar z ψ g
  have e : (fun t : ℝ => ψ.1 (g * GeneralLinearGroup.scalar (Fin a) (infId E (expU (t • z))))) =
      fun t : ℝ => Complex.exp (t * dchi ω z) * ψ.1 g := by
    funext t
    rw [← scalar_comm, h.apply hψ]
    congr 1
    refine (chiInf_expU ω _).trans ?_
    rw [map_smul, Complex.real_smul]
  rw [e] at h1
  refine h1.unique ?_
  change HasDerivAt _ (dchi ω z * ψ.1 g) 0
  simpa using (((Complex.ofRealCLM.hasDerivAt (x := 0)).mul_const (dchi ω z)).cexp).mul_const (ψ.1 g)

end

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {a : ℕ}

theorem thetaOp_scL (z : Cinf L) : thetaOp (.lie (scL a z)) = (.lie (scL a (-star z)) : Op L a) := by
  refine congrArg (fun X => Op.lie (toL X)) ?_
  change -(GlobalTheory.Tw.Phi a (Cinf L) * (Matrix.diagonal fun _ => z)ᴴ * (GlobalTheory.Tw.Phi a (Cinf L))ᵀ) = _
  have e : (Matrix.diagonal fun _ : Fin a => z)ᴴ = star z • (1 : Matrix (Fin a) (Fin a) (Cinf L)) := by
    rw [Matrix.diagonal_conjTranspose, Matrix.smul_one_eq_diagonal]; rfl
  rw [e, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Phi_mul_transpose, ← neg_smul,
    Matrix.smul_one_eq_diagonal]

theorem dchi_theta {π : CuspSub L a} {ω : HChar L} (h : π.HasCentral ω) (hπ : π.IsCsd) (z : Cinf L) :
    dchi ω (-star z) = dchi ω z := by
  obtain ⟨T, hT⟩ := hπ
  have := Submodule.nontrivial_iff_ne_bot.2 π.ne_bot
  obtain ⟨φ, hφ⟩ := exists_ne (0 : π.V)
  have e : ∀ (x : Cinf L) (ψ : π.V), π.op (.lie (scL a x)) ψ = dchi ω x • ψ := fun x ψ =>
    Subtype.ext (lie_scL h x ψ.2)
  have h1 := hT (.lie (scL a z)) φ
  rw [thetaOp_scL, e, e, map_smul] at h1
  exact smul_left_injective ℂ ((map_ne_zero_iff T T.injective).2 hφ) h1

theorem isUnitary_of_isCsd : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (a : ℕ) (π : GlobalTheory.CuspRep.CG L a),
    π.IsCsd → π.IsUnitary := by
  intro L _ _ _ a π hπ
  induction π using Quotient.inductionOn with
  | _ π =>
    obtain ⟨ω, h⟩ := exists_hasCentral L a π
    refine (CG.isUnitary_mk π).2 ⟨ω, isUnitary_of_inf ω (norm_chiInf ω fun z hz => ?_), h⟩
    have h1 := dchi_theta h hπ z
    rw [hz, map_neg] at h1
    linear_combination -h1 / 2

end GlobalTheory.CuspRep.CsdUnitary
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColLieApply
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Matrix
open scoped ComplexOrder

namespace GlobalTheory.DefLift

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Poly

variable {ι : Type} {m n : ℕ}

abbrev Pol (ι : Type) (m n : ℕ) : Type := MvPolynomial (ι × Fin m × Fin n) ℂ

def subst (a : ι → Matrix (Fin n) (Fin n) ℂ) (b : ι → Matrix (Fin m) (Fin m) ℂ) : Pol ι m n →ₐ[ℂ] Pol ι m n :=
  MvPolynomial.aeval fun v => ∑ i, ∑ c, (b v.1 i v.2.1 * a v.1 v.2.2 c) • MvPolynomial.X (v.1, i, c)


open Classical in
def rowSub (n : ℕ) (τ : ι) (u : Matrix.unitaryGroup (Fin m) ℂ) : Pol ι m n →ₗ[ℂ] Pol ι m n :=
  (subst (fun _ => 1) (fun ρ => if ρ = τ then (u : Matrix (Fin m) (Fin m) ℂ) else 1)).toLinearMap


open Classical in
def colSub (m : ℕ) (τ : ι) (g : Matrix.unitaryGroup (Fin n) ℂ) : Pol ι m n →ₗ[ℂ] Pol ι m n :=
  (subst (fun ρ => if ρ = τ then star (g : Matrix (Fin n) (Fin n) ℂ) else 1) (fun _ => 1)).toLinearMap

def rowLie (n : ℕ) (τ : ι) (k l : Fin m) : Pol ι m n →ₗ[ℂ] Pol ι m n :=
  ∑ c : Fin n, LinearMap.mulLeft ℂ (MvPolynomial.X (τ, k, c)) ∘ₗ (MvPolynomial.pderiv (τ, l, c)).toLinearMap

def colLie (m : ℕ) (τ : ι) (k l : Fin n) : Pol ι m n →ₗ[ℂ] Pol ι m n :=
  ∑ i : Fin m, LinearMap.mulLeft ℂ (MvPolynomial.X (τ, i, k)) ∘ₗ (MvPolynomial.pderiv (τ, i, l)).toLinearMap

theorem rowLie_apply (τ : ι) (k l : Fin m) (P : Pol ι m n) :
    rowLie n τ k l P = ∑ c : Fin n, MvPolynomial.X (τ, k, c) * MvPolynomial.pderiv (τ, l, c) P := by
  simp [rowLie, LinearMap.sum_apply]

theorem colLie_apply (τ : ι) (k l : Fin n) (P : Pol ι m n) :
    colLie m τ k l P = ∑ i : Fin m, MvPolynomial.X (τ, i, k) * MvPolynomial.pderiv (τ, i, l) P := by
  simp [colLie, LinearMap.sum_apply]

end Poly

def IrrFam {ι κ X : Type} [AddCommGroup X] [Module ℂ X] (π : ι → κ → Module.End ℂ X) : Prop :=
  ∀ U : Submodule ℂ X, (∀ τ u, ∀ x ∈ U, π τ u x ∈ U) → U = ⊥ ∨ U = ⊤

section Model

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

def AllPlus (M : DSModel V S) : Prop := ∀ τ a, M.ε τ a = true

def unfr (M : DSModel V S) (τ : D.what₂.Tau) (u : Matrix (Fin V.rank) (Fin V.rank) ℂ) : Matrix (Fin V.rank) (Fin V.rank) ℂ :=
  (M.fr τ)⁻¹ * u * M.fr τ

def IsTensAct (M : DSModel V S) (π : D.what₂.Tau → Matrix.unitaryGroup (Fin V.rank) ℂ → Module.End ℂ (SmT M)) : Prop :=
  ∀ τ u x, inclT M (π τ u x) = actT M τ (unfr M τ u) (inclT M x)

variable {M : DSModel V S}

theorem AllPlus.jm (h : AllPlus M) (τ : D.what₂.Tau) : Formalism.REAL.Jm (M.ε τ) = 1 := by
  unfold Formalism.REAL.Jm
  simp [h τ]

theorem fr_det (M : DSModel V S) (τ : D.what₂.Tau) : IsUnit (M.fr τ).det :=
  (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)

theorem AllPlus.gram (h : AllPlus M) (τ : D.what₂.Tau) : gramAt D V τ = (M.fr τ)ᴴ * M.fr τ := by
  rw [← M.fr_gram τ, h.jm, Matrix.mul_one]

theorem AllPlus.posDef (h : AllPlus M) (τ : D.what₂.Tau) : (gramAt D V τ).PosDef := by
  rw [h.gram]
  exact Matrix.PosDef.conjTranspose_mul_self _ (Matrix.mulVec_injective_iff_isUnit.2 (M.fr_unit τ))

theorem AllPlus.cart (h : AllPlus M) (τ : D.what₂.Tau) : cart M τ = 1 := by
  unfold Links.cart
  rw [h.jm, Matrix.mul_one, Matrix.nonsing_inv_mul _ (fr_det M τ)]

theorem fr_unfr (M : DSModel V S) (τ : D.what₂.Tau) (u : Matrix (Fin V.rank) (Fin V.rank) ℂ) :
    M.fr τ * unfr M τ u * (M.fr τ)⁻¹ = u := by
  unfold unfr
  rw [Matrix.mul_assoc (M.fr τ)⁻¹, Matrix.mul_nonsing_inv_cancel_left _ _ (fr_det M τ),
    Matrix.mul_nonsing_inv_cancel_right _ _ (fr_det M τ)]

theorem rep_unfr (M : DSModel V S) (τ : D.what₂.Tau) (u : Matrix (Fin V.rank) (Fin V.rank) ℂ) :
    M.rep τ (unfr M τ u) = M.σ τ u := by
  unfold DSModel.rep
  rw [fr_unfr]

theorem AllPlus.unfr_mem (h : AllPlus M) (τ : D.what₂.Tau) (u : Matrix.unitaryGroup (Fin V.rank) ℂ) :
    unfr M τ u ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) := by
  have hu : (u : Matrix (Fin V.rank) (Fin V.rank) ℂ)ᴴ * u = 1 := Matrix.mem_unitaryGroup_iff'.1 u.2
  have e : M.fr τ * unfr M τ u = u * M.fr τ := by
    unfold unfr
    rw [Matrix.mul_assoc (M.fr τ)⁻¹, Matrix.mul_nonsing_inv_cancel_left _ _ (fr_det M τ)]
  show (unfr M τ u)ᴴ * gramAt D V τ * unfr M τ u = gramAt D V τ
  rw [h.gram]
  calc _ = (M.fr τ * unfr M τ u)ᴴ * (M.fr τ * unfr M τ u) := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = (M.fr τ)ᴴ * ((u : Matrix (Fin V.rank) (Fin V.rank) ℂ)ᴴ * u) * M.fr τ := by
      rw [e]; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = _ := by rw [hu, Matrix.mul_one]

theorem AllPlus.exists_unfr (h : AllPlus M) (τ : D.what₂.Tau) {g : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) : ∃ u : Matrix.unitaryGroup (Fin V.rank) ℂ, unfr M τ u = g := by
  have hg' : gᴴ * ((M.fr τ)ᴴ * M.fr τ) * g = (M.fr τ)ᴴ * M.fr τ := by rw [← h.gram]; exact hg
  refine ⟨⟨M.fr τ * g * (M.fr τ)⁻¹, Matrix.mem_unitaryGroup_iff'.2 ?_⟩, ?_⟩
  · calc _ = ((M.fr τ)⁻¹)ᴴ * (gᴴ * ((M.fr τ)ᴴ * M.fr τ) * g) * (M.fr τ)⁻¹ := by
          simp only [star_eq_conjTranspose, Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = (M.fr τ * (M.fr τ)⁻¹)ᴴ * (M.fr τ * (M.fr τ)⁻¹) := by
          rw [hg']; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = 1 := by rw [Matrix.mul_nonsing_inv _ (fr_det M τ)]; simp
  · show (M.fr τ)⁻¹ * (M.fr τ * g * (M.fr τ)⁻¹) * M.fr τ = g
    rw [Matrix.mul_assoc (M.fr τ), Matrix.nonsing_inv_mul_cancel_left _ _ (fr_det M τ),
      Matrix.nonsing_inv_mul_cancel_right _ _ (fr_det M τ)]

end Model

end GlobalTheory.DefLift

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockPolynomialVectorsOfSmoothThetaStable
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockPolynomialVectorsOfSmoothThetaStable
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum

namespace GlobalTheory.FockTheta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem ptStable : ∀ D : D7, Formalism.IndefR.Fin.PtStable D := by
  intro D ψ θ hψ hθ S T sS sT BS BT f P hf
  exact (GlobalTheory.OrientedHeis.pureTensorL_intertwine (IsThetaFunO ψ S T) GlobalTheory.OrientedHeis.theta_zero
    (fun _ _ => GlobalTheory.OrientedHeis.theta_add) (fun c _ => GlobalTheory.OrientedHeis.theta_smul c) _
    (aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT) 1
    (fun k _ hg => ⟨GlobalTheory.OrientedHeis.theta_smul _ (GlobalTheory.OrientedHeis.theta_sub
      (GlobalTheory.OrientedHeis.theta_dRho hθ hψ k.1 _ hg)
      (GlobalTheory.OrientedHeis.theta_smul _ (GlobalTheory.OrientedHeis.theta_dRho hθ hψ k.1 _ hg))), rfl⟩) f hf P).1

end GlobalTheory.FockTheta

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockPolynomialVectorsOfSmoothThetaStableStatement
open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockPolynomialVectors_of_smoothTheta_stable : ∀ D : D7, Formalism.IndefR.Fin.PtStable D := by
  first | exact @GlobalTheory.FockTheta.ptStable | exact GlobalTheory.FockTheta.ptStable | (intros; apply GlobalTheory.FockTheta.ptStable <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceAnnihilatorRelativelyCompact
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceAnnihilatorRelativelyCompact
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.BesselData GlobalTheory.RootExch
open scoped TensorProduct RestrictedProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitAnnihilator

open GlobalTheory.IdemModTwo


open Classical in
theorem continuous_singleV (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    Continuous (singleV F v) := by
  have hS : Filter.cofinite ≤ Filter.principal ({v}ᶜ : Set (HeightOneSpectrum (𝓞 F))) :=
    Filter.le_principal_iff.2 (Set.finite_singleton v).compl_mem_cofinite
  let f : v.adicCompletion F → Πʳ w : HeightOneSpectrum (𝓞 F),
      [w.adicCompletion F, w.adicCompletionIntegers F]_[Filter.principal ({v}ᶜ : Set _)] :=
    fun x => ⟨Pi.single (M := fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F) v x, by
      intro w hw
      have hw' : w ≠ v := hw
      simp only [Set.mem_ofPred_eq, Pi.single_eq_of_ne hw', SetLike.mem_coe]
      exact zero_mem _⟩
  have hf : Continuous f := RestrictedProduct.continuous_rng_of_principal.2 (continuous_single v)
  exact (RestrictedProduct.continuous_inclusion hS).comp hf

theorem trace_split {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)} {e : AE D} (he : SplitAt D v e)
    (x y : Fv D.host.F v) :
    Algebra.trace (AF D.host.F) (AE D) (fj D (singleV D.host.F v x) * e * (fj D (singleV D.host.F v y) * e)) =
      pairA D.host.F 0 (singleV D.host.F v (x * y)) := by
  have h1 : fj D (singleV D.host.F v x) * e * (fj D (singleV D.host.F v y) * e) =
      fj D (singleV D.host.F v (x * y)) * e := by
    rw [mul_mul_mul_comm, he.1, ← map_mul, singleV_mul, GlobalTheory.SplitIdem.evalV_singleV_same]
  have h2 := GlobalTheory.FockCompare.SymplVal.trace_AE D (fj D (singleV D.host.F v (x * y)) * e)
  rw [map_mul (cA D), cA_fj, ← mul_add, he.2.2, ← map_mul (fj D), singleV_mul, GlobalTheory.SplitIdem.evalV_singleV_same, mul_one] at h2
  rw [h1]
  exact tmul_one_inj (F := D.host.F) (E := D.host.E) h2

theorem annihilator_subset_compact : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), (∀ v, ∃ y, psiV D.host.F ψ v y ≠ 1) → ∀ ε : AE D, IsSplitIdem D ε → ∀ V ∈ nhds (0 : AE D), ∃ C : Set (AE D), IsCompact C ∧ ∀ a, ε * a = a → (∀ s ∈ V, ε * s = s → ψ (Algebra.trace (AF D.host.F) (AE D) (a * s)) = 1) → a ∈ C := by
  intro D ψ hψ e hε V hV
  obtain ⟨v, he⟩ := (isSplitIdem_iff e).1 hε
  obtain ⟨y, hy⟩ := hψ v
  have : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  have : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)
  have : ProperSpace (Fv D.host.F v) := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion D.host.F v
  let j : Fv D.host.F v → AE D := fun x => fj D (singleV D.host.F v x) * e
  have hj : Continuous j := by
    have h1 : Continuous (algebraMap (AF D.host.F) (AE D)) :=
      IsModuleTopology.continuous_of_linearMap (Algebra.linearMap (AF D.host.F) (AE D))
    have h2 : Continuous fun x : Fv D.host.F v => pairA D.host.F 0 (singleV D.host.F v x) :=
      Continuous.prodMk continuous_const (continuous_singleV D.host.F v)
    exact (h1.comp h2).mul continuous_const
  have hj0 : j 0 = 0 := by
    have h0 : singleV D.host.F v 0 = 0 := by
      rw [← sub_self (0 : Fv D.host.F v), singleV_sub, sub_self]
    simp only [j, h0, map_zero, zero_mul]
  have hV' : j ⁻¹' V ∈ nhds (0 : Fv D.host.F v) := hj.continuousAt.preimage_mem_nhds (by rwa [hj0])
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 hV'
  refine ⟨j '' Metric.closedBall 0 (‖y‖ / r), (isCompact_closedBall _ _).image hj, fun a ha hs => ?_⟩
  obtain ⟨x, hx⟩ := he.exists_scalar a
  rw [ha] at hx
  refine ⟨x, ?_, hx.symm⟩
  by_contra hn
  rw [mem_closedBall_zero_iff, not_le] at hn
  have hxpos : 0 < ‖x‖ := lt_of_le_of_lt (div_nonneg (norm_nonneg _) hr.le) hn
  have hx0 : x ≠ 0 := norm_pos_iff.1 hxpos
  have hmem : y / x ∈ Metric.ball (0 : Fv D.host.F v) r := by
    rw [mem_ball_zero_iff, norm_div, div_lt_iff₀ hxpos]
    rw [div_lt_iff₀ hr] at hn
    linarith
  have h := hs (j (y / x)) (hball hmem) (by
    show e * (_ * e) = _ * e
    rw [mul_left_comm, he.1])
  rw [hx] at h
  change ψ (Algebra.trace _ _ (_ * (_ * e))) = 1 at h
  rw [trace_split he, mul_div_cancel₀ _ hx0] at h
  exact hy h

end GlobalTheory.SplitAnnihilator

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceAnnihilatorRelativelyCompactStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.BesselData GlobalTheory.RootExch
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlace_annihilator_relativelyCompact : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), (∀ v, ∃ y, psiV D.host.F ψ v y ≠ 1) → ∀ ε : AE D, IsSplitIdem D ε → ∀ V ∈ nhds (0 : AE D), ∃ C : Set (AE D), IsCompact C ∧ ∀ a, ε * a = a → (∀ s ∈ V, ε * s = s → ψ (Algebra.trace (AF D.host.F) (AE D) (a * s)) = 1) → a ∈ C := by
  first | exact @GlobalTheory.SplitAnnihilator.annihilator_subset_compact | exact GlobalTheory.SplitAnnihilator.annihilator_subset_compact | (intros; apply GlobalTheory.SplitAnnihilator.annihilator_subset_compact <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaWeightArithmeticAtPlaceProof
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaWeightArithmeticAtPlaceProof
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.DivisionValues
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.InfinityTypes Formalism.L2.NTheta

namespace GlobalTheory.PairWeightArith

lemma toNat_floor_cast {x : ℚ} (hz : ∃ z : ℤ, x = z) (h0 : 0 ≤ x) : ((⌊x⌋.toNat : ℕ) : ℚ) = x := by
  obtain ⟨z, rfl⟩ := hz
  have hz : 0 ≤ z := by exact_mod_cast h0
  rw [Int.floor_intCast]
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hz
  simp

lemma lamAt_tail {R : Ranks} (h : HCParam R) (n : ℕ) (c : Fin R.m) (hn : n + 1 = R.k + c) :
    lamAt h n = -h.b c := by
  have hk := R.m_add_three_le_k
  have hc := c.2
  unfold lamAt
  rw [dite_eq_right (by omega), dite_eq_left (by omega)]
  congr 2
  exact Fin.ext (by simp only; omega)

lemma lamAt_anti {R : Ranks} (h : HCParam R) {a b : ℕ} (hab : a ≤ b) (hb : b < R.r) :
    lamAt h b + b ≤ lamAt h a + a := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  have := lamAt_add_add_le h d a hb
  push_cast
  linarith

variable (D : D7) (i : Fin D.R.m) (τ : D.what₂.Tau)

lemma sig_eq : pS D i τ = D.R.k + i ∧ qS D i τ = D.R.m - ((i : ℕ) + 1) := by
  have h := D.sp.W_sigval ((i : ℕ) + 1) (Nat.le_add_left _ _) i.2 (tauE D τ)
  refine ⟨?_, ?_⟩
  · show ((D.sp.W ((i : ℕ) + 1)).sig (tauE D τ)).1 = _
    rw [h]; simp [Ranks.sigW]
  · show ((D.sp.W ((i : ℕ) + 1)).sig (tauE D τ)).2 = _
    rw [h]; rfl

lemma pq_eq : pS D i τ + qS D i τ = D.R.r := by
  obtain ⟨h1, h2⟩ := sig_eq D i τ
  have hk := D.R.m_add_three_le_k
  have hi := i.2
  rw [h1, h2]; unfold Ranks.r; omega

lemma t_half : ∃ s : ℕ, (D.R.t : ℚ) = 2 * s + 1 := by
  obtain ⟨s, hs⟩ := D.R.t_odd
  exact ⟨s, by exact_mod_cast hs⟩

lemma aPlusQ_int (a : ℕ) : ∃ z : ℤ, aPlusQ D i τ a = z := by
  obtain ⟨s, hs⟩ := t_half D
  obtain ⟨z, hz⟩ := lamAt_int (D.hc τ) a
  obtain ⟨e, he⟩ := (D.hc τ).e_int i
  refine ⟨z + e - (pS D i τ : ℕ) + a - s, ?_⟩
  simp only [aPlusQ, centred, eS, hs, hz, he]
  push_cast; ring

lemma neg_dRowQ_int (c : ℕ) : ∃ z : ℤ, -dRowQ D i τ c = z := by
  obtain ⟨s, hs⟩ := t_half D
  obtain ⟨z, hz⟩ := lamAt_int (D.hc τ) (pS D i τ + c)
  obtain ⟨e, he⟩ := (D.hc τ).e_int i
  refine ⟨-(z + e + c + 1 + s), ?_⟩
  simp only [dRowQ, centred, eS, hs, hz, he]
  push_cast; ring

lemma aPlusQ_anti {a b : ℕ} (hab : a ≤ b) (hb : b < pS D i τ) : aPlusQ D i τ b ≤ aPlusQ D i τ a := by
  have h := pq_eq D i τ
  have := lamAt_anti (D.hc τ) hab (by omega)
  simp only [aPlusQ, centred]
  linarith

lemma dRowQ_anti {a b : ℕ} (hab : a ≤ b) (hb : b < qS D i τ) : dRowQ D i τ b ≤ dRowQ D i τ a := by
  have h := pq_eq D i τ
  have := lamAt_anti (D.hc τ) (Nat.add_le_add_left hab (pS D i τ)) (by omega)
  simp only [dRowQ, centred]
  push_cast at this
  linarith

lemma one_le_aPlusQ {a : ℕ} (ha : a < pS D i τ) : 1 ≤ aPlusQ D i τ a := by
  obtain ⟨n, hn⟩ : ∃ n, pS D i τ = n + 1 := ⟨pS D i τ - 1, by omega⟩
  refine le_trans ?_ (aPlusQ_anti D i τ (show a ≤ n by omega) (by omega))
  have h1 := lamAt_tail (D.hc τ) n i (by rw [← hn]; exact (sig_eq D i τ).1)
  have g := (D.hc τ).gap_be i
  have hn' : (pS D i τ : ℚ) = n + 1 := by exact_mod_cast hn
  simp only [aPlusQ, centred, eS, h1, hn']
  linarith

lemma one_le_neg_dRowQ {c : ℕ} (hc : c < qS D i τ) : 1 ≤ -dRowQ D i τ c := by
  obtain ⟨hp, hq⟩ := sig_eq D i τ
  have h0 := dRowQ_anti D i τ (Nat.zero_le c) hc
  have hi : (i : ℕ) + 1 < D.R.m := by omega
  have h1 := lamAt_tail (D.hc τ) (pS D i τ + 0) ⟨i + 1, hi⟩ (by simp only; omega)
  have g := (D.hc τ).gap_eb i hi
  have : dRowQ D i τ 0 ≤ -1 := by
    simp only [dRowQ, centred, eS, h1]
    push_cast
    linarith
  linarith

lemma cast_aPlus {a : ℕ} (ha : a < pS D i τ) : (aP D i τ a : ℚ) = aPlusQ D i τ a := by
  unfold aP aPl
  rw [if_pos ha]
  exact toNat_floor_cast (aPlusQ_int D i τ a) (le_trans zero_le_one (one_le_aPlusQ D i τ ha))

lemma aM_cast {c : ℕ} (hc : c < qS D i τ) : (aM D i τ (qS D i τ - 1 - c) : ℚ) = -dRowQ D i τ c := by
  unfold aM aMi
  have e1 : qS D i τ - (qS D i τ - 1 - c) = c + 1 := by omega
  rw [if_pos (by omega), e1, show pS D i τ + (c + 1) - 1 = pS D i τ + c by omega]
  have e2 : -((D.hc τ).e i + lamAt (D.hc τ) (pS D i τ + c) + ((c + 1 : ℕ) : ℚ) + ((D.R.t : ℚ) - 1) / 2)
      = -dRowQ D i τ c := by
    simp only [dRowQ, centred, eS]; push_cast; ring
  rw [e2]
  exact toNat_floor_cast (neg_dRowQ_int D i τ c) (le_trans zero_le_one (one_le_neg_dRowQ D i τ hc))

lemma aM_cast' {a : ℕ} (ha : a < qS D i τ) : (aM D i τ a : ℚ) = -dRowQ D i τ (qS D i τ - 1 - a) := by
  rw [← aM_cast D i τ (by omega)]
  congr 2
  omega

lemma lam_eq {w : IndefiniteWeightData.WeightData} (hw : IsDataOf D i τ w) {a : ℕ} (ha : a < D.R.r) :
    (w.lam (a + 1) : ℚ) = lamAt (D.hc τ) a := by
  obtain ⟨hk, -, -, -, -, hv, hb⟩ := hw
  have hk3 := D.R.m_add_three_le_k
  unfold Ranks.r at ha
  unfold IndefiniteWeightData.WeightData.lam
  rw [hk]
  by_cases h : a < D.R.k - 1
  · rw [if_pos (by omega)]
    unfold lamAt
    rw [dite_eq_left h]
    exact hv ⟨a, h⟩
  · rw [if_neg (by omega), lamAt_tail (D.hc τ) a ⟨a + 1 - D.R.k, by omega⟩ (by simp only; omega),
      ← hb, Int.cast_neg]
    congr 3
    simp only; omega

lemma lamPrime_eq (w : IndefiniteWeightData.WeightData) (hw : IsDataOf D i τ w) (a : ℕ) (ha : a < D.R.r + D.R.t) :
    w.lamPrime (a + 1) = (thetaWt D i τ a : ℚ) + dShift D i τ := by
  obtain ⟨hp, hq⟩ := sig_eq D i τ
  have hr := pq_eq D i τ
  have hl := fun a ha => lam_eq D i τ (a := a) hw ha
  obtain ⟨hk, hm, ht, hj, he, hv, hb⟩ := hw
  have hk3 := D.R.m_add_three_le_k
  have wp : w.p = pS D i τ := by unfold IndefiniteWeightData.WeightData.p; omega
  have wq : w.q = qS D i τ := by unfold IndefiniteWeightData.WeightData.q; omega
  have wn : w.nV = pS D i τ + qS D i τ + D.R.t := by
    unfold IndefiniteWeightData.WeightData.nV IndefiniteWeightData.WeightData.r; unfold Ranks.r at hr; omega
  unfold IndefiniteWeightData.WeightData.lamPrime
  congr 1
  · unfold IndefiniteWeightData.WeightData.thetaWt thetaWt
    rw [wp, wq, ht]
    by_cases h1 : a < pS D i τ
    · rw [if_pos (by omega), if_pos h1, Int.cast_natCast, cast_aPlus D i τ h1]
      unfold IndefiniteWeightData.WeightData.aPlus
      rw [hl a (by omega), wn, wp, wq, he]
      simp only [aPlusQ, centred]
      push_cast; ring
    · rw [if_neg (by omega), if_neg h1]
      by_cases h2 : a < pS D i τ + D.R.t
      · rw [if_pos (by omega), if_pos h2]; simp
      · rw [if_neg (by omega), if_neg h2]
        obtain ⟨c, rfl⟩ : ∃ c, a = pS D i τ + D.R.t + c := ⟨a - (pS D i τ + D.R.t), by omega⟩
        have hc : c < qS D i τ := by omega
        rw [Nat.add_sub_cancel_left, Int.cast_neg, Int.cast_natCast, aM_cast D i τ hc]
        unfold IndefiniteWeightData.WeightData.aMinus
        have e1 : w.q + 1 - (qS D i τ + 1 - (pS D i τ + D.R.t + c + 1 - pS D i τ - D.R.t)) = c + 1 := by
          omega
        have hi : (i : ℕ) + c + 1 < D.R.m := by omega
        have e2 : (w.b (w.j + (c + 1)) : ℚ) = (D.hc τ).b ⟨i + c + 1, hi⟩ := by
          rw [← hb]; congr 2; simp only; omega
        rw [e1, e2, he, ht]
        simp only [dRowQ, centred]
        rw [lamAt_tail (D.hc τ) (pS D i τ + c) ⟨i + c + 1, hi⟩ (by simp only; omega)]
        push_cast; ring
  · unfold IndefiniteWeightData.WeightData.dTau dShift
    rw [wp, wq, he]

theorem arithAt : ∀ (D : D7) (i : Fin D.R.m) (τ : D.what₂.Tau), ArithAt D i τ := by
  intro D i τ
  have hr := pq_eq D i τ
  have hV : (Vc D i).rank = D.R.r + D.R.t := D.sp.V_rank _ (Nat.le_add_left _ _) i.2
  have hr' : (D.R.r : ℚ) = (pS D i τ : ℚ) + (qS D i τ : ℚ) := by exact_mod_cast hr.symm
  have ho : Odd (pS D i τ + qS D i τ) := hr ▸ odd_r D.R
  have hL := GlobalTheory.ForcedWeights.lamLForced D ((i : ℕ) + 1) (Nat.le_add_left _ _) i.2 τ
  refine ⟨sig_eq D i τ, ⟨hr, hV⟩, fun a ha => cast_aPlus D i τ ha, fun c hc => aM_cast D i τ hc,
    fun a b hab hb => ?_, fun a b hab hb => ?_, fun a ha => ?_, fun a ha => ?_, fun a => ?_, fun c => ?_, ?_,
    lamPrime_eq D i τ, hL, fun a => ?_⟩
  · rw [← Nat.cast_le (α := ℚ), cast_aPlus D i τ hb, cast_aPlus D i τ (by omega)]
    exact aPlusQ_anti D i τ hab hb
  · rw [← Nat.cast_le (α := ℚ), aM_cast' D i τ hb, aM_cast' D i τ (by omega), neg_le_neg_iff]
    exact dRowQ_anti D i τ (by omega) (by omega)
  · rw [← Nat.cast_le (α := ℚ), cast_aPlus D i τ ha, Nat.cast_one]
    exact one_le_aPlusQ D i τ ha
  · rw [← Nat.cast_le (α := ℚ), aM_cast' D i τ ha, Nat.cast_one]
    exact one_le_neg_dRowQ D i τ (by omega)
  · rw [kapW_cast _ _ _ ho, cast_aPlus D i τ a.2]
    simp only [kapQ, Sum.elim_inl, aPlusQ, centred, hr']; ring
  · rw [kapW_cast _ _ _ ho, aM_cast D i τ c.2]
    simp only [kapQ, Sum.elim_inr, dRowQ, centred, hr']; ring
  · obtain ⟨s, hs⟩ := ho
    have hs' : (qS D i τ : ℚ) = 2 * s + 1 - pS D i τ := by
      have : (pS D i τ : ℚ) + qS D i τ = 2 * s + 1 := by exact_mod_cast hs
      linarith
    obtain ⟨e, he⟩ := (D.hc τ).e_int i
    refine ⟨(pS D i τ : ℕ) - s - 1 - e, ?_⟩
    simp only [dShift, eS, he, hs']
    push_cast; ring
  · obtain ⟨_, w, hk, hm, ht, hj, he, hv, hb, hw⟩ := hL
    rw [hw a]
    exact lamPrime_eq D i τ w ⟨hk, hm, ht, hj, he, hv, hb⟩ a (hV ▸ a.2)

end GlobalTheory.PairWeightArith
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaWeightArithmeticAtPlaceProofStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.JointHarm
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaWeightArithmeticAtPlace_proof : ∀ (D : D7) (i : Fin D.R.m) (τ : D.what₂.Tau), GlobalTheory.IndefiniteRowSideFullHecke.InfinityTypes.ArithAt D i τ := by
  first | exact @GlobalTheory.PairWeightArith.arithAt | exact GlobalTheory.PairWeightArith.arithAt | (intros; apply GlobalTheory.PairWeightArith.arithAt <;> assumption)
end
end
