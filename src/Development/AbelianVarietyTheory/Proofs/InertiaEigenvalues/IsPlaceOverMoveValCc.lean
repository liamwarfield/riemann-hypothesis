module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsIntegralOfNormLeOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachInclusionInjectiveSaturatedInter
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CrysOnCond
public import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypes
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleOfSurjective
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NcardPrimesOverOfStabilizer

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPlaceOverMoveValCc
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.AntiRamConj
open scoped TensorProduct Pointwise

namespace GlobalTheory.TwistDet

section Places

variable {D : Formalism.BasicNotions.D7}

def conjInt (D : Formalism.BasicNotions.D7) : 𝓞 D.host.E ≃+* 𝓞 D.host.E := RingOfIntegers.mapRingEquiv D.host.conj.toRingEquiv

theorem conjInt_coe (x : 𝓞 D.host.E) : ((conjInt D x : 𝓞 D.host.E) : D.host.E) = D.host.conj (x : D.host.E) := rfl

theorem conjInt_conjInt (x : 𝓞 D.host.E) : conjInt D (conjInt D x) = x := by
  apply RingOfIntegers.ext
  rw [conjInt_coe, conjInt_coe, host_conj_conj]

theorem isConjPl_iff {P P' : PlE D.host} :
    IsConjPl D.host P P' ↔ ∀ x, x ∈ P.asIdeal ↔ conjInt D x ∈ P'.asIdeal := by
  constructor
  · intro h x
    exact h x _ rfl
  · intro h x y hxy
    have e : y = conjInt D x := RingOfIntegers.ext hxy
    rw [e, h]

theorem isConjPl_symm {P P' : PlE D.host} (h : IsConjPl D.host P P') : IsConjPl D.host P' P := by
  rw [isConjPl_iff] at h ⊢
  intro x
  rw [h, conjInt_conjInt]

theorem isConjPl_unique {P P' P'' : PlE D.host} (h : IsConjPl D.host P P') (h' : IsConjPl D.host P P'') : P' = P'' := by
  have a := isConjPl_iff.1 (isConjPl_symm h)
  have b := isConjPl_iff.1 (isConjPl_symm h')
  ext x
  rw [a, b]

theorem exists_isConjPl (P : PlE D.host) : ∃ P', IsConjPl D.host P P' := by
  refine ⟨P.comap (conjInt D : 𝓞 D.host.E →+* 𝓞 D.host.E) (conjInt D).surjective, isConjPl_iff.2 fun x => ?_⟩
  change x ∈ P.asIdeal ↔ conjInt D (conjInt D x) ∈ P.asIdeal
  rw [conjInt_conjInt]

theorem ne_of_isSplitPl {P P' : PlE D.host} (hs : IsSplitPl D.host P) (h : IsConjPl D.host P P') : P ≠ P' := by
  rintro rfl
  obtain ⟨x, hx, hy⟩ := hs
  exact hy (conjInt D x) rfl ((isConjPl_iff.1 h x).1 hx)

theorem normV_conj {P P' : PlE D.host} (h : IsConjPl D.host P P') : normV P' = normV P := by
  have e : P'.asIdeal = P.asIdeal.map (conjInt D : 𝓞 D.host.E →+* 𝓞 D.host.E) := by
    ext y
    obtain ⟨x, rfl⟩ := (conjInt D).surjective y
    rw [← isConjPl_iff.1 h]
    exact (Ideal.apply_mem_of_equiv_iff (f := conjInt D)).symm
  exact (Nat.card_congr (Ideal.quotientEquiv _ _ (conjInt D) e).toEquiv).symm

theorem mem_placesOver_conj {P P' : PlE D.host} (h : IsConjPl D.host P P') {p : ℕ}
    (hp : P ∈ placesOver D.host.E p) : P' ∈ placesOver D.host.E p := by
  have := (isConjPl_iff.1 h (p : 𝓞 D.host.E)).1 hp
  rwa [map_natCast] at this

theorem over_refl (P : PlE D.host) : Over P P := Or.inl rfl

theorem over_symm {P v : PlE D.host} (h : Over P v) : Over v P :=
  h.elim (fun e => Or.inl e.symm) fun c => Or.inr (isConjPl_symm c)

theorem over_trans {P v w : PlE D.host} (h : Over P v) (h' : Over v w) : Over P w := by
  rcases h with rfl | h
  · exact h'
  · rcases h' with rfl | h'
    · exact Or.inr h
    · exact Or.inl (isConjPl_unique h' (isConjPl_symm h))

end Places

section Galois

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} (X : NTw D.R D.host D.what₂ D.LL0 N)

theorem cc_algebraMap (x : D.host.E) :
    X.cc (algebraMap D.host.E N.Om x) = algebraMap D.host.E N.Om (D.host.conj x) := by
  obtain ⟨j, hj⟩ := X.cc_cm.1
  apply j.injective
  rw [hj]
  exact (D.host.conjE_apply (j.comp (algebraMap D.host.E N.Om)) x).symm

theorem cc_cc (x : N.Om) : X.cc (X.cc x) = x := by
  obtain ⟨j, hj⟩ := X.cc_cm.1
  apply j.injective
  rw [hj, hj, Complex.conj_conj]

theorem cc_symm (x : N.Om) : X.cc.symm x = X.cc x := by
  rw [RingEquiv.symm_apply_eq, cc_cc]

theorem cc_symm_mem (x : D.host.E) : ∃ y : D.host.E,
    X.cc.symm (algebraMap D.host.E N.Om x) = algebraMap D.host.E N.Om y :=
  ⟨_, by rw [cc_symm, cc_algebraMap]⟩

def cConj : GE N →* GE N where
  toFun := conjAut X.cc (cc_symm_mem X)
  map_one' := by
    ext x
    exact X.cc.apply_symm_apply x
  map_mul' g h := by
    ext x
    change X.cc (g (h (X.cc.symm x))) = X.cc (g (X.cc.symm (X.cc (h (X.cc.symm x)))))
    rw [RingEquiv.symm_apply_apply]

theorem cConj_apply (g : GE N) (x : N.Om) : cConj X g x = X.cc (g (X.cc.symm x)) := rfl

theorem cConj_cConj (g : GE N) : cConj X (cConj X g) = g := by
  ext x
  rw [cConj_apply, cConj_apply, cc_cc, cc_symm, cc_symm, cc_cc]

theorem antiHom_cConj {A : Type} [CommGroup A] {φ : GE N →* A} (h : AntiHom X.cc φ) (g : GE N) :
    φ (cConj X g) = (φ g)⁻¹ := h g _ (cConj_apply X g)

theorem isPlaceOver_moveVal_cc {P P' : PlE D.host} (h : IsConjPl D.host P P') {B : ValuationSubring N.Om}
    (hB : IsPlaceOver B P) : IsPlaceOver (moveVal X.cc B) P' := by
  intro y
  rw [moveVal_lt_one, cc_symm, cc_algebraMap, ← conjInt_coe, hB]
  exact (isConjPl_iff.1 (isConjPl_symm h) y).symm

theorem cConj_mem_ine {B : ValuationSubring N.Om} {σ : GE N} (hσ : σ ∈ Ine (F := D.host.E) B) :
    cConj X σ ∈ Ine (F := D.host.E) (moveVal X.cc B) := conjAut_mem_ine X.cc (cc_symm_mem X) hσ

theorem isFrob_cConj {B : ValuationSubring N.Om} {q : ℕ} {σ : GE N} (hσ : IsFrob B q σ) :
    IsFrob (moveVal X.cc B) q (cConj X σ) := by
  have hd : σ ∈ Dec (F := D.host.E) B := hσ.1
  refine ⟨?_, fun x hx => ?_⟩
  · show cConj X σ ∈ Dec (F := D.host.E) (moveVal X.cc B)
    rw [mem_Dec]
    ext x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def]
    obtain ⟨z, rfl⟩ := (cConj X σ).surjective x
    have h1 : ((cConj X σ)⁻¹ : GE N) (cConj X σ z) = z := (cConj X σ).symm_apply_apply z
    rw [h1, mem_moveVal, mem_moveVal, cConj_apply, RingEquiv.symm_apply_apply, apply_mem_iff_of_mem_Dec hd]
  · rw [moveVal_lt_one, map_sub, cConj_apply, RingEquiv.symm_apply_apply, map_pow]
    apply hσ.2
    rw [ValuationSubring.valuation_le_one_iff] at hx ⊢
    exact hx

theorem isFrob_smul {B : ValuationSubring N.Om} {q : ℕ} {σ : GE N} (hσ : IsFrob B q σ) (g : GE N) :
    IsFrob (g • B) q (g * σ * g⁻¹) := by
  have hd : σ • B = B := hσ.1
  have hm : ∀ y : N.Om, y ∈ g • B ↔ (g⁻¹ : GE N) y ∈ B := fun y => by
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def]
  refine ⟨?_, fun x hx => ?_⟩
  · show (g * σ * g⁻¹) • g • B = g • B
    rw [← mul_smul, inv_mul_cancel_right, mul_smul, hd]
  · rw [ValuationSubring.valuation_le_one_iff, hm] at hx
    have h2 := hσ.2 _ ((B.valuation_le_one_iff _).2 hx)
    have e : (g⁻¹ : GE N) ((g * σ * g⁻¹) x - x ^ q) = σ ((g⁻¹ : GE N) x) - ((g⁻¹ : GE N) x) ^ q := by
      rw [map_sub, map_pow, ← AlgEquiv.mul_apply, mul_assoc, inv_mul_cancel_left, AlgEquiv.mul_apply]
    rw [valuation_lt_one_iff'] at h2 ⊢
    rw [hm, hm, map_inv₀, ← map_eq_zero_iff (g⁻¹ : GE N) (g⁻¹ : GE N).injective, e]
    exact h2

theorem exists_frob_of_conj {P P' : PlE D.host} (h : IsConjPl D.host P P') {σ : GE N}
    (hσ : IsFrob (N.plOm.1 P') (normV P') σ) :
    ∃ σ₀ g : GE N, IsFrob (N.plOm.1 P) (normV P) σ₀ ∧ σ = g * cConj X σ₀ * g⁻¹ := by
  have h1 := isFrob_cConj X hσ
  have h2 := isPlaceOver_moveVal_cc X (isConjPl_symm h) (N.plOm.2 P')
  obtain ⟨g, hg⟩ := exists_smul_eq_of_isPlaceOver (F := D.host.E) h2 (N.plOm.2 P)
  have h3 := isFrob_smul h1 g
  rw [hg, normV_conj h] at h3
  refine ⟨_, (cConj X g)⁻¹, h3, ?_⟩
  rw [map_mul, map_mul, map_inv, cConj_cConj]
  group

theorem isOpen_comap_cConj {H : Subgroup (GE N)} (hH : IsOpen (H : Set (GE N))) :
    IsOpen ((H.comap (cConj X) : Subgroup (GE N)) : Set (GE N)) := by
  obtain ⟨L, hL, hLH⟩ := (krullTopology_mem_nhds_one_iff D.host.E N.Om (H : Set (GE N))).1 (hH.mem_nhds H.one_mem)
  obtain ⟨S, hS⟩ := IntermediateField.fg_of_fg_toSubalgebra L (Subalgebra.fg_of_fg_toSubmodule
    ((Submodule.fg_iff_finiteDimensional L.toSubalgebra.toSubmodule).2 hL))
  classical
  let L' := IntermediateField.adjoin D.host.E ((S.image X.cc.symm : Finset N.Om) : Set N.Om)
  have hL' : FiniteDimensional D.host.E L' :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  refine Subgroup.isOpen_mono (H₁ := L'.fixingSubgroup) (fun g hg => ?_) (IntermediateField.fixingSubgroup_isOpen L')
  apply hLH
  rw [IntermediateField.mem_fixingSubgroup_iff] at hg
  have : L ≤ IntermediateField.fixedField (Subgroup.zpowers (cConj X g)) := by
    rw [← hS, IntermediateField.adjoin_le_iff]
    intro x hx
    rw [SetLike.mem_coe, IntermediateField.mem_fixedField_iff]
    intro f hf
    have h1 : cConj X g x = x := by
      rw [cConj_apply, hg _ (IntermediateField.subset_adjoin _ _ (by simpa using hx)), RingEquiv.apply_symm_apply]
    exact (Subgroup.zpowers_le (H := MulAction.stabilizer (GE N) x)).2 h1 hf
  rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  exact (IntermediateField.mem_fixedField_iff _ _).1 (this hx) _ (Subgroup.mem_zpowers _)

end Galois

end GlobalTheory.TwistDet

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachInclusionXQFrobenius
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachInclusionXQFrobenius
noncomputable section

namespace GlobalTheory.NL.IoXQ

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL PowerSeries

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem q_eq (W : LocWach PD LL O v n) : W.q = ∑ i ∈ Finset.range PD.p, (1 + letπ) ^ i := by
  funext j
  have h : (X : O⟦X⟧) * W.q₀ = X * ∑ i ∈ Finset.range PD.p, (1 + X) ^ i := by
    rw [W.q₀_def, ← geom_sum_mul, add_sub_cancel_left, mul_comm]
  have h2 := PowerSeries.X_mul_cancel h
  simpa [LocWach.q, letπ, Finset.sum_apply] using h2

theorem φA_one_add (W : LocWach PD LL O v n) : W.φA (1 + letπ) = (1 + letπ) ^ PD.p := by
  rw [map_add (f := _), map_one, W.φA_π, q_eq]
  linear_combination geom_sum_mul (1 + (letπ : LetA O n)) PD.p

theorem φA_pow_one_add (W : LocWach PD LL O v n) (k : ℕ) :
    (W.φA ^ k) (1 + letπ) = (1 + letπ) ^ (PD.p ^ k) := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', AlgHom.mul_apply, ih, map_pow, φA_one_add, ← pow_mul, pow_succ']

theorem X_eq (W : LocWach PD LL O v n) : W.X = (1 + letπ) ^ (PD.p ^ (W.s - 1)) - 1 := by
  rw [← φA_pow_one_add W, map_add (f := _), map_one, add_sub_cancel_left, LocWach.X]

theorem Q_eq (W : LocWach PD LL O v n) :
    W.Q = ∑ i ∈ Finset.range PD.p, ((1 + letπ) ^ (PD.p ^ (W.s - 1))) ^ i := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [LocWach.Q, q_eq, map_sum]
  simp only [map_pow, φA_pow_one_add]

theorem isUnit_φA_pow (W : LocWach PD LL O v n) {a : LetA O n} (ha : IsUnit (algebraMap _ W.EE a)) (k : ℕ) :
    IsUnit (algebraMap _ W.EE ((W.φA ^ k) a)) := by
  induction k with
  | zero => simpa using ha
  | succ k ih =>
    rw [pow_succ', AlgHom.mul_apply, LocWach.φA, ← W.φE_ext]
    exact ih.map W.φE

theorem isUnit_X (W : LocWach PD LL O v n) : IsUnit (algebraMap _ W.EE W.X) :=
  isUnit_φA_pow W W.EE_π _

theorem isUnit_Q (W : LocWach PD LL O v n) : IsUnit (algebraMap _ W.EE W.Q) := by
  have h := isUnit_φA_pow W (isUnit_X W) 1
  rw [pow_one, W.φA_X, map_mul] at h
  exact isUnit_of_mul_isUnit_right h

variable {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}

theorem ioE_φ (hO : Function.Injective (algebraMap O LL)) {W : LocWach PD LL O v n}
    (E : EtTie W RA RW inclR φR gR πA) (x : W.EE) : E.ioE (W.φE x) = φR (E.ioE x) := by
  obtain ⟨e, e₀, hspan, hj, -⟩ := E.one_e
  obtain ⟨e₁, he₁, hT⟩ := W.one_line
  have he₀ : (e₀ : W.one.V) ≠ 0 := by
    intro h
    have hm : e₁ ∈ W.one.L.T := hT ▸ Submodule.mem_span_singleton_self e₁
    have h1 : (⟨e₁, hm⟩ : W.one.L.T) ∈ Submodule.span O {e₀} := hspan ▸ Submodule.mem_top
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 h1
    apply he₁
    have := congrArg Subtype.val hc
    simpa [h] using this.symm
  have hinj : Function.Injective (LinearMap.toSpanSingleton O W.one.L.T e₀) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro c hc
    have h1 : c • (e₀ : W.one.V) = 0 := congrArg Subtype.val hc
    rw [← algebraMap_smul LL, smul_eq_zero] at h1
    exact hO ((h1.resolve_right he₀).trans (map_zero _).symm)
  have hsurj : Function.Surjective (LinearMap.toSpanSingleton O W.one.L.T e₀) := by
    rw [← LinearMap.range_eq_top, ← LinearMap.span_singleton_eq_range, hspan]
  obtain ⟨f, hf⟩ : ∃ f : W.one.L.T ≃ₗ[O] O, f e₀ = 1 :=
    ⟨(LinearEquiv.ofBijective _ ⟨hinj, hsurj⟩).symm, (LinearEquiv.symm_apply_eq _).2 (one_smul O e₀).symm⟩
  have h1 := E.jD_φ W.one (x • e)
  rw [W.φD_smul, E.jD_smul, E.jD_smul, E.jD_φ, hj] at h1
  simp only [TWmap, TensorProduct.smul_tmul', smul_eq_mul, mul_one, TensorProduct.map_tmul,
    AlgHom.toLinearMap_apply, map_one, LinearMap.id_apply] at h1
  have h2 := congrArg (fun z => TensorProduct.rid O RW (LinearMap.lTensor RW f.toLinearMap z)) h1
  simpa [hf] using h2

theorem io_X_gen {W : LocWach PD LL O v n} (E : EtTie W RA RW inclR φR gR πA) :
    E.io W.X = (1 + πA) ^ (PD.p ^ (W.s - 1)) - 1 := by
  rw [X_eq, map_sub, map_pow, map_add (f := _), map_one, E.io_π]

theorem io_Q_gen {W : LocWach PD LL O v n} (E : EtTie W RA RW inclR φR gR πA) :
    E.io W.Q = ∑ i ∈ Finset.range PD.p, ((1 + πA) ^ (PD.p ^ (W.s - 1))) ^ i := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Q_eq, map_sum]
  simp only [map_pow, map_add (f := _), map_one, E.io_π]

end Generic

theorem tmul_X {Z O A : Type} [CommRing Z] [CommRing O] [CommRing A] [Algebra Z O] [Algebra Z A]
    (t u : A) (m : ℕ) (h : t ^ m = u) :
    (1 + (1 : O) ⊗ₜ[Z] (t - 1)) ^ m - 1 = (1 : O) ⊗ₜ[Z] (u - 1) := by
  rw [Algebra.TensorProduct.one_def, ← TensorProduct.tmul_add, add_sub_cancel,
    Algebra.TensorProduct.tmul_pow, one_pow, h, TensorProduct.tmul_sub]

theorem tmul_Q {Z O A : Type} [CommRing Z] [CommRing O] [CommRing A] [Algebra Z O] [Algebra Z A]
    (t u : A) (m p : ℕ) (h : t ^ m = u) :
    ∑ i ∈ Finset.range p, ((1 + (1 : O) ⊗ₜ[Z] (t - 1)) ^ m) ^ i = (1 : O) ⊗ₜ[Z] (∑ i ∈ Finset.range p, u ^ i) := by
  rw [Algebra.TensorProduct.one_def, ← TensorProduct.tmul_add, add_sub_cancel,
    Algebra.TensorProduct.tmul_pow, one_pow, h, TensorProduct.tmul_sum]
  simp only [Algebra.TensorProduct.tmul_pow, one_pow]

theorem εroot_pow {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P) (k : ℕ) :
    AI.εroot (k + 1) ^ (l ^ k) = AI.ε1 := by
  induction k with
  | zero => simp [LocAinf.εroot, LocAinf.ε1]
  | succ k ih =>
    rw [pow_succ', pow_mul, ← ih]
    congr 1
    rw [LocAinf.εroot, Function.iterate_succ_apply', frobeniusEquiv_symm_pow_p]
    rfl

section Concrete

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} {K : FinExt l} {LL : FinExt l}
  {W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) (Module.finrank ℚ_[l] ↥(K0 K))} {s : ℕ}
  (E : EtTie W (RA LL) (RW LL) (inclR LL) (φRW LL) (fun g : ↥(GK K) => AI.gRW LL (g : GQ l))
    ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] (WittVector.teichmuller l (AI.εroot s) - 1)))

omit E in
theorem teich_pow (hs : W.s = s) : WittVector.teichmuller l (AI.εroot s) ^ ((P.PD K).p ^ (W.s - 1)) =
    WittVector.teichmuller l AI.ε1 := by
  obtain ⟨k, hk⟩ : ∃ k, s = k + 1 := ⟨s - 1, by have := W.s_pos; omega⟩
  rw [← map_pow, P.PD_p K, hs, hk, Nat.add_sub_cancel, εroot_pow]

theorem io_X (hs : W.s = s) : E.io W.X = (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] AI.π₁ :=
  (io_X_gen E).trans (tmul_X _ _ _ (teich_pow hs))

theorem io_Q (hs : W.s = s) : E.io W.Q = (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] AI.ξ :=
  ((io_Q_gen E).trans (tmul_Q _ _ _ _ (teich_pow hs))).trans
    (congrArg (fun p => (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] ∑ i ∈ Finset.range p, (WittVector.teichmuller l AI.ε1) ^ i)
      (P.PD_p K))

theorem ioE_φ' (x : W.EE) : E.ioE (W.φE x) = φRW LL (E.ioE x) :=
  ioE_φ Subtype.val_injective E x

theorem incl_io_φ (a : AA K LL) : inclR LL (E.io (W.φA a)) = φRW LL (inclR LL (E.io a)) :=
  ((E.ioE_ext _).symm.trans (congrArg E.ioE (W.φE_ext a).symm)).trans
    ((ioE_φ' E _).trans (congrArg (φRW LL) (E.ioE_ext a)))


open GlobalTheory.IoInj in
set_option maxHeartbeats 1000000 in
theorem ioE_inj_inter : Function.Injective E.ioE ∧
      ∀ x : W.EE, (∃ y, inclR LL y = E.ioE x) → ∃ a : AA K LL, algebraMap _ W.EE a = x := by
  set_option synthInstance.maxHeartbeats 200000 in
    classical
    obtain ⟨_, hc, hl0, hlu, hfree, -, -⟩ := GlobalTheory.Per.integers_completeDVR l LL
    obtain ⟨hWc, hWtf, -, hsat, hμ⟩ := GlobalTheory.HWL.TensorWitt.main l LL
    haveI : FiniteDimensional ℚ_[l] K.1 := K.2
    haveI : FiniteDimensional ℚ_[l] (K0 K) :=
      Module.Finite.of_injective (IntermediateField.inclusion (inf_le_left : K0 K ≤ K.1)).toLinearMap
        (IntermediateField.inclusion_injective (inf_le_left : K0 K ≤ K.1))
    haveI : NeZero (Module.finrank ℚ_[l] (K0 K)) := ⟨Module.finrank_pos.ne'⟩
    haveI : Nontrivial (RW LL) := Module.FaithfullyFlat.lTensor_nontrivial ℤ_[l] ↥(OL LL) (WCb l)
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible ↥(OL LL)
    obtain ⟨N, hN⟩ := IsDiscreteValuationRing.associated_pow_irreducible hl0 hϖ
    obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := by
      rcases N with _ | n
      · exact absurd (by simpa using hN) hlu
      · exact ⟨n, rfl⟩
    obtain ⟨u, hu⟩ := hN.symm
    have hm : IsLocalRing.maximalIdeal ↥(OL LL) = Ideal.span {ϖ} := hϖ.maximalIdeal_eq
    have hO : ∀ a : ↥(OL LL), IsUnit a ∨ ϖ ∣ a := by
      intro a
      by_cases h : IsUnit a
      · exact Or.inl h
      · right
        rw [← Ideal.mem_span_singleton, ← hm]
        exact h
    have hOp : ∀ a : ℕ → ↥(OL LL), (∀ k k', k ≤ k' → (l : ↥(OL LL)) ^ k ∣ a k - a k') →
        ∃ L, ∀ k, (l : ↥(OL LL)) ^ k ∣ a k - L := by
      intro a ha
      have hiff : ∀ (k : ℕ) (x y : ↥(OL LL)),
          x ≡ y [SMOD (IsLocalRing.maximalIdeal ↥(OL LL) ^ k • ⊤ : Submodule ↥(OL LL) ↥(OL LL))] ↔ ϖ ^ k ∣ x - y := by
        intro k x y
        rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, hm, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
      obtain ⟨L, hL⟩ := IsPrecomplete.prec hc.toIsPrecomplete (f := a) (by
        intro k k' hk
        rw [hiff]
        refine (pow_dvd_pow_of_dvd ?_ k).trans (ha k k' hk)
        exact ⟨ϖ ^ n * u, by rw [← hu]; ring⟩)
      refine ⟨L, fun k => ?_⟩
      have h1 := (hiff _ _ _).mp (hL ((n + 1) * k))
      have h2 : (l : ↥(OL LL)) ^ k ∣ ϖ ^ ((n + 1) * k) := by
        rw [pow_mul]
        exact pow_dvd_pow_of_dvd hN.dvd k
      have : a k - L = (a k - a ((n + 1) * k)) + (a ((n + 1) * k) - L) := by ring
      rw [this]
      exact dvd_add (ha _ _ (by nlinarith)) (h2.trans h1)
    have hp := P.PD_p K
    have hE := W.EE_complete
    have hdense := W.EE_dense
    have hEsat := W.EE_sat
    rw [hp] at hE hdense hEsat
    refine (fun h => ⟨h.1, h.2.2.2⟩) (abstract (algebraMap _ W.EE) E.ioE.toRingHom E.io.toRingHom
      (inclR LL).toRingHom E.ioE_ext l
      (fun _ => C ϖ) letπ (fun _ => C (u : ↥(OL LL))) n
      (Pi.isUnit_iff.mpr fun _ => u.isUnit.map C) ?_ (fun i => Pi.single i 1) ?_ ?_
      (letter_form ϖ hO) (prec_pi l hOp) W.EE_π hE (fun x => hdense x 1) hEsat
      (IsAdicComplete.le_jacobson_bot _ (Ideal.mem_span_singleton_self _)) hWtf hsat ?_ ?_)
    · funext i
      have := congrArg (C : ↥(OL LL) →+* _) hu
      rw [map_natCast, map_mul, map_pow] at this
      simp only [Pi.natCast_apply, Pi.mul_apply, Pi.pow_apply, ← this]
      ring
    · intro i
      rw [← Pi.single_mul, mul_one]
    · exact Finset.univ_sum_single (1 : LetA ↥(OL LL) _)
    · haveI := hμ _ (not_isUnit_εroot_sub_one AI s)
      change E.io letπ ∈ _
      rw [E.io_π]
      exact IsAdicComplete.le_jacobson_bot _ (Ideal.mem_span_singleton_self _)
    · exact idem_ne_zero (algebraMap _ W.EE) E.ioE.toRingHom W.φ₀ W.φE (φRW LL) (map_zero _) W.φE_ext (ioE_φ' E)

end Concrete

theorem main : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; E.io W.X = (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] (D.locA l).π₁ ∧ E.io W.Q = (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] (D.locA l).ξ ∧ Function.Injective (inclR LL) ∧ Function.Injective E.ioE ∧ (∀ a, inclR LL (E.io (W.φA a)) = φRW LL (inclR LL (E.io a))) ∧ (∀ x : W.EE, (∃ y, inclR LL y = E.ioE x) → ∃ a : AA K LL, algebraMap _ W.EE a = x) ∧ ∀ j : ℕ, IsUnit (algebraMap (AA K LL) W.EE ((W.φA ^ j) W.X)) ∧ IsUnit (algebraMap (AA K LL) W.EE ((W.φA ^ j) W.Q)) := by
  intro D HW F l _ K s LL h W E
  have hs : W.s = s := (HW l).W_s K s LL h
  exact ⟨io_X E hs, io_Q E hs, (GlobalTheory.HWL.TensorWitt.main l LL).2.2.1, (ioE_inj_inter E).1, incl_io_φ E,
    (ioE_inj_inter E).2, fun j => ⟨isUnit_φA_pow W (isUnit_X W) j, isUnit_φA_pow W (isUnit_Q W) j⟩⟩

end GlobalTheory.NL.IoXQ
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachInclusionXQFrobeniusStatement
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wachInclusion_X_Q_frobenius : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; E.io W.X = (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] (D.locA l).π₁ ∧ E.io W.Q = (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] (D.locA l).ξ ∧ Function.Injective (inclR LL) ∧ Function.Injective E.ioE ∧ (∀ a, inclR LL (E.io (W.φA a)) = φRW LL (inclR LL (E.io a))) ∧ (∀ x : W.EE, (∃ y, inclR LL y = E.ioE x) → ∃ a : AA K LL, algebraMap _ W.EE a = x) ∧ ∀ j : ℕ, IsUnit (algebraMap (AA K LL) W.EE ((W.φA ^ j) W.X)) ∧ IsUnit (algebraMap (AA K LL) W.EE ((W.φA ^ j) W.Q)) := by
  first | exact @GlobalTheory.NL.IoXQ.main | exact GlobalTheory.NL.IoXQ.main | (intros; apply GlobalTheory.NL.IoXQ.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameDescentConditionsEveryLocalisation
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

namespace GlobalTheory.TameDesign
open scoped Pointwise

private theorem wild_mem_Ine {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    {A : ValuationSubring Ω} {σ : Formalism.ConjugateSelfDual.G E Ω}
    (hσ : ∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1) : σ ∈ Ine (F := E) A := _root_.GlobalTheory.TameGenPowers.wild_mem_Ine (E := E) (Ω := Ω) (A := A) (σ := σ) hσ

section General

variable {Γ R : Type} [Group Γ] [CommRing R]

private theorem mem_ker_char_iff (J : Ideal R) (χ : Γ →* Rˣ) (g : Γ) :
    g ∈ ((Units.map (Ideal.Quotient.mk J).toMonoidHom).comp χ).ker ↔ ((χ g : Rˣ) : R) - 1 ∈ J := by
  rw [MonoidHom.mem_ker, Units.ext_iff, ← Ideal.Quotient.eq]
  rfl

private theorem isOpen_ker_char [TopologicalSpace Γ] [TopologicalSpace R] [IsTopologicalRing R]
    (J : Ideal R) (hJ : IsOpen (J : Set R)) (χ : Γ →* Rˣ)
    (hχ : Continuous fun g => ((χ g : Rˣ) : R)) :
    IsOpen (((Units.map (Ideal.Quotient.mk J).toMonoidHom).comp χ).ker : Set Γ) := by
  have : (((Units.map (Ideal.Quotient.mk J).toMonoidHom).comp χ).ker : Set Γ) =
      (fun g => ((χ g : Rˣ) : R) - 1) ⁻¹' (J : Set R) := by
    ext g
    simp only [SetLike.mem_coe, mem_ker_char_iff, Set.mem_preimage]
  rw [this]
  exact hJ.preimage (hχ.sub continuous_const)

end General

section Wild

variable {E Ω R : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [TopologicalSpace R] [IsTopologicalRing R]
  {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 E)}

omit [TopologicalSpace R] [IsTopologicalRing R] in
private theorem eq_zero_of_mem_pow (x : R) (h : ∀ m, x ∈ IsLocalRing.maximalIdeal R ^ (m + 1)) : x = 0 := by
  rw [← Ideal.mem_bot, ← Ideal.iInf_pow_eq_bot_of_isLocalRing (IsLocalRing.maximalIdeal R)
    (IsLocalRing.maximalIdeal.isMaximal R).ne_top, Ideal.mem_iInf]
  exact fun m => Ideal.pow_le_pow_right (Nat.le_succ m) (h m)

private theorem char_eq_one_of_wild (hR : IsAdic (IsLocalRing.maximalIdeal R)) (hA : IsPlaceOver A v) (n : ℕ)
    (hv : ((n : ℕ) : 𝓞 E) ∉ v.asIdeal) (χ : Formalism.ConjugateSelfDual.G E Ω →* Rˣ) (hχ : Continuous fun g => ((χ g : Rˣ) : R))
    (σ : Formalism.ConjugateSelfDual.G E Ω) (hσ : ∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1) (h1 : χ σ ^ n = 1) : χ σ = 1 := by
  rw [Units.ext_iff, Units.val_one, ← sub_eq_zero]
  refine eq_zero_of_mem_pow _ fun m => ?_
  rw [← mem_ker_char_iff]
  refine GlobalTheory.mem_of_wild_of_pow_mem_open_normal E Ω A v hA _ inferInstance
    (isOpen_ker_char _ ((isAdic_iff.mp hR).1 _) χ hχ) σ n hv hσ ?_
  rw [mem_ker_char_iff, map_pow, h1]
  simp

end Wild

theorem firstLocalChar_wild_eq_one_away_from_l (D : D7) (i : D.nd.Loc) (v : HeightOneSpectrum (𝓞 D.host.E))
    (hvl : v ∉ placesOver D.host.E (D.nd.l i)) (σ : GE D.nd) (hσ : σ ∈ wildSet D.nd (D.nd.plOm.1 v)) :
    D.nd.chi i 1 σ = 1 := by
  have hA : IsPlaceOver (D.nd.plOm.1 v) v := D.nd.plOm.2 v
  have hI : σ ∈ Ine (F := D.host.E) (D.nd.plOm.1 v) := wild_mem_Ine hσ
  have hvl' : v ∉ placesOver D.host.E (D.ntw.l (D.ntw.twOf i)) := by rwa [D.ntw.twOf_l]

  have hψ : D.ntw.psiL i σ = 1 := by
    obtain ⟨n, hn⟩ := D.ntw.psiL_ord i σ
    have hmem := GlobalTheory.mem_of_wild_of_pow_mem_open_normal _ _ (D.nd.plOm.1 v) v hA (D.ntw.psiL i).ker
      inferInstance (D.ntw.psiL_open i) σ (D.nd.l i ^ n) ?_ hσ (by rw [MonoidHom.mem_ker, map_pow, hn])
    · exact hmem
    · intro h
      apply hvl
      have hp : (D.nd.l i).Prime := Fact.out
      exact v.isPrime.mem_of_pow_mem n (by simpa using h)

  have hc : D.ntw.chi1 (D.ntw.twOf i) (D.nd.j i) (D.ntw.twSide i) σ = 1 := by
    by_cases hpD : v ∈ D.ntw.pD (D.ntw.twOf i)
    · have h15 := D.ntw.delta_15 (D.ntw.twOf i) v hpD _ hA
      have hd : D.ntw.delta (D.ntw.twOf i) σ ^ 15 = 1 := by
        have h := pow_card_eq_one'
          (G := (Ine (F := D.host.E) (D.nd.plOm.1 v)).map (D.ntw.delta (D.ntw.twOf i)))
          (x := ⟨_, σ, hI, rfl⟩)
        rw [h15] at h
        exact congrArg Subtype.val h
      have h15v : ((15 : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal := by
        intro h
        have hN := D.ntw.delta_tame (D.ntw.twOf i) v hpD
        have hm : ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 D.host.E) ∈ v.asIdeal := Ideal.absNorm_mem _
        have e : Ideal.absNorm v.asIdeal = 15 * (Ideal.absNorm v.asIdeal / 15) + 1 := by omega
        rw [e] at hm
        push_cast at hm
        have h1 : (1 : 𝓞 D.host.E) ∈ v.asIdeal := by
          have := v.asIdeal.sub_mem hm (v.asIdeal.mul_mem_right (((Ideal.absNorm v.asIdeal / 15 : ℕ)) : 𝓞 D.host.E) (by simpa using h))
          simpa using this
        exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1)
      refine char_eq_one_of_wild (D.ntw.twistBaseCoefficientRing_isAdic _) hA 15 h15v _
        (D.ntw.twistCharacterFamily_continuous _ _ _) σ hσ ?_
      rw [D.ntw.twistCharacterFamily_at_auxiliaryPlaces _ _ _ v hpD _ hA σ hI]
      split_ifs
      · exact hd
      · rw [inv_pow, hd, inv_one]
    · by_cases hg : ∃ k, v ∈ placesOver D.host.E (D.host.g k)
      · obtain ⟨k, hvg⟩ := hg
        have hg1 : ((D.host.g k - 1 : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal := fun hm => by
          refine v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr ?_)
          have := v.asIdeal.sub_mem hvg hm
          rwa [Nat.cast_sub (D.host.g_prime k).one_le, Nat.cast_one, sub_sub_cancel] at this
        exact char_eq_one_of_wild (D.ntw.twistBaseCoefficientRing_isAdic _) hA _ hg1 _
          (D.ntw.twistCharacterFamily_continuous _ _ _) σ hσ (D.ntw.twistCharacterFamily_tame _ _ _ k v hvg hvl' _ hA σ hI)
      · push_neg at hg
        exact D.ntw.twistCharacterFamily_unramified _ _ _ v hvl' hg hpD _ hA σ hI
  rw [D.ntw.chi_tw i]
  simp [hψ, hc]

theorem main : ∀ (D : D7) (i : D.nd.Loc), TameCharacterConditions D i ∧ TruncatedSeriesCountingIdentities.TameGeneratorConditions (D := D) i := by
  intro D i
  have hc : TameCharacterConditions D i := by
    refine ⟨fun v hv σ hσ => GlobalTheory.TameDesign.firstLocalChar_wild_eq_one_away_from_l D i v ?_ σ hσ, Formalism.MainNotions.SumRepresentations.Del_holds D i⟩
    rcases hv with hQ | ⟨hS, -⟩
    · exact D.nd.SQ_l i v (Or.inr hQ)
    · exact D.nd.SQ_l i v (Or.inl hS)
  exact ⟨hc, galois_condition_five_extra_of D i hc⟩

end GlobalTheory.TameDesign
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AmbientFiltrationEveryDeclaration
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AmbientFiltrationEveryDeclaration
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.Per.AmbFil

theorem filCount_at (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) {n : ℕ}
    (M : Br.G D.nbr i w hw →* Matrix (Fin n) (Fin n) ↥C.LL.1) :
    EmbeddingTypes.FilCount (Br.PD D.loc D.nbr i w hw) (matRep M) := by
  intro τ J hJ
  exact GlobalTheory.Per.FilCount.fil_count (D.nd.l i) (D.loc (D.nd.l i)) (D.locA (D.nd.l i)) (D.locT (D.nd.l i))
    (D.nbr i w hw).Kw C.LL _ (matRep M) τ J hJ

theorem main : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (dc : TruncatedSeriesCountingIdentities.Decl D i), EmbeddingTypes.ambFil (D := D) i r ρ π dc := by
  intro D i r ρ π dc
  exact ⟨fun w hw _ C x => filCount_at D i w hw C _,
    fun _ => ⟨fun w hw _ C => filCount_at D i w hw C _, fun w hw _ C => filCount_at D i w hw C _⟩⟩

end GlobalTheory.Per.AmbFil
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AmbientFiltrationEveryDeclarationStatement
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ambientFiltration_every_declaration : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (dc : TruncatedSeriesCountingIdentities.Decl D i), EmbeddingTypes.ambFil (D := D) i r ρ π dc := by
  first | exact @GlobalTheory.Per.AmbFil.main | exact GlobalTheory.Per.AmbFil.main | (intros; apply GlobalTheory.Per.AmbFil.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RatioInvariantInK0
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RatioInvariantInK0
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct

namespace GlobalTheory.Per.FracInv

theorem tied_frac_invariant : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI →
    ∀ (K : FinExt l) (a b : P.R.B), b ≠ 0 → (∀ g ∈ GK K, P.actQ g a * b = a * P.actQ g b) →
      ∃ c : ↥(K0 K), a = algebraMap ↥(K0 K) P.R.B c * b := by
  intro l _ P AI T K a b hb h
  have hF : IsField P.R.BdR := GlobalTheory.Per.FontaineBound.isField_of_tied T
  have h' : ∀ g, b * (P.PD K).actB g a = (P.PD K).actB g b * a := by
    intro g
    have := h g.1 g.2
    rw [P.PD_actB, P.PD_actB, mul_comm, this, mul_comm]
  obtain ⟨c, hc⟩ := GlobalTheory.Per.FontaineBound.frac_dR (P.PD K) hF ((P.PD K).ι b) ((P.PD K).ι a)
    (fun h0 => hb ((P.PD K).ι_inj (h0.trans (map_zero _).symm)))
    (fun g => by rw [← (P.PD K).ι_comm, ← (P.PD K).ι_comm, ← map_mul, ← map_mul, h' g])
  have hcU : (c : Om l) ∈ MaximalUnramifiedExtension l := by
    refine GlobalTheory.FracAlg.mem_Kur_of_ratio l P AI T a b (c : Om l) hb ?_
    have h1 := hc
    rw [P.PD_ι, P.PD_ι] at h1
    exact h1
  refine ⟨⟨c, c.2, hcU⟩, (P.PD K).ι_inj ?_⟩
  rw [map_mul, AlgHom.commutes, hc]
  rfl

end GlobalTheory.Per.FracInv
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RatioInvariantInK0Statement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ratio_invariant_in_K0 : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (a b : P.R.B), b ≠ 0 → (∀ g ∈ GK K, P.actQ g a * b = a * P.actQ g b) → ∃ c : ↥(K0 K), a = algebraMap ↥(K0 K) P.R.B c * b := by
  first | exact @GlobalTheory.Per.FracInv.tied_frac_invariant | exact GlobalTheory.Per.FracInv.tied_frac_invariant | (intros; apply GlobalTheory.Per.FracInv.tied_frac_invariant <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameInertiaElementActsByScalar
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameInertiaElementActsByScalar
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys
open scoped TensorProduct

namespace GlobalTheory.TwSys.TameScalar

theorem not_mem_placesOver {E : Type} [Field E] [NumberField E] {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h : p ≠ q)
    {v : HeightOneSpectrum (𝓞 E)} (hv : v ∈ placesOver E p) : v ∉ placesOver E q := by
  intro hv'
  have hc : IsCoprime ((p : ℕ) : 𝓞 E) ((q : ℕ) : 𝓞 E) := Nat.Coprime.cast ((Nat.coprime_primes hp hq).2 h)
  obtain ⟨a, b, hab⟩ := hc
  apply v.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← hab]
  exact v.asIdeal.add_mem (v.asIdeal.mul_mem_left _ hv) (v.asIdeal.mul_mem_left _ hv')

theorem isUnit_inv_sq_sub_one {O : Type} [CommRing O] (u : Oˣ) (h : IsUnit ((u : O) ^ 2 - 1)) :
    IsUnit (((u⁻¹ : Oˣ) : O) ^ 2 - 1) := by
  have e : ((u⁻¹ : Oˣ) : O) ^ 2 - 1 = -(((u⁻¹ : Oˣ) : O) ^ 2 * ((u : O) ^ 2 - 1)) := by
    rw [mul_sub, ← mul_pow, Units.inv_mul]; ring
  rw [e]
  exact (((u⁻¹).isUnit.pow 2).mul h).neg

theorem isUnit_sub_one {O : Type} [CommRing O] (x : O) (h : IsUnit (x ^ 2 - 1)) : IsUnit (x - 1) := by
  have e : x ^ 2 - 1 = (x - 1) * (x + 1) := by ring
  rw [e] at h
  exact isUnit_of_mul_isUnit_left h

theorem exists_scalar_tmat_of_tame_inertia : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i) (z : GE N), IsotypicValuationAtRing bkP i s → IsTameInertiaElementAtTwistPrime X i z → ∃ d : (X.O0 i)ˣ, Tmat i s z = (d : X.O0 i) • (1 : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)) ∧ IsUnit ((d : X.O0 i) ^ 2 - 1) ∧ IsUnit ((d : X.O0 i) - 1) ∧ eps0 X i z = 1 := by
  intro D N X bkP i s z h hz
  obtain ⟨v, hv, A, hA, hzA, hu, -⟩ := hz
  have hlp : (X.l i).Prime := (X.lPrime i).out
  have hv' : v ∈ placesOver D.host.E (if X.l i = D.host.pde then D.host.pde' else D.host.pde) := by
    rw [← X.pD_eq i]; exact hv
  have hp : (if X.l i = D.host.pde then D.host.pde' else D.host.pde).Prime := by
    split_ifs
    exacts [D.host.pde'_prime, D.host.pde_prime]
  have hl : v ∉ placesOver D.host.E (X.l i) := by
    refine not_mem_placesOver hp hlp ?_ hv'
    split_ifs with hh
    · rw [hh]; exact D.host.pde_ne.symm
    · exact fun e => hh e.symm
  have hg : ∀ k, v ∉ placesOver D.host.E (D.host.g k) := fun k => by
    refine not_mem_placesOver hp (D.host.g_prime k) ?_ hv'
    split_ifs
    exacts [(D.host.pde_ne_g k).2, (D.host.pde_ne_g k).1]
  have h1 : X.rhoS i s z = 1 := h.1 v hl hg A hA z hzA
  have h2 : chiS i s z = if X.side i s then X.delta i z else (X.delta i z)⁻¹ :=
    X.twistCharacterFamily_at_auxiliaryPlaces i _ _ v hv A hA z hzA
  have h3 : IsUnit ((((chiS i s z)⁻¹ : (X.O0 i)ˣ) : X.O0 i) ^ 2 - 1) := by
    rw [h2]
    split_ifs
    · exact isUnit_inv_sq_sub_one _ hu
    · rw [inv_inv]; exact hu
  refine ⟨(chiS i s z)⁻¹, ?_, h3, isUnit_sub_one _ h3, ?_⟩
  · rw [Tmat, h1, Units.val_one]
  · have h4 : cycZ D.host.E N.Om (X.l i) z = 1 := by
      refine Units.ext (PadicInt.ext_of_toZModPow.1 fun n => ?_)
      rw [cycZ_toZModPow_eq hl hA (q := 1) (fun x hx => by simpa using hzA.2 x hx) n]
      simp
    simp [eps0, h4]

end GlobalTheory.TwSys.TameScalar
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameInertiaElementActsByScalarStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tameInertiaElement_acts_by_scalar : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i) (z : GE N), IsotypicValuationAtRing bkP i s → IsTameInertiaElementAtTwistPrime X i z → ∃ d : (X.O0 i)ˣ, Tmat i s z = (d : X.O0 i) • (1 : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)) ∧ IsUnit ((d : X.O0 i) ^ 2 - 1) ∧ IsUnit ((d : X.O0 i) - 1) ∧ eps0 X i z = 1 := by
  first | exact @GlobalTheory.TwSys.TameScalar.exists_scalar_tmat_of_tame_inertia | exact GlobalTheory.TwSys.TameScalar.exists_scalar_tmat_of_tame_inertia | (intros; apply GlobalTheory.TwSys.TameScalar.exists_scalar_tmat_of_tame_inertia <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisTwistedSelmerAuxprimesOfMatrixAndBounds
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys
open scoped TensorProduct

namespace GlobalTheory.TwSys


open Classical in
theorem aeval_gen_sub_one_surjective (O : Type) [CommRing O] (n : ℕ) [NeZero n] (ι : Type) [Fintype ι] :
    Function.Surjective (MvPolynomial.aeval (R := O) fun q : ι =>
      MonoidAlgebra.of O (Multiplicative (ι → ZMod n)) (Multiplicative.ofAdd (Pi.single q 1)) - 1) := by
  set φ := (MvPolynomial.aeval (R := O) fun q : ι =>
      MonoidAlgebra.of O (Multiplicative (ι → ZMod n)) (Multiplicative.ofAdd (Pi.single q 1)) - 1) with hφ
  have hg : ∀ g : Multiplicative (ι → ZMod n), MonoidAlgebra.of O _ g ∈ φ.range := by
    intro g
    refine ⟨∏ q, (MvPolynomial.X q + 1) ^ (Multiplicative.toAdd g q).val, ?_⟩
    have h1 : g = ∏ q, (Multiplicative.ofAdd (Pi.single q (1 : ZMod n) : ι → ZMod n)) ^ (Multiplicative.toAdd g q).val := by
      apply Multiplicative.toAdd.injective
      rw [toAdd_prod]
      funext j
      simp only [toAdd_pow, toAdd_ofAdd, Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_ite, smul_zero,
        Finset.sum_ite_eq, Finset.mem_univ, if_true, nsmul_one, ZMod.natCast_zmod_val]
    conv_rhs => rw [h1]
    simp only [hφ, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_prod, map_pow, map_add (f := _), map_one,
      MvPolynomial.aeval_X, sub_add_cancel]
  intro x
  change x ∈ φ.range
  induction x using MonoidAlgebra.induction_on with
  | of g => exact hg g
  | add f g hf hg => exact add_mem hf hg
  | smul r f hf => exact Subalgebra.smul_mem _ hf r

theorem toLam_surjective {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} (X : NTw D.R D.host D.what₂ D.LL0 N)
    (i : X.Tw) (M : ℕ) (ι : Type) [Fintype ι] : Function.Surjective (toLam X i M ι) := by
  have : NeZero (X.l i ^ M) := ⟨pow_ne_zero _ (X.lPrime i).out.ne_zero⟩
  exact aeval_gen_sub_one_surjective (X.O0 i) (X.l i ^ M) ι

theorem SlopeTestRemainingChoices.empty {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}
    {i : X.Tw} {M : ℕ} {A : Finset (PlE D.host)} {ι : Type} {P : ι → PlE D.host} {d}
    (h : SlopeTestRemainingChoices X i M A P d) : SlopeTestRemainingChoices X i M ∅ P d := by
  refine ⟨fun q v hv => ?_, h.2⟩
  obtain ⟨h1, h2, h3, h4, -, h6⟩ := h.1 q v hv
  exact ⟨h1, h2, h3, h4, Finset.notMem_empty _, h6⟩

theorem galois_twisted_selmer_auxprimes_of_matrix_and_bounds : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂)
    (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X),
    ThmS bkP → SelmerLengthsByDeterminant bkP → ResidualBoundOddPrimes bkP → ThmC bkP → GaloisSideTwistedSelmerAuxiliaryPrimes bkP := by
  intro D N X bkP hS hS4 h103 hC i T hT
  have hO : OrdBound bkP i (IsDiscreteValuationRing.addVal (X.O0 i) ((X.l i : X.O0 i) ^ nu X i)) := by
    rcases Nat.eq_zero_or_pos (nu X i) with h | h
    · rw [h, pow_zero, IsDiscreteValuationRing.addVal_one]
      exact h103 i h
    · exact hC i h
  obtain ⟨R, Dd, M₀, hM₀⟩ := hO T hT
  refine ⟨R, Dd, max M₀ 1, le_max_right _ _, fun M hM H S d hF z hz H' ho hn A => ?_⟩
  have hM1 : 1 ≤ M := le_trans (le_max_right _ _) hM
  obtain ⟨P, hA, hSt, hP⟩ := hM₀ M (le_trans (le_max_left _ _) hM) H S d hF z hz H' ho hn A
  refine ⟨P, hA, hSt, fun s hs Q hQ => ?_⟩
  obtain ⟨a, Φ, hΦ, -⟩ := hS i s (hT s hs) M _ P _ Q hM1 hA.empty hQ
  obtain ⟨F, hFΦ⟩ := toLam_surjective X i M (Fin R ⊕ Fin R) Φ.det
  exact ⟨F, hS4 i s M _ P _ Q hM1 hA.empty hQ a Φ hΦ F hFΦ, hP s hs Q hQ a Φ hΦ F hFΦ⟩

end GlobalTheory.TwSys
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormalizedValuationOfPrimeOfGaloisExtension
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormalizedValuationOfPrimeOfGaloisExtension
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem ordIs_of_ordIs_ext : ∀ (F L : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra F L] [ValuativeExtension F L] [FiniteDimensional F L] [IsGalois F L] (p E : ℕ), OrdIs L p E → ∃ e : ℕ, OrdIs F p e ∧ E = (_root_.Ideal.ramificationIdx (_root_.IsLocalRing.maximalIdeal (_root_.Valuation.integer (_root_.ValuativeRel.valuation L))) (_root_.Valuation.integer (_root_.ValuativeRel.valuation F))) * e ∧ (_root_.Ideal.ramificationIdx (_root_.IsLocalRing.maximalIdeal (_root_.Valuation.integer (_root_.ValuativeRel.valuation L))) (_root_.Valuation.integer (_root_.ValuativeRel.valuation F))) = Nat.card ↥(lowerRamificationGroup F L 0) := by
  intro F L _ _ _ _ _ _ _ _ _ _ _ _ p E h
  unfold OrdIs at h ⊢
  have hmap := addVal_algebraMap_integer F L (p : 𝒪[F])
  rw [map_natCast] at hmap
  rw [hmap] at h
  have hne : IsDiscreteValuationRing.addVal 𝒪[F] (p : 𝒪[F]) ≠ ⊤ := by
    intro ht
    rw [ht, ENat.mul_top (by exact_mod_cast (ramificationIndex_pos F L).ne')] at h
    exact ENat.coe_ne_top E h.symm
  obtain ⟨e, he⟩ := ENat.ne_top_iff_exists.mp hne
  refine ⟨e, he.symm, ?_, (card_lowerRamificationGroup_zero (K := F) (L := L)).symm⟩
  rw [← he] at h
  exact_mod_cast h.symm

end GlobalTheory.PMon.Ram
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormalizedValuationOfPrimeOfGaloisExtensionStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalizedValuationOfPrime_of_galoisExtension : ∀ (F L : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra F L] [ValuativeExtension F L] [FiniteDimensional F L] [IsGalois F L] (p E : ℕ), OrdIs L p E → ∃ e : ℕ, OrdIs F p e ∧ E = (_root_.Ideal.ramificationIdx (_root_.IsLocalRing.maximalIdeal (_root_.Valuation.integer (_root_.ValuativeRel.valuation L))) (_root_.Valuation.integer (_root_.ValuativeRel.valuation F))) * e ∧ (_root_.Ideal.ramificationIdx (_root_.IsLocalRing.maximalIdeal (_root_.Valuation.integer (_root_.ValuativeRel.valuation L))) (_root_.Valuation.integer (_root_.ValuativeRel.valuation F))) = Nat.card ↥(lowerRamificationGroup F L 0) := by
  first | exact @GlobalTheory.PMon.Ram.ordIs_of_ordIs_ext | exact GlobalTheory.PMon.Ram.ordIs_of_ordIs_ext | (intros; apply GlobalTheory.PMon.Ram.ordIs_of_ordIs_ext <;> assumption)
end
end
