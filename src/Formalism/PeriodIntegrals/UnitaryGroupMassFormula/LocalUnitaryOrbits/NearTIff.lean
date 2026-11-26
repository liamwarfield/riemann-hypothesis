module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.SigRAlgebraMap

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.GramCoord
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.CfCoe
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.HRAddRight
noncomputable section

namespace PI.OmLocU.Red

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain Formalism.UG
open PI.VolStabSW PI.OmLocU
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

abbrev OR : Subring (Fv F v ⊗[F] E) := Orb.oRing (E := E) v (Orb.oSub (E := E) v)

def IsRes (ϖ : Fv F v) {K : Type} [CommRing K] (τ : K →+* K) (π : OR (E := E) v →+* K) : Prop :=
  Function.Surjective π ∧ (∀ x : OR (E := E) v, π x = 0 ↔ (x : Fv F v ⊗[F] E) ∈ PO (E := E) v ϖ) ∧
    ∀ x y : OR (E := E) v, (y : Fv F v ⊗[F] E) = sigR (Fv F v) σ x → π y = τ (π x)

theorem hR_add_right (x y z : Fin n → Fv F v ⊗[F] E) :
    hR (Fv F v) σ J x (y + z) = hR (Fv F v) σ J x y + hR (Fv F v) σ J x z := by
  simp only [hR, hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem coord_eq (e : Fin n → Fin n → Fv F v ⊗[F] E) (he1 : gramR (Fv F v) σ J e = 1)
    (c : Fin n → Fv F v ⊗[F] E) (j : Fin n) : hR (Fv F v) σ J (e j) (∑ i, c i • e i) = c j := by
  rw [Orb.hR_sum_right σ J v]
  have h : ∀ i, hR (Fv F v) σ J (e j) (e i) = (1 : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) j i := by
    intro i; rw [← he1]; rfl
  simp only [h, Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem bas_mem {e : Fin n → Fin n → Fv F v ⊗[F] E} (he : Orb.IsOBas v Λ e) (j : Fin n) :
    e j ∈ latLoc (E := E) v Λ := by
  refine (he _).2 ⟨Pi.single j 1, fun i => ?_, ?_⟩
  · by_cases h : i = j
    · subst h; simpa using (Orb.oSub (E := E) v).1
    · simpa [Pi.single_apply, h] using Orb.oev_zero (E := E) v
  · simp [Pi.single_apply, ite_smul]

theorem expand {e : Fin n → Fin n → Fv F v ⊗[F] E} (he : Orb.IsOBas v Λ e) (he1 : gramR (Fv F v) σ J e = 1)
    {x : Fin n → Fv F v ⊗[F] E} (hx : x ∈ latLoc (E := E) v Λ) :
    x = ∑ j, hR (Fv F v) σ J (e j) x • e j := by
  obtain ⟨c, -, rfl⟩ := (he x).1 hx
  simp only [coord_eq σ J v e he1]

theorem ffGram_one {K : Type} [CommRing K] (τ : K →+* K) {a : ℕ} (X : Fin a → Fin n → K) (i j : Fin a) :
    ffGram τ (1 : Matrix (Fin n) (Fin n) K) X i j = ∑ p, τ (X i p) * X j p := by
  simp only [ffGram, ffH, Matrix.one_apply, mul_ite, ite_mul, mul_one, mul_zero, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem gY_mem {a : ℕ} {Y : TupV (E := E) v n a} (hG : GoodY σ J ψ v Λ a Y) (i j : Fin a) :
    gramR (Fv F v) σ J Y i j ∈ OR (E := E) v :=
  (hG.2.2.1 (Y j)).1 (hG.2.2.2.2.2.1.1 j) (Y i) (hG.2.2.2.2.2.1.1 i)

end PI.OmLocU.Red
end
end

noncomputable section

namespace PI.OmLocU.Red

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain Formalism.UG
open PI.VolStabSW PI.OmLocU
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

theorem memA {a : ℕ} (X : lamA v Λ a) (i : Fin a) : (X : TupV (E := E) v n a) i ∈ latLoc (E := E) v Λ :=
  X.2 i

def cf (hSD : IsSDLoc σ J v Λ) {e : Fin n → Fin n → Fv F v ⊗[F] E} (he : Orb.IsOBas v Λ e) {a : ℕ}
    (X : lamA v Λ a) (i : Fin a) (p : Fin n) : OR (E := E) v :=
  ⟨hR (Fv F v) σ J (e p) ((X : TupV (E := E) v n a) i), (hSD _).1 (memA v Λ X i) _ (bas_mem v Λ he p)⟩

theorem cf_coe (hSD : IsSDLoc σ J v Λ) {e : Fin n → Fin n → Fv F v ⊗[F] E} (he : Orb.IsOBas v Λ e) {a : ℕ}
    (X : lamA v Λ a) (i : Fin a) (p : Fin n) :
    (cf σ J v Λ hSD he X i p : Fv F v ⊗[F] E) = hR (Fv F v) σ J (e p) ((X : TupV (E := E) v n a) i) := rfl

def phi (hSD : IsSDLoc σ J v Λ) {e : Fin n → Fin n → Fv F v ⊗[F] E} (he : Orb.IsOBas v Λ e) {K : Type} [CommRing K]
    (π : OR (E := E) v →+* K) (a : ℕ) : lamA v Λ a →+ (Fin a → Fin n → K) where
  toFun X := fun i p => π (cf σ J v Λ hSD he X i p)
  map_zero' := by
    funext i p
    have h : cf σ J v Λ hSD he (0 : lamA v Λ a) i p = 0 := by
      apply Subtype.ext
      rw [cf_coe]
      simp [hR, hform]
    simp only [h, map_zero, Pi.zero_apply]
  map_add' X Y := by
    funext i p
    have h : cf σ J v Λ hSD he (X + Y) i p = cf σ J v Λ hSD he X i p + cf σ J v Λ hSD he Y i p := by
      apply Subtype.ext
      simp only [cf_coe, AddSubgroup.coe_add, Pi.add_apply, Subring.coe_add]
      exact hR_add_right σ J v _ _ _
    simp only [h, map_add (f := _), Pi.add_apply]

theorem phi_apply (hSD : IsSDLoc σ J v Λ) {e : Fin n → Fin n → Fv F v ⊗[F] E} (he : Orb.IsOBas v Λ e) {K : Type}
    [CommRing K] (π : OR (E := E) v →+* K) {a : ℕ} (X : lamA v Λ a) (i : Fin a) (p : Fin n) :
    phi σ J v Λ hSD he π a X i p = π (cf σ J v Λ hSD he X i p) := rfl

end PI.OmLocU.Red
end
end

noncomputable section

namespace PI.OmLocU.Red

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain Formalism.UG
open PI.VolStabSW PI.OmLocU
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

theorem phi_surj (hSD : IsSDLoc σ J v Λ) {e : Fin n → Fin n → Fv F v ⊗[F] E} (he : Orb.IsOBas v Λ e)
    (he1 : gramR (Fv F v) σ J e = 1) {ϖ : Fv F v} {K : Type} [CommRing K] {τ : K →+* K}
    {π : OR (E := E) v →+* K} (hπ : IsRes σ v ϖ τ π) (a : ℕ) :
    Function.Surjective (phi σ J v Λ hSD he π a) := by
  intro M
  choose c hc using fun i p => hπ.1 (M i p)
  have hX : (fun i => ∑ p, (c i p : Fv F v ⊗[F] E) • e p) ∈ lamA v Λ a := fun i =>
    (he _).2 ⟨fun p => (c i p : Fv F v ⊗[F] E), fun p => (c i p).2, rfl⟩
  refine ⟨⟨_, hX⟩, ?_⟩
  funext i p
  rw [phi_apply]
  have h : cf σ J v Λ hSD he ⟨_, hX⟩ i p = c i p := by
    apply Subtype.ext
    rw [cf_coe]
    exact coord_eq σ J v e he1 (fun q => (c i q : Fv F v ⊗[F] E)) p
  rw [h, hc]

theorem phi_ker (hSD : IsSDLoc σ J v Λ) {e : Fin n → Fin n → Fv F v ⊗[F] E} (he : Orb.IsOBas v Λ e)
    (he1 : gramR (Fv F v) σ J e = 1) {ϖ : Fv F v} {K : Type} [CommRing K] {τ : K →+* K}
    {π : OR (E := E) v →+* K} (hπ : IsRes σ v ϖ τ π) (a : ℕ) :
    (lamP v Λ a ϖ).addSubgroupOf (lamA v Λ a) = (phi σ J v Λ hSD he π a).ker := by
  ext X
  rw [AddSubgroup.mem_addSubgroupOf, AddMonoidHom.mem_ker]
  constructor
  · rintro ⟨Z, hZ, hZX⟩
    funext i p
    rw [phi_apply, Pi.zero_apply, Pi.zero_apply]
    apply (hπ.2.1 _).2
    rw [cf_coe, ← hZX]
    refine ⟨hR (Fv F v) σ J (e p) (Z i), (hSD _).1 (hZ i) _ (bas_mem v Λ he p), ?_⟩
    show hR (Fv F v) σ J (e p) (sc (E := E) v ϖ • Z i) = _
    rw [Orb.hR_smul_right]
  · intro h0
    have hP : ∀ i p, ∃ d ∈ OEv (E := E) v,
        hR (Fv F v) σ J (e p) ((X : TupV (E := E) v n a) i) = sc (E := E) v ϖ * d := by
      intro i p
      have := (hπ.2.1 (cf σ J v Λ hSD he X i p)).1 (by
        have h1 := congrFun (congrFun h0 i) p
        rw [phi_apply] at h1
        exact h1)
      exact this
    choose d hd hde using hP
    have hZ : (fun i => ∑ p, d i p • e p) ∈ lamA v Λ a := fun i => (he _).2 ⟨d i, hd i, rfl⟩
    refine ⟨_, hZ, ?_⟩
    funext i
    rw [DistribSMul.toAddMonoidHom_apply, Pi.smul_apply, expand σ J v Λ he he1 (memA v Λ X i), Finset.smul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [hde, smul_smul]

theorem gram_coord (hcm : IsCMExt F E σ) (hJ : ∀ i j, σ (J j i) = J i j) (hSD : IsSDLoc σ J v Λ)
    {e : Fin n → Fin n → Fv F v ⊗[F] E} (he : Orb.IsOBas v Λ e) (he1 : gramR (Fv F v) σ J e = 1) {a : ℕ}
    (X : lamA v Λ a) (i j : Fin a) :
    gramR (Fv F v) σ J (X : TupV (E := E) v n a) i j = ∑ p, sigR (Fv F v) σ (cf σ J v Λ hSD he X i p : Fv F v ⊗[F] E) *
      (cf σ J v Λ hSD he X j p : Fv F v ⊗[F] E) := by
  show hR (Fv F v) σ J ((X : TupV (E := E) v n a) i) ((X : TupV (E := E) v n a) j) = _
  conv_lhs => rw [expand σ J v Λ he he1 (memA v Λ X j)]
  rw [Orb.hR_sum_right σ J v]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [cf_coe, cf_coe, Orb.hR_conj σ J v hcm hJ, mul_comm]

end PI.OmLocU.Red
end
end

noncomputable section

namespace PI.OmLocU.Red

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain Formalism.UG
open PI.VolStabSW PI.OmLocU
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

theorem nearT_iff (hcm : IsCMExt F E σ) (hJ : ∀ i j, σ (J j i) = J i j) (hSD : IsSDLoc σ J v Λ)
    {e : Fin n → Fin n → Fv F v ⊗[F] E} (he : Orb.IsOBas v Λ e) (he1 : gramR (Fv F v) σ J e = 1)
    {ϖ : Fv F v} {K : Type} [CommRing K] {τ : K →+* K} {π : OR (E := E) v →+* K} (hπ : IsRes σ v ϖ τ π)
    {a : ℕ} (T : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) (hT : ∀ i j, T i j ∈ OR (E := E) v) (X : lamA v Λ a) :
    (X : TupV (E := E) v n a) ∈ NearT v σ J ϖ T ↔
      ffGram τ 1 (phi σ J v Λ hSD he π a X) = fun i j => π ⟨T i j, hT i j⟩ := by
  have hg : ∀ i j, gramR (Fv F v) σ J (X : TupV (E := E) v n a) i j ∈ OR (E := E) v := fun i j =>
    (hSD _).1 (memA v Λ X j) _ (memA v Λ X i)
  have hconj : ∀ i p, π ⟨hR (Fv F v) σ J ((X : TupV (E := E) v n a) i) (e p),
      (hSD _).1 (bas_mem v Λ he p) _ (memA v Λ X i)⟩ = τ (π (cf σ J v Λ hSD he X i p)) := fun i p =>
    hπ.2.2 _ _ (by rw [cf_coe, Orb.hR_conj σ J v hcm hJ])
  have hG : ∀ i j, π ⟨_, hg i j⟩ = ffGram τ 1 (phi σ J v Λ hSD he π a X) i j := by
    intro i j
    rw [ffGram_one]
    have e1 : (⟨_, hg i j⟩ : OR (E := E) v) = ∑ p, (⟨hR (Fv F v) σ J ((X : TupV (E := E) v n a) i) (e p),
        (hSD _).1 (bas_mem v Λ he p) _ (memA v Λ X i)⟩ : OR (E := E) v) * cf σ J v Λ hSD he X j p := by
      apply Subtype.ext
      simp only [AddSubmonoidClass.coe_finsetSum, Subring.coe_mul]
      rw [gram_coord σ J v Λ hcm hJ hSD he he1]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [cf_coe, Orb.hR_conj σ J v hcm hJ]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [e1, map_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [map_mul, hconj, phi_apply, phi_apply]
  constructor
  · intro hN
    funext i j
    rw [← hG]
    have h0 := (hπ.2.1 (⟨_, hg i j⟩ - ⟨T i j, hT i j⟩)).2 (hN i j)
    rw [map_sub, sub_eq_zero] at h0
    exact h0
  · intro hE i j
    have h1 := congrFun (congrFun hE i) j
    rw [← hG] at h1
    have h0 : π (⟨_, hg i j⟩ - ⟨T i j, hT i j⟩) = 0 := by rw [map_sub, h1, sub_self]
    exact (hπ.2.1 _).1 h0

theorem card_cls (hcm : IsCMExt F E σ) (hJ : ∀ i j, σ (J j i) = J i j) (hSD : IsSDLoc σ J v Λ)
    {e : Fin n → Fin n → Fv F v ⊗[F] E} (he : Orb.IsOBas v Λ e) (he1 : gramR (Fv F v) σ J e = 1)
    {ϖ : Fv F v} {K : Type} [CommRing K] (τ : K →+* K) (π : OR (E := E) v →+* K) (hπ : IsRes σ v ϖ τ π)
    {a : ℕ} (T : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) (hT : ∀ i j, T i j ∈ OR (E := E) v) :
    Nat.card (clsU σ J v Λ a ϖ T) =
      Nat.card {X : Fin a → Fin n → K // ffGram τ 1 X = fun i j => π ⟨T i j, hT i j⟩} := by
  set Φ := phi σ J v Λ hSD he π a with hΦ
  let eq : (lamA v Λ a ⧸ (lamP v Λ a ϖ).addSubgroupOf (lamA v Λ a)) ≃+ (Fin a → Fin n → K) :=
    (QuotientAddGroup.quotientAddEquivOfEq (phi_ker σ J v Λ hSD he he1 hπ a)).trans
      (QuotientAddGroup.quotientKerEquivOfSurjective Φ (phi_surj σ J v Λ hSD he he1 hπ a))
  have heq : ∀ x : lamA v Λ a, eq (QuotientAddGroup.mk x) = Φ x := fun x => rfl
  set P : (Fin a → Fin n → K) → Prop := fun M => ffGram τ 1 M = fun i j => π ⟨T i j, hT i j⟩ with hP
  have hset : clsU σ J v Λ a ϖ T = {q | P (eq q)} := by
    ext q
    induction q using QuotientAddGroup.induction_on with
    | H x =>
      constructor
      · rintro ⟨y, hy, hyx⟩
        show P (eq (QuotientAddGroup.mk x))
        rw [← hyx, heq]
        exact (nearT_iff σ J v Λ hcm hJ hSD he he1 hπ T hT y).1 hy
      · intro hx
        refine ⟨x, (nearT_iff σ J v Λ hcm hJ hSD he he1 hπ T hT x).2 ?_, rfl⟩
        have : P (eq (QuotientAddGroup.mk x)) := hx
        rw [heq] at this
        exact this
  rw [hset]
  exact Nat.card_congr (Equiv.subtypeEquiv (p := fun q => q ∈ {q | P (eq q)}) eq.toEquiv (fun q => Iff.rfl))

end PI.OmLocU.Red
