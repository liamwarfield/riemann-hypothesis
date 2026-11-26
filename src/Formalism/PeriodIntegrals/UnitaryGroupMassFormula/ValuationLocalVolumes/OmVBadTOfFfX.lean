module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.OmVBadTOfRestX

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.LocalGramMatrixCorankOne
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.ProdDiagonalShiftOneMinus
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.CorOneRed
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.PrimIff
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.CoordComb
noncomputable section

namespace PI.OmVg

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain PI.OmLocU PI.OmLocU.Red
  Topology Filter
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

theorem exists_pow_mem {ϖ : Fv F v} (hϖ : IsUnif v ϖ) {a : ℕ} (c : Fin a → Fv F v ⊗[F] E) :
    ∃ m : ℕ, ∀ i, sc (E := E) v (ϖ ^ m) * c i ∈ OEv (E := E) v := by
  obtain ⟨-, hπ, -⟩ := unif_spec v ϖ hϖ
  have hN : OEv (E := E) v ∈ 𝓝 (0 : Fv F v ⊗[F] E) := (isOpen_oEv v).mem_nhds (Orb.oev_zero v)
  obtain ⟨m, hm⟩ := PI.VolStabSW.eventually_smul_sub (Set.range c) (Set.finite_range c).isCompact
    (fun k => ϖ ^ k) hπ _ hN
  exact ⟨m, fun i => by rw [← smul_eq_sc]; exact hm _ ⟨i, rfl⟩⟩

variable (hSD : IsSDLoc σ J v Λ) {e : Fin n → Fin n → Fv F v ⊗[F] E} (he : Orb.IsOBas v Λ e)
  (he1 : gramR (Fv F v) σ J e = 1)

theorem coord_comb {K : Type} [CommRing K] (π : OR (E := E) v →+* K) {a : ℕ} (x : lamA v Λ a)
    (d : Fin a → OR (E := E) v) (p : Fin n)
    (hw : hR (Fv F v) σ J (e p) (∑ i, (d i : Fv F v ⊗[F] E) • (x : TupV (E := E) v n a) i) ∈ OR (E := E) v) :
    π ⟨_, hw⟩ = ∑ i, π (d i) * phi σ J v Λ hSD he π a x i p := by
  have e1 : (⟨_, hw⟩ : OR (E := E) v) = ∑ i, d i * cf σ J v Λ hSD he x i p := by
    apply Subtype.ext
    simp only [AddSubmonoidClass.coe_finsetSum, Subring.coe_mul, cf_coe]
    rw [Orb.hR_sum_right σ J v]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e1, map_sum]
  simp only [map_mul, phi_apply]


include he1 in
theorem ker_vec {ϖ : Fv F v} {K : Type} [CommRing K] {τ : K →+* K} {π : OR (E := E) v →+* K}
    (hπ : IsRes σ v ϖ τ π) {w : Fin n → Fv F v ⊗[F] E} (hw : w ∈ latLoc (E := E) v Λ)
    (h0 : ∀ p, π ⟨hR (Fv F v) σ J (e p) w, (hSD _).1 hw _ (bas_mem v Λ he p)⟩ = 0) :
    ∃ w' ∈ latLoc (E := E) v Λ, w = sc (E := E) v ϖ • w' := by
  have hP : ∀ p, ∃ d ∈ OEv (E := E) v, hR (Fv F v) σ J (e p) w = sc (E := E) v ϖ * d :=
    fun p => (hπ.2.1 _).1 (h0 p)
  choose d hd hde using hP
  refine ⟨∑ p, d p • e p, (he _).2 ⟨d, hd, rfl⟩, ?_⟩
  rw [expand σ J v Λ he he1 hw, Finset.smul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [hde, smul_smul]

end PI.OmVg
end
end

noncomputable section

namespace PI.OmVg

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain PI.OmLocU PI.OmLocU.Red
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))
  (hSD : IsSDLoc σ J v Λ) {e : Fin n → Fin n → Fv F v ⊗[F] E} (he : Orb.IsOBas v Λ e)
  (he1 : gramR (Fv F v) σ J e = 1)


include he1 in
theorem prim_iff (hL : ∃ L : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E L ∧ (L : Set (Fin n → E)) = Λ)
    {ϖ : Fv F v} (hϖ : IsUnif v ϖ) {K : Type} [CommRing K] {τ : K →+* K} {π : OR (E := E) v →+* K}
    (hπ : IsRes σ v ϖ τ π) {a : ℕ} (x : lamA v Λ a) :
    IsPrim v Λ (x : TupV (E := E) v n a) ↔ LinearIndependent K (phi σ J v Λ hSD he π a x) := by
  obtain ⟨h0, -, hint⟩ := unif_spec v ϖ hϖ
  have hcomb : ∀ d : Fin a → OR (E := E) v,
      (∑ i, (d i : Fv F v ⊗[F] E) • (x : TupV (E := E) v n a) i) ∈ latLoc (E := E) v Λ := fun d =>
    Submodule.sum_mem _ fun i _ => Orb.oSmul v Λ hL _ (d i).2 _ (memA v Λ x i)
  rw [Fintype.linearIndependent_iff]
  constructor
  · intro hP κ hκ i
    choose d hd using fun j => hπ.1 (κ j)
    have hw := hcomb d
    have hz : ∀ p, π ⟨hR (Fv F v) σ J (e p) (∑ j, (d j : Fv F v ⊗[F] E) • (x : TupV (E := E) v n a) j),
        (hSD _).1 hw _ (bas_mem v Λ he p)⟩ = 0 := by
      intro p
      refine (coord_comb σ J v Λ hSD he π x d p _).trans ?_
      have := congrFun hκ p
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
      simpa [hd] using this
    obtain ⟨w', hw', hww⟩ := ker_vec σ J v Λ hSD he he1 hπ hw hz
    have hc := hP.2 (fun j => sc (E := E) v ϖ⁻¹ * d j) (by
      have e2 : (∑ j, (sc (E := E) v ϖ⁻¹ * d j) • (x : TupV (E := E) v n a) j) =
          sc (E := E) v ϖ⁻¹ • ∑ j, (d j : Fv F v ⊗[F] E) • (x : TupV (E := E) v n a) j := by
        rw [Finset.smul_sum]
        exact Finset.sum_congr rfl fun j _ => by rw [smul_smul]
      rw [e2, hww, smul_smul, sc_mul, inv_mul_cancel₀ h0, sc_one, one_smul]
      exact hw') i
    rw [← hd i]
    apply (hπ.2.1 _).2
    refine ⟨_, hc, ?_⟩
    rw [← mul_assoc, sc_mul, mul_inv_cancel₀ h0, sc_one, one_mul]
  · intro hLI
    refine ⟨fun i => memA v Λ x i, fun c hc => ?_⟩
    have key : ∀ m : ℕ, ∀ c : Fin a → Fv F v ⊗[F] E,
        (∑ i, c i • (x : TupV (E := E) v n a) i) ∈ latLoc (E := E) v Λ →
        (∀ i, sc (E := E) v (ϖ ^ m) * c i ∈ OEv (E := E) v) → ∀ i, c i ∈ OEv (E := E) v := by
      intro m
      induction m with
      | zero => intro c _ hm i; simpa [sc_one] using hm i
      | succ m ih =>
        intro c hc hm
        apply ih c hc
        set u := ∑ i, c i • (x : TupV (E := E) v n a) i with hu
        have hpm : sc (E := E) v (ϖ ^ m) ∈ OEv (E := E) v := by
          simpa using sc_mul_mem_oEv v (pow_mem hint m) (Orb.oSub (E := E) v).1
        have hu' : sc (E := E) v (ϖ ^ m) • u ∈ latLoc (E := E) v Λ := Orb.oSmul v Λ hL _ hpm _ hc
        let d : Fin a → OR (E := E) v := fun i => ⟨_, hm i⟩
        have hwe : (∑ i, (d i : Fv F v ⊗[F] E) • (x : TupV (E := E) v n a) i) =
            sc (E := E) v ϖ • (sc (E := E) v (ϖ ^ m) • u) := by
          rw [smul_smul, sc_mul, ← pow_succ', hu, Finset.smul_sum]
          exact Finset.sum_congr rfl fun i _ => by rw [smul_smul]
        have hw := hcomb d
        have hz : ∀ p, ∑ i, π (d i) * phi σ J v Λ hSD he π a x i p = 0 := by
          intro p
          rw [← coord_comb σ J v Λ hSD he π x d p ((hSD _).1 hw _ (bas_mem v Λ he p))]
          apply (hπ.2.1 _).2
          refine ⟨hR (Fv F v) σ J (e p) (sc (E := E) v (ϖ ^ m) • u),
            (hSD _).1 hu' _ (bas_mem v Λ he p), ?_⟩
          show hR (Fv F v) σ J (e p) (∑ i, (d i : Fv F v ⊗[F] E) • (x : TupV (E := E) v n a) i) = _
          rw [hwe, Orb.hR_smul_right]
        have hd0 := hLI (fun i => π (d i)) (by
          funext p
          simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
          exact hz p)
        intro i
        obtain ⟨g, hg, hge⟩ := (hπ.2.1 (d i)).1 (hd0 i)
        have : sc (E := E) v (ϖ ^ m) * c i = g := by
          have h1 : sc (E := E) v ϖ * (sc (E := E) v (ϖ ^ m) * c i) = sc (E := E) v ϖ * g := by
            rw [← mul_assoc, sc_mul, ← pow_succ']
            exact hge
          have h2 := congrArg (fun y => sc (E := E) v ϖ⁻¹ * y) h1
          simp only [← mul_assoc, sc_mul, inv_mul_cancel₀ h0, sc_one, one_mul] at h2
          exact h2
        rw [this]
        exact hg
    obtain ⟨m, hm⟩ := exists_pow_mem v hϖ c
    exact key m c hc hm

end PI.OmVg
end
end

noncomputable section

namespace PI.OmVg

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain PI.OmLocU PI.OmLocU.Red
  PI.VolStabSW
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

theorem card_clsP (hL : ∃ L : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E L ∧ (L : Set (Fin n → E)) = Λ)
    (hcm : IsCMExt F E σ) (hJ : ∀ i j, σ (J j i) = J i j) (hSD : IsSDLoc σ J v Λ)
    {e : Fin n → Fin n → Fv F v ⊗[F] E} (he : Orb.IsOBas v Λ e) (he1 : gramR (Fv F v) σ J e = 1)
    {ϖ : Fv F v} (hϖ : IsUnif v ϖ) {K : Type} [CommRing K] (τ : K →+* K) (π : OR (E := E) v →+* K)
    (hπ : IsRes σ v ϖ τ π) {a : ℕ} (T : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E))
    (hT : ∀ i j, T i j ∈ OR (E := E) v) :
    Nat.card (PI.OmVd.clsP σ J v Λ a ϖ T) =
      Nat.card {X : Fin a → Fin n → K //
        ffGram τ 1 X = (fun i j => π ⟨T i j, hT i j⟩) ∧ LinearIndependent K X} := by
  set Φ := phi σ J v Λ hSD he π a with hΦ
  let eq : (lamA v Λ a ⧸ (lamP v Λ a ϖ).addSubgroupOf (lamA v Λ a)) ≃+ (Fin a → Fin n → K) :=
    (QuotientAddGroup.quotientAddEquivOfEq (phi_ker σ J v Λ hSD he he1 hπ a)).trans
      (QuotientAddGroup.quotientKerEquivOfSurjective Φ (phi_surj σ J v Λ hSD he he1 hπ a))
  have heq : ∀ x : lamA v Λ a, eq (QuotientAddGroup.mk x) = Φ x := fun x => rfl
  set P : (Fin a → Fin n → K) → Prop := fun M =>
    ffGram τ 1 M = (fun i j => π ⟨T i j, hT i j⟩) ∧ LinearIndependent K M with hP
  have hset : PI.OmVd.clsP σ J v Λ a ϖ T = {q | P (eq q)} := by
    ext q
    induction q using QuotientAddGroup.induction_on with
    | H x =>
      constructor
      · rintro ⟨y, ⟨hyP, hyN⟩, hyx⟩
        show P (eq (QuotientAddGroup.mk x))
        rw [← hyx, heq]
        exact ⟨(nearT_iff σ J v Λ hcm hJ hSD he he1 hπ T hT y).1 hyN,
          (prim_iff σ J v Λ hSD he he1 hL hϖ hπ y).1 hyP⟩
      · intro hx
        have h2 : P (eq (QuotientAddGroup.mk x)) := hx
        rw [heq] at h2
        exact ⟨x, ⟨(prim_iff σ J v Λ hSD he he1 hL hϖ hπ x).2 h2.2,
          (nearT_iff σ J v Λ hcm hJ hSD he he1 hπ T hT x).2 h2.1⟩, rfl⟩
  rw [hset]
  exact Nat.card_congr (Equiv.subtypeEquiv (p := fun q => q ∈ {q | P (eq q)}) eq.toEquiv (fun q => Iff.rfl))

def GramCor (ϖ : Fv F v) {a : ℕ} (T : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) : Prop :=
  ∃ i₀ : Fin a, (∀ j, T i₀ j ∈ PO (E := E) v ϖ) ∧ (∀ j, T j i₀ ∈ PO (E := E) v ϖ) ∧
    ∃ w ∈ OEv (E := E) v, (T + Matrix.single i₀ i₀ 1).det * w = 1

theorem corOne_red {ϖ : Fv F v} {K : Type} [CommRing K] {τ : K →+* K} {π : OR (E := E) v →+* K}
    (hπ : IsRes σ v ϖ τ π) {a : ℕ} (T : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E))
    (hT : ∀ i j, T i j ∈ OR (E := E) v) (hC : GramCor v ϖ T) :
    PI.OmVd.CorOne (fun i j => π ⟨T i j, hT i j⟩ : Matrix (Fin a) (Fin a) K) := by
  obtain ⟨i₀, hr, hc, w, hw, hd⟩ := hC
  refine ⟨i₀, fun j => (hπ.2.1 _).2 (hr j), fun j => (hπ.2.1 _).2 (hc j), ?_⟩
  have hT' : ∀ i j, (T + Matrix.single i₀ i₀ 1 : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j ∈ OR (E := E) v := by
    intro i j
    rw [Matrix.add_apply, Matrix.single_apply]
    split_ifs
    · exact (OR (E := E) v).add_mem (hT i j) (OR (E := E) v).one_mem
    · simpa using hT i j
  convert det_red v π _ hT' hw hd using 2
  congr 1
  ext i j
  by_cases h : i₀ = i ∧ i₀ = j
  · obtain ⟨h1', h2'⟩ := h
    subst h1'
    subst h2'
    have h1 : (⟨(T + Matrix.single i₀ i₀ 1 : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i₀ i₀, hT' i₀ i₀⟩ :
        OR (E := E) v) = ⟨T i₀ i₀, hT i₀ i₀⟩ + 1 := by
      apply Subtype.ext
      simp [Matrix.add_apply]
    rw [h1, map_add (f := _), map_one]
    show π ⟨T i₀ i₀, hT i₀ i₀⟩ + (Matrix.single i₀ i₀ 1 : Matrix (Fin a) (Fin a) K) i₀ i₀ = _
    simp
  · have h1 : (⟨(T + Matrix.single i₀ i₀ 1 : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j, hT' i j⟩ :
        OR (E := E) v) = ⟨T i j, hT i j⟩ := by
      apply Subtype.ext
      simp [Matrix.add_apply, Matrix.single_apply, h]
    rw [h1]
    show π ⟨T i j, hT i j⟩ + (Matrix.single i₀ i₀ 1 : Matrix (Fin a) (Fin a) K) i j = _
    simp [Matrix.single_apply, h]

theorem redP_of_gramCor (a : ℕ) (Y : TupV (E := E) v n a)
    (hC : ∀ ϖ : Fv F v, IsUnif v ϖ → GramCor v ϖ (gramR (Fv F v) σ J Y)) :
    PI.OmVd.RedP σ J ψ v Λ a Y := by
  intro hG ϖ hϖ
  have hR : ResAlg σ J ψ v := resAlg_of_sp σ J ψ v (etaSp_holds σ J ψ v)
  have hU : Orb.UnitV σ J ψ v Λ :=
    Orb.unitV_of σ J ψ v Λ (NormOneUnitFixedPoints.normOne_of σ J ψ v hR) (UnN.unitNorm_of_res σ J ψ v Λ hR)
  have hstd := hG.1
  have hcm := hstd.1
  have hJ : ∀ i j, σ (J j i) = J i j := hstd.2.1.1
  have hL := hG.2.1
  have hSD : IsSDLoc σ J v Λ := hG.2.2.1
  obtain ⟨e, he, he1⟩ := oBas1_of_unitV σ J ψ v Λ hU hstd hL hSD hG.2.2.2.1
  have hY := hG.2.2.2.2.2.1
  have hT : ∀ i j, gramR (Fv F v) σ J Y i j ∈ OR (E := E) v := fun i j =>
    (hSD (Y j)).1 (hY j) (Y i) (hY i)
  have hconj : ∀ i j, gramR (Fv F v) σ J Y i j = sigR (Fv F v) σ (gramR (Fv F v) σ J Y j i) := fun i j =>
    (Orb.hR_conj σ J v hcm hJ (Y j) (Y i)).symm
  obtain ⟨k, _, _, hk, h⟩ := hR hstd hG.2.2.2.1 ϖ hϖ
  refine ⟨k, inferInstance, inferInstance, hk, ?_⟩
  rcases h with ⟨hη, K, _, _, σ', π, hσ, h2, hne, hπ⟩ | ⟨hη, π, hπ⟩
  · refine Or.inl ⟨hη, K, inferInstance, inferInstance, σ', 1, fun i j => π ⟨_, hT i j⟩, hσ, h2, hne, ?_,
      by simp, ?_, corOne_red σ v hπ _ hT (hC ϖ hϖ),
      card_clsP σ J v Λ hL hcm hJ hSD he he1 hϖ (σ' : K →+* K) π hπ _ hT⟩
    · intro i j
      by_cases h : i = j
      · subst h; simp
      · simp [h, Ne.symm h]
    · intro i j
      exact (hπ.2.2 _ _ (hconj i j)).symm
  · refine Or.inr ⟨hη, 1, fun i j => π ⟨_, hT i j⟩, ?_, by simp, ?_, corOne_red σ v hπ _ hT (hC ϖ hϖ),
      card_clsP σ J v Λ hL hcm hJ hSD he he1 hϖ (RingEquiv.prodComm (R := k) (S := k)).toRingHom π hπ _ hT⟩
    · intro i j
      by_cases h : i = j
      · subst h; ext <;> simp
      · ext <;> simp [h, Ne.symm h]
    · intro i j
      exact (hπ.2.2 _ _ (hconj i j)).symm

end PI.OmVg
end
end

noncomputable section

namespace PI.OmVg

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  NumberField IsDedekindDomain Matrix PI.OmLocU Formalism.L2.SG.Pf.NcVal.OmVSt Formalism.L2.SG.Pf.NcVal.OmVSt.OmW
open scoped TensorProduct

theorem le_exp_neg_one {x : WithZero (Multiplicative ℤ)} (h : x < 1) : x ≤ WithZero.exp (-1) := by
  rw [← WithZero.lt_mul_exp_iff_le WithZero.exp_ne_zero, ← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero]
  exact h

theorem natCast_div_mem {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (t : ℕ)
    (ht : ((t : 𝓞 F)) ∈ v.asIdeal) {ϖ : Fv F v} (hϖ : IsUnif v ϖ) :
    ((t : ℕ) : Fv F v) * ϖ⁻¹ ∈ v.adicCompletionIntegers F := by
  have h1 : ((t : ℕ) : Fv F v) = algebraMap (𝓞 F) (Fv F v) (t : 𝓞 F) := by simp
  have hlt : Valued.v ((t : ℕ) : Fv F v) < 1 := by
    rw [h1]
    refine (HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := F) v (t : 𝓞 F)).trans_lt ?_
    erw [HeightOneSpectrum.valuation_of_algebraMap]
    exact (HeightOneSpectrum.intValuation_lt_one_iff_mem v _).2 ht
  have hv : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hϖ
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, map_inv₀, hv]
  calc Valued.v ((t : ℕ) : Fv F v) * (WithZero.exp (-1 : ℤ))⁻¹
      ≤ WithZero.exp (-1 : ℤ) * (WithZero.exp (-1 : ℤ))⁻¹ := by gcongr; exact le_exp_neg_one hlt
    _ = 1 := mul_inv_cancel₀ WithZero.exp_ne_zero

variable {D : D7} (X : HidaSetting D) (u' : D.what₂.Word)

def iz : Fin (D.R.rS + 1 + D.R.rS) := ⟨D.R.rS, by omega⟩

theorem piv_iz : piv D.R.rS (iz (D := D)) = iz := by
  apply Fin.ext
  simp [piv, iz]

theorem eq_iz_of_piv {a : Fin (D.R.rS + 1 + D.R.rS)} (h : piv D.R.rS a = iz) : a = iz := by
  have := congrArg (piv D.R.rS) h
  rwa [piv_invol D.R.rS a, piv_iz] at this

theorem gramE_apply (a b : Fin (D.R.rS + 1 + D.R.rS)) :
    gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) a b = if piv D.R.rS a = b then cD X u' a else 0 := by
  rw [gram_eq, diagonal_mul]
  simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def,
    Option.some.injEq, Function.Involutive.coe_toPerm]
  by_cases h : piv D.R.rS a = b <;> simp [h]

theorem cD_iz : cD X u' (iz (D := D)) = -((Tw u' : ℕ) : X.B.I.E) := by
  simp [cD, iz]

def diagonalShiftOneMinus (a : Fin (D.R.rS + 1 + D.R.rS)) : X.B.I.E :=
  if a.val = D.R.rS then 1 - ((Tw u' : ℕ) : X.B.I.E) else 1

theorem prod_diagonalShiftOneMinus : ∏ a, diagonalShiftOneMinus X u' a = 1 - ((Tw u' : ℕ) : X.B.I.E) := by
  rw [Finset.prod_eq_single (iz (D := D))]
  · simp [diagonalShiftOneMinus, iz]
  · intro b _ hb
    have : b.val ≠ D.R.rS := fun e => hb (Fin.ext e)
    simp [diagonalShiftOneMinus, this]
  · simp

end PI.OmVg
end
end

noncomputable section

namespace PI.OmVg

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  NumberField IsDedekindDomain Matrix PI.OmLocU Formalism.L2.SG.Pf.NcVal.OmVSt Formalism.L2.SG.Pf.NcVal.OmVSt.OmW
open scoped TensorProduct

theorem natCast_val_lt {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (t : ℕ)
    (ht : ((t : 𝓞 F)) ∈ v.asIdeal) : Valued.v ((t : ℕ) : Fv F v) < 1 := by
  have h1 : ((t : ℕ) : Fv F v) = algebraMap (𝓞 F) (Fv F v) (t : 𝓞 F) := by simp
  rw [h1]
  refine (HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := F) v (t : 𝓞 F)).trans_lt ?_
  erw [HeightOneSpectrum.valuation_of_algebraMap]
  exact (HeightOneSpectrum.intValuation_lt_one_iff_mem v _).2 ht

variable {D : D7} (X : HidaSetting D) (u' : D.what₂.Word)

theorem localGramMatrixFrame_apply (v : PlX X) (a b : Fin (D.R.rS + 1 + D.R.rS)) :
    localGramMatrixFrame X u' v a b = inclR (Fv X.B.I.F v) (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) a b) := rfl

theorem negT_mem (v : PlX X) (hv : ((Tw u' : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal) {ϖ : Fv X.B.I.F v}
    (hϖ : IsUnif v ϖ) : inclR (Fv X.B.I.F v) (-((Tw u' : ℕ) : X.B.I.E)) ∈ PO (E := X.B.I.E) v ϖ := by
  obtain ⟨h0, -, -⟩ := unif_spec v ϖ hϖ
  have hm := natCast_div_mem v (Tw u') hv hϖ
  refine ⟨sc (E := X.B.I.E) v (-(((Tw u' : ℕ) : Fv X.B.I.F v) * ϖ⁻¹)), ?_, ?_⟩
  · simpa using sc_mul_mem_oEv v (neg_mem hm) (Orb.oSub (E := X.B.I.E) v).1
  · rw [sc_mul]
    have e : ϖ * -(((Tw u' : ℕ) : Fv X.B.I.F v) * ϖ⁻¹) = -((Tw u' : ℕ) : Fv X.B.I.F v) := by field_simp
    rw [e, show sc (E := X.B.I.E) v (-((Tw u' : ℕ) : Fv X.B.I.F v)) =
      algebraMap (Fv X.B.I.F v) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) (-((Tw u' : ℕ) : Fv X.B.I.F v)) from rfl,
      map_neg, map_neg, map_natCast, map_natCast]

theorem local_gram_matrix_corank_one (v : PlX X) (hv : ((Tw u' : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal) {ϖ : Fv X.B.I.F v}
    (hϖ : IsUnif v ϖ) : GramCor v ϖ (localGramMatrixFrame X u' v) := by
  have hN := negT_mem X u' v hv hϖ
  have h0 : (0 : Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) ∈ PO (E := X.B.I.E) v ϖ :=
    ⟨0, Orb.oev_zero v, by rw [mul_zero]⟩
  refine ⟨iz, fun j => ?_, fun j => ?_, ?_⟩
  · rw [localGramMatrixFrame_apply, gramE_apply, piv_iz]
    split_ifs with h
    · rw [cD_iz]; exact hN
    · rw [map_zero]; exact h0
  · rw [localGramMatrixFrame_apply, gramE_apply]
    split_ifs with h
    · rw [eq_iz_of_piv h, cD_iz]; exact hN
    · rw [map_zero]; exact h0
  · set P := (Function.Involutive.toPerm _ (piv_invol D.R.rS)).permMatrix X.B.I.E with hPdef
    have hM : localGramMatrixFrame X u' v + Matrix.single iz iz 1 = (diagonal (diagonalShiftOneMinus X u') * P).map (inclR (Fv X.B.I.F v)) := by
      ext a b
      rw [Matrix.add_apply, localGramMatrixFrame_apply, gramE_apply, Matrix.map_apply, diagonal_mul, Matrix.single_apply]
      simp only [hPdef, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def,
        Option.some.injEq, Function.Involutive.coe_toPerm]
      by_cases ha : a = iz
      · subst ha
        rw [piv_iz]
        by_cases hb : iz = b
        · subst hb
          rw [cD_iz]
          simp [diagonalShiftOneMinus, iz]
          ring
        · simp [hb]
      · have hav : a.val ≠ D.R.rS := fun e => ha (Fin.ext e)
        have h1 : ¬ (iz = a ∧ iz = b) := fun h => ha h.1.symm
        simp [cD, diagonalShiftOneMinus, hav, h1]
    obtain ⟨s, hs, hPd⟩ : ∃ s : ℤ, s * s = 1 ∧ P.det = (s : X.B.I.E) :=
      ⟨((Equiv.Perm.sign (Function.Involutive.toPerm _ (piv_invol D.R.rS)) : ℤˣ) : ℤ),
        by rw [← Units.val_mul, Int.units_mul_self, Units.val_one], by rw [hPdef, det_permutation]⟩
    have hdet : (localGramMatrixFrame X u' v + Matrix.single iz iz 1).det =
        inclR (Fv X.B.I.F v) ((1 - ((Tw u' : ℕ) : X.B.I.E)) * (s : X.B.I.E)) := by
      rw [hM, ← RingHom.mapMatrix_apply, ← RingHom.map_det, det_mul, det_diagonal, prod_diagonalShiftOneMinus, hPd]
    set t : Fv X.B.I.F v := 1 - ((Tw u' : ℕ) : Fv X.B.I.F v) with htdef
    have hv1 : Valued.v t = 1 := Valuation.map_one_sub_of_lt _ (natCast_val_lt v _ hv)
    have ht0 : t ≠ 0 := fun h => by rw [h, map_zero] at hv1; exact zero_ne_one hv1
    have hti : t⁻¹ ∈ v.adicCompletionIntegers X.B.I.F := by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hv1, inv_one]
    refine ⟨sc (E := X.B.I.E) v t⁻¹ * inclR (Fv X.B.I.F v) (((s : 𝓞 X.B.I.E)) : X.B.I.E),
      sc_mul_mem_oEv v hti (inclR_mem_OEv X v _), ?_⟩
    rw [hdet]
    have e1 : inclR (Fv X.B.I.F v) (1 - ((Tw u' : ℕ) : X.B.I.E)) = sc (E := X.B.I.E) v t := by
      rw [htdef, show sc (E := X.B.I.E) v (1 - ((Tw u' : ℕ) : Fv X.B.I.F v)) =
        algebraMap (Fv X.B.I.F v) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) (1 - ((Tw u' : ℕ) : Fv X.B.I.F v)) from rfl,
        map_sub, map_sub, map_one, map_one, map_natCast, map_natCast]
    have e2 : (((s : 𝓞 X.B.I.E)) : X.B.I.E) = (s : X.B.I.E) := by simp
    rw [e2, map_mul, e1]
    calc sc (E := X.B.I.E) v t * inclR (Fv X.B.I.F v) (s : X.B.I.E) *
          (sc (E := X.B.I.E) v t⁻¹ * inclR (Fv X.B.I.F v) (s : X.B.I.E))
        = (sc (E := X.B.I.E) v t * sc (E := X.B.I.E) v t⁻¹) * inclR (Fv X.B.I.F v) ((s : X.B.I.E) * s) := by
          rw [map_mul]; ring
      _ = 1 := by
          rw [sc_mul, mul_inv_cancel₀ ht0, sc_one, ← Int.cast_mul, hs, Int.cast_one, map_one, mul_one]

end PI.OmVg
end
end

noncomputable section

namespace PI.OmVg

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  NumberField IsDedekindDomain PI.OmLocU PI.OmVd Formalism.L2.SG.Pf.NcVal.OmVSt

variable {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ)

theorem redP_holds : ∀ v : PlX X, ((Tw u' : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal →
    RedP X.B.I.cm.sig X.B.I.J ψ v (abelian₂ X) (D.R.rS + 1 + D.R.rS) (yTup X u' v) := fun v hv =>
  redP_of_gramCor X.B.I.cm.sig X.B.I.J ψ v (abelian₂ X) _ _ (fun ϖ hϖ => by
    rw [OmW.omVGram_holds X u' v]
    exact local_gram_matrix_corank_one X u' v hv hϖ)

theorem omVBadT_of_ffX (hStd : Formalism.L2.SG.Pf.NcX.OmVSt.OmVStd X ψ) (hLat : Formalism.L2.SG.Pf.NcX.OmVSt.OmVLat X)
    (hGram : Formalism.L2.SG.Pf.NcX.OmVSt.OmVGram X u') (hFI : FFInertB) (hFS : FFSplitB) :
    Formalism.L2.SG.Pf.NcX.OmVSt.OmVBadT X u' ψ :=
  PI.OmVf.omVBadT_of_restX X u' ψ hStd hLat hGram (redP_holds X u' ψ) hFI hFS

end PI.OmVg
