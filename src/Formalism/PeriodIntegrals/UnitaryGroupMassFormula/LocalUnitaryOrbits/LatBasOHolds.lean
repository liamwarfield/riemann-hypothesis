module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.MemUnifOIff

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.LatBasOHolds
noncomputable section

namespace PI.OmLocU

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

theorem exists_basO (L : Submodule (𝓞 E) (Fin n → E)) (hLat : Submodule.IsFullLattice E L) :
    ∃ (m : ℕ) (b : Fin m → Fin n → Fv F v ⊗[F] E), LinearIndependent (Fv F v) b ∧
      (∀ x, x ∈ latLoc (E := E) v (L : Set (Fin n → E)) ↔
        ∃ c : Fin m → v.adicCompletionIntegers F, x = ∑ i, (c i : Fv F v) • b i) ∧
      ⊤ ≤ Submodule.span (Fv F v) (Set.range b) := by
  classical
  set M := latLoc (E := E) v (L : Set (Fin n → E)) with hM
  have : Module.Finite (v.adicCompletionIntegers F) M := Module.Finite.iff_fg.2 (basLat_fg v L hLat.toIsLattice)
  have : Module.IsTorsionFree (v.adicCompletionIntegers F) (Fin n → Fv F v ⊗[F] E) :=
    Module.IsTorsionFree.of_smul_eq_zero fun r x h => by
      have h' : (r : Fv F v) • x = 0 := h
      rcases smul_eq_zero.1 h' with h0 | h0
      · exact Or.inl (Subtype.ext h0)
      · exact Or.inr h0
  have : Module.Free (v.adicCompletionIntegers F) M := Module.free_of_finite_type_torsion_free'
  let bM := Module.finBasis (v.adicCompletionIntegers F) M
  let b0 : Fin (Module.finrank (v.adicCompletionIntegers F) M) → Fin n → Fv F v ⊗[F] E := fun i => (bM i : _)
  have hli0 : LinearIndependent (v.adicCompletionIntegers F) b0 :=
    bM.linearIndependent.map' M.subtype (Submodule.ker_subtype M)
  have hli : LinearIndependent (Fv F v) b0 :=
    (LinearIndependent.iff_fractionRing (v.adicCompletionIntegers F) (Fv F v)).1 hli0
  have hmem : ∀ x, x ∈ M ↔ ∃ c : Fin (Module.finrank (v.adicCompletionIntegers F) M) → v.adicCompletionIntegers F,
      x = ∑ i, (c i : Fv F v) • b0 i := by
    intro x
    constructor
    · intro hx
      refine ⟨fun i => bM.repr ⟨x, hx⟩ i, ?_⟩
      have h := congrArg Subtype.val (bM.sum_repr ⟨x, hx⟩)
      rw [Submodule.coe_sum] at h
      exact h.symm.trans (Finset.sum_congr rfl fun i _ => rfl)
    · rintro ⟨c, rfl⟩
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem M (c i) (bM i).2
  refine ⟨_, b0, hli, hmem, ?_⟩
  rw [← basSpan_top v L hLat, Submodule.span_le]
  intro x hx
  obtain ⟨c, rfl⟩ := (hmem x).1 hx
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem latBasO_holds
    (hFull : ∃ L : Submodule (𝓞 E) (Fin n → E),
      Submodule.IsFullLattice E L ∧ (L : Set (Fin n → E)) = Λ)
    (a : ℕ) (Y : TupV (E := E) v n a) : LatBasO σ J ψ v Λ a Y := by
  classical
  rintro ⟨⟨hCM, -⟩, -, -⟩
  obtain ⟨L, hLat, rfl⟩ := hFull
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have h2 : Module.finrank F E = 2 := hCM.2.2.1
  obtain ⟨m, b, hli, hmem, hsp⟩ := exists_basO v L hLat
  have hm : m = 2 * n := by
    have h1 := Module.finrank_eq_card_basis (Module.Basis.mk hli hsp)
    rw [Fintype.card_fin] at h1
    rw [← h1, Module.finrank_pi_fintype]
    simp only [Module.finrank_baseChange, h2, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    ring
  subst hm
  exact ⟨b, hli, hmem⟩

end PI.OmLocU
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.EtaVCases
noncomputable section

namespace PI.OmLocU.Red

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain Formalism.UG
open PI.VolStabSW PI.OmLocU
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F))

abbrev IE : Ideal (𝓞 E) := v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E))

abbrev QE : Type := 𝓞 E ⧸ IE (E := E) v

def sigO : 𝓞 E →+* 𝓞 E := RingOfIntegers.mapRingHom (σ : E →+* E)

theorem sigO_coe (x : 𝓞 E) : (sigO σ x : E) = σ (x : E) := rfl

theorem sigO_alg (a : 𝓞 F) : sigO σ (algebraMap (𝓞 F) (𝓞 E) a) = algebraMap (𝓞 F) (𝓞 E) a := by
  apply RingOfIntegers.ext
  rw [sigO_coe]
  show σ (algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) a)) = algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) a)
  rw [← IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 E) E, IsScalarTower.algebraMap_apply (𝓞 F) F E]
  exact σ.commutes _

theorem IE_le : IE (E := E) v ≤ (IE (E := E) v).comap (sigO σ) := by
  rw [← Ideal.map_le_iff_le_comap, Ideal.map_map]
  have hc : (sigO σ).comp (algebraMap (𝓞 F) (𝓞 E)) = algebraMap (𝓞 F) (𝓞 E) := RingHom.ext (sigO_alg σ)
  rw [hc]

def sigQ : QE (E := E) v →+* QE (E := E) v := Ideal.quotientMap (IE (E := E) v) (sigO σ) (IE_le σ v)

theorem sigQ_mk (x : 𝓞 E) : sigQ σ v (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (sigO σ x) := rfl

theorem sig_sig (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2 τ, h.2.2.2 τ, star_star]

theorem sigQ_sigQ (h : IsCMExt F E σ) (x : QE (E := E) v) : sigQ σ v (sigQ σ v x) = x := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [sigQ_mk, sigQ_mk]
  congr 1
  apply RingOfIntegers.ext
  simp only [sigO_coe]
  exact sig_sig σ h _

theorem sigQ_alg (c : 𝓞 F ⧸ v.asIdeal) :
    sigQ σ v (algebraMap (𝓞 F ⧸ v.asIdeal) (QE (E := E) v) c) = algebraMap (𝓞 F ⧸ v.asIdeal) (QE (E := E) v) c := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
  rw [Ideal.Quotient.algebraMap_quotient_map_quotient, sigQ_mk, sigO_alg]

def ResQ : Prop :=
  StdHyp σ J ψ → UnramAt (E := E) v → ∀ ϖ : Fv F v, IsUnif v ϖ →
    ∃ ρ : OR (E := E) v →+* QE (E := E) v, IsRes σ v ϖ (sigQ σ v) ρ

def EtaLink : Prop :=
  StdHyp σ J ψ → UnramAt (E := E) v → (etaV (E := E) v = 1 ↔ ¬ (IE (E := E) v).IsPrime)

def QInert : Prop :=
  StdHyp σ J ψ → UnramAt (E := E) v → (IE (E := E) v).IsPrime → sigQ σ v ≠ RingHom.id _

def QSplit : Prop :=
  StdHyp σ J ψ → UnramAt (E := E) v → ¬ (IE (E := E) v).IsPrime →
    ∃ e : QE (E := E) v ≃+* (𝓞 F ⧸ v.asIdeal) × (𝓞 F ⧸ v.asIdeal), ∀ x, e (sigQ σ v x) = (e x).swap

theorem card_res : Nat.card (𝓞 F ⧸ v.asIdeal) = Ideal.absNorm v.asIdeal := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]

theorem finite_res : Finite (𝓞 F ⧸ v.asIdeal) := by
  apply Nat.finite_of_card_ne_zero
  rw [card_res]
  exact fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.mp h)

theorem IE_ne_bot : IE (E := E) v ≠ ⊥ := by
  exact Ideal.map_ne_bot_of_ne_bot v.ne_bot

end PI.OmLocU.Red
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.GramInvOHolds
noncomputable section

namespace PI.OmLocU

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F))

def oEvS : Submodule (v.adicCompletionIntegers F) (Fv F v ⊗[F] E) :=
  Submodule.span (v.adicCompletionIntegers F)
    ((fun x : 𝓞 E => inclR (F := F) (Fv F v) (x : E)) '' Set.univ)

theorem oEvS_fg : (oEvS (E := E) v).FG := by
  let g : 𝓞 E →+ (Fv F v ⊗[F] E) :=
    (inclR (F := F) (Fv F v)).toAddMonoidHom.comp (algebraMap (𝓞 E) E).toAddMonoidHom
  have hfg : (Submodule.map g.toIntLinearMap ⊤).FG := Submodule.FG.map _ Module.Finite.fg_top
  obtain ⟨t, ht⟩ := hfg
  have himg : (fun x : 𝓞 E => inclR (F := F) (Fv F v) (x : E)) '' Set.univ =
      ↑(Submodule.map g.toIntLinearMap ⊤) := by
    ext y
    simp [g] <;> rfl
  refine ⟨t, ?_⟩
  unfold oEvS
  rw [himg, ← ht, Submodule.span_span_of_tower]

theorem oEv_one : (1 : Fv F v ⊗[F] E) ∈ OEv (E := E) v := by
  unfold OEv
  exact Submodule.subset_span ⟨1, Set.mem_univ _, by simp⟩

theorem one_add_inv {ϖ : Fv F v} (hϖ : IsUnif v ϖ) {x : Fv F v ⊗[F] E} (hx : x ∈ OEv (E := E) v) :
    ∃ m ∈ OEv (E := E) v, (1 + sc (E := E) v ϖ * x) * m = 1 := by
  have hϖi : ϖ ∈ v.adicCompletionIntegers F := by
    unfold IsUnif at hϖ
    rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, hϖ, ← WithZero.coe_one,
      WithZero.coe_le_coe]
    show Multiplicative.ofAdd (-1 : ℤ) ≤ Multiplicative.ofAdd 0
    exact Multiplicative.ofAdd_le.mpr (by norm_num)
  have hsc : ∀ z : Fv F v ⊗[F] E,
      sc (E := E) v ϖ * z = (⟨ϖ, hϖi⟩ : v.adicCompletionIntegers F) • z := by
    intro z
    unfold sc
    rw [Algebra.smul_def]
    rfl
  have hcomm : ∀ (r : v.adicCompletionIntegers F) (a b : Fv F v ⊗[F] E), a * (r • b) = r • (a * b) :=
    fun r a b => mul_smul_comm r a b
  let y := 1 + sc (E := E) v ϖ * x
  let N' : Submodule (v.adicCompletionIntegers F) (Fv F v ⊗[F] E) :=
    Submodule.span (v.adicCompletionIntegers F) ((fun m => y * m) '' (OEv (E := E) v))
  have hN'sub : ∀ z ∈ N', ∃ m ∈ OEv (E := E) v, z = y * m := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨m, hm, rfl⟩ := hz
      exact ⟨m, hm, rfl⟩
    | zero => exact ⟨0, oEv_zero v, (mul_zero y).symm⟩
    | add a b _ _ ha hb =>
      obtain ⟨m1, hm1, rfl⟩ := ha
      obtain ⟨m2, hm2, rfl⟩ := hb
      exact ⟨m1 + m2, oEv_add v hm1 hm2, (mul_add y m1 m2).symm⟩
    | smul r a _ ha =>
      obtain ⟨m, hm, rfl⟩ := ha
      refine ⟨r • m, ?_, (hcomm r y m).symm⟩
      unfold OEv at hm ⊢
      exact Submodule.smul_mem _ r hm
  have hle : oEvS (E := E) v ≤ N' := by
    apply Submodule.le_of_le_smul_of_le_jacobson_bot (oEvS_fg v)
      (IsLocalRing.maximalIdeal_le_jacobson _)
    intro m hm
    have hm' : m ∈ OEv (E := E) v := hm
    have hxm : x * m ∈ oEvS (E := E) v := oEv_mul v hx hm'
    have h1 : y * m ∈ N' := Submodule.subset_span ⟨m, hm', rfl⟩
    have h2 : (-(⟨ϖ, hϖi⟩ : v.adicCompletionIntegers F)) • (x * m) ∈
        IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) • oEvS (E := E) v := by
      apply Submodule.smul_mem_smul _ hxm
      apply neg_mem
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      rintro ⟨u, hu⟩
      have hmul := congrArg (fun z : v.adicCompletionIntegers F => Valued.v (z : Fv F v)) u.mul_inv
      simp only [MulMemClass.coe_mul, OneMemClass.coe_one, map_mul, map_one] at hmul
      have hui : Valued.v (((u⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F) : Fv F v) ≤ 1 :=
        (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (u⁻¹ : (v.adicCompletionIntegers F)ˣ).1.2
      rw [hu] at hmul
      unfold IsUnif at hϖ
      change Valued.v ϖ * _ = 1 at hmul
      rw [hϖ] at hmul
      have hlt : (↑(Multiplicative.ofAdd (-1 : ℤ)) : WithZero (Multiplicative ℤ)) < 1 := by
        rw [← WithZero.coe_one, WithZero.coe_lt_coe]
        show Multiplicative.ofAdd (-1 : ℤ) < Multiplicative.ofAdd 0
        exact Multiplicative.ofAdd_lt.mpr (by norm_num)
      have hcon : (1 : WithZero (Multiplicative ℤ)) ≤ ↑(Multiplicative.ofAdd (-1 : ℤ)) := by
        calc (1 : WithZero (Multiplicative ℤ)) = _ := hmul.symm
          _ ≤ ↑(Multiplicative.ofAdd (-1 : ℤ)) * 1 := by gcongr
          _ = _ := mul_one _
      exact absurd hcon (not_le.mpr hlt)
    have hdecomp : m = y * m + (-(⟨ϖ, hϖi⟩ : v.adicCompletionIntegers F)) • (x * m) := by
      rw [neg_smul, ← hsc]
      simp only [y]
      ring
    rw [hdecomp]
    exact Submodule.add_mem_sup h1 h2
  have h1 : (1 : Fv F v ⊗[F] E) ∈ N' := hle (oEv_one v)
  obtain ⟨m, hm, hm1⟩ := hN'sub 1 h1
  exact ⟨m, hm, hm1.symm⟩

section Main

variable (Λ : Set (Fin n → E)) (ψ : AddChar (AF F) ℂ)

def oEvR : Subring (Fv F v ⊗[F] E) where
  carrier := OEv (E := E) v
  mul_mem' := oEv_mul v
  one_mem' := oEv_one v
  add_mem' := oEv_add v
  zero_mem' := oEv_zero v
  neg_mem' := oEv_neg v

theorem det_sub_mem {a : ℕ} {ϖ : Fv F v} (hint : ϖ ∈ v.adicCompletionIntegers F)
    (A B : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) (hA : ∀ i j, A i j ∈ OEv (E := E) v)
    (hB : ∀ i j, B i j ∈ OEv (E := E) v) (hAB : ∀ i j, A i j - B i j ∈ PO (E := E) v ϖ) :
    A.det - B.det ∈ PO (E := E) v ϖ := by
  have hsc : sc (E := E) v ϖ ∈ OEv (E := E) v := by
    have h1 := oEv_one (E := E) v
    unfold OEv at h1 ⊢
    have h2 := Submodule.smul_mem _ (⟨ϖ, hint⟩ : v.adicCompletionIntegers F) h1
    convert h2 using 1
    simp [sc, Algebra.smul_def, Algebra.TensorProduct.one_def]
  let A' : Matrix (Fin a) (Fin a) (oEvR (E := E) v) := fun i j => ⟨A i j, hA i j⟩
  let B' : Matrix (Fin a) (Fin a) (oEvR (E := E) v) := fun i j => ⟨B i j, hB i j⟩
  let s : oEvR (E := E) v := ⟨sc (E := E) v ϖ, hsc⟩
  have hdA : ((A'.det : oEvR (E := E) v) : Fv F v ⊗[F] E) = A.det := by
    calc ((A'.det : oEvR (E := E) v) : Fv F v ⊗[F] E) = (oEvR (E := E) v).subtype A'.det := rfl
      _ = ((oEvR (E := E) v).subtype.mapMatrix A').det := RingHom.map_det _ _
      _ = A.det := rfl
  have hdB : ((B'.det : oEvR (E := E) v) : Fv F v ⊗[F] E) = B.det := by
    calc ((B'.det : oEvR (E := E) v) : Fv F v ⊗[F] E) = (oEvR (E := E) v).subtype B'.det := rfl
      _ = ((oEvR (E := E) v).subtype.mapMatrix B').det := RingHom.map_det _ _
      _ = B.det := rfl
  have hmem : A'.det - B'.det ∈ Ideal.span {s} := by
    rw [← Ideal.Quotient.eq, RingHom.map_det, RingHom.map_det]
    congr 1
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply]
    rw [Ideal.Quotient.eq, Ideal.mem_span_singleton']
    obtain ⟨c, hc, hceq⟩ := hAB i j
    refine ⟨⟨c, hc⟩, Subtype.ext ?_⟩
    show c * sc (E := E) v ϖ = A i j - B i j
    rw [hceq, mul_comm]
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp hmem
  show ∃ c ∈ OEv (E := E) v, A.det - B.det = sc (E := E) v ϖ * c
  refine ⟨b, b.2, ?_⟩
  rw [← hdA, ← hdB]
  calc ((A'.det : oEvR (E := E) v) : Fv F v ⊗[F] E) - B'.det
      = ((A'.det - B'.det : oEvR (E := E) v) : Fv F v ⊗[F] E) := rfl
    _ = ((b * s : oEvR (E := E) v) : Fv F v ⊗[F] E) := by rw [hb]
    _ = sc (E := E) v ϖ * b := by
      show (b : Fv F v ⊗[F] E) * sc (E := E) v ϖ = _
      exact mul_comm _ _

theorem gramInvO_holds (a : ℕ) (Y : TupV (E := E) v n a) : GramInvO σ J v Λ ψ a Y := by
  intro hG ϖ hϖ y hy hd
  unfold GoodY at hG
  have hSD := hG.2.2.1
  have hy' : ∀ i, y i ∈ latLoc (E := E) v Λ := hy
  have hϖi : ϖ ∈ v.adicCompletionIntegers F := by
    unfold IsUnif at hϖ
    rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, hϖ, ← WithZero.coe_one,
      WithZero.coe_le_coe]
    show Multiplicative.ofAdd (-1 : ℤ) ≤ Multiplicative.ofAdd 0
    exact Multiplicative.ofAdd_le.mpr (by norm_num)
  have hsc : sc (E := E) v ϖ ∈ OEv (E := E) v := by
    have h1 := oEv_one (E := E) v
    unfold OEv at h1 ⊢
    have h2 := Submodule.smul_mem _ (⟨ϖ, hϖi⟩ : v.adicCompletionIntegers F) h1
    convert h2 using 1
    simp [sc, Algebra.smul_def, Algebra.TensorProduct.one_def]
  have hyI : ∀ i j, gramR (Fv F v) σ J y i j ∈ OEv (E := E) v := fun i j =>
    hR_mem_oEv (σ := σ) (J := J) (v := v) (Λ := Λ) hSD (hy' i) (hy' j)
  have hYI : ∀ i j, gramR (Fv F v) σ J Y i j ∈ OEv (E := E) v := by
    intro i j
    obtain ⟨c, hc, hceq⟩ := hd i j
    have e : gramR (Fv F v) σ J Y i j = gramR (Fv F v) σ J y i j + -(sc (E := E) v ϖ * c) := by
      rw [← hceq]
      ring
    rw [e]
    exact oEv_add v (hyI i j) (oEv_neg v (oEv_mul v hsc hc))
  obtain ⟨w, hw, -, hdw⟩ := hG.2.2.2.2.2.2
  obtain ⟨c, hc, hceq⟩ := det_sub_mem v hϖi (gramR (Fv F v) σ J y) (gramR (Fv F v) σ J Y) hyI hYI hd
  have hwc : w * c ∈ OEv (E := E) v := oEv_mul v hw hc
  obtain ⟨m, hm, hm1⟩ := one_add_inv v hϖ hwc
  have e1 : (gramR (Fv F v) σ J y).det =
      (gramR (Fv F v) σ J Y).det + sc (E := E) v ϖ * c := by
    rw [← hceq]
    ring
  have e2 : (gramR (Fv F v) σ J y).det =
      (gramR (Fv F v) σ J Y).det * (1 + sc (E := E) v ϖ * (w * c)) := by
    linear_combination e1 - (sc (E := E) v ϖ * c) * hdw
  have hdy1 : (m * w) * (gramR (Fv F v) σ J y).det = 1 := by
    calc (m * w) * (gramR (Fv F v) σ J y).det
        = (gramR (Fv F v) σ J Y).det * w * ((1 + sc (E := E) v ϖ * (w * c)) * m) := by
          rw [e2]
          ring
      _ = 1 := by rw [hdw, hm1, one_mul]
  let A' : Matrix (Fin a) (Fin a) (oEvR (E := E) v) := fun i j => ⟨gramR (Fv F v) σ J y i j, hyI i j⟩
  have hadj : ∀ i j, (gramR (Fv F v) σ J y).adjugate i j ∈ OEv (E := E) v := by
    intro i j
    have e : (gramR (Fv F v) σ J y).adjugate = (oEvR (E := E) v).subtype.mapMatrix A'.adjugate := by
      rw [RingHom.map_adjugate]
      rfl
    rw [e]
    exact (A'.adjugate i j).2
  refine ⟨(m * w) • (gramR (Fv F v) σ J y).adjugate, fun i j => ?_, ?_⟩
  · rw [Matrix.smul_apply, smul_eq_mul]
    exact oEv_mul v (oEv_mul v hm hw) (hadj i j)
  · rw [Matrix.mul_smul, Matrix.mul_adjugate, smul_smul, hdy1, one_smul]

end Main

end PI.OmLocU
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.OmLocUOfOnto
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.FibTop
noncomputable section

namespace PI.OmLocU

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

theorem omLocU_of' (a : ℕ) (Y : TupV (E := E) v n a)
    (hSd : (StdHyp σ J ψ → (∃ μ, SdW F E σ n J (Fv F v) (psiV F ψ v) a μ) ∧ ∃ ν, SdHerm F E σ (Fv F v) (psiV F ψ v) a ν))
    (hOm : OmUnique σ J ψ v a) (hU : UnifEx v)
    (h1 : OrbAll σ J ψ v Λ a Y) (h2 : FibU' σ J ψ v Λ a Y) (h3 : CountU σ J ψ v Λ a Y)
    (h4 : SdVolW σ J ψ v Λ a) (h5 : SdVolH σ J ψ v a) :
    Formalism.L2.SG.Pf.NcLoc.OmLocU σ J ψ v Λ a Y := by
  have h2' : FibU σ J ψ v Λ a Y := by
    intro hG hfib ϖ hϖ
    obtain ⟨hW, hH⟩ := hSd hG.1
    exact h2 hG hW hH hfib ϖ hϖ
  exact omLocU_of σ J ψ v Λ a Y hSd hOm hU h1 h2' h3 h4 h5

theorem omLocU_of_fib (a : ℕ) (Y : TupV (E := E) v n a)
    (hSd : (StdHyp σ J ψ → (∃ μ, SdW F E σ n J (Fv F v) (psiV F ψ v) a μ) ∧ ∃ ν, SdHerm F E σ (Fv F v) (psiV F ψ v) a ν))
    (hOm : OmUnique σ J ψ v a)
    (h1 : OrbAll σ J ψ v Λ a Y) (hL : LamOC v Λ a) (hH : HermOC σ v a) (hHe : FibHens σ J ψ v Λ a Y)
    (h3 : CountU σ J ψ v Λ a Y) (h4 : SdVolW σ J ψ v Λ a) (h5 : SdVolH σ J ψ v a) :
    Formalism.L2.SG.Pf.NcLoc.OmLocU σ J ψ v Λ a Y :=
  omLocU_of' σ J ψ v Λ a Y hSd hOm (unifEx_holds v) h1 (fibU'_of σ J ψ v Λ a Y hL hH hHe) h3 h4 h5

theorem omLocU_of_hens (a : ℕ) (Y : TupV (E := E) v n a)
    (hSd : (StdHyp σ J ψ → (∃ μ, SdW F E σ n J (Fv F v) (psiV F ψ v) a μ) ∧ ∃ ν, SdHerm F E σ (Fv F v) (psiV F ψ v) a ν))
    (hOm : OmUnique σ J ψ v a) (h1 : OrbAll σ J ψ v Λ a Y)
    (hFull : ∃ L : Submodule (𝓞 E) (Fin n → E),
      Submodule.IsFullLattice E L ∧ (L : Set (Fin n → E)) = Λ)
    (hHe : FibHens σ J ψ v Λ a Y)
    (h3 : CountU σ J ψ v Λ a Y) (h4 : SdVolW σ J ψ v Λ a) (h5 : SdVolH σ J ψ v a) :
    Formalism.L2.SG.Pf.NcLoc.OmLocU σ J ψ v Λ a Y :=
  omLocU_of_fib σ J ψ v Λ a Y hSd hOm h1 (lamOC_holds v Λ a hFull) (hermOC_holds v σ a) hHe h3 h4 h5

end PI.OmLocU
end
end

noncomputable section

namespace PI.OmLocU

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

theorem omLocU_of_onto (a : ℕ) (Y : TupV (E := E) v n a)
    (hSd : (StdHyp σ J ψ → (∃ μ, SdW F E σ n J (Fv F v) (psiV F ψ v) a μ) ∧ ∃ ν, SdHerm F E σ (Fv F v) (psiV F ψ v) a ν))
    (hOm : OmUnique σ J ψ v a) (h1 : OrbAll σ J ψ v Λ a Y) (hO : HensOnto σ J v Λ ψ a Y)
    (hFull : ∃ L : Submodule (𝓞 E) (Fin n → E),
      Submodule.IsFullLattice E L ∧ (L : Set (Fin n → E)) = Λ)
    (h3 : CountU σ J ψ v Λ a Y) (h4 : SdVolW σ J ψ v Λ a) (h5 : SdVolH σ J ψ v a) :
    Formalism.L2.SG.Pf.NcLoc.OmLocU σ J ψ v Λ a Y :=
  omLocU_of_hens σ J ψ v Λ a Y hSd hOm h1 hFull (fibHens_of σ J v Λ ψ a Y hO) h3 h4 h5

theorem omLocU_of_tr (a : ℕ) (Y : TupV (E := E) v n a)
    (hSd : (StdHyp σ J ψ → (∃ μ, SdW F E σ n J (Fv F v) (psiV F ψ v) a μ) ∧ ∃ ν, SdHerm F E σ (Fv F v) (psiV F ψ v) a ν))
    (hOm : OmUnique σ J ψ v a) (h1 : OrbAll σ J ψ v Λ a Y) (hGI : GramInvO σ J v Λ ψ a Y) (hTr : TrOnto σ v)
    (hFull : ∃ L : Submodule (𝓞 E) (Fin n → E),
      Submodule.IsFullLattice E L ∧ (L : Set (Fin n → E)) = Λ)
    (h3 : CountU σ J ψ v Λ a Y) (h4 : SdVolW σ J ψ v Λ a) (h5 : SdVolH σ J ψ v a) :
    Formalism.L2.SG.Pf.NcLoc.OmLocU σ J ψ v Λ a Y :=
  omLocU_of_onto σ J ψ v Λ a Y hSd hOm h1 (hensOnto_of σ J v Λ ψ a Y hGI hTr) hFull h3 h4 h5

end PI.OmLocU
end
end
