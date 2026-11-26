module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasNormGroups
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TrueColumnChoicesHeckeCharReferenceEqOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MixedLaplacianKillsProductOfMinors
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ArBirational
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsDefiniteOfAllPlus
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodTupleConditionOfIdempotentZero

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeightEqOfFinitePartNeBot
noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

namespace GlobalTheory.DefU

theorem isIrreducible_sqRep (n : ℕ) (mu : DomWeight n) : (GlobalTheory.Branching.sqRep ℂ n mu).IsIrreducible := by
  have hU := GlobalTheory.Branching.isIrreducible_smallRep_unitary n mu
  obtain ⟨hn, hs⟩ := (CuspRep.isIrreducible_iff _).1 hU
  exact (CuspRep.isIrreducible_iff _).2 ⟨hn, fun S hS => hs S fun u => hS _⟩

theorem rhoK_tenMul {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) (g : ι → GL (Fin n) ℂ)
    (u : ∀ τ, nablaSq ℂ n (lam τ)) :
    Formalism.L2.DIV.rhoK lam g (GlobalTheory.CoefIrred.tenMul lam u) =
      GlobalTheory.CoefIrred.tenMul lam fun τ => GlobalTheory.Branching.sqRep ℂ n (lam τ) (g τ) (u τ) := by
  apply Subtype.ext
  rw [Formalism.L2.DIV.rhoK_coe, GlobalTheory.CoefIrred.tenMul_coe, GlobalTheory.CoefIrred.tenMul_coe, Formalism.L2.DIV.actTen]
  rfl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem cAll_of_mem_embU {v u : InfinitePlace E} (huv : u ≠ v) {x : UA E n} (hx : x ∈ embU n v.embedding) :
    cAll x u = 1 := by
  have h := (Subgroup.mem_inf.1 hx).2
  rw [Subgroup.mem_iInf] at h
  have h2 := h u.embedding
  rw [Subgroup.mem_iInf] at h2
  exact h2 (by simpa using huv)

theorem embU_le_infU (τ : E →+* ℂ) : embU n τ ≤ infU E n := inf_le_left

theorem rep_tenMul_update [DecidableEq (InfinitePlace E)] (W : Wt E n) (v : InfinitePlace E) (x : infU E n)
    (hx : x.1 ∈ embU n v.embedding) (e : ∀ u, nablaSq ℂ n (W u)) (a : nablaSq ℂ n (W v)) :
    W.rep x (GlobalTheory.CoefIrred.tenMul W (Function.update e v a)) =
      GlobalTheory.CoefIrred.tenMul W (Function.update e v (GlobalTheory.Branching.sqRep ℂ n (W v) (cEmb v.embedding x.1) a)) := by
  change Formalism.L2.DIV.rhoK W (cAll x.1) _ = _
  rw [rhoK_tenMul]
  congr 1
  funext u
  by_cases h : u = v
  · subst h
    simp only [Function.update_self]
    rfl
  · simp only [Function.update_of_ne h, cAll_of_mem_embU h hx, map_one, Module.End.one_apply]

theorem hasWeightAt_of_finPart (π : AutSub E n) (W : Wt E n) {f : algForms W} (hf : f ∈ π.finPart W) (hf0 : f ≠ 0)
    (v : InfinitePlace E) : HasWeightAt π.V v.embedding (W v) := by
  classical
  obtain ⟨e, he⟩ : ∃ e, f.1 (GlobalTheory.CoefIrred.tenMul W e) ≠ 0 := by
    by_contra hc
    push Not at hc
    have h1 : f.1 = 0 := by
      apply (Formalism.L2.DIV.bVV ℂ W).ext
      intro i
      have hb : Formalism.L2.DIV.bVV ℂ W i = GlobalTheory.CoefIrred.tenMul W
          (fun τ => GlobalTheory.CoefIrred.ssBasis ℂ (W τ) (i τ)) := by
        apply Subtype.ext
        rw [Formalism.L2.DIV.bVV_coe, GlobalTheory.CoefIrred.tenMul_coe,
          Formalism.L2.DIV.bVVfun]
        simp only [GlobalTheory.CoefIrred.ssBasis_coe]
      rw [hb]
      exact hc _
    exact hf0 (Subtype.ext h1)
  refine ⟨isIrreducible_sqRep n (W v), f.1 ∘ₗ (GlobalTheory.CoefIrred.tenMul W).toLinearMap e v, fun h0 => he ?_, fun a => ?_,
    fun x a => ?_⟩
  · have := LinearMap.congr_fun h0 (e v)
    simpa [MultilinearMap.toLinearMap] using this
  · exact AutSub.mem_finPart.1 hf _
  · have hx : x.1 ∈ infU E n := embU_le_infU _ x.2
    have h2 := f.2.2 ⟨x.1, hx⟩ (GlobalTheory.CoefIrred.tenMul W (Function.update e v a))
    rw [rep_tenMul_update W v ⟨x.1, hx⟩ x.2] at h2
    exact h2

end GlobalTheory.DefU

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinAfMemIntUIff
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.Mem GlobalTheory.Mem.Col2
open ReciprocityTheory.Neutral.Bridge.HCFR hiding infIdele
open Neutral.B1 hiding localIdele locF
open GlobalTheory.Mem.Chr hiding Ideles aboveF IsUnitAt atFin HChar HChar.UnrAt HChar.resFin HChar.resInf atInf upF IsDelta
open scoped TensorProduct

namespace GlobalTheory.Mem.ReadTwist

section General

open Formalism.L2.DIV GlobalTheory.Mem.LocTriv

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem afIso_finAf_apply (a : Ideles E) (P : HeightOneSpectrum (𝓞 E)) :
    afIso F E (finAf F E a : AfE F E) P = ev P (a : AdeleRing (𝓞 E) E) := by
  rw [afIso_finAf]
  rfl

theorem mem_above {v : HeightOneSpectrum (𝓞 F)} {P : HeightOneSpectrum (𝓞 E)} :
    P ∈ aboveF (L := E) F v ↔ P.under (𝓞 F) = v := by
  unfold aboveF
  rw [Set.Finite.mem_toFinset]
  rfl

theorem finAf_mem_intU_iff (a : Ideles E) : finAf F E a ∈ intU F E ↔ a ∈ unitIdl E := by
  unfold intU
  rw [Submonoid.mem_units_iff, ← map_inv]
  change (finAf F E a : AfE F E) ∈ RInt F E ∧ (finAf F E a⁻¹ : AfE F E) ∈ RInt F E ↔ _
  simp only [mem_rInt_iff, afIso_finAf]
  refine ⟨fun h P => le_antisymm (h.1 P) ?_, fun h => ⟨fun P => (h P).le, fun P => ((unitIdl E).inv_mem h P).le⟩⟩
  have h1 : (a : AdeleRing (𝓞 E) E).2 P * ((a⁻¹ : Ideles E) : AdeleRing (𝓞 E) E).2 P = 1 :=
    congrArg (fun z : AdeleRing (𝓞 E) E => z.2 P) a.mul_inv
  have h2 := congrArg (Valued.v : Valuation (P.adicCompletion E) _) h1
  rw [map_mul, map_one] at h2
  rw [← h2]
  exact mul_le_of_le_one_right' (h.2 P)

theorem local_mem_suppAt (P : HeightOneSpectrum (𝓞 E)) (x : (P.adicCompletion E)ˣ) :
    finAf F E (localIdele E P x) ∈ suppAt E (P.under (𝓞 F)) := by
  rw [mem_suppAt_iff]
  intro Q hQ
  rw [afIso_finAf_apply]
  exact ev_local_ne (fun e => hQ (by rw [e])) x

theorem local_mem_unitIdl {P : HeightOneSpectrum (𝓞 E)} {x : (P.adicCompletion E)ˣ} (hx : IsUnitAt P x) :
    localIdele E P x ∈ unitIdl E := fun Q => by
  change Valued.v (ev Q (localIdele E P x : AdeleRing (𝓞 E) E)) = 1
  by_cases h : Q = P
  · subst h
    rw [ev_local_self]
    exact hx
  · rw [ev_local_ne h, map_one]

theorem finAf_part {v : HeightOneSpectrum (𝓞 F)} {a : Ideles E} (ha : finAf F E a ∈ suppAt E v) :
    finAf F E (part a (aboveF (L := E) F v)) = finAf F E a := by
  refine Units.ext ((afIso F E).injective (FiniteAdeleRing.ext _ fun P => ?_))
  rw [afIso_finAf_apply]
  by_cases h : P ∈ aboveF (L := E) F v
  · rw [ev_part_mem a h, afIso_finAf_apply]
  · rw [ev_part_not_mem a h]
    exact ((mem_suppAt_iff F E v _).1 ha P fun e => h (mem_above.2 e)).symm

theorem plc_dvd_iff (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) : Formalism.EigenvalueLevelCeiling.plc v ∣ n ↔ (n : 𝓞 F) ∈ v.asIdeal := by
  unfold Formalism.EigenvalueLevelCeiling.plc
  rw [← ringChar.spec, ← map_natCast (Ideal.Quotient.mk v.asIdeal), Ideal.Quotient.eq_zero_iff_mem]

theorem plc_ne_zero (v : HeightOneSpectrum (𝓞 F)) : Formalism.EigenvalueLevelCeiling.plc v ≠ 0 := fun h => by
  have h1 := (plc_dvd_iff v _).2 (Ideal.absNorm_mem v.asIdeal)
  rw [h, zero_dvd_iff] at h1
  exact v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h1)

theorem plc_under_eq_iff (P : HeightOneSpectrum (𝓞 E)) {p : ℕ} (hp : p.Prime) :
    Formalism.EigenvalueLevelCeiling.plc (P.under (𝓞 F)) = p ↔ (p : 𝓞 E) ∈ P.asIdeal := by
  have h1 : (p : 𝓞 E) ∈ P.asIdeal ↔ (p : 𝓞 F) ∈ (P.under (𝓞 F)).asIdeal := by
    rw [← map_natCast (algebraMap (𝓞 F) (𝓞 E))]
    rfl
  rw [h1, ← plc_dvd_iff, Nat.dvd_prime hp]
  refine ⟨Or.inr, fun h => h.resolve_left fun e => ?_⟩
  have h2 := (plc_dvd_iff (P.under (𝓞 F)) 1).1 (by rw [e])
  rw [Nat.cast_one] at h2
  exact (P.under (𝓞 F)).isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h2)

theorem exists_under_eq (v : HeightOneSpectrum (𝓞 F)) : ∃ P : HeightOneSpectrum (𝓞 E), P.under (𝓞 F) = v := by
  have := v.isPrime
  obtain ⟨Q, hQ, hl⟩ := (Ideal.nonempty_primesOver v.asIdeal (S := 𝓞 E)).some
  exact ⟨⟨Q, hQ, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩, HeightOneSpectrum.ext hl.over.symm⟩

theorem local_mem_wildAt {P : HeightOneSpectrum (𝓞 E)} {x : (P.adicCompletion E)ˣ} (hx : IsUnitAt P x)
    (h1 : Valued.v ((x : P.adicCompletion E) - 1) ≤ WithZero.exp (-1 : ℤ)) :
    finAf F E (localIdele E P x) ∈ wildAt E (P.under (𝓞 F)) := by
  refine ⟨?_, local_mem_suppAt P x⟩
  have hu := (finAf_mem_intU_iff (F := F) _).2 (local_mem_unitIdl hx)
  set y := finAf F E (localIdele E P x) with hy
  have hu1 : (y : AfE F E) ∈ RInt F E := hu.1
  have hu2 : ((y⁻¹ : (AfE F E)ˣ) : AfE F E) ∈ RInt F E := hu.2
  refine ⟨⟨⟨_, hu1⟩, ⟨_, hu2⟩, Subtype.ext y.mul_inv, Subtype.ext y.inv_mul⟩, ?_, Units.ext rfl⟩
  rw [SetLike.mem_coe, mem_kerRed]
  set p := Formalism.EigenvalueLevelCeiling.plc (P.under (𝓞 F)) with hp
  have hp0 : (p : E) ≠ 0 := Nat.cast_ne_zero.2 (plc_ne_zero _)
  have hv0 : Valued.v (algebraMap E (P.adicCompletion E) (p : E)⁻¹) ≠ 0 :=
    (Valuation.ne_zero_iff _).2 ((map_ne_zero _).2 (inv_ne_zero hp0))
  obtain ⟨m, hm⟩ : ∃ m : ℕ, Valued.v (algebraMap E (P.adicCompletion E) (p : E)⁻¹) ≤ WithZero.exp (m : ℤ) := by
    refine ⟨(WithZero.log (Valued.v (algebraMap E (P.adicCompletion E) (p : E)⁻¹))).toNat, ?_⟩
    conv_lhs => rw [← WithZero.exp_log hv0]
    exact WithZero.exp_le_exp.2 (Int.self_le_toNat _)
  have hw : (p : E)⁻¹ ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F) * ((y : AfE F E) - 1) ^ (m + 1) ∈ RInt F E := by
    rw [mem_rInt_iff]
    intro Q
    rw [map_mul, map_pow, map_sub, map_one, afIso_tmul_one]
    change Valued.v (algebraMap E (Q.adicCompletion E) (p : E)⁻¹ * (afIso F E (y : AfE F E) Q - 1) ^ (m + 1)) ≤ 1
    rw [hy, afIso_finAf_apply]
    by_cases h : Q = P
    · subst h
      rw [ev_local_self, map_mul, map_pow]
      refine (mul_le_mul' hm (pow_le_pow_left' h1 _)).trans ?_
      rw [← WithZero.exp_nsmul, ← WithZero.exp_add, ← WithZero.exp_zero, WithZero.exp_le_exp]
      simp
    · rw [ev_local_ne h]
      simp
  refine ⟨m + 1, Ideal.mem_span_singleton'.2 ⟨⟨_, hw⟩, Subtype.ext ?_⟩⟩
  change (p : E)⁻¹ ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F) * ((y : AfE F E) - 1) ^ (m + 1) * ((p : RInt F E) : AfE F E) =
    ((y : AfE F E) - 1) ^ (m + 1)
  have e : ((p : RInt F E) : AfE F E) = (p : E) ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F) :=
    (SubringClass.coe_natCast _ _).trans (map_natCast (Algebra.TensorProduct.includeLeftRingHom (R := F) (A := E)
      (B := FiniteAdeleRing (𝓞 F) F)) p).symm
  rw [e, mul_right_comm, Algebra.TensorProduct.tmul_mul_tmul, inv_mul_cancel₀ hp0, mul_one,
    ← Algebra.TensorProduct.one_def, one_mul]

theorem afIso_one_tmul (a : FiniteAdeleRing (𝓞 F) F) (k : F) (P : HeightOneSpectrum (𝓞 E))
    (h : a (P.under (𝓞 F)) = algebraMap F _ k) :
    afIso F E (1 ⊗ₜ[F] a) P = algebraMap E _ (algebraMap F E k) := by
  have h4 := (GlobalTheory.AdeleBaseChange.exists_finiteAdele_baseChange_equiv F E).choose_spec.2.2.2 a k P
  change ∀ n : ℕ, _ → Valued.v (afIso F E (1 ⊗ₜ[F] a) P - _) ≤ _ at h4
  by_contra hne
  have h0 := (Valuation.ne_zero_iff (Valued.v : Valuation (P.adicCompletion E) _)).2 (sub_ne_zero.2 hne)
  have h5 := h4 ((-WithZero.log (Valued.v (afIso F E (1 ⊗ₜ[F] a) P - algebraMap E _ (algebraMap F E k)))).toNat + 1)
    (by rw [h, sub_self, map_zero]; exact zero_le')
  rw [← WithZero.exp_log h0, WithZero.exp_le_exp, WithZero.log_exp] at h5
  omega

theorem finAf_locF_mem (v : HeightOneSpectrum (𝓞 F)) (k : Fˣ) :
    finAf F E (locF F v k) ∈ (idF F E).range := by
  refine ⟨Units.map (RingHom.snd (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)).toMonoidHom (localIdele F v (atFin v k)), Units.ext ((afIso F E).injective (FiniteAdeleRing.ext _ fun P => ?_))⟩
  rw [afIso_finAf_apply, locF, Units.coe_prod, map_prod]
  change afIso F E (1 ⊗ₜ[F] ((localIdele F v (atFin v k) : Ideles F) : AdeleRing (𝓞 F) F).2) P = _
  have hloc : ∀ (Q : HeightOneSpectrum (𝓞 E)) (x : (Q.adicCompletion E)ˣ),
      ev P (Neutral.B1.localIdele E Q x : AdeleRing (𝓞 E) E) = ev P (localIdele E Q x : AdeleRing (𝓞 E) E) := by
    intro Q x
    by_cases hPQ : P = Q
    · subst hPQ; exact (Neutral.B1.localIdele_snd_self E P x).trans (ev_local_self P x).symm
    · exact ((Neutral.B1.localIdele_isSupportedAt E Q x).2 P hPQ).trans (ev_local_ne hPQ x).symm
  simp_rw [hloc]
  by_cases h : P ∈ aboveF (L := E) F v
  · rw [Finset.prod_eq_single_of_mem P h (fun Q _ hQ => ev_local_ne hQ.symm _), ev_local_self]
    obtain rfl := mem_above.1 h
    exact afIso_one_tmul _ (k : F) P (ev_local_self (P.under (𝓞 F)) (atFin _ k))
  · rw [Finset.prod_eq_one fun Q hQ => ev_local_ne (fun e : P = Q => h (e ▸ hQ)) _,
      afIso_one_tmul _ 1 P ((ev_local_ne (fun e => h (mem_above.2 e)) (atFin v k)).trans (map_one _).symm),
      map_one, map_one]

variable {K : Type} [Field K] {σ : K →+* ℂ} {μ : Chr F E K} {ξ : HChar E}

theorem pow_eq_one_iff (h : Reads σ μ ξ) (a : Ideles E) (n : ℕ) : ξ.1 a ^ n = 1 ↔ μ (finAf F E a) ^ n = 1 := by
  rw [Units.ext_iff, Units.ext_iff, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, h a, ← map_pow, Units.val_one,
    Units.val_one, map_eq_one_iff σ σ.injective]

theorem eq_one_iff (h : Reads σ μ ξ) (a : Ideles E) : ξ.1 a = 1 ↔ μ (finAf F E a) = 1 := by
  simpa using pow_eq_one_iff h a 1

theorem inert_pow_iff (h : Reads σ μ ξ) (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) :
    (∀ y ∈ inertAt E v, μ y ^ n = 1) ↔
      ∀ P : HeightOneSpectrum (𝓞 E), P.under (𝓞 F) = v → ∀ x, IsUnitAt P x → ξ.loc P x ^ n = 1 := by
  constructor
  · rintro hy P rfl x hx
    exact (pow_eq_one_iff h _ n).2
      (hy _ ⟨(finAf_mem_intU_iff _).2 (local_mem_unitIdl hx), local_mem_suppAt P x⟩)
  · intro hP y hy
    obtain ⟨a, rfl⟩ := finAf_surjective F E y
    rw [← finAf_part hy.2, ← pow_eq_one_iff h, part, map_prod, ← Finset.prod_pow]
    exact Finset.prod_eq_one fun P hPv => hP P (mem_above.1 hPv) _ ((finAf_mem_intU_iff a).1 hy.1 P)

theorem mem_qprime_iff (h : Reads σ μ ξ) (v : HeightOneSpectrum (𝓞 F)) :
    v ∈ Qprime μ ↔ ∃ P : HeightOneSpectrum (𝓞 E), P.under (𝓞 F) = v ∧ ¬ ξ.UnrAt P := by
  have h1 := inert_pow_iff h v 1
  simp only [pow_one] at h1
  refine (not_congr h1).trans ?_
  simp only [not_forall, exists_prop, HChar.UnrAt]

theorem tameAt (h : Reads σ μ ξ) (hw : ∀ v : HeightOneSpectrum (𝓞 F), wildAt E v ≤ μ.ker)
    (P : HeightOneSpectrum (𝓞 E)) : ξ.TameAt P := fun x hx h1 =>
  (eq_one_iff h _).2 (hw _ (local_mem_wildAt hx (by simpa using h1)))

theorem trivOn (h : Reads σ μ ξ) (hF : (idF F E).range ≤ μ.ker) : ξ.TrivOn F := by
  constructor
  · intro v k
    have h1 := (eq_one_iff h _).2 (hF (finAf_locF_mem v k))
    rw [locF, map_prod] at h1
    rw [HChar.resFin, MonoidHom.finsetProd_apply]
    exact h1
  · intro w k
    rw [HChar.resInf, MonoidHom.finsetProd_apply]
    refine Finset.prod_eq_one fun w' _ => (eq_one_iff h (infIdele E w' (atInf w' (upF F k)))).2 ?_
    have e : finAf F E (infIdele E w' (atInf w' (upF F k))) = 1 :=
      Units.ext ((afIso F E).injective (by rw [afIso_finAf, Units.val_one, map_one]; rfl))
    rw [e, map_one]

end General

theorem isTwist_of_reads : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (K : Type) [Field K] (σ : K →+* ℂ) (S : Set ℕ) (μ : Formalism.L2.DIV.Tup H.F H.E K S) (ξ : HChar H.E), Reads σ (μ.1 : Formalism.L2.DIV.Chr H.F H.E K) ξ → IsTwist H S ξ ∧ (∀ v : HeightOneSpectrum (𝓞 H.F), v ∈ Formalism.L2.DIV.Qprime (μ.1 : Formalism.L2.DIV.Chr H.F H.E K) ↔ ∃ P : HeightOneSpectrum (𝓞 H.E), P.under (𝓞 H.F) = v ∧ ¬ ξ.UnrAt P) ∧ ∀ p : ℕ, p.Prime → (Formalism.L2.DIV.IsBaseChar p (μ.1 : Formalism.L2.DIV.Chr H.F H.E K) ↔ IsDelta (H := H) p ξ) := by
  intro R H K _ σ S μ ξ h
  obtain ⟨⟨⟨⟨-, hfin⟩, hF⟩, hw⟩, hg⟩ := μ.2
  have htw : IsTwist H S ξ := by
    refine ⟨?_, trivOn h hF, tameAt h fun v => Subgroup.mem_iInf.1 hw v, fun P hP => ?_⟩
    · obtain ⟨n, hn, e⟩ := isOfFinOrder_iff_pow_eq_one.1 hfin
      exact ⟨n, hn, h.orderDvd e⟩
    · rw [← GlobalTheory.Mem.GoodPlace.goodPl_under_iff]
      by_contra hn
      exact (mem_qprime_iff h _).2 ⟨P, rfl, hP⟩ (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hg _) hn)
  refine ⟨htw, mem_qprime_iff h, fun p hp => ⟨fun hb => ⟨htw.1, htw.2.1, htw.2.2.1, fun P hP => ?_, fun P hP n => ?_⟩,
    fun hd => ⟨hp, fun v => ⟨fun hv n => ?_, fun hv hq => ?_⟩⟩⟩⟩
  · by_contra hn
    exact (hb.2 _).2 (fun e => hP ((plc_under_eq_iff P hp).1 e)) ((mem_qprime_iff h _).2 ⟨P, rfl, hn⟩)
  · rw [← (hb.2 _).1 ((plc_under_eq_iff (F := H.F) P hp).2 hP) n, inert_pow_iff h]
    exact ⟨fun hx Q hQ => twist_pow_units_of_under_eq R H S ξ htw Q P hQ n hx, fun hx => hx P rfl⟩
  · rw [inert_pow_iff h]
    obtain ⟨P, rfl⟩ := exists_under_eq (E := H.E) v
    exact ⟨fun hx => (hd.ine P ((plc_under_eq_iff P hp).1 hv) n).1 (hx P rfl),
      fun hn Q hQ => (hd.ine Q ((plc_under_eq_iff (F := H.F) Q hp).1 (hQ ▸ hv)) n).2 hn⟩
  · obtain ⟨P, rfl, hP⟩ := (mem_qprime_iff h _).1 hq
    exact hP (hd.unr P fun e => hv ((plc_under_eq_iff P hp).2 e))

end GlobalTheory.Mem.ReadTwist

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdmissibleLocalComponentDefiniteUnitary
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdmissibleLocalComponentDefiniteUnitary
noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

namespace GlobalTheory.DefU.LocAdm

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem continuous_finGL : Continuous (finGL E n) := by
  refine Continuous.units_map _ ?_
  have hs : Continuous (sFin E : Af E → Ad E) :=
    (continuous_const.prodMk continuous_id : Continuous fun x : Af E => ((0, x) : InfiniteAdeleRing E × Af E))
  exact (continuous_const.add (continuous_id.matrix_map hs) :
    Continuous fun x : Matrix (Fin n) (Fin n) (Af E) => 1 - matN n (sFin E) 1 + x.map (sFin E))

theorem t2Space_finiteAdeleRing_cmField : T2Space (FiniteAdeleRing (𝓞 E) E) :=
  inferInstanceAs (T2Space (RestrictedProduct (fun v : HeightOneSpectrum (𝓞 E) => v.adicCompletion E)
    (fun v => (v.adicCompletionIntegers E : Set (v.adicCompletion E))) Filter.cofinite))

theorem t2Space_adeleRing_cmField : T2Space (Ad E) :=
  haveI := t2Space_finiteAdeleRing_cmField (E := E)
  haveI : T2Space (InfiniteAdeleRing E) := inferInstanceAs (T2Space ((v : InfinitePlace E) → v.Completion))
  inferInstanceAs (T2Space (InfiniteAdeleRing E × FiniteAdeleRing (𝓞 E) E))

theorem t2Space_adelicGL_cmField : T2Space (GA E n) :=
  haveI := t2Space_adeleRing_cmField (E := E)
  Units.isEmbedding_embedProduct.t2Space

theorem isClosed_UA : IsClosed ((UA E n : Subgroup (GA E n)) : Set (GA E n)) := by
  haveI := t2Space_adeleRing_cmField (E := E)
  show IsClosed {g : GA E n | ((g : Matrix (Fin n) (Fin n) (Ad E)).map (conjAd E))ᵀ * 1 * (g : Matrix (Fin n) (Fin n) (Ad E)) = 1}
  exact isClosed_eq (((Units.continuous_val.matrix_map GlobalTheory.ThetaPull.continuous_conjAd).matrix_transpose.matrix_mul
    continuous_const).matrix_mul Units.continuous_val) continuous_const

theorem locU_le_finU (w : HeightOneSpectrum (𝓞 E)) : locU n w ≤ finU (E := E) (n := n) := inf_le_left

theorem continuous_inclusion_locU (w : HeightOneSpectrum (𝓞 E)) :
    Continuous (Subgroup.inclusion (locU_le_finU (n := n) w)) :=
  Continuous.subtype_mk continuous_subtype_val _

theorem isClosed_of_retract (w : HeightOneSpectrum (𝓞 E)) (r : UA E n →* locU n w) (hr : Continuous r)
    (hx : ∀ x : locU n w, r x = x) : IsClosed ((locU n w : Subgroup (UA E n)) : Set (UA E n)) := by
  haveI := t2Space_adelicGL_cmField (E := E) (n := n)
  have e : ((locU n w : Subgroup (UA E n)) : Set (UA E n)) = {x | ((r x : locU n w) : UA E n) = x} := by
    ext x
    constructor
    · intro h
      exact congrArg Subtype.val (hx ⟨x, h⟩)
    · intro h
      change x ∈ locU n w
      rw [← show ((r x : locU n w) : UA E n) = x from h]
      exact (r x).2

  rw [e]
  exact isClosed_eq (continuous_subtype_val.comp hr) continuous_id

theorem isSmooth_loc (π : AutSub E n) (w : HeightOneSpectrum (𝓞 E)) :
    IsSmooth (π.rep.comp (locU n w).subtype) := fun v => by
  have h := (π.isAut.aut v.1 v.2).level
  convert h.preimage (continuous_inclusion_locU (n := n) w) using 1
  ext k
  exact Subtype.ext_iff

theorem exists_compact_open (w : HeightOneSpectrum (𝓞 E)) (r : UA E n →* locU n w) (hr : Continuous r)
    (hx : ∀ x : locU n w, r x = x) (L : Subgroup (finU (E := E) (n := n))) (hL : IsOpen (L : Set (finU (E := E) (n := n)))) :
    ∃ K : Subgroup (locU n w), IsOpen (K : Set (locU n w)) ∧ IsCompact (K : Set (locU n w)) ∧
      K ≤ L.comap (Subgroup.inclusion (locU_le_finU w)) := by
  obtain ⟨U0, hU0o, hU0c⟩ := GlobalTheory.GLIntegral.exists_isOpen_isCompact E n
  let p : locU n w →* GL (Fin n) (Af E) :=
    (GeneralLinearGroup.map (pFin E)).comp ((UA E n).subtype.comp (locU n w).subtype)
  have hp : Continuous p := continuous_map_pFin.comp (continuous_subtype_val.comp continuous_subtype_val)
  let K : Subgroup (locU n w) := U0.comap p ⊓ L.comap (Subgroup.inclusion (locU_le_finU w))
  have hKo : IsOpen (K : Set (locU n w)) :=
    (hU0o.preimage hp).inter (hL.preimage (continuous_inclusion_locU w))
  have hι : Topology.IsClosedEmbedding (fun x : locU n w => ((x : UA E n) : GA E n)) :=
    isClosed_UA.isClosedEmbedding_subtypeVal.comp (isClosed_of_retract w r hr hx).isClosedEmbedding_subtypeVal
  refine ⟨K, hKo, IsCompact.of_isClosed_subset (hι.isCompact_preimage (hU0c.image continuous_finGL))
    (Subgroup.isClosed_of_isOpen K hKo) fun x hx => ⟨p x, (Subgroup.mem_inf.1 hx).1, ?_⟩, inf_le_right⟩
  have h1 : GeneralLinearGroup.map (pInf E) ((x : UA E n) : GA E n) = 1 := (Subgroup.mem_inf.1 x.2).1
  exact ga_ext (by rw [pInf_finGL, h1]) (by rw [pFin_finGL]; rfl)

theorem exists_admissible_comp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : AutSub E n)
    (w : HeightOneSpectrum (𝓞 E)), ∃ σ : SmIrr (locU n w), IsAdmissible σ.ρ ∧
      IsCompAlong π.V (locU n w) (MonoidHom.id _) σ.ρ := by
  intro E _ _ _ n π w
  obtain ⟨r, hr, hrx, hrc⟩ := GlobalTheory.T.exists_continuous_retraction_onto_unitaryLocalPoints E n w
  have hadm := (GlobalTheory.T.definiteUnitary_admissible_finiteMultiplicity E n π).1
  let ρ : Representation ℂ (locU n w) π.V := π.rep.comp (locU n w).subtype
  let ρf : Representation ℂ (finU (E := E) (n := n)) π.V := π.rep.comp (finU (E := E) (n := n)).subtype
  have hρ : IsSmooth ρ := isSmooth_loc π w
  have hle := locU_le_finU (n := n) w
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 π.isAut.ne_bot
  let v0 : π.V := ⟨φ, hφ⟩
  have hv0 : v0 ≠ 0 := fun e => h0 (congrArg Subtype.val e)
  let L : Subgroup (finU (E := E) (n := n)) := LocEx.stab ρf v0
  have hLo : IsOpen (L : Set (finU (E := E) (n := n))) := by
    convert (π.isAut.aut φ hφ).level using 1
    ext k
    exact Subtype.ext_iff
  have hLl : IsOpen ((L.comap (Subgroup.inclusion hle) : Subgroup (locU n w)) : Set (locU n w)) :=
    hLo.preimage (continuous_inclusion_locU w)
  obtain ⟨K, hKo, hKc, hKL⟩ := exists_compact_open w r hr hrx L hLo

  have hT : ∀ x : UA E n, ∀ (g : locU n w) (y : π.V),
      π.rep ((r x : UA E n)⁻¹ * x) (ρ g y) = ρ g (π.rep ((r x : UA E n)⁻¹ * x) y) := fun x g y => by
    change π.rep _ (π.rep (g : UA E n) y) = π.rep (g : UA E n) (π.rep _ y)
    rw [← Module.End.mul_apply, ← map_mul, (hrc x g).eq, map_mul, Module.End.mul_apply]
  have hst : ∀ x, ∀ y ∈ LocEx.nullPart ρ K, π.rep x y ∈ LocEx.nullPart ρ K := fun x y hy => by
    have h1 := LocEx.nullPart_act ρ K (r x) (LocEx.nullPart_comm ρ K (π.rep ((r x : UA E n)⁻¹ * x)) (hT x) hy)
    have e : π.rep x y = ρ (r x) (π.rep ((r x : UA E n)⁻¹ * x) y) := by
      change _ = π.rep (r x : UA E n) _
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]
    rw [e]
    exact h1
  have hφK : v0 ∈ fixed ρ K := LocEx.mem_fix.2 fun k hk => hKL hk
  have h2 : ∀ W : Submodule ℂ π.V, (∀ g, ∀ v ∈ W, ρ g v ∈ W) → W ⊓ fixed ρ K = ⊥ → W = ⊥ := by
    intro W hW h
    rcases ((CuspRep.isIrreducible_iff _).1 π.isIrreducible_rep).2 (LocEx.nullPart ρ K) hst with h1 | h1
    · exact le_bot_iff.1 (h1 ▸ LocEx.le_nullPart hρ hKc W hW h)
    · exact absurd (LocEx.eq_zero_of_mem_nullPart hρ hKc hφK (h1 ▸ Submodule.mem_top)) hv0

  let M : Subgroup (UA E n) := L.map (finU (E := E) (n := n)).subtype ⊓ r.ker
  have hcomm : ∀ k ∈ M, ∀ g : locU n w, Commute k (g : UA E n) := fun k hk g => by
    have h := hrc k g
    rwa [MonoidHom.mem_ker.1 (Subgroup.mem_inf.1 hk).2, OneMemClass.coe_one, inv_one, one_mul] at h
  have hU : ∀ g, ∀ v ∈ fixed π.rep M, ρ g v ∈ fixed π.rep M := fun g v hv => LocEx.mem_fix.2 fun k hk => by
    change π.rep k (π.rep (g : UA E n) v) = π.rep (g : UA E n) v
    rw [← Module.End.mul_apply, ← map_mul, (hcomm k hk g).eq, map_mul, Module.End.mul_apply,
      LocEx.mem_fix.1 hv k hk]
  have hU0 : fixed π.rep M ≠ ⊥ := (Submodule.ne_bot_iff _).2 ⟨v0, LocEx.mem_fix.2 fun k hk => by
    obtain ⟨k', hk', rfl⟩ := (Subgroup.mem_inf.1 hk).1
    exact hk', hv0⟩
  have hfin : ∀ K' : Subgroup (locU n w), IsOpen (K' : Set (locU n w)) →
      FiniteDimensional ℂ ↥(fixed π.rep M ⊓ fixed ρ K') := fun K' hK' => by
    let r' : finU (E := E) (n := n) →* locU n w := r.comp (finU (E := E) (n := n)).subtype
    let H : Subgroup (finU (E := E) (n := n)) := L ⊓ (K' ⊓ L.comap (Subgroup.inclusion hle)).comap r'
    have hHo : IsOpen (H : Set (finU (E := E) (n := n))) := hLo.inter ((hK'.inter hLl).preimage (hr.comp continuous_subtype_val))
    haveI := hadm H hHo
    refine Submodule.finiteDimensional_of_le (S₂ := fixed ρf H) fun v hv => LocEx.mem_fix.2 fun k hk => ?_
    obtain ⟨hv1, hv2⟩ := Submodule.mem_inf.1 hv
    obtain ⟨hkL, hkK, hkL'⟩ := And.intro (Subgroup.mem_inf.1 hk).1 (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hk).2)
    have hcM : (r k : UA E n)⁻¹ * k ∈ M := by
      refine Subgroup.mem_inf.2 ⟨⟨(Subgroup.inclusion hle (r' k))⁻¹ * k, L.mul_mem (L.inv_mem hkL') hkL, rfl⟩, ?_⟩
      rw [MonoidHom.mem_ker, map_mul, map_inv, hrx (r k), inv_mul_cancel]
    have e1 := LocEx.mem_fix.1 hv1 _ hcM
    have e2 : π.rep (r k : UA E n) v = v := LocEx.mem_fix.1 hv2 _ hkK
    change π.rep (k : UA E n) v = v
    rw [← mul_inv_cancel_left (r k : UA E n) (k : UA E n), map_mul, Module.End.mul_apply, e1, e2]
  obtain ⟨σ, ⟨f, hf0, hf⟩, hσ⟩ := LocEx.exists_irred hρ hKo h2 (fixed π.rep M) hU hU0 hfin
  refine ⟨σ, hσ, σ.irred, π.V.subtype ∘ₗ f, fun e => hf0 (LinearMap.ext fun v => Subtype.ext ?_), fun v => (f v).2,
    fun x v => ?_⟩
  · exact LinearMap.congr_fun e v
  · change (f (σ.ρ x v)).1 = _
    rw [hf]
    rfl

end GlobalTheory.DefU.LocAdm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdmissibleLocalComponentDefiniteUnitaryStatement
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_admissible_localComponent_definiteUnitary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : AutSub E n) (w : HeightOneSpectrum (𝓞 E)), ∃ σ : SmIrr (locU n w), IsAdmissible σ.ρ ∧ IsCompAlong π.V (locU n w) (MonoidHom.id _) σ.ρ := by
  first | exact @GlobalTheory.DefU.LocAdm.exists_admissible_comp | exact GlobalTheory.DefU.LocAdm.exists_admissible_comp | (intros; apply GlobalTheory.DefU.LocAdm.exists_admissible_comp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasChernIntegralOfEqMul
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial MeasureTheory
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ENNReal

namespace GlobalTheory.ChernScale

section General

variable {α : Type*} [MeasurableSpace α] {κ : Sort*}

theorem restrict_iSup_eq (μ : κ → Measure α) {S : Set α} (hS : MeasurableSet S) :
    (⨆ i, μ i).restrict S = ⨆ i, (μ i).restrict S := by
  refine le_antisymm ?_ (iSup_le fun i => Measure.restrict_mono subset_rfl (le_iSup μ i))
  have h : (⨆ i, μ i) ≤ (⨆ i, (μ i).restrict S) + (⨆ i, μ i).restrict Sᶜ := by
    refine iSup_le fun i => Measure.le_iff.2 fun B hB => ?_
    rw [← Measure.restrict_add_restrict_compl (μ := μ i) hS, Measure.add_apply, Measure.add_apply]
    exact add_le_add (Measure.le_iff'.1 (le_iSup (fun i => (μ i).restrict S) i) B)
      (Measure.le_iff'.1 (Measure.restrict_mono subset_rfl (le_iSup μ i)) B)
  calc (⨆ i, μ i).restrict S ≤ ((⨆ i, (μ i).restrict S) + (⨆ i, μ i).restrict Sᶜ).restrict S :=
        Measure.restrict_mono subset_rfl h
    _ = (⨆ i, (μ i).restrict S).restrict S := by
        rw [Measure.restrict_add, Measure.restrict_restrict hS, Set.inter_compl_self,
          Measure.restrict_empty, add_zero]
    _ ≤ _ := Measure.restrict_le_self

theorem smul_iSup_eq (ν : κ → Measure α) {c : ℝ≥0∞} (hc : c ≠ ⊤) :
    c • (⨆ i, ν i) = ⨆ i, c • ν i := by
  have mono : ∀ (d : ℝ≥0∞) {μ μ' : Measure α}, μ ≤ μ' → d • μ ≤ d • μ' := fun d μ μ' h =>
    Measure.le_iff.2 fun s _ => by
      simp only [Measure.smul_apply, smul_eq_mul]
      exact mul_le_mul' le_rfl <| Measure.le_iff'.1 h s
  rcases eq_or_ne c 0 with rfl | h0
  · simp only [zero_smul]
    exact (le_antisymm (iSup_le fun _ => le_rfl) (Measure.zero_le _)).symm
  refine le_antisymm ?_ (iSup_le fun i => mono c (le_iSup ν i))
  have key : (⨆ i, ν i) ≤ c⁻¹ • ⨆ i, c • ν i := iSup_le fun i => by
    calc ν i = c⁻¹ • c • ν i := by rw [smul_smul, ENNReal.inv_mul_cancel h0 hc, one_smul]
      _ ≤ _ := mono _ (le_iSup (fun i => c • ν i) i)
  calc c • (⨆ i, ν i) ≤ c • c⁻¹ • ⨆ i, c • ν i := mono c key
    _ = _ := by rw [smul_smul, ENNReal.mul_inv_cancel h0 hc, one_smul]

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] {n : ℕ}

theorem chartMeas_restrict_eq (e : OpenPartialHomeomorph X (V n)) {ρ ρ' : X → ℝ≥0∞} {c : ℝ≥0∞}
    (hc : c ≠ ⊤) {S : Set X} (hS : MeasurableSet S) (h : ∀ y ∈ e.source, y ∈ S → ρ y = c * ρ' y) :
    (chartMeas e ρ).restrict S = c • (chartMeas e ρ').restrict S := by
  ext B hB
  rw [Measure.smul_apply, Measure.restrict_apply hB, Measure.restrict_apply hB, smul_eq_mul,
    chartMeas_apply e ρ (hB.inter hS), chartMeas_apply e ρ' (hB.inter hS), ← lintegral_const_mul' c _ hc]
  refine setLIntegral_congr_fun (measurableSet_image e (e.open_source.measurableSet.inter (hB.inter hS))
    Set.inter_subset_left) ?_
  rintro _ ⟨y, hy, rfl⟩
  show ρ (e.symm (e y)) = c * ρ' (e.symm (e y))
  rw [e.left_inv hy.1]
  exact h y hy.1 hy.2.2

theorem glueMeas_restrict_eq {ι : Type*} (e : ι → OpenPartialHomeomorph X (V n)) {ρ ρ' : ι → X → ℝ≥0∞}
    {c : ℝ≥0∞} (hc : c ≠ ⊤) {S : Set X} (hS : MeasurableSet S)
    (h : ∀ i, ∀ y ∈ (e i).source, y ∈ S → ρ i y = c * ρ' i y) :
    (glueMeas e ρ).restrict S = c • (glueMeas e ρ').restrict S := by
  rw [glueMeas, glueMeas, restrict_iSup_eq _ hS, restrict_iSup_eq _ hS, smul_iSup_eq _ hc]
  exact iSup_congr fun i => chartMeas_restrict_eq (e i) hc hS (h i)

end General

end GlobalTheory.ChernScale

namespace GlobalTheory.GoodMetric

open GlobalTheory.ChernScale

theorem hasChernIntegral_of_eq_mul : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {ι : Type} {m : ι → ℕ}
    (E : Fr (ratOf X) m 0) (O : X.X.Opens) (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ)
    (R R₀ : MvPolynomial (ι × ℕ) ℝ) (t v : ℝ),
    (∀ y ∈ ptsIn X.str σ O, ∀ c : AlgChart X.str σ X.dim, y ∈ c.e.source → ∀ A ∈ E.S (under y),
      chernTop R (fun w => H A (c.e.symm w)) (c.e y) = t * chernTop R₀ (fun w => H A (c.e.symm w)) (c.e y)) →
    HasChernIntegral E O H R₀ v → HasChernIntegral E O H R (t * v) := by
  intro F _ σ X ι m E O H R R₀ t v hRt hv
  have hP : MeasurableSet (ptsIn X.str σ O) := (isOpen_ptsIn O).measurableSet
  have key : ∀ (ε ε' : ℤˣ) (c : ℝ), 0 ≤ c → (∀ x : ℝ, ((ε : ℤ) : ℝ) * (t * x) = c * (((ε' : ℤ) : ℝ) * x)) →
      chernTopPart E H R ε (ptsIn X.str σ O) =
        ENNReal.ofReal c * chernTopPart E H R₀ ε' (ptsIn X.str σ O) := by
    intro ε ε' c hc hx
    have hm : (chernTopPart E H R ε).restrict (ptsIn X.str σ O) =
        ENNReal.ofReal c • (chernTopPart E H R₀ ε').restrict (ptsIn X.str σ O) :=
      glueMeas_restrict_eq _ ENNReal.ofReal_ne_top hP fun a y hy hyS => ?_
    · have := congrArg (fun μ : Measure (CxPts X.str σ) => μ (ptsIn X.str σ O)) hm
      simpa only [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply_self] using this
    · have e1 := hRt y hyS a hy _ (E.nonempty (under y)).choose_spec
      beta_reduce
      rw [e1, hx, ENNReal.ofReal_mul hc]
  rcases le_or_gt 0 t with ht | ht
  · refine ⟨fun ε => ?_, ?_⟩
    · rw [key ε ε t ht (fun x => by ring)]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hv.1 ε)
    · rw [← hv.2, measureReal_def, measureReal_def, measureReal_def, measureReal_def,
        key 1 1 t ht (fun x => by ring), key (-1) (-1) t ht (fun x => by ring),
        ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal ht]
      ring
  · have ht' : 0 ≤ -t := by linarith
    refine ⟨fun ε => ?_, ?_⟩
    · rw [key ε (-ε) (-t) ht' (fun x => by rw [Units.val_neg, Int.cast_neg]; ring)]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hv.1 _)
    · rw [← hv.2, measureReal_def, measureReal_def, measureReal_def, measureReal_def,
        key 1 (-1) (-t) ht' (fun x => by push_cast; ring), key (-1) 1 (-t) ht' (fun x => by push_cast; ring),
        ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal ht']
      ring

end GlobalTheory.GoodMetric
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalFieldNormValuation
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompletionNorm

variable {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))

theorem isEquiv_valued :
    (valuation (w.adicCompletion E)).IsEquiv
      (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))) := by
  have : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  exact isEquiv (valuation (w.adicCompletion E))
    (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ)))

theorem exists_unit_valued_eq :
    ∃ ϖ : (w.adicCompletion E)ˣ, Valued.v (ϖ : w.adicCompletion E) = WithZero.exp (-1) := by
  obtain ⟨π, hπ⟩ := w.valuation_exists_uniformizer E
  have h : Valued.v ((π : E) : w.adicCompletion E) = WithZero.exp (-1) := by
    rw [w.valuedAdicCompletion_eq_valuation']; exact hπ
  have h0 : ((π : E) : w.adicCompletion E) ≠ 0 := by
    intro h'; rw [h', map_zero] at h; exact WithZero.zero_ne_coe h
  exact ⟨Units.mk0 _ h0, h⟩

theorem le_exp_neg_one_of_lt_one {a : WithZero (Multiplicative ℤ)} (ha : a < 1) : a ≤ WithZero.exp (-1) := by
  by_cases h0 : a = 0
  · simp [h0]
  · rw [← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_lt_exp] at ha
    rw [← WithZero.exp_log h0, WithZero.exp_le_exp]
    omega

theorem valued_eq_exp (x : (w.adicCompletion E)ˣ) :
    Valued.v (x : w.adicCompletion E) = WithZero.exp (-ord (w.adicCompletion E) x) := by
  have he := isEquiv_valued w
  obtain ⟨ϖ, hϖ⟩ := exists_unit_valued_eq w
  have hϖ1 : Valued.v (ϖ : w.adicCompletion E) < 1 := by
    rw [hϖ, ← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
  have hu : valuation (w.adicCompletion E) (ϖ : w.adicCompletion E) = uniformizer (w.adicCompletion E) := by
    apply le_antisymm
    · exact le_uniformizer_iff.2 (he.lt_one_iff_lt_one.2 hϖ1)
    · obtain ⟨y, hy⟩ := valuation_surjective (uniformizer (w.adicCompletion E))
      rw [← hy]
      have hy1 : Valued.v y < 1 := he.lt_one_iff_lt_one.1 (hy ▸ uniformizer_lt_one)
      exact (he y ϖ).2 (hϖ ▸ le_exp_neg_one_of_lt_one hy1)
  have hord : ord (w.adicCompletion E) ϖ = 1 := SmGL.ord_eq_one hu
  let o : (w.adicCompletion E)ˣ →* Multiplicative ℤ :=
    MonoidHom.mk' (fun x => .ofAdd (ord (w.adicCompletion E) x)) fun x y => by rw [SmGL.ord_mul, ofAdd_add]
  set n := ord (w.adicCompletion E) x
  set u := x * ϖ ^ (-n)
  have hou : o u = 1 := by
    rw [map_mul, map_zpow, show o ϖ = .ofAdd 1 from congrArg Multiplicative.ofAdd hord, ← ofAdd_zsmul,
      smul_eq_mul, mul_one]
    show Multiplicative.ofAdd n * Multiplicative.ofAdd (-n) = 1
    rw [← ofAdd_add, add_neg_cancel, ofAdd_zero]
  have hu1 : valuation (w.adicCompletion E) (u : w.adicCompletion E) = 1 :=
    SmGL.ord_eq_zero_iff.1 (ofAdd_eq_one.1 hou)
  have hv1 : Valued.v (u : w.adicCompletion E) = 1 := he.eq_one_iff_eq_one.1 hu1
  have hx : x = u * ϖ ^ n := by simp [u]
  rw [hx, Units.val_mul, map_mul, hv1, one_mul, Units.val_zpow_eq_zpow_val, map_zpow₀, hϖ, ← WithZero.exp_zsmul,
    smul_eq_mul, mul_neg_one]

theorem normV_eq_absNorm : normV w = Ideal.absNorm w.asIdeal := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; rfl

theorem norm_eq_zpow (x : (w.adicCompletion E)ˣ) :
    ‖(x : w.adicCompletion E)‖ = ((normV w : ℕ) : ℝ) ^ (-ord (w.adicCompletion E) x) := by
  rw [FinitePlace.norm_def, valued_eq_exp, WithZeroMulInt.toNNReal_neg_apply _ (WithZero.exp_ne_zero (a := -ord (w.adicCompletion E) x)), WithZero.log_exp]
  simp [normV_eq_absNorm]

theorem one_lt_normV : 1 < normV w := by
  have := one_lt_resCard (w.adicCompletion E)
  rwa [GlobalTheory.LocLanglands.resCard_eq_normV] at this

theorem valuation_le_iff_norm_le (x y : w.adicCompletion E) :
    valuation (w.adicCompletion E) x ≤ valuation (w.adicCompletion E) y ↔ ‖x‖ ≤ ‖y‖ := by
  have h1 : (1 : NNReal) < (Ideal.absNorm w.asIdeal : NNReal) := by
    rw [← normV_eq_absNorm]; exact_mod_cast one_lt_normV w
  rw [isEquiv_valued w x y, FinitePlace.norm_def, FinitePlace.norm_def, NNReal.coe_le_coe]
  exact (WithZeroMulInt.toNNReal_strictMono h1).le_iff_le.symm

theorem range_map_eq_KO (m : ℕ) :
    (GeneralLinearGroup.map (w.adicCompletionIntegers E).subtype).range = KO (w.adicCompletion E) (Fin m) := by
  have he := isEquiv_valued w
  have hO : 𝒪[w.adicCompletion E] = (w.adicCompletionIntegers E).toSubring := by
    ext y
    rw [Valuation.mem_integer_iff, he.le_one_iff_le_one]
    exact Iff.rfl
  let e := RingEquiv.subringCongr hO
  ext g
  constructor
  · rintro ⟨h, rfl⟩
    refine ⟨GeneralLinearGroup.map e.symm.toRingHom h, ?_⟩
    ext i j; rfl
  · rintro ⟨h, rfl⟩
    refine ⟨GeneralLinearGroup.map e.toRingHom h, ?_⟩
    ext i j; rfl

end GlobalTheory.CompletionNorm


open GlobalTheory.CompletionNorm in
theorem GlobalTheory.CompletionNorm.norm_nabs_valuation : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)), (∀ x : (w.adicCompletion E)ˣ, ‖(x : w.adicCompletion E)‖ = nabs (w.adicCompletion E) x ∧ ‖(x : w.adicCompletion E)‖ = ((normV w : ℕ) : ℝ) ^ (-ord (w.adicCompletion E) x) ∧ Valued.v (x : w.adicCompletion E) = WithZero.exp (-ord (w.adicCompletion E) x)) ∧ (∀ x y : w.adicCompletion E, valuation (w.adicCompletion E) x ≤ valuation (w.adicCompletion E) y ↔ ‖x‖ ≤ ‖y‖) ∧ ∀ m : ℕ, (GeneralLinearGroup.map (w.adicCompletionIntegers E).subtype).range = KO (w.adicCompletion E) (Fin m) := by
  intro E _ _ w
  refine ⟨fun x => ⟨?_, norm_eq_zpow w x, valued_eq_exp w x⟩, valuation_le_iff_norm_le w, range_map_eq_KO w⟩
  let k := w.adicCompletion E
  have ord_pow (z : kˣ) (n : ℕ) : SmGL.ord k (z ^ n) = n * SmGL.ord k z := by
    induction n with
    | zero =>
      simp only [pow_zero, Nat.cast_zero, zero_mul]
      exact SmGL.ord_eq_zero (by simp)
    | succ n ih =>
      rw [pow_succ, SmGL.ord_mul, ih]
      push_cast
      ring
  have hexists : ∃ ϖ : kˣ, SmGL.ord k ϖ = 1 ∧ nabs k ϖ = (resCard k : ℝ)⁻¹ := by
    obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible (valuation k).integer
    have hp0 : (p : k) ≠ 0 := by
      intro h
      exact hp.ne_zero (Subtype.ext h)
    obtain ⟨y, hy⟩ : ∃ y : k, valuation k y = uniformizer k := valuation_surjective _
    have hy0 : y ≠ 0 := by
      intro h
      rw [h, map_zero] at hy
      exact (uniformizer_pos (R := k)).ne hy
    have hyint : y ∈ (valuation k).integer := by
      rw [Valuation.mem_integer_iff, hy]
      exact uniformizer_lt_one.le
    obtain ⟨m, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (x := (⟨y, hyint⟩ : (valuation k).integer)) (fun h => hy0 (congrArg Subtype.val h)) hp
    have hu0 : ((u : (valuation k).integer) : k) ≠ 0 := by
      intro h
      exact u.ne_zero (Subtype.ext h)
    refine ⟨Units.mk0 (p : k) hp0, ?_, _root_.GlobalTheory.SplitWeil.nabs_uniformiser hp rfl⟩
    have hyo : _root_.GlobalTheory.SmGL.ord k (Units.mk0 y hy0) = 1 :=
      _root_.GlobalTheory.SmGL.ord_eq_one hy
    have huo : _root_.GlobalTheory.SmGL.ord k (Units.mk0 _ hu0) = 0 := by
      apply _root_.GlobalTheory.SmGL.ord_eq_zero
      exact (Valuation.integer.integers (valuation k)).one_of_isUnit u.isUnit
    have hsplit : Units.mk0 y hy0 = Units.mk0 _ hu0 * Units.mk0 (p : k) hp0 ^ m := by
      apply Units.ext
      have := congrArg Subtype.val hu
      simpa using this
    rw [hsplit, _root_.GlobalTheory.SmGL.ord_mul, huo, ord_pow,
      zero_add] at hyo
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' hyo with ⟨_, h2⟩ | ⟨h1, _⟩
    · exact h2
    · omega
  have hnabs (x : kˣ) : nabs k x = (resCard k : ℝ) ^ (-SmGL.ord k x) := by
    obtain ⟨ϖ, hord, habs⟩ := hexists
    have hq : (_root_.GlobalTheory.SplitWeil.resCard k : ℝ) ≠ 0 := by
      have := _root_.GlobalTheory.SplitWeil.one_lt_resCard k
      positivity
    have hinv : _root_.GlobalTheory.SplitWeil.nabs k ϖ⁻¹ = _root_.GlobalTheory.SplitWeil.resCard k := by
      have h := _root_.GlobalTheory.SplitWeil.nabs_mul k ϖ ϖ⁻¹
      rw [mul_inv_cancel, _root_.GlobalTheory.SplitWeil.nabs_one, habs] at h
      exact ((inv_mul_eq_one₀ hq).mp h.symm).symm
    have oinv : _root_.GlobalTheory.SmGL.ord k ϖ⁻¹ = -1 := by
      have h := _root_.GlobalTheory.SmGL.ord_mul k ϖ ϖ⁻¹
      rw [mul_inv_cancel, hord,
        _root_.GlobalTheory.SmGL.ord_eq_zero (x := (1 : kˣ)) (by simp only [Units.val_one, map_one])] at h
      omega
    have key : ∀ m : ℤ, _root_.GlobalTheory.SplitWeil.nabs k (ϖ ^ m) =
        (_root_.GlobalTheory.SplitWeil.resCard k : ℝ) ^ (-m) ∧ _root_.GlobalTheory.SmGL.ord k (ϖ ^ m) = m := by
      intro m
      refine Int.induction_on m ?_ ?_ ?_
      · refine ⟨by simp [_root_.GlobalTheory.SplitWeil.nabs_one], ?_⟩
        rw [zpow_zero]
        exact _root_.GlobalTheory.SmGL.ord_eq_zero (by simp only [Units.val_one, map_one])
      · intro i ih
        rw [_root_.zpow_add_one, _root_.GlobalTheory.SplitWeil.nabs_mul, _root_.GlobalTheory.SmGL.ord_mul,
          ih.1, ih.2, habs, hord]
        refine ⟨?_, rfl⟩
        rw [neg_add, zpow_add₀ hq, _root_.zpow_neg_one]
      · intro i ih
        rw [_root_.zpow_sub_one, _root_.GlobalTheory.SplitWeil.nabs_mul, _root_.GlobalTheory.SmGL.ord_mul,
          ih.1, ih.2, hinv, oinv]
        refine ⟨?_, by ring⟩
        rw [show -(-(i : ℤ) - 1) = -(-(i : ℤ)) + 1 by ring, zpow_add₀ hq, _root_.zpow_one]
    set o := _root_.GlobalTheory.SmGL.ord k x
    have hy : _root_.GlobalTheory.SmGL.ord k (x * ϖ ^ (-o)) = 0 := by
      rw [_root_.GlobalTheory.SmGL.ord_mul, (key _).2]
      ring
    have hy1 : _root_.GlobalTheory.SplitWeil.nabs k (x * ϖ ^ (-o)) = 1 :=
      _root_.GlobalTheory.SmGL.nabs_eq_one k
        (_root_.GlobalTheory.SmGL.ord_eq_zero_iff.mp hy)
    have hx : x * ϖ ^ (-o) * ϖ ^ o = x := by
      rw [mul_assoc, ← _root_.zpow_add, neg_add_cancel, zpow_zero, mul_one]
    calc _root_.GlobalTheory.SplitWeil.nabs k x
        = _root_.GlobalTheory.SplitWeil.nabs k (x * ϖ ^ (-o) * ϖ ^ o) := by rw [hx]
      _ = (_root_.GlobalTheory.SplitWeil.resCard k : ℝ) ^ (-o) := by
        rw [_root_.GlobalTheory.SplitWeil.nabs_mul, hy1, (key o).1, one_mul]
  rw [norm_eq_zpow, hnabs, GlobalTheory.LocLanglands.resCard_eq_normV]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopMultAndExtVInjective
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DefiniteMult

theorem topMult_and_extV_injective : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.BaseW F → Formalism.IndefR.RecTie.TopMultH R ∧ ∀ i t, Function.Injective (R.extV i t) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F h
  refine ⟨?_, fun i t => extV_injective R h.models.HV i t⟩
  intro t
  exact range_top R h.models.inf h.models.cX h.models.prX h.models.HX t

end GlobalTheory.DefiniteMult
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNegSqZero
set_option autoImplicit false

noncomputable section

open Matrix MvPolynomial GlobalTheory.GoodMetric GlobalTheory.HermFrame
open ReciprocityTheory.L2DbarEstimates (V)

namespace GlobalTheory.PointFormSign

def domGram (m r : ℕ) (x : Fin m → Fin r → ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  ((1 - Matrix.of x * (Matrix.of x)ᴴ)⁻¹)ᵀ

def IsNegSq {E : Type*} [AddCommGroup E] [Module ℂ E] {m : ℕ} (F : E → E → Matrix (Fin m) (Fin m) ℂ) (r : ℕ) : Prop :=
  ∃ (S : Matrix (Fin m) (Fin m) ℂ) (T : E →ₗ[ℂ] Matrix (Fin m) (Fin r) ℂ), IsUnit S.det ∧
    ∀ ξ η, F ξ η = S⁻¹ * (-(T ξ * (T η)ᴴ)) * S

def sqPoly {n m r : ℕ} (T : V n →ₗ[ℂ] Matrix (Fin m) (Fin r) ℂ) :
    Matrix (Fin m) (Fin m) (MvPolynomial (Fin n × Fin n) ℂ) :=
  Matrix.of fun i j => ∑ a, ∑ b, C ((T (coordVec a) * (T (coordVec b))ᴴ) i j) * X (a, b)

end GlobalTheory.PointFormSign
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCmConjugationOmega
open Formalism.BasicNotions GlobalTheory.Mem GlobalTheory.MemN NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial

namespace GlobalTheory.MemN

theorem exists_isCMConjOm_nData : ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (nd : NData R H what₂), ∃ c : nd.Om ≃+* nd.Om, IsCMConjOm H.E nd.Om c :=
  fun _ H _ nd => GlobalTheory.Mem.GaloisStage.exists_isCMConjOm H nd.Om

end GlobalTheory.MemN
end
