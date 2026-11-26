module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledVacuumStabilizerGaussDecompositionBigCell
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInversePreservingAdelicLatticeAtPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictedSectionChartCoords
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitEqNormCompletionTensorOfIsInertAt

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTraceZeroAdeleUnitLatticeAtInertPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTraceZeroAdeleUnitLatticeAtInertPlace
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.InertSph.Scal

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem disc_sub_sq_notMem (v : Pl (F := F)) (b c t : 𝓞 F) (h2 : (2 : 𝓞 F) ∉ v.asIdeal)
    (hroot : ∀ r : 𝓞 F, r ^ 2 + b * r + c ∉ v.asIdeal) : t ^ 2 - (b ^ 2 - 4 * c) ∉ v.asIdeal := by
  intro h
  obtain ⟨s, a, ha, hs⟩ := v.isMaximal.exists_inv h2
  apply hroot (s * (t - b))
  have h4 : (2 : 𝓞 F) * (2 * ((s * (t - b)) ^ 2 + b * (s * (t - b)) + c)) ∈ v.asIdeal := by
    have e : (2 : 𝓞 F) * (2 * ((s * (t - b)) ^ 2 + b * (s * (t - b)) + c)) =
        (t ^ 2 - (b ^ 2 - 4 * c)) + a * ((t - b) * (a * (t - b) - 2 * t)) := by
      have : a = 1 - s * 2 := by linear_combination hs
      subst this
      ring
    rw [e]
    exact add_mem h (Ideal.mul_mem_right _ _ ha)
  exact ((v.isPrime.mem_or_mem ((v.isPrime.mem_or_mem h4).resolve_left h2)).resolve_left h2)

theorem exists_delta (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E))
    (hin : Formalism.UG.IsInertAt F E v w) (h2 : (2 : 𝓞 F) ∉ v.asIdeal) :
    ∃ (δ : 𝓞 E) (D : 𝓞 F), σ (δ : E) = -(δ : E) ∧ (δ : E) * δ = algebraMap F E (D : F) ∧ D ∉ v.asIdeal ∧
      1 - D ∉ v.asIdeal := by
  have hp : (v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E))).IsPrime := by
    rw [show v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E)) = w.asIdeal from hin]
    exact w.isPrime
  obtain ⟨a, b, c, hq, hc, hroot⟩ := GlobalTheory.InertUnitNorm.exists_integral_gen σ hσ v hp
  have hδ : ((2 * a + algebraMap (𝓞 F) (𝓞 E) b : 𝓞 E) : E) = 2 * (a : E) + algebraMap F E (b : F) := rfl
  have hD : ((b ^ 2 - 4 * c : 𝓞 F) : F) = (b : F) ^ 2 - 4 * (c : F) := rfl
  refine ⟨2 * a + algebraMap (𝓞 F) (𝓞 E) b, b ^ 2 - 4 * c, ?_, ?_, ?_, ?_⟩
  · rw [hδ, map_add (f := _), map_mul, map_ofNat, AlgHom.commutes, hc]
    ring
  · rw [hδ, hD, map_sub, map_mul, map_pow, map_ofNat]
    linear_combination 4 * hq
  · intro h
    apply disc_sub_sq_notMem v b c 0 h2 hroot
    simpa using neg_mem h
  · simpa using disc_sub_sq_notMem v b c 1 h2 hroot

theorem exists_inv (v : Pl (F := F)) (D : 𝓞 F) (hD : D ∉ v.asIdeal) :
    ∃ c : Fv F v, c ∈ v.adicCompletionIntegers F ∧ c * algebraMap F (Fv F v) (D : F) = 1 := by
  have h1 : Valued.v (algebraMap F (Fv F v) (D : F)) = 1 := by
    have h := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (D : F)
    have h' : v.valuation F (D : F) = 1 := (HeightOneSpectrum.valuation_eq_one_iff_notMem v).2 hD
    rw [← h', ← h]
    rfl
  have h0 : algebraMap F (Fv F v) (D : F) ≠ 0 := by
    intro h
    rw [h, map_zero] at h1
    exact zero_ne_one h1
  refine ⟨(algebraMap F (Fv F v) (D : F))⁻¹, ?_, inv_mul_cancel₀ h0⟩
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, h1, inv_one]

theorem smul_eq_of_at {M : Type} [AddCommGroup M] [Module (AF F) M] {v : Pl (F := F)} {z : M} (hz : At (evFin F v) z)
    {a : AF F} (ha : evFin F v a = 1) : a • z = z := by
  have h := hz (a - 1) (by rw [map_sub, map_one, ha, sub_self])
  rwa [sub_smul, one_smul, sub_eq_zero] at h

theorem at_of_mem_latAt {d : ℕ} (W : Spc F E d) (v : Pl (F := F)) {z : Fin d → AE F E} (hz : z ∈ latAt W v) :
    At (evFin F v) z := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, -, y, -, rfl⟩ := hz
    intro u hu
    rw [smul_smul, ← smul_eq_mul u a, ha u hu, zero_smul]
  | zero => intro u _; exact smul_zero u
  | add x y _ _ hx hy => intro u hu; rw [smul_add, hx u hu, hy u hu, add_zero]
  | neg x _ hx => intro u hu; rw [smul_neg, hx u hu, neg_zero]

theorem lift_smul_mem {d : ℕ} (W : Spc F E d) (v : Pl (F := F)) {c : Fv F v} (hc : c ∈ v.adicCompletionIntegers F)
    (o : 𝓞 E) {z : Fin d → AE F E} (hz : z ∈ latAt W v) :
    (GlobalTheory.LatVac.liftV v c • inclR (F := F) (AF F) (o : E)) • z ∈ latAt W v :=
  GlobalTheory.InertLocFrame.Lat.smul_mem_latAt W (AddSubgroup.subset_closure
    ⟨_, GlobalTheory.LatVac.at_liftV v c, by rwa [GlobalTheory.LatVac.evFin_liftV], o, rfl⟩) hz

end GlobalTheory.InertSph.Scal

namespace GlobalTheory.InertSph


open GlobalTheory.InertSph.Scal GlobalTheory.LatVac in
theorem exists_traceZero_unit : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (d : ℕ) (W : Spc F E d) (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w →
    ∃ β b up um : AE F E, At (evFin F v) β ∧ cA σ β = -β ∧ ∀ z ∈ GlobalTheory.InertSph.latAt W v,
      β • z ∈ GlobalTheory.InertSph.latAt W v ∧ b • z ∈ GlobalTheory.InertSph.latAt W v ∧ up • z ∈ GlobalTheory.InertSph.latAt W v ∧
      um • z ∈ GlobalTheory.InertSph.latAt W v ∧ (β * b) • z = z ∧ ((1 + β) * up) • z = z ∧ ((1 - β) * um) • z = z := by
  intro F E _ _ _ _ _ σ B hB d W v w hin
  obtain ⟨δ, D, hσ, hsq, hD, hD1⟩ := exists_delta σ hB.cm v w hin (hB.inert v w hin).1
  obtain ⟨c, hc, hcD⟩ := exists_inv v D hD
  obtain ⟨c', hc', hcD'⟩ := exists_inv v (1 - D) hD1
  have hcD'' : c' * (1 - algebraMap F (Fv F v) (D : F)) = 1 := by
    rwa [show ((1 - D : 𝓞 F) : F) = 1 - (D : F) from rfl, map_sub, map_one] at hcD'
  set x : AE F E := inclR (F := F) (AF F) (δ : E) with hx
  have hxx : x * x = algebraMap (AF F) (AE F E) (algebraMap F (AF F) (D : F)) := by
    rw [hx, ← map_mul, hsq, ← IsScalarTower.algebraMap_apply]
    exact (Algebra.TensorProduct.includeRight : E →ₐ[F] AE F E).commutes _
  have hp : inclR (F := F) (AF F) ((1 + δ : 𝓞 E) : E) = 1 + x := by
    rw [show ((1 + δ : 𝓞 E) : E) = 1 + (δ : E) from rfl, map_add (f := _), map_one]
  have hm : inclR (F := F) (AF F) ((1 - δ : 𝓞 E) : E) = 1 - x := by
    rw [show ((1 - δ : 𝓞 E) : E) = 1 - (δ : E) from rfl, map_sub, map_one]
  have he : liftV v (1 : Fv F v) * liftV v c' = liftV v c' :=
    smul_eq_of_at (at_liftV v c') (evFin_liftV v 1)
  have he' : algebraMap (AF F) (AE F E) (liftV v (1 : Fv F v)) * algebraMap (AF F) (AE F E) (liftV v c') =
      algebraMap (AF F) (AE F E) (liftV v c') := by rw [← map_mul, he]
  have key : ∀ z ∈ latAt W v, ∀ a : AF F, evFin F v a = 1 → algebraMap (AF F) (AE F E) a • z = z := by
    intro z hz a ha
    rw [algebraMap_smul]
    exact smul_eq_of_at (at_of_mem_latAt W v hz) ha
  have hu : evFin F v (liftV v c' * (1 - algebraMap F (AF F) (D : F))) = 1 := by
    rw [map_mul, map_sub, map_one, evFin_liftV, AlgHom.commutes, hcD'']
  refine ⟨liftV v 1 • x, liftV v c • x, liftV v c' • (1 - x), liftV v c' • (1 + x), ?_, ?_, fun z hz =>
    ⟨lift_smul_mem W v (one_mem _) δ hz, lift_smul_mem W v hc δ hz, hm ▸ lift_smul_mem W v hc' (1 - δ) hz,
      hp ▸ lift_smul_mem W v hc' (1 + δ) hz, ?_, ?_, ?_⟩⟩
  · intro u hu
    rw [smul_smul, ← smul_eq_mul, at_liftV v 1 u hu, zero_smul]
  · have h : cA σ x = -x := by
      have h1 : cA σ x = inclR (F := F) (AF F) (σ (δ : E)) := by
        simp [hx, cA, inclR]
      rw [h1, hσ, map_neg]
    rw [map_smul, h, smul_neg]
  · have h := key z hz (liftV v 1 * liftV v c * algebraMap F (AF F) (D : F)) (by
      rw [map_mul, map_mul, evFin_liftV, evFin_liftV, AlgHom.commutes, one_mul, hcD])
    convert h using 2
    simp only [Algebra.smul_def, map_mul, ← hxx]
    ring
  · convert key z hz _ hu using 2
    simp only [Algebra.smul_def, map_mul, map_sub, map_one, ← hxx]
    linear_combination (x * (1 - x)) * he'
  · convert key z hz _ hu using 2
    simp only [Algebra.smul_def, map_mul, map_sub, map_one, ← hxx]
    linear_combination (-x * (1 + x)) * he'

end GlobalTheory.InertSph

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTraceZeroAdeleUnitLatticeAtInertPlaceStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_traceZero_adele_unit_lattice_at_inert_place : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (d : ℕ) (W : Spc F E d) (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w →
    ∃ β b up um : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), At (evFin F v) β ∧ cA σ β = -β ∧ ∀ z ∈ GlobalTheory.InertSph.latAt W v,
      β • z ∈ GlobalTheory.InertSph.latAt W v ∧ b • z ∈ GlobalTheory.InertSph.latAt W v ∧ up • z ∈ GlobalTheory.InertSph.latAt W v ∧
      um • z ∈ GlobalTheory.InertSph.latAt W v ∧ (β * b) • z = z ∧ ((1 + β) * up) • z = z ∧ ((1 - β) * um) • z = z := by
  first | exact @GlobalTheory.InertSph.exists_traceZero_unit | exact GlobalTheory.InertSph.exists_traceZero_unit | (intros; apply GlobalTheory.InertSph.exists_traceZero_unit <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowIdempotentAdelicLatticeModPrime
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowIdempotentAdelicLatticeModPrime
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.LatIdem

theorem exists_iterate_idem {X : Type*} [Finite X] (u : X → X) : ∃ N : ℕ, 0 < N ∧ u^[2 * N] = u^[N] := by
  obtain ⟨i, j, hij, h⟩ : ∃ i j : ℕ, i < j ∧ u^[i] = u^[j] := by
    obtain ⟨i, j, hne, h⟩ := Finite.exists_ne_map_eq_of_infinite (fun n : ℕ => u^[n])
    rcases lt_or_gt_of_ne hne with h1 | h1
    · exact ⟨i, j, h1, h⟩
    · exact ⟨j, i, h1, h.symm⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hij
  have key : ∀ m : ℕ, u^[i + m * (k + 1)] = u^[i] := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have : i + (m + 1) * (k + 1) = (i + m * (k + 1)) + (k + 1) := by ring
      rw [this, Function.iterate_add, ih, ← Function.iterate_add, ← add_assoc, ← h]
  refine ⟨(i + 1) * (k + 1), by positivity, ?_⟩
  have e1 : 2 * ((i + 1) * (k + 1)) = (i + (i + 1) * (k + 1)) + (i * k + k + 1) := by ring
  have e2 : (i + 1) * (k + 1) = i + (i * k + k + 1) := by ring
  rw [e1, Function.iterate_add, key, ← Function.iterate_add, ← e2]

theorem exists_idem_mod {M : Type*} [AddCommGroup M] (Λ P : AddSubgroup M) (g : M →+ M)
    (hΛ : ∀ z ∈ Λ, g z ∈ Λ) (hP : ∀ z ∈ P, g z ∈ P) [Finite (Λ.map (QuotientAddGroup.mk' P))] :
    ∃ N : ℕ, 0 < N ∧ ∀ z ∈ Λ, g^[2 * N] z - g^[N] z ∈ P := by
  let gb : M ⧸ P →+ M ⧸ P := QuotientAddGroup.map P P g hP
  let u : Λ.map (QuotientAddGroup.mk' P) → Λ.map (QuotientAddGroup.mk' P) := fun x => ⟨gb x, by
    obtain ⟨_, z, hz, rfl⟩ := x
    exact ⟨g z, hΛ z hz, rfl⟩⟩
  have hu : ∀ (n : ℕ) (z : M) (hz : z ∈ Λ), (u^[n] ⟨QuotientAddGroup.mk' P z, z, hz, rfl⟩ : M ⧸ P) =
      QuotientAddGroup.mk' P (g^[n] z) := by
    intro n
    induction n with
    | zero => intro z hz; rfl
    | succ n ih =>
      intro z hz
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      show gb _ = _
      rw [ih z hz]; rfl
  obtain ⟨N, hN, h⟩ := exists_iterate_idem u
  refine ⟨N, hN, fun z hz => ?_⟩
  have := hu (2 * N) z hz
  rw [h, hu N z hz] at this
  exact QuotientAddGroup.eq_iff_sub_mem.1 this.symm

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

open GlobalTheory.EmbChart GlobalTheory.InertSph

theorem at_atPlace (v : Pl (F := F)) (a : Fv F v) : At (evFin F v) (atPlace v a) := by
  intro u hu
  rw [smul_eq_mul, mul_comm, atPlace_mul_right, hu, mul_zero, map_zero]

theorem eq_atPlace (v : Pl (F := F)) (a : AF F) (ha : At (evFin F v) a) : a = atPlace v (evFin F v a) := by
  have h := ha (1 - atPlace v 1) (by rw [map_sub, map_one, evFin_atPlace, sub_self])
  rw [smul_eq_mul, sub_mul, one_mul, atPlace_mul_right, one_mul, sub_eq_zero] at h
  exact h

omit [NumberField E] in
theorem gen_mem {d : ℕ} (W : Spc F E d) (v : Pl (F := F)) (c : v.adicCompletionIntegers F) (y : Fin d → E) (hy : y ∈ W.L) :
    (atPlace v (c : Fv F v) • fun i => inclR (F := F) (AF F) (y i)) ∈ latAt W v :=
  AddSubgroup.subset_closure ⟨_, at_atPlace v _, by rw [evFin_atPlace]; exact c.2, y, hy, rfl⟩

theorem finite_mod {d : ℕ} (W : Spc F E d) (hW : W.L.FG) (v : Pl (F := F)) (p : ℕ) (hp : 0 < p) :
    Finite ((latAt W v).map (QuotientAddGroup.mk' ((latAt W v).map (nsmulAddMonoidHom p)))) := by
  set P := (latAt W v).map (nsmulAddMonoidHom p) with hPdef
  have hp0 : (p : v.adicCompletionIntegers F) ≠ 0 := by
    intro h
    have h1 : ((p : v.adicCompletionIntegers F) : Fv F v) = 0 := congrArg Subtype.val h
    have h2 : (p : Fv F v) = 0 := by simpa using h1
    rw [← map_natCast (algebraMap F (Fv F v)), map_eq_zero] at h2
    exact (Nat.cast_ne_zero.2 hp.ne') h2
  have hfin : Finite (v.adicCompletionIntegers F ⧸ Ideal.span {(p : v.adicCompletionIntegers F)}) :=
    Formalism.UG.P.glint_finite_quotient_of_dvr (Formalism.UG.P.glint_finite_residueField v) _
      (by rwa [Ne, Ideal.span_singleton_eq_bot])
  obtain ⟨T, hT⟩ : (W.L.restrictScalars ℤ).FG := by
    have : Module.Finite (𝓞 E) W.L := Module.Finite.iff_fg.2 hW
    have : Module.Finite ℤ W.L := Module.Finite.trans (𝓞 E) W.L
    exact Module.Finite.iff_fg.1 this
  have hTL : ∀ t ∈ T, t ∈ W.L := fun t ht => by
    have : t ∈ W.L.restrictScalars ℤ := hT ▸ Submodule.subset_span ht
    exact this
  let s : (v.adicCompletionIntegers F ⧸ Ideal.span {(p : v.adicCompletionIntegers F)}) × T → (Fin d → AE F E) ⧸ P :=
    fun x => QuotientAddGroup.mk' P
      (atPlace v ((x.1.out : v.adicCompletionIntegers F) : Fv F v) • fun i => inclR (F := F) (AF F) (x.2.1 i))
  have heq : (latAt W v).map (QuotientAddGroup.mk' P) = AddSubgroup.closure (Set.range s) := by
    apply le_antisymm
    · rw [AddSubgroup.map_le_iff_le_comap, InertSph.latAt, AddSubgroup.closure_le]
      rintro _ ⟨a, ha, hav, y, hy, rfl⟩
      have hy' : y ∈ Submodule.span ℤ (T : Set (Fin d → E)) := hT ▸ hy
      clear hy
      rw [SetLike.mem_coe]
      induction hy' using Submodule.span_induction with
      | mem t ht =>
        let x : v.adicCompletionIntegers F := ⟨_, hav⟩
        let q := Ideal.Quotient.mk (Ideal.span {(p : v.adicCompletionIntegers F)}) x
        obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq.1 (Ideal.Quotient.mk_out q).symm)
        have hc' : evFin F v a - ((q.out : v.adicCompletionIntegers F) : Fv F v) = p • (c : Fv F v) := by
          have := congrArg Subtype.val hc
          simp only [MulMemClass.coe_mul, SubringClass.coe_natCast, AddSubgroupClass.coe_sub] at this
          rw [nsmul_eq_mul, mul_comm]; exact this.symm
        rw [AddSubgroup.mem_comap]
        refine AddSubgroup.subset_closure ⟨(q, ⟨t, ht⟩), ?_⟩
        refine (QuotientAddGroup.eq_iff_sub_mem.2 ?_).symm
        refine ⟨_, gen_mem W v c t (hTL t ht), ?_⟩
        rw [← sub_smul, eq_atPlace v a ha, ← map_sub, hc', map_nsmul, smul_assoc]
        rfl
      | zero =>
        have : (a • fun i => inclR (F := F) (AF F) ((0 : Fin d → E) i)) = 0 := by
          funext i; simp
        rw [this]; exact zero_mem _
      | add x y _ _ hx hy =>
        have : (a • fun i => inclR (F := F) (AF F) ((x + y) i)) =
            (a • fun i => inclR (F := F) (AF F) (x i)) + (a • fun i => inclR (F := F) (AF F) (y i)) := by
          funext i; simp
        rw [this]; exact add_mem hx hy
      | smul n x _ hx =>
        have : (a • fun i => inclR (F := F) (AF F) ((n • x) i)) =
            n • (a • fun i => inclR (F := F) (AF F) (x i)) := by
          funext i
          simp only [Pi.smul_apply, map_zsmul]
          rw [smul_comm]
        rw [this]; exact zsmul_mem hx n
    · rw [AddSubgroup.closure_le]
      rintro _ ⟨x, rfl⟩
      exact ⟨_, gen_mem W v _ _ (hTL _ x.2.2), rfl⟩
  have hfg : ((latAt W v).map (QuotientAddGroup.mk' P)).FG :=
    (AddSubgroup.fg_iff _).2 ⟨_, heq.symm, Set.finite_range s⟩
  have : AddGroup.FG ((latAt W v).map (QuotientAddGroup.mk' P)) := (AddGroup.fg_iff_addSubgroup_fg _).2 hfg
  refine AddCommGroup.finite_of_fg_isAddTorsion _ ?_
  rintro ⟨_, z, hz, rfl⟩
  refine isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨p, hp, Subtype.ext ?_⟩
  show p • QuotientAddGroup.mk' P z = 0
  rw [← map_nsmul]
  exact (QuotientAddGroup.eq_zero_iff _).2 ⟨z, hz, rfl⟩

theorem exists_pow_idem : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (d : ℕ) (W : Spc F E d),
    W.L.IsLattice E → ∀ (v : Pl (F := F)) (p : ℕ), 0 < p → (p : 𝓞 F) ∈ v.asIdeal →
    ∀ f : Matrix (Fin d) (Fin d) (AE F E), (∀ z ∈ GlobalTheory.InertSph.latAt W v, f *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) →
    ∃ N : ℕ, 0 < N ∧ ∀ z ∈ GlobalTheory.InertSph.latAt W v, ∃ y ∈ GlobalTheory.InertSph.latAt W v, (f ^ (2 * N)) *ᵥ z - (f ^ N) *ᵥ z = p • y := by
  intro F E _ _ _ _ _ d W hW v p hp _ f hf
  have := finite_mod W hW.fg v p hp
  let g : (Fin d → AE F E) →+ (Fin d → AE F E) := (Matrix.mulVecLin f).toAddMonoidHom
  have hg : ∀ (n : ℕ) (z : Fin d → AE F E), g^[n] z = (f ^ n) *ᵥ z := by
    intro n
    induction n with
    | zero => intro z; simp
    | succ n ih =>
      intro z
      rw [Function.iterate_succ_apply', ih, pow_succ', ← Matrix.mulVec_mulVec]; rfl
  obtain ⟨N, hN, h⟩ := exists_idem_mod (latAt W v) ((latAt W v).map (nsmulAddMonoidHom p)) g hf (by
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨g z, hf z hz, (map_nsmul g p z).symm⟩)
  refine ⟨N, hN, fun z hz => ?_⟩
  obtain ⟨y, hy, e⟩ := h z hz
  rw [hg, hg] at e
  exact ⟨y, hy, e.symm⟩

end GlobalTheory.LatIdem
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowIdempotentAdelicLatticeModPrimeStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pow_idempotent_adelicLattice_mod_prime : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (d : ℕ) (W : Spc F E d),
    W.L.IsLattice E → ∀ (v : Pl (F := F)) (p : ℕ), 0 < p → (p : 𝓞 F) ∈ v.asIdeal →
    ∀ f : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), (∀ z ∈ GlobalTheory.InertSph.latAt W v, f *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) →
    ∃ N : ℕ, 0 < N ∧ ∀ z ∈ GlobalTheory.InertSph.latAt W v, ∃ y ∈ GlobalTheory.InertSph.latAt W v, (f ^ (2 * N)) *ᵥ z - (f ^ N) *ᵥ z = p • y := by
  first | exact @GlobalTheory.LatIdem.exists_pow_idem | exact GlobalTheory.LatIdem.exists_pow_idem | (intros; apply GlobalTheory.LatIdem.exists_pow_idem <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSkewCayleyInertPlaceStabilizer
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.TwoFacCore

theorem alg {Q : Type*} [CommRing Q] (k ki β b up um h : Q) (N₀ : ℕ) (hK : k * ki = 1) (hb : β * b = 1)
    (h2 : h + h = 1) (hp : (1 + β) * up = 1) (hm : (1 - β) * um = 1)
    (hD : (k + ki + 1 + 1) ^ (2 * (N₀ + 1)) = (k + ki + 1 + 1) ^ (N₀ + 1)) :
    IsUnit (1 + β * (1 - (k + ki + 1 + 1) ^ (N₀ + 1))) ∧ IsUnit (1 - β * (1 - (k + ki + 1 + 1) ^ (N₀ + 1))) ∧
    IsUnit (1 + β * (1 - (k + ki + 1 + 1) ^ (N₀ + 1)) + k * (1 - β * (1 - (k + ki + 1 + 1) ^ (N₀ + 1)))) := by
  set f := k + ki + 1 + 1 with hf
  set F := f ^ (N₀ + 1) with hFdef
  set G := f ^ N₀ with hG
  have hF : f * G = F := by rw [hFdef, hG, pow_succ']
  have hF2 : F ^ 2 = F := by rw [hFdef, ← pow_mul, mul_comm]; exact hD
  have he : (1 - F) ^ 2 = 1 - F := by linear_combination hF2
  refine ⟨isUnit_iff_exists_inv.mpr ⟨1 - up * β * (1 - F), ?_⟩, isUnit_iff_exists_inv.mpr ⟨1 + um * β * (1 - F), ?_⟩, ?_⟩
  · linear_combination (-up * β ^ 2) * he - β * (1 - F) * hp
  · linear_combination (-um * β ^ 2) * he + β * (1 - F) * hm
  set x := -((1 - β) * h * b) * (1 + k) with hx
  set s := ∑ i ∈ Finset.range (2 * (N₀ + 1)), x ^ i with hsdef
  have hs : s * (x - 1) = x ^ (2 * (N₀ + 1)) - 1 := geom_sum_mul x _
  have hn : (1 + k) ^ 2 = k * f := by rw [hf]; linear_combination (-1 : Q) * hK
  have hxp : x ^ (2 * (N₀ + 1)) = ((1 - β) * h * b) ^ (2 * (N₀ + 1)) * (k ^ (N₀ + 1) * F) := by
    rw [hx, neg_mul, Even.neg_pow ⟨N₀ + 1, by ring⟩, mul_pow ((1 - β) * h * b) (1 + k), pow_mul (1 + k), hn, mul_pow k f]
  have hx0 : x ^ (2 * (N₀ + 1)) * (1 - F) = 0 := by
    rw [hxp]; linear_combination (-((1 - β) * h * b) ^ (2 * (N₀ + 1)) * k ^ (N₀ + 1)) * hF2
  have hAA : ((1 + β) + (1 - β) * k) * (h * b * s) = 1 - x ^ (2 * (N₀ + 1)) := by
    rw [hx] at hs ⊢; linear_combination (s * β * b) * h2 + s * hb - hs
  have e1 : (1 + k) * ((1 + k) * ki * G) = F := by
    rw [← hF, hf]; linear_combination (2 + k) * G * hK
  refine isUnit_iff_exists_inv.mpr ⟨(1 + k) * ki * G * F + h * b * s * (1 - F), ?_⟩
  linear_combination F ^ 2 * e1 + (F + 2 - ((1 + k) * (h * b * s) + ((1 + β) + (1 - β) * k) * ((1 + k) * ki * G)) -
    x ^ (2 * (N₀ + 1))) * hF2 + (1 - F) ^ 2 * hAA - hx0

end GlobalTheory.TwoFacCore

noncomputable section
namespace GlobalTheory.TwoFacCore

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

section Ring

variable {d : ℕ} {S : Type*} [CommRing S] (φ : S →+* Matrix (Fin d) (Fin d) (AE F E))
  (Λ : AddSubgroup (Fin d → AE F E)) (p : ℕ)

def keepT : Subring S where
  carrier := {x | ∀ z ∈ Λ, φ x *ᵥ z ∈ Λ}
  mul_mem' {x y} hx hy z hz := by
    simp only [Set.mem_setOf_eq, map_mul, ← Matrix.mulVec_mulVec] at *
    exact hx _ (hy z hz)
  one_mem' z hz := by simpa using hz
  add_mem' {x y} hx hy z hz := by
    simp only [Set.mem_setOf_eq, map_add (f := _), Matrix.add_mulVec] at *
    exact add_mem (hx z hz) (hy z hz)
  zero_mem' z hz := by simp
  neg_mem' {x} hx z hz := by
    simp only [Set.mem_setOf_eq, map_neg, Matrix.neg_mulVec] at *
    exact neg_mem (hx z hz)

def congI : Ideal (keepT φ Λ) where
  carrier := {x | ∀ z ∈ Λ, ∃ y ∈ Λ, φ (x : S) *ᵥ z = p • y}
  add_mem' {x y} hx hy z hz := by
    obtain ⟨a, ha, e1⟩ := hx z hz
    obtain ⟨c, hc, e2⟩ := hy z hz
    refine ⟨a + c, add_mem ha hc, ?_⟩
    rw [AddMemClass.coe_add, map_add (f := _), Matrix.add_mulVec, e1, e2, smul_add]
  zero_mem' z hz := ⟨0, zero_mem _, by simp⟩
  smul_mem' c {x} hx z hz := by
    obtain ⟨a, ha, e⟩ := hx z hz
    refine ⟨φ (c : S) *ᵥ a, c.2 a ha, ?_⟩
    rw [smul_eq_mul, MulMemClass.coe_mul, map_mul, ← Matrix.mulVec_mulVec, e, Matrix.mulVec_smul]

theorem mk_eq_of {x y : keepT φ Λ} (h : ∀ z ∈ Λ, φ (x : S) *ᵥ z = φ (y : S) *ᵥ z) :
    Ideal.Quotient.mk (congI φ Λ p) x = Ideal.Quotient.mk (congI φ Λ p) y := by
  refine Ideal.Quotient.eq.mpr fun z hz => ⟨0, zero_mem _, ?_⟩
  rw [AddSubgroupClass.coe_sub, map_sub, Matrix.sub_mulVec, h z hz, sub_self, smul_zero]

theorem surj_of_isUnit {x : keepT φ Λ} (hx : IsUnit (Ideal.Quotient.mk (congI φ Λ p) x)) :
    ∀ z ∈ Λ, ∃ y ∈ Λ, ∃ y' ∈ Λ, z = φ (x : S) *ᵥ y + p • y' := by
  obtain ⟨u, hu⟩ := hx
  obtain ⟨t, ht⟩ := Ideal.Quotient.mk_surjective (I := congI φ Λ p) (↑u⁻¹)
  have h1 : Ideal.Quotient.mk (congI φ Λ p) (x * t) = Ideal.Quotient.mk (congI φ Λ p) 1 := by
    rw [map_mul, ← hu, ht, Units.mul_inv, map_one]
  have h2 := Ideal.Quotient.eq.mp h1
  intro z hz
  obtain ⟨a, ha, e⟩ := h2 z hz
  refine ⟨φ (t : S) *ᵥ z, t.2 z hz, -a, neg_mem ha, ?_⟩
  rw [AddSubgroupClass.coe_sub, MulMemClass.coe_mul, OneMemClass.coe_one, map_sub, map_mul, map_one, Matrix.sub_mulVec,
    ← Matrix.mulVec_mulVec, Matrix.one_mulVec, sub_eq_iff_eq_add] at e
  rw [smul_neg, e]; abel

end Ring

end GlobalTheory.TwoFacCore

noncomputable section
namespace GlobalTheory.TwoFacCore

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def SelfAdj (σ : E →ₐ[F] E) {d : ℕ} (J Q : Matrix (Fin d) (Fin d) (AE F E)) : Prop :=
  Qᵀ * J = J * (cA σ).mapMatrix Q

theorem selfAdj_one (σ : E →ₐ[F] E) {d : ℕ} (J : Matrix (Fin d) (Fin d) (AE F E)) : SelfAdj σ J 1 := by
  simp [SelfAdj]

theorem selfAdj_add {σ : E →ₐ[F] E} {d : ℕ} {J P Q : Matrix (Fin d) (Fin d) (AE F E)} (hP : SelfAdj σ J P)
    (hQ : SelfAdj σ J Q) : SelfAdj σ J (P + Q) := by
  unfold SelfAdj at *
  rw [Matrix.transpose_add, Matrix.add_mul, hP, hQ, map_add (f := _), Matrix.mul_add]

theorem selfAdj_sub {σ : E →ₐ[F] E} {d : ℕ} {J P Q : Matrix (Fin d) (Fin d) (AE F E)} (hP : SelfAdj σ J P)
    (hQ : SelfAdj σ J Q) : SelfAdj σ J (P - Q) := by
  unfold SelfAdj at *
  rw [Matrix.transpose_sub, Matrix.sub_mul, hP, hQ, map_sub, Matrix.mul_sub]

theorem selfAdj_pow {σ : E →ₐ[F] E} {d : ℕ} {J Q : Matrix (Fin d) (Fin d) (AE F E)} (hQ : SelfAdj σ J Q) :
    ∀ n : ℕ, SelfAdj σ J (Q ^ n)
  | 0 => by rw [pow_zero]; exact selfAdj_one σ J
  | n + 1 => by
    have ih := selfAdj_pow hQ n
    unfold SelfAdj at *
    rw [pow_succ, Matrix.transpose_mul, Matrix.mul_assoc, ih, ← Matrix.mul_assoc, hQ, Matrix.mul_assoc, ← map_mul,
      ← pow_succ']
    rw [pow_succ]

theorem sa_gen {σ : E →ₐ[F] E} {d : ℕ}
    {J K Ki : Matrix (Fin d) (Fin d) (AE F E)} (hK : Kᵀ * J * K.map (cA σ) = J) (hKi : Kiᵀ * J * Ki.map (cA σ) = J)
    (hKK : K * Ki = 1) (hKiK : Ki * K = 1) : SelfAdj σ J (K + Ki + 1 + 1) := by
  have h1 : Kᵀ * J = J * (cA σ).mapMatrix Ki := by
    calc Kᵀ * J = Kᵀ * J * ((cA σ).mapMatrix K * (cA σ).mapMatrix Ki) := by rw [← map_mul, hKK, map_one, Matrix.mul_one]
      _ = J * (cA σ).mapMatrix Ki := by rw [← Matrix.mul_assoc, AlgHom.mapMatrix_apply, hK]
  have h2 : Kiᵀ * J = J * (cA σ).mapMatrix K := by
    calc Kiᵀ * J = Kiᵀ * J * ((cA σ).mapMatrix Ki * (cA σ).mapMatrix K) := by rw [← map_mul, hKiK, map_one, Matrix.mul_one]
      _ = J * (cA σ).mapMatrix K := by rw [← Matrix.mul_assoc, AlgHom.mapMatrix_apply, hKi]
  have h3 : SelfAdj σ J (K + Ki) := by
    unfold SelfAdj
    rw [Matrix.transpose_add, Matrix.add_mul, h1, h2, map_add (f := _), Matrix.mul_add, add_comm]
  exact selfAdj_add (selfAdj_add h3 (selfAdj_one σ J)) (selfAdj_one σ J)

end GlobalTheory.TwoFacCore

noncomputable section
namespace GlobalTheory.TwoFacCore

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]


set_option maxHeartbeats 1000000 in
theorem units_mod {d : ℕ} (Λ : AddSubgroup (Fin d → AE F E)) (p : ℕ) (K Ki : Matrix (Fin d) (Fin d) (AE F E))
    (β b up um h : AE F E) (N₀ : ℕ) (hKK : K * Ki = 1) (hKiK : Ki * K = 1)
    (hK : ∀ z ∈ Λ, K *ᵥ z ∈ Λ) (hKi : ∀ z ∈ Λ, Ki *ᵥ z ∈ Λ)
    (hsc : ∀ z ∈ Λ, β • z ∈ Λ ∧ b • z ∈ Λ ∧ up • z ∈ Λ ∧ um • z ∈ Λ ∧ h • z ∈ Λ)
    (hb : ∀ z ∈ Λ, (β * b) • z = z) (hh : ∀ z ∈ Λ, (h + h) • z = z) (hp : ∀ z ∈ Λ, ((1 + β) * up) • z = z)
    (hm : ∀ z ∈ Λ, ((1 - β) * um) • z = z)
    (hD : ∀ z ∈ Λ, ∃ y ∈ Λ, ((K + Ki + 1 + 1) ^ (2 * (N₀ + 1))) *ᵥ z - ((K + Ki + 1 + 1) ^ (N₀ + 1)) *ᵥ z = p • y)
    (Y : Matrix (Fin d) (Fin d) (AE F E)) (hY : Y = β • (1 - (K + Ki + 1 + 1) ^ (N₀ + 1))) :
    (∀ z ∈ Λ, Y *ᵥ z ∈ Λ) ∧
    (∀ z ∈ Λ, ∃ y ∈ Λ, ∃ y' ∈ Λ, z = (1 + Y) *ᵥ y + p • y') ∧
    (∀ z ∈ Λ, ∃ y ∈ Λ, ∃ y' ∈ Λ, z = (1 - Y) *ᵥ y + p • y') ∧
    (∀ z ∈ Λ, ∃ y ∈ Λ, ∃ y' ∈ Λ, z = (1 + Y + K * (1 - Y)) *ᵥ y + p • y') := by
  have hcomm : ∀ x ∈ ({K, Ki} : Set (Matrix (Fin d) (Fin d) (AE F E))),
      ∀ y ∈ ({K, Ki} : Set (Matrix (Fin d) (Fin d) (AE F E))), x * y = y * x := by
    intro x hx y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> simp [hKK, hKiK]
  letI : IsMulCommutative (Algebra.adjoin (AE F E) ({K, Ki} : Set (Matrix (Fin d) (Fin d) (AE F E)))) :=
    Algebra.isMulCommutative_adjoin (AE F E) (fun x hx y hy _ => hcomm x hx y hy)
  letI : CommRing (Algebra.adjoin (AE F E) ({K, Ki} : Set (Matrix (Fin d) (Fin d) (AE F E)))) :=
    by
      open scoped IsMulCommutative in
        infer_instance
  let φ : (Algebra.adjoin (AE F E) ({K, Ki} : Set (Matrix (Fin d) (Fin d) (AE F E)))) →+*
      Matrix (Fin d) (Fin d) (AE F E) := (Algebra.adjoin (AE F E) ({K, Ki} : Set (Matrix (Fin d) (Fin d) (AE F E)))).val.toRingHom
  let kS : Algebra.adjoin (AE F E) ({K, Ki} : Set (Matrix (Fin d) (Fin d) (AE F E))) :=
    ⟨K, Algebra.subset_adjoin (by simp)⟩
  let kiS : Algebra.adjoin (AE F E) ({K, Ki} : Set (Matrix (Fin d) (Fin d) (AE F E))) :=
    ⟨Ki, Algebra.subset_adjoin (by simp)⟩
  let cS : AE F E → Algebra.adjoin (AE F E) ({K, Ki} : Set (Matrix (Fin d) (Fin d) (AE F E))) :=
    fun c => algebraMap (AE F E) _ c
  have hφk : φ kS = K := rfl
  have hφki : φ kiS = Ki := rfl
  have hφc : ∀ c z, φ (cS c) *ᵥ z = c • z := by
    intro c z
    show (algebraMap (AE F E) (Matrix (Fin d) (Fin d) (AE F E)) c) *ᵥ z = c • z
    rw [Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, Matrix.one_mulVec]
  set_option synthInstance.maxHeartbeats 200000 in
  let kT : keepT φ Λ := ⟨kS, fun z hz => hK z hz⟩
  let kiT : keepT φ Λ := ⟨kiS, fun z hz => hKi z hz⟩
  have cmem : ∀ c : AE F E, (∀ z ∈ Λ, c • z ∈ Λ) → cS c ∈ keepT φ Λ := fun c hc z hz => by
    show φ (cS c) *ᵥ z ∈ Λ
    rw [hφc]; exact hc z hz
  let βT : keepT φ Λ := ⟨cS β, cmem β fun z hz => (hsc z hz).1⟩
  let bT : keepT φ Λ := ⟨cS b, cmem b fun z hz => (hsc z hz).2.1⟩
  let upT : keepT φ Λ := ⟨cS up, cmem up fun z hz => (hsc z hz).2.2.1⟩
  let umT : keepT φ Λ := ⟨cS um, cmem um fun z hz => (hsc z hz).2.2.2.1⟩
  let hT : keepT φ Λ := ⟨cS h, cmem h fun z hz => (hsc z hz).2.2.2.2⟩
  let mk := Ideal.Quotient.mk (congI φ Λ p)
  have hK' : mk kT * mk kiT = 1 := by
    have : mk (kT * kiT) = mk 1 := mk_eq_of φ Λ p fun z hz => by
      show (K * Ki) *ᵥ z = (1 : Matrix (Fin d) (Fin d) (AE F E)) *ᵥ z
      rw [hKK]
    simpa only [map_mul, map_one] using this
  have hsc2 : ∀ (c c' : AE F E) (z : Fin d → AE F E), φ (cS c * cS c') *ᵥ z = (c * c') • z := by
    intro c c' z
    rw [map_mul, ← Matrix.mulVec_mulVec, hφc, hφc, smul_smul]
  have hb' : mk βT * mk bT = 1 := by
    have : mk (βT * bT) = mk 1 := mk_eq_of φ Λ p fun z hz => by
      show φ (cS β * cS b) *ᵥ z = (1 : Matrix (Fin d) (Fin d) (AE F E)) *ᵥ z
      rw [hsc2, hb z hz, Matrix.one_mulVec]
    simpa only [map_mul, map_one] using this
  have hh' : mk hT + mk hT = 1 := by
    have : mk (hT + hT) = mk 1 := mk_eq_of φ Λ p fun z hz => by
      show φ (cS h + cS h) *ᵥ z = (1 : Matrix (Fin d) (Fin d) (AE F E)) *ᵥ z
      rw [map_add (f := _), Matrix.add_mulVec, hφc, ← add_smul, hh z hz, Matrix.one_mulVec]
    simpa only [map_add (f := _), map_one] using this
  have hp' : (1 + mk βT) * mk upT = 1 := by
    have : mk ((1 + βT) * upT) = mk 1 := mk_eq_of φ Λ p fun z hz => by
      show φ ((1 + cS β) * cS up) *ᵥ z = (1 : Matrix (Fin d) (Fin d) (AE F E)) *ᵥ z
      have e : (1 + cS β) * cS up = cS ((1 + β) * up) := by simp only [cS, map_add (f := _), map_mul, map_one]
      rw [e, hφc, hp z hz, Matrix.one_mulVec]
    simpa only [map_mul, map_add (f := _), map_one] using this
  have hm' : (1 - mk βT) * mk umT = 1 := by
    have : mk ((1 - βT) * umT) = mk 1 := mk_eq_of φ Λ p fun z hz => by
      show φ ((1 - cS β) * cS um) *ᵥ z = (1 : Matrix (Fin d) (Fin d) (AE F E)) *ᵥ z
      have e : (1 - cS β) * cS um = cS ((1 - β) * um) := by simp only [cS, map_sub, map_mul, map_one]
      rw [e, hφc, hm z hz, Matrix.one_mulVec]
    simpa only [map_mul, map_sub, map_one] using this
  let fT : keepT φ Λ := kT + kiT + 1 + 1
  have hφf : φ ((fT : _)) = K + Ki + 1 + 1 := by
    show φ (kS + kiS + 1 + 1) = K + Ki + 1 + 1
    rw [map_add (f := _), map_add (f := _), map_add (f := _), map_one, hφk, hφki]
  have hD' : (mk kT + mk kiT + 1 + 1) ^ (2 * (N₀ + 1)) = (mk kT + mk kiT + 1 + 1) ^ (N₀ + 1) := by
    have e : mk kT + mk kiT + 1 + 1 = mk fT := by simp only [fT, map_add (f := _), map_one]
    rw [e, ← map_pow, ← map_pow]
    refine Ideal.Quotient.eq.mpr fun z hz => ?_
    obtain ⟨y, hy, ey⟩ := hD z hz
    refine ⟨y, hy, ?_⟩
    rw [AddSubgroupClass.coe_sub, SubmonoidClass.coe_pow, SubmonoidClass.coe_pow, map_sub, map_pow, map_pow, hφf,
      Matrix.sub_mulVec]
    exact ey
  obtain ⟨u1, u2, u3⟩ := alg (mk kT) (mk kiT) (mk βT) (mk bT) (mk upT) (mk umT) (mk hT) N₀ hK' hb' hh' hp' hm' hD'
  let YT : keepT φ Λ := βT * (1 - fT ^ (N₀ + 1))
  have hφY : φ (YT : _) = Y := by
    show φ (cS β * (1 - (kS + kiS + 1 + 1) ^ (N₀ + 1))) = Y
    rw [map_mul, map_sub, map_one, map_pow, map_add (f := _), map_add (f := _), map_add (f := _), map_one, hφk, hφki, hY, Algebra.smul_def]
    rfl
  have eY : mk βT * (1 - (mk kT + mk kiT + 1 + 1) ^ (N₀ + 1)) = mk YT := by
    simp only [YT, fT, map_mul, map_sub, map_one, map_pow, map_add (f := _)]
  rw [eY] at u1 u2 u3
  have u1' : IsUnit (mk (1 + YT)) := by rw [map_add (f := _), map_one]; exact u1
  have u2' : IsUnit (mk (1 - YT)) := by rw [map_sub, map_one]; exact u2
  have u3' : IsUnit (mk (1 + YT + kT * (1 - YT))) := by
    rw [map_add (f := _), map_add (f := _), map_mul, map_sub, map_one]; exact u3
  refine ⟨fun z hz => hφY ▸ YT.2 z hz, ?_, ?_, ?_⟩
  · have s1 := surj_of_isUnit φ Λ p u1'
    have : φ ((1 + YT : keepT φ Λ) : Algebra.adjoin (AE F E) ({K, Ki} : Set (Matrix (Fin d) (Fin d) (AE F E)))) = 1 + Y := by
      show φ (1 + (YT : Algebra.adjoin (AE F E) ({K, Ki} : Set (Matrix (Fin d) (Fin d) (AE F E))))) = 1 + Y
      rw [map_add (f := _), map_one, hφY]
    rwa [this] at s1
  · have s2 := surj_of_isUnit φ Λ p u2'
    have : φ ((1 - YT : keepT φ Λ) : Algebra.adjoin (AE F E) ({K, Ki} : Set (Matrix (Fin d) (Fin d) (AE F E)))) = 1 - Y := by
      show φ (1 - (YT : Algebra.adjoin (AE F E) ({K, Ki} : Set (Matrix (Fin d) (Fin d) (AE F E))))) = 1 - Y
      rw [map_sub, map_one, hφY]
    rwa [this] at s2
  · have s3 := surj_of_isUnit φ Λ p u3'
    have : φ ((1 + YT + kT * (1 - YT) : keepT φ Λ) : Algebra.adjoin (AE F E) ({K, Ki} : Set (Matrix (Fin d) (Fin d) (AE F E))))
        = 1 + Y + K * (1 - Y) := by
      show φ (1 + (YT : Algebra.adjoin (AE F E) ({K, Ki} : Set (Matrix (Fin d) (Fin d) (AE F E)))) +
        kS * (1 - (YT : Algebra.adjoin (AE F E) ({K, Ki} : Set (Matrix (Fin d) (Fin d) (AE F E)))))) = 1 + Y + K * (1 - Y)
      rw [map_add (f := _), map_add (f := _), map_mul, map_sub, map_one, hφY, hφk]
    rwa [this] at s3

end GlobalTheory.TwoFacCore

noncomputable section
namespace GlobalTheory.TwoFacCore

theorem smul_map {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {d : ℕ}
    (c : AE F E) (Q : Matrix (Fin d) (Fin d) (AE F E)) : (c • Q).map (cA σ) = cA σ c • Q.map (cA σ) := by
  ext i j
  simp [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]


set_option maxHeartbeats 1000000 in
theorem exists_skew_cayley : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w →
    ∀ k ∈ GlobalTheory.InertSph.KAt σ G.W v, ∃ Y : Matrix (Fin (a + a')) (Fin (a + a')) (AE F E),
    At (evFin F v) Y ∧ (∀ z ∈ GlobalTheory.InertSph.latAt G.W v, Y *ᵥ z ∈ GlobalTheory.InertSph.latAt G.W v) ∧
    Yᵀ * incM F G.W.J + incM F G.W.J * Y.map (cA σ) = 0 ∧
    (∃ M : Matrix (Fin (a + a')) (Fin (a + a')) (AE F E), (1 + Y) * M = 1 ∧ M * (1 + Y) = 1 ∧
      ∀ z ∈ GlobalTheory.InertSph.latAt G.W v, M *ᵥ z ∈ GlobalTheory.InertSph.latAt G.W v) ∧
    (∃ M : Matrix (Fin (a + a')) (Fin (a + a')) (AE F E), (1 - Y) * M = 1 ∧ M * (1 - Y) = 1 ∧
      ∀ z ∈ GlobalTheory.InertSph.latAt G.W v, M *ᵥ z ∈ GlobalTheory.InertSph.latAt G.W v) ∧
    (∃ M : Matrix (Fin (a + a')) (Fin (a + a')) (AE F E), (1 + Y + mat k * (1 - Y)) * M = 1 ∧
      M * (1 + Y + mat k * (1 - Y)) = 1 ∧ ∀ z ∈ GlobalTheory.InertSph.latAt G.W v, M *ᵥ z ∈ GlobalTheory.InertSph.latAt G.W v) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v w hin k hk
  have hlat : G.W.L.IsLattice E := hT.geo.hW.lat.toIsLattice
  obtain ⟨h2v, h3, -⟩ := hT.base.inert v w hin
  have hp0 : 0 < Ideal.absNorm v.asIdeal := by omega
  have hpv : ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 F) ∈ v.asIdeal := Ideal.absNorm_mem _
  obtain ⟨β, b, up, um, hβat, hβσ, hsc⟩ := GlobalTheory.T.exists_traceZero_adele_unit_lattice_at_inert_place F E σ B hT.base (a + a') G.W v w hin
  have hKK : mat k * mat k⁻¹ = 1 := by
    show mat (k * k⁻¹) = 1
    rw [mul_inv_cancel]; rfl
  have hKiK : mat k⁻¹ * mat k = 1 := by
    show mat (k⁻¹ * k) = 1
    rw [inv_mul_cancel]; rfl
  have hKk : ∀ z ∈ GlobalTheory.InertSph.latAt G.W v, mat k *ᵥ z ∈ GlobalTheory.InertSph.latAt G.W v := fun z hz => (hk.2 z hz).1
  have hKik : ∀ z ∈ GlobalTheory.InertSph.latAt G.W v, mat k⁻¹ *ᵥ z ∈ GlobalTheory.InertSph.latAt G.W v := fun z hz => (hk.2 z hz).2
  have hfk : ∀ z ∈ GlobalTheory.InertSph.latAt G.W v, (mat k + mat k⁻¹ + 1 + 1) *ᵥ z ∈ GlobalTheory.InertSph.latAt G.W v := by
    intro z hz
    rw [Matrix.add_mulVec, Matrix.add_mulVec, Matrix.add_mulVec, Matrix.one_mulVec]
    exact add_mem (add_mem (add_mem (hKk z hz) (hKik z hz)) hz) hz
  obtain ⟨N, hN0, hN⟩ := GlobalTheory.T.exists_pow_idempotent_adelicLattice_mod_prime F E (a + a') G.W hlat v _ hp0 hpv _ hfk
  obtain ⟨N₀, rfl⟩ : ∃ N₀, N = N₀ + 1 := ⟨N - 1, by omega⟩
  have hh : ∀ z ∈ GlobalTheory.InertSph.latAt G.W v, (algebraMap (AF F) (AE F E) ⅟(2 : AF F)) • z ∈ GlobalTheory.InertSph.latAt G.W v :=
    fun z hz => by rw [algebraMap_smul]; exact GlobalTheory.DblVacGauss.invOf_two_smul_mem_latAt G.W v h2v hz
  have hh2 : ∀ z ∈ GlobalTheory.InertSph.latAt G.W v,
      (algebraMap (AF F) (AE F E) ⅟(2 : AF F) + algebraMap (AF F) (AE F E) ⅟(2 : AF F)) • z = z := by
    intro z _
    rw [← map_add (f := _), ← two_mul, mul_invOf_self', map_one, one_smul]
  obtain ⟨hYk, s1, s2, s3⟩ := units_mod (GlobalTheory.InertSph.latAt G.W v) (Ideal.absNorm v.asIdeal) (mat k) (mat k⁻¹) β b up um
    (algebraMap (AF F) (AE F E) ⅟(2 : AF F)) N₀ hKK hKiK hKk hKik
    (fun z hz => ⟨(hsc z hz).1, (hsc z hz).2.1, (hsc z hz).2.2.1, (hsc z hz).2.2.2.1, hh z hz⟩)
    (fun z hz => (hsc z hz).2.2.2.2.1) hh2 (fun z hz => (hsc z hz).2.2.2.2.2.1) (fun z hz => (hsc z hz).2.2.2.2.2.2)
    hN _ rfl
  set Y := β • (1 - (mat k + mat k⁻¹ + 1 + 1) ^ (N₀ + 1)) with hYdef
  have hYat : At (evFin F v) Y := by
    intro u hu
    rw [hYdef, ← smul_assoc, hβat u hu, zero_smul]
  have hKat : At (evFin F v) (mat k - 1) := hk.1
  have keepAdd : ∀ {A C : Matrix (Fin (a + a')) (Fin (a + a')) (AE F E)},
      (∀ z ∈ GlobalTheory.InertSph.latAt G.W v, A *ᵥ z ∈ GlobalTheory.InertSph.latAt G.W v) →
      (∀ z ∈ GlobalTheory.InertSph.latAt G.W v, C *ᵥ z ∈ GlobalTheory.InertSph.latAt G.W v) →
      ∀ z ∈ GlobalTheory.InertSph.latAt G.W v, (A + C) *ᵥ z ∈ GlobalTheory.InertSph.latAt G.W v :=
    fun hA hC z hz => by rw [Matrix.add_mulVec]; exact add_mem (hA z hz) (hC z hz)
  have keepSub : ∀ {A C : Matrix (Fin (a + a')) (Fin (a + a')) (AE F E)},
      (∀ z ∈ GlobalTheory.InertSph.latAt G.W v, A *ᵥ z ∈ GlobalTheory.InertSph.latAt G.W v) →
      (∀ z ∈ GlobalTheory.InertSph.latAt G.W v, C *ᵥ z ∈ GlobalTheory.InertSph.latAt G.W v) →
      ∀ z ∈ GlobalTheory.InertSph.latAt G.W v, (A - C) *ᵥ z ∈ GlobalTheory.InertSph.latAt G.W v :=
    fun hA hC z hz => by rw [Matrix.sub_mulVec]; exact sub_mem (hA z hz) (hC z hz)
  have keepMul : ∀ {A C : Matrix (Fin (a + a')) (Fin (a + a')) (AE F E)},
      (∀ z ∈ GlobalTheory.InertSph.latAt G.W v, A *ᵥ z ∈ GlobalTheory.InertSph.latAt G.W v) →
      (∀ z ∈ GlobalTheory.InertSph.latAt G.W v, C *ᵥ z ∈ GlobalTheory.InertSph.latAt G.W v) →
      ∀ z ∈ GlobalTheory.InertSph.latAt G.W v, (A * C) *ᵥ z ∈ GlobalTheory.InertSph.latAt G.W v :=
    fun hA hC z hz => by rw [← Matrix.mulVec_mulVec]; exact hA _ (hC z hz)
  have keepOne : ∀ z ∈ GlobalTheory.InertSph.latAt G.W v, (1 : Matrix (Fin (a + a')) (Fin (a + a')) (AE F E)) *ᵥ z ∈
      GlobalTheory.InertSph.latAt G.W v := fun z hz => by rw [Matrix.one_mulVec]; exact hz
  refine ⟨Y, hYat, hYk, ?_, ?_, ?_, ?_⟩
  ·
    have hsa : SelfAdj σ (incM F G.W.J) (1 - (mat k + mat k⁻¹ + 1 + 1) ^ (N₀ + 1)) :=
      selfAdj_sub (selfAdj_one σ _) (selfAdj_pow (sa_gen k.2 (k⁻¹).2 hKK hKiK) _)
    unfold SelfAdj at hsa
    rw [hYdef, Matrix.transpose_smul, Matrix.smul_mul, hsa, smul_map, hβσ, Matrix.mul_smul, ← AlgHom.mapMatrix_apply,
      neg_smul, add_neg_cancel]
  · refine GlobalTheory.T.exists_inverse_preserving_adelicLatticeAtPlace F E (a + a') G.W hT.geo.hW.lat v _ hpv 1 isUnit_one _ ?_ (keepAdd keepOne hYk) s1
    rw [one_smul, add_sub_cancel_left]; exact hYat
  · refine GlobalTheory.T.exists_inverse_preserving_adelicLatticeAtPlace F E (a + a') G.W hT.geo.hW.lat v _ hpv 1 isUnit_one _ ?_ (keepSub keepOne hYk) s2
    intro u hu
    rw [one_smul, sub_sub_cancel_left, smul_neg, hYat u hu, neg_zero]
  · refine GlobalTheory.T.exists_inverse_preserving_adelicLatticeAtPlace F E (a + a') G.W hT.geo.hW.lat v _ hpv 2 (isUnit_of_invertible _) _ ?_
      (keepAdd (keepAdd keepOne hYk) (keepMul hKk (keepSub keepOne hYk))) s3
    intro u hu
    have e : 1 + Y + mat k * (1 - Y) - (2 : AF F) • (1 : Matrix (Fin (a + a')) (Fin (a + a')) (AE F E)) =
        Y + (mat k - 1) - mat k * Y := by
      rw [two_smul, Matrix.mul_sub, Matrix.mul_one]; abel
    rw [e, smul_sub, smul_add, ← Matrix.mul_smul, hYat u hu, hKat u hu, Matrix.mul_zero, add_zero, sub_zero]

end GlobalTheory.TwoFacCore
end
end
end
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSkewCayleyInertPlaceStabilizerStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_skew_cayley_inertPlace_stabilizer : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w →
    ∀ k ∈ GlobalTheory.InertSph.KAt σ G.W v, ∃ Y : Matrix (Fin (a + a')) (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
    At (evFin F v) Y ∧ (∀ z ∈ GlobalTheory.InertSph.latAt G.W v, Y *ᵥ z ∈ GlobalTheory.InertSph.latAt G.W v) ∧
    Yᵀ * incM F G.W.J + incM F G.W.J * Y.map (cA σ) = 0 ∧
    (∃ M : Matrix (Fin (a + a')) (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), (1 + Y) * M = 1 ∧ M * (1 + Y) = 1 ∧
      ∀ z ∈ GlobalTheory.InertSph.latAt G.W v, M *ᵥ z ∈ GlobalTheory.InertSph.latAt G.W v) ∧
    (∃ M : Matrix (Fin (a + a')) (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), (1 - Y) * M = 1 ∧ M * (1 - Y) = 1 ∧
      ∀ z ∈ GlobalTheory.InertSph.latAt G.W v, M *ᵥ z ∈ GlobalTheory.InertSph.latAt G.W v) ∧
    (∃ M : Matrix (Fin (a + a')) (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), (1 + Y + mat k * (1 - Y)) * M = 1 ∧
      M * (1 + Y + mat k * (1 - Y)) = 1 ∧ ∀ z ∈ GlobalTheory.InertSph.latAt G.W v, M *ᵥ z ∈ GlobalTheory.InertSph.latAt G.W v) := by
  first | exact @GlobalTheory.TwoFacCore.exists_skew_cayley | exact GlobalTheory.TwoFacCore.exists_skew_cayley | (intros; apply GlobalTheory.TwoFacCore.exists_skew_cayley <;> assumption)
end
