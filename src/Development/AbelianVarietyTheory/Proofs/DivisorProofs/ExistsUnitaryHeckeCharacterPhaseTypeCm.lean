module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonsplitCentraliserNormElement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EllipticCharpolySelfReciprocal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableAtFoldrLineDer
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousUgReindex
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrangianEvaluationTranslation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdArgRealUnitEqOneStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryHeckeCharacterPhaseTypeCm
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenIdeleSubgroupCongruenceModQ
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenIdeleSubgroupCongruenceModQ
open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.IndefR.DatumF

noncomputable section

namespace GlobalTheory.OpenCongrIdele

theorem exists_open_congr : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsCMField E] (q : ℕ), q ≠ 0 → ∃ U : Subgroup (AF F ⊗[F] E)ˣ, IsOpen (U : Set (AF F ⊗[F] E)ˣ) ∧ (∀ z : (AF F ⊗[F] E)ˣ, At (evI F) ((z : AF F ⊗[F] E) - 1) → z ∈ U) ∧ ∀ k : Eˣ, Units.map (incAF F E).toMonoidHom k ∈ U → ∃ u : (𝓞 E)ˣ, ((u : 𝓞 E) : E) = k ∧ (u : 𝓞 E) - 1 ∈ Ideal.span {((q : ℕ) : 𝓞 E)} := by
  intro F E _ _ _ _ _ _ q hq
  obtain ⟨Θ, hc, hΘ⟩ := GlobalTheory.CharTransport.exists_toAdele F E
  set 𝔪 : Ideal (𝓞 E) := Ideal.span {((q : ℕ) : 𝓞 E)} with h𝔪
  have hm : 𝔪 ≠ ⊥ := by
    rw [h𝔪, Ne, Ideal.span_singleton_eq_bot]; exact Nat.cast_ne_zero.2 hq
  let V : Subgroup (Neutral.B1.Ideles E) := GlobalTheory.Mem.Chr.unitIdl E ⊓ GlobalTheory.RayChar.congrIdl 𝔪
  let φ : (AF F ⊗[F] E)ˣ →* Neutral.B1.Ideles E := Units.map Θ.toMonoidHom
  refine ⟨V.comap φ, ?_, fun z hz => ?_, fun k hk => ?_⟩
  · exact (GlobalTheory.Mem.UnitOpen.isOpen_unitIdl.inter (GlobalTheory.RayChar.isOpen_congrIdl hm)).preimage
      (Continuous.units_map _ hc)
  · have hfin : (Θ (z : AF F ⊗[F] E)).2 = 1 := by
      let a : AF F := pairA F 0 1
      have ha : evI F a = 0 := by
        show InfiniteAdeleRing.ringEquiv_mixedSpace F 0 = 0
        exact map_zero _
      have h0 : a • ((z : AF F ⊗[F] E) - 1) = 0 := hz a ha
      have h1 : Θ (a • ((z : AF F ⊗[F] E) - 1)) =
          GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap F E a * Θ ((z : AF F ⊗[F] E) - 1) := by
        rw [Algebra.smul_def, map_mul]
        congr 1
        change Θ (a ⊗ₜ[F] (1 : E)) = _
        rw [hΘ, map_one, mul_one]
      have h2 : (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap F E a).2 = 1 := map_one (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteAdeleMap F E)
      have h3 : (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap F E a * Θ ((z : AF F ⊗[F] E) - 1)).2 = 0 := by
        rw [← h1, h0, map_zero]; rfl
      have h4 : (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap F E a).2 * (Θ ((z : AF F ⊗[F] E) - 1)).2 = 0 := h3
      rw [h2, one_mul, map_sub, map_one] at h4
      exact sub_eq_zero.1 h4
    have hv : ∀ v : HeightOneSpectrum (𝓞 E), GlobalTheory.RayChar.cmp (φ z) v = 1 := fun v => by
      show (Θ (z : AF F ⊗[F] E)).2 v = 1
      rw [hfin]; rfl
    refine ⟨fun v => ?_, (GlobalTheory.RayChar.mem_congrIdl hm).2 fun v _ => ?_⟩
    · show Valued.v (GlobalTheory.RayChar.cmp (φ z) v) = 1
      rw [hv v, map_one]
    · rw [hv v, sub_self, map_zero]; exact zero_le'
  · have he : φ (Units.map (incAF F E).toMonoidHom k) = Neutral.B1.diagUnits E k := Units.ext (by
      change Θ ((1 : AF F) ⊗ₜ[F] (k : E)) = _
      rw [hΘ, map_one, one_mul]; rfl)
    have hk' : Neutral.B1.diagUnits E k ∈ V := by rw [← he]; exact hk
    obtain ⟨u, hu⟩ := GlobalTheory.DefU.NonTriv.exists_unit k hk'.1
    refine ⟨u, hu, (GlobalTheory.RayChar.mem_iff_at hm _).2 fun v hv => ?_⟩
    rw [GlobalTheory.RayChar.at'_sub_one]
    have h2 := (GlobalTheory.RayChar.mem_congrIdl hm).1 hk'.2 v hv
    change Valued.v (GlobalTheory.RayChar.cmp (GlobalTheory.Mem.Chr.diagUnits E k) v - 1) ≤ _ at h2
    rw [GlobalTheory.RayChar.cmp_diag, ← hu] at h2
    exact h2

end GlobalTheory.OpenCongrIdele
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenIdeleSubgroupCongruenceModQStatement
open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.IndefR.DatumF
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_open_idele_subgroup_congruence_mod_q : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsCMField E] (q : ℕ), q ≠ 0 → ∃ U : Subgroup (AF F ⊗[F] E)ˣ, IsOpen (U : Set (AF F ⊗[F] E)ˣ) ∧ (∀ z : (AF F ⊗[F] E)ˣ, At (evI F) ((z : AF F ⊗[F] E) - 1) → z ∈ U) ∧ ∀ k : Eˣ, Units.map (incAF F E).toMonoidHom k ∈ U → ∃ u : (𝓞 E)ˣ, ((u : 𝓞 E) : E) = k ∧ (u : 𝓞 E) - 1 ∈ Ideal.span {((q : ℕ) : 𝓞 E)} := by
  first | exact @GlobalTheory.OpenCongrIdele.exists_open_congr | exact GlobalTheory.OpenCongrIdele.exists_open_congr | (intros; apply GlobalTheory.OpenCongrIdele.exists_open_congr <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypeUnitPhaseProdEqOneOfCongruentOne
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypeUnitPhaseProdEqOneOfCongruentOne
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace GlobalTheory

theorem weil_unit_phase_prod : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsCMField E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (emb : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w) (q : ℕ), q.Prime → 2 < q → ¬ q ∣ Nat.card (Units.torsion E) → ∀ u : (𝓞 E)ˣ, (u : 𝓞 E) - 1 ∈ Ideal.span {((q : ℕ) : 𝓞 E)} → ∏ w : InfinitePlace F, ((emb w).1 ((u : 𝓞 E) : E) / ((‖(emb w).1 ((u : 𝓞 E) : E)‖ : ℝ) : ℂ)) = 1 := by
  intro F E _ _ _ _ _ _ σ h emb q hq hq2 ht u hu
  have hr := GlobalTheory.T.unit_real_of_sub_one_mem_span_prime E q hq ht u hu
  have hs := GlobalTheory.T.prod_arg_real_unit_eq_one' E q hq hq2 u hu hr
  obtain ⟨hF, hE, h2, -⟩ := h
  let f : InfinitePlace F → InfinitePlace E := fun w => InfinitePlace.mk (emb w).1
  have hcomap : ∀ w, (f w).comap (algebraMap F E) = w := by
    intro w
    simp only [f]
    rw [InfinitePlace.comap_mk, (emb w).2, InfinitePlace.mk_embedding]
  have hinj : Function.Injective f := fun a b hab => by
    rw [← hcomap a, ← hcomap b, hab]
  have hcard : Fintype.card (InfinitePlace F) = Fintype.card (InfinitePlace E) := by
    have a1 := InfinitePlace.card_add_two_mul_card_eq_rank F
    have a2 := InfinitePlace.card_add_two_mul_card_eq_rank E
    have b1 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces (K := F)
    have b2 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces (K := E)
    have c1 := IsTotallyReal.nrComplexPlaces_eq_zero F
    have c2 := IsTotallyComplex.nrRealPlaces_eq_zero E
    have d := Module.finrank_mul_finrank ℚ F E
    rw [h2] at d
    omega
  have hbij : Function.Bijective f := (Fintype.bijective_iff_injective_and_card f).2 ⟨hinj, hcard⟩
  have hfac : ∀ w, (emb w).1 ((u : 𝓞 E) : E) = (f w).embedding ((u : 𝓞 E) : E) := by
    intro w
    rcases InfinitePlace.embedding_mk_eq (emb w).1 with h' | h'
    · simp only [f]; rw [h']
    · simp only [f]; rw [h', ComplexEmbedding.conjugate_coe_eq, hr]
  rw [← hs]
  rw [← Fintype.prod_bijective f hbij (fun w => ((emb w).1 ((u : 𝓞 E) : E) / ((‖(emb w).1 ((u : 𝓞 E) : E)‖ : ℝ) : ℂ))) (fun v => (v.embedding ((u : 𝓞 E) : E) / ((‖v.embedding ((u : 𝓞 E) : E)‖ : ℝ) : ℂ))) (fun w => by rw [hfac w])]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypeUnitPhaseProdEqOneOfCongruentOneStatement
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmType_unit_phase_prod_eq_one_of_congruent_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsCMField E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (emb : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w) (q : ℕ), q.Prime → 2 < q → ¬ q ∣ Nat.card (Units.torsion E) → ∀ u : (𝓞 E)ˣ, (u : 𝓞 E) - 1 ∈ Ideal.span {((q : ℕ) : 𝓞 E)} → ∏ w : InfinitePlace F, ((emb w).1 ((u : 𝓞 E) : E) / ((‖(emb w).1 ((u : 𝓞 E) : E)‖ : ℝ) : ℂ)) = 1 := by
  first | exact @GlobalTheory.weil_unit_phase_prod | exact GlobalTheory.weil_unit_phase_prod | (intros; apply GlobalTheory.weil_unit_phase_prod <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryHeckeCharacterPhaseTypeCm
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

noncomputable section

namespace GlobalTheory.WeilTypeChar

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem isCMField_of_cmExt {σ : E →ₐ[F] E} (h : IsCMExt F E σ) : IsCMField E := by
  haveI := h.1; haveI := h.2.1
  haveI : Algebra.IsQuadraticExtension F E := { finrank_eq_two' := h.2.2.1 }
  exact IsCMField.ofCMExtension F E

def phase : ℂˣ →* ℂˣ where
  toFun z := Units.mk0 ((z : ℂ) / ((‖(z : ℂ)‖ : ℝ) : ℂ)) (div_ne_zero z.ne_zero (by simp))
  map_one' := by ext; simp
  map_mul' x y := by
    ext
    simp only [Units.val_mul, Units.val_mk0, norm_mul, Complex.ofReal_mul]
    ring

theorem phase_val (z : ℂˣ) : ((phase z : ℂˣ) : ℂ) = (z : ℂ) / ((‖(z : ℂ)‖ : ℝ) : ℂ) := rfl

theorem continuous_phase : Continuous phase := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · show Continuous fun z : ℂˣ => (z : ℂ) / ((‖(z : ℂ)‖ : ℝ) : ℂ)
    exact Units.continuous_val.div (Complex.continuous_ofReal.comp Units.continuous_val.norm) fun z => by simp
  · have : (fun z : ℂˣ => (((phase z)⁻¹ : ℂˣ) : ℂ)) = fun z => ((phase z⁻¹ : ℂˣ) : ℂ) :=
      funext fun z => by rw [map_inv]
    show Continuous fun z : ℂˣ => (((phase z)⁻¹ : ℂˣ) : ℂ)
    rw [this]
    show Continuous fun z : ℂˣ => ((z⁻¹ : ℂˣ) : ℂ) / ((‖((z⁻¹ : ℂˣ) : ℂ)‖ : ℝ) : ℂ)
    exact Units.continuous_coe_inv.div (Complex.continuous_ofReal.comp Units.continuous_coe_inv.norm) fun z => by simp

theorem norm_phase (z : ℂˣ) : ‖((phase z : ℂˣ) : ℂ)‖ = 1 := by
  rw [phase_val, norm_div, Complex.norm_real, norm_norm, div_self (by simp)]

def chiInf (emb : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w) : (AF F ⊗[F] E)ˣ →* ℂˣ :=
  ∏ w, phase.comp (Units.map (piInf (emb w)).toMonoidHom)

theorem chiInf_apply (emb : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w) (z : (AF F ⊗[F] E)ˣ) :
    ((chiInf emb z : ℂˣ) : ℂ) = ∏ w, (piInf (emb w) z / ((‖piInf (emb w) z‖ : ℝ) : ℂ)) := by
  simp [chiInf, phase_val]

theorem continuous_chiInf (emb : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w) : Continuous (chiInf emb) := by
  have e : ⇑(chiInf emb) = fun z => ∏ w, phase (Units.map (piInf (emb w)).toMonoidHom z) :=
    funext fun z => by simp [chiInf]
  rw [e]
  exact continuous_finsetProd _ fun w _ =>
    continuous_phase.comp (Continuous.units_map _ (GlobalTheory.ContMapReal.continuous_piInf (emb w)))

theorem norm_chiInf (emb : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w) (z : (AF F ⊗[F] E)ˣ) :
    ‖((chiInf emb z : ℂˣ) : ℂ)‖ = 1 := by
  simp [chiInf, norm_prod, norm_phase]

theorem exists_weil_char : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∃ ξ : (AF F ⊗[F] E)ˣ →* Circle, IsHeckeCharF ξ ∧ HasExp B.emb ξ (fun _ => 1) := by
  intro F E _ _ _ _ _ σ B hB
  haveI : IsCMField E := isCMField_of_cmExt hB.cm
  haveI : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  obtain ⟨q, hq1, hq⟩ := Nat.exists_infinite_primes (max 3 (Nat.card (Units.torsion E) + 1))
  have hq2 : 2 < q := by omega
  have htq : Nat.card (Units.torsion E) < q := by omega
  have ht : ¬ q ∣ Nat.card (Units.torsion E) := fun h => absurd (Nat.le_of_dvd Nat.card_pos h) (by omega)
  obtain ⟨U, hU, hUinf, hUk⟩ := GlobalTheory.T.exists_open_idele_subgroup_congruence_mod_q F E q hq.ne_zero
  obtain ⟨χ, hχc, hχ1, hχU, hχk⟩ := GlobalTheory.exists_unitary_char_of_open_subgroup_and_hom (AF F ⊗[F] E)ˣ Eˣ U hU
    (Units.map (incAF F E).toMonoidHom) 1 (chiInf B.emb) (continuous_chiInf B.emb) (norm_chiInf B.emb)
    (fun _ => by simp) (fun k hk => by
      obtain ⟨u, hu, hu1⟩ := hUk k hk
      refine Units.ext ?_
      rw [chiInf_apply, MonoidHom.one_apply, Units.val_one]
      have e : ∀ w, piInf (B.emb w) ((Units.map (incAF F E).toMonoidHom k : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) =
          (B.emb w).1 ((u : 𝓞 E) : E) := fun w => by
        rw [hu]
        exact GlobalTheory.ThK.EvAt0.ZPartArc.piInf_inclR' (B.emb w) (k : E)
      simp only [e]
      exact (GlobalTheory.T.cmType_unit_phase_prod_eq_one_of_congruent_one F E σ hB.cm B.emb q hq hq2 ht u hu1).symm)
  refine ⟨GlobalTheory.unitaryCharToCircle χ hχ1, ⟨?_, fun k => ?_⟩, fun z hz => ?_⟩
  · exact Continuous.subtype_mk (Units.continuous_val.comp hχc) _
  · apply Circle.ext
    show ((χ (Units.map (incAF F E).toMonoidHom k) : ℂˣ) : ℂ) = 1
    rw [hχk]; rfl
  · show ((χ z : ℂˣ) : ℂ) = _
    rw [hχU z (hUinf z hz), chiInf_apply]
    simp

end GlobalTheory.WeilTypeChar
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryHeckeCharacterPhaseTypeCmStatement
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitary_heckeCharacter_phase_type_cm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∃ ξ : (AF F ⊗[F] E)ˣ →* Circle, IsHeckeCharF ξ ∧ HasExp B.emb ξ (fun _ => 1) := by
  first | exact @GlobalTheory.WeilTypeChar.exists_weil_char | exact GlobalTheory.WeilTypeChar.exists_weil_char | (intros; apply GlobalTheory.WeilTypeChar.exists_weil_char <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHermitianFormCharPoly
open NumberField IsDedekindDomain Matrix Polynomial Filter Formalism.UG GlobalTheory.BCT
open scoped Classical

noncomputable section

namespace GlobalTheory.EllHermGlobal

variable {E : Type} [Field E]

theorem trace_semilinear {A : Type} [CommRing A] [Algebra E A] {ι : Type} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι E A) (c : E →+* E) (hc : ∀ x, c (c x) = x) (σ : A →+* A) (hσσ : ∀ y, σ (σ y) = y)
    (hσ : ∀ e, σ (algebraMap E A e) = algebraMap E A (c e)) (a : A) :
    Algebra.trace E A (σ a) = c (Algebra.trace E A a) := by
  have hsm : ∀ (e : E) (y : A), σ (e • y) = c e • σ y := by
    intro e y; rw [Algebra.smul_def, Algebra.smul_def, map_mul, hσ]
  let e : A ≃ₗ[E] (ι → E) :=
    { toFun := fun y i => c (b.equivFun (σ y) i)
      map_add' := by intro y z; ext i; simp
      map_smul' := by intro r y; ext i; simp [hsm, hc]
      invFun := fun v => σ (b.equivFun.symm (fun i => c (v i)))
      left_inv := by
        intro y
        simp only [hc]
        show σ (b.equivFun.symm (b.equivFun (σ y))) = y
        rw [LinearEquiv.symm_apply_apply, hσσ]
      right_inv := by
        intro v
        ext i
        simp only [hσσ, LinearEquiv.apply_symm_apply, hc] }
  let b' : Module.Basis ι E A := Module.Basis.ofEquivFun e
  have hrep : ∀ y i, b'.repr y i = c (b.repr (σ y) i) := by
    intro y i
    rw [Module.Basis.ofEquivFun_repr_apply]; rfl
  have hb' : ∀ j, b' j = σ (b j) := by
    intro j
    rw [Module.Basis.coe_ofEquivFun]
    show σ (b.equivFun.symm (fun i => c ((Pi.single j (1 : E) : ι → E) i))) = σ (b j)
    congr 1
    have : (fun i => c ((Pi.single j (1 : E) : ι → E) i)) = (Pi.single j 1 : ι → E) := by
      ext i; by_cases h : i = j
      · subst h; simp
      · simp [h]
    rw [this]; simp [Module.Basis.equivFun_symm_apply, Pi.single_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Algebra.trace_eq_matrix_trace b', Algebra.trace_eq_matrix_trace b, Matrix.trace, Matrix.trace, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Matrix.diag, Algebra.leftMulMatrix_eq_repr_mul, hrep, hb', ← map_mul, hσσ]

end GlobalTheory.EllHermGlobal

noncomputable section

namespace GlobalTheory.EllHermGlobal

variable {E : Type} [Field E] (c : E →+* E) (P : E[X])

def rinv : AdjoinRoot P := AdjoinRoot.mk P (C (-(P.coeff 0)⁻¹) * divX P)

theorem root_mul_rinv (h0 : P.coeff 0 ≠ 0) : AdjoinRoot.root P * rinv P = 1 := by
  have hC : C (-(P.coeff 0)⁻¹) * C (P.coeff 0) = (-1 : E[X]) := by
    rw [← C_mul, neg_mul, inv_mul_cancel₀ h0, C_neg, C_1]
  have h := divX_mul_X_add P
  have key : X * (C (-(P.coeff 0)⁻¹) * divX P) = C (-(P.coeff 0)⁻¹) * P + 1 := by
    linear_combination (C (-(P.coeff 0)⁻¹)) * h - hC
  rw [rinv, ← AdjoinRoot.mk_X, ← map_mul, key, map_add (f := _), map_mul, AdjoinRoot.mk_self, mul_zero, zero_add, map_one]

def sig (h0 : P.coeff 0 ≠ 0) (hr : C (c (P.coeff 0)) * P = (P.map c).reverse) : AdjoinRoot P →+* AdjoinRoot P :=
  AdjoinRoot.lift ((algebraMap E (AdjoinRoot P)).comp c) (rinv P) (by
    letI : Invertible (rinv P) :=
      { invOf := AdjoinRoot.root P
        invOf_mul_self := root_mul_rinv P h0
        mul_invOf_self := by rw [mul_comm]; exact root_mul_rinv P h0 }
    rw [← eval₂_map, ← eval₂_reverse_eq_zero_iff, ← hr]
    have : ⅟(rinv P) = AdjoinRoot.root P := rfl
    rw [this, eval₂_mul, eval₂_C, AdjoinRoot.algebraMap_eq, AdjoinRoot.eval₂_root, mul_zero])

variable {c P}

theorem sig_root (h0 : P.coeff 0 ≠ 0) (hr : C (c (P.coeff 0)) * P = (P.map c).reverse) :
    sig c P h0 hr (AdjoinRoot.root P) = rinv P := AdjoinRoot.lift_root _

theorem sig_alg (h0 : P.coeff 0 ≠ 0) (hr : C (c (P.coeff 0)) * P = (P.map c).reverse) (e : E) :
    sig c P h0 hr (algebraMap E (AdjoinRoot P) e) = algebraMap E (AdjoinRoot P) (c e) := by
  rw [AdjoinRoot.algebraMap_eq]
  exact AdjoinRoot.lift_of _

theorem sig_sig (hc : ∀ x, c (c x) = x) (h0 : P.coeff 0 ≠ 0) (hr : C (c (P.coeff 0)) * P = (P.map c).reverse)
    (y : AdjoinRoot P) : sig c P h0 hr (sig c P h0 hr y) = y := by
  have hinv : sig c P h0 hr (rinv P) = AdjoinRoot.root P := by
    have h1 : sig c P h0 hr (AdjoinRoot.root P) * sig c P h0 hr (rinv P) = 1 := by
      rw [← map_mul, root_mul_rinv P h0, map_one]
    rw [sig_root] at h1
    calc sig c P h0 hr (rinv P) = (AdjoinRoot.root P * rinv P) * sig c P h0 hr (rinv P) := by
          rw [root_mul_rinv P h0, one_mul]
      _ = AdjoinRoot.root P * (rinv P * sig c P h0 hr (rinv P)) := by ring
      _ = AdjoinRoot.root P := by rw [h1, mul_one]
  have hext : (sig c P h0 hr).comp (sig c P h0 hr) = RingHom.id _ := by
    apply Ideal.Quotient.ringHom_ext
    apply Polynomial.ringHom_ext
    · intro e
      have := sig_alg h0 hr e
      rw [AdjoinRoot.algebraMap_eq] at this
      show sig c P h0 hr (sig c P h0 hr (AdjoinRoot.of P e)) = AdjoinRoot.of P e
      rw [this, ← AdjoinRoot.algebraMap_eq, sig_alg, hc]
    · show sig c P h0 hr (sig c P h0 hr (AdjoinRoot.root P)) = AdjoinRoot.root P
      rw [sig_root, hinv]
  exact congrArg (fun f : AdjoinRoot P →+* AdjoinRoot P => f y) hext

theorem sig_root_mul_root (h0 : P.coeff 0 ≠ 0) (hr : C (c (P.coeff 0)) * P = (P.map c).reverse) :
    sig c P h0 hr (AdjoinRoot.root P) * AdjoinRoot.root P = 1 := by
  rw [sig_root, mul_comm, root_mul_rinv P h0]

end GlobalTheory.EllHermGlobal

noncomputable section

namespace GlobalTheory.EllHermGlobal

variable {E : Type} [Field E]

theorem eq_zero_of_isNilpotent {P : E[X]} (hs : Squarefree P) (y : AdjoinRoot P) (hy : IsNilpotent y) : y = 0 := by
  obtain ⟨f, rfl⟩ := AdjoinRoot.mk_surjective y
  obtain ⟨m, hm⟩ := hy
  rw [← map_pow, AdjoinRoot.mk_eq_zero] at hm
  rcases Nat.eq_zero_or_pos m with h | h
  · subst h
    rw [pow_zero] at hm
    have h1 : (AdjoinRoot.mk P 1) = 0 := AdjoinRoot.mk_eq_zero.2 hm
    rw [map_one] at h1
    rw [← mul_one (AdjoinRoot.mk P f), h1, mul_zero]
  · exact AdjoinRoot.mk_eq_zero.2 ((hs.dvd_pow_iff_dvd h.ne').1 hm)

theorem trace_expand {A : Type} [CommRing A] [Algebra E A] {ι : Type} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι E A) (c : E →+* E) (σ : A →+* A)
    (hσ : ∀ e, σ (algebraMap E A e) = algebraMap E A (c e)) (x y : A) :
    Algebra.trace E A (σ x * y) = ∑ k, ∑ l, c (b.repr x k) * Algebra.trace E A (σ (b k) * b l) * b.repr y l := by
  have hsm : ∀ (e : E) (z : A), σ (e • z) = c e • σ z := by
    intro e z; rw [Algebra.smul_def, Algebra.smul_def, map_mul, hσ]
  conv_lhs => rw [← b.sum_repr x, ← b.sum_repr y]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, hsm, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm, map_smul, smul_eq_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

end GlobalTheory.EllHermGlobal

noncomputable section

namespace GlobalTheory.EllHermGlobal

variable {E : Type} [Field E]

theorem exists_herm_of_selfRecip [CharZero E] (c : E →+* E) (hc : ∀ x, c (c x) = x) (P : E[X]) (hP : P.Monic)
    (hsep : P.Separable) (h0 : P.coeff 0 ≠ 0) (hr : C (c (P.coeff 0)) * P = (P.map c).reverse) :
    ∃ M G : Matrix (Fin P.natDegree) (Fin P.natDegree) E, M.charpoly = P ∧ IsUnit G ∧ cT c G = G ∧
      cT c M * G * M = G := by
  let A := AdjoinRoot P
  let pb := AdjoinRoot.powerBasis hP.ne_zero
  haveI : Module.Finite E A := pb.finite
  let b : Module.Basis (Fin P.natDegree) E A :=
    pb.basis.reindex (finCongr (AdjoinRoot.powerBasis_dim hP.ne_zero))
  let σ := sig c P h0 hr
  have hσ := sig_alg (c := c) h0 hr
  let M := Algebra.leftMulMatrix b (AdjoinRoot.root P)
  let G : Matrix (Fin P.natDegree) (Fin P.natDegree) E := fun i j => Algebra.trace E A (σ (b i) * b j)
  have hexp := trace_expand b c σ hσ
  refine ⟨M, G, ?_, ?_, ?_, ?_⟩
  · have h := charpoly_leftMulMatrix pb
    rw [Algebra.leftMulMatrix_apply, LinearMap.charpoly_toMatrix, AdjoinRoot.powerBasis_gen,
      AdjoinRoot.minpoly_root hP.ne_zero, hP.leadingCoeff, inv_one, C_1, mul_one] at h
    show (Algebra.leftMulMatrix b (AdjoinRoot.root P)).charpoly = P
    rw [Algebra.leftMulMatrix_apply, LinearMap.charpoly_toMatrix, h]
  · rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
    intro hdet
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
    let y := b.equivFun.symm v
    have hy : ∀ l, b.repr y l = v l := fun l => by
      rw [← b.equivFun_apply, LinearEquiv.apply_symm_apply]
    have htr : ∀ z : A, Algebra.trace E A (z * y) = 0 := by
      intro z
      rw [← sig_sig hc h0 hr z]
      rw [hexp]
      refine Finset.sum_eq_zero fun k _ => ?_
      simp only [hy, mul_assoc, ← Finset.mul_sum]
      have := congrFun hv k
      simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at this
      rw [this, mul_zero]
    have hnil : IsNilpotent y :=
      GlobalTheory.UnitLemma.TraceNondeg.isNilpotent_of_trace_mul y fun z => by rw [mul_comm]; exact htr z
    have hy0 : y = 0 := eq_zero_of_isNilpotent hsep.squarefree y hnil
    apply hv0
    have : b.equivFun y = v := LinearEquiv.apply_symm_apply _ _
    rw [← this, hy0, map_zero]
  · ext i j
    show c (Algebra.trace E A (σ (b j) * b i)) = Algebra.trace E A (σ (b i) * b j)
    rw [← trace_semilinear b c hc σ (sig_sig hc h0 hr) hσ, map_mul, sig_sig hc h0 hr, mul_comm]
  · ext i j
    simp only [cT, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, M,
      Algebra.leftMulMatrix_eq_repr_mul]
    have hinv : G i j = Algebra.trace E A (σ (AdjoinRoot.root P * b i) * (AdjoinRoot.root P * b j)) := by
      have h1 : σ (AdjoinRoot.root P) * AdjoinRoot.root P = 1 := sig_root_mul_root h0 hr
      have e1 : σ (AdjoinRoot.root P * b i) = σ (AdjoinRoot.root P) * σ (b i) := map_mul σ _ _
      have e2 : σ (AdjoinRoot.root P * b i) * (AdjoinRoot.root P * b j) = σ (b i) * b j := by
        rw [e1]; linear_combination (σ (b i) * b j) * h1
      rw [e2]
    rw [hinv, hexp, Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.sum_mul]

end GlobalTheory.EllHermGlobal

namespace GlobalTheory.EllHermGlobal

theorem exists_charpoly_herm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (P : E[X]), P ∈ Ell E n →
    ∃ M G : Matrix (Fin n) (Fin n) E, M.charpoly = P ∧ IsUnit G ∧
      cT (IsCMField.complexConj E).toRingEquiv.toRingHom G = G ∧
      cT (IsCMField.complexConj E).toRingEquiv.toRingHom M * G * M = G := by
  intro E _ _ _ n P hP
  obtain ⟨h0, hr⟩ := GlobalTheory.ConjSelfRecip.ell_conj_selfRecip E n P hP
  obtain ⟨hm, hdeg, hsep, -⟩ := hP
  subst hdeg
  exact exists_herm_of_selfRecip (IsCMField.complexConj E).toRingEquiv.toRingHom
    (fun x => IsCMField.complexConj_apply_apply (K := E) x) P hm hsep h0 hr

end GlobalTheory.EllHermGlobal
end
end
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousIteratedRealLineDerivUnitaryAdelic
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondKindCoordinatesInfiniteAdelicUnitaryPoints
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondKindCoordinatesInfiniteAdelicUnitaryPoints
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut Filter Topology
open scoped TensorProduct ContDiff

namespace GlobalTheory.InfChartConcat

theorem concat {G X ι : Type*} [Monoid G] (l : Filter X) (P : (ℝ → G) → Prop)
    (d : ι → ℕ) (η : ∀ j, Fin (d j) → ℝ → G) (s : ∀ j, X → Fin (d j) → ℝ)
    (hP : ∀ j i, P (η j i)) (hs : ∀ j, Tendsto (s j) l (𝓝 0)) :
    ∀ L : List ι, ∃ (m : ℕ) (η' : Fin m → ℝ → G) (s' : X → Fin m → ℝ),
      (∀ i, P (η' i)) ∧ Tendsto s' l (𝓝 0) ∧
      ∀ x, (List.ofFn fun i => η' i (s' x i)).prod =
        (L.map fun j => (List.ofFn fun i => η j i (s j x i)).prod).prod := by
  intro L
  induction L with
  | nil => exact ⟨0, Fin.elim0, fun _ => Fin.elim0, fun i => i.elim0,
      tendsto_pi_nhds.2 fun i => i.elim0, fun x => by simp⟩
  | cons j L ih =>
    obtain ⟨m, η', s', hP', hs', he⟩ := ih
    refine ⟨d j + m, Fin.append (η j) η', fun x => Fin.append (s j x) (s' x), ?_, ?_, ?_⟩
    · intro i
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · simpa using hP j i
      · simpa using hP' i
    · rw [tendsto_pi_nhds]
      intro i
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · have := ((continuous_apply i).tendsto _).comp (hs j)
        simpa [Function.comp_def] using this
      · have := ((continuous_apply i).tendsto _).comp hs'
        simpa [Function.comp_def] using this
    · intro x
      have hf : (fun i => Fin.append (η j) η' i (Fin.append (s j x) (s' x) i)) =
          Fin.append (fun i => η j i (s j x i)) (fun i => η' i (s' x i)) := by
        funext i
        refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp
      rw [hf, List.ofFn_fin_append, List.prod_append, he x]
      simp

theorem prod_map_ite_eq {ι M : Type*} [DecidableEq ι] [Monoid M] (u : ι) (a : M) (L : List ι) :
    (L.map fun w => if w = u then a else 1).prod = a ^ L.count u := by
  induction L with
  | nil => simp
  | cons w L ih =>
    simp only [List.map_cons, List.prod_cons, ih, List.count_cons]
    by_cases h : w = u
    · subst h; simp [pow_succ']
    · simp [h]

theorem decomp {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {x : GAd σ J} (hx : x ∈ infPts σ J) :
    x = ((Finset.univ : Finset (InfinitePlace F)).toList.map
      fun w => embArch σ J w (projArch σ J w x)).prod := by
  classical
  apply GAd_ext σ J
  · intro u
    rw [map_list_prod, List.map_map]
    have hf : (projArch σ J u ∘ fun w => embArch σ J w (projArch σ J w x)) =
        fun w => if w = u then projArch σ J u x else 1 := by
      funext w
      by_cases h : w = u
      · subst h; simp
      · simp [h, projArch_embArch_ne σ J (Ne.symm h)]
    rw [hf, prod_map_ite_eq, List.count_eq_one_of_mem (Finset.nodup_toList _)
      (Finset.mem_toList.2 (Finset.mem_univ _)), pow_one]
  · intro v
    rw [map_list_prod, List.map_map, (mem_infPts_iff_forall).1 hx v]
    simp [Function.comp_def]

end GlobalTheory.InfChartConcat

theorem GlobalTheory.infPts_secondKind_chart : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E),
    IsHermND σ J → ∃ (m : ℕ) (η : Fin m → ℝ → GAd σ J) (s : GAd σ J → Fin m → ℝ),
    (∀ i, GlobalTheory.SiegelSet.IsRealLine σ J (η i)) ∧
    Tendsto s (𝓝[(infPts σ J : Set (GAd σ J))] 1) (𝓝 0) ∧
    ∀ᶠ x in 𝓝[(infPts σ J : Set (GAd σ J))] 1, x = (List.ofFn fun i => η i (s x i)).prod := by
  intro F E _ _ _ _ _ σ hCM n J hJ
  classical
  have hp : ∀ w : InfinitePlace F, ∃ (d : ℕ) (η : Fin d → ℝ → GAd σ J)
      (s : GArch σ J w → Fin d → ℝ), (∀ i, GlobalTheory.SiegelSet.IsRealLine σ J (η i)) ∧
      Tendsto s (𝓝 1) (𝓝 0) ∧
      ∀ᶠ y in 𝓝 1, embArch σ J w y = (List.ofFn fun i => η i (s y i)).prod := by
    intro w
    obtain ⟨τ⟩ : Nonempty (EmbOver E w) := inferInstance
    let A : Matrix (Fin n) (Fin n) ℂ := J.map τ.1
    obtain ⟨d, Z, s₀, hZ, hs, hev⟩ := GlobalTheory.T.coordsSecondKind_formPreservingGroup n A
    have hd : IsUnit A.det := by
      rw [show A = J.map τ.1 from rfl, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
      exact (IsUnit.mk0 _ hJ.2).map _
    have hy : ∀ (i : Fin d) (t : ℝ), ∃ y : GArch σ J w,
        GlobalTheory.Orb.archMat σ J τ y = NormedSpace.exp (t • Z i) := by
      intro i t
      obtain ⟨u, hu⟩ := Matrix.isUnit_exp (t • Z i)
      have hskew : (t • Z i)ᴴ * A + A * (t • Z i) = 0 := by
        rw [conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, ← smul_add,
          hZ i, smul_zero]
      have hpres := GlobalTheory.SmoothForms.exp_mem_UH (X := t • Z i) hd hskew
      refine ⟨(archEquiv J hCM τ).symm ⟨u, show _ * _ * _ = _ from hu ▸ hpres⟩, ?_⟩
      rw [GlobalTheory.Orb.archMat_eq_archEquiv J hCM, MulEquiv.apply_symm_apply]
      exact hu
    choose y hy using hy
    have hS (g : GArch σ J w) :
        GlobalTheory.Orb.archMat σ J τ g ∈ {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * A * X = A} := by
      rw [Set.mem_ofPred_eq, GlobalTheory.Orb.archMat_eq_archEquiv J hCM]
      exact (archEquiv J hCM τ g).2
    have hc : Tendsto (GlobalTheory.Orb.archMat σ J τ) (𝓝 1)
        (𝓝[{X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * A * X = A}] 1) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall hS⟩
      simpa using (GlobalTheory.Orb.continuous_archMat σ J τ).tendsto 1
    have hinj : Function.Injective (GlobalTheory.Orb.archMat σ J τ) := fun a b e =>
      (GlobalTheory.Orb.isEmbedding_archMat J hCM τ).injective (by
        show (fun i j => GlobalTheory.Orb.archMat σ J τ a i j) = fun i j =>
          GlobalTheory.Orb.archMat σ J τ b i j
        rw [e])
    refine ⟨d, fun i t => embArch σ J w (y i t), fun g => s₀ (GlobalTheory.Orb.archMat σ J τ g),
      fun i => ⟨w, τ, Z i, hZ i, fun t => ⟨y i t, rfl, hy i t⟩⟩, hs.comp hc, ?_⟩
    filter_upwards [hc.eventually hev] with g hg
    have e : (List.ofFn fun i => embArch σ J w (y i (s₀ (GlobalTheory.Orb.archMat σ J τ g) i))).prod =
        embArch σ J w (List.ofFn fun i => y i (s₀ (GlobalTheory.Orb.archMat σ J τ g) i)).prod := by
      rw [map_list_prod, List.map_ofFn]
      rfl
    rw [e]
    congr 1
    apply hinj
    rw [map_list_prod, List.map_ofFn]
    refine hg.trans (congrArg List.prod ?_)
    exact List.ofFn_inj.2 (funext fun i => (hy i _).symm)
  choose d η s hη hs he using hp
  have hproj : ∀ w, Tendsto (projArch σ J w) (𝓝[(infPts σ J : Set (GAd σ J))] 1) (𝓝 1) := fun w => by
    have := (continuous_projArch σ J w).tendsto 1
    rw [map_one] at this
    exact this.mono_left nhdsWithin_le_nhds
  obtain ⟨m, η', s', hP', hs', heq⟩ := GlobalTheory.InfChartConcat.concat
    (𝓝[(infPts σ J : Set (GAd σ J))] 1) (GlobalTheory.SiegelSet.IsRealLine σ J) d η
    (fun w x => s w (projArch σ J w x)) hη (fun w => (hs w).comp (hproj w))
    (Finset.univ : Finset (InfinitePlace F)).toList
  refine ⟨m, η', s', hP', hs', ?_⟩
  have hev : ∀ᶠ x in 𝓝[(infPts σ J : Set (GAd σ J))] 1, ∀ w, embArch σ J w (projArch σ J w x) =
      (List.ofFn fun i => η w i (s w (projArch σ J w x) i)).prod :=
    Filter.eventually_all.2 fun w => (hproj w).eventually (he w)
  filter_upwards [hev, self_mem_nhdsWithin] with x hx hmem
  rw [heq x, List.map_congr_left (fun w _ => (hx w).symm)]
  exact GlobalTheory.InfChartConcat.decomp σ J hmem
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondKindCoordinatesInfiniteAdelicUnitaryPointsStatement
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut Filter Topology
open scoped TensorProduct ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.secondKindCoordinates_infiniteAdelicUnitaryPoints : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∃ (m : ℕ) (η : Fin m → ℝ → GAd σ J) (s : GAd σ J → Fin m → ℝ), (∀ i, IsRealLine σ J (η i)) ∧ Tendsto s (𝓝[(infPts σ J : Set (GAd σ J))] 1) (𝓝 0) ∧ ∀ᶠ x in 𝓝[(infPts σ J : Set (GAd σ J))] 1, x = (List.ofFn fun i => η i (s x i)).prod := by
  first | exact @GlobalTheory.infPts_secondKind_chart | exact GlobalTheory.infPts_secondKind_chart | (intros; apply GlobalTheory.infPts_secondKind_chart <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousIteratedRealLineDerivUnitaryAdelic
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut Filter Topology
open scoped TensorProduct ContDiff

namespace GlobalTheory.DerCont

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

theorem commute_isRealLine_finPts {γ : ℝ → GAd σ J} (hγ : IsRealLine σ J γ) (t : ℝ) {k : GAd σ J}
    (hk : k ∈ finPts σ J) : Commute (γ t) k := by
  obtain ⟨w, τ, Z, -, hy⟩ := hγ
  obtain ⟨y, e, -⟩ := hy t
  rw [e]; exact commute_embArch σ J y (mem_finPts_iff_forall.1 hk w)

theorem foldr_lineDer_mul_level {φ : GAd σ J → ℂ} {U : Subgroup (GAd σ J)}
    (hφ : ∀ k ∈ U, k ∈ finPts σ J → ∀ g, φ (g * k) = φ g) :
    ∀ l : List (ℝ → GAd σ J), (∀ γ ∈ l, IsRealLine σ J γ) →
      ∀ k ∈ U, k ∈ finPts σ J → ∀ g, l.foldr lineDer φ (g * k) = l.foldr lineDer φ g := by
  intro l
  induction l with
  | nil => intro _ k hk hk' g; exact hφ k hk hk' g
  | cons γ l ih =>
    intro hl k hk hk' g
    have hγ := hl γ List.mem_cons_self
    have ih' := ih (fun δ hδ => hl δ (List.mem_cons_of_mem _ hδ)) k hk hk'
    simp only [List.foldr_cons, lineDer]
    congr 1
    funext t
    rw [mul_assoc, ← (commute_isRealLine_finPts hγ t hk').eq, ← mul_assoc, ih']

theorem eventually_decomp {U : Subgroup (GAd σ J)} (hU : IsOpen (U : Set (GAd σ J))) (g₀ : GAd σ J) :
    Tendsto (fun g => ofInf σ J (projInf σ J (g₀⁻¹ * g))) (𝓝 g₀) (𝓝 1) ∧
    ∀ᶠ g in 𝓝 g₀, ofFin σ J (projFin σ J (g₀⁻¹ * g)) ∈ U ∧ ofFin σ J (projFin σ J (g₀⁻¹ * g)) ∈ finPts σ J := by
  have hc : Tendsto (fun g => g₀⁻¹ * g) (𝓝 g₀) (𝓝 1) := by
    exact Continuous.tendsto' (by fun_prop) g₀ 1 (by simp)
  have h1 : Tendsto (fun h => ofInf σ J (projInf σ J h)) (𝓝 1) (𝓝 1) := by
    exact Continuous.tendsto' ((continuous_ofInf σ J).comp (continuous_projInf σ J)) 1 1 (by simp)
  have h2 : Tendsto (fun h => ofFin σ J (projFin σ J h)) (𝓝 1) (𝓝 1) := by
    exact Continuous.tendsto' ((continuous_ofFin σ J).comp (continuous_projFin σ J)) 1 1 (by simp)
  refine ⟨h1.comp hc, ?_⟩
  filter_upwards [(h2.comp hc).eventually (hU.mem_nhds U.one_mem)] with g hg
  exact ⟨hg, mem_finPts.2 (projInf_ofFin σ J _)⟩

theorem chart (h : IsCMExt F E σ) (hJ : IsHermND σ J) :
    ∃ (m : ℕ) (η : Fin m → ℝ → GAd σ J) (s : GAd σ J → Fin m → ℝ), (∀ i, IsRealLine σ J (η i)) ∧
      Tendsto s (𝓝[(infPts σ J : Set (GAd σ J))] 1) (𝓝 0) ∧
      ∀ᶠ x in 𝓝[(infPts σ J : Set (GAd σ J))] 1, x = (List.ofFn fun i => η i (s x i)).prod :=
  GlobalTheory.T.secondKindCoordinates_infiniteAdelicUnitaryPoints F E σ h n J hJ

theorem continuous_foldr_lineDer : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ φ : GAd σ J → ℂ, (∃ U : Subgroup (GAd σ J), IsOpen (U : Set (GAd σ J)) ∧ ∀ k ∈ U, k ∈ finPts σ J → ∀ g, φ (g * k) = φ g) → Continuous φ → IsSm σ J φ → ∀ l : List (ℝ → GAd σ J), (∀ γ ∈ l, IsRealLine σ J γ) → Continuous (l.foldr lineDer φ) := by
  intro F E _ _ _ _ _ σ h n J hJ φ ⟨U, hU, hlev⟩ _ hsm l hl
  obtain ⟨m, η, s, hη, hs, hP⟩ := chart h hJ
  refine continuous_iff_continuousAt.2 fun g₀ => ?_
  have hH : Continuous fun t : Fin m → ℝ => l.foldr lineDer φ (g₀ * (List.ofFn fun i => η i (t i)).prod) :=
    (GlobalTheory.ThK.RealLineGrowthDerivative.contDiff_foldr_lineDer hsm l hl m η hη g₀).continuous
  have hη0 : ∀ i, η i 0 = 1 := fun i => by
    have e := isRealLine_add F E σ h n J (η i) (hη i) 0 0
    rw [add_zero] at e
    exact left_eq_mul.1 e
  have h0 : (List.ofFn fun i => η i ((0 : Fin m → ℝ) i)).prod = 1 := by
    simp [hη0]
  obtain ⟨hx, hu⟩ := eventually_decomp hU g₀
  have hx' : Tendsto (fun g => ofInf σ J (projInf σ J (g₀⁻¹ * g))) (𝓝 g₀) (𝓝[(infPts σ J : Set (GAd σ J))] 1) :=
    tendsto_nhdsWithin_iff.2 ⟨hx, Eventually.of_forall fun g => mem_infPts.2 (projFin_ofInf σ J _)⟩
  have key : ∀ᶠ g in 𝓝 g₀, l.foldr lineDer φ (g₀ * (List.ofFn fun i =>
      η i (s (ofInf σ J (projInf σ J (g₀⁻¹ * g))) i)).prod) = l.foldr lineDer φ g := by
    filter_upwards [hu, hx'.eventually hP] with g hu' hP'
    rw [← hP']
    have e : g = g₀ * ofInf σ J (projInf σ J (g₀⁻¹ * g)) * ofFin σ J (projFin σ J (g₀⁻¹ * g)) := by
      rw [mul_assoc, ofInf_projInf_mul_ofFin_projFin, mul_inv_cancel_left]
    conv_rhs => rw [e]
    exact (foldr_lineDer_mul_level hlev l hl _ hu'.1 hu'.2 _).symm
  have lim := (hH.tendsto 0).comp (hs.comp hx')
  rw [h0, mul_one] at lim
  exact lim.congr' key

end GlobalTheory.DerCont
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousIteratedRealLineDerivUnitaryAdelicStatement
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_iteratedRealLineDeriv_unitaryAdelic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ φ : GAd σ J → ℂ, (∃ U : Subgroup (GAd σ J), IsOpen (U : Set (GAd σ J)) ∧ ∀ k ∈ U, k ∈ finPts σ J → ∀ g, φ (g * k) = φ g) → Continuous φ → IsSm σ J φ → ∀ l : List (ℝ → GAd σ J), (∀ γ ∈ l, IsRealLine σ J γ) → Continuous (l.foldr lineDer φ) := by
  first | exact @GlobalTheory.DerCont.continuous_foldr_lineDer | exact GlobalTheory.DerCont.continuous_foldr_lineDer | (intros; apply GlobalTheory.DerCont.continuous_foldr_lineDer <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActOOneOne
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.DblBox

open Formalism.IndefR.Datum

variable {D : D7} {S T : HSp D}

def top (w : WO S (GlobalTheory.Doubling.dblSp T)) : WO S T := w.submatrix (finSumFinEquiv ∘ Sum.inl) id

def bot (w : WO S (GlobalTheory.Doubling.dblSp T)) : WO S T := w.submatrix (finSumFinEquiv ∘ Sum.inr) id

def join (u v : WO S T) : WO S (GlobalTheory.Doubling.dblSp T) := (Matrix.fromRows u v).submatrix finSumFinEquiv.symm id

@[simp] theorem top_join (u v : WO S T) : top (join u v) = u := by
  ext i j
  simp only [top, join, Matrix.submatrix_apply, Function.comp_apply, Equiv.symm_apply_apply, Matrix.fromRows_apply_inl, id]

@[simp] theorem bot_join (u v : WO S T) : bot (join u v) = v := by
  ext i j
  simp only [bot, join, Matrix.submatrix_apply, Function.comp_apply, Equiv.symm_apply_apply, Matrix.fromRows_apply_inr, id]

theorem join_top_bot (w : WO S (GlobalTheory.Doubling.dblSp T)) : join (top w) (bot w) = w := by
  ext i j
  obtain ⟨k | k, rfl⟩ := finSumFinEquiv.surjective i <;>
    simp only [top, bot, join, Matrix.submatrix_apply, Function.comp_apply, Equiv.symm_apply_apply,
      Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, id]

@[simp] theorem top_add (x y : WO S (GlobalTheory.Doubling.dblSp T)) : top (x + y) = top x + top y := rfl
@[simp] theorem bot_add (x y : WO S (GlobalTheory.Doubling.dblSp T)) : bot (x + y) = bot x + bot y := rfl

def box (f₁ f₂ : WO S T → ℂ) : WO S (GlobalTheory.Doubling.dblSp T) → ℂ := fun w => f₁ (top w) * star (f₂ (bot w))

theorem hO_dbl (x y : WO S (GlobalTheory.Doubling.dblSp T)) :
    hO S (GlobalTheory.Doubling.dblSp T) x y = hO S T (top x) (top y) - hO S T (bot x) (bot y) := by
  simp only [hO, GlobalTheory.Doubling.gram_hdbl, GlobalTheory.Doubling.dblGram, GlobalTheory.Doubling.blkMat]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type]
  simp only [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type, Matrix.submatrix_apply, Equiv.symm_apply_apply,
    Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
    Matrix.zero_apply, Matrix.neg_apply, map_zero, map_neg, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, zero_add,
    top, bot, Function.comp_apply, id]
  simp only [neg_mul, mul_neg, Finset.sum_neg_distrib, sub_eq_add_neg]

theorem symplO_dbl (x y : WO S (GlobalTheory.Doubling.dblSp T)) :
    symplO S (GlobalTheory.Doubling.dblSp T) x y = symplO S T (top x) (top y) - symplO S T (bot x) (bot y) := by
  simp only [symplO, hO_dbl, mul_sub, map_sub]

theorem symplOH_dbl (x y : WO S (GlobalTheory.Doubling.dblSp T)) :
    symplOH S (GlobalTheory.Doubling.dblSp T) x y = symplOH S T (top x) (top y) - symplOH S T (bot x) (bot y) := by
  simp only [symplOH, symplO_dbl, mul_sub]

def IsTopDiag (h : GA D T) (hd : GA D (GlobalTheory.Doubling.dblSp T)) : Prop :=
  Formalism.L2.Theta.mt (GlobalTheory.Doubling.dblSp T) hd =
    Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks (Formalism.L2.Theta.mt T h) 0 0 1)

theorem top_actO {h : GA D T} {hd : GA D (GlobalTheory.Doubling.dblSp T)} (hh : IsTopDiag h hd) (g : GA D S)
    (w : WO S (GlobalTheory.Doubling.dblSp T)) : top (actO S (GlobalTheory.Doubling.dblSp T) g hd w) = actO S T g h (top w) := by
  ext i j
  simp only [top, actO, IsTopDiag] at hh ⊢
  rw [hh]
  simp only [Matrix.submatrix_apply, Function.comp_apply, id, Matrix.mul_apply, Matrix.reindex_apply,
    ← finSumFinEquiv.sum_comp, Fintype.sum_sum_type, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₁,
    Matrix.fromBlocks_apply₁₂, Matrix.zero_apply, zero_mul, Finset.sum_const_zero, add_zero]

theorem bot_actO {h : GA D T} {hd : GA D (GlobalTheory.Doubling.dblSp T)} (hh : IsTopDiag h hd) (g : GA D S)
    (w : WO S (GlobalTheory.Doubling.dblSp T)) : bot (actO S (GlobalTheory.Doubling.dblSp T) g hd w) = actO S T g 1 (bot w) := by
  ext i j
  simp only [bot, actO, IsTopDiag] at hh ⊢
  rw [hh]
  simp only [Matrix.submatrix_apply, Function.comp_apply, id, Matrix.mul_apply, Matrix.reindex_apply,
    ← finSumFinEquiv.sum_comp, Fintype.sum_sum_type, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₂₁,
    Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, zero_mul, Finset.sum_const_zero, zero_add]
  rw [show Formalism.L2.Theta.mt T 1 = 1 from rfl]

theorem actO_one_one (w : WO S T) : actO S T 1 1 w = w := by
  simp only [actO, inv_one, show Formalism.L2.Theta.mt T 1 = 1 from rfl, show Formalism.L2.Theta.mt S 1 = 1 from rfl,
    Matrix.one_mul, Matrix.mul_one]

theorem psi_neg {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (b : AF D.host.F) : ψ (-b) = star (ψ b) := by
  have h1 : ψ (-b) * ψ b = 1 := by rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
  have h2 := GlobalTheory.ThetaSchur.mul_star_psi hψ b
  linear_combination (-ψ (-b)) * h2 + star (ψ b) * h1

theorem heisO_box {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (w : WO S (GlobalTheory.Doubling.dblSp T))
    (f₁ f₂ : WO S T → ℂ) :
    heisO ψ S (GlobalTheory.Doubling.dblSp T) w (box f₁ f₂) = box (heisO ψ S T (top w) f₁) (heisO ψ S T (bot w) f₂) := by
  funext x
  simp only [heisO, box, symplOH_dbl, top_add, bot_add, sub_eq_add_neg, AddChar.map_add_eq_mul, psi_neg hψ, star_mul']
  ring

end GlobalTheory.DblBox
end
end
