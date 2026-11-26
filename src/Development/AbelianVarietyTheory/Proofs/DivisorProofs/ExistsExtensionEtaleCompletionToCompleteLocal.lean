module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasseNormTheoremQuadraticExtension

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExtensionEtaleCompletionToCompleteLocal
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExtensionEtaleCompletionToCompleteLocal
open IsLocalRing GlobalTheory.Toroidal

namespace GlobalTheory.EtaleCompletionLift

section Etale

variable {O S : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [CommRing S] [IsLocalRing S]
  [IsNoetherianRing S] [Algebra O S]


omit [IsNoetherianRing O] in
theorem finite_quotient (hm : (maximalIdeal O).map (algebraMap O S) = maximalIdeal S)
    [Module.Finite O (S ⧸ maximalIdeal S)] (n : ℕ) :
    Module.Finite O (S ⧸ (maximalIdeal O ^ (n + 1)).map (algebraMap O S)) := by
  rw [Ideal.map_pow, hm]
  have hle : maximalIdeal S ^ (n + 1) ≤ maximalIdeal S := Ideal.pow_le_self n.succ_ne_zero
  refine Module.finite_of_surjective_of_ker_le_nilradical (Ideal.Quotient.factorₐ O hle)
    (Ideal.Quotient.factor_surjective hle) ?_ (IsNoetherian.noetherian _)
  intro x hx
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hx' : x ∈ maximalIdeal S := Ideal.Quotient.eq_zero_iff_mem.1 hx
  exact mem_nilradical.2 ⟨n + 1, by rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]; exact Ideal.pow_mem_pow hx' _⟩


omit [IsNoetherianRing O] in
theorem formallyUnramified_quotient (hm : (maximalIdeal O).map (algebraMap O S) = maximalIdeal S)
    [Module.Finite O (S ⧸ maximalIdeal S)] [Algebra.FormallyUnramified O (S ⧸ maximalIdeal S)] (n : ℕ) :
    Algebra.FormallyUnramified O (S ⧸ (maximalIdeal O ^ (n + 1)).map (algebraMap O S)) := by
  have := finite_quotient hm n
  set J := (maximalIdeal O ^ (n + 1)).map (algebraMap O S) with hJ
  have hle : J ≤ maximalIdeal S := by
    rw [hJ, Ideal.map_pow, hm]; exact Ideal.pow_le_self n.succ_ne_zero
  have : Nontrivial (S ⧸ J) :=
    Ideal.Quotient.nontrivial_iff.mpr <| ne_top_of_le_ne_top (maximalIdeal.isMaximal S).ne_top hle
  have : IsLocalRing (S ⧸ J) := .of_surjective' _ Ideal.Quotient.mk_surjective
  have hmk : IsLocalHom (Ideal.Quotient.mk J) := IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  have hmap : (maximalIdeal S).map (Ideal.Quotient.mk J) = maximalIdeal (S ⧸ J) :=
    IsLocalRing.map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective
  have H : (maximalIdeal O).map (algebraMap O (S ⧸ J)) = maximalIdeal (S ⧸ J) := by
    rw [← hmap, ← hm, Ideal.map_map]; rfl
  have : IsLocalHom (algebraMap O (S ⧸ J)) :=
    ((local_hom_tfae (algebraMap O (S ⧸ J))).out 3 1 rfl rfl).mp H.le
  let g : (S ⧸ maximalIdeal S) →ₐ[O] ResidueField (S ⧸ J) :=
    Ideal.Quotient.liftₐ _ ((IsScalarTower.toAlgHom O (S ⧸ J) (ResidueField (S ⧸ J))).comp (Ideal.Quotient.mkₐ O J))
      fun a ha => by
        change residue (S ⧸ J) (Ideal.Quotient.mk J a) = 0
        rw [residue_eq_zero_iff, ← hmap]
        exact Ideal.mem_map_of_mem _ ha
  have hg : Function.Surjective g := by
    intro x
    obtain ⟨x, rfl⟩ := residue_surjective x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨Ideal.Quotient.mk _ x, rfl⟩
  have : Algebra.FormallyUnramified O (ResidueField (S ⧸ J)) := .of_surjective g hg
  have : Algebra.FormallyUnramified (ResidueField O) (ResidueField (S ⧸ J)) := .of_restrictScalars O _ _
  have : Module.Finite O (ResidueField (S ⧸ J)) := .of_surjective g.toLinearMap hg
  have : Module.Finite (ResidueField O) (ResidueField (S ⧸ J)) := .of_restrictScalars_finite O _ _
  have : Algebra.IsSeparable (ResidueField O) (ResidueField (S ⧸ J)) := Algebra.FormallyUnramified.isSeparable _ _
  exact Algebra.FormallyUnramified.of_map_maximalIdeal H

theorem etale_quotient (hm : (maximalIdeal O).map (algebraMap O S) = maximalIdeal S) [Module.Flat O S]
    [Module.Finite O (S ⧸ maximalIdeal S)] [Algebra.FormallyUnramified O (S ⧸ maximalIdeal S)] (n : ℕ) :
    Algebra.Etale (O ⧸ maximalIdeal O ^ (n + 1)) (S ⧸ (maximalIdeal O ^ (n + 1)).map (algebraMap O S)) := by
  have := finite_quotient hm n
  have := formallyUnramified_quotient hm n
  set I := maximalIdeal O ^ (n + 1)
  have : Module.Finite (O ⧸ I) (S ⧸ I.map (algebraMap O S)) := .of_restrictScalars_finite O _ _
  have : Algebra.FormallyUnramified (O ⧸ I) (S ⧸ I.map (algebraMap O S)) := .of_restrictScalars O _ _
  have : Algebra.FinitePresentation (O ⧸ I) (S ⧸ I.map (algebraMap O S)) :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have : Module.Flat (O ⧸ I) (S ⧸ I.map (algebraMap O S)) :=
    .of_linearEquiv (Algebra.TensorProduct.quotIdealMapEquivQuotTensor S I).toLinearEquiv
  exact .of_formallyUnramified_of_flat

theorem existsUnique_lift (hm : (maximalIdeal O).map (algebraMap O S) = maximalIdeal S) [Module.Flat O S]
    [Module.Finite O (S ⧸ maximalIdeal S)] [Algebra.FormallyUnramified O (S ⧸ maximalIdeal S)] (n : ℕ)
    {B : Type} [CommRing B] (χ : O →+* B) (hχ : ∀ x ∈ maximalIdeal O ^ (n + 1), χ x = 0) (K : Ideal B)
    (hK : IsNilpotent K) (g : S →+* B ⧸ K) (hg : g.comp (algebraMap O S) = (Ideal.Quotient.mk K).comp χ) :
    ∃! F : S →+* B, F.comp (algebraMap O S) = χ ∧ (Ideal.Quotient.mk K).comp F = g := by
  have := etale_quotient hm n
  set I := maximalIdeal O ^ (n + 1)
  letI : Algebra (O ⧸ I) B := (Ideal.Quotient.lift I χ hχ).toAlgebra
  have desc : ∀ {C : Type} [CommRing C] [Algebra (O ⧸ I) C] (f : S →+* C),
      (∀ x, f (algebraMap O S x) = algebraMap (O ⧸ I) C (Ideal.Quotient.mk I x)) →
      ∃ f' : (S ⧸ I.map (algebraMap O S)) →ₐ[O ⧸ I] C, ∀ x, f' (Ideal.Quotient.mk _ x) = f x := by
    intro C _ _ f hf
    have h0 : I.map (algebraMap O S) ≤ RingHom.ker f := by
      rw [Ideal.map_le_iff_le_comap]
      intro x hx
      change f (algebraMap O S x) = 0
      rw [hf, Ideal.Quotient.eq_zero_iff_mem.2 hx, map_zero]
    refine ⟨⟨Ideal.Quotient.lift _ f fun a ha => h0 ha, fun r => ?_⟩, fun x => rfl⟩
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
    exact hf r
  obtain ⟨g', hg'⟩ := desc g fun x => congr($hg x)
  let F := Algebra.FormallySmooth.lift K hK g'
  refine ⟨F.toRingHom.comp (Ideal.Quotient.mk _), ⟨RingHom.ext fun x => ?_, RingHom.ext fun x => ?_⟩, ?_⟩
  · exact F.commutes (Ideal.Quotient.mk I x)
  · exact (Algebra.FormallySmooth.mk_lift K hK g' _).trans (hg' x)
  · rintro G ⟨h1, h2⟩
    obtain ⟨G', hG'⟩ := desc G fun x => congr($h1 x)
    have : G' = F := Algebra.FormallyUnramified.ext K hK fun x => by
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      rw [Algebra.FormallySmooth.mk_lift K hK g', hg', hG']
      exact congr($h2 x)
    ext x
    rw [← hG', this]
    rfl

theorem existsUnique_lift_of_surjective (hm : (maximalIdeal O).map (algebraMap O S) = maximalIdeal S)
    [Module.Flat O S] [Module.Finite O (S ⧸ maximalIdeal S)] [Algebra.FormallyUnramified O (S ⧸ maximalIdeal S)]
    (n : ℕ) {B C : Type} [CommRing B] [CommRing C] (χ : O →+* B) (hχ : ∀ x ∈ maximalIdeal O ^ (n + 1), χ x = 0)
    (w : B →+* C) (hw : Function.Surjective w) (hK : IsNilpotent (RingHom.ker w)) (g : S →+* C)
    (hg : g.comp (algebraMap O S) = w.comp χ) :
    ∃! F : S →+* B, F.comp (algebraMap O S) = χ ∧ w.comp F = g := by
  let e := RingHom.quotientKerEquivOfSurjective hw
  have := existsUnique_lift hm n χ hχ _ hK (e.symm.toRingHom.comp g) (by
    ext x
    exact e.symm_apply_eq.2 congr($hg x))
  refine (existsUnique_congr fun F => and_congr Iff.rfl ?_).1 this
  simp only [RingHom.ext_iff]
  exact forall_congr' fun x => e.eq_symm_apply

end Etale

theorem existsUnique_lift_of_isEtaleCompletion {O S : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [CommRing S] [IsLocalRing S] [IsNoetherianRing S] {φ : O →+* S} (h : IsEtaleCompletion φ)
    (hun : ((residue S).comp φ).FormallyUnramified)
    (n : ℕ) {B C : Type} [CommRing B] [CommRing C] (χ : O →+* B) (hχ : ∀ x ∈ maximalIdeal O ^ (n + 1), χ x = 0)
    (w : B →+* C) (hw : Function.Surjective w) (hK : IsNilpotent (RingHom.ker w)) (g : S →+* C)
    (hg : g.comp φ = w.comp χ) :
    ∃! F : S →+* B, F.comp φ = χ ∧ w.comp F = g := by
  obtain ⟨hfl, hm, hfin⟩ := h
  letI := φ.toAlgebra
  have : Module.Flat O S := hfl
  have : Module.Finite O (S ⧸ maximalIdeal S) := RingHom.finite_algebraMap.1 hfin
  have : Algebra.FormallyUnramified O (S ⧸ maximalIdeal S) := RingHom.formallyUnramified_algebraMap.1 hun
  exact existsUnique_lift_of_surjective hm n χ hχ w hw hK g hg

theorem isNilpotent_ker {E C : Type} [CommRing E] [CommRing C] {I : Ideal E} {v : E →+* C} (hv : RingHom.ker v = I)
    (n : ℕ) (w : E ⧸ I ^ (n + 1) →+* C) (hw : ∀ x, w (Ideal.Quotient.mk _ x) = v x) :
    IsNilpotent (RingHom.ker w) := by
  have : RingHom.ker w ≤ I.map (Ideal.Quotient.mk (I ^ (n + 1))) := fun x hx => by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    refine Ideal.mem_map_of_mem _ ?_
    rw [← hv, RingHom.mem_ker, ← hw]
    exact hx
  refine ⟨n + 1, le_bot_iff.1 ((Ideal.pow_right_mono this _).trans ?_)⟩
  rw [← Ideal.map_pow, Ideal.map_quotient_self]

theorem exists_extension_of_surjective {O S : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [CommRing S] [IsLocalRing S] [IsNoetherianRing S] {φ : O →+* S} (het : IsEtaleCompletion φ)
    (hun : ((residue S).comp φ).FormallyUnramified) {E C : Type} [CommRing E] [CommRing C] (m : Ideal E)
    [IsAdicComplete m E] (ψ : O →+* E) (h1 : (maximalIdeal O).map ψ ≤ m) (v : E →+* C) (hs : Function.Surjective v)
    (hv : RingHom.ker v = m) (u : S →+* C) (hc : u.comp φ = v.comp ψ) :
    ∃ b : S →+* E, b.comp φ = ψ ∧ v.comp b = u := by
  have hle : ∀ n : ℕ, m ^ (n + 1) ≤ RingHom.ker v := fun n => (Ideal.pow_le_self n.succ_ne_zero).trans hv.ge
  obtain ⟨w, hw⟩ : ∃ w : ∀ n : ℕ, E ⧸ m ^ (n + 1) →+* C, ∀ n x, w n (Ideal.Quotient.mk _ x) = v x :=
    ⟨fun n => Ideal.Quotient.lift _ v fun a ha => hle n ha, fun n x => Ideal.Quotient.lift_mk _ _ _⟩
  have hws : ∀ n, Function.Surjective (w n) := fun n y => by
    obtain ⟨x, rfl⟩ := hs y
    exact ⟨_, hw n x⟩
  have key : ∀ n, ∃! F : S →+* E ⧸ m ^ (n + 1),
      F.comp φ = (Ideal.Quotient.mk _).comp ψ ∧ (w n).comp F = u := fun n => by
    refine existsUnique_lift_of_isEtaleCompletion het hun n _ (fun x hx => ?_) _ (hws n)
      (isNilpotent_ker hv n _ (hw n)) _ ?_
    · rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
      refine Ideal.pow_right_mono h1 _ ?_
      rw [← Ideal.map_pow]
      exact Ideal.mem_map_of_mem _ hx
    · ext x
      rw [hc, RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply, hw]
  choose F hF hU using key
  have hF1 : ∀ n x, F n (φ x) = Ideal.Quotient.mk _ (ψ x) := fun n x => RingHom.congr_fun (hF n).1 x
  have hF2 : ∀ n x, w n (F n x) = u x := fun n x => RingHom.congr_fun (hF n).2 x
  have ha : StrictMono (fun n : ℕ => n + 1) := strictMono_id.add_const 1
  have hcomp : ∀ {k : ℕ}, (Ideal.Quotient.factorPow m (ha.monotone k.le_succ)).comp (F (k + 1)) = F k := by
    intro k
    refine hU k _ ⟨RingHom.ext fun x => ?_, RingHom.ext fun x => ?_⟩
    · simp only [RingHom.comp_apply, hF1, Ideal.Quotient.factor_mk]
    · rw [← hF2 (k + 1), RingHom.comp_apply, RingHom.comp_apply]
      obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (F (k + 1) x)
      rw [← hy, hw]
      exact (congrArg (w k) (Ideal.Quotient.factor_mk _ y)).trans (hw k y)
  obtain ⟨b, hb⟩ : ∃ b : S →+* E, ∀ n x, Ideal.Quotient.mk (m ^ (n + 1)) (b x) = F n x :=
    ⟨_, fun n x => IsAdicComplete.StrictMono.mk_liftRingHom m ha F hcomp x⟩
  refine ⟨b, ?_, ?_⟩
  · apply DFunLike.coe_injective
    apply IsHausdorff.StrictMono.funext' m ha
    intro n x
    exact (hb n _).trans (hF1 n x)
  · ext x
    rw [RingHom.comp_apply, ← hw 0, hb, hF2]

theorem exists_extension : ∀ (O R' E Ω : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [CommRing R']
    [IsLocalRing R'] [IsNoetherianRing R'] [CommRing E] [IsLocalRing E] [Field Ω] (φ' : O →+* R') (ψ : O →+* E)
    (u' : R' →+* Ω) (v : E →+* Ω), IsEtaleCompletion φ' → ((residue R').comp φ').FormallyUnramified →
    IsAdicComplete (maximalIdeal E) E → IsLocalHom ψ → RingHom.ker u' = maximalIdeal R' →
    RingHom.ker v = maximalIdeal E → v.comp ψ = u'.comp φ' → (∀ r : R', u' r ∈ v.range) →
    ∃ b : R' →+* E, b.comp φ' = ψ ∧ v.comp b = u' := by
  intro O R' E Ω _ _ _ _ _ _ _ _ _ φ' ψ u' v het hun hE hψ _ hv hc hr
  obtain ⟨b, h1, h2⟩ := exists_extension_of_surjective het hun (maximalIdeal E) ψ
    (((local_hom_tfae ψ).out 1 3 rfl rfl).mp hψ) v.rangeRestrict v.rangeRestrict_surjective
    (v.ker_rangeRestrict.trans hv) (u'.codRestrict v.range hr)
    (RingHom.ext fun x => Subtype.ext (RingHom.congr_fun hc x).symm)
  exact ⟨b, h1, RingHom.ext fun x => congrArg Subtype.val (RingHom.congr_fun h2 x)⟩

end GlobalTheory.EtaleCompletionLift
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExtensionEtaleCompletionToCompleteLocalStatement
open IsLocalRing GlobalTheory.Toroidal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_extension_etaleCompletion_to_complete_local : ∀ (O R' E Ω : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [CommRing R'] [IsLocalRing R'] [IsNoetherianRing R'] [CommRing E] [IsLocalRing E] [Field Ω] (φ' : O →+* R') (ψ : O →+* E) (u' : R' →+* Ω) (v : E →+* Ω), IsEtaleCompletion φ' → ((residue R').comp φ').FormallyUnramified → IsAdicComplete (maximalIdeal E) E → IsLocalHom ψ → RingHom.ker u' = maximalIdeal R' → RingHom.ker v = maximalIdeal E → v.comp ψ = u'.comp φ' → (∀ r : R', u' r ∈ v.range) → ∃ b : R' →+* E, b.comp φ' = ψ ∧ v.comp b = u' := by
  first | exact @GlobalTheory.EtaleCompletionLift.exists_extension | exact GlobalTheory.EtaleCompletionLift.exists_extension | (intros; apply GlobalTheory.EtaleCompletionLift.exists_extension <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalPureQuaternionSqOfAdelic
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalPureQuaternionSqOfAdelic
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct

namespace GlobalTheory.QSA.PureSq

theorem mul_self_of_re_eq_zero {R : Type*} [CommRing R] {a b : R} (p : ℍ[R, a, b]) (hp : p.re = 0) :
    p * p = algebraMap R ℍ[R, a, b] (a * p.imI ^ 2 + b * p.imJ ^ 2 - a * b * p.imK ^ 2) := by
  ext <;> simp [QuaternionAlgebra.algebraMap_eq, hp] <;> ring

theorem exists_completion_hom_of_real {K : Type} [Field K] (σ : K →+* ℝ) :
    ∃ (w : InfinitePlace K) (f : w.Completion →+* ℝ), ∀ x : K, f (algebraMap K w.Completion x) = σ x := by
  have hφ : ComplexEmbedding.IsReal (Complex.ofRealHom.comp σ) := by
    rw [ComplexEmbedding.isReal_iff]
    ext x
    simp
  have hw : (InfinitePlace.mk (Complex.ofRealHom.comp σ)).IsReal := InfinitePlace.isReal_mk_iff.2 hφ
  refine ⟨_, InfinitePlace.Completion.extensionEmbeddingOfIsReal hw, fun x => ?_⟩
  have he := InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe hw
    ((WithAbs.equiv _).symm x)
  rw [AbsoluteValue.Completion.algebraMap_def, WithAbs.algebraMap_right_apply,
    Algebra.algebraMap_self_apply]
  refine Eq.trans he ?_
  apply Complex.ofReal_injective
  rw [InfinitePlace.embedding_of_isReal_apply, InfinitePlace.embedding_mk_eq_of_isReal hφ]
  simp

variable {F : Type} [Field F] [NumberField F]

theorem isotropic_of_ringHom {a b c : F} (q : DA F a b) (hq0 : q.re = 0)
    (hqq : q * q = algebraMap (AF F) (DA F a b) (algebraMap F (AF F) c))
    {k : Type*} [Field k] (φ : AF F →+* k) (ψ : F →+* k)
    (hφ : ∀ x, φ (algebraMap F (AF F) x) = ψ x) :
    ∃ x : Fin 4 → k, x ≠ 0 ∧ ∑ i, ψ (![a, b, -(a * b), -c] i) * x i ^ 2 = 0 := by
  rw [mul_self_of_re_eq_zero q hq0] at hqq
  have h1 := congrArg QuaternionAlgebra.re hqq
  simp only [QuaternionAlgebra.algebraMap_eq, QuaternionAlgebra.re_coe] at h1
  have h2 := congrArg φ h1
  simp only [map_add (f := _), map_sub, map_mul, map_pow, hφ] at h2
  refine ⟨![φ q.imI, φ q.imJ, φ q.imK, 1], fun h => by simpa using congrFun h 3, ?_⟩
  simp [Fin.sum_univ_four]
  linear_combination h2

end GlobalTheory.QSA.PureSq

namespace GlobalTheory.QSA.PureSq

variable {F : Type} [Field F] [NumberField F]

theorem isotropic_real {a b c : F} (q : DA F a b) (hq0 : q.re = 0)
    (hqq : q * q = algebraMap (AF F) (DA F a b) (algebraMap F (AF F) c)) (σ : F →+* ℝ) :
    ∃ x : Fin 4 → ℝ, x ≠ 0 ∧ ∑ i, σ (![a, b, -(a * b), -c] i) * x i ^ 2 = 0 := by
  obtain ⟨w, f, hf⟩ := exists_completion_hom_of_real σ
  refine isotropic_of_ringHom q hq0 hqq
    (f.comp ((Pi.evalRingHom (fun v : InfinitePlace F => v.Completion) w).comp (fstA F).toRingHom)) σ
    (fun x => ?_)
  rw [← hf x]
  rfl

theorem isotropic_finite {a b c : F} (q : DA F a b) (hq0 : q.re = 0)
    (hqq : q * q = algebraMap (AF F) (DA F a b) (algebraMap F (AF F) c)) (v : HeightOneSpectrum (𝓞 F)) :
    ∃ x : Fin 4 → v.adicCompletion F, x ≠ 0 ∧
      ∑ i, algebraMap F (v.adicCompletion F) (![a, b, -(a * b), -c] i) * x i ^ 2 = 0 :=
  isotropic_of_ringHom q hq0 hqq ((evalV F v).comp (sndA F)).toRingHom (algebraMap F _)
    (fun x => ((evalV F v).comp (sndA F)).commutes x)

theorem exists_ternary_eq {a b : F} (ha : a ≠ 0) (hb : b ≠ 0) {u₁ u₂ u₃ : F}
    (hu : (u₁, u₂, u₃) ≠ (0, 0, 0)) (h : a * u₁ ^ 2 + b * u₂ ^ 2 - a * b * u₃ ^ 2 = 0) (c : F) :
    ∃ y₁ y₂ y₃ : F, a * y₁ ^ 2 + b * y₂ ^ 2 - a * b * y₃ ^ 2 = c := by
  have key : ∀ v₁ v₂ v₃ : F, a * u₁ * v₁ + b * u₂ * v₂ - a * b * u₃ * v₃ ≠ 0 →
      ∃ y₁ y₂ y₃ : F, a * y₁ ^ 2 + b * y₂ ^ 2 - a * b * y₃ ^ 2 = c := by
    intro v₁ v₂ v₃ hD
    set D := a * u₁ * v₁ + b * u₂ * v₂ - a * b * u₃ * v₃ with hDdef
    set t := (c - (a * v₁ ^ 2 + b * v₂ ^ 2 - a * b * v₃ ^ 2)) / (2 * D) with ht
    have h2 : (2 : F) * D ≠ 0 := mul_ne_zero two_ne_zero hD
    have ht' : t * (2 * D) = c - (a * v₁ ^ 2 + b * v₂ ^ 2 - a * b * v₃ ^ 2) := div_mul_cancel₀ _ h2
    refine ⟨t * u₁ + v₁, t * u₂ + v₂, t * u₃ + v₃, ?_⟩
    linear_combination t ^ 2 * h + ht'
  by_cases h1 : u₁ = 0
  · by_cases h2 : u₂ = 0
    · have h3 : u₃ ≠ 0 := fun h3 => hu (by simp [h1, h2, h3])
      exact key 0 0 1 (by simp [ha, hb, h3])
    · exact key 0 1 0 (by simp [hb, h2, h1])
  · exact key 1 0 0 (by simp [ha, h1])

theorem exists_rat_of_adelic : ∀ (F : Type) [Field F] [NumberField F] (a b : F), a ≠ 0 → b ≠ 0 → ∀ c : F, c ≠ 0 →
    ∀ q : DA F a b, q.re = 0 → q * q = algebraMap (AF F) (DA F a b) (algebraMap F (AF F) c) →
    ∃ p : ℍ[F, a, b], p.re = 0 ∧ p * p = algebraMap F ℍ[F, a, b] c := by
  intro F _ _ a b ha hb c hc q hq0 hqq
  obtain ⟨x, hx0, hx⟩ := GlobalTheory.LocalQuad.isotropic_of_locally_isotropic GlobalTheory.QNorm.hasseNormSt F
    (ι := Fin 4) (by simp) ![a, b, -(a * b), -c]
    (fun i => by fin_cases i <;> simp [ha, hb, hc])
    (isotropic_real q hq0 hqq) (isotropic_finite q hq0 hqq)
  simp [Fin.sum_univ_four] at hx
  have pure : ∀ y₁ y₂ y₃ : F, a * y₁ ^ 2 + b * y₂ ^ 2 - a * b * y₃ ^ 2 = c →
      ∃ p : ℍ[F, a, b], p.re = 0 ∧ p * p = algebraMap F ℍ[F, a, b] c := by
    intro y₁ y₂ y₃ hy
    refine ⟨⟨0, y₁, y₂, y₃⟩, rfl, ?_⟩
    rw [mul_self_of_re_eq_zero _ rfl]
    change algebraMap F ℍ[F, a, b] (a * y₁ ^ 2 + b * y₂ ^ 2 - a * b * y₃ ^ 2) = _
    rw [hy]
  by_cases h3 : x 3 = 0
  · rw [h3] at hx
    obtain ⟨y₁, y₂, y₃, hy⟩ := exists_ternary_eq ha hb (u₁ := x 0) (u₂ := x 1) (u₃ := x 2)
      (fun h => hx0 (by
        simp only [Prod.mk.injEq] at h
        funext i; fin_cases i <;> simp [h.1, h.2.1, h.2.2, h3]))
      (by linear_combination hx) c
    exact pure y₁ y₂ y₃ hy
  · refine pure (x 0 / x 3) (x 1 / x 3) (x 2 / x 3) ?_
    field_simp
    linear_combination hx

end GlobalTheory.QSA.PureSq
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalPureQuaternionSqOfAdelicStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rational_pure_quaternion_sq_of_adelic : ∀ (F : Type) [Field F] [NumberField F] (a b : F), a ≠ 0 → b ≠ 0 → ∀ c : F, c ≠ 0 → ∀ q : DA F a b, q.re = 0 → q * q = algebraMap (AF F) (DA F a b) (algebraMap F (AF F) c) → ∃ p : ℍ[F, a, b], p.re = 0 ∧ p * p = algebraMap F ℍ[F, a, b] c := by
  first | exact @GlobalTheory.QSA.PureSq.exists_rat_of_adelic | exact GlobalTheory.QSA.PureSq.exists_rat_of_adelic | (intros; apply GlobalTheory.QSA.PureSq.exists_rat_of_adelic <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosureNormOneProductsSubgroupProperties
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosureNormOneProductsSubgroupProperties
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct

namespace GlobalTheory.QSA.Grp
variable {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] {a b : R}

theorem cont_coords : Continuous (coords : ℍ[R, a, b] → Fin 4 → R) := continuous_induced_dom
theorem cont_re : Continuous (fun x : ℍ[R, a, b] => x.re) := (continuous_apply 0).comp cont_coords
theorem cont_imI : Continuous (fun x : ℍ[R, a, b] => x.imI) := (continuous_apply 1).comp cont_coords
theorem cont_imJ : Continuous (fun x : ℍ[R, a, b] => x.imJ) := (continuous_apply 2).comp cont_coords
theorem cont_imK : Continuous (fun x : ℍ[R, a, b] => x.imK) := (continuous_apply 3).comp cont_coords

theorem cont_of {X : Type*} [TopologicalSpace X] {f : X → ℍ[R, a, b]}
    (h0 : Continuous fun x => (f x).re) (h1 : Continuous fun x => (f x).imI)
    (h2 : Continuous fun x => (f x).imJ) (h3 : Continuous fun x => (f x).imK) : Continuous f := by
  refine continuous_induced_rng.2 (continuous_pi fun i => ?_)
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3

theorem cont_mul : Continuous (fun p : ℍ[R, a, b] × ℍ[R, a, b] => p.1 * p.2) := by
  have r1 := (cont_re (a := a) (b := b)).comp (continuous_fst : Continuous (Prod.fst : ℍ[R, a, b] × ℍ[R, a, b] → ℍ[R, a, b]))
  have i1 := (cont_imI (a := a) (b := b)).comp (continuous_fst : Continuous (Prod.fst : ℍ[R, a, b] × ℍ[R, a, b] → ℍ[R, a, b]))
  have j1 := (cont_imJ (a := a) (b := b)).comp (continuous_fst : Continuous (Prod.fst : ℍ[R, a, b] × ℍ[R, a, b] → ℍ[R, a, b]))
  have k1 := (cont_imK (a := a) (b := b)).comp (continuous_fst : Continuous (Prod.fst : ℍ[R, a, b] × ℍ[R, a, b] → ℍ[R, a, b]))
  have r2 := (cont_re (a := a) (b := b)).comp (continuous_snd : Continuous (Prod.snd : ℍ[R, a, b] × ℍ[R, a, b] → ℍ[R, a, b]))
  have i2 := (cont_imI (a := a) (b := b)).comp (continuous_snd : Continuous (Prod.snd : ℍ[R, a, b] × ℍ[R, a, b] → ℍ[R, a, b]))
  have j2 := (cont_imJ (a := a) (b := b)).comp (continuous_snd : Continuous (Prod.snd : ℍ[R, a, b] × ℍ[R, a, b] → ℍ[R, a, b]))
  have k2 := (cont_imK (a := a) (b := b)).comp (continuous_snd : Continuous (Prod.snd : ℍ[R, a, b] × ℍ[R, a, b] → ℍ[R, a, b]))
  simp only [Function.comp_def] at r1 i1 j1 k1 r2 i2 j2 k2
  apply cont_of <;> simp only [QuaternionAlgebra.re_mul, QuaternionAlgebra.imI_mul,
    QuaternionAlgebra.imJ_mul, QuaternionAlgebra.imK_mul] <;> fun_prop

theorem cont_star : Continuous (fun x : ℍ[R, a, b] => star x) := by
  have r1 := cont_re (a := a) (b := b)
  have i1 := cont_imI (a := a) (b := b)
  have j1 := cont_imJ (a := a) (b := b)
  have k1 := cont_imK (a := a) (b := b)
  apply cont_of <;> simp only [QuaternionAlgebra.re_star, QuaternionAlgebra.imI_star,
    QuaternionAlgebra.imJ_star, QuaternionAlgebra.imK_star] <;> fun_prop

theorem cont_nrm : Continuous (nrm : ℍ[R, a, b] → R) := by
  have r1 := cont_re (a := a) (b := b)
  have i1 := cont_imI (a := a) (b := b)
  have j1 := cont_imJ (a := a) (b := b)
  have k1 := cont_imK (a := a) (b := b)
  unfold nrm
  fun_prop

theorem cont_conj (c d : ℍ[R, a, b]) : Continuous fun y : ℍ[R, a, b] => c * y * d := by
  have h1 : Continuous fun p : ℍ[R, a, b] × ℍ[R, a, b] => p.1 * p.2 := cont_mul
  have hl : Continuous fun y : ℍ[R, a, b] => c * y :=
    h1.comp (Continuous.prodMk (continuous_const : Continuous fun _ : ℍ[R, a, b] => c) continuous_id)
  exact h1.comp (Continuous.prodMk hl (continuous_const : Continuous fun _ : ℍ[R, a, b] => d))

omit [TopologicalSpace R] [IsTopologicalRing R] in
theorem nrm_star (x : ℍ[R, a, b]) : nrm (star x) = nrm x := by
  simp [nrm]

omit [TopologicalSpace R] [IsTopologicalRing R] in
theorem star_mul_eq (x : ℍ[R, a, b]) : star x * x = algebraMap R ℍ[R, a, b] (nrm x) := by
  ext <;> simp [nrm, QuaternionAlgebra.algebraMap_eq] <;> ring

omit [TopologicalSpace R] [IsTopologicalRing R] in
theorem nrm_one' : nrm (1 : ℍ[R, a, b]) = 1 := by simp [nrm]

end GlobalTheory.QSA.Grp

namespace GlobalTheory.QSA.Grp
variable {F : Type} [Field F] [NumberField F] {a b : F}

theorem rat_mul (x y : ℍ[F, a, b]) : rat (x * y) = rat x * rat y := by
  ext <;> simp [rat, QuaternionAlgebra.re_mul, QuaternionAlgebra.imI_mul, QuaternionAlgebra.imJ_mul,
    QuaternionAlgebra.imK_mul]

theorem rat_one : rat (1 : ℍ[F, a, b]) = 1 := by
  ext <;> simp [rat]

theorem rat_star (x : ℍ[F, a, b]) : rat (star x) = star (rat x) := by
  ext <;> simp [rat]

theorem supp {ε : AF F} (p q u : DA F a b) (hu : ε • u = u) : ε • (p * u * q) = p * u * q := by
  rw [← smul_mul_assoc, ← mul_smul_comm, hu]

theorem rat_inv {γ : ℍ[F, a, b]} (hγ : nrm γ = 1) :
    rat γ * rat (star γ) = 1 ∧ rat (star γ) * rat γ = 1 := by
  constructor
  · rw [← rat_mul, mul_star_eq, hγ, map_one, rat_one]
  · rw [← rat_mul, star_mul_eq, hγ, map_one, rat_one]

theorem nrm_of_mem {ε : AF F} {x : DA F a b} (hx : x ∈ H0 ε) : nrm x = 1 := by
  obtain ⟨γ, hγ, h, hh, -, rfl⟩ := hx
  rw [nrm_mul, nrm_rat, hγ, hh, map_one, one_mul]

theorem mul_mem {ε : AF F} {x y : DA F a b} (hx : x ∈ H0 ε) (hy : y ∈ H0 ε) : x * y ∈ H0 ε := by
  obtain ⟨γ, hγ, h, hh, hs, rfl⟩ := hx
  obtain ⟨γ', hγ', h', hh', hs', rfl⟩ := hy
  obtain ⟨e1, e2⟩ := rat_inv hγ'
  refine ⟨γ * γ', by rw [nrm_mul, hγ, hγ', one_mul], rat (star γ') * h * rat γ' * h', ?_, ?_, ?_⟩
  · rw [nrm_mul, nrm_mul, nrm_mul, hh, hh', nrm_rat, nrm_rat, nrm_star, hγ', map_one]; ring
  · have : rat (star γ') * h * rat γ' * h' - 1
        = rat (star γ') * (h - 1) * (rat γ' * h') + (h' - 1) := by
      rw [show rat (star γ') * (h - 1) * (rat γ' * h')
          = rat (star γ') * h * rat γ' * h' - rat (star γ') * rat γ' * h' by noncomm_ring, e2, one_mul]
      abel
    rw [this, smul_add, hs', supp _ _ _ hs]
  · rw [rat_mul]
    simp only [mul_assoc]
    rw [← mul_assoc (rat γ') (rat (star γ')), e1, one_mul]

theorem star_mem {ε : AF F} {x : DA F a b} (hx : x ∈ H0 ε) : star x ∈ H0 ε := by
  obtain ⟨γ, hγ, h, hh, hs, rfl⟩ := hx
  obtain ⟨e1, e2⟩ := rat_inv hγ
  refine ⟨star γ, by rw [nrm_star, hγ], rat γ * star h * rat (star γ), ?_, ?_, ?_⟩
  · rw [nrm_mul, nrm_mul, nrm_star, hh, nrm_rat, nrm_rat, nrm_star, hγ, map_one]; ring
  · have hs1 : ε • star (h - 1) = star (h - 1) := by
      rw [← QuaternionAlgebra.star_smul, hs]
    have : rat γ * star h * rat (star γ) - 1 = rat γ * star (h - 1) * rat (star γ) := by
      rw [star_sub, star_one, show rat γ * (star h - 1) * rat (star γ)
          = rat γ * star h * rat (star γ) - rat γ * rat (star γ) by noncomm_ring, e1]
    rw [this, supp _ _ _ hs1]
  · rw [star_mul, ← rat_star]
    simp only [← mul_assoc]
    rw [e2, one_mul]

theorem inv_right {δ δ' : ℍ[F, a, b]} (h : δ * δ' = 1) : δ' * δ = 1 := by
  have hn : nrm δ' * nrm δ = 1 := by rw [mul_comm, ← nrm_mul, h, nrm_one']
  have e : star δ * δ * δ' * δ = star δ * δ := by rw [mul_assoc (star δ), h, mul_one]
  rw [star_mul_eq] at e
  calc δ' * δ = algebraMap F ℍ[F, a, b] (nrm δ' * nrm δ) * (δ' * δ) := by rw [hn, map_one, one_mul]
    _ = algebraMap F ℍ[F, a, b] (nrm δ') * (algebraMap F ℍ[F, a, b] (nrm δ) * δ' * δ) := by
      rw [map_mul]; simp only [mul_assoc]
    _ = 1 := by rw [e, ← map_mul, hn, map_one]

theorem conj_mem {ε : AF F} {δ δ' : ℍ[F, a, b]} (hδ : δ * δ' = 1) {x : DA F a b} (hx : x ∈ H0 ε) :
    rat δ * x * rat δ' ∈ H0 ε := by
  obtain ⟨γ, hγ, h, hh, hs, rfl⟩ := hx
  have hδ2 := inv_right hδ
  have e1 : rat δ * rat δ' = 1 := by rw [← rat_mul, hδ, rat_one]
  have e2 : rat δ' * rat δ = 1 := by rw [← rat_mul, hδ2, rat_one]
  have hn : nrm δ * nrm δ' = 1 := by rw [← nrm_mul, hδ, nrm_one']
  refine ⟨δ * γ * δ', by rw [nrm_mul, nrm_mul, hγ, mul_one, hn], rat δ * h * rat δ', ?_, ?_, ?_⟩
  · rw [nrm_mul, nrm_mul, hh, nrm_rat, nrm_rat, mul_one, ← map_mul, hn, map_one]
  · have : rat δ * h * rat δ' - 1 = rat δ * (h - 1) * rat δ' := by
      rw [show rat δ * (h - 1) * rat δ' = rat δ * h * rat δ' - rat δ * rat δ' by noncomm_ring, e1]
    rw [this, supp _ _ _ hs]
  · rw [rat_mul, rat_mul]
    simp only [mul_assoc]
    rw [← mul_assoc (rat δ') (rat δ), e2, one_mul]

end GlobalTheory.QSA.Grp

namespace GlobalTheory.QSA.Grp

theorem t2Space_adeleRing_numberField (F : Type) [Field F] [NumberField F] : T2Space (AF F) :=
  haveI : T2Space (FiniteAdeleRing (𝓞 F) F) :=
    inferInstanceAs (T2Space (RestrictedProduct (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite))
  haveI : T2Space (InfiniteAdeleRing F) := inferInstanceAs (T2Space (∀ v : InfinitePlace F, v.Completion))
  inferInstanceAs (T2Space (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))

theorem closure_normOneProducts_subgroup_properties : ∀ (F : Type) [Field F] [NumberField F] (a b : F) (ε : AF F), ε * ε = ε →
    (∀ x ∈ closure (H0 (a := a) (b := b) ε), ∀ y ∈ closure (H0 (a := a) (b := b) ε),
      x * y ∈ closure (H0 (a := a) (b := b) ε)) ∧
    (∀ x ∈ closure (H0 (a := a) (b := b) ε), star x ∈ closure (H0 (a := a) (b := b) ε)) ∧
    (∀ δ δ' : ℍ[F, a, b], δ * δ' = 1 → ∀ x ∈ closure (H0 (a := a) (b := b) ε),
      rat δ * x * rat δ' ∈ closure (H0 (a := a) (b := b) ε)) ∧
    (∀ x ∈ closure (H0 (a := a) (b := b) ε), nrm x = 1) := by
  intro F _ _ a b ε _
  haveI := t2Space_adeleRing_numberField F
  refine ⟨fun x hx y hy => ?_, fun x hx => ?_, fun δ δ' hδ x hx => ?_, fun x hx => ?_⟩
  · exact map_mem_closure₂ cont_mul hx hy fun u hu v hv => mul_mem hu hv
  · exact map_mem_closure cont_star hx fun u hu => star_mem hu
  · have hc : Continuous fun y : DA F a b => rat δ * y * rat δ' := cont_conj (rat δ) (rat δ')
    have hm : Set.MapsTo (fun y : DA F a b => rat δ * y * rat δ') (H0 ε) (H0 ε) :=
      fun u hu => conj_mem hδ hu
    have key := map_mem_closure (x := x) hc hx hm
    exact key
  · have hcl : IsClosed {y : DA F a b | nrm y = 1} := isClosed_eq cont_nrm continuous_const
    exact closure_minimal (fun y hy => nrm_of_mem hy) hcl hx

end GlobalTheory.QSA.Grp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosureNormOneProductsSubgroupPropertiesStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closure_normOneProducts_h0_properties : ∀ (F : Type) [Field F] [NumberField F] (a b : F) (ε : AF F), ε * ε = ε → (∀ x ∈ closure (H0 (a := a) (b := b) ε), ∀ y ∈ closure (H0 (a := a) (b := b) ε), x * y ∈ closure (H0 (a := a) (b := b) ε)) ∧ (∀ x ∈ closure (H0 (a := a) (b := b) ε), star x ∈ closure (H0 (a := a) (b := b) ε)) ∧ (∀ δ δ' : ℍ[F, a, b], δ * δ' = 1 → ∀ x ∈ closure (H0 (a := a) (b := b) ε), rat δ * x * rat δ' ∈ closure (H0 (a := a) (b := b) ε)) ∧ (∀ x ∈ closure (H0 (a := a) (b := b) ε), nrm x = 1) := by
  first | exact @GlobalTheory.QSA.Grp.closure_normOneProducts_subgroup_properties | exact GlobalTheory.QSA.Grp.closure_normOneProducts_subgroup_properties | (intros; apply GlobalTheory.QSA.Grp.closure_normOneProducts_subgroup_properties <;> assumption)
end
end
