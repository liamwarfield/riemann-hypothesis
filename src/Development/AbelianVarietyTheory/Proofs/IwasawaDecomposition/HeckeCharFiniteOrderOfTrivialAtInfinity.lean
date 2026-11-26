module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterUnramifiedAeAndExistsLevel
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjugateEmbApply
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNatCongrOfAbsNormPrime

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharFiniteOrderOfTrivialAtInfinity
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharFiniteOrderOfTrivialAtInfinity
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.Mem.Chr
open Neutral.B1 hiding localIdele Ideles diagUnits
open ReciprocityTheory.Neutral.Bridge.HCFR hiding infIdele

namespace GlobalTheory.Mem.FinOrder

variable {L : Type} [Field L] [NumberField L]

theorem exists_pow_congr (v : HeightOneSpectrum (𝓞 L)) (n : ℕ) :
    ∃ m : ℕ, 0 < m ∧ ∀ x : (v.adicCompletion L)ˣ, IsUnitAt v x →
      Valued.v (((x ^ m : (v.adicCompletion L)ˣ) : v.adicCompletion L) - 1) ≤ WithZero.exp (-(n : ℤ)) := by
  have hu : Valued.v ((atFin v (unif v) : (v.adicCompletion L)ˣ) : v.adicCompletion L) = WithZero.exp (-1 : ℤ) :=
    unif_spec v
  have hc : Valued.v (((atFin v (unif v) : (v.adicCompletion L)ˣ) : v.adicCompletion L) ^ n) = WithZero.exp (-(n : ℤ)) := by
    rw [map_pow, hu, ← WithZero.exp_nsmul]; simp
  have hc1 : ((atFin v (unif v) : (v.adicCompletion L)ˣ) : v.adicCompletion L) ^ n ∈ v.adicCompletionIntegers L := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, hc, ← WithZero.exp_zero, WithZero.exp_le_exp]
    omega
  let c : v.adicCompletionIntegers L := ⟨_, hc1⟩
  have hc0 : c ≠ 0 := fun h => pow_ne_zero n (Units.ne_zero _) (congrArg Subtype.val h)
  have : Finite (v.adicCompletionIntegers L ⧸ Ideal.span {c}) :=
    Formalism.UG.P.glint_finite_quotient_of_dvr (Formalism.UG.P.glint_finite_residueField v) _
      (by rwa [Ne, Ideal.span_singleton_eq_bot])
  refine ⟨Nat.card (v.adicCompletionIntegers L ⧸ Ideal.span {c})ˣ, Nat.card_pos, fun x hx => ?_⟩
  have hx : Valued.v (x : v.adicCompletion L) = 1 := hx
  have hx' : Valued.v ((x⁻¹ : (v.adicCompletion L)ˣ) : v.adicCompletion L) = 1 := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, hx, inv_one]
  let y : (v.adicCompletionIntegers L)ˣ :=
    ⟨⟨x, hx.le⟩, ⟨(x⁻¹ : (v.adicCompletion L)ˣ), hx'.le⟩, Subtype.ext x.mul_inv, Subtype.ext x.inv_mul⟩
  have h1 := pow_card_eq_one' (x := Units.map (Ideal.Quotient.mk (Ideal.span {c})).toMonoidHom y)
  have h2 : Ideal.Quotient.mk (Ideal.span {c})
      ((y : v.adicCompletionIntegers L) ^ Nat.card (v.adicCompletionIntegers L ⧸ Ideal.span {c})ˣ) =
      Ideal.Quotient.mk (Ideal.span {c}) 1 := by
    rw [map_pow, map_one]
    exact congrArg Units.val h1
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq.1 h2)
  have h3 : (a : v.adicCompletion L) * ((atFin v (unif v) : (v.adicCompletion L)ˣ) : v.adicCompletion L) ^ n =
      (x : v.adicCompletion L) ^ Nat.card (v.adicCompletionIntegers L ⧸ Ideal.span {c})ˣ - 1 :=
    congrArg Subtype.val ha
  rw [Units.val_pow_eq_pow_val, ← h3, map_mul, hc]
  exact mul_le_of_le_one_left' a.2

theorem triv_inf (χ : HChar L) (h : ∀ k, χ.inf k = 1) (u : ∀ w : InfinitePlace L, (w.Completion)ˣ) :
    χ.1 (∏ w, infIdele L w (u w)) = 1 := by
  have key : (fun u : ∀ w : InfinitePlace L, (w.Completion)ˣ => χ.1 (∏ w, infIdele L w (u w))) = fun _ => 1 := by
    refine (GlobalTheory.InfTypeLocal.denseRange_atInf L).equalizer ?_ continuous_const ?_
    · exact χ.2.1.comp (continuous_finsetProd _ fun w _ =>
        (GlobalTheory.InfTypeLocal.continuous_infIdele L w).comp (continuous_apply w))
    · funext k
      have h1 : χ.1 (infDiag k) = 1 := h k
      unfold infDiag at h1
      rw [MonoidHom.finsetProd_apply] at h1
      exact h1
  exact congrFun key u

theorem exists_decomp (a : Ideles L) :
    ∃ u : ∀ w : InfinitePlace L, (w.Completion)ˣ, a = (∏ w, infIdele L w (u w)) * finPartI L a := by
  classical
  let p : ∀ w : InfinitePlace L, AdeleRing (𝓞 L) L →* w.Completion := fun w =>
    (Pi.evalMonoidHom (fun w : InfinitePlace L => w.Completion) w).comp
      (MonoidHom.fst (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L))
  let q : AdeleRing (𝓞 L) L →* FiniteAdeleRing (𝓞 L) L :=
    MonoidHom.snd (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L)
  refine ⟨fun w => Units.map (p w) a, Units.ext (Prod.ext (funext fun w => ?_) ?_)⟩
  · show p w a = p w ((∏ w, infIdele L w (Units.map (p w) a)) * finPartI L a : Ideles L)
    rw [Units.val_mul, map_mul, Units.coe_prod, map_prod, Finset.prod_eq_single w]
    · show p w a = Pi.mulSingle (M := fun w : InfinitePlace L => w.Completion) w (p w a) w * 1
      simp
    · intro w' _ hw
      show Pi.mulSingle (M := fun w : InfinitePlace L => w.Completion) w' (p w' a) w = 1
      exact Pi.mulSingle_eq_of_ne hw.symm _
    · simp
  · show q a = q ((∏ w, infIdele L w (Units.map (p w) a)) * finPartI L a : Ideles L)
    rw [Units.val_mul, map_mul, Units.coe_prod, map_prod, Finset.prod_eq_one, one_mul]
    · rfl
    · exact fun _ _ => rfl


open Classical in
theorem finite_order_of_inf_eq_one : ∀ (L : Type) [Field L] [NumberField L] (χ : HChar L),
    (∀ k, χ.inf k = 1) → ∃ n : ℕ, 0 < n ∧ χ.OrderDvd n := by
  intro L _ _ χ h
  obtain ⟨hfin, hlev⟩ := GlobalTheory.T.heckeCharacter_unramified_ae_and_exists_level L χ
  have hm : ∀ v, ∃ m : ℕ, 0 < m ∧ ∀ x, IsUnitAt v x → χ.loc v x ^ m = 1 := by
    intro v
    obtain ⟨n, hn⟩ := hlev v
    obtain ⟨m, hm, hx⟩ := exists_pow_congr v n
    refine ⟨m, hm, fun x hu => ?_⟩
    rw [← map_pow]
    refine hn _ ?_ (hx x hu)
    show Valued.v (((x ^ m : (v.adicCompletion L)ˣ) : v.adicCompletion L)) = 1
    rw [Units.val_pow_eq_pow_val, map_pow, show Valued.v (x : v.adicCompletion L) = 1 from hu, one_pow]
  choose m hm0 hm using hm
  set M := ∏ v ∈ hfin.toFinset, m v with hM
  have hM0 : 0 < M := Finset.prod_pos fun v _ => hm0 v
  have hloc : ∀ v x, IsUnitAt v x → χ.loc v x ^ M = 1 := by
    intro v x hx
    by_cases hv : χ.UnrAt v
    · rw [hv x hx, one_pow]
    · obtain ⟨d, hd⟩ : m v ∣ M := Finset.dvd_prod_of_mem _ (hfin.mem_toFinset.2 hv)
      rw [hd, pow_mul, hm v x hx, one_pow]
  have hunit : ∀ a ∈ unitIdl L, (χ ^ M).1 a = 1 := by
    intro a ha
    obtain ⟨u, hu⟩ := exists_decomp a
    have h1 : (χ ^ M).1 (finPartI L a) = 1 := by
      refine GlobalTheory.Mem.LocTriv.eq_one_of_local L _ (χ ^ M).2.1 _ (finPartI_mem_unitIdl.2 ha) (fun _ => rfl) fun v x hx => ?_
      refine hloc v x ?_
      show Valued.v (x : v.adicCompletion L) = 1
      rw [hx]
      exact ha v
    have h2 : (χ ^ M).1 (∏ w, infIdele L w (u w)) = 1 := by
      show χ.1 _ ^ M = 1
      rw [triv_inf χ h, one_pow]
    rw [hu, map_mul, h1, h2, one_mul]
  have hle : unitIdl L ⊔ (diagUnits L).range ≤ (χ ^ M).1.ker := by
    refine sup_le hunit ?_
    rintro _ ⟨k, rfl⟩
    exact (χ ^ M).2.2 k
  have hfi := GlobalTheory.Mem.UnitIndex.finiteIndex_unitIdl_sup L
  refine ⟨M * (unitIdl L ⊔ (diagUnits L).range).index, Nat.mul_pos hM0 (Nat.pos_of_ne_zero hfi.index_ne_zero), ?_⟩
  unfold HChar.OrderDvd
  rw [pow_mul]
  refine Subtype.ext (MonoidHom.ext fun a => ?_)
  show (χ ^ M).1 a ^ _ = 1
  rw [← map_pow]
  exact hle (Subgroup.pow_index_mem _ a)

end GlobalTheory.Mem.FinOrder
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharFiniteOrderOfTrivialAtInfinityStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.Mem.Chr Classical
open Neutral.B1 hiding localIdele Ideles diagUnits
open ReciprocityTheory.Neutral.Bridge.HCFR hiding infIdele
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeChar_finiteOrder_of_trivial_at_infinity : ∀ (L : Type) [Field L] [NumberField L] (χ : HChar L), (∀ k, χ.inf k = 1) → ∃ n : ℕ, 0 < n ∧ χ.OrderDvd n := by
  first | exact @GlobalTheory.Mem.FinOrder.finite_order_of_inf_eq_one | exact GlobalTheory.Mem.FinOrder.finite_order_of_inf_eq_one | (intros; apply GlobalTheory.Mem.FinOrder.finite_order_of_inf_eq_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOfValuedEq
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.Mem.Chr
open Neutral.B1 hiding localIdele Ideles diagUnits
open ReciprocityTheory.Neutral.Bridge.HCFR hiding infIdele

namespace GlobalTheory.Mem.Chr

section General

theorem continuous_of_valued_eq {A B Γ : Type*} [Ring A] [Ring B] [LinearOrderedCommGroupWithZero Γ]
    [Valued A Γ] [Valued B Γ] (hs : Function.Surjective (Valued.v : A → Γ)) (f : A →+* B)
    (hf : ∀ x, Valued.v (f x) = Valued.v x) : Continuous f := by
  refine continuous_of_continuousAt_zero f ?_
  rw [ContinuousAt, map_zero, (Valued.hasBasis_nhds_zero A _).tendsto_iff (Valued.hasBasis_nhds_zero B _)]
  intro γ _
  obtain ⟨a, ha⟩ := hs (MonoidWithZeroHom.ValueGroup₀.embedding γ.1)
  have ha0 : (Valued.v : Valuation A Γ).restrict a ≠ 0 := by
    simp [ha]
  refine ⟨Units.mk0 _ ha0, trivial, fun x hx => ?_⟩
  simp only [Set.mem_setOf_eq, Units.val_mk0, Valuation.restrict_lt_iff] at hx
  simp only [Set.mem_setOf_eq, Valuation.restrict_lt_iff_lt_embedding]
  rw [hf, ← ha]
  exact hx

variable {L : Type} [Field L] [NumberField L]


open scoped WithZeroTopology in
theorem exists_finCompl_map (c : L ≃+* L) {v v' : HeightOneSpectrum (𝓞 L)} (h : ConjPl c v v') :
    ∃ φ : v.adicCompletion L →+* v'.adicCompletion L, Continuous φ ∧
      (∀ k : L, φ (algebraMap L _ k) = algebraMap L _ (c k)) ∧ ∀ x, Valued.v (φ x) = Valued.v x := by
  have hc : Continuous (WithVal.map (v.valuation L) (v'.valuation L) (c : L →+* L)) :=
    continuous_of_valued_eq (fun γ => by
      obtain ⟨k, hk⟩ := v.valuation_surjective L γ
      exact ⟨WithVal.toVal _ k, hk⟩) _ fun x => h x.ofVal
  let φ : v.adicCompletion L →+* v'.adicCompletion L :=
    ((HeightOneSpectrum.adicCompletion.equiv L v').symm.toRingHom.comp
      (UniformSpace.Completion.mapRingHom _ hc)).comp (HeightOneSpectrum.adicCompletion.equiv L v).toRingHom
  have h1 : Continuous φ :=
    (HeightOneSpectrum.adicCompletion.continuous_ofCompletion L v').comp
      (UniformSpace.Completion.continuous_map.comp (HeightOneSpectrum.adicCompletion.continuous_toCompletion L v))
  have h2 : ∀ k : L, φ (algebraMap L _ k) = algebraMap L _ (c k) := fun k => by
    apply HeightOneSpectrum.adicCompletion.ext
    exact UniformSpace.Completion.mapRingHom_coe hc (WithVal.toVal _ k)
  refine ⟨φ, h1, h2, fun x => ?_⟩
  refine (HeightOneSpectrum.denseRange_algebraMap L v).induction_on (p := fun x => Valued.v (φ x) = Valued.v x) x
    (isClosed_eq ((Valued.continuous_valuation_of_surjective (v'.valuedAdicCompletion_surjective L)).comp h1)
      (Valued.continuous_valuation_of_surjective (v.valuedAdicCompletion_surjective L))) fun k => ?_
  rw [h2]
  exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v' _).trans
    ((h k).trans (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _).symm)


omit [NumberField L] in
theorem exists_infCompl_map (c : L ≃+* L) (w : InfinitePlace L) :
    ∃ φ : (w.comap (c : L →+* L)).Completion →+* w.Completion, Continuous φ ∧
      ∀ k : L, φ (algebraMap L _ k) = algebraMap L _ (c k) := by
  have hc : Continuous (WithAbs.map (w.comap (c : L →+* L)).1 w.1 (c : L →+* L)) :=
    (AddMonoidHomClass.isometry_of_norm _ fun x => rfl).continuous
  let φ : (w.comap (c : L →+* L)).Completion →+* w.Completion :=
    ((AbsoluteValue.Completion.ofCompletion (v := w.1)).comp
      (UniformSpace.Completion.mapRingHom _ hc)).comp
        (AbsoluteValue.Completion.toCompletion (v := (w.comap (c : L →+* L)).1))
  have hφ : Continuous φ :=
    (AbsoluteValue.Completion.continuous_ofCompletion w.1).comp
      (UniformSpace.Completion.continuous_map.comp
        (AbsoluteValue.Completion.continuous_toCompletion _))
  refine ⟨φ, hφ, fun k => ?_⟩
  apply AbsoluteValue.Completion.toCompletion_injective w.1
  simpa [φ, AbsoluteValue.Completion.algebraMap_def, WithAbs.algebraMap_right_apply] using
    (UniformSpace.Completion.mapRingHom_coe hc (WithAbs.toAbs _ k))

theorem conjPl_symm_iff (c : L ≃+* L) (v v' : HeightOneSpectrum (𝓞 L)) : ConjPl c.symm v' v ↔ ConjPl c v v' :=
  ⟨fun h x => by simpa using (h (c x)).symm, fun h x => by simpa using (h (c.symm x)).symm⟩

theorem map_update_one {ι : Type} [DecidableEq ι] {M : ι → Type} [∀ i, Ring (M i)] {f : ι → ι}
    (hf : Function.Injective f) (φ : ∀ j, M (f j) →+* M j) (j : ι) (x : M (f j)) :
    (fun i => φ i (Function.update (fun i => (1 : M i)) (f j) x (f i))) =
      Function.update (fun i => (1 : M i)) j (φ j x) := by
  funext i
  by_cases hi : i = j
  · subst hi
    simp
  · rw [Function.update_of_ne hi, Function.update_of_ne (hf.ne hi), map_one]

end General


open Classical in
theorem exists_isConjI : ∀ (L : Type) [Field L] [NumberField L] (c : L ≃+* L), ∃ C : Ideles L →* Ideles L, IsConjI c C := by
  intro L _ _ c
  choose f hf hfu using fun v => existsUnique_conjPl c.symm v
  have hf' : ∀ v, ConjPl c (f v) v := fun v => (conjPl_symm_iff c _ _).1 (hf v)
  have hfe : ∀ {v v'}, ConjPl c v v' → v = f v' := fun h => hfu _ _ ((conjPl_symm_iff c _ _).2 h)
  have hfi : Function.Injective f := fun a b hab =>
    (existsUnique_conjPl c (f a)).unique (hf' a) (hab ▸ hf' b)
  choose φ φc φk φv using fun v => exists_finCompl_map c (hf' v)
  choose ψ ψc ψk using exists_infCompl_map c
  have hg : ∀ w : InfinitePlace L, (w.comap (c.symm : L →+* L)).comap (c : L →+* L) = w := fun w => by
    ext x
    simp
  have hgi : Function.Injective fun w : InfinitePlace L => w.comap (c : L →+* L) := fun a b hab => by
    ext x
    simpa using congrArg (fun w : InfinitePlace L => w (c.symm x)) hab
  have hφ : ∀ᶠ j in Filter.cofinite, Set.MapsTo (φ j) ((f j).adicCompletionIntegers L) (j.adicCompletionIntegers L) :=
    Filter.Eventually.of_forall fun j x hx => (φv j x).trans_le hx
  let Φ : FiniteAdeleRing (𝓞 L) L →+* FiniteAdeleRing (𝓞 L) L :=
    RestrictedProduct.mapAlongRingHom (fun v : HeightOneSpectrum (𝓞 L) => v.adicCompletion L)
      (fun v : HeightOneSpectrum (𝓞 L) => v.adicCompletion L) f hfi.tendsto_cofinite φ hφ
  have Φc : Continuous Φ :=
    RestrictedProduct.mapAlong_continuous (fun v : HeightOneSpectrum (𝓞 L) => v.adicCompletion L)
      (fun v : HeightOneSpectrum (𝓞 L) => v.adicCompletion L) f hfi.tendsto_cofinite (fun j r => φ j r) hφ φc
  let Ψ : InfiniteAdeleRing L →+* InfiniteAdeleRing L :=
    RingHom.pi fun w => (ψ w).comp (Pi.evalRingHom (fun w : InfinitePlace L => w.Completion) (w.comap (c : L →+* L)))
  have Ψc : Continuous Ψ := continuous_pi fun w => (ψc w).comp (continuous_apply _)
  let A : AdeleRing (𝓞 L) L →+* AdeleRing (𝓞 L) L := RingHom.prodMap Ψ Φ
  have Ac : Continuous A := Ψc.prodMap Φc
  let C : Ideles L →* Ideles L := Units.map A.toMonoidHom
  have hinf : ∀ (w w' : InfinitePlace L) (e : w'.comap (c : L →+* L) = w), ∃ θ : w.Completion →+* w'.Completion,
      (∀ k : L, θ (algebraMap L _ k) = algebraMap L _ (c k)) ∧
      ∀ y, C (ReciprocityTheory.Neutral.Bridge.HCFR.infIdele L w y) = ReciprocityTheory.Neutral.Bridge.HCFR.infIdele L w' (Units.map θ.toMonoidHom y) := by
    rintro _ w' rfl
    exact ⟨ψ w', ψk w', fun y => Units.ext (Prod.ext (map_update_one hgi ψ w' y) (map_one Φ))⟩
  have hloc : ∀ v (y : ((f v).adicCompletion L)ˣ),
      C (Neutral.B1.localIdele L (f v) y) = Neutral.B1.localIdele L v (Units.map (φ v).toMonoidHom y) := fun v y =>
    Units.ext (Prod.ext (map_one Ψ) (Subtype.ext (map_update_one hfi φ v y)))
  refine ⟨C, Continuous.units_map _ Ac, fun k => ?_, fun w k => ?_, fun w y => ?_, fun v v' h k => ?_,
    fun v v' h x => ?_, fun v v' h a => ?_⟩
  · exact Units.ext (Prod.ext (funext fun w => ψk w k) (FiniteAdeleRing.ext _ fun v => φk v k))
  · obtain ⟨θ, h1, h2⟩ := hinf w _ (hg w)
    rw [h2]
    exact congrArg _ (Units.ext (h1 k))
  · obtain ⟨θ, -, h2⟩ := hinf w _ (hg w)
    exact ⟨_, h2 y⟩
  · obtain rfl := hfe h
    rw [hloc]
    exact congrArg _ (Units.ext (φk v' k))
  · obtain rfl := hfe h
    exact ⟨_, hloc v' x⟩
  · obtain rfl := hfe h
    refine ⟨φv v' _, ?_⟩
    rw [← φv v' (_ - 1), map_sub (φ v'), map_one (φ v')]
    rfl

end GlobalTheory.Mem.Chr
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuedPowSubOneLtOne
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuationPowSubPowLe
universe u_1 u_2

namespace GlobalTheory.ValuationPowSubPow

theorem valuation_pow_sub_pow_le {K : Type u_1} {Γ : Type u_2} [Field K]
    [LinearOrderedCommGroupWithZero Γ] (w : Valuation K Γ) {a b : K}
    (ha : w a ≤ 1) (hb : w b ≤ 1) (m : ℕ) : w (a ^ m - b ^ m) ≤ w (a - b) := by
  induction m with
  | zero => simp
  | succ n ih =>
    have h : a ^ (n + 1) - b ^ (n + 1) = a * (a ^ n - b ^ n) + b ^ n * (a - b) := by ring
    rw [h]
    refine w.map_add_le ?_ ?_
    · rw [map_mul]
      exact (mul_le_of_le_one_left' ha).trans ih
    · rw [map_mul, map_pow]
      exact mul_le_of_le_one_left' (pow_le_one' hb n)

end GlobalTheory.ValuationPowSubPow
end

open NumberField IsDedekindDomain Formalism.L2.Host IsLocalRing Polynomial

namespace GlobalTheory.Mem.WildChar

theorem le_exp_neg_one_of_lt_one {g : WithZero (Multiplicative ℤ)} (hy : g < 1) :
    g ≤ WithZero.exp (-1 : ℤ) := by
  by_cases hg : g = 0
  · rw [hg]; exact zero_le
  · rw [← WithZero.exp_log hg] at hy ⊢
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at hy
    rw [WithZero.exp_le_exp]
    omega

theorem val_pow_sub_pow_le {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]
    (w : Valuation K Γ) {a b : K} (ha : w a ≤ 1) (hb : w b ≤ 1) (m : ℕ) :
    w (a ^ m - b ^ m) ≤ w (a - b) := by
  first
  | exact @_root_.GlobalTheory.ValuationPowSubPow.valuation_pow_sub_pow_le
  | exact _root_.GlobalTheory.ValuationPowSubPow.valuation_pow_sub_pow_le
  | (apply _root_.GlobalTheory.ValuationPowSubPow.valuation_pow_sub_pow_le <;> assumption)
  | (intros; apply _root_.GlobalTheory.ValuationPowSubPow.valuation_pow_sub_pow_le <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ValuationPowSubPow.valuation_pow_sub_pow_le <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ValuationPowSubPow.valuation_pow_sub_pow_le ..)

theorem val_pow_sub_one_le {K : Type*} [Field K] (w : Valuation K (WithZero (Multiplicative ℤ)))
    {u : K} (hu : w u ≤ 1) (hu1 : w (u - 1) < 1) {q : ℕ} (hq : w (q : K) < 1) :
    w (u ^ q - 1) ≤ w (u - 1) * WithZero.exp (-1 : ℤ) := by
  rw [← mul_geom_sum, map_mul]
  refine mul_le_mul_right (le_exp_neg_one_of_lt_one ?_) _
  have e : ∑ i ∈ Finset.range q, u ^ i = (q : K) + ∑ i ∈ Finset.range q, (u ^ i - 1 ^ i) := by
    simp
  rw [e]
  refine Valuation.map_add_lt _ hq (Valuation.map_sum_lt _ one_ne_zero fun i _ => ?_)
  exact (val_pow_sub_pow_le w hu (map_one w).le i).trans_lt hu1

theorem val_pow_pow_sub_one_le {K : Type*} [Field K] (w : Valuation K (WithZero (Multiplicative ℤ)))
    {u : K} (hu : w u ≤ 1) (hu1 : w (u - 1) < 1) {q : ℕ} (hq : w (q : K) < 1) (n : ℕ) :
    w (u ^ (q ^ n) - 1) ≤ WithZero.exp (-(n : ℤ)) := by
  induction n with
  | zero => simpa using hu1.le
  | succ n ih =>
    have h1 : w (u ^ (q ^ n)) ≤ 1 := by rw [map_pow]; exact pow_le_one' hu _
    have h2 : w (u ^ (q ^ n) - 1) < 1 := by
      have := val_pow_sub_pow_le w hu (map_one w).le (q ^ n)
      rw [one_pow] at this
      exact this.trans_lt hu1
    rw [pow_succ, pow_mul]
    refine (val_pow_sub_one_le w h1 h2 hq).trans ((mul_le_mul_left ih _).trans (le_of_eq ?_))
    rw [← WithZero.exp_add]
    congr 1
    push_cast
    ring

variable {L : Type} [Field L] [NumberField L] (v : HeightOneSpectrum (𝓞 L))

theorem valued_algebraMap_lt_one {y : 𝓞 L} :
    Valued.v (algebraMap (𝓞 L) (v.adicCompletion L) y) < 1 ↔ y ∈ v.asIdeal := by
  have h3 : Valued.v (algebraMap (𝓞 L) (v.adicCompletion L) y)
      = v.valuation L (algebraMap (𝓞 L) L y) :=
    ReciprocityTheory.Aut.adic_valued_algebraMap v (algebraMap (𝓞 L) L y)
  rw [h3]
  exact HeightOneSpectrum.valuation_lt_one_iff_mem v _

theorem valued_absNorm_lt_one :
    Valued.v ((Ideal.absNorm v.asIdeal : ℕ) : v.adicCompletion L) < 1 := by
  rw [← map_natCast (algebraMap (𝓞 L) (v.adicCompletion L)), valued_algebraMap_lt_one]
  exact Ideal.absNorm_mem v.asIdeal

theorem one_lt_absNorm : 1 < Ideal.absNorm v.asIdeal := by
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]; exact v.isPrime.ne_top
  omega

theorem valued_pow_sub_one_lt_one {x : v.adicCompletion L} (hx : Valued.v x = 1) :
    Valued.v (x ^ (Ideal.absNorm v.asIdeal - 1) - 1) < 1 := by
  obtain ⟨y, hy⟩ := ReciprocityTheory.Aut.adic_exists_approx v x hx.le
  have hy1 : Valued.v (algebraMap (𝓞 L) (v.adicCompletion L) y) = 1 := by
    rw [← hx]
    apply Valuation.map_eq_of_sub_lt
    rw [Valuation.map_sub_swap, hx]
    exact hy
  have hnot : y ∉ v.asIdeal := by
    rw [← valued_algebraMap_lt_one, hy1]; exact lt_irrefl _
  have hmem : y ^ (Ideal.absNorm v.asIdeal - 1) - 1 ∈ v.asIdeal := by
    haveI := v.isMaximal
    letI := Ideal.Quotient.field v.asIdeal
    haveI : Finite (𝓞 L ⧸ v.asIdeal) := v.asIdeal.finiteQuotientOfFreeOfNeBot v.ne_bot
    letI := Fintype.ofFinite (𝓞 L ⧸ v.asIdeal)
    rw [← Ideal.Quotient.eq, map_pow, map_one, Ideal.absNorm_apply, Submodule.cardQuot_apply,
      Nat.card_eq_fintype_card]
    exact FiniteField.pow_card_sub_one_eq_one _ (fun h => hnot (Ideal.Quotient.eq_zero_iff_mem.1 h))
  rw [← valued_algebraMap_lt_one, map_sub, map_pow, map_one] at hmem
  rw [← sub_add_sub_cancel _
    (algebraMap (𝓞 L) (v.adicCompletion L) y ^ (Ideal.absNorm v.asIdeal - 1))]
  exact Valuation.map_add_lt _ ((val_pow_sub_pow_le _ hx.le hy1.le _).trans_lt hy) hmem

theorem mem_maximalIdeal_iff (a : v.adicCompletionIntegers L) :
    a ∈ maximalIdeal (v.adicCompletionIntegers L) ↔ Valued.v (a : v.adicCompletion L) < 1 := by
  rw [mem_maximalIdeal, mem_nonunits_iff,
    HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
  have h : Valued.v (a : v.adicCompletion L) ≤ 1 := a.2
  exact ⟨fun h' => lt_of_le_of_ne h h', fun h' => h'.ne⟩

theorem exists_rootOfUnity_congr {x : v.adicCompletion L} (hx : Valued.v x = 1) :
    ∃ ζ : v.adicCompletion L, ζ ^ (Ideal.absNorm v.asIdeal - 1) = 1 ∧ Valued.v (ζ - x) < 1 := by
  have hc : IsAdicComplete (maximalIdeal (v.adicCompletionIntegers L))
      (v.adicCompletionIntegers L) := by
    refine NormIntegers.isAdicComplete_of_fg (C := v.adicCompletion L) ⟨?_, ?_, ?_⟩
      (IsNoetherian.noetherian _) (maximalIdeal.isMaximal _).ne_top
    · exact FaithfulSMul.algebraMap_injective _ _
    · intro x
      have : ‖(x : v.adicCompletion L)‖ ≤ 1 := Valued.toNormedField.norm_le_one_iff.2 x.2
      exact_mod_cast this
    · intro x hx
      have : ‖x‖ ≤ 1 := by exact_mod_cast hx
      exact ⟨⟨x, Valued.toNormedField.norm_le_one_iff.1 this⟩, rfl⟩
  have hq := one_lt_absNorm v
  let a : v.adicCompletionIntegers L := ⟨x, hx.le⟩
  obtain ⟨ζ, h1, h2⟩ := HenselianRing.is_henselian (I := maximalIdeal (v.adicCompletionIntegers L))
    (X ^ (Ideal.absNorm v.asIdeal - 1) - C 1) (monic_X_pow_sub_C _ (by omega)) a
    (by
      rw [mem_maximalIdeal_iff]
      simpa [a] using valued_pow_sub_one_lt_one v hx)
    (by
      apply IsUnit.map
      rw [HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
      have h3 : Valued.v (((Ideal.absNorm v.asIdeal - 1 : ℕ)) : v.adicCompletion L) = 1 := by
        rw [Nat.cast_sub hq.le, Nat.cast_one, Valuation.map_sub_swap]
        exact Valuation.map_one_sub_of_lt _ (valued_absNorm_lt_one v)
      simp [a, derivative_X_pow, hx, h3])
  refine ⟨ζ, ?_, ?_⟩
  · have h4 : ζ ^ (Ideal.absNorm v.asIdeal - 1) = 1 := by
      simpa [sub_eq_zero] using h1
    have h5 := congrArg (algebraMap (v.adicCompletionIntegers L) (v.adicCompletion L)) h4
    rw [map_pow, map_one] at h5
    exact h5
  · have h6 := (mem_maximalIdeal_iff v _).1 h2
    rw [AddSubgroupClass.coe_sub] at h6
    exact h6

theorem orders_on_units : ∀ (L : Type) [Field L] [NumberField L] (χ : HChar L) (v : HeightOneSpectrum (𝓞 L)), (χ.TameAt v → ∀ x, IsUnitAt v x → χ.loc v x ^ (Ideal.absNorm v.asIdeal - 1) = 1) ∧ ((∀ x : (v.adicCompletion L)ˣ, x ^ (Ideal.absNorm v.asIdeal - 1) = 1 → χ.loc v x = 1) → ∀ x, IsUnitAt v x → ∃ n : ℕ, χ.loc v x ^ (Ideal.absNorm v.asIdeal ^ n) = 1) := by
  intro L _ _ χ v
  refine ⟨fun h x hx => ?_, fun h x hx => ?_⟩
  · rw [← map_pow]
    refine h _ (GlobalTheory.Mem.UnrAe.isUnitAt_pow hx _) ?_
    rw [Units.val_pow_eq_pow_val]
    simpa using le_exp_neg_one_of_lt_one (valued_pow_sub_one_lt_one v hx)
  · obtain ⟨n, hn⟩ := GlobalTheory.Mem.UnrAe.exists_levelLe χ v
    have hx' : Valued.v (x : v.adicCompletion L) = 1 := hx
    obtain ⟨ζ, h1, h2⟩ := exists_rootOfUnity_congr v hx'
    have hζ : Valued.v ζ = 1 := by
      rw [← hx']
      apply Valuation.map_eq_of_sub_lt
      rwa [hx']
    have h0 : ζ ≠ 0 := by
      rintro rfl
      simp at hζ
    let z : (v.adicCompletion L)ˣ := Units.mk0 ζ h0
    have hz : χ.loc v z = 1 := h z (Units.ext (by simpa [z] using h1))
    have hu : IsUnitAt v (x * z⁻¹) := by
      simp [IsUnitAt, z, hx', hζ]
    have hu1 : Valued.v (((x * z⁻¹ : (v.adicCompletion L)ˣ) : v.adicCompletion L) - 1) < 1 := by
      have e : ((x * z⁻¹ : (v.adicCompletion L)ˣ) : v.adicCompletion L) - 1 = (x - ζ) * ζ⁻¹ := by
        simp [z, sub_mul, h0]
      rw [e, map_mul, map_inv₀, hζ, inv_one, mul_one, Valuation.map_sub_swap]
      exact h2
    refine ⟨n, ?_⟩
    have h3 := hn _ (GlobalTheory.Mem.UnrAe.isUnitAt_pow hu (Ideal.absNorm v.asIdeal ^ n)) (by
      rw [Units.val_pow_eq_pow_val]
      exact val_pow_pow_sub_one_le _ (le_of_eq hu) hu1 (valued_absNorm_lt_one v) n)
    rwa [map_pow, map_mul, map_inv, hz, inv_one, mul_one] at h3

end GlobalTheory.Mem.WildChar
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuedEqOneOfLe
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.Mem.Chr
open Neutral.B1 hiding localIdele Ideles diagUnits
open ReciprocityTheory.Neutral.Bridge.HCFR hiding infIdele
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.Mem.TupHecke

section General

variable {L : Type} [Field L] [NumberField L]

abbrev FI (L : Type) [Field L] [NumberField L] : Type := (FiniteAdeleRing (𝓞 L) L)ˣ

def sing (P : HeightOneSpectrum (𝓞 L)) : (P.adicCompletion L)ˣ →* FI L := Units.map (finiteSingle L P)

def cmp (P : HeightOneSpectrum (𝓞 L)) : FI L →* (P.adicCompletion L)ˣ :=
  Units.map { toFun := fun a => a P, map_one' := rfl, map_mul' := fun _ _ => rfl }



variable (L) in
def finP : Ideles L →* FI L := Units.map (MonoidHom.snd (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L))

theorem cmp_val (P : HeightOneSpectrum (𝓞 L)) (u : FI L) :
    (cmp P u : P.adicCompletion L) = (u : FiniteAdeleRing (𝓞 L) L) P := rfl

open Classical in
theorem cmp_sing_self (P : HeightOneSpectrum (𝓞 L)) (x) : cmp P (sing P x) = x := by
  apply Units.ext
  show Function.update (fun w : HeightOneSpectrum (𝓞 L) => (1 : w.adicCompletion L)) P x P = x
  exact Function.update_self (β := fun w : HeightOneSpectrum (𝓞 L) => w.adicCompletion L) P _ _

open Classical in
theorem cmp_sing_ne {P Q : HeightOneSpectrum (𝓞 L)} (h : P ≠ Q) (x) : cmp P (sing Q x) = 1 := by
  apply Units.ext
  show Function.update (fun w : HeightOneSpectrum (𝓞 L) => (1 : w.adicCompletion L)) Q x P = 1
  exact Function.update_of_ne (β := fun w : HeightOneSpectrum (𝓞 L) => w.adicCompletion L) h _ _


theorem valued_eq_one_of_le {P : HeightOneSpectrum (𝓞 L)} (x : (P.adicCompletion L)ˣ)
    (h : Valued.v (x : P.adicCompletion L) ≤ 1) (h' : Valued.v ((x⁻¹ : (P.adicCompletion L)ˣ) : P.adicCompletion L) ≤ 1) :
    Valued.v (x : P.adicCompletion L) = 1 := by
  refine le_antisymm h ?_
  have e : Valued.v (x : P.adicCompletion L) * Valued.v ((x⁻¹ : (P.adicCompletion L)ˣ) : P.adicCompletion L) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  exact e.symm.le.trans (mul_le_of_le_one_right' h')

theorem finite_nonunit (u : FI L) : {P | ¬ IsUnitAt P (cmp P u)}.Finite := by
  have h1 := Filter.eventually_cofinite.1 (u : FiniteAdeleRing (𝓞 L) L).2
  have h2 := Filter.eventually_cofinite.1 ((u⁻¹ : FI L) : FiniteAdeleRing (𝓞 L) L).2
  refine (h1.union h2).subset fun P hP => ?_
  by_contra hn
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hn
  exact hP (valued_eq_one_of_le _ hn.1 hn.2)

theorem finite_nat {N : ℕ} (hN : 0 < N) :
    {P : HeightOneSpectrum (𝓞 L) | Valued.v (N : P.adicCompletion L) ≠ 1}.Finite := by
  refine (finite_nonunit (Units.map (algebraMap L (FiniteAdeleRing (𝓞 L) L)).toMonoidHom
    (Units.mk0 (N : L) (Nat.cast_ne_zero.2 hN.ne')))).subset fun P hP h => hP ?_
  rw [← map_natCast (algebraMap L (P.adicCompletion L))]
  exact h

def Cong (N : ℕ) (u : FI L) : Prop :=
  ∀ P, IsUnitAt P (cmp P u) ∧ Valued.v ((cmp P u : P.adicCompletion L) - 1) ≤ Valued.v (N : P.adicCompletion L)

variable {G : Type} [CommGroup G]

theorem cong_sing {N : ℕ} {P : HeightOneSpectrum (𝓞 L)} {x : (P.adicCompletion L)ˣ} (h : IsUnitAt P x)
    (h' : Valued.v ((x : P.adicCompletion L) - 1) ≤ Valued.v (N : P.adicCompletion L)) : Cong N (sing P x) := by
  intro Q
  by_cases e : Q = P
  · subst e
    rw [cmp_sing_self]
    exact ⟨h, h'⟩
  · rw [cmp_sing_ne e]
    simp [IsUnitAt]

theorem continuous_finP {N : ℕ} (hN : 0 < N) (ψ : FI L →* ℂˣ) (hψ : ∀ u, Cong N u → ψ u = 1) :
    Continuous (ψ.comp (finP L)) := by
  classical
  obtain ⟨T, hT⟩ : ∃ T : Finset (HeightOneSpectrum (𝓞 L)), ∀ P, P ∉ T → Valued.v (N : P.adicCompletion L) = 1 :=
    ⟨(finite_nat (L := L) hN).toFinset, fun P hP => by simpa using hP⟩
  choose n hn using fun P : HeightOneSpectrum (𝓞 L) =>
    GlobalTheory.Idele.exists_exp_neg_lt (GlobalTheory.AdLat.valued_natCast_ne_zero P hN)
  have ho := (GlobalTheory.Mem.UnitOpen.unit_open_and_congr_open L).2 T (T.sup n)
  have h1 := ho.mem_nhds (x := (1 : Ideles L)) ⟨one_mem _, fun v _ => by
    have : ((1 : Ideles L) : AdeleRing (𝓞 L) L).2 v = 1 := rfl
    rw [this, sub_self, map_zero]
    exact zero_le⟩
  have h2 : (fun _ => (1 : ℂˣ)) =ᶠ[nhds (1 : Ideles L)] (ψ.comp (finP L)) := by
    filter_upwards [h1] with a ha
    have hu : ∀ P, IsUnitAt P (cmp P (finP L a)) := ha.1
    refine (hψ (finP L a) fun P => ⟨hu P, ?_⟩).symm
    by_cases hP : P ∈ T
    · refine le_trans (ha.2 P hP) (le_trans ?_ (hn P).le)
      rw [WithZero.exp_le_exp]
      have := Finset.le_sup (f := n) hP
      omega
    · rw [hT P hP]
      exact Valuation.map_sub_le _ (hu P).le (by simp)
  exact continuous_of_continuousAt_one _ (continuousAt_const.congr h2)

end General

end GlobalTheory.Mem.TupHecke
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OrdSubDetSubSelfDual
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.Mem.Chr
open Neutral.B1 hiding localIdele Ideles diagUnits
open ReciprocityTheory.Neutral.Bridge.HCFR hiding infIdele

namespace GlobalTheory.Mem.Chr.DetSD

variable {L : Type} [Field L] [NumberField L]

theorem exists_det_ge {N : ℕ} (M : Submodule (𝓞 L) (Fin N → L)) (w : HeightOneSpectrum (𝓞 L)) (k : L) (hk0 : k ≠ 0)
    (hk : k ∈ detSub M) :
    ∃ x : Fin N → Fin N → L, (∀ i, x i ∈ M) ∧ w.valuation L k ≤ w.valuation L (Matrix.of x).det := by
  by_contra hn
  push Not at hn
  have h0 : w.valuation L k ≠ 0 := by simpa using hk0
  have key : ∀ z ∈ detSub M, w.valuation L z < w.valuation L k := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem d hd =>
      obtain ⟨x, hx, rfl⟩ := hd
      exact hn x hx
    | zero => rw [map_zero]; exact zero_lt_iff.2 h0
    | add x y _ _ hx hy => exact Valuation.map_add_lt _ hx hy
    | smul r x _ hx =>
      rw [Algebra.smul_def, map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_left' (w.valuation_le_one r)) hx
  exact lt_irrefl _ (key k hk)

theorem coord_le_one {N : ℕ} (M : Submodule (𝓞 L) (Fin N → L)) (w : HeightOneSpectrum (𝓞 L))
    (x : Fin N → Fin N → L) (hx : ∀ i, x i ∈ M) (hd : (Matrix.of x).det ≠ 0)
    (hmax : ∀ z ∈ detSub M, w.valuation L z ≤ w.valuation L (Matrix.of x).det) (m : Fin N → L) (hm : m ∈ M)
    (j : Fin N) : w.valuation L (Matrix.vecMul m (Matrix.of x)⁻¹ j) ≤ 1 := by
  have hu : IsUnit (Matrix.of x).det := IsUnit.mk0 _ hd
  have h1 := congrFun (Matrix.det_smul_inv_vecMul_eq_cramer_transpose (Matrix.of x) m hu) j
  rw [Matrix.cramer_transpose_apply] at h1
  have h2 : ((Matrix.of x).updateRow j m).det ∈ detSub M := by
    refine det_mem_detSub (Function.update x j m) fun i => ?_
    by_cases h : i = j
    · subst h; simpa using hm
    · simpa [Function.update_of_ne h] using hx i
  have h3 := hmax _ h2
  rw [← h1, Pi.smul_apply, smul_eq_mul, map_mul] at h3
  have h0 : 0 < w.valuation L (Matrix.of x).det := zero_lt_iff.2 (by simpa using hd)
  exact (mul_le_iff_le_one_right h0).1 h3

theorem exists_den_prime {V : Type} [AddCommGroup V] [Module (𝓞 L) V] {N : ℕ} (M : Submodule (𝓞 L) V) (hM : M.FG)
    (w : HeightOneSpectrum (𝓞 L)) (f : Fin N → V → L) (hadd : ∀ j x y, f j (x + y) = f j x + f j y)
    (hsm : ∀ j (r : 𝓞 L) x, ∃ r' : 𝓞 L, f j (r • x) = r' • f j x)
    (hf : ∀ j, ∀ m ∈ M, w.valuation L (f j m) ≤ 1) :
    ∃ s : 𝓞 L, s ∉ w.asIdeal ∧ ∀ j, ∀ m ∈ M, (s : L) * f j m ∈ (algebraMap (𝓞 L) L).range := by
  classical
  obtain ⟨t, rfl⟩ := hM
  have := w.isPrime
  choose n d h using fun p : Fin N × t => w.exists_primeCompl_mul_eq_of_integer (f p.1 p.2)
    (hf p.1 p.2 (Submodule.subset_span p.2.2))
  refine ⟨((∏ p, d p : w.asIdeal.primeCompl) : 𝓞 L), (∏ p, d p).2, fun j m hm => ?_⟩
  induction hm using Submodule.span_induction with
  | mem x hx =>
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ (j, (⟨x, hx⟩ : t)))]
    refine ⟨((∏ p ∈ Finset.univ.erase (j, (⟨x, hx⟩ : t)), d p : w.asIdeal.primeCompl) : 𝓞 L) * n (j, ⟨x, hx⟩), ?_⟩
    rw [map_mul, ← h]
    simp only [Submonoid.coe_mul]
    push_cast
    simp only [RingOfIntegers.coe_eq_algebraMap]
    ring
  | zero =>
    obtain ⟨r, hr⟩ := hsm j 0 0
    have h0 : f j 0 = 0 := by simpa using hadd j 0 0
    rw [h0, mul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [hadd, mul_add]; exact add_mem hx hy
  | smul r x _ hx =>
    obtain ⟨r', hr⟩ := hsm j r x
    rw [hr, Algebra.smul_def, mul_left_comm]
    exact mul_mem ⟨r', rfl⟩ hx

variable [StarRing L]

theorem star_integer (r : 𝓞 L) : ∃ r' : 𝓞 L, (r' : L) = star (r : L) :=
  ⟨RingOfIntegers.mapRingEquiv (starRingAut : RingAut L) r, rfl⟩

theorem star_mul_integer {N : ℕ} (M : Submodule (𝓞 L) (Fin N → L))
    (hM : ∀ y ∈ M, ∀ x ∈ M, stdH L N x y ∈ (algebraMap (𝓞 L) L).range) (a b : L) (ha : a ∈ detSub M)
    (hb : b ∈ detSub M) : star a * b ∈ (algebraMap (𝓞 L) L).range := by
  induction ha using Submodule.span_induction with
  | mem d hd =>
    obtain ⟨x, hx, rfl⟩ := hd
    induction hb using Submodule.span_induction with
    | mem d hd =>
      obtain ⟨y, hy, rfl⟩ := hd
      have e : star (Matrix.of x).det * (Matrix.of y).det = (Matrix.of fun i j => stdH L N (x j) (y i)).det := by
        rw [← Matrix.det_conjTranspose, mul_comm, ← Matrix.det_mul]
        congr 1
        ext i j
        simp [Matrix.mul_apply, stdH, mul_comm]
      rw [e]
      exact Formalism.L2.LamCM.A2.isInteger_det _ fun i j => hM _ (hy i) _ (hx j)
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
    | smul r x _ hx => rw [Algebra.smul_def, mul_left_comm]; exact mul_mem ⟨r, rfl⟩ hx
  | zero => simp
  | add x y _ _ hx hy => rw [star_add, add_mul]; exact add_mem hx hy
  | smul r x _ hx =>
    obtain ⟨r', hr⟩ := star_integer r
    rw [Algebra.smul_def, star_mul', mul_assoc]
    exact mul_mem ⟨r', hr⟩ hx

theorem ordSub_add_eq_zero {N : ℕ} (M : Submodule (𝓞 L) (Fin N → L)) (hM : IsSDLat L N M)
    (w w' : HeightOneSpectrum (𝓞 L)) (hw : ∀ x : L, w'.valuation L (star x) = w.valuation L x) :
    ordSub w (detSub M) + ordSub w' (detSub M) = 0 := by
  obtain ⟨hfg, hsp, hsd⟩ := hM
  have hl := (ordSub_detSub_lattice L N M hfg hsp).2.1
  obtain ⟨⟨k, hk, ek⟩, hkl⟩ := hl w
  obtain ⟨⟨k', hk', ek'⟩, hkl'⟩ := hl w'
  have nz : ∀ (v : HeightOneSpectrum (𝓞 L)) (a : Lˣ), v.valuation L (a : L) ≠ 0 := fun v a => by simp
  apply le_antisymm
  · obtain ⟨x, hx, hxk⟩ := exists_det_ge M w k k.ne_zero hk
    have hd : (Matrix.of x).det ≠ 0 := by
      intro h
      rw [h, map_zero] at hxk
      exact nz w k (le_zero_iff.1 hxk)
    have hmax : ∀ z ∈ detSub M, w.valuation L z ≤ w.valuation L k := by
      intro z hz
      by_cases h0 : z = 0
      · simp [h0]
      · have h1 := hkl ⟨Units.mk0 z h0, hz, rfl⟩
        rw [← ek] at h1
        exact (WithZero.log_le_log (nz w (Units.mk0 z h0)) (nz w k)).1 (neg_le_neg_iff.1 h1)
    have hdk : w.valuation L (Matrix.of x).det = w.valuation L k := le_antisymm (hmax _ (det_mem_detSub x hx)) hxk
    have hc := coord_le_one M w x hx hd (fun z hz => hdk ▸ hmax z hz)
    set Y : Matrix (Fin N) (Fin N) L := ((Matrix.of x)⁻¹).conjTranspose with hY
    have hf : ∀ j m, stdH L N m (Y j) = star (Matrix.vecMul m (Matrix.of x)⁻¹ j) := by
      intro j m
      simp [stdH, hY, Matrix.vecMul, dotProduct]
    obtain ⟨s, hs, hint⟩ := exists_den_prime M hfg w' (fun j m => stdH L N m (Y j))
      (fun j a b => by simp [stdH, add_mul, Finset.sum_add_distrib])
      (fun j r a => by
        obtain ⟨r', hr⟩ := star_integer r
        refine ⟨r', ?_⟩
        have hr' : algebraMap (𝓞 L) L r' = star (algebraMap (𝓞 L) L r) := hr
        simp [stdH, Algebra.smul_def, hr', Finset.mul_sum, mul_assoc])
      (fun j m hm => by
        show w'.valuation L (stdH L N m (Y j)) ≤ 1
        rw [hf, hw]; exact hc m hm j)
    have hsY : ∀ j, ((s : L) • Y) j ∈ M := fun j => (hsd _).2 fun m hm => by
      have := hint j m hm
      convert this using 1
      simp [stdH, Finset.mul_sum, mul_left_comm]
    have hmem : ((s : L) • Y).det ∈ detSub M := det_mem_detSub (fun j => ((s : L) • Y) j) hsY
    have hsv : w'.valuation L (s : L) = 1 :=
      le_antisymm (w'.valuation_le_one s) (not_lt.1 fun h => hs ((w'.valuation_lt_one_iff_mem s).1 h))
    have hval : w'.valuation L ((s : L) • Y).det = (w.valuation L k)⁻¹ := by
      rw [Matrix.det_smul, map_mul, map_pow, hsv, one_pow, one_mul, hY, Matrix.det_conjTranspose, hw,
        Matrix.det_nonsing_inv, Ring.inverse_eq_inv', map_inv₀, hdk]
    have h0 : ((s : L) • Y).det ≠ 0 := by
      intro h
      rw [h, map_zero] at hval
      exact inv_ne_zero (nz w k) hval.symm
    have h1 := hkl' ⟨Units.mk0 _ h0, hmem, rfl⟩
    have h2 : ordF w' (Units.mk0 _ h0) = -ordF w k := by
      unfold ordF
      rw [Units.val_mk0, hval, WithZero.log_inv]
    omega
  · have h1 := star_mul_integer M (fun y hy => (hsd y).1 hy) k k' hk hk'
    have h2 := DetOrd.ordF_nonneg_of_isInteger w' (star k * k') h1
    rw [DetOrd.ordF_mul'] at h2
    have h3 : ordF w' (star k) = ordF w k := by
      unfold ordF
      rw [Units.coe_star, hw]
    omega

end GlobalTheory.Mem.Chr.DetSD

namespace GlobalTheory.Mem.Chr


open Classical in
theorem ordSub_detSub_selfDual : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (N : ℕ), letI := H.cmStar; ∀ (M : SDLat H.E N) (w w' : HeightOneSpectrum (𝓞 H.E)), IsConjPl H w w' → ordSub w (detSub M.1) + ordSub w' (detSub M.1) = 0 := by
  intro R H N
  letI := H.cmStar
  intro M w w' h
  have hc : ConjPl H.conj.toRingEquiv w w' := (conjPl_main.2.1 R H w w').1 h
  refine DetSD.ordSub_add_eq_zero M.1 M.2 w w' fun x => ?_
  have := H.isCMField_hostE
  have e : star x = H.conj x :=
    H.φ₀.injective ((NumberField.IsCMField.complexEmbedding_complexConj _ H.φ₀ x).trans
      (H.conjE_apply H.φ₀ x).symm)
  rw [e]
  exact hc x

end GlobalTheory.Mem.Chr
end
end
