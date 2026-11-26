module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GKeyFin
public import Formalism.LocalToGlobal.FiniteTOf
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ClassSumPin

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharTrivialOnCongruenceUnitIdeles
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharTrivialOnCongruenceUnitIdeles
noncomputable section

open IsDedekindDomain NumberField Filter Topology

namespace GlobalTheory.LevelChars.LevTriv

open Neutral.B1 _root_.Formalism.L2.Host

variable {L : Type} [Field L] [NumberField L]


open Classical in
theorem prod_localIdele_comp (z : ∀ v : HeightOneSpectrum (𝓞 L), (v.adicCompletion L)ˣ)
    (F : Finset (HeightOneSpectrum (𝓞 L))) :
    ((∏ v ∈ F, localIdele L v (z v) : Ideles L) : AdeleRing (𝓞 L) L).1 = 1 ∧
    ∀ w, ((∏ v ∈ F, localIdele L v (z v) : Ideles L) : AdeleRing (𝓞 L) L).2 w =
      if w ∈ F then ((z w : (w.adicCompletion L)ˣ) : w.adicCompletion L) else 1 := by
  classical
  induction F using Finset.induction_on with
  | empty => exact ⟨rfl, fun w => by simp⟩
  | insert a F ha ih =>
    rw [Finset.prod_insert ha, Units.val_mul]
    have e1 : ∀ x y : AdeleRing (𝓞 L) L, (x * y).1 = x.1 * y.1 := fun _ _ => rfl
    have e2 : ∀ x y : AdeleRing (𝓞 L) L, (x * y).2 = x.2 * y.2 := fun _ _ => rfl
    refine ⟨?_, fun w => ?_⟩
    · rw [e1, ih.1, mul_one]; rfl
    · have e : ∀ x y : FiniteAdeleRing (𝓞 L) L, (x * y) w = x w * y w := fun _ _ => rfl
      rw [e2, e, ih.2 w]
      by_cases hw : w = a
      · subst hw
        rw [localIdele_snd_self, if_neg ha, if_pos (Finset.mem_insert_self _ _), mul_one]
      · rw [(localIdele_isSupportedAt L a (z a)).2 w hw, one_mul]
        by_cases hF : w ∈ F
        · rw [if_pos hF, if_pos (Finset.mem_insert_of_mem hF)]
        · rw [if_neg hF, if_neg (fun h => (Finset.mem_insert.1 h).elim hw hF)]

theorem tendsto_prod_localIdele (z : ∀ v : HeightOneSpectrum (𝓞 L), (v.adicCompletion L)ˣ) (hz : ∀ v, IsUnitAt v (z v))
    (c : Ideles L) (hc1 : (c : AdeleRing (𝓞 L) L).1 = 1)
    (hc2 : ∀ v, (c : AdeleRing (𝓞 L) L).2 v = ((z v : (v.adicCompletion L)ˣ) : v.adicCompletion L)) :
    Tendsto (fun F : Finset (HeightOneSpectrum (𝓞 L)) => ((∏ v ∈ F, localIdele L v (z v) : Ideles L) : AdeleRing (𝓞 L) L))
      atTop (𝓝 (c : AdeleRing (𝓞 L) L)) := by
  classical
  let A : ∀ w : HeightOneSpectrum (𝓞 L), Set (w.adicCompletion L) := fun w => w.adicCompletionIntegers L
  have hA : ∀ w, ((z w : (w.adicCompletion L)ˣ) : w.adicCompletion L) ∈ A w := fun w => (hz w).le
  let g : Finset (HeightOneSpectrum (𝓞 L)) → ∀ w, A w := fun F w =>
    if w ∈ F then ⟨_, hA w⟩ else ⟨1, one_mem (w.adicCompletionIntegers L)⟩
  let o : ∀ w, A w := fun w => ⟨_, hA w⟩
  have hg : Tendsto g atTop (𝓝 o) := by
    rw [tendsto_pi_nhds]
    intro w
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop {w}] with F hF
    have hw : w ∈ F := hF (Finset.mem_singleton_self w)
    simp only [g, o, if_pos hw]
  have h2 := ((RestrictedProduct.isEmbedding_structureMap (A := A) (𝓕 := cofinite)).continuous.tendsto o).comp hg
  have h3 : Tendsto (fun F : Finset (HeightOneSpectrum (𝓞 L)) =>
      ((∏ v ∈ F, localIdele L v (z v) : Ideles L) : AdeleRing (𝓞 L) L).2) atTop (𝓝 (c : AdeleRing (𝓞 L) L).2) := by
    have eo : RestrictedProduct.structureMap _ A cofinite o = (c : AdeleRing (𝓞 L) L).2 := by
      apply Subtype.ext; funext w; exact (hc2 w).symm
    rw [← eo]
    refine Tendsto.congr (fun F => ?_) h2
    apply Subtype.ext; funext w
    show ((g F w : A w) : w.adicCompletion L) = _
    refine Eq.trans ?_ ((prod_localIdele_comp z F).2 w).symm
    by_cases hw : w ∈ F
    · simp only [g, if_pos hw]
    · simp only [g, if_neg hw]
  have h4 := (tendsto_const_nhds (x := (1 : InfiniteAdeleRing L))).prodMk_nhds h3
  have ec : (c : AdeleRing (𝓞 L) L) = ((1 : InfiniteAdeleRing L), (c : AdeleRing (𝓞 L) L).2) := Prod.ext hc1 rfl
  rw [ec]
  refine Tendsto.congr (fun F => ?_) h4
  exact Prod.ext (prod_localIdele_comp z F).1.symm rfl

theorem eq_one_fin (S : Set (HeightOneSpectrum (𝓞 L))) (N : ℕ) (ψ : HChar L) (hU : ∀ v, v ∉ S → ψ.UnrAt v)
    (hN : ∀ v ∈ S, ψ.LevelLe v N) (f : Ideles L) (hf1 : (f : AdeleRing (𝓞 L) L).1 = 1)
    (hf : f ∈ GlobalTheory.LevelChars.levSub L S N) : ψ.1 f = 1 := by
  classical
  let u : ∀ v : HeightOneSpectrum (𝓞 L), (v.adicCompletion L)ˣ := fun v =>
    ⟨(f : AdeleRing (𝓞 L) L).2 v, ((f⁻¹ : Ideles L) : AdeleRing (𝓞 L) L).2 v,
      congrArg (fun y : AdeleRing (𝓞 L) L => y.2 v) f.mul_inv,
      congrArg (fun y : AdeleRing (𝓞 L) L => y.2 v) f.inv_mul⟩
  have hu : ∀ v, IsUnitAt v (u v) := fun v => (hf v).1
  have hui : ∀ v, IsUnitAt v (u v)⁻¹ := fun v => by
    unfold IsUnitAt
    rw [Units.val_inv_eq_inv_val, map_inv₀, hu v, inv_one]
  have hloc : ∀ v, ψ.1 (localIdele L v (u v)) = 1 := fun v => by
    by_cases hv : v ∈ S
    · exact hN v hv (u v) (hu v) ((hf v).2 hv)
    · exact hU v hv (u v) (hu v)
  let b : Finset (HeightOneSpectrum (𝓞 L)) → Ideles L := fun F => ∏ v ∈ F, localIdele L v (u v)
  have hb1 : ∀ F, ψ.1 (b F) = 1 := fun F => by
    simp only [b, map_prod]
    exact Finset.prod_eq_one fun v _ => hloc v
  have hfi1 : ((f⁻¹ : Ideles L) : AdeleRing (𝓞 L) L).1 = 1 := by
    have h := congrArg (fun y : AdeleRing (𝓞 L) L => y.1) f.inv_mul
    have e1 : ∀ x y : AdeleRing (𝓞 L) L, (x * y).1 = x.1 * y.1 := fun _ _ => rfl
    simp only [e1, hf1, mul_one] at h
    exact h
  have t1 := tendsto_prod_localIdele u hu f hf1 fun v => rfl
  have t2 := tendsto_prod_localIdele (fun v => (u v)⁻¹) hui f⁻¹ hfi1 fun v => rfl
  have tb : Tendsto b atTop (𝓝 f) := by
    rw [Units.isEmbedding_embedProduct.tendsto_nhds_iff]
    refine t1.prodMk_nhds ((MulOpposite.continuous_op.tendsto _).comp (Tendsto.congr (fun F => ?_) t2))
    show ((∏ v ∈ F, localIdele L v (u v)⁻¹ : Ideles L) : AdeleRing (𝓞 L) L) = (((b F)⁻¹ : Ideles L) : AdeleRing (𝓞 L) L)
    congr 1
    simp only [b, map_inv, Finset.prod_inv_distrib]
  have t3 := (ψ.2.1.tendsto f).comp tb
  have t4 : Tendsto (ψ.1 ∘ b) atTop (𝓝 1) := tendsto_const_nhds.congr fun F => (hb1 F).symm
  exact tendsto_nhds_unique t3 t4

theorem infIdele_mem (S : Set (HeightOneSpectrum (𝓞 L))) (N : ℕ) (x : (InfiniteAdeleRing L)ˣ) :
    GlobalTheory.HeckeSplit.infIdele L x ∈ GlobalTheory.LevelChars.levSub L S N := fun v => by
  have e : GlobalTheory.LevelChars.compAt L v (GlobalTheory.HeckeSplit.infIdele L x) = 1 := rfl
  refine ⟨by rw [e, map_one], fun _ => ?_⟩
  rw [e, sub_self, map_zero]
  exact zero_le

theorem infDiag_eq_infIdele (k : Lˣ) :
    infDiag k = GlobalTheory.HeckeSplit.infIdele L (Units.map (algebraMap L (InfiniteAdeleRing L)).toMonoidHom k) := by
  classical
  apply Units.ext
  show ((infDiag k : Ideles L) : AdeleRing (𝓞 L) L) = (algebraMap L (InfiniteAdeleRing L) k, 1)
  unfold infDiag
  rw [MonoidHom.finsetProd_apply, Units.coe_prod]
  let ι : (∀ w : InfinitePlace L, w.Completion) →* AdeleRing (𝓞 L) L :=
    MonoidHom.inl (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L)
  change ∏ w : InfinitePlace L, ι (Pi.mulSingle w (algebraMap L w.Completion k)) =
    ι (fun w => algebraMap L w.Completion k)
  rw [← map_prod, Finset.univ_prod_mulSingle]

theorem eq_one_inf (ψ : HChar L) (hinf : ∀ k : Lˣ, ψ.inf k = 1) (x : (InfiniteAdeleRing L)ˣ) :
    ψ.1 (GlobalTheory.HeckeSplit.infIdele L x) = 1 := by
  have hc : Continuous (GlobalTheory.HeckeSplit.infIdele L) :=
    Continuous.units_map _ (continuous_id.prodMk continuous_const)
  refine (GlobalTheory.HeckeGal.denseRange_units_inf L).induction_on x
    (isClosed_eq (ψ.2.1.comp hc) continuous_const) fun k => ?_
  rw [← infDiag_eq_infIdele]
  exact hinf k

theorem levSub_triv : ∀ (L : Type) [Field L] [NumberField L] (S : Set (HeightOneSpectrum (𝓞 L))) (N : ℕ)
    (ψ : Formalism.L2.Host.HChar L), (∀ k : Lˣ, ψ.inf k = 1) → (∀ v, v ∉ S → ψ.UnrAt v) → (∀ v ∈ S, ψ.LevelLe v N) →
    ∀ a ∈ GlobalTheory.LevelChars.levSub L S N, ψ.1 a = 1 := by
  intro L _ _ S N ψ hinf hU hN a ha
  set x := GlobalTheory.HeckeSplit.infPart L a
  have hdec : a = GlobalTheory.HeckeSplit.infIdele L x * ((GlobalTheory.HeckeSplit.infIdele L x)⁻¹ * a) := by
    rw [mul_inv_cancel_left]
  have hf1 : (((GlobalTheory.HeckeSplit.infIdele L x)⁻¹ * a : Ideles L) : AdeleRing (𝓞 L) L).1 = 1 := by
    rw [← map_inv]
    show ((a⁻¹ : Ideles L) : AdeleRing (𝓞 L) L).1 * (a : AdeleRing (𝓞 L) L).1 = 1
    have h := congrArg (fun y : AdeleRing (𝓞 L) L => y.1) a.inv_mul
    exact h
  have hmem : (GlobalTheory.HeckeSplit.infIdele L x)⁻¹ * a ∈ GlobalTheory.LevelChars.levSub L S N :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ (infIdele_mem S N x)) ha
  rw [hdec, map_mul, eq_one_inf ψ hinf x, eq_one_fin S N ψ hU hN _ hf1 hmem, mul_one]

end GlobalTheory.LevelChars.LevTriv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharTrivialOnCongruenceUnitIdelesStatement
open IsDedekindDomain NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeChar_trivial_on_congruenceUnitIdeles : ∀ (L : Type) [Field L] [NumberField L] (S : Set (HeightOneSpectrum (𝓞 L))) (N : ℕ) (ψ : Formalism.L2.Host.HChar L), (∀ k : Lˣ, ψ.inf k = 1) → (∀ v, v ∉ S → ψ.UnrAt v) → (∀ v ∈ S, ψ.LevelLe v N) → ∀ a ∈ GlobalTheory.LevelChars.levSub L S N, ψ.1 a = 1 := by
  first | exact @GlobalTheory.LevelChars.LevTriv.levSub_triv | exact GlobalTheory.LevelChars.LevTriv.levSub_triv | (intros; apply GlobalTheory.LevelChars.LevTriv.levSub_triv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RayClassGroupIdelicFiniteIndex
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RayClassGroupIdelicFiniteIndex
open IsDedekindDomain NumberField

namespace GlobalTheory.LevelChars

theorem exists_finset_close (L : Type) [Field L] [NumberField L] (v : HeightOneSpectrum (𝓞 L)) (N : ℕ) :
    ∃ F : Finset (v.adicCompletion L), ∀ x : v.adicCompletion L, Valued.v x ≤ 1 →
      ∃ f ∈ F, Valued.v (x - f) ≤ WithZero.exp (-(N : ℤ)) := by
  classical
  obtain ⟨π, hπ⟩ := HeightOneSpectrum.valuation_exists_uniformizer L v
  set s : v.adicCompletion L := ((π ^ N : L) : v.adicCompletion L) with hsdef
  have hs : Valued.v s = WithZero.exp (-(N : ℤ)) := by
    rw [hsdef, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', map_pow, hπ, ← WithZero.exp_nsmul]
    congr 1
    simp
  have hball : IsOpen {y : v.adicCompletion L | Valued.v y < Valued.v s} := by
    have h := Valued.isOpen_ball (v.adicCompletion L) (Valued.v.restrict s)
    simpa [Valuation.restrict_lt_iff] using h
  obtain ⟨t, -, ht⟩ := (PI.IntAdCpctOpenWork.isCompact_adicCompletionIntegers (F := L) v).elim_nhds_subcover
    (fun x => {y | Valued.v (y - x) < Valued.v s})
    (fun x _ => (hball.preimage (continuous_id.sub continuous_const)).mem_nhds (by
      show Valued.v (x - x) < Valued.v s
      rw [sub_self, map_zero, hs]
      exact zero_lt_iff.2 WithZero.exp_ne_zero))
  refine ⟨t, fun x hx => ?_⟩
  have hxO : x ∈ (v.adicCompletionIntegers L : Set (v.adicCompletion L)) :=
    by rw [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers]; exact hx
  obtain ⟨f, hf, hxf⟩ := Set.mem_iUnion₂.1 (ht hxO)
  exact ⟨f, hf, le_of_lt (hs ▸ hxf)⟩

end GlobalTheory.LevelChars

namespace GlobalTheory.LevelChars

theorem relIndex_levSub_ne_zero (L : Type) [Field L] [NumberField L] (S : Set (HeightOneSpectrum (𝓞 L))) (N : ℕ)
    (hS : S.Finite) : (levSub L S N).relIndex (levSub L ∅ 0) ≠ 0 := by
  classical
  haveI : Finite S := hS.to_subtype
  choose F hF using fun v : S => exists_finset_close L v.1 N
  have hint : ∀ a : levSub L ∅ 0, ∀ v, Valued.v (compAt L v (a : (AdeleRing (𝓞 L) L)ˣ)) ≤ 1 :=
    fun a v => le_of_eq (a.2 v).1
  choose g hg hg' using fun (a : levSub L ∅ 0) (v : S) => hF v (compAt L v.1 a) (hint a v.1)
  let φ : levSub L ∅ 0 ⧸ (levSub L S N).subgroupOf (levSub L ∅ 0) → ((v : S) → (F v : Set (v.1.adicCompletion L))) :=
    fun q v => ⟨g q.out v, hg q.out v⟩
  have hφ : Function.Injective φ := by
    intro q q' hqq
    rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q', QuotientGroup.eq, Subgroup.mem_subgroupOf]
    intro w
    refine ⟨((q.out⁻¹ * q'.out).2 w).1, fun hw => ?_⟩
    have e1 : g q.out ⟨w, hw⟩ = g q'.out ⟨w, hw⟩ := congrArg Subtype.val (congrFun hqq ⟨w, hw⟩)
    have h1 := hg' q.out ⟨w, hw⟩
    have h2 := hg' q'.out ⟨w, hw⟩
    rw [e1] at h1
    set a : (AdeleRing (𝓞 L) L)ˣ := (q.out : (AdeleRing (𝓞 L) L)ˣ)
    set b : (AdeleRing (𝓞 L) L)ˣ := (q'.out : (AdeleRing (𝓞 L) L)ˣ)
    have hinv : Valued.v (compAt L w a⁻¹) = 1 := ((q.out⁻¹).2 w).1
    have hc : compAt L w a⁻¹ * compAt L w a = 1 := by rw [← compAt_mul, inv_mul_cancel, compAt_one]
    have e2 : compAt L w ((q.out⁻¹ * q'.out : levSub L ∅ 0) : (AdeleRing (𝓞 L) L)ˣ) - 1 =
        compAt L w a⁻¹ * ((compAt L w b - g q'.out ⟨w, hw⟩) - (compAt L w a - g q'.out ⟨w, hw⟩)) := by
      have : ((q.out⁻¹ * q'.out : levSub L ∅ 0) : (AdeleRing (𝓞 L) L)ˣ) = a⁻¹ * b := rfl
      rw [this, compAt_mul]
      linear_combination hc
    rw [e2, map_mul, hinv, one_mul]
    exact (Valuation.map_sub _ _ _).trans (max_le h2 h1)
  haveI : Finite (levSub L ∅ 0 ⧸ (levSub L S N).subgroupOf (levSub L ∅ 0)) := Finite.of_injective φ hφ
  exact Subgroup.index_ne_zero_of_finite

end GlobalTheory.LevelChars

namespace GlobalTheory.LevelChars

theorem levSub_le_levSub_empty (L : Type) [Field L] [NumberField L] (S : Set (HeightOneSpectrum (𝓞 L))) (N : ℕ) :
    levSub L S N ≤ levSub L ∅ 0 := fun a ha v => ⟨(ha v).1, fun h => absurd h (Set.notMem_empty v)⟩

theorem finiteIndex_range_sup_levSub_empty (L : Type) [Field L] [NumberField L] :
    ((Units.map (algebraMap L (AdeleRing (𝓞 L) L)).toMonoidHom).range ⊔ levSub L ∅ 0).FiniteIndex := by
  classical
  haveI : Finite (ReciprocityTheory.Neutral.Bridge.HCFR.classOf L).range := inferInstance
  haveI := Subgroup.finiteIndex_ker (ReciprocityTheory.Neutral.Bridge.HCFR.classOf L)
  refine Subgroup.finiteIndex_of_le (H := (ReciprocityTheory.Neutral.Bridge.HCFR.classOf L).ker) ?_
  intro a ha
  obtain ⟨k, u, hu, rfl⟩ := (ReciprocityTheory.Neutral.Bridge.HCFR.classOf_eq_one_iff L a).1 ha
  refine Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨k, rfl⟩) (Subgroup.mem_sup_right ?_)
  exact fun v => ⟨(ReciprocityTheory.Neutral.Bridge.HCFR.rayUnits_top_iff L u).1 hu v, fun h => absurd h (Set.notMem_empty v)⟩

theorem finiteIndex_range_sup_levSub (L : Type) [Field L] [NumberField L] (S : Set (HeightOneSpectrum (𝓞 L))) (N : ℕ)
    (hS : S.Finite) :
    ((Units.map (algebraMap L (AdeleRing (𝓞 L) L)).toMonoidHom).range ⊔ levSub L S N).FiniteIndex := by
  set R := (Units.map (algebraMap L (AdeleRing (𝓞 L) L)).toMonoidHom).range
  have hle := levSub_le_levSub_empty L S N
  haveI := finiteIndex_range_sup_levSub_empty L
  have hT : R ⊔ levSub L S N ≤ R ⊔ levSub L ∅ 0 := sup_le_sup_left hle _
  have h1 : (R ⊔ levSub L S N).relIndex (levSub L ∅ 0) ≠ 0 := by
    intro h0
    have hd : (R ⊔ levSub L S N).relIndex (levSub L ∅ 0) ∣ (levSub L S N).relIndex (levSub L ∅ 0) :=
      Subgroup.relIndex_dvd_of_le_left (levSub L ∅ 0) le_sup_right
    rw [h0] at hd
    exact relIndex_levSub_ne_zero L S N hS (Nat.eq_zero_of_zero_dvd hd)
  have h2 : R ⊔ levSub L S N ⊔ levSub L ∅ 0 = R ⊔ levSub L ∅ 0 := by
    rw [sup_assoc, sup_eq_right.2 hle]
  have h3 : (R ⊔ levSub L S N).relIndex (R ⊔ levSub L ∅ 0) ≠ 0 := by
    rw [← h2, Subgroup.relIndex_sup_left]; exact h1
  rw [Subgroup.finiteIndex_iff, ← Subgroup.relIndex_mul_index hT]
  exact mul_ne_zero h3 (Subgroup.FiniteIndex.index_ne_zero)

theorem rayClass_finite : ∀ (L : Type) [Field L] [NumberField L] (S : Set (HeightOneSpectrum (𝓞 L))) (N : ℕ), S.Finite →
    ((Units.map (algebraMap L (AdeleRing (𝓞 L) L)).toMonoidHom).range ⊔ GlobalTheory.LevelChars.levSub L S N).FiniteIndex :=
  fun L _ _ S N hS => finiteIndex_range_sup_levSub L S N hS

end GlobalTheory.LevelChars
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RayClassGroupIdelicFiniteIndexStatement
open IsDedekindDomain NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rayClassGroup_idelic_finiteIndex : ∀ (L : Type) [Field L] [NumberField L] (S : Set (HeightOneSpectrum (𝓞 L))) (N : ℕ), S.Finite → ((Units.map (algebraMap L (AdeleRing (𝓞 L) L)).toMonoidHom).range ⊔ GlobalTheory.LevelChars.levSub L S N).FiniteIndex := by
  first | exact @GlobalTheory.LevelChars.rayClass_finite | exact GlobalTheory.LevelChars.rayClass_finite | (intros; apply GlobalTheory.LevelChars.rayClass_finite <;> assumption)
end
end

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.RowEx GlobalTheory.Mem.LiteralAutomorphy
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open IsDedekindDomain NumberField

namespace GlobalTheory.Mem.LiteralAutomorphy

theorem heckeFin : ∀ (L : Type) [Field L] [NumberField L] (I : Type) [Fintype I] (φ : I → L →+* ℂ) (n : I → ℤ)
    (S : Set (HeightOneSpectrum (𝓞 L))) (N : ℕ), S.Finite →
    {χ : Formalism.L2.Host.HChar L | χ.HasInf φ n ∧ (∀ v, v ∉ S → χ.UnrAt v) ∧ ∀ v ∈ S, χ.LevelLe v N}.Finite :=
  GlobalTheory.LevelChars.heckeFin_of GlobalTheory.T.heckeChar_trivial_on_congruenceUnitIdeles GlobalTheory.T.rayClassGroup_idelic_finiteIndex

namespace KeyFiniteness

theorem levelLe_one_two {L : Type} [Field L] [NumberField L] {χ : Formalism.L2.Host.HChar L} {v : HeightOneSpectrum (𝓞 L)}
    (h : χ.LevelLe v 1) : χ.LevelLe v 2 := fun x hx hle =>
  h x hx (hle.trans (WithZero.exp_le_exp.2 (by norm_num)))

def Sv (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) : Set (HeightOneSpectrum (𝓞 D.host.E)) :=
  {PP | (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) = v ∨ (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ∈ GlobalTheory.ChiGrid.S1 D}

def CS (D : D7) (c : ℝ) (v : HeightOneSpectrum (𝓞 D.host.F)) (a : Fin D.R.m) : Set (Formalism.L2.Host.HChar D.host.E) :=
  {χ | χ.HasInf (Formalism.L2.Host.embTau D) (fun τ => 2 * GlobalTheory.ChiGrid.cen D c τ (a.1 + 1)) ∧
      (∀ PP, PP ∉ Sv D v → χ.UnrAt PP) ∧ ∀ PP ∈ Sv D v, χ.LevelLe PP 2}

def Q0 (D : D7) : Set (HeightOneSpectrum (𝓞 D.host.F)) := {v | ((GlobalTheory.ChiGrid.q0 D : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal}

def KS (D : D7) (c : ℝ) : Set (HeightOneSpectrum (𝓞 D.host.F) × HeightOneSpectrum (𝓞 D.host.E) × (Fin D.R.m → Formalism.L2.Host.HChar D.host.E)) :=
  ⋃ v ∈ Q0 D, {v} ×ˢ ({w | w.under (𝓞 D.host.F) = v} ×ˢ Set.pi Set.univ (CS D c v))

theorem KS_finite (D : D7) (c : ℝ) : (KS D c).Finite := by
  classical
  have hQ0 : (Q0 D).Finite := by
    refine (Formalism.L2.DIV.primesOf ((GlobalTheory.ChiGrid.q0 D : ℕ) : 𝓞 D.host.F)).finite_toSet.subset fun v hv => ?_
    exact Formalism.L2.DIV.mem_primesOf.2 ⟨Nat.cast_ne_zero.2 (GlobalTheory.ChiGrid.leastSplitAuxiliaryPrimeThetaChain_spec D).1.ne_zero, hv⟩
  have hSv : ∀ v, (Sv D v).Finite := fun v => by
    refine ((Formalism.L2.Host.finite_aboveF (L := D.host.E) D.host.F v).union
      ((GlobalTheory.ChiGrid.S1 D).finite_toSet.biUnion fun u _ => Formalism.L2.Host.finite_aboveF (L := D.host.E) D.host.F u)).subset ?_
    rintro PP (h | h)
    · exact Or.inl h
    · exact Or.inr (Set.mem_biUnion (Finset.mem_coe.2 h) rfl)
  exact hQ0.biUnion fun v _ => (Set.finite_singleton v).prod
    ((Formalism.L2.Host.finite_aboveF (L := D.host.E) D.host.F v).prod
      (Set.Finite.pi fun a => heckeFin _ _ _ _ _ 2 (hSv v)))

theorem mem_KS {X : Stages} {T : Type} {L : Formalism.IndefR.Links.LevCh X.toD7 T} {sc : GlobalTheory.ChiGrid.Consts}
    (G : GlobalTheory.ChiGrid.GridData L sc) : gkeyOf G ∈ KS X.toD7 sc.cGap := by
  refine Set.mem_biUnion (x := G.pl.v0) G.pl.basePlace_over_qZero ⟨rfl, G.pl.under_w (G.pl.mem_S0_of_sum_eq.2 (Or.inl rfl)), fun a _ => ?_⟩
  have h1 : 1 ≤ a.1 + 1 := by omega
  have h2 : a.1 + 1 ≤ X.toD7.R.m := a.2
  refine ⟨G.ch.inf _ h1 h2, fun PP hPP => G.ch.unr _ h1 h2 PP fun h => hPP ?_, fun PP hPP => ?_⟩
  · rcases G.pl.mem_S0_of_sum_eq.1 h with h | h
    · exact Or.inl h
    · exact Or.inr h
  · rcases hPP with h | h
    · exact levelLe_one_two (G.ch.lev0 _ h1 h2 PP h).1
    · exact (G.ch.lev1 _ h1 h2 PP h).1

theorem KS_transfer (X X₀ : Stages) (h : X.B.toPre = X₀.B.toPre) (c : ℝ) :
    ∀ κ ∈ KS X.toD7 c, ∃ κ' ∈ KS X₀.toD7 c, HEq κ κ' := by
  obtain ⟨⟨P1⟩, C1, W1, V1, S1', N1, G1⟩ := X
  obtain ⟨⟨P0⟩, C0, W0, V0, S0, N0, G0⟩ := X₀
  change P1 = P0 at h
  subst h
  exact fun κ hκ => ⟨κ, hκ, HEq.rfl⟩

end KeyFiniteness

open KeyFiniteness in
theorem gKeyFin : GKeyFin := by
  intro P c
  by_cases hP : ∃ X : Stages, X.B.toPre = P
  swap
  · exact ⟨∅, Set.finite_empty, fun X _ _ _ _ h _ => (hP ⟨X, h⟩).elim⟩
  obtain ⟨X₀, rfl⟩ := hP
  refine ⟨KS X₀.toD7 c, KS_finite _ _, ?_⟩
  rintro X T L sc G hX rfl
  exact KS_transfer X X₀ hX _ _ (mem_KS G)

end GlobalTheory.Mem.LiteralAutomorphy
