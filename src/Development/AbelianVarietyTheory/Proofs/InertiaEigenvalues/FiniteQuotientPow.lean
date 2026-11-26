module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsAlgClosedTiltFieldAndValuationRing
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CentralIdempotentIrreducibleCharacterProps
public import Formalism.LocalRingCardinality.DataParams
public import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ResBound
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MapExactMiddle

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteQuotientPow
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

namespace GlobalTheory.LocalIntegers

theorem finite_quotient_pow (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O]
    [Module.Finite ℤ_[l] O] (n : ℕ) : Finite (O ⧸ Ideal.span {((l : ℕ) : O) ^ n}) := by
  have h : Ideal.span {((l : ℕ) : O) ^ n} =
      (Ideal.span {((l : ℕ) : ℤ_[l]) ^ n}).map (algebraMap ℤ_[l] O) := by
    simp [Ideal.map_span]
  rw [h]
  haveI : Finite (ℤ_[l] ⧸ Ideal.span {((l : ℕ) : ℤ_[l]) ^ n}) := by
    rw [← PadicInt.ker_toZModPow]
    haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
    exact Finite.of_injective _ (RingHom.kerLift_injective (PadicInt.toZModPow (p := l) n))
  haveI : Module.Finite (ℤ_[l] ⧸ Ideal.span {((l : ℕ) : ℤ_[l]) ^ n})
      (O ⧸ (Ideal.span {((l : ℕ) : ℤ_[l]) ^ n}).map (algebraMap ℤ_[l] O)) :=
    Module.Finite.of_restrictScalars_finite ℤ_[l] _ _
  exact Module.finite_of_finite (ℤ_[l] ⧸ Ideal.span {((l : ℕ) : ℤ_[l]) ^ n})

theorem isOpen_integers (l : ℕ) [Fact l.Prime] (LL : FinExt l) :
    IsOpen (Set.range (algebraMap ↥(OL LL) ↥LL.1)) := by
  have h : Set.range (algebraMap ↥(OL LL) ↥LL.1) =
      (fun x : ↥LL.1 => (x : PadicAlgCl l)) ⁻¹' Metric.closedBall 0 1 := by
    ext x
    rw [Set.mem_preimage, mem_closedBall_zero_iff, ← mem_integralClosure_padicInt_iff]
    exact ⟨by rintro ⟨y, rfl⟩; exact y.2, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩
  rw [h]
  exact (IsUltrametricDist.isOpen_closedBall _ one_ne_zero).preimage continuous_subtype_val

theorem good_integers : ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l), GoodO (Qp := ℚ_[l]) ↥LL.1 ↥(OL LL) ∧ ∀ n : ℕ, Finite (↥(OL LL) ⧸ Ideal.span {((l : ℕ) : ↥(OL LL)) ^ n}) := by
  intro l _ LL
  haveI := LL.2
  haveI : Module.Finite ℤ_[l] ↥(OL LL) := finite_integralClosure_padicInt l ↥LL.1
  haveI : ContinuousSMul ℚ_[l] ↥LL.1 :=
    Topology.IsInducing.continuousSMul (f := id) (g := fun x : ↥LL.1 => (x : PadicAlgCl l))
      Topology.IsInducing.subtypeVal continuous_id rfl
  haveI : IsTopologicalRing ↥LL.1 := inferInstanceAs (IsTopologicalRing ↥LL.1.toSubfield.toSubring)
  refine ⟨⟨⟨inferInstance, isDiscreteValuationRing_integralClosure_padicInt l ↥LL.1,
    isFractionRing_integralClosure_padicInt l ↥LL.1⟩, LL.2, isModuleTopologyOfFiniteDimensional,
    inferInstance, isOpen_integers l LL⟩, finite_quotient_pow l _⟩

end GlobalTheory.LocalIntegers
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFinExt
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.FitsEx

theorem exists_lift {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (i : B →+* C)
    (hi : Function.Injective i) (f : A →+* C) (h : ∀ x, ∃ y, f x = i y) :
    ∃ g : A →+* B, ∀ x, i (g x) = f x := by
  choose g hg using h
  exact ⟨{ toFun := g
           map_one' := hi (by rw [← hg, map_one, map_one])
           map_mul' := fun x y => hi (by rw [map_mul, ← hg, ← hg, ← hg, map_mul])
           map_zero' := hi (by rw [← hg, map_zero, map_zero])
           map_add' := fun x y => hi (by rw [map_add (f := _), ← hg, ← hg, ← hg, map_add (f := _)]) }, fun x => (hg x).symm⟩

variable {l : ℕ} [Fact l.Prime]

theorem eps_root {P : LocPrime l} (AI : LocAinf l P) (m : ℕ) :
    (rootT (l := l) AI.ε m : ℂ_[l]) = algebraMap (Om l) ℂ_[l] (P.ζQ m) := by
  have : rootT (l := l) AI.ε m = AI.ζ m := by
    refine Perfection.teichmuller_spec (I := Ideal.span {(l : Per.OC l)}) fun n => ?_
    refine ⟨AI.ζ (m + n), ?_, by rw [zeta_pow_iter AI.ζ_succ]⟩
    have := zeta_coeff_root_iterate (p := l) (O := Per.OC l) AI.ε m n
    rw [add_comm] at this
    exact (AI.ε_coeff (m + n)).symm.trans this.symm
  rw [this]
  exact AI.ζ_eq m

theorem isLog_unique {e : Per.Fl l} (he : e.untilt = 1) {y y' : Per.BdRp l}
    (h : Per.IsLog l e y) (h' : Per.IsLog l e y') :
    y = y' :=
  GlobalTheory.CrisIncl.log_unique l e he y y' h h'

theorem exists_finExt (x : Om l) : ∃ K : FinExt l, x ∈ K.1 :=
  ⟨⟨IntermediateField.adjoin ℚ_[l] {x},
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)⟩,
    IntermediateField.mem_adjoin_simple_self _ x⟩

theorem iota_alg (P : LocPrime l) (c : ↥(MaximalUnramifiedExtension l)) :
    P.ιB (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B c) = algebraMap (Om l) P.R.BdR (c : Om l) := by
  obtain ⟨K, hK⟩ := exists_finExt (c : Om l)
  rw [← P.PD_ι K]
  exact (P.PD K).ι.commutes (⟨c, hK, c.2⟩ : ↥(K0 K))

theorem iota_inj (P : LocPrime l) : Function.Injective P.ιB := by
  obtain ⟨K, -⟩ := exists_finExt (0 : Om l)
  intro a b h
  exact (P.PD K).ι_inj (by rw [P.PD_ι, P.PD_ι, h])

theorem phi_alg {P : LocPrime l} (AI : LocAinf l P) (σ : ↥(MaximalUnramifiedExtension l) →ₐ[ℚ_[l]] ↥(MaximalUnramifiedExtension l))
    (hσ : ∀ (c : ↥(MaximalUnramifiedExtension l)) (m : ℕ), 0 < m → ¬ l ∣ m → c ^ m = 1 → σ c = c ^ l) (c : ↥(MaximalUnramifiedExtension l)) :
    P.φB (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B c) = algebraMap ↥(MaximalUnramifiedExtension l) P.R.B (σ c) := by
  have key : P.φB.comp (IsScalarTower.toAlgHom ℚ_[l] ↥(MaximalUnramifiedExtension l) P.R.B) =
      (IsScalarTower.toAlgHom ℚ_[l] ↥(MaximalUnramifiedExtension l) P.R.B).comp σ := by
    refine IntermediateField.algHom_ext_of_eq_adjoin ℚ_[l] (S := MaximalUnramifiedExtension l) rfl fun x hx => ?_
    obtain ⟨m, hm, hlm, hxm⟩ := id hx
    obtain ⟨xb, hxb⟩ := exists_isTiltOf x m hm hlm hxm
    have hx' : x ∈ MaximalUnramifiedExtension l := IntermediateField.subset_adjoin _ _ hx
    have h1 := AI.ιA_teich ⟨x, hx'⟩ m hm hlm hxm xb hxb
    change P.φB (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B ⟨x, hx'⟩) = algebraMap ↥(MaximalUnramifiedExtension l) P.R.B (σ ⟨x, hx'⟩)
    rw [hσ ⟨x, hx'⟩ m hm hlm (Subtype.ext hxm), map_pow, ← h1, ← AI.ιA_φ, ← map_pow,
      WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller, frobenius_def, map_pow]
  exact DFunLike.congr_fun key c

theorem sigma_eq {P : LocPrime l} (AI : LocAinf l P) (σ : ↥(MaximalUnramifiedExtension l) →ₐ[ℚ_[l]] ↥(MaximalUnramifiedExtension l))
    (hσ : ∀ (c : ↥(MaximalUnramifiedExtension l)) (m : ℕ), 0 < m → ¬ l ∣ m → c ^ m = 1 → σ c = c ^ l)
    (K : FinExt l) (x : ↥(K0 K)) (c : ↥(MaximalUnramifiedExtension l)) (h : (c : Om l) = (x : Om l)) :
    (((P.PD K).σ x : ↥(K0 K)) : Om l) = ((σ c : ↥(MaximalUnramifiedExtension l)) : Om l) := by
  have : Nontrivial P.R.B := by
    refine ⟨⟨1, 0, fun h0 => one_ne_zero (AI.ιA_inj ?_)⟩⟩
    rw [map_one, map_zero, h0]
  have h1 := (P.PD K).φ_K₀ x
  rw [P.PD_φ] at h1
  have hc : c = ⟨x, x.2.2⟩ := Subtype.ext h
  have h2 := phi_alg AI σ hσ c
  rw [hc] at h2 ⊢
  have h3 : algebraMap ↥(MaximalUnramifiedExtension l) P.R.B ⟨((P.PD K).σ x : ↥(K0 K)), ((P.PD K).σ x).2.2⟩ = _ := h1.symm.trans h2
  exact congrArg Subtype.val ((algebraMap ↥(MaximalUnramifiedExtension l) P.R.B).injective h3)

theorem zeta_prim (P : LocPrime l) (m : ℕ) : IsPrimitiveRoot (P.ζQ (m + 1)) (l ^ (m + 1)) := by
  have h0 := zeta_pow_iter P.ζQ_succ 0 (m + 1)
  rw [zero_add, P.ζQ_zero] at h0
  have h1 := zeta_pow_iter P.ζQ_succ 1 m
  rw [add_comm] at h1
  have := orderOf_eq_prime_pow (x := P.ζQ (m + 1)) (p := l) (n := m) (by rw [h1]; exact P.ζQ_one) h0
  rw [← this]
  exact IsPrimitiveRoot.orderOf _

theorem chi_eq (P : LocPrime l) (χ : GQ l →* ℤ_[l]ˣ)
    (hχ : ∀ (g : GQ l) (m : ℕ) (x : Om l), x ^ (l ^ m) = 1 → g x = x ^ (PadicInt.toZModPow m (χ g : ℤ_[l])).val)
    (g : GQ l) : ((P.χQ g : ℚ_[l]ˣ) : ℚ_[l]) = (((χ g : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) := by
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have key : ∀ m : ℕ, ‖((P.χQ g : ℚ_[l]ˣ) : ℚ_[l]) - (((χ g : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l])‖ ≤
      (l : ℝ) ^ (-((m + 1 : ℕ) : ℤ)) := by
    intro m
    have hp := zeta_prim P m
    obtain ⟨a, ha, hg⟩ := P.χQ_cyc g (m + 1) _ hp.pow_eq_one
    rw [hχ g (m + 1) _ hp.pow_eq_one] at hg
    have hmod : (PadicInt.toZModPow (m + 1) (χ g : ℤ_[l])).val ≡ a [MOD l ^ (m + 1)] := by
      have hfin : IsOfFinOrder (P.ζQ (m + 1)) :=
        isOfFinOrder_iff_pow_eq_one.2 ⟨_, pow_pos (Fact.out : l.Prime).pos _, hp.pow_eq_one⟩
      have := hfin.pow_eq_pow_iff_modEq.1 hg
      rwa [← hp.eq_orderOf] at this
    have hk : ((a : ℤ_[l]) - (χ g : ℤ_[l])) ∈ Ideal.span {(l : ℤ_[l]) ^ (m + 1)} := by
      rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_natCast,
        ← (ZMod.natCast_eq_natCast_iff _ _ _).2 hmod]
      have : NeZero (l ^ (m + 1)) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
      rw [ZMod.natCast_zmod_val, sub_self]
    have hn := (PadicInt.norm_le_pow_iff_mem_span_pow _ _).2 hk
    have hn' : ‖(a : ℚ_[l]) - (((χ g : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l])‖ ≤ (l : ℝ) ^ (-((m + 1 : ℕ) : ℤ)) := by
      simpa [PadicInt.norm_def] using hn
    rw [← sub_add_sub_cancel _ (a : ℚ_[l])]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hn')
  by_contra hne
  have hpos := norm_pos_iff.2 (sub_ne_zero.2 hne)
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hpos (inv_lt_one_of_one_lt₀ hl)
  have h1 := key n
  rw [zpow_neg, zpow_natCast, ← inv_pow] at h1
  have h2 : (l : ℝ)⁻¹ ^ (n + 1) ≤ (l : ℝ)⁻¹ ^ n :=
    pow_le_pow_of_le_one (by positivity) (inv_lt_one_of_one_lt₀ hl).le (Nat.le_succ n)
  linarith

set_option allowUnsafeReducibility true in
attribute [local irreducible] Per.Acris Per.Bcris

theorem exists_fits : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI),
    ∃ C : Core l, Fits T C := by
  intro l _ P AI T
  have hinj := (BdRField.bdR_isField l).2.1
  obtain ⟨o, ho⟩ := exists_lift _ hinj (T.eD.toRingHom.comp (algebraMap (Om l) P.R.BdR))
    fun x => (T.om x).imp fun _ h => h.1
  have hosec : IsSec o := by
    refine ⟨fun x => ?_, fun z => hinj ?_⟩
    · obtain ⟨y, hy, hy'⟩ := T.om x
      rw [← hy', hinj ((ho x).trans hy)]
    · rw [ho]
      change T.eD (algebraMap (Om l) P.R.BdR _) = _
      rw [← IsScalarTower.algebraMap_apply, T.zD]
      exact GlobalTheory.RingIface.zD_eq_alg l z
  have hincl := T.incl
  set ι := (T.eD.toRingHom.comp (P.ιB : P.R.B →+* P.R.BdR)).comp T.eB.symm.toRingHom with hι
  have hιe : ∀ b : P.R.B, T.eD (P.ιB b) = ι (T.eB b) := fun b => by simp [hι]
  clear_value ι
  obtain ⟨j, hj', hj0, hjb⟩ := GlobalTheory.CrisIncl.exists_restrict l ι hincl
  have hj : ∀ x, algebraMap (Per.BdRp l) (Per.BdR l) (j x) =
      (ι.comp (algebraMap (Per.Acris l) (Per.Bcris l))) x := fun x => (hj' x).symm
  have hjc : IsCrisP j := ⟨hj0, hjb⟩
  have he : PreTilt.untilt (AI.ε : Per.Fl l) = 1 := Subtype.ext (by
    have := eps_root AI 0
    rw [P.ζQ_zero, map_one] at this
    exact this)
  obtain ⟨t, -, ht, -⟩ := exists_isLogA l AI.ε he
  obtain ⟨σ, hσ⟩ := exists_frobenius_Kur l
  obtain ⟨χ, hχ⟩ := exists_cyclotomicChar l
  refine ⟨{ ζ := P.ζQ, ζ_zero := P.ζQ_zero, ζ_succ := P.ζQ_succ, ζ_one := P.ζQ_one
            ε := AI.ε, ε_root := eps_root AI, o := o, o_sec := hosec, j := j, j_cris := hjc
            ι := ι, ι_j := fun x => (hj x).symm
            u := T.eB.toRingHom.comp (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B)
            ι_u := fun c => ?_
            t := t, t_log := ht, σ := σ, σ_root := hσ, χ := χ, χ_cyc := hχ },
    ⟨rfl, rfl, fun x => (ho x).symm, hιe, fun _ => rfl, ?_, chi_eq P χ hχ, sigma_eq AI σ hσ⟩⟩
  · rw [ho]
    exact (hιe _).symm.trans (congrArg T.eD (iota_alg P c))
  · obtain ⟨y, hy, hy'⟩ := T.t
    have h1 := isLog_unique he hy ((LogFun.log_fun l AI.ε t he ht).2.2.2 j hjc)
    have h2 : T.eD (P.ιB P.tB) = T.eD (P.ιB (T.eB.symm (algebraMap (Per.Acris l) (Per.Bcris l) t))) := by
      rw [hy', h1, hj, hιe, RingEquiv.apply_symm_apply]
      rfl
    rw [iota_inj P (T.eD.injective h2), RingEquiv.apply_symm_apply]
    rfl

end GlobalTheory.MemLoc.FitsEx
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffZeroEqZeroIff
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.Decompl

section Near

variable {A R : Type} [CommRing A] [CommRing R] (ι : A →+* R) (p : ℕ) (t : R)

def Near (m : ℕ) (x : R) : Prop := ∃ (a : A) (r : R), x = t ^ m * ι a + (p : R) * r

variable {ι p t}

theorem Near.of_mul (m : ℕ) (r : R) : Near ι p t m ((p : R) * r) := ⟨0, r, by simp⟩

theorem Near.zero (m : ℕ) : Near ι p t m 0 := ⟨0, 0, by simp⟩

theorem Near.pow_mul (m : ℕ) (a : A) : Near ι p t m (t ^ m * ι a) := ⟨a, 0, by simp⟩

theorem Near.add {m : ℕ} {x y : R} (hx : Near ι p t m x) (hy : Near ι p t m y) :
    Near ι p t m (x + y) := by
  obtain ⟨a, r, rfl⟩ := hx
  obtain ⟨b, s, rfl⟩ := hy
  exact ⟨a + b, r + s, by rw [map_add (f := _)]; ring⟩

theorem Near.neg {m : ℕ} {x : R} (hx : Near ι p t m x) : Near ι p t m (-x) := by
  obtain ⟨a, r, rfl⟩ := hx
  exact ⟨-a, -r, by rw [map_neg]; ring⟩

theorem Near.sub {m : ℕ} {x y : R} (hx : Near ι p t m x) (hy : Near ι p t m y) :
    Near ι p t m (x - y) := by
  rw [sub_eq_add_neg]; exact hx.add hy.neg

theorem Near.sum {I : Type} {m : ℕ} (s : Finset I) {f : I → R} (h : ∀ i ∈ s, Near ι p t m (f i)) :
    Near ι p t m (∑ i ∈ s, f i) :=
  Finset.sum_induction f _ (fun _ _ => Near.add) (Near.zero m) h

theorem Near.mul {m n : ℕ} {x y : R} (hx : Near ι p t m x) (hy : Near ι p t n y) :
    Near ι p t (m + n) (x * y) := by
  obtain ⟨a, r, rfl⟩ := hx
  obtain ⟨b, s, rfl⟩ := hy
  exact ⟨a * b, t ^ m * ι a * s + r * (t ^ n * ι b + p * s), by rw [map_mul]; ring⟩

theorem Near.mul_ι {m : ℕ} {x : R} (hx : Near ι p t m x) (b : A) : Near ι p t m (ι b * x) := by
  obtain ⟨a, r, rfl⟩ := hx
  exact ⟨b * a, ι b * r, by rw [map_mul]; ring⟩

theorem Near.mono {τ : A} (ht : ι τ = t) {m n : ℕ} (h : m ≤ n) {x : R} (hx : Near ι p t n x) :
    Near ι p t m x := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  obtain ⟨a, r, rfl⟩ := hx
  exact ⟨τ ^ k * a, r, by rw [map_mul, map_pow, ht]; ring⟩

theorem Near.cancel (ht : IsUnit t) {k m : ℕ} {x : R} (hx : Near ι p t (k + m) (t ^ k * x)) :
    Near ι p t m x := by
  obtain ⟨u, hu⟩ := ht.exists_right_inv
  obtain ⟨a, r, h⟩ := hx
  have h1 : t ^ k * u ^ k = 1 := by rw [← mul_pow, hu, one_pow]
  refine ⟨a, u ^ k * r, ?_⟩
  rw [pow_add] at h
  linear_combination u ^ k * h - (x - t ^ m * ι a) * h1

end Near

variable {l : ℕ} [Fact l.Prime]

def piW {P : LocPrime l} (AI : LocAinf l P) (s : ℕ) : Ainf l :=
  WittVector.teichmuller l (AI.εroot s) - 1

def piR {P : LocPrime l} (AI : LocAinf l P) (LL : FinExt l) (s : ℕ) : RW LL :=
  inclR LL ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] piW AI s)

abbrev NearPi {P : LocPrime l} (AI : LocAinf l P) (LL : FinExt l) (s m : ℕ) (x : RW LL) : Prop :=
  Near (inclR LL : RA LL →+* RW LL) l (piR AI LL s) m x

def fixSub {P : LocPrime l} (AI : LocAinf l P) (LL : FinExt l) (H : Set (GQ l)) : Subring (RW LL) :=
  ⨅ g ∈ H, RingHom.eqLocus (AI.gRW LL g : RW LL →+* RW LL) (RingHom.id _)

theorem mem_fixSub {P : LocPrime l} {AI : LocAinf l P} {LL : FinExt l} {H : Set (GQ l)}
    {x : RW LL} : x ∈ fixSub AI LL H ↔ ∀ g ∈ H, AI.gRW LL g x = x := by
  simp only [fixSub, Subring.mem_iInf]
  rfl

abbrev Wach (P : LocPrime l) (K LL : FinExt l) : Type 1 :=
  LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) (Module.finrank ℚ_[l] ↥(K0 K))

theorem finite_OL (LL : FinExt l) : Module.Finite ℤ_[l] ↥(OL LL) :=
  haveI : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  IsIntegralClosure.finite ℤ_[l] ℚ_[l] ↥LL.1 ↥(integralClosure ℤ_[l] ↥LL.1)

theorem free_OL (LL : FinExt l) : Module.Free ℤ_[l] ↥(OL LL) :=
  haveI : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  haveI : Module.IsTorsionFree ℤ_[l] ↥LL.1 :=
    Module.IsTorsionFree.trans_faithfulSMul ℤ_[l] ℚ_[l] ↥LL.1
  IsIntegralClosure.module_free ℤ_[l] ℚ_[l] ↥LL.1 ↥(integralClosure ℤ_[l] ↥LL.1)

def basisO (LL : FinExt l) : Module.Basis (Fin (Module.finrank ℤ_[l] ↥(OL LL))) ℤ_[l] ↥(OL LL) :=
  haveI := finite_OL LL
  haveI := free_OL LL
  Module.finBasis ℤ_[l] ↥(OL LL)

section Coord

variable {Z O : Type} [CommRing Z] [CommRing O] [Algebra Z O] {I : Type} [Fintype I]
  (b : Module.Basis I Z O) {W W' : Type} [CommRing W] [Algebra Z W] [CommRing W'] [Algebra Z W']

def crd (i : I) : O ⊗[Z] W →ₗ[Z] W :=
  TensorProduct.lift ((LinearMap.lsmul Z W).comp (b.coord i))

omit [Fintype I] in
@[simp] theorem crd_tmul (i : I) (o : O) (w : W) : crd b i (o ⊗ₜ[Z] w) = b.repr o i • w := rfl

theorem sum_crd (x : O ⊗[Z] W) : ∑ i, b i ⊗ₜ[Z] crd b i x = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul o w =>
    simp only [crd_tmul, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
    rw [← TensorProduct.sum_tmul, b.sum_repr]
  | add x y hx hy => simp only [map_add (f := _), TensorProduct.tmul_add, Finset.sum_add_distrib, hx, hy]

theorem crd_sum (w : I → W) (i : I) : crd b i (∑ j, b j ⊗ₜ[Z] w j) = w i := by
  classical
  set_option synthInstance.maxHeartbeats 100000 in
    simp [map_sum, Finsupp.single_apply]

theorem ext_crd {x y : O ⊗[Z] W} (h : ∀ i, crd b i x = crd b i y) : x = y := by
  rw [← sum_crd b x, ← sum_crd b y]
  simp only [h]

omit [Fintype I] in
theorem crd_map (f : W →ₐ[Z] W') (i : I) (x : O ⊗[Z] W) :
    crd b i (Algebra.TensorProduct.map (AlgHom.id O O) f x) = f (crd b i x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul o w => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

omit [Fintype I] in
theorem crd_mul (w : W) (i : I) (x : O ⊗[Z] W) :
    crd b i (((1 : O) ⊗ₜ[Z] w) * x) = w * crd b i x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul o w => simp
  | add x y hx hy => simp only [mul_add, map_add (f := _), hx, hy]

omit [Fintype I] in
theorem crd_natCast_mul (n : ℕ) (i : I) (x : O ⊗[Z] W) :
    crd b i ((n : O ⊗[Z] W) * x) = (n : W) * crd b i x := by
  rw [← nsmul_eq_mul, map_nsmul, nsmul_eq_mul]

end Coord

instance perfectRing_Cb : PerfectRing (Cb l) l :=
  haveI := (GlobalTheory.TiltAlgClosed.isAlgClosed_tilt_and_valuationRing l).1
  inferInstance

instance valuationRing_OCb : ValuationRing (OCb l) :=
  (GlobalTheory.TiltAlgClosed.isAlgClosed_tilt_and_valuationRing l).2

theorem coeff_zero_eq_zero_iff (w : WCb l) : w.coeff 0 = 0 ↔ ∃ r, w = (l : WCb l) * r := by
  rw [← WittVector.constantCoeff_apply, ← RingHom.mem_ker, WittVector.ker_constantCoeff,
    Ideal.mem_span_singleton]
  rfl

theorem sub_coeff_zero (x y : WCb l) : (x - y).coeff 0 = x.coeff 0 - y.coeff 0 :=
  map_sub (WittVector.constantCoeff : WCb l →+* Cb l) x y

theorem piR_eq {P : LocPrime l} (AI : LocAinf l P) (LL : FinExt l) (s : ℕ) :
    piR AI LL s = (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] inclW l (piW AI s) := rfl

theorem coeff_zero_piW {P : LocPrime l} (AI : LocAinf l P) (s : ℕ) :
    (inclW l (piW AI s)).coeff 0 = algebraMap (OCb l) (Cb l) (AI.εroot s - 1) := by
  rw [inclW, WittVector.map_coeff, piW, ← WittVector.constantCoeff_apply, map_sub, map_one,
    WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]

theorem crd_inclR (LL : FinExt l) (i) (a : RA LL) :
    crd (basisO LL) i (inclR LL a) = inclW l (crd (basisO LL) i a) :=
  crd_map (basisO LL) (inclWA l) i a

theorem crd_φRW (LL : FinExt l) (i) (x : RW LL) :
    crd (basisO LL) i (φRW LL x) = frobW l (crd (basisO LL) i x) :=
  crd_map (basisO LL) (frobW l) i x

theorem crd_gRW {P : LocPrime l} (AI : LocAinf l P) (LL : FinExt l) (g : GQ l) (i) (x : RW LL) :
    crd (basisO LL) i (AI.gRW LL g x) = AI.actWCbHom g (crd (basisO LL) i x) :=
  crd_map (basisO LL) (AI.actWCbHom g).toAlgHom i x

theorem coeff_actWCbHom {P : LocPrime l} (AI : LocAinf l P) (g : GQ l) (w : WCb l) (n : ℕ) :
    (AI.actWCbHom g w).coeff n = autCb l (AI.actT g) (w.coeff n) :=
  WittVector.map_coeff (autCb l (AI.actT g)).toRingHom w n

theorem coeff_frobW (w : WCb l) (n : ℕ) : (frobW l w).coeff n = w.coeff n ^ l :=
  WittVector.map_coeff (frobenius (Cb l) l) w n

theorem coeff_inclW (a : Ainf l) (n : ℕ) :
    (inclW l a).coeff n = algebraMap (OCb l) (Cb l) (a.coeff n) :=
  WittVector.map_coeff _ a n

theorem dvd_iff_crd (LL : FinExt l) (x : RW LL) :
    (∃ r, x = (l : RW LL) * r) ↔ ∀ i, (crd (basisO LL) i x).coeff 0 = 0 := by
  constructor
  · rintro ⟨r, rfl⟩ i
    rw [crd_natCast_mul, coeff_zero_eq_zero_iff]
    exact ⟨_, rfl⟩
  · intro h
    choose r hr using fun i => (coeff_zero_eq_zero_iff _).1 (h i)
    refine ⟨∑ j, basisO LL j ⊗ₜ[ℤ_[l]] r j, ext_crd (basisO LL) fun i => ?_⟩
    rw [crd_natCast_mul, crd_sum, hr]

theorem nearPi_iff_crd {P : LocPrime l} (AI : LocAinf l P) (LL : FinExt l) (s m : ℕ) (x : RW LL) :
    NearPi AI LL s m x ↔ ∀ i, ∃ c : OCb l,
      (crd (basisO LL) i x).coeff 0 = algebraMap (OCb l) (Cb l) ((AI.εroot s - 1) ^ m * c) := by
  have key : ∀ (a : RA LL) i, (crd (basisO LL) i (piR AI LL s ^ m * inclR LL a)).coeff 0 =
      algebraMap (OCb l) (Cb l) ((AI.εroot s - 1) ^ m * (crd (basisO LL) i a).coeff 0) := by
    intro a i
    have h1 : piR AI LL s ^ m = (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] (inclW l (piW AI s) ^ m) := by
      rw [piR_eq, Algebra.TensorProduct.tmul_pow, one_pow]
    have h2 : crd (basisO LL) i (inclR LL a) = inclW l (crd (basisO LL) i a) :=
      crd_map (basisO LL) (inclWA l) i a
    have h3 : (inclW l (crd (basisO LL) i a)).coeff 0 =
        algebraMap (OCb l) (Cb l) ((crd (basisO LL) i a).coeff 0) := WittVector.map_coeff _ _ _
    have h4 : (inclW l (piW AI s) ^ m).coeff 0 = (inclW l (piW AI s)).coeff 0 ^ m :=
      map_pow (WittVector.constantCoeff : WCb l →+* Cb l) _ _
    rw [h1, crd_mul, h2, WittVector.mul_coeff_zero, h3, h4, coeff_zero_piW, map_mul, map_pow]
  constructor
  · rintro ⟨a, r, h⟩ i
    refine ⟨(crd (basisO LL) i a).coeff 0, ?_⟩
    have h' : x - piR AI LL s ^ m * inclR LL a = (l : RW LL) * r := sub_eq_of_eq_add' h
    have h5 := (dvd_iff_crd LL _).1 ⟨r, h'⟩ i
    rw [LinearMap.map_sub, sub_coeff_zero] at h5
    exact (sub_eq_zero.1 h5).trans (key a i)
  · intro h
    choose c hc using h
    obtain ⟨a, ha⟩ : ∃ a : RA LL, ∀ i, (crd (basisO LL) i a).coeff 0 = c i :=
      ⟨∑ j, basisO LL j ⊗ₜ[ℤ_[l]] WittVector.teichmuller l (c j), fun i => by
        rw [crd_sum, WittVector.teichmuller_coeff_zero]⟩
    obtain ⟨r, hr⟩ := (dvd_iff_crd LL (x - piR AI LL s ^ m * inclR LL a)).2 fun i => by
      have h6 := key a i
      rw [ha] at h6
      rw [LinearMap.map_sub, sub_coeff_zero]
      exact sub_eq_zero.2 ((hc i).trans h6.symm)
    exact ⟨a, r, eq_add_of_sub_eq' hr⟩

end GlobalTheory.Decompl
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeAlgebraMapOC
noncomputable section

namespace GlobalTheory.Cyc.Decomp

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

variable {l : ℕ} [Fact l.Prime]

theorem norm_zC (x : ℤ_[l]) : ‖zC x‖ = ‖x‖ := by
  unfold zC
  rw [norm_algebraMap']
  rfl

theorem mem_OC (y : PadicComplex l) : y ∈ PadicComplexInt l ↔ ‖y‖ ≤ 1 := by
  rw [PadicComplexInt, Valuation.mem_valuationSubring_iff, PadicComplex.norm_eq_norm]
  simp [Valuation.norm_def, ← NNReal.coe_one, ← NNReal.coe_le_coe,
    ← map_one (Valuation.RankLeOne.hom' Valued.v),
    (Valuation.RankLeOne.strictMono' (v := (Valued.v : Valuation (PadicComplex l) _))).le_iff_le, ← map_one Valued.v.restrict]

theorem act_zC {act : GQ l →* (PadicComplex l ≃+* PadicComplex l)} (h : IsActC act) (g : GQ l)
    (x : ℤ_[l]) : act g (zC x) = zC x := by
  have h1 : zC x = ((algebraMap ℚ_[l] (Om l) (x : ℚ_[l]) : Om l) : PadicComplex l) := rfl
  rw [h1, h.1, AlgEquiv.commutes]

def zOC (l : ℕ) [Fact l.Prime] : ℤ_[l] →+* OC l :=
  ((algebraMap ℚ_[l] (PadicComplex l)).comp PadicInt.Coe.ringHom).codRestrict (PadicComplexInt l)
    (fun x => (mem_OC _).2 ((norm_zC x).le.trans x.norm_le_one))

scoped instance algOC : Algebra ℤ_[l] (OC l) := (zOC l).toAlgebra

theorem coe_algebraMap_OC (x : ℤ_[l]) :
    ((algebraMap ℤ_[l] (OC l) x : OC l) : PadicComplex l) = zC x := rfl

abbrev OCO (LL : FinExt l) : Type := OC l ⊗[ℤ_[l]] ↥(OL LL)

def gRA {P : LocPrime l} (AI : LocAinf l P) (LL : FinExt l) (g : GQ l) : RA LL →ₐ[↥(OL LL)] RA LL :=
  Algebra.TensorProduct.map (AlgHom.id _ _) (AI.actWHom g).toAlgHom

def IsThetaShift {P : LocPrime l} (AI : LocAinf l P) (n : ℕ) (θ : Ainf l →ₐ[ℤ_[l]] OC l) : Prop :=
  (∀ (g : GQ l) (a : Ainf l), ((θ (AI.actWHom g a) : OC l) : PadicComplex l) =
    AI.actC g ((θ a : OC l) : PadicComplex l)) ∧
  ∀ j : ℕ, θ (WittVector.teichmuller l (AI.εroot j)) = AI.ζ (j + n)

def thR (LL : FinExt l) (θ : Ainf l →ₐ[ℤ_[l]] OC l) : RA LL →+* OCO LL :=
  ((Algebra.TensorProduct.comm ℤ_[l] ↥(OL LL) (OC l)).toAlgHom.comp
    (Algebra.TensorProduct.map (AlgHom.id ℤ_[l] ↥(OL LL)) θ)).toRingHom

theorem thR_tmul (LL : FinExt l) (θ : Ainf l →ₐ[ℤ_[l]] OC l) (a : ↥(OL LL)) (w : Ainf l) :
    thR LL θ (a ⊗ₜ[ℤ_[l]] w) = θ w ⊗ₜ[ℤ_[l]] a := rfl

def kap {LL : FinExt l} {f : ℕ} (o : Module.Basis (Fin f) ℤ_[l] ↥(OL LL)) (x : OCO LL) (k : Fin f) :
    PadicComplex l :=
  (((Algebra.TensorProduct.basis (OC l) o).repr x k : OC l) : PadicComplex l)

theorem kap_tmul {LL : FinExt l} {f : ℕ} (o : Module.Basis (Fin f) ℤ_[l] ↥(OL LL)) (c : OC l)
    (a : ↥(OL LL)) (k : Fin f) :
    kap o (c ⊗ₜ[ℤ_[l]] a) k = (c : PadicComplex l) * zC (o.repr a k) := by
  simp [kap, Algebra.TensorProduct.basis_repr_tmul, coe_algebraMap_OC]

theorem kap_add {LL : FinExt l} {f : ℕ} (o : Module.Basis (Fin f) ℤ_[l] ↥(OL LL)) (x y : OCO LL)
    (k : Fin f) : kap o (x + y) k = kap o x k + kap o y k := by
  simp [kap]

theorem kap_zero {LL : FinExt l} {f : ℕ} (o : Module.Basis (Fin f) ℤ_[l] ↥(OL LL))
    (k : Fin f) : kap o 0 k = 0 := by
  simp [kap]

theorem kap_tmul_one_mul {LL : FinExt l} {f : ℕ} (o : Module.Basis (Fin f) ℤ_[l] ↥(OL LL))
    (c : OC l) (x : OCO LL) (k : Fin f) :
    kap o ((c ⊗ₜ[ℤ_[l]] (1 : ↥(OL LL))) * x) k = (c : PadicComplex l) * kap o x k := by
  have : (c ⊗ₜ[ℤ_[l]] (1 : ↥(OL LL))) * x = c • x := by
    rw [Algebra.smul_def]; rfl
  rw [this]
  simp [kap]

theorem norm_kap_le {LL : FinExt l} {f : ℕ} (o : Module.Basis (Fin f) ℤ_[l] ↥(OL LL)) (x : OCO LL)
    (k : Fin f) : ‖kap o x k‖ ≤ 1 := (mem_OC _).1 (Subtype.property _)

def lam {LL : FinExt l} {f d : ℕ} (o : Module.Basis (Fin f) ℤ_[l] ↥(OL LL))
    (A : ↥(OL LL) → Matrix (Fin d) (Fin d) (PadicComplex l)) (x : OCO LL) :
    Matrix (Fin d) (Fin d) (PadicComplex l) :=
  ∑ k, kap o x k • A (o k)

theorem freeOL (LL : FinExt l) : Module.Free ℤ_[l] ↥(OL LL) :=
  haveI : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  haveI : Module.IsTorsionFree ℤ_[l] ↥LL.1 := Module.isTorsionFree_iff_algebraMap_injective.mpr (by
    rw [IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] ↥LL.1]
    exact (algebraMap ℚ_[l] ↥LL.1).injective.comp (IsFractionRing.injective ℤ_[l] ℚ_[l]))
  IsIntegralClosure.module_free ℤ_[l] ℚ_[l] ↥LL.1 ↥(integralClosure ℤ_[l] ↥LL.1)

theorem finiteOL (LL : FinExt l) : Module.Finite ℤ_[l] ↥(OL LL) :=
  haveI : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  IsIntegralClosure.finite ℤ_[l] ℚ_[l] ↥LL.1 ↥(integralClosure ℤ_[l] ↥LL.1)

theorem inclR_injective (LL : FinExt l) : Function.Injective (inclR LL) := by
  haveI := freeOL LL
  letI : Module.Flat ℤ_[l] ↥(OL LL) := Module.Flat.of_free
  exact Module.Flat.lTensor_preserves_injective_linearMap (M := ↥(OL LL)) (inclWA l).toLinearMap
    (WittVector.map_injective _ (IsFractionRing.injective (OCb l) (Cb l)))

set_option synthInstance.maxHeartbeats 400000 in
theorem inclR_gRA {P : LocPrime l} (AI : LocAinf l P) (LL : FinExt l) (g : GQ l) (r : RA LL) :
    inclR LL (gRA AI LL g r) = AI.gRW LL g (inclR LL r) := by
  induction r using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul a w =>
    exact congrArg (fun u => a ⊗ₜ[ℤ_[l]] u) (inclW_act AI g w).symm

set_option synthInstance.maxHeartbeats 400000 in
theorem kap_thR_gRA {P : LocPrime l} (AI : LocAinf l P) {LL : FinExt l} {f n : ℕ}
    (o : Module.Basis (Fin f) ℤ_[l] ↥(OL LL)) {θ : Ainf l →ₐ[ℤ_[l]] OC l} (hθ : IsThetaShift AI n θ)
    (g : GQ l) (r : RA LL) (k : Fin f) :
    kap o (thR LL θ (gRA AI LL g r)) k = AI.actC g (kap o (thR LL θ r) k) := by
  induction r using TensorProduct.induction_on with
  | zero => simp only [map_zero, kap_zero]
  | add x y hx hy => simp only [map_add (f := _), kap_add, hx, hy]
  | tmul a w =>
    have h1 : gRA AI LL g (a ⊗ₜ[ℤ_[l]] w) = a ⊗ₜ[ℤ_[l]] AI.actWHom g w := rfl
    rw [h1, thR_tmul, thR_tmul, kap_tmul, kap_tmul, map_mul, hθ.1, act_zC ⟨AI.actC_ext, AI.actC_norm⟩]

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp] [Field LL]
  [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL]
  {R R' : Type} [CommRing R] [Algebra O R] [CommRing R'] [Algebra O R']

scoped instance (priority := high) twModule (T : LocLat G Qp LL O) : Module R (TW R T) :=
  inferInstance

scoped instance (priority := high) twSMul (T : LocLat G Qp LL O) : SMul R (TW R T) :=
  inferInstance

theorem TWincl_smul (f : R →ₐ[O] R') (T : LocLat G Qp LL O) (r : R) (z : TW R T) :
    TWincl f T (r • z) = f r • TWincl f T z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero, smul_zero]
  | add x y hx hy => simp only [map_add (f := _), smul_add, hx, hy]
  | tmul a t => simp [TWincl, TensorProduct.smul_tmul']

theorem TWact_smul (f : R →ₐ[O] R) (T : LocLat G Qp LL O) (g : G) (r : R) (z : TW R T) :
    TWact f T g (r • z) = f r • TWact f T g z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero, smul_zero]
  | add x y hx hy => simp only [map_add (f := _), smul_add, hx, hy]
  | tmul a t => simp [TWact, TensorProduct.smul_tmul']

theorem TWincl_act (f : R →ₐ[O] R') (u : R →ₐ[O] R) (u' : R' →ₐ[O] R') (h : ∀ r, f (u r) = u' (f r))
    (T : LocLat G Qp LL O) (g : G) (z : TW R T) :
    TWincl f T (TWact u T g z) = TWact u' T g (TWincl f T z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul a t => simp [TWact, TWincl, h]

theorem TWincl_injective (f : R →ₐ[O] R') (hf : Function.Injective f) (T : LocLat G Qp LL O) :
    Function.Injective (TWincl f T) := by
  haveI : Module.Free O ↥T.L.T := T.L.free
  exact Module.Flat.rTensor_preserves_injective_linearMap (M := ↥T.L.T) f.toLinearMap hf

theorem TWincl_one_tmul (f : R →ₐ[O] R') (T : LocLat G Qp LL O) (t : ↥T.L.T) :
    TWincl f T ((1 : R) ⊗ₜ[O] t) = (1 : R') ⊗ₜ[O] t := by
  simp [TWincl]

end Generic

end GlobalTheory.Cyc.Decomp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralIdempotentOfIrrCharacterOrthogonalCentral
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralIdempotentOfIrrCharacterOrthogonalCentral
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

noncomputable section

namespace GlobalTheory.GLq.ZOrth

open GlobalTheory.BadShare GlobalTheory.BadShare.Basic

theorem zOf_eq_alg {G : Type} [Group G] [Fintype G] (χ : G → ℂ) : zOf χ = alg (zc χ) := rfl

theorem ip_simple {G : Type} [Group G] [Fintype G] (V W : FDRep ℂ G) [CategoryTheory.Simple V]
    [CategoryTheory.Simple W] :
    ip V.character W.character = if V.character = W.character then 1 else 0 := by
  haveI : Invertible (Nat.card G : ℂ) := invertibleOfNonzero (by
    rw [Nat.card_eq_fintype_card]; exact_mod_cast Fintype.card_ne_zero)
  have h := FDRep.char_orthonormal V W
  rw [Nat.card_eq_fintype_card] at h
  unfold ip
  rw [h]
  by_cases hi : Nonempty (V ≅ W)
  · rw [if_pos hi, if_pos (FDRep.char_iso hi.some)]
  · rw [if_neg hi]
    by_cases hc : V.character = W.character
    · exfalso
      have h1 := FDRep.char_orthonormal V V
      rw [if_pos ⟨CategoryTheory.Iso.refl V⟩] at h1
      have h2 := FDRep.char_orthonormal V W
      rw [if_neg hi, ← hc] at h2
      rw [h1] at h2
      simp at h2
    · rw [if_neg hc]

theorem zorth : ∀ (G : Type) [Group G] [Fintype G] (χ χ' : G → ℂ), IsIrr χ → IsIrr χ' → (zOf χ * zOf χ' = if χ = χ' then zOf χ else 0) ∧ (∀ a, zOf χ * a = a * zOf χ) ∧ ip χ χ' = if χ = χ' then 1 else 0 := by
  intro G _ _ χ χ' hχ hχ'
  obtain ⟨V, hV, hVχ⟩ := hχ
  obtain ⟨W, hW, hWχ⟩ := hχ'
  have eV : V.character = χ := funext hVχ
  have eW : W.character = χ' := funext hWχ
  subst eV eW
  obtain ⟨⟨hidem, _⟩, hcen, horth, _⟩ := GlobalTheory.BadShare.ZCalc.zc_calc G V
  refine ⟨?_, ?_, ip_simple V W⟩
  · rw [zOf_eq_alg, zOf_eq_alg, ← alg_conv]
    by_cases hc : V.character = W.character
    · rw [if_pos hc, ← hc, hidem]
    · rw [if_neg hc, horth W hc]
      unfold alg; simp
  · intro a
    rw [zOf_eq_alg, ← alg_coeff a, ← alg_conv, ← alg_conv, hcen]
end GlobalTheory.GLq.ZOrth
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralIdempotentOfIrrCharacterOrthogonalCentralStatement
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.centralIdempotentOfIrrCharacter_orthogonal_central : ∀ (G : Type) [Group G] [Fintype G] (χ χ' : G → ℂ), IsIrr χ → IsIrr χ' → (zOf χ * zOf χ' = if χ = χ' then zOf χ else 0) ∧ (∀ a, zOf χ * a = a * zOf χ) ∧ ip χ χ' = if χ = χ' then 1 else 0 := by
  first | exact @GlobalTheory.GLq.ZOrth.zorth | exact GlobalTheory.GLq.ZOrth.zorth | (intros; apply GlobalTheory.GLq.ZOrth.zorth <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TypePrimeExceedsConstant
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

namespace GlobalTheory

theorem typePrime_real_bound {C F N k b : ℝ} (hF0 : 0 ≤ F) (hN0 : 0 ≤ N)
    (hC : C ≤ b) (hF : F ≤ 5 * b) (hN : N ≤ 3 * (k * b)) (hk : 5 ≤ k) (hb : 1 ≤ b) :
    C * (F * N ^ 2 + N ^ 3) < (k * b) ^ 8 := by
  set y := k * b with hy
  have hby : 5 * b ≤ y := by rw [hy]; nlinarith
  have hy5 : 5 ≤ y := by linarith
  have hy0 : 0 < y := by linarith
  have h1 : F * N ^ 2 + N ^ 3 ≤ y * (3 * y) ^ 2 + (3 * y) ^ 3 := by
    have hFy : F ≤ y := by linarith
    gcongr
  have h0 : 0 ≤ F * N ^ 2 + N ^ 3 := by positivity
  have h2 : C * (F * N ^ 2 + N ^ 3) ≤ y * (y * (3 * y) ^ 2 + (3 * y) ^ 3) :=
    mul_le_mul (by linarith) h1 h0 hy0.le
  have h3 : y * (y * (3 * y) ^ 2 + (3 * y) ^ 3) = 36 * y ^ 4 := by ring
  have h4 : (5 : ℝ) ^ 4 ≤ y ^ 4 := by gcongr
  have h5 : 0 < y ^ 4 := by positivity
  have h6 : y ^ 8 = y ^ 4 * y ^ 4 := by ring
  rw [h6]
  nlinarith

theorem typePrime_exceeds_constant :
    ∀ (D : D7) (L : SizeData₂ D), ParameterChoice' D L → L.etaSz + D.R.t + L.Sc ≤ L.sc.b → 1 ≤ L.sc.b → ∀ CT : ℕ, (CT : ℝ) ≤ L.sc.b → (⌊L.etaSz⌋₊ + D.R.t + 1 < ⌊3 * L.sc.b⌋₊ + 2) ∧ ((⌊L.etaSz⌋₊ : ℝ) ≤ 2 * L.etaSz) ∧ ∀ k : Fin 2, CT * ((⌊3 * L.sc.b⌋₊ + 2 + 0) * (D.R.nV + 1) ^ 2 + (D.R.nV + 1) ^ 3) < D.host.g k := by
  intro D L P hsum hb CT hCT
  have heta := L.etaSz_pos
  have hSc := L.Sc_pos
  have hfl : (⌊L.etaSz⌋₊ : ℝ) ≤ L.etaSz := Nat.floor_le heta.le
  have ht0 : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
  refine ⟨?_, by linarith, fun i => ?_⟩
  · have : ⌊L.etaSz⌋₊ + D.R.t ≤ ⌊3 * L.sc.b⌋₊ := by
      apply Nat.le_floor
      push_cast
      linarith
    omega
  · obtain ⟨Y, hY, -, -, hg⟩ := P.g_Y
    have hgi := (hg i).1
    have hm := D.R.m_add_three_le_k
    have hm2 := D.R.two_le_m
    have hk5 : (5 : ℝ) ≤ D.R.k := by exact_mod_cast (by omega : 5 ≤ D.R.k)
    have hnV : D.R.nV + 1 ≤ 2 * D.R.k + D.R.t := by
      unfold Ranks.nV Ranks.r
      omega
    have hnVR : (D.R.nV : ℝ) + 1 ≤ 2 * D.R.k + D.R.t := by exact_mod_cast hnV
    have hfl3 : (⌊3 * L.sc.b⌋₊ : ℝ) ≤ 3 * L.sc.b := Nat.floor_le (by linarith)
    have hN : (D.R.nV : ℝ) + 1 ≤ 3 * ((D.R.k : ℝ) * L.sc.b) := by nlinarith
    have key := typePrime_real_bound (C := (CT : ℝ)) (F := (⌊3 * L.sc.b⌋₊ : ℝ) + 2)
      (N := (D.R.nV : ℝ) + 1) (by positivity) (by positivity) hCT (by linarith) hN hk5 hb
    have : ((CT * ((⌊3 * L.sc.b⌋₊ + 2 + 0) * (D.R.nV + 1) ^ 2 + (D.R.nV + 1) ^ 3) : ℕ) : ℝ) <
        (D.host.g i : ℝ) := by
      push_cast
      simp only [add_zero]
      linarith
    exact_mod_cast this

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormalizedValuationPrimitiveRootPrimePowSubOne
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormalizedValuationPrimitiveRootPrimePowSubOne
namespace GlobalTheory

open Polynomial IsDiscreteValuationRing

theorem associated_primitiveRoot_sub_one_pow_totient_prime_pow {O : Type} [CommRing O] [IsDomain O]
    {l k : ℕ} (hl : l.Prime) {ζ : O} (hζ : IsPrimitiveRoot ζ (l ^ (k + 1))) :
    Associated ((ζ - 1) ^ Nat.totient (l ^ (k + 1))) (l : O) := by
  classical
  haveI : Fact l.Prime := ⟨hl⟩
  haveI : NeZero (l ^ (k + 1)) := ⟨pow_ne_zero _ hl.ne_zero⟩
  have h1 := Polynomial.eval_one_cyclotomic_prime_pow (R := O) (p := l) k
  rw [Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hζ, Polynomial.eval_prod] at h1
  rw [← h1, ← hζ.card_primitiveRoots, ← Finset.prod_const]
  refine Associated.prod _ _ _ fun μ hμ => ?_
  have hμ' : IsPrimitiveRoot μ (l ^ (k + 1)) :=
    (mem_primitiveRoots (pow_pos hl.pos _)).1 hμ
  obtain ⟨i, -, hi, rfl⟩ := (hζ.isPrimitiveRoot_iff).1 hμ'
  simpa using (hζ.associated_sub_one_pow_sub_one_of_coprime hi).neg_right

theorem nval_primitiveRoot_prime_pow_sub_one :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (l k : ℕ), l.Prime → 1 ≤ k → (l : O) ≠ 0 → ¬ IsUnit (l : O) → ∀ ζ : O, IsPrimitiveRoot ζ (l ^ k) → ζ - 1 ≠ 0 ∧ Formalism.MainNotions.BlochKatoReduction.Gen.nval O l (ζ - 1) = 1 / (Nat.totient (l ^ k) : ℝ) := by
  intro O _ _ _ l k hl hk hl0 hlu ζ hζ
  obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hass := associated_primitiveRoot_sub_one_pow_totient_prime_pow hl hζ
  have hφ : 0 < Nat.totient (l ^ (k + 1)) := Nat.totient_pos.2 (pow_pos hl.pos _)
  have hne : ζ - 1 ≠ 0 := by
    intro h
    rw [h, zero_pow hφ.ne'] at hass
    exact hl0 ((associated_zero_iff_eq_zero _).1 hass.symm)
  refine ⟨hne, ?_⟩
  have hv : addVal O ((ζ - 1) ^ Nat.totient (l ^ (k + 1))) = addVal O (l : O) :=
    (addVal_eq_iff_associated _ _).2 hass
  rw [addVal_pow] at hv
  have ht : addVal O (ζ - 1) ≠ ⊤ := fun h => hne (addVal_eq_top_iff.1 h)
  obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.1 ht
  have hl1 : addVal O (l : O) ≠ 0 := fun h => hlu (addVal_eq_zero_iff.1 h)
  have hv' : addVal O (l : O) = ((Nat.totient (l ^ (k + 1)) * a : ℕ) : ℕ∞) := by
    rw [← hv, ← ha]; simp
  have ha0 : a ≠ 0 := by
    rintro rfl
    apply hl1
    rw [hv']; simp
  unfold Formalism.MainNotions.BlochKatoReduction.Gen.nval
  rw [hv', ← ha, ENat.toNat_coe, ENat.toNat_coe]
  have : (a : ℝ) ≠ 0 := by exact_mod_cast ha0
  have : (Nat.totient (l ^ (k + 1)) : ℝ) ≠ 0 := by exact_mod_cast hφ.ne'
  push_cast
  field_simp

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormalizedValuationPrimitiveRootPrimePowSubOneStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalizedValuation_primitiveRoot_prime_pow_sub_one : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (l k : ℕ), l.Prime → 1 ≤ k → (l : O) ≠ 0 → ¬ IsUnit (l : O) → ∀ ζ : O, IsPrimitiveRoot ζ (l ^ k) → ζ - 1 ≠ 0 ∧ Formalism.MainNotions.BlochKatoReduction.Gen.nval O l (ζ - 1) = 1 / (Nat.totient (l ^ k) : ℝ) := by
  first | exact @GlobalTheory.nval_primitiveRoot_prime_pow_sub_one | exact GlobalTheory.nval_primitiveRoot_prime_pow_sub_one | (intros; apply GlobalTheory.nval_primitiveRoot_prime_pow_sub_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ReductionSameSSOfLattices
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries

namespace GlobalTheory.TopSteps

theorem reduction_sameSS_of_lattices :
    ∀ {G LL O V : Type} [Group G] [Field LL] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
      [Algebra O LL] [IsFractionRing O LL] [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
      (ρ : Representation LL G V) (L L' : Lattice (O := O) ρ) (lam : O), Irreducible lam →
      SameSS (modRep (latRep L) lam) (modRep (latRep L') lam) :=
  fun _ L L' _ hlam => lattice_reduction_sameSS hlam L L'

end GlobalTheory.TopSteps
end
