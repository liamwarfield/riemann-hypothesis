module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionsDimZero
public import GroundTheory.HeightsAndTheta.Heights.Intersections.TableDegreeThreeBase
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPowerBlock
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PNmSectionsFinite
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ImportsFurther

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PFibreRelLift
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace FibreRelLift

set_option linter.unusedSectionVars false

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (ℓ : ℕ)

def ratio (p : Σ k, ι k) : chartRingZ y c :=
  ⟨y p / y ⟨p.1, c p.1⟩, Algebra.subset_adjoin ⟨p, rfl⟩⟩

def dehom : MRing ι →ₐ[ℤ] chartRingZ y c := aeval (ratio y c)

theorem coe_dehom (f : MRing ι) :
    ((dehom y c f : chartRingZ y c) : Ω) = aeval (fun k => (y ⟨k, c k⟩)⁻¹) (mConeMap y f) := by
  show ((chartRingZ y c).val.toRingHom.comp (dehom y c).toRingHom) f =
    ((aeval (fun k => (y ⟨k, c k⟩)⁻¹) : MvPolynomial K Ω →ₐ[Ω] Ω).toRingHom.comp (mConeMap y).toRingHom) f
  refine RingHom.congr_fun (MvPolynomial.ringHom_ext (fun r => ?_) (fun p => ?_)) f
  · simp
  · simp [dehom, ratio, mConeMap, div_eq_mul_inv]

theorem coe_dehom_of_homog {f : MRing ι} {d : K → ℕ} (hf : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f d) :
    ((dehom y c f : chartRingZ y c) : Ω) = aeval y f * ∏ k, (y ⟨k, c k⟩)⁻¹ ^ d k := by
  rw [coe_dehom, ProjLine.mConeMap_eq_of_isMultiHomog y hf, map_mul, aeval_C, map_prod]
  simp only [map_pow, aeval_X, Algebra.algebraMap_self, RingHom.id_apply]

theorem dehom_eq_zero {f : MRing ι} (hf : f ∈ mCoordIdeal y) : dehom y c f = 0 := by
  have h0 : mConeMap y f = 0 := RingHom.mem_ker.mp hf
  apply Subtype.ext
  rw [coe_dehom, h0]
  simp

abbrev ChartQ := chartRingZ y c ⧸ Ideal.span {((ℓ : ℕ) : chartRingZ y c)}

theorem natCast_chartQ : ((ℓ : ℕ) : ChartQ y c ℓ) = 0 := by
  rw [← map_natCast (Ideal.Quotient.mk (Ideal.span {((ℓ : ℕ) : chartRingZ y c)})) ℓ]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)

def dehomMod : MRingOver (ZMod ℓ) ι →+* ChartQ y c ℓ :=
  eval₂Hom (ZMod.castHom (ringChar.dvd (natCast_chartQ y c ℓ)) (ChartQ y c ℓ))
    (fun p => Ideal.Quotient.mk _ (ratio y c p))

theorem dehomMod_map (f : MRing ι) :
    dehomMod y c ℓ (MvPolynomial.map (Int.castRingHom (ZMod ℓ)) f) =
      Ideal.Quotient.mk (Ideal.span {((ℓ : ℕ) : chartRingZ y c)}) (dehom y c f) := by
  show ((dehomMod y c ℓ).comp (MvPolynomial.map (Int.castRingHom (ZMod ℓ)))) f =
    ((Ideal.Quotient.mk (Ideal.span {((ℓ : ℕ) : chartRingZ y c)})).comp (dehom y c).toRingHom) f
  refine RingHom.congr_fun (MvPolynomial.ringHom_ext (fun r => ?_) (fun p => ?_)) f
  · simp [dehomMod]
  · simp [dehomMod, dehom]

theorem idealOver_le_ker : GenOnFibres.idealOver y (ZMod ℓ) ≤ RingHom.ker (dehomMod y c ℓ) := by
  refine Ideal.map_le_iff_le_comap.mpr fun f hf => ?_
  rw [Ideal.mem_comap, RingHom.mem_ker, dehomMod_map, dehom_eq_zero y c hf, map_zero]

def dehomQuot : MRingOver (ZMod ℓ) ι ⧸ GenOnFibres.idealOver y (ZMod ℓ) →+* ChartQ y c ℓ :=
  Ideal.Quotient.lift _ (dehomMod y c ℓ) fun _ hf => RingHom.mem_ker.mp (idealOver_le_ker y c ℓ hf)

theorem dehomQuot_smul (r : MRingOver (ZMod ℓ) ι) (m : MRingOver (ZMod ℓ) ι ⧸ GenOnFibres.idealOver y (ZMod ℓ)) :
    dehomQuot y c ℓ (r • m) = dehomMod y c ℓ r * dehomQuot y c ℓ m := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective m
  rw [GenOnFibres.smul_mk, dehomQuot, Ideal.Quotient.lift_mk, Ideal.Quotient.lift_mk, map_mul]

theorem dehomMod_cellMon (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) {I : ∀ k, Finset (ι k)} (hI : ∀ k, ∀ i ∈ I k, i = c k)
    {t : MRingOver (ZMod ℓ) ι} (ht : t ∈ KH.cellMon (ZMod ℓ) I) : dehomMod y c ℓ t = 1 := by
  have hle : KH.cellMon (ZMod ℓ) I ≤ (⊥ : Submonoid (ChartQ y c ℓ)).comap (dehomMod y c ℓ).toMonoidHom := by
    unfold KH.cellMon
    refine Submonoid.closure_le.mpr ?_
    rintro f ⟨k, i, hi, rfl⟩
    obtain rfl := hI k i hi
    have h1 : ratio y c ⟨k, c k⟩ = 1 := Subtype.ext (by simp [ratio, div_self (hc k)])
    rw [SetLike.mem_coe, Submonoid.mem_comap, Submonoid.mem_bot]
    simp [dehomMod, h1]
  exact Submonoid.mem_bot.mp (hle ht)

variable {y c ℓ}

def dehomLocFun (T : Submonoid (MRingOver (ZMod ℓ) ι)) (hT : ∀ t ∈ T, dehomMod y c ℓ t = 1)
    (x : LocalizedModule T (MRingOver (ZMod ℓ) ι ⧸ GenOnFibres.idealOver y (ZMod ℓ))) : ChartQ y c ℓ :=
  x.liftOn (fun p => dehomQuot y c ℓ p.1) (by
    rintro ⟨m, s⟩ ⟨m', s'⟩ ⟨u, hu⟩
    have h := congrArg (dehomQuot y c ℓ) hu
    simp only [Submonoid.smul_def, dehomQuot_smul, hT _ u.2, hT _ s.2, hT _ s'.2, one_mul] at h
    exact h)

theorem dehomLocFun_mk (T : Submonoid (MRingOver (ZMod ℓ) ι)) (hT : ∀ t ∈ T, dehomMod y c ℓ t = 1)
    (m : MRingOver (ZMod ℓ) ι ⧸ GenOnFibres.idealOver y (ZMod ℓ)) (t : T) :
    dehomLocFun T hT (LocalizedModule.mk m t) = dehomQuot y c ℓ m := by
  unfold dehomLocFun
  rw [LocalizedModule.liftOn_mk]

def dehomLoc (T : Submonoid (MRingOver (ZMod ℓ) ι)) (hT : ∀ t ∈ T, dehomMod y c ℓ t = 1) :
    LocalizedModule T (MRingOver (ZMod ℓ) ι ⧸ GenOnFibres.idealOver y (ZMod ℓ)) →+* ChartQ y c ℓ where
  toFun := dehomLocFun T hT
  map_one' := by
    rw [show (1 : LocalizedModule T (MRingOver (ZMod ℓ) ι ⧸ GenOnFibres.idealOver y (ZMod ℓ))) =
      LocalizedModule.mk 1 1 by rw [OreLocalization.one_def], dehomLocFun_mk, map_one]
  map_mul' x x' := by
    induction x, x' using LocalizedModule.induction_on₂ with
    | h m m' s s' =>
      rw [LocalizedModule.mk_mul_mk, dehomLocFun_mk, dehomLocFun_mk, dehomLocFun_mk, map_mul]
  map_zero' := by
    rw [← LocalizedModule.zero_mk 1, dehomLocFun_mk, map_zero]
  map_add' x x' := by
    induction x, x' using LocalizedModule.induction_on₂ with
    | h m m' s s' =>
      rw [LocalizedModule.mk_add_mk, dehomLocFun_mk, dehomLocFun_mk, dehomLocFun_mk,
        (dehomQuot y c ℓ).map_add,
        Submonoid.smul_def, Submonoid.smul_def, dehomQuot_smul, dehomQuot_smul, hT _ s.2, hT _ s'.2,
        one_mul, one_mul]

theorem dehomLoc_mk (T : Submonoid (MRingOver (ZMod ℓ) ι)) (hT : ∀ t ∈ T, dehomMod y c ℓ t = 1)
    (m : MRingOver (ZMod ℓ) ι ⧸ GenOnFibres.idealOver y (ZMod ℓ)) (t : T) :
    dehomLoc T hT (LocalizedModule.mk m t) = dehomQuot y c ℓ m :=
  dehomLocFun_mk T hT m t

end FibreRelLift


open FibreRelLift in
theorem FibreRelLift.proof : FibreRelLift.Statement := by
  intro K _ _ ι _ _ Ω _ y ℓ a r s J u hs hc _ hrel
  set c := GenOnFibres.cellChart J with hcdef
  have hI : ∀ k, ∀ i ∈ J.1 k, i = c k := by
    intro k i hi
    have h1 : (J.1 k).card - 1 = 0 := (Finset.sum_eq_zero_iff.mp J.2.2) k (Finset.mem_univ k)
    exact Finset.card_le_one.mp (by omega) i hi (c k) (GenOnFibres.cellChart_mem J k)
  have hT : ∀ t ∈ KH.cellMon (ZMod ℓ) J.1, dehomMod y c ℓ t = 1 := fun t ht =>
    dehomMod_cellMon y c ℓ hc hI ht
  have hw : ∀ j, s j * ∏ k, y ⟨k, c k⟩ ^ (-a k) ∈ chartRingZ y c := fun j => by
    simpa using hs j c hc
  have hz : ∀ j, dehomLoc _ hT (GenOnFibres.secCoch y (ZMod ℓ) (s j) a J) =
      Ideal.Quotient.mk (Ideal.span {((ℓ : ℕ) : chartRingZ y c)}) ⟨_, hw j⟩ := by
    intro j
    obtain ⟨e, F, ⟨d, hF, hd, hv⟩, h, he⟩ := GenOnFibres.secCoch_spec (S := ZMod ℓ) (hs j) J hc
    rw [he, dehomLoc_mk, dehomQuot, Ideal.Quotient.lift_mk, dehomMod_map]
    congr 1
    apply Subtype.ext
    rw [coe_dehom_of_homog y c hF, hv, mul_assoc, ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [inv_pow, ← zpow_natCast, ← zpow_natCast, ← zpow_neg, ← zpow_add₀ (hc k)]
    congr 1
    have := hd k
    omega
  have h1 := congrArg (dehomLoc _ hT) hrel
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_one] at h1
  simp only [map_mul, hz] at h1
  choose b hb using fun j => Ideal.Quotient.mk_surjective (dehomLoc _ hT (u j))
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [← hb, ← map_mul, ← map_sum] at h1
  rw [← map_one (Ideal.Quotient.mk (Ideal.span {((ℓ : ℕ) : chartRingZ y c)})), Ideal.Quotient.eq,
    Ideal.mem_span_singleton'] at h1
  obtain ⟨q, hq⟩ := h1
  refine ⟨fun j => (b j : Ω), -(q : Ω), fun j => (b j).2, neg_mem q.2, ?_⟩
  have h2 := congrArg (fun x : chartRingZ y c => (x : Ω)) hq
  push_cast at h2
  linear_combination (-1 : Ω) * h2

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PLiftModel
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1

noncomputable section

theorem LiftModel.ideal_eq_top_of_pow_mem {A : Type} [CommRing A] (J : Ideal A) {m : ℕ} (hm0 : m ≠ 0) (e : ℕ)
    (hm : (m : A) ^ e ∈ J) (hp : ∀ p ∈ m.primeFactors, J ⊔ Ideal.span {(p : A)} = ⊤) : J = ⊤ := by
  by_contra hJ
  obtain ⟨M, hM, hJM⟩ := Ideal.exists_le_maximal J hJ
  have hmM : (m : A) ∈ M := hM.isPrime.mem_of_pow_mem e (hJM hm)
  rw [Nat.prod_primeFactors_pow_factorization hm0, Nat.cast_prod] at hmM
  obtain ⟨p, hp', hpM⟩ := (Ideal.IsPrime.prod_mem_iff (hp := hM.isPrime)).mp hmM
  rw [Nat.cast_pow] at hpM
  have h1 : (p : A) ∈ M := hM.isPrime.mem_of_pow_mem _ hpM
  have hle : J ⊔ Ideal.span {(p : A)} ≤ M := sup_le hJM ((Ideal.span_singleton_le_iff_mem M).mpr h1)
  rw [hp p hp'] at hle
  exact hM.ne_top (top_le_iff.mp hle)

theorem LiftModel.mem_chartRingZ_of_mem_chartLat {K : Type} [Fintype K] {ι : K → Type} {Ω : Type} [Field Ω]
    {y : (Σ k, ι k) → Ω} {n : K → ℤ} {x : Ω} (hx : x ∈ chartLat y n 1) (c : ∀ k, ι k)
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) : x * ∏ k, y ⟨k, c k⟩ ^ (-n k) ∈ chartRingZ y c := by
  have h := hx c hc
  simpa using h

theorem LiftModel.combine {K : Type} [Fintype K] {ι : K → Type} {Ω : Type} [Field Ω]
    (y : (Σ k, ι k) → Ω) (n : K → ℤ) {m : ℕ} (hm0 : m ≠ 0) {r₁ : ℕ} (x₁ : Fin r₁ → Ω)
    (hx₁ : ∀ j, x₁ j ∈ chartLat y n 1)
    (hg₁ : ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) → ∃ (e : ℕ) (u : Fin r₁ → Ω), (∀ j, u j ∈ chartRingZ y c) ∧
      ∑ j, u j * (x₁ j * ∏ k, y ⟨k, c k⟩ ^ (-n k)) = (m : Ω) ^ e)
    (rP : ℕ → ℕ) (xP : ∀ p, Fin (rP p) → Ω) (hxP : ∀ p ∈ m.primeFactors, ∀ j, xP p j ∈ chartLat y n 1)
    (hgP : ∀ p ∈ m.primeFactors, ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) → ∃ (u : Fin (rP p) → Ω) (v : Ω),
      (∀ j, u j ∈ chartRingZ y c) ∧ v ∈ chartRingZ y c ∧
        ∑ j, u j * (xP p j * ∏ k, y ⟨k, c k⟩ ^ (-n k)) + p * v = 1)
    {r₃ : ℕ} (x₃ : Fin r₃ → Ω) (hx₃ : ∀ j, x₃ j ∈ chartLat y n 1) :
    ∃ F : Finset Ω, (∀ f ∈ F, f ∈ chartLat y n 1) ∧ KH.GeneratesOn y n (fun f : F => (f : Ω)) ∧
      ∀ j, x₃ j ∈ F := by
  classical
  let F : Finset Ω := Finset.univ.image x₁ ∪ m.primeFactors.biUnion (fun p => Finset.univ.image (xP p)) ∪
    Finset.univ.image x₃
  have h₁F : ∀ j, x₁ j ∈ F := fun j => by simp [F]
  have hPF : ∀ p ∈ m.primeFactors, ∀ j, xP p j ∈ F := by
    intro p hp j
    simp only [F, Finset.mem_union, Finset.mem_biUnion, Finset.mem_image, Finset.mem_univ, true_and]
    exact Or.inl (Or.inr ⟨p, hp, j, rfl⟩)
  have h₃F : ∀ j, x₃ j ∈ F := fun j => by simp [F]
  have hFmem : ∀ f ∈ F, f ∈ chartLat y n 1 := by
    intro f hf
    simp only [F, Finset.mem_union, Finset.mem_biUnion, Finset.mem_image, Finset.mem_univ, true_and] at hf
    rcases hf with (⟨j, rfl⟩ | ⟨p, hp, j, rfl⟩) | ⟨j, rfl⟩
    · exact hx₁ j
    · exact hxP p hp j
    · exact hx₃ j
  refine ⟨F, hFmem, fun c hc => ?_, h₃F⟩
  let v : F → chartRingZ y c := fun f =>
    ⟨(f : Ω) * ∏ k, y ⟨k, c k⟩ ^ (-n k), LiftModel.mem_chartRingZ_of_mem_chartLat (hFmem f f.2) c hc⟩
  have hv : ∀ f (hf : f ∈ F), (⟨f * ∏ k, y ⟨k, c k⟩ ^ (-n k),
      LiftModel.mem_chartRingZ_of_mem_chartLat (hFmem f hf) c hc⟩ : chartRingZ y c) ∈ Ideal.span (Set.range v) :=
    fun f hf => Ideal.subset_span ⟨⟨f, hf⟩, rfl⟩
  obtain ⟨e, u, hu, hsum⟩ := hg₁ c hc
  have htop : Ideal.span (Set.range v) = ⊤ := by
    refine LiftModel.ideal_eq_top_of_pow_mem _ hm0 e ?_ fun p hp => ?_
    · have heq : ((m : chartRingZ y c) ^ e) = ∑ j, (⟨u j, hu j⟩ : chartRingZ y c) *
          ⟨x₁ j * ∏ k, y ⟨k, c k⟩ ^ (-n k), LiftModel.mem_chartRingZ_of_mem_chartLat (hFmem _ (h₁F j)) c hc⟩ := by
        apply Subtype.val_injective
        push_cast
        exact hsum.symm
      rw [heq]
      exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hv _ (h₁F j))
    · obtain ⟨u', w, hu', hw, hsum'⟩ := hgP p hp c hc
      rw [Ideal.eq_top_iff_one]
      have heq : (1 : chartRingZ y c) = ∑ j, (⟨u' j, hu' j⟩ : chartRingZ y c) *
          ⟨xP p j * ∏ k, y ⟨k, c k⟩ ^ (-n k), LiftModel.mem_chartRingZ_of_mem_chartLat (hFmem _ (hPF p hp j)) c hc⟩ +
          (p : chartRingZ y c) * ⟨w, hw⟩ := by
        apply Subtype.val_injective
        push_cast
        exact hsum'.symm
      rw [heq]
      exact Ideal.add_mem _ (Ideal.mem_sup_left (Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hv _ (hPF p hp j))))
        (Ideal.mem_sup_right (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)))
  have h1 : (1 : chartRingZ y c) ∈ Ideal.span (Set.range v) := by
    rw [htop]
    exact Submodule.mem_top
  obtain ⟨a, ha⟩ := Ideal.mem_span_range_iff_exists_fun.mp h1
  refine ⟨fun f => (a f : Ω), fun f => (a f).2, ?_⟩
  have h := congrArg Subtype.val ha
  push_cast at h
  exact h

theorem LiftModel.isMultiHomog_rename {κ κ' : Type} [Fintype κ] [Fintype κ']
    (φ : (Σ _ : Unit, κ) → (Σ _ : Unit, κ')) {g : MRing (fun _ : Unit => κ)} {d : Unit → ℕ}
    (hg : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g d) : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (rename φ g) d := by
  have hdeg : ∀ {τ : Type} [Fintype τ] (m : (Σ _ : Unit, τ) →₀ ℕ), m.degree = ∑ i, m ⟨(), i⟩ := by
    intro τ _ m
    classical
    rw [Finsupp.degree_apply, Finset.sum_subset (Finset.subset_univ _) (fun x _ hx => by
      simpa using hx), Fintype.sum_sigma, Fintype.sum_unique]
  have hw : ∀ {τ : Type} (m : τ →₀ ℕ), Finsupp.weight 1 m = m.degree := by
    intro τ m
    rw [Finsupp.degree_eq_weight_one]
    rfl
  have hH : g.IsHomogeneous (d ()) := by
    intro m hm
    rw [hw, hdeg]
    exact hg m (mem_support_iff.mpr hm) ()
  have h := hH.rename_isHomogeneous (f := φ)
  intro m hm k
  have := h (mem_support_iff.mp hm)
  rw [hw, hdeg] at this
  exact this

theorem LiftModel.birational_of_subfamily {Ω : Type} [Field Ω] {r : ℕ} (x₃ : Fin r → Ω) (F : Finset Ω)
    (h : ∀ j, x₃ j ∈ F) (hb : Birational (fun p : Σ _ : Unit, Fin r => x₃ p.2)) :
    Birational (fun p : Σ _ : Unit, F => (p.2 : Ω)) := by
  intro s
  obtain ⟨d, g, g', hg, hg', hg0, hgs⟩ := hb s
  let φ : (Σ _ : Unit, Fin r) → (Σ _ : Unit, F) := fun p => ⟨(), ⟨x₃ p.2, h p.2⟩⟩
  have hev : ∀ f : MRing (fun _ : Unit => Fin r), aeval (fun p : Σ _ : Unit, F => (p.2 : Ω)) (rename φ f) =
      aeval (fun p : Σ _ : Unit, Fin r => x₃ p.2) f := fun f => by
    rw [aeval_rename]
    rfl
  refine ⟨d, rename φ g, rename φ g', LiftModel.isMultiHomog_rename φ hg, LiftModel.isMultiHomog_rename φ hg', ?_, ?_⟩
  · rw [hev]
    exact hg0
  · rw [hev, hev]
    exact hgs

theorem LiftModel.core {K : Type} [Fintype K] {ι : K → Type} {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω)
    (N : K → ℤ) (B : ∀ r : ℕ, (Fin r → Ω) → Prop) {q₁ m t₁ : ℕ} (hq₁ : 1 ≤ q₁) (hm : 1 ≤ m)
    (h₁ : ∀ t : ℕ, t₁ ≤ t → ∃ (r : ℕ) (x' : Fin r → Ω), (∀ j, x' j ∈ chartLat y ((t * q₁) • N) 1) ∧
      ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) → ∃ (e : ℕ) (u : Fin r → Ω), (∀ j, u j ∈ chartRingZ y c) ∧
        ∑ j, u j * (x' j * ∏ k, y ⟨k, c k⟩ ^ (-((t * q₁) • N) k)) = (m : Ω) ^ e)
    (qP tP : ℕ → ℕ) (hqP : ∀ p ∈ m.primeFactors, 1 ≤ qP p)
    (hP : ∀ p ∈ m.primeFactors, ∀ t : ℕ, tP p ≤ t → ∃ (r : ℕ) (x' : Fin r → Ω),
      (∀ j, x' j ∈ chartLat y ((t * qP p) • N) 1) ∧
      ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) → ∃ (u : Fin r → Ω) (v : Ω), (∀ j, u j ∈ chartRingZ y c) ∧
        v ∈ chartRingZ y c ∧ ∑ j, u j * (x' j * ∏ k, y ⟨k, c k⟩ ^ (-((t * qP p) • N) k)) + p * v = 1)
    {q₃ t₃ : ℕ} (hq₃ : 1 ≤ q₃)
    (h₃ : ∀ t : ℕ, t₃ ≤ t → ∃ (r : ℕ) (x' : Fin r → Ω), (∀ j, x' j ∈ chartLat y ((t * q₃) • N) 1) ∧ B r x') :
    ∃ (a : ℕ) (F : Finset Ω), 1 ≤ a ∧ (∀ f ∈ F, f ∈ chartLat y (a • N) 1) ∧
      KH.GeneratesOn y (a • N) (fun f : F => (f : Ω)) ∧ ∃ (r : ℕ) (x₃ : Fin r → Ω), (∀ j, x₃ j ∈ F) ∧ B r x₃ := by
  classical
  have hprod : ∀ s ⊆ m.primeFactors, 1 ≤ ∏ p ∈ s, qP p := fun s hs =>
    Nat.one_le_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun p hp => by have := hqP p (hs hp); omega)
  have hprodS := hprod m.primeFactors subset_rfl
  set t := t₁ + t₃ + ∑ p ∈ m.primeFactors, tP p + 1 with ht
  set Q := q₁ * q₃ * ∏ p ∈ m.primeFactors, qP p with hQ
  have hQ1 : 1 ≤ Q := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have ht1 : 1 ≤ t := by omega

  have hT₁ : t₁ ≤ t * (q₃ * ∏ p ∈ m.primeFactors, qP p) :=
    le_trans (by omega) (Nat.le_mul_of_pos_right _ (by positivity))
  obtain ⟨r₁, x₁, hx₁, hg₁⟩ := h₁ _ hT₁
  have e₁ : t * (q₃ * ∏ p ∈ m.primeFactors, qP p) * q₁ = t * Q := by rw [hQ]; ring
  rw [e₁] at hx₁ hg₁

  have hT₃ : t₃ ≤ t * (q₁ * ∏ p ∈ m.primeFactors, qP p) :=
    le_trans (by omega) (Nat.le_mul_of_pos_right _ (by positivity))
  obtain ⟨r₃, x₃, hx₃, hB₃⟩ := h₃ _ hT₃
  have e₃ : t * (q₁ * ∏ p ∈ m.primeFactors, qP p) * q₃ = t * Q := by rw [hQ]; ring
  rw [e₃] at hx₃

  have hP' : ∀ p ∈ m.primeFactors, ∃ (r : ℕ) (x' : Fin r → Ω), (∀ j, x' j ∈ chartLat y ((t * Q) • N) 1) ∧
      ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) → ∃ (u : Fin r → Ω) (v : Ω), (∀ j, u j ∈ chartRingZ y c) ∧
        v ∈ chartRingZ y c ∧ ∑ j, u j * (x' j * ∏ k, y ⟨k, c k⟩ ^ (-((t * Q) • N) k)) + p * v = 1 := by
    intro p hp
    have hprodp := hprod (m.primeFactors.erase p) (Finset.erase_subset _ _)
    have htp : tP p ≤ t := by
      have := Finset.single_le_sum (f := tP) (fun _ _ => Nat.zero_le _) hp
      omega
    have hTp : tP p ≤ t * (q₁ * q₃ * ∏ p' ∈ m.primeFactors.erase p, qP p') :=
      le_trans htp (Nat.le_mul_of_pos_right _ (by positivity))
    obtain ⟨r, x', hx, hg⟩ := hP p hp _ hTp
    have ep : t * (q₁ * q₃ * ∏ p' ∈ m.primeFactors.erase p, qP p') * qP p = t * Q := by
      rw [hQ, ← Finset.mul_prod_erase m.primeFactors qP hp]
      ring
    rw [ep] at hx hg
    exact ⟨r, x', hx, hg⟩
  choose! rP xP hxP hgP using hP'
  obtain ⟨F, hFmem, hFgen, hF₃⟩ :=
    LiftModel.combine y ((t * Q) • N) (by omega) x₁ hx₁ hg₁ rP xP hxP hgP x₃ hx₃
  exact ⟨t * Q, F, Nat.one_le_iff_ne_zero.mpr (by positivity), hFmem, hFgen, r₃, x₃, hF₃, hB₃⟩

theorem LiftModel.proof (hS : LiftSpread.Statement) (hA : LiftAtPrime.Statement)
    (hB : LiftBirationalAmple.Statement) : LiftModel.Statement := by
  intro K _ _ ι _ _ Ω _ _ y D N hV hbir hQ hcQ hF
  classical
  obtain ⟨c, hc1, hcQ⟩ := hcQ
  obtain ⟨q₁, m, t₁, hq₁, hm, h₁⟩ := hS K ι Ω y D N hV hQ
  have hP := fun p (hp : p ∈ m.primeFactors) =>
    hA K ι Ω y D N p hV (Nat.prime_of_mem_primeFactors hp) (hF p (Nat.prime_of_mem_primeFactors hp))
  choose! qP tP hqP hP using hP
  obtain ⟨q₃, t₃, hq₃, h₃⟩ := hB K ι Ω y D N c hV hbir hc1 hcQ
  obtain ⟨a, F, ha, hmem, hgen, r, x₃, hx₃F, hbir₃⟩ :=
    LiftModel.core y N (fun r x => Birational (fun p : Σ _ : Unit, Fin r => x p.2)) hq₁ hm h₁ qP tP hqP hP hq₃ h₃
  exact ⟨a, {x // x ∈ F}, inferInstance, Subtype.val, ha, fun j => hmem j j.2, hgen,
    LiftModel.birational_of_subfamily x₃ F hx₃F hbir₃⟩

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ImportsMore
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter Asymptotics MeasureTheory

theorem TensorPowerL2Degree.proof (hDat : PowerBlockDatum.Statement) (hTop : PowerBlockTop.Statement)
    (hChi : BlockChiCovolume.Statement) (hHS : TheoremHSMBlock.Statement) : TensorPowerL2Degree.Statement := by
  intro K _ ι _ Ω _ _ y D A P0 II hD1 hII har hb hA hc
  classical
  obtain ⟨m, N, v, d, μ, hm, hdy, hk, hv, hgen, hmet, hlat, hμ, hnull, hZ, hnorm⟩ :=
    hDat K ι Ω y D A P0 hD1 har hb hA hc
  have htop : II (Option K) (addIdx ι N) (mCoordIdeal d.y) (D + 1) (fun _ => d.A) =
      (m : ℝ) ^ (D + 1) * II K ι (mCoordIdeal y) (D + 1) (fun _ => A) := by
    rw [hdy]
    refine hTop K ι Ω y D A m N v d.A II hII har hA.semipos.1 hm hv hgen (by rw [d.deg, hk]) d.semipos.1 ?_
    rw [← hdy]
    exact hmet
  obtain ⟨hdef, -⟩ := hHS D (Option K) (addIdx ι N) Ω II d hII
  refine ⟨μ, m, hμ, hnull, hZ, hm, fun ε hε => ?_⟩
  have hfac : (0 : ℝ) < ((D + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hmpos : (0 : ℝ) < (m : ℝ) ^ (D + 1) := pow_pos (by exact_mod_cast hm) _
  have hc' : 0 < ε * (m : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ) := by positivity
  filter_upwards [hdef.bound hc', hlat] with q hq hl
  intro r ψ hψ hiso _ _
  have hcov := hChi D (Option K) (addIdx ι N) Ω d q (chartLat y A.a (m * q)) (by rw [hk]; exact hl) r ψ hψ
    (fun s f hf hs => by
      rw [hk] at hf
      rw [hiso, ← hs]
      exact hnorm q f hf)
  rw [hcov]
  rw [htop] at hq
  simp only [hsDefect, pw, Real.norm_eq_abs] at hq
  have hq' := (abs_le.mp hq).2
  rw [abs_of_nonneg (by positivity)] at hq'
  push_cast
  rw [mul_pow]
  have key : (II K ι (mCoordIdeal y) (D + 1) (fun _ => A) + ε) *
      ((m : ℝ) ^ (D + 1) * (q : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) =
      (m : ℝ) ^ (D + 1) * II K ι (mCoordIdeal y) (D + 1) (fun _ => A) * (q : ℝ) ^ (D + 1) /
          ((D + 1).factorial : ℝ) +
        ε * (m : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ) * (q : ℝ) ^ (D + 1) := by
    ring
  rw [key]
  linarith

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PChartLatRank
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

theorem chartLat_subset_chartLatQ {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
    [CharZero Ω] (y : (Σ k, ι k) → Ω) (a : K → ℤ) (n : ℕ) {s : Ω} (hs : s ∈ chartLat y a n) :
    s ∈ chartLatQ y a n := by
  intro c hc
  have hle : chartRingZ y c ≤ (chartRingQ y c).restrictScalars ℤ :=
    Algebra.adjoin_le (Algebra.subset_adjoin (R := ℚ))
  exact hle (hs c hc)

theorem ChartLatRank.proof (hfin : SectionLatticeFinite.Statement) : ChartLatRank.Statement := by
  intro K _ ι _ Ω _ _ y a n hy
  classical
  set M := AddSubgroup.toIntSubmodule (chartLat y a n) with hM
  have hfg : M.FG := (Submodule.fg_iff_addSubgroup_fg M).mpr (hfin K ι Ω y a n hy)
  have : Module.Finite ℤ M := Module.Finite.iff_fg.mpr hfg
  obtain ⟨r, b⟩ := Module.basisOfFiniteTypeTorsionFree' (R := ℤ) (M := M)
  set v : Fin r → Ω := fun i => ((b i : M) : Ω) with hv
  have hvZ : LinearIndependent ℤ v := b.linearIndependent.map' M.subtype M.ker_subtype
  have hvQ : LinearIndependent ℚ v := (LinearIndependent.iff_fractionRing ℤ ℚ).mp hvZ
  have hspan : Submodule.span ℚ (Set.range v) = chartLatQ y a n := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact chartLat_subset_chartLatQ y a n (b i).2
    · intro s hs
      obtain ⟨N, hN, hNs⟩ := ChartDenominator.proof K ι Ω y a n s hs
      have hmemM : (⟨(N : Ω) * s, hNs⟩ : M) ∈ Submodule.span ℤ (Set.range b) := b.mem_span _
      have hmemZ : (N : Ω) * s ∈ Submodule.span ℤ (Set.range v) := by
        have h := Submodule.mem_map_of_mem (f := M.subtype) hmemM
        rw [Submodule.map_span, ← Set.range_comp] at h
        exact h
      have hmemQ : (N : Ω) * s ∈ Submodule.span ℚ (Set.range v) :=
        Submodule.span_le_restrictScalars ℤ ℚ _ hmemZ
      have hN0 : (N : Ω) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
      have hs' : s = ((N : ℚ)⁻¹) • ((N : Ω) * s) := by
        rw [Rat.smul_def]
        push_cast
        field_simp
      rw [hs']
      exact Submodule.smul_mem _ _ hmemQ
  rw [Module.finrank_eq_card_basis b, ← hspan, finrank_span_eq_card hvQ]

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PResolutionFormsIndependent
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MeasureTheory

noncomputable section

theorem ResolutionFormsIndependent.proof (hND : NonvanishingDense.Statement) :
    ResolutionFormsIndependent.Statement := by
  intro D Ω _ _ κ _ d n r b hb a ha
  obtain ⟨g, hgJ, hgP⟩ := SetLike.not_le_iff_exists.1 d.R.nondeg
  set F : (Ix κ → ℂ) → ℂ := fun z => ∑ k, a k * secFun (b k) z with hF
  have hFc : Continuous F :=
    continuous_finsetSum _ fun k _ => continuous_const.mul (continuous_secFun _)

  have hoff : ∀ z, z ∈ mcPts (ι := GlobalTheory κ) (coordIdeal ℤ d.x) →
      eval z (map (Int.castRingHom ℂ) g) ≠ 0 → F z = 0 := by
    intro z hz hgz
    obtain ⟨y, c, hc, hyz⟩ := d.R.surj z hz (fun hJ => hgz (hJ.2 g hgJ))
    have h1 : resPt d y = c () • z := by
      funext p
      simp [resPt, hyz]
    have h2 : F (resPt d y) = 0 := ha y
    rw [h1, hF] at h2
    simp only at h2
    rw [sum_secFun_smul hb.1] at h2
    exact (mul_eq_zero.1 h2).resolve_left (pow_ne_zero _ (hc ()))

  have hpts : ∀ z ∈ mcPts (ι := GlobalTheory κ) (coordIdeal ℤ d.x), F z = 0 := by
    intro z hz
    have hcl := hND Unit (GlobalTheory κ) (coordIdeal ℤ d.x) (D + 1) g d.arith hgP hz
    have hsub : {z' | z' ∈ mcPts (ι := GlobalTheory κ) (coordIdeal ℤ d.x) ∧
        eval z' (map (Int.castRingHom ℂ) g) ≠ 0} ⊆ {z' | F z' = 0} := by
      intro z' hz'
      exact hoff z' hz'.1 hz'.2
    exact closure_minimal hsub (isClosed_eq hFc continuous_const) hcl

  have : IsProbabilityMeasure d.dV := d.vol.1
  obtain ⟨y₀⟩ : Nonempty d.R.X := by
    by_contra h
    rw [not_nonempty_iff] at h
    have h1 := measure_univ (μ := d.dV)
    rw [Set.univ_eq_empty_iff.2 h, measure_empty] at h1
    exact zero_ne_one h1
  have hz₀ : resPt d y₀ ∈ mcPts (ι := GlobalTheory κ) (coordIdeal ℤ d.x) := d.R.mem y₀ y₀ (d.R.mem_U y₀)
  refine coeff_eq_zero_of_vanish (linIndep_rat_of_isSecBasis hb) fun z hz => ?_
  by_cases h0 : z = 0
  · have h1 := hpts _ hz₀
    rw [hF] at h1
    simp only at h1
    rw [h0, ← zero_smul ℂ (resPt d y₀), sum_secFun_smul hb.1, h1, mul_zero]
  · refine hpts z ⟨fun k => ?_, hz⟩
    by_contra hk
    push Not at hk
    exact h0 (funext fun p => by obtain ⟨⟨⟩, i⟩ := p; exact hk i)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PProjFrameImage
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

namespace ProjFrameImage

variable {D : ℕ} {Ω : Type} [Field Ω] {κ : Type} [Fintype κ]

theorem linForm_projMat (e : Fin (D + 1) → Ix κ) (k : Fin (D + 1)) :
    ReciprocityTheory.ChartRestriction.G.AI.I4.linForm (ι := GlobalTheory κ) (ι₂ := GlobalTheory (Fin (D + 1))) (projMat e) ⟨(), k⟩ = X (e k) := by
  classical
  simp only [ReciprocityTheory.ChartRestriction.G.AI.I4.linForm, projMat]
  rw [Finset.sum_eq_single (e k).2]
  · simp
  · intro i _ hi
    simp [Ne.symm hi]
  · simp

def coneEval (x : Ix κ → Ω) :
    MvPolynomial Unit (MRing (GlobalTheory κ) ⧸ coordIdeal ℤ x) →+* Polynomial Ω :=
  eval₂Hom (Ideal.Quotient.lift (coordIdeal ℤ x) (coneMap ℤ x).toRingHom
    (fun _a ha => (RingHom.mem_ker).1 ha)) (fun _ => 1)

theorem coneEval_graphMap (x : Ix κ → Ω) (e : Fin (D + 1) → Ix κ) (f : MRing (GlobalTheory (Fin (D + 1)))) :
    coneEval x (graphMap (coordIdeal ℤ x) (ReciprocityTheory.ChartRestriction.G.AI.I4.linForm (ι := GlobalTheory κ) (ι₂ := GlobalTheory (Fin (D + 1))) (projMat e))
        (rename (inrV (ι := GlobalTheory κ) (ι₂ := GlobalTheory (Fin (D + 1)))) f)) =
      coneMap ℤ (x ∘ e) (rename (fun q : Σ _ : Unit, Fin (D + 1) => q.2) f) := by
  set_option synthInstance.maxHeartbeats 200000 in
  induction f using MvPolynomial.induction_on with
  | C a => simp [graphMap, coneEval, coneMap]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p q hp =>
    obtain ⟨⟨⟩, k⟩ := q
    simp only [map_mul, hp, rename_X]
    congr 1
    simp [graphMap, inrV, coneEval, coneMap, linForm_projMat]

end ProjFrameImage


open ProjFrameImage in
theorem ProjFrameImage.proof : ProjFrameImage.Statement := by
  intro D Ω _ _ κ _ x e hP
  refine le_antisymm (fun f hf => ?_) bot_le
  have h0 : graphMap (coordIdeal ℤ x) (ReciprocityTheory.ChartRestriction.G.AI.I4.linForm (ι := GlobalTheory κ) (ι₂ := GlobalTheory (Fin (D + 1))) (projMat e))
      (rename (inrV (ι := GlobalTheory κ) (ι₂ := GlobalTheory (Fin (D + 1)))) f) = 0 :=
    (RingHom.mem_ker).1 (Ideal.mem_comap.1 hf)
  have h1 : rename (fun q : Σ _ : Unit, Fin (D + 1) => q.2) f ∈ coordIdeal ℤ (x ∘ e) := by
    rw [coordIdeal, RingHom.mem_ker, ← coneEval_graphMap x e f, h0, map_zero]
  rw [hP.free, Ideal.mem_bot] at h1
  have hinj : Function.Injective (fun q : Σ _ : Unit, Fin (D + 1) => q.2) := by
    rintro ⟨⟨⟩, a⟩ ⟨⟨⟩, b⟩ h
    cases h
    rfl
  exact (Ideal.mem_bot).2 (rename_injective _ hinj (by rw [h1, map_zero]))

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PProjFrameBasePtFree
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

namespace ProjFrameBasePtFree

theorem linForm_projMat {κ : Type} [Fintype κ] {D : ℕ} (e : Fin (D + 1) → Ix κ) (k : Fin (D + 1)) :
    ReciprocityTheory.ChartRestriction.G.AI.I4.linForm (ι := GlobalTheory κ) (ι₂ := GlobalTheory (Fin (D + 1))) (projMat e) ⟨(), k⟩ = X (e k) := by
  classical
  simp only [ReciprocityTheory.ChartRestriction.G.AI.I4.linForm, projMat]
  generalize e k = q
  obtain ⟨⟨⟩, j⟩ := q
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hi
    simp [Ne.symm hi]
  · simp

theorem rename_mem_span {κ : Type} {D : ℕ} (e : Fin (D + 1) → Ix κ) {h : MvPolynomial (Fin (D + 1)) ℤ} {n : ℕ}
    (hh : h.IsHomogeneous n) (hn : 0 < n) :
    rename e h ∈ Ideal.span (Set.range fun k => (X (e k) : MvPolynomial (Ix κ) ℤ)) := by
  have h1 : h ∈ Ideal.span ((X : Fin (D + 1) → MvPolynomial (Fin (D + 1)) ℤ) '' Set.univ) := by
    rw [mem_ideal_span_X_image]
    intro m hm
    by_contra hcon
    push Not at hcon
    have hm0 : m = 0 := Finsupp.ext fun i => hcon i (Set.mem_univ i)
    have := hh (mem_support_iff.mp hm)
    rw [hm0, map_zero] at this
    omega
  have h2 := Ideal.mem_map_of_mem (rename e : MvPolynomial (Fin (D + 1)) ℤ →ₐ[ℤ] MvPolynomial (Ix κ) ℤ) h1
  rw [Ideal.map_span, Set.image_image, Set.image_univ] at h2
  simpa [rename_X] using h2

theorem pow_mem (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) (x : Ix κ → Ω)
    (e : Fin (D + 1) → Ix κ) (hfr : IsProjFrame x e) (p : Ix κ) :
    ∃ N : ℕ, (X p : MvPolynomial (Ix κ) ℤ) ^ N ∈
      coordIdeal ℤ x ⊔ Ideal.span (Set.range fun k => (X (e k) : MvPolynomial (Ix κ) ℤ)) := by
  obtain ⟨q, hmon, hq⟩ := hfr.integral p
  set N := q.natDegree with hNdef
  have hcoef : ∀ j, ∃ f : MvPolynomial (Fin (D + 1)) ℤ,
      coneMap ℤ (x ∘ e) f = ((q.coeff j : coneRing ℤ (x ∘ e)) : Polynomial Ω) :=
    fun j => (q.coeff j).2
  choose f hf using hcoef
  set F : MvPolynomial (Ix κ) ℤ := X p ^ N +
      ∑ j ∈ Finset.range N, rename e (homogeneousComponent (N - j) (f j)) * X p ^ j with hFdef
  have hFh : F.IsHomogeneous N := by
    refine (isHomogeneous_X_pow p N).add (IsHomogeneous.sum _ _ _ fun j hj => ?_)
    have hj' : N - j + j = N := Nat.sub_add_cancel (Finset.mem_range.mp hj).le
    have := ((homogeneousComponent_isHomogeneous (N - j) (f j)).rename_isHomogeneous (f := e)).mul
      (isHomogeneous_X_pow p j)
    rwa [hj'] at this
  have hFx : aeval x F = 0 := by
    have h0 := congrArg (fun r : Polynomial Ω => r.coeff N) hq
    simp only [Polynomial.coeff_zero] at h0
    rw [hmon.as_sum, Polynomial.eval₂_add, Polynomial.eval₂_finsetSum, Polynomial.coeff_add,
      Polynomial.finsetSum_coeff] at h0
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← h0, hFdef, map_add (f := _), map_sum]
    congr 1
    · rw [Polynomial.eval₂_X_pow, mul_pow, ← Polynomial.C_pow, Polynomial.coeff_C_mul_X_pow, if_pos rfl,
        map_pow, aeval_X]
    · refine Finset.sum_congr rfl fun j hj => ?_
      have hjN : j ≤ N := (Finset.mem_range.mp hj).le
      rw [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X_pow, mul_pow, ← Polynomial.C_pow,
        ← mul_assoc, Polynomial.coeff_mul_X_pow', if_pos hjN, Polynomial.coeff_mul_C]
      rw [map_mul, map_pow, aeval_X, aeval_rename]
      have : algebraMap (coneRing ℤ (x ∘ e)) (Polynomial Ω) (q.coeff j) = coneMap ℤ (x ∘ e) (f j) := (hf j).symm
      rw [this, coeff_coneMap]
  have hFP : F ∈ coordIdeal ℤ x := mem_coordIdeal_of_isHomogeneous ℤ x hFh hFx
  refine ⟨N, ?_⟩
  have hsum : (∑ j ∈ Finset.range N, rename e (homogeneousComponent (N - j) (f j)) * X p ^ j) ∈
      Ideal.span (Set.range fun k => (X (e k) : MvPolynomial (Ix κ) ℤ)) := by
    refine Ideal.sum_mem _ fun j hj => Ideal.mul_mem_right _ _ ?_
    have hjN : j < N := Finset.mem_range.mp hj
    exact rename_mem_span e (homogeneousComponent_isHomogeneous (N - j) (f j)) (by omega)
  have : (X p : MvPolynomial (Ix κ) ℤ) ^ N =
      F - ∑ j ∈ Finset.range N, rename e (homogeneousComponent (N - j) (f j)) * X p ^ j := by
    rw [hFdef]; ring
  rw [this]
  exact Ideal.sub_mem _ (Ideal.mem_sup_left hFP) (Ideal.mem_sup_right hsum)

end ProjFrameBasePtFree


open ProjFrameBasePtFree in
theorem ProjFrameBasePtFree.proof : ProjFrameBasePtFree.Statement := by
  intro D Ω _ _ κ _ x e hfr k₂ i
  obtain ⟨N, hN⟩ := pow_mem D Ω κ x e hfr ⟨(), i ()⟩
  refine ⟨N, ?_⟩
  have hspan : (Set.range fun j : GlobalTheory (Fin (D + 1)) k₂ =>
      ReciprocityTheory.ChartRestriction.G.AI.I4.linForm (ι := GlobalTheory κ) (ι₂ := GlobalTheory (Fin (D + 1))) (projMat e) ⟨k₂, j⟩) =
      Set.range fun k => (X (e k) : MvPolynomial (Ix κ) ℤ) := by
    cases k₂
    ext
    simp [linForm_projMat]
  rw [hspan, Fintype.prod_unique]
  exact hN

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
