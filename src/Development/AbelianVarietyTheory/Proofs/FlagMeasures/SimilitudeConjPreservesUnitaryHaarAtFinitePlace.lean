module

public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RationalVectorsSameLengthOneUnitaryOrbit
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsHaarFrameStabiliserCompatibleFibre

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GramMapFibreMeasureUnitriangularInvariant
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitriangularColumnOpsPreserveHaarTuplesHermitia
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitriangularColumnOpsPreserveHaarTuplesHermitia
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal

namespace GlobalTheory.UnitriTuple

theorem exists_compactOpen (k G : Type*) [NormedField k] [IsUltrametricDist k] [ProperSpace k]
    [AddCommGroup G] [Module k G] [Module.Finite k G] [TopologicalSpace G] [IsModuleTopology k G] :
    ∃ K : AddSubgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) := by
  have : IsTopologicalAddGroup G := IsModuleTopology.topologicalAddGroup k G
  let e₀ : G ≃ₗ[k] (Fin (Module.finrank k G) → k) := (Module.finBasis k G).equivFun
  let e : G ≃ₜ (Fin (Module.finrank k G) → k) :=
    { e₀.toEquiv with
      continuous_toFun := IsModuleTopology.continuous_of_linearMap e₀.toLinearMap
      continuous_invFun := IsModuleTopology.continuous_of_linearMap e₀.symm.toLinearMap }
  let K₀ := IsUltrametricDist.closedBall_openAddSubgroup (Fin (Module.finrank k G) → k) one_pos
  exact ⟨K₀.toAddSubgroup.comap e₀.toLinearMap.toAddMonoidHom, K₀.isOpen.preimage e.continuous,
    e.isCompact_preimage.2 (isCompact_closedBall (0 : Fin (Module.finrank k G) → k) 1)⟩

theorem map_add_nilpotent_of_compactOpen {G : Type*} [AddCommGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsAddHaarMeasure]
    (K : AddSubgroup G) (hKo : IsOpen (K : Set G)) (hKc : IsCompact (K : Set G))
    (N : Module.End ℤ G) (hNc : Continuous N) (hN : IsNilpotent N) :
    μ.map (fun x => x + N x) = μ := by
  have hpow : ∀ (f : Module.End ℤ G), Continuous f → ∀ j : ℕ, Continuous (f ^ j : Module.End ℤ G) :=
    fun f hf j => by rw [Module.End.coe_pow]; exact hf.iterate j
  have hnegc : Continuous (-N : Module.End ℤ G) := by
    have : ⇑(-N : Module.End ℤ G) = fun x => -(N x) := rfl
    rw [this]; exact hNc.neg
  obtain ⟨m, hm⟩ := hN
  let B : AddSubgroup G := ⨅ j : ℕ, K.comap (N ^ j).toAddMonoidHom
  have hB : ∀ x, x ∈ B ↔ ∀ j : ℕ, (N ^ j) x ∈ K := fun x => by
    simp [B, AddSubgroup.mem_iInf]
  have hBo : IsOpen (B : Set G) := by
    have : (B : Set G) = ⋂ j ∈ Finset.range m, (N ^ j : Module.End ℤ G) ⁻¹' (K : Set G) := by
      ext x
      simp only [SetLike.mem_coe, hB, Set.mem_iInter, Set.mem_preimage, Finset.mem_range]
      refine ⟨fun h j _ => h j, fun h j => ?_⟩
      by_cases hj : j < m
      · exact h j hj
      · rw [pow_eq_zero_of_le (not_lt.1 hj) hm]; exact K.zero_mem
    rw [this]
    exact isOpen_biInter_finset fun j _ => hKo.preimage (hpow N hNc j)
  have hBc : IsCompact (B : Set G) :=
    hKc.of_isClosed_subset (B.isClosed_of_isOpen hBo) fun x hx => by
      simpa using (hB x).1 hx 0
  have hNB : ∀ x ∈ B, N x ∈ B := fun x hx => (hB _).2 fun j => by
    rw [← Module.End.mul_apply, ← pow_succ]; exact (hB x).1 hx _
  have hNp : ∀ (j : ℕ), ∀ x ∈ B, ((-N) ^ j) x ∈ B := fun j => by
    induction j with
    | zero => intro x hx; simpa using hx
    | succ j ih =>
      intro x hx
      rw [pow_succ', Module.End.mul_apply, LinearMap.neg_apply]
      exact B.neg_mem (hNB _ (ih x hx))
  have hm' : (-N) ^ m = 0 := by rw [neg_pow, hm, mul_zero]
  have h1 : (∑ j ∈ Finset.range m, (-N) ^ j) * (1 + N) = 1 := by
    have := geom_sum_mul_neg (-N) m
    rwa [hm', sub_zero, sub_neg_eq_add] at this
  have h2 : (1 + N) * (∑ j ∈ Finset.range m, (-N) ^ j) = 1 := by
    have := mul_neg_geom_sum (-N) m
    rwa [hm', sub_zero, sub_neg_eq_add] at this
  have hinv : Continuous (∑ j ∈ Finset.range m, (-N) ^ j : Module.End ℤ G) := by
    have : ⇑(∑ j ∈ Finset.range m, (-N) ^ j : Module.End ℤ G) =
        fun x => ∑ j ∈ Finset.range m, ((-N) ^ j : Module.End ℤ G) x :=
      funext fun x => LinearMap.sum_apply _ _ _
    rw [this]
    exact continuous_finsetSum _ fun j _ => hpow _ hnegc j
  let L : G ≃ₜ+ G :=
    { toFun := fun x => x + N x
      invFun := (∑ j ∈ Finset.range m, (-N) ^ j : Module.End ℤ G)
      left_inv := fun x => LinearMap.congr_fun h1 x
      right_inv := fun x => LinearMap.congr_fun h2 x
      map_add' := fun x y => by rw [map_add (f := _)]; abel
      continuous_toFun := continuous_id.add hNc
      continuous_invFun := hinv }
  have hLB : L ⁻¹' (B : Set G) = B := by
    ext x
    refine ⟨fun hx => ?_, fun hx => B.add_mem hx (hNB x hx)⟩
    have : x = (∑ j ∈ Finset.range m, (-N) ^ j : Module.End ℤ G) (L x) := (L.left_inv x).symm
    rw [this, LinearMap.sum_apply]
    exact B.sum_mem fun j _ => hNp j _ hx
  change μ.map L = μ
  have : (μ.map L).IsAddHaarMeasure := L.isAddHaarMeasure_map μ
  have h3 := Measure.isAddLeftInvariant_eq_smul (μ.map L) μ
  have h4 : μ.map L B = μ B := by
    rw [Measure.map_apply (show Continuous L from L.continuous).measurable hBo.measurableSet, hLB]
  have h5 : μ B ≠ 0 := (hBo.measure_pos μ ⟨0, B.zero_mem⟩).ne'
  have h6 : μ B ≠ ⊤ := hBc.measure_lt_top.ne
  have h7 : Measure.addHaarScalarFactor (μ.map L) μ = 1 := by
    rw [h3, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h4
    have := (ENNReal.mul_left_inj h5 h6).1 (h4.trans (one_mul _).symm)
    exact_mod_cast this
  rw [h3, h7, one_smul]

theorem sub_one_pow {R : Type*} [CommRing R] {a : ℕ} (u : Matrix (Fin a) (Fin a) R)
    (h1 : ∀ i, u i i = 1) (h0 : ∀ i j, j < i → u i j = 0) : (u - 1) ^ a = 0 := by
  refine GlobalTheory.UnitriHaar.nilpotent_of_strict _ fun i j h => ?_
  rcases (not_lt.1 h).eq_or_lt with rfl | h
  · simp [h1]
  · simp [h0 i j h, Matrix.one_apply_ne h.ne']

def colOp {R : Type*} [CommRing R] {a n : ℕ} (w : Matrix (Fin a) (Fin a) R) :
    Module.End R (Fin a → Fin n → R) where
  toFun X b := ∑ c, w c b • X c
  map_add' X Y := by funext b; simp [Finset.sum_add_distrib, smul_add]
  map_smul' r X := by funext b; simp [Finset.smul_sum, smul_comm r]

theorem colOp_pow {R : Type*} [CommRing R] {a n : ℕ} (w : Matrix (Fin a) (Fin a) R) (j : ℕ)
    (X : Fin a → Fin n → R) (b : Fin a) :
    ((colOp (n := n) w ^ j) X) b = ∑ c, (w ^ j) c b • X c := by
  induction j generalizing b with
  | zero => simp [Matrix.one_apply]
  | succ j ih =>
    rw [pow_succ', Module.End.mul_apply, pow_succ]
    change ∑ c, w c b • (((colOp (n := n) w ^ j) X) c) = _
    simp only [ih, Finset.smul_sum, Matrix.mul_apply, Finset.sum_smul, smul_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by rw [mul_comm]


open GlobalTheory.GaugeEx in
theorem unitri_haar : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F)), ∀ (a : ℕ) (u : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)), (∀ i, u i i = 1) → (∀ i j, j < i → u i j = 0) → (∀ μ : Measure (Fin a → Fin n → Fv F v ⊗[F] E), μ.IsAddHaarMeasure → μ.map (fun X b => ∑ c, u c b • X c) = μ) ∧ ∀ ν : Measure (HermR (Fv F v) σ a), ν.IsAddHaarMeasure → ∀ φ : HermR (Fv F v) σ a → HermR (Fv F v) σ a, (∀ S, (φ S : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) = (u.map (sigR (Fv F v) σ)).transpose * (S : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) * u) → ν.map φ = ν := by
  intro F E _ _ _ _ _ σ _ n J _ v a u h1 h0
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  refine ⟨fun μ hμ => ?_, fun ν hν φ hφ => ?_⟩
  · let N := colOp (n := n) (u - 1)
    have hN : IsNilpotent N := ⟨a, LinearMap.ext fun X => funext fun b => by
      rw [colOp_pow, sub_one_pow u h1 h0]; simp⟩
    have hN' : IsNilpotent (N.restrictScalars (Fv F v) : Module.End (Fv F v) _) := by
      obtain ⟨m, hm⟩ := hN
      refine ⟨m, LinearMap.ext fun x => ?_⟩
      have := LinearMap.congr_fun hm x
      rw [Module.End.pow_apply] at this ⊢
      exact this
    have h2 := GlobalTheory.UnitriHaar.map_add_nilpotent μ _ hN'
    have hx : (fun (X : Fin a → Fin n → Fv F v ⊗[F] E) b => ∑ c, u c b • X c) =
        fun X => X + N.restrictScalars (Fv F v) X := by
      funext X b
      change _ = X b + ∑ c, (u - 1) c b • X c
      simp [sub_smul, Finset.sum_sub_distrib, Matrix.one_apply]
    rw [hx]; exact h2
  · have hTR : IsTopologicalRing (Fv F v) := inferInstance
    let Ev := Fv F v ⊗[F] E
    have : LocallyCompactSpace (Matrix (Fin a) (Fin a) Ev) :=
      inferInstanceAs (LocallyCompactSpace (Fin a → Fin a → Ev))
    have : SecondCountableTopology (Matrix (Fin a) (Fin a) Ev) :=
      inferInstanceAs (SecondCountableTopology (Fin a → Fin a → Ev))
    have : BorelSpace (HermR (Fv F v) σ a) := ⟨rfl⟩
    have hc : IsClosed (HermR (Fv F v) σ a : Set (Matrix (Fin a) (Fin a) Ev)) := by
      have : (HermR (Fv F v) σ a : Set (Matrix (Fin a) (Fin a) Ev)) =
          ⋂ i, ⋂ j, {S | sigR (Fv F v) σ (S j i) = S i j} := by
        ext S
        simp only [Set.mem_iInter, Set.mem_setOf_eq]
        rfl
      rw [this]
      refine isClosed_iInter fun i => isClosed_iInter fun j => isClosed_eq ?_ ?_
      · exact (GlobalTheory.AdelicUnitaryTop.continuous_sigR (Fv F v) σ).comp (continuous_id.matrix_elem j i)
      · exact continuous_id.matrix_elem i j
    have : LocallyCompactSpace (HermR (Fv F v) σ a) :=
      hc.isClosedEmbedding_subtypeVal.locallyCompactSpace
    have : SecondCountableTopology (HermR (Fv F v) σ a) :=
      hc.isClosedEmbedding_subtypeVal.isEmbedding.secondCountableTopology
    obtain ⟨K₀, hK₀o, hK₀c⟩ := exists_compactOpen (Fv F v) (Fin a → Fin a → Ev)
    let K : AddSubgroup (HermR (Fv F v) σ a) :=
      AddSubgroup.comap (HermR (Fv F v) σ a).subtype K₀
    have hKo : IsOpen (K : Set (HermR (Fv F v) σ a)) := hK₀o.preimage continuous_subtype_val
    have hKc : IsCompact (K : Set (HermR (Fv F v) σ a)) :=
      hc.isClosedEmbedding_subtypeVal.isCompact_preimage hK₀c
    set A : Matrix (Fin a) (Fin a) Ev := (u.map (sigR (Fv F v) σ)).transpose with hA
    have hS1 : ∀ i, (u.map (sigR (Fv F v) σ)) i i = 1 := fun i => by simp [h1]
    have hS0 : ∀ i j, j < i → (u.map (sigR (Fv F v) σ)) i j = 0 := fun i j h => by simp [h0 i j h]
    have hAn : (A - 1) ^ a = 0 := by
      have := sub_one_pow _ hS1 hS0
      have h3 : A - 1 = (u.map (sigR (Fv F v) σ) - 1).transpose := by
        rw [Matrix.transpose_sub, Matrix.transpose_one]
      rw [h3, ← Matrix.transpose_pow, this, Matrix.transpose_zero]
    have hun : (u - 1) ^ a = 0 := sub_one_pow u h1 h0
    let La : Module.End Ev (Matrix (Fin a) (Fin a) Ev) := LinearMap.mulLeft Ev A
    let Ru : Module.End Ev (Matrix (Fin a) (Fin a) Ev) := LinearMap.mulRight Ev u
    have hLR : Commute La Ru := LinearMap.commute_mulLeft_right A u
    have hLn : IsNilpotent (La - 1) := by
      have : La - 1 = LinearMap.mulLeft Ev (A - 1) := by
        ext1 S; simp [La, sub_mul]
      rw [this]
      exact ⟨a, by rw [LinearMap.pow_mulLeft, hAn, LinearMap.mulLeft_zero_eq_zero]⟩
    have hRn : IsNilpotent (Ru - 1) := by
      have : Ru - 1 = LinearMap.mulRight Ev (u - 1) := by
        ext1 S; simp [Ru, mul_sub]
      rw [this]
      exact ⟨a, by rw [LinearMap.pow_mulRight, hun, LinearMap.mulRight_zero_eq_zero]⟩
    have hTn : IsNilpotent (La * Ru - 1) := by
      have : La * Ru - 1 = (La - 1) * Ru + (Ru - 1) := by noncomm_ring
      rw [this]
      have c1 : Commute (La - 1) Ru := hLR.sub_left (Commute.one_left _)
      have c2 : Commute ((La - 1) * Ru) (Ru - 1) :=
        Commute.mul_left (c1.sub_right (Commute.one_right _))
          ((Commute.refl Ru).sub_right (Commute.one_right _))
      exact c2.isNilpotent_add (c1.isNilpotent_mul_right hLn) hRn
    have hadd : ∀ S S', φ (S + S') = φ S + φ S' := fun S S' => Subtype.ext (by
      rw [AddSubgroup.coe_add, hφ, hφ, hφ, AddSubgroup.coe_add, mul_add, add_mul])
    let N₀ : HermR (Fv F v) σ a →+ HermR (Fv F v) σ a :=
      AddMonoidHom.mk' (fun S => φ S - S) fun S S' => by rw [hadd]; abel
    let N : Module.End ℤ (HermR (Fv F v) σ a) := N₀.toIntLinearMap
    have hNa : ∀ S, ((N S : HermR (Fv F v) σ a) : Matrix (Fin a) (Fin a) Ev) =
        (La * Ru - 1) (S : Matrix (Fin a) (Fin a) Ev) := fun S => by
      change ((φ S - S : HermR (Fv F v) σ a) : Matrix (Fin a) (Fin a) Ev) = _
      rw [AddSubgroup.coe_sub, hφ]
      simp [La, Ru, mul_assoc]
    have hNp : ∀ (j : ℕ) S, (((N ^ j) S : HermR (Fv F v) σ a) : Matrix (Fin a) (Fin a) Ev) =
        ((La * Ru - 1) ^ j) (S : Matrix (Fin a) (Fin a) Ev) := fun j => by
      induction j with
      | zero => intro S; simp
      | succ j ih =>
        intro S
        rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, hNa, ih]
    have hN : IsNilpotent N := by
      obtain ⟨m, hm⟩ := hTn
      refine ⟨m, LinearMap.ext fun S => Subtype.ext ?_⟩
      rw [hNp, hm]; rfl
    have hNc : Continuous N := by
      refine continuous_induced_rng.2 ?_
      have : (Subtype.val ∘ ⇑N) = fun S : HermR (Fv F v) σ a =>
          A * (S : Matrix (Fin a) (Fin a) Ev) * u - (S : Matrix (Fin a) (Fin a) Ev) :=
        funext fun S => by
          change ((N S : HermR (Fv F v) σ a) : Matrix (Fin a) (Fin a) Ev) = _
          rw [hNa]; simp [La, Ru, mul_assoc]
      rw [this]
      exact ((continuous_const.matrix_mul continuous_subtype_val).matrix_mul continuous_const).sub
        continuous_subtype_val
    have h2 := map_add_nilpotent_of_compactOpen ν K hKo hKc N hNc hN
    have hx : φ = fun S => S + N S := funext fun S => by
      change φ S = S + (φ S - S); abel
    rw [hx]; exact h2

end GlobalTheory.UnitriTuple
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitriangularColumnOpsPreserveHaarTuplesHermitiaStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitriangular_column_ops_preserve_haar_tuples_hermitian : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F)), ∀ (a : ℕ) (u : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)), (∀ i, u i i = 1) → (∀ i j, j < i → u i j = 0) → (∀ μ : Measure (Fin a → Fin n → Fv F v ⊗[F] E), μ.IsAddHaarMeasure → μ.map (fun X b => ∑ c, u c b • X c) = μ) ∧ ∀ ν : Measure (HermR (Fv F v) σ a), ν.IsAddHaarMeasure → ∀ φ : HermR (Fv F v) σ a → HermR (Fv F v) σ a, (∀ S, (φ S : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) = (u.map (sigR (Fv F v) σ)).transpose * (S : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) * u) → ν.map φ = ν := by
  first | exact @GlobalTheory.UnitriTuple.unitri_haar | exact GlobalTheory.UnitriTuple.unitri_haar | (intros; apply GlobalTheory.UnitriTuple.unitri_haar <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GramMapFibreMeasureUnitriangularInvariant
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal

namespace GlobalTheory.FibreUnitri
open Matrix

section Alg
variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  (σ : E →ₐ[F] E)

theorem sigR_invol (hσ : ∀ x, σ (σ x) = x) (z : R ⊗[F] E) : sigR R σ (sigR R σ z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [sigR, hσ]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem gramR_comb {M a : ℕ} (J : Matrix (Fin M) (Fin M) E) (u : Matrix (Fin a) (Fin a) (R ⊗[F] E))
    (X : Fin a → Fin M → R ⊗[F] E) :
    gramR R σ J (fun b => ∑ c, u c b • X c) = (u.map (sigR R σ)).transpose * gramR R σ J X * u := by
  ext i j
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [gramR, hR, Formalism.UG.hform, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]
  conv_lhs => enter [2, k]; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => enter [2, d, 2, k]; rw [Finset.sum_comm]
  conv_lhs => enter [2, d]; rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun c _ =>
    Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring

def cgr {a : ℕ} (m A : Matrix (Fin a) (Fin a) (R ⊗[F] E)) : Matrix (Fin a) (Fin a) (R ⊗[F] E) :=
  (m.map (sigR R σ)).transpose * A * m

theorem cgr_cgr {a : ℕ} (u w A : Matrix (Fin a) (Fin a) (R ⊗[F] E)) (huw : u * w = 1) :
    cgr R σ w (cgr R σ u A) = A := by
  have e1 : (w.map (sigR R σ)).transpose * (u.map (sigR R σ)).transpose = 1 := by
    rw [← Matrix.transpose_mul, ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, ← map_mul, huw,
      map_one, Matrix.transpose_one]
  unfold cgr
  calc (w.map (sigR R σ)).transpose * ((u.map (sigR R σ)).transpose * A * u) * w
      = ((w.map (sigR R σ)).transpose * (u.map (sigR R σ)).transpose) * A * (u * w) := by
        simp only [Matrix.mul_assoc]
    _ = A := by rw [e1, huw, Matrix.one_mul, Matrix.mul_one]

theorem cgr_mem (hσ : ∀ x, σ (σ x) = x) {a : ℕ} (m : Matrix (Fin a) (Fin a) (R ⊗[F] E))
    (S : HermR R σ a) : cgr R σ m (S : Matrix (Fin a) (Fin a) (R ⊗[F] E)) ∈ HermR R σ a := by
  have hS : ∀ p q, sigR R σ ((S : Matrix (Fin a) (Fin a) (R ⊗[F] E)) q p) =
      (S : Matrix (Fin a) (Fin a) (R ⊗[F] E)) p q := S.2
  intro p q
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [cgr, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul,
    sigR_invol R σ hσ, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun l _ => ?_
  rw [hS]
  ring

def cgrH (hσ : ∀ x, σ (σ x) = x) {a : ℕ} (m : Matrix (Fin a) (Fin a) (R ⊗[F] E)) (S : HermR R σ a) :
    HermR R σ a :=
  ⟨cgr R σ m S, cgr_mem R σ hσ m S⟩

theorem comb_comb {M a : ℕ} (u w : Matrix (Fin a) (Fin a) (R ⊗[F] E)) (X : Fin a → Fin M → R ⊗[F] E) :
    (fun b => ∑ c, w c b • ∑ d, u d c • X d) = fun b => ∑ d, (u * w) d b • X d := by
  funext b
  simp only [Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun c _ => by rw [mul_comm]

theorem comb_one {M a : ℕ} (X : Fin a → Fin M → R ⊗[F] E) :
    (fun b => ∑ d, (1 : Matrix (Fin a) (Fin a) (R ⊗[F] E)) d b • X d) = X := by
  funext b
  simp [Matrix.one_apply]

theorem linIndep_comb {M a : ℕ} (m m' : Matrix (Fin a) (Fin a) (R ⊗[F] E)) (h : m' * m = 1)
    (X : Fin a → Fin M → R ⊗[F] E) (hX : LinearIndependent (R ⊗[F] E) X) :
    LinearIndependent (R ⊗[F] E) (fun b => ∑ c, m c b • X c) := by
  rw [Fintype.linearIndependent_iff] at hX ⊢
  intro g hg
  have h0 : ∑ c, (m *ᵥ g) c • X c = 0 := by
    rw [← hg]
    simp only [Matrix.mulVec, dotProduct, Finset.smul_sum, smul_smul, Finset.sum_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => by rw [mul_comm]
  have hv : m *ᵥ g = 0 := funext (hX _ h0)
  have : g = m' *ᵥ (m *ᵥ g) := by rw [Matrix.mulVec_mulVec, h, Matrix.one_mulVec]
  intro i
  rw [this, hv, Matrix.mulVec_zero]
  rfl

end Alg

section Abstract

variable {V Y X : Type} [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V]
  [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]

theorem isFibreFamily_transport (e : V ≃ₜ V) (r : X ≃ₜ X) {μ : Measure V} {f : V → Y} {ι : X → Y}
    {U : Set V} {ν : Measure X} {fib : X → Measure V} (hfib : IsFibreFamily μ f ι U ν Set.univ fib)
    (hμ : μ.map e.toMeasurableEquiv = μ) (hν : ν.map r.toMeasurableEquiv = ν)
    (hf : ∀ x b, f (e x) = ι (r b) ↔ f x = ι b) (hU : e ⁻¹' U = U) :
    IsFibreFamily μ f ι U ν Set.univ
      (fun b => (fib (r.symm b)).map e.toMeasurableEquiv) := by
  set em := e.toMeasurableEquiv with hem
  set rm := r.toMeasurableEquiv with hrm
  have hU' : em ⁻¹' U = U := hU
  refine ⟨fun b => ?_, fun φ hφ => ?_, fun φ hc hcs hts => ?_⟩
  · rw [MeasurableEquiv.map_apply]
    have : em ⁻¹' (f ⁻¹' {ι b} ∩ U)ᶜ = (f ⁻¹' {ι (r.symm b)} ∩ U)ᶜ := by
      ext x
      have hx : e x ∈ U ↔ x ∈ U := Set.ext_iff.1 hU x
      have hb := hf x (r.symm b)
      rw [r.apply_symm_apply] at hb
      simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_inter_iff, Set.mem_singleton_iff]
      change ¬ (f (e x) = ι b ∧ e x ∈ U) ↔ ¬ (f x = ι (r.symm b) ∧ x ∈ U)
      rw [hb, hx]
    rw [this]
    exact hfib.1 _
  · have key : ∫⁻ x in U, φ (em x) ∂μ = ∫⁻ x in U, φ x ∂μ := by
      calc ∫⁻ x in U, φ (em x) ∂μ = ∫⁻ x, φ (em x) ∂(μ.restrict (em ⁻¹' U)) := by rw [hU']
        _ = ∫⁻ x, φ x ∂((μ.restrict (em ⁻¹' U)).map em) := (lintegral_map_equiv _ _).symm
        _ = ∫⁻ x, φ x ∂((μ.map em).restrict U) := by rw [MeasurableEquiv.restrict_map]
        _ = ∫⁻ x in U, φ x ∂μ := by rw [hμ]
    rw [← key, hfib.2.1 (fun x => φ (em x)) (hφ.comp em.measurable)]
    have h2 : ∀ c, ∫⁻ x, φ (em x) ∂(fib c) = ∫⁻ x, φ x ∂((fib (r.symm (rm c))).map em) := by
      intro c
      rw [lintegral_map_equiv]
      change _ = ∫⁻ x, φ (em x) ∂(fib (r.symm (r c)))
      rw [r.symm_apply_apply]
    simp_rw [h2]
    conv_rhs => rw [← hν]
    exact (lintegral_map_equiv (fun b => ∫⁻ x, φ x ∂((fib (r.symm b)).map em)) rm).symm
  · have hts' : tsupport (φ ∘ e) ⊆ U := by
      rw [tsupport, Function.support_comp_eq_preimage, ← e.preimage_closure, ← hU]
      exact Set.preimage_mono hts
    obtain ⟨h1, h2⟩ := hfib.2.2 (φ ∘ e) (hc.comp e.continuous) (hcs.comp_homeomorph e) hts'
    refine ⟨fun b _ => (integrable_map_equiv em φ).2 (h1 _ (Set.mem_univ _)), ?_⟩
    have e2 : (fun b => ∫ x, φ x ∂((fib (r.symm b)).map em)) =
        (fun c => ∫ x, (φ ∘ e) x ∂(fib c)) ∘ r.symm :=
      funext fun b => integral_map_equiv _ _
    rw [e2]
    have h3 : Continuous fun c => ∫ x, (φ ∘ e) x ∂(fib c) := continuousOn_univ.1 h2
    exact (h3.comp r.symm.continuous).continuousOn

end Abstract
end GlobalTheory.FibreUnitri

namespace GlobalTheory.FibreUnitri
open Matrix

theorem fibre_unitri_invariant : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F)), ∀ a : ℕ, ∀ (μ : Measure (Fin a → Fin n → Fv F v ⊗[F] E)) (ν : Measure (HermR (Fv F v) σ a)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → ∀ fib : HermR (Fv F v) σ a → Measure (Fin a → Fin n → Fv F v ⊗[F] E), IsFibreFamily μ (gramR (Fv F v) σ J) Subtype.val {X | LinearIndependent (Fv F v ⊗[F] E) X} ν Set.univ fib → ∀ (S : HermR (Fv F v) σ a) (u : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)), (∀ i, u i i = 1) → (∀ i j, j < i → u i j = 0) → (u.map (sigR (Fv F v) σ)).transpose * (S : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) * u = (S : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) → (fib S).map (fun X b => ∑ c, u c b • X c) = fib S := by
  intro F E _ _ _ _ _ σ hE n J hJ v a μ ν hμ hν fib hfib S u hdiag htri hS
  have hσ : ∀ x, σ (σ x) = x := PI.VolStabS.sigma_invol σ hE.2.2.2
  obtain ⟨hring, -, -, hsc, -⟩ := GlobalTheory.LocalUnitaryTop.top_facts F E σ hE n J hJ v
  have : BorelSpace (Fv F v ⊗[F] E) := ⟨rfl⟩
  have : BorelSpace (HermR (Fv F v) σ a) := ⟨rfl⟩

  have hdet : u.det = 1 := by
    rw [Matrix.det_of_upperTriangular (fun i j hij => htri i j hij)]
    simp [hdiag]
  have hu : IsUnit u.det := by rw [hdet]; exact isUnit_one
  set w := u⁻¹ with hw
  have huw : u * w = 1 := Matrix.mul_nonsing_inv u hu
  have hwu : w * u = 1 := Matrix.nonsing_inv_mul u hu

  have hcont : ∀ m : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E),
      Continuous (fun (X : Fin a → Fin n → Fv F v ⊗[F] E) b => ∑ c, m c b • X c) := by
    intro m
    refine continuous_pi fun b => continuous_finsetSum _ fun c _ => ?_
    exact (continuous_apply c).const_smul (m c b)
  let e : (Fin a → Fin n → Fv F v ⊗[F] E) ≃ₜ (Fin a → Fin n → Fv F v ⊗[F] E) :=
    { toFun := fun X b => ∑ c, u c b • X c
      invFun := fun X b => ∑ c, w c b • X c
      left_inv := fun X => by
        show (fun b => ∑ c, w c b • ∑ d, u d c • X d) = X
        rw [comb_comb, huw, comb_one]
      right_inv := fun X => by
        show (fun b => ∑ c, u c b • ∑ d, w d c • X d) = X
        rw [comb_comb, hwu, comb_one]
      continuous_toFun := hcont u
      continuous_invFun := hcont w }

  have hcontH : ∀ m : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E), Continuous (cgrH (Fv F v) σ hσ m) := by
    intro m
    refine Continuous.subtype_mk ?_ _
    exact (continuous_const.matrix_mul continuous_subtype_val).matrix_mul continuous_const
  let r : HermR (Fv F v) σ a ≃ₜ HermR (Fv F v) σ a :=
    { toFun := cgrH (Fv F v) σ hσ u
      invFun := cgrH (Fv F v) σ hσ w
      left_inv := fun T => Subtype.ext (cgr_cgr (Fv F v) σ u w _ huw)
      right_inv := fun T => Subtype.ext (cgr_cgr (Fv F v) σ w u _ hwu)
      continuous_toFun := hcontH u
      continuous_invFun := hcontH w }
  obtain ⟨hμu, hνu⟩ := GlobalTheory.T.unitriangular_column_ops_preserve_haar_tuples_hermitian F E σ hE n J hJ v a u hdiag htri
  have hμe : μ.map e.toMeasurableEquiv = μ := hμu μ hμ
  have hνr : ν.map r.toMeasurableEquiv = ν := hνu ν hν r (fun T => rfl)
  have hf : ∀ X T, gramR (Fv F v) σ J (e X) = ((r T : HermR (Fv F v) σ a) :
      Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) ↔
      gramR (Fv F v) σ J X = (T : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) := by
    intro X T
    have h1 : gramR (Fv F v) σ J (e X) = cgr (Fv F v) σ u (gramR (Fv F v) σ J X) :=
      gramR_comb (Fv F v) σ J u X
    have h2 : ((r T : HermR (Fv F v) σ a) : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) =
        cgr (Fv F v) σ u T := rfl
    rw [h1, h2]
    constructor
    · intro h
      have := congrArg (cgr (Fv F v) σ w) h
      rwa [cgr_cgr _ _ _ _ _ huw, cgr_cgr _ _ _ _ _ huw] at this
    · intro h
      rw [h]
  have hU : e ⁻¹' {X | LinearIndependent (Fv F v ⊗[F] E) X} =
      {X | LinearIndependent (Fv F v ⊗[F] E) X} := by
    ext X
    constructor
    · intro h
      have h' := linIndep_comb (Fv F v) w u huw _ h
      have e2 : (fun b => ∑ c, w c b • (e X) c) = X := e.left_inv X
      rw [e2] at h'
      exact h'
    · intro h
      exact linIndep_comb (Fv F v) u w hwu X h
  have hfam := isFibreFamily_transport e r hfib hμe hνr hf hU
  have heq := GlobalTheory.LocalFibreUnique.fibre_family_unique F E σ hE n J hJ v a μ ν hμ hν fib hfib _ hfam
  have hrS : r.symm S = S := by
    rw [Homeomorph.symm_apply_eq]
    exact Subtype.ext hS.symm
  have := congrFun heq S
  simp only [hrS] at this
  exact this.symm

end GlobalTheory.FibreUnitri
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GramMapFibreMeasureUnitriangularInvariantStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gramMap_fibreMeasure_unitriangular_invariant : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F)), ∀ a : ℕ, ∀ (μ : Measure (Fin a → Fin n → Fv F v ⊗[F] E)) (ν : Measure (HermR (Fv F v) σ a)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → ∀ fib : HermR (Fv F v) σ a → Measure (Fin a → Fin n → Fv F v ⊗[F] E), IsFibreFamily μ (gramR (Fv F v) σ J) Subtype.val {X | LinearIndependent (Fv F v ⊗[F] E) X} ν Set.univ fib → ∀ (S : HermR (Fv F v) σ a) (u : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)), (∀ i, u i i = 1) → (∀ i j, j < i → u i j = 0) → (u.map (sigR (Fv F v) σ)).transpose * (S : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) * u = (S : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) → (fib S).map (fun X b => ∑ c, u c b • X c) = fib S := by
  first | exact @GlobalTheory.FibreUnitri.fibre_unitri_invariant | exact GlobalTheory.FibreUnitri.fibre_unitri_invariant | (intros; apply GlobalTheory.FibreUnitri.fibre_unitri_invariant <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SimilitudeConjPreservesUnitaryHaarAtFinitePlace
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal

namespace GlobalTheory.ConjStabiliserHaar

section Abstract

variable {G X : Type} [Group G] [MulAction G X]

def conjInv (x0 : X) (s : G) (h1 : ∀ h ∈ MulAction.stabilizer G x0, s⁻¹ * h * s ∈ MulAction.stabilizer G x0)
    (h2 : ∀ h ∈ MulAction.stabilizer G x0, s * h * s⁻¹ ∈ MulAction.stabilizer G x0) :
    MulAction.stabilizer G x0 ≃* MulAction.stabilizer G x0 where
  toFun h := ⟨s⁻¹ * h * s, h1 h h.2⟩
  invFun h := ⟨s * h * s⁻¹, h2 h h.2⟩
  left_inv h := by
    apply Subtype.ext
    simp [mul_assoc]
  right_inv h := by
    apply Subtype.ext
    simp [mul_assoc]
  map_mul' a b := by
    apply Subtype.ext
    simp [mul_assoc]

variable [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [MeasurableSpace X]

theorem conj_map_eq (x0 : X) (hcl : IsClosed (MulAction.stabilizer G x0 : Set G))
    (μG : Measure G) [μG.IsHaarMeasure] [μG.IsMulRightInvariant] (ρ : Measure X)
    (μ1 : Measure (MulAction.stabilizer G x0)) [μ1.IsHaarMeasure]
    (hw : ∀ f : G → ℝ≥0∞, Measurable f → ∀ sec : X → G,
      (∀ y, (∃ g : G, g • x0 = y) → sec y • x0 = y) →
      ∫⁻ g, f g ∂μG = ∫⁻ y, ∫⁻ h', f (sec y * (h' : G)) ∂μ1 ∂ρ)
    (R : X ≃ᵐ X) (hR : ∀ (g : G) (x : X), R (g • x) = g • R x) (hρ : ρ.map R = ρ)
    (s : G) (hs : s • x0 = R x0)
    (h1 : ∀ h ∈ MulAction.stabilizer G x0, s⁻¹ * h * s ∈ MulAction.stabilizer G x0)
    (h2 : ∀ h ∈ MulAction.stabilizer G x0, s * h * s⁻¹ ∈ MulAction.stabilizer G x0) :
    μ1.map (conjInv x0 s h1 h2) = μ1 := by
  haveI : LocallyCompactSpace (MulAction.stabilizer G x0) :=
    hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology (MulAction.stabilizer G x0) :=
    TopologicalSpace.Subtype.secondCountableTopology _
  set e := conjInv x0 s h1 h2 with he
  have hec : Continuous e := by
    refine Continuous.subtype_mk ?_ _
    exact (continuous_const.mul continuous_subtype_val).mul continuous_const
  have hes : Continuous e.symm := by
    refine Continuous.subtype_mk ?_ _
    exact (continuous_const.mul continuous_subtype_val).mul continuous_const
  haveI : (μ1.map e).IsHaarMeasure := e.isHaarMeasure_map μ1 hec hes
  have hc : μ1.map e = Measure.haarScalarFactor (μ1.map e) μ1 • μ1 :=
    Measure.isMulLeftInvariant_eq_smul _ _
  set c : NNReal := Measure.haarScalarFactor (μ1.map e) μ1 with hcdef

  classical
  let sec : X → G := fun y => if h : ∃ g : G, g • x0 = y then h.choose else 1
  have hsec : ∀ y, (∃ g : G, g • x0 = y) → sec y • x0 = y := by
    intro y h
    simp only [sec, dif_pos h]
    exact h.choose_spec
  have horb : ∀ y, (∃ g : G, g • x0 = y) → ∃ g : G, g • x0 = R.symm y := by
    rintro y ⟨g, rfl⟩
    refine ⟨g * s⁻¹, ?_⟩
    apply R.injective
    rw [MeasurableEquiv.apply_symm_apply, hR, mul_smul, ← hs, inv_smul_smul]
  let sec' : X → G := fun y => sec (R.symm y) * s
  have hsec' : ∀ y, (∃ g : G, g • x0 = y) → sec' y • x0 = y := by
    intro y hy
    simp only [sec', mul_smul]
    rw [hs, ← hR, hsec _ (horb y hy), MeasurableEquiv.apply_symm_apply]
  have key : ∀ f : G → ℝ≥0∞, Measurable f → ∫⁻ g, f g ∂μG = c * ∫⁻ g, f g ∂μG := by
    intro f hf
    have hfs : Measurable (fun g => f (g * s)) := hf.comp (measurable_mul_const s)
    have hA : ∫⁻ g, f (g * s) ∂μG = ∫⁻ g, f g ∂μG := lintegral_mul_right_eq_self f s
    have hB := hw _ hfs sec hsec
    have hC := hw f hf sec' hsec'
    have hinner : ∀ y, ∫⁻ h' : MulAction.stabilizer G x0, f (sec y * (h' : G) * s) ∂μ1 =
        c * ∫⁻ h' : MulAction.stabilizer G x0, f (sec y * s * (h' : G)) ∂μ1 := by
      intro y
      have hm : Measurable (fun h' : MulAction.stabilizer G x0 => f (sec y * s * (h' : G))) :=
        hf.comp ((measurable_const_mul _).comp measurable_subtype_coe)
      have h3 : ∫⁻ h', f (sec y * s * (h' : G)) ∂(μ1.map e) =
          ∫⁻ h' : MulAction.stabilizer G x0, f (sec y * (h' : G) * s) ∂μ1 := by
        rw [lintegral_map hm hec.measurable]
        refine lintegral_congr fun h => ?_
        congr 1
        show sec y * s * (s⁻¹ * (h : G) * s) = _
        group
      rw [← h3, hc, lintegral_smul_measure]
      rfl
    have hD : ∫⁻ y, ∫⁻ h' : MulAction.stabilizer G x0, f (sec' y * (h' : G)) ∂μ1 ∂ρ =
        ∫⁻ y, ∫⁻ h' : MulAction.stabilizer G x0, f (sec y * s * (h' : G)) ∂μ1 ∂ρ := by
      conv_lhs => rw [← hρ]
      rw [lintegral_map_equiv]
      simp only [sec', MeasurableEquiv.symm_apply_apply]
    calc ∫⁻ g, f g ∂μG = ∫⁻ g, f (g * s) ∂μG := hA.symm
      _ = ∫⁻ y, ∫⁻ h' : MulAction.stabilizer G x0, f (sec y * (h' : G) * s) ∂μ1 ∂ρ := hB
      _ = ∫⁻ y, c * ∫⁻ h' : MulAction.stabilizer G x0, f (sec y * s * (h' : G)) ∂μ1 ∂ρ := by
          simp only [hinner]
      _ = c * ∫⁻ y, ∫⁻ h' : MulAction.stabilizer G x0, f (sec y * s * (h' : G)) ∂μ1 ∂ρ :=
          lintegral_const_mul' _ _ ENNReal.coe_ne_top
      _ = c * ∫⁻ g, f g ∂μG := by rw [hC, hD]
  obtain ⟨K, hK, hK1⟩ := exists_compact_mem_nhds (1 : G)
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have h4 := key (K.indicator 1) (measurable_one.indicator hKm)
  rw [lintegral_indicator_one hKm] at h4
  have hpos : μG K ≠ 0 := (Measure.measure_pos_of_mem_nhds μG hK1).ne'
  have hfin : μG K ≠ ∞ := hK.measure_lt_top.ne
  have hc1 : (c : ℝ≥0∞) = 1 := by
    have h5 : (1 : ℝ≥0∞) * μG K = c * μG K := by rw [one_mul]; exact h4
    exact ((ENNReal.mul_left_inj hpos hfin).1 h5).symm
  have hc2 : c = 1 := by exact_mod_cast hc1
  rw [hc, hc2, one_smul]

theorem conj_lintegral_eq (x0 : X) (hcl : IsClosed (MulAction.stabilizer G x0 : Set G))
    (μG : Measure G) [μG.IsHaarMeasure] [μG.IsMulRightInvariant] (ρ : Measure X)
    (μ1 : Measure (MulAction.stabilizer G x0)) (hμ1 : μ1.IsHaarMeasure)
    (hw : ∀ f : G → ℝ≥0∞, Measurable f → ∀ sec : X → G,
      (∀ y, (∃ g : G, g • x0 = y) → sec y • x0 = y) →
      ∫⁻ g, f g ∂μG = ∫⁻ y, ∫⁻ h', f (sec y * (h' : G)) ∂μ1 ∂ρ)
    (R : X ≃ᵐ X) (hR : ∀ (g : G) (x : X), R (g • x) = g • R x) (hρ : ρ.map R = ρ)
    (s : G) (hs : s • x0 = R x0)
    (μ0 : Measure (MulAction.stabilizer G x0)) (hμ0 : μ0.IsHaarMeasure)
    (f : G → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ h : MulAction.stabilizer G x0, f (s * (h : G) * s⁻¹) ∂μ0 =
      ∫⁻ h : MulAction.stabilizer G x0, f (h : G) ∂μ0 := by
  haveI := hμ1
  haveI := hμ0
  haveI : LocallyCompactSpace (MulAction.stabilizer G x0) :=
    hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology (MulAction.stabilizer G x0) :=
    TopologicalSpace.Subtype.secondCountableTopology _
  have h1 : ∀ h ∈ MulAction.stabilizer G x0, s⁻¹ * h * s ∈ MulAction.stabilizer G x0 := by
    intro h hh
    rw [MulAction.mem_stabilizer_iff] at hh ⊢
    rw [mul_smul, mul_smul, hs, ← hR, hh, ← hs, inv_smul_smul]
  have h2 : ∀ h ∈ MulAction.stabilizer G x0, s * h * s⁻¹ ∈ MulAction.stabilizer G x0 := by
    intro h hh
    rw [MulAction.mem_stabilizer_iff] at hh ⊢
    apply R.injective
    rw [hR, ← hs, mul_smul, mul_smul, inv_smul_smul, hh]
  have hmap := conj_map_eq x0 hcl μG ρ μ1 hw R hR hρ s hs h1 h2
  have hc : μ0 = Measure.haarScalarFactor μ0 μ1 • μ1 := Measure.isMulLeftInvariant_eq_smul _ _
  have hm : Measurable (fun h : MulAction.stabilizer G x0 => f (s * (h : G) * s⁻¹)) :=
    hf.comp (((measurable_const_mul s).comp measurable_subtype_coe).mul_const _)
  have hec : Continuous (conjInv x0 s h1 h2) := by
    refine Continuous.subtype_mk ?_ _
    exact (continuous_const.mul continuous_subtype_val).mul continuous_const
  have h3 : ∫⁻ h : MulAction.stabilizer G x0, f (s * (h : G) * s⁻¹) ∂μ1 =
      ∫⁻ h : MulAction.stabilizer G x0, f (h : G) ∂μ1 := by
    conv_lhs => rw [← hmap]
    rw [lintegral_map hm hec.measurable]
    refine lintegral_congr fun h => ?_
    congr 1
    show s * (s⁻¹ * (h : G) * s) * s⁻¹ = _
    group
  rw [hc, lintegral_smul_measure, lintegral_smul_measure, h3]

end Abstract

section Tuples

variable {A : Type} [CommRing A] {n a : ℕ}

def mv (u : Matrix (Fin a) (Fin a) A) (X : Fin a → Fin n → A) : Fin a → Fin n → A :=
  fun b => ∑ c, u c b • X c

theorem mv_mv (u w : Matrix (Fin a) (Fin a) A) (X : Fin a → Fin n → A) :
    mv w (mv u X) = mv (u * w) X := by
  funext b
  simp only [mv, Matrix.mul_apply, Finset.smul_sum, Finset.sum_smul, smul_smul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by rw [mul_comm]

theorem mv_one (X : Fin a → Fin n → A) : mv 1 X = X := by
  funext b
  simp [mv, Matrix.one_apply]

theorem continuous_mv [TopologicalSpace A] [IsTopologicalRing A] (u : Matrix (Fin a) (Fin a) A) :
    Continuous (mv (n := n) u) :=
  continuous_pi fun b => continuous_finsetSum _ fun c _ => (continuous_apply c).const_smul (u c b)

theorem det_unitriangular (u : Matrix (Fin a) (Fin a) A) (h1 : ∀ i, u i i = 1)
    (h2 : ∀ i j, j < i → u i j = 0) : u.det = 1 := by
  rw [Matrix.det_of_upperTriangular (fun i j hij => h2 i j hij)]
  simp [h1]

noncomputable def mvHomeo [TopologicalSpace A] [IsTopologicalRing A] (u : Matrix (Fin a) (Fin a) A)
    (hu : IsUnit u.det) : (Fin a → Fin n → A) ≃ₜ (Fin a → Fin n → A) where
  toFun := mv u
  invFun := mv u⁻¹
  left_inv X := by rw [mv_mv, Matrix.mul_nonsing_inv u hu, mv_one]
  right_inv X := by rw [mv_mv, Matrix.nonsing_inv_mul u hu, mv_one]
  continuous_toFun := continuous_mv u
  continuous_invFun := continuous_mv _

end Tuples

section Gram

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  (σ : E →ₐ[F] E) {n a : ℕ} (J : Matrix (Fin n) (Fin n) E)

theorem smul_mv [TopologicalSpace R] (g : HA R σ J) (u : Matrix (Fin a) (Fin a) (R ⊗[F] E))
    (X : Fin a → Fin n → R ⊗[F] E) : g • mv u X = mv u (g • X) := by
  funext b
  show lin R σ J g (∑ c, u c b • X c) = ∑ c, u c b • lin R σ J g (X c)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  simp only [map_smul]

theorem hR_sum_left {ι : Type} (t : Finset ι) (x : ι → Fin n → R ⊗[F] E) (y : Fin n → R ⊗[F] E) :
    hR R σ J (∑ i ∈ t, x i) y = ∑ i ∈ t, hR R σ J (x i) y := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [hR_zero_left]
  | insert i t hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, hR_add_left, ih]

theorem hR_sum_right {ι : Type} (t : Finset ι) (x : Fin n → R ⊗[F] E) (y : ι → Fin n → R ⊗[F] E) :
    hR R σ J x (∑ i ∈ t, y i) = ∑ i ∈ t, hR R σ J x (y i) :=
  map_sum (GlobalTheory.UnitriangularCoeff.hRight R σ J x) y t

theorem gramR_mv (u : Matrix (Fin a) (Fin a) (R ⊗[F] E)) (X : Fin a → Fin n → R ⊗[F] E) :
    gramR R σ J (mv u X) = (u.map (sigR R σ)).transpose * gramR R σ J X * u := by
  ext i j
  simp only [gramR, mv, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
  rw [hR_sum_left]
  simp only [hR_smul_left, hR_sum_right, GlobalTheory.UnitriangularCoeff.hR_smul_right, Finset.sum_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by ring

theorem gramR_ratTup (X : Fin a → Fin n → E) :
    gramR R σ J (ratTup (F := F) R X) = (gramE σ J X).map (inclR R) := by
  ext i j
  simp [gramR, gramE, hE, hR, Formalism.UG.hform, ratTup, JR, sigR, inclR, Matrix.map_apply, mul_assoc]

theorem gramR_smul [TopologicalSpace R] (g : HA R σ J) (X : Fin a → Fin n → R ⊗[F] E) :
    gramR R σ J (g • X) = gramR R σ J X := by
  ext i j
  exact hR_lin g (X i) (X j)

end Gram

theorem conj_preserves_haar : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F)), ∀ (r : ℕ) (P : Frame E n r) (T : F), P.IsStd σ J T → ∀ (hT : ∀ i j, σ (gramE σ J (F0 P) j i) = gramE σ J (F0 P) i j), ∀ (μ : Measure (Fin (r + 1) → Fin n → Fv F v ⊗[F] E)) (ν : Measure (HermR (Fv F v) σ (r + 1))), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → ∀ fib : HermR (Fv F v) σ (r + 1) → Measure (Fin (r + 1) → Fin n → Fv F v ⊗[F] E), IsFibreFamily μ (gramR (Fv F v) σ J) Subtype.val {X | LinearIndependent (Fv F v ⊗[F] E) X} ν Set.univ fib → ∀ μ0 : Measure (S0 (Fv F v) σ J P), μ0.IsHaarMeasure → ∀ s ∈ Ssub (Fv F v) σ J P, ∀ f : HA (Fv F v) σ J → ℝ≥0∞, Measurable f → ∫⁻ h, f (s * (h : HA (Fv F v) σ J) * s⁻¹) ∂μ0 = ∫⁻ h, f (h : HA (Fv F v) σ J) ∂μ0 := by
  intro F E _ _ _ _ _ σ hCM n J hJ v r P T hP hT μ ν hμ hν fib hfib μ0 hμ0 s hs f hf
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := GlobalTheory.LocalUnitaryTop.top_facts F E σ hCM n J hJ v
  haveI := h1
  haveI := h2
  haveI := h3
  haveI := h4
  haveI := h5
  haveI := h6
  haveI := h7
  haveI := h8
  haveI : BorelSpace (Fv F v ⊗[F] E) := ⟨rfl⟩
  haveI : BorelSpace (HA (Fv F v) σ J) := ⟨rfl⟩
  obtain ⟨⟨-, -, -, -, -, ⟨μG, hμG⟩, hright⟩, -⟩ :=
    GlobalTheory.LocalUnitaryUnimod.unimodularOver_adicCompletion F E σ hCM n J hJ v
  haveI := hμG
  haveI := hright μG hμG
  obtain ⟨μ1, hμ1, -, hw⟩ := GlobalTheory.T.exists_haar_frameStabiliser_compatible_fibre F E σ hCM n J hJ v r P T hP hT μ ν hμ hν fib hfib μG hμG
  set x0 := ratTup (F := F) (Fv F v) (F0 P) with hx0def
  set S := hermOf (Fv F v) σ (gramE σ J (F0 P)) hT with hS
  have hgram : gramR (Fv F v) σ J x0 = (S : Matrix (Fin (r + 1)) (Fin (r + 1)) (Fv F v ⊗[F] E)) :=
    gramR_ratTup (Fv F v) σ J (F0 P)
  obtain ⟨co, -, hco⟩ := GlobalTheory.UnitriangularCoeff.exists_coeff F E σ hCM n J hJ v r P T hP
  let u : Matrix (Fin (r + 1)) (Fin (r + 1)) (Fv F v ⊗[F] E) := fun a b =>
    if a = b then 1 else if h : a < b then co ⟨s, hs⟩ ⟨(a, b), h⟩ else 0
  have hu1 : ∀ i, u i i = 1 := fun i => by simp [u]
  have hu2 : ∀ i j, j < i → u i j = 0 := by
    intro i j hij
    simp [u, hij.ne', not_lt.2 hij.le]
  have hsu : s • x0 = mv u x0 := by
    funext b
    exact (hco ⟨s, hs⟩ (co ⟨s, hs⟩)).1 rfl b
  have hg : (u.map (sigR (Fv F v) σ)).transpose *
      (S : Matrix (Fin (r + 1)) (Fin (r + 1)) (Fv F v ⊗[F] E)) * u =
      (S : Matrix (Fin (r + 1)) (Fin (r + 1)) (Fv F v ⊗[F] E)) := by
    rw [← hgram, ← gramR_mv, ← hsu, gramR_smul]
  have hfu := GlobalTheory.T.gramMap_fibreMeasure_unitriangular_invariant F E σ hCM n J hJ v (r + 1) μ ν hμ hν fib hfib S u hu1 hu2 hg
  have hdet : IsUnit u.det := by
    rw [det_unitriangular u hu1 hu2]
    exact isUnit_one
  let Rm := (mvHomeo (n := n) u hdet).toMeasurableEquiv
  have hcl : IsClosed (MulAction.stabilizer (HA (Fv F v) σ J) x0 : Set (HA (Fv F v) σ J)) := by
    have hc : Continuous (fun g : HA (Fv F v) σ J => g • x0) :=
      (h9 (r + 1)).2.comp (Continuous.prodMk continuous_id continuous_const)
    exact isClosed_singleton.preimage hc
  exact conj_lintegral_eq x0 hcl μG (fib S) μ1 hμ1 hw Rm (fun g x => (smul_mv (Fv F v) σ J g u x).symm)
    hfu s hsu μ0 hμ0 f hf

end GlobalTheory.ConjStabiliserHaar
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SimilitudeConjPreservesUnitaryHaarAtFinitePlaceStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.similitude_conj_preserves_unitary_haar_at_finite_place : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F)), ∀ (r : ℕ) (P : Frame E n r) (T : F), P.IsStd σ J T → ∀ (hT : ∀ i j, σ (gramE σ J (F0 P) j i) = gramE σ J (F0 P) i j), ∀ (μ : Measure (Fin (r + 1) → Fin n → Fv F v ⊗[F] E)) (ν : Measure (HermR (Fv F v) σ (r + 1))), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → ∀ fib : HermR (Fv F v) σ (r + 1) → Measure (Fin (r + 1) → Fin n → Fv F v ⊗[F] E), IsFibreFamily μ (gramR (Fv F v) σ J) Subtype.val {X | LinearIndependent (Fv F v ⊗[F] E) X} ν Set.univ fib → ∀ μ0 : Measure (S0 (Fv F v) σ J P), μ0.IsHaarMeasure → ∀ s ∈ Ssub (Fv F v) σ J P, ∀ f : HA (Fv F v) σ J → ℝ≥0∞, Measurable f → ∫⁻ h, f (s * (h : HA (Fv F v) σ J) * s⁻¹) ∂μ0 = ∫⁻ h, f (h : HA (Fv F v) σ J) ∂μ0 := by
  first | exact @GlobalTheory.ConjStabiliserHaar.conj_preserves_haar | exact GlobalTheory.ConjStabiliserHaar.conj_preserves_haar | (intros; apply GlobalTheory.ConjStabiliserHaar.conj_preserves_haar <;> assumption)
end
