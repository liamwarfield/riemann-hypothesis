module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.FinAm
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.ArPresAlt

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.LcOfOpen
open Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem lc_of_open {R Γ M : Type} [CommRing R] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [AddCommGroup M] [Module R M] (ρ : Representation R Γ M) (H : Subgroup Γ) (hH : IsOpen (H : Set Γ))
    (h : ∀ m, IsLocallyConstant fun g : H => ρ g m) : LC ρ := by
  intro m
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hU : IsOpen ((Subtype.val : H → Γ) '' {z : H | ρ z m = m}) :=
    hH.isOpenMap_subtype_val _ ((h m).isOpen_fiber m)
  have h1 : (1 : Γ) ∈ (Subtype.val : H → Γ) '' {z : H | ρ z m = m} := ⟨1, by simp, rfl⟩
  have ht : Filter.Tendsto (fun y => x⁻¹ * y) (nhds x) (nhds 1) := by
    have h0 := (continuous_const_mul x⁻¹).tendsto x
    simpa using h0
  filter_upwards [ht (hU.mem_nhds h1)] with y hy
  obtain ⟨z, hz, hzy⟩ := hy
  have hz' : ρ z m = m := hz
  have hy : y = x * z := by rw [hzy]; group
  rw [hy, map_mul]
  show ρ x (ρ z m) = ρ x m
  rw [hz']

private theorem lc_mat {Γ R : Type} [TopologicalSpace Γ] {n : ℕ} (f : Γ → Matrix (Fin n) (Fin n) R)
    (h : ∀ i j, IsLocallyConstant fun g => f g i j) : IsLocallyConstant f := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hev : ∀ᶠ y in nhds x, ∀ i j, f y i j = f x i j := by
    simp only [Filter.eventually_all]
    intro i j
    exact (h i j).eventually_eq x
  filter_upwards [hev] with y hy
  exact Matrix.ext hy

private theorem lc_padic {l : ℕ} [Fact l.Prime] {R : Type} [CommRing R] (f : ℤ_[l] →+* R) (hl : (l : R) = 0) :
    IsLocallyConstant f := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hev : ∀ᶠ y in nhds x, ‖y - x‖ < 1 := by
    filter_upwards [Metric.ball_mem_nhds x one_pos] with y hy
    simpa [dist_eq_norm] using hy
  filter_upwards [hev] with y hy
  obtain ⟨z, hz⟩ := (PadicInt.norm_lt_one_iff_dvd _).1 hy
  have hyz : y = x + (l : ℤ_[l]) * z := by rw [← hz]; ring
  rw [hyz, map_add (f := _), map_mul, map_natCast, hl, zero_mul, add_zero]

private theorem maximalIdeal_powerSeries_eq_span_X (K : Type) [Field K] :
    IsLocalRing.maximalIdeal (PowerSeries K) = Ideal.span {(PowerSeries.X : PowerSeries K)} := by
  ext φ
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, Ideal.mem_span_singleton, PowerSeries.X_dvd_iff,
    PowerSeries.isUnit_iff_constantCoeff, isUnit_iff_ne_zero, not_not]

private theorem isLocallyConstant_pi_of_forall_isLocallyConstant {Γ ι Y : Type} [TopologicalSpace Γ] [Finite ι] (f : Γ → ι → Y)
    (h : ∀ i, IsLocallyConstant fun g => f g i) : IsLocallyConstant f := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hev : ∀ᶠ y in nhds x, ∀ i, f y i = f x i :=
    Filter.eventually_all.2 fun i => (h i).eventually_eq x
  filter_upwards [hev] with y hy
  exact funext hy

private theorem isLocallyConstant_comp_of_adicCont_of_pow_eq_zero {Γ A B : Type} [TopologicalSpace Γ] [CommRing A] [CommRing B] (s : A) (N : ℕ)
    (φ : A →+* B) (hs : φ s ^ N = 0) (f : Γ → A) (hf : AdicCont (Ideal.span {s}) f) :
    IsLocallyConstant fun g => φ (f g) := by
  have hI : ∀ a ∈ Ideal.span {s} ^ N, φ a = 0 := by
    intro a ha
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at ha
    obtain ⟨c, rfl⟩ := ha
    rw [map_mul, map_pow, hs, mul_zero]
  have h2 := (hf N).comp (Ideal.Quotient.lift (Ideal.span {s} ^ N) φ hI)
  convert h2 using 1
  funext g
  exact (Ideal.Quotient.lift_mk (Ideal.span {s} ^ N) φ hI).symm

theorem UpperTheory.V.Pa.lc1 :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n) (k : Kap x) (m : ℕ), (IsLocallyConstant fun g : G.G₀ => k.ρ1 (x.Am m) (h.p₀ g)) ∧ (IsLocallyConstant fun g : G.Γ => epsD k (x.Am m) (h.p g)) ∧ ∀ (χ : G.Γ → DD (x.Am m) k.g) (V : Submodule x.A (Matrix (Fin n) (Fin n) (DD (x.Am m) k.g))) (rep : Representation x.A G.Γ V), IsLocallyConstant χ → IsAd G.frame (fun g => k.ρ1 (x.Am m) (h.p₀ g)) χ V rep → LC rep := by
  intro l _ L G G0 h n x k m
  obtain ⟨-, -, -, -, hlD, htA, htD, -, -⟩ := finAm l G0.frame n x m k.g
  have hM : IsLocalRing.maximalIdeal (PowerSeries x.K) = Ideal.span {x.t} := maximalIdeal_powerSeries_eq_span_X x.K
  have hp0 : Continuous h.p₀ := continuous_induced_rng.2 (h.cont.comp continuous_subtype_val)
  have hE : IsLocallyConstant fun g : G0.G₀ =>
      DD.epM (fun j => (k.κ j g).map (algebraMap x.A (x.Am m))) := by
    apply lc_mat
    intro a b
    have hv : IsLocallyConstant fun g : G0.G₀ => fun j => algebraMap x.A (x.Am m) (k.κ j g a b) := by
      apply isLocallyConstant_pi_of_forall_isLocallyConstant
      intro j
      exact isLocallyConstant_comp_of_adicCont_of_pow_eq_zero (algebraMap x.A x.A x.t) m (algebraMap x.A (x.Am m)) (by simpa using htA) _
        ((k.mem j).2.1 a b)
    exact hv.comp (fun v => ({ a := 0, ep := v, ep' := 0, eta := 0 } : DD (x.Am m) k.g))
  have hR : IsLocallyConstant fun g : G0.G₀ => x.ρX (DD (x.Am m) k.g) g := by
    apply lc_mat
    intro a b
    simp only [NP.ρX, Matrix.map_apply]
    exact isLocallyConstant_comp_of_adicCont_of_pow_eq_zero x.t m (algebraMap x.A (DD (x.Am m) k.g)) htD _ (by rw [← hM]; exact x.cont a b)
  have hρ : IsLocallyConstant fun g : G0.G₀ => k.ρ1 (x.Am m) g :=
    (hE.comp (fun M => 1 + M)).comp₂ hR (· * ·)
  have hρ' : IsLocallyConstant fun g : G.G₀ => k.ρ1 (x.Am m) (h.p₀ g) := hρ.comp_continuous hp0
  refine ⟨hρ', ?_, ?_⟩
  · have hl' : ((l : ℕ) : DD (x.Am m) k.g) = 0 := by simpa using hlD 1
    exact (lc_padic ((algebraMap x.A (DD (x.Am m) k.g)).comp (algebraMap ℤ_[l] x.A)) hl').comp_continuous
      (Units.continuous_val.comp (G0.ε_cont.comp h.cont))
  · intro χ V rep hχ hAd
    apply lc_of_open rep G.η.ker G.η_open
    intro Z
    have hinv : IsLocallyConstant fun g : G.G₀ => k.ρ1 (x.Am m) (h.p₀ g⁻¹) :=
      hρ'.comp_continuous continuous_inv
    have hχ' : IsLocallyConstant fun g : G.G₀ => χ g := hχ.comp_continuous continuous_subtype_val
    have key : IsLocallyConstant fun g : G.G₀ => ((rep g Z : V) : Matrix (Fin n) (Fin n) (DD (x.Am m) k.g)) := by
      have e : (fun g : G.G₀ => ((rep g Z : V) : Matrix (Fin n) (Fin n) (DD (x.Am m) k.g))) =
          fun g : G.G₀ => χ g • (k.ρ1 (x.Am m) (h.p₀ g) * (Z : Matrix (Fin n) (Fin n) (DD (x.Am m) k.g)) *
            k.ρ1 (x.Am m) (h.p₀ g⁻¹)) := by
        funext g
        exact hAd.1 g Z
      rw [e]
      exact hχ'.comp₂ (hρ'.comp₂ hinv fun A B => A * (Z : Matrix (Fin n) (Fin n) (DD (x.Am m) k.g)) * B)
        fun c M => c • M
    exact (IsLocallyConstant.iff_eventually_eq _).2 fun g =>
      (key.eventually_eq g).mono fun y hy => Subtype.ext hy
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.GaloisLiftMemFirstOrderDeformations
open Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

section Gen

variable {A R : Type} [CommRing A] [CommRing R] [Algebra A R] {n a : ℕ}

private theorem mem_blkMat_iff_mem_of_same_block_and_mem_off {V₁ V₂ : Submodule A R} {Z : Matrix (Fin n) (Fin n) R} :
    Z ∈ blkMat n a V₁ V₂ ↔ ∀ i j : Fin n, (((i : ℕ) < a ↔ (j : ℕ) < a) → Z i j ∈ V₁) ∧
      (¬((i : ℕ) < a ↔ (j : ℕ) < a) → Z i j ∈ V₂) :=
  Iff.rfl

private theorem blk_tr {V₁ V₂ : Submodule A R} {Z : Matrix (Fin n) (Fin n) R} (hZ : Z ∈ blkMat n a V₁ V₂) :
    Zᵀ ∈ blkMat n a V₁ V₂ := by
  rw [mem_blkMat_iff_mem_of_same_block_and_mem_off] at hZ ⊢
  intro i j
  obtain ⟨h1, h2⟩ := hZ j i
  exact ⟨fun h => h1 h.symm, fun h => h2 (fun h' => h h'.symm)⟩

private def Act (U₁ U₂ V₁ V₂ : Submodule A R) : Prop :=
  (∀ u ∈ U₁, ∀ v ∈ V₁, u * v ∈ V₁) ∧ (∀ u ∈ U₁, ∀ v ∈ V₂, u * v ∈ V₂) ∧
    (∀ u ∈ U₂, ∀ v ∈ V₁, u * v ∈ V₂) ∧ (∀ u ∈ U₂, ∀ v ∈ V₂, u * v ∈ V₁)

private theorem blk_mul {U₁ U₂ V₁ V₂ : Submodule A R} (H : Act U₁ U₂ V₁ V₂) {P Z : Matrix (Fin n) (Fin n) R}
    (hP : P ∈ blkMat n a U₁ U₂) (hZ : Z ∈ blkMat n a V₁ V₂) : P * Z ∈ blkMat n a V₁ V₂ := by
  rw [mem_blkMat_iff_mem_of_same_block_and_mem_off] at hP hZ ⊢
  obtain ⟨h11, h12, h21, h22⟩ := H
  intro i j
  constructor
  · intro hij
    rw [Matrix.mul_apply]
    refine Submodule.sum_mem _ (fun k _ => ?_)
    by_cases hik : ((i : ℕ) < a ↔ (k : ℕ) < a)
    · exact h11 _ ((hP i k).1 hik) _ ((hZ k j).1 (hik.symm.trans hij))
    · have hkj : ¬((k : ℕ) < a ↔ (j : ℕ) < a) := fun h => hik (hij.trans h.symm)
      exact h22 _ ((hP i k).2 hik) _ ((hZ k j).2 hkj)
  · intro hij
    rw [Matrix.mul_apply]
    refine Submodule.sum_mem _ (fun k _ => ?_)
    by_cases hik : ((i : ℕ) < a ↔ (k : ℕ) < a)
    · have hkj : ¬((k : ℕ) < a ↔ (j : ℕ) < a) := fun h => hij (hik.trans h)
      exact h12 _ ((hP i k).1 hik) _ ((hZ k j).2 hkj)
    · have hkj : ((k : ℕ) < a ↔ (j : ℕ) < a) := by tauto
      exact h21 _ ((hP i k).2 hik) _ ((hZ k j).1 hkj)

private theorem blk_sand {U₁ U₂ V₁ V₂ : Submodule A R} (H : Act U₁ U₂ V₁ V₂) {P Q Z : Matrix (Fin n) (Fin n) R}
    (hP : P ∈ blkMat n a U₁ U₂) (hQ : Q ∈ blkMat n a U₁ U₂) (hZ : Z ∈ blkMat n a V₁ V₂) :
    P * Z * Q ∈ blkMat n a V₁ V₂ := by
  have h1 := blk_mul H hP hZ
  have h2 := blk_tr (blk_mul H (blk_tr hQ) (blk_tr h1))
  simpa [Matrix.transpose_mul] using h2

private theorem alg_smul_mem {V : Submodule A (Matrix (Fin n) (Fin n) R)} (c : A) {Z : Matrix (Fin n) (Fin n) R}
    (hZ : Z ∈ V) : algebraMap A R c • Z ∈ V := by
  rw [algebraMap_smul]
  exact V.smul_mem c hZ

end Gen

section Parts

variable {A X : Type} [CommRing A] [CommRing X] [Algebra A X] {g : ℕ}

private theorem ep_algebraMap_eq_zero (c : A) (j : Fin g) : (algebraMap A (DD X g) c).ep j = 0 := rfl

private theorem ep'_algebraMap_eq_zero (c : A) (j : Fin g) : (algebraMap A (DD X g) c).ep' j = 0 := rfl

private theorem eta_algebraMap_eq_zero (c : A) : (algebraMap A (DD X g) c).eta = 0 := rfl

private theorem mem_part {p q r s : Bool} {y : DD X g} : y ∈ ddPart A X g p q r s ↔
    (p = false → y.a = 0) ∧ (q = false → ∀ j, y.ep j = 0) ∧ (r = false → ∀ j, y.ep' j = 0) ∧ (s = false → y.eta = 0) := by
  show ((p = false → y.a = 0) ∧ (q = false → y.ep = 0) ∧ (r = false → y.ep' = 0) ∧ (s = false → y.eta = 0)) ↔ _
  simp only [funext_iff, Pi.zero_apply]

private theorem act1 : Act (ddPart A X g true false false false) (ddPart A X g false true false false)
    (ddPart A X g true false false false) (ddPart A X g false true false false) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro u hu v hv <;> rw [mem_part] at hu hv ⊢ <;> simp_all

private theorem act1s : Act (ddPart A X g true false false false) (ddPart A X g false true false false)
    (ddPart A X g false false false true) (ddPart A X g false false true false) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro u hu v hv <;> rw [mem_part] at hu hv ⊢ <;> simp_all

private theorem act2 : Act (ddPart A X g true false false false) (ddPart A X g false true false false)
    (ddPart A X g false false true false) (ddPart A X g false false false true) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro u hu v hv <;> rw [mem_part] at hu hv ⊢ <;> simp_all

end Parts

private theorem galois_lift_mem_first_order_deformations {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} {x : NP F n} (k : Kap x) (X : Type)
    [CommRing X] [Algebra x.A X] (g : F.G₀) : k.ρ1 X g ∈ W1 n x.A X k.g x.a := by
  have hP : (1 + DD.epM fun j => (k.κ j g).map (algebraMap x.A X)) ∈ W1 n x.A X k.g x.a := by
    show _ ∈ blkMat n x.a (ddPart x.A X k.g true false false false) (ddPart x.A X k.g false true false false)
    refine mem_blkMat_iff_mem_of_same_block_and_mem_off.2 (fun i j => ⟨fun h => ?_, fun h => ?_⟩)
    · have hκ : ∀ m, k.κ m g i j = 0 := fun m => by
        have hm := ((mem_blkMat_iff_mem_of_same_block_and_mem_off.1 ((k.mem m).1 g)) i j).1 h
        simpa using hm
      rw [mem_part]
      by_cases hij : i = j
      · subst hij
        simp [Matrix.one_apply, DD.epM, hκ]
      · simp [hij, Matrix.one_apply, DD.epM, hκ]
    · have hne : i ≠ j := by
        rintro rfl
        exact h Iff.rfl
      rw [mem_part]
      simp [hne, Matrix.one_apply, DD.epM]
  have hZ : x.ρX (DD X k.g) g ∈ W1 n x.A X k.g x.a := by
    show _ ∈ blkMat n x.a (ddPart x.A X k.g true false false false) (ddPart x.A X k.g false true false false)
    refine mem_blkMat_iff_mem_of_same_block_and_mem_off.2 (fun i j => ⟨fun h => ?_, fun h => ?_⟩)
    · rw [mem_part]
      simp [NP.ρX, ep_algebraMap_eq_zero, ep'_algebraMap_eq_zero, eta_algebraMap_eq_zero]
    · have h0 : (mat x.ρ) g i j = 0 := by
        simpa using ((mem_blkMat_iff_mem_of_same_block_and_mem_off.1 (x.blk g)) i j).2 h
      rw [mem_part]
      simp [NP.ρX, h0]
  exact blk_mul act1 hP hZ

theorem UpperTheory.V.Pa.ok1 :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n) (k : Kap x) (X : Type) [CommRing X] [Algebra x.A X] (χ : G.Γ →* x.A), AdOk G.frame (fun g => k.ρ1 X (h.p₀ g)) (fun g => algebraMap x.A (DD X k.g) (χ g)) (W1 n x.A X k.g x.a) ∧ AdOk G.frame (fun g => k.ρ1 X (h.p₀ g)) (fun g => algebraMap x.A (DD X k.g) (χ g)) (pairedDualFirstOrderDualMatrixSpace n x.A X k.g x.a) ∧ AdOk G.frame (fun g => k.ρ1 X (h.p₀ g)) (fun g => algebraMap x.A (DD X k.g) (χ g)) (W2 n x.A X k.g x.a) := by
  intro l _ L G G0 h n x k X _ _ χ
  obtain ⟨r1, r2, r3, -, -⟩ := rho1 l G0.frame n x k X
  have hconj : ∀ g : G.frame.G₀, h.p₀ (G.frame.conj g) = G0.frame.conj (h.p₀ g) := by
    intro g
    apply Subtype.ext
    simp [Glob.Hom.p₀, GFrame.conj, h.c]
  have key : ∀ V₁ V₂ : Submodule x.A (DD X k.g),
      Act (ddPart x.A X k.g true false false false) (ddPart x.A X k.g false true false false) V₁ V₂ →
      AdOk G.frame (fun g => k.ρ1 X (h.p₀ g)) (fun g => algebraMap x.A (DD X k.g) (χ g)) (blkMat n x.a V₁ V₂) := by
    intro V₁ V₂ H
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show k.ρ1 X (h.p₀ 1) = 1
      rw [map_one]
      exact r1
    · intro a b
      show k.ρ1 X (h.p₀ (a * b)) = k.ρ1 X (h.p₀ a) * k.ρ1 X (h.p₀ b)
      rw [map_mul]
      exact r2 _ _
    · intro g
      refine ⟨Units.map (algebraMap x.A (DD X k.g) : x.A →* DD X k.g)
        ((G0.frame.eps ℤ_[l] x.A) (h.p₀ g) ^ (1 - (n : ℤ))), ?_⟩
      show (k.ρ1 X (h.p₀ g))ᵀ * k.ρ1 X (h.p₀ (G.frame.conj g)) = _
      rw [hconj, r3]
      rfl
    · show algebraMap x.A (DD X k.g) (χ 1) = 1
      simp
    · intro a b
      show algebraMap x.A (DD X k.g) (χ (a * b)) = algebraMap x.A (DD X k.g) (χ a) * algebraMap x.A (DD X k.g) (χ b)
      simp
    · intro g Z hZ
      show algebraMap x.A (DD X k.g) (χ g) • (k.ρ1 X (h.p₀ g) * Z * k.ρ1 X (h.p₀ g⁻¹)) ∈ _
      exact alg_smul_mem _ (blk_sand H (galois_lift_mem_first_order_deformations k X _) (galois_lift_mem_first_order_deformations k X _) hZ)
    · intro Z hZ
      show algebraMap x.A (DD X k.g) (χ G.frame.c) • Zᵀ ∈ _
      exact alg_smul_mem _ (blk_tr hZ)
  exact ⟨key _ _ act1, key _ _ act1s, key _ _ act2⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.AuxiliaryVectorCutByHermitianLinearForm
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.FrobFormTrunc
open Polynomial Matrix IsLocalRing TensorProduct

theorem UpperTheory.V.AlgebraTools.frob_form_trunc :
    ∀ {k : Type} [Field k] [Finite k] (l : ℕ) [Fact l.Prime] [Algebra (ZMod l) k] (m : ℕ), ∃ lam : (PowerSeries k ⧸ Ideal.span {(PowerSeries.X : PowerSeries k) ^ (m + 1)}) →+ ZMod l, (∀ f, lam (Ideal.Quotient.mk _ f) = Algebra.trace (ZMod l) k (PowerSeries.coeff m f)) ∧ (∀ x, (∀ y, lam (x * y) = 0) → x = 0) ∧ Finite (PowerSeries k ⧸ Ideal.span {(PowerSeries.X : PowerSeries k) ^ (m + 1)}) := by
  intro k _ _ l _ _ m
  classical
  let I : Ideal (PowerSeries k) := Ideal.span {(PowerSeries.X : PowerSeries k) ^ (m + 1)}
  have hmem : ∀ f : PowerSeries k, f ∈ I ↔ ∀ j, j < m + 1 → PowerSeries.coeff j f = 0 := by
    intro f
    rw [Ideal.mem_span_singleton, PowerSeries.X_pow_dvd_iff]
  have hW : ∀ f g : PowerSeries k, Ideal.Quotient.mk I f = Ideal.Quotient.mk I g →
      ∀ j, j < m + 1 → PowerSeries.coeff j f = PowerSeries.coeff j g := by
    intro f g h j hj
    rw [Ideal.Quotient.eq, hmem] at h
    have := h j hj
    rw [map_sub, sub_eq_zero] at this
    exact this
  let s := Function.surjInv (Ideal.Quotient.mk_surjective (I := I))
  have hs : ∀ x, Ideal.Quotient.mk I (s x) = x := Function.surjInv_eq _
  let L : (PowerSeries k ⧸ I) → ZMod l := fun x => Algebra.trace (ZMod l) k (PowerSeries.coeff m (s x))
  have hL : ∀ f, L (Ideal.Quotient.mk I f) = Algebra.trace (ZMod l) k (PowerSeries.coeff m f) := by
    intro f
    simp only [L]
    rw [hW _ _ (hs _) m (Nat.lt_succ_self m)]
  let lam : (PowerSeries k ⧸ I) →+ ZMod l :=
    { toFun := L
      map_zero' := by
        have := hL 0
        rw [map_zero, map_zero, map_zero] at this
        exact this
      map_add' := by
        intro x y
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
        obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
        rw [← map_add (f := _), hL, hL, hL, map_add (f := _), map_add (f := _)] }
  refine ⟨lam, hL, ?_, ?_⟩
  · intro x hx
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
    by_contra hne
    have hnot : f ∉ I := fun h => hne (Ideal.Quotient.eq_zero_iff_mem.2 h)
    rw [hmem] at hnot
    push_neg at hnot
    obtain ⟨j, hj, hfj⟩ := hnot
    have hnd := (traceForm_nondegenerate (ZMod l) k).1 (PowerSeries.coeff j f)
    have hex : ∃ b : k, Algebra.trace (ZMod l) k (PowerSeries.coeff j f * b) ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact hfj (hnd fun b => by rw [Algebra.traceForm_apply]; exact hc b)
    obtain ⟨b, hb⟩ := hex
    apply hb
    have := hx (Ideal.Quotient.mk I (PowerSeries.C b * PowerSeries.X ^ (m - j)))
    rw [← map_mul] at this
    change L _ = 0 at this
    rw [hL] at this
    have hjm : j ≤ m := Nat.lt_succ_iff.mp hj
    have hc : PowerSeries.coeff m (f * (PowerSeries.C b * PowerSeries.X ^ (m - j))) =
        PowerSeries.coeff j f * b := by
      rw [show f * (PowerSeries.C b * PowerSeries.X ^ (m - j)) =
          PowerSeries.C b * (PowerSeries.X ^ (m - j) * f) by ring]
      rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul', if_pos (Nat.sub_le m j),
        Nat.sub_sub_self hjm, mul_comm]
    rw [hc] at this
    exact this
  · let e : (PowerSeries k ⧸ I) → (Fin (m + 1) → k) := fun x j => PowerSeries.coeff j (s x)
    apply Finite.of_injective e
    intro x y hxy
    rw [← hs x, ← hs y, Ideal.Quotient.eq, hmem]
    intro j hj
    have := congrFun hxy ⟨j, hj⟩
    rw [map_sub, sub_eq_zero]
    exact this
end

open Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem linearMap_comp_eq_on_smul_of_eq (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (φ : ℤ_[l] →+* R)
    (h : ∀ y : R, l • y = 0) (τ : R →+ ZMod l) (a : ℤ_[l]) (y : R) :
    τ (φ a * y) = PadicInt.toZMod a * τ y := by
  have hspec := PadicInt.toZMod_spec a
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton'] at hspec
  obtain ⟨c, hc⟩ := hspec
  have ha : a = c * (l : ℤ_[l]) + ((PadicInt.toZMod a).val : ℤ_[l]) := by
    rw [hc, ZMod.cast_eq_val]
    ring
  have key : φ a * y = ((PadicInt.toZMod a).val : R) * y := by
    have e : φ a = φ c * (l : R) + ((PadicInt.toZMod a).val : R) := by
      rw [← map_natCast φ l, ← map_natCast φ, ← map_mul, ← map_add (f := _), ← ha]
    rw [e, add_mul, mul_assoc, ← nsmul_eq_mul l y, h y, mul_zero, zero_add]
  rw [key, ← nsmul_eq_mul, map_nsmul, nsmul_eq_mul, ZMod.natCast_zmod_val]

private theorem hermOrthExt_gram_entry_eq_single_and_frame_gram_eq_zero (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [Finite k] [CharP k l] (m : ℕ) :
    ∃ τ : (PowerSeries k ⧸ Ideal.span {(PowerSeries.X : PowerSeries k) ^ m}) →+ ZMod l,
      ∀ y, (∀ z, τ (y * z) = 0) → y = 0 := by
  cases m with
  | zero =>
    refine ⟨0, fun y _ => ?_⟩
    have htop : Ideal.span {(PowerSeries.X : PowerSeries k) ^ 0} = ⊤ := by
      rw [pow_zero, Ideal.span_singleton_one]
    exact (Ideal.Quotient.subsingleton_iff.2 htop).elim _ _
  | succ k0 =>
    letI := ZMod.algebra k l
    obtain ⟨lam, -, hlam, -⟩ := UpperTheory.V.AlgebraTools.frob_form_trunc (k := k) l k0
    exact ⟨lam, hlam⟩

theorem UpperTheory.V.Pa.pair1 :
    ∀ (l : ℕ) [Fact l.Prime] (F : GFrame l) (n : ℕ) (x : NP F n) (m : ℕ), ∃ τ : x.Am m →+ ZMod l, (∀ y, (∀ z, τ (y * z) = 0) → y = 0) ∧ ∀ (a : ℤ_[l]) y, τ (algebraMap x.A (x.Am m) (algebraMap ℤ_[l] x.A a) * y) = PadicInt.toZMod a * τ y := by
  intro l _ F n x m
  obtain ⟨-, -, -, h4, -, -, -, -, hc⟩ := finAm l F n x m 0
  obtain ⟨τ, hτ⟩ := hermOrthExt_gram_entry_eq_single_and_frame_gram_eq_zero l x.K m
  exact ⟨τ, hτ, fun a y =>
    linearMap_comp_eq_on_smul_of_eq l (x.Am m) ((algebraMap x.A (x.Am m)).comp (algebraMap ℤ_[l] x.A)) h4 τ a y⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.ArPres
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.SumDegF
open Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

theorem UpperTheory.V.Pa.sumDegF :
    ∀ (l : ℕ) [Fact l.Prime] (F : Type) [Field F] [NumberField F], ∑ᶠ v : {v : HeightOneSpectrum (𝓞 F) // ((l : ℕ) : 𝓞 F) ∈ v.asIdeal}, locDeg v.1 = Module.finrank ℚ F := by
  intro l _ F _ _
  classical
  have hl : l.Prime := Fact.out
  let p : Ideal ℤ := Ideal.span {(l : ℤ)}
  haveI hpmax : p.IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hl).irreducible
  have hp0 : p ≠ ⊥ := by
    simp only [p, ne_eq, Ideal.span_singleton_eq_bot, Nat.cast_eq_zero]
    exact hl.ne_zero
  let e1 : {v : HeightOneSpectrum (𝓞 F) // ((l : ℕ) : 𝓞 F) ∈ v.asIdeal} ≃
      {v : HeightOneSpectrum (𝓞 F) // v.asIdeal ∣ Ideal.map (algebraMap ℤ (𝓞 F)) p} :=
    Equiv.subtypeEquivRight (fun v => by
      rw [Ideal.dvd_iff_le, Ideal.map_span, Set.image_singleton, Ideal.span_singleton_le_iff_mem,
        map_natCast])
  let e := e1.trans (HeightOneSpectrum.equivPrimesOver (𝓞 F) hp0)
  have h1 : ∑ᶠ v : {v : HeightOneSpectrum (𝓞 F) // ((l : ℕ) : 𝓞 F) ∈ v.asIdeal}, locDeg v.1
      = ∑ᶠ q : p.primesOver (𝓞 F), q.1.ramificationIdx ℤ * q.1.inertiaDeg ℤ := by
    rw [← finsum_comp_equiv e]
    rfl
  rw [h1, finsum_eq_sum_of_fintype, Ideal.sum_ramification_inertia_eq_finrank,
    NumberField.RingOfIntegers.rank]
end

open Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

section SlopeTestRemainingChoices

variable {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]

private theorem l_not_mem_base_prime (s : HidaSetting l L Ω) : ((l : ℕ) : 𝓞 (Lp L)) ∉ s.v0.asIdeal := by
  intro h
  have h1 : ((s.p : ℕ) : 𝓞 (Lp L)) ∈ s.v0.asIdeal := by
    rw [← s.norm_v0_eq_one]
    simpa only [normV, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply] using
      Ideal.absNorm_mem s.v0.asIdeal
  have hc : IsCoprime (s.p : 𝓞 (Lp L)) (l : 𝓞 (Lp L)) :=
    ((Nat.coprime_primes s.p_prime Fact.out).2 s.p_ne).cast
  obtain ⟨a, b, hab⟩ := hc
  exact s.v0.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
    (hab ▸ add_mem (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ h)))

private def plF (s : HidaSetting l L Ω) {q : ℕ} (v : Fin q → Plc (Lp L)) : Vl l L ⊕ s.St ⊕ Option (Fin q) → Plc (Lp L)
  | .inl u => u.1
  | .inr (.inl u) => u.1
  | .inr (.inr none) => s.v0
  | .inr (.inr (some j)) => v j

private theorem plF_l (s : HidaSetting l L Ω) {q : ℕ} (v : Fin q → Plc (Lp L)) (hn : ∀ j, v j ∉ s.S) (w) :
    ((l : ℕ) : 𝓞 (Lp L)) ∈ (plF s v w).asIdeal ↔ ∃ u, w = .inl u := by
  rcases w with u | u | _ | j
  · exact iff_of_true u.2 ⟨u, rfl⟩
  · exact iff_of_false (s.St_l u.1 u.2) (by simp)
  · exact iff_of_false (l_not_mem_base_prime s) (by simp)
  · exact iff_of_false (fun h => hn j (Or.inl h)) (by simp)

private theorem plF_inj (s : HidaSetting l L Ω) {q : ℕ} (v : Fin q → Plc (Lp L)) (hi : Function.Injective v)
    (hn : ∀ j, v j ∉ s.S) : Function.Injective (plF s v) := by
  have key : ∀ (u : Vl l L) w, plF s v (.inl u) = plF s v (.inr w) → False := fun u w h => by
    have := (plF_l s v hn (.inr w)).1 (h ▸ u.2)
    simp at this
  rintro (a | a) (b | b) h
  · exact congrArg _ (Subtype.ext h)
  · exact (key _ _ h).elim
  · exact (key _ _ h.symm).elim
  · rcases a with a | _ | a <;> rcases b with b | _ | b <;> simp only [plF] at h
    · rw [Subtype.ext h]
    · exact (s.v0_St (h ▸ a.2)).elim
    · exact (hn b (h ▸ Or.inr (Or.inl a.2))).elim
    · exact (s.v0_St (h ▸ b.2)).elim
    · rfl
    · exact (hn b (Or.inr (Or.inr h.symm))).elim
    · exact (hn a (h ▸ Or.inr (Or.inl b.2))).elim
    · exact (hn a (Or.inr (Or.inr h))).elim
    · rw [hi h]

private theorem plF_range (s : HidaSetting l L Ω) {q : ℕ} (v : Fin q → Plc (Lp L)) :
    Set.range (plF s v) = s.S ∪ Set.range v := by
  ext x
  constructor
  · rintro ⟨u | u | _ | j, rfl⟩
    · exact Or.inl (Or.inl u.2)
    · exact Or.inl (Or.inr (Or.inl u.2))
    · exact Or.inl (Or.inr (Or.inr rfl))
    · exact Or.inr ⟨j, rfl⟩
  · rintro ((h | h | h) | ⟨j, h⟩)
    · exact ⟨.inl ⟨x, h⟩, rfl⟩
    · exact ⟨.inr (.inl ⟨x, h⟩), rfl⟩
    · exact ⟨.inr (.inr none), h.symm⟩
    · exact ⟨.inr (.inr (some j)), h⟩

private def vaF (s : HidaSetting l L Ω) {q : ℕ} (B : Fin q → ValuationSubring Ω) :
    Vl l L ⊕ s.St ⊕ Option (Fin q) → ValuationSubring Ω
  | .inl u => s.A u.1
  | .inr (.inl u) => s.A u.1
  | .inr (.inr o) => o.elim (s.A s.v0) B

end SlopeTestRemainingChoices

theorem UpperTheory.V.Pa.arPres :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (V0 : s.Lev) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (n : ℕ) (r : Resid V0.frame O n) (T : TWGrp (globOf r V0)) (_ : TWPl r T), V0.S' = s.S → ∀ N, ∃ (a : ArData (T.GN N) T.q (Module.finrank ℚ (Lp L))) (_ : ArPres a (Lp L) Ω), (∀ v : Vl l L, a.dv v = locDeg v.1) ∧ (((T.h N).p₀).comp (a.φq none)).range = V0.frame.D0 ∧ ∀ j, T.ph N j ∈ (a.φq (some j)).range ∧ T.ta N j ∈ (a.φq (some j)).range := by
  intro l _ L Ω _ _ _ _ _ _ s V0 O _ _ _ _ _ n r T P _ N
  classical
  obtain ⟨hex, hcc⟩ := ccEx l L Ω
  choose c hc using hex
  have hc' : ∀ w, ∃ j : Ω →+* ℂ, ∀ x, j (c w x) = starRingEnd ℂ (j x) := fun w => by
    obtain ⟨j, h, -⟩ := hc w
    exact ⟨j, h⟩
  have hcard : Fintype.card (InfinitePlace (Lp L)) = Module.finrank ℚ (Lp L) := by
    rw [IsTotallyReal.finrank, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
      IsTotallyReal.nrComplexPlaces_eq_zero, add_zero]
  let ip : Fin (Module.finrank ℚ (Lp L)) ≃ InfinitePlace (Lp L) := (Fintype.equivFinOfCardEq hcard).symm
  have hε : ∀ g, (T.GN N).ε ((P.e N).p (toGS Ω (P.V N).S' g)) = cycZ (Lp L) Ω l g := fun g =>
    ((P.e N).ε _).trans (DFunLike.congr_fun (P.V N).hε g)
  let a : ArData (T.GN N) T.q (Module.finrank ℚ (Lp L)) :=
    { Dq := fun o => Dec (F := L) (vaF s (P.B N) (.inr (.inr o)))
      cpt := fun o => isCompact_iff_compactSpace.1 (isClosed_Dec (F := L) _).isCompact
      φq := fun o => (P.e N).p₀.comp ((P.V N).pr.comp (Dec (F := L) _).subtype)
      φq_cont := fun o => ((P.e N).cont.comp
        (((continuous_toGS Ω _).comp continuous_resP).comp continuous_subtype_val)).subtype_mk _
      cw := fun i => (P.e N).p (toGS Ω (P.V N).S' (c (ip i)))
      cw_sq := fun i => (map_mul (P.e N).p _ _).symm.trans
        ((congrArg (P.e N).p ((map_mul (toGS Ω (P.V N).S') _ _).symm.trans
          (by rw [(hcc _ (hc' _)).1, map_one]; rfl))).trans (map_one (P.e N).p))
      cw_η := fun i => ((P.e N).η _).trans
        ((Int.units_eq_one_or _).resolve_left fun h => (hcc _ (hc' _)).2.1 (((P.V N).hη _).1 h))
      cw_ε := fun i => (hε _).trans (hcc _ (hc' _)).2.2
      c_ε := by
        rw [← (P.e N).c]
        exact (hε s.c).trans (hcc _ s.hc).2.2
      dv := fun v => locDeg (Subtype.val v)
      sum_dv := by
        rw [← finsum_eq_sum_of_fintype]
        exact sumDegF l (Lp L) }
  have hsp : ∀ w, Dec (F := Lp L) (vaF s (P.B N) w) ≤ (resP L Ω).range := by
    rintro (u | u | _ | j)
    · exact s.split _ (Or.inl u.2)
    · exact s.split _ (Or.inr (Or.inl u.2))
    · exact s.split _ (Or.inr (Or.inr rfl))
    · exact P.split N j
  choose α hα using fun w => decSplit L Ω _ (hsp w)
  let e0 := MulEquiv.ofBijective (P.e N).p ⟨P.e_inj N, (P.e N).surj⟩
  have ec : Continuous e0.toEquiv := (P.e N).cont
  let e : GS Ω (P.V N).S' ≃ₜ* (T.GN N).Γ :=
    { e0 with
      continuous_toFun := (P.e N).cont
      continuous_invFun := (Continuous.homeoOfEquivCompactToT2 ec).symm.continuous }
  let pl : ArData.W (locOf r) T.q ≃ (P.V N).S' :=
    (Equiv.ofInjective _ (plF_inj s (P.v N) (P.v_inj N) (P.v_not N))).trans
      (Set.equivOfEq ((plF_range s _).trans (P.S_eq N).symm))
  refine ⟨a,
    { S := (P.V N).S'
      above := fun v hv => (P.V N).sub (Or.inl hv)
      e := e
      e_ε := hε
      pl := pl
      pl_l := fun w => plF_l s (P.v N) (P.v_not N) w
      A := vaF s (P.B N)
      isOver := ?_
      α := fun w => match w with
        | .inl u => α (.inl u)
        | .inr (.inl u) => α (.inr (.inl u))
        | .inr (.inr o) => α (.inr (.inr o))
      ι_eq := ?_
      dv_eq := fun v => rfl
      ip := ip
      c := fun i => c (ip i)
      cc := fun i => hc _
      cw_eq := fun i => rfl }, fun v => rfl, ?_, fun j => ⟨⟨⟨P.fr N j, P.fr_dec N j⟩, (P.ph N j).symm⟩, ?_⟩⟩
  · rintro (u | u | _ | j)
    · exact s.hA _
    · exact s.hA _
    · exact s.hA _
    · exact P.B_v N j
  · rintro (u | u | o) g
    · exact ((P.e N).φ u g).symm.trans (congrArg (fun x => (P.e N).p (toGS Ω _ x)) (hα (.inl u) g).symm)
    · exact ((P.e N).φu u g).symm.trans (congrArg (fun x => (P.e N).p (toGS Ω _ x)) (hα (.inr (.inl u)) g).symm)
    · exact congrArg (fun x => (P.e N).p (toGS Ω _ x)) (hα (.inr (.inr o)) g).symm
  · have : ((T.h N).p₀).comp (a.φq none) = V0.pr.comp (Dec (F := L) (s.A s.v0)).subtype :=
      MonoidHom.ext fun g => Subtype.ext (P.e_h N _)
    rw [this]
    exact (MonoidHom.range_comp _ _).trans (congrArg (Subgroup.map V0.pr) (Subgroup.range_subtype _))
  · exact ⟨⟨P.τ N j, Ine_le_Dec _ (P.τ_gen N j).1⟩, (P.ta N j).symm⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.HomCount
open Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem padic_hom_zero {l : ℕ} [Fact l.Prime] {M : Type} [AddCommGroup M] (hM : ∀ y : M, l • y = 0)
    (φ : ℤ_[l] →+ M) (h1 : φ 1 = 0) (c : ℤ_[l]) : φ c = 0 := by
  have hn : ∀ n : ℕ, φ (n : ℤ_[l]) = 0 := fun n => by
    rw [← nsmul_one, map_nsmul, h1, smul_zero]
  have hmem := PadicInt.sub_zmodRepr_mem c
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton'] at hmem
  obtain ⟨a, ha⟩ := hmem
  have hc : c = (c.zmodRepr : ℤ_[l]) + l • a := by
    rw [nsmul_eq_mul, mul_comm, ha]
    ring
  rw [hc, map_add (f := _), hn, map_nsmul, hM, add_zero]

private theorem free_hom_zero {l : ℕ} [Fact l.Prime] {M : Type} [AddCommGroup M] (hM : ∀ y : M, l • y = 0)
    {d : ℕ} (f : ((Fin d → ℤ_[l]) × ℤ_[l]) →+ M) (h1 : ∀ i, f (Pi.single i 1, 0) = 0) (h2 : f (0, 1) = 0)
    (v : (Fin d → ℤ_[l]) × ℤ_[l]) : f v = 0 := by
  have e1 : ∀ i c, f (Pi.single i c, 0) = 0 := fun i c =>
    padic_hom_zero hM (f.comp ((AddMonoidHom.inl _ _).comp (AddMonoidHom.single (fun _ : Fin d => ℤ_[l]) i)))
      (h1 i) c
  have e2 : ∀ c, f (0, c) = 0 := fun c =>
    padic_hom_zero hM (f.comp (AddMonoidHom.inr _ _)) h2 c
  obtain ⟨u, w⟩ := v
  have hs : ((u, w) : (Fin d → ℤ_[l]) × ℤ_[l]) = (∑ i, ((Pi.single i (u i), 0) : (Fin d → ℤ_[l]) × ℤ_[l])) + (0, w) := by
    ext j
    · simp [Prod.fst_sum, Finset.univ_sum_single]
    · simp [Prod.snd_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hs, map_add (f := _), map_sum, e2, add_zero]
  exact Finset.sum_eq_zero fun i _ => e1 i (u i)

private theorem eq_zero_of_eq_self_add_self {M : Type} [AddCommGroup M] (a : M) (h : a = a + a) : a = 0 := by
  have := congrArg (fun x => x - a) h
  simpa using this.symm

private theorem char_zero {l : ℕ} [Fact l.Prime] {M : Type} [AddCommGroup M] [Finite M] (hM : ∀ y : M, l • y = 0)
    {D : Type} [Group D] [TopologicalSpace D] [IsTopologicalGroup D] {I : Subgroup D} {d : ℕ} (A : LocAb l D I d)
    (s : Fin d → D) (t : D) (hs : ∀ i, A.a (s i) = Multiplicative.ofAdd (Pi.single i 1, 0))
    (ht : A.a t = Multiplicative.ofAdd (0, 1))
    (z : D → M) (hz : IsLocallyConstant z) (hm : ∀ g h, z (g * h) = z g + z h) (hμ : ∀ g ∈ muG l D, z g = 0)
    (h1 : ∀ i, z (s i) = 0) (h2 : z t = 0) (g : D) : z g = 0 := by
  have hz1 : z 1 = 0 := by
    have := hm 1 1
    rw [one_mul] at this
    exact eq_zero_of_eq_self_add_self _ this
  let χ : D →* Multiplicative M :=
    { toFun := fun g => Multiplicative.ofAdd (z g)
      map_one' := by simp [hz1]
      map_mul' := fun g h => by simp [hm] }
  have hP : IsPGroup l (Multiplicative M) := fun g => ⟨1, by
    rw [pow_one]
    apply Multiplicative.toAdd.injective
    simp [toAdd_pow, hM]⟩
  have hχ : ∀ g, g ∈ χ.ker ↔ z g = 0 := fun g => by
    rw [MonoidHom.mem_ker]
    show Multiplicative.ofAdd (z g) = 1 ↔ _
    exact ofAdd_eq_one
  have hopen : IsOpen (χ.ker : Set D) := by
    have : (χ.ker : Set D) = z ⁻¹' {0} := by
      ext g
      exact hχ g
    rw [this]
    exact hz.isOpen_fiber 0
  have hmu : muG l D ≤ χ.ker := fun g hg => (hχ g).mpr (hμ g hg)
  have hker := A.univ (Multiplicative M) hP χ hopen hmu
  have dep : ∀ g g', A.a g = A.a g' → z g = z g' := by
    intro g g' h
    have hk : g⁻¹ * g' ∈ A.a.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
    have h0 := (hχ _).mp (hker hk)
    have := hm g (g⁻¹ * g')
    rw [mul_inv_cancel_left, h0, add_zero] at this
    exact this.symm
  let pre : (Fin d → ℤ_[l]) × ℤ_[l] → D := fun v => Classical.choose (A.surj (Multiplicative.ofAdd v))
  have hpre : ∀ v, A.a (pre v) = Multiplicative.ofAdd v := fun v => Classical.choose_spec (A.surj _)
  let φ : ((Fin d → ℤ_[l]) × ℤ_[l]) →+ M := AddMonoidHom.mk' (fun v => z (pre v)) (by
    intro v w
    rw [← hm]
    apply dep
    rw [map_mul, hpre, hpre, hpre]
    rfl)
  have hφ := free_hom_zero hM φ (fun i => by
      show z (pre _) = 0
      rw [dep _ (s i) (by rw [hpre, hs])]
      exact h1 i)
    (by
      show z (pre _) = 0
      rw [dep _ t (by rw [hpre, ht])]
      exact h2)
    (Multiplicative.toAdd (A.a g))
  have : φ (Multiplicative.toAdd (A.a g)) = z g := by
    show z (pre _) = z g
    apply dep
    rw [hpre]
    rfl
  rw [← this, hφ]

theorem UpperTheory.V.Pa.homCount :
    ∀ (l : ℕ) [Fact l.Prime] (F : GFrame l) (n : ℕ) (x : NP F n) (D : Type) [Group D] [TopologicalSpace D] [IsTopologicalGroup D] (I : Subgroup D) (d m : ℕ), LocAb l D I d → {z : D → x.Am m | IsLocallyConstant z ∧ (∀ g h, z (g * h) = z g + z h) ∧ ∀ g ∈ muG l D, z g = 0}.Finite ∧ {z : D → x.Am m | IsLocallyConstant z ∧ (∀ g h, z (g * h) = z g + z h) ∧ ∀ g ∈ muG l D, z g = 0}.ncard ≤ Nat.card x.K ^ (m * (d + 1)) := by
  intro l _ F n x D _ _ _ I d m A
  obtain ⟨hfin, hcard, -, hl, -⟩ := finAm l F n x m 0
  haveI := hfin
  have hs : ∀ i, A.a (Classical.choose (A.surj (Multiplicative.ofAdd ((Pi.single i 1, 0) : (Fin d → ℤ_[l]) × ℤ_[l])))) =
      Multiplicative.ofAdd ((Pi.single i 1, 0) : (Fin d → ℤ_[l]) × ℤ_[l]) :=
    fun i => Classical.choose_spec (A.surj _)
  have ht : A.a (Classical.choose (A.surj (Multiplicative.ofAdd ((0, 1) : (Fin d → ℤ_[l]) × ℤ_[l])))) =
      Multiplicative.ofAdd ((0, 1) : (Fin d → ℤ_[l]) × ℤ_[l]) :=
    Classical.choose_spec (A.surj _)
  set s : Fin d → D := fun i => Classical.choose (A.surj (Multiplicative.ofAdd ((Pi.single i 1, 0) : (Fin d → ℤ_[l]) × ℤ_[l]))) with hs_def
  set t : D := Classical.choose (A.surj (Multiplicative.ofAdd ((0, 1) : (Fin d → ℤ_[l]) × ℤ_[l]))) with ht_def
  set S := {z : D → x.Am m | IsLocallyConstant z ∧ (∀ g h, z (g * h) = z g + z h) ∧ ∀ g ∈ muG l D, z g = 0} with hS
  let ev : (D → x.Am m) → (Fin d → x.Am m) × x.Am m := fun z => (fun i => z (s i), z t)
  have hinj : Set.InjOn ev S := by
    intro z hz z' hz' he
    funext g
    have key := char_zero hl A s t hs ht (z - z') (hz.1.sub hz'.1)
      (fun g h => by
        simp only [Pi.sub_apply, hz.2.1, hz'.2.1]
        abel)
      (fun g hg => by simp [hz.2.2 g hg, hz'.2.2 g hg])
      (fun i => by
        simp only [Pi.sub_apply, sub_eq_zero]
        exact congrFun (congrArg Prod.fst he) i)
      (by
        simp only [Pi.sub_apply, sub_eq_zero]
        exact congrArg Prod.snd he) g
    exact sub_eq_zero.mp key
  refine ⟨Set.Finite.of_finite_image (Set.toFinite _) hinj, ?_⟩
  rw [← hinj.ncard_image]
  refine (Set.ncard_le_card _).trans (le_of_eq ?_)
  rw [Nat.card_prod, Nat.card_fun, Nat.card_fin, hcard, ← pow_succ, ← pow_mul]
end
