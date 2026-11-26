module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlESymmApply
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.CocompactTensor
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousDistribHaarCharUnits
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryStabilizerAnisotropicVectorEquivComplemen
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DiscreteTopologyRatN

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSmulMemLatticeOfMemCompletion
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSmulMemLatticeOfMemCompletion
open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases NumberField IsDedekindDomain Matrix GlobalTheory.LevelHecke
open scoped TensorProduct

namespace GlobalTheory.LatticeDescent

theorem exists_rational_solution {F K V : Type} [Field F] [Field K] [Algebra F K]
    [TopologicalSpace K] [IsTopologicalRing K] (hd : DenseRange (algebraMap F K))
    [AddCommGroup V] [Module F V] {k : ℕ} (s : Fin k → V) (z : V) (a : Fin k → K)
    (U : Set K) (hU : IsOpen U) (ha : ∀ j, a j ∈ U)
    (h : ∀ l : V →ₗ[F] F, algebraMap F K (l z) = ∑ j, algebraMap F K (l (s j)) * a j) :
    ∃ c : Fin k → F, (∀ j, algebraMap F K (c j) ∈ U) ∧ ∑ j, c j • s j = z := by
  classical
  let S : (Fin k → F) →ₗ[F] V := Fintype.linearCombination F s
  have hS : ∀ c, S c = ∑ j, c j • s j := fun c => Fintype.linearCombination_apply F s c
  have hs : ∀ j, s j ∈ LinearMap.range S := fun j => ⟨Pi.single j 1, by
    simp [S]⟩
  have hz : z ∈ LinearMap.range S := by
    by_contra hz
    obtain ⟨f, hf, hm⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hz inferInstance
    have h0 : ∀ j, f (s j) = 0 := fun j => by
      have : f (s j) ∈ Submodule.map f (LinearMap.range S) := Submodule.mem_map_of_mem (hs j)
      rwa [hm] at this
    have := h f
    simp only [h0, map_zero, zero_mul, Finset.sum_const_zero] at this
    exact hf ((algebraMap F K).injective (by rw [this, map_zero]))
  obtain ⟨T0, hT0⟩ := S.rangeRestrict.exists_rightInverse_of_surjective S.range_rangeRestrict
  obtain ⟨T, hT⟩ := LinearMap.exists_extend T0
  have hST : ∀ y ∈ LinearMap.range S, S (T y) = y := fun y hy => by
    have e1 : T y = T0 ⟨y, hy⟩ := LinearMap.congr_fun hT ⟨y, hy⟩
    have e2 := congrArg Subtype.val (LinearMap.congr_fun hT0 ⟨y, hy⟩)
    rw [e1]
    exact e2
  let φ : (Fin k → K) → (Fin k → K) := fun x i =>
    x i - ∑ j, algebraMap F K (T (s j) i) * x j + algebraMap F K (T z i)
  have hφ : Continuous φ := by
    refine continuous_pi fun i => ?_
    simp only [φ]
    fun_prop
  have hφa : φ a = a := by
    funext i
    have := h ((LinearMap.proj i).comp T)
    simp only [LinearMap.comp_apply, LinearMap.proj_apply] at this
    simp only [φ, this]
    ring
  have hopen : IsOpen (φ ⁻¹' Set.pi Set.univ fun _ => U) :=
    (isOpen_set_pi Set.finite_univ fun _ _ => hU).preimage hφ
  obtain ⟨b, hb⟩ := (DenseRange.piMap (fun _ : Fin k => hd)).exists_mem_open hopen
    ⟨a, by rw [Set.mem_preimage, hφa]; exact fun j _ => ha j⟩
  refine ⟨b - T (S b) + T z, fun i => ?_, ?_⟩
  · have := hb i trivial
    convert this using 1
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [φ, Pi.map_apply, hS, map_sum, map_smul, Pi.add_apply, Pi.sub_apply,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_add, map_sub, map_mul, mul_comm]
  · rw [← hS, map_add (f := _), map_sub, hST _ ⟨b, rfl⟩, hST _ hz, sub_self, zero_add]

theorem functional_of_tmul {F E K : Type} [Field F] [Field E] [Field K] [Algebra F E] [Algebra F K]
    {n k : ℕ} (s : Fin k → Fin n → E) (z : Fin n → E) (a : Fin k → K)
    (h : ∀ i, z i ⊗ₜ[F] (1 : K) = ∑ j, s j i ⊗ₜ[F] a j) (l : (Fin n → E) →ₗ[F] F) :
    algebraMap F K (l z) = ∑ j, algebraMap F K (l (s j)) * a j := by
  classical
  have hl : ∀ y : Fin n → E, l y = ∑ i, l (Pi.single i (y i)) := fun y => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_sum, Finset.univ_sum_single]
  have hi : ∀ i, l (Pi.single i (z i)) • (1 : K) = ∑ j, l (Pi.single i (s j i)) • a j := fun i => by
    have := congrArg (fun t => TensorProduct.lid F K
      (LinearMap.rTensor K (l.comp (LinearMap.single F (fun _ : Fin n => E) i)) t)) (h i)
    set_option synthInstance.maxHeartbeats 100000 in
      simpa only [map_sum, LinearMap.rTensor_tmul, TensorProduct.lid_tmul, LinearMap.comp_apply,
      LinearMap.single_apply] using this
  rw [hl z, Algebra.algebraMap_eq_smul_one, Finset.sum_smul]
  simp only [hi]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_smul, ← hl, Algebra.smul_def]

theorem exists_smul_mem_of_mem_latS : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) (M : Submodule (𝓞 E) (Fin n → E)), Submodule.IsLattice E M → ∀ z : Fin n → E, (fun a => inclE (F := F) (v.adicCompletion F) (z a)) ∈ latS (F := F) (v.adicCompletion F) (intV E v) M → ∃ r : 𝓞 F, r ∉ v.asIdeal ∧ algebraMap (𝓞 F) (𝓞 E) r • z ∈ M := by
  intro F E _ _ _ _ _ v n M hM z hz
  classical
  have : Module.Finite (𝓞 E) M := Module.Finite.iff_fg.2 hM.fg
  have : Module.Finite ℤ M := Module.Finite.trans (𝓞 E) M
  obtain ⟨k, s, hs⟩ := Module.Finite.exists_fin (R := ℤ) (M := M)
  obtain ⟨a, ha, ea⟩ := (GlobalTheory.LatticeStabLocal.mem_latS_iff_isComb hs _).1 hz
  obtain ⟨c, hc, ec⟩ := exists_rational_solution (HeightOneSpectrum.denseRange_algebraMap F v)
    (fun j => (s j : Fin n → E)) z a (v.adicCompletionIntegers F)
    (Valued.isOpen_valuationSubring _) ha
    (functional_of_tmul (fun j => (s j : Fin n → E)) z a ea)
  have hv : ∀ j, v.valuation F (c j) ≤ 1 := fun j => by
    rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (c j)]
    exact hc j
  choose m d hmd using fun j => v.exists_primeCompl_mul_eq_of_integer (c j) (hv j)
  refine ⟨∏ j, (d j : 𝓞 F), (prod_mem fun j _ => (d j).2 : _ ∈ v.asIdeal.primeCompl), ?_⟩
  rw [← ec, Finset.smul_sum]
  refine sum_mem fun j _ => ?_
  have e : algebraMap (𝓞 F) (𝓞 E) (∏ j, (d j : 𝓞 F)) • c j • (s j : Fin n → E) =
      algebraMap (𝓞 F) (𝓞 E) ((∏ i ∈ Finset.univ.erase j, (d i : 𝓞 F)) * m j) •
        (s j : Fin n → E) := by
    have key : ∀ (x : 𝓞 F) (y : Fin n → E),
        algebraMap (𝓞 F) (𝓞 E) x • y = algebraMap (𝓞 F) F x • y := fun x y => by
      funext i
      simp only [Pi.smul_apply, Algebra.smul_def]
      rfl
    rw [key, key, smul_smul, map_mul, ← hmd j, ← Finset.prod_erase_mul _ _ (Finset.mem_univ j),
      map_mul]
    congr 1
    ring
  rw [e]
  exact M.smul_mem _ (s j).2

end GlobalTheory.LatticeDescent
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSmulMemLatticeOfMemCompletionStatement
open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases NumberField IsDedekindDomain Matrix GlobalTheory.LevelHecke
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_smul_mem_lattice_of_mem_completion : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) (M : Submodule (𝓞 E) (Fin n → E)), Submodule.IsLattice E M → ∀ z : Fin n → E, (fun a => inclE (F := F) (v.adicCompletion F) (z a)) ∈ latS (F := F) (v.adicCompletion F) (intV E v) M → ∃ r : 𝓞 F, r ∉ v.asIdeal ∧ algebraMap (𝓞 F) (𝓞 E) r • z ∈ M := by
  first | exact @GlobalTheory.LatticeDescent.exists_smul_mem_of_mem_latS | exact GlobalTheory.LatticeDescent.exists_smul_mem_of_mem_latS | (intros; apply GlobalTheory.LatticeDescent.exists_smul_mem_of_mem_latS <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DualLatticeBidual
open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases NumberField IsDedekindDomain Matrix GlobalTheory.LevelHecke
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.LevelHecke.DualConj

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem mem_dualL (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)) (y : Fin n → E) :
    y ∈ dualL σ J L ↔ ∀ x ∈ L, hform σ J x y ∈ (algebraMap (𝓞 E) E).range := by
  have := bwG_span_dualSet σ J L
  change y ∈ ((Submodule.span (𝓞 E) (dualSet σ J L) : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)) ↔ _
  rw [this]; rfl

omit [NumberField E] in
theorem hform_eq (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) :
    hform σ J x y = (fun i => σ (x i)) ⬝ᵥ (J *ᵥ y) := by
  simp only [hform, dotProduct, mulVec, Finset.mul_sum, mul_assoc]

omit [NumberField E] in
theorem hform_unitary (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E) (g : Matrix (Fin n) (Fin n) E)
    (hg : cT σ g * J * g = J) (x y : Fin n → E) : hform σ J (g *ᵥ x) (g *ᵥ y) = hform σ J x y := by
  have e : (fun i => σ ((g *ᵥ x) i)) = (fun i => σ (x i)) ᵥ* cT σ g := by
    funext i
    simp [cT, mulVec, vecMul, dotProduct, mul_comm]
  rw [hform_eq, hform_eq, e, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, hg]

omit [NumberField E] in
theorem hform_smul_left (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E) (a : E) (x y : Fin n → E) :
    hform σ J (a • x) y = σ a * hform σ J x y := by
  simp only [hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum, mul_assoc]

omit [NumberField E] in
theorem hform_smul_right (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E) (a : E) (x y : Fin n → E) :
    hform σ J x (a • y) = a * hform σ J x y := by
  simp only [hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

@[reducible] def starOf (σ : E →+* E) (hσ : ∀ x, σ (σ x) = x) : StarRing E where
  star := σ
  star_involutive := hσ
  star_mul a b := by rw [map_mul, mul_comm]
  star_add := map_add σ

theorem dual_lattice_bidual (σ : E →+* E) (hσ : ∀ x, σ (σ x) = x) (J : Matrix (Fin n) (Fin n) E)
    (hJ : IsUnit J.det) (hH : cT σ J = J) (L : Submodule (𝓞 E) (Fin n → E)) (hL : Submodule.IsFullLattice E L) :
    Submodule.IsFullLattice E (dualL σ J L) ∧ dualL σ J (dualL σ J L) = L := by
  letI : StarRing E := starOf σ hσ
  let h : (Fin n → E) →ₗ⋆[E] (Fin n → E) →ₗ[E] E :=
    LinearMap.mk₂'ₛₗ (starRingEnd E) (RingHom.id E) (hform σ J)
      (fun x x' y => by simp only [hform, Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib])
      (fun a x y => hform_smul_left σ J a x y)
      (fun x y y' => by simp only [hform, Pi.add_apply, mul_add, Finset.sum_add_distrib])
      (fun a x y => hform_smul_right σ J a x y)
  have hh : ∀ x y, h x y = hform σ J x y := fun _ _ => rfl
  have hsym' : ∀ x y, σ (hform σ J x y) = hform σ J y x := by
    intro x y
    have e : ∀ i j, σ (J i j) = J j i := fun i j => congrFun (congrFun hH j) i
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hform, map_sum, map_mul, hσ, e]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hsym : h.IsSymm := ⟨fun x y => hsym' x y⟩
  have hr : ∀ y, (∀ x, hform σ J x y = 0) → y = 0 := by
    intro y hy
    have h1 : J *ᵥ y = 0 := by
      funext i
      have := hy (Pi.single i 1)
      rw [hform_eq, dotProduct, Finset.sum_eq_single i] at this
      · simpa using this
      · intro b _ hb
        simp [hb]
      · simp
    have ey : y = J⁻¹ *ᵥ (J *ᵥ y) := by
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul J hJ, Matrix.one_mulVec]
    rw [ey, h1, mulVec_zero]
  have hnd : h.Nondegenerate := by
    refine ⟨fun x hx => hr x fun y => ?_, fun y hy => hr y hy⟩
    rw [← hsym', ← hh, hx y, map_zero]
  have hd : ∀ M : Submodule (𝓞 E) (Fin n → E), Formalism.HermitianLatticesTheory.dual h M = dualL σ J M := by
    intro M
    ext y
    rw [mem_dualL]
    simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, Submodule.mem_one]
    rfl
  have := Formalism.HermitianLatticesTheory.dualLattice (𝓞 E) E (Fin n → E) h hsym hnd (fun r => LocB.sig_int σ r) L hL
  rw [hd, hd] at this
  exact ⟨this.1, this.2.1⟩

theorem localization_dualL_le (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E) (P Q : Ideal (𝓞 E)) [P.IsPrime] [Q.IsPrime]
    (hPQ : ∀ a b : 𝓞 E, (a : E) = σ (b : E) → a ∈ Q → b ∈ P) (M N : Submodule (𝓞 E) (Fin n → E)) (hM : M.FG)
    (h : Formalism.HermitianLatticesTheory.localization₂ P M ≤ Formalism.HermitianLatticesTheory.localization₂ P N) :
    Formalism.HermitianLatticesTheory.localization₂ Q (dualL σ J N) ≤ Formalism.HermitianLatticesTheory.localization₂ Q (dualL σ J M) := by
  have h1P : (1 : 𝓞 E) ∉ P := P.ne_top_iff_one.1 (Ideal.IsPrime.ne_top inferInstance)
  have key : ∃ s : 𝓞 E, s ∉ P ∧ ∀ x ∈ M, s • x ∈ N := by
    have h0 : M ≤ Formalism.HermitianLatticesTheory.localization₂ P N := fun x hx =>
      h ((rlv_mem_locP P M x).2 ⟨1, h1P, by rwa [one_smul]⟩)
    clear h
    induction M, hM using Submodule.fg_induction with
    | singleton x =>
      obtain ⟨s, hs, hx⟩ := (rlv_mem_locP P N x).1 (h0 (Submodule.mem_span_singleton_self x))
      refine ⟨s, hs, fun y hy => ?_⟩
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hy
      rw [smul_comm]; exact N.smul_mem a hx
    | sup A B _ _ hA hB =>
      obtain ⟨s, hs, h1⟩ := hA (le_sup_left.trans h0)
      obtain ⟨t, ht, h2⟩ := hB (le_sup_right.trans h0)
      refine ⟨s * t, fun hst => (Ideal.IsPrime.mem_or_mem inferInstance hst).elim hs ht, fun y hy => ?_⟩
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hy
      rw [smul_add]
      refine N.add_mem ?_ ?_
      · rw [mul_comm, mul_smul]; exact N.smul_mem _ (h1 a ha)
      · rw [mul_smul]; exact N.smul_mem _ (h2 b hb)
  obtain ⟨s, hs, hsM⟩ := key
  obtain ⟨s', hs'⟩ := LocB.sig_int σ s
  have hs'Q : s' ∉ Q := fun hq => hs (hPQ s' s hs' hq)
  intro y hy
  obtain ⟨t, ht, hty⟩ := (rlv_mem_locP Q _ y).1 hy
  refine (rlv_mem_locP Q _ y).2 ⟨s' * t, fun hst => (Ideal.IsPrime.mem_or_mem inferInstance hst).elim hs'Q ht, ?_⟩
  rw [mem_dualL] at hty ⊢
  intro x hx
  have := hty _ (hsM x hx)
  rw [← algebraMap_smul E s x, hform_smul_left] at this
  rw [mul_smul, ← algebraMap_smul E s' (t • y), hform_smul_right, hs']
  exact this

theorem mem_mulLat (γ : GL (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)) (y : Fin n → E) :
    y ∈ mulLat γ.1 L ↔ (γ⁻¹).1 *ᵥ y ∈ L := by
  rw [← map_glE, Submodule.mem_map_equiv, glE_symm_apply]

theorem mulLat_lattice (γ : GL (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)) (hL : Submodule.IsFullLattice E L) :
    Submodule.IsFullLattice E (mulLat γ.1 L) := by
  letI : Submodule.IsLattice E (mulLat γ.1 L) := Submodule.IsLattice.of_fg E (hL.fg.map _)
  constructor
  change Submodule.span E ((L.map ((Matrix.mulVecLin γ.1).restrictScalars (𝓞 E)) :
    Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)) = ⊤
  rw [show Submodule.span E ((L.map ((Matrix.mulVecLin γ.1).restrictScalars (𝓞 E)) :
      Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)) =
      (Submodule.span E (L : Set (Fin n → E))).map (Matrix.mulVecLin γ.1) by
        rw [Submodule.map_span]; rfl,
    hL.span_eq_top, Submodule.map_top, LinearMap.range_eq_top]
  exact (glE γ).surjective

theorem dualL_mulLat (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E) (γ : GL (Fin n) E) (hγ : γ ∈ UJ σ J)
    (L : Submodule (𝓞 E) (Fin n → E)) : dualL σ J (mulLat γ.1 L) = mulLat γ.1 (dualL σ J L) := by
  ext y
  have ey : γ.1 *ᵥ ((γ⁻¹).1 *ᵥ y) = y := (glE γ).apply_symm_apply y
  rw [mem_mulLat, mem_dualL, mem_dualL]
  constructor
  · intro h x hx
    rw [← hform_unitary σ J γ.1 hγ, ey]
    exact h _ ⟨x, hx, rfl⟩
  · rintro h _ ⟨x, hx, rfl⟩
    have := h x hx
    rw [← hform_unitary σ J γ.1 hγ, ey] at this
    exact this

theorem dual_conj_primes : ∀ (E : Type) [Field E] [NumberField E] (σ : E →+* E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (P Q : Ideal (𝓞 E)) [P.IsPrime] [Q.IsPrime], (∀ x, σ (σ x) = x) → IsUnit J.det → cT σ J = J → (∀ a b : 𝓞 E, (b : E) = σ (a : E) → (a ∈ Q ↔ b ∈ P)) → ∀ M N : Submodule (𝓞 E) (Fin n → E), Submodule.IsFullLattice E M → Submodule.IsFullLattice E N → (Formalism.HermitianLatticesTheory.localization₂ P M = Formalism.HermitianLatticesTheory.localization₂ P N → Formalism.HermitianLatticesTheory.localization₂ Q (dualL σ J M) = Formalism.HermitianLatticesTheory.localization₂ Q (dualL σ J N)) ∧ (Formalism.HermitianLatticesTheory.localization₂ P (dualL σ J M) = Formalism.HermitianLatticesTheory.localization₂ P (dualL σ J N) → Formalism.HermitianLatticesTheory.localization₂ Q M = Formalism.HermitianLatticesTheory.localization₂ Q N) ∧ ∀ γ : GL (Fin n) E, γ ∈ UJ σ J → Submodule.IsFullLattice E (mulLat γ.1 M) ∧ dualL σ J (mulLat γ.1 M) = mulLat γ.1 (dualL σ J M) := by
  intro E _ _ σ n J P Q _ _ hσ hJ hH hPQ M N hM hN
  have hPQ' : ∀ a b : 𝓞 E, (a : E) = σ (b : E) → a ∈ Q → b ∈ P := fun a b hab =>
    (hPQ a b (by rw [hab, hσ])).1
  have one : ∀ A B : Submodule (𝓞 E) (Fin n → E), A.FG → B.FG → Formalism.HermitianLatticesTheory.localization₂ P A = Formalism.HermitianLatticesTheory.localization₂ P B →
      Formalism.HermitianLatticesTheory.localization₂ Q (dualL σ J A) = Formalism.HermitianLatticesTheory.localization₂ Q (dualL σ J B) := fun A B hA hB h =>
    le_antisymm (localization_dualL_le σ J P Q hPQ' B A hB h.ge) (localization_dualL_le σ J P Q hPQ' A B hA h.le)
  obtain ⟨hM1, hM2⟩ := dual_lattice_bidual σ hσ J hJ hH M hM
  obtain ⟨hN1, hN2⟩ := dual_lattice_bidual σ hσ J hJ hH N hN
  refine ⟨one M N hM.fg hN.fg, fun h => ?_, fun γ hγ => ⟨mulLat_lattice γ M hM, dualL_mulLat σ J γ hγ M⟩⟩
  have := one _ _ hM1.fg hN1.fg h
  rwa [hM2, hN2] at this

end GlobalTheory.LevelHecke.DualConj

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.QuadraticGelfandInvariantEqNegSumSqDefinite
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.QuadraticGelfandInvariantEqNegSumSqDefinite
open Matrix
attribute [local instance 100] LieRing.ofAssociativeRing

namespace GlobalTheory.DefiniteUnitaryCasimir

open GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.UnitaryLieComplexification

variable {n : ℕ} {J : Matrix (Fin n) (Fin n) ℂ}

theorem exists_linear_extension (hJ : Jᴴ = J) (hu : IsUnit J.det) {A : Type} [Ring A] [Algebra ℂ A] (ρ : lieU J → A)
    (hadd : ∀ X Y, ρ (X + Y) = ρ X + ρ Y) (hsm : ∀ (c : ℝ) X, ρ (c • X) = (c : ℂ) • ρ X) :
    ∃ R : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] A,
      (∀ Z, R Z = ρ (rePart hJ hu Z) + Complex.I • ρ (imPart hJ hu Z)) ∧ (∀ X : lieU J, R X.1 = ρ X) := by
  have hsub : ∀ X Y, ρ (X - Y) = ρ X - ρ Y := by
    intro X Y
    have := hadd (X - Y) Y
    rw [sub_add_cancel] at this
    rw [this, add_sub_cancel_right]
  have h0 : ρ 0 = 0 := by
    have := hsub 0 0
    rwa [sub_self, sub_self] at this
  let r : Matrix (Fin n) (Fin n) ℂ → A := fun Z => ρ (rePart hJ hu Z) + Complex.I • ρ (imPart hJ hu Z)
  have key : ∀ X Y : lieU J, r (X.1 + Complex.I • Y.1) = ρ X + Complex.I • ρ Y := by
    intro X Y
    simp only [r, rePart_mk, imPart_mk]
  have hII : ∀ {M : Type} [AddCommGroup M] [Module ℂ M] (m : M), Complex.I • Complex.I • m = -m := by
    intro M _ _ m
    rw [smul_smul, Complex.I_mul_I, neg_one_smul]
  refine ⟨{ toFun := r, map_add' := ?_, map_smul' := ?_ }, fun Z => rfl, ?_⟩
  · intro Z W
    obtain ⟨X, Y, rfl⟩ := exists_mk hJ hu Z
    obtain ⟨X', Y', rfl⟩ := exists_mk hJ hu W
    have : X.1 + Complex.I • Y.1 + (X'.1 + Complex.I • Y'.1) = (X + X').1 + Complex.I • (Y + Y').1 := by
      change _ = (X.1 + X'.1) + Complex.I • (Y.1 + Y'.1)
      module
    rw [this, key, key, key, hadd, hadd]
    module
  · intro c Z
    obtain ⟨X, Y, rfl⟩ := exists_mk hJ hu Z
    have hc : c = (c.re : ℂ) + (c.im : ℂ) * Complex.I := (Complex.re_add_im c).symm
    generalize c.re = a at hc
    generalize c.im = b at hc
    subst hc
    have : ((a : ℂ) + (b : ℂ) * Complex.I) • (X.1 + Complex.I • Y.1) =
        (a • X - b • Y).1 + Complex.I • (b • X + a • Y).1 := by
      change _ = ((a : ℂ) • X.1 - (b : ℂ) • Y.1) + Complex.I • ((b : ℂ) • X.1 + (a : ℂ) • Y.1)
      simp only [add_smul, smul_add, mul_smul, hII]
      module
    rw [this, key, key, hsub, hadd, hsm, hsm, hsm, hsm]
    simp only [RingHom.id_apply, add_smul, smul_add, mul_smul, hII]
    module
  · intro X
    have := key X 0
    simpa [h0] using this

theorem mul_single_mul (U V : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) :
    U * single a b (1 : ℂ) * V = ∑ c, ∑ d, (U c a * V b d) • single c d (1 : ℂ) := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single (U * single a b (1 : ℂ) * V)]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  rw [Matrix.smul_single, smul_eq_mul, mul_one]
  congr 1
  simp [Matrix.mul_apply, Matrix.single_apply, ite_and]

theorem casimir_move {A : Type} [Ring A] [Algebra ℂ A] (R R' : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] A)
    (U V : Matrix (Fin n) (Fin n) ℂ) :
    ∑ a, ∑ b, R (U * single a b 1 * V) * R' (single b a 1) =
      ∑ c, ∑ d, R (single c d 1) * R' (V * single d c 1 * U) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [mul_single_mul, map_sum, map_smul, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm]
  rw [← Fintype.sum_prod_type', ← Fintype.sum_prod_type' (f := fun c d => ∑ b, ∑ a, (V b d * U c a) • (R (single c d 1) * R' (single b a 1)))]
  simp only [← Fintype.sum_prod_type']
  refine Fintype.sum_equiv ((Equiv.prodComm _ _).trans (Equiv.prodCongr (Equiv.refl _) (Equiv.prodComm _ _))) _ _
    fun q => ?_
  simp [mul_comm]

theorem casimir_conj {A : Type} [Ring A] [Algebra ℂ A] (R : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] A)
    (B : Matrix (Fin n) (Fin n) ℂ) (hB : IsUnit B.det) :
    ∑ a, ∑ b, R (single a b 1) * R (single b a 1) =
      ∑ a, ∑ b, R (B⁻¹ * single a b 1 * B) * R (B⁻¹ * single b a 1 * B) := by
  have := casimir_move R (R ∘ₗ (LinearMap.mulRight ℂ B) ∘ₗ (LinearMap.mulLeft ℂ B⁻¹)) B⁻¹ B
  simp only [LinearMap.comp_apply, LinearMap.mulRight_apply, LinearMap.mulLeft_apply] at this
  rw [this]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  congr 2
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul B hB, Matrix.one_mul, Matrix.mul_assoc,
    Matrix.nonsing_inv_mul B hB, Matrix.mul_one]

theorem cj_conj_single (B : Matrix (Fin n) (Fin n) ℂ) (hB : IsUnit B.det) (h : J = Bᴴ * B ∨ J = -(Bᴴ * B))
    (a b : Fin n) : cj J (B⁻¹ * single a b 1 * B) = -(B⁻¹ * single b a 1 * B) := by
  have hBH : IsUnit Bᴴ.det := by rw [det_conjTranspose]; exact hB.star
  have key : (Bᴴ * B)⁻¹ * (B⁻¹ * single a b (1 : ℂ) * B)ᴴ * (Bᴴ * B) = B⁻¹ * single b a 1 * B := by
    rw [Matrix.mul_inv_rev, conjTranspose_mul, conjTranspose_mul, conjTranspose_nonsing_inv, conjTranspose_single,
      star_one]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Bᴴ⁻¹ Bᴴ B, ← Matrix.mul_assoc Bᴴ⁻¹ Bᴴ, Matrix.nonsing_inv_mul _ hBH, Matrix.one_mul,
      Matrix.one_mul]
  rcases h with rfl | rfl
  · rw [cj, key]
  · have hu : IsUnit (Bᴴ * B).det := by rw [det_mul]; exact hBH.mul hB
    have : (-(Bᴴ * B))⁻¹ = -(Bᴴ * B)⁻¹ := by
      apply Matrix.inv_eq_left_inv
      rw [neg_mul_neg, Matrix.nonsing_inv_mul _ hu]
    rw [cj, this, neg_mul, neg_mul_neg, key]

theorem sum_squares {A : Type} [Ring A] [Algebra ℂ A] (F : Fin n → Fin n → A) :
    ∑ a, ∑ b, F a b * F b a =
      -∑ a, ∑ b, (((1 / 2 : ℂ) • (F a b - F b a)) * ((1 / 2 : ℂ) • (F a b - F b a)) +
        ((1 / (2 * Complex.I) : ℂ) • (F a b + F b a)) * ((1 / (2 * Complex.I) : ℂ) • (F a b + F b a))) := by
  have h : (1 / (2 * Complex.I) : ℂ) * (1 / (2 * Complex.I)) = -(1 / 4) := by
    field_simp
    simp
    norm_num
  have h1 : ∀ a b, ((1 / 2 : ℂ) • (F a b - F b a)) * ((1 / 2 : ℂ) • (F a b - F b a)) +
        ((1 / (2 * Complex.I) : ℂ) • (F a b + F b a)) * ((1 / (2 * Complex.I) : ℂ) • (F a b + F b a)) =
        -((1 / 2 : ℂ) • (F a b * F b a) + (1 / 2 : ℂ) • (F b a * F a b)) := by
    intro a b
    simp only [smul_mul_smul_comm, h, mul_add, add_mul, mul_sub, sub_mul]
    module
  simp only [h1, Finset.sum_neg_distrib, neg_neg, Finset.sum_add_distrib, ← Finset.smul_sum]
  rw [Finset.sum_comm (f := fun a b => F b a * F a b)]
  module

theorem casimir_eq_neg_sum_sq : ∀ (n : ℕ) (J B : Matrix (Fin n) (Fin n) ℂ), IsUnit B.det → (J = Bᴴ * B ∨ J = -(Bᴴ * B)) → ∃ X : Fin n × Fin n × Bool → GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.lieU J, Submodule.span ℝ (Set.range X) = ⊤ ∧ ∀ P Q : Fin n → Fin n → GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.lieU J, (∀ a b, (P a b).1 = (1 / 2 : ℂ) • (Matrix.single a b 1 + -(J⁻¹ * (Matrix.single a b (1 : ℂ))ᴴ * J)) ∧ (Q a b).1 = (1 / (2 * Complex.I)) • (Matrix.single a b 1 - -(J⁻¹ * (Matrix.single a b (1 : ℂ))ᴴ * J))) → ∀ (A : Type) [Ring A] [Algebra ℂ A] (ρ : GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.lieU J → A), (∀ Y Z, ρ (Y + Z) = ρ Y + ρ Z) → (∀ (c : ℝ) Y, ρ (c • Y) = (c : ℂ) • ρ Y) → ∑ a, ∑ b, (ρ (P a b) + Complex.I • ρ (Q a b)) * (ρ (P b a) + Complex.I • ρ (Q b a)) = -∑ i, ρ (X i) * ρ (X i) := by
  intro n J B hB h
  have hBH : IsUnit Bᴴ.det := by rw [det_conjTranspose]; exact hB.star
  have hJ : Jᴴ = J := by
    rcases h with rfl | rfl <;> simp
  have hu : IsUnit J.det := by
    rcases h with rfl | rfl
    · rw [det_mul]; exact hBH.mul hB
    · rw [det_neg, det_mul]; exact (isUnit_one.neg.pow _).mul (hBH.mul hB)
  let F : Fin n → Fin n → Matrix (Fin n) (Fin n) ℂ := fun a b => B⁻¹ * single a b 1 * B
  let X : Fin n × Fin n × Bool → lieU J := fun p =>
    if p.2.2 then rePart hJ hu (F p.1 p.2.1) else imPart hJ hu (F p.1 p.2.1)
  refine ⟨X, ?_, ?_⟩
  · rw [eq_top_iff]
    rintro Y -
    let S : Submodule ℝ (lieU J) := Submodule.span ℝ (Set.range X)
    have hS : ∀ Z : Matrix (Fin n) (Fin n) ℂ, Z ∈ Submodule.span ℂ (Set.range fun p : Fin n × Fin n => F p.1 p.2) →
        ∃ U ∈ S, ∃ V ∈ S, Z = U.1 + Complex.I • V.1 := by
      intro Z hZ
      induction hZ using Submodule.span_induction with
      | mem Z hZ =>
        obtain ⟨⟨a, b⟩, rfl⟩ := hZ
        exact ⟨_, Submodule.subset_span ⟨(a, b, true), rfl⟩, _, Submodule.subset_span ⟨(a, b, false), rfl⟩,
          (re_add_im hJ hu _).symm⟩
      | zero => exact ⟨0, S.zero_mem, 0, S.zero_mem, by simp⟩
      | add Z W _ _ hZ hW =>
        obtain ⟨U, hU, V, hV, rfl⟩ := hZ
        obtain ⟨U', hU', V', hV', rfl⟩ := hW
        refine ⟨U + U', S.add_mem hU hU', V + V', S.add_mem hV hV', ?_⟩
        change _ = (U.1 + U'.1) + Complex.I • (V.1 + V'.1)
        module
      | smul c Z _ hZ =>
        obtain ⟨U, hU, V, hV, rfl⟩ := hZ
        have hc : c = (c.re : ℂ) + (c.im : ℂ) * Complex.I := (Complex.re_add_im c).symm
        generalize c.re = a at hc
        generalize c.im = b at hc
        subst hc
        refine ⟨a • U - b • V, S.sub_mem (S.smul_mem _ hU) (S.smul_mem _ hV), b • U + a • V,
          S.add_mem (S.smul_mem _ hU) (S.smul_mem _ hV), ?_⟩
        have hII : ∀ (m : Matrix (Fin n) (Fin n) ℂ), Complex.I • Complex.I • m = -m := by
          intro m
          rw [smul_smul, Complex.I_mul_I, neg_one_smul]
        change _ = ((a : ℂ) • U.1 - (b : ℂ) • V.1) + Complex.I • ((b : ℂ) • U.1 + (a : ℂ) • V.1)
        simp only [add_smul, smul_add, mul_smul, hII]
        module
    have hY : Y.1 ∈ Submodule.span ℂ (Set.range fun p : Fin n × Fin n => F p.1 p.2) := by
      have : Y.1 = B⁻¹ * (B * Y.1 * B⁻¹) * B := by
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul B hB, Matrix.one_mul, Matrix.mul_assoc,
          Matrix.nonsing_inv_mul B hB, Matrix.mul_one]
      rw [this, Matrix.matrix_eq_sum_single (B * Y.1 * B⁻¹)]
      simp only [Finset.mul_sum, Finset.sum_mul]
      refine Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ => ?_
      have : Matrix.single a b ((B * Y.1 * B⁻¹) a b) = (B * Y.1 * B⁻¹) a b • Matrix.single a b (1 : ℂ) := by
        rw [Matrix.smul_single, smul_eq_mul, mul_one]
      rw [this, mul_smul_comm, smul_mul_assoc]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(a, b), rfl⟩)
    obtain ⟨U, hU, V, -, hUV⟩ := hS _ hY
    have h1 := rePart_mk hJ hu U V
    have h2 := rePart_mk hJ hu Y 0
    have h3 : Y.1 + Complex.I • (0 : lieU J).1 = Y.1 := by simp
    rw [h3, hUV, h1] at h2
    rw [← h2]
    exact hU
  · intro P Q hPQ A _ _ ρ hadd hsm
    obtain ⟨R, hR, hX⟩ := exists_linear_extension hJ hu ρ hadd hsm
    have hP : ∀ a b, P a b = rePart hJ hu (single a b 1) := fun a b => Subtype.ext (hPQ a b).1
    have hQ : ∀ a b, Q a b = imPart hJ hu (single a b 1) := fun a b => Subtype.ext (hPQ a b).2
    simp only [hP, hQ, ← hR]
    rw [casimir_conj R B hB, sum_squares (fun a b => R (F a b))]
    congr 1
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun b _ => ?_
    have e1 : ρ (X (a, b, true)) = (1 / 2 : ℂ) • (R (F a b) - R (F b a)) := by
      rw [← hX]
      change R ((1 / 2 : ℂ) • (F a b + cj J (F a b))) = _
      rw [cj_conj_single B hB h, map_smul, map_add (f := _), map_neg, ← sub_eq_add_neg]
    have e2 : ρ (X (a, b, false)) = (1 / (2 * Complex.I) : ℂ) • (R (F a b) + R (F b a)) := by
      rw [← hX]
      change R ((1 / (2 * Complex.I) : ℂ) • (F a b - cj J (F a b))) = _
      rw [cj_conj_single B hB h, map_smul, map_sub, map_neg, sub_neg_eq_add]
    rw [Fintype.sum_bool, e1, e2]

end GlobalTheory.DefiniteUnitaryCasimir
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.QuadraticGelfandInvariantEqNegSumSqDefiniteStatement
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quadraticGelfandInvariant_eq_neg_sum_sq_definite : ∀ (n : ℕ) (J B : Matrix (Fin n) (Fin n) ℂ), IsUnit B.det → (J = Bᴴ * B ∨ J = -(Bᴴ * B)) → ∃ X : Fin n × Fin n × Bool → GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.lieU J, Submodule.span ℝ (Set.range X) = ⊤ ∧ ∀ P Q : Fin n → Fin n → GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.lieU J, (∀ a b, (P a b).1 = (1 / 2 : ℂ) • (Matrix.single a b 1 + -(J⁻¹ * (Matrix.single a b (1 : ℂ))ᴴ * J)) ∧ (Q a b).1 = (1 / (2 * Complex.I)) • (Matrix.single a b 1 - -(J⁻¹ * (Matrix.single a b (1 : ℂ))ᴴ * J))) → ∀ (A : Type) [Ring A] [Algebra ℂ A] (ρ : GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.lieU J → A), (∀ Y Z, ρ (Y + Z) = ρ Y + ρ Z) → (∀ (c : ℝ) Y, ρ (c • Y) = (c : ℂ) • ρ Y) → ∑ a, ∑ b, (ρ (P a b) + Complex.I • ρ (Q a b)) * (ρ (P b a) + Complex.I • ρ (Q b a)) = -∑ i, ρ (X i) * ρ (X i) := by
  first | exact @GlobalTheory.DefiniteUnitaryCasimir.casimir_eq_neg_sum_sq | exact GlobalTheory.DefiniteUnitaryCasimir.casimir_eq_neg_sum_sq | (intros; apply GlobalTheory.DefiniteUnitaryCasimir.casimir_eq_neg_sum_sq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryRepOfActionOnTotalFamilyStatement
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryRepOfActionOnTotalFamily
noncomputable section

namespace GlobalTheory.TotalFamilyRep

variable {S H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem norm_linearCombination_eq (E F : S → H) (h : ∀ p q, inner ℂ (F p) (F q) = inner ℂ (E p) (E q))
    (x : S →₀ ℂ) : ‖Finsupp.linearCombination ℂ F x‖ = ‖Finsupp.linearCombination ℂ E x‖ := by
  have : inner ℂ (Finsupp.linearCombination ℂ F x) (Finsupp.linearCombination ℂ F x) =
      inner ℂ (Finsupp.linearCombination ℂ E x) (Finsupp.linearCombination ℂ E x) := by
    simp only [Finsupp.linearCombination_apply, Finsupp.sum, sum_inner, inner_sum, inner_smul_left,
      inner_smul_right, h]
  rw [@norm_eq_sqrt_re_inner ℂ, @norm_eq_sqrt_re_inner ℂ _ _ _ _ (Finsupp.linearCombination ℂ E x), this]

theorem exists_isometry [CompleteSpace H] (E F : S → H) (hE : Dense (Submodule.span ℂ (Set.range E) : Set H))
    (h : ∀ p q, inner ℂ (F p) (F q) = inner ℂ (E p) (E q)) :
    ∃ T : H →L[ℂ] H, (∀ x, ‖T x‖ = ‖x‖) ∧ ∀ p, T (E p) = F p := by
  have hd : DenseRange (Finsupp.linearCombination ℂ E) := by
    rw [← Finsupp.range_linearCombination] at hE
    exact hE
  have hT : ∀ x, (Finsupp.linearCombination ℂ F).extendOfNorm (Finsupp.linearCombination ℂ E)
      (Finsupp.linearCombination ℂ E x) = Finsupp.linearCombination ℂ F x :=
    LinearMap.extendOfNorm_eq hd ⟨1, fun x => by rw [one_mul, norm_linearCombination_eq E F h]⟩
  refine ⟨(Finsupp.linearCombination ℂ F).extendOfNorm (Finsupp.linearCombination ℂ E), fun x => ?_,
    fun p => ?_⟩
  · refine hd.induction_on (p := fun x => ‖(Finsupp.linearCombination ℂ F).extendOfNorm
      (Finsupp.linearCombination ℂ E) x‖ = ‖x‖) x (isClosed_eq (by fun_prop) (by fun_prop)) fun y => ?_
    rw [hT, norm_linearCombination_eq E F h]
  · simpa using hT (Finsupp.single p 1)

theorem exists_rep : ∀ (G S H : Type) [Group G] [TopologicalSpace G] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (act : G → S → S) (E : S → H), (∀ p, act 1 p = p) →
    (∀ g h p, act (g * h) p = act g (act h p)) → Dense (Submodule.span ℂ (Set.range E) : Set H) →
    (∀ g p q, inner ℂ (E (act g p)) (E (act g q)) = inner ℂ (E p) (E q)) →
    (∀ p q, Continuous fun g => inner ℂ (E q) (E (act g p))) →
    ∃ π : G →* (H →L[ℂ] H), (∀ g x, ‖π g x‖ = ‖x‖) ∧ (∀ x, Continuous fun g => π g x) ∧
      ∀ g p, π g (E p) = E (act g p) := by
  intro G S H _ _ _ _ _ act E h1 hmul hE hinv hcont
  choose T hT hTE using fun g => exists_isometry E (fun p => E (act g p)) hE (hinv g)
  have hp : ∀ p, Continuous fun g => T g (E p) := by
    intro p
    refine continuous_iff_continuousAt.2 fun g₀ => ?_
    rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
    have key : ∀ g, ‖T g (E p) - T g₀ (E p)‖ =
        √(‖E p‖ ^ 2 - 2 * RCLike.re (inner ℂ (E (act g₀ p)) (E (act g p))) + ‖E p‖ ^ 2) := by
      intro g
      rw [norm_sub_rev, ← hTE, ← hTE, ← Real.sqrt_sq (norm_nonneg (T g₀ (E p) - T g (E p))),
        @norm_sub_sq ℂ, hT, hT]
    have hc : Continuous fun g => ‖T g (E p) - T g₀ (E p)‖ := by
      simp only [key]
      have := hcont p (act g₀ p)
      fun_prop
    simpa using hc.tendsto g₀
  refine ⟨{ toFun := T, map_one' := ?_, map_mul' := fun g h => ?_ }, hT, ?_, hTE⟩
  · refine ContinuousLinearMap.ext_on hE ?_
    rintro _ ⟨p, rfl⟩
    simp [hTE, h1]
  · refine ContinuousLinearMap.ext_on hE ?_
    rintro _ ⟨p, rfl⟩
    simp [hTE, hmul]
  · refine GlobalTheory.FockSeq.continuous_of_dense T hT hE fun x hx => ?_
    induction hx using Submodule.span_induction with
    | mem x hx => obtain ⟨p, rfl⟩ := hx; exact hp p
    | zero => simpa using continuous_const
    | add x y _ _ hx hy => simp only [map_add (f := _)]; exact hx.add hy
    | smul a x _ hx => simp only [map_smul]; exact hx.const_smul a

end GlobalTheory.TotalFamilyRep
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.Mem.Osc GlobalTheory.OscGauss Matrix
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitaryRep_of_action_on_total_family : ∀ (G S H : Type) [Group G] [TopologicalSpace G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (act : G → S → S) (E : S → H), (∀ p, act 1 p = p) → (∀ g h p, act (g * h) p = act g (act h p)) → Dense (Submodule.span ℂ (Set.range E) : Set H) → (∀ g p q, inner ℂ (E (act g p)) (E (act g q)) = inner ℂ (E p) (E q)) → (∀ p q, Continuous fun g => inner ℂ (E q) (E (act g p))) → ∃ π : G →* (H →L[ℂ] H), (∀ g x, ‖π g x‖ = ‖x‖) ∧ (∀ x, Continuous fun g => π g x) ∧ ∀ g p, π g (E p) = E (act g p) := by
  first | exact @GlobalTheory.TotalFamilyRep.exists_rep | exact GlobalTheory.TotalFamilyRep.exists_rep | (intros; apply GlobalTheory.TotalFamilyRep.exists_rep <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueUnitaryTwoStepPairMeasure
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueUnitaryTwoStepPairMeasure
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeEx

section

variable {F E : Type} [Field F] [Field E] [Algebra F E]
  (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {M : ℕ}
  (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (B : Matrix (Fin (M + 1)) (Fin M) E)

theorem pairOf_mul_frame (J' : Matrix (Fin M) (Fin M) E) (y : Fin 1 → Fin (M + 1) → R ⊗[F] E)
    (g h : HA R σ J) (h' : HA R σ J') (hh : FrameRelR R σ J J' B h h')
    (y' : Fin 1 → Fin M → R ⊗[F] E) :
    pairOf R σ J B y (g * h) y' = pairOf R σ J B y g (h' • y') := by
  unfold pairOf
  congr 2
  have h1 : (h' • y') 0 = ((HA.mat R σ J' h' : GL (Fin M) (R ⊗[F] E)) :
      Matrix (Fin M) (Fin M) (R ⊗[F] E)).mulVec (y' 0) := rfl
  have h2 : ((HA.mat R σ J (g * h) : GL (Fin (M + 1)) (R ⊗[F] E)) : Matrix (Fin (M + 1)) (Fin (M + 1)) (R ⊗[F] E)) =
      ((HA.mat R σ J g : GL (Fin (M + 1)) (R ⊗[F] E)) : Matrix (Fin (M + 1)) (Fin (M + 1)) (R ⊗[F] E)) *
      ((HA.mat R σ J h : GL (Fin (M + 1)) (R ⊗[F] E)) : Matrix (Fin (M + 1)) (Fin (M + 1)) (R ⊗[F] E)) := rfl
  unfold FrameRelR at hh
  rw [h1, h2]
  simp only [Matrix.mulVec_mulVec]
  rw [Matrix.mul_assoc]
  exact congrArg (fun A => Matrix.mulVec (((HA.mat R σ J g : GL (Fin (M + 1)) (R ⊗[F] E)) :
    Matrix (Fin (M + 1)) (Fin (M + 1)) (R ⊗[F] E)) * A) (y' 0)) hh

variable [TopologicalSpace R] [FiniteDimensional F E] [IsTopologicalRing R]

theorem continuous_pairOf : Continuous fun p : (Fin 1 → Fin (M + 1) → R ⊗[F] E) × HA R σ J ×
    (Fin 1 → Fin M → R ⊗[F] E) => pairOf R σ J B p.1 p.2.1 p.2.2 := by
  refine continuous_pi fun a => ?_
  fin_cases a
  · exact (by fun_prop : Continuous fun p : (Fin 1 → Fin (M + 1) → R ⊗[F] E) × HA R σ J ×
      (Fin 1 → Fin M → R ⊗[F] E) => p.1 0)
  · exact ((continuous_mat R σ J).comp (continuous_fst.comp continuous_snd)).matrix_mulVec
      (continuous_const.matrix_mulVec
        ((continuous_apply 0).comp (continuous_snd.comp continuous_snd)))

end

theorem twoStep_existsUnique : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R], ∀ (M : ℕ) (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (x : Fin 1 → Fin (M + 1) → E) (a : F) (B : Matrix (Fin (M + 1)) (Fin M) E) (J' : Matrix (Fin M) (Fin M) E) (m : Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : Measure (Fin 1 → Fin M → R ⊗[F] E)), StepData σ J x a B J' → OnOrbit R σ J x m → IsFiniteMeasureOnCompacts m → IsFiniteMeasureOnCompacts m' → IsInvTup R σ J' m' → ∃! N, TwoStep R σ J x B m m' N := by
  intro F E _ _ _ _ _ σ hσ R _ _ _ _ _ _ _ _ _ M J x a B J' m m' hd horb hm hm' hinv
  obtain ⟨-, ⟨e, he, -⟩, -⟩ := GlobalTheory.T.unitary_stabilizer_anisotropic_vector_equiv_complement F E σ hσ R M J x a B J' hd
  obtain ⟨-, s₀, hs₀m, hs₀⟩ := GlobalTheory.T.measurableSet_orbit_exists_measurable_section (HA R σ J) (Fin 1 → Fin (M + 1) → R ⊗[F] E)
    (ratTup (F := F) R x)
  have hP : Measurable fun p : (Fin 1 → Fin (M + 1) → R ⊗[F] E) × HA R σ J ×
      (Fin 1 → Fin M → R ⊗[F] E) => pairOf R σ J B p.1 p.2.1 p.2.2 :=
    (continuous_pairOf R σ J B).measurable
  have hΦ : Measurable fun p : (Fin 1 → Fin (M + 1) → R ⊗[F] E) × (Fin 1 → Fin M → R ⊗[F] E) =>
      pairOf R σ J B p.1 (s₀ p.1) p.2 :=
    hP.comp (measurable_fst.prodMk ((hs₀m.comp measurable_fst).prodMk measurable_snd))
  have hex : TwoStep R σ J x B m m' ((m.prod m').map fun p => pairOf R σ J B p.1 (s₀ p.1) p.2) := by
    intro f hf s hs
    rw [lintegral_map hf hΦ, lintegral_prod (fun p : (Fin 1 → Fin (M + 1) → R ⊗[F] E) ×
      (Fin 1 → Fin M → R ⊗[F] E) => f (pairOf R σ J B p.1 (s₀ p.1) p.2)) (hf.comp hΦ).aemeasurable]
    refine lintegral_congr_ae ?_
    have hae : ∀ᵐ y ∂m, ∃ g : HA R σ J, g • ratTup (F := F) R x = y := horb
    filter_upwards [hae] with y hy
    have hst : (s₀ y)⁻¹ * s y ∈ Hstab R σ J x := by
      change ((s₀ y)⁻¹ * s y) • ratTup (F := F) R x = ratTup (F := F) R x
      rw [mul_smul, hs y hy, inv_smul_eq_iff, hs₀ y hy]
    have hfac : s y = s₀ y * ((s₀ y)⁻¹ * s y) := by group
    have hk : Measurable fun y' => f (pairOf R σ J B y (s₀ y) y') :=
      (hf.comp hΦ).comp measurable_prodMk_left
    have hsm : Measurable fun X : Fin 1 → Fin M → R ⊗[F] E => e ⟨_, hst⟩ • X :=
      (continuous_const_smul _).measurable
    calc ∫⁻ y', f (pairOf R σ J B y (s₀ y) y') ∂m'
        = ∫⁻ y', f (pairOf R σ J B y (s₀ y) y') ∂(m'.map fun X => e ⟨_, hst⟩ • X) := by
          rw [hinv]
      _ = ∫⁻ y', f (pairOf R σ J B y (s₀ y) (e ⟨_, hst⟩ • y')) ∂m' := lintegral_map hk hsm
      _ = ∫⁻ y', f (pairOf R σ J B y (s y) y') ∂m' := by
          refine lintegral_congr fun y' => ?_
          rw [← pairOf_mul_frame R σ J B J' y (s₀ y) _ _ (he ⟨_, hst⟩), ← hfac]
  refine ⟨_, hex, fun N hN => ?_⟩
  ext A hA
  rw [← lintegral_indicator_one hA, ← lintegral_indicator_one hA,
    hN _ (measurable_one.indicator hA) s₀ hs₀, hex _ (measurable_one.indicator hA) s₀ hs₀]

end GlobalTheory.GaugeEx
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueUnitaryTwoStepPairMeasureStatement
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_unitaryTwoStepPairMeasure : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R], ∀ (M : ℕ) (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (x : Fin 1 → Fin (M + 1) → E) (a : F) (B : Matrix (Fin (M + 1)) (Fin M) E) (J' : Matrix (Fin M) (Fin M) E) (m : Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : Measure (Fin 1 → Fin M → R ⊗[F] E)), StepData σ J x a B J' → OnOrbit R σ J x m → IsFiniteMeasureOnCompacts m → IsFiniteMeasureOnCompacts m' → IsInvTup R σ J' m' → ∃! N, TwoStep R σ J x B m m' N := by
  first | exact @GlobalTheory.GaugeEx.twoStep_existsUnique | exact GlobalTheory.GaugeEx.twoStep_existsUnique | (intros; apply GlobalTheory.GaugeEx.twoStep_existsUnique <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteHermitianEqPmGramUnitaryCompact
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteHermitianEqPmGramUnitaryCompact
open Matrix

namespace GlobalTheory.DefiniteFrame

theorem exists_frame {n p q : ℕ} {J : Matrix (Fin n) (Fin n) ℂ} (h : Formalism.UG.HasSignature J p q) :
    ∃ (e : Fin n ≃ Fin p ⊕ Fin q) (B : Matrix (Fin n) (Fin n) ℂ), IsUnit B.det ∧
      J = Bᴴ * (Formalism.UG.Jpq p q).submatrix e e * B := by
  obtain ⟨e, P, hP⟩ := h
  have hP' : P.valᴴ * (reindex e e J) * P.val = Formalism.UG.Jpq p q := hP
  refine ⟨e, (P⁻¹).val.submatrix e e, ?_, ?_⟩
  · rw [det_submatrix_equiv_self]
    exact (Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit _)
  · have h1 := Units.mul_inv P
    have h2 : (P⁻¹).valᴴ * P.valᴴ = 1 := by
      rw [← conjTranspose_mul, h1, conjTranspose_one]
    rw [conjTranspose_submatrix, submatrix_mul_equiv, submatrix_mul_equiv, ← hP']
    have h3 : (P⁻¹).valᴴ *
        (P.valᴴ * (reindex e e J) * P.val) *
        (P⁻¹).val = reindex e e J := by
      calc _ = ((P⁻¹).valᴴ * P.valᴴ) * (reindex e e J) *
          (P.val * (P⁻¹).val) := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]
    rw [h3]
    ext i j
    simp

theorem isCompact_UH_gram {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ) (hB : IsUnit B.det) :
    IsCompact (Formalism.QuantumDeterminants.UH (Bᴴ * B)) := by
  have hc : Continuous fun u : Matrix (Fin n) (Fin n) ℂ => B⁻¹ * u * B :=
    (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  have h1 : B * B⁻¹ = 1 := mul_nonsing_inv B hB
  have h1' : B⁻¹ * B = 1 := nonsing_inv_mul B hB
  have h2 : (B⁻¹)ᴴ * Bᴴ = 1 := by rw [← conjTranspose_mul, h1, conjTranspose_one]
  have h2' : Bᴴ * (B⁻¹)ᴴ = 1 := by rw [← conjTranspose_mul, h1', conjTranspose_one]
  convert (GlobalTheory.isCompact_unitaryGroup (Fin n) ℂ).image hc using 1
  ext g
  simp only [Formalism.QuantumDeterminants.UH, Set.mem_ofPred_eq, Set.mem_image, SetLike.mem_coe,
    Matrix.mem_unitaryGroup_iff', star_eq_conjTranspose]
  constructor
  · intro hg
    refine ⟨B * g * B⁻¹, ?_, ?_⟩
    · calc (B * g * B⁻¹)ᴴ * (B * g * B⁻¹) = (B⁻¹)ᴴ * (gᴴ * (Bᴴ * B) * g) * B⁻¹ := by
            simp only [conjTranspose_mul, Matrix.mul_assoc]
        _ = ((B⁻¹)ᴴ * Bᴴ) * (B * B⁻¹) := by rw [hg]; simp only [Matrix.mul_assoc]
        _ = 1 := by rw [h1, h2, Matrix.one_mul]
    · calc B⁻¹ * (B * g * B⁻¹) * B = (B⁻¹ * B) * g * (B⁻¹ * B) := by
            simp only [Matrix.mul_assoc]
        _ = g := by rw [h1', Matrix.one_mul, Matrix.mul_one]
  · rintro ⟨u, hu, rfl⟩
    calc (B⁻¹ * u * B)ᴴ * (Bᴴ * B) * (B⁻¹ * u * B)
        = Bᴴ * (uᴴ * ((B⁻¹)ᴴ * Bᴴ) * (B * B⁻¹) * u) * B := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = Bᴴ * B := by rw [h1, h2, Matrix.mul_one, Matrix.mul_one, hu, Matrix.mul_one]

theorem UH_neg {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) : Formalism.QuantumDeterminants.UH (-H) = Formalism.QuantumDeterminants.UH H := by
  ext g
  simp [Formalism.QuantumDeterminants.UH]

theorem definite_frame (n p q : ℕ) (J : Matrix (Fin n) (Fin n) ℂ)
    (h : Formalism.UG.HasSignature J p q) (hpq : p = 0 ∨ q = 0) :
    (∃ B : Matrix (Fin n) (Fin n) ℂ, IsUnit B.det ∧ (J = Bᴴ * B ∨ J = -(Bᴴ * B))) ∧
      IsCompact (Formalism.QuantumDeterminants.UH J) := by
  obtain ⟨e, B, hB, hJ⟩ := exists_frame h
  rcases hpq with rfl | rfl
  · have h1 : Formalism.UG.Jpq 0 q = -1 := by
      ext i j
      rcases i with i | i
      · exact i.elim0
      rcases j with j | j
      · exact j.elim0
      simp [Formalism.UG.Jpq, Matrix.one_apply]
    have h2 : J = -(Bᴴ * B) := by
      rw [hJ, h1, submatrix_neg]
      simp
    refine ⟨⟨B, hB, Or.inr h2⟩, ?_⟩
    rw [h2, UH_neg]
    exact isCompact_UH_gram B hB
  · have h1 : Formalism.UG.Jpq p 0 = 1 := by
      ext i j
      rcases i with i | i
      swap
      · exact i.elim0
      rcases j with j | j
      swap
      · exact j.elim0
      simp [Formalism.UG.Jpq, Matrix.one_apply]
    have h2 : J = Bᴴ * B := by
      rw [hJ, h1]
      simp
    refine ⟨⟨B, hB, Or.inl h2⟩, ?_⟩
    rw [h2]
    exact isCompact_UH_gram B hB

end GlobalTheory.DefiniteFrame
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteHermitianEqPmGramUnitaryCompactStatement
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definite_hermitian_eq_pm_gram_unitary_compact : ∀ (n p q : ℕ) (J : Matrix (Fin n) (Fin n) ℂ), Formalism.UG.HasSignature J p q → (p = 0 ∨ q = 0) → (∃ B : Matrix (Fin n) (Fin n) ℂ, IsUnit B.det ∧ (J = Bᴴ * B ∨ J = -(Bᴴ * B))) ∧ IsCompact (Formalism.QuantumDeterminants.UH J) := by
  first | exact @GlobalTheory.DefiniteFrame.definite_frame | exact GlobalTheory.DefiniteFrame.definite_frame | (intros; apply GlobalTheory.DefiniteFrame.definite_frame <;> assumption)
end
end
