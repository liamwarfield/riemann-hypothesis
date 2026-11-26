module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzRestFunction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorLatticeInertPlaceSelfDual

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedIntegersStableSubgroupEqDoubleOrthogonal
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedIntegersStableSubgroupEqDoubleOrthogonal
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
open scoped GlobalTheory.VacAny

namespace GlobalTheory.LatticeDual

theorem exists_integral_form_separating {R K : Type} [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R] [Field K] [Algebra R K] [IsFractionRing R K] {κ : Type} [Fintype κ]
    (M : Submodule R (κ → K)) (hM : M.FG) (z : K) (hz : z ∉ (algebraMap R K).range)
    (t : κ → K) (ht : t ∉ M) :
    ∃ y : κ → K, (∀ s ∈ M, s ⬝ᵥ y ∈ (algebraMap R K).range) ∧ t ⬝ᵥ y ∉ (algebraMap R K).range := by
  classical
  haveI : Module.Finite R M := Module.Finite.iff_fg.mpr hM
  haveI : Module.Free R M := Module.free_of_finite_type_torsion_free'
  let b := Module.Free.chooseBasis R M
  let ι := Module.Free.ChooseBasisIndex R M
  let a : ι → (κ → K) := fun i => (b i : κ → K)
  have hliR : LinearIndependent R a := b.linearIndependent.map' M.subtype (Submodule.ker_subtype M)
  have hli : LinearIndependent K a := (LinearIndependent.iff_fractionRing R K).mp hliR
  let B := Module.Basis.sumExtend hli
  have hfin : Finite (ι ⊕ Module.Basis.sumExtendIndex hli) := Module.Finite.finite_basis B
  have : Finite (Module.Basis.sumExtendIndex hli) :=
    Finite.of_injective (Sum.inr : _ → ι ⊕ _) Sum.inr_injective
  have : Fintype (Module.Basis.sumExtendIndex hli) := Fintype.ofFinite _
  have hB : ∀ i, B (Sum.inl i) = a i := by
    intro i
    simp only [B, Module.Basis.sumExtend, Module.Basis.reindex_apply, Module.Basis.coe_extend,
      Equiv.symm_symm, Equiv.trans_apply, Equiv.sumCongr_apply]
    rfl

  have key : ∀ f : (κ → K) →ₗ[K] K, (∀ i, f (a i) ∈ (algebraMap R K).range) →
      ∀ s ∈ M, f s ∈ (algebraMap R K).range := by
    intro f hf s hs
    have hs' : s = ∑ i, b.repr ⟨s, hs⟩ i • a i := by
      have := congrArg Subtype.val (b.sum_repr ⟨s, hs⟩)
      simp only [Submodule.coe_sum, Submodule.coe_smul] at this
      exact this.symm
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hs', map_sum]
    refine Subring.sum_mem _ fun i _ => ?_
    rw [f.map_smul_of_tower]
    obtain ⟨r, hr⟩ := hf i
    exact ⟨b.repr ⟨s, hs⟩ i * r, by rw [map_mul, hr, Algebra.smul_def]⟩

  have dot : ∀ f : (κ → K) →ₗ[K] K, ∃ y : κ → K, ∀ x, x ⬝ᵥ y = f x := by
    intro f
    refine ⟨fun k => f (fun j => if k = j then 1 else 0), fun x => ?_⟩
    rw [LinearMap.pi_apply_eq_sum_univ f x]
    simp [dotProduct, smul_eq_mul]
  suffices h : ∃ f : (κ → K) →ₗ[K] K, (∀ i, f (a i) ∈ (algebraMap R K).range) ∧
      f t ∉ (algebraMap R K).range by
    obtain ⟨f, hf, hft⟩ := h
    obtain ⟨y, hy⟩ := dot f
    exact ⟨y, fun s hs => (hy s).symm ▸ key f hf s hs, (hy t).symm ▸ hft⟩
  by_cases h1 : ∃ i, B.repr t (Sum.inl i) ∉ (algebraMap R K).range
  · obtain ⟨i, hi⟩ := h1
    refine ⟨B.coord (Sum.inl i), fun i' => ?_, by simpa using hi⟩
    rw [← hB, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
    split_ifs
    · exact ⟨1, map_one _⟩
    · exact ⟨0, map_zero _⟩
  by_cases h2 : ∃ j, B.repr t (Sum.inr j) ≠ 0
  · obtain ⟨j, hj⟩ := h2
    refine ⟨(z / B.repr t (Sum.inr j)) • B.coord (Sum.inr j), fun i => ?_, ?_⟩
    · rw [LinearMap.smul_apply, ← hB, Module.Basis.coord_apply, Module.Basis.repr_self,
        Finsupp.single_apply, if_neg Sum.inl_ne_inr, smul_zero]
      exact ⟨0, map_zero _⟩
    · rw [LinearMap.smul_apply, Module.Basis.coord_apply, smul_eq_mul, div_mul_cancel₀ _ hj]
      exact hz
  push_neg at h1 h2
  choose c hc using h1
  exfalso
  apply ht
  have htc : t = ∑ i, c i • a i := by
    conv_lhs => rw [← B.sum_repr t]
    rw [Fintype.sum_sum_type]
    simp [h2, hB, ← hc, algebraMap_smul]
  rw [htc]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (b i).2

end GlobalTheory.LatticeDual

namespace GlobalTheory.LatticeDual

theorem mem_of_mem_doubleOrth : ∀ (F : Type) [Field F] [NumberField F] (v : Pl (F := F)) (κ : Type) [Fintype κ] (ψ₀ : AddChar (Fv F v) ℂ),
    (∀ x : Fv F v, (∀ y ∈ HeightOneSpectrum.adicCompletionIntegers F v, ψ₀ (x * y) = 1) ↔ x ∈ HeightOneSpectrum.adicCompletionIntegers F v) →
    ∀ A : AddSubgroup (κ → Fv F v), (∀ c ∈ HeightOneSpectrum.adicCompletionIntegers F v, ∀ t ∈ A, c • t ∈ A) →
    (∃ c : Fv F v, c ≠ 0 ∧ ∀ t ∈ A, ∀ k, c * t k ∈ HeightOneSpectrum.adicCompletionIntegers F v) →
    ∀ t : κ → Fv F v, (∀ y : κ → Fv F v, (∀ s ∈ A, ψ₀ (s ⬝ᵥ y) = 1) → ψ₀ (t ⬝ᵥ y) = 1) → t ∈ A := by
  intro F _ _ v κ _ ψ₀ hψ A hA hbd t ht
  classical
  let O := HeightOneSpectrum.adicCompletionIntegers F v
  have hrange : ∀ x : Fv F v, x ∈ (algebraMap O (Fv F v)).range ↔ x ∈ O :=
    fun x => ⟨fun ⟨r, hr⟩ => hr ▸ r.2, fun h => ⟨⟨x, h⟩, rfl⟩⟩
  have hψO : ∀ x ∈ O, ψ₀ x = 1 := fun x hx => by
    simpa using (hψ 1).mpr (one_mem _) x hx

  let M : Submodule O (κ → Fv F v) :=
    { carrier := A
      add_mem' := fun h h' => A.add_mem h h'
      zero_mem' := A.zero_mem
      smul_mem' := fun c x hx => hA _ c.2 x hx }
  obtain ⟨c, hc0, hc⟩ := hbd

  let N : Submodule O (κ → Fv F v) :=
    Submodule.span O (Set.range fun k : κ => c⁻¹ • (Pi.single k 1 : κ → Fv F v))
  have hN : N.FG := Submodule.fg_span (Set.finite_range _)
  have hMN : M ≤ N := by
    intro s hs
    have hs' : s = ∑ k, (⟨c * s k, hc s hs k⟩ : O) • (c⁻¹ • (Pi.single k 1 : κ → Fv F v)) := by
      funext j
      simp [Finset.sum_apply, Pi.single_apply]
      show s j = c * s j * c⁻¹
      rw [mul_comm c, mul_inv_cancel_right₀ hc0]
    rw [hs']
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  have hMfg : M.FG := by
    haveI := isNoetherian_of_fg_of_noetherian N hN
    have h1 : (M.comap N.subtype).FG := IsNoetherian.noetherian _
    have h2 := h1.map N.subtype
    rwa [Submodule.map_comap_subtype, inf_eq_right.mpr hMN] at h2

  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hϖ0 : (ϖ : Fv F v) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  have hz : (ϖ : Fv F v)⁻¹ ∉ (algebraMap O (Fv F v)).range := by
    rw [hrange]
    intro h
    apply hϖ.not_isUnit
    refine isUnit_iff_exists_inv.mpr ⟨⟨_, h⟩, Subtype.ext ?_⟩
    simp [hϖ0]
  by_contra htA
  obtain ⟨y', hyA, hyt⟩ := exists_integral_form_separating M hMfg _ hz t htA
  simp only [hrange] at hyA hyt
  obtain ⟨b, hb, hbψ⟩ : ∃ b ∈ O, ψ₀ ((t ⬝ᵥ y') * b) ≠ 1 := by
    by_contra h
    push_neg at h
    exact hyt ((hψ _).mp h)
  apply hbψ
  have := ht (b • y') (fun s hs => by
    rw [dotProduct_smul, smul_eq_mul, mul_comm]
    exact hψO _ (mul_mem (hyA s hs) hb))
  rwa [dotProduct_smul, smul_eq_mul, mul_comm] at this

end GlobalTheory.LatticeDual
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedIntegersStableSubgroupEqDoubleOrthogonalStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
open scoped GlobalTheory.VacAny
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.boundedIntegersStableSubgroup_eq_doubleOrthogonal : ∀ (F : Type) [Field F] [NumberField F] (v : Pl (F := F)) (κ : Type) [Fintype κ] (ψ₀ : AddChar (Fv F v) ℂ),
    (∀ x : Fv F v, (∀ y ∈ HeightOneSpectrum.adicCompletionIntegers F v, ψ₀ (x * y) = 1) ↔ x ∈ HeightOneSpectrum.adicCompletionIntegers F v) →
    ∀ A : AddSubgroup (κ → Fv F v), (∀ c ∈ HeightOneSpectrum.adicCompletionIntegers F v, ∀ t ∈ A, c • t ∈ A) →
    (∃ c : Fv F v, c ≠ 0 ∧ ∀ t ∈ A, ∀ k, c * t k ∈ HeightOneSpectrum.adicCompletionIntegers F v) →
    ∀ t : κ → Fv F v, (∀ y : κ → Fv F v, (∀ s ∈ A, ψ₀ (s ⬝ᵥ y) = 1) → ψ₀ (t ⬝ᵥ y) = 1) → t ∈ A := by
  first | exact @GlobalTheory.LatticeDual.mem_of_mem_doubleOrth | exact GlobalTheory.LatticeDual.mem_of_mem_doubleOrth | (intros; apply GlobalTheory.LatticeDual.mem_of_mem_doubleOrth <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeLocalDarbouxCoordinatesBounded
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeLocalDarbouxCoordinatesBounded
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
open scoped GlobalTheory.VacAny

set_option maxHeartbeats 1000000

namespace GlobalTheory.LatVacBdd

theorem exists_ne_zero_mul_mem {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (S : Finset (v.adicCompletion F)) :
    ∃ c : v.adicCompletion F, c ≠ 0 ∧ ∀ a ∈ S, c * a ∈ v.adicCompletionIntegers F := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, one_ne_zero, by simp⟩
  | insert b S hb ih =>
    obtain ⟨c, hc0, hc⟩ := ih
    by_cases hcb : c * b ∈ v.adicCompletionIntegers F
    · refine ⟨c, hc0, ?_⟩
      intro a ha
      rcases Finset.mem_insert.1 ha with rfl | ha
      · exact hcb
      · exact hc a ha
    · have hinv : (c * b)⁻¹ ∈ v.adicCompletionIntegers F :=
        ((v.adicCompletionIntegers F).mem_or_inv_mem (c * b)).resolve_left hcb
      have hcb0 : c * b ≠ 0 := fun h => hcb (h ▸ zero_mem _)
      refine ⟨c * (c * b)⁻¹, mul_ne_zero hc0 (inv_ne_zero hcb0), ?_⟩
      intro a ha
      rcases Finset.mem_insert.1 ha with rfl | ha
      · rw [mul_assoc, mul_comm _ a, ← mul_assoc, mul_inv_cancel₀ hcb0]; exact one_mem _
      · rw [mul_comm c, mul_assoc]; exact mul_mem hinv (hc a ha)

end GlobalTheory.LatVacBdd

theorem GlobalTheory.LatVacBdd.locCo_bounded : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ v : Pl (F := F), ∃ c : Fv F v, c ≠ 0 ∧ ∀ γ ∈ latAtV G.V G.W v, ∀ k,
      c * (GlobalTheory.LatVac.locCo G.M.co v γ).1 k ∈ HeightOneSpectrum.adicCompletionIntegers F v ∧
      c * (GlobalTheory.LatVac.locCo G.M.co v γ).2 k ∈ HeightOneSpectrum.adicCompletionIntegers F v := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v
  classical
  choose yf zf hyz using hT.geo.hM.rat
  obtain ⟨sX, hsX⟩ := hT.geo.hV.lat.fg.restrictScalars (R := ℤ)
  obtain ⟨sY, hsY⟩ := hT.geo.hW.lat.fg.restrictScalars (R := ℤ)
  let f : (Fin a → E) →ₗ[ℤ] (Fin (a + a') → E) →ₗ[ℤ] Matrix (Fin a) (Fin (a + a')) E :=
    LinearMap.mk₂ ℤ (fun x y => Matrix.vecMulVec x y)
      (fun x x' y => by ext i j; simp [Matrix.vecMulVec_apply, add_mul])
      (fun c x y => by ext i j; simp [Matrix.vecMulVec_apply, mul_assoc])
      (fun x y y' => by ext i j; simp [Matrix.vecMulVec_apply, mul_add])
      (fun c x y => by ext i j; simp [Matrix.vecMulVec_apply, mul_left_comm])
  let T₀ : Finset (Matrix (Fin a) (Fin (a + a')) E) := Finset.image₂ (fun x y => f x y) sX sY
  have hmem : ∀ x ∈ G.V.L, ∀ y ∈ G.W.L, Matrix.vecMulVec x y ∈ Submodule.span ℤ (T₀ : Set _) := by
    intro x hx y hy
    have hx' : x ∈ Submodule.span ℤ (sX : Set (Fin a → E)) := by
      rw [hsX]; exact hx
    have hy' : y ∈ Submodule.span ℤ (sY : Set (Fin (a + a') → E)) := by
      rw [hsY]; exact hy
    have := Submodule.apply_mem_map₂ f hx' hy'
    rw [Submodule.map₂_span_span] at this
    rw [Finset.coe_image₂]; exact this
  have hgen : latAtV G.V G.W v ≤ AddSubgroup.closure {z | ∃ b : AF F,
      At (evFin F v) b ∧ evFin F v b ∈ v.adicCompletionIntegers F ∧ ∃ t ∈ T₀, z = b • incM F t} := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro z ⟨b, hb, hbv, x, hx, y, hy, rfl⟩
    let g : Matrix (Fin a) (Fin (a + a')) E →+ Matrix (Fin a) (Fin (a + a')) (AE F E) :=
      (DistribSMul.toAddMonoidHom _ b).comp
        (AddMonoidHom.mapMatrix (inclR (F := F) (E := E) (AF F)).toAddMonoidHom)
    have h1 : Matrix.vecMulVec x y ∈ AddSubgroup.closure (T₀ : Set _) := by
      rw [← Submodule.span_int_eq_addSubgroupClosure]; exact hmem x hx y hy
    have h2 : g (Matrix.vecMulVec x y) ∈ (AddSubgroup.closure (T₀ : Set _)).map g :=
      AddSubgroup.mem_map_of_mem g h1
    rw [AddMonoidHom.map_closure] at h2
    refine AddSubgroup.closure_mono ?_ h2
    rintro _ ⟨t, ht, rfl⟩
    exact ⟨b, hb, hbv, t, ht, rfl⟩
  let S : Finset (Fv F v) :=
    (T₀ ×ˢ (Finset.univ : Finset (Fin a × Fin (a + a')))).image (fun p => algebraMap F (Fv F v) (yf p.1 p.2)) ∪
    (T₀ ×ˢ (Finset.univ : Finset (Fin a × Fin (a + a')))).image (fun p => algebraMap F (Fv F v) (zf p.1 p.2))
  obtain ⟨c, hc0, hc⟩ := GlobalTheory.LatVacBdd.exists_ne_zero_mul_mem v S
  have hcy : ∀ t ∈ T₀, ∀ k, c * algebraMap F (Fv F v) (yf t k) ∈ v.adicCompletionIntegers F := fun t ht k =>
    hc _ (Finset.mem_union_left _ (Finset.mem_image.2 ⟨(t, k), Finset.mem_product.2 ⟨ht, Finset.mem_univ _⟩, rfl⟩))
  have hcz : ∀ t ∈ T₀, ∀ k, c * algebraMap F (Fv F v) (zf t k) ∈ v.adicCompletionIntegers F := fun t ht k =>
    hc _ (Finset.mem_union_right _ (Finset.mem_image.2 ⟨(t, k), Finset.mem_product.2 ⟨ht, Finset.mem_univ _⟩, rfl⟩))
  have hev : ∀ y : F, evFin F v (algebraMap F (AF F) y) = algebraMap F (Fv F v) y := fun y => AlgHom.commutes _ _
  refine ⟨c, hc0, fun γ hγ => ?_⟩
  clear_value T₀
  revert hγ
  intro hγ
  have hγ' := hgen hγ
  clear hγ
  induction hγ' using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨b, -, hbv, t, ht, rfl⟩ := hz
    intro k
    simp only [GlobalTheory.LatVac.locCo, AddMonoidHom.coe_mk, ZeroHom.coe_mk, LinearEquiv.map_smul, hyz,
      Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, map_mul, hev]
    exact ⟨by rw [mul_left_comm]; exact mul_mem hbv (hcy t ht k),
      by rw [mul_left_comm]; exact mul_mem hbv (hcz t ht k)⟩
  | zero => intro k; simp
  | add x y _ _ hx hy =>
    intro k
    rw [map_add (f := _)]
    exact ⟨by rw [Prod.fst_add, Pi.add_apply, mul_add]; exact add_mem (hx k).1 (hy k).1,
      by rw [Prod.snd_add, Pi.add_apply, mul_add]; exact add_mem (hx k).2 (hy k).2⟩
  | neg x _ hx =>
    intro k
    rw [map_neg]
    exact ⟨by rw [Prod.fst_neg, Pi.neg_apply, mul_neg]; exact neg_mem (hx k).1,
      by rw [Prod.snd_neg, Pi.neg_apply, mul_neg]; exact neg_mem (hx k).2⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeLocalDarbouxCoordinatesBoundedStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
open scoped GlobalTheory.VacAny
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeLocalDarbouxCoordinates_bounded : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ v : Pl (F := F), ∃ c : Fv F v, c ≠ 0 ∧ ∀ γ ∈ latAtV G.V G.W v, ∀ k,
      c * (GlobalTheory.LatVac.locCo G.M.co v γ).1 k ∈ HeightOneSpectrum.adicCompletionIntegers F v ∧
      c * (GlobalTheory.LatVac.locCo G.M.co v γ).2 k ∈ HeightOneSpectrum.adicCompletionIntegers F v := by
  first | exact @GlobalTheory.LatVacBdd.locCo_bounded | exact GlobalTheory.LatVacBdd.locCo_bounded | (intros; apply GlobalTheory.LatVacBdd.locCo_bounded <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceLatticeVacuumFixedAndUnique
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.InertLatVac

theorem two_inv_mem {F : Type} [Field F] [NumberField F] (v : Pl (F := F)) (h : (2 : 𝓞 F) ∉ v.asIdeal) :
    (⅟(2 : Fv F v)) ∈ HeightOneSpectrum.adicCompletionIntegers F v := by
  have hv : Valued.v (2 : Fv F v) = 1 := by
    have e : (2 : Fv F v) = algebraMap F (v.adicCompletion F) (((2 : 𝓞 F) : F)) := by
      rw [show (((2 : 𝓞 F) : F)) = 2 from map_ofNat (algebraMap (𝓞 F) F) 2, map_ofNat]
    have e2 : algebraMap F (v.adicCompletion F) (((2 : 𝓞 F) : F)) =
        ((algebraMap (𝓞 F) F (2 : 𝓞 F) : F) : v.adicCompletion F) := rfl
    rw [e, e2, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_eq_one_iff_notMem]
    exact h
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, invOf_eq_inv, map_inv₀, hv, inv_one]

theorem hTens_smul_left {R E : Type} [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E) {α β : Type}
    [Fintype α] [Fintype β] (JA : Matrix α α E) (JB : Matrix β β E) (e : E) (x y : Matrix α β E) :
    GlobalTheory.WeilM.hTens c JA JB (e • x) y = e * GlobalTheory.WeilM.hTens c JA JB x y := by
  simp only [GlobalTheory.WeilM.hTens, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

theorem symp_smul_left {R E : Type} [CommRing R] [CommRing E] [Algebra R E] [Module.Free R E] [Module.Finite R E]
    (c : E →ₐ[R] E) {α β : Type} [Fintype α] [Fintype β] (ξ : E) (JA : Matrix α α E) (JB : Matrix β β E) (r : R)
    (x y : Matrix α β E) :
    GlobalTheory.WeilM.symp c ξ JA JB (r • x) y = r * GlobalTheory.WeilM.symp c ξ JA JB x y := by
  have : r • x = (algebraMap R E r) • x := (algebraMap_smul E r x).symm
  rw [this]
  simp only [GlobalTheory.WeilM.symp, hTens_smul_left]
  rw [mul_left_comm, ← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul]

theorem latAtV_smul_int {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n d : ℕ} (X : Spc F E n)
    (Y : Spc F E d) (v : Pl (F := F)) (e : 𝓞 E) :
    ∀ γ ∈ latAtV X Y v, (inclR (F := F) (AF F) (e : E)) • γ ∈ latAtV X Y v := by
  intro γ hγ
  induction hγ using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨r, hr, hr', x, hx, y, hy, rfl⟩ := hz
    apply AddSubgroup.subset_closure
    refine ⟨r, hr, hr', e • x, X.L.smul_mem e hx, y, hy, ?_⟩
    ext i j
    simp only [incM, Matrix.smul_apply, Matrix.map_apply, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul,
      Algebra.smul_def, map_mul, RingOfIntegers.coe_eq_algebraMap]
    ring
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

theorem phase_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w →
    ∀ θ : 𝓞 E, (θ : E) + σ (θ : E) = 1 → ∀ γ ∈ latAtV G.V G.W v,
      B.ψ (⅟2 * symp (cA σ) ((inclR (AF F)) (θ : E)) (incM F G.V.J) (incM F G.W.J) γ γ) = 1 := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v w hin θ hθ γ hγ
  have hst := GlobalTheory.LatVac.latAtV_at_stable G.V G.W v
  have h2 := two_inv_mem v (hT.base.inert v w hin).1
  have hγ' : GlobalTheory.LatVac.liftV v (⅟2) • γ ∈ latAtV G.V G.W v := hst.2 _ h2 γ hγ
  have e1 : (⅟(2 : AF F)) • γ = GlobalTheory.LatVac.liftV v (⅟2) • γ := by
    have hev : evFin F v (⅟(2 : AF F)) = ⅟(2 : Fv F v) := by
      refine (invOf_eq_right_inv ?_).symm
      have h : evFin F v (2 * ⅟(2 : AF F)) = 1 := by rw [mul_invOf_self, map_one]
      rwa [map_mul, map_ofNat] at h
    have h0 : ((⅟(2 : AF F)) - GlobalTheory.LatVac.liftV v (⅟2)) • γ = 0 :=
      hst.1 γ hγ _ (by rw [map_sub, GlobalTheory.LatVac.evFin_liftV, hev, sub_self])
    rwa [sub_smul, sub_eq_zero] at h0
  have hz : -((inclR (F := F) (AF F) (θ : E)) • GlobalTheory.LatVac.liftV v (⅟2) • γ) ∈ latAtV G.V G.W v :=
    neg_mem (latAtV_smul_int G.V G.W v θ _ hγ')
  have key := (GlobalTheory.InertSelfDual.latAtV_selfDual F E σ B a a' G X om om' hT v w hin _ (hst.1 _ hz)).1 hz γ hγ
  rw [← symp_smul_left, e1]
  refine Eq.trans ?_ key
  congr 1
  rw [← neg_smul, GlobalTheory.WeilM.symp, GlobalTheory.WeilM.symp, hTens_smul_left]
  ring_nf

theorem acts_unique {F : Type} [Field F] [NumberField F] (v : Pl (F := F)) {κ : Type} [Fintype κ]
    (T : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ) {φ φ₁ φ₂ : (κ → Fv F v) → ℂ}
    (hφ : φ ∈ SB (κ → Fv F v)) (h₁ : Acts (evFin F v) T φ φ₁) (h₂ : Acts (evFin F v) T φ φ₂) : φ₁ = φ₂ := by
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.RestWitness.exists_rest κ v
  have e := (h₁ R (hR φ hφ)).symm.trans (h₂ R (hR φ hφ))
  funext y
  have hx := congrFun e (fun i => GlobalTheory.LatVac.liftV v (y i))
  have hat : At (evFin F v) (fun i => GlobalTheory.LatVac.liftV v (y i)) :=
    fun u hu => funext fun i => GlobalTheory.LatVac.at_liftV v (y i) u hu
  have hRx : R (fun i => GlobalTheory.LatVac.liftV v (y i)) = R 0 := by
    have := (hR φ hφ).1 0 _ hat
    simpa using this
  simp only [tens, GlobalTheory.LatVac.evFin_liftV, hRx] at hx
  exact mul_right_cancel₀ hR0 hx

theorem fixed_eq_smul {K : Type} [Field K] {h2 : Invertible (2 : K)} {κ : Type} [Fintype κ] (ψ₀ : AddChar K ℂ)
    (Λ : AddSubgroup ((κ → K) × (κ → K)))
    (hdual : ∀ w, w ∈ Λ ↔ ∀ l ∈ Λ, ψ₀ (w.1 ⬝ᵥ l.2 - l.1 ⬝ᵥ w.2) = 1)
    (hrefl : ∀ t : κ → K, (∀ y : κ → K, (∀ l ∈ Λ, ψ₀ (l.1 ⬝ᵥ y) = 1) → ψ₀ (t ⬝ᵥ y) = 1) → ∃ l ∈ Λ, l.1 = t)
    {f g : (κ → K) → ℂ} (hg : g ≠ 0)
    (hf : ∀ l ∈ Λ, @GlobalTheory.WeilM.schr K _ h2 ψ₀ κ _ l f = f) (hgf : ∀ l ∈ Λ, @GlobalTheory.WeilM.schr K _ h2 ψ₀ κ _ l g = g) :
    ∃ c : ℂ, f = c • g := by
  have hne : ∀ x : K, ψ₀ x ≠ 0 := fun x h => by
    have := AddChar.map_add_eq_mul ψ₀ x (-x)
    rw [add_neg_cancel, AddChar.map_zero_eq_one, h, zero_mul] at this
    exact one_ne_zero this

  have key1 : ∀ h : (κ → K) → ℂ, (∀ l ∈ Λ, @GlobalTheory.WeilM.schr K _ h2 ψ₀ κ _ l h = h) →
      ∀ t, h t ≠ 0 → ∃ l ∈ Λ, l.1 = t := by
    intro h hh t ht
    apply hrefl
    intro y hy
    have hmem : ((0 : κ → K), y) ∈ Λ := by
      rw [hdual]
      intro l hl
      simp only [zero_dotProduct, zero_sub, AddChar.map_neg_eq_inv, hy l hl, inv_one]
    have := congrFun (hh _ hmem) t
    simp only [GlobalTheory.WeilM.schr, zero_dotProduct, mul_zero, add_zero] at this
    have h' : ψ₀ (t ⬝ᵥ y) * h t = 1 * h t := by rw [one_mul]; exact this
    exact mul_right_cancel₀ ht h'

  have key2 : ∀ h : (κ → K) → ℂ, (∀ l ∈ Λ, @GlobalTheory.WeilM.schr K _ h2 ψ₀ κ _ l h = h) →
      ∀ l ∈ Λ, ψ₀ (⅟2 * l.1 ⬝ᵥ l.2) * h l.1 = h 0 := by
    intro h hh l hl
    have := congrFun (hh l hl) 0
    simpa [GlobalTheory.WeilM.schr] using this
  have hg0 : g 0 ≠ 0 := by
    intro h0
    apply hg
    funext t
    by_contra ht
    obtain ⟨l, hl, rfl⟩ := key1 g hgf t ht
    have := key2 g hgf l hl
    rw [h0] at this
    exact ht ((mul_eq_zero.1 this).resolve_left (hne _))
  refine ⟨f 0 / g 0, ?_⟩
  funext t
  simp only [Pi.smul_apply, smul_eq_mul]
  by_cases ht : ∃ l ∈ Λ, l.1 = t
  · obtain ⟨l, hl, rfl⟩ := ht
    have e1 := key2 f hf l hl
    have e2 := key2 g hgf l hl
    apply mul_left_cancel₀ (hne (⅟2 * l.1 ⬝ᵥ l.2))
    rw [e1, ← mul_assoc, mul_comm _ (f 0 / g 0), mul_assoc, e2, div_mul_cancel₀ _ hg0]
  · have hf0 : f t = 0 := by by_contra h; exact ht (key1 f hf t h)
    have hg0' : g t = 0 := by by_contra h; exact ht (key1 g hgf t h)
    rw [hf0, hg0', mul_zero]

theorem locCo_smul {F : Type} [Field F] [NumberField F] {W : Type} [AddCommGroup W] [Module (AF F) W]
    {Bf : W → W → AF F} {κ : Type} [Fintype κ] (co : GlobalTheory.WeilM.Darboux Bf κ) (v : Pl (F := F)) (c : Fv F v) (z : W) :
    GlobalTheory.LatVac.locCo co v (GlobalTheory.LatVac.liftV v c • z) =
      (c • (GlobalTheory.LatVac.locCo co v z).1, c • (GlobalTheory.LatVac.locCo co v z).2) := by
  simp only [GlobalTheory.LatVac.locCo, AddMonoidHom.coe_mk, ZeroHom.coe_mk, LinearEquiv.map_smul, Prod.smul_fst,
    Prod.smul_snd, Pi.smul_apply, smul_eq_mul, map_mul, GlobalTheory.LatVac.evFin_liftV]
  rfl

theorem vac_fixed_and_unique : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ (Y : Type) [AddCommGroup Y] (Xm : Y →+ Matrix (Fin a) (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (P : Y → Prop),
      (∀ u, P u → Xm u ∈ latAtV G.V G.W v) → (∀ z ∈ latAtV G.V G.W v, ∃ u, P u ∧ Xm u = z) →
      ∀ ρ : Y → Module.End ℂ (SB (Fin a × Fin (a + a') → Fv F v)),
      (∀ x (φ : SB (Fin a × Fin (a + a') → Fv F v)), Acts (evFin F v) (G.M.co.rho B.ψ (Xm x))
        (φ : (Fin a × Fin (a + a') → Fv F v) → ℂ) ((ρ x φ : SB (Fin a × Fin (a + a') → Fv F v)) : (Fin a × Fin (a + a') → Fv F v) → ℂ)) →
      (∀ s : SB (Fin a × Fin (a + a') → Fv F v), (s : (Fin a × Fin (a + a') → Fv F v) → ℂ) = G.M.vac v → ∀ u, P u → ρ u s = s) ∧
      ∀ s : SB (Fin a × Fin (a + a') → Fv F v), (∀ u, P u → ρ u s = s) →
        ∃ c : ℂ, (s : (Fin a × Fin (a + a') → Fv F v) → ℂ) = c • G.M.vac v := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v w hin hvT Y _ Xm P hP hPs ρ hρ
  obtain ⟨hvSB, hv0, θ, hθ, hvac⟩ := hT.geo.hM.vac v
  have hAt : ∀ γ ∈ latAtV G.V G.W v, At (evFin F v) γ := (GlobalTheory.LatVac.latAtV_at_stable G.V G.W v).1
  have hloc : ∀ γ ∈ latAtV G.V G.W v, ∀ φ : (Fin a × Fin (a + a') → Fv F v) → ℂ,
      Acts (evFin F v) (G.M.co.rho B.ψ γ) φ
        (GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M.co v γ) φ) :=
    fun γ hγ φ => GlobalTheory.VacBridge.rho_acts_locCo G.M.co B.ψ v γ (hAt γ hγ) φ
  have hph := phase_one F E σ B a a' G X om om' hT v w hin θ hθ
  have hvfix : ∀ γ ∈ latAtV G.V G.W v,
      GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M.co v γ) (G.M.vac v) = G.M.vac v := by
    intro γ hγ
    have h1 := hvac γ hγ
    rw [hph γ hγ, one_smul] at h1
    exact acts_unique v _ hvSB (hloc γ hγ _) h1
  have hρs : ∀ u, P u → ∀ s : SB (Fin a × Fin (a + a') → Fv F v),
      ((ρ u s : SB (Fin a × Fin (a + a') → Fv F v)) : (Fin a × Fin (a + a') → Fv F v) → ℂ) =
        GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M.co v (Xm u)) s :=
    fun u hu s => acts_unique v _ s.2 (hρ u s) (hloc _ (hP u hu) _)
  refine ⟨fun s hs u hu => ?_, fun s hs => ?_⟩
  · apply Subtype.ext
    rw [hρs u hu s, hs]
    exact hvfix _ (hP u hu)
  · set Λ := (latAtV G.V G.W v).map (GlobalTheory.LatVac.locCo G.M.co v) with hΛ
    have hdual : ∀ l, l ∈ Λ ↔ ∀ m ∈ Λ, GlobalTheory.LatVac.psiAt B.ψ v (l.1 ⬝ᵥ m.2 - m.1 ⬝ᵥ l.2) = 1 :=
      fun l => GlobalTheory.LatVac.DualLoc.map_selfDual v G.M.co B.ψ (latAtV G.V G.W v) hAt
        (GlobalTheory.InertSelfDual.latAtV_selfDual F E σ B a a' G X om om' hT v w hin) l
    have hsfix : ∀ l ∈ Λ, GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt B.ψ v) l (s : (Fin a × Fin (a + a') → Fv F v) → ℂ) = s := by
      rintro l ⟨z, hz, rfl⟩
      obtain ⟨u, hu, rfl⟩ := hPs z hz
      have := hρs u hu s
      rw [hs u hu] at this
      exact this.symm
    have hgfix : ∀ l ∈ Λ, GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt B.ψ v) l (G.M.vac v) = G.M.vac v := by
      rintro l ⟨z, hz, rfl⟩
      exact hvfix z hz
    have hPU := (hT.base.inert v w hin).2.2
    have hψ : ∀ x : Fv F v, (∀ y ∈ HeightOneSpectrum.adicCompletionIntegers F v, GlobalTheory.LatVac.psiAt B.ψ v (x * y) = 1) ↔
        x ∈ HeightOneSpectrum.adicCompletionIntegers F v := by
      intro x
      simp only [GlobalTheory.LatVac.psiAt_apply]
      exact hPU x
    obtain ⟨c, hc0, hc⟩ := GlobalTheory.T.latticeLocalDarbouxCoordinates_bounded F E σ B a a' G X om om' hT v
    have hrefl : ∀ t : Fin a × Fin (a + a') → Fv F v,
        (∀ y, (∀ l ∈ Λ, GlobalTheory.LatVac.psiAt B.ψ v (l.1 ⬝ᵥ y) = 1) → GlobalTheory.LatVac.psiAt B.ψ v (t ⬝ᵥ y) = 1) →
          ∃ l ∈ Λ, l.1 = t := by
      intro t ht
      have := GlobalTheory.T.boundedIntegersStableSubgroup_eq_doubleOrthogonal F v (Fin a × Fin (a + a')) (GlobalTheory.LatVac.psiAt B.ψ v) hψ (Λ.map (AddMonoidHom.fst _ _))
        (by
          rintro r hr _ ⟨l, ⟨z, hz, rfl⟩, rfl⟩
          refine ⟨GlobalTheory.LatVac.locCo G.M.co v (GlobalTheory.LatVac.liftV v r • z),
            ⟨_, (GlobalTheory.LatVac.latAtV_at_stable G.V G.W v).2 r hr z hz, rfl⟩, ?_⟩
          rw [locCo_smul]
          rfl)
        ⟨c, hc0, by
          rintro _ ⟨l, ⟨z, hz, rfl⟩, rfl⟩ k
          exact (hc z hz k).1⟩ t
        (fun y hy => ht y fun l hl => hy _ ⟨l, hl, rfl⟩)
      obtain ⟨l, hl, rfl⟩ := this
      exact ⟨l, hl, rfl⟩
    exact fixed_eq_smul (GlobalTheory.LatVac.psiAt B.ψ v) Λ hdual hrefl hv0 hsfix hgfix

end GlobalTheory.InertLatVac
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceLatticeVacuumFixedAndUniqueStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertPlace_latticeVacuum_fixed_and_unique : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ (Y : Type) [AddCommGroup Y] (Xm : Y →+ Matrix (Fin a) (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (P : Y → Prop),
      (∀ u, P u → Xm u ∈ latAtV G.V G.W v) → (∀ z ∈ latAtV G.V G.W v, ∃ u, P u ∧ Xm u = z) →
      ∀ ρ : Y → Module.End ℂ (SB (Fin a × Fin (a + a') → Fv F v)),
      (∀ x (φ : SB (Fin a × Fin (a + a') → Fv F v)), Acts (evFin F v) (G.M.co.rho B.ψ (Xm x))
        (φ : (Fin a × Fin (a + a') → Fv F v) → ℂ) ((ρ x φ : SB (Fin a × Fin (a + a') → Fv F v)) : (Fin a × Fin (a + a') → Fv F v) → ℂ)) →
      (∀ s : SB (Fin a × Fin (a + a') → Fv F v), (s : (Fin a × Fin (a + a') → Fv F v) → ℂ) = G.M.vac v → ∀ u, P u → ρ u s = s) ∧
      ∀ s : SB (Fin a × Fin (a + a') → Fv F v), (∀ u, P u → ρ u s = s) →
        ∃ c : ℂ, (s : (Fin a × Fin (a + a') → Fv F v) → ℂ) = c • G.M.vac v := by
  first | exact @GlobalTheory.InertLatVac.vac_fixed_and_unique | exact GlobalTheory.InertLatVac.vac_fixed_and_unique | (intros; apply GlobalTheory.InertLatVac.vac_fixed_and_unique <;> assumption)
end
