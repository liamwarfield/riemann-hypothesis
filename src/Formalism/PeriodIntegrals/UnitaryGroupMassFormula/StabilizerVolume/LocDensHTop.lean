module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocDensHIL
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocDensFFIn
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocDensVol
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.MeasureEqOfCos

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocDensHH
noncomputable section

namespace PI.VolStabS

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.VolFromSW
  Matrix

section Mat

variable {A : Type} [CommRing A] (s : A →+* A)

theorem hform_mul_right {M a : ℕ} (Jm : Matrix (Fin M) (Fin M) A) (Y : Fin a → Fin M → A)
    (C : Matrix (Fin a) (Fin a) A) (i j : Fin a) :
    Formalism.UG.hform s Jm (Y i) (fun l => ∑ k, C j k * Y k l) =
      ∑ k, Formalism.UG.hform s Jm (Y i) (Y k) * C j k := by

  unfold Formalism.UG.hform
  simp only [Finset.mul_sum, Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun k _ => ?_
  ring

theorem hform_mul_left {M a : ℕ} (Jm : Matrix (Fin M) (Fin M) A) (Y : Fin a → Fin M → A)
    (C : Matrix (Fin a) (Fin a) A) (i j : Fin a) :
    Formalism.UG.hform s Jm (fun l => ∑ k, C i k * Y k l) (Y j) =
      ∑ k, s (C i k) * Formalism.UG.hform s Jm (Y k) (Y j) := by

  unfold Formalism.UG.hform
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun k _ => ?_
  ring

theorem pol_solve {a : ℕ} (h πA : A) (hh : h + h = 1) (hsh : s h = h)
    (Γ Tm Tinv Sm E0 : Matrix (Fin a) (Fin a) A) (hΓ : Γ = Tm + πA • E0)
    (hTT : Tm * Tinv = 1) (hTs : (Tinv.map s)ᵀ * Tm = 1) (hS : ∀ i k, s (Sm k i) = Sm i k) :
    Γ * ((h • (Tinv * Sm))ᵀ)ᵀ + ((h • (Tinv * Sm))ᵀ).map s * Γ =
      Sm + πA • (h • (E0 * Tinv * Sm + Sm * (Tinv.map s)ᵀ * E0)) := by

  have hSm : (Smᵀ).map s = Sm := by
    ext i k
    simp [Matrix.map_apply, Matrix.transpose_apply, hS]
  have h2 : ((h • (Tinv * Sm))ᵀ).map s = h • (Sm * (Tinv.map s)ᵀ) := by
    ext i k
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply, hS, hsh, map_sum]
  have e1 : Tm * (Tinv * Sm) = Sm := by rw [← Matrix.mul_assoc, hTT, Matrix.one_mul]
  have e2 : Sm * ((Tinv.map s)ᵀ * Tm) = Sm := by rw [hTs, Matrix.mul_one]
  have key : ∀ X Y Z : Matrix (Fin a) (Fin a) A,
      h • (Z + πA • X) + (h • Z + πA • h • Y) = (h + h) • Z + πA • h • (X + Y) := by
    intro X Y Z
    simp only [smul_add, add_smul]
    rw [smul_comm h πA X]
    abel
  rw [Matrix.transpose_transpose, h2, hΓ]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]
  rw [e1, e2, key, hh, one_smul]

end Mat

section Int

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {d : ℕ}
  (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))

def intA (z : Fv F v ⊗[F] E) : Prop :=
  ∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr z k ∈ v.adicCompletionIntegers F

variable {b v}

theorem intA_add {z w : Fv F v ⊗[F] E} (hz : intA b v z) (hw : intA b v w) : intA b v (z + w) := by
  intro k
  rw [map_add (f := _), Finsupp.add_apply]
  exact add_mem (hz k) (hw k)

theorem intA_sum {ι : Type} (t : Finset ι) (f : ι → Fv F v ⊗[F] E) (hf : ∀ i ∈ t, intA b v (f i)) :
    intA b v (∑ i ∈ t, f i) := by

  intro k
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finsupp.finsetSum_apply]
  exact sum_mem fun i hi => hf i hi k

theorem intA_smul {c : Fv F v} (hc : c ∈ v.adicCompletionIntegers F) {z : Fv F v ⊗[F] E}
    (hz : intA b v z) : intA b v (c • z) := by
  intro k
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
  exact mul_mem hc (hz k)

theorem intA_incl (e : E) (h : ∀ m, algebraMap F (Fv F v) (b.repr e m) ∈ v.adicCompletionIntegers F) :
    intA b v (inclR (Fv F v) e) := by
  intro k
  have he : inclR (Fv F v) e = (1 : Fv F v) ⊗ₜ[F] e := rfl
  rw [he, Algebra.TensorProduct.basis_repr_tmul]
  simpa using h k

theorem incl_eq_tmul (e : E) : inclR (Fv F v) e = (1 : Fv F v) ⊗ₜ[F] e := rfl

theorem intA_mul (hg : ∀ k l m, algebraMap F (Fv F v) (b.repr (b k * b l) m) ∈
      v.adicCompletionIntegers F)
    {z w : Fv F v ⊗[F] E} (hz : intA b v z) (hw : intA b v w) : intA b v (z * w) := by

  have hB : ∀ k, (Algebra.TensorProduct.basis (Fv F v) b) k = inclR (Fv F v) (b k) := fun k => by
    rw [Algebra.TensorProduct.basis_apply]
    rfl
  rw [← (Algebra.TensorProduct.basis (Fv F v) b).sum_repr z,
    ← (Algebra.TensorProduct.basis (Fv F v) b).sum_repr w, Finset.sum_mul_sum]
  refine intA_sum _ _ fun k _ => intA_sum _ _ fun l _ => ?_
  rw [smul_mul_smul_comm, hB, hB, ← map_mul]
  exact intA_smul (mul_mem (hz k) (hw l)) (intA_incl _ (hg k l))

theorem sigR_incl (σ : E →ₐ[F] E) (e : E) :
    sigR (Fv F v) σ (inclR (Fv F v) e) = inclR (Fv F v) (σ e) := by

  simp [sigR, inclR, Algebra.TensorProduct.map_tmul]

theorem sigR_smul (σ : E →ₐ[F] E) (c : Fv F v) (z : Fv F v ⊗[F] E) :
    sigR (Fv F v) σ (c • z) = c • sigR (Fv F v) σ z := by

  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [sigR, TensorProduct.smul_tmul', Algebra.TensorProduct.map_tmul]
  | add x y hx hy => rw [smul_add, map_add (f := _), map_add (f := _), hx, hy, smul_add]

theorem intA_sig (σ : E →ₐ[F] E)
    (hg : ∀ k m, algebraMap F (Fv F v) (b.repr (σ (b k)) m) ∈ v.adicCompletionIntegers F)
    {z : Fv F v ⊗[F] E} (hz : intA b v z) : intA b v (sigR (Fv F v) σ z) := by

  set_option synthInstance.maxHeartbeats 100000 in
    rw [← (Algebra.TensorProduct.basis (Fv F v) b).sum_repr z, map_sum]
  refine intA_sum _ _ fun k _ => ?_
  rw [sigR_smul, Algebra.TensorProduct.basis_apply, ← incl_eq_tmul, sigR_incl]
  exact intA_smul (hz k) (intA_incl _ (hg k))

theorem aaInt (x : F) : ∀ᶠ v in cofinite,
    algebraMap F (Fv F v) x ∈ v.adicCompletionIntegers F := by

  first
  | exact (algebraMap F (FiniteAdeleRing (𝓞 F) F) x).2
  | (rw [Filter.eventually_cofinite]
     refine (HeightOneSpectrum.Support.finite (𝓞 F) x).subset fun v hv => ?_
     simp only [Set.mem_setOf_eq, HeightOneSpectrum.mem_adicCompletionIntegers, not_le] at hv
     simpa [HeightOneSpectrum.Support, HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] using hv)

def GoodV (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (σ : E →ₐ[F] E) {M a : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (Tinv : Matrix (Fin a) (Fin a) E) : Prop :=
  (∀ k l m, algebraMap F (Fv F v) (b.repr (b k * b l) m) ∈ v.adicCompletionIntegers F) ∧
  (∀ k m, algebraMap F (Fv F v) (b.repr (σ (b k)) m) ∈ v.adicCompletionIntegers F) ∧
  (∀ i j m, algebraMap F (Fv F v) (b.repr (J i j) m) ∈ v.adicCompletionIntegers F) ∧
  (∀ m, algebraMap F (Fv F v) (b.repr (1 / 2 : E) m) ∈ v.adicCompletionIntegers F) ∧
  (∀ i j m, algebraMap F (Fv F v) (b.repr (Tinv i j) m) ∈ v.adicCompletionIntegers F)

theorem goodV_aa (b : Module.Basis (Fin d) F E) (σ : E →ₐ[F] E) {M a : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (Tinv : Matrix (Fin a) (Fin a) E) :
    ∀ᶠ v in cofinite, GoodV b v σ J Tinv := by

  simp only [GoodV, Filter.eventually_and, Filter.eventually_all]
  exact ⟨fun k l m => aaInt _, fun k m => aaInt _, fun i j m => aaInt _, fun m => aaInt _,
    fun i j m => aaInt _⟩

end Int

theorem map_smulSub' {K V X : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup X]
    [Module K X] (D : V →+ X) (hDs : ∀ (t : K) w, D (t • w) = t • D w) (t : K)
    (L : AddSubgroup V) : (smulSub t L).map D = smulSub t (L.map D) := by

  simp only [smulSub, AddSubgroup.map_map]
  congr 1
  ext w
  simp [hDs]

theorem hensAA_holds : HensAA := by
  intro F E _ _ _ _ _ σ hCM M J hJ _ _ a ha1 ha2 X0 hT hdet d b
  have : FiniteDimensional F E := Module.Finite.of_basis b
  have hσ := sigma_invol σ hCM.2.2.2
  set TE := gramE σ J X0 with hTE
  have hu : IsUnit TE.det := isUnit_iff_ne_zero.2 hdet
  filter_upwards [goodV_aa b σ J TE⁻¹] with v hg
  obtain ⟨g1, g2, g3, g4, g5⟩ := hg
  intro y hy hyT
  have := locallyCompact_Fv F v
  have : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalAddGroup (Fv F v ⊗[F] E) :=
    IsModuleTopology.topologicalAddGroup (Fv F v) (Fv F v ⊗[F] E)
  have : T2Space (Fv F v ⊗[F] E) := by
    obtain ⟨ι, _, ⟨h⟩⟩ := PI.AdicCompletionValuation.exists_homeomorph_tens (F := F) (E := E) (Fv F v)
    exact h.isEmbedding.t2Space
  have : T2Space (Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) :=
    inferInstanceAs (T2Space (Fin a → Fin a → Fv F v ⊗[F] E))
  obtain ⟨hπ0, hπ, hπO⟩ := unifV_spec v
  set π := unifV v with hπdef
  set s := sigR (Fv F v) σ with hsdef
  set L := latSub b v a M with hLdef
  have hLc : IsCompact (L : Set (Fin a → Fin M → Fv F v ⊗[F] E)) :=
    PositiveNearLattice.isCompact_latV b v a M
  have hπL : ∀ w ∈ L, π • w ∈ L := fun w hw => LatFactsW.smul_mem_latSub b v hπO hw
  have hyL : ∀ i l, intA b v (y i l) := fun i l => hy i l

  let D : (Fin a → Fin M → Fv F v ⊗[F] E) →+ HermR (Fv F v) σ a :=
    { toFun := fun W => ⟨gramB (Fv F v) σ J y W, gramB_mem (Fv F v) σ hσ J hJ.1 y W⟩
      map_zero' := by
        apply Subtype.ext
        funext i j
        simp [gramB, hR, Formalism.UG.hform]
      map_add' := fun W W' => Subtype.ext (gramB_add_right (Fv F v) σ J y W W') }
  have hDv : ∀ W, (D W : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) = gramB (Fv F v) σ J y W :=
    fun _ => rfl
  have hDc : Continuous D :=
    ((continuous_gramB (Fv F v) σ J).comp (Continuous.prodMk continuous_const continuous_id)).subtype_mk _
  have hDs : ∀ (t : Fv F v) W, D (t • W) = t • D W := by
    intro t W
    apply Subtype.ext
    funext i j
    show gramB (Fv F v) σ J y (t • W) i j = t • gramB (Fv F v) σ J y W i j
    simp only [gramB, Pi.smul_apply, hR_smul_left, hR_smul_right, smul_add]

  have hJi : ∀ i j, intA b v (JR (Fv F v) J i j) := fun i j => intA_incl _ (g3 i j)
  have hmul : ∀ {z w : Fv F v ⊗[F] E}, intA b v z → intA b v w → intA b v (z * w) :=
    fun hz hw => intA_mul g1 hz hw
  have hsig : ∀ {z : Fv F v ⊗[F] E}, intA b v z → intA b v (s z) := fun hz => intA_sig σ g2 hz
  have hRi : ∀ x z : Fin M → Fv F v ⊗[F] E, (∀ l, intA b v (x l)) → (∀ l, intA b v (z l)) →
      intA b v (hR (Fv F v) σ J x z) := by
    intro x z hx hz
    have e : hR (Fv F v) σ J x z = ∑ i, ∑ j, s (x i) * JR (Fv F v) J i j * z j := rfl
    rw [e]
    exact intA_sum _ _ fun i _ => intA_sum _ _ fun j _ =>
      hmul (hmul (hsig (hx i)) (hJi i j)) (hz j)
  have hgB : ∀ u w, u ∈ L → w ∈ L →
      (⟨gramB (Fv F v) σ J u w, gramB_mem (Fv F v) σ hσ J hJ.1 u w⟩ : HermR (Fv F v) σ a) ∈
        hermO b v σ a := by
    intro u w hu' hw' i j
    exact intA_add (hRi _ _ (hu' i) (hw' j)) (hRi _ _ (hw' i) (hu' j))
  have hgR : ∀ w, w ∈ L → gramH (Fv F v) σ hσ J hJ.1 w ∈ hermO b v σ a := by
    intro w hw' i j
    exact hRi _ _ (hw' i) (hw' j)
  have hOsm : ∀ {c : Fv F v}, c ∈ v.adicCompletionIntegers F → ∀ S ∈ hermO b v σ a,
      c • S ∈ hermO b v σ a := by
    intro c hc S hS i j
    exact intA_smul hc (hS i j)

  set Tm : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E) := TE.map (inclR (Fv F v)) with hTm
  set Ti : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E) := TE⁻¹.map (inclR (Fv F v)) with hTi
  have hTT : Tm * Ti = 1 := by
    rw [hTm, hTi, ← Matrix.map_mul, Matrix.mul_nonsing_inv _ hu, Matrix.map_one _ (map_zero _)
      (map_one _)]
  have hTh : (TE.map (σ : E →+* E))ᵀ = TE := by
    ext i j
    exact hT i j
  have hE1 : (TE⁻¹.map (σ : E →+* E))ᵀ * TE = 1 := by
    calc (TE⁻¹.map (σ : E →+* E))ᵀ * TE
        = (TE⁻¹.map (σ : E →+* E))ᵀ * (TE.map (σ : E →+* E))ᵀ := by rw [hTh]
      _ = ((TE.map (σ : E →+* E)) * (TE⁻¹.map (σ : E →+* E)))ᵀ := (Matrix.transpose_mul _ _).symm
      _ = ((TE * TE⁻¹).map (σ : E →+* E))ᵀ := by rw [Matrix.map_mul]
      _ = 1 := by
        rw [Matrix.mul_nonsing_inv _ hu, Matrix.map_one _ (map_zero _) (map_one _),
          Matrix.transpose_one]
  have hTs : (Ti.map s)ᵀ * Tm = 1 := by
    have e : (Ti.map s)ᵀ = ((TE⁻¹.map (σ : E →+* E))ᵀ).map (inclR (Fv F v)) := by
      ext i j
      simp [hTi, hsdef, sigR_incl]
    rw [e, hTm, ← Matrix.map_mul, hE1, Matrix.map_one _ (map_zero _) (map_one _)]
  have hTii : ∀ i j, intA b v (Ti i j) := fun i j => intA_incl _ (g5 i j)

  set h : Fv F v ⊗[F] E := inclR (Fv F v) (1 / 2 : E) with hhdef
  have hh : h + h = 1 := by rw [hhdef, ← map_add (f := _), add_halves, map_one]
  have hsh : s h = h := by
    rw [hsdef, hhdef, sigR_incl]
    congr 1
    rw [map_div₀, map_one, map_ofNat]
  have hhi : intA b v h := intA_incl _ g4

  have hyT' : gramH (Fv F v) σ hσ J hJ.1 y - hermOf (Fv F v) σ TE hT ∈ smulSub π (hermO b v σ a) := by
    have := hyT
    simp only [hF, zero_add, pow_one] at this
    exact this
  obtain ⟨E0h, hE0, hE0eq⟩ := (mem_smulSub _ _ _).1 hyT'
  set πA : Fv F v ⊗[F] E := algebraMap (Fv F v) (Fv F v ⊗[F] E) π with hπA
  have hΓ : gramR (Fv F v) σ J y = Tm + πA • (E0h : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) := by
    have e := congrArg Subtype.val hE0eq
    have e2 : π • (E0h : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) = gramR (Fv F v) σ J y - Tm := e
    rw [hπA, algebraMap_smul, e2]
    abel

  have hbase : ∀ S ∈ hermO b v σ a, ∃ l ∈ L, S - D l ∈ smulSub π (hermO b v σ a) := by
    intro S hS
    set Sm : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E) := S.1 with hSm
    have hSh : ∀ i k, s (Sm k i) = Sm i k := fun i k => S.2 i k
    set C : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E) := (h • (Ti * Sm))ᵀ with hC
    set W : Fin a → Fin M → Fv F v ⊗[F] E := fun j l => ∑ k, C j k * y k l with hW
    have hCi : ∀ j k, intA b v (C j k) := by
      intro j k
      simp only [hC, Matrix.transpose_apply, Matrix.smul_apply, Matrix.mul_apply, smul_eq_mul]
      exact hmul hhi (intA_sum _ _ fun m _ => hmul (hTii k m) (hS m j))
    have hWL : W ∈ L := fun j l => intA_sum _ _ fun k _ => hmul (hCi j k) (hyL k l)
    have hgW : gramB (Fv F v) σ J y W = gramR (Fv F v) σ J y * Cᵀ + C.map s * gramR (Fv F v) σ J y := by
      ext i j
      simp only [gramB, Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
      rw [show hR (Fv F v) σ J (y i) (W j) = ∑ k, hR (Fv F v) σ J (y i) (y k) * C j k from
          hform_mul_right s (JR (Fv F v) J) y C i j,
        show hR (Fv F v) σ J (W i) (y j) = ∑ k, s (C i k) * hR (Fv F v) σ J (y k) (y j) from
          hform_mul_left s (JR (Fv F v) J) y C i j]
      rfl
    have hsol := pol_solve s h πA hh hsh (gramR (Fv F v) σ J y) Tm Ti Sm E0h hΓ hTT hTs hSh
    set R : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E) :=
      h • ((E0h : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) * Ti * Sm + Sm * (Ti.map s)ᵀ * E0h)
      with hRdef
    have hRi' : ∀ i j, intA b v (R i j) := by
      intro i j
      simp only [hRdef, Matrix.smul_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply,
        Matrix.map_apply, smul_eq_mul]
      refine hmul hhi (intA_add (intA_sum _ _ fun k _ => hmul (intA_sum _ _ fun m _ =>
        hmul (hE0 i m) (hTii m k)) (hS k j)) (intA_sum _ _ fun k _ => hmul (intA_sum _ _ fun m _ =>
        hmul (hS i m) (hsig (hTii k m))) (hE0 k j)))
    have hsol' : gramR (Fv F v) σ J y * Cᵀ + C.map s * gramR (Fv F v) σ J y = Sm + πA • R := hsol
    have hDW : (D W : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) = Sm + π • R := by
      rw [hDv, hgW, hsol', hπA, algebraMap_smul]
    set Rh : HermR (Fv F v) σ a := π⁻¹ • (D W - S) with hRh
    have hRhv : (Rh : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) = R := by
      show π⁻¹ • ((D W : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) - Sm) = R
      rw [hDW, add_sub_cancel_left, inv_smul_smul₀ hπ0]
    have hRhO : Rh ∈ hermO b v σ a := by
      intro i j
      show intA b v ((Rh : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j)
      rw [hRhv]
      exact hRi' i j
    refine ⟨W, hWL, (mem_smulSub _ _ _).2 ⟨-Rh, (hermO b v σ a).neg_mem hRhO, ?_⟩⟩
    rw [hRh, smul_neg, smul_inv_smul₀ hπ0, neg_sub]
  have hreach := reach_of_approx π hπ L hLc hπL D hDc hDs (hermO b v σ a)
    (LatFactsW.isCompact_hermO b v σ a) hbase
  have hDL : L.map D = hermO b v σ a := by
    refine le_antisymm ?_ fun p hp => ?_
    · rintro _ ⟨W, hW, rfl⟩
      exact hgB y W hy hW
    · obtain ⟨l, hl, e⟩ := hreach p hp
      exact AddSubgroup.mem_map.2 ⟨l, hl, e⟩
  refine ⟨D, fun n => ?_, fun n Z hZ W hW => ?_⟩
  · rw [lamF, hF, map_smulSub' D hDs, hDL]
  · obtain ⟨z, hz, rfl⟩ := (mem_smulSub _ _ _).1 hZ
    obtain ⟨w, hw, rfl⟩ := (mem_smulSub _ _ _).1 hW
    rw [hF, mem_smulSub]
    have hB : (⟨gramB (Fv F v) σ J z w, gramB_mem (Fv F v) σ hσ J hJ.1 z w⟩ :
        HermR (Fv F v) σ a) ∈ hermO b v σ a := hgB z w hz hw
    have hG : π ^ n • gramH (Fv F v) σ hσ J hJ.1 w ∈ hermO b v σ a :=
      hOsm (pow_mem hπO n) _ (hgR w hw)
    refine ⟨_, (hermO b v σ a).add_mem hB hG, ?_⟩
    apply Subtype.ext
    show π ^ (n + 1 + 1) • (gramB (Fv F v) σ J z w + π ^ n • gramR (Fv F v) σ J w) =
      gramR (Fv F v) σ J (y + unifV v ^ (0 + 1) • z + unifV v ^ (n + 1) • w) -
        gramR (Fv F v) σ J (y + unifV v ^ (0 + 1) • z) - gramB (Fv F v) σ J y (unifV v ^ (n + 1) • w)
    have e2 : gramR (Fv F v) σ J (y + unifV v ^ (0 + 1) • z + unifV v ^ (n + 1) • w) -
        gramR (Fv F v) σ J (y + unifV v ^ (0 + 1) • z) - gramB (Fv F v) σ J y (unifV v ^ (n + 1) • w) =
        gramB (Fv F v) σ J (unifV v ^ (0 + 1) • z) (unifV v ^ (n + 1) • w) +
          gramR (Fv F v) σ J (unifV v ^ (n + 1) • w) := by
      ext i j
      simp only [Matrix.sub_apply, Matrix.add_apply, gramB, gramR, Pi.add_apply, hR_add_left,
        hR_add_right]
      ring
    have gBs : ∀ (t t' : Fv F v) (u u' : Fin a → Fin M → Fv F v ⊗[F] E),
        gramB (Fv F v) σ J (t • u) (t' • u') = (t * t') • gramB (Fv F v) σ J u u' := by
      intro t t' u u'
      ext i j
      simp only [gramB, Pi.smul_apply, hR_smul_left, hR_smul_right, Matrix.smul_apply]
      module
    have gRs : ∀ (t : Fv F v) (u : Fin a → Fin M → Fv F v ⊗[F] E),
        gramR (Fv F v) σ J (t • u) = (t * t) • gramR (Fv F v) σ J u := by
      intro t u
      ext i j
      simp only [gramR, Pi.smul_apply, hR_smul_left, hR_smul_right, Matrix.smul_apply]
      module
    rw [e2, gBs, gRs, ← hπdef]
    module

end PI.VolStabS
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocDensFFAll
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocDensFFT
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocDensFFS
noncomputable section

namespace PI.VolStabS

namespace FiniteFieldSplitting

open Matrix

variable {k : Type} [Field k] [Finite k]

def cols {M a : ℕ} (P : Matrix (Fin M) (Fin a) k) : Fin a → Fin M → k := fun j i ↦ P i j

theorem linInd_cols_iff {M a : ℕ} (P : Matrix (Fin M) (Fin a) k) :
    LinearIndependent k (cols P) ↔ ∀ v : Fin a → k, P *ᵥ v = 0 → v = 0 := by
  rw [Fintype.linearIndependent_iff]
  constructor
  · intro h v hv
    funext j
    refine h v ?_ j
    funext i
    have := congrFun hv i
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at this
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, cols, Pi.zero_apply]
    rw [← this]
    exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)
  · intro h g hg i
    have hPg : P *ᵥ g = 0 := by
      funext r
      have := congrFun hg r
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, cols, Pi.zero_apply] at this
      simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
      rw [← this]
      exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)
    exact congrFun (h g hPg) i

theorem exists_left_inv {M a : ℕ} (P : Matrix (Fin M) (Fin a) k)
    (hP : LinearIndependent k (cols P)) : ∃ L : Matrix (Fin a) (Fin M) k, L * P = 1 := by
  have hker : LinearMap.ker (Matrix.toLin' P) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro v hv
    rw [Matrix.toLin'_apply] at hv
    exact (linInd_cols_iff P).1 hP v hv
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' P) hker
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  have h1 := congrArg LinearMap.toMatrix' hg
  rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_id] at h1

theorem linInd_of_left_inv {M a : ℕ} (W : Matrix (Fin a) (Fin M) k) (P : Matrix (Fin M) (Fin a) k)
    (h : W * P = 1) : LinearIndependent k (cols P) := by
  rw [linInd_cols_iff]
  intro v hv
  calc v = (W * P) *ᵥ v := by rw [h, Matrix.one_mulVec]
    _ = W *ᵥ (P *ᵥ v) := by rw [Matrix.mulVec_mulVec]
    _ = 0 := by rw [hv, Matrix.mulVec_zero]

theorem card_left_inv {M a : ℕ} (P : Matrix (Fin M) (Fin a) k)
    (hP : LinearIndependent k (cols P)) :
    Nat.card {W : Matrix (Fin a) (Fin M) k // W * P = 1} = Nat.card k ^ (a * (M - a)) := by
  classical
  obtain ⟨L, hL⟩ := exists_left_inv P hP
  let f : Matrix (Fin a) (Fin M) k →ₗ[k] Matrix (Fin a) (Fin a) k :=
    { toFun := fun D => D * P
      map_add' := fun D E => Matrix.add_mul D E P
      map_smul' := fun c D => Matrix.smul_mul c D P }
  have hf : ∀ D, f D = D * P := fun D => rfl
  have hsurj : LinearMap.range f = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro E
    exact ⟨E * L, by rw [hf, Matrix.mul_assoc, hL, Matrix.mul_one]⟩
  have hrk := LinearMap.finrank_range_add_finrank_ker f
  rw [hsurj, finrank_top] at hrk
  simp only [Module.finrank_matrix, Fintype.card_fin, Module.finrank_self, mul_one] at hrk
  have hker : Module.finrank k (LinearMap.ker f) = a * M - a * a := by omega
  have e : {W : Matrix (Fin a) (Fin M) k // W * P = 1} ≃ LinearMap.ker f :=
    { toFun := fun W => ⟨W.1 - L, by rw [LinearMap.mem_ker, hf, Matrix.sub_mul, W.2, hL, sub_self]⟩
      invFun := fun D => ⟨D.1 + L, by
        have hD := D.2
        rw [LinearMap.mem_ker, hf] at hD
        rw [Matrix.add_mul, hD, hL, zero_add]⟩
      left_inv := fun W => by ext1; simp
      right_inv := fun D => by ext1; simp }
  rw [Nat.card_congr e, Module.natCard_eq_pow_finrank (K := k), hker, Nat.mul_sub_left_distrib]

theorem card_pairs {M a : ℕ} (ha : a ≤ M) :
    Nat.card {WP : Matrix (Fin a) (Fin M) k × Matrix (Fin M) (Fin a) k // WP.1 * WP.2 = 1} =
      (∏ i : Fin a, (Nat.card k ^ M - Nat.card k ^ (i : ℕ))) * Nat.card k ^ (a * (M - a)) := _root_.PI.VolStabSW.FiniteFieldSplitting.card_pairs (M := M) (a := a) ha

end FiniteFieldSplitting

namespace FiniteFieldSplitting

open Matrix

variable {k : Type} [Field k] [Finite k] {M a : ℕ}

abbrev swapR (k : Type) [Field k] : k × k →+* k × k := (RingEquiv.prodComm (R := k) (S := k)).toRingHom

def U1 (X : Fin a → Fin M → k × k) : Matrix (Fin a) (Fin M) k := fun r i ↦ (X r i).1

def V1 (X : Fin a → Fin M → k × k) : Matrix (Fin a) (Fin M) k := fun r i ↦ (X r i).2

theorem ffH_fst (J : Matrix (Fin M) (Fin M) (k × k)) (x y : Fin M → k × k) :
    (ffH (swapR k) J x y).1 = ∑ i, ∑ j, (x i).2 * (J i j).1 * (y j).1 := by
  unfold ffH
  simp [Prod.fst_sum, swapR]

theorem ffH_snd (J : Matrix (Fin M) (Fin M) (k × k)) (x y : Fin M → k × k) :
    (ffH (swapR k) J x y).2 = ∑ i, ∑ j, (x i).1 * (J i j).2 * (y j).2 := by
  unfold ffH
  simp [Prod.snd_sum, swapR]

private theorem ffGram_apply (J : Matrix (Fin M) (Fin M) (k × k))
    (X : Fin a → Fin M → k × k) (r s : Fin a) :
    ffGram (swapR k) J X r s = ffH (swapR k) J (X r) (X s) := by
  first
  | rfl
  | simp [ffGram]
  | (unfold ffGram; simp)

private theorem fst_ffGram_eq_V1_mul_map_fst (J : Matrix (Fin M) (Fin M) (k × k)) (X : Fin a → Fin M → k × k)
    (r s : Fin a) :
    (V1 X * J.map Prod.fst * (U1 X)ᵀ) r s = (ffGram (swapR k) J X r s).1 := by
  rw [ffGram_apply, ffH_fst]
  simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply, V1, U1, Finset.sum_mul]
  exact Finset.sum_comm

private theorem snd_ffGram_eq_fst_ffGram_swap (J : Matrix (Fin M) (Fin M) (k × k)) (hJ : ∀ i j, (J j i).swap = J i j)
    (X : Fin a → Fin M → k × k) (r s : Fin a) :
    (ffGram (swapR k) J X r s).2 = (ffGram (swapR k) J X s r).1 := by
  rw [ffGram_apply, ffGram_apply, ffH_fst, ffH_snd]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
  have h := congrArg Prod.fst (hJ x y)
  rw [Prod.fst_swap] at h
  rw [h]
  ring

theorem gram_iff (J : Matrix (Fin M) (Fin M) (k × k)) (hJ : ∀ i j, (J j i).swap = J i j)
    (T : Matrix (Fin a) (Fin a) (k × k)) (hT : ∀ i j, (T j i).swap = T i j)
    (X : Fin a → Fin M → k × k) :
    ffGram (swapR k) J X = T ↔
      V1 X * J.map Prod.fst * (U1 X)ᵀ = T.map Prod.fst := by
  constructor
  · rintro rfl
    refine Matrix.ext fun r s => ?_
    rw [fst_ffGram_eq_V1_mul_map_fst]
    rfl
  · intro h
    have hf : ∀ r s, (ffGram (swapR k) J X r s).1 = (T r s).1 := fun r s => by
      rw [← fst_ffGram_eq_V1_mul_map_fst]
      exact congrFun (congrFun h r) s
    refine Matrix.ext fun r s => Prod.ext (hf r s) ?_
    rw [snd_ffGram_eq_fst_ffGram_swap J hJ X, hf s r]
    have h2 := congrArg Prod.snd (hT r s)
    rw [Prod.snd_swap] at h2
    exact h2

theorem fFSplit_nat (M a : ℕ) (ha : a ≤ M)
    (J : Matrix (Fin M) (Fin M) (k × k)) (hJ : ∀ i j, (J j i).swap = J i j) (hJd : IsUnit J.det)
    (T : Matrix (Fin a) (Fin a) (k × k)) (hT : ∀ i j, (T j i).swap = T i j) (hTd : IsUnit T.det) :
    Nat.card {X : Fin a → Fin M → k × k // ffGram (swapR k) J X = T} =
      (∏ i : Fin a, (Nat.card k ^ M - Nat.card k ^ (i : ℕ))) * Nat.card k ^ (a * (M - a)) := by
  classical
  have hJ1 : IsUnit (J.map Prod.fst).det := by
    have h1 := (Prod.isUnit_iff.mp hJd).1
    rwa [show J.det.1 = (J.map Prod.fst).det from RingHom.map_det (RingHom.fst k k) J] at h1
  have hT1 : IsUnit (T.map Prod.fst).det := by
    have h1 := (Prod.isUnit_iff.mp hTd).1
    rwa [show T.det.1 = (T.map Prod.fst).det from RingHom.map_det (RingHom.fst k k) T] at h1
  have e : {X : Fin a → Fin M → k × k // ffGram (swapR k) J X = T} ≃
      {WP : Matrix (Fin a) (Fin M) k × Matrix (Fin M) (Fin a) k // WP.1 * WP.2 = 1} :=
    { toFun := fun X => ⟨((T.map Prod.fst)⁻¹ * V1 X.1, J.map Prod.fst * (U1 X.1)ᵀ), by
        have h := (gram_iff J hJ T hT X.1).1 X.2
        show (T.map Prod.fst)⁻¹ * V1 X.1 * (J.map Prod.fst * (U1 X.1)ᵀ) = 1
        rw [Matrix.mul_assoc, ← Matrix.mul_assoc (V1 X.1), h, Matrix.nonsing_inv_mul _ hT1]⟩
      invFun := fun WP => ⟨fun r i => ((((J.map Prod.fst)⁻¹ * WP.1.2)ᵀ) r i,
          (T.map Prod.fst * WP.1.1) r i), by
        rw [gram_iff J hJ T hT]
        have hU : U1 (fun r i => ((((J.map Prod.fst)⁻¹ * WP.1.2)ᵀ) r i,
            (T.map Prod.fst * WP.1.1) r i)) = ((J.map Prod.fst)⁻¹ * WP.1.2)ᵀ := rfl
        have hV : V1 (fun r i => ((((J.map Prod.fst)⁻¹ * WP.1.2)ᵀ) r i,
            (T.map Prod.fst * WP.1.1) r i)) = T.map Prod.fst * WP.1.1 := rfl
        rw [hU, hV, Matrix.transpose_transpose, Matrix.mul_assoc, ← Matrix.mul_assoc (J.map Prod.fst),
          Matrix.mul_nonsing_inv _ hJ1, Matrix.one_mul, Matrix.mul_assoc, WP.2, Matrix.mul_one]⟩
      left_inv := fun X => by
        apply Subtype.ext
        funext r i
        apply Prod.ext
        · show (((J.map Prod.fst)⁻¹ * (J.map Prod.fst * (U1 X.1)ᵀ))ᵀ) r i = (X.1 r i).1
          rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hJ1, Matrix.one_mul,
            Matrix.transpose_transpose]
          rfl
        · show (T.map Prod.fst * ((T.map Prod.fst)⁻¹ * V1 X.1)) r i = (X.1 r i).2
          rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hT1, Matrix.one_mul]
          rfl
      right_inv := fun WP => by
        apply Subtype.ext
        apply Prod.ext
        · show (T.map Prod.fst)⁻¹ * (T.map Prod.fst * WP.1.1) = WP.1.1
          rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hT1, Matrix.one_mul]
        · show J.map Prod.fst * (((J.map Prod.fst)⁻¹ * WP.1.2)ᵀ)ᵀ = WP.1.2
          rw [Matrix.transpose_transpose, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hJ1,
            Matrix.one_mul] }
  rw [Nat.card_congr e, card_pairs ha]

end FiniteFieldSplitting

theorem fFSplit_holds : FFSplit := by
  unfold FFSplit
  intro k _ _ M a ha J hJ hJd T hT hTd
  have h := FiniteFieldSplitting.fFSplit_nat M a ha J hJ hJd T hT hTd
  simp only [FiniteFieldSplitting.swapR] at h
  rw [h, Nat.cast_mul, Nat.cast_prod, Nat.cast_pow]
  congr 1
  refine Finset.prod_congr rfl (fun i _ => ?_)
  have h1 : 1 ≤ Nat.card k := Nat.card_pos
  have hi : (i : ℕ) ≤ M := by have := i.isLt; omega
  rw [Nat.cast_sub (Nat.pow_le_pow_right h1 hi), Nat.cast_pow, Nat.cast_pow]

end PI.VolStabS
end
end

noncomputable section

namespace PI.VolStabS

namespace FiniteFieldCounting

theorem prod_bound {ι : Type} (δ : ι → ℝ) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (h : ∀ j, |δ j| ≤ t) (s : Finset ι) :
    |∏ j ∈ s, (1 + δ j) - 1| ≤ t * (2 ^ s.card - 1) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
    have h1 : |∏ j ∈ s, (1 + δ j)| ≤ 1 + t * (2 ^ s.card - 1) := by
      have := abs_sub_abs_le_abs_sub (∏ j ∈ s, (1 + δ j)) 1
      rw [abs_one] at this
      linarith
    have hpow : (1 : ℝ) ≤ 2 ^ s.card := one_le_pow₀ (by norm_num)
    have h2 : |δ a * ∏ j ∈ s, (1 + δ j)| ≤ t * (1 + t * (2 ^ s.card - 1)) := by
      rw [abs_mul]
      exact mul_le_mul (h a) h1 (abs_nonneg _) ht0
    have h3 : (1 + δ a) * ∏ j ∈ s, (1 + δ j) - 1 =
        (∏ j ∈ s, (1 + δ j) - 1) + δ a * ∏ j ∈ s, (1 + δ j) := by ring
    rw [h3]
    have h4 : t * (t * (2 ^ s.card - 1)) ≤ t * (2 ^ s.card - 1) := by
      apply mul_le_mul_of_nonneg_left _ ht0
      nlinarith
    calc |(∏ j ∈ s, (1 + δ j) - 1) + δ a * ∏ j ∈ s, (1 + δ j)|
        ≤ |∏ j ∈ s, (1 + δ j) - 1| + |δ a * ∏ j ∈ s, (1 + δ j)| := abs_add_le _ _
      _ ≤ t * (2 ^ s.card - 1) + t * (1 + t * (2 ^ s.card - 1)) := add_le_add ih h2
      _ ≤ t * (2 ^ (s.card + 1) - 1) := by
          rw [pow_succ]
          nlinarith

theorem ratio_bound (M a : ℕ) (ha : a ≤ M) (q : ℝ) (hq : 1 ≤ q) (δ : Fin a → ℝ)
    (h : ∀ j, |δ j| ≤ (q⁻¹) ^ 2) : |∏ j, (1 + δ j) - 1| ≤ 2 ^ M * (q⁻¹) ^ 2 := by
  have hq0 : 0 ≤ q⁻¹ := inv_nonneg.mpr (by linarith)
  have hq1 : q⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hq
  have ht0 : 0 ≤ (q⁻¹) ^ 2 := by positivity
  have ht1 : (q⁻¹) ^ 2 ≤ 1 := pow_le_one₀ hq0 hq1
  have h1 := prod_bound δ _ ht0 ht1 h Finset.univ
  rw [Finset.card_univ, Fintype.card_fin] at h1
  have h2 : (2 : ℝ) ^ a ≤ 2 ^ M := pow_le_pow_right₀ (by norm_num) ha
  nlinarith

theorem inv_pow_le (q : ℝ) (hq : 1 ≤ q) (m : ℕ) (hm : 2 ≤ m) : (q⁻¹) ^ m ≤ (q⁻¹) ^ 2 := pow_le_pow_of_le_one (inv_nonneg.mpr (by linarith)) (inv_le_one_of_one_le₀ hq) hm

theorem exp_id (M a : ℕ) (ha : a ≤ M) : M * a + a * (M - a) = 2 * M * a - a ^ 2 := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le ha
  rw [Nat.add_sub_cancel_left]
  symm
  apply Nat.sub_eq_of_eq_add
  ring

theorem sum_exp (M : ℕ) : ∀ a, a ≤ M →
    ∑ j ∈ Finset.range a, (2 * (M - j) - 1) = 2 * M * a - a ^ 2 := by
  intro a
  induction a with
  | zero => intro _; simp
  | succ a ih =>
    intro ha
    rw [Finset.sum_range_succ, ih (by omega)]
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le ha
    have e1 : a + 1 + d - a = d + 1 := by omega
    rw [e1]
    have e2 : 2 * (a + 1 + d) * a - a ^ 2 = a ^ 2 + 2 * a * (d + 1) := by
      apply Nat.sub_eq_of_eq_add
      ring
    have e3 : 2 * (a + 1 + d) * (a + 1) - (a + 1) ^ 2 = (a + 1) ^ 2 + 2 * (a + 1) * d := by
      apply Nat.sub_eq_of_eq_add
      ring
    rw [e2, e3]
    have e4 : 2 * (d + 1) - 1 = 2 * d + 1 := by omega
    rw [e4]
    ring

theorem split_ratio (M a : ℕ) (ha : a ≤ M) (q : ℝ) (hq : q ≠ 0) :
    (∏ i : Fin a, (q ^ M - q ^ (i : ℕ))) * q ^ (a * (M - a)) / q ^ (2 * M * a - a ^ 2) =
      ∏ i : Fin a, (1 + -(q ^ (i : ℕ) / q ^ M)) := by
  have hqM : q ^ M ≠ 0 := pow_ne_zero _ hq
  rw [← exp_id M a ha, pow_add]
  have h1 : ∀ i : Fin a, q ^ M - q ^ (i : ℕ) = q ^ M * (1 + -(q ^ (i : ℕ) / q ^ M)) := by
    intro i
    field_simp
    ring
  simp_rw [h1]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]
  have hA : q ^ (M * a) ≠ 0 := pow_ne_zero _ hq
  have hB : q ^ (a * (M - a)) ≠ 0 := pow_ne_zero _ hq
  rw [mul_comm (q ^ (M * a)), mul_assoc, mul_div_assoc, div_self (mul_ne_zero hA hB), mul_one]

theorem inert_ratio (M a : ℕ) (ha : a ≤ M) (q : ℝ) (hq : q ≠ 0) :
    (∏ j : Fin a, (q ^ (2 * (M - j) - 1) - (-1) ^ (M - j) * q ^ (M - j - 1))) /
        q ^ (2 * M * a - a ^ 2) =
      ∏ j : Fin a, (1 + -((-1) ^ (M - j) * q ^ (M - j - 1) / q ^ (2 * (M - j) - 1))) := by
  have hs : ∑ j : Fin a, (2 * (M - (j : ℕ)) - 1) = 2 * M * a - a ^ 2 :=
    (Fin.sum_univ_eq_sum_range (fun j => 2 * (M - j) - 1) a).trans (sum_exp M a ha)
  have hden : q ^ (2 * M * a - a ^ 2) = ∏ j : Fin a, q ^ (2 * (M - (j : ℕ)) - 1) := by
    rw [Finset.prod_pow_eq_pow_sum, hs]
  rw [hden, ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  have hB : q ^ (2 * (M - (j : ℕ)) - 1) ≠ 0 := pow_ne_zero _ hq
  rw [sub_div, div_self hB]
  ring

theorem split_delta (M a : ℕ) (ha : a + 2 ≤ M) (q : ℝ) (hq : 1 ≤ q) (i : Fin a) :
    |-(q ^ (i : ℕ) / q ^ M)| ≤ (q⁻¹) ^ 2 := by
  have hq0 : 0 < q := by linarith
  have hi := i.isLt
  rw [abs_neg, abs_of_nonneg (div_nonneg (pow_nonneg hq0.le _) (pow_nonneg hq0.le _))]
  have hM : M = (i : ℕ) + (M - i) := by omega
  have h1 : q ^ (i : ℕ) / q ^ M = (q⁻¹) ^ (M - i) := by
    conv_lhs => rw [hM, pow_add]
    rw [div_mul_eq_div_div, div_self (pow_ne_zero _ hq0.ne'), inv_pow, one_div]
  rw [h1]
  exact inv_pow_le q hq (M - i) (by omega)

theorem inert_delta (M a : ℕ) (ha : a + 2 ≤ M) (q : ℝ) (hq : 1 ≤ q) (j : Fin a) :
    |-((-1) ^ (M - j) * q ^ (M - j - 1) / q ^ (2 * (M - j) - 1))| ≤ (q⁻¹) ^ 2 := by
  have hq0 : 0 < q := by linarith
  have hj := j.isLt
  rw [abs_neg, abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_pos (pow_pos hq0 _), abs_of_pos (pow_pos hq0 _)]
  have he : 2 * (M - (j : ℕ)) - 1 = (M - (j : ℕ) - 1) + (M - (j : ℕ)) := by omega
  rw [he, pow_add, div_mul_eq_div_div, div_self (pow_ne_zero _ hq0.ne'), one_div, ← inv_pow]
  exact inv_pow_le q hq _ (by omega)

theorem card_transport {k K : Type} [Field k] [CommRing K] [Algebra k K] (σ : K ≃ₐ[k] K)
    (e : K ≃ₐ[k] k × k) (he : ∀ x, e (σ x) = (e x).swap) {M a : ℕ}
    (J : Matrix (Fin M) (Fin M) K) (T : Matrix (Fin a) (Fin a) K) :
    Nat.card {X : Fin a → Fin M → K // ffGram (σ : K →+* K) J X = T} =
      Nat.card {Y : Fin a → Fin M → k × k //
        ffGram (FiniteFieldSplitting.swapR k) (J.map e) Y = T.map e} := by
  apply Nat.card_congr
  refine Equiv.subtypeEquiv (Equiv.piCongrRight fun _ => Equiv.piCongrRight fun _ => e.toEquiv) ?_
  intro X
  have key : ffGram (FiniteFieldSplitting.swapR k) (J.map e)
      ((Equiv.piCongrRight fun _ => Equiv.piCongrRight fun _ => e.toEquiv) X) =
        (ffGram (σ : K →+* K) J X).map e := by
    funext i j
    show ∑ a', ∑ b, (e (X i a')).swap * e (J a' b) * e (X j b) =
      e (∑ a', ∑ b, σ (X i a') * J a' b * X j b)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun a' _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [map_mul, map_mul, he]
  rw [key]
  constructor
  · intro h
    rw [h]
  · intro h
    ext i j
    exact e.injective (congrFun (congrFun h i) j)

end FiniteFieldCounting

theorem fFCount_of (hS : FFSplit) (hI : FFInert) : FFCount := by
  intro M
  refine ⟨2 ^ M, ?_⟩
  intro k K _ _ _ _ σ hσ h2 J hJ hJd a ha T hT hTd
  have hq1 : (1 : ℝ) ≤ (Nat.card k : ℝ) := by exact_mod_cast Nat.card_pos
  have hq0 : (Nat.card k : ℝ) ≠ 0 := by linarith
  have haM : a ≤ M := by omega
  rcases hσ.2 with ⟨hF, hrank, hne⟩ | ⟨e, he⟩
  · letI : Field K := hF.toField
    have hc := hI k K σ hσ.1 hrank hne h2 M a haM J hJ hJd T hT hTd
    rw [hc, FiniteFieldCounting.inert_ratio M a haM _ hq0]
    exact FiniteFieldCounting.ratio_bound M a haM _ hq1 _ (fun j => FiniteFieldCounting.inert_delta M a ha _ hq1 j)
  · have hc := FiniteFieldCounting.card_transport σ e he J T
    have hJ' : ∀ i j, ((J.map e) j i).swap = (J.map e) i j := by
      intro i j
      simp only [Matrix.map_apply]
      rw [← he, hJ]
    have hT' : ∀ i j, ((T.map e) j i).swap = (T.map e) i j := by
      intro i j
      simp only [Matrix.map_apply]
      rw [← he, hT]
    have hJd' : IsUnit (J.map e).det := by
      have h := hJd.map (e : K →+* k × k)
      rwa [RingHom.map_det] at h
    have hTd' : IsUnit (T.map e).det := by
      have h := hTd.map (e : K →+* k × k)
      rwa [RingHom.map_det] at h
    have hs : (Nat.card {Y : Fin a → Fin M → k × k //
        ffGram (FiniteFieldSplitting.swapR k) (J.map e) Y = T.map e} : ℝ) =
        (∏ i : Fin a, ((Nat.card k : ℝ) ^ M - (Nat.card k : ℝ) ^ (i : ℕ))) *
          (Nat.card k : ℝ) ^ (a * (M - a)) := hS k M a haM (J.map e) hJ' hJd' (T.map e) hT' hTd'
    rw [hc, hs, FiniteFieldCounting.split_ratio M a haM _ hq0]
    exact FiniteFieldCounting.ratio_bound M a haM _ hq1 _ (fun i => FiniteFieldCounting.split_delta M a ha _ hq1 i)

theorem fFCount_of_inert (hI : FFInert) : FFCount := fFCount_of fFSplit_holds hI

end PI.VolStabS
end
end

namespace PI.VolStabS

theorem fFCount_holds : FFCount := fFCount_of_inert FFHS.fFInert_holds

end PI.VolStabS
end

namespace PI.VolStabS

theorem densAA_of_open (hV : VolAA) (hH : HensAA) (hI : IdxH) (hC : CntAA) : DensAA :=
  densAA_of fibLat_holds fFCount_holds
    (resAA_of hV latFacts_holds hH (idxAA_of idxL_holds hI) hC)

end PI.VolStabS
