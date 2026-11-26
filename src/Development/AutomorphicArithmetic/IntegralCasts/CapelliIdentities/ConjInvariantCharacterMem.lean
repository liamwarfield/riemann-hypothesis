module

public import Mathlib

@[expose] public section

/-!
# Topology of `R`-Points of a Unitary Group `H(R) ⊆ GL_M(R ⊗_F E)`

Defines the twisted transpose `cT`, the unitary subgroup `UJ σ J = {g | cT σ g * J * g = J}`,
its base change `HR R σ J` / `HA R σ J` over a topological `F`-algebra `R` with the
module topology `topTens` on `R ⊗_F E`, and proves that when `R` is a locally compact,
second-countable, Hausdorff topological ring and `E / F` is finite-dimensional, `HA R σ J`
is locally compact, second-countable, and Hausdorff (`lcsc_HA`).
-/

noncomputable def UpperTheory.Reformulated.B.Yzd4.cT
    {A : Type} [CommRing A] (σ : A →+* A) {m p : Type} (M : Matrix m p A) : Matrix p m A :=
  (M.map ⇑σ).transpose

private theorem cT_mul {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]
    (σ : A →+* A) (a b : Matrix n n A) :
    UpperTheory.Reformulated.B.Yzd4.cT σ (a * b) =
      UpperTheory.Reformulated.B.Yzd4.cT σ b * UpperTheory.Reformulated.B.Yzd4.cT σ a := by
  simp only [UpperTheory.Reformulated.B.Yzd4.cT]
  rw [Matrix.map_mul, Matrix.transpose_mul]

private theorem cT_one {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]
    (σ : A →+* A) : UpperTheory.Reformulated.B.Yzd4.cT σ (1 : Matrix n n A) = 1 := by
  simp only [UpperTheory.Reformulated.B.Yzd4.cT]
  rw [Matrix.map_one _ (map_zero σ) (map_one σ), Matrix.transpose_one]

theorem UpperTheory.Reformulated.B.Yzd4.aux2
    {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]
    (σ : A →+* A) (J : Matrix n n A) {a b : GL n A}
    (ha : a ∈ {g : GL n A | UpperTheory.Reformulated.B.Yzd4.cT σ (g : Matrix n n A) * J * g = J})
    (hb : b ∈ {g : GL n A | UpperTheory.Reformulated.B.Yzd4.cT σ (g : Matrix n n A) * J * g = J}) :
    a * b ∈ {g : GL n A | UpperTheory.Reformulated.B.Yzd4.cT σ (g : Matrix n n A) * J * g = J} := by
  have ha' : UpperTheory.Reformulated.B.Yzd4.cT σ (a : Matrix n n A) * J * (a : Matrix n n A) = J := ha
  have hb' : UpperTheory.Reformulated.B.Yzd4.cT σ (b : Matrix n n A) * J * (b : Matrix n n A) = J := hb
  change UpperTheory.Reformulated.B.Yzd4.cT σ ((a * b : GL n A) : Matrix n n A) * J *
    ((a * b : GL n A) : Matrix n n A) = J
  rw [Units.val_mul, cT_mul]
  calc _ = UpperTheory.Reformulated.B.Yzd4.cT σ (b : Matrix n n A) *
        (UpperTheory.Reformulated.B.Yzd4.cT σ (a : Matrix n n A) * J * (a : Matrix n n A)) * (b : Matrix n n A) := by
        simp only [Matrix.mul_assoc]
    _ = J := by rw [ha', hb']

theorem UpperTheory.Reformulated.B.Yzd4.aux3
    {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]
    (σ : A →+* A) (J : Matrix n n A) :
    UpperTheory.Reformulated.B.Yzd4.cT σ ((1 : GL n A) : Matrix n n A) * J *
      ((1 : GL n A) : Matrix n n A) = J := by
  rw [Units.val_one, cT_one, Matrix.one_mul, Matrix.mul_one]

theorem UpperTheory.Reformulated.B.Yzd4.aux4
    {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]
    (σ : A →+* A) (J : Matrix n n A) {g : GL n A}
    (hg : g ∈ {g : GL n A | UpperTheory.Reformulated.B.Yzd4.cT σ (g : Matrix n n A) * J * g = J}) :
    g⁻¹ ∈ {g : GL n A | UpperTheory.Reformulated.B.Yzd4.cT σ (g : Matrix n n A) * J * g = J} := by
  have hg' : UpperTheory.Reformulated.B.Yzd4.cT σ (g : Matrix n n A) * J * (g : Matrix n n A) = J := hg
  change UpperTheory.Reformulated.B.Yzd4.cT σ ((g⁻¹ : GL n A) : Matrix n n A) * J *
    ((g⁻¹ : GL n A) : Matrix n n A) = J
  have h1 : (g : Matrix n n A) * ((g⁻¹ : GL n A) : Matrix n n A) = 1 :=
    Units.mul_inv g
  have h2 : UpperTheory.Reformulated.B.Yzd4.cT σ ((g⁻¹ : GL n A) : Matrix n n A) *
      UpperTheory.Reformulated.B.Yzd4.cT σ (g : Matrix n n A) = 1 := by
    rw [← cT_mul, h1, cT_one]
  calc _ = UpperTheory.Reformulated.B.Yzd4.cT σ ((g⁻¹ : GL n A) : Matrix n n A) *
        (UpperTheory.Reformulated.B.Yzd4.cT σ (g : Matrix n n A) * J * (g : Matrix n n A)) *
        ((g⁻¹ : GL n A) : Matrix n n A) := by rw [hg']
    _ = (UpperTheory.Reformulated.B.Yzd4.cT σ ((g⁻¹ : GL n A) : Matrix n n A) *
        UpperTheory.Reformulated.B.Yzd4.cT σ (g : Matrix n n A)) * J *
        ((g : Matrix n n A) * ((g⁻¹ : GL n A) : Matrix n n A)) := by
        simp only [Matrix.mul_assoc]
    _ = J := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]

noncomputable def UpperTheory.Reformulated.B.Yzd4.UJ
    {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]
    (σ : A →+* A) (J : Matrix n n A) : Subgroup (GL n A) where
  carrier := {g : GL n A | UpperTheory.Reformulated.B.Yzd4.cT σ (g : Matrix n n A) * J * g = J}
  mul_mem' := UpperTheory.Reformulated.B.Yzd4.aux2 σ J
  one_mem' := UpperTheory.Reformulated.B.Yzd4.aux3 σ J
  inv_mem' := UpperTheory.Reformulated.B.Yzd4.aux4 σ J

theorem UpperTheory.Reformulated.B.Yzd4.aux6
    {F : Type} [Field F] (R : Type) [CommRing R] [Algebra F R] :
    SMulCommClass F F R :=
  inferInstance

theorem UpperTheory.Reformulated.B.Yzd4.aux7
    {F : Type} [Field F] (R : Type) [CommRing R] [Algebra F R] :
    IsScalarTower F F R :=
  inferInstance

noncomputable def UpperTheory.Reformulated.B.Yzd4.sigR
    {F E : Type} [Field F] [Field E] [Algebra F E]
    (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) :
    TensorProduct F R E →+* TensorProduct F R E :=
  (Algebra.TensorProduct.map (AlgHom.id F R) σ).toRingHom

theorem UpperTheory.Reformulated.B.Yzd4.aux9
    {F : Type} [Field F] (R : Type) [CommRing R] [Algebra F R] :
    SMulCommClass F R R :=
  inferInstance

theorem UpperTheory.Reformulated.B.Yzd4.laurent_T_neg_one_mul_T_one
    {F : Type} [Field F] (R : Type) [CommRing R] [Algebra F R] :
    IsScalarTower F R R :=
  inferInstance

theorem UpperTheory.Reformulated.B.Yzd4.aux11
    {F E : Type} [Field F] [Field E] [Algebra F E] :
    SMulCommClass F E E :=
  inferInstance

theorem UpperTheory.Reformulated.B.Yzd4.aux12
    {F E : Type} [Field F] [Field E] [Algebra F E] :
    IsScalarTower F E E :=
  inferInstance

noncomputable def UpperTheory.Reformulated.B.Yzd4.inclR
    {F E : Type} [Field F] [Field E] [Algebra F E]
    (R : Type) [CommRing R] [Algebra F R] : E →+* TensorProduct F R E :=
  Algebra.TensorProduct.includeRight.toRingHom

noncomputable def UpperTheory.Reformulated.B.Yzd4.JR
    {F E : Type} [Field F] [Field E] [Algebra F E]
    (R : Type) [CommRing R] [Algebra F R] {M : ℕ} (J : Matrix (Fin M) (Fin M) E) :
    Matrix (Fin M) (Fin M) (TensorProduct F R E) :=
  J.map ⇑(UpperTheory.Reformulated.B.Yzd4.inclR R)

noncomputable def UpperTheory.Reformulated.B.Yzd4.HR
    {F E : Type} [Field F] [Field E] [Algebra F E]
    (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E)
    {M : ℕ} (J : Matrix (Fin M) (Fin M) E) :
    Subgroup (GL (Fin M) (TensorProduct F R E)) :=
  UpperTheory.Reformulated.B.Yzd4.UJ (UpperTheory.Reformulated.B.Yzd4.sigR R σ)
    (UpperTheory.Reformulated.B.Yzd4.JR R J)

noncomputable def UpperTheory.Reformulated.B.Yzd4.HA
    {F E : Type} [Field F] [Field E] [Algebra F E]
    (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E)
    {M : ℕ} (J : Matrix (Fin M) (Fin M) E) : Type :=
  ↥(UpperTheory.Reformulated.B.Yzd4.HR R σ J)

noncomputable def UpperTheory.Reformulated.B.Yzd4.topTens
    {F E : Type} [Field F] [Field E] [Algebra F E]
    (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] :
    TopologicalSpace (TensorProduct F R E) :=
  moduleTopology R (TensorProduct F R E)

noncomputable def UpperTheory.Reformulated.B.Yzd4.d18
    {F E : Type} [Field F] [Field E] [Algebra F E]
    (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E)
    {M : ℕ} (J : Matrix (Fin M) (Fin M) E) [TopologicalSpace R]
    (s : Set (UpperTheory.Reformulated.B.Yzd4.HA R σ J)) : Prop :=
  letI : TopologicalSpace (TensorProduct F R E) := UpperTheory.Reformulated.B.Yzd4.topTens R
  ∃ t : Set (GL (Fin M) (TensorProduct F R E)), IsOpen t ∧ Subtype.val ⁻¹' t = s

theorem UpperTheory.Reformulated.B.Yzd4.blockM_one_partner_eq_one
    {F E : Type} [Field F] [Field E] [Algebra F E]
    (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E)
    {M : ℕ} (J : Matrix (Fin M) (Fin M) E) [TopologicalSpace R] :
    UpperTheory.Reformulated.B.Yzd4.d18 R σ J Set.univ := by
  letI : TopologicalSpace (TensorProduct F R E) := UpperTheory.Reformulated.B.Yzd4.topTens R
  exact ⟨Set.univ, isOpen_univ, rfl⟩

theorem UpperTheory.Reformulated.B.Yzd4.blockM_mul_alt
    {F E : Type} [Field F] [Field E] [Algebra F E]
    (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E)
    {M : ℕ} (J : Matrix (Fin M) (Fin M) E) [TopologicalSpace R]
    (s t : Set (UpperTheory.Reformulated.B.Yzd4.HA R σ J))
    (hs : UpperTheory.Reformulated.B.Yzd4.d18 R σ J s)
    (ht : UpperTheory.Reformulated.B.Yzd4.d18 R σ J t) :
    UpperTheory.Reformulated.B.Yzd4.d18 R σ J (s ∩ t) := by
  letI : TopologicalSpace (TensorProduct F R E) := UpperTheory.Reformulated.B.Yzd4.topTens R
  obtain ⟨a, ha, rfl⟩ := hs
  obtain ⟨b, hb, rfl⟩ := ht
  exact ⟨a ∩ b, ha.inter hb, rfl⟩

theorem UpperTheory.Reformulated.B.Yzd4.conj_invariant_character_mem
    {F E : Type} [Field F] [Field E] [Algebra F E]
    (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E)
    {M : ℕ} (J : Matrix (Fin M) (Fin M) E) [TopologicalSpace R]
    (s : Set (Set (UpperTheory.Reformulated.B.Yzd4.HA R σ J)))
    (hs : ∀ t ∈ s, UpperTheory.Reformulated.B.Yzd4.d18 R σ J t) :
    UpperTheory.Reformulated.B.Yzd4.d18 R σ J (⋃₀ s) := by
  letI : TopologicalSpace (TensorProduct F R E) := UpperTheory.Reformulated.B.Yzd4.topTens R
  refine ⟨⋃₀ {u : Set (Matrix.GeneralLinearGroup (Fin M) (TensorProduct F R E)) |
    IsOpen u ∧ Subtype.val ⁻¹' u ∈ s}, isOpen_sUnion (fun u hu => hu.1), ?_⟩
  ext x
  simp only [Set.mem_preimage, Set.mem_sUnion]
  constructor
  · rintro ⟨u, ⟨_, hu⟩, hx⟩
    exact ⟨_, hu, hx⟩
  · rintro ⟨t, ht, hx⟩
    obtain ⟨u, hu, rfl⟩ := hs t ht
    exact ⟨u, ⟨hu, ht⟩, hx⟩

@[reducible] noncomputable def UpperTheory.Reformulated.B.Yzd4.instTopologicalSpaceHA
    {F E : Type} [Field F] [Field E] [Algebra F E]
    (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E)
    {M : ℕ} (J : Matrix (Fin M) (Fin M) E) [TopologicalSpace R] :
    TopologicalSpace (UpperTheory.Reformulated.B.Yzd4.HA R σ J) where
  IsOpen := UpperTheory.Reformulated.B.Yzd4.d18 R σ J
  isOpen_univ := UpperTheory.Reformulated.B.Yzd4.blockM_one_partner_eq_one R σ J
  isOpen_inter := UpperTheory.Reformulated.B.Yzd4.blockM_mul_alt R σ J
  isOpen_sUnion := UpperTheory.Reformulated.B.Yzd4.conj_invariant_character_mem R σ J

attribute [local instance] UpperTheory.Reformulated.B.Yzd4.instTopologicalSpaceHA

private theorem closed_UJ {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [T2Space A] {n : Type} [Fintype n] [DecidableEq n] (σ : A →+* A) (hσ : Continuous σ)
    (J : Matrix n n A) :
    IsClosed ((UpperTheory.Reformulated.B.Yzd4.UJ σ J : Subgroup (Matrix.GeneralLinearGroup n A)) :
      Set (Matrix.GeneralLinearGroup n A)) := by
  have hv : Continuous (fun g : Matrix.GeneralLinearGroup n A => (g : Matrix n n A)) :=
    Units.continuous_val
  have hc : Continuous (fun g : Matrix.GeneralLinearGroup n A =>
      UpperTheory.Reformulated.B.Yzd4.cT σ (g : Matrix n n A) * J * (g : Matrix n n A)) := by
    simp only [UpperTheory.Reformulated.B.Yzd4.cT]
    exact ((hv.matrix_map hσ).matrix_transpose.matrix_mul continuous_const).matrix_mul hv
  exact isClosed_eq hc continuous_const

private theorem lcsc_GL {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [T2Space A] [LocallyCompactSpace A] [SecondCountableTopology A] {n : Type} [Fintype n]
    [DecidableEq n] :
    LocallyCompactSpace (Matrix.GeneralLinearGroup n A) ∧
      SecondCountableTopology (Matrix.GeneralLinearGroup n A) ∧
      T2Space (Matrix.GeneralLinearGroup n A) := by
  haveI : LocallyCompactSpace (Matrix n n A) := inferInstanceAs (LocallyCompactSpace (n → n → A))
  haveI : SecondCountableTopology (Matrix n n A) :=
    inferInstanceAs (SecondCountableTopology (n → n → A))
  haveI : SecondCountableTopology (Matrix n n A)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  have he : Topology.IsClosedEmbedding (Units.embedProduct (Matrix n n A)) :=
    Units.isClosedEmbedding_embedProduct
  exact ⟨he.locallyCompactSpace, he.isEmbedding.secondCountableTopology, he.isEmbedding.t2Space⟩

private theorem lcsc_sub {G : Type} [Group G] [TopologicalSpace G] (H : Subgroup G)
    (hH : IsClosed (H : Set G)) [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] :
    LocallyCompactSpace H ∧ SecondCountableTopology H ∧ T2Space H :=
  ⟨hH.isClosedEmbedding_subtypeVal.locallyCompactSpace,
    Topology.IsEmbedding.subtypeVal.secondCountableTopology, inferInstance⟩

private theorem props_of_free {R D : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R] [Ring D] [Algebra R D]
    {ι : Type} [Fintype ι] (B : Module.Basis ι R D) [Module.Finite R D] [TopologicalSpace D]
    [IsModuleTopology R D] :
    IsTopologicalRing D ∧ LocallyCompactSpace D ∧ SecondCountableTopology D ∧ T2Space D := by
  have hr := IsModuleTopology.isTopologicalRing R D
  haveI := IsModuleTopology.toContinuousAdd R D
  let e := B.equivFun
  have c1 : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
  have c2 : Continuous e.symm := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap
  let h : D ≃ₜ (ι → R) := { toEquiv := e.toEquiv, continuous_toFun := c1, continuous_invFun := c2 }
  exact ⟨hr, h.isClosedEmbedding.locallyCompactSpace, h.isEmbedding.secondCountableTopology,
    h.isEmbedding.t2Space⟩

private theorem tens_props (F E : Type) [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
    [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R]
    [TopologicalSpace (TensorProduct F R E)] [IsModuleTopology R (TensorProduct F R E)] :
    IsTopologicalRing (TensorProduct F R E) ∧ LocallyCompactSpace (TensorProduct F R E) ∧
      SecondCountableTopology (TensorProduct F R E) ∧ T2Space (TensorProduct F R E) :=
  props_of_free (Algebra.TensorProduct.basis R (Module.finBasis F E))

private theorem sigR_continuous {F E : Type} [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R]
    [IsTopologicalRing R] [TopologicalSpace (TensorProduct F R E)]
    [IsModuleTopology R (TensorProduct F R E)] (σ : E →ₐ[F] E) :
    Continuous (UpperTheory.Reformulated.B.Yzd4.sigR R σ) := by
  haveI := IsModuleTopology.toContinuousAdd R (TensorProduct F R E)
  have h : (⇑(UpperTheory.Reformulated.B.Yzd4.sigR R σ) : TensorProduct F R E → TensorProduct F R E) =
      ⇑(LinearMap.baseChange R σ.toLinearMap) := by
    funext x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [UpperTheory.Reformulated.B.Yzd4.sigR]
    | add a b ha hb => simp [map_add (f := _), ha, hb]
  rw [h]
  exact IsModuleTopology.continuous_of_linearMap _

theorem UpperTheory.Reformulated.B.Yzd4.lcsc_HA
    {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R]
    [IsTopologicalRing R] [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R]
    (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) :
    LocallyCompactSpace (UpperTheory.Reformulated.B.Yzd4.HA R σ J) ∧
      SecondCountableTopology (UpperTheory.Reformulated.B.Yzd4.HA R σ J) ∧
        T2Space (UpperTheory.Reformulated.B.Yzd4.HA R σ J) := by
  letI τ : TopologicalSpace (TensorProduct F R E) := UpperTheory.Reformulated.B.Yzd4.topTens R
  haveI hm : IsModuleTopology R (TensorProduct F R E) := ⟨rfl⟩
  obtain ⟨h1, h2, h3, h4⟩ := tens_props F E R
  haveI := h1
  haveI := h2
  haveI := h3
  haveI := h4
  obtain ⟨g1, g2, g3⟩ := lcsc_GL (A := TensorProduct F R E) (n := Fin M)
  haveI := g1
  haveI := g2
  haveI := g3
  have hc := closed_UJ (UpperTheory.Reformulated.B.Yzd4.sigR R σ) (sigR_continuous R σ)
    (UpperTheory.Reformulated.B.Yzd4.JR R J)
  exact lcsc_sub _ hc
