module

public import Development.AutomorphicArithmetic.Foundations.Convolution.TensFun
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.ClosedProperAlt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTwistedClassesCharpoly
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.HeckeRepresentationSatake

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.TensSmooth
noncomputable section

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Geo
open scoped ComplexConjugate

namespace UpperTheory.ConvolutionTheory.L1

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

abbrev InfD (σ : E ≃ₐ[F] E) (m : ℕ) : Type :=
  Split (GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap (K := F) (L := E)) (galInf σ) m

variable {σ : E ≃ₐ[F] E} {m : ℕ}

def compA (D : InfD σ m) (n : ℕ) (i : Fin (m + 1)) : archGroup E n →* archGroup F n :=
  (archEquiv F n).toMonoidHom.comp ((D.comp n i).comp (archEquiv E n).symm.toMonoidHom)

def glueA (D : InfD σ m) (n : ℕ) (g : Fin (m + 1) → archGroup F n) : archGroup E n :=
  archEquiv E n (D.glue n fun i => (archEquiv F n).symm (g i))

def IsTens (D : InfD σ m) {n : ℕ} (φ : Fin (m + 1) → TI F n) (β : TI E n) : Prop := ∀ g, β g = ∏ i, φ i (compA D n i g)

def IsBlockElement (D : InfD σ m) (n : ℕ) (s : Fin (m + 1) → archGroup F n →* archGroup E n) : Prop :=
  ∀ i g, s i g = glueA D n (Pi.mulSingle i g)

def InSlot (D : InfD σ m) (τ : E →+* ℂ) (k : Fin (m + 1)) : Prop :=
  ∀ z : ℂ, (InfiniteAdeleRing.ringEquiv_mixedSpace E).symm (along τ z) =
    D.e.symm (Pi.single k ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (along (τ.comp (algebraMap F E)) z)))

structure ArchSlot (D : InfD σ m) {n : ℕ} (νE : Measure (archGroup E n)) (νF : Measure (archGroup F n)) (b a : TI F n)
    (aE : TI E n) (aF : TI F n) : Prop where
  meas : νE = Measure.map (glueA D n) (Measure.pi fun _ => νF)
  smooth : SmoothT b
  fin : LeftFin b
  norm : ∫ g, ‖b g‖ ∂νF ≤ 1
  sq : ∀ g, a g = cv νF b (fun x => conj (b x⁻¹)) g
  tens : IsTens D (fun _ => a) aE
  pow : ∀ g, aF g = cvPow νF a m g

end

def ArchBasic : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E ≃ₐ[F] E) (m : ℕ) (D : InfD σ m) (n : ℕ),
    (∀ g i, compA D n i (glueA D n g) = g i) ∧ (∀ x, glueA D n (fun i => compA D n i x) = x) ∧
    (∀ g h, glueA D n (g * h) = glueA D n g * glueA D n h) ∧ Continuous (glueA D n) ∧ (∀ i, Continuous (compA D n i)) ∧
    (∃ s, IsBlockElement D n s ∧ ∀ i, Continuous (s i)) ∧
    (∀ (νF : Measure (archGroup F n)) [νF.IsHaarMeasure], (Measure.map (glueA D n) (Measure.pi fun _ => νF)).IsHaarMeasure) ∧
    ∀ φ : Fin (m + 1) → TI F n, ∃ β, IsTens D φ β

def PositionOf : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [_root_.NumberField.IsTotallyComplex F] (σ : E ≃ₐ[F] E) (m : ℕ)
    (D : InfD σ m), (∀ τ, ∃ k, InSlot D τ k) ∧
      ∀ (n : ℕ) (g : archGroup E n), g ∈ archCompact E n ↔ ∀ i, compA D n i g ∈ archCompact F n

def TensSmooth : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [_root_.NumberField.IsTotallyComplex F] (σ : E ≃ₐ[F] E) (m : ℕ)
    (D : InfD σ m) (n : ℕ) (φ : Fin (m + 1) → TI F n) (β : TI E n), IsTens D φ β →
    ((∀ i, SmoothT (φ i)) → SmoothT β) ∧ ((∀ i, LeftFin (φ i)) → LeftFin β)

def JUnique : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] (n : ℕ) (τ : K →+* ℂ),
    (∃! j, IsJ (n := n) τ j) ∧ ∀ i : Fin n, zc τ i ∈ Subalgebra.center ℂ (UC K n)

def LactLaws : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (β : TI K n), SmoothT β →
    (∀ u, SmoothT (lact u β)) ∧ lact 1 β = β ∧ (∀ u v, lact (u * v) β = lact u (lact v β)) ∧
      (∀ u v, lact (u + v) β = lact u β + lact v β) ∧ ∀ (c : ℂ) u, lact (c • u) β = c • lact u β

def LactGen : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [_root_.NumberField.IsTotallyComplex F] (σ : E ≃ₐ[F] E) (m : ℕ)
    (D : InfD σ m) (n : ℕ) (τ : E →+* ℂ) (k : Fin (m + 1)), InSlot D τ k → ∀ (φ : Fin (m + 1) → TI F n) (β : TI E n),
    (∀ i, SmoothT (φ i)) → IsTens D φ β → ∀ (p q : Fin n) (z : ℂ),
      IsTens D (Function.update φ k (lact ((1 : ℂ) ⊗ₜ elem (τ.comp (algebraMap F E)) p q z) (φ k))) (lact ((1 : ℂ) ⊗ₜ elem τ p q z) β)

def LactTens : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [_root_.NumberField.IsTotallyComplex F] [_root_.NumberField.IsTotallyComplex E]
    (σ : E ≃ₐ[F] E) (m : ℕ) (D : InfD σ m) (n : ℕ) (τ : E →+* ℂ) (k : Fin (m + 1)), InSlot D τ k →
    ∀ (φ : Fin (m + 1) → TI F n) (β : TI E n), (∀ i, SmoothT (φ i)) → IsTens D φ β → ∀ i : Fin n,
      IsTens D (Function.update φ k (lact (zc (τ.comp (algebraMap F E)) i) (φ k))) (lact (zc τ i) β)

def LactCv : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] (n : ℕ) (ν : Measure (archGroup K n)) [ν.IsHaarMeasure]
    (α β γ : TI K n), SmoothT α → (∀ g, γ g = cv ν α β g) → SmoothT γ ∧ (LeftFin α → LeftFin γ) ∧
      (∀ u g, lact u γ g = cv ν (lact u α) β g) ∧
      (SmoothT β → ∀ z ∈ Subalgebra.center ℂ (UC K n), ∀ g, lact z γ g = cv ν α (lact z β) g)

def TensOp : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E ≃ₐ[F] E) (m : ℕ) (D : InfD σ m) (n : ℕ)
    (νE : Measure (archGroup E n)) [νE.IsHaarMeasure] (νF : Measure (archGroup F n)) [νF.IsHaarMeasure],
    νE = Measure.map (glueA D n) (Measure.pi fun _ => νF) →
    ∀ (s : Fin (m + 1) → archGroup F n →* archGroup E n) (hs : ∀ i, Continuous (s i)), IsBlockElement D n s →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : UnitaryRep (archGroup E n) H)
      (φ : Fin (m + 1) → TI F n) (β : TI E n), IsTens D φ β →
      π.integrated νE (UnitaryRep.ccToL1 νE β) =
        (List.ofFn fun i => (π.compHom (s i) (hs i)).integrated νF (UnitaryRep.ccToL1 νF (φ i))).prod

def SqOp : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (ν : Measure (archGroup K n)) [ν.IsHaarMeasure] (b a aF : TI K n) (m : ℕ),
    (∀ g, a g = cv ν b (fun x => conj (b x⁻¹)) g) → (∀ g, aF g = cvPow ν a m g) → ∫ g, ‖b g‖ ∂ν ≤ 1 →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : UnitaryRep (archGroup K n) H),
      π.integrated ν (UnitaryRep.ccToL1 ν a) =
          π.integrated ν (UnitaryRep.ccToL1 ν b) * star (π.integrated ν (UnitaryRep.ccToL1 ν b)) ∧
        0 ≤ π.integrated ν (UnitaryRep.ccToL1 ν a) ∧ ‖π.integrated ν (UnitaryRep.ccToL1 ν a)‖ ≤ 1 ∧
        π.integrated ν (UnitaryRep.ccToL1 ν aF) = π.integrated ν (UnitaryRep.ccToL1 ν a) ^ (m + 1)

def ArchSlotEx : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E ≃ₐ[F] E) (m : ℕ) (D : InfD σ m) (n : ℕ)
    (νF : Measure (archGroup F n)) [νF.IsHaarMeasure] (b : TI F n), SmoothT b → LeftFin b → ∫ g, ‖b g‖ ∂νF ≤ 1 →
    ∃ (νE : Measure (archGroup E n)) (_ : νE.IsHaarMeasure) (a : TI F n) (aE : TI E n) (aF : TI F n), ArchSlot D νE νF b a aE aF

def BumpEx : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (ν : Measure (archGroup K n)) [ν.IsHaarMeasure]
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : UnitaryRep (archGroup K n) H) (v : H), v ≠ 0 →
    ∃ b : TI K n, SmoothT b ∧ LeftFin b ∧ ∫ g, ‖b g‖ ∂ν ≤ 1 ∧ star (π.integrated ν (UnitaryRep.ccToL1 ν b)) v ≠ 0

end UpperTheory.ConvolutionTheory.L1
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.GlueBasic
noncomputable section

open PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.Tf.Geo
open scoped Fin.NatCast Fin.CommRing

namespace UpperTheory.ConvolutionTheory.L1

section SlopeTestRemainingChoices

variable {R S : Type} [CommRing R] [CommRing S] [TopologicalSpace R] [TopologicalSpace S]
  {ι : R →+* S} {s : S →+* S} {m : ℕ} (D : Split ι s m) (n : ℕ)

private theorem comp_apply (i : Fin (m + 1)) (x : GL (Fin n) S) (a b : Fin n) :
    (D.comp n i x : Matrix (Fin n) (Fin n) R) a b = D.e ((x : Matrix (Fin n) (Fin n) S) a b) i := rfl

private theorem comp_glue (g : Fin (m + 1) → GL (Fin n) R) (i : Fin (m + 1)) :
    D.comp n i (D.glue n g) = g i := by
  apply Units.ext
  ext a b
  rw [comp_apply]
  show D.e (D.e.symm fun i => (g i : Matrix (Fin n) (Fin n) R) a b) i = _
  simp

private theorem glue_comp (x : GL (Fin n) S) : D.glue n (fun i => D.comp n i x) = x := by
  apply Units.ext
  ext a b
  show D.e.symm (fun i => (D.comp n i x : Matrix (Fin n) (Fin n) R) a b) = _
  simp only [comp_apply]
  exact D.e.symm_apply_apply _

private theorem comp_inj {x y : GL (Fin n) S} (h : ∀ i, D.comp n i x = D.comp n i y) : x = y := by
  rw [← glue_comp D n x, ← glue_comp D n y]
  exact congrArg _ (funext h)

private theorem comp_diag (t : GL (Fin n) R) (i : Fin (m + 1)) : D.comp n i (mapGL n ι t) = t := by
  apply Units.ext
  ext a b
  rw [comp_apply]
  exact D.map_diag _ i

private theorem comp_shift (x : GL (Fin n) S) (i : Fin (m + 1)) :
    D.comp n i (mapGL n s x) = D.comp n (i + 1) x := by
  apply Units.ext
  ext a b
  rw [comp_apply, comp_apply]
  exact D.map_shift _ i

private theorem comp_pow (θ : Monoid.End (GL (Fin n) S)) (hθ : ∀ x, θ x = mapGL n s x) (k : ℕ)
    (x : GL (Fin n) S) (i : Fin (m + 1)) :
    D.comp n i ((θ ^ k) x) = D.comp n (i + (k : Fin (m + 1))) x := by
  induction k generalizing i with
  | zero => simp
  | succ k ih =>
    rw [pow_succ']
    show D.comp n i (θ ((θ ^ k) x)) = _
    rw [hθ, comp_shift, ih]
    congr 1
    push_cast
    abel_nf

private theorem ofFn_range {G : Type} [Monoid G] (k : ℕ) (f : ℕ → G) :
    (List.ofFn fun i : Fin k => f i).prod = ((List.range k).map f).prod := by
  congr 1
  apply List.ext_getElem <;> simp

private theorem comp_twNorm (θ : Monoid.End (GL (Fin n) S)) (hθ : ∀ x, θ x = mapGL n s x)
    (δ : GL (Fin n) S) (j : Fin (m + 1)) :
    D.comp n j (twNorm θ (m + 1) δ) = (List.ofFn fun i => D.comp n (j + i) δ).prod := by
  have hh : (fun i : Fin (m + 1) => D.comp n (j + i) δ) =
      fun i : Fin (m + 1) => (fun k : ℕ => D.comp n (j + (k : Fin (m + 1))) δ) i := by
    funext i
    simp only [Fin.cast_val_eq_self]
  rw [hh, ofFn_range (m + 1) (fun k : ℕ => D.comp n (j + (k : Fin (m + 1))) δ), twNorm, map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro k _
  exact comp_pow D n θ hθ k δ j

private theorem entry {T : Type} [CommRing T] [TopologicalSpace T] (a b : Fin n) :
    Continuous fun x : GL (Fin n) T => (x : Matrix (Fin n) (Fin n) T) a b :=
  (Units.continuous_val (M := Matrix (Fin n) (Fin n) T)).matrix_elem a b

private theorem entryInv {T : Type} [CommRing T] [TopologicalSpace T] (a b : Fin n) :
    Continuous fun x : GL (Fin n) T => ((x⁻¹ : GL (Fin n) T) : Matrix (Fin n) (Fin n) T) a b :=
  (Units.continuous_iff.mp (continuous_id (X := GL (Fin n) T))).2.matrix_elem a b

private theorem norm_shift {G : Type} [Group G] (c : Fin (m + 1) → G) (j : Fin (m + 1)) :
    (List.ofFn fun i => c (j + i)).prod * c j = c j * (List.ofFn fun i => c (j + 1 + i)).prod := by
  rw [List.ofFn_succ, List.ofFn_succ' (f := fun i => c (j + 1 + i))]
  simp only [List.prod_cons, List.concat_eq_append, List.prod_append, List.prod_nil, mul_one, List.prod_singleton,
    add_zero, Fin.zero_eta]
  have h1 : ∀ i : Fin m, j + i.succ = j + 1 + i.castSucc := fun i => by
    rw [← Fin.coeSucc_eq_succ]
    abel
  have h2 : j + 1 + Fin.last m = j := by
    rw [add_assoc, add_comm 1, Fin.last_add_one, add_zero]
  simp only [h1, h2, mul_assoc]

end SlopeTestRemainingChoices

end UpperTheory.ConvolutionTheory.L1

open UpperTheory.ConvolutionTheory.L1 in
theorem UpperTheory.ConvolutionTheory.L1.glueBasic :
    UpperTheory.ConvolutionTheory.L1.GlueBasic := by
  intro R S _ _ _ _ _ _ ι s m D n
  refine ⟨comp_glue D n, glue_comp D n, ?_, ?_, ?_, comp_diag D n, comp_shift D n, ?_⟩
  · intro g h
    apply comp_inj D n
    intro i
    rw [map_mul, comp_glue, comp_glue, comp_glue]
    rfl
  · refine Units.continuous_iff.mpr ⟨?_, ?_⟩
    · refine continuous_matrix fun a b => ?_
      exact D.cont_symm.comp (continuous_pi fun i => (entry n a b).comp (continuous_apply i))
    · refine continuous_matrix fun a b => ?_
      exact D.cont_symm.comp (continuous_pi fun i => (entryInv n a b).comp (continuous_apply i))
  · intro i
    refine Units.continuous_iff.mpr ⟨?_, ?_⟩
    · refine continuous_matrix fun a b => ?_
      exact (continuous_apply i).comp (D.cont.comp (entry n a b))
    · refine continuous_matrix fun a b => ?_
      have : (fun x : GL (Fin n) S => (((D.comp n i x)⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) a b) =
          fun x => D.e (((x⁻¹ : GL (Fin n) S) : Matrix (Fin n) (Fin n) S) a b) i := by
        funext x
        rw [← map_inv, comp_apply]
      show Continuous (fun x : GL (Fin n) S => (((D.comp n i x)⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) a b)
      rw [this]
      exact (continuous_apply i).comp (D.cont.comp (entryInv n a b))
  · intro δ γ
    constructor
    · intro h
      have N : ∀ j : Fin (m + 1), (List.ofFn fun i => D.comp n (j + i) δ).prod = γ := fun j => by
        rw [← comp_twNorm D n (mapGL n s) (fun _ => rfl), h, comp_diag]
      refine ⟨fun i => ?_, ?_, N⟩
      · have e := norm_shift (fun i => D.comp n i δ) i
        rw [N, N] at e
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact e.symm
      · simpa using N 0
    · rintro ⟨-, -, N⟩
      apply comp_inj D n
      intro j
      rw [comp_twNorm D n (mapGL n s) (fun _ => rfl), N, comp_diag]
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.CvBasic
open MeasureTheory

namespace UpperTheory.ConvolutionTheory.L1

section

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]

omit [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G] in
private theorem cvb_int {a b : G → ℂ} (ha : Continuous a) (ha' : HasCompactSupport a) (hb : Continuous b) (x : G) :
    Integrable (fun y => a y * b (y⁻¹ * x)) μ :=
  Continuous.integrable_of_hasCompactSupport (by fun_prop) (ha'.mul_right)

private theorem cvb_cont {a b : G → ℂ} (ha : Continuous a) (ha' : HasCompactSupport a) (hb : Continuous b) :
    Continuous (cv μ a b) := by
  have h : cv μ a b = fun x => ∫ y in tsupport a, a y * b (y⁻¹ * x) ∂μ := by
    funext x
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => ?_).symm
    rw [image_eq_zero_of_notMem_tsupport hy, zero_mul]
  rw [h]
  refine continuous_parametric_integral_of_continuous (f := fun x y => a y * b (y⁻¹ * x)) ?_ ha'
  unfold Function.uncurry
  fun_prop

omit [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [SecondCountableTopology G] [BorelSpace G] [μ.IsHaarMeasure] in
private theorem cvb_supp {a b : G → ℂ} (x : G) (hx : cv μ a b x ≠ 0) :
    ∃ y z, a y ≠ 0 ∧ b z ≠ 0 ∧ x = y * z := by
  by_contra h
  apply hx
  have : (fun y => a y * b (y⁻¹ * x)) = fun _ => 0 := by
    funext y
    by_contra h'
    exact h ⟨y, y⁻¹ * x, left_ne_zero_of_mul h', right_ne_zero_of_mul h', by simp⟩
  simp only [cv, this, integral_zero]

open scoped Pointwise in
omit [LocallyCompactSpace G] [SecondCountableTopology G] [BorelSpace G] [μ.IsHaarMeasure] in
private theorem cvb_cs {a b : G → ℂ} (ha' : HasCompactSupport a) (hb' : HasCompactSupport b) :
    HasCompactSupport (cv μ a b) := by
  refine HasCompactSupport.intro (K := tsupport a * tsupport b) (IsCompact.mul ha' hb') fun x hx => ?_
  by_contra h
  obtain ⟨y, z, hy, hz, rfl⟩ := cvb_supp μ x h
  exact hx (Set.mul_mem_mul (subset_tsupport _ hy) (subset_tsupport _ hz))

open scoped Pointwise in
private theorem cvb_assoc {a b c : G → ℂ} (ha : Continuous a) (ha' : HasCompactSupport a) (hb : Continuous b)
    (hb' : HasCompactSupport b) (hc : Continuous c) : cv μ (cv μ a b) c = cv μ a (cv μ b c) := by
  funext x
  have hint : Integrable (Function.uncurry fun y z : G => a z * b (z⁻¹ * y) * c (y⁻¹ * x)) (μ.prod μ) := by
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · unfold Function.uncurry
      fun_prop
    · refine HasCompactSupport.intro (K := (tsupport a * tsupport b) ×ˢ tsupport a)
        ((IsCompact.mul ha' hb').prod ha') fun p hp => ?_
      by_contra h
      have h1 := left_ne_zero_of_mul h
      have h2 : a p.2 ≠ 0 := left_ne_zero_of_mul h1
      have h3 : b (p.2⁻¹ * p.1) ≠ 0 := right_ne_zero_of_mul h1
      refine hp ⟨?_, subset_tsupport _ h2⟩
      have := Set.mul_mem_mul (subset_tsupport _ h2) (subset_tsupport _ h3)
      simpa using this
  calc cv μ (cv μ a b) c x = ∫ y, ∫ z, a z * b (z⁻¹ * y) * c (y⁻¹ * x) ∂μ ∂μ := by
        simp only [cv, integral_mul_const]
    _ = ∫ z, ∫ y, a z * b (z⁻¹ * y) * c (y⁻¹ * x) ∂μ ∂μ := integral_integral_swap hint
    _ = cv μ a (cv μ b c) x := by
        simp only [cv]
        refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
        simp only
        rw [← integral_const_mul, ← integral_mul_left_eq_self _ z]
        refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        simp [mul_assoc]

end

end UpperTheory.ConvolutionTheory.L1

open UpperTheory.ConvolutionTheory.L1 in
theorem UpperTheory.ConvolutionTheory.L1.cvBasic :
    UpperTheory.ConvolutionTheory.L1.CvBasic := by
  intro G _ _ _ _ _ _ _ _ μ _ a b c ha ha' hb hb' hc hc'
  refine ⟨cvb_cont μ ha ha' hb, cvb_cs μ ha' hb', cvb_supp μ, cvb_assoc μ ha ha' hb hb' hc, ?_, ?_, fun t => ⟨?_, ?_⟩⟩
  · funext x
    simp only [cv, Pi.add_apply, add_mul]
    exact integral_add (cvb_int μ ha ha' hc x) (cvb_int μ hb hb' hc x)
  · funext x
    simp only [cv, Pi.add_apply, mul_add]
    exact integral_add (cvb_int μ ha ha' hb x) (cvb_int μ ha ha' hc x)
  · funext x
    simp only [cv, Pi.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul]
  · funext x
    simp only [cv, Pi.smul_apply, smul_eq_mul, mul_left_comm _ t, integral_const_mul]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.CutIrr
open GroundTheory.Automorphic UpperTheory.ConvolutionTheory.C

private lemma UpperTheory.ConvolutionTheory.L1.cutIrr_prod {Γ G H : Type} [Group Γ] [TopologicalSpace Γ] [Group G]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : UnitaryRep Γ H) (E : H →L[ℂ] H) {m : ℕ} (ι : Fin (m + 1) → G →* Γ)
    (hE : ∀ i g v, E (π (ι i g) v) = π (ι i g) (E v)) (P : Submodule ℂ H)
    (hP : ∀ i g, ∀ v ∈ P, π (ι i g) v ∈ P) (l : List Γ) (hl : ∀ x ∈ l, ∃ i g, x = ι i g) :
    (∀ v, E (π l.prod v) = π l.prod (E v)) ∧ ∀ v ∈ P, π l.prod v ∈ P := by
  induction l with
  | nil => simp
  | cons a l ih =>
    obtain ⟨i, g, rfl⟩ := hl a (by simp)
    obtain ⟨h1, h2⟩ := ih (fun x hx => hl x (by simp [hx]))
    refine ⟨fun v => ?_, fun v hv => ?_⟩
    · rw [List.prod_cons, UnitaryRep.map_mul_apply, UnitaryRep.map_mul_apply, hE, h1]
    · rw [List.prod_cons, UnitaryRep.map_mul_apply]
      exact hP _ _ _ (h2 v hv)

theorem UpperTheory.ConvolutionTheory.L1.cutIrr :
    UpperTheory.ConvolutionTheory.L1.CutIrr := by
  intro Γ G H _ _ _ _ _ _ π V m ι E A U h
  have hfix : ∀ v, v ∈ eigIn V E 1 ↔ v ∈ V ∧ E v = v := by
    intro v
    simp [eigIn, Module.End.mem_eigenspace_iff]
  refine ⟨?_, ?_, ?_⟩
  · have hset : (eigIn V E 1 : Set H) = (V : Set H) ∩ {v | E v = v} := by
      ext v
      exact hfix v
    rw [hset]
    exact h.summand.closed.inter (isClosed_eq E.continuous continuous_id)
  · intro i g v hv
    obtain ⟨hV, hE⟩ := (hfix v).1 hv
    exact (hfix _).2 ⟨h.summand.inv _ _ hV, by rw [h.E_ι, hE]⟩
  · intro P hPle hPc hPinv
    by_cases hbot : P = ⊥
    · exact Or.inl hbot
    right
    obtain ⟨w, hwP, hw0⟩ := P.ne_bot_iff.1 hbot
    obtain ⟨hwV, hEw⟩ := (hfix w).1 (hPle hwP)
    let S : Submodule ℂ H := Submodule.span ℂ (Set.range fun γ => π γ w)
    have hSinv : π.IsInvariant S := by
      intro g v hv
      induction hv using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨γ, rfl⟩ := hx
        exact Submodule.subset_span ⟨g * γ, by simp [UnitaryRep.map_mul_apply]⟩
      | zero => simp
      | add x y _ _ hx hy =>
        rw [map_add (f := _)]
        exact S.add_mem hx hy
      | smul a x _ hx =>
        rw [map_smul]
        exact S.smul_mem a hx
    have hSV : S ≤ V := Submodule.span_le.2 (by
      rintro _ ⟨γ, rfl⟩
      exact h.summand.inv _ _ hwV)
    have hQle : S.topologicalClosure ≤ V :=
      Submodule.topologicalClosure_minimal _ hSV h.summand.closed
    have hQ : S.topologicalClosure = V := by
      rcases h.summand.irred _ hQle S.isClosed_topologicalClosure hSinv.topologicalClosure with h0 | h1
      · exfalso
        have hmem : w ∈ S.topologicalClosure :=
          S.le_topologicalClosure (Submodule.subset_span ⟨1, by simp⟩)
        rw [h0] at hmem
        exact hw0 (by simpa using hmem)
      · exact h1
    have hES : ∀ v ∈ S, E v ∈ P := by
      intro v hv
      induction hv using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨γ, rfl⟩ := hx
        obtain ⟨g, γ', c, hγ, hc⟩ := h.rest γ
        have hl : ∀ x ∈ List.ofFn (fun i => ι i (g i)), ∃ i g, x = ι i g := by
          intro x hx
          obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hx
          exact ⟨i, g i, rfl⟩
        obtain ⟨h1, h2⟩ := UpperTheory.ConvolutionTheory.L1.cutIrr_prod π E ι h.E_ι P hPinv _ hl
        have hc' := hc w hwV
        rw [hEw] at hc'
        show E (π γ w) ∈ P
        rw [hγ, UnitaryRep.map_mul_apply, h1, hc']
        exact h2 _ (P.smul_mem c hwP)
      | zero => simp
      | add x y _ _ hx hy =>
        rw [map_add (f := _)]
        exact P.add_mem hx hy
      | smul a x _ hx =>
        rw [map_smul]
        exact P.smul_mem a hx
    have hEQ : ∀ v ∈ V, E v ∈ P := by
      intro v hv
      rw [← hQ] at hv
      have hcl : v ∈ closure (S : Set H) := hv
      have hm := map_mem_closure E.continuous hcl (t := (P : Set H)) (fun x hx => hES x hx)
      rwa [hPc.closure_eq] at hm
    refine le_antisymm hPle fun v hv => ?_
    obtain ⟨hV, hE⟩ := (hfix v).1 hv
    rw [← hE]
    exact hEQ v hV
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.RegOkPi
open Matrix Polynomial

namespace UpperTheory.ConvolutionTheory.L1

private theorem centComm_field {k : Type} [Field k] {n : ℕ} (γ a b : GL (Fin n) k)
    (hs : (γ : Matrix (Fin n) (Fin n) k).charpoly.Separable)
    (ha : a ∈ Subgroup.centralizer {γ}) (hb : b ∈ Subgroup.centralizer {γ}) : a * b = b * a := by
  rw [Subgroup.mem_centralizer_singleton_iff] at ha hb
  have hA : Commute (a : Matrix (Fin n) (Fin n) k) (γ : Matrix (Fin n) (Fin n) k) := by
    simpa [Commute, SemiconjBy] using congrArg Units.val ha
  have hB : Commute (b : Matrix (Fin n) (Fin n) k) (γ : Matrix (Fin n) (Fin n) k) := by
    simpa [Commute, SemiconjBy] using congrArg Units.val hb
  exact Units.ext (UpperTheory.V.Z.Tf.Orb.centComm k n _ _ _ hs hA hB)

private theorem regOk_field (k : Type) [Field k] [TopologicalSpace k] [IsTopologicalRing k] [T2Space k]
    (n : ℕ) : RegOk k n := by
  intro γ hs
  refine ⟨?_, fun a ha b hb => centComm_field γ a b hs ha hb⟩
  have e : {y : GL (Fin n) k | ∃ x : GL (Fin n) k, y = x⁻¹ * γ * x} =
      ⋂ i : ℕ, {y : GL (Fin n) k | (y : Matrix (Fin n) (Fin n) k).charpoly.coeff i =
        (γ : Matrix (Fin n) (Fin n) k).charpoly.coeff i} := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · rintro ⟨x, rfl⟩ i
      have h := Matrix.charpoly_units_conj x⁻¹ (γ : Matrix (Fin n) (Fin n) k)
      rw [← Matrix.coe_units_inv, inv_inv] at h
      rw [Units.val_mul, Units.val_mul]
      exact congrArg (fun p => _root_.AddMonoidAlgebra.coeff (M := ℕ) p i) h
    · intro h
      exact GlobalTheory.BCT.ClsFin.conj_of_charpoly γ y hs (Polynomial.ext h).symm
  rw [e]
  exact isClosed_iInter fun i => isClosed_eq
    ((GroundTheory.Automorphic.ContragredientTranspose.continuous_charpoly_coeff i).comp Units.continuous_val)
    continuous_const

section Pi

variable {I : Type} {k : I → Type} [∀ i, Field (k i)] {n : ℕ}

private abbrev ev (i : I) : GL (Fin n) (∀ i, k i) →* GL (Fin n) (k i) :=
  Matrix.GeneralLinearGroup.map (Pi.evalRingHom k i)

private theorem ev_val (i : I) (g : GL (Fin n) (∀ i, k i)) :
    ((ev i g : GL (Fin n) (k i)) : Matrix (Fin n) (Fin n) (k i)) =
      (g : Matrix (Fin n) (Fin n) (∀ i, k i)).map (Pi.evalRingHom k i) := rfl

private theorem ev_ext {g h : GL (Fin n) (∀ i, k i)} (e : ∀ i, ev i g = ev i h) : g = h := by
  refine Units.ext (Matrix.ext fun a b => funext fun i => ?_)
  have h : ((ev i g : GL (Fin n) (k i)) : Matrix (Fin n) (Fin n) (k i)) a b =
      ((ev i h : GL (Fin n) (k i)) : Matrix (Fin n) (Fin n) (k i)) a b := by rw [e i]
  exact h

private def asm (x : ∀ i, GL (Fin n) (k i)) : GL (Fin n) (∀ i, k i) where
  val := Matrix.of fun a b i => (x i : Matrix (Fin n) (Fin n) (k i)) a b
  inv := Matrix.of fun a b i => ((x i)⁻¹ : GL (Fin n) (k i)).val a b
  val_inv := by
    ext a b i
    have h := congrFun (congrFun (x i).val_inv a) b
    simp only [Matrix.mul_apply, Matrix.of_apply, Finset.sum_apply, Pi.mul_apply] at h ⊢
    rw [show ((x i)⁻¹ : GL (Fin n) (k i)).val = (x i).inv from rfl, h]
    by_cases hab : a = b <;> simp [Matrix.one_apply, hab]
  inv_val := by
    ext a b i
    have h := congrFun (congrFun (x i).inv_val a) b
    simp only [Matrix.mul_apply, Matrix.of_apply, Finset.sum_apply, Pi.mul_apply] at h ⊢
    rw [show ((x i)⁻¹ : GL (Fin n) (k i)).val = (x i).inv from rfl, h]
    by_cases hab : a = b <;> simp [Matrix.one_apply, hab]

private theorem ev_asm (x : ∀ i, GL (Fin n) (k i)) (i : I) : ev i (asm x) = x i := by
  refine Units.ext (Matrix.ext fun a b => ?_)
  rfl

end Pi

private theorem regOk_pi (I : Type) (k : I → Type) [∀ i, Field (k i)] [∀ i, TopologicalSpace (k i)]
    [∀ i, IsTopologicalRing (k i)] [∀ i, T2Space (k i)] (n : ℕ) : RegOk (∀ i, k i) n := by
  intro γ hs
  have hsi : ∀ i, ((ev i γ : GL (Fin n) (k i)) : Matrix (Fin n) (Fin n) (k i)).charpoly.Separable := fun i => by
    rw [ev_val, Matrix.charpoly_map]
    exact hs.map
  have hc : ∀ i, Continuous (ev (n := n) (k := k) i) := fun i =>
    Continuous.units_map _ ((continuous_id).matrix_map (continuous_apply i))
  refine ⟨?_, fun a ha b hb => ev_ext fun i => ?_⟩
  · have e : {y : GL (Fin n) (∀ i, k i) | ∃ x : GL (Fin n) (∀ i, k i), y = x⁻¹ * γ * x} =
        ⋂ i, (ev i) ⁻¹' {y : GL (Fin n) (k i) | ∃ x : GL (Fin n) (k i), y = x⁻¹ * ev i γ * x} := by
      ext y
      simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage]
      constructor
      · rintro ⟨x, rfl⟩ i
        exact ⟨ev i x, by simp only [map_mul, map_inv]⟩
      · intro h
        choose x hx using h
        refine ⟨asm x, ev_ext fun i => ?_⟩
        simp only [map_mul, map_inv, ev_asm]
        exact hx i
    rw [e]
    exact isClosed_iInter fun i => ((regOk_field (k i) n (ev i γ) (hsi i)).1).preimage (hc i)
  · rw [Subgroup.mem_centralizer_singleton_iff] at ha hb
    have hA : Commute (ev i a) (ev i γ) := by
      change (ev i a) * (ev i γ) = (ev i γ) * (ev i a)
      simpa only [map_mul] using congrArg (ev i) ha
    have hB : Commute (ev i b) (ev i γ) := by
      change (ev i b) * (ev i γ) = (ev i γ) * (ev i b)
      simpa only [map_mul] using congrArg (ev i) hb
    have ha' : ev i a ∈ Subgroup.centralizer {ev i γ} :=
      Subgroup.mem_centralizer_singleton_iff.mpr hA
    have hb' : ev i b ∈ Subgroup.centralizer {ev i γ} :=
      Subgroup.mem_centralizer_singleton_iff.mpr hB
    have hab : ev i a * ev i b = ev i b * ev i a :=
      centComm_field (ev i γ) (ev i a) (ev i b) (hsi i) ha' hb'
    simpa only [map_mul] using hab

end UpperTheory.ConvolutionTheory.L1

theorem UpperTheory.ConvolutionTheory.L1.regOkPi :
    UpperTheory.ConvolutionTheory.L1.RegOkPi :=
  ⟨fun k _ _ _ _ n => UpperTheory.ConvolutionTheory.L1.regOk_field k n, fun I k _ _ _ _ n => UpperTheory.ConvolutionTheory.L1.regOk_pi I k n,
    fun F _ _ n => UpperTheory.ConvolutionTheory.L1.regOk_pi (NumberField.InfinitePlace F) (fun v => v.Completion) n⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.GalSplit
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.DeterminantNonzero
theorem UpperTheory.Reformulated.B.DeterminantNonzero.det_ne {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E] [IsGalois F E] (σ : E ≃ₐ[F] E) (hσ : ∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ) {m : ℕ}
    (hm : Module.finrank F E = m + 1) (b : Module.Basis (Fin (m + 1)) F E) :
    (Matrix.of fun (i j : Fin (m + 1)) => (σ ^ (i : ℕ)) (b j)).det ≠ 0 := by
  intro h
  obtain ⟨v, hv, hvM⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr h
  have hord : orderOf σ = m + 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hσ, IsGalois.card_aut_eq_finrank, hm]
  have hinj : Function.Injective
      (fun i : Fin (m + 1) => ((σ ^ (i : ℕ) : E ≃ₐ[F] E) : E →ₐ[F] E)) := by
    intro i j hij
    have h1 : σ ^ (i : ℕ) = σ ^ (j : ℕ) := by
      ext x
      exact DFunLike.congr_fun hij x
    apply Fin.ext
    exact pow_injOn_Iio_orderOf (by rw [hord]; exact i.2) (by rw [hord]; exact j.2) h1
  have hli := (linearIndependent_toLinearMap F E E).comp _ hinj
  rw [Fintype.linearIndependent_iff] at hli
  apply hv
  funext i
  refine hli v ?_ i
  apply b.ext
  intro j
  have := congrFun hvM j
  simpa [Matrix.vecMul, dotProduct, LinearMap.sum_apply] using this
end

open scoped TensorProduct
open PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.Tf.Geo

namespace UpperTheory.ConvolutionTheory.L1

section SlopeTestRemainingChoices

variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E] [IsGalois F E]

private theorem orderOf_gen (σ : E ≃ₐ[F] E) (hσ : ∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ) {m : ℕ}
    (hm : Module.finrank F E = m + 1) : orderOf σ = m + 1 := by
  rw [orderOf_eq_card_of_forall_mem_zpowers hσ, IsGalois.card_aut_eq_finrank, hm]

private theorem det_ne (σ : E ≃ₐ[F] E) (hσ : ∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ) {m : ℕ}
    (hm : Module.finrank F E = m + 1) (b : Module.Basis (Fin (m + 1)) F E) :
    (Matrix.of fun (i j : Fin (m + 1)) => (σ ^ (i : ℕ)) (b j)).det ≠ 0 :=
  _root_.UpperTheory.Reformulated.B.DeterminantNonzero.det_ne σ hσ hm b

variable {A : Type} [CommRing A] [Algebra F A]

private noncomputable def phi (σ : E ≃ₐ[F] E) (p : E →ₐ[F] A) (m : ℕ) : E ⊗[F] A →ₐ[F] (Fin (m + 1) → A) :=
  Algebra.TensorProduct.productMap
    (Pi.algHom F _ fun i : Fin (m + 1) => p.comp ((σ ^ (i : ℕ) : E ≃ₐ[F] E) : E →ₐ[F] E))
    (Pi.algHom F _ fun _ => AlgHom.id F A)

private theorem phi_tmul (σ : E ≃ₐ[F] E) (p : E →ₐ[F] A) (m : ℕ) (x : E) (a : A) (i : Fin (m + 1)) :
    phi σ p m (x ⊗ₜ a) i = p ((σ ^ (i : ℕ)) x) * a := by
  simp [phi]

private theorem phi_bij (σ : E ≃ₐ[F] E) (hσ : ∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ) {m : ℕ}
    (hm : Module.finrank F E = m + 1) (p : E →ₐ[F] A) : Function.Bijective (phi σ p m) := by
  let b : Module.Basis (Fin (m + 1)) F E := Module.finBasisOfFinrankEq F E hm
  let M : Matrix (Fin (m + 1)) (Fin (m + 1)) E := Matrix.of fun i j => (σ ^ (i : ℕ)) (b j)
  have hunit : IsUnit M.det := isUnit_iff_ne_zero.2 (det_ne σ hσ hm b)
  let N := M⁻¹
  have hMN : M * N = 1 := Matrix.mul_nonsing_inv _ hunit
  have hNM : N * M = 1 := Matrix.nonsing_inv_mul _ hunit
  let Ψ : (Fin (m + 1) → A) → E ⊗[F] A := fun f => ∑ j, b j ⊗ₜ[F] (∑ i, p (N j i) * f i)
  have hr : Function.RightInverse Ψ (phi σ p m) := by
    intro f
    funext k
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Ψ, map_sum, Finset.sum_apply, phi_tmul]
    have h1 : ∀ i, ∑ j, p ((σ ^ (k : ℕ)) (b j)) * p (N j i) = if k = i then 1 else 0 := fun i => by
      have h2 := congrArg p (congrFun (congrFun hMN k) i)
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Matrix.mul_apply, Matrix.one_apply, M, Matrix.of_apply, map_sum, map_mul] at h2
      rw [h2]
      split_ifs <;> simp
    calc _ = ∑ i, (∑ j, p ((σ ^ (k : ℕ)) (b j)) * p (N j i)) * f i := by
          simp only [Finset.mul_sum, Finset.sum_mul]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
      _ = f k := by
          simp only [h1, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have hadd : ∀ f g, Ψ (f + g) = Ψ f + Ψ g := fun f g => by
    simp only [Ψ, Pi.add_apply, mul_add, Finset.sum_add_distrib, TensorProduct.tmul_add]
  have hl : Function.LeftInverse Ψ (phi σ p m) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp [Ψ]
    | add s t hs ht => rw [map_add (f := _), hadd, hs, ht]
    | tmul x a =>
      let c : Fin (m + 1) → E := fun l => algebraMap F E (b.repr x l)
      have hx : (fun i : Fin (m + 1) => (σ ^ (i : ℕ)) x) = M.mulVec c := by
        funext i
        conv_lhs => rw [← b.sum_repr x]
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum]
        simp only [Matrix.mulVec, dotProduct, M, Matrix.of_apply, c]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_smul, Algebra.smul_def, mul_comm]
      have hc : ∀ j, ∑ i, N j i * (σ ^ (i : ℕ)) x = c j := fun j => by
        have : N.mulVec (fun i : Fin (m + 1) => (σ ^ (i : ℕ)) x) = c := by
          rw [hx, Matrix.mulVec_mulVec, hNM, Matrix.one_mulVec]
        exact congrFun this j
      have h3 : ∀ j, ∑ i, p (N j i) * (p ((σ ^ (i : ℕ)) x) * a) = b.repr x j • a := fun j => by
        calc _ = p (∑ i, N j i * (σ ^ (i : ℕ)) x) * a := by
              set_option synthInstance.maxHeartbeats 100000 in
                simp only [map_sum, map_mul, Finset.sum_mul, mul_assoc]
          _ = _ := by rw [hc]; simp only [c, p.commutes, Algebra.smul_def]
      simp only [Ψ, phi_tmul, h3, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
      rw [← TensorProduct.sum_tmul, b.sum_repr]
  exact ⟨hl.injective, hr.surjective⟩

private theorem phi_shift (σ : E ≃ₐ[F] E) (hσ : ∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ) {m : ℕ}
    (hm : Module.finrank F E = m + 1) (p : E →ₐ[F] A) (t : E ⊗[F] A) (i : Fin (m + 1)) :
    phi σ p m (Algebra.TensorProduct.map (σ : E →ₐ[F] E) (AlgHom.id F A) t) i = phi σ p m t (i + 1) := by
  have h1 : σ ^ (m + 1) = 1 := by rw [← orderOf_gen σ hσ hm]; exact pow_orderOf_eq_one σ
  have hv : ((i + 1 : Fin (m + 1)) : ℕ) = ((i : ℕ) + 1) % (m + 1) := by simp [Fin.val_add]
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add s t hs ht => simp only [map_add (f := _), Pi.add_apply, hs, ht]
  | tmul x a =>
    rw [Algebra.TensorProduct.map_tmul, phi_tmul, phi_tmul, hv, ← pow_eq_pow_mod _ h1, pow_succ]
    rfl

end SlopeTestRemainingChoices

end UpperTheory.ConvolutionTheory.L1

open UpperTheory.ConvolutionTheory.L1 in
theorem UpperTheory.ConvolutionTheory.L1.galSplit :
    UpperTheory.ConvolutionTheory.L1.GalSplit := by
  intro F E _ _ _ _ _ _ σ hσ m hm A B _ _ _ _ e₀ p
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  refine ⟨e₀.symm.toRingEquiv.trans (RingEquiv.ofBijective (phi σ p m) (phi_bij σ hσ hm p)),
    fun x a i => ?_, fun b i => ?_⟩
  · show phi σ p m (e₀.symm (e₀ (x ⊗ₜ a))) i = _
    rw [AlgEquiv.symm_apply_apply, phi_tmul]
  · show phi σ p m (e₀.symm (galOf e₀ σ b)) i = phi σ p m (e₀.symm b) (i + 1)
    rw [← phi_shift σ hσ hm p]
    have h : e₀.symm (galOf e₀ σ b) =
        Algebra.TensorProduct.map (σ : E →ₐ[F] E) (AlgHom.id F A) (e₀.symm b) :=
      e₀.symm_apply_apply _
    rw [h]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.PushTest
open MeasureTheory

namespace UpperTheory.ConvolutionTheory.L1

private theorem cont_prodFn {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (m : ℕ) :
    Continuous fun y : Fin m → G => (List.ofFn y).prod := by
  simp only [List.ofFn_eq_map]
  exact continuous_list_prod (f := fun i (y : Fin m → G) => y i) _ fun i _ => continuous_apply i

private theorem cont_fib {G : Type} [Group G] [MeasurableSpace G] [TopologicalSpace G] [IsTopologicalGroup G] (m : ℕ) :
    Continuous fun p : G × (Fin m → G) => fib p.2 p.1 := by
  refine continuous_pi fun i => ?_
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [fib, Fin.snoc_last]
    exact ((cont_prodFn m).comp continuous_snd).inv.mul continuous_fst
  · simp only [fib, Fin.snoc_castSucc]
    exact (continuous_apply j).comp continuous_snd

private theorem prod_fib {G : Type} [Group G] [MeasurableSpace G] {m : ℕ} (y : Fin m → G) (x : G) :
    (List.ofFn (fib y x)).prod = x := by
  rw [List.ofFn_succ']
  simp [fib]

private theorem integrable_fib {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (m : ℕ)
    (Φ : (Fin (m + 1) → G) → ℂ) (hc : Continuous Φ) (hs : HasCompactSupport Φ) :
    ∃ K : Set (Fin m → G), IsCompact K ∧ (∀ x y, y ∉ K → Φ (fib y x) = 0) ∧
      ∀ x, Integrable (fun y : Fin m → G => Φ (fib y x)) (Measure.pi fun _ => μ) := by
  have hK : IsCompact ((fun g : Fin (m + 1) → G => fun i : Fin m => g i.castSucc) '' tsupport Φ) :=
    hs.isCompact.image (continuous_pi fun i => continuous_apply _)
  have h0 : ∀ x y, y ∉ ((fun g : Fin (m + 1) → G => fun i : Fin m => g i.castSucc) '' tsupport Φ) →
      Φ (fib y x) = 0 := by
    intro x y hy
    by_contra h
    exact hy ⟨fib y x, subset_tsupport _ h, funext fun i => by simp [fib]⟩
  refine ⟨_, hK, h0, fun x => ?_⟩
  refine Continuous.integrable_of_hasCompactSupport ?_ (HasCompactSupport.intro hK (h0 x))
  exact hc.comp ((cont_fib m).comp (Continuous.prodMk_right x))

end UpperTheory.ConvolutionTheory.L1

open UpperTheory.ConvolutionTheory.L1 in
theorem UpperTheory.ConvolutionTheory.L1.pushTest :
    UpperTheory.ConvolutionTheory.L1.PushTest := by
  intro G _ _ _ _ _ _ _ _ μ _ m Φ hc hs
  obtain ⟨K, hK, h0, hint⟩ := integrable_fib μ m Φ hc hs
  have hsup : ∀ x, push μ m Φ x ≠ 0 → ∃ g, Φ g ≠ 0 ∧ (List.ofFn g).prod = x := by
    intro x hx
    by_contra h
    apply hx
    have : ∀ y : Fin m → G, Φ (fib y x) = 0 := fun y => by
      by_contra h'
      exact h ⟨_, h', prod_fib y x⟩
    simp [push, this]
  refine ⟨?_, ?_, hsup, hint, ?_, ?_⟩
  · have e : push μ m Φ = fun x => ∫ y in K, Φ (fib y x) ∂(Measure.pi fun _ => μ) := by
      funext x
      exact (setIntegral_eq_integral_of_forall_compl_eq_zero (h0 x)).symm
    rw [e]
    exact continuous_parametric_integral_of_continuous (f := fun x y => Φ (fib y x)) (hc.comp (cont_fib m)) hK
  · refine HasCompactSupport.intro (hs.isCompact.image (cont_prodFn (m + 1))) fun x hx => ?_
    by_contra h
    obtain ⟨g, hg, rfl⟩ := hsup x h
    exact hx ⟨g, subset_tsupport _ hg, rfl⟩
  · intro c
    funext x
    simp [push, integral_const_mul]
  · intro Ψ hc' hs'
    obtain ⟨_, _, _, hint'⟩ := integrable_fib μ m Ψ hc' hs'
    funext x
    simp only [push, Pi.add_apply]
    exact integral_add (hint x) (hint' x)
end
