module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.AffineCoverOfProductFibres
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCohomologyGenericFibreHenselLineSubsing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubsingletonEtaleCohomologyGenericFibreHenselian
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieModelIsBaseChange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralGeneratorRigidificationAllLevels

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernFormSignedPartMeasureChartApply
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernFormSignedPartMeasureChartApply
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

noncomputable section

namespace GlobalTheory.Mix.PartApply

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}

def colSum (H : Fin D → Matrix (Fin D) (Fin D) ℂ) : ℂ :=
  ∑ τ : Equiv.Perm (Fin D), (Matrix.of fun j l => H (τ l) j l).det

theorem colSum_mul_left (A : Matrix (Fin D) (Fin D) ℂ) (H : Fin D → Matrix (Fin D) (Fin D) ℂ) :
    colSum (fun a => A * H a) = A.det * colSum H := by
  simp only [colSum, Finset.mul_sum, ← Matrix.det_mul]
  refine Finset.sum_congr rfl fun τ _ => congrArg _ ?_
  ext j l
  simp [Matrix.mul_apply]

theorem colSum_transpose (H : Fin D → Matrix (Fin D) (Fin D) ℂ) :
    colSum (fun a => (H a).transpose) = colSum H := by
  simp only [colSum, Matrix.det_apply', Matrix.of_apply, Matrix.transpose_apply]
  rw [Finset.sum_comm, Finset.sum_comm (f := fun (τ ρ : Equiv.Perm (Fin D)) => ((Equiv.Perm.sign ρ : ℤ) : ℂ) * ∏ i, H (τ i) (ρ i) i)]
  refine Fintype.sum_equiv (Equiv.inv _) _ _ fun ρ => ?_
  refine Fintype.sum_equiv (Equiv.mulRight ρ⁻¹) _ _ fun τ => ?_
  simp only [Equiv.inv_apply, Equiv.Perm.sign_inv, Equiv.coe_mulRight]
  congr 1
  refine Fintype.prod_equiv ρ _ _ fun i => ?_
  simp

theorem colSum_mul (A B : Matrix (Fin D) (Fin D) ℂ) (H : Fin D → Matrix (Fin D) (Fin D) ℂ) :
    colSum (fun a => A * H a * B) = A.det * B.det * colSum H := by
  have e : colSum (fun a => H a * B) = B.det * colSum H := by
    rw [← colSum_transpose, ← colSum_transpose H, ← Matrix.det_transpose B, ← colSum_mul_left]
    simp only [Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]
  rw [colSum_mul_left A fun a => H a * B, e, mul_assoc]

theorem dens_eq (L : Fin D → MLine p σ) (c : AlgChart p σ D) (y : CxPts p σ) :
    dens L c y = (Real.pi ^ D)⁻¹ * (colSum fun a => c.hess (L a).φ (pick (L a).φ.isLB y) y).re := rfl

theorem dens_trans (L : Fin D → MLine p σ) (c c' : AlgChart p σ D) {y : CxPts p σ} (hy : y ∈ c.e.source)
    (hy' : y ∈ c'.e.source) : dens L c y = ‖transDet c.e c'.e y‖ ^ 2 * dens L c' y := _root_.GlobalTheory.Mix.ChartChange.dens_trans (y := y) L c c' hy hy'

end GlobalTheory.Mix.PartApply

namespace GlobalTheory.Mix

theorem part_apply : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) [SecondCountableTopology (CxPts p σ)] (D : ℕ) (L : Fin D → MLine p σ) (ε : ℤˣ) (c : AlgChart p σ D) (S : Set (CxPts p σ)), MeasurableSet S → S ⊆ c.e.source → part L ε S = ∫⁻ v in c.e '' S, ENNReal.ofReal ((ε : ℤ) * dens L c (c.e.symm v)) := by
  intro k _ X p σ _ D L ε c S hS hc
  rw [part, glueMeas_apply _ _ (fun c c' => c.holo_trans c') (fun c c' y hy hy' => by
    rw [PartApply.dens_trans L c c' hy hy', mul_left_comm, ENNReal.ofReal_mul (sq_nonneg _)])
    c hS hc, chartMeas_apply_of_subset _ _ hS hc]

end GlobalTheory.Mix
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernFormSignedPartMeasureChartApplyStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixedChernFormSignedPartMeasure_chart_apply : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) [SecondCountableTopology (CxPts p σ)] (D : ℕ) (L : Fin D → MLine p σ) (ε : ℤˣ) (c : AlgChart p σ D) (S : Set (CxPts p σ)), MeasurableSet S → S ⊆ c.e.source → part L ε S = ∫⁻ v in c.e '' S, ENNReal.ofReal ((ε : ℤ) * dens L c (c.e.symm v)) := by
  first | exact @GlobalTheory.Mix.part_apply | exact GlobalTheory.Mix.part_apply | (intros; apply GlobalTheory.Mix.part_apply <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyFiniteHomKernelKilledByNat
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyFiniteHomKernelKilledByNat
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AV.KerKill

theorem flat_of_isFinite_field (K : Type) [Field K] (H : Over (Sp K)) [GrpObj H] (hf : IsFinite H.hom) :
    Flat H.hom := by
  have haff : IsAffine H.left := isAffine_of_isAffineHom H.hom
  obtain ⟨A, ⟨e⟩⟩ := (essImage_hopfSpec (G := Grp.mk H)).2 haff
  let B : Type := A.unop
  letI : HopfAlgebra K B := A.unop.hopfAlgebra
  let G : Over (Spec (CommRingCat.of K)) :=
    (Spec (CommRingCat.of B)).asOver (Spec (CommRingCat.of K))
  letI : GrpObj G := instGrpObjSpecAsOverSpec (R := CommRingCat.of K) (A := CommRingCat.of B)
  let i : G ≅ H := (Grp.forget _).mapIso e
  obtain ⟨j, hj, hw⟩ : ∃ j : Spec (CommRingCat.of B) ⟶ H.left, IsIso j ∧
      Spec.map (CommRingCat.ofHom (algebraMap K B)) = j ≫ H.hom :=
    ⟨i.hom.left, inferInstanceAs (IsIso ((Over.forget _).map i.hom)), (Over.w i.hom).symm⟩
  haveI h1 : Flat (Spec.map (CommRingCat.ofHom (algebraMap K B))) := by
    rw [Flat.SpecMap_iff]
    exact RingHom.flat_algebraMap_iff.2 inferInstance
  have e : H.hom = inv j ≫ Spec.map (CommRingCat.ofHom (algebraMap K B)) := by
    rw [hw, IsIso.inv_hom_id_assoc]
  rw [e]
  infer_instance

theorem kernel_killed : ∀ (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B), IsFinite f.hom.left →
    ∃ n : ℕ, 0 < n ∧ ∀ (T : Over (Sp K)) (x : T ⟶ A.X), x ≫ f.hom = 1 → x ^ n = 1 := by
  intro K _ A B f hf
  let H := pullback f.hom η[B.X]
  let i : H ⟶ A.X := pullback.fst _ _
  have hp : IsPullback i (toUnit H) f.hom η[B.X] := by
    rw [toUnit_unique (toUnit _) (pullback.snd f.hom η[B.X])]
    exact IsPullback.of_hasPullback _ _
  haveI : Mono i := ⟨fun _ _ e => hp.hom_ext e (toUnit_unique _ _)⟩
  let lift {W : Over (Sp K)} (g : W ⟶ A.X) (hg : g ≫ f.hom = 1) : W ⟶ H :=
    GlobalTheory.CompanionTheory.KerPull.Kernel.kerLift hp g hg
  have lift_comp {W : Over (Sp K)} (g : W ⟶ A.X) (hg : g ≫ f.hom = 1) :
      lift g hg ≫ i = g := GlobalTheory.CompanionTheory.KerPull.Kernel.kerLift_comp hp g hg
  have kills (W : Over (Sp K)) (x : W ⟶ H) : (x ≫ i) ≫ f.hom = 1 := by
    rw [Category.assoc, hp.w, ← Category.assoc, toUnit_unique (x ≫ toUnit H) (toUnit W), Hom.one_def]
  letI : GrpObj H :=
    { one := lift η[A.X] (by rw [IsMonHom.one_hom, Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp])
      mul := lift (fst H H ≫ i * snd H H ≫ i) (by
        rw [MonObj.mul_comp, kills, kills, _root_.mul_one])
      inv := lift (i ≫ ι[A.X]) (by
        have e : i ≫ f.hom = 1 := by simpa using kills H (𝟙 H)
        have h : (i⁻¹ * i) ≫ f.hom = 1 := by rw [inv_mul_cancel, MonObj.one_comp]
        rw [MonObj.mul_comp, e, _root_.mul_one] at h
        exact h)
      one_mul := by
        rw [← cancel_mono i]
        simp [MonObj.comp_mul, lift, lift_comp]
        rw [toUnit_unique (fst (𝟙_ (Over (Sp K))) H) (toUnit _), ← Hom.one_def, _root_.one_mul, leftUnitor_hom]
      mul_one := by
        rw [← cancel_mono i]
        simp [MonObj.comp_mul, lift, lift_comp]
        rw [toUnit_unique (snd H (𝟙_ (Over (Sp K)))) (toUnit _), ← Hom.one_def, _root_.mul_one, rightUnitor_hom]
      mul_assoc := by
        rw [← cancel_mono i]
        simp [MonObj.comp_mul, lift, lift_comp]
        exact _root_.mul_assoc _ _ _
      left_inv := by
        rw [← cancel_mono i]
        simp [MonObj.comp_mul, lift, lift_comp]
        rw [← Hom.one_def]
        exact inv_mul_cancel i
      right_inv := by
        rw [← cancel_mono i]
        simp [MonObj.comp_mul, lift, lift_comp]
        rw [← Hom.one_def]
        exact mul_inv_cancel i }
  haveI : IsMonHom i := by
    refine { one_hom := lift_comp _ _, mul_hom := ?_ }
    refine (lift_comp _ _).trans ?_
    rw [Hom.mul_def]
    simp
  haveI : IsCommMonObj A.X := A.ab.comm
  haveI : IsCommMonObj H := by
    refine (isCommMonObj_iff_isMulCommutative _).mpr fun T => ⟨⟨fun x y => ?_⟩⟩
    rw [← cancel_mono i, MonObj.mul_comp, MonObj.mul_comp, mul_comm]
  have hHf : IsFinite H.hom := by
    have hl := hp.map (Over.forget _)
    have h1 : IsFinite (toUnit H).left := MorphismProperty.of_isPullback (P := @IsFinite) hl hf
    have h2 : H.hom = (toUnit H).left ≫ (𝟙_ (Over (Sp K))).hom := (Over.w _).symm
    rw [h2]
    exact inferInstanceAs (IsFinite (_ ≫ 𝟙 _))
  have hfl : Flat H.hom := flat_of_isFinite_field K H hHf
  obtain ⟨N, hN, h⟩ := GlobalTheory.FiniteFlatKilled.main K H hHf hfl
  refine ⟨N, hN, fun T x hx => ?_⟩
  obtain ⟨y, rfl⟩ : ∃ y : T ⟶ H, y ≫ i = x := ⟨_, GlobalTheory.CompanionTheory.KerPull.Kernel.kerLift_comp hp x hx⟩
  rw [← MonObj.comp_pow, ← Category.id_comp i,
    ← MonObj.pow_comp, h, MonObj.one_comp, MonObj.comp_one]

end GlobalTheory.AV.KerKill
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyFiniteHomKernelKilledByNatStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianVariety_finiteHom_kernel_killed_by_nat : ∀ (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B), IsFinite f.hom.left → ∃ n : ℕ, 0 < n ∧ ∀ (T : Over (Sp K)) (x : T ⟶ A.X), x ≫ f.hom = 1 → x ^ n = 1 := by
  first | exact @GlobalTheory.AV.KerKill.kernel_killed | exact GlobalTheory.AV.KerKill.kernel_killed | (intros; apply GlobalTheory.AV.KerKill.kernel_killed <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InductiveArakelovFormulaRhsTensorAdditive
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InductiveArakelovFormulaRhsTensorAdditive
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace GlobalTheory.MixHt

variable {k : Type} [CommRing k] {Y : Scheme.{0}} [IsIntegral Y] {q : Y ⟶ Sp k}

theorem divOfRatSec_congr {B : LB Y} (hB : B.IsLB) {t t' : B.ι → Y.functionFieldˣ} (ht : IsRatSec B t)
    (ht' : IsRatSec B t') (e : ∀ c, genericPoint Y ∈ B.U c → t c = t' c) :
    divOfRatSec hB ht = divOfRatSec hB ht' :=
  CartierDiv.ext_of_isEqn fun z => by
    obtain ⟨c, hc⟩ := exists_chart hB z
    refine ⟨t c, (presents_divOfRatSec hB ht).isEqn c z hc, ?_⟩
    rw [e c (gen_mem hc)]
    exact (presents_divOfRatSec hB ht').isEqn c z hc

theorem logNorm_congr {σ : k →+* ℂ} {B : LB Y} (φ : Weight q σ B) {t t' : B.ι → Y.functionFieldˣ}
    (e : ∀ c, genericPoint Y ∈ B.U c → t c = t' c) (y : CxPts q σ) : logNorm φ t y = logNorm φ t' y := by
  rw [logNorm, logNorm, e _ (gen_mem (mem_ptsIn.1 (mem_pick φ.isLB y)))]

theorem logNorm_tens_mul {σ : k →+* ℂ} (M A : HermLB q) {r : M.B.ι → Y.functionFieldˣ}
    {u : A.B.ι → Y.functionFieldˣ} (hr : IsRatSec M.B r) (hu : IsRatSec A.B u) {y : CxPts q σ}
    (hyr : y ∈ offSupp q σ (M.div hr)) (hyu : y ∈ offSupp q σ (A.div hu)) :
    logNorm ((M.tens A).φ σ) (fun c : M.B.ι × A.B.ι => r c.1 * u c.2) y =
      logNorm (M.φ σ) r y + logNorm (A.φ σ) u y := by
  obtain ⟨h₁, h₂⟩ := mem_ptsIn_inf.1 (mem_pick ((M.tens A).φ σ).isLB y)
  have hu₁ := hr.unitAt M.isLB hyr h₁
  have hu₂ := hu.unitAt A.isLB hyu h₂
  rw [logNorm_eq (M.φ σ) hr hyr h₁, logNorm_eq (A.φ σ) hu hyu h₂]
  change Real.log ‖ratVal ((r (pick ((M.tens A).φ σ).isLB y).1 * u (pick ((M.tens A).φ σ).isLB y).2 :
      Y.functionFieldˣ) : Y.functionField) y‖ - ((M.φ σ).φ (pick ((M.tens A).φ σ).isLB y).1 y +
      (A.φ σ).φ (pick ((M.tens A).φ σ).isLB y).2 y) / 2 = _
  rw [Units.val_mul, ratVal_mul hu₁.regAt hu₂.regAt, norm_mul,
    Real.log_mul (norm_ne_zero_iff.2 (ratVal_ne_zero hu₁)) (norm_ne_zero_iff.2 (ratVal_ne_zero hu₂))]
  ring

theorem chernInt_eq_of_null {D : ℕ} (hY : IsArithVar q D) {σ : k →+* ℂ} {B : LB Y} (φ : Weight q σ B)
    {S S' : Set (CxPts q σ)} (hS : S ⊆ S') (Z : Set Y) (hZ : IsClosed Z) (hg : genericPoint Y ∉ Z)
    (hd : S' \ S ⊆ {y | under y ∈ Z}) (f : CxPts q σ → ℝ) : φ.chernInt D S' f = φ.chernInt D S f := by
  have h (ε : ℤˣ) : S' =ᵐ[φ.chernPart D ε] S := ae_eq_set.2
    ⟨measure_mono_null hd (ChernNull.chernPart_over_closed hY Z hZ hg σ φ ε), by
      rw [Set.diff_eq_empty.2 hS]; exact measure_empty⟩
  rw [Weight.chernInt, Weight.chernInt, setIntegral_congr_set (h 1), setIntegral_congr_set (h (-1))]

theorem chernInt_tens {D : ℕ} (hY : IsArithVar q D) (σ : k →+* ℂ) {B : LB Y} (φ : Weight q σ B)
    (M A : HermLB q) {r : M.B.ι → Y.functionFieldˣ} {u : A.B.ι → Y.functionFieldˣ} (hr : IsRatSec M.B r)
    (hu : IsRatSec A.B u) {t : (M.tens A).B.ι → Y.functionFieldˣ} (ht : IsRatSec (M.tens A).B t)
    (htu : ∀ c : M.B.ι × A.B.ι, genericPoint Y ∈ (M.tens A).B.U c → t c = r c.1 * u c.2)
    (h₁ : φ.ChernIntegrableOn D (offSupp q σ (M.div hr)) (logNorm (M.φ σ) r))
    (h₂ : φ.ChernIntegrableOn D (offSupp q σ (A.div hu)) (logNorm (A.φ σ) u)) :
    φ.chernInt D (offSupp q σ ((M.tens A).div ht)) (logNorm ((M.tens A).φ σ) t) =
      φ.chernInt D (offSupp q σ (M.div hr)) (logNorm (M.φ σ) r) +
        φ.chernInt D (offSupp q σ (A.div hu)) (logNorm (A.φ σ) u) := by
  let S := offSupp q σ (M.div hr) ∩ offSupp q σ (A.div hu) ∩ offSupp q σ ((M.tens A).div ht)
  let Z : Set Y := ((M.div hr).supp : Set Y) ∪ (A.div hu).supp ∪ ((M.tens A).div ht).supp
  have hZ : IsClosed Z :=
    ((M.div hr).supp.isClosed.union (A.div hu).supp.isClosed).union ((M.tens A).div ht).supp.isClosed
  have hg : genericPoint Y ∉ Z := by
    simp only [Z, Set.mem_union, SetLike.mem_coe, not_or]
    exact ⟨⟨CartierDiv.genericPoint_notMem_supp _, CartierDiv.genericPoint_notMem_supp _⟩,
      CartierDiv.genericPoint_notMem_supp _⟩
  have hd (T : Set (CxPts q σ)) : T \ S ⊆ {y | under y ∈ Z} := fun y hy => by
    by_contra hz
    simp only [Set.mem_setOf_eq, Z, Set.mem_union, SetLike.mem_coe, not_or] at hz
    exact hy.2 ⟨⟨mem_offSupp.2 hz.1.1, mem_offSupp.2 hz.1.2⟩, mem_offSupp.2 hz.2⟩
  have hSm : MeasurableSet S :=
    (((isOpen_offSupp _).inter (isOpen_offSupp _)).inter (isOpen_offSupp _)).measurableSet
  have hsT : S ⊆ offSupp q σ ((M.tens A).div ht) := fun _ h => h.2
  have hsM : S ⊆ offSupp q σ (M.div hr) := fun _ h => h.1.1
  have hsA : S ⊆ offSupp q σ (A.div hu) := fun _ h => h.1.2
  rw [chernInt_eq_of_null hY φ hsT Z hZ hg (hd _),
    chernInt_eq_of_null hY φ hsM Z hZ hg (hd _) (logNorm (M.φ σ) r),
    chernInt_eq_of_null hY φ hsA Z hZ hg (hd _) (logNorm (A.φ σ) u),
    Weight.chernInt_congr hSm (g := fun y => logNorm (M.φ σ) r y + logNorm (A.φ σ) u y) ?_]
  · exact Weight.chernInt_add ⟨h₁.1.mono_set fun _ h => h.1.1, h₁.2.mono_set fun _ h => h.1.1⟩
      ⟨h₂.1.mono_set fun _ h => h.1.2, h₂.2.mono_set fun _ h => h.1.2⟩
  · intro y hy
    rw [logNorm_congr _ htu y]
    exact logNorm_tens_mul M A hr hu hy.1.1 hy.1.2

theorem archInt_tens (hAI : ArchInteg) {e : ℕ} (hY : IsArithVar q e) (N M A : HermLB q)
    {r : M.B.ι → Y.functionFieldˣ} {u : A.B.ι → Y.functionFieldˣ} (hr : IsRatSec M.B r)
    (hu : IsRatSec A.B u) {t : (M.tens A).B.ι → Y.functionFieldˣ} (ht : IsRatSec (M.tens A).B t)
    (htu : ∀ c : M.B.ι × A.B.ι, genericPoint Y ∈ (M.tens A).B.U c → t c = r c.1 * u c.2) :
    N.archInt (M.tens A) e ht = N.archInt M e hr + N.archInt A e hu := by
  have := hY.finite_emb
  unfold HermLB.archInt
  rw [← finsum_add_distrib (Set.toFinite _) (Set.toFinite _)]
  exact finsum_congr fun σ => chernInt_tens hY σ (N.φ σ) M A hr hu ht htu
    (hAI k Y q e hY M N r hr σ) (hAI k Y q e hY A N u hu σ)

theorem archInt_of_isEmpty (hE : ∀ σ : k →+* ℂ, IsEmpty (CxPts q σ)) (N M : HermLB q)
    {r : M.B.ι → Y.functionFieldˣ} (hr : IsRatSec M.B r) (e : ℕ) : N.archInt M e hr = 0 := by
  unfold HermLB.archInt
  refine (finsum_congr fun σ => ?_).trans finsum_zero
  have := hE σ
  rw [Weight.chernInt, Set.eq_empty_of_isEmpty (offSupp q σ (M.div hr))]
  simp only [Measure.restrict_empty, integral_zero_measure, sub_zero]

theorem isArithVar_or_isEmpty (hq : IsAmb q) {e : ℕ} (he : topologicalKrullDim Y = (e + 1 : ℕ)) :
    IsArithVar q e ∨ ∀ σ : k →+* ℂ, IsEmpty (CxPts q σ) := by
  obtain ⟨ℓ, _⟩ := CharP.exists Γ(Y, ⊤)
  rcases CharP.char_is_prime_or_zero Γ(Y, ⊤) ℓ with hℓ | rfl
  · refine .inr fun σ => ⟨fun y => ?_⟩
    let f : Γ(Y, ⊤) →+* ℂ := (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom.comp y.1.appTop.hom
    have h0 : (ℓ : ℂ) = 0 := by rw [← map_natCast f, CharP.cast_eq_zero, map_zero]
    exact hℓ.ne_zero (Nat.cast_eq_zero.1 h0)
  · have := CharP.charP_to_charZero Γ(Y, ⊤)
    exact .inl ⟨hq.1, hq.2, ‹_›, hq.3, (flat_int_iff_charZero _).2 this, he⟩

theorem pol_add {ι : Type} [Fintype ι] (a b : (ι → ℤ) → ℝ) :
    FibreProj.pol (fun n => a n + b n) = FibreProj.pol a + FibreProj.pol b := by
  simp only [FibreProj.pol, mul_add, Finset.sum_add_distrib]

theorem finsum_mult_add [IsLocallyNoetherian Y] [CompactSpace Y] (D E : CartierDiv Y) (h : Y → ℝ) :
    ∑ᶠ z, ((D + E).mult z : ℝ) * h z = ∑ᶠ z, (D.mult z : ℝ) * h z + ∑ᶠ z, (E.mult z : ℝ) * h z := by
  have hfin (D : CartierDiv Y) : (Function.support fun z => (D.mult z : ℝ) * h z).Finite :=
    D.finite_support_mult.subset fun z hz h0 => hz (by simp [h0])
  simp only [CartierDiv.mult_add, Int.cast_add, add_mul]
  exact finsum_add_distrib (hfin D) (hfin E)

theorem recVal_tens : ArchInteg → ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k), IsAmb q → ∀ e : ℕ, topologicalKrullDim Y = (e + 1 : ℕ) → ∀ (h : Y → ℝ) (L : Fin e → HermLB q) (M A : HermLB q) (r : M.B.ι → Y.functionFieldˣ) (hr : IsRatSec M.B r) (u : A.B.ι → Y.functionFieldˣ) (hu : IsRatSec A.B u) (t : (M.tens A).B.ι → Y.functionFieldˣ) (ht : IsRatSec (M.tens A).B t), (∀ (i : M.B.ι) (j : A.B.ι), genericPoint Y ∈ M.B.U i → genericPoint Y ∈ A.B.U j → t (i, j) = r i * u j) → recVal h L (M.tens A) ht = recVal h L M hr + recVal h L A hu := by
  intro hAI k _ Y _ _ q hq e he h L M A r hr u hu t ht htu
  have := hq.isNoetherian
  have htu' : ∀ c : M.B.ι × A.B.ι, genericPoint Y ∈ (M.tens A).B.U c → t c = r c.1 * u c.2 :=
    fun c hc => htu c.1 c.2 hc.1 hc.2
  have hdiv : (M.tens A).div ht = M.div hr + A.div hu :=
    (divOfRatSec_congr _ ht (PtHtComb.isRatSec_tens hr hu) htu').trans (PtHtComb.div_tens M A hr hu)
  have hmix : mixArch L (M.tens A) ht = mixArch L M hr + mixArch L A hu := by
    rcases isArithVar_or_isEmpty hq he with hY | hE
    · unfold mixArch
      rw [← add_div, ← pol_add]
      congr 2
      funext n
      exact archInt_tens hAI hY (comb L n) M A hr hu ht htu'
    · have h0 (N' : HermLB q) {r' : N'.B.ι → Y.functionFieldˣ} (hr' : IsRatSec N'.B r') :
          mixArch L N' hr' = 0 := by
        simp [mixArch, archInt_of_isEmpty hE, FibreProj.pol]
      rw [h0, h0, h0, add_zero]
  unfold recVal
  rw [hdiv, finsum_mult_add, hmix]
  ring

end GlobalTheory.MixHt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InductiveArakelovFormulaRhsTensorAdditiveStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inductiveArakelovFormula_rhs_tensor_additive : ArchInteg → ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k), IsAmb q → ∀ e : ℕ, topologicalKrullDim Y = (e + 1 : ℕ) → ∀ (h : Y → ℝ) (L : Fin e → HermLB q) (M A : HermLB q) (r : M.B.ι → Y.functionFieldˣ) (hr : IsRatSec M.B r) (u : A.B.ι → Y.functionFieldˣ) (hu : IsRatSec A.B u) (t : (M.tens A).B.ι → Y.functionFieldˣ) (ht : IsRatSec (M.tens A).B t), (∀ (i : M.B.ι) (j : A.B.ι), genericPoint Y ∈ M.B.U i → genericPoint Y ∈ A.B.U j → t (i, j) = r i * u j) → recVal h L (M.tens A) ht = recVal h L M hr + recVal h L A hu := by
  first | exact @GlobalTheory.MixHt.recVal_tens | exact GlobalTheory.MixHt.recVal_tens | (intros; apply GlobalTheory.MixHt.recVal_tens <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyIndEtaleBaseChange
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyEquivStrictHenselianLinePoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyEquivStrictHenselianLinePoint
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC TensorProduct

namespace GlobalTheory.EtC.LineLocal

open Polynomial

theorem bijective_of_subsingleton {X Y : Type*} [Subsingleton X] [Subsingleton Y] (f : X → Y) (x : X) :
    Function.Bijective f :=
  ⟨fun a b _ => Subsingleton.elim a b, fun y => ⟨x, Subsingleton.elim _ _⟩⟩

theorem idem_of_domain {A : Type} [CommRing A] [IsDomain A] (e : A) (he : IsIdempotentElem e) :
    e = 0 ∨ e = 1 := by
  have h : e * (e - 1) = 0 := by rw [mul_sub, mul_one, he.eq, sub_self]
  rcases mul_eq_zero.mp h with h | h
  · exact Or.inl h
  · exact Or.inr (sub_eq_zero.mp h)


attribute [local instance] Algebra.TensorProduct.rightAlgebra in
theorem isDomain_tensor_fractionRing (T O : Type) [CommRing T] [IsDomain T] [CommRing O] [IsDomain O]
    [Algebra T O] (hinj : Function.Injective (algebraMap T O)) : IsDomain (O ⊗[T] FractionRing T) := by
  haveI : IsLocalization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))
      (O ⊗[T] FractionRing T) := by
    rw [Algebra.isLocalization_iff_isPushout (nonZeroDivisors T) (FractionRing T)]
    infer_instance
  exact IsLocalization.isDomain_of_le_nonZeroDivisors (M := Algebra.algebraMapSubmonoid O (nonZeroDivisors T))
    (O ⊗[T] FractionRing T) (by
      rintro _ ⟨a, ha, rfl⟩
      exact mem_nonZeroDivisors_of_ne_zero ((map_ne_zero_iff _ hinj).mpr (nonZeroDivisors.ne_zero ha)))

theorem eqv_local : ∀ (q : ℕ) [NeZero q] (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T], AIC T →
    IsUnit (q : T) → ∀ (O : Type) [CommRing O] [Algebra (Polynomial T) O] [Algebra T O]
    [IsScalarTower T (Polynomial T) O], SH O → IndEt (Polynomial T) O → ∀ i : ℤ,
    Eqv _ (spMap (Algebra.TensorProduct.includeRight (R := T) (A := FractionRing T) (B := O)).toRingHom)
      (tw q i) := by
  intro q _ T _ _ _ hT hq O _ _ _ _ hSH hInd i
  unfold Eqv
  intro n
  have hfac : ∀ a : O, ∃ (E : Type) (_ : CommRing E) (_ : Algebra (Polynomial T) E)
      (_ : Algebra.Etale (Polynomial T) E) (φ : E →ₐ[Polynomial T] O), a ∈ φ.range := by
    intro a
    obtain ⟨C, _, _, _, ψ, χ, h⟩ := exists_etale_factor_of_indEt (Polynomial T) O hInd
      (Polynomial (Polynomial T)) (Polynomial.aeval a)
    refine ⟨C, ‹_›, ‹_›, ‹_›, χ, ⟨ψ Polynomial.X, ?_⟩⟩
    have := DFunLike.congr_fun h Polynomial.X
    simpa using this
  rcases lt_trichotomy n 0 with hn | rfl | hn
  · have h1 : ∀ E : Spc, ∀ n : ℤ, n < 0 → Subsingleton (H (ZMod q) E (tw q i) n) := by
      intro E n hn
      have hz : ∀ α : CochainComplex.HomComplex.Cochain ((chains (ZMod q)).obj E)
          (res (ZMod q) (tw q i)) n, α = 0 := by
        intro α
        apply (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.2.1 α 0
        intro p s h U x
        have hs : s < 0 := by omega
        haveI := ((GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_sections_exactness
          (ZMod q) (tw q i) U).2.2.2 s hs)
        exact Subsingleton.elim _ _
      refine ⟨fun a b => ?_⟩
      obtain ⟨a, rfl⟩ := a.mk_surjective
      obtain ⟨b, rfl⟩ := b.mk_surjective
      have : a = b := CochainComplex.HomComplex.Cocycle.ext (by rw [hz a.1, hz b.1])
      rw [this]
    haveI := h1 (sp O) n hn
    haveI := h1 (sp (TensorProduct T (FractionRing T) O)) n hn
    exact bijective_of_subsingleton _ 0
  · haveI : IsIntegrallyClosed T := GlobalTheory.AICStalk.isIntegrallyClosed_of_aic hT
    obtain ⟨hH, -⟩ := hSH
    haveI : IsLocalRing O := hH.toIsLocalRing
    haveI : IsDomain O := GlobalTheory.AICStalk.isDomain_of_indEt hInd
    have hinjX : Function.Injective (algebraMap (Polynomial T) O) :=
      GlobalTheory.AICStalk.algebraMap_injective_of_indEt hInd
    have hinj : Function.Injective (algebraMap T O) := by
      rw [IsScalarTower.algebraMap_eq T (Polynomial T) O]
      exact hinjX.comp (Polynomial.C_injective)
    haveI : IsDomain (O ⊗[T] FractionRing T) := isDomain_tensor_fractionRing T O hinj
    haveI : IsDomain (TensorProduct T (FractionRing T) O) :=
      MulEquiv.isDomain _ (Algebra.TensorProduct.comm T (FractionRing T) O).toRingEquiv.toMulEquiv
    have hqO : IsUnit (q : O) := by
      have := hq.map (algebraMap T O)
      rwa [map_natCast] at this
    obtain ⟨z, hz⟩ := hT (Polynomial.cyclotomic q T) (Polynomial.cyclotomic.monic q T) (by
      rw [Polynomial.natDegree_cyclotomic]; exact Nat.totient_pos.2 (NeZero.pos q))
    have hζ : Polynomial.aeval (algebraMap T O z) (Polynomial.cyclotomic q ℤ) = 0 := by
      rw [Polynomial.aeval_algebraMap_apply, Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map,
        Polynomial.map_cyclotomic, hz, map_zero]
    exact GlobalTheory.T.h_zero_pullback_twist_bijective q O (TensorProduct T (FractionRing T) O)
      (Algebra.TensorProduct.includeRight (R := T) (A := FractionRing T) (B := O)).toRingHom hqO
      ⟨_, hζ⟩ inferInstance (idem_of_domain) (idem_of_domain) i
  · haveI : Subsingleton (H (ZMod q) (sp O) (tw q i) n) := GlobalTheory.T.strictlyHenselianLocalRing_acyclic_every_sheaf (ZMod q) O hSH (tw q i) n hn
    haveI : Subsingleton (H (ZMod q) (sp (TensorProduct T (FractionRing T) O)) (tw q i) n) := by
      rcases (show n = 1 ∨ 2 ≤ n by omega) with rfl | h2
      · exact GlobalTheory.T.subsingleton_ht_one_genericFibre_of_sh_etale_cover q T hT hq O hSH hfac i
      · exact GlobalTheory.T.subsingleton_etaleCohomology_genericFibre_henselianLine q T hT hq O hSH hInd n i h2
    exact bijective_of_subsingleton _ 0

end GlobalTheory.EtC.LineLocal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyEquivStrictHenselianLinePointStatement
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleCohomology_equiv_strictHenselian_line_point : ∀ (q : ℕ) [NeZero q] (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T], AIC T → IsUnit (q : T) → ∀ (O : Type) [CommRing O] [Algebra (Polynomial T) O] [Algebra T O] [IsScalarTower T (Polynomial T) O], SH O → IndEt (Polynomial T) O → ∀ i : ℤ, Eqv _ (spMap (Algebra.TensorProduct.includeRight (R := T) (A := FractionRing T) (B := O)).toRingHom) (tw q i) := by
  first | (exact @GlobalTheory.EtC.LineLocal.eqv_local) | (exact GlobalTheory.EtC.LineLocal.eqv_local) | (intros; apply GlobalTheory.EtC.LineLocal.eqv_local  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyIndEtaleBaseChange
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC TensorProduct

noncomputable section

namespace GlobalTheory.EtC.LineAcyc

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  dsimp only [spMap]
  rw [CommRingCat.ofHom_comp, Spec.map_comp, Functor.map_comp]

theorem spMap_id' (A : Type) [CommRing A] : spMap (RingHom.id A) = 𝟙 (sp A) := by
  dsimp only [spMap]
  rw [CommRingCat.ofHom_id, Spec.map_id]
  exact sch.map_id _

theorem pull_bijective_of_ringEquiv {A B : Type} [CommRing A] [CommRing B] (e : A ≃+* B)
    (R : Type) [CommRing R] (F : Shv R) (n : ℤ) :
    Function.Bijective (pull R (spMap (e : A →+* B)) F n) := by
  have h1 : ∀ x, pull R (spMap (e.symm : B →+* A)) F n (pull R (spMap (e : A →+* B)) F n x) = x := by
    intro x
    rw [← pull_comp, ← spMap_comp', show ((e.symm : B →+* A).comp (e : A →+* B)) = RingHom.id A by
      ext; simp, spMap_id', pull_id]
  have h2 : ∀ x, pull R (spMap (e : A →+* B)) F n (pull R (spMap (e.symm : B →+* A)) F n x) = x := by
    intro x
    rw [← pull_comp, ← spMap_comp', show ((e : A →+* B).comp (e.symm : B →+* A)) = RingHom.id B by
      ext; simp, spMap_id', pull_id]
  exact ⟨Function.LeftInverse.injective h1, Function.RightInverse.surjective h2⟩

theorem eqv_of_square {X Y X' Y' : Type} [CommRing X] [CommRing Y] [CommRing X'] [CommRing Y']
    (g : X →+* Y) (g' : X' →+* Y') (eX : X ≃+* X') (eY : Y ≃+* Y')
    (h : (eY : Y →+* Y').comp g = g'.comp (eX : X →+* X')) {R : Type} [CommRing R] (F : Shv R) :
    Eqv R (spMap g') F → Eqv R (spMap g) F := by
  intro hg' n
  have hc : spMap (eY : Y →+* Y') ≫ spMap g = spMap g' ≫ spMap (eX : X →+* X') := by
    rw [← spMap_comp', ← spMap_comp', h]
  have key : (pull R (spMap (eY : Y →+* Y')) F n) ∘ (pull R (spMap g) F n) =
      (pull R (spMap g') F n) ∘ (pull R (spMap (eX : X →+* X')) F n) := by
    funext x
    simp only [Function.comp_apply]
    rw [← pull_comp, ← pull_comp, hc]
  have hY := pull_bijective_of_ringEquiv eY R F n
  have hX := pull_bijective_of_ringEquiv eX R F n
  refine (Function.Bijective.of_comp_iff' hY _).mp ?_
  rw [key]
  exact (hg' n).comp hX

end GlobalTheory.EtC.LineAcyc

namespace GlobalTheory.EtC.LineAcyc

theorem affineLine_localAcyclicity_of_strictHenselian_points (core : ∀ (q : ℕ) [NeZero q] (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T], AIC T → IsUnit (q : T) →
    ∀ (O : Type) [CommRing O] [Algebra (Polynomial T) O] [Algebra T O] [IsScalarTower T (Polynomial T) O],
    SH O → IndEt (Polynomial T) O → ∀ i : ℤ,
    Eqv _ (spMap (Algebra.TensorProduct.includeRight (R := T) (A := FractionRing T) (B := O)).toRingHom) (tw q i)) : C3 := by
  intro q _ T _ _ _ hT hq B _ _ _ _ _ i

  have hB := GlobalTheory.T.etaleCohomology_local_to_global_ringMap_indEtale (ZMod q) (tw q i) (GlobalTheory.T.tateTwist_finitary q i) B B (B ⊗[T] FractionRing T)
    (Algebra.ofId B (B ⊗[T] FractionRing T))

  refine eqv_of_square _ (Algebra.ofId B (B ⊗[T] FractionRing T)).toRingHom (RingEquiv.refl B)
    (Algebra.TensorProduct.comm T (FractionRing T) B).toRingEquiv ?_ _ (hB ?_)
  · ext b
    simp [Algebra.TensorProduct.algebraMap_apply]
  intro O _ _ hO hOi
  letI : Algebra (Polynomial T) O := ((algebraMap B O).comp (algebraMap (Polynomial T) B)).toAlgebra
  letI : Algebra T O := ((algebraMap B O).comp (algebraMap T B)).toAlgebra
  haveI : IsScalarTower T (Polynomial T) O := IsScalarTower.of_algebraMap_eq fun x => by
    show algebraMap B O (algebraMap T B x) = algebraMap B O (algebraMap (Polynomial T) B (algebraMap T (Polynomial T) x))
    rw [IsScalarTower.algebraMap_apply T (Polynomial T) B x]
  haveI : IsScalarTower T B O := IsScalarTower.of_algebraMap_eq fun x => rfl
  have hOi' : IndEt (Polynomial T) O :=
    isIndEtale_comp_etale (algebraMap (Polynomial T) B) (RingHom.etale_algebraMap.2 inferInstance)
      (algebraMap B O) hOi
  have hc := core q T hT hq O hO hOi' i
  refine eqv_of_square _ _ (Algebra.TensorProduct.rid B B O).toRingEquiv
    ((Algebra.TensorProduct.cancelBaseChange T B B O (FractionRing T)).toRingEquiv.trans
      (Algebra.TensorProduct.comm T O (FractionRing T)).toRingEquiv) ?_ _ hc
  refine RingHom.ext fun x => ?_
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul o b => simp [Algebra.smul_def]
  | add x y hx hy => simp only [map_add (f := _)] at hx hy ⊢; rw [hx, hy]

end GlobalTheory.EtC.LineAcyc

namespace GlobalTheory.EtC.LineAcyc

theorem c3 : C3 := affineLine_localAcyclicity_of_strictHenselian_points GlobalTheory.T.etaleCohomology_equiv_strictHenselian_line_point

end GlobalTheory.EtC.LineAcyc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyIndEtaleBaseChangeStatement
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_cohomology_ind_etale_base_change : GlobalTheory.EtC.C3 := by
  first | (exact @GlobalTheory.EtC.LineAcyc.c3) | (exact GlobalTheory.EtC.LineAcyc.c3) | (intros; apply GlobalTheory.EtC.LineAcyc.c3  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalTrivialityOfNoetherianDescent
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFgModel
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AmpleFibreMove

theorem exists_fg_model :
    ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G], IsAbelianScheme G → ∀ L : LB G.left, L.IsLB →
    ∃ (S : Subring R) (G₀ : Over (Sp S)) (_ : GrpObj G₀) (φ : G.left ⟶ G₀.left) (L₀ : LB G₀.left),
      Algebra.FiniteType ℤ S ∧ IsAbelianScheme G₀ ∧ IsGrpPullback G G₀ (spMap S.subtype) φ ∧ L₀.IsLB ∧
        LBIso L (L₀.pull φ) := by
  intro R _ G _ hG L hL
  classical
  obtain ⟨S₀, B₀, _, φ₀, -, hft₀, hab₀, hpb₀⟩ :=
    GlobalTheory.AbelianLimit.abelianScheme_descends_to_fg_subring_anyDim R G ∅ hG
  have := hab₀.comm
  have := hab₀.smooth
  have := hab₀.proper
  have := hab₀.geomConnected
  obtain ⟨SP, hSP⟩ := GlobalTheory.LBLimit.lb_descends_to_fg_subring R S₀ G.left B₀.left
    G.hom B₀.hom φ₀ L hpb₀.1 hL
  obtain ⟨R₁, h, hT, hft⟩ := GlobalTheory.KeyTf.exists_finiteType_subring_adjoin R S₀ SP hft₀
  let t : Sp R₁ ⟶ Sp S₀ := spMap (Subring.inclusion h)
  have e : spMap R₁.subtype ≫ t = spMap S₀.subtype := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  let G₁ : Over (Sp R₁) := (Over.pullback t).obj B₀
  have hab₁ : IsAbelianScheme G₁ :=
    { comm := inferInstance
      smooth := inferInstanceAs (Smooth (pullback.snd B₀.hom t))
      proper := inferInstanceAs (IsProper (pullback.snd B₀.hom t))
      geomConnected := inferInstanceAs (GeometricallyConnected (pullback.snd B₀.hom t)) }
  have hpb₁ : IsPullback (pullback.fst B₀.hom t) G₁.hom B₀.hom t := IsPullback.of_hasPullback _ _
  have wφ : φ₀ ≫ B₀.hom = (G.hom ≫ spMap R₁.subtype) ≫ t := by
    rw [Category.assoc, e]; exact hpb₀.1.w
  let φ : G.left ⟶ G₁.left := pullback.lift φ₀ (G.hom ≫ spMap R₁.subtype) wφ
  have hφ₁ : φ ≫ pullback.fst B₀.hom t = φ₀ := pullback.lift_fst _ _ _
  have hφ₂ : φ ≫ G₁.hom = G.hom ≫ spMap R₁.subtype := pullback.lift_snd _ _ _
  have hφ : IsGrpPullback G G₁ (spMap R₁.subtype) φ :=
    (isGrpPullback_pullback B₀ t).cancel (hpb₀.congr e.symm hφ₁.symm) hφ₂
  obtain ⟨L₁, hL₁, hiso⟩ := hSP R₁ h hT G₁.left G₁.hom (pullback.fst B₀.hom t) φ hpb₁ hφ₁ hφ₂
  exact ⟨R₁, G₁, inferInstance, φ, L₁, hft, hab₁, hφ, hL₁, hiso⟩

end GlobalTheory.AmpleFibreMove
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalTrivialityOfNoetherianDescent
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.LocTrivDescent
open GlobalTheory.CechPic

theorem triv_iff {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) (f : Y ⟶ X) :
    (∃ t : (L.pull f).Gen, t.IsGen) ↔ CechPic.pull f (cls L hL) = 0 := by
  rw [← cls_pull hL f (pull_isLB hL f), cls_eq_zero_iff]

theorem cls_lbPow_eq {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) (k : ℕ) (h : (Hecke.lbPow L k).IsLB) :
    cls _ h = k • cls L hL :=
  (cls_linComb hL _ _ h).trans (by simp [pull_id])

theorem one_left_comp {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) :
    (1 : 𝟙_ (Over S') ⟶ G').left ≫ φ = f ≫ (1 : 𝟙_ (Over S) ⟶ G).left := by
  have e := congrArg (fun z => z.left) (map_one (pushHom h (𝟙_ (Over S'))))
  let U : Over.mk ((𝟙_ (Over S')).hom ≫ f) ⟶ 𝟙_ (Over S) := Over.homMk f (by simp)
  have e2 : (1 : Over.mk ((𝟙_ (Over S')).hom ≫ f) ⟶ G) = U ≫ 1 := (comp_one U).symm
  exact e.trans (by rw [e2]; rfl)

theorem fibre_triv {R R₁ : Type} [CommRing R] [CommRing R₁] (j : R₁ →+* R) {A : Over (Sp R)} {A₁ : Over (Sp R₁)}
    {ψ : A.left ⟶ A₁.left} (hψ : IsPullback ψ A.hom A₁.hom (spMap j)) {K : Type} [Field K] (g₀ : R →+* K)
    (c : Pic A₁.left) (h : CechPic.pull (pullback.fst A.hom (spMap g₀)) (CechPic.pull ψ c) = 0) :
    CechPic.pull (pullback.fst A₁.hom (spMap (g₀.comp j))) c = 0 := by
  have w : pullback.fst A₁.hom (spMap (g₀.comp j)) ≫ A₁.hom =
      (pullback.snd A₁.hom (spMap (g₀.comp j)) ≫ spMap g₀) ≫ spMap j := by
    rw [pullback.condition, Category.assoc, GlobalTheory.spMap_comp_ring]
  let a := hψ.lift _ _ w
  have ha1 : a ≫ ψ = pullback.fst _ _ := hψ.lift_fst _ _ _
  have ha2 : a ≫ A.hom = pullback.snd _ _ ≫ spMap g₀ := hψ.lift_snd _ _ _
  let n := pullback.lift a (pullback.snd _ _) ha2
  have hn : n ≫ pullback.fst A.hom (spMap g₀) = a := pullback.lift_fst _ _ _
  rw [← ha1, ← hn, Category.assoc, pull_comp, pull_comp, h, map_zero]

theorem basicOpen_triv {R R₁ : Type} [CommRing R] [CommRing R₁] (j : R₁ →+* R) {A : Over (Sp R)}
    {A₁ : Over (Sp R₁)} {ψ : A.left ⟶ A₁.left} (w : ψ ≫ A₁.hom = A.hom ≫ spMap j) (c : Pic A₁.left) (r : R₁)
    (h : CechPic.pull (A₁.hom ⁻¹ᵁ PrimeSpectrum.basicOpen r).ι c = 0) :
    CechPic.pull (A.hom ⁻¹ᵁ PrimeSpectrum.basicOpen (j r)).ι (CechPic.pull ψ c) = 0 := by
  have le : A.hom ⁻¹ᵁ PrimeSpectrum.basicOpen (j r) ≤ ψ ⁻¹ᵁ (A₁.hom ⁻¹ᵁ PrimeSpectrum.basicOpen r) := by
    intro x hx
    have e : A₁.hom.base (ψ.base x) = (spMap j).base (A.hom.base x) := by
      rw [← Scheme.Hom.comp_apply, w, Scheme.Hom.comp_apply]
    show A₁.hom.base (ψ.base x) ∈ PrimeSpectrum.basicOpen r
    rw [e]
    exact hx
  rw [← pull_comp, ← Scheme.Hom.resLE_comp_ι ψ le, pull_comp, h, map_zero]

end GlobalTheory.LocTrivDescent

namespace GlobalTheory.LocTrivDescent
open GlobalTheory.CechPic

theorem cls_spread (S : Type) [CommRing S] (R₀ : Subring S) (X X₀ : Scheme.{0}) (f : X ⟶ Sp S) (f₀ : X₀ ⟶ Sp R₀)
    (π : X ⟶ X₀) [QuasiCompact f₀] [QuasiSeparated f₀] (M : LB X₀) (hM : M.IsLB)
    (hp : IsPullback π f f₀ (spMap R₀.subtype)) (h0 : CechPic.pull π (cls M hM) = 0) :
    ∃ F : Finset S, ∀ (R₁ : Subring S) (h : R₀ ≤ R₁), (F : Set S) ⊆ R₁ → ∀ (X₁ : Scheme.{0}) (f₁ : X₁ ⟶ Sp R₁)
      (π₁ : X₁ ⟶ X₀), IsPullback π₁ f₁ f₀ (spMap (Subring.inclusion h)) → CechPic.pull π₁ (cls M hM) = 0 := by
  have hT := LB.isLB_triv X₀
  have z : cls (LB.triv X₀) hT = 0 := rfl
  have key : ∀ {Y : Scheme.{0}} (g : Y ⟶ X₀),
      CechPic.pull g (cls M hM) = 0 ↔ LBIso (M.pull g) ((LB.triv X₀).pull g) := by
    intro Y g
    rw [← cls_eq_iff (pull_isLB hM g) (pull_isLB hT g), cls_pull hM, cls_pull hT, z, map_zero]
  obtain ⟨F, hF⟩ := GlobalTheory.lbIso_descends_to_subring_containing_finset S R₀ X X₀ f f₀ π M (LB.triv X₀) hp hM hT
    ((key π).1 h0)
  exact ⟨F, fun R₁ h hs X₁ f₁ π₁ hp₁ => (key π₁).2 (hF R₁ h hs X₁ f₁ π₁ hp₁)⟩

theorem locTriv_of_noetherian : (∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ (M : LB A.left), M.IsLB → (∃ t : (M.pull (1 : 𝟙_ (Over (Sp R)) ⟶ A).left).Gen, t.IsGen) → ∀ k : ℕ, IsUnit (k : R) → (∃ t : (GlobalTheory.UPel.HT.Hecke.lbPow M k).Gen, t.IsGen) → ∀ (K : Type) [Field K] (g₀ : R →+* K), (∃ t : (M.pull (pullback.fst A.hom (spMap g₀))).Gen, t.IsGen) → ∃ r : R, g₀ r ≠ 0 ∧ ∃ t : (M.pull (A.hom ⁻¹ᵁ PrimeSpectrum.basicOpen r).ι).Gen, t.IsGen) → ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ (M : LB A.left), M.IsLB → (∃ t : (M.pull (1 : 𝟙_ (Over (Sp R)) ⟶ A).left).Gen, t.IsGen) → ∀ k : ℕ, IsUnit (k : R) → (∃ t : (GlobalTheory.UPel.HT.Hecke.lbPow M k).Gen, t.IsGen) → ∀ (K : Type) [Field K] (g₀ : R →+* K), (∃ t : (M.pull (pullback.fst A.hom (spMap g₀))).Gen, t.IsGen) → ∃ r : R, g₀ r ≠ 0 ∧ ∃ t : (M.pull (A.hom ⁻¹ᵁ PrimeSpectrum.basicOpen r).ι).Gen, t.IsGen := by
  intro H R _ A _ hA M hM h1 k hk h2 K _ g₀ h3
  classical
  obtain ⟨S, G₀, _, φ, L₀, hft, hab, hφ, hL₀, hiso⟩ := GlobalTheory.AmpleFibreMove.exists_fg_model R A hA M hM
  have := hab.proper
  set c₀ := cls L₀ hL₀ with hc₀
  have hc : cls M hM = CechPic.pull φ c₀ := by
    rw [hc₀, ← cls_pull hL₀ φ (pull_isLB hL₀ φ)]
    exact (cls_eq_iff _ _).2 hiso

  let e₀ : Sp S ⟶ G₀.left := (1 : 𝟙_ (Over (Sp S)) ⟶ G₀).left
  have ha : CechPic.pull (spMap S.subtype) (CechPic.pull e₀ c₀) = 0 := by
    rw [← pull_comp, ← one_left_comp hφ, pull_comp, ← hc]
    exact (triv_iff hM _).1 h1
  obtain ⟨F₁, hF₁⟩ := cls_spread R S (Sp R) (Sp S) (𝟙 _) (𝟙 _) (spMap S.subtype) (L₀.pull e₀)
    (pull_isLB hL₀ e₀) (IsPullback.id_vert _) ha

  have hP₀ : (Hecke.lbPow L₀ k).IsLB := LB.isLB_linComb hL₀ _ _
  have hb : CechPic.pull φ (cls _ hP₀) = 0 := by
    obtain ⟨t, ht⟩ := h2
    have hPM : (Hecke.lbPow M k).IsLB := LB.isLB_linComb hM _ _
    have e := (cls_eq_zero_iff hPM).2 ⟨t, ht⟩
    rw [cls_lbPow_eq hM, hc] at e
    rw [cls_lbPow_eq hL₀, map_nsmul]
    exact e
  obtain ⟨F₂, hF₂⟩ := cls_spread R S A.left G₀.left A.hom G₀.hom φ _ hP₀ hφ.1 hb

  obtain ⟨u, hu⟩ : ∃ u : R, (k : R) * u = 1 := ⟨_, hk.mul_val_inv⟩
  obtain ⟨R₁, h, hT, hft₁⟩ := GlobalTheory.KeyTf.exists_finiteType_subring_adjoin R S (F₁ ∪ F₂ ∪ {u}) hft
  have hT₁ : (F₁ : Set R) ⊆ R₁ := fun x hx => hT (by simp [hx])
  have hT₂ : (F₂ : Set R) ⊆ R₁ := fun x hx => hT (by simp [hx])
  have hu₁ : u ∈ R₁ := hT (by simp)
  have : IsNoetherianRing R₁ := Algebra.FiniteType.isNoetherianRing ℤ R₁
  let t : Sp R₁ ⟶ Sp S := spMap (Subring.inclusion h)
  have et : spMap R₁.subtype ≫ t = spMap S.subtype := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  have := hab.comm
  have := hab.smooth
  have := hab.geomConnected
  letI : GrpObj ((Over.pullback t).obj G₀) := Functor.grpObjObj
  let A₁ : Over (Sp R₁) := (Over.pullback t).obj G₀
  have hab₁ : IsAbelianScheme A₁ :=
    { comm := inferInstance
      smooth := inferInstanceAs (Smooth (pullback.snd G₀.hom t))
      proper := inferInstanceAs (IsProper (pullback.snd G₀.hom t))
      geomConnected := inferInstanceAs (GeometricallyConnected (pullback.snd G₀.hom t)) }
  have hpb₁ : IsPullback (pullback.fst G₀.hom t) A₁.hom G₀.hom t := IsPullback.of_hasPullback _ _
  have wφ : φ ≫ G₀.hom = (A.hom ≫ spMap R₁.subtype) ≫ t := by
    rw [Category.assoc, et]; exact hφ.1.w
  let ψ : A.left ⟶ A₁.left := pullback.lift φ (A.hom ≫ spMap R₁.subtype) wφ
  have hψ₁ : ψ ≫ pullback.fst G₀.hom t = φ := pullback.lift_fst _ _ _
  have hψ₂ : ψ ≫ A₁.hom = A.hom ≫ spMap R₁.subtype := pullback.lift_snd _ _ _
  have hψ : IsGrpPullback A A₁ (spMap R₁.subtype) ψ :=
    (isGrpPullback_pullback G₀ t).cancel (hφ.congr et.symm hψ₁.symm) hψ₂
  let M₁ : LB A₁.left := L₀.pull (pullback.fst G₀.hom t)
  have hM₁ : M₁.IsLB := pull_isLB hL₀ _
  have hc₁ : cls M₁ hM₁ = CechPic.pull (pullback.fst G₀.hom t) c₀ := cls_pull hL₀ _ _
  have hcM : cls M hM = CechPic.pull ψ (cls M₁ hM₁) := by
    rw [hc₁, ← pull_comp, hψ₁, hc]
  obtain ⟨r, hr, hgen⟩ := H R₁ A₁ hab₁ M₁ hM₁
    ((triv_iff hM₁ _).2 (by
      rw [hc₁, ← pull_comp, one_left_comp (isGrpPullback_pullback G₀ t), pull_comp]
      exact hF₁ R₁ h hT₁ (Sp R₁) (𝟙 _) t (IsPullback.id_vert _)))
    k (isUnit_iff_exists_inv.2 ⟨⟨u, hu₁⟩, Subtype.ext (by simpa using hu)⟩)
    (by
      have hPM₁ : (Hecke.lbPow M₁ k).IsLB := LB.isLB_linComb hM₁ _ _
      refine (cls_eq_zero_iff hPM₁).1 ?_
      rw [cls_lbPow_eq hM₁, hc₁, ← map_nsmul, ← cls_lbPow_eq hL₀ k hP₀]
      exact hF₂ R₁ h hT₂ A₁.left A₁.hom _ hpb₁)
    K (g₀.comp R₁.subtype)
    ((triv_iff hM₁ _).2 (fibre_triv R₁.subtype hψ.1 g₀ _ (by rw [← hcM]; exact (triv_iff hM _).1 h3)))
  refine ⟨r, hr, (triv_iff hM _).2 ?_⟩
  rw [hcM]
  exact basicOpen_triv R₁.subtype hψ₂ _ r ((triv_iff hM₁ _).1 hgen)

end GlobalTheory.LocTrivDescent
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalTrivialityOfNoetherianDescentStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localTriviality_of_noetherian_descent : (∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ (M : LB A.left), M.IsLB → (∃ t : (M.pull (1 : 𝟙_ (Over (Sp R)) ⟶ A).left).Gen, t.IsGen) → ∀ k : ℕ, IsUnit (k : R) → (∃ t : (GlobalTheory.UPel.HT.Hecke.lbPow M k).Gen, t.IsGen) → ∀ (K : Type) [Field K] (g₀ : R →+* K), (∃ t : (M.pull (pullback.fst A.hom (spMap g₀))).Gen, t.IsGen) → ∃ r : R, g₀ r ≠ 0 ∧ ∃ t : (M.pull (A.hom ⁻¹ᵁ PrimeSpectrum.basicOpen r).ι).Gen, t.IsGen) → ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ (M : LB A.left), M.IsLB → (∃ t : (M.pull (1 : 𝟙_ (Over (Sp R)) ⟶ A).left).Gen, t.IsGen) → ∀ k : ℕ, IsUnit (k : R) → (∃ t : (GlobalTheory.UPel.HT.Hecke.lbPow M k).Gen, t.IsGen) → ∀ (K : Type) [Field K] (g₀ : R →+* K), (∃ t : (M.pull (pullback.fst A.hom (spMap g₀))).Gen, t.IsGen) → ∃ r : R, g₀ r ≠ 0 ∧ ∃ t : (M.pull (A.hom ⁻¹ᵁ PrimeSpectrum.basicOpen r).ι).Gen, t.IsGen := by
  first | (exact @GlobalTheory.LocTrivDescent.locTriv_of_noetherian) | (exact GlobalTheory.LocTrivDescent.locTriv_of_noetherian) | (intros; apply GlobalTheory.LocTrivDescent.locTriv_of_noetherian <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyIntersectionEqLineBundleIntersecti
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyIntersectionEqLineBundleIntersecti
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem inter_cls_eq_interNum : ∀ (K : Type) [Field K] (A : AbVar K) (J : Type) [Fintype J] (L : J → LB A.X.left) (hL : ∀ j, (L j).IsLB), inter A (fun j => cls (L j) (hL j)) = (letI := A.algΓ; interNum K (structureModule A.X.left) L) := by
  intro K _ A J _ L hL
  letI := A.algΓ
  exact (interNum_eq_multiDiff K (structureModule A.X.left) hL).symm

end GlobalTheory.AV.AbVar
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyIntersectionEqLineBundleIntersectiStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianVariety_intersection_eq_lineBundleIntersection : ∀ (K : Type) [Field K] (A : AbVar K) (J : Type) [Fintype J] (L : J → LB A.X.left) (hL : ∀ j, (L j).IsLB), inter A (fun j => cls (L j) (hL j)) = (letI := A.algΓ; interNum K (structureModule A.X.left) L) := by
  first | exact @GlobalTheory.AV.AbVar.inter_cls_eq_interNum | exact GlobalTheory.AV.AbVar.inter_cls_eq_interNum | (intros; apply GlobalTheory.AV.AbVar.inter_cls_eq_interNum <;> assumption)
end
end
