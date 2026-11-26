module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SizesOfSizeRows
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorNegSpaceFrameChangeConjSubst
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyDefiniteSpacesStandardAndLarge
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockMatrixMulVecBasis
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceAdjointMatrixIsCoordinateEquivariant
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceAdjointMatrixIsCoordinateEquivariant
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PlaceTensor.AdjCoord

variable {D : D7} {v : FinPl D}

def conjProj (φ : SplitProj D v) : SplitProj D v :=
  φ.comp (Algebra.TensorProduct.map (AlgHom.id (Fv D.host.F v) (Fv D.host.F v)) D.sp.cm.sig)

theorem rdA_conjProj (φ : SplitProj D v) (a : AE D) : rdA (conjProj φ) a = rdA φ (cA D a) := by
  induction a using TensorProduct.induction_on with
  | zero => simp only [_root_.map_zero]
  | tmul x y =>
    simp only [rdA, conjProj, RingHom.comp_apply, cA, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, GlobalTheory.AdelicU.compFin,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.comp_apply, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
  | add x y hx hy => simp only [_root_.map_add (f := _), hx, hy]

theorem isIdemOf_conjProj {φ : SplitProj D v} {e : AE D} (he : IsIdemOf φ e) : IsIdemOf (conjProj φ) (cA D e) := by
  have hcc : ∀ x : AE D, cA D (cA D x) = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp only [_root_.map_zero]
    | tmul a y =>
      simp only [cA, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul,
        AlgHom.id_apply]
      congr 1
      exact star_star y
    | add x y hx hy => simp only [_root_.map_add (f := _), hx, hy]
  refine ⟨GlobalTheory.SplitScalar.isSplitIdem_conj he.1, ?_, ?_⟩
  · rw [hcc, add_comm]; exact he.2.1
  · rw [rdA_conjProj, hcc]; exact he.2.2

def trHomeo {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] {m n : ℕ}
    (A A' : Matrix (Fin n) (Fin n) K) (B B' : Matrix (Fin m) (Fin m) K) (hA : A' * A = 1) (hB : B * B' = 1) :
    Matrix (Fin m) (Fin n) K ≃ₜ Matrix (Fin n) (Fin m) K where
  toFun y := A * yᵀ * B
  invFun z := (A' * z * B')ᵀ
  left_inv y := by
    have : A' * (A * yᵀ * B) * B' = (A' * A) * yᵀ * (B * B') := by simp only [Matrix.mul_assoc]
    simp only [this, hA, hB, Matrix.one_mul, Matrix.mul_one, Matrix.transpose_transpose]
  right_inv z := by
    have : A * (A' * z * B') * B = (A * A') * z * (B' * B) := by simp only [Matrix.mul_assoc]
    simp only [Matrix.transpose_transpose, this, mul_eq_one_comm.1 hA, mul_eq_one_comm.1 hB, Matrix.one_mul,
      Matrix.mul_one]
  continuous_toFun := (continuous_const.matrix_mul continuous_id.matrix_transpose).matrix_mul continuous_const
  continuous_invFun := ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const).matrix_transpose

theorem isCoord_comp {S T : HSp D} {m n : ℕ} {a : AE D} {Λ : AddSubgroup (WO S T)}
    {κ : WO S T → Matrix (Fin m) (Fin n) (Fv D.host.F v)} (h : IsCoord a Λ κ)
    (A A' : Matrix (Fin n) (Fin n) (Fv D.host.F v)) (B B' : Matrix (Fin m) (Fin m) (Fv D.host.F v))
    (hA : A' * A = 1) (hB : B * B' = 1) : IsCoord a Λ (fun t => A * (κ t)ᵀ * B) := by
  have e : (fun t => A * (κ t)ᵀ * B) = ⇑(trHomeo A A' B B' hA hB) ∘ κ := rfl
  refine ⟨fun x y => ?_, ?_, ?_, ?_⟩
  · simp only [h.1 x y, Matrix.transpose_add, Matrix.mul_add, Matrix.add_mul]
  · rw [e]; exact (Set.bijOn_univ.2 (trHomeo A A' B B' hA hB).bijective).comp h.2.1
  · rw [e, Set.image_comp]; exact (trHomeo A A' B B' hA hB).isOpenMap _ h.2.2.1
  · rw [e, Set.image_comp]; exact h.2.2.2.image (trHomeo A A' B B' hA hB).continuous

theorem gram_inv_mul (V : HSp D) : (V.gram⁻¹).map (incA D) * V.gram.map (incA D) = 1 := by
  rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ (GlobalTheory.LatVac.gram_det_isUnit V)]
  exact Matrix.map_one _ (_root_.map_zero _) (_root_.map_one _)

theorem adj_mul {A : Type} [CommRing A] (σ : A →+* A) {a b : ℕ} (G G' k k' : Matrix (Fin a) (Fin a) A)
    (H m m' : Matrix (Fin b) (Fin b) A) (x : Matrix (Fin b) (Fin a) A) (h1 : G' * G = 1)
    (hk : Formalism.UG.cT σ k * G * k = G) (hm : Formalism.UG.cT σ m * H * m = H) (hk' : k * k' = 1) (hm' : m * m' = 1) :
    G' * Formalism.UG.cT σ (m * x * k) * H = k' * (G' * Formalism.UG.cT σ x * H) * m' := by
  have hG : G * G' = 1 := mul_eq_one_comm.1 h1
  have s1 : Formalism.UG.cT σ k * G = G * k' := calc
    Formalism.UG.cT σ k * G = Formalism.UG.cT σ k * G * (k * k') := by rw [hk', Matrix.mul_one]
    _ = (Formalism.UG.cT σ k * G * k) * k' := by simp only [Matrix.mul_assoc]
    _ = G * k' := by rw [hk]
  have e1 : G' * Formalism.UG.cT σ k = k' * G' := calc
    G' * Formalism.UG.cT σ k = G' * (Formalism.UG.cT σ k * (G * G')) := by rw [hG, Matrix.mul_one]
    _ = G' * ((Formalism.UG.cT σ k * G) * G') := by simp only [Matrix.mul_assoc]
    _ = (G' * G) * k' * G' := by rw [s1]; simp only [Matrix.mul_assoc]
    _ = k' * G' := by rw [h1, Matrix.one_mul]
  have e2 : Formalism.UG.cT σ m * H = H * m' := calc
    Formalism.UG.cT σ m * H = Formalism.UG.cT σ m * H * (m * m') := by rw [hm', Matrix.mul_one]
    _ = (Formalism.UG.cT σ m * H * m) * m' := by simp only [Matrix.mul_assoc]
    _ = H * m' := by rw [hm]
  unfold Formalism.UG.cT at *
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_mul, Matrix.transpose_mul]
  calc G' * ((k.map σ)ᵀ * ((x.map σ)ᵀ * (m.map σ)ᵀ)) * H
      = (G' * (k.map σ)ᵀ) * (x.map σ)ᵀ * ((m.map σ)ᵀ * H) := by simp only [Matrix.mul_assoc]
    _ = k' * (G' * (x.map σ)ᵀ * H) * m' := by rw [e1, e2]; simp only [Matrix.mul_assoc]

theorem map_mul_conj {A K : Type} [CommRing A] [CommRing K] (π : A →+* K) {a b : ℕ} (P : GL (Fin a) K) (Q : GL (Fin b) K)
    (k : Matrix (Fin a) (Fin a) A) (m : Matrix (Fin b) (Fin b) A) (X Y : Matrix (Fin a) (Fin b) A) (h : Y = k * X * m) :
    (P⁻¹).val * Y.map π * Q.val =
      ((P⁻¹).val * k.map π * P.val) * ((P⁻¹).val * X.map π * Q.val) * ((Q⁻¹).val * m.map π * Q.val) := by
  subst h
  simp only [Matrix.map_mul, Matrix.mul_assoc, Units.mul_inv_cancel_left]
  first
  | rw [Units.mul_inv_cancel_left]
  | rw [← Matrix.mul_assoc (P : Matrix (Fin a) (Fin a) K), Units.mul_inv, Matrix.one_mul]

theorem mt_mul_mt_inv (V : HSp D) (g : GA D V) : Formalism.L2.Theta.mt V g * Formalism.L2.Theta.mt V g⁻¹ = 1 := by
  unfold Formalism.L2.Theta.mt
  rw [← Units.val_mul, ← _root_.map_mul, _root_.mul_inv_cancel, _root_.map_one, Units.val_one]

theorem grpCo_val (φ : SplitProj D v) (V : HSp D) (B : GL (Fin V.rank) (Fv D.host.F v)) (g : GA D V) :
    (grpCo φ V B g).val = (B⁻¹).val * (Formalism.L2.Theta.mt V g).map (rdA φ) * B.val := rfl

theorem grpCo_inv (φ : SplitProj D v) (V : HSp D) (B : GL (Fin V.rank) (Fv D.host.F v)) (g : GA D V) :
    (grpCo φ V B g)⁻¹ = grpCo φ V B g⁻¹ := by
  simp only [grpCo, _root_.mul_inv_rev, _root_.inv_inv, _root_.map_inv, _root_.mul_assoc]

theorem adjCo_actO (φ : SplitProj D v) (S T : HSp D) (BS : GL (Fin S.rank) (Fv D.host.F v))
    (BT : GL (Fin T.rank) (Fv D.host.F v)) (g : GA D S) (h : GA D T) (t : WO S T) :
    adjCo φ S T BS BT (actO S T g⁻¹ h⁻¹ t) = ((grpCo φ S BS g)⁻¹).val * adjCo φ S T BS BT t * (grpCo φ T BT h).val := by
  have hm' : Formalism.L2.Theta.mt T h⁻¹ * Formalism.L2.Theta.mt T h = 1 := by
    simpa only [_root_.inv_inv] using mt_mul_mt_inv T h⁻¹
  have key := adj_mul (cA D) (S.gram.map (incA D)) ((S.gram⁻¹).map (incA D)) (Formalism.L2.Theta.mt S g)
    (Formalism.L2.Theta.mt S g⁻¹) (T.gram.map (incA D)) (Formalism.L2.Theta.mt T h⁻¹) (Formalism.L2.Theta.mt T h)
    (t : Matrix (Fin T.rank) (Fin S.rank) (AE D)) (gram_inv_mul S) (by exact g.2) (by exact h⁻¹.2)
    (mt_mul_mt_inv S g) hm'
  unfold Formalism.UG.cT at key
  have hact : (actO S T g⁻¹ h⁻¹ t : Matrix (Fin T.rank) (Fin S.rank) (AE D)) =
      Formalism.L2.Theta.mt T h⁻¹ * t * Formalism.L2.Theta.mt S g := by
    first
    | rfl
    | (simp only [actO, _root_.inv_inv]; done)
    | simp [actO]
  unfold adjCo
  rw [hact, key, map_mul_conj (rdA φ) BS BT (Formalism.L2.Theta.mt S g⁻¹) (Formalism.L2.Theta.mt T h) _ _ rfl, grpCo_inv,
    grpCo_val, grpCo_val]

end GlobalTheory.PlaceTensor.AdjCoord

namespace GlobalTheory.PlaceTensor

open AdjCoord

theorem adjCo_isCoord : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ (v : FinPl D) (φ : SplitProj D v) (e : AE D), IsIdemOf φ e → ∀ (BS : GL (Fin S.rank) (Fv D.host.F v)) (BT : GL (Fin T.rank) (Fv D.host.F v)), IsCoord (cA D e) (latO S T ΛS ΛT fun _ => True) (adjCo φ S T BS BT) ∧ ∀ (g : GA D S) (h : GA D T) (t : WO S T), adjCo φ S T BS BT (actO S T g⁻¹ h⁻¹ t) = ((grpCo φ S BS g)⁻¹).val * adjCo φ S T BS BT t * (grpCo φ T BT h).val := by
  intro D S T ΛS ΛT hS hT v φ e he BS BT
  refine ⟨?_, fun g h t => adjCo_actO φ S T BS BT g h t⟩
  have hc := (GlobalTheory.T.splitPlace_matrix_coordinate_on_half D S T ΛS ΛT hS hT v (conjProj φ) (cA D e) (isIdemOf_conjProj he) 1 1).1
  have h1 : ((S.gram⁻¹).map (incA D)).map (rdA φ) * (S.gram.map (incA D)).map (rdA φ) = 1 := by
    rw [← Matrix.map_mul, gram_inv_mul, Matrix.map_one _ (_root_.map_zero _) (_root_.map_one _)]
  have h2 : ((T.gram⁻¹).map (incA D)).map (rdA φ) * (T.gram.map (incA D)).map (rdA φ) = 1 := by
    rw [← Matrix.map_mul, gram_inv_mul, Matrix.map_one _ (_root_.map_zero _) (_root_.map_one _)]
  have hA : ((S.gram.map (incA D)).map (rdA φ) * BS.val) * ((BS⁻¹).val * ((S.gram⁻¹).map (incA D)).map (rdA φ)) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc BS.val, Units.mul_inv, Matrix.one_mul]
    exact mul_eq_one_comm.1 h1
  have hB : ((T.gram.map (incA D)).map (rdA φ) * BT.val) * ((BT⁻¹).val * ((T.gram⁻¹).map (incA D)).map (rdA φ)) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc BT.val, Units.mul_inv, Matrix.one_mul]
    exact mul_eq_one_comm.1 h2
  convert isCoord_comp hc _ _ _ _ hA hB using 1
  funext t
  have ht : (((t : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (cA D))ᵀ).map (rdA φ) =
      ((t : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (rdA (conjProj φ)))ᵀ := by
    ext i j
    simp only [Matrix.map_apply, Matrix.transpose_apply, rdA_conjProj]
  simp only [adjCo, mapCo, Matrix.map_mul, ht, _root_.inv_one, Units.val_one, Matrix.one_mul, Matrix.mul_one,
    Matrix.mul_assoc]

end GlobalTheory.PlaceTensor

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceAdjointMatrixIsCoordinateEquivariantStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlaceAdjointMatrix_isCoordinate_equivariant : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ (v : FinPl D) (φ : SplitProj D v) (e : AE D), IsIdemOf φ e → ∀ (BS : GL (Fin S.rank) (Fv D.host.F v)) (BT : GL (Fin T.rank) (Fv D.host.F v)), IsCoord (cA D e) (latO S T ΛS ΛT fun _ => True) (adjCo φ S T BS BT) ∧ ∀ (g : GA D S) (h : GA D T) (t : WO S T), adjCo φ S T BS BT (actO S T g⁻¹ h⁻¹ t) = ((grpCo φ S BS g)⁻¹).val * adjCo φ S T BS BT t * (grpCo φ T BT h).val := by
  first | exact @GlobalTheory.PlaceTensor.adjCo_isCoord | exact GlobalTheory.PlaceTensor.adjCo_isCoord | (intros; apply GlobalTheory.PlaceTensor.adjCo_isCoord <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ArchimedeanWeilOperatorIntertwinesSchroedinger
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ArchimedeanWeilOperatorIntertwinesSchroedinger
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.ArchUniq GlobalTheory.ArchUniq.Coord GlobalTheory.ArchLine
open scoped Matrix Classical SchwartzMap

noncomputable section

namespace GlobalTheory.ArchHeis

variable {F : Type} [Field F] [NumberField F]

def intFin (κ : Type) : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ :=
  (Set.pi Set.univ fun _ : κ => (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set (FiniteAdeleRing (𝓞 F) F))).indicator 1

theorem intFin_mem (κ : Type) [Fintype κ] : intFin (F := F) κ ∈ SB (κ → FiniteAdeleRing (𝓞 F) F) := by
  set B := Set.pi Set.univ fun _ : κ => (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set (FiniteAdeleRing (𝓞 F) F)) with hB
  have hO : IsOpen B := isOpen_set_pi Set.finite_univ fun _ _ => GroundTheory.Global.isOpen_integralFiniteAdeles
  have hK : IsCompact B := isCompact_univ_pi fun _ => GroundTheory.Global.isCompact_integralFiniteAdeles F
  have hC : IsClosed B := hK.isClosed
  refine ⟨?_, HasCompactSupport.intro hK fun x hx => Set.indicator_of_notMem hx _⟩
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  by_cases hx : x ∈ B
  · refine ⟨_, hO, hx, fun y hy => ?_⟩
    simp only [intFin, ← hB, Set.indicator_of_mem hy, Set.indicator_of_mem hx, Pi.one_apply]
  · refine ⟨_, hC.isOpen_compl, hx, fun y hy => ?_⟩
    simp only [intFin, ← hB, Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]

def refFin (κ : Type) (x : κ → AF F) : ℂ := intFin κ (fun i => (x i).2)

theorem fst_eq_zero_of_ev {a : AF F} (h : evI F a = 0) : a.1 = 0 :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).map_eq_zero_iff.mp h

theorem snd_eq_zero_of_at {κ : Type} {z : κ → AF F} (hz : At (evI F) z) (i : κ) : (z i).2 = 0 := by
  have h0 : evI F ((0, 1) : AF F) = 0 := map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)
  have := congrArg Prod.snd (congrFun (hz (0, 1) h0) i)
  change (((0, 1) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F).2 * (z i).2) = (0 : AF F).2 at this
  rw [one_mul] at this
  exact this

theorem refFin_of_zero (κ : Type) (x : κ → AF F) (hx : ∀ i, (x i).2 = 0) : refFin κ x = 1 := by
  have : (fun i => (x i).2) = 0 := funext hx
  simp only [refFin, this, intFin]
  rw [Set.indicator_of_mem (show (0 : κ → FiniteAdeleRing (𝓞 F) F) ∈ Set.pi Set.univ
    fun _ : κ => (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set (FiniteAdeleRing (𝓞 F) F)) from
      fun i _ => zero_mem (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F))]
  rfl

theorem refFin_liftV {κ : Type} (y : κ → mixedEmbedding.mixedSpace F) : refFin κ (liftV y) = 1 :=
  refFin_of_zero κ _ fun _ => rfl

theorem refFin_add_liftV {κ : Type} (x : κ → AF F) (y : κ → mixedEmbedding.mixedSpace F) :
    refFin κ (x + liftV y) = refFin κ x := by
  have : (fun i => ((x + liftV y) i).2) = fun i => (x i).2 := by
    funext i
    change (x i).2 + 0 = (x i).2
    rw [add_zero]
  simp only [refFin, this]

theorem rest_refFin (κ : Type) [Fintype κ] (f : SInf F κ) :
    Rest (evI F) (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (refFin κ) := by
  refine ⟨fun x z hz => ?_, Submodule.subset_span ⟨f, intFin κ, intFin_mem κ, rfl⟩⟩
  have : (fun i => ((x + z) i).2) = fun i => (x i).2 := by
    funext i
    change (x i).2 + (z i).2 = (x i).2
    rw [snd_eq_zero_of_at hz i, add_zero]
  simp only [refFin, this]

theorem liftV_locV_of_at {κ : Type} {z : κ → AF F} (hz : At (evI F) z) : liftV (locV z) = z := by
  funext i
  refine Prod.ext ?_ ?_
  · exact (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm_apply_apply _
  · exact (snd_eq_zero_of_at hz i).symm

theorem evI_liftV {κ : Type} (y : κ → mixedEmbedding.mixedSpace F) (i : κ) : evI F (liftV y i) = y i :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply _

theorem evH_invTwo : evH F (⅟(2 : AF F)) = algebraMap ℝ (mixedEmbedding.mixedSpace F) (1 / 2) := by
  have h1 : evH F (⅟(2 : AF F)) * 2 = 1 := by
    rw [← map_ofNat (evH F) 2, ← map_mul, invOf_mul_self, map_one]
  have h2 : (2 : mixedEmbedding.mixedSpace F) * algebraMap ℝ (mixedEmbedding.mixedSpace F) (1 / 2) = 1 := by
    rw [← map_ofNat (algebraMap ℝ (mixedEmbedding.mixedSpace F)) 2, ← map_mul]
    norm_num
  calc evH F (⅟(2 : AF F)) = evH F (⅟(2 : AF F)) * (2 * algebraMap ℝ _ (1 / 2)) := by rw [h2, mul_one]
    _ = algebraMap ℝ _ (1 / 2) := by rw [← mul_assoc, h1, one_mul]

theorem schr_tens {κ : Type} [Fintype κ] (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ)
    (v : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F))
    (g : (κ → mixedEmbedding.mixedSpace F) → ℂ) :
    schr ψ (liftV v.1, liftV v.2) (tens (evI F) g (refFin κ)) = tens (evI F) (schrF (trP F κ) v g) (refFin κ) := by
  funext x
  set z : AF F := x ⬝ᵥ liftV v.2 + ⅟(2 : AF F) * (liftV v.1 ⬝ᵥ liftV v.2) with hz
  let finH : AF F →+* FiniteAdeleRing (𝓞 F) F := RingHom.snd _ _
  have hfin : finH z = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hz, dotProduct, map_add (f := _), map_mul, map_sum]
    have e : ∀ i, finH (liftV v.2 i) = 0 := fun _ => rfl
    simp only [e, mul_zero, Finset.sum_const_zero, add_zero]
  have hAt : At (evI F) z := by
    intro c hc
    refine Prod.ext ?_ ?_
    · change c.1 * z.1 = 0
      rw [fst_eq_zero_of_ev hc, zero_mul]
    · change c.2 * finH z = 0
      rw [hfin, mul_zero]
  have htr : Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F z) =
      trP F κ (fun i => evI F (x i)) v.2 + trP F κ v.1 v.2 / 2 := by
    rw [evI_eq, hz]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [dotProduct, map_add (f := _), map_mul, map_sum, ← evI_eq, evI_liftV, trP]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [show evI F (⅟(2 : AF F)) = algebraMap ℝ _ (1 / 2) from evH_invTwo, ← Algebra.smul_def, map_smul, map_sum,
      smul_eq_mul]
    ring
  have hloc : (fun i => evI F ((x + liftV v.1) i)) = (fun i => evI F (x i)) + v.1 := by
    funext i
    simp only [Pi.add_apply, evI_eq, map_add (f := _)]
    exact congrArg (evH F (x i) + ·) (evI_liftV v.1 i)
  simp only [schr, tens, schrF]
  rw [hψ.2.2 z hAt, htr, hloc, refFin_add_liftV]
  ring

end GlobalTheory.ArchHeis

namespace GlobalTheory.ArchHeis

theorem archOp_schrF : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
    IsStd ψ → M.IsWeil ψ χX χW om → (∀ h ∈ UAt σ W (evI F), ∀ f : SInf F (Fin n × Fin d), ∃ f₁ : SInf F (Fin n × Fin d),
      Acts (evI F) (om (1, h)) ⇑f ⇑f₁) →
    ∀ h ∈ UAt σ W (evI F), ∀ (v : (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F))
      (f f₁ : SInf F (Fin n × Fin d)), ⇑f₁ = schrF (trP F (Fin n × Fin d)) v ⇑f →
      ⇑(archOp om h f₁) = schrF (trP F (Fin n × Fin d)) (archAct M h v) ⇑(archOp om h f) := by
  intro F E _ _ _ _ _ σ n d X W M ψ χX χW om hψ hW hex h hh v f f₁ hf₁
  have hS := IsUWeilPair.isUSplitting hW
  set u := M.co.e.symm (liftV v.1, liftV v.2) with hu
  set u' := actAB (cA σ) ((1 : UA σ X.J), h) u with hu'
  have hAt : ∀ c : AF F, evI F c = 0 → c • u' = 0 := by
    intro c hc
    have h0 : c • u = 0 := by
      have hl : ∀ y : Fin n × Fin d → mixedEmbedding.mixedSpace F, c • liftV y = 0 := by
        intro y
        funext i
        refine Prod.ext ?_ ?_
        · change c.1 * _ = 0
          rw [fst_eq_zero_of_ev hc, zero_mul]
        · change c.2 * 0 = 0
          rw [mul_zero]
      rw [hu, ← LinearEquiv.map_smul, Prod.smul_mk, hl, hl, Prod.mk_zero_zero, LinearEquiv.map_zero]
    simp only [hu', actAB]
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, h0, Matrix.mul_zero, Matrix.zero_mul]
  have hAt₁ : At (evI F) (M.co.e u').1 := by
    intro c hc
    have := congrArg Prod.fst (congrArg M.co.e (hAt c hc))
    rwa [LinearEquiv.map_smul, LinearEquiv.map_zero] at this
  have hAt₂ : At (evI F) (M.co.e u').2 := by
    intro c hc
    have := congrArg Prod.snd (congrArg M.co.e (hAt c hc))
    rwa [LinearEquiv.map_smul, LinearEquiv.map_zero] at this
  have he' : M.co.e u' = (liftV (archAct M h v).1, liftV (archAct M h v).2) := by
    change M.co.e u' = (liftV (locV (M.co.e u').1), liftV (locV (M.co.e u').2))
    rw [liftV_locV_of_at hAt₁, liftV_locV_of_at hAt₂]
  have hA₁ := acts_archOp om h f₁ (hex h hh f₁) (refFin _) (rest_refFin _ f₁)
  have hA := acts_archOp om h f (hex h hh f) (refFin _) (rest_refFin _ f)
  have himpl := hS.impl (1, h) u (tens (evI F) ⇑f (refFin _)) (rest_refFin _ f).2
  have h1 : M.co.rho ψ u (tens (evI F) ⇑f (refFin _)) = tens (evI F) ⇑f₁ (refFin _) := by
    simp only [Darboux.rho, hu, LinearEquiv.apply_symm_apply]
    rw [schr_tens ψ hψ v, hf₁]
  have h2 : M.co.rho ψ u' (tens (evI F) ⇑(archOp om h f) (refFin _)) =
      tens (evI F) (schrF (trP F (Fin n × Fin d)) (archAct M h v) ⇑(archOp om h f)) (refFin _) := by
    simp only [Darboux.rho]
    rw [he', schr_tens ψ hψ]
  rw [h1, hA₁, hA, ← hu', h2] at himpl
  funext y
  have := congrFun himpl (liftV y)
  simp only [tens, refFin_liftV, mul_one] at this
  have hy : (fun i => evI F (liftV y i)) = y := funext fun i => evI_liftV y i
  rwa [hy] at this

end GlobalTheory.ArchHeis
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ArchimedeanWeilOperatorIntertwinesSchroedingerStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.ArchUniq GlobalTheory.ArchUniq.Coord GlobalTheory.ArchLine
open scoped Matrix Classical SchwartzMap
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_weilOperator_intertwines_schroedinger : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
    IsStd ψ → M.IsWeil ψ χX χW om → (∀ h ∈ UAt σ W (evI F), ∀ f : SInf F (Fin n × Fin d), ∃ f₁ : SInf F (Fin n × Fin d),
      Acts (evI F) (om (1, h)) ⇑f ⇑f₁) →
    ∀ h ∈ UAt σ W (evI F), ∀ (v : (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F))
      (f f₁ : SInf F (Fin n × Fin d)), ⇑f₁ = schrF (trP F (Fin n × Fin d)) v ⇑f →
      ⇑(archOp om h f₁) = schrF (trP F (Fin n × Fin d)) (archAct M h v) ⇑(archOp om h f) := by
  first | exact @GlobalTheory.ArchHeis.archOp_schrF | exact GlobalTheory.ArchHeis.archOp_schrF | (intros; apply GlobalTheory.ArchHeis.archOp_schrF <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairPtsEq
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.TopZeroInv

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

abbrev Arr (D : D7) : Type := Fin D.R.m ⊕ Fin D.R.m

def arrP (t : T) : Arr D → Pair T
  | .inl j => .top t j
  | .inr i => .chi i D.R.m


variable (G) in
abbrev Vecs (t : T) : Type := ∀ a : Arr D, WO (G.pS (arrP t a)) (G.pT (arrP t a)) → ℂ

def vecsOf (S : GridChoice W U) {t : T} (d : PureDat G t) : Vecs G t
  | .inl j => S.Z.vec (d.1 j)
  | .inr i => S.Z.vec (d.2 i)

def kkVec (S : GridChoice W U) (p : Pair T) (f : WO (G.pS p) (G.pT p) → ℂ) (x : FinPt G p.small) (y : FinPt G p.big) :
    VV ℂ (wt G p.small) →ₗ[ℂ] VV ℂ (wt G p.big) :=
  S.Z.scal 1 p • fockComp W S.N.frC p f (x * S.N.u _) (y * S.N.u _)

def colV (S : GridChoice W U) {t : T} (fs : Vecs G t) (x : ∀ j, FinPt G (.top j)) :
    VV ℂ (wt G (.top 0)) →ₗ[ℂ] VV ℂ (wt G (.top D.R.m)) :=
  chainTo (V := fun j => VV ℂ (wt G (.top j)))
    (fun j => if h : j < D.R.m then kkVec S (.top t j) (fs (.inl ⟨j, h⟩)) (x j) (x (j + 1)) else 0) D.R.m ∘ₗ
    rhoVr (tauE D) _ (S.N.fr (.top 0))⁻¹

def rowV (S : GridChoice W U) {t : T} (fs : Vecs G t) (y : ∀ i, FinPt G (.grid i D.R.m)) :
    VV ℂ (listedWt G (.grid 0 D.R.m)) →ₗ[ℂ] VV ℂ (wt G (.grid D.R.m D.R.m)) :=
  chainTo (V := fun i => VV ℂ (wt G (.grid i D.R.m)))
    (fun i => if h : i < D.R.m then kkVec S (.chi i D.R.m) (fs (.inr ⟨i, h⟩)) (y i) (y (i + 1)) else 0) D.R.m ∘ₗ
    rhoVr (tauE D) _ (S.N.fr (.grid 0 D.R.m))⁻¹ ∘ₗ funOf (listedWt G (.grid 0 D.R.m))

def pairVec (S : GridChoice W U) {t : T} (x : ∀ j, FinPt G (.top j)) (y : ∀ i, FinPt G (.grid i D.R.m)) (fs : Vecs G t) :
    VV ℂ (wt G (.top 0)) →ₗ[ℂ] VV ℂ (listedWt G (.grid 0 D.R.m)) →ₗ[ℂ] ℂ :=
  (brPair (listedWt G (.grid D.R.m D.R.m)) G.sp.topDec.rank.symm (wt G (.top D.R.m))).compl₁₂ (colV S fs x) (rowV S fs y)

theorem pairPts_eq (S : GridChoice W U) {t : T} (τ : PureDat G t →₀ ℂ) (x : ∀ j, FinPt G (.top j))
    (y : ∀ i, FinPt G (.grid i D.R.m)) (v w) :
    pairPts S τ x y v w = τ.sum fun d a => a * pairVec S x y (vecsOf S d) v w := by
  unfold pairPts Finsupp.sum
  rw [LinearMap.sum_apply, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul]
  rfl

def first : Arr D := .inl ⟨0, by have := D.R.two_le_m; omega⟩

def moveFirst (W : G.Weil) {t : T} (g : FinPt G (.top 0)) (fs : Vecs G t) : Vecs G t :=
  Function.update fs first (W.om (.top t 0) (G.toPair (.top t 0) g.1 1) (fs first))

end GlobalTheory.TopZeroInv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilActionNegPairPureTensorFock
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilActionNegPairPureTensorFock
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Kronecker

noncomputable section

namespace GlobalTheory.FockRealNeg

theorem gramAt_negSp {D : D7} (S : HSp D) (τ : D.what₂.Tau) :
    gramAt D (GlobalTheory.ChiGrid.negSp S) τ = -gramAt D S τ := by
  unfold gramAt
  rw [GlobalTheory.ChiGrid.negSp_gram, Matrix.map_neg _ (map_neg _)]

theorem isCartanInv_neg_one {k : ℕ} {G : Matrix (Fin k) (Fin k) ℂ} (h : IsCartanInv G 1) :
    IsCartanInv (-G) (-1) := by
  obtain ⟨-, -, h3⟩ := h
  refine ⟨by simp, by simp, ?_⟩
  simpa using h3

theorem detPlus_neg_one_one {m n : ℕ} (a : Matrix (Fin n) (Fin n) ℂ) (b : Matrix (Fin m) (Fin m) ℂ) :
    GlobalTheory.WeilParts.detPlus (-1) 1 a b = 1 := by
  unfold GlobalTheory.WeilParts.detPlus
  have e : (1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ (-1 : Matrix (Fin n) (Fin n) ℂ)ᵀ = -1 := by
    ext ⟨i, j⟩ ⟨k, l⟩
    simp only [Matrix.kroneckerMap_apply, Matrix.transpose_apply, Matrix.neg_apply, Matrix.one_apply]
    split_ifs <;> simp_all
  have e2 : (1 / 2 : ℂ) • ((1 + -1 : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) * (b ⊗ₖ aᵀ)) +
      (1 / 2 : ℂ) • (1 - -1 : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) = 1 := by
    rw [add_neg_cancel, Matrix.zero_mul, smul_zero, zero_add, sub_neg_eq_add, ← two_smul ℂ, smul_smul]
    norm_num
  rw [e, e2, Matrix.det_one]

end GlobalTheory.FockRealNeg

namespace GlobalTheory.FockRealNeg

theorem om_pureTensorO_neg : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D (GlobalTheory.ChiGrid.negSp S) × GA D T →* Module.End ℂ (WO (GlobalTheory.ChiGrid.negSp S) T → ℂ)), IsWeilDatumO ψ (GlobalTheory.ChiGrid.negSp S) T χS χT om → IsInfFam θ → ∀ (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ), (∀ τ, (BS τ)ᴴ * gramAt D S τ * BS τ = 1) → (∀ τ, (BT τ)ᴴ * gramAt D T τ * BT τ = 1) → ∀ (a b : D.what₂.Tau → ℚ), (∀ τ, HasInfExp D χS τ (a τ)) → (∀ τ, HasInfExp D χT τ (b τ)) → ∀ (e₁ e₂ : D.what₂.Tau → ℤ), (∀ τ, (e₁ τ : ℚ) = a τ - (S.rank : ℚ) / 2) → (∀ τ, (e₂ τ : ℚ) = -(b τ - (T.rank : ℚ) / 2)) → ∀ f, IsThetaFunO ψ (GlobalTheory.ChiGrid.negSp S) T f → (∀ τ, IsFockVacAt (heisO ψ (GlobalTheory.ChiGrid.negSp S) T) θ τ (cplxO (-1) 1) f) → ∀ g ∈ GinfC (GlobalTheory.ChiGrid.negSp S), ∀ h ∈ GinfC T, ∀ P : MvPolynomial (FVar D T.rank S.rank) ℂ, om (g, h) (pureTensorO ψ θ (GlobalTheory.ChiGrid.negSp S) T (fun _ => -1) (fun _ => 1) BS BT f P) = (∏ τ, (compAt θ τ (Formalism.L2.Theta.mt (GlobalTheory.ChiGrid.negSp S) g)).det ^ e₂ τ * (compAt θ τ (Formalism.L2.Theta.mt T h)).det ^ e₁ τ) • pureTensorO ψ θ (GlobalTheory.ChiGrid.negSp S) T (fun _ => -1) (fun _ => 1) BS BT f (GlobalTheory.CompactHowe.substF (fun τ => ((BT τ)⁻¹ * compAt θ τ (Formalism.L2.Theta.mt T h) * BT τ).map (starRingEnd ℂ)) (fun τ => ((((BS τ)⁻¹ * compAt θ τ (Formalism.L2.Theta.mt (GlobalTheory.ChiGrid.negSp S) g) * BS τ)⁻¹)ᵀ).map (starRingEnd ℂ)) P) := by
  intro D ψ θ S T χS χT om hom hθ BS BT hBS hBT a b ha hb e₁ e₂ he₁ he₂ f hf hv g hg h hh P
  have hS1 : ∀ τ, IsCartanInv (gramAt D S τ) 1 := fun τ => GlobalTheory.FockCompactAction.isCartanInv_one (hBS τ)
  have hT1 : ∀ τ, IsCartanInv (gramAt D T τ) 1 := fun τ => GlobalTheory.FockCompactAction.isCartanInv_one (hBT τ)
  have hSn : ∀ τ, IsCartanInv (gramAt D (GlobalTheory.ChiGrid.negSp S) τ) (-1) := fun τ => by
    rw [gramAt_negSp]; exact isCartanInv_neg_one (hS1 τ)
  have hdet : ∀ {k : ℕ} {G s : Matrix (Fin k) (Fin k) ℂ}, IsCartanInv G s → G.det ≠ 0 := fun {k G s} hG => by
    have := hG.2.2.det_pos.ne'
    rw [Matrix.det_mul] at this
    exact left_ne_zero_of_mul this
  obtain ⟨η, hη⟩ := GlobalTheory.WeilParts.exists_isEtaTilde_unramified D
  obtain ⟨x, hx, hxv⟩ := GlobalTheory.VacuumCharacter.exists_root hθ (GlobalTheory.ChiGrid.negSp S) (fun τ => hdet (hSn τ)) g hg
  obtain ⟨y, hy, hyv⟩ := GlobalTheory.VacuumCharacter.exists_root hθ T (fun τ => hdet (hT1 τ)) h hh
  have c1 : ∀ τ, (fun _ => (-1 : Matrix (Fin S.rank) (Fin S.rank) ℂ)) τ *
      compAt θ τ (Formalism.L2.Theta.mt (GlobalTheory.ChiGrid.negSp S) g) =
      compAt θ τ (Formalism.L2.Theta.mt (GlobalTheory.ChiGrid.negSp S) g) * (fun _ => (-1 : Matrix (Fin S.rank) (Fin S.rank) ℂ)) τ :=
    fun τ => by simp
  have c2 : ∀ τ, (fun _ => (1 : Matrix (Fin T.rank) (Fin T.rank) ℂ)) τ * compAt θ τ (Formalism.L2.Theta.mt T h) =
      compAt θ τ (Formalism.L2.Theta.mt T h) * (fun _ => (1 : Matrix (Fin T.rank) (Fin T.rank) ℂ)) τ :=
    fun τ => by simp
  have hvac := GlobalTheory.WeilVacChar.vacuum_character D ψ hom.std (GlobalTheory.ChiGrid.negSp S) T θ hθ χS χT om η hη hom
    (fun _ => -1) (fun _ => 1) hSn hT1 g hg h hh c1 c2 x y hx hy f hf hv
  have b1 : ∀ τ, BS τ * (BS τ)⁻¹ = 1 := fun τ => by
    have hB : BS τ * ((BS τ)ᴴ * gramAt D S τ) = 1 := mul_eq_one_comm.1 (hBS τ)
    rw [Matrix.inv_eq_right_inv hB, hB]
  have b2 : ∀ τ, BT τ * (BT τ)⁻¹ = 1 := fun τ => by
    have hB : BT τ * ((BT τ)ᴴ * gramAt D T τ) = 1 := mul_eq_one_comm.1 (hBT τ)
    rw [Matrix.inv_eq_right_inv hB, hB]
  have hneg := GlobalTheory.T.fockVector_negSpace_frameChange_conjSubst D ψ θ S T hom.std hθ BS
    (fun τ => (BS τ)⁻¹ * compAt θ τ (Formalism.L2.Theta.mt (GlobalTheory.ChiGrid.negSp S) g) * BS τ) BT
    (fun τ => (BT τ)⁻¹ * compAt θ τ (Formalism.L2.Theta.mt T h) * BT τ) f hf P
  rw [(GlobalTheory.OrientedHeis.om_pureTensorO D ψ θ (GlobalTheory.ChiGrid.negSp S) T χS χT om hom hθ (fun _ => -1) (fun _ => -1) BS
      (fun τ => BS τ * ((BS τ)⁻¹ * compAt θ τ (Formalism.L2.Theta.mt (GlobalTheory.ChiGrid.negSp S) g) * BS τ))
      (fun _ => 1) (fun _ => 1) BT (fun τ => BT τ * ((BT τ)⁻¹ * compAt θ τ (Formalism.L2.Theta.mt T h) * BT τ)) g h c1 c2
      (fun τ => by rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, b1, Matrix.one_mul])
      (fun τ => by rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, b2, Matrix.one_mul]) f hf P).2,
    hvac, GlobalTheory.FockCompactAction.pureTensorO_smul, hneg]
  congr 1
  simp only [detPlus_neg_one_one, Finset.prod_const_one, mul_one]
  have hx' : ∀ τ, HasInfExp D (χT * (η ^ T.rank)⁻¹) τ ((-e₂ τ : ℤ) : ℚ) := fun τ => by
    have e : ((-e₂ τ : ℤ) : ℚ) = b τ - (T.rank : ℚ) / 2 := by push_cast; rw [he₂]; ring
    rw [e]; exact GlobalTheory.VacuumCharacter.hasInfExp_twist (hb τ) (hη.2.2.2 τ) _
  have hy' : ∀ τ, HasInfExp D (χS * (η ^ (GlobalTheory.ChiGrid.negSp S).rank)⁻¹) τ ((e₁ τ : ℤ) : ℚ) := fun τ => by
    rw [he₁]; exact GlobalTheory.VacuumCharacter.hasInfExp_twist (ha τ) (hη.2.2.2 τ) _
  rw [Circle.coe_mul, Circle.coe_inv, hxv _ (fun τ => -e₂ τ) hx', hyv _ e₁ hy', ← Finset.prod_inv_distrib,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [_root_.zpow_neg, inv_inv]

end GlobalTheory.FockRealNeg
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilActionNegPairPureTensorFockStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilAction_negPair_pureTensor_fock : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D (GlobalTheory.ChiGrid.negSp S) × GA D T →* Module.End ℂ (WO (GlobalTheory.ChiGrid.negSp S) T → ℂ)), IsWeilDatumO ψ (GlobalTheory.ChiGrid.negSp S) T χS χT om → IsInfFam θ → ∀ (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ), (∀ τ, (BS τ)ᴴ * gramAt D S τ * BS τ = 1) → (∀ τ, (BT τ)ᴴ * gramAt D T τ * BT τ = 1) → ∀ (a b : D.what₂.Tau → ℚ), (∀ τ, HasInfExp D χS τ (a τ)) → (∀ τ, HasInfExp D χT τ (b τ)) → ∀ (e₁ e₂ : D.what₂.Tau → ℤ), (∀ τ, (e₁ τ : ℚ) = a τ - (S.rank : ℚ) / 2) → (∀ τ, (e₂ τ : ℚ) = -(b τ - (T.rank : ℚ) / 2)) → ∀ f, IsThetaFunO ψ (GlobalTheory.ChiGrid.negSp S) T f → (∀ τ, IsFockVacAt (heisO ψ (GlobalTheory.ChiGrid.negSp S) T) θ τ (cplxO (-1) 1) f) → ∀ g ∈ GinfC (GlobalTheory.ChiGrid.negSp S), ∀ h ∈ GinfC T, ∀ P : MvPolynomial (FVar D T.rank S.rank) ℂ, om (g, h) (pureTensorO ψ θ (GlobalTheory.ChiGrid.negSp S) T (fun _ => -1) (fun _ => 1) BS BT f P) = (∏ τ, (compAt θ τ (Formalism.L2.Theta.mt (GlobalTheory.ChiGrid.negSp S) g)).det ^ e₂ τ * (compAt θ τ (Formalism.L2.Theta.mt T h)).det ^ e₁ τ) • pureTensorO ψ θ (GlobalTheory.ChiGrid.negSp S) T (fun _ => -1) (fun _ => 1) BS BT f (GlobalTheory.CompactHowe.substF (fun τ => ((BT τ)⁻¹ * compAt θ τ (Formalism.L2.Theta.mt T h) * BT τ).map (starRingEnd ℂ)) (fun τ => ((((BS τ)⁻¹ * compAt θ τ (Formalism.L2.Theta.mt (GlobalTheory.ChiGrid.negSp S) g) * BS τ)⁻¹)ᵀ).map (starRingEnd ℂ)) P) := by
  first | exact @GlobalTheory.FockRealNeg.om_pureTensorO_neg | exact GlobalTheory.FockRealNeg.om_pureTensorO_neg | (intros; apply GlobalTheory.FockRealNeg.om_pureTensorO_neg <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.OneParameterOperatorUnique
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.OneParameterOperatorUnique
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Classical

noncomputable section

namespace GlobalTheory.ArchimedeanUnitaryL2

open scoped ENNReal
open GlobalTheory.WeilAdm.HaarSplit

private theorem opensMeasurableSpace_pi_mixedSpace (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] :
    OpensMeasurableSpace (κ → mixedEmbedding.mixedSpace F) := by
  haveI : SecondCountableTopology (mixedEmbedding.mixedSpace F) := inferInstance
  haveI : BorelSpace (mixedEmbedding.mixedSpace F) := inferInstance
  infer_instance

theorem exists_haar (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (μ : Measure (κ → mixedEmbedding.mixedSpace F)) [μ.IsAddHaarMeasure]
    (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) (hg : g ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F)) (hg0 : g 0 ≠ 0) :
    ∃ μA : @Measure (κ → AdeleRing (𝓞 F) F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μA ∧
      ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ ∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ,
        ∫⁻ x, ‖GlobalTheory.WeilM.pureA F f g x‖ₑ ^ 2 ∂μA = c * ∫⁻ z, ‖f z‖ₑ ^ 2 ∂μ := by
  classical
  haveI := opensMeasurableSpace_pi_mixedSpace F κ
  letI : LocallyCompactSpace (FiniteAdeleRing (𝓞 F) F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele F
  haveI : SecondCountableTopology (FiniteAdeleRing (𝓞 F) F) := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele F
  haveI : T2Space (FiniteAdeleRing (𝓞 F) F) := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField F
  letI : MeasurableSpace (FiniteAdeleRing (𝓞 F) F) := borel _
  haveI : BorelSpace (FiniteAdeleRing (𝓞 F) F) := ⟨rfl⟩
  letI mA : MeasurableSpace (κ → AdeleRing (𝓞 F) F) := borel _
  haveI : BorelSpace (κ → AdeleRing (𝓞 F) F) := ⟨rfl⟩
  obtain ⟨ν, hν⟩ : ∃ ν : Measure (κ → FiniteAdeleRing (𝓞 F) F), ν = Measure.addHaar := ⟨_, rfl⟩
  haveI : ν.IsAddHaarMeasure := by rw [hν]; infer_instance
  haveI : SFinite ν := by rw [hν]; infer_instance
  haveI : SFinite μ := inferInstance
  haveI : MeasurableAdd (κ → FiniteAdeleRing (𝓞 F) F) := inferInstance
  haveI : MeasurableAdd (κ → mixedEmbedding.mixedSpace F) := inferInstance
  let h : ((κ → mixedEmbedding.mixedSpace F) × (κ → FiniteAdeleRing (𝓞 F) F)) ≃ₜ (κ → AdeleRing (𝓞 F) F) :=
    { toEquiv := (splitE F κ).toEquiv
      continuous_toFun := continuous_splitE F κ
      continuous_invFun := continuous_splitE_symm F κ }
  let m := h.toMeasurableEquiv
  have hm : (m : _ → _) = splitE F κ := rfl
  have hgc : Continuous g := hg.1.continuous
  refine ⟨(μ.prod ν).map m, ?_, ∫⁻ y, ‖g y‖ₑ ^ 2 ∂ν, ?_, ?_, ?_⟩
  · rw [hm]
    exact AddEquiv.isAddHaarMeasure_map (μ.prod ν) (splitE F κ) (continuous_splitE F κ) (continuous_splitE_symm F κ)
  · apply ne_of_gt
    have hU : IsOpen {y | g y = g 0} := hg.1.isOpen_fiber _
    have hpos : 0 < ν {y | g y = g 0} := hU.measure_pos ν ⟨0, rfl⟩
    calc (0 : ℝ≥0∞) < ‖g 0‖ₑ ^ 2 * ν {y | g y = g 0} :=
          ENNReal.mul_pos (pow_ne_zero _ (enorm_ne_zero.2 hg0)) hpos.ne'
      _ = ∫⁻ y, {y | g y = g 0}.indicator (fun _ => ‖g 0‖ₑ ^ 2) y ∂ν :=
          (lintegral_indicator_const hU.measurableSet _).symm
      _ ≤ ∫⁻ y, ‖g y‖ₑ ^ 2 ∂ν := by
          refine lintegral_mono fun y => ?_
          by_cases hy : g y = g 0
          · simp [Set.indicator, hy]
          · simp [Set.indicator, hy]
  · have hs : HasCompactSupport fun y => ‖g y‖ ^ 2 := hg.2.comp_left (g := fun z : ℂ => ‖z‖ ^ 2) (by simp)
    have hint : Integrable (fun y => ‖g y‖ ^ 2) ν := (hgc.norm.pow 2).integrable_of_hasCompactSupport hs
    have h2 := hint.2
    unfold HasFiniteIntegral at h2
    refine ne_of_lt (lt_of_le_of_lt (le_of_eq ?_) h2)
    refine lintegral_congr fun y => ?_
    rw [enorm_pow, enorm_norm]
  · intro f
    rw [lintegral_map_equiv, hm]
    have hpt : ∀ p : (κ → mixedEmbedding.mixedSpace F) × (κ → FiniteAdeleRing (𝓞 F) F),
        ‖GlobalTheory.WeilM.pureA F f g (splitE F κ p)‖ₑ ^ 2 = ‖f p.1‖ₑ ^ 2 * ‖g p.2‖ₑ ^ 2 := by
      intro p
      rw [pureA_splitE, enorm_mul, mul_pow]
    simp_rw [hpt]
    rw [mul_comm]
    exact lintegral_prod_mul (μ := μ) (ν := ν) (f := fun z => ‖f z‖ₑ ^ 2) (g := fun y => ‖g y‖ₑ ^ 2)
      (f.continuous.measurable.enorm.pow_const 2).aemeasurable (hgc.measurable.enorm.pow_const 2).aemeasurable

theorem integral_sq_eq {V : Type} [TopologicalSpace V] [MeasurableSpace V] [OpensMeasurableSpace V] (μ : Measure V)
    {f : V → ℂ} (hf : Continuous f) : ∫ x, ‖f x‖ ^ 2 ∂μ = (∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ).toReal := by
  have hc : Continuous fun x => ‖f x‖ ^ 2 := hf.norm.pow 2
  rw [integral_eq_lintegral_of_nonneg_ae (f := fun x => ‖f x‖ ^ 2)
    (Filter.Eventually.of_forall fun x => by positivity) hc.aestronglyMeasurable]
  congr 1
  refine lintegral_congr fun x => ?_
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]

theorem opensMeasurable (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] :
    OpensMeasurableSpace (κ → mixedEmbedding.mixedSpace F) := opensMeasurableSpace_pi_mixedSpace F κ

theorem snd_eq_zero {F : Type} [Field F] [NumberField F] {κ : Type} {z : κ → AF F} (hz : At (evI F) z) (i : κ) :
    (z i).2 = 0 := by
  have h := hz (((0 : InfiniteAdeleRing F), (1 : FiniteAdeleRing (𝓞 F) F)) : AdeleRing (𝓞 F) F) (by
    show InfiniteAdeleRing.ringEquiv_mixedSpace F 0 = 0
    exact map_zero _)
  have h2 : (((0 : InfiniteAdeleRing F), (1 : FiniteAdeleRing (𝓞 F) F)) * ((z i).1, (z i).2)).2 =
      (0 : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F).2 := congrArg Prod.snd (congrFun h i)
  simpa using h2

theorem integral_norm_sq_eq : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {a a' : ℕ} (B : Base F E) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om' → ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ G.W,
    ∀ T : ℝ → SInf F (Fin a × Fin (a + a')) →ₗ[ℂ] SInf F (Fin a × Fin (a + a')),
    (∀ (t : ℝ) (f : SInf F (Fin a × Fin (a + a'))), Acts (evI F) (om (1, γ (Multiplicative.ofAdd t))) f (T t f)) →
    ∀ (μ : Measure (Fin a × Fin (a + a') → mixedEmbedding.mixedSpace F)), μ.IsAddHaarMeasure →
    ∀ (t : ℝ) (f : SInf F (Fin a × Fin (a + a'))), ∫ x, ‖T t f x‖ ^ 2 ∂μ = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  intro F E _ _ _ _ _ σ a a' B G X om om' hT γ _ T hAct μ hμ t f
  classical
  haveI := hμ
  haveI := opensMeasurable F (Fin a × Fin (a + a'))
  set g : (Fin a × Fin (a + a') → FiniteAdeleRing (𝓞 F) F) → ℂ :=
    (GlobalTheory.SchANonzero.intPts F (Fin a × Fin (a + a'))).indicator 1 with hgdef
  have hgSB : g ∈ GlobalTheory.WeilM.SB _ := GlobalTheory.SchANonzero.indicator_intPts_mem_SB F _
  have h0mem : (0 : Fin a × Fin (a + a') → FiniteAdeleRing (𝓞 F) F) ∈ GlobalTheory.SchANonzero.intPts F _ := by
    intro i _ v
    exact zero_mem (v.adicCompletionIntegers F)
  have hg0 : g 0 ≠ 0 := by
    rw [hgdef, Set.indicator_of_mem h0mem]
    simp
  obtain ⟨μA, hμA, c, hc0, hctop, hc⟩ := exists_haar F (Fin a × Fin (a + a')) μ g hgSB hg0
  have hU := (GlobalTheory.WeilM.IsUWeilPair.isUSplitting hT.weil).unit
  let r : (Fin a × Fin (a + a') → AF F) → ℂ := fun x => g (fun i => (x i).2)
  have htens : ∀ φ : SInf F (Fin a × Fin (a + a')), tens (evI F) (φ : _ → ℂ) r = GlobalTheory.WeilM.pureA F φ g :=
    fun φ => rfl
  have hRest : Rest (evI F) (f : _ → ℂ) r := by
    refine ⟨fun x z hz => ?_, ?_⟩
    · show g _ = g _
      congr 1
      funext i
      show (x i).2 + (z i).2 = (x i).2
      rw [snd_eq_zero hz i, add_zero]
    · rw [htens]
      exact Submodule.subset_span ⟨f, g, hgSB, rfl⟩
  have hA := hAct t f r hRest
  rw [htens, htens] at hA
  have hmem : GlobalTheory.WeilM.pureA F f g ∈ GlobalTheory.WeilM.schA F (Fin a × Fin (a + a')) :=
    Submodule.subset_span ⟨f, g, hgSB, rfl⟩
  have hu := hU μA hμA (1, γ (Multiplicative.ofAdd t)) _ hmem
  rw [hA, hc, hc] at hu
  have hl := (ENNReal.mul_right_inj hc0 hctop).1 hu
  rw [integral_sq_eq μ (T t f).continuous, integral_sq_eq μ f.continuous, hl]

end GlobalTheory.ArchimedeanUnitaryL2

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.OneParameterOperatorUniqueStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.one_parameter_operator_unique : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {a a' : ℕ} (B : Base F E) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om' → ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ G.W,
    ∀ T : ℝ → SInf F (Fin a × Fin (a + a')) →ₗ[ℂ] SInf F (Fin a × Fin (a + a')),
    (∀ (t : ℝ) (f : SInf F (Fin a × Fin (a + a'))), Acts (evI F) (om (1, γ (Multiplicative.ofAdd t))) f (T t f)) →
    ∀ (μ : Measure (Fin a × Fin (a + a') → mixedEmbedding.mixedSpace F)), μ.IsAddHaarMeasure →
    ∀ (t : ℝ) (f : SInf F (Fin a × Fin (a + a'))), ∫ x, ‖T t f x‖ ^ 2 ∂μ = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  first | exact @GlobalTheory.ArchimedeanUnitaryL2.integral_norm_sq_eq | exact GlobalTheory.ArchimedeanUnitaryL2.integral_norm_sq_eq | (intros; apply GlobalTheory.ArchimedeanUnitaryL2.integral_norm_sq_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExFieldOfKeyFinExKey
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx

noncomputable section

namespace GlobalTheory.RowEx

theorem exField_of_keyFin_exKey : KeyFin → ExKey → ExField := by
  classical
  intro h2 h1
  obtain ⟨c, h1⟩ := h1
  refine ⟨c, fun ε CF hC => ?_⟩
  obtain ⟨x, h1⟩ := h1 ε CF hC
  refine ⟨x, fun s e hx P f Ξ hΞ => ?_⟩
  obtain ⟨𝒦, hK, H⟩ := h2 P Ξ hΞ
  choose S hS HS using h1 s e hx P f
  refine ⟨hK.toFinset.biUnion S, fun z hz => ?_, fun Y f' hP hf large₂ hs Γ _ _ Pl0 U A Ks _ _ _ R F st hC ho hc hz => ?_⟩
  · obtain ⟨κ, -, hz⟩ := Finset.mem_biUnion.1 hz
    exact hS κ z hz
  · obtain ⟨κ, hκ, hk⟩ := H Y U R.toLevCh A.μ0 hP st.core.lev hc
    exact HS κ Y f' hP hf large₂ hs Γ Pl0 U A Ks R F st hC ho hk fun z hz' =>
      hz z (Finset.mem_biUnion.2 ⟨κ, hK.mem_toFinset.2 hκ, hz'⟩)

end GlobalTheory.RowEx

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.KeyFinHolds
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowEx

theorem keyFin_holds : KeyFin := by
  classical
  intro P Ξ hΞ
  let U : Key P := {p | p.1 ∈ Ξ ∧ {w | ¬ p.1.UnrAt w}.Finite ∧ ∀ w ∈ p.2, ¬ p.1.UnrAt w}
  have hU : U.Finite := by
    refine (hΞ.biUnion (t := fun ξ => {p ∈ U | p.1 = ξ}) fun ξ _ => ?_).subset fun p hp => Set.mem_biUnion hp.1 ⟨hp, rfl⟩
    by_cases hf : {w | ¬ ξ.UnrAt w}.Finite
    · refine ((hf.toFinset.powerset.finite_toSet).image fun Q => (ξ, Q)).subset ?_
      rintro ⟨a, Q⟩ ⟨h, rfl⟩
      exact ⟨Q, Finset.mem_coe.2 (Finset.mem_powerset.2 fun w hw => hf.mem_toFinset.2 (h.2.2 w hw)), rfl⟩
    · refine Set.finite_empty.subset ?_
      rintro ⟨a, Q⟩ ⟨h, rfl⟩
      exact hf h.2.1
  refine ⟨{κ | κ ⊆ U}, hU.finite_subsets, ?_⟩
  rintro X T L μ₀ rfl hL h
  refine ⟨keyOf L, ?_, HEq.rfl⟩
  rintro _ ⟨t, rfl⟩
  obtain ⟨ξ, h1, h2⟩ := h t
  refine ⟨by rw [← eq_of_heq h2] at h1; exact h1, ?_, fun w hw => (hL.Q_ram t w).2 (Or.inl hw)⟩
  refine ((L.Q t).finite_toSet.union ((L.Q t).finite_toSet.image Formalism.DivisionValues.conjPl)).subset fun w hw => ?_
  rcases (hL.Q_ram t w).1 hw with h | ⟨w', h, h'⟩
  · exact Or.inl h
  · exact Or.inr ⟨w', h, (GlobalTheory.GoodPrimes.isConjPl_iff.1 h').symm⟩

end GlobalTheory.RowEx
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HalfLat
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open GlobalTheory.SplitHecke GlobalTheory.LFun.ConjPlace GlobalTheory.AdelicU

namespace GlobalTheory.SplitIdx

variable {D : D7}

def intMat (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (m n : ℕ) :
    AddSubgroup (Matrix (Fin m) (Fin n) (v.adicCompletion F)) where
  carrier := {y | ∀ i j, y i j ∈ v.adicCompletionIntegers F}
  add_mem' hx hy i j := add_mem (hx i j) (hy i j)
  zero_mem' _ _ := zero_mem _
  neg_mem' hx i j := neg_mem (hx i j)

def mulL {K : Type} [CommRing K] {m n : ℕ} (P : Matrix (Fin m) (Fin m) K) :
    Matrix (Fin m) (Fin n) K →+ Matrix (Fin m) (Fin n) K :=
  AddMonoidHom.mk' (fun y => P * y) (Matrix.mul_add P)

def halfLat (S T : HSp D) (e : AE D) : AddSubgroup (WO S T) :=
  (latO S T (frameLat S) (frameLat T) fun _ => True) ⊓ GlobalTheory.PlaceModel.half S T e

def actL (S T : HSp D) (h : GA D T) : WO S T →+ WO S T :=
  AddMonoidHom.mk' (actO S T 1 h) fun x y => by simp only [actO, Matrix.mul_add, Matrix.add_mul]

end GlobalTheory.SplitIdx

end
end
