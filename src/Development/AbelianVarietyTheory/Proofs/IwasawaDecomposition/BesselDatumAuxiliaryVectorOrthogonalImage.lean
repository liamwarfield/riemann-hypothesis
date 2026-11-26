module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankOrth
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemNormGroupIffEverywhereNorm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RestrictedProductMeasureBasicProperties
public import Formalism.LocalToGlobal.Columns.TiedVal
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntOv
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsUnitaryOfCharIff

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BesselDatumAuxiliaryVectorOrthogonalImage
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.BesselData
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RootExch

open GlobalTheory.BesselCompare (mt_mul mt_one hA_add hA_smul hA_smul_right hA_vec cA_inc)

variable {D : D7} {A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V}

def exF (d : BesselDatum A B ι) (ε : AE D) (i : Fin (d.ρ + 1)) (m : Measure (d.Ex ε i)) (β : GA D B → ℂ) :
    GA D B → ℂ := fun g => ∫ u, β ((u : GA D B) * g) ∂m

def toPosF (d : BesselDatum A B ι) (ε : AE D) (m : ∀ i, Measure (d.Ex ε i)) (p : ℕ) (β : GA D B → ℂ) : GA D B → ℂ :=
  ((List.finRange (d.ρ + 1)).filter fun i => decide (p ≤ i.1)).foldr (fun i β' => exF d ε i (m i) β') β

def moveF (P : PosDatum A B ι) (β : GA D B → ℂ) : GA D B → ℂ :=
  (List.finRange P.n).foldr (fun a β' => toPosF P.bes (P.ε a) (P.m a) (P.p a) β') β

def Lvl (β : GA D B → ℂ) : Prop :=
  ∃ U : Subgroup (GA D B), IsOpen (U : Set (GA D B)) ∧ ∀ k ∈ U, k ∈ GfC B → ∀ g, β (g * k) = β g

def Eqv (d : BesselDatum A B ι) (ψ : AddChar (AF D.host.F) ℂ) (ε : AE D) (β : GA D B → ℂ) : Prop :=
  ∀ n ∈ d.N, SuppAt ε B n → ∀ g, β (n * g) = d.psiN ψ n * β g

def IsK (B : HSp D) (v y : Fin B.rank → AE D) (k : GA D B) : Prop :=
  ∀ x, (mt B k).mulVec x = x + hA B x y • v - hA B x v • y

def iA (ι : A.V →ₗ[D.host.E] B.V) (t : Fin A.rank → AE D) : Fin B.rank → AE D :=
  ((frameMat B A ι).map (incA D)).mulVec t

def dual (d : BesselDatum A B ι) : Fin (d.ρ + 1) → B.V :=
  Fin.snoc (α := fun _ => B.V) d.f ((B.hD d.z d.z)⁻¹ • d.z)

def ExGe (d : BesselDatum A B ι) (ε : AE D) (p : ℕ) : Subgroup (GA D B) :=
  Subgroup.closure (⋃ l : Fin (d.ρ + 1), ⋃ _ : p ≤ l.1, d.ExSet ε l)

theorem rTr_rTr (u g : GA D B) (F : GA D B → ℂ) : rTr B u (rTr B g F) = rTr B (u * g) F := by
  funext x; simp only [rTr, mul_assoc]

theorem rTr_one (F : GA D B → ℂ) : rTr B 1 F = F := by funext x; simp only [rTr, mul_one]

theorem toPos_rTr (d : BesselDatum A B ι) (ε : AE D) (m : ∀ i, Measure (d.Ex ε i)) (p : ℕ)
    (b : (GA D B → ℂ) → ℂ) (F : GA D B → ℂ) :
    (fun g => d.toPos ε m p b (rTr B g F)) = toPosF d ε m p fun g => b (rTr B g F) := by
  unfold BesselDatum.toPos toPosF
  induction (List.finRange (d.ρ + 1)).filter fun i => decide (p ≤ i.1) with
  | nil => rfl
  | cons i l ih =>
    funext g
    simp only [List.foldr_cons, BesselDatum.exch, exF, ← ih, rTr_rTr]

theorem move_rTr (P : PosDatum A B ι) (b : (GA D B → ℂ) → ℂ) (F : GA D B → ℂ) :
    (fun g => P.move b (rTr B g F)) = moveF P fun g => b (rTr B g F) := by
  unfold PosDatum.move moveF
  induction List.finRange P.n with
  | nil => rfl
  | cons i l ih => simp only [List.foldr_cons, ← ih, toPos_rTr]

theorem cA_cA (a : AE D) : cA D (cA D a) = a := GlobalTheory.DualPairCheck.cA_cA a

theorem mt_inj {g h : GA D B} (e : mt B g = mt B h) : g = h := Subtype.ext (Units.ext e)

theorem mt_ext {g h : GA D B} (e : ∀ x, (mt B g).mulVec x = (mt B h).mulVec x) : g = h :=
  mt_inj (Matrix.mulVec_injective (funext e))

theorem mulVec_mul (g h : GA D B) (x) : (mt B (g * h)).mulVec x = (mt B g).mulVec ((mt B h).mulVec x) := by
  rw [mt_mul, Matrix.mulVec_mulVec]

theorem mulVec_inv_cancel (g : GA D B) (x) : (mt B g⁻¹).mulVec ((mt B g).mulVec x) = x := by
  rw [← mulVec_mul, inv_mul_cancel, mt_one, Matrix.one_mulVec]

theorem mulVec_cancel_inv (g : GA D B) (x) : (mt B g).mulVec ((mt B g⁻¹).mulVec x) = x := by
  rw [← mulVec_mul, mul_inv_cancel, mt_one, Matrix.one_mulVec]

theorem hA_eq (x y : Fin B.rank → AE D) : hA B x y = (fun i => cA D (y i)) ⬝ᵥ (B.gram.map (incA D)).mulVec x := by
  simp only [hA, dotProduct, Matrix.mulVec, Matrix.map_apply, Finset.mul_sum, mul_assoc]

theorem hA_herm (x y : Fin B.rank → AE D) : cA D (hA B x y) = hA B y x := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hA, map_sum, RingHom.map_mul, cA_inc, cA_cA, GlobalTheory.LatVac.gram_star]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

theorem hA_add_right (x y y' : Fin B.rank → AE D) : hA B x (y + y') = hA B x y + hA B x y' := by
  simp only [hA, Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib]

theorem hA_neg (x y : Fin B.rank → AE D) : hA B (-x) y = -hA B x y := by
  simp only [hA, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]

theorem hA_neg_right (x y : Fin B.rank → AE D) : hA B x (-y) = -hA B x y := by
  simp only [hA, Pi.neg_apply, map_neg, neg_mul, Finset.sum_neg_distrib]

theorem hA_sub (x x' y : Fin B.rank → AE D) : hA B (x - x') y = hA B x y - hA B x' y := by
  rw [sub_eq_add_neg, hA_add, hA_neg, ← sub_eq_add_neg]

theorem hA_sub_right (x y y' : Fin B.rank → AE D) : hA B x (y - y') = hA B x y - hA B x y' := by
  rw [sub_eq_add_neg, hA_add_right, hA_neg_right, ← sub_eq_add_neg]

theorem hA_zero (y : Fin B.rank → AE D) : hA B 0 y = 0 := by simp [hA]

theorem hA_zero_right (x : Fin B.rank → AE D) : hA B x 0 = 0 := by simp [hA]

theorem hA_mt (g : GA D B) (x y : Fin B.rank → AE D) :
    hA B ((mt B g).mulVec x) ((mt B g).mulVec y) = hA B x y := by
  have hg : ((mt B g).map (cA D))ᵀ * B.gram.map (incA D) * mt B g = B.gram.map (incA D) := g.2
  have e : (fun i => cA D ((mt B g).mulVec y i)) = ((mt B g).map (cA D)).mulVec fun i => cA D (y i) :=
    funext fun i => RingHom.map_mulVec (cA D) _ y i
  rw [hA_eq, hA_eq, e, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, hg]

theorem hA_mt_left (g : GA D B) (x y : Fin B.rank → AE D) :
    hA B ((mt B g).mulVec x) y = hA B x ((mt B g⁻¹).mulVec y) := by
  rw [← hA_mt g x, mulVec_cancel_inv]

theorem hA_nondeg {x : Fin B.rank → AE D} (h : ∀ y, hA B x y = 0) : x = 0 := by
  have hu : IsUnit (B.gram.map (incA D)) := (GlobalTheory.BesselCompare.gram_isUnit B).map (incA D).mapMatrix
  refine Matrix.mulVec_injective_of_isUnit hu ?_
  rw [Matrix.mulVec_zero]
  funext i
  have := h (Pi.single i 1)
  rw [hA_eq, show (fun j => cA D ((Pi.single i 1 : Fin B.rank → AE D) j)) = Pi.single i 1 from
    funext fun j => by by_cases e : j = i <;> simp [e], single_one_dotProduct] at this
  exact this

theorem suppAt_iff {ε : AE D} {g : GA D B} : SuppAt ε B g ↔ (ε + cA D ε) • (mt B g - 1) = mt B g - 1 :=
  ⟨fun h => Matrix.ext h, fun h i j => congrFun (congrFun h i) j⟩

theorem suppAt_iff_vec {ε : AE D} {g : GA D B} :
    SuppAt ε B g ↔ ∀ x, (ε + cA D ε) • ((mt B g).mulVec x - x) = (mt B g).mulVec x - x := by
  rw [suppAt_iff]
  refine ⟨fun h x => ?_, fun h => Matrix.mulVec_injective (funext fun x => ?_)⟩
  · simpa only [Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec] using congrArg (· *ᵥ x) h
  · simpa only [Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec] using h x

theorem suppAt_one (ε : AE D) : SuppAt ε B 1 := by
  rw [suppAt_iff, mt_one, sub_self, smul_zero]

theorem suppAt_mul {ε : AE D} {g h : GA D B} (hg : SuppAt ε B g) (hh : SuppAt ε B h) : SuppAt ε B (g * h) := by
  have e : mt B (g * h) - 1 = (mt B g - 1) * mt B h + (mt B h - 1) := by
    rw [mt_mul, Matrix.sub_mul, Matrix.one_mul, sub_add_sub_cancel]
  rw [suppAt_iff, e, smul_add, ← Matrix.smul_mul, suppAt_iff.1 hg, suppAt_iff.1 hh]

theorem suppAt_inv {ε : AE D} {g : GA D B} (hg : SuppAt ε B g) : SuppAt ε B g⁻¹ := by
  have h := suppAt_iff.1 hg
  have h1 : mt B g⁻¹ - 1 = (mt B g - 1) * (-mt B g⁻¹) := by
    rw [Matrix.mul_neg, Matrix.sub_mul, ← mt_mul, mul_inv_cancel, mt_one, Matrix.one_mul, neg_sub]
  rw [suppAt_iff, h1, ← Matrix.smul_mul, h]

def suppGrp (ε : AE D) (B : HSp D) : Subgroup (GA D B) where
  carrier := {g | SuppAt ε B g}
  one_mem' := suppAt_one ε
  mul_mem' := suppAt_mul
  inv_mem' := suppAt_inv

theorem suppAt_of_mem_Ex {d : BesselDatum A B ι} {ε : AE D} {i} {g : GA D B} (hg : g ∈ d.Ex ε i) : SuppAt ε B g :=
  (Subgroup.closure_le (suppGrp ε B)).2 (fun _ (h : _ ∈ d.ExSet ε i) => h.1) hg

theorem suppAt_of_mem_ExGe {d : BesselDatum A B ι} {ε : AE D} {p} {g : GA D B} (hg : g ∈ ExGe d ε p) :
    SuppAt ε B g :=
  (Subgroup.closure_le (suppGrp ε B)).2
    (Set.iUnion_subset fun i => Set.iUnion_subset fun _ _ (h : _ ∈ d.ExSet ε i) => h.1) hg

theorem Ex_le_ExGe (d : BesselDatum A B ι) (ε : AE D) {p : ℕ} {i : Fin (d.ρ + 1)} (h : p ≤ i.1) :
    d.Ex ε i ≤ ExGe d ε p :=
  Subgroup.closure_mono fun _ hg => Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨h, hg⟩⟩

theorem mem_GfC {e : AE D} (he : IsSplitIdem D e) {g : GA D B} (hg : SuppAt e B g) : g ∈ GfC B := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  have h : infPart D ((mt B g - 1) i j) = 0 := by
    rw [← hg i j, RingHom.map_mul, RingHom.map_add (f := _), GlobalTheory.SplitScalar.infPart_splitIdem he,
      GlobalTheory.SplitScalar.infPart_splitIdem (GlobalTheory.SplitScalar.isSplitIdem_conj he), add_zero, zero_mul]
  rw [Matrix.sub_apply, RingHom.map_sub, sub_eq_zero] at h
  show infPart D (mt B g i j) = (1 : Matrix _ _ _) i j
  rw [h, Matrix.one_apply, Matrix.one_apply]
  split_ifs
  · rw [RingHom.map_one]
  · rw [RingHom.map_zero]

theorem commute_of_apart {ε ε' : AE D} (h : (ε + cA D ε) * (ε' + cA D ε') = 0) {g g' : GA D B}
    (hg : SuppAt ε B g) (hg' : SuppAt ε' B g') : g * g' = g' * g := by
  have h1 : (mt B g - 1) * (mt B g' - 1) = 0 := by
    rw [← suppAt_iff.1 hg, ← suppAt_iff.1 hg', Matrix.smul_mul, Matrix.mul_smul, smul_smul, h, zero_smul]
  have h2 : (mt B g' - 1) * (mt B g - 1) = 0 := by
    rw [← suppAt_iff.1 hg, ← suppAt_iff.1 hg', Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_comm, h, zero_smul]
  refine mt_inj ?_
  rw [mt_mul, mt_mul]
  have : mt B g * mt B g' - mt B g' * mt B g = (mt B g - 1) * (mt B g' - 1) - (mt B g' - 1) * (mt B g - 1) := by
    noncomm_ring
  rw [h1, h2, sub_zero, sub_eq_zero] at this
  exact this

theorem hA_iA (hι : HSpace.IsIsomEmb A B ι) (s t : Fin A.rank → AE D) : hA B (iA ι s) (iA ι t) = hA A s t := by
  have e : ∀ s, iA ι s = ∑ l, s l • vecA B (ι (A.frame l)) := fun s => by
    rw [iA, GlobalTheory.BesselCompare.frameMat_eq, GlobalTheory.BesselCompare.eMat_mulVec]
  have e2 : ∀ l, hA B (vecA B (ι (A.frame l))) (iA ι t) = ∑ k, cA D (t k) * incA D (A.gram k l) := fun l => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hA_herm, e, GlobalTheory.BesselCompare.hA_sum, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hA_smul, RingHom.map_mul, hA_herm, hA_vec]
    congr 2
    exact hι _ _
  rw [e s, GlobalTheory.BesselCompare.hA_sum]
  simp only [hA_smul, e2]
  rw [hA, Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by ring

theorem hA_vec_iA {v : B.V} (h : ∀ x, B.hD v (ι x) = 0) (t : Fin A.rank → AE D) : hA B (vecA B v) (iA ι t) = 0 := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← hA_herm, iA, GlobalTheory.BesselCompare.frameMat_eq, GlobalTheory.BesselCompare.eMat_mulVec, GlobalTheory.BesselCompare.hA_sum, map_sum]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [hA_smul, RingHom.map_mul, hA_herm, hA_vec, h, map_zero, mul_zero]

theorem iA_smul (a : AE D) (t : Fin A.rank → AE D) : iA ι (a • t) = a • iA ι t := Matrix.mulVec_smul _ _ _

theorem iA_add (s t : Fin A.rank → AE D) : iA ι (s + t) = iA ι s + iA ι t := Matrix.mulVec_add _ _ _

theorem iA_neg (t : Fin A.rank → AE D) : iA ι (-t) = -iA ι t := Matrix.mulVec_neg _ _

theorem besselDatum_auxiliaryVector_orthogonal_image (d : BesselDatum A B ι) (i) (x : A.V) : B.hD (d.aux i) (ι x) = 0 := by
  unfold BesselDatum.aux
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [Fin.snoc_last]; exact d.zA x
  · rw [Fin.snoc_castSucc]; exact d.eA j x

theorem dual_perp (d : BesselDatum A B ι) (i) (x : A.V) : B.hD (dual d i) (ι x) = 0 := by
  unfold dual
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [Fin.snoc_last]
    have := d.zA x
    unfold HSpace.hD at this ⊢
    rw [map_smul, this, smul_zero]
  · rw [Fin.snoc_castSucc]; exact d.fA j x

end GlobalTheory.RootExch

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNontrivialAdeleCharTrivialOnTotallyReal
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNontrivialAdeleCharTrivialOnTotallyReal
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeEx.CharZero

private theorem extensionEmbedding_infiniteAdele_algebraMap (F : Type) [Field F] [NumberField F]
    (x : F) (v : InfinitePlace F) :
    InfinitePlace.Completion.extensionEmbedding v ((algebraMap F (InfiniteAdeleRing F) x) v) =
      v.embedding x := by
  simp [InfinitePlace.Completion.extensionEmbedding_coe]

private theorem sum_infinitePlace_embedding_eq_trace (F : Type) [Field F] [NumberField F]
    [IsTotallyReal F] (x : F) :
    ∑ v : InfinitePlace F, v.embedding x = ((Algebra.trace ℚ F x : ℚ) : ℂ) := by
  let e : InfinitePlace F ≃ (F →+* ℂ) :=
    { toFun := fun v => v.embedding
      invFun := InfinitePlace.mk
      left_inv := fun v => InfinitePlace.mk_embedding v
      right_inv := fun φ => InfinitePlace.embedding_mk_eq_of_isReal
        (IsTotallyReal.complexEmbedding_isReal φ) }
  rw [Fintype.sum_equiv e (fun v => v.embedding x) (fun φ => φ x) (fun _ => rfl)]
  have h := trace_eq_sum_embeddings (K := ℚ) (L := F) (E := ℂ) (x := x)
  rw [← eq_ratCast (algebraMap ℚ ℂ), h]
  convert Fintype.sum_equiv (RingHom.equivRatAlgHom F ℂ) (fun φ : F →+* ℂ => φ x)
    (fun φ : F →ₐ[ℚ] ℂ => φ x) (fun _ => rfl)

theorem _root_.GlobalTheory.GaugeEx.CharZero.exists_isCharAF :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], ∃ ψ, _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCharAF F ψ := by
  intro F _ _ _
  let L : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf F →+ ℂ := ∑ v : InfinitePlace F,
    (InfinitePlace.Completion.extensionEmbedding v).toAddMonoidHom.comp
      (Pi.evalAddMonoidHom (fun w : InfinitePlace F => w.Completion) v)
  have hLapply : (L : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf F → ℂ) = fun a => ∑ v : InfinitePlace F,
      InfinitePlace.Completion.extensionEmbedding v (a v) := by
    ext a
    simp [L, Pi.evalAddMonoidHom]
  have hL : Continuous L := by
    rw [hLapply]
    exact continuous_finsetSum _ fun v _ =>
      (InfinitePlace.Completion.isometry_extensionEmbedding v).continuous.comp
        (continuous_apply v)
  obtain ⟨ψ, hψ, -⟩ := _root_.GlobalTheory.StdAdelicChar.exists_char_of_trace F L hL (fun x => by
    rw [hLapply]
    change ∑ v : InfinitePlace F, InfinitePlace.Completion.extensionEmbedding v
      ((algebraMap F (InfiniteAdeleRing F) x) v) = _
    simp only [extensionEmbedding_infiniteAdele_algebraMap]
    exact sum_infinitePlace_embedding_eq_trace F x)
  exact ⟨ψ, hψ⟩

end GlobalTheory.GaugeEx.CharZero

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNontrivialAdeleCharTrivialOnTotallyRealStatement
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nontrivial_adeleChar_trivial_on_totallyReal : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], ∃ ψ, IsCharAF F ψ := by
  first | exact @GlobalTheory.GaugeEx.CharZero.exists_isCharAF | exact GlobalTheory.GaugeEx.CharZero.exists_isCharAF | (intros; apply GlobalTheory.GaugeEx.CharZero.exists_isCharAF <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOrientedWeilDatumOfAdelicWeilRepTheta
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOrientedWeilDatumOfAdelicWeilRepTheta
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.Mem.Th GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.WeilOriented

theorem exists_extend {G M M' : Type} [Monoid G] [AddCommGroup M] [Module ℂ M] [AddCommGroup M'] [Module ℂ M']
    (p : Submodule ℂ M) (E : M ≃ₗ[ℂ] M') (om : G →* Module.End ℂ p) :
    ∃ om' : G →* Module.End ℂ M', ∀ (g : G) (Φ : p), om' g (E Φ.1) = E (om g Φ).1 := by
  obtain ⟨q, hq⟩ := p.exists_isCompl
  let T : (p × q) ≃ₗ[ℂ] M' := (Submodule.prodEquivOfIsCompl p q hq).trans E
  have hT : ∀ Φ : p, T (Φ, 0) = E Φ.1 := fun Φ => by simp [T]
  refine ⟨{ toFun := fun g => T.toLinearMap ∘ₗ (LinearMap.prodMap (om g) LinearMap.id) ∘ₗ T.symm.toLinearMap
            map_one' := ?_
            map_mul' := fun a b => ?_ }, fun g Φ => ?_⟩
  · ext x
    simp
  · ext x
    simp
  · simp [← hT]

theorem lintegral_eq_of_integral_eq {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (Γ : AddSubgroup G) [DiscreteTopology Γ] {K : Set G} (hK : IsCompact K) (hcov : ∀ x : G, ∃ γ ∈ Γ, γ + x ∈ K)
    {f f' : G → ℂ} (hf : Continuous f) (hf' : Continuous f') (hp : ∀ γ ∈ Γ, ∀ w, ‖f (γ + w)‖ = ‖f w‖)
    (hp' : ∀ γ ∈ Γ, ∀ w, ‖f' (γ + w)‖ = ‖f' w‖) {μ : Measure G} {𝓕 : Set G} (hμ : μ.IsAddHaarMeasure)
    (h𝓕 : IsAddFundamentalDomain Γ 𝓕 μ) (h : ∫ w in 𝓕, ‖f w‖ ^ 2 ∂μ = ∫ w in 𝓕, ‖f' w‖ ^ 2 ∂μ) :
    ∫⁻ w in 𝓕, ‖f w‖ₑ ^ 2 ∂μ = ∫⁻ w in 𝓕, ‖f' w‖ₑ ^ 2 ∂μ := by
  have key := (GlobalTheory.meanSquare_addFundamentalDomain_of_cocompact G Γ K hK hcov).2
  obtain ⟨N, hN⟩ := key f hf hp
  obtain ⟨N', hN'⟩ := key f' hf' hp'
  obtain ⟨h0, h1, h2, h3⟩ := hN μ 𝓕 hμ h𝓕
  obtain ⟨-, -, h2', h3'⟩ := hN' μ 𝓕 hμ h𝓕
  rw [h3, h3'] at h
  have : N = N' := NNReal.coe_injective (mul_left_cancel₀ (ENNReal.toReal_ne_zero.2 ⟨h0, h1⟩) h)
  rw [h2, h2', this]

theorem norm_periodic {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {V W : HSp D}
    {f : WO V W → ℂ} (hf : IsThetaFunO ψ V W f) : ∀ γ ∈ ratL W V, ∀ w, ‖f (γ + w)‖ = ‖f w‖ := by
  rintro _ ⟨γ, rfl⟩ w
  have := congrArg norm (hf.quasi γ w)
  rw [norm_mul, hψ.1.2.1, one_mul] at this
  exact this

theorem exists_isWeilDatumO : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V W : HSp D) (χ χ' : IdC D) (om : GA D V × GA D W →* Module.End ℂ (ThS ψ V W)), admitted V W χ χ' → V.rank < W.rank → IsWeilOn ψ V W χ χ' om → ∃ omO : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ), IsWeilDatumO ψ V W χ χ' omO ∧ ∀ (p : GA D V × GA D W) (Φ : ThS ψ V W), omO p (fun x => Φ.1 (toTWsmall V W x)) = fun x => (om p Φ).1 (toTWsmall V W x) := by
  intro D ψ hψ V W χ χ' om ha hr hw
  obtain ⟨e, hc, hcs, he, hrat, hsm, hheis, hth, -⟩ := GlobalTheory.OrientedCoord.exists_coord D V W hr.le
  let E : (WA V W → ℂ) ≃ₗ[ℂ] (WO V W → ℂ) := LinearEquiv.funCongrLeft ℂ ℂ e.toEquiv
  obtain ⟨omO, hom⟩ := exists_extend (ThS ψ V W) E om
  have hom' : ∀ p (Φ : ThS ψ V W), omO p (fun x => Φ.1 (e x)) = fun x => (om p Φ).1 (e x) := hom
  have hsurj : ∀ f, IsThetaFunO ψ V W f → ∃ Φ : ThS ψ V W, f = fun x => Φ.1 (e x) := fun f hf => by
    have e1 : f = fun x => (fun y => f (e.symm y)) (e x) := by funext x; simp
    refine ⟨⟨fun y => f (e.symm y), mem_ThS.2 ((hth ψ _).1 ?_)⟩, e1⟩
    rw [← e1]; exact hf
  have hTh : ∀ Φ : ThS ψ V W, IsThetaFunO ψ V W fun x => Φ.1 (e x) := fun Φ => (hth ψ _).2 (mem_ThS.1 Φ.2)
  have hact : ∀ g h x, e (actO V W g h x) = actHom V W g h (e x) := fun g h x => by
    rw [he, he]; exact (GlobalTheory.OrientedSmall.bridgeSmall D V W hr.le).2 g h x
  refine ⟨omO, ⟨hψ, ha.2.1.1, ha.2.2.1.1, ha.2.2.2.1, ha.2.2.2.2, fun p f hf => ?_, fun g h w₀ f hf => ?_,
    fun γ hγ γ' hγ' f hf => ?_, fun f hf w => ?_, fun μ 𝓕 hμ h𝓕 p f hf => ?_,
    fun ε hε g h hg hh x y hx hy => ?_⟩, fun p Φ => ?_⟩
  · obtain ⟨Φ, rfl⟩ := hsurj f hf
    rw [hom']; exact hTh _
  · obtain ⟨Φ, rfl⟩ := hsurj f hf
    let Φ' : ThS ψ V W := ⟨Heisenberg₂ ψ V W (e w₀) Φ.1,
      mem_ThS.2 (GlobalTheory.Mem.ThetaClosed.isThetaFun_heis hψ (mem_ThS.1 Φ.2) _)⟩
    rw [hheis, hom', hheis, hact, ← hw.Heisenberg₂ g h (e w₀) Φ Φ' rfl]
    exact hom' _ Φ'
  · obtain ⟨Φ, rfl⟩ := hsurj f hf
    rw [hom']
    simp only [map_zero]
    exact hw.aut γ hγ γ' hγ' Φ
  · obtain ⟨Φ, rfl⟩ := hsurj f hf
    simp only [hom']
    exact hw.cont Φ (e w)
  · obtain ⟨Φ, rfl⟩ := hsurj f hf
    rw [hom']
    obtain ⟨i1, i2, i3, i4, i5, K, hK, hcov⟩ := GlobalTheory.AdelicMatrixLattice.lattice D W V
    obtain ⟨j1, -⟩ := GlobalTheory.AdelicMatrixLattice.lattice D V W
    have : BorelSpace (WA V W) := ⟨rfl⟩
    have : BorelSpace (WO V W) := ⟨rfl⟩
    obtain ⟨ν, hν, hF, hint⟩ := GlobalTheory.exists_isAddHaarMeasure_isAddFundamentalDomain_preimage (WA V W) (WO V W) e.symm hcs
      (by simpa using hc) (ratL V W) (ratL W V) (fun x => by rw [← hrat, e.apply_symm_apply]) μ 𝓕 hμ h𝓕
    refine lintegral_eq_of_integral_eq (ratL W V) hK hcov (hTh _).cont (hTh _).cont (norm_periodic hψ (hTh _))
      (norm_periodic hψ (hTh _)) hμ h𝓕 ?_
    rw [← hint, ← hint]
    simp only [e.apply_symm_apply]
    exact hw.unit ν _ hν hF p Φ
  · obtain ⟨r, hr0, hℓ⟩ := hw.split ε hε g h hg hh x y hx hy
    refine ⟨r, hr0, fun ℓ hinv f hf => ?_⟩
    obtain ⟨Φ, rfl⟩ := hsurj f hf
    have := hℓ (ℓ ∘ₗ E.toLinearMap ∘ₗ (ThS ψ V W).subtype) (fun u hu Ψ Ψ' hΨ => ?_) Φ
    · rw [hom']
      unfold splitFac at this
      rw [if_pos hr.le] at this
      exact this
    · have hu' : cA D ε • e.symm u = e.symm u := by
        apply e.injective
        rw [hsm, e.apply_symm_apply]
        exact Matrix.ext hu
      have := hinv (e.symm u) (fun i j => congrFun (congrFun hu' i) j) _ (hTh Ψ)
      rw [hheis, e.apply_symm_apply, ← hΨ] at this
      exact this
  · simp only [← he]
    exact hom' p Φ

end GlobalTheory.Mem.WeilOriented
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOrientedWeilDatumOfAdelicWeilRepThetaStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.Mem.Th GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_orientedWeilDatum_of_adelicWeilRep_theta : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V W : HSp D) (χ χ' : IdC D) (om : GA D V × GA D W →* Module.End ℂ (ThS ψ V W)), admitted V W χ χ' → V.rank < W.rank → IsWeilOn ψ V W χ χ' om → ∃ omO : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ), IsWeilDatumO ψ V W χ χ' omO ∧ ∀ (p : GA D V × GA D W) (Φ : ThS ψ V W), omO p (fun x => Φ.1 (toTWsmall V W x)) = fun x => (om p Φ).1 (toTWsmall V W x) := by
  first | exact @GlobalTheory.Mem.WeilOriented.exists_isWeilDatumO | exact GlobalTheory.Mem.WeilOriented.exists_isWeilDatumO | (intros; apply GlobalTheory.Mem.WeilOriented.exists_isWeilDatumO <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinPartAlgebraMap
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.LocWeil
open Formalism.MainNotions.KudlaSiegelWeil (Pl FinF FinE FF Over Split LocW Restr IntV)
open GlobalTheory.IndefiniteRowSideFullHecke.SymplecticTensorMeasures (ConjIsom basConj omTens toHom)
open Formalism.IndefR.Datum (IsHalf IsLatVac)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LocWeil.PlaceIdem

section General

variable (F : Type) [Field F] [NumberField F]

theorem evalV_single_same (v : HeightOneSpectrum (𝓞 F)) : evalV F v (singleV F v 1) = 1 :=
  RestrictedProduct.single_eq_same (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) v 1

theorem evalV_single_ne {u v : HeightOneSpectrum (𝓞 F)} (h : u ≠ v) : evalV F u (singleV F v 1) = 0 :=
  RestrictedProduct.single_eq_of_ne (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) 1 h

theorem af_ext {a b : Af F} (h : ∀ u, evalV F u a = evalV F u b) : a = b :=
  DFunLike.ext _ _ h

def eFin (v : HeightOneSpectrum (𝓞 F)) : AF F := pairA F 0 (singleV F v 1)

def eInf (v : InfinitePlace F) : AF F := pairA F (Pi.single v 1) 0

theorem eFin_mul_eFin {u v : HeightOneSpectrum (𝓞 F)} (h : u ≠ v) : eFin F u * eFin F v = 0 := by
  refine Prod.ext (mul_zero _) ?_
  change singleV F u 1 * singleV F v 1 = 0
  refine af_ext F fun w => ?_
  rw [map_mul, map_zero]
  by_cases hw : w = u
  · subst hw
    rw [evalV_single_ne F h, mul_zero]
  · rw [evalV_single_ne F hw, zero_mul]

theorem eFin_mul_eInf (u : HeightOneSpectrum (𝓞 F)) (v : InfinitePlace F) : eFin F u * eInf F v = 0 :=
  Prod.ext (zero_mul _) (mul_zero _)

theorem eInf_mul_eInf {u v : InfinitePlace F} (h : u ≠ v) : eInf F u * eInf F v = 0 := by
  refine Prod.ext ?_ (mul_zero _)
  funext w
  change (Pi.single u 1 : ∀ w : InfinitePlace F, w.Completion) w *
    (Pi.single v 1 : ∀ w : InfinitePlace F, w.Completion) w = 0
  by_cases hw : w = u
  · subst hw
    rw [Pi.single_eq_of_ne h, mul_zero]
  · rw [Pi.single_eq_of_ne hw, zero_mul]

theorem eq_zero_of_idem (a : AF F) (h1 : ∀ v, eFin F v * a = 0) (h2 : ∀ v, eInf F v * a = 0) : a = 0 := by
  refine Prod.ext ?_ ?_
  · funext w
    have h : (Pi.single w 1 : ∀ w : InfinitePlace F, w.Completion) w * a.1 w = 0 :=
      congrFun (congrArg Prod.fst (h2 w)) w
    rw [Pi.single_eq_same, one_mul] at h
    exact h
  · refine af_ext F fun w => ?_
    have h : singleV F w 1 * sndA F a = 0 := congrArg Prod.snd (h1 w)
    have h' := congrArg (evalV F w) h
    rw [map_mul, evalV_single_same, one_mul] at h'
    exact h'

theorem tensor_eq_zero {K E R I : Type} [Field K] [Field E] [Algebra K E] [CommRing R] [Algebra K R] (e : I → R)
    (he : ∀ a : R, (∀ i, e i * a = 0) → a = 0) (x : R ⊗[K] E)
    (hx : ∀ i, algebraMap R (R ⊗[K] E) (e i) * x = 0) : x = 0 := by
  let b := Algebra.TensorProduct.basis R (Module.Free.chooseBasis K E)
  refine b.ext_elem fun j => ?_
  rw [map_zero]
  refine he _ fun i => ?_
  have h := hx i
  rw [← Algebra.smul_def] at h
  have h' := congrArg (fun y => b.repr y j) h
  simpa using h'

theorem sum_single_one : (∑ v : InfinitePlace F, fstA F (eInf F v)) = 1 := by
  change (∑ v : InfinitePlace F, (Pi.single v 1 : ∀ w : InfinitePlace F, w.Completion)) = fun _ => 1
  exact Finset.univ_sum_single (fun w : InfinitePlace F => (1 : w.Completion))

theorem ext_eInf (σ : F →+* ℂ) (v : InfinitePlace F) :
    GlobalTheory.InfAdeleCM.ext σ (fstA F (eInf F v)) = if InfinitePlace.mk σ = v then 1 else 0 := by
  rw [GlobalTheory.InfAdeleCM.ext_apply]
  change InfinitePlace.Completion.extensionEmbedding (InfinitePlace.mk σ)
    ((Pi.single v 1 : ∀ w : InfinitePlace F, w.Completion) (InfinitePlace.mk σ)) = _
  split_ifs with h
  · subst h
    rw [Pi.single_eq_same, map_one]
  · rw [Pi.single_eq_of_ne h, map_zero]

end General

def plc (D : D7) (τ : D.what₂.Tau) : InfinitePlace D.host.F :=
  InfinitePlace.mk ((tauE D τ).comp (algebraMap D.host.F D.host.E))

theorem plc_bijective (D : D7) : Function.Bijective (plc D) := GlobalTheory.CMTypePlaces.places_bijective D

theorem idem_inl (D : D7) (v : FinF D) :
    idem D (.inl v) = algebraMap (AF D.host.F) (AE D) (eFin D.host.F v) := rfl

theorem idem_inr (D : D7) (τ : D.what₂.Tau) :
    idem D (.inr τ) = algebraMap (AF D.host.F) (AE D) (eInf D.host.F (plc D τ)) := rfl

theorem infPart_algebraMap (D : D7) (a : AF D.host.F) :
    infPart D (algebraMap (AF D.host.F) (AE D) a) = fstA D.host.F a ⊗ₜ[D.host.F] (1 : D.host.E) := rfl

theorem finPart_algebraMap (D : D7) (a : AF D.host.F) :
    finPart D (algebraMap (AF D.host.F) (AE D) a) = sndA D.host.F a ⊗ₜ[D.host.F] (1 : D.host.E) := rfl

theorem idem_props : ∀ D : D7, (∀ v v' : Pl D, v ≠ v' → idem D v * idem D v' = 0) ∧ (∀ θ : InfF D, IsInfFam θ → ∀ τ τ', θ τ' (infPart D (idem D (.inr τ))) = if τ' = τ then 1 else 0) ∧ (∀ τ, finPart D (idem D (.inr τ)) = 0) ∧ infPart D (∑ τ, idem D (.inr τ)) = 1 ∧ (∀ v : FinF D, ∃ a, IsPlaceIdem D v a ∧ idem D (.inl v) = algebraMap (AF D.host.F) (AE D) a) ∧ ∀ x : AE D, (∀ v, idem D v * x = 0) → x = 0 := by
  intro D
  have hb := plc_bijective D
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro (v | τ) (v' | τ') h
    · rw [idem_inl, idem_inl, ← RingHom.map_mul, eFin_mul_eFin _ fun e => h (congrArg _ e), RingHom.map_zero]
    · rw [idem_inl, idem_inr, ← RingHom.map_mul, eFin_mul_eInf, RingHom.map_zero]
    · rw [idem_inr, idem_inl, ← RingHom.map_mul, mul_comm, eFin_mul_eInf, RingHom.map_zero]
    · rw [idem_inr, idem_inr, ← RingHom.map_mul, eInf_mul_eInf _ fun e => h (congrArg _ (hb.1 e)), RingHom.map_zero]
  · intro θ hθ τ τ'
    haveI := D.sp.cm.totReal
    have h := GlobalTheory.InfAdeleCM.hom_tmul (tauE D τ') (θ τ') (hθ τ').1 (hθ τ').2
      (fstA D.host.F (eInf D.host.F (plc D τ))) 1
    rw [RingHom.map_one, mul_one, ext_eInf] at h
    rw [idem_inr, infPart_algebraMap]
    refine h.trans ?_
    exact if_congr (hb.1.eq_iff (a := τ') (b := τ)) rfl rfl
  · intro τ
    rw [idem_inr, finPart_algebraMap]
    exact TensorProduct.zero_tmul _ _
  · have h : (∑ τ, idem D (.inr τ)) =
        algebraMap (AF D.host.F) (AE D) (∑ v : InfinitePlace D.host.F, eInf D.host.F v) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← hb.sum_comp, map_sum (algebraMap (AF D.host.F) (AE D))]
      rfl
    set_option synthInstance.maxHeartbeats 100000 in
      rw [h, infPart_algebraMap, map_sum (fstA D.host.F), sum_single_one]
    rfl
  · intro v
    exact ⟨eFin D.host.F v, ⟨singleV D.host.F v 1, rfl, evalV_single_same _ v, fun v' h => evalV_single_ne _ h⟩, rfl⟩
  · intro x hx
    refine tensor_eq_zero (Sum.elim (eFin D.host.F) fun τ => eInf D.host.F (plc D τ)) (fun a ha => ?_) x ?_
    · refine eq_zero_of_idem _ a (fun v => ha (.inl v)) fun w => ?_
      obtain ⟨τ, rfl⟩ := hb.2 w
      exact ha (.inr τ)
    · rintro (v | τ)
      · exact hx (.inl v)
      · exact hx (.inr τ)

end GlobalTheory.LocWeil.PlaceIdem

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneSubMemIdS
open NumberField IsDedekindDomain Matrix Formalism.L2.Col
open Formalism.L2.DIV (Pl kP St resS oToS idS cmpS)
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.InertNbr

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def IdemOf (F : Type) [Field F] [NumberField F] [Algebra F E] (Q : Pl E) (ε : E ⊗[F] Formalism.L2.Herm.Af F) : Prop :=
  ε * ε = ε ∧ ∀ x : 𝓞 E, x ≠ 0 → (x ∈ Q.asIdeal ↔ ε * iA F E ((x : E)⁻¹) ∉ Formalism.L2.Herm.intAf F E)

namespace IdemOf

variable {Q : Pl E} {ε : E ⊗[F] Formalism.L2.Herm.Af F} (h : IdemOf F Q ε)
include h

theorem div_mem {t : 𝓞 E} (ht : t ∉ Q.asIdeal) : ε * iA F E ((t : E)⁻¹) ∈ Formalism.L2.Herm.intAf F E := by
  have t0 : t ≠ 0 := fun h0 => ht (h0 ▸ Q.asIdeal.zero_mem)
  by_contra hn
  exact ht ((h.2 t t0).2 hn)

theorem mem : ε ∈ Formalism.L2.Herm.intAf F E := by
  have := h.div_mem (one_notMem Q)
  simpa using this

theorem one_sub_mem : 1 - ε ∈ Formalism.L2.Herm.intAf F E := sub_mem (one_mem _) h.mem

theorem mul_one_sub : ε * (1 - ε) = 0 := by rw [mul_sub, h.1, mul_one, sub_self]

theorem mul_mem_of_val {x : E} (hx : Q.valuation E x ≤ 1) : ε * iA F E x ∈ Formalism.L2.Herm.intAf F E := by
  obtain ⟨a, t, ht, e⟩ := qsp_frac Q x hx
  have t0 : (t : E) ≠ 0 := fun h0 => ht (by rw [RingOfIntegers.coe_eq_zero_iff.1 h0]; exact zero_mem _)
  have e2 : x = (t : E)⁻¹ * algebraMap (𝓞 E) E a := by
    rw [← e]; field_simp
  rw [e2, map_mul, ← mul_assoc]
  exact mul_mem (h.div_mem ht) (iA_mem a)

theorem resS_eq_zero {w : Pl E} (hw : w ≠ Q) {a : E ⊗[F] Formalism.L2.Herm.Af F} (ha : ε * a ∈ Formalism.L2.Herm.intAf F E) :
    resS F w ⟨ε * a, ha⟩ = 0 := by
  obtain ⟨t, htw, htQ⟩ : ∃ t ∈ w.asIdeal, t ∉ Q.asIdeal := by
    by_contra hn
    push Not at hn
    exact hw (HeightOneSpectrum.ext (w.isMaximal.eq_of_le Q.isPrime.ne_top hn))
  have t0 : (t : E) ≠ 0 := fun h0 => htQ (by rw [RingOfIntegers.coe_eq_zero_iff.1 h0]; exact zero_mem _)
  have e : (⟨ε * a, ha⟩ : Formalism.L2.Herm.intAf F E) = oToS F E t * (⟨_, h.div_mem htQ⟩ * ⟨ε * a, ha⟩) := by
    apply Subtype.ext
    show ε * a = iA F E (t : E) * (ε * iA F E ((t : E)⁻¹) * (ε * a))
    have : iA F E (t : E) * iA F E ((t : E)⁻¹) = 1 := by rw [← map_mul, mul_inv_cancel₀ t0, map_one]
    linear_combination (-(ε * a) * ε) * this - a * h.1
  rw [e, map_mul, Formalism.L2.DIV.resS_oToS, Ideal.Quotient.eq_zero_iff_mem.2 htw, zero_mul]

omit h in
theorem val_unif {ϖ : 𝓞 E} (h1 : ϖ ∈ Q.asIdeal) (h2 : ϖ ∉ Q.asIdeal ^ 2) :
    Q.valuation E (ϖ : E) = WithZero.exp (-1 : ℤ) := by
  rw [show (ϖ : E) = algebraMap (𝓞 E) E ϖ from rfl, HeightOneSpectrum.valuation_of_algebraMap]
  have a1 := (Q.intValuation_le_pow_iff_mem ϖ 1).2 (by rwa [pow_one])
  have a2 := (Q.intValuation_le_pow_iff_mem ϖ 2).not.2 h2
  have h0 : Q.intValuation ϖ ≠ 0 := fun h0 => a2 (by rw [h0]; exact zero_le)
  rw [← WithZero.exp_log h0, WithZero.exp_le_exp] at a1 a2
  rw [← WithZero.exp_log h0]
  congr 1
  push_cast at a1 a2
  omega

omit h in
theorem unif_ne {ϖ : 𝓞 E} (h2 : ϖ ∉ Q.asIdeal ^ 2) : (ϖ : E) ≠ 0 := fun h0 =>
  h2 (by rw [RingOfIntegers.coe_eq_zero_iff.1 h0]; exact zero_mem _)

theorem div_pow_mem {ϖ : 𝓞 E} (h1 : ϖ ∈ Q.asIdeal) (h2 : ϖ ∉ Q.asIdeal ^ 2) (m : ℕ) {a : Formalism.L2.Herm.intAf F E}
    (ha : a ∈ idS F (Q.asIdeal ^ m)) :
    ε * iA F E (((ϖ : E) ^ m)⁻¹) * a ∈ Formalism.L2.Herm.intAf F E := by
  refine Submodule.span_induction
    (p := fun (a : Formalism.L2.Herm.intAf F E) _ => ε * iA F E (((ϖ : E) ^ m)⁻¹) * (a : E ⊗[F] Formalism.L2.Herm.Af F) ∈ Formalism.L2.Herm.intAf F E) ?_ ?_ ?_ ?_ ha
  · rintro _ ⟨p, hp, rfl⟩
    rw [← iA_coe, mul_assoc, ← map_mul]
    refine h.mul_mem_of_val ?_
    have a1 := (Q.intValuation_le_pow_iff_mem p m).2 hp
    rw [map_mul, map_inv₀, map_pow, val_unif h1 h2, HeightOneSpectrum.valuation_of_algebraMap, ← WithZero.exp_nsmul,
      inv_mul_le_iff₀ (zero_lt_iff.2 WithZero.exp_ne_zero), mul_one]
    simpa using a1
  · simp
  · intro a b _ _ ha hb
    rw [Subring.coe_add, mul_add]; exact add_mem ha hb
  · intro c a _ ha
    rw [smul_eq_mul, Subring.coe_mul, mul_left_comm]; exact mul_mem c.2 ha

theorem one_sub_mem_idS [StarRing E] (m : ℕ) : (⟨1 - ε, h.one_sub_mem⟩ : Formalism.L2.Herm.intAf F E) ∈ idS F (Q.asIdeal ^ m) := by
  obtain ⟨ϖ, h1, h2⟩ := Ideal.exists_mem_pow_notMem_pow_succ Q.asIdeal Q.ne_bot Q.isPrime.ne_top 1
  rw [pow_one] at h1
  have hi : (⟨1 - ε, h.one_sub_mem⟩ : Formalism.L2.Herm.intAf F E) * ⟨ε, h.mem⟩ = 0 :=
    Subtype.ext (by show (1 - ε) * ε = 0; rw [mul_comm, h.mul_one_sub])
  have h3 : resS F Q ⟨1 - ε, h.one_sub_mem⟩ = 0 := by
    have := congrArg (resS F Q) hi
    rw [map_mul, map_zero] at this
    refine (mul_eq_zero.1 this).resolve_right fun h0 => ?_
    have h4 := h.div_pow_mem h1 h2 1 (a := ⟨ε, h.mem⟩) (by rw [pow_one]; exact mem_idS_of_resS h0)
    have ϖ0 : ϖ ≠ 0 := fun h0 => h2 (h0 ▸ zero_mem _)
    refine (h.2 ϖ ϖ0).1 h1 ?_
    rwa [pow_one, mul_right_comm, h.1] at h4
  have h5 := Ideal.pow_mem_pow (mem_idS_of_resS h3) m
  have h6 : (⟨1 - ε, h.one_sub_mem⟩ : Formalism.L2.Herm.intAf F E) * ⟨1 - ε, h.one_sub_mem⟩ = ⟨1 - ε, h.one_sub_mem⟩ :=
    Subtype.ext (by show (1 - ε) * (1 - ε) = 1 - ε; linear_combination h.1)
  rcases m with _ | m
  · unfold idS
    rw [pow_zero, Ideal.one_eq_top, Ideal.map_top]; trivial
  · rw [IsIdempotentElem.pow_succ_eq m h6] at h5
    unfold idS at h5 ⊢
    rwa [Ideal.map_pow]

theorem mem_idS_pow_iff [StarRing E] {ϖ : 𝓞 E} (h1 : ϖ ∈ Q.asIdeal) (h2 : ϖ ∉ Q.asIdeal ^ 2) (m : ℕ) (a : Formalism.L2.Herm.intAf F E) :
    a ∈ idS F (Q.asIdeal ^ m) ↔ ε * iA F E (((ϖ : E) ^ m)⁻¹) * a ∈ Formalism.L2.Herm.intAf F E := by
  refine ⟨h.div_pow_mem h1 h2 m, fun ha => ?_⟩
  have e : a = oToS F E (ϖ ^ m) * ⟨_, ha⟩ + ⟨1 - ε, h.one_sub_mem⟩ * a := by
    apply Subtype.ext
    show (a : E ⊗[F] Formalism.L2.Herm.Af F) = iA F E (algebraMap (𝓞 E) E (ϖ ^ m)) * (ε * iA F E (((ϖ : E) ^ m)⁻¹) * a) + (1 - ε) * a
    have : iA F E (algebraMap (𝓞 E) E (ϖ ^ m)) * iA F E (((ϖ : E) ^ m)⁻¹) = 1 := by
      rw [← map_mul, map_pow, mul_inv_cancel₀ (pow_ne_zero _ (unif_ne h2)), map_one]
    linear_combination (-(ε * (a : E ⊗[F] Formalism.L2.Herm.Af F))) * this
  rw [e]
  exact add_mem (Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (Ideal.pow_mem_pow h1 m)))
    (Ideal.mul_mem_right _ _ (h.one_sub_mem_idS m))

end IdemOf

end GlobalTheory.InertNbr
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DenseRangeOfImNeZero
open Formalism.BasicNotions Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.IndefR.Links NumberField GlobalTheory.Mem.SJ
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.SJ

theorem denseRange_of_im_ne_zero {K : Type} [Field K] [CharZero K] (σ : K →+* ℂ) (h : ∃ a, (σ a).im ≠ 0) :
    DenseRange σ := by
  obtain ⟨a, ha⟩ := h
  have hg : Continuous fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * σ a := by fun_prop
  have hs : Function.Surjective fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * σ a := by
    intro z
    refine ⟨(z.re - z.im / (σ a).im * (σ a).re, z.im / (σ a).im), ?_⟩
    apply Complex.ext
    · simp only [Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul]
      ring
    · simp only [Complex.add_im, Complex.ofReal_im, Complex.im_ofReal_mul]
      field_simp
      ring
  have hq : DenseRange (Prod.map ((↑) : ℚ → ℝ) ((↑) : ℚ → ℝ)) :=
    Rat.denseRange_cast.prodMap Rat.denseRange_cast
  have hc := hs.denseRange.comp hq hg
  refine hc.mono ?_
  rintro _ ⟨⟨p, q⟩, rfl⟩
  exact ⟨(p : K) + (q : K) * a, by simp⟩

theorem normAt_sq_eq_majAt_re {K V ι : Type*} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K)
    (x : V) : Formalism.HermitianLatticesTheory.normAt b X v x = Real.sqrt (Formalism.HermitianLatticesTheory.majAt b X v x x).re := by
  unfold Formalism.HermitianLatticesTheory.normAt Formalism.HermitianLatticesTheory.cnorm Formalism.HermitianLatticesTheory.majAt
  congr 1
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]

theorem fnorm_cjv_eq_norm : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (σ : K →+* ℂ) (s : Bool), (∀ a, (InfinitePlace.mk σ).embedding a = cj s (σ a)) → (∃ a, (σ a).im ≠ 0) → ∀ (A : HLat K) (d : ℕ) (L : Submodule (RingOfIntegers K) (Fin d → K)) (Xf : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ) (e : (Fin d → K) ≃ₗ[K] A.V), HLatTie A L Xf e → ∀ (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] (j : A.V →ₛₗ[σ] W) (c : W ≃ₗ[ℂ] (Fin d → ℂ)), (∀ x, Formalism.HermitianLatticesTheory.normAt A.b A.X (InfinitePlace.mk σ) x = ‖j x‖) → (∀ x, c.symm (cpt σ x) = j (e x)) → ∀ w : W, Formalism.DivisionValues.fnorm (Xf (InfinitePlace.mk σ)) (cjv s (c w)) = ‖w‖ := by
  intro K _ _ _ σ s htw hnr A d L Xf e hT W _ _ j c hn hc w
  have hd : DenseRange (cpt σ : (Fin d → K) → Fin d → ℂ) :=
    DenseRange.piMap (fun _ : Fin d => denseRange_of_im_ne_zero σ hnr)
  have hcj : Continuous (cj s) := by
    cases s
    · exact continuous_id
    · exact Complex.continuous_conj
  have h1 : Continuous fun z : Fin d → ℂ => Formalism.DivisionValues.fnorm (Xf (InfinitePlace.mk σ)) (cjv s z) := by
    unfold Formalism.DivisionValues.fnorm Formalism.HermitianLatticesTheory.cnorm cjv Matrix.mulVec dotProduct
    fun_prop
  have h2 : Continuous fun z : Fin d → ℂ => ‖c.symm z‖ :=
    (LinearMap.continuous_of_finiteDimensional c.symm.toLinearMap).norm
  have key : ∀ z : Fin d → ℂ, Formalism.DivisionValues.fnorm (Xf (InfinitePlace.mk σ)) (cjv s z) = ‖c.symm z‖ := by
    intro z
    refine hd.induction_on z (isClosed_eq h1 h2) fun x => ?_
    rw [hc, ← hn, normAt_sq_eq_majAt_re, hT.metric, ← normAt_sq_eq_majAt_re]
    have hv : cjv s (cpt σ x) = Formalism.HermitianLatticesTheory.vecAt (Pi.basisFun K (Fin d)) (InfinitePlace.mk σ) x := by
      funext i
      simp [cjv, cpt, Formalism.HermitianLatticesTheory.vecAt, htw]
    rw [hv]
    rfl
  rw [key, c.symm_apply_apply]

end GlobalTheory.Mem.SJ
end
