module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ComplexConjugationMapsMultiplicitySpace
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeVecMemFixed
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrameMatrixMovedHomIntegralReduction
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrameMatrixMovedHomIntegralReduction
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.StepLaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FrameRed

section General

variable {R k : Type} [CommRing R] [CommRing k] {b a : ℕ}


open Classical in
theorem int_mul (O : Subring R) (ρ : O →+* k) (z : Matrix (Fin b) (Fin b) O) (y : Matrix (Fin a) (Fin a) O)
    (N : Matrix (Fin b) (Fin a) R) (h : ∀ i j, N i j ∈ O) :
    (∀ i j, (z.map O.subtype * N * y.map O.subtype) i j ∈ O) ∧
    (Matrix.of fun i j => if h : (z.map O.subtype * N * y.map O.subtype) i j ∈ O then
        ρ ⟨(z.map O.subtype * N * y.map O.subtype) i j, h⟩ else 0) =
      z.map ρ * (Matrix.of fun i j => if h : N i j ∈ O then ρ ⟨N i j, h⟩ else 0) * y.map ρ := by
  obtain ⟨M, rfl⟩ : ∃ M : Matrix (Fin b) (Fin a) O, N = M.map O.subtype :=
    ⟨Matrix.of fun i j => ⟨N i j, h i j⟩, by ext i j; rfl⟩
  have key : z.map O.subtype * M.map O.subtype * y.map O.subtype = (z * M * y).map O.subtype := by
    rw [Matrix.map_mul, Matrix.map_mul]
  have mem : ∀ i j, (z.map O.subtype * M.map O.subtype * y.map O.subtype) i j ∈ O := fun i j => by
    rw [key]; exact ((z * M * y) i j).2
  refine ⟨mem, ?_⟩
  have lhs : (Matrix.of fun i j => if h : (z.map O.subtype * M.map O.subtype * y.map O.subtype) i j ∈ O then
      ρ ⟨(z.map O.subtype * M.map O.subtype * y.map O.subtype) i j, h⟩ else 0) = (z * M * y).map ρ := by
    ext i j
    rw [Matrix.of_apply, dite_eq_left (mem i j), Matrix.map_apply]
    congr 1
    exact Subtype.ext (congrFun (congrFun key i) j)
  have mid : (Matrix.of fun i j => if h : M.map O.subtype i j ∈ O then ρ ⟨M.map O.subtype i j, h⟩ else 0) = M.map ρ := by
    ext i j
    rw [Matrix.of_apply, dite_eq_left (h i j)]
    rfl
  rw [lhs, mid, Matrix.map_mul, Matrix.map_mul]

theorem cancel (Z : GL (Fin b) R) (Y : GL (Fin a) R) (N : Matrix (Fin b) (Fin a) R) :
    Z.val * ((Z⁻¹).val * N * Y.val) * (Y⁻¹).val = N := by
  calc Z.val * ((Z⁻¹).val * N * Y.val) * (Y⁻¹).val
      = (Z.val * (Z⁻¹).val) * N * (Y.val * (Y⁻¹).val) := by simp only [Matrix.mul_assoc]
    _ = N := by rw [Units.mul_inv, Units.mul_inv, Matrix.one_mul, Matrix.mul_one]

theorem move {A : Type} [CommRing A] (f : A →+* R) (βS G Y : GL (Fin a) R) (βT H Z : GL (Fin b) R)
    (hY : βS * Y * βS⁻¹ = G) (hZ : βT * Z * βT⁻¹ = H)
    (g : Matrix (Fin a) (Fin a) A) (h : Matrix (Fin b) (Fin b) A) (hg : g.map f = G.val) (hh : h.map f = (H⁻¹).val)
    (x : Matrix (Fin b) (Fin a) A) :
    (βT⁻¹).val * (h * x * g).map f * βS.val = (Z⁻¹).val * ((βT⁻¹).val * x.map f * βS.val) * Y.val := by
  have eH : (H⁻¹).val = βT.val * ((Z⁻¹).val * (βT⁻¹).val) := by
    rw [← hZ, mul_inv_rev, mul_inv_rev, inv_inv, Units.val_mul, Units.val_mul]
  have eG : G.val = βS.val * (Y.val * (βS⁻¹).val) := by
    rw [← hY, Units.val_mul, Units.val_mul, Matrix.mul_assoc]
  rw [Matrix.map_mul, Matrix.map_mul, hg, hh, eH, eG]
  simp only [Matrix.mul_assoc]
  rw [Units.inv_mul, Matrix.mul_one, ← Matrix.mul_assoc (βT⁻¹).val βT.val, Units.inv_mul, Matrix.one_mul]

private theorem bc_mul_restrict_mul_bc_eq (O : Subring R) (ρ : O →+* k) (z : GL (Fin b) O) (y : GL (Fin a) O)
    (N : Matrix (Fin b) (Fin a) R) (h : ∀ i j, N i j ∈ O) :
    (∀ i j, ((Formalism.UG.bc O.subtype z).val * N * (Formalism.UG.bc O.subtype y).val) i j ∈ O) ∧
    (Matrix.of fun i j => @dite _ (((Formalism.UG.bc O.subtype z).val * N * (Formalism.UG.bc O.subtype y).val) i j ∈ O)
        (Classical.propDecidable _) (fun h => ρ ⟨_, h⟩) (fun _ => 0)) =
      (Formalism.UG.bc ρ z).val *
        (Matrix.of fun i j => @dite _ (N i j ∈ O) (Classical.propDecidable _) (fun h => ρ ⟨N i j, h⟩) (fun _ => 0)) *
        (Formalism.UG.bc ρ y).val := by
  have ez : (Formalism.UG.bc O.subtype z).val = z.val.map O.subtype := rfl
  have ey : (Formalism.UG.bc O.subtype y).val = y.val.map O.subtype := rfl
  have ez' : (Formalism.UG.bc ρ z).val = z.val.map ρ := rfl
  have ey' : (Formalism.UG.bc ρ y).val = y.val.map ρ := rfl
  rw [ez, ey, ez', ey']
  exact GlobalTheory.FrameRed.int_mul O ρ z.val y.val N h

end General

variable {D : D7}

theorem isIntM_mul {b a : ℕ} (z : GL (Fin b) (Formalism.L2.Herm.intAf D.host.F D.host.E))
    (y : GL (Fin a) (Formalism.L2.Herm.intAf D.host.F D.host.E)) {N : Matrix (Fin b) (Fin a) (Datum.EAf D)}
    (h : IsIntM (D := D) N) :
    IsIntM (D := D) ((intGL D.host.F D.host.E b z).val * N * (intGL D.host.F D.host.E a y).val) ∧
    ∀ PP, redM (D := D) PP ((intGL D.host.F D.host.E b z).val * N * (intGL D.host.F D.host.E a y).val) =
      (Formalism.UG.bc (resS D.host.F PP) z).val * redM (D := D) PP N * (Formalism.UG.bc (resS D.host.F PP) y).val := by
  exact ⟨(bc_mul_restrict_mul_bc_eq _ (RingHom.id _) z y N h).1, fun PP => (bc_mul_restrict_mul_bc_eq _ (resS D.host.F PP) z y N h).2⟩

theorem mt_map (V : HSp D) (g : GA D V) :
    (Formalism.L2.Theta.mt V g).map (toEAf D) = (finE V g).val := rfl

theorem frMapO_actO {S T : HSp D} {βS : GL (Fin S.rank) (Lev.EAf D)} {βT : GL (Fin T.rank) (Lev.EAf D)}
    {g : GA D S} {h : GA D T} {y : GL (Fin S.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E)}
    {z : GL (Fin T.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E)}
    (hy : frGL βS y = finE S g) (hz : frGL βT z = finE T h) (x : WO S T) :
    frMapO S T βS βT (actO S T g⁻¹ h⁻¹ x) =
      ((intGL D.host.F D.host.E _ z)⁻¹).val * frMapO S T βS βT x * (intGL D.host.F D.host.E _ y).val := by
  have hY : βS * intGL D.host.F D.host.E _ y * βS⁻¹ = finE S g := by rw [← hy]; rfl
  have hZ : βT * intGL D.host.F D.host.E _ z * βT⁻¹ = finE T h := by rw [← hz]; rfl
  have hg : (Formalism.L2.Theta.mt S g⁻¹⁻¹).map (toEAf D) = (finE S g).val := by rw [inv_inv]; exact GlobalTheory.FrameRed.mt_map S g
  have hh : (Formalism.L2.Theta.mt T h⁻¹).map (toEAf D) = ((finE T h)⁻¹).val := by rw [GlobalTheory.FrameRed.mt_map, map_inv]
  show (βT⁻¹).val * (Formalism.L2.Theta.mt T h⁻¹ * x * Formalism.L2.Theta.mt S g⁻¹⁻¹).map (toEAf D) * βS.val = _
  exact GlobalTheory.FrameRed.move (toEAf D) βS (finE S g) (intGL D.host.F D.host.E _ y) βT (finE T h)
    (intGL D.host.F D.host.E _ z) hY hZ _ _ hg hh x

theorem isIntM_iff {b a : ℕ} (z : GL (Fin b) (Formalism.L2.Herm.intAf D.host.F D.host.E))
    (y : GL (Fin a) (Formalism.L2.Herm.intAf D.host.F D.host.E)) (N : Matrix (Fin b) (Fin a) (Datum.EAf D)) :
    IsIntM (D := D) (((intGL D.host.F D.host.E b z)⁻¹).val * N * (intGL D.host.F D.host.E a y).val) ↔
      IsIntM (D := D) N := by
  constructor
  · intro hM
    have h1 := (GlobalTheory.FrameRed.isIntM_mul (D := D) z y⁻¹ hM).1
    rwa [map_inv (intGL D.host.F D.host.E a) y, GlobalTheory.FrameRed.cancel] at h1
  · intro hN
    have h1 := (GlobalTheory.FrameRed.isIntM_mul (D := D) z⁻¹ y hN).1
    rwa [map_inv (intGL D.host.F D.host.E b) z] at h1

theorem redM_mul {b a : ℕ} (z : GL (Fin b) (Formalism.L2.Herm.intAf D.host.F D.host.E))
    (y : GL (Fin a) (Formalism.L2.Herm.intAf D.host.F D.host.E)) {N : Matrix (Fin b) (Fin a) (Datum.EAf D)}
    (h : IsIntM (D := D) N) (PP : Pl D.host.E) :
    redM (D := D) PP (((intGL D.host.F D.host.E b z)⁻¹).val * N * (intGL D.host.F D.host.E a y).val) =
      ((Formalism.UG.bc (resS D.host.F PP) z)⁻¹).val * redM (D := D) PP N * (Formalism.UG.bc (resS D.host.F PP) y).val := by
  have h1 := (GlobalTheory.FrameRed.isIntM_mul (D := D) z⁻¹ y h).2 PP
  rwa [map_inv (intGL D.host.F D.host.E b) z, map_inv (Formalism.UG.bc (resS D.host.F PP)) z] at h1

theorem frMapO_actO_red : ∀ (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (g : GA D S) (h : GA D T), finE S g ∈ St βS → finE T h ∈ St βT → ∀ x : WO S T, (IsIntM (frMapO S T βS βT (actO S T g⁻¹ h⁻¹ x)) ↔ IsIntM (frMapO S T βS βT x)) ∧ (IsIntM (frMapO S T βS βT x) → ∀ PP, redM PP (frMapO S T βS βT (actO S T g⁻¹ h⁻¹ x)) = ((redFn βT PP (finE T h))⁻¹).val * redM PP (frMapO S T βS βT x) * (redFn βS PP (finE S g)).val) := by
  intro D S T βS βT g h hg hh x
  unfold St at hg hh
  obtain ⟨y, hy⟩ := MonoidHom.mem_range.1 hg
  obtain ⟨z, hz⟩ := MonoidHom.mem_range.1 hh
  have e := GlobalTheory.FrameRed.frMapO_actO hy hz x
  refine ⟨?_, fun hI PP => ?_⟩
  · rw [e]
    exact GlobalTheory.FrameRed.isIntM_iff z y _
  · rw [e, GlobalTheory.FrameRed.redM_mul z y hI PP]
    have a : redFn βS PP (finE S g) = Formalism.UG.bc (resS D.host.F PP) y := by
      rw [← hy]; exact redFn_frGL βS PP y
    have b : redFn βT PP (finE T h) = Formalism.UG.bc (resS D.host.F PP) z := by
      rw [← hz]; exact redFn_frGL βT PP z
    rw [a, b]

end GlobalTheory.FrameRed

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrameMatrixMovedHomIntegralReductionStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.StepLaw
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameMatrix_movedHom_integral_reduction : ∀ (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (g : GA D S) (h : GA D T), finE S g ∈ St βS → finE T h ∈ St βT → ∀ x : WO S T, (IsIntM (frMapO S T βS βT (actO S T g⁻¹ h⁻¹ x)) ↔ IsIntM (frMapO S T βS βT x)) ∧ (IsIntM (frMapO S T βS βT x) → ∀ PP, redM PP (frMapO S T βS βT (actO S T g⁻¹ h⁻¹ x)) = ((redFn βT PP (finE T h))⁻¹).val * redM PP (frMapO S T βS βT x) * (redFn βS PP (finE S g)).val) := by
  first | exact @GlobalTheory.FrameRed.frMapO_actO_red | exact GlobalTheory.FrameRed.frMapO_actO_red | (intros; apply GlobalTheory.FrameRed.frMapO_actO_red <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TypePlacesLocalDatumBlockTriangularLaw
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TypePlacesLocalDatumBlockTriangularLaw
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.StepLaw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StepLaw.TypeDatum

section Mat

variable {κ : Type} [CommRing κ] {a b r t j : ℕ}

theorem blkOf_le {n : ℕ} (ea : a = r + j * t) (i : Fin n) (hi : i.val < a) : blkOf r t i ≤ j := by
  unfold blkOf
  split_ifs with h
  · exact Nat.zero_le _
  · have : (i.val - r) / t < j := Nat.div_lt_of_lt_mul (by rw [mul_comm]; omega)
    omega

theorem blkOf_eq (ea : a = r + j * t) (eb : b = r + (j + 1) * t) (i : Fin b) (hi : a ≤ i.val) :
    blkOf r t i = j + 1 := by
  unfold blkOf
  have h2 := i.2
  rw [if_neg (by omega), Nat.div_eq_of_lt_le (k := j) (by omega) (by omega)]

theorem mem_twoBlockTriangular_of_blockTriangular (ea : a = r + j * t) (eb : b = r + (j + 1) * t) {g : GL (Fin b) κ}
    (hg : g ∈ blockTri (blkOf r t)) : g ∈ blockTri (blk2 a) := by
  intro p q hpq
  refine hg ?_
  unfold blk2 at hpq
  have hq : q.val < a := by
    by_contra hq
    split_ifs at hpq <;> omega
  have hp : a ≤ p.val := by
    by_contra hp
    split_ifs at hpq <;> omega
  rw [blkOf_eq ea eb p hp]
  exact Nat.lt_succ_of_le (blkOf_le ea q hq)

theorem top_mem (hab : a ≤ b) {g : GL (Fin b) κ} (h2 : g ∈ blockTri (blk2 a))
    (hg : g ∈ blockTri (blkOf r t)) : upperLeftBlock hab g ∈ blockTri (blkOf r t) := by
  rw [mem_blockTri]
  intro p q hpq
  rw [upper_block_val_submatrix hab h2]
  exact hg (show blkOf r t (Fin.castLE hab q) < blkOf r t (Fin.castLE hab p) from hpq)

theorem restrictTopBlock_restrictTopBlock (hab : a ≤ b) (ha : r ≤ a) (hb : r ≤ b) {g : GL (Fin b) κ} (h2 : g ∈ blockTri (blk2 a))
    (hg : g ∈ blockTri (blkOf r t)) : upperLeftBlock ha (upperLeftBlock hab g) = upperLeftBlock hb g := by
  apply Units.ext
  rw [upper_block_val_submatrix ha (blockTri_blkOf_le r t (top_mem hab h2 hg)), upper_block_val_submatrix hab h2, upper_block_val_submatrix hb (blockTri_blkOf_le r t hg)]
  rfl

theorem diagonalBlock_restrictTopBlock (hab : a ≤ b) (ea : a = r + j * t) (eb : b = r + (j + 1) * t) {g : GL (Fin b) κ}
    (hg : g ∈ blockTri (blkOf r t)) {c : ℕ} (hc : c ≤ j) :
    dBlk (blkOf r t) c (upperLeftBlock hab g) = dBlk (blkOf r t) c g := by
  have h2 := mem_twoBlockTriangular_of_blockTriangular ea eb hg
  apply Units.ext
  rw [diag_block_det_val c (top_mem hab h2 hg), diag_block_det_val c hg, upper_block_val_submatrix hab h2]
  have hlt : ∀ i : {i : Fin b // blkOf r t i = c}, i.1.val < a := fun i => by
    by_contra hi
    have := blkOf_eq ea eb i.1 (not_lt.1 hi)
    have := i.2
    omega
  let e : {i : Fin a // blkOf r t i = c} ≃ {i : Fin b // blkOf r t i = c} :=
    { toFun := fun i => ⟨Fin.castLE hab i.1, i.2⟩
      invFun := fun i => ⟨⟨i.1.val, hlt i⟩, i.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← Matrix.det_submatrix_equiv_self e]
  rfl

theorem det_top (hab : a ≤ b) (ea : a = r + j * t) (eb : b = r + (j + 1) * t) {g : GL (Fin b) κ}
    (hg : g ∈ blockTri (blkOf r t)) :
    Matrix.GeneralLinearGroup.det g =
      Matrix.GeneralLinearGroup.det (upperLeftBlock hab g) * dBlk (blkOf r t) (j + 1) g := by
  have h2 := mem_twoBlockTriangular_of_blockTriangular ea eb hg
  apply Units.ext
  rw [Units.val_mul, Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply,
    diag_block_det_val _ hg, upper_block_val_submatrix hab h2,
    Matrix.twoBlockTriangular_det (g : Matrix (Fin b) (Fin b) κ) (fun i => i.val < a) (fun p hp q hq =>
      h2 (show blk2 a q < blk2 a p by simp [blk2, hp, hq]))]
  let e : Fin a ≃ {i : Fin b // i.val < a} :=
    { toFun := fun i => ⟨Fin.castLE hab i, i.2⟩
      invFun := fun i => ⟨i.1.val, i.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let e' : {i : Fin b // blkOf r t i = j + 1} ≃ {i : Fin b // ¬ i.val < a} :=
    Equiv.subtypeEquivRight fun i =>
      ⟨fun h h' => by have := blkOf_le ea i h'; omega, fun h => blkOf_eq ea eb i (not_lt.1 h)⟩
  rw [← Matrix.det_submatrix_equiv_self e, ← Matrix.det_submatrix_equiv_self e']
  rfl

theorem topL_apply (hab : a ≤ b) (y : Matrix (Fin b) (Fin a) κ) (p q : Fin a) :
    topL a y p q = y (Fin.castLE hab p) q := by
  unfold topL
  rw [dite_eq_left ⟨lt_of_lt_of_le p.2 hab, q.2⟩]
  rfl

theorem lowZero_mul {g : GL (Fin b) κ} (h2 : g ∈ blockTri (blk2 a)) {y : Matrix (Fin b) (Fin a) κ}
    (hy : LowZero a y) (s : Matrix (Fin a) (Fin a) κ) : LowZero a (g.val * y * s) := by
  intro p q hp _
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  rw [Matrix.mul_apply, Finset.sum_eq_zero fun m _ => ?_, zero_mul]
  by_cases hm : m.val < a
  · rw [h2 (show blk2 a m < blk2 a p by simp [blk2, hm, not_lt.2 hp]), zero_mul]
  · rw [hy m l (not_lt.1 hm) l.2, mul_zero]

theorem topL_mul (hab : a ≤ b) {g : GL (Fin b) κ} (h2 : g ∈ blockTri (blk2 a)) {y : Matrix (Fin b) (Fin a) κ}
    (hy : LowZero a y) (s : Matrix (Fin a) (Fin a) κ) :
    topL a (g.val * y * s) = (upperLeftBlock hab g).val * topL a y * s := by
  ext p q
  rw [topL_apply hab, upper_block_val_submatrix hab h2, Matrix.mul_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  congr 1
  rw [Matrix.mul_apply, Matrix.mul_apply]
  refine (Fintype.sum_of_injective (Fin.castLE hab) (Fin.castLE_injective hab) _ _ (fun m hm => ?_) fun m => ?_).symm
  · have hm' : ¬ m.val < a := fun h => hm ⟨⟨m.val, h⟩, by ext; rfl⟩
    rw [hy m l (not_lt.1 hm') l.2, mul_zero]
  · rw [topL_apply hab]; rfl

def IsTop (t : ℕ) (ha : r ≤ a) (y : Matrix (Fin b) (Fin a) κ) (g : GL (Fin a) κ) : Prop :=
  LowZero a y ∧ g.val = topL a y ∧ g ∈ blockTri (blkOf r t) ∧ upperLeftBlock ha g = 1

theorem IsTop.move (hab : a ≤ b) (ha : r ≤ a) (hb : r ≤ b) (ea : a = r + j * t) (eb : b = r + (j + 1) * t)
    {y : Matrix (Fin b) (Fin a) κ} {g gS : GL (Fin a) κ} {gT : GL (Fin b) κ} (h : IsTop t ha y g)
    (hS : gS ∈ blockTri (blkOf r t)) (hT : gT ∈ blockTri (blkOf r t)) (hST : upperLeftBlock ha gS = upperLeftBlock hb gT) :
    IsTop t ha ((gT⁻¹).val * y * gS.val) ((upperLeftBlock hab gT)⁻¹ * g * gS) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have t2 := mem_twoBlockTriangular_of_blockTriangular ea eb hT
  have tm := top_mem hab t2 hT
  have hinv : upperLeftBlock hab gT⁻¹ = (upperLeftBlock hab gT)⁻¹ := extendOne_inv _ t2
  refine ⟨lowZero_mul (Subgroup.inv_mem _ t2) h1 _, ?_, Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ tm) h3) hS, ?_⟩
  · rw [topL_mul hab (Subgroup.inv_mem _ t2) h1, hinv, ← h2, Units.val_mul, Units.val_mul]
  · have le := blockTri_blkOf_le (κ := κ) (n := a) r t
    have m1 : upperLeftBlock ha ((upperLeftBlock hab gT)⁻¹ * g * gS) = upperLeftBlock ha ((upperLeftBlock hab gT)⁻¹ * g) * upperLeftBlock ha gS :=
      extendMatrixByIdentityAlongIndices_mul _ (le (Subgroup.mul_mem _ (Subgroup.inv_mem _ tm) h3)) (le hS)
    have m2 : upperLeftBlock ha ((upperLeftBlock hab gT)⁻¹ * g) = upperLeftBlock ha (upperLeftBlock hab gT)⁻¹ * upperLeftBlock ha g :=
      extendMatrixByIdentityAlongIndices_mul _ (le (Subgroup.inv_mem _ tm)) (le h3)
    have m3 : upperLeftBlock ha (upperLeftBlock hab gT)⁻¹ = (upperLeftBlock ha (upperLeftBlock hab gT))⁻¹ := extendOne_inv _ (le tm)
    rw [m1, m2, m3, h4, restrictTopBlock_restrictTopBlock hab ha hb t2 hT, hST, mul_one, inv_mul_cancel]

theorem char_law (hab : a ≤ b) (ea : a = r + j * t) (eb : b = r + (j + 1) * t) {A : Type} [CommGroup A]
    (χ : ℕ → κˣ →* A) {g gS : GL (Fin a) κ} {gT : GL (Fin b) κ} (hg : g ∈ blockTri (blkOf r t))
    (hS : gS ∈ blockTri (blkOf r t)) (hT : gT ∈ blockTri (blkOf r t)) :
    (χ (j + 1) (Matrix.GeneralLinearGroup.det gS) * (χ (j + 1) (Matrix.GeneralLinearGroup.det gT))⁻¹) *
      ((∏ c ∈ Finset.range j, χ (c + 1) (dBlk (blkOf r t) (c + 1) ((upperLeftBlock hab gT)⁻¹ * g * gS))) *
        (χ (j + 1) (Matrix.GeneralLinearGroup.det ((upperLeftBlock hab gT)⁻¹ * g * gS)))⁻¹) =
    (∏ c ∈ Finset.range j, χ (c + 1) (dBlk (blkOf r t) (c + 1) gS)) *
      (∏ c ∈ Finset.range (j + 1), χ (c + 1) (dBlk (blkOf r t) (c + 1) gT))⁻¹ *
      ((∏ c ∈ Finset.range j, χ (c + 1) (dBlk (blkOf r t) (c + 1) g)) *
        (χ (j + 1) (Matrix.GeneralLinearGroup.det g))⁻¹) := by
  have tm := top_mem hab (mem_twoBlockTriangular_of_blockTriangular ea eb hT) hT
  have e1 : ∏ c ∈ Finset.range j, χ (c + 1) (dBlk (blkOf r t) (c + 1) ((upperLeftBlock hab gT)⁻¹ * g * gS)) =
      (∏ c ∈ Finset.range j, χ (c + 1) (dBlk (blkOf r t) (c + 1) gT))⁻¹ *
      (∏ c ∈ Finset.range j, χ (c + 1) (dBlk (blkOf r t) (c + 1) g)) *
      (∏ c ∈ Finset.range j, χ (c + 1) (dBlk (blkOf r t) (c + 1) gS)) := by
    rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun c hc => ?_
    have hi : dBlk (blkOf r t) (c + 1) (upperLeftBlock hab gT)⁻¹ = (dBlk (blkOf r t) (c + 1) (upperLeftBlock hab gT))⁻¹ :=
      extendOne_inv _ tm
    rw [diag_block_det_mul (Subgroup.mul_mem _ (Subgroup.inv_mem _ tm) hg) hS, diag_block_det_mul (Subgroup.inv_mem _ tm) hg, hi,
      diagonalBlock_restrictTopBlock hab ea eb hT (Finset.mem_range.1 hc), map_mul, map_mul, map_inv]
  rw [e1, Finset.prod_range_succ, det_top hab ea eb hT]
  simp only [map_mul, map_inv, mul_inv, inv_inv]
  generalize χ (j + 1) (Matrix.GeneralLinearGroup.det gS) = x1
  generalize χ (j + 1) (Matrix.GeneralLinearGroup.det (upperLeftBlock hab gT)) = x2
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

end Mat

section Dat

variable {D : D7} {a b r t j : ℕ} (ha : r ≤ a) (Pg Q : Finset (Pl D.host.E))
  (χ : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (ξ χj : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
  (y : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP))

theorem omegaG_of_isTop (g : ∀ PP : ↥Pg, GL (Fin a) (kP PP.1)) (hg : ∀ PP : ↥Pg, IsTop t ha (y PP.1) (g PP)) :
    omegaG (datY a r t j ha Pg Q (LevelP.triv Pg r ℂ) χ ξ Frm.B) χj y =
      ((∏ PP : ↥Pg, ((∏ c ∈ Finset.range j, χ (c + 1) PP.1 (dBlk (blkOf r t) (c + 1) (g PP))) *
        (χj PP.1 (Matrix.GeneralLinearGroup.det (g PP)))⁻¹) : ℂˣ) : ℂ) := by
  unfold omegaG
  split_ifs with h
  · have e : ∀ PP, h.2.choose PP = g PP := fun PP =>
      Units.ext ((h.2.choose_spec.1 PP).trans (hg PP).2.1.symm)
    have e2 : ∀ x, (datY a r t j ha Pg Q (LevelP.triv Pg r ℂ) χ ξ Frm.B).P.chi x = 1 := fun _ => rfl
    rw [e2]
    simp only [e, Units.val_one, one_mul, Finset.prod_mul_distrib, Units.val_mul, Units.coe_prod, Units.val_inv_eq_inv_val]
    rfl
  · exfalso
    refine h ⟨fun PP hP => (hg ⟨PP, hP⟩).1, g, fun PP => (hg PP).2.1, fun PP => (hg PP).2.2.1, ?_⟩
    exact Subgroup.mem_bot.2 (funext fun PP => (hg PP).2.2.2)

theorem omegaG_of_not (hg : ¬ ∃ g : ∀ PP : ↥Pg, GL (Fin a) (kP PP.1), ∀ PP : ↥Pg, IsTop t ha (y PP.1) (g PP)) :
    omegaG (datY a r t j ha Pg Q (LevelP.triv Pg r ℂ) χ ξ Frm.B) χj y = 0 := by
  unfold omegaG
  split_ifs with h
  · exfalso
    obtain ⟨h1, g, g1, g2, g3⟩ := h
    exact hg ⟨g, fun PP => ⟨h1 PP.1 PP.2, g1 PP, g2 PP, congrFun (Subgroup.mem_bot.1 g3) PP⟩⟩
  · rfl

end Dat

theorem omegaG_law : ∀ (D : D7) (a b r t j : ℕ) (ha : r ≤ a) (hb : r ≤ b), a = r + j * t → b = r + (j + 1) * t → ∀ (Pg Q : Finset (Pl D.host.E)) (χ : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (gS : ∀ PP : Pl D.host.E, GL (Fin a) (kP PP)) (gT : ∀ PP : Pl D.host.E, GL (Fin b) (kP PP)) (y y' : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP)), (∀ PP ∈ Pg, gS PP ∈ blockTri (blkOf r t)) → (∀ PP ∈ Pg, gT PP ∈ blockTri (blkOf r t)) → (∀ PP ∈ Pg, upperLeftBlock ha (gS PP) = upperLeftBlock hb (gT PP)) → (∀ PP ∈ Pg, y' PP = ((gT PP)⁻¹).val * y PP * (gS PP).val) → (∏ PP ∈ Pg, (((χ (j + 1) PP (Matrix.GeneralLinearGroup.det (gS PP)) : ℂˣ) : ℂ) * ((χ (j + 1) PP (Matrix.GeneralLinearGroup.det (gT PP)) : ℂˣ) : ℂ)⁻¹)) * omegaG (datY a r t j ha Pg Q (LevelP.triv Pg r ℂ) χ ξ Frm.B) (χ (j + 1)) y' = ((∏ PP ∈ Pg, ∏ c ∈ Finset.range j, χ (c + 1) PP (dBlk (blkOf r t) (c + 1) (gS PP)) : ℂˣ) : ℂ) * ((∏ PP ∈ Pg, ∏ c ∈ Finset.range (j + 1), χ (c + 1) PP (dBlk (blkOf r t) (c + 1) (gT PP)) : ℂˣ) : ℂ)⁻¹ * omegaG (datY a r t j ha Pg Q (LevelP.triv Pg r ℂ) χ ξ Frm.B) (χ (j + 1)) y := by
  intro D a b r t j ha hb ea eb Pg Q χ ξ gS gT y y' hS hT hST hy
  have hab : a ≤ b := by rw [ea, eb, add_mul]; omega
  by_cases h : ∃ g : ∀ PP : ↥Pg, GL (Fin a) (kP PP.1), ∀ PP : ↥Pg, IsTop t ha (y PP.1) (g PP)
  · obtain ⟨g, hg⟩ := h
    have hg' : ∀ PP : ↥Pg, IsTop t ha (y' PP.1) ((upperLeftBlock hab (gT PP.1))⁻¹ * g PP * gS PP.1) := fun PP => by
      rw [hy PP.1 PP.2]
      exact (hg PP).move hab ha hb ea eb (hS _ PP.2) (hT _ PP.2) (hST _ PP.2)
    rw [omegaG_of_isTop ha Pg Q χ ξ _ y g hg, omegaG_of_isTop ha Pg Q χ ξ _ y' _ hg']
    simp only [← Units.val_inv_eq_inv_val, ← Units.val_mul, ← Units.coe_prod]
    congr 1
    rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_coe_sort Pg, ← Finset.prod_coe_sort Pg,
      ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun PP _ =>
      char_law hab ea eb (fun c => χ c PP.1) (hg PP).2.2.1 (hS _ PP.2) (hT _ PP.2)
  · have h' : ¬ ∃ g : ∀ PP : ↥Pg, GL (Fin a) (kP PP.1), ∀ PP : ↥Pg, IsTop t ha (y' PP.1) (g PP) := by
      rintro ⟨g, hg⟩
      refine h ⟨fun PP => (upperLeftBlock hab (gT PP.1)⁻¹)⁻¹ * g PP * (gS PP.1)⁻¹, fun PP => ?_⟩
      have e : y PP.1 = ((gT PP.1)⁻¹⁻¹).val * y' PP.1 * ((gS PP.1)⁻¹).val := by
        rw [hy PP.1 PP.2, inv_inv, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc, ← Units.val_mul,
          mul_inv_cancel, Units.val_one, Matrix.mul_one, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel,
          Units.val_one, Matrix.one_mul]
      have i1 : upperLeftBlock ha (gS PP.1)⁻¹ = (upperLeftBlock ha (gS PP.1))⁻¹ := extendOne_inv _ (blockTri_blkOf_le r t (hS _ PP.2))
      have i2 : upperLeftBlock hb (gT PP.1)⁻¹ = (upperLeftBlock hb (gT PP.1))⁻¹ := extendOne_inv _ (blockTri_blkOf_le r t (hT _ PP.2))
      rw [e]
      exact (hg PP).move hab ha hb ea eb (Subgroup.inv_mem _ (hS _ PP.2)) (Subgroup.inv_mem _ (hT _ PP.2))
        (by rw [i1, i2, hST _ PP.2])
    rw [omegaG_of_not ha Pg Q χ ξ _ y h, omegaG_of_not ha Pg Q χ ξ _ y' h', mul_zero, mul_zero]

end GlobalTheory.StepLaw.TypeDatum

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TypePlacesLocalDatumBlockTriangularLawStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.StepLaw
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.typePlaces_localDatum_blockTriangular_law : ∀ (D : D7) (a b r t j : ℕ) (ha : r ≤ a) (hb : r ≤ b), a = r + j * t → b = r + (j + 1) * t → ∀ (Pg Q : Finset (Pl D.host.E)) (χ : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (gS : ∀ PP : Pl D.host.E, GL (Fin a) (kP PP)) (gT : ∀ PP : Pl D.host.E, GL (Fin b) (kP PP)) (y y' : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP)), (∀ PP ∈ Pg, gS PP ∈ blockTri (blkOf r t)) → (∀ PP ∈ Pg, gT PP ∈ blockTri (blkOf r t)) → (∀ PP ∈ Pg, upperLeftBlock ha (gS PP) = upperLeftBlock hb (gT PP)) → (∀ PP ∈ Pg, y' PP = ((gT PP)⁻¹).val * y PP * (gS PP).val) → (∏ PP ∈ Pg, (((χ (j + 1) PP (Matrix.GeneralLinearGroup.det (gS PP)) : ℂˣ) : ℂ) * ((χ (j + 1) PP (Matrix.GeneralLinearGroup.det (gT PP)) : ℂˣ) : ℂ)⁻¹)) * omegaG (datY a r t j ha Pg Q (LevelP.triv Pg r ℂ) χ ξ Frm.B) (χ (j + 1)) y' = ((∏ PP ∈ Pg, ∏ c ∈ Finset.range j, χ (c + 1) PP (dBlk (blkOf r t) (c + 1) (gS PP)) : ℂˣ) : ℂ) * ((∏ PP ∈ Pg, ∏ c ∈ Finset.range (j + 1), χ (c + 1) PP (dBlk (blkOf r t) (c + 1) (gT PP)) : ℂˣ) : ℂ)⁻¹ * omegaG (datY a r t j ha Pg Q (LevelP.triv Pg r ℂ) χ ξ Frm.B) (χ (j + 1)) y := by
  first | exact @GlobalTheory.StepLaw.TypeDatum.omegaG_law | exact GlobalTheory.StepLaw.TypeDatum.omegaG_law | (intros; apply GlobalTheory.StepLaw.TypeDatum.omegaG_law <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitarySatakeTransformStarParameterEqOfUnitarisa
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitarySatakeTransformStarParameterEqOfUnitarisa
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.PRep GlobalTheory.AdelicU GlobalTheory.LFun

noncomputable section

namespace GlobalTheory.LFun.ConjParam

section General

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {K : Subgroup G}

theorem conj_mem_hecke {h : G → ℂ} (hh : h ∈ Hecke ℂ K) : (fun g => starRingEnd ℂ (h g)) ∈ Hecke ℂ K := by
  obtain ⟨h1, S, hS⟩ := hh
  exact ⟨fun a b g => congrArg _ (h1 a b g), S, fun g hg => hS g fun h0 => hg (by simp [h0])⟩

theorem eigen_conj (hK : IsCommensurated K) (hinv : ∀ g : G, ∃ k₁ ∈ K, ∃ k₂ ∈ K, g⁻¹ = k₁ * g * k₂)
    {ρ : Representation ℂ G V} (hρ : GlobalTheory.LGrp.IsUnitarisable ρ) {x : V} (h0 : x ≠ 0) (hx : x ∈ fixed ρ K)
    {h : G → ℂ} (hh : h ∈ Hecke ℂ K) {a b : ℂ} (ha : heckeVec ρ K h x = a • x)
    (hb : heckeVec ρ K (fun g => starRingEnd ℂ (h g)) x = b • x) : starRingEnd ℂ b = a := by
  obtain ⟨B, hB, hpos, hinvB⟩ := hρ
  have hfix := GlobalTheory.LGrp.mem_fixed.1 hx
  have hreal : ∀ g, starRingEnd ℂ (B (ρ g x) x) = B (ρ g x) x := fun g => by
    obtain ⟨k₁, hk₁, k₂, hk₂, e⟩ := hinv g
    have e1 : B x (ρ g x) = B (ρ g⁻¹ x) x := by
      rw [← hinvB g (ρ g⁻¹ x) x, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    have e2 : B (ρ k₁ (ρ g x)) x = B (ρ g x) x := by
      rw [← hinvB k₁ (ρ g x) x, hfix k₁ hk₁]
    rw [← hB, e1, e, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hfix k₂ hk₂, e2]
  have key : ∀ f ∈ Hecke ℂ K, B (heckeVec ρ K f x) x = ∑ᶠ c : G ⧸ K, f c.out * B (ρ c.out x) x := fun f hf => by
    refine ((B.flip x).toAddMonoidHom.map_finsum (finite_heckeVec hK hf ρ x)).trans (finsum_congr fun c => ?_)
    simp
  have hxx : starRingEnd ℂ (B x x) = B x x := (hB x x).symm
  have hne : B x x ≠ 0 := fun e => by simpa [e] using hpos x h0
  have e1 := key h hh
  have e2 := congrArg (starRingEnd ℂ) (key _ (conj_mem_hecke hh))
  rw [ha] at e1
  rw [hb, show ⇑(starRingEnd ℂ) = (starAddEquiv : ℂ ≃+ ℂ) from rfl, AddEquiv.map_finsum] at e2
  apply mul_right_cancel₀ hne
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at e1 e2
  rw [e1]
  refine Eq.trans ?_ (e2.trans (finsum_congr fun c => ?_))
  · change _ = starRingEnd ℂ _
    rw [map_mul, hxx]
  · change starRingEnd ℂ _ = _
    rw [map_mul, hreal]
    exact congrArg (· * _) (Complex.conj_conj _)

end General

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {n : ℕ}

theorem conj_satU {m : ℕ} (ϖ : L) (q : ℕ) (h : GU σ n → ℂ) (α : Fin m → ℂ) :
    starRingEnd ℂ (SatU ϖ q (fun g => starRingEnd ℂ (h g)) α) = SatU ϖ q h fun i => starRingEnd ℂ (α i) := by
  have hs : ∀ {ι : Type} (f : ι → ℂ), starRingEnd ℂ (∑ᶠ i, f i) = ∑ᶠ i, starRingEnd ℂ (f i) := fun f =>
    AddEquiv.map_finsum (starAddEquiv : ℂ ≃+ ℂ) f
  unfold SatU
  rw [hs]
  refine finsum_congr fun a => ?_
  rw [map_mul, hs, map_prod]
  congr 1
  · simp
  · refine finsum_congr fun c => ?_
    split_ifs <;> simp

theorem inv_mem {ϖ : L} {q : ℕ} (hU : IsUnramInv ϖ σ q) (g : GU σ n) :
    ∃ k₁ ∈ KU σ n, ∃ k₂ ∈ KU σ n, g⁻¹ = k₁ * g * k₂ := by
  have hint : ∀ i j, antiJ L n i j ∈ intL L := by
    intro i j; unfold antiJ; split_ifs
    · exact one_mem _
    · exact zero_mem _
  obtain ⟨J, hJ, hJe⟩ := P.cartan_exists_glint (intL L) _ _
    (GlobalTheory.UnitarySwap.antiJ_mul_self (L := L) (n := n)) hint hint
  obtain ⟨k₁, hk₁, k₂, hk₂, e⟩ := GlobalTheory.UnitarySwap.inv_mem_doubleCoset hU hJ (g := (g : GL (Fin n) L)) (by
    intro i j
    rw [hJe]
    simp only [antiJ, add_comm i.val j.val]
    split_ifs <;> simp) (by rw [hJe]; exact g.2)
  rw [hJe] at hk₁ hk₂
  exact ⟨⟨k₁, hk₁.1⟩, hk₁, ⟨k₂, hk₂.1⟩, hk₂, Subtype.ext e⟩

theorem satU_star_eq : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q n : ℕ), IsUnramInv ϖ σ q → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GU σ n) V) (x : V) (α : Fin (n / 2) → ℂˣ), GlobalTheory.LGrp.IsUnitarisable ρ → IsSatVecU ϖ q ρ x α → ∀ h ∈ Hecke ℂ (KU σ n), SatU ϖ q h (fun i => ((star (α i) : ℂˣ) : ℂ)) = SatU ϖ q h (fun i => (α i : ℂ)) := by
  intro L _ _ _ ϖ σ q n hU V _ _ ρ x α hρ hx h hh
  exact (conj_satU ϖ q h fun i => (α i : ℂ)).symm.trans
    (eigen_conj (P.isCommensurated_integral_unitary_of_unramified hU n) (inv_mem hU) hρ hx.1 hx.2.1 hh (hx.2.2 h hh) (hx.2.2 _ (conj_mem_hecke hh)))

end GlobalTheory.LFun.ConjParam

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitarySatakeTransformStarParameterEqOfUnitarisaStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.PRep GlobalTheory.AdelicU GlobalTheory.LFun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitarySatakeTransform_star_parameter_eq_of_unitarisable : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q n : ℕ), IsUnramInv ϖ σ q → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GU σ n) V) (x : V) (α : Fin (n / 2) → ℂˣ), GlobalTheory.LGrp.IsUnitarisable ρ → IsSatVecU ϖ q ρ x α → ∀ h ∈ Hecke ℂ (KU σ n), SatU ϖ q h (fun i => ((star (α i) : ℂˣ) : ℂ)) = SatU ϖ q h (fun i => (α i : ℂ)) := by
  first | exact @GlobalTheory.LFun.ConjParam.satU_star_eq | exact GlobalTheory.LFun.ConjParam.satU_star_eq | (intros; apply GlobalTheory.LFun.ConjParam.satU_star_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RationalZeroIffRationalSubspace
section -- merged from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PositiveRowsTuple
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S NumberField IsDedekindDomain Polynomial
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx

namespace GlobalTheory.IndefiniteRowSideFullHecke.PositiveDimensionTuples

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A)

def dimQ (b : Bool) : ℕ := (lv (F.fc (R.toCx F).zs) b).dQ A.μ0

theorem dimQ_eq (b : Bool) :
    dimQ R F b = Module.finrank D.what₂.LL ((A.fam.R A.μ0).inV0 (F.lvl b) ((R.toCx F).Z A.μ0)) := by
  cases b <;> rfl

theorem pos_iff (b : Bool) : (lv (F.fc (R.toCx F).zs) b).Pos ↔ 0 < dimQ R F b := Iff.rfl

theorem pos_iff_ne_bot (b : Bool) :
    (lv (F.fc (R.toCx F).zs) b).Pos ↔ (A.fam.R A.μ0).inV0 (F.lvl b) ((R.toCx F).Z A.μ0) ≠ ⊥ := by
  rw [pos_iff, dimQ_eq, pos_iff_ne_zero, Ne, Submodule.finrank_eq_zero]

end

end GlobalTheory.IndefiniteRowSideFullHecke.PositiveDimensionTuples

end
end

noncomputable section

open Module

namespace GlobalTheory.QPosCompare

section Rat

variable {K X E : Type} [Field K] [AddCommGroup X] [Module K X] [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  {σ : K →+* ℂ} (j : X →ₛₗ[σ] E)

structure IsForm : Prop where
  basis : ∃ (n : ℕ) (b : Basis (Fin n) K X), LinearIndependent ℂ (fun i => j (b i)) ∧ Submodule.span ℂ (Set.range j) = ⊤
  inner : ∀ x y, ∃ a : K, inner ℂ (j x) (j y) = σ a

variable {j}

theorem IsForm.linInd (h : IsForm j) {ι : Type} [Fintype ι] {v : ι → X} (hv : LinearIndependent K v) :
    LinearIndependent ℂ fun i => j (v i) := by
  obtain ⟨n, b, hb, -⟩ := h.basis
  let _ := σ.toAlgebra
  have h1 : LinearIndependent K fun i => b.equivFun (v i) :=
    hv.map' (b.equivFun : X →ₗ[K] (Fin n → K)) b.equivFun.ker
  have h2 := (linearIndependent_algebraMap_comp_iff (S := ℂ)).2 h1
  have h3 := h2.map' (Fintype.linearCombination ℂ fun i => j (b i))
    (LinearMap.ker_eq_bot'.2 fun c hc => funext (Fintype.linearIndependent_iff.1 hb c
      (by simpa [Fintype.linearCombination_apply] using hc)))
  suffices he : (fun i => j (v i)) = (Fintype.linearCombination ℂ fun i => j (b i)) ∘
      fun i => (algebraMap K ℂ) ∘ b.equivFun (v i) by rw [he]; exact h3
  funext i
  simp only [Function.comp, Fintype.linearCombination_apply]
  conv_lhs => rw [← b.sum_equivFun (v i)]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smulₛₗ]; rfl

end Rat

section Twist

open Formalism.IndefR.Links

variable {E E' : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedAddCommGroup E'] [InnerProductSpace ℂ E'] (s : Bool)

theorem tw_map_sub (V : Submodule ℂ E) : V.map (Tw.mkL s E) = Tw.sub s V := by
  ext x
  exact ⟨fun ⟨y, hy, h⟩ => h ▸ hy, fun hx => ⟨Tw.out x, hx, rfl⟩⟩

theorem tw_span (S : Set E) : Submodule.span ℂ (Tw.mk s '' S) = Tw.sub s (Submodule.span ℂ S) := by
  rw [← tw_map_sub, Submodule.map_span]; rfl

variable [FiniteDimensional ℂ E] [FiniteDimensional ℂ E'] {K X : Type} [Field K] [AddCommGroup X] [Module K X] {σ σ' : K →+* ℂ}
  (h : ∀ a, σ' a = cj s (σ a)) (j : X →ₛₗ[σ] E) (f : E →ₗ[ℂ] E')

end Twist

theorem isForm_of_pres {G Γ W K : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W] [Field K] [NumberField K]
    [StarRing K] {ι : Γ →* G} {S : Formalism.L2.DIV.CSD K} {σ : K →+* ℂ} {ρ : Γ →* Module.End ℂ W} {J : Subgroup G} {χ : J →* ℂˣ}
    (P : Formalism.IndefR.Bridge.ClassPres ι S σ ρ J χ) (M : Formalism.IndefR.Links.HMod (G → W))
    (hM : M.Is (Formalism.IndefR.Bridge.AdForms ι ρ J χ) (Formalism.IndefR.Bridge.adInner ι J P.y))
    (j : S.Forms →ₛₗ[σ] M.H) (hj : ∀ x, M.e (j x) = P.extL x) : IsForm j := by
  obtain ⟨hinj, hr, hip⟩ := hM
  obtain ⟨-, ⟨hli, hsp⟩, hiso⟩ := GlobalTheory.classPres_extMem_extBij_isom _ _ _ _ _ _ _ _ _ _ P
  refine ⟨⟨_, S.basis, ?_, ?_⟩, fun x y => ⟨S.csum x y, ?_⟩⟩
  · refine LinearIndependent.of_comp M.e ?_
    have : (M.e ∘ fun i => j (S.basis i)) = fun i => P.extL (S.basis i) := funext fun i => hj _
    rw [this]; exact hli
  · apply Submodule.map_injective_of_injective hinj
    rw [Submodule.map_span, Submodule.map_top, hr, ← Set.range_comp]
    have : (M.e ∘ j) = P.extL := funext hj
    rw [this]; exact hsp
  · rw [hip, hj, hj]; exact hiso x y

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S NumberField IsDedekindDomain Polynomial
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open GlobalTheory.IndefiniteRowSideFullHecke.PositiveDimensionTuples

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Compare

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A)

theorem lPos_iff_ne_bot : R.LPos F ↔ ∀ b, (A.fam.R A.μ0).inV0 (F.lvl b) ((R.toCx F).Z A.μ0) ≠ ⊥ :=
  forall_congr' fun b => pos_iff_ne_bot R F b


variable {R} in
theorem isForm_jX (h : R.IsModels) (t : T) : IsForm (R.jX t) :=
  isForm_of_pres (R.B.R t).pres (R.HX t) (h.HX t) (R.jX t) (h.jX t)

end Compare

end GlobalTheory.QPosCompare

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeActsByScalarCommutative
noncomputable section

namespace GlobalTheory.LFun.HeckeScalar

open Formalism.UG GlobalTheory.PRep GlobalTheory.LFun GlobalTheory.LFun.SatCompare

variable {G V M : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup M] [Module ℂ M]
  {ρ : Representation ℂ G V} {K : Subgroup G} {x : V}

def finOrbit (τ : Representation ℂ G M) (K : Subgroup G) : Submodule ℂ M where
  carrier := {m | (Set.range fun k : K => τ k m).Finite}
  zero_mem' := (Set.finite_singleton 0).subset (by rintro _ ⟨k, rfl⟩; simp)
  add_mem' {a b} ha hb := (Set.Finite.add ha hb).subset (by
    rintro _ ⟨k, rfl⟩
    exact ⟨_, ⟨k, rfl⟩, _, ⟨k, rfl⟩, by simp⟩)
  smul_mem' c a ha := (Set.Finite.image (c • ·) ha).subset (by
    rintro _ ⟨k, rfl⟩
    exact ⟨_, ⟨k, rfl⟩, by simp⟩)

private theorem mem_fixed_iff_twisted_operators {W : Type} [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ G W)
    (L : Subgroup G) (v : W) : v ∈ fixed τ L ↔ ∀ k : L, τ k v = v := by
  change (∀ k : L, τ k v = ((1 : L →* ℂˣ) k : ℂ) • v) ↔ _
  simp

theorem exists_fixed_preimage {τ : Representation ℂ G M} (π : M →ₗ[ℂ] V) (hπ : ∀ g m, π (τ g m) = ρ g (π m))
    {m : M} (hm : m ∈ finOrbit τ K) (hy : π m ∈ fixed ρ K) : ∃ m' ∈ fixed τ K, π m' = π m := by
  classical

  have hfin : (Set.range fun k : K => τ k m).Finite := hm
  obtain ⟨O, hO⟩ : ∃ O : Finset M, ∀ o, o ∈ O ↔ ∃ k : K, τ k m = o :=
    ⟨hfin.toFinset, fun o => by rw [Set.Finite.mem_toFinset]; try exact Iff.rfl⟩
  have hmul : ∀ (a b : K) (o : M), τ (a : G) (τ (b : G) o) = τ ((a * b : K) : G) o := by
    intro a b o
    rw [Subgroup.coe_mul, map_mul, Module.End.mul_apply]
  have hperm : ∀ a : K, ∑ o ∈ O, τ (a : G) o = ∑ o ∈ O, o := by
    intro a
    refine Finset.sum_nbij' (fun o => τ (a : G) o) (fun o => τ ((a⁻¹ : K) : G) o) ?_ ?_ ?_ ?_ ?_
    · intro o ho
      obtain ⟨k, rfl⟩ := (hO o).1 ho
      exact (hO _).2 ⟨a * k, (hmul a k m).symm⟩
    · intro o ho
      obtain ⟨k, rfl⟩ := (hO o).1 ho
      exact (hO _).2 ⟨a⁻¹ * k, (hmul a⁻¹ k m).symm⟩
    · intro o _
      show τ ((a⁻¹ : K) : G) (τ (a : G) o) = o
      rw [hmul, inv_mul_cancel]
      simp
    · intro o _
      show τ (a : G) (τ ((a⁻¹ : K) : G) o) = o
      rw [hmul, mul_inv_cancel]
      simp
    · intro o _
      rfl
  have hne : (O.card : ℂ) ≠ 0 := by
    have hm' : m ∈ O := (hO m).2 ⟨1, by simp⟩
    exact Nat.cast_ne_zero.2 (Finset.card_ne_zero_of_mem hm')
  refine ⟨(O.card : ℂ)⁻¹ • ∑ o ∈ O, o, ?_, ?_⟩
  · rw [mem_fixed_iff_twisted_operators]
    intro a
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_smul, map_sum, hperm a]
  · have hconst : ∀ o ∈ O, π o = π m := by
      intro o ho
      obtain ⟨k, rfl⟩ := (hO o).1 ho
      rw [hπ]
      exact (mem_fixed_iff_twisted_operators ρ K (π m)).1 hy k
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_smul, map_sum, Finset.sum_congr rfl hconst, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℂ,
      smul_smul, inv_mul_cancel₀ hne, one_smul]

def permRep (K : Subgroup G) : Representation ℂ G (G ⧸ K →₀ ℂ) where
  toFun g := Finsupp.lmapDomain ℂ ℂ (g • ·)
  map_one' := by ext; simp
  map_mul' g h := by ext; simp [mul_smul]

theorem permRep_single (g : G) (c : G ⧸ K) (a : ℂ) :
    permRep K g (Finsupp.single c a) = Finsupp.single (g • c) a := by
  change Finsupp.mapDomain (g • ·) (Finsupp.single c a) = _
  exact Finsupp.mapDomain_single

private theorem permRep_apply_eq_mapDomain (g : G) (φ : G ⧸ K →₀ ℂ) :
    permRep K g φ = Finsupp.mapDomain (g • ·) φ :=
  rfl

theorem permRep_apply (g : G) (φ : G ⧸ K →₀ ℂ) (c : G ⧸ K) : permRep K g φ (g • c) = φ c := by
  rw [permRep_apply_eq_mapDomain]
  exact Finsupp.mapDomain_apply_of_injective (MulAction.injective g) φ c

theorem mem_finOrbit (hK : IsCommensurated K) (φ : G ⧸ K →₀ ℂ) : φ ∈ finOrbit (permRep K) K := by
  classical

  have hpi : (Set.pi Set.univ fun c : φ.support => MulAction.orbit K (c : G ⧸ K)).Finite := by
    refine Set.Finite.pi fun c => ?_
    obtain ⟨s, hs⟩ := QuotientGroup.mk_surjective (c : G ⧸ K)
    rw [← hs]
    exact Formalism.UG.P.orbit_coset_finite K hK s
  change (Set.range fun k : K => permRep K k φ).Finite
  refine (hpi.image fun t => ∑ c : φ.support, Finsupp.single (t c) (φ c)).subset ?_
  rintro _ ⟨k, rfl⟩
  refine ⟨fun c => k • (c : G ⧸ K), ?_, ?_⟩
  · rw [Set.mem_univ_pi]
    intro c
    exact MulAction.mem_orbit _ k
  · show (∑ c : φ.support, Finsupp.single (k • (c : G ⧸ K)) (φ c)) = permRep K (k : G) φ
    rw [permRep_apply_eq_mapDomain]
    exact Finset.sum_coe_sort φ.support fun a => Finsupp.single ((k : G) • a) (φ a)

def orbitMap (ρ : Representation ℂ G V) (K : Subgroup G) (x : V) : (G ⧸ K →₀ ℂ) →ₗ[ℂ] V :=
  Finsupp.linearCombination ℂ fun c => ρ c.out x

theorem orbitMap_single (hx : x ∈ fixed ρ K) (g : G) (a : ℂ) :
    orbitMap ρ K x (Finsupp.single (g : G ⧸ K) a) = a • ρ g x := by
  obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (s := K) g
  simp only [orbitMap, Finsupp.linearCombination_single]
  rw [hk, map_mul, Module.End.mul_apply, (mem_fixed_iff_twisted_operators ρ K x).1 hx k]

theorem orbitMap_permRep (hx : x ∈ fixed ρ K) (g : G) (φ : G ⧸ K →₀ ℂ) :
    orbitMap ρ K x (permRep K g φ) = ρ g (orbitMap ρ K x φ) := by
  induction φ using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add φ₁ φ₂ h₁ h₂ => simp only [map_add (f := _), h₁, h₂]
  | single c a =>
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective c
    rw [permRep_single, MulAction.Quotient.smul_mk, smul_eq_mul, orbitMap_single hx, orbitMap_single hx, map_smul,
      map_mul, Module.End.mul_apply]

theorem orbitMap_surjective (hρ : ρ.IsIrreducible) (hx : x ∈ fixed ρ K) (h0 : x ≠ 0) :
    Function.Surjective (orbitMap ρ K x) := by

  let S : Subrepresentation ρ := ⟨LinearMap.range (orbitMap ρ K x), by
    intro g v hv
    obtain ⟨φ, rfl⟩ := LinearMap.mem_range.1 hv
    exact LinearMap.mem_range.2 ⟨permRep K g φ, orbitMap_permRep hx g φ⟩⟩
  have hxS : x ∈ S.toSubmodule := by
    show x ∈ LinearMap.range (orbitMap ρ K x)
    refine LinearMap.mem_range.2 ⟨Finsupp.single ((1 : G) : G ⧸ K) 1, ?_⟩
    rw [orbitMap_single hx, one_smul, map_one, Module.End.one_apply]
  haveI : IsSimpleOrder (Subrepresentation ρ) := hρ
  rcases eq_bot_or_eq_top S with h | h
  · rw [h] at hxS
    exact absurd ((Submodule.mem_bot ℂ).1 hxS) h0
  · intro y
    have hy : y ∈ S.toSubmodule := by
      rw [h]
      exact Submodule.mem_top
    exact LinearMap.mem_range.1 hy

end GlobalTheory.LFun.HeckeScalar

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IoYStOfIoPair
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Lev Formalism.IndefR.Cx GlobalTheory.Chain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Chain

theorem IoPair.of_index_eq {D : D7} (hP : IoPair D) (k : Fin D.R.m) (a b : ℕ) (ha : a = k) (hb : b = k + 1)
    (V W : HSp D) (M : DSModel V (parB (Ptw D) a)) (M' : DSModel W (parB (Ptw D) b))
    (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ) (hθ : IsInfFam θ) (hC : ChainPar D k)
    (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (f : WO V W → ℂ)
    (hW : IsStepWeil k ψ V W ω) (hV : IsVacVec ψ θ M M' f)
    (It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M) (hI : IsItW θ M M' ω (ptOf ψ θ M M' f) It)
    (J : Set (GA D V)) (χ : GA D V → ℂ) (hJ : ∀ κ ∈ J, κ ∈ GfC V ∧ ω (κ, 1) f = χ κ • f)
    (ν : MeasureTheory.Measure (GA D W)) (𝓕 : Set (GA D W)) (hν : ν.IsHaarMeasure)
    (h𝓕 : MeasureTheory.IsFundamentalDomain (GQ W) 𝓕 ν)
    (J' : Set (GA D W)) (χ' : GA D W → ℂ) (C : Submodule ℂ (SmT M' →ₗ[ℂ] (GA D W → ℂ)))
    (hle : C ≤ MultT θ M' J' χ') :
    Lift.IoExists ν 𝓕 (thetaKO ω) (ptOf ψ θ M M' f) It C (MultT θ M J χ) := by
  subst ha hb
  exact hP k V W M M' θ ψ hθ hC ω f hW hV It hI J χ hJ ν 𝓕 hν h𝓕 J' χ' C hle

theorem ioYSt_of_ioPair (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)
    (hP : IoPair D) (hC : ∀ k, ChainPar D k) (hθ : IsInfFam R.θ) (hS : StepsOK R) (hL : LawsOK R)
    (hν : R.models_νY) (hν' : R.models_νY') (hI : R.chain_ItY) : IoYSt R := by
  intro t k hk
  have hkm : k < D.R.m := Nat.lt_of_succ_lt hk
  have hIt := hI
  have hInner := hν
  have hLast := hν'
  unfold RealDat.chain_ItY at hIt
  unfold RealDat.models_νY at hInner
  unfold RealDat.models_νY' at hLast

  have hmeas : (R.νY t (k + 1)).IsHaarMeasure ∧
      MeasureTheory.IsFundamentalDomain (GQ (Yc D (k + 1))) (R.fdY t (k + 1)) (R.νY t (k + 1)) := by
    by_cases h2 : k + 1 + 1 < D.R.m
    · exact ⟨(hInner t (k + 1) h2).1.1, (hInner t (k + 1) h2).2⟩
    · have atLast : ∀ j, j = D.R.m - 1 → (R.νY t j).IsHaarMeasure ∧
          MeasureTheory.IsFundamentalDomain (GQ (Yc D j)) (R.fdY t j) (R.νY t j) := by
        rintro j rfl
        exact ⟨(hLast t).1.1, (hLast t).2⟩
      exact atLast (k + 1) (by omega)
  obtain ⟨hW, hV⟩ := hS.1 t ⟨k, hkm⟩ hk
  exact IoPair.of_index_eq hP ⟨k, hkm⟩ (min k D.R.m) (min (k + 1) D.R.m) (min_eq_left hkm.le)
    (min_eq_left hk.le) (Yc D k) (Yc D (k + 1)) (R.MY k) (R.MY (k + 1)) R.θ R.ψ hθ (hC _) (R.ωY t k)
    (R.vY t k) hW hV (R.ItY k) (hIt t k hk) _ _ (hL.1 t k hk) (R.νY t (k + 1)) (R.fdY t (k + 1))
    hmeas.1 hmeas.2 _ _ (R.CC t (k + 1)) le_rfl

end GlobalTheory.Chain
end
