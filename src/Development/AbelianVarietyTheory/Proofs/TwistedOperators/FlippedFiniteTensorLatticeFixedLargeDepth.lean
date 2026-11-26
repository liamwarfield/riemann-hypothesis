module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LastRowLatticesGoodPositionLargeDepth
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldingExpansionProductFunctionLocalInvariant

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MovY
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowKFix

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc)

def movY (j : ℕ) (hj : j + 1 + 1 < D.R.m) (k : GA D (G.V (.grid D.R.m (j + 1))))
    (y : ∀ i : Fin D.R.m, Mx D (G.V (.grid D.R.m (i + 1))).rank (G.V (.grid D.R.m i)).rank) :
    ∀ i : Fin D.R.m, Mx D (G.V (.grid D.R.m (i + 1))).rank (G.V (.grid D.R.m i)).rank :=
  Function.update (Function.update y ⟨j, by omega⟩
      (actO (G.V (.grid D.R.m j)) (G.V (.grid D.R.m (j + 1))) 1 k⁻¹ (y ⟨j, by omega⟩)))
    ⟨j + 1, by omega⟩ (actO (G.V (.grid D.R.m (j + 1))) (G.V (.grid D.R.m (j + 1 + 1))) k⁻¹ 1 (y ⟨j + 1, by omega⟩))

end GlobalTheory.RowKFix

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LastRowInnerVertexVacuaScaledLocalProduct
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LastRowInnerVertexVacuaScaledLocalProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.RowKFix.LocProd

open GlobalTheory.SplitFlip GlobalTheory.RowVacScalar

theorem mem_inner_col {m j : ℕ} (hj : j + 1 + 1 < m) : (m, j + 1) ∈ innerVertices (oppositePath m) := by
  obtain ⟨n, hn⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  have h : Edge.theta m j ∈ (oppositePath m).tail := by
    rw [oppositePath, hn, List.range_succ_eq_map, List.map_cons, List.cons_append, List.tail_cons, ← List.range_succ_eq_map]
    exact List.mem_append_right _ (List.mem_map.2 ⟨j, List.mem_reverse.2 (List.mem_range.2 (by omega)), rfl⟩)
  exact List.mem_map.2 ⟨_, h, rfl⟩

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

theorem detIdl_eq {w : Pl D.host.E} (hw : Formalism.L2.NTheta.IsIdemAt (idemAt w) w) (V : HSp D) {n : ℕ} (h : n = V.rank)
    (β : GL (Fin V.rank) (Lev.EAf D)) {g : GA D V} (hg : g ∈ GfC V) :
    detIdl (idemAt w) V g = GlobalTheory.LFun.locIdele D.host.F w (gdet (inBasis h β w (Lev.finE V g))) :=
  GlobalTheory.RowDetLocal.detIdl_eq_locIdele V g w ⟨_, hw⟩ _ (GlobalTheory.RowDetLocal.gdet_inBasis_val V h β w ⟨g, hg⟩)

variable {G : GridData L sc}

def trCoord (w : Pl D.host.E) {a b a' b' : ℕ} (ha : a' = a) (hb : b' = b) (β : GL (Fin a) (Lev.EAf D)) (γ : GL (Fin b) (Lev.EAf D))
    (y : Matrix (Fin a) (Fin b) (AE D)) : Matrix (Fin b') (Fin a') (Kw w) :=
  ((((loc w β)⁻¹).val * (y.map fun a => cpt w (toEAf D a)) * (loc w γ).val).submatrix (Fin.cast ha) (Fin.cast hb))ᵀ

theorem trCoord_left (w : Pl D.host.E) (V : HSp D) {b a' b' : ℕ} (ha : a' = V.rank) (hb : b' = b)
    (β : GL (Fin V.rank) (Lev.EAf D)) (γ : GL (Fin b) (Lev.EAf D)) (k : GA D V) (y : Matrix (Fin V.rank) (Fin b) (AE D)) :
    trCoord w ha hb β γ (HMul.hMul (Formalism.L2.Theta.mt V k⁻¹) y) =
      trCoord w ha hb β γ y * (Assignment.one.read (inBasis ha β w (Lev.finE V k))).val := by
  have e1 : ((HMul.hMul (Formalism.L2.Theta.mt V k⁻¹) y).map fun a => cpt w (toEAf D a)) =
      HMul.hMul (loc w (Lev.finE V k⁻¹)).val (y.map fun a => cpt w (toEAf D a)) :=
    Matrix.map_mul (f := (cpt w).comp (toEAf D))
  have e2 : (Assignment.one.read (inBasis ha β w (Lev.finE V k))).val = (inBasis ha β w (Lev.finE V k⁻¹)).valᵀ := by
    rw [map_inv (Lev.finE V), map_inv (inBasis ha β w)]; rfl
  rw [e2, trCoord, trCoord, e1, GlobalTheory.RowMoveAt.mul_sub_cast, GlobalTheory.RowMoveAt.inBasis_val, Matrix.transpose_mul]

theorem trCoord_right (w : Pl D.host.E) (V : HSp D) {a a' b' : ℕ} (ha : a' = a) (hb : b' = V.rank)
    (β : GL (Fin a) (Lev.EAf D)) (γ : GL (Fin V.rank) (Lev.EAf D)) (k : GA D V) (y : Matrix (Fin a) (Fin V.rank) (AE D)) :
    trCoord w ha hb β γ (HMul.hMul y (Formalism.L2.Theta.mt V k)) =
      ((Assignment.one.read (inBasis hb γ w (Lev.finE V k)))⁻¹).val * trCoord w ha hb β γ y := by
  have e1 : ((HMul.hMul y (Formalism.L2.Theta.mt V k)).map fun a => cpt w (toEAf D a)) =
      HMul.hMul (y.map fun a => cpt w (toEAf D a)) (loc w (Lev.finE V k)).val :=
    Matrix.map_mul (f := (cpt w).comp (toEAf D))
  have e2 : ((Assignment.one.read (inBasis hb γ w (Lev.finE V k)))⁻¹).val = (inBasis hb γ w (Lev.finE V k)).valᵀ := rfl
  rw [e2, trCoord, trCoord, e1, GlobalTheory.RowMoveAt.sub_mul_cast, GlobalTheory.RowMoveAt.inBasis_val, Matrix.transpose_mul]

theorem oppArgs_theta (B : Frames G) (t : T) (w : Pl D.host.E)
    (x : ∀ i : Fin D.R.m, Mx D (G.V (.grid i D.R.m)).rank (G.V (.grid (i + 1) D.R.m)).rank)
    (y : ∀ j : Fin D.R.m, Mx D (G.V (.grid D.R.m (j + 1))).rank (G.V (.grid D.R.m j)).rank) {l : ℕ} (hl : l < D.R.m) :
    oppArgs t B w x y (.theta D.R.m l) = trCoord w (rank_vertex G t w (X := (D.R.m, l + 1)) ⟨le_rfl, hl⟩)
      (rank_vertex G t w (X := (D.R.m, l)) ⟨le_rfl, hl.le⟩) (B.β D.R.m (l + 1)) (B.β D.R.m l) (y ⟨l, hl⟩) := by
  rw [oppArgs, dif_pos ⟨hl, rfl⟩]
  rfl

abbrev kapCol (B : Frames G) (t : T) (w : Pl D.host.E) {j : ℕ} (hj : j + 1 + 1 < D.R.m) (k : GA D (G.V (.grid D.R.m (j + 1)))) :
    GL (Fin ((locGrid G t w).rank (D.R.m, j + 1))) (Kw w) :=
  inBasis (rank_vertex G t w (X := (D.R.m, j + 1)) ⟨le_rfl, by omega⟩) (B.β D.R.m (j + 1)) w (Lev.finE (G.V (.grid D.R.m (j + 1))) k)

theorem movY_two {j : ℕ} (hj : j + 1 + 1 < D.R.m) (k : GA D (G.V (.grid D.R.m (j + 1))))
    (y : ∀ j : Fin D.R.m, Mx D (G.V (.grid D.R.m (j + 1))).rank (G.V (.grid D.R.m j)).rank) (h : j + 1 < D.R.m) :
    movY G j hj k y ⟨j + 1, h⟩ = HMul.hMul (y ⟨j + 1, h⟩ : Matrix (Fin (G.V (.grid D.R.m (j + 1 + 1))).rank)
      (Fin (G.V (.grid D.R.m (j + 1))).rank) (AE D)) (Formalism.L2.Theta.mt (G.V (.grid D.R.m (j + 1))) k) := by
  rw [movY, Function.update_self, actO, inv_inv, GlobalTheory.LatStabScalar.mt_one, Matrix.one_mul]

theorem movY_one {j : ℕ} (hj : j + 1 + 1 < D.R.m) (k : GA D (G.V (.grid D.R.m (j + 1))))
    (y : ∀ j : Fin D.R.m, Mx D (G.V (.grid D.R.m (j + 1))).rank (G.V (.grid D.R.m j)).rank) (h : j < D.R.m) :
    movY G j hj k y ⟨j, h⟩ = HMul.hMul (Formalism.L2.Theta.mt (G.V (.grid D.R.m (j + 1))) k⁻¹)
      (y ⟨j, h⟩ : Matrix (Fin (G.V (.grid D.R.m (j + 1))).rank) (Fin (G.V (.grid D.R.m j)).rank) (AE D)) := by
  rw [movY, Function.update_of_ne (fun h => by simp [Fin.ext_iff] at h), Function.update_self, actO, inv_one,
    GlobalTheory.LatStabScalar.mt_one, Matrix.mul_one]

theorem movY_other {j : ℕ} (hj : j + 1 + 1 < D.R.m) (k : GA D (G.V (.grid D.R.m (j + 1))))
    (y : ∀ j : Fin D.R.m, Mx D (G.V (.grid D.R.m (j + 1))).rank (G.V (.grid D.R.m j)).rank) {l : ℕ} (h : l < D.R.m)
    (h1 : l ≠ j + 1) (h2 : l ≠ j) : movY G j hj k y ⟨l, h⟩ = y ⟨l, h⟩ := by
  rw [movY, Function.update_of_ne (fun h => h1 (by simpa [Fin.ext_iff] using h)),
    Function.update_of_ne (fun h => h2 (by simpa [Fin.ext_iff] using h))]


omit G in
theorem moveArgs_col {K : Type} [Field K] (Γ : Grid K) {m j : ℕ} (hj : j + 1 + 1 < m) (κ : GL (Fin (Γ.rank (m, j + 1))) K)
    (z z' : Γ.Args) (hex : ∀ i l, z' (.ex i l) = z (.ex i l)) (hex0 : ∀ i l, l ≠ m → z (.ex i l) = 0)
    (hth0 : ∀ i l, i ≠ m → z' (.theta i l) = 0 ∧ z (.theta i l) = 0)
    (hth : ∀ l, l ≠ j + 1 → l ≠ j → z' (.theta m l) = z (.theta m l))
    (h1 : z' (.theta m j) = z (.theta m j) * (Assignment.one.read κ).val)
    (h2 : z' (.theta m (j + 1)) = ((Assignment.one.read κ)⁻¹).val * z (.theta m (j + 1))) :
    z' = Γ.moveArgs .one (Pi.mulSingle (m, j + 1) κ) z := by
  have hone : ∀ X : ℕ × ℕ, X ≠ (m, j + 1) → (Pi.mulSingle (m, j + 1) κ : Γ.VertexGroup) X = 1 := fun X hX =>
    Pi.mulSingle_eq_of_ne hX _
  have hsame : (Pi.mulSingle (m, j + 1) κ : Γ.VertexGroup) (m, j + 1) = κ := Pi.mulSingle_eq_same _ _
  funext b
  cases b with
  | ex i l =>
    by_cases h : l = m
    · have e1 := hone (i, l) (by simp; omega)
      have e2 := hone (i + 1, l) (by simp; omega)
      simp only [Grid.moveArgs, Edge.src, Edge.tgt, e1, e2, map_one, inv_one, Units.val_one, Matrix.one_mul, Matrix.mul_one, hex]
    · simp only [Grid.moveArgs, hex, hex0 i l h, Matrix.mul_zero, Matrix.zero_mul]
  | theta i l =>
    by_cases h : i = m
    · subst h
      simp only [Grid.moveArgs, Edge.src, Edge.tgt]
      by_cases e1 : l = j + 1
      · subst e1
        rw [hsame, hone (i, j + 1 + 1) (by simp), map_one, Units.val_one, Matrix.mul_one, h2]
      by_cases e2 : l = j
      · subst e2
        rw [hsame, hone (i, l) (by simp), map_one, inv_one, Units.val_one, Matrix.one_mul, h1]
      · rw [hone (i, l) (by simp; omega), hone (i, l + 1) (by simp; omega), map_one, map_one, inv_one, Units.val_one,
          Units.val_one, Matrix.one_mul, Matrix.mul_one, hth l e1 e2]
    · simp only [Grid.moveArgs, (hth0 i l h).1, (hth0 i l h).2, Matrix.mul_zero, Matrix.zero_mul]

theorem oppArgs_movY (B : Frames G) (t : T) (w : Pl D.host.E) {j : ℕ} (hj : j + 1 + 1 < D.R.m)
    (k : GA D (G.V (.grid D.R.m (j + 1))))
    (x : ∀ i : Fin D.R.m, Mx D (G.V (.grid i D.R.m)).rank (G.V (.grid (i + 1) D.R.m)).rank)
    (y : ∀ j : Fin D.R.m, Mx D (G.V (.grid D.R.m (j + 1))).rank (G.V (.grid D.R.m j)).rank) :
    oppArgs t B w x (movY G j hj k y) =
      (locGrid G t w).moveArgs .one (Pi.mulSingle (D.R.m, j + 1) (kapCol B t w hj k)) (oppArgs t B w x y) := by
  refine moveArgs_col (locGrid G t w) hj _ _ _ (fun _ _ => rfl) (fun i l h => ?_) (fun i l h => ⟨?_, ?_⟩)
    (fun l h1 h2 => ?_) ?_ ?_
  · exact dif_neg fun h' => h h'.2
  · exact dif_neg fun h' => h h'.2
  · exact dif_neg fun h' => h h'.2
  · by_cases hl : l < D.R.m
    · rw [oppArgs_theta B t w x _ hl, oppArgs_theta B t w x _ hl, movY_other hj k y hl h1 h2]
    · have h0 : ¬ (l < D.R.m ∧ D.R.m = D.R.m) := fun h' => hl h'.1
      have e0 : ∀ y', oppArgs t B w x y' (.theta D.R.m l) = 0 := fun _ => dif_neg h0
      rw [e0, e0]
  · have hl : j < D.R.m := by omega
    rw [oppArgs_theta B t w x _ hl, oppArgs_theta B t w x _ hl, movY_one hj k y hl]
    exact trCoord_left w _ _ _ _ _ k _
  · have hl : j + 1 < D.R.m := by omega
    rw [oppArgs_theta B t w x _ hl, oppArgs_theta B t w x _ hl, movY_two hj k y hl]
    exact trCoord_right w _ _ _ _ _ k _

theorem kapCol_mem {μ₀ : T} (hL : L.Is μ₀) (B : Frames G) (t : T) (w : Pl D.host.E) {j : ℕ} (hj : j + 1 + 1 < D.R.m)
    {k : GA D (G.V (.grid D.R.m (j + 1)))} (hk : k ∈ latGrp G (j + 1)) : kapCol B t w hj k ∈ GlobalTheory.SplitWeil.KO (Kw w) _ := by
  have h2 := (mem_congLev.1 hk.2).2.1
  have hSt : Lev.finE (G.V (.grid D.R.m (j + 1))) k ∈ St (B.β D.R.m (j + 1)) :=
    (GlobalTheory.LevSplit.mem_St_iff _ _ (B.isFrame_β hL le_rfl (by omega)) _).2
      ⟨fun y hy => (h2 y).1 hy, fun y hy => (inv_mem h2 y).1 hy⟩
  have key : ∀ {n n' : ℕ} (h : n' = n) (β x : GL (Fin n) (Lev.EAf D)), x ∈ St β →
      inBasis h β w x ∈ GlobalTheory.SplitWeil.KO (Kw w) (Fin n') := by
    rintro n _ rfl β x hx
    exact GlobalTheory.FunObj.inBasis_mem_KO β x hx w
  exact key _ _ _ hSt

theorem mu_locIdele {μ₀ : T} (hL : L.Is μ₀) (t : T) (w : Pl D.host.E) {i : ℕ} (hi : i < D.R.m) (y : (Kw w)ˣ) :
    ((L.mu t (i + 1) (GlobalTheory.LFun.locIdele D.host.F w y) : Circle) : ℂ) = (((locGrid G t w).mu (i + 1) y : ℂˣ) : ℂ) := by
  have hE : ChrEq (L.mu t (i + 1)) (muBase L (i + 1) * L.xiH t) := by
    have h1 : muBase L (i + 1) = L.C.mu0 ⟨i, hi⟩ := dif_pos hi
    rw [h1]
    have := GlobalTheory.Mem.TupChar.chrEq_mul (hL.mu0 ⟨i, hi⟩) (hL.xi t)
    exact this
  exact congrArg (fun f => ((f y : ℂˣ) : ℂ)) (GlobalTheory.LFun.locChar_eq_of_chrEq hE w)

theorem splitScal_col {μ₀ : T} (hL : L.Is μ₀) (B : Frames G) (t : T) {w : Pl D.host.E} (hw : w ∈ locPl G t) {j : ℕ}
    (hj : j + 1 + 1 < D.R.m) {k : GA D (G.V (.grid D.R.m (j + 1)))} (hk : k ∈ GfC (G.V (.grid D.R.m (j + 1)))) :
    splitScal G (.mu t D.R.m j) w 1 k * splitScal G (.mu t D.R.m (j + 1)) w k 1 =
      (((locGrid G t w).mu (j + 1) (gdet (kapCol B t w hj k)) : ℂˣ) : ℂ) *
        ((((locGrid G t w).mu (j + 1 + 1) (gdet (kapCol B t w hj k)))⁻¹ : ℂˣ) : ℂ) := by
  have hs := isIdemAt_idemAt hL G t hw
  have d1 : ∀ V : HSp D, detIdl (idemAt w) V 1 = 1 := fun V => by
    unfold detIdl; split_ifs <;> simp
  have hpar : Odd (G.V (.grid D.R.m j)).rank ↔ Odd (G.V (.grid D.R.m (j + 1 + 1))).rank := by
    have r0 := (rank_vertex G t w (X := (D.R.m, j)) ⟨le_rfl, by omega⟩).symm
    have r2 := (rank_vertex G t w (X := (D.R.m, j + 1 + 1)) ⟨le_rfl, by omega⟩).symm
    rw [r0, r2]
    simp only [Grid.rank, locGrid]
    rw [show D.R.r + (j + 1 + 1) * D.R.t + D.R.m * sLen D = (D.R.r + j * D.R.t + D.R.m * sLen D) + 2 * D.R.t by ring,
      Nat.odd_add (n := 2 * D.R.t)]
    exact ⟨fun h => ⟨fun _ => even_two_mul _, fun _ => h⟩, fun h => h.2 (even_two_mul _)⟩
  have key : ∀ (a b η : (AE D)ˣ →* Circle) (n n' : ℕ), (Odd n ↔ Odd n') → ∀ x,
      Formalism.IndefR.Lift.attChr a η n x * (Formalism.IndefR.Lift.attChr b η n' x)⁻¹ = a x * (b x)⁻¹ := by
    intro a b η n n' h x
    unfold Formalism.IndefR.Lift.attChr
    by_cases hn : Odd n
    · rw [if_pos hn, if_pos (h.1 hn), MonoidHom.mul_apply, MonoidHom.mul_apply, MonoidHom.inv_apply, mul_inv, inv_inv,
        mul_mul_mul_comm, inv_mul_cancel, mul_one]
    · rw [if_neg hn, if_neg (fun h' => hn (h.2 h'))]
  have hd : detIdl (idemAt w) (G.V (.grid D.R.m (j + 1))) k =
      GlobalTheory.LFun.locIdele D.host.F w (gdet (kapCol B t w hj k)) := detIdl_eq hs _ _ _ hk
  simp only [splitScal, splitFacO, map_one, d1, inv_one, one_mul, mul_one]
  rw [hd, ← Circle.coe_mul, GridData.chrT, GridData.chrS, key _ _ _ _ _ hpar, Circle.coe_mul, Circle.coe_inv]
  dsimp only [GridData.chr]
  rw [mu_locIdele (G := G) hL t w (by omega), mu_locIdele (G := G) hL t w (by omega), Units.val_inv_eq_inv_val]

theorem om_vac {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (t : T) {i : ℕ} (hi : i < D.R.m)
    (hunr : ∀ v, (∀ w ∈ locPl G t, w.under (𝓞 D.host.F) ≠ v) →
      GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D (G.chrS (.mu t D.R.m i)) v ∧ GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D (G.chrT (.mu t D.R.m i)) v)
    {g : GA D (G.V (.grid D.R.m i))} (hg : g ∈ latGrp G i) {h : GA D (G.V (.grid D.R.m (i + 1)))} (hh : h ∈ latGrp G (i + 1))
    {f : WO (G.V (.grid D.R.m i)) (G.V (.grid D.R.m (i + 1))) → ℂ} (hf : W.IsVac (.mu t D.R.m i) f) :
    W.om (.mu t D.R.m i) (g, h) f = (∏ w ∈ locPl G t, splitScal G (.mu t D.R.m i) w g h) • f := by
  have hm := D.R.two_le_m
  have hp : (Pair.mu t D.R.m i : Pair T).InRange D.R.m := by
    simp only [Pair.InRange, Pair.big, Node.InRange]; omega
  have sd : ∀ l, l ≤ D.R.m → IsSelfDualC (G.V (.grid D.R.m l)) (G.Λ (.grid D.R.m l)) := fun l hl =>
    (G.isV (X := .grid D.R.m l) ⟨le_rfl, hl⟩ (fun j e => by simp at e; omega)).sd
  exact GlobalTheory.LatStabScalar.om_eq_prod_splitFac (W.om_is _ hp) (sd i hi.le) (sd (i + 1) hi) (locPl G t)
    (fun w hw => isIdemAt_idemAt hL G t hw) (Good.under_injOn hL G t) hunr g hg.1 h hh.1
    (GlobalTheory.RowMovedLat.latHat_stab_of_hatL _ g _ (mem_congLev.1 hg.2).2.1)
    (GlobalTheory.RowMovedLat.latHat_stab_of_hatL _ h _ (mem_congLev.1 hh.2).2.1) f hf.2.theta hf.2.lat

end GlobalTheory.RowKFix.LocProd

namespace GlobalTheory.RowKFix

open GlobalTheory.SplitFlip GlobalTheory.RowVacScalar LocProd

theorem local_prod_col : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (large₂ : SizeData₂ D) (F : Face D A), HidaSetting large₂ R F → ch.Is → ShapeAt ch → ∀ (t : T) (Φ : ch.G.Datum) (j : ℕ) (hj : j + 1 + 1 < D.R.m), ∀ k ∈ latGrp ch.G (j + 1), ∃ c₁ c₂ : ℂ, ch.W.om (.mu t D.R.m j) (1, k) (ch.rm.vT D.R.m j) = c₁ • ch.rm.vT D.R.m j ∧ ch.W.om (.mu t D.R.m (j + 1)) (k, 1) (ch.rm.vT D.R.m (j + 1)) = c₂ • ch.rm.vT D.R.m (j + 1) ∧ ∀ x y, c₁ * c₂ * ∏ w ∈ locPl ch.G t, Tflip ch.W ch.S.B t Φ w (oppArgs t ch.S.B w x (GlobalTheory.RowKFix.movY ch.G j hj k y)) = ∏ w ∈ locPl ch.G t, Tflip ch.W ch.S.B t Φ w (oppArgs t ch.S.B w x y) := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R ch large₂ F hS hch hsh t Φ j hj k hk
  have hL : R.toLevCh.Is A.μ0 := hS.core.lev
  have hm := D.R.two_le_m
  obtain ⟨N, N₀, LL, LZ, -, -, -, hsh⟩ := hsh
  obtain ⟨M, hM⟩ := exists_vol ch.G hL t
  have hunr := fun v => (hsh t M hM (D.R.m - 2) 0 (by omega) (GlobalTheory.Unf.Inhab.nonempty_volN _).some v).2.2.2.2.2
  refine ⟨_, _, om_vac hL ch.W t (by omega) (fun v hv => hunr v hv j (by omega)) (one_mem _) hk
      (ch.rm.vT_is t _ _ le_rfl (by omega)),
    om_vac hL ch.W t (by omega) (fun v hv => hunr v hv (j + 1) (by omega)) hk (one_mem _)
      (ch.rm.vT_is t _ _ le_rfl (by omega)), fun x y => ?_⟩
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun w hw => ?_
  have hK := kapCol_mem hL ch.S.B t w hj hk
  have hadm := GlobalTheory.TopLevelInv.isAdmissible_Tflip hL ch.W ch.S.B t Φ (GlobalTheory.FlipIntegrand.pde_ne_q_of_setting hS)
    (hch.guard t) hw _ (mem_inner_col hj) _ ((GlobalTheory.TopLevelInv.givenLevel_col t w j).symm ▸ hK)
  have e := congrFun hadm (oppArgs t ch.S.B w x y)
  have ef := GlobalTheory.TopLevelInv.prod_edgeFactor_col (Γ := locGrid ch.G t w) (j := j) (by show j + 1 < D.R.m; omega)
    (kapCol ch.S.B t w hj k) (valuation_gdet_of_mem_KO hK)
  rw [splitScal_col hL ch.S.B t hw hj hk.1, oppArgs_movY]
  exact (congrArg (· * _) ef.symm).trans e

end GlobalTheory.RowKFix

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LastRowInnerVertexVacuaScaledLocalProductStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lastRowInnerVertex_vacua_scaled_localProduct : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (large₂ : SizeData₂ D) (F : Face D A), HidaSetting large₂ R F → ch.Is → ShapeAt ch → ∀ (t : T) (Φ : ch.G.Datum) (j : ℕ) (hj : j + 1 + 1 < D.R.m), ∀ k ∈ latGrp ch.G (j + 1), ∃ c₁ c₂ : ℂ, ch.W.om (.mu t D.R.m j) (1, k) (ch.rm.vT D.R.m j) = c₁ • ch.rm.vT D.R.m j ∧ ch.W.om (.mu t D.R.m (j + 1)) (k, 1) (ch.rm.vT D.R.m (j + 1)) = c₂ • ch.rm.vT D.R.m (j + 1) ∧ ∀ x y, c₁ * c₂ * ∏ w ∈ locPl ch.G t, Tflip ch.W ch.S.B t Φ w (oppArgs t ch.S.B w x (GlobalTheory.RowKFix.movY ch.G j hj k y)) = ∏ w ∈ locPl ch.G t, Tflip ch.W ch.S.B t Φ w (oppArgs t ch.S.B w x y) := by
  first | exact @GlobalTheory.RowKFix.local_prod_col | exact GlobalTheory.RowKFix.local_prod_col | (intros; apply GlobalTheory.RowKFix.local_prod_col <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilRepPairFixesFlippedTensorSum
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilRepPairFixesFlippedTensorSum
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowKFix.Tens

def sumFun {ι κ : Type} {X : ι → Type} {Y : κ → Type} (A : ∀ i, (X i → ℂ) →ₗ[ℂ] ℂ) (B : ∀ k, (Y k → ℂ) →ₗ[ℂ] ℂ) :
    ∀ a : ι ⊕ κ, (Sum.elim X Y a → ℂ) →ₗ[ℂ] ℂ
  | .inl i => A i
  | .inr k => B k

theorem sum_prod_functional_eq {ι κ : Type} [Fintype ι] [Fintype κ] {X : ι → Type} {Y : κ → Type}
    (A : ∀ i, (X i → ℂ) →ₗ[ℂ] ℂ) (B : ∀ k, (Y k → ℂ) →ₗ[ℂ] ℂ) {α : Type} (τ : α →₀ ℂ)
    (f f' : α → ∀ i, X i → ℂ) (g g' : α → ∀ k, Y k → ℂ)
    (h : ∀ (x : ∀ i, X i) (y : ∀ k, Y k), (τ.sum fun d c => c * ((∏ i, f d i (x i)) * ∏ k, g d k (y k))) =
      τ.sum fun d c => c * ((∏ i, f' d i (x i)) * ∏ k, g' d k (y k))) :
    (τ.sum fun d c => c * ((∏ i, A i (f d i)) * ∏ k, B k (g d k))) =
      τ.sum fun d c => c * ((∏ i, A i (f' d i)) * ∏ k, B k (g' d k)) := by
  classical
  let Z : ι ⊕ κ → Type := Sum.elim X Y
  let C : ∀ a : ι ⊕ κ, (Z a → ℂ) →ₗ[ℂ] ℂ := sumFun A B
  let J : (α → ∀ i, X i → ℂ) → (α → ∀ k, Y k → ℂ) → α → ∀ a, Z a → ℂ := fun f g d a =>
    Sum.rec (motive := fun a => Z a → ℂ) (f d) (g d) a
  let M : (Π a, ↥(⊤ : Submodule ℂ (Z a → ℂ))) →ₘₗ[ℂ] ℂ :=
    (MultilinearMap.mkPiAlgebra ℂ (ι ⊕ κ) ℂ).compLinearMap fun a => C a ∘ₗ (⊤ : Submodule ℂ (Z a → ℂ)).subtype
  have key := GlobalTheory.finsupp_sum_multilinear_eq_of_prod_eq (X := Z) (fun _ => ⊤) M τ τ
    (fun d a => ⟨J f g d a, trivial⟩) (fun d a => ⟨J f' g' d a, trivial⟩) (fun z => by
      simp only [Fintype.prod_sum_type]
      exact h (fun i => z (.inl i)) (fun k => z (.inr k)))
  simp only [smul_eq_mul, M, MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply, Fintype.prod_sum_type] at key
  exact key

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem selfDual_last {i : ℕ} (hi : i ≤ D.R.m) : IsSelfDualC (G.V (.grid D.R.m i)) (G.Λ (.grid D.R.m i)) :=
  (G.isV (X := .grid D.R.m i) ⟨le_rfl, hi⟩ (fun k hk => by
    have := D.R.two_le_m
    simp only [Node.grid.injEq] at hk; omega)).sd

theorem keep_pair {i : ℕ} (hi : i < D.R.m) (a : GA D (G.V (.grid D.R.m i))) (b : GA D (G.V (.grid D.R.m (i + 1))))
    (ha : Lev.finE (G.V (.grid D.R.m i)) a ∈ G.levMax (.grid D.R.m i)) (hb : Lev.finE (G.V (.grid D.R.m (i + 1))) b ∈ G.levMax (.grid D.R.m (i + 1)))
    (u : WO (G.V (.grid D.R.m i)) (G.V (.grid D.R.m (i + 1)))) :
    u ∈ latO _ _ (G.Λ (.grid D.R.m i) : Set _) (G.Λ (.grid D.R.m (i + 1)) : Set _) (fun _ => True) ↔
      actO _ _ a b u ∈ latO _ _ (G.Λ (.grid D.R.m i) : Set _) (G.Λ (.grid D.R.m (i + 1)) : Set _) (fun _ => True) := by
  have sdS := selfDual_last (G := G) hi.le
  have sdT := selfDual_last (G := G) (i := i + 1) hi
  classical
  have hfull : ∀ (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)),
      IsSelfDualC V Λ → Submodule.IsFullLattice D.host.E Λ := by
    intro V Λ hΛ
    haveI : Submodule.IsLattice D.host.E Λ := hΛ.1
    refine ⟨?_⟩
    obtain ⟨s, hs⟩ := hΛ.1.fg
    apply eq_top_iff.mpr
    intro y _
    let f : (Fin V.rank → D.host.E) → D.host.E := fun x =>
      ∑ i, ∑ j, star (x i) * V.gram i j * y j
    obtain ⟨a, ha⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 D.host.E)) s f
    have ha0 : (algebraMap (𝓞 D.host.E) D.host.E a) ≠ 0 := by
      exact (FaithfulSMul.algebraMap_injective _ _).ne (mem_nonZeroDivisors_iff_ne_zero.mp a.2)
    let P : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E) := {
      carrier := {x | ∃ b : 𝓞 D.host.E, (b : D.host.E) = (algebraMap (𝓞 D.host.E) D.host.E a) * f x}
      zero_mem' := by refine ⟨0, ?_⟩; simp [f]
      add_mem' := by
        rintro x z ⟨b, hb⟩ ⟨c, hc⟩
        refine ⟨b + c, ?_⟩
        change (b : D.host.E) + c = _
        rw [hb, hc]
        simp [f, map_add, add_mul, Finset.sum_add_distrib, mul_add]
      smul_mem' := by
        rintro c x ⟨b, hb⟩
        refine ⟨RingOfIntegers.mapRingHom (starRingEnd D.host.E) c * b, ?_⟩
        simp only [map_mul, hb, f, Pi.smul_apply, Algebra.smul_def, map_mul, RingOfIntegers.mapRingHom_apply, star_mul]
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        change star (c : D.host.E) * _ = _
        ring }
    have hsP : (s : Set (Fin V.rank → D.host.E)) ⊆ P := by
      intro x hx
      obtain ⟨b, hb⟩ := ha x hx
      exact ⟨b, by simpa [Algebra.smul_def] using hb⟩
    have hy : (algebraMap (𝓞 D.host.E) D.host.E a) • y ∈ Λ := by
      apply (hΛ.2 _).2
      intro x hx
      have hxP : x ∈ P := (hs ▸ Submodule.span_le.mpr hsP) hx
      obtain ⟨b, hb⟩ := hxP
      refine ⟨b, ?_⟩
      rw [hb]
      dsimp only [f, Pi.smul_apply]
      simp only [smul_eq_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    have hy' : (algebraMap (𝓞 D.host.E) D.host.E a) • y ∈ Submodule.span D.host.E (Λ : Set (Fin V.rank → D.host.E)) :=
      Submodule.subset_span hy
    have := (Submodule.span D.host.E (Λ : Set (Fin V.rank → D.host.E))).smul_mem
      (algebraMap (𝓞 D.host.E) D.host.E a)⁻¹ hy' 
    change (algebraMap (𝓞 D.host.E) D.host.E a)⁻¹ •
      ((algebraMap (𝓞 D.host.E) D.host.E a) • y) ∈ _ at this
    rw [← smul_assoc, smul_eq_mul, inv_mul_cancel₀ ha0, one_smul] at this
    exact this
  obtain ⟨βT, hβT⟩ := GlobalTheory.AdelicFrame.exists_isFrame D.host.F _ sdT.1.fg (by
    letI := hfull _ _ sdT
    exact Submodule.IsFullLattice.span_eq_top)
  obtain ⟨βS, hβS⟩ := GlobalTheory.AdelicFrame.exists_isFrame D.host.F _ sdS.1.fg (by
    letI := hfull _ _ sdS
    exact Submodule.IsFullLattice.span_eq_top)
  have keep : ∀ {V : HSp D} (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)),
      Formalism.L2.DIV.IsFrame β Λ → ∀ X : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D),
      X ∈ congLev D.sp.cm V.gram Λ ⊤ → X ∈ Formalism.L2.DIV.St β := by
    intro V Λ β hβ X hX
    rw [congLev_top] at hX
    have hst := (Subgroup.mem_inf.1 hX).2
    have hst' := (Subgroup.mem_inf.1 (inv_mem hX)).2
    exact (GlobalTheory.LevSplit.mem_St_iff β Λ hβ X).2 ⟨fun v hv => (hst v).1 hv, fun v hv => (hst' v).1 hv⟩
  exact GlobalTheory.StabLatInv.mem_latO_iff_actO_mem D _ _ _ _ βS βT sdS sdT hβS hβT a b (keep _ βS hβS _ ha) (keep _ βT hβT _ hb) u

theorem vT_ne_zero {W : G.Weil} (ρ : RealMatch W) (t : T) {i : ℕ} (hi : i < D.R.m) : ρ.vT D.R.m i ≠ 0 := by
  intro h0
  obtain ⟨⟨p, hp⟩, hn⟩ := (ρ.vT_is t D.R.m i le_rfl hi).2.norm
  have := hn p hp
  simp [nrm2, h0] at this

theorem sum_om_eq {W : G.Weil} (ρ : RealMatch W) (t : T) {e : AE D} (hee : e * e = e) (hinf : infPart D e = 0)
    (τ : SchRow G × SchDown G t →₀ ℂ) (φ : SchRow G × SchDown G t → SchRow G × SchDown G t)
    (hloc : ∀ d ∈ τ.support, (∀ i : Fin D.R.m, IsLocVec W (.chi i D.R.m) e (ρ.vX i D.R.m) ((φ d).1 i) (d.1 i)) ∧
      ∀ j : Fin D.R.m, IsLocVec W (.mu t D.R.m j) e (ρ.vT D.R.m j) ((φ d).2 j) (d.2 j))
    (h : Pts G) (hh : ∀ i, Lev.finE (G.V (.grid D.R.m i)) (h i) ∈ G.levMax (.grid D.R.m i)) (c : Fin D.R.m → ℂ)
    (hc : ∀ i : Fin D.R.m, W.om (.mu t D.R.m i) (h i, h (i + 1)) (ρ.vT D.R.m i) = c i • ρ.vT D.R.m i)
    (hsum : ∀ (x : RowPt G) (y : ∀ i : Fin D.R.m, WO (G.V (.grid D.R.m i)) (G.V (.grid D.R.m (i + 1)))),
      (τ.sum fun d a => a * ((∏ n, (φ d).1 n (x n)) * ∏ i : Fin D.R.m, c i * (φ d).2 i (actO _ _ (h i)⁻¹ (h (i + 1))⁻¹ (y i)))) =
        τ.sum fun d a => a * ((∏ n, (φ d).1 n (x n)) * ∏ i, (φ d).2 i (y i)))
    (y : RowPt G) (v : ∀ i : Fin D.R.m, WO (G.V (.grid D.R.m i)) (G.V (.grid D.R.m (i + 1)))) :
    (τ.sum fun d x => x * ((∏ n, d.1 n (y n)) * ∏ i : Fin D.R.m, W.om (.mu t D.R.m i) (h i, h (i + 1)) (d.2 i) (v i))) =
      τ.sum fun d x => x * ((∏ n, d.1 n (y n)) * ∏ i, d.2 i (v i)) := by
  classical
  let P : ∀ (p : Pair T) (f₀ : WO (G.pS p) (G.pT p) → ℂ), ((WO (G.pS p) (G.pT p) → ℂ) →ₗ[ℂ] (WO (G.pS p) (G.pT p) → ℂ)) → Prop :=
    fun p f₀ => IsPlaceModel W.ψ (symplO _ _) (heisO W.ψ _ _) e
      (latO (G.pS p) (G.pT p) (G.latS p : Set _) (G.latT p : Set _) fun _ => True) 1 f₀
  have hP : ∀ (p : Pair T) (f₀ f₁ f : WO (G.pS p) (G.pT p) → ℂ), IsLocVec W p e f₀ f₁ f →
      P p f₀ (Classical.epsilon (P p f₀)) ∧ f = Classical.epsilon (P p f₀) f₁ := fun p f₀ f₁ f hf =>
    have hs := Classical.epsilon_spec hf.2.1
    ⟨hs, hf.2.2 _ hs⟩
  have key := sum_prod_functional_eq
    (X := fun n : Fin D.R.m => WO (G.pS (.chi n D.R.m : Pair T)) (G.pT (.chi n D.R.m : Pair T)))
    (Y := fun i : Fin D.R.m => WO (G.V (.grid D.R.m i)) (G.V (.grid D.R.m (i + 1))))
    (fun n => LinearMap.proj (y n) ∘ₗ Classical.epsilon (P (.chi n D.R.m) (ρ.vX n D.R.m)))
    (fun i => LinearMap.proj (v i) ∘ₗ Classical.epsilon (P (.mu t D.R.m i) (ρ.vT D.R.m i))) τ
    (fun d => (φ d).1) (fun d => (φ d).1)
    (fun d i => c i • fun u => (φ d).2 i (actO _ _ (h i)⁻¹ (h (i + 1))⁻¹ u)) (fun d => (φ d).2) hsum
  have hrow : ∀ d ∈ τ.support, ∀ n : Fin D.R.m, d.1 n (y n) =
      (LinearMap.proj (y n) ∘ₗ Classical.epsilon (P (.chi n D.R.m) (ρ.vX n D.R.m))) ((φ d).1 n) := fun d hd n =>
    congrFun (hP _ _ _ _ ((hloc d hd).1 n)).2 _
  refine Eq.trans (Finsupp.sum_congr fun d hd => ?_) (key.trans (Finsupp.sum_congr fun d hd => ?_))
  · refine congrArg _ (congrArg₂ _ (Finset.prod_congr rfl fun n _ => hrow d hd n) (Finset.prod_congr rfl fun i _ => ?_))
    have hl := (hloc d hd).2 i
    exact congrFun (GlobalTheory.RowVertexInv.FactorTheta.om_theta_eq (W.om_is (.mu t D.R.m i) ⟨le_rfl, i.2⟩) hee hinf
      (selfDual_last i.2.le) (selfDual_last (i := i + 1) i.2) (ρ.vT_is t D.R.m i le_rfl i.2).2.theta (h i, h (i + 1))
      (keep_pair i.2 _ _ (hh _) (hh _))
      (GlobalTheory.RowVertexInv.FactorTheta.scalar_ne_zero (p := .mu t D.R.m i) _ (vT_ne_zero ρ t i.2) (hc i)) (hc i)
      (hP _ _ _ _ hl).1 hl.2) (v i)
  · refine congrArg _ (congrArg₂ _ (Finset.prod_congr rfl fun n _ => (hrow d hd n).symm) (Finset.prod_congr rfl fun i _ => ?_))
    exact (congrFun (hP _ _ _ _ ((hloc d hd).2 i)).2 (v i)).symm

theorem actO_one_one (S T' : HSp D) (u : WO S T') : actO S T' 1 1 u = u := by
  unfold actO
  rw [inv_one]
  exact (Matrix.mul_one _).trans (Matrix.one_mul _)

theorem movY_eq (j : ℕ) (hj : j + 1 + 1 < D.R.m) (k : GA D (G.V (.grid D.R.m (j + 1))))
    (y : ∀ i : Fin D.R.m, WO (G.V (.grid D.R.m i)) (G.V (.grid D.R.m (i + 1)))) (i : Fin D.R.m) :
    GlobalTheory.RowKFix.movY G j hj k y i =
      actO _ _ ((Pi.mulSingle (j + 1) k : Pts G) i)⁻¹ ((Pi.mulSingle (j + 1) k : Pts G) (i + 1))⁻¹ (y i) := by
  let B : Fin D.R.m → Type := fun i => Mx D (G.V (.grid D.R.m (i + 1))).rank (G.V (.grid D.R.m i)).rank
  by_cases h2 : i = ⟨j + 1, by omega⟩
  · subst h2
    refine (Function.update_self (β := B) _ _ _).trans ?_
    have e1 : (Pi.mulSingle (j + 1) k : Pts G) (j + 1) = k := Pi.mulSingle_eq_same _ _
    have e2 : (Pi.mulSingle (j + 1) k : Pts G) (j + 1 + 1) = 1 := Pi.mulSingle_eq_of_ne (by omega) _
    change _ = actO _ _ ((Pi.mulSingle (j + 1) k : Pts G) (j + 1))⁻¹ ((Pi.mulSingle (j + 1) k : Pts G) (j + 1 + 1))⁻¹ _
    rw [e1, e2, inv_one]
  refine (Function.update_of_ne (β := B) h2 _ _).trans ?_
  by_cases h1 : i = ⟨j, by omega⟩
  · subst h1
    refine (Function.update_self (β := B) _ _ _).trans ?_
    have e1 : (Pi.mulSingle (j + 1) k : Pts G) (j + 1) = k := Pi.mulSingle_eq_same _ _
    have e2 : (Pi.mulSingle (j + 1) k : Pts G) j = 1 := Pi.mulSingle_eq_of_ne (by omega) _
    change _ = actO _ _ ((Pi.mulSingle (j + 1) k : Pts G) j)⁻¹ ((Pi.mulSingle (j + 1) k : Pts G) (j + 1))⁻¹ _
    rw [e1, e2, inv_one]
  refine (Function.update_of_ne (β := B) h1 _ _).trans ?_
  have e1 : (Pi.mulSingle (j + 1) k : Pts G) i = 1 := Pi.mulSingle_eq_of_ne (fun h => h2 (Fin.ext h)) _
  have e2 : (Pi.mulSingle (j + 1) k : Pts G) (i + 1) = 1 :=
    Pi.mulSingle_eq_of_ne (fun h => h1 (Fin.ext (Nat.succ_injective h))) _
  rw [e1, e2, inv_one, inv_one, actO_one_one]

theorem sum_om_single_eq : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (large₂ : SizeData₂ D) (F : Face D A), HidaSetting large₂ R F → ch.Is → ∀ (t : T) (Φ : ch.G.Datum) (τ : SchRow ch.G × SchDown ch.G t →₀ ℂ), IsFlipFin t ch.S.B ch.rm Φ τ → ∀ (j : ℕ) (hj : j + 1 + 1 < D.R.m), ∀ k ∈ latGrp ch.G (j + 1), ∀ c₁ c₂ : ℂ, ch.W.om (.mu t D.R.m j) (1, k) (ch.rm.vT D.R.m j) = c₁ • ch.rm.vT D.R.m j → ch.W.om (.mu t D.R.m (j + 1)) (k, 1) (ch.rm.vT D.R.m (j + 1)) = c₂ • ch.rm.vT D.R.m (j + 1) → (∀ x y, c₁ * c₂ * ∏ w ∈ locPl ch.G t, Tflip ch.W ch.S.B t Φ w (oppArgs t ch.S.B w x (GlobalTheory.RowKFix.movY ch.G j hj k y)) = ∏ w ∈ locPl ch.G t, Tflip ch.W ch.S.B t Φ w (oppArgs t ch.S.B w x y)) → ∀ (y : RowPt ch.G) (v : ∀ i : Fin D.R.m, WO (ch.G.V (.grid D.R.m i)) (ch.G.V (.grid D.R.m (i + 1)))), (τ.sum fun d x => x * ((∏ n, d.1 n (y n)) * ∏ i : Fin D.R.m, ch.W.om (.mu t D.R.m i) ((Pi.mulSingle (j + 1) k : Pts ch.G) i, (Pi.mulSingle (j + 1) k : Pts ch.G) (i + 1)) (d.2 i) (v i))) = τ.sum fun d x => x * ((∏ n, d.1 n (y n)) * ∏ i, d.2 i (v i)) := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R ch large₂ F _ _ t Φ τ hτ j hj k hk c₁ c₂ h₁ h₂ hT y v
  classical
  obtain ⟨e, he, φ, hloc, hid⟩ := hτ
  have hne : (⟨j, by omega⟩ : Fin D.R.m) ≠ ⟨j + 1, by omega⟩ := by simp
  let c : Fin D.R.m → ℂ := fun i => (Pi.mulSingle (⟨j, by omega⟩ : Fin D.R.m) c₁ : Fin D.R.m → ℂ) i *
    (Pi.mulSingle (⟨j + 1, by omega⟩ : Fin D.R.m) c₂ : Fin D.R.m → ℂ) i
  have hprod : ∏ i, c i = c₁ * c₂ := by
    simp only [c]
    rw [Finset.prod_mul_distrib, Fintype.prod_pi_mulSingle', Fintype.prod_pi_mulSingle']
  have e1 : (Pi.mulSingle (j + 1) k : Pts ch.G) (j + 1) = k := Pi.mulSingle_eq_same _ _
  refine sum_om_eq ch.rm t (GlobalTheory.PlaceDatum.idemSum_mul_self he) (GlobalTheory.PlaceDatum.infPart_idemSum he) τ φ hloc
    (Pi.mulSingle (j + 1) k) (fun i => ?_) c (fun i => ?_) (fun x z => ?_) y v
  · by_cases hi : i = j + 1
    · subst hi
      rw [e1]
      exact (Subgroup.mem_inf.1 hk).2
    · rw [Pi.mulSingle_eq_of_ne hi, MonoidHom.map_one]
      exact one_mem _
  · by_cases h2 : i = ⟨j + 1, by omega⟩
    · subst h2
      have e2 : (Pi.mulSingle (j + 1) k : Pts ch.G) (j + 1 + 1) = 1 := Pi.mulSingle_eq_of_ne (by omega) _
      have e3 : c ⟨j + 1, by omega⟩ = c₂ := by simp [c, Pi.mulSingle_apply]
      rw [e3]
      change ch.W.om (.mu t D.R.m (j + 1)) ((Pi.mulSingle (j + 1) k : Pts ch.G) (j + 1),
        (Pi.mulSingle (j + 1) k : Pts ch.G) (j + 1 + 1)) _ = _
      rw [e1, e2]
      exact h₂
    by_cases h1 : i = ⟨j, by omega⟩
    · subst h1
      have e2 : (Pi.mulSingle (j + 1) k : Pts ch.G) j = 1 := Pi.mulSingle_eq_of_ne (by omega) _
      have e3 : c ⟨j, by omega⟩ = c₁ := by simp [c, Pi.mulSingle_apply]
      rw [e3]
      change ch.W.om (.mu t D.R.m j) ((Pi.mulSingle (j + 1) k : Pts ch.G) j,
        (Pi.mulSingle (j + 1) k : Pts ch.G) (j + 1)) _ = _
      rw [e1, e2]
      exact h₁
    have e2 : (Pi.mulSingle (j + 1) k : Pts ch.G) i = 1 := Pi.mulSingle_eq_of_ne (fun h => h2 (Fin.ext h)) _
    have e3 : (Pi.mulSingle (j + 1) k : Pts ch.G) (i + 1) = 1 :=
      Pi.mulSingle_eq_of_ne (fun h => h1 (Fin.ext (Nat.succ_injective h))) _
    have e4 : c i = 1 := by simp [c, Pi.mulSingle_apply, h1, h2]
    have e5 : ch.W.om (.mu t D.R.m i) (1, 1) = 1 := map_one _
    rw [e2, e3, e4, e5, one_smul]
    rfl
  · have hL : (τ.sum fun d a => a * ((∏ n, (φ d).1 n (x n)) * ∏ i : Fin D.R.m, c i * (φ d).2 i
        (actO _ _ ((Pi.mulSingle (j + 1) k : Pts ch.G) i)⁻¹ ((Pi.mulSingle (j + 1) k : Pts ch.G) (i + 1))⁻¹ (z i)))) =
        c₁ * c₂ * τ.sum fun d a => a * (∏ n, (φ d).1 n (x n)) * ∏ i, (φ d).2 i (GlobalTheory.RowKFix.movY ch.G j hj k z i) := by
      rw [Finsupp.mul_sum]
      refine Finsupp.sum_congr fun d _ => ?_
      rw [Finset.prod_mul_distrib, hprod, Finset.prod_congr rfl fun i _ => congrArg ((φ d).2 i) (movY_eq j hj k z i)]
      ring
    have hR : (τ.sum fun d a => a * ((∏ n, (φ d).1 n (x n)) * ∏ i, (φ d).2 i (z i))) =
        τ.sum fun d a => a * (∏ n, (φ d).1 n (x n)) * ∏ i, (φ d).2 i (z i) :=
      Finsupp.sum_congr fun d _ => (mul_assoc _ _ _).symm
    have hmov : ∀ i, IsHalf e (GlobalTheory.RowKFix.movY ch.G j hj k z i) ↔ IsHalf e (z i) := fun i => by
      rw [movY_eq]
      exact GlobalTheory.SchrMove.isHalf_actO_iff _ _ _
    have hzero : ∀ z' : ∀ i : Fin D.R.m, WO (ch.G.V (.grid D.R.m i)) (ch.G.V (.grid D.R.m (i + 1))),
        ¬ ((∀ n, IsHalf e (x n)) ∧ ∀ i, IsHalf e (z' i)) →
        (τ.sum fun d a => a * (∏ n, (φ d).1 n (x n)) * ∏ i, (φ d).2 i (z' i)) = 0 := by
      intro z' hz'
      refine Finset.sum_eq_zero fun d hd => ?_
      by_contra h0
      obtain ⟨ha, hb⟩ := mul_ne_zero_iff.1 h0
      exact hz' ⟨fun n => ((hloc d hd).1 n).1.1 _ (Finset.prod_ne_zero_iff.1 (right_ne_zero_of_mul ha) n (Finset.mem_univ _)),
        fun i => ((hloc d hd).2 i).1.1 _ (Finset.prod_ne_zero_iff.1 hb i (Finset.mem_univ _))⟩
    refine hL.trans (Eq.trans ?_ hR.symm)
    by_cases hall : (∀ n, IsHalf e (x n)) ∧ ∀ i, IsHalf e (z i)
    · rw [hid x z hall.1 hall.2, hid x _ hall.1 fun i => (hmov i).2 (hall.2 i)]
      exact hT x z
    · rw [hzero z hall, hzero _ fun h => hall ⟨h.1, fun i => (hmov i).1 (h.2 i)⟩, mul_zero]

end GlobalTheory.RowKFix.Tens

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilRepPairFixesFlippedTensorSumStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilRep_pair_fixes_flippedTensorSum : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (large₂ : SizeData₂ D) (F : Face D A), HidaSetting large₂ R F → ch.Is → ∀ (t : T) (Φ : ch.G.Datum) (τ : SchRow ch.G × SchDown ch.G t →₀ ℂ), IsFlipFin t ch.S.B ch.rm Φ τ → ∀ (j : ℕ) (hj : j + 1 + 1 < D.R.m), ∀ k ∈ latGrp ch.G (j + 1), ∀ c₁ c₂ : ℂ, ch.W.om (.mu t D.R.m j) (1, k) (ch.rm.vT D.R.m j) = c₁ • ch.rm.vT D.R.m j → ch.W.om (.mu t D.R.m (j + 1)) (k, 1) (ch.rm.vT D.R.m (j + 1)) = c₂ • ch.rm.vT D.R.m (j + 1) → (∀ x y, c₁ * c₂ * ∏ w ∈ locPl ch.G t, Tflip ch.W ch.S.B t Φ w (oppArgs t ch.S.B w x (GlobalTheory.RowKFix.movY ch.G j hj k y)) = ∏ w ∈ locPl ch.G t, Tflip ch.W ch.S.B t Φ w (oppArgs t ch.S.B w x y)) → ∀ (y : RowPt ch.G) (v : ∀ i : Fin D.R.m, WO (ch.G.V (.grid D.R.m i)) (ch.G.V (.grid D.R.m (i + 1)))), (τ.sum fun d x => x * ((∏ n, d.1 n (y n)) * ∏ i : Fin D.R.m, ch.W.om (.mu t D.R.m i) ((Pi.mulSingle (j + 1) k : Pts ch.G) i, (Pi.mulSingle (j + 1) k : Pts ch.G) (i + 1)) (d.2 i) (v i))) = τ.sum fun d x => x * ((∏ n, d.1 n (y n)) * ∏ i, d.2 i (v i)) := by
  first | exact @GlobalTheory.RowKFix.Tens.sum_om_single_eq | exact GlobalTheory.RowKFix.Tens.sum_om_single_eq | (intros; apply GlobalTheory.RowKFix.Tens.sum_om_single_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlippedFiniteTensorLatticeFixedLargeDepth
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowKFix

theorem key {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks]
    [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (large₂ : SizeData₂ D) (F : Face D A)
    (hS : HidaSetting large₂ R F) (hch : ch.Is) (hsh : ShapeAt ch) : KFix ch := by
  intro t Φ τ hτ J hJ k hk y v
  have hJ' : 1 ≤ J ∧ J + 1 < D.R.m := by
    simp only [idx, List.mem_range'_1] at hJ
    omega
  obtain ⟨j, rfl⟩ : ∃ j, J = j + 1 := ⟨J - 1, by omega⟩
  have hj : j + 1 + 1 < D.R.m := hJ'.2
  obtain ⟨c₁, c₂, h1, h2, h3⟩ := GlobalTheory.T.lastRowInnerVertex_vacua_scaled_localProduct ch large₂ F hS hch hsh t Φ j hj k hk
  exact GlobalTheory.T.weilRep_pair_fixes_flippedTensorSum ch large₂ F hS hch t Φ τ hτ j hj k hk c₁ c₂ h1 h2 h3 y v

theorem kfix : Big fun ch => KFix ch := by
  obtain ⟨CF0, h⟩ := GlobalTheory.T.lastRowLatticesGoodPosition_large_depth
  refine ⟨CF0, fun ε CF hCF => ?_⟩
  obtain ⟨x₀, hx⟩ := h ε CF hCF
  exact ⟨x₀, fun D large₂ he hx' Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hch hsc =>
    key ch large₂ F hS hch (hx D large₂ he hx' Γ Pl0 T A Ks R F hS ch hch hsc)⟩

end GlobalTheory.RowKFix
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlippedFiniteTensorLatticeFixedLargeDepthStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flippedFiniteTensorLatticeFixed_largeDepth : Big fun ch => KFix ch := by
  first | exact @GlobalTheory.RowKFix.kfix | exact GlobalTheory.RowKFix.kfix | (intros; apply GlobalTheory.RowKFix.kfix <;> assumption)
end
