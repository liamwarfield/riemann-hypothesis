module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.SharpSpanCounting.Common
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBwdNA

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.SharpSpanCounting.SharpEquivApply
noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA

namespace Formalism.L2.SG.LocalCountModules.LocCntCommon

section O

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem cj_mem_O (L : LocE F E) {x : E} (hx : x ∈ L.O) : L.cj x ∈ L.O := by
  rw [L.O_def] at hx ⊢
  exact hx.map ((L.cj : E →ₐ[F] E).restrictScalars 𝒪[F])

end O

section Pair

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V)

theorem h_add_right (x y y' : V) : H.h x (y + y') = H.h x y + H.h x y' := by
  rw [H.h_herm (y + y') x, H.h_add_left, map_add (f := _), ← H.h_herm, ← H.h_herm]

theorem h_smul_right (a : E) (x y : V) : H.h x (a • y) = M.L.cj a * H.h x y := by
  rw [H.h_herm (a • y) x, H.h_smul_left, map_mul, ← H.h_herm]

theorem h_zero_right (x : V) : H.h x 0 = 0 := by
  rw [H.h_herm 0 x, H.h_zero_left, map_zero]

def hLm (y : V) : V →ₗ[E] E where
  toFun v := H.h v y
  map_add' x x' := H.h_add_left x x' y
  map_smul' a x := by simp [H.h_smul_left]

theorem h_sum_left {ι : Type} (s : Finset ι) (c : ι → E) (g : ι → V) (y : V) :
    H.h (∑ i ∈ s, c i • g i) y = ∑ i ∈ s, c i * H.h (g i) y := by
  have := map_sum (hLm H y) (fun i => c i • g i) s
  simp only [map_smul, smul_eq_mul] at this
  exact this

def pairing {ι : Type} (g : ι → V) : V →ₗ[E] (ι → E) where
  toFun v i := H.h v (g i)
  map_add' x y := by funext i; simp [H.h_add_left]
  map_smul' a x := by funext i; simp [H.h_smul_left]

def gramH {ι : Type} (g : ι → V) : Matrix ι ι E := Matrix.of fun i j => H.h (g i) (g j)

theorem pairing_sum {ι : Type} [Fintype ι] (g : ι → V) (c : ι → E) :
    pairing H g (∑ i, c i • g i) = Matrix.vecMul c (gramH H g) := by
  funext j
  simp [pairing, gramH, Matrix.vecMul, dotProduct, h_sum_left H]

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def pairSpan (g : ι → V) : Submodule.span E (Set.range g) →ₗ[E] (ι → E) :=
  (pairing H g).comp (Submodule.span E (Set.range g)).subtype

theorem pairSpan_bij (g : ι → V) (hG : IsUnit (gramH H g).det) :
    Function.Bijective (pairSpan H g) := by
  constructor
  · intro x y hxy
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 x.2
    obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 y.2
    have h1 : Matrix.vecMul c (gramH H g) = Matrix.vecMul d (gramH H g) := by
      rw [← pairing_sum, ← pairing_sum, hc, hd]; exact hxy
    have h2 : c = d := by
      have := congrArg (fun w => Matrix.vecMul w (gramH H g)⁻¹) h1
      simpa [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hG] using this
    apply Subtype.ext
    rw [← hc, ← hd, h2]
  · intro y
    refine ⟨⟨∑ i, (Matrix.vecMul y (gramH H g)⁻¹) i • g i,
      (Submodule.mem_span_range_iff_exists_fun E).2 ⟨_, rfl⟩⟩, ?_⟩
    show pairing H g (∑ i, (Matrix.vecMul y (gramH H g)⁻¹) i • g i) = y
    rw [pairing_sum, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hG, Matrix.vecMul_one]

def pairEquiv (g : ι → V) (hG : IsUnit (gramH H g).det) :
    Submodule.span E (Set.range g) ≃ₗ[E] (ι → E) :=
  LinearEquiv.ofBijective (pairSpan H g) (pairSpan_bij H g hG)

theorem pairEquiv_apply (g : ι → V) (hG : IsUnit (gramH H g).det)
    (x : Submodule.span E (Set.range g)) (i : ι) : pairEquiv H g hG x i = H.h x (g i) := rfl

end Pair

section Sharp

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V)

theorem mem_MMsharp_iff {r : ℕ} (t : Term V M r) (u : V) :
    u ∈ MMsharp H t ↔ u ∈ Submodule.span E (Set.range (H.MMfam t)) ∧
      ∀ i, H.h u (H.MMfam t i) ∈ M.L.O := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun i => h2 _ (Submodule.subset_span ⟨i, rfl⟩)⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun m hm => ?_⟩
    induction hm using Submodule.span_induction with
    | mem x hx => obtain ⟨i, rfl⟩ := hx; exact h2 i
    | zero => rw [h_zero_right]; exact M.L.O.zero_mem
    | add x y _ _ hx hy => rw [h_add_right]; exact M.L.O.add_mem hx hy
    | smul a x _ hx =>
      rw [Subring.smul_def, h_smul_right]; exact M.L.O.mul_mem (cj_mem_O M.L a.2) hx

theorem mem_MMo_iff {r : ℕ} (t : Term V M r) (u : V) :
    u ∈ MMo H t ↔ ∃ c : Fin (r + 1) ⊕ Fin (r + 1) → M.L.O, ∑ i, (c i : E) • H.MMfam t i = u := by
  unfold MMo
  rw [Submodule.mem_span_range_iff_exists_fun]
  simp only [Subring.smul_def]

def sharpEquiv {r : ℕ} (t : Term V M r) (hG : IsUnit (gramH H (H.MMfam t)).det) :
    ↥(MMsharp H t) ≃ₗ[M.L.O] (Fin (r + 1) ⊕ Fin (r + 1) → M.L.O) where
  toFun u i := ⟨H.h u (H.MMfam t i), ((mem_MMsharp_iff H t u).1 u.2).2 i⟩
  map_add' x y := by funext i; apply Subtype.ext; simp [H.h_add_left]
  map_smul' a x := by
    funext i; apply Subtype.ext
    simp [Subring.smul_def, H.h_smul_left]
  invFun y := ⟨(pairEquiv H (H.MMfam t) hG).symm (fun i => (y i : E)), by
    rw [mem_MMsharp_iff]
    refine ⟨Submodule.coe_mem _, fun i => ?_⟩
    have := congrFun ((pairEquiv H (H.MMfam t) hG).apply_symm_apply (fun i => (y i : E))) i
    rw [pairEquiv_apply] at this
    rw [this]; exact (y i).2⟩
  left_inv u := by
    apply Subtype.ext
    have hs : (u : V) ∈ Submodule.span E (Set.range (H.MMfam t)) :=
      ((mem_MMsharp_iff H t u).1 u.2).1
    have : (pairEquiv H (H.MMfam t) hG).symm (fun i => H.h u (H.MMfam t i)) = ⟨u, hs⟩ := by
      rw [LinearEquiv.symm_apply_eq]; funext i; rfl
    simp only [this]
  right_inv y := by
    funext i; apply Subtype.ext
    have := congrFun ((pairEquiv H (H.MMfam t) hG).apply_symm_apply (fun i => (y i : E))) i
    rw [pairEquiv_apply] at this
    exact this

theorem sharpEquiv_apply {r : ℕ} (t : Term V M r) (hG : IsUnit (gramH H (H.MMfam t)).det)
    (u : ↥(MMsharp H t)) (i) : (sharpEquiv H t hG u i : E) = H.h u (H.MMfam t i) := rfl

def relSub {r : ℕ} (t : Term V M r) : Submodule M.L.O (Fin (r + 1) ⊕ Fin (r + 1) → M.L.O) where
  carrier := {y | ∃ c : Fin (r + 1) ⊕ Fin (r + 1) → M.L.O,
    ∀ j, (y j : E) = ∑ i, (c i : E) * H.h (H.MMfam t i) (H.MMfam t j)}
  add_mem' := by
    rintro a b ⟨c, hc⟩ ⟨d, hd⟩
    refine ⟨c + d, fun j => ?_⟩
    simp only [Pi.add_apply, Subring.coe_add, hc j, hd j, add_mul, Finset.sum_add_distrib]
  zero_mem' := ⟨0, fun j => by simp⟩
  smul_mem' := by
    rintro a y ⟨c, hc⟩
    refine ⟨a • c, fun j => ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul, Subring.coe_mul, hc j, Finset.mul_sum, mul_assoc]

theorem map_sharp_MMo {r : ℕ} (t : Term V M r) (hG : IsUnit (gramH H (H.MMfam t)).det) :
    ((MMo H t).comap (MMsharp H t).subtype).map (sharpEquiv H t hG : _ →ₗ[M.L.O] _) =
      relSub H t := by
  ext y
  constructor
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨c, hc⟩ := (mem_MMo_iff H t u).1 hu
    refine ⟨c, fun j => ?_⟩
    rw [LinearEquiv.coe_coe, sharpEquiv_apply, ← hc, h_sum_left]
  · rintro ⟨c, hc⟩
    have hs : (∑ i, (c i : E) • H.MMfam t i) ∈ MMsharp H t := by
      rw [mem_MMsharp_iff]
      refine ⟨Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
        (Submodule.subset_span ⟨i, rfl⟩), fun j => ?_⟩
      rw [h_sum_left, ← hc j]; exact (y j).2
    refine ⟨⟨_, hs⟩, (mem_MMo_iff H t _).2 ⟨c, rfl⟩, ?_⟩
    funext j; apply Subtype.ext
    rw [LinearEquiv.coe_coe, sharpEquiv_apply, h_sum_left, ← hc j]

def ddEquiv {r : ℕ} (t : Term V M r) (hG : IsUnit (gramH H (H.MMfam t)).det) :
    DDt H t ≃ₗ[M.L.O] (Fin (r + 1) ⊕ Fin (r + 1) → M.L.O) ⧸ relSub H t :=
  Submodule.Quotient.equiv _ _ (sharpEquiv H t hG) (map_sharp_MMo H t hG)

end Sharp

end Formalism.L2.SG.LocalCountModules.LocCntCommon
end
end

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA

namespace Formalism.L2.SG.LocalCountModules.LocCntCommon

section Coord

variable {E : Type} [CommRing E] (O : Subring E) (cj : E →+* E) {r : ℕ}

abbrev Ix (r : ℕ) : Type := Fin (r + 1) ⊕ Fin (r + 1)

def gramC (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : E) : Matrix (Ix r) (Ix r) E :=
  Matrix.fromBlocks (Matrix.of fun a b => if a = Fin.last r ∧ b = Fin.last r then -T else 0)
    (Matrix.of fun a b => cj (Z a b)) Z.transpose
    (Matrix.of fun a b => if a = Fin.last r ∧ b = Fin.last r then -T' else 0)

def relC (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : E) : Submodule O (Ix r → O) where
  carrier := {y | ∃ c : Ix r → O, ∀ j, (y j : E) = ∑ i, (c i : E) * gramC cj Z T T' i j}
  add_mem' := by
    rintro a b ⟨c, hc⟩ ⟨d, hd⟩
    refine ⟨c + d, fun j => ?_⟩
    simp only [Pi.add_apply, Subring.coe_add, hc j, hd j, add_mul, Finset.sum_add_distrib]
  zero_mem' := ⟨0, fun j => by simp⟩
  smul_mem' := by
    rintro a y ⟨c, hc⟩
    refine ⟨a • c, fun j => ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul, Subring.coe_mul, hc j, Finset.mul_sum, mul_assoc]

abbrev DDc (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : E) : Type :=
  (Ix r → O) ⧸ relC O cj Z T T'

def formC (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : E) (Y W : Ix r → O) : E :=
  ∑ i, ∑ j, (Y i : E) * (gramC cj Z T T')⁻¹ i j * cj (W j)

def lamC (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (y : Fin (r + 1) → E) : E :=
  (Z⁻¹.mulVec y) (Fin.last r)

def lamStarC (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (y : Fin (r + 1) → E) : E :=
  ∑ b, cj (Z⁻¹ b (Fin.last r)) * y b

def GamC (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : E) : Set (DDc O cj Z T T' × (E × E)) :=
  {p | ∃ Y : Ix r → O, (∀ a : Fin r, Y (Sum.inl a.castSucc) = 0) ∧
    p = (Submodule.Quotient.mk Y, ((Y (Sum.inl (Fin.last r)) : E),
      lamStarC cj Z (fun b => (Y (Sum.inr b) : E))))}

def GamC' (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : E) : Set (DDc O cj Z T T' × (E × E)) :=
  {p | ∃ Y : Ix r → O, (∀ b : Fin r, Y (Sum.inr b.castSucc) = 0) ∧
    p = (Submodule.Quotient.mk Y, (lamC Z (fun a => (Y (Sum.inl a) : E)),
      (Y (Sum.inr (Fin.last r)) : E)))}

def ThetaC (Z₁ Z₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : E) :
    Set (DDc O cj Z₁ T T' ≃ₗ[O] DDc O cj Z₂ T T') :=
  {θ | (∀ Y W Y₂ W₂ : Ix r → O, θ (Submodule.Quotient.mk Y) = Submodule.Quotient.mk Y₂ →
      θ (Submodule.Quotient.mk W) = Submodule.Quotient.mk W₂ →
      formC O cj Z₂ T T' Y₂ W₂ - formC O cj Z₁ T T' Y W ∈ O) ∧
    (fun p => (θ p.1, p.2)) '' GamC O cj Z₁ T T' = GamC O cj Z₂ T T' ∧
    (fun p => (θ p.1, p.2)) '' GamC' O cj Z₁ T T' = GamC' O cj Z₂ T T'}

end Coord

section Steps

def CoordL : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E), M.OK → M.split = none →
  ∀ (r n : ℕ) (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V), Module.finrank E V = n →
  ∀ (t₁ : Term V M r) (f₂ f₂' : Fin (r + 1) → V)
    (φ : H.Wb t₁.f ≃ₗ[E] H.Wb f₂) (φ' : H.Wb t₁.f' ≃ₗ[E] H.Wb f₂'), LocalCountHypotheses H t₁ f₂ f₂' φ φ' →
    H.Dl t₁.f t₁.f' r = 0 → IsUnit (H.Dl f₂ f₂' (r + 1)) →
    (∀ a b, H.Zhat f₂ f₂' a b ∈ M.L.O) →
    Nat.card (Theta H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ φ φ') =
      Nat.card (ThetaC M.L.O (M.L.cj : E →+* E) (H.Zhat t₁.f t₁.f') (H.Zhat f₂ f₂')
        (algebraMap F E t₁.T) (algebraMap F E t₁.T'))

def UnramifiedIsoCountZero : Prop :=
  ∀ (E : Type) [CommRing E] (O : Subring E) (cj : E →+* E), (∀ x, cj (cj x) = x) →
    (∀ x ∈ O, cj x ∈ O) →
  ∀ (r : ℕ) (T T' : E), T ∈ O → T' ∈ O → cj T = T → cj T' = T' →
  ∀ (Z₁ Z₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) O),
    IsUnit (Z₁.map O.subtype).det → IsUnit (Z₂.map O.subtype).det →
    ((Z₁.map O.subtype).submatrix Fin.castSucc Fin.castSucc).det = 0 →
    ((Z₂.map O.subtype).submatrix Fin.castSucc Fin.castSucc).det = 0 →
    IsUnit (gramC cj (Z₁.map O.subtype) T T').det → IsUnit (gramC cj (Z₂.map O.subtype) T T').det →
    Nat.card (ThetaC O cj (Z₁.map O.subtype) (Z₂.map O.subtype) T T') = Nat.card (IsoMbe Z₁ Z₂)

end Steps

section Deriv

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]

theorem dl_full (H : HermSp M V) {r : ℕ} (f f' : Fin (r + 1) → V) :
    H.Dl f f' (r + 1) = (H.Zhat f f').det := by
  unfold HermSp.Dl
  rw [dite_eq_left le_rfl]
  congr 1

theorem gramC_eq (H : HermSp M V) {r : ℕ} (f f' : Fin (r + 1) → V) (T T' : F)
    (hF : Formalism.MainNotions.ThinScalesBound.FrameK H f T) (hF' : Formalism.MainNotions.ThinScalesBound.FrameK H f' T') :
    gramC (M.L.cj : E →+* E) (H.Zhat f f') (algebraMap F E T) (algebraMap F E T') =
      (H.gram (Sum.elim f f')).transpose := by
  rw [gram_eq_fromBlocks H f f' T T' hF hF', Matrix.fromBlocks_transpose]
  ext (a | a) (b | b) <;> simp [gramC, cornerM, Function.swap, and_comm]

theorem unit_gramC (H : HermSp M V) {r : ℕ} (f f' : Fin (r + 1) → V) (T T' : F)
    (hF : Formalism.MainNotions.ThinScalesBound.FrameK H f T) (hF' : Formalism.MainNotions.ThinScalesBound.FrameK H f' T')
    (hD1 : IsUnit (H.Dl f f' (r + 1))) (hD0 : H.Dl f f' r = 0) :
    IsUnit (gramC (M.L.cj : E →+* E) (H.Zhat f f') (algebraMap F E T) (algebraMap F E T')).det := by
  rw [gramC_eq H f f' T T' hF hF', Matrix.det_transpose]
  obtain ⟨s, hs, hdet⟩ := gram_det H f f' T T' hF hF' hD1
  have hGd : IsUnit (H.Gdet f f' T T') := by
    unfold HermSp.Gdet HermSp.normE
    rw [hD0, map_zero, mul_zero, mul_zero, sub_zero]
    exact hD1.mul (hD1.map M.L.cj)
  have hsu : IsUnit s := ⟨⟨s, s, hs, hs⟩, rfl⟩
  have : (H.gram (Sum.elim f f')).det = H.Gdet f f' T T' * s := by
    rw [← hdet, mul_assoc, hs, mul_one]
  rw [this]
  exact hGd.mul hsu

theorem thetaMbe0_L_of (h1 : CoordL) (h2 : UnramifiedIsoCountZero) :
    Formalism.MainNotions.ThinScalesBound.AllLoc (fun M => ∀ r n, ThetaMbe0 M r n false) := by
  intro F _ _ _ E _ _ _ _ M hOK r n hmode
  obtain ⟨L, sp, mu⟩ := M
  cases sp with
  | some g => simp at hmode
  | none =>
  intro V _ _ H hn t₁ f₂ f₂' φ φ' hyp hD Z₁ Z₂ e₁ e₂
  have hs : (⟨L, none, mu⟩ : Model F E).split = none := rfl
  have z₁ : Z₁.Z.map (Model.R ⟨L, none, mu⟩).subtype = H.Zhat t₁.f t₁.f' := by
    rw [e₁]; exact zzplusOf_none hs _ _ _
  have z₂ : Z₂.Z.map (Model.R ⟨L, none, mu⟩).subtype = H.Zhat f₂ f₂' := by
    rw [e₂]; exact zzplusOf_none hs _ _ _
  have hD2 : H.Dl f₂ f₂' r = 0 := dl_zero_two hyp hD
  have hU1 : IsUnit (H.Dl t₁.f t₁.f' (r + 1)) := dl_succ_unit hyp
  have hU2 : IsUnit (H.Dl f₂ f₂' (r + 1)) := by rw [dl_full, ← z₂]; exact Z₂.unit
  have hint : ∀ a b, H.Zhat f₂ f₂' a b ∈ L.O := by
    intro a b
    rw [← z₂]
    exact (Z₂.Z a b).2
  have hT : t₁.T ∈ 𝒪[F] := hyp.1.1.2.1.2.2.2.1
  have hT' : t₁.T' ∈ 𝒪[F] := hyp.1.1.2.2.1.2.2.2.1
  have hF₁ : Formalism.MainNotions.ThinScalesBound.FrameK H t₁.f t₁.T := ⟨hyp.1.1.2.1.2.1, hyp.1.1.2.1.2.2.1⟩
  have hF₁' : Formalism.MainNotions.ThinScalesBound.FrameK H t₁.f' t₁.T' := ⟨hyp.1.1.2.2.1.2.1, hyp.1.1.2.2.1.2.2.1⟩
  have hG1 := unit_gramC H _ _ _ _ hF₁ hF₁' hU1 hD
  have hG2 := unit_gramC H _ _ _ _ hyp.2.1 hyp.2.2.1 hU2 hD2
  have hh1 : ((Z₁.Z.map (Model.R ⟨L, none, mu⟩).subtype).submatrix Fin.castSucc Fin.castSucc).det = 0 := by
    rw [z₁, ← dl_eq_det]; exact hD
  have hh2 : ((Z₂.Z.map (Model.R ⟨L, none, mu⟩).subtype).submatrix Fin.castSucc Fin.castSucc).det = 0 := by
    rw [z₂, ← dl_eq_det]; exact hD2
  rw [← z₁] at hG1
  rw [← z₂] at hG2
  rw [h1 F E ⟨L, none, mu⟩ hOK hs r n V H hn t₁ f₂ f₂' φ φ' hyp hD hU2 hint, ← z₁, ← z₂]
  exact h2 E L.O (L.cj : E →+* E) (fun x => L.cj_cj x) (fun x hx => cj_mem_O L hx)
    r _ _ (Formalism.MainNotions.LocalModelPeriodLattices.algebraMap_mem_O L ⟨t₁.T, hT⟩) (Formalism.MainNotions.LocalModelPeriodLattices.algebraMap_mem_O L ⟨t₁.T', hT'⟩)
    (AlgEquiv.commutes _ _) (AlgEquiv.commutes _ _) Z₁.Z Z₂.Z Z₁.unit Z₂.unit hh1 hh2 hG1 hG2

end Deriv

end Formalism.L2.SG.LocalCountModules.LocCntCommon
