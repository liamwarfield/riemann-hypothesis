module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionPointActionPeriodValueFractionFiel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientLineDegreeLeOfTriangularFamilyStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiNegativeDescendsFieldExtensionCurve
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetDegreeNonposOfAdelicDegreeNonpos
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieSubsheafLinesDegreeNonpos

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieSheafSemiAbelianSemiNegOfIsAlgClosed
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenericFrameAndLocalFramesAllPlaces
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenericFrameAndLocalFramesAllPlaces
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Nef

theorem top_le_preimage_of_isDominant {K : Type} [Field K] {C : Scheme.{0}} (x : Sp K ⟶ C) [IsDominant x]
    (V : C.Opens) (hV : (V : Set C).Nonempty) : ⊤ ≤ x ⁻¹ᵁ V := by
  obtain ⟨y, hy⟩ := x.denseRange.exists_mem_open V.isOpen hV
  intro z _
  have : z = y := Subsingleton.elim _ _
  subst this
  exact hy

theorem top_le_preimage_of_closedPoint {R : Type} [CommRing R] [IsLocalRing R] {C : Scheme.{0}} (b : Sp R ⟶ C)
    (V : C.Opens) (h : b (IsLocalRing.closedPoint R) ∈ V) : ⊤ ≤ b ⁻¹ᵁ V := by
  intro z _
  have hs : z ⤳ IsLocalRing.closedPoint R :=
    (PrimeSpectrum.le_iff_specializes _ _).1 (IsLocalRing.le_maximalIdeal z.2.ne_top)
  exact (hs.map b.continuous).mem_open V.isOpen h

theorem locFrame_of_frames {k K : Type} [Field k] [Field K] [Algebra k K] {C : Scheme.{0}} (x : Sp K ⟶ C)
    {W : C.Modules} {r : ℕ} {V₀ V : C.Opens} {s : Fin r → Γ(W, V₀)} {t : Fin r → Γ(W, V)}
    (hs : IsFrame s) (ht : IsFrame t) (v : Place k K) (b : Sp v.O ⟶ C) (hb : spMap v.O.subtype ≫ b = x)
    (hbV : ⊤ ≤ b ⁻¹ᵁ V) (hx : ⊤ ≤ x ⁻¹ᵁ (V₀ ⊓ V)) :
    LocFrame x s v (((ht.basis (inf_le_right : V₀ ⊓ V ≤ V)).toMatrix
        (hs.basis (inf_le_left : V₀ ⊓ V ≤ V₀))).map (evAt x hx)) ∧
      (((ht.basis (inf_le_right : V₀ ⊓ V ≤ V)).toMatrix
        (hs.basis (inf_le_left : V₀ ⊓ V ≤ V₀))).map (evAt x hx)).det ≠ 0 := by
  set M := (ht.basis (inf_le_right : V₀ ⊓ V ≤ V)).toMatrix (hs.basis (inf_le_left : V₀ ⊓ V ≤ V₀)) with hM
  refine ⟨⟨b, V, t, V₀ ⊓ V, inf_le_left, inf_le_right, hx, M, hb, hbV, ht, fun j => ?_, rfl⟩, ?_⟩
  · have := (ht.basis (inf_le_right : V₀ ⊓ V ≤ V)).sum_repr (hs.basis (inf_le_left : V₀ ⊓ V ≤ V₀) j)
    simp only [IsFrame.basis_apply] at this
    rw [hM]
    simp only [Module.Basis.toMatrix_apply, IsFrame.basis_apply]
    exact this.symm
  · have hu : IsUnit M.det := by
      have := Module.Basis.toMatrix_mul_toMatrix_flip (ht.basis (inf_le_right : V₀ ⊓ V ≤ V))
        (hs.basis (inf_le_left : V₀ ⊓ V ≤ V₀))
      exact isUnit_iff_exists_inv.2 ⟨_, by rw [← Matrix.det_mul, this, Matrix.det_one]⟩
    have := (hu.map (evAt x hx)).ne_zero
    rwa [RingHom.map_det] at this

theorem unimod_one' {k F : Type} [Field k] [Field F] [Algebra k F] {n : ℕ} (v : Place k F) :
    Unimod v (1 : Matrix (Fin n) (Fin n) F) :=
  ⟨fun i j => by by_cases h : i = j <;> simp [Matrix.one_apply, h], by simp⟩

theorem exists_frame_locFrames : ∀ (k K : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k K] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)] (x : Sp K ⟶ C), IsGenOver k x →
  ∀ (W : C.Modules) (r : ℕ), IsVB W r → ∃ (V₀ : C.Opens) (s : Fin r → Γ(W, V₀)) (g : Place k K → Matrix (Fin r) (Fin r) K), (V₀ : Set C).Nonempty ∧ IsFrame s ∧ admitted g ∧ ∀ v, LocFrame x s v (g v) := by
  intro k K _ _ _ _ _ C _ x hx W r hW
  haveI : IsDominant x := hx.2.1.1
  have hxx : spMap (algebraMap K K) ≫ x = x := by
    change spMap (RingHom.id K) ≫ x = x
    exact (congrArg (· ≫ x) (Spec.map_id _)).trans (Category.id_comp x)
  obtain ⟨V₀, s, hη, hs⟩ := hW (x (IsLocalRing.closedPoint K))
  have hV₀ : (V₀ : Set C).Nonempty := ⟨_, hη⟩
  have hcen : ∀ v : Place k K, ∃ b : Sp v.O ⟶ C, spMap v.O.subtype ≫ b = x := fun v => by
    obtain ⟨b, hb, -⟩ := GlobalTheory.T.existsUnique_centre_functionFieldPlace_curve k K K C x hx v
    exact ⟨b, hb.trans hxx⟩
  choose b hb using hcen
  have key : ∀ v, ∃ gv : Matrix (Fin r) (Fin r) K,
      LocFrame x s v gv ∧ gv.det ≠ 0 ∧ (⊤ ≤ b v ⁻¹ᵁ V₀ → gv = 1) := by
    intro v
    by_cases hv : ⊤ ≤ b v ⁻¹ᵁ V₀
    · have hx' : ⊤ ≤ x ⁻¹ᵁ (V₀ ⊓ V₀) := by
        rw [inf_idem]; exact top_le_preimage_of_isDominant x V₀ hV₀
      obtain ⟨h1, h2⟩ := locFrame_of_frames x hs hs v (b v) (hb v) hv hx'
      refine ⟨_, h1, h2, fun _ => ?_⟩
      rw [Module.Basis.toMatrix_self]
      simp
    · obtain ⟨V, t, hc, ht⟩ := hW (b v (IsLocalRing.closedPoint v.O))
      have hbV := top_le_preimage_of_closedPoint (b v) V hc
      have hx' : ⊤ ≤ x ⁻¹ᵁ (V₀ ⊓ V) := fun z hz =>
        ⟨top_le_preimage_of_isDominant x V₀ hV₀ hz, top_le_preimage_of_isDominant x V ⟨_, hc⟩ hz⟩
      obtain ⟨h1, h2⟩ := locFrame_of_frames x hs ht v (b v) (hb v) hbV hx'
      exact ⟨_, h1, h2, fun h => absurd h hv⟩
  choose g hg1 hg2 hg3 using key
  refine ⟨V₀, s, g, hV₀, hs, ⟨hg2, ?_⟩, hg1⟩
  refine (GlobalTheory.T.finite_places_centre_outside_open k K K C x hx V₀ hV₀).subset fun v hv => ⟨b v, (hb v).trans hxx.symm, fun h => hv ?_⟩
  rw [hg3 v h]
  exact unimod_one' v

end GlobalTheory.Nef
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenericFrameAndLocalFramesAllPlacesStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_genericFrame_and_localFrames_allPlaces : ∀ (k K : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k K] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)] (x : Sp K ⟶ C), IsGenOver k x →
  ∀ (W : C.Modules) (r : ℕ), IsVB W r → ∃ (V₀ : C.Opens) (s : Fin r → Γ(W, V₀)) (g : Place k K → Matrix (Fin r) (Fin r) K), (V₀ : Set C).Nonempty ∧ IsFrame s ∧ admitted g ∧ ∀ v, LocFrame x s v (g v) := by
  first | exact @GlobalTheory.Nef.exists_frame_locFrames | exact GlobalTheory.Nef.exists_frame_locFrames | (intros; apply GlobalTheory.Nef.exists_frame_locFrames <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicMatrixFamilyDegreeLeRankMulLineBound
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IwasawaDecompositionAdmissibleFamily
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IwasawaDecompositionAdmissibleFamily
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

namespace GlobalTheory.IwaFam

open Matrix

lemma det_one_add_vmv {R : Type} [CommRing R] {n : ℕ} (a b : Fin n → R) :
    (1 + Matrix.vecMulVec a b).det = 1 + b ⬝ᵥ a := by
  have h := Matrix.det_one_add_replicateCol_mul_replicateRow (ι := Unit) a b
  have e : Matrix.replicateCol Unit a * Matrix.replicateRow Unit b = Matrix.vecMulVec a b := by
    ext i j; simp [Matrix.mul_apply, Matrix.vecMulVec_apply]
  rwa [e] at h

variable {k F : Type} [Field k] [Field F] [Algebra k F]

lemma val_det_le_one (v : Place k F) {n : ℕ} (M : Matrix (Fin n) (Fin n) F)
    (h : ∀ i j, v.1 (M i j) ≤ 1) : v.1 M.det ≤ 1 := by
  let M' : Matrix (Fin n) (Fin n) v.O := Matrix.of fun i j => ⟨M i j, (Valuation.mem_valuationSubring_iff _ _).2 (h i j)⟩
  have e : v.O.subtype M'.det = M.det := by rw [RingHom.map_det]; rfl
  rw [← e]; exact (Valuation.mem_valuationSubring_iff _ _).1 M'.det.2

lemma eq_one_of_mul {a b : WithZero (Multiplicative ℤ)} (ha : a ≤ 1) (hb : b ≤ 1) (h : a * b = 1) : b = 1 :=
  le_antisymm hb (calc 1 = a * b := h.symm
    _ ≤ b := mul_le_of_le_one_left' ha)

lemma val_sign (v : Place k F) {n : ℕ} (σ : Equiv.Perm (Fin n)) : v.1 ((Equiv.Perm.sign σ : ℤ) : F) = 1 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]

lemma exists_u (v : Place k F) {r : ℕ} (y : Fin (r+1) → F) (hy : y ≠ 0) :
    ∃ u : Matrix (Fin (r+1)) (Fin (r+1)) F, Unimod v u ∧ ∀ a : Fin r, (u *ᵥ y) a.succ = 0 := by
  obtain ⟨-, -, -, -, -, -, hmax, -⟩ := GlobalTheory.T.functionFieldPlaceOrder_calculus k F v
  obtain ⟨i, hi, -, -, hle⟩ := hmax (r+1) y hy
  set c : Fin (r+1) → F := fun j => if j = i then 0 else y j / y i with hc
  set u0 : Matrix (Fin (r+1)) (Fin (r+1)) F := 1 + Matrix.vecMulVec (-c) (Pi.single i 1) with hu0
  have hcle : ∀ j, v.1 (c j) ≤ 1 := by
    intro j; simp only [hc]; split_ifs
    · simp
    · rw [Valuation.map_div]
      exact div_le_one_of_le₀ (hle j) zero_le'
  have hu0y : ∀ j, (u0 *ᵥ y) j = y j - c j * y i := by
    intro j
    simp only [hu0, Matrix.add_mulVec, Matrix.one_mulVec, Pi.add_apply]
    simp [Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply, Pi.single_apply, ite_mul]
    ring
  refine ⟨u0.submatrix (Equiv.swap 0 i) id, ⟨?_, ?_⟩, ?_⟩
  · intro a b
    simp only [Matrix.submatrix_apply, id, hu0, Matrix.add_apply, Matrix.vecMulVec_apply]
    refine Valuation.map_add_le _ ?_ ?_
    · rw [Matrix.one_apply]; split_ifs <;> simp
    · rw [Pi.neg_apply, Valuation.map_mul, Valuation.map_neg]
      refine mul_le_one' (hcle _) ?_
      rw [Pi.single_apply]; split_ifs <;> simp
  · rw [Matrix.det_permute, det_one_add_vmv, Valuation.map_mul, val_sign]
    simp [hc]
  · intro a
    show (u0 *ᵥ y) (Equiv.swap 0 i a.succ) = 0
    have hne : Equiv.swap 0 i a.succ ≠ i := by
      intro h
      have := congrArg (Equiv.swap 0 i) h
      rw [Equiv.swap_apply_self, Equiv.swap_apply_right] at this
      exact Fin.succ_ne_zero a this
    rw [hu0y]; simp only [hc, if_neg hne]; field_simp; ring

lemma exists_h {n : ℕ} (x : Fin (n+1) → F) (hx : x ≠ 0) :
    ∃ h : Matrix (Fin (n+1)) (Fin (n+1)) F, h.det ≠ 0 ∧ ∀ a, h a 0 = x a := by
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra hc; push_neg at hc; exact hx (funext hc)
  refine ⟨(1 + Matrix.vecMulVec (x - Pi.single i 1) (Pi.single i 1)).submatrix id (Equiv.swap 0 i), ?_, ?_⟩
  · rw [Matrix.det_permute', det_one_add_vmv]
    simp [hi]
    split_ifs <;> simp
  · intro a
    simp [Matrix.submatrix_apply, Matrix.one_apply, Matrix.vecMulVec_apply]
    split_ifs <;> simp_all

lemma unimod_ae [IsAlgClosed k] [CharZero k] (hF : IsFF k F) {n : ℕ} (h : Matrix (Fin n) (Fin n) F) (hd : h.det ≠ 0) :
    {v : Place k F | ¬ Unimod v h}.Finite := by
  have fin1 : ∀ c : F, {v : Place k F | ¬ v.1 c ≤ 1}.Finite := by
    intro c
    by_cases hc : c = 0
    · simp [hc]
    · exact (GlobalTheory.T.functionField_finite_support_sum_order_eq_zero k F hF c hc).1.subset fun v hv h1 => hv (le_of_eq h1)
  refine ((GlobalTheory.T.functionField_finite_support_sum_order_eq_zero k F hF _ hd).1.union (Set.finite_iUnion fun p : Fin n × Fin n => fin1 (h p.1 p.2))).subset ?_
  intro v hv
  simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_iUnion]
  by_contra hc; push_neg at hc
  exact hv ⟨fun i j => hc.2 (i, j), hc.1⟩

lemma unimod_pull {E : Type} [Field E] [Algebra k E] [Algebra F E] (ρ : Place k E → Place k F) (hρ : IsRes ρ)
    (p : Place k E) {n : ℕ} (u : Matrix (Fin n) (Fin n) F) (hu : Unimod (ρ p) u) :
    Unimod p (u.map (algebraMap F E)) := by
  refine ⟨fun i j => (hρ p _).2 (hu.1 i j), ?_⟩
  have e : (u.map (algebraMap F E)).det = algebraMap F E u.det := (RingHom.map_det _ _).symm
  have hd0 : u.det ≠ 0 := fun h0 => by
    have := hu.2; rw [h0, Valuation.map_zero] at this; exact zero_ne_one this
  have h1 : p.1 (algebraMap F E u.det) ≤ 1 := (hρ p _).2 hu.2.le
  have h2 : p.1 (algebraMap F E u.det⁻¹) ≤ 1 := (hρ p _).2 (by rw [map_inv₀, hu.2, inv_one])
  have h3 : p.1 (algebraMap F E u.det⁻¹) * p.1 (algebraMap F E u.det) = 1 := by
    rw [← Valuation.map_mul, ← map_mul, inv_mul_cancel₀ hd0, map_one, Valuation.map_one]
  rw [e]; exact eq_one_of_mul h2 h1 h3

lemma ordVec_pull {E : Type} [Field E] [Algebra k E] [Algebra F E] (ρ : Place k E → Place k F) (hρ : IsRes ρ)
    {n : ℕ} (u g h : Place k F → Matrix (Fin n) (Fin n) F) (hu : ∀ v, Unimod v (u v)) (p : Place k E) (w : Fin n → E) :
    ordVec p (pullAd ρ (fun v => u v * g v * h v) p *ᵥ w) = ordVec p (pullAd ρ g p *ᵥ ((h (ρ p)).map (algebraMap F E) *ᵥ w)) := by
  obtain ⟨-, -, -, -, -, -, -, -, hnrm, -⟩ := GlobalTheory.T.functionFieldPlaceOrder_calculus k E p
  simp only [pullAd, Matrix.map_mul]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  simp only [ordVec, hnrm _ _ _ (unimod_pull ρ hρ p _ (hu (ρ p)))]

end GlobalTheory.IwaFam


open Matrix in
theorem GlobalTheory.iwasawa_family : ∀ (k F : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Algebra k F], IsFF k F →
  ∀ (r : ℕ) (g : Place k F → Matrix (Fin (r + 1)) (Fin (r + 1)) F), admitted g → ∀ x : Fin (r + 1) → F, x ≠ 0 → ∃ (h : Matrix (Fin (r + 1)) (Fin (r + 1)) F) (u : Place k F → Matrix (Fin (r + 1)) (Fin (r + 1)) F), h.det ≠ 0 ∧ (∀ v, Unimod v (u v)) ∧ (∀ (v : Place k F) (i : Fin r), (u v * g v * h) i.succ 0 = 0) ∧ admitted (fun v => u v * g v * h) ∧ admitted (fun v => (u v * g v * h).submatrix Fin.succ Fin.succ) ∧ deg g = degLine g x + deg (fun v => (u v * g v * h).submatrix Fin.succ Fin.succ) ∧ ∑ᶠ v, ord v ((u v * g v * h) 0 0) = degLine g x ∧ ∀ b : ℝ, LinesLE g b → LinesLE (fun v => u v * g v * h) b := by
  intro k F _ _ _ _ _ hF r g hg x hx
  obtain ⟨h, hdet, hcol⟩ := GlobalTheory.IwaFam.exists_h x hx
  have hy : ∀ v, g v *ᵥ x ≠ 0 := fun v h0 => (hg.1 v) (Matrix.exists_mulVec_eq_zero_iff.1 ⟨x, hx, h0⟩)
  choose u hu hz using fun v => GlobalTheory.IwaFam.exists_u v (g v *ᵥ x) (hy v)
  have hcol0 : ∀ v a, (u v * g v * h) a 0 = (u v *ᵥ (g v *ᵥ x)) a := by
    intro v a
    rw [Matrix.mulVec_mulVec, Matrix.mul_apply]
    simp only [hcol]
    rfl
  have hz' : ∀ v (i : Fin r), (u v * g v * h) i.succ 0 = 0 := fun v i => by rw [hcol0]; exact hz v i
  have hdetA : ∀ v, (u v * g v * h).det = (u v * g v * h) 0 0 * ((u v * g v * h).submatrix Fin.succ Fin.succ).det := by
    intro v
    rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
    simp [hz', Fin.succAbove_zero]
  have hdu : ∀ v, (u v).det ≠ 0 := fun v h0 => by
    have := (hu v).2; rw [h0, Valuation.map_zero] at this; exact zero_ne_one this
  have hdA : ∀ v, (u v * g v * h).det ≠ 0 := fun v => by
    rw [Matrix.det_mul, Matrix.det_mul]; exact mul_ne_zero (mul_ne_zero (hdu v) (hg.1 v)) hdet
  have h00 : ∀ v, (u v * g v * h) 0 0 ≠ 0 := fun v h0 => hdA v (by rw [hdetA, h0, zero_mul])
  have hdS : ∀ v, ((u v * g v * h).submatrix Fin.succ Fin.succ).det ≠ 0 := fun v h0 => hdA v (by rw [hdetA, h0, mul_zero])

  have hov : ∀ v, ordVec v (g v *ᵥ x) = ord v ((u v * g v * h) 0 0) := by
    intro v
    obtain ⟨-, -, -, -, -, -, hmax, -, hnrm, -⟩ := GlobalTheory.T.functionFieldPlaceOrder_calculus k F v
    have hzne : u v *ᵥ (g v *ᵥ x) ≠ 0 := fun h0 => hdu v (Matrix.exists_mulVec_eq_zero_iff.1 ⟨_, hy v, h0⟩)
    obtain ⟨i, hi, -, hoi, -⟩ := hmax _ _ hzne
    have hi0 : i = 0 := by
      induction i using Fin.cases with
      | zero => rfl
      | succ j => exact absurd (hz v j) hi
    subst hi0
    have e1 : ordVec v (g v *ᵥ x) = ordVec v (u v *ᵥ (g v *ᵥ x)) := by
      simp only [ordVec, hnrm _ _ _ (hu v)]
    rw [e1, hoi, hcol0]

  have hpt : ∀ v, ord v (g v).det + ord v h.det = ord v ((u v * g v * h) 0 0) + ord v ((u v * g v * h).submatrix Fin.succ Fin.succ).det := by
    intro v
    obtain ⟨hmul, -, -, hord1, -⟩ := GlobalTheory.T.functionFieldPlaceOrder_calculus k F v
    have e1 := hmul _ _ (h00 v) (hdS v)
    rw [← hdetA, Matrix.det_mul, Matrix.det_mul, hmul _ _ (mul_ne_zero (hdu v) (hg.1 v)) hdet,
      hmul _ _ (hdu v) (hg.1 v), (hord1 _ (hdu v)).1 (hu v).2, zero_add] at e1
    exact e1
  have fg : (Function.support fun v => ord v (g v).det).Finite := (GlobalTheory.T.admissibleAdelicMatrixFamily_orders_finite k F hF _ g hg).1
  have fh : (Function.support fun v : Place k F => ord v h.det).Finite := by
    refine (GlobalTheory.T.functionField_finite_support_sum_order_eq_zero k F hF _ hdet).1.subset fun v hv h1 => hv ?_
    exact ((GlobalTheory.T.functionFieldPlaceOrder_calculus k F v).2.2.2.1 _ hdet).1 h1
  have fc : (Function.support fun v => ord v ((u v * g v * h) 0 0)).Finite := by
    refine ((GlobalTheory.T.admissibleAdelicMatrixFamily_orders_finite k F hF _ g hg).2 x hx).1.subset fun v hv h1 => hv ?_
    show ord v ((u v * g v * h) 0 0) = 0
    rw [← hov, ordVec, h1]; simp
  have fd : (Function.support fun v => ord v ((u v * g v * h).submatrix Fin.succ Fin.succ).det).Finite := by
    refine ((fg.union fh).union fc).subset fun v hv => ?_
    by_contra hc
    simp only [Set.mem_union, Function.mem_support, not_or, not_not] at hc hv
    have := hpt v
    rw [hc.1.1, hc.1.2, hc.2] at this
    exact hv (by linarith)
  have hline : ∑ᶠ v, ord v ((u v * g v * h) 0 0) = degLine g x := by
    unfold degLine; exact finsum_congr fun v => (hov v).symm
  refine ⟨h, u, hdet, hu, hz', ⟨hdA, ?_⟩, ⟨hdS, ?_⟩, ?_, hline, ?_⟩
  · refine ((hg.2).union (GlobalTheory.IwaFam.unimod_ae hF h hdet)).subset fun v hv => ?_
    by_contra hc
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hc hv
    obtain ⟨-, -, -, -, -, -, -, -, -, hprod⟩ := GlobalTheory.T.functionFieldPlaceOrder_calculus k F v
    exact hv ((hprod _ _ _ ((hprod _ _ _ (hu v) hc.1).1) hc.2).1)
  · refine ((hg.2).union (GlobalTheory.IwaFam.unimod_ae hF h hdet)).subset fun v hv => ?_
    by_contra hc
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hc hv
    obtain ⟨-, -, -, -, -, -, -, -, -, hprod⟩ := GlobalTheory.T.functionFieldPlaceOrder_calculus k F v
    have hA := (hprod _ _ _ ((hprod _ _ _ (hu v) hc.1).1) hc.2).1
    refine hv ⟨fun i j => hA.1 i.succ j.succ, ?_⟩
    have e := hA.2
    rw [hdetA, Valuation.map_mul] at e
    exact GlobalTheory.IwaFam.eq_one_of_mul (hA.1 0 0)
      (GlobalTheory.IwaFam.val_det_le_one v _ fun i j => hA.1 i.succ j.succ) e
  · unfold deg
    rw [← hline, ← finsum_add_distrib fc fd, ← add_zero (∑ᶠ v, ord v (g v).det), ← (GlobalTheory.T.functionField_finite_support_sum_order_eq_zero k F hF _ hdet).2,
      ← finsum_add_distrib fg fh]
    exact finsum_congr hpt
  · intro b hb E _ _ _ _ _ ρ hρ w hw
    let h' := h.map (algebraMap F E)
    have hne : h' *ᵥ w ≠ 0 := fun h0 => by
      have e : h'.det = algebraMap F E h.det := (RingHom.map_det _ _).symm
      exact (map_ne_zero _).2 hdet (e ▸ Matrix.exists_mulVec_eq_zero_iff.1 ⟨w, hw, h0⟩)
    have e : degLine (pullAd ρ fun v => u v * g v * h) w = degLine (pullAd ρ g) (h' *ᵥ w) := by
      unfold degLine
      exact finsum_congr fun p => GlobalTheory.IwaFam.ordVec_pull ρ hρ u g (fun _ => h) hu p w
    rw [e]
    exact hb E ρ hρ _ hne
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IwasawaDecompositionAdmissibleFamilyStatement
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iwasawa_decomposition_admissible_family : ∀ (k F : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Algebra k F], IsFF k F →
  ∀ (r : ℕ) (g : Place k F → Matrix (Fin (r + 1)) (Fin (r + 1)) F), admitted g → ∀ x : Fin (r + 1) → F, x ≠ 0 → ∃ (h : Matrix (Fin (r + 1)) (Fin (r + 1)) F) (u : Place k F → Matrix (Fin (r + 1)) (Fin (r + 1)) F), h.det ≠ 0 ∧ (∀ v, Unimod v (u v)) ∧ (∀ (v : Place k F) (i : Fin r), (u v * g v * h) i.succ 0 = 0) ∧ admitted (fun v => u v * g v * h) ∧ admitted (fun v => (u v * g v * h).submatrix Fin.succ Fin.succ) ∧ deg g = degLine g x + deg (fun v => (u v * g v * h).submatrix Fin.succ Fin.succ) ∧ ∑ᶠ v, ord v ((u v * g v * h) 0 0) = degLine g x ∧ ∀ b : ℝ, LinesLE g b → LinesLE (fun v => u v * g v * h) b := by
  first | exact @GlobalTheory.iwasawa_family | exact GlobalTheory.iwasawa_family | (intros; apply GlobalTheory.iwasawa_family <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicMatrixFamilyDegreeLeRankMulLineBound
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

namespace GlobalTheory.Nef

theorem deg_le_rank_mul_of_linesLE : ∀ (r : ℕ) (k F : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Algebra k F], IsFF k F → ∀ g : Place k F → Matrix (Fin r) (Fin r) F, admitted g → ∀ b : ℝ, LinesLE g b → (deg g : ℝ) ≤ r * b := by
  intro r
  induction r with
  | zero =>
    intro k F _ _ _ _ _ _ g _ b _
    have : deg g = 0 := by simp [deg, ord, Matrix.det_isEmpty]
    simp [this]
  | succ r ih =>
    intro k F _ _ _ _ _ hF g hg b hb

    set S : Set ℝ := {c | LinesLE g c} with hS
    have hbS : b ∈ S := hb

    have hbdd : BddBelow S := by
      refine ⟨(degLine (pullAd (id : Place k F → Place k F) g) (Pi.single 0 1) : ℝ), ?_⟩
      intro c hc
      have hres : IsRes (k := k) (F := F) (E := F) (id : Place k F → Place k F) := by
        intro p x; rfl
      have h1 := hc F id hres (Pi.single 0 1) (by
        intro h; have := congrFun h 0; simp at this)
      simpa [Module.finrank_self] using h1
    set a := sInf S with ha
    have hab : a ≤ b := csInf_le hbdd hbS
    have haS : LinesLE g a := by
      intro E _ _ _ _ _ ρ hρ w hw
      have hn : (0 : ℝ) < Module.finrank F E := by exact_mod_cast Module.finrank_pos
      have : (degLine (pullAd ρ g) w : ℝ) / Module.finrank F E ≤ a := by
        refine le_csInf ⟨b, hbS⟩ ?_
        intro c hc
        rw [div_le_iff₀ hn]
        exact hc E ρ hρ w hw
      rwa [div_le_iff₀ hn] at this
    have key : ∀ ε : ℝ, 0 < ε → (deg g : ℝ) ≤ (r + 1) * a + r * ε := by
      intro ε hε
      have hnot : ¬ LinesLE g (a - ε) := fun h => by
        have := csInf_le hbdd (show a - ε ∈ S from h); linarith
      simp only [LinesLE, not_forall, not_le] at hnot
      obtain ⟨E, _, _, _, _, _, ρ, hρ, x, hx, hlt⟩ := hnot
      have hn : (0 : ℝ) < Module.finrank F E := by exact_mod_cast Module.finrank_pos
      obtain ⟨hGadm, hGdeg, -, hGlines⟩ := GlobalTheory.T.isAdmissibleAdelicMatrixFamily_pullback_extension k F E hF ρ hρ (r + 1) g hg
      have hE : IsFF k E := (GlobalTheory.T.functionFieldOneVariable_transcendental_finite_and_ext k F hF).2 E
      have hLG : LinesLE (pullAd ρ g) (a * Module.finrank F E) := hGlines a haS
      have hδle : (degLine (pullAd ρ g) x : ℝ) ≤ a * Module.finrank F E := haS E ρ hρ x hx
      obtain ⟨h, u, -, -, hzero, hadm', hadmq, hdeg, hsum, hlines⟩ :=
        GlobalTheory.T.iwasawa_decomposition_admissible_family k E hE r (pullAd ρ g) hGadm x hx
      have hLq := GlobalTheory.T.quotient_line_degree_le_of_triangular_family k E hE r (fun v => u v * pullAd ρ g v * h) hadm' hzero hadmq
        (a * Module.finrank F E) (hlines _ hLG)
      rw [hsum] at hLq
      have hq := ih k E hE _ hadmq _ hLq
      have hdegZ : (Module.finrank F E : ℤ) * deg g =
          degLine (pullAd ρ g) x + deg (fun v => (u v * pullAd ρ g v * h).submatrix Fin.succ Fin.succ) := by
        rw [← hGdeg, hdeg]
      have hdegR : (Module.finrank F E : ℝ) * (deg g : ℝ) =
          (degLine (pullAd ρ g) x : ℝ) + (deg (fun v => (u v * pullAd ρ g v * h).submatrix Fin.succ Fin.succ) : ℝ) := by
        exact_mod_cast hdegZ
      set n : ℝ := (Module.finrank F E : ℝ)
      set δ : ℝ := (degLine (pullAd ρ g) x : ℝ)
      have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
      have h2 : (r : ℝ) * (a * n - δ) ≤ r * (ε * n) := by
        apply mul_le_mul_of_nonneg_left _ hr; nlinarith
      have h3 : n * (deg g : ℝ) ≤ n * ((r + 1) * a + r * ε) := by nlinarith
      exact le_of_mul_le_mul_left h3 hn
    have hfin : (deg g : ℝ) ≤ (r + 1) * a := by
      refine le_of_forall_pos_le_add fun ε hε => ?_
      have := key (ε / (r + 1)) (by positivity)
      have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
      have : (r : ℝ) * (ε / (r + 1)) ≤ ε := by
        rw [mul_div_assoc']; rw [div_le_iff₀ (by positivity)]; nlinarith
      linarith
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ) r]

end GlobalTheory.Nef
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicMatrixFamilyDegreeLeRankMulLineBoundStatement
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicMatrixFamilyDegree_le_rank_mul_line_bound : ∀ (r : ℕ) (k F : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Algebra k F], IsFF k F → ∀ g : Place k F → Matrix (Fin r) (Fin r) F, admitted g → ∀ b : ℝ, LinesLE g b → (deg g : ℝ) ≤ r * b := by
  first | exact @GlobalTheory.Nef.deg_le_rank_mul_of_linesLE | exact GlobalTheory.Nef.deg_le_rank_mul_of_linesLE | (intros; apply GlobalTheory.Nef.deg_le_rank_mul_of_linesLE <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieSheafSemiAbelianSemiNegOfIsAlgClosed
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

set_option autoImplicit false

namespace GlobalTheory.Nef

theorem exists_isGenOver (k : Type) [Field k] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)] (h : IsCurve k C) :
    ∃ (K : Type) (_ : Field K) (_ : Algebra k K) (x : Sp K ⟶ C), IsGenOver k x := by
  have := LieSemineg.isIntegral_curve h.1 h.2.2
  let x : Sp C.functionField ⟶ C := C.fromSpecStalk (genericPoint C)
  let φ : CommRingCat.of k ⟶ CommRingCat.of C.functionField := Spec.preimage (x ≫ strHom k C)
  refine ⟨C.functionField, inferInstance, φ.hom.toAlgebra, x, h, isGen_fromSpecStalk C, ?_⟩
  exact (Spec.map_preimage (x ≫ strHom k C)).symm

theorem semiNeg_lie_of_isAlgClosed : ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)], IsCurve k C → ∀ (G : Over C) [GrpObj G], IsSemiAbelian G → SemiNeg k (Lie G) := by
  intro k _ _ _ C _ h G _ hG W r hW i hi
  obtain ⟨K, _, _, x, hx⟩ := exists_isGenOver k C h
  obtain ⟨V₀, s, g, hV, hs, hg, hl⟩ := GlobalTheory.T.exists_genericFrame_and_localFrames_allPlaces k K C x hx W r hW
  have hL := GlobalTheory.T.lie_subsheaf_lines_degree_nonpos k K C x hx G hG W r i hi V₀ s g hV hs hg hl
  have hd := GlobalTheory.T.adelicMatrixFamilyDegree_le_rank_mul_line_bound r k K (GlobalTheory.T.isFunctionFieldOfOneVariable_of_genericPointOfCurve k K C x hx) g hg 0 hL
  rw [mul_zero] at hd
  exact GlobalTheory.T.detDegree_nonpos_of_adelicDegree_nonpos k K C x hx W r hW V₀ s g hV hs hg hl (by exact_mod_cast hd)

end GlobalTheory.Nef
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieSheafSemiAbelianSemiNegOfIsAlgClosedStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lieSheaf_semiAbelian_semiNeg_of_isAlgClosed : ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)], IsCurve k C → ∀ (G : Over C) [GrpObj G], IsSemiAbelian G → SemiNeg k (Lie G) := by
  first | exact @GlobalTheory.Nef.semiNeg_lie_of_isAlgClosed | exact GlobalTheory.Nef.semiNeg_lie_of_isAlgClosed | (intros; apply GlobalTheory.Nef.semiNeg_lie_of_isAlgClosed <;> assumption)
end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Nef

theorem semiAbelianLieSeminegative : GlobalTheory.Published.SemiAbelianLieSeminegative := by
  intro k _ _ C _ hs hp hc G _ hG W r hW i hi
  obtain ⟨C', _, π, hC', hdesc⟩ := GlobalTheory.T.semiNegative_descends_fieldExtension_curve k C ⟨hs, hp, hc⟩ (AlgebraicClosure k)
  have : IsIntegral C := GlobalTheory.LieSemineg.isIntegral_curve hs hc
  refine hdesc (Lie G) ?_ W r hW i hi
  exact GlobalTheory.NeronCurve.LieDescent.semiNeg_of_iso (GlobalTheory.NeronCurve.LieDescent.lieBaseIso π G).symm
    (GlobalTheory.T.lieSheaf_semiAbelian_semiNeg_of_isAlgClosed (AlgebraicClosure k) C' hC' _ (IsSemiAbelian.pullback π G hG))

end GlobalTheory.Nef
