module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClassicalThetaDescriptionAbelianPart
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRealCoords
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvTEqTerm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetFamilyDeriv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralLabels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmulIntZSqNonnegOfSqDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TermsumTrFacDifferentiable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThJetOfNormalForm

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKeyInClassicalFrame
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.KeyOfPeriod

theorem exists_keyIn_classicalFrame :
    ∀ (g : ℕ) (τ₀ : Matrix (Fin g) (Fin g) ℂ) (a₀ b₀ : Fin g → ℂ), 1 ≤ g → τ₀.IsSymm → (τ₀.map Complex.im).PosDef → (∀ i, a₀ i = 0 ∨ a₀ i = 1 / 2) → (∀ i, b₀ i = 0 ∨ b₀ i = 1 / 2) → ∃ (x : KeyIn ℂ) (h : x.P.g = g) (u : HolUnif x.P.A x.P.L x.P.g) (τ : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (a b : Fin x.P.g → ℂ), τ = τ₀.submatrix (Fin.cast h) (Fin.cast h) ∧ (a = fun i => a₀ (i.cast h)) ∧ (b = fun i => b₀ (i.cast h)) ∧ τ.IsSymm ∧ (τ.map Complex.im).PosDef ∧ (∀ i, a i = 0 ∨ a i = 1 / 2) ∧ (∀ i, b i = 0 ∨ b i = 1 / 2) ∧ (∀ z, z ∈ u.Λ ↔ ∃ m n : Fin x.P.g → ℤ, z = (fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ))) ∧ u.IsRig x.rig ∧ u.IsFn x.th (thetaChar τ a b) ∧ (∀ i, u.IsDiff (Pi.single i (2 * Real.pi * Complex.I)⁻¹) (x.v i)) := by
  intro g τ₀ a₀ b₀ hg hs hp ha hb
  obtain ⟨x, h, hx⟩ := exists_keyIn_normalAt GlobalTheory.thetaUnifAV_all GlobalTheory.torusAlgebraic_holds g τ₀ a₀ b₀ hg hs hp
    ⟨ha, hb⟩
  obtain ⟨u, h₁, h₂, h₃, h₄, h₅, h₆⟩ := (GlobalTheory.KeyPow.normalAt_one_iff x _ _ _).1 hx
  exact ⟨x, h, u, _, _, _, rfl, rfl, rfl, h₁, h₂, fun i => ha _, fun i => hb _, h₃, h₄, h₅, h₆⟩

end GlobalTheory.KeyOfPeriod
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DimensionZeroCase
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

noncomputable section

namespace GlobalTheory.MBLow.DimZero

section Basics

variable {R : Type} [CommRing R] [IsDomain R]

theorem isIso_hom (D : DegPre R) (hg : D.P.g = 0) : IsIso D.P.A.hom :=
  GlobalTheory.ZM.Model.isIso_of_dim_zero D.P.A D.P.isAb (hg ▸ D.P.smoothDim)

theorem hom_subsingleton (D : DegPre R) (hg : D.P.g = 0) (T : Over (Sp R)) : Subsingleton (T ⟶ D.P.A) := by
  haveI := isIso_hom D hg
  refine ⟨fun f f' => Over.OverMorphism.ext ?_⟩
  rw [← cancel_mono D.P.A.hom, Over.w f, Over.w f']

theorem subsingleton_A {F : Type} [Field F] [Algebra (FractionRing R) F] {D : DegPre R} {N : NumD F} (ν : NumOf D F N)
    (hg : D.P.g = 0) : Subsingleton N.A := by
  haveI := hom_subsingleton D hg (TF (R := R) F)
  exact ⟨fun x y => ν.eA.injective (Subsingleton.elim _ _)⟩

theorem th_one_ne_zero {F : Type} [Field F] [Algebra (FractionRing R) F] {D : DegPre R} {N : NumD F} (ν : NumOf D F N)
    (hg : D.P.g = 0) : N.th 1 ≠ 0 := by
  haveI : IsIso D.P.A.hom := isIso_hom D hg
  have he : eSec D.P.A ≫ D.P.A.hom = 𝟙 _ := Over.w η[D.P.A]
  have he' : D.P.A.hom ≫ eSec D.P.A = 𝟙 _ := by
    rw [← cancel_mono D.P.A.hom, Category.assoc, Category.id_comp]
    exact (congrArg _ he).trans (Category.comp_id _)
  obtain ⟨s, hs⟩ := GlobalTheory.MBLow.AbKey.exists_unit_sec D.P.L (D.P.A.hom ≫ eSec D.P.A) he'
    (LB.pullGen D.P.L (fun _ : PUnit => eSec D.P.A) (fun _ => 1) D.rig D.P.A.hom)
    (DVR.pullGen_isGen _ _ _ _ D.rig_gen _)
  obtain ⟨r, hr⟩ := ν.th_gen s
  have hu : ∀ j, IsUnit (ν.th.f j) := fun j => isUnit_of_mul_isUnit_right (hr j ▸ hs j)
  intro h0
  have h := ν.th_eq 1
  rw [h0, zero_mul] at h
  have hU : ⊤ ≤ (ν.eA 1).left ⁻¹ᵁ D.P.L.U (ν.J (ν.eA 1).left) := ν.good _
  have hx : ⊤ ≤ (ν.eA 1).left ⁻¹ᵁ LB.wchart D.P.L (fun _ : Fin 1 => 𝟙 D.P.A.left)
      (fun _ => ν.J ((ν.eA 1).left ≫ 𝟙 _)) := fun y hy => Set.mem_iInter.2 fun _ => by
    rw [Category.comp_id]; exact hU hy
  unfold sF valF at h
  rw [dite_eq_left hx] at h
  exact (((hu _).map _).map _).ne_zero h.symm

end Basics

section Classical

variable {g : ℕ}

theorem dot_empty [IsEmpty (Fin g)] (u v : Fin g → ℂ) : u ⬝ᵥ v = 0 := by
  simp [dotProduct]

theorem thetaChar_empty [IsEmpty (Fin g)] (τ : Matrix (Fin g) (Fin g) ℂ) (a b z : Fin g → ℂ) :
    thetaChar τ a b z = 1 := by
  unfold thetaChar
  rw [tsum_fintype, Fintype.sum_unique]
  simp [dot_empty]

theorem autV_empty [IsEmpty (Fin g)] (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (M N : Fin g → ℤ) (z : Fin g → ℂ) :
    autV τ a b M N z = 1 := by
  simp [autV, dot_empty]

theorem posDef_empty [IsEmpty (Fin g)] (A : Matrix (Fin g) (Fin g) ℝ) : A.PosDef :=
  ⟨by ext i; exact isEmptyElim i, fun x hx => (hx (Subsingleton.elim _ _)).elim⟩

theorem differentiableOn_empty [IsEmpty (Fin g)] (f : (Fin g → ℂ) → ℂ) (s : Set (Fin g → ℂ)) :
    DifferentiableOn ℂ f s := fun x _ =>
  ((hasFDerivAt_const (f x) x).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun y => congrArg f (Subsingleton.elim y x))).differentiableAt.differentiableWithinAt

def abZero (B : NumB ℂ) (g : ℕ) (hg : g = 0) (hA : Subsingleton B.A) (hth : B.th 1 ≠ 0) : AB B g where
  τ := 0
  a := 0
  b := 0
  c := B.th 1
  symm := by ext i; haveI : IsEmpty (Fin g) := hg ▸ inferInstance; exact isEmptyElim i
  pos := by haveI : IsEmpty (Fin g) := hg ▸ inferInstance; exact posDef_empty _
  ha i := by haveI : IsEmpty (Fin g) := hg ▸ inferInstance; exact isEmptyElim i
  hb i := by haveI : IsEmpty (Fin g) := hg ▸ inferInstance; exact isEmptyElim i
  hc := hth
  ex _ := 1
  ex_add _ _ := (mul_one 1).symm
  onto x := ⟨0, Subsingleton.elim _ _⟩
  ker z := by
    haveI : IsEmpty (Fin g) := hg ▸ inferInstance
    exact ⟨fun _ => ⟨0, 0, Subsingleton.elim _ _⟩, fun _ => rfl⟩
  fr _ := 1
  fr_zero := rfl
  fr_per M N z := by
    haveI : IsEmpty (Fin g) := hg ▸ inferInstance
    simp [autV_empty]
  th z := by
    haveI : IsEmpty (Fin g) := hg ▸ inferInstance
    simp [thetaChar_empty]

end Classical

section Geo

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} [Algebra (FractionRing R) ℂ] {N : NumD ℂ} {g : ℕ}

theorem valF_eq_valR {F : Type} [Field F] {X : Scheme.{0}} (x : Sp F ⟶ X) (U : X.Opens) (f : Γ(X, U)) :
    valF x U f = valR x U f := rfl

theorem val_res {X : Scheme.{0}} {U V : X.Opens} (e : V ≤ U) (u : Γ(X, U)ˣ) : (res e u).val = resG X e u.val := rfl

def frZ (ν : NumOf D ℂ N) (i : D.P.L.ι) : ℂ :=
  valF (ν.eA 1).left (D.P.L.U i ⊓ D.P.L.U (ν.J (ν.eA 1).left)) (D.P.L.g i (ν.J (ν.eA 1).left)).val * ν.rg

theorem frZ_compat (ν : NumOf D ℂ N) (i j : D.P.L.ι) (h : ⊤ ≤ (ν.eA 1).left ⁻¹ᵁ (D.P.L.U i ⊓ D.P.L.U j)) :
    frZ ν i = valF (ν.eA 1).left (D.P.L.U i ⊓ D.P.L.U j) (D.P.L.g i j).val * frZ ν j := by
  unfold frZ
  set x := (ν.eA 1).left
  set k := ν.J x
  have hk : ⊤ ≤ x ⁻¹ᵁ D.P.L.U k := ν.good x
  have h3 : ⊤ ≤ x ⁻¹ᵁ (D.P.L.U i ⊓ D.P.L.U j ⊓ D.P.L.U k) := fun y hy => ⟨h hy, hk hy⟩
  have c := congrArg (fun u => valR x _ (Units.val u)) (D.P.isLB.cocycle i j k)
  simp only [Units.val_mul] at c
  rw [GlobalTheory.ZH.CrdCalc.valR_mul x _ h3, val_res, val_res, val_res, GlobalTheory.ZH.CrdCalc.valR_res x _ h3,
    GlobalTheory.ZH.CrdCalc.valR_res x _ h3, GlobalTheory.ZH.CrdCalc.valR_res x _ h3] at c
  simp only [valF_eq_valR]
  rw [← c]
  ring

theorem frZ_self (ν : NumOf D ℂ N) : frZ ν (ν.J (ν.eA 1).left) = ν.rg := by
  unfold frZ
  set x := (ν.eA 1).left
  set k := ν.J x
  have hk : ⊤ ≤ x ⁻¹ᵁ D.P.L.U k := ν.good x
  have c := congrArg (fun u => valR x _ (Units.val u)) (D.P.isLB.g_self k)
  simp only [val_res, Units.val_one] at c
  rw [GlobalTheory.ZH.CrdCalc.valR_res x _ hk, GlobalTheory.ZH.CrdCalc.valR_eq x _ hk, map_one] at c
  rw [valF_eq_valR, c, _root_.one_mul]

theorem isD_zero (ν : NumOf D ℂ N) (hg : D.P.g = 0) (d : AB N.toNumB g) (b : TE R ℂ ⟶ D.P.A) : IsD ν d 0 b := by
  haveI := hom_subsingleton D hg (TE R ℂ)
  intro U f hU
  have hb : b = (Over.homMk (spMap (algebraMap ℂ (DualNumber ℂ))) rfl : TE R ℂ ⟶ TF (R := R) ℂ) ≫ ν.eA (d.ex 0) :=
    Subsingleton.elim _ _
  have hl : (lift (Over.homMk (spMap (algebraMap ℂ (DualNumber ℂ))) rfl : TE R ℂ ⟶ TF (R := R) ℂ) b).left =
      spMap (algebraMap ℂ (DualNumber ℂ)) ≫ ptB ν d 0 := by
    rw [hb]
    have e : lift (Over.homMk (spMap (algebraMap ℂ (DualNumber ℂ))) rfl : TE R ℂ ⟶ TF (R := R) ℂ)
        ((Over.homMk (spMap (algebraMap ℂ (DualNumber ℂ))) rfl : TE R ℂ ⟶ TF (R := R) ℂ) ≫ ν.eA (d.ex 0)) =
        (Over.homMk (spMap (algebraMap ℂ (DualNumber ℂ))) rfl : TE R ℂ ⟶ TF (R := R) ℂ) ≫
          lift (𝟙 (TF (R := R) ℂ)) (ν.eA (d.ex 0)) := by
      rw [comp_lift, Category.comp_id]
    rw [e]
    rfl
  rw [hl, (GlobalTheory.ZH.CrdCalc.valR_spMap _ _ U hU).2, map_zero, TrivSqZeroExt.inr_zero, add_zero,
    TrivSqZeroExt.algebraMap_eq_inl]
  rfl

def geoZero (ν : NumOf D ℂ N) (hg : D.P.g = 0) (d : AB N.toNumB g) (hg' : g = 0) (hex : ∀ z, d.ex z = 1)
    (hfr : ∀ z, d.fr z = 1) : Geo ν d where
  frG i _ := frZ ν i
  hol U f := by
    haveI : IsEmpty (Fin g) := hg' ▸ inferInstance
    exact ⟨isOpen_discrete _, differentiableOn_empty _ _⟩
  fr_hol i := by
    haveI : IsEmpty (Fin g) := hg' ▸ inferInstance
    exact differentiableOn_empty _ _
  fr_compat i j z h := by
    rw [hex] at h ⊢
    exact frZ_compat ν i j h
  fr_eq z := by
    rw [hex, hfr, Units.val_one, _root_.one_mul]
    exact (frZ_self ν).symm
  dif b _ := ⟨0, isD_zero ν hg d b⟩

end Geo

section Main

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} [Algebra (FractionRing R) ℂ] {N : NumD ℂ}

theorem keyOK_zero (κ : Rule) (ν : NumOf D ℂ N) (hg : D.P.g = 0) (d : AB N.toNumB D.P.g) (hc : d.c = N.th 1) :
    KeyOK κ ν d := by
  intro vB b MB k₀ _ _ _ hk
  haveI : IsEmpty (Fin D.P.g) := hg ▸ inferInstance
  rw [Matrix.det_isEmpty, one_pow, hc, mul_comm]
  exact ⟨one_ne_zero, hk.1 hg⟩

theorem main : ∀ κ : Rule, AllC fun {R} _ _ {D} _ {N} ν => D.P.g = 0 →
    ∃ (d : AB N.toNumB D.P.g) (_ : Geo ν d), KeyOK κ ν d := by
  intro κ R _ _ _ _ D _ _ _ N ν hg
  let d := abZero N.toNumB D.P.g hg (subsingleton_A ν hg) (th_one_ne_zero ν hg)
  exact ⟨d, geoZero ν hg d hg (fun _ => rfl) (fun _ => rfl), keyOK_zero κ ν hg d rfl⟩

end Main

end GlobalTheory.MBLow.DimZero
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullMulVec
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

namespace GlobalTheory.MBLow.Cl.TwistExp

variable {N : NumD ℂ} {g' r g : ℕ} {bX : Module.Basis (Fin r) ℤ N.X}

theorem full_mulVec (d : CD N g' r bX) (σ : Fin g ≃ Fin g' ⊕ Fin r) (S : Matrix (Fin r) (Fin r) ℂ) (x : Fin g → ℂ) :
    d.full σ S *ᵥ x = d.full σ 0 *ᵥ x + fun i => Sum.elim (0 : Fin g' → ℂ) (S *ᵥ tP σ x) (σ i) := by
  ext i
  simp only [CD.full, Matrix.submatrix_mulVec_equiv, Function.comp_apply, Pi.add_apply, Matrix.fromBlocks_mulVec]
  rcases h : σ i with j | j
  · simp [tP]
  · simp [tP, Matrix.add_mulVec, add_assoc]
    rfl

theorem leftComponent_fullMatrix_mulVec (d : CD N g' r bX) (σ : Fin g ≃ Fin g' ⊕ Fin r) (S : Matrix (Fin r) (Fin r) ℂ) (x : Fin g → ℂ) :
    zP σ (d.full σ S *ᵥ x) = zP σ (d.full σ 0 *ᵥ x) := by
  rw [full_mulVec]; ext i; simp [zP]

theorem secondBlock_full_mulVec (d : CD N g' r bX) (σ : Fin g ≃ Fin g' ⊕ Fin r) (S : Matrix (Fin r) (Fin r) ℂ) (x : Fin g → ℂ) :
    tP σ (d.full σ S *ᵥ x) = tP σ (d.full σ 0 *ᵥ x) + S *ᵥ tP σ x := by
  rw [full_mulVec]; ext i; simp [tP]

theorem dot_full (d : CD N g' r bX) (σ : Fin g ≃ Fin g' ⊕ Fin r) (S : Matrix (Fin r) (Fin r) ℂ) (x : Fin g → ℂ) :
    x ⬝ᵥ d.full σ S *ᵥ x = x ⬝ᵥ d.full σ 0 *ᵥ x + tP σ x ⬝ᵥ S *ᵥ tP σ x := by
  rw [full_mulVec, dotProduct_add]
  congr 1
  simp only [dotProduct]
  rw [← σ.symm.sum_comp, Fintype.sum_sum_type]
  simp [tP]

theorem co_form {k : ℕ} (β : N.Form k) (x y : N.X) :
    co bX x ⬝ᵥ bmat bX β *ᵥ co bX y = (β.be x y : ℂ) := by
  conv_rhs => rw [← bX.sum_repr x, ← bX.sum_repr y]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, LinearMap.sum_apply, map_zsmul, LinearMap.smul_apply, smul_eq_mul, dotProduct, mulVec, co, bmat,
    Matrix.of_apply, Int.cast_sum, Int.cast_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun l' _ => ?_
  ring

theorem co_sum (σ : Fin g ≃ Fin g' ⊕ Fin r) (Nn : Fin g → ℤ) :
    co bX (∑ l, tP σ Nn l • bX l) = tP σ (cv Nn) := by
  ext l; simp [co, tP, cv, Finsupp.single_apply]

end GlobalTheory.MBLow.Cl.TwistExp

namespace GlobalTheory.MBLow.Cl.TwistExp
open GlobalTheory.MBLow.Cl.TwistExp

theorem main_eq {N : NumD ℂ} {g' r g : ℕ} {bX : Module.Basis (Fin r) ℤ N.X} (d : CD N g' r bX)
    (σ : Fin g ≃ Fin g' ⊕ Fin r) (k m : ℕ) (β : N.Form k) (hm : 1 ≤ m) (hk : m ^ 2 ∣ k) (w : ℂ) (M Nn : Fin g → ℤ)
    (χ : N.X) (Z : Fin g → ℂ) :
    d.term σ (w • bmat bX β) m M Nn χ Z = d.term σ 0 m M Nn χ Z * Complex.exp ((2 * Real.pi * Complex.I : ℂ) * w) ^
      (β.be ((∑ l, tP σ Nn l • bX l) + m • χ) ((∑ l, tP σ Nn l • bX l) + m • χ) / (2 * m ^ 2)).toNat := by
  set S := w • bmat bX β with hS
  have hz : ∀ S' : Matrix (Fin r) (Fin r) ℂ, zP σ ((m:ℂ) • Z + (m:ℂ)⁻¹ • perV (d.full σ S') M Nn) =
      zP σ ((m:ℂ) • Z + (m:ℂ)⁻¹ • perV (d.full σ 0) M Nn) := fun S' => by
    ext i
    have := congrFun (leftComponent_fullMatrix_mulVec d σ S' (cv Nn)) i
    simp only [zP, perV, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
    rw [this]
  have ht : tP σ ((m:ℂ) • Z + (m:ℂ)⁻¹ • perV (d.full σ S) M Nn) =
      tP σ ((m:ℂ) • Z + (m:ℂ)⁻¹ • perV (d.full σ 0) M Nn) + (m:ℂ)⁻¹ • (S *ᵥ tP σ (cv Nn)) := by
    ext i
    have := congrFun (secondBlock_full_mulVec d σ S (cv Nn)) i
    simp only [tP, perV, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
    rw [this]; ring
  unfold CD.term trFac CD.fj
  rw [hz S, ht, dot_full d σ S (cv Nn)]

  set y : N.X := ∑ l, tP σ Nn l • bX l with hy
  have hn : tP σ (cv Nn) = co bX y := (co_sum σ Nn).symm
  have hSv : ∀ u v : Fin r → ℂ, ∀ x x' : N.X, u = co bX x → v = co bX x' → u ⬝ᵥ S *ᵥ v = w * (β.be x x' : ℂ) := by
    intro u v x x' hu hv
    rw [hS, Matrix.smul_mulVec, dotProduct_smul, hu, hv, co_form, smul_eq_mul]
  have h1 := hSv _ _ y y hn hn
  have h2 := hSv _ _ χ χ rfl rfl
  have h3 := hSv _ _ χ y rfl hn
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have hsymm : β.be y χ = β.be χ y := β.symm y χ
  have hα : β.be (y + m • χ) (y + m • χ) = β.be y y + 2 * m * β.be χ y + m ^ 2 * β.be χ χ := by
    simp only [map_add (f := _), map_nsmul, LinearMap.add_apply, LinearMap.smul_apply, nsmul_eq_mul, hsymm]; ring
  have hdvd : (2 * m ^ 2 : ℤ) ∣ β.be (y + m • χ) (y + m • χ) :=
    (mul_dvd_mul_left 2 (by exact_mod_cast hk)).trans (β.dvd _ _)
  have hnn : 0 ≤ β.be (y + m • χ) (y + m • χ) := by
    by_cases h0 : y + m • χ = 0
    · rw [h0]; simp
    · exact (β.pos _ h0).le
  have hK : (((β.be (y + m • χ) (y + m • χ) / (2 * m ^ 2)).toNat : ℕ) : ℂ) =
      ((β.be y y : ℂ) + 2 * m * β.be χ y + m ^ 2 * β.be χ χ) / (2 * m ^ 2) := by
    obtain ⟨q, hq⟩ := hdvd
    have hm2 : (2 * m ^ 2 : ℤ) ≠ 0 := by positivity
    have hq0 : 0 ≤ q := by
      rw [hq] at hnn
      have hp : (0:ℤ) < 2 * m ^ 2 := by positivity
      by_contra hc; push_neg at hc
      have := mul_neg_of_pos_of_neg hp hc; linarith
    rw [hq, Int.mul_ediv_cancel_left _ hm2]
    have : ((q.toNat : ℕ) : ℂ) = (q : ℂ) := by exact_mod_cast Int.toNat_of_nonneg hq0
    rw [this, eq_div_iff (by simpa using hm0)]
    have hc : ((β.be (y + m • χ) (y + m • χ) : ℤ) : ℂ) = ((2 * m ^ 2 * q : ℤ) : ℂ) := by rw [hq]
    rw [hα] at hc; push_cast at hc; linear_combination -hc
  have key : ∀ a b a' b' f t : ℂ, a + b = a' + b' + f →
      Complex.exp a * (Complex.exp b * t) = Complex.exp a' * (Complex.exp b' * t) * Complex.exp f := by
    intro a b a' b' f t h
    have : Complex.exp a * Complex.exp b = Complex.exp a' * Complex.exp b' * Complex.exp f := by
      rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add, h]
    linear_combination t * this
  rw [← Complex.exp_nat_mul]
  refine key _ _ _ _ _ _ ?_
  simp only [Matrix.add_mulVec, dotProduct_add, dotProduct_smul, smul_eq_mul, add_zero, Matrix.zero_mulVec,
    dotProduct_zero, h1, h2, h3, hK]
  field_simp
  ring

end GlobalTheory.MBLow.Cl.TwistExp

namespace GlobalTheory.MBLow.Cl.TwistExp

theorem term_differentiable {N : NumD ℂ} {g' r g : ℕ} {bX : Module.Basis (Fin r) ℤ N.X} (d : CD N g' r bX)
    (σ : Fin g ≃ Fin g' ⊕ Fin r) (S : Matrix (Fin r) (Fin r) ℂ) (m : ℕ) (M Nn : Fin g → ℤ) (χ : N.X) :
    Differentiable ℂ (d.term σ S m M Nn χ) := by
  have hθ := (thetaChar_entire_ne_zero_automorphy g' d.τ d.a d.b d.symm d.pos d.ha d.hb).1
  have hzP : Differentiable ℂ (fun Z : Fin g → ℂ => zP σ Z) := differentiable_pi.2 fun i => differentiable_apply _
  have htP : Differentiable ℂ (fun Z : Fin g → ℂ => tP σ Z) := differentiable_pi.2 fun i => differentiable_apply _
  have hdot : ∀ {n : Type} [Fintype n] (v : n → ℂ), Differentiable ℂ (fun Z : n → ℂ => v ⬝ᵥ Z) := by
    intro n _ v
    simp only [dotProduct]
    fun_prop
  have haff : Differentiable ℂ (fun Z : Fin g → ℂ => (m : ℂ) • Z + (m : ℂ)⁻¹ • perV (d.full σ S) M Nn) := by fun_prop
  unfold CD.term trFac CD.fj
  have e1 : Differentiable ℂ (fun Z : Fin g → ℂ => thetaChar d.τ d.a d.b
      (zP σ ((m : ℂ) • Z + (m : ℂ)⁻¹ • perV (d.full σ S) M Nn) + d.t12 *ᵥ co bX χ)) :=
    hθ.comp ((hzP.comp haff).add_const _)
  have e2 : Differentiable ℂ (fun Z : Fin g → ℂ => co bX χ ⬝ᵥ (tP σ ((m : ℂ) • Z + (m : ℂ)⁻¹ • perV (d.full σ S) M Nn) + d.b2)) :=
    by have := (hdot (co bX χ)).comp ((htP.comp haff).add_const d.b2); exact this
  have e3 : Differentiable ℂ (fun Z : Fin g → ℂ => cv Nn ⬝ᵥ Z) := hdot _
  refine Differentiable.mul ?_ (Differentiable.mul ?_ e1)
  · fun_prop
  · fun_prop
end GlobalTheory.MBLow.Cl.TwistExp

namespace GlobalTheory.MBLow.Cl

theorem term_smul_bmat : AllCD fun {N} {g'} {r} {g} {bX} d σ => (∀ S m M Nn χ, Differentiable ℂ (d.term σ S m M Nn χ)) ∧ ∀ (k m : ℕ) (β : N.Form k), 1 ≤ m → m ^ 2 ∣ k → ∀ (w : ℂ) (M Nn : Fin g → ℤ) (χ : N.X) (Z : Fin g → ℂ), d.term σ (w • bmat bX β) m M Nn χ Z = d.term σ 0 m M Nn χ Z * Complex.exp ((2 * Real.pi * Complex.I : ℂ) * w) ^ (β.be ((∑ l, tP σ Nn l • bX l) + m • χ) ((∑ l, tP σ Nn l • bX l) + m • χ) / (2 * m ^ 2)).toNat := by
  intro N g' r g bX d σ
  exact ⟨fun S m M Nn χ => TwistExp.term_differentiable d σ S m M Nn χ,
    fun k m β hm hk w M Nn χ Z => TwistExp.main_eq d σ k m β hm hk w M Nn χ Z⟩

end GlobalTheory.MBLow.Cl
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuad
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

noncomputable section

namespace GlobalTheory.MBLow.Cl.PsiFrame

theorem char_ext {X G : Type} [AddCommGroup X] [CommGroup G] {r : ℕ} (bX : Module.Basis (Fin r) ℤ X) (f g : X → G)
    (hf : ∀ a b, f (a + b) = f a * f b) (hg : ∀ a b, g (a + b) = g a * g b) (h : ∀ l, f (bX l) = g (bX l)) (χ : X) :
    f χ = g χ := by
  let F : X →+ Additive G := AddMonoidHom.mk' (fun x => Additive.ofMul (f x)) (fun a b => by simp [hf])
  let G' : X →+ Additive G := AddMonoidHom.mk' (fun x => Additive.ofMul (g x)) (fun a b => by simp [hg])
  have : F.toIntLinearMap = G'.toIntLinearMap := bX.ext fun l => by simp [F, G', h]
  have := LinearMap.congr_fun this χ
  simpa [F, G'] using this

def eu (z : ℂ) : ℂˣ := Units.mk0 (Complex.exp z) (Complex.exp_ne_zero z)

theorem eu_add (z w : ℂ) : eu (z + w) = eu z * eu w := by
  ext; simp [eu, Complex.exp_add]

theorem co_add {X : Type} [AddCommGroup X] {r : ℕ} (bX : Module.Basis (Fin r) ℤ X) (a b : X) :
    co bX (a + b) = co bX a + co bX b := by
  ext l; simp [co]

theorem co_neg {X : Type} [AddCommGroup X] {r : ℕ} (bX : Module.Basis (Fin r) ℤ X) (a : X) :
    co bX (-a) = - co bX a := by
  ext l; simp [co]

theorem co_basis {X : Type} [AddCommGroup X] {r : ℕ} (bX : Module.Basis (Fin r) ℤ X) (l : Fin r) :
    co bX (bX l) = Pi.single l 1 := by
  ext l'
  by_cases h : l' = l
  · subst h; simp [co]
  · simp [co, h, Finsupp.single_apply, Ne.symm h]

theorem exists_quad {X : Type} [AddCommGroup X] {r : ℕ} (bX : Module.Basis (Fin r) ℤ X) (Ψ : X → ℂˣ)
    (hev : ∀ a, Ψ (-a) = Ψ a)
    (hb : ∀ a a' b, Ψ (a + a' + b) / Ψ (a + a') / Ψ b = (Ψ (a + b) / Ψ a / Ψ b) * (Ψ (a' + b) / Ψ a' / Ψ b)) :
    ∃ (t : Matrix (Fin r) (Fin r) ℂ) (b2 : Fin r → ℂ), t.IsSymm ∧ Half b2 ∧ ∀ χ, (Ψ χ : ℂ) =
      Complex.exp (Real.pi * Complex.I * (co bX χ ⬝ᵥ t *ᵥ co bX χ) + 2 * Real.pi * Complex.I * (co bX χ ⬝ᵥ b2)) := by
  classical
  set T : X → X → ℂˣ := fun a b => Ψ (a + b) / Ψ a / Ψ b with hT
  have Ts : ∀ a b, T a b = T b a := fun a b => by simp only [hT, add_comm a b, div_right_comm]
  have Tl : ∀ a a' b, T (a + a') b = T a b * T a' b := hb
  have Tr : ∀ a b b', T a (b + b') = T a b * T a b' := fun a b b' => by rw [Ts, Tl, Ts b, Ts b']
  have hc : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
  let t : Matrix (Fin r) (Fin r) ℂ := Matrix.of fun l l' => Complex.log (T (bX l) (bX l')) / (2 * Real.pi * Complex.I)
  have ts : t.IsSymm := by
    ext l l'; simp [t, Ts (bX l)]
  have hs : ∀ u v : Fin r → ℂ, u ⬝ᵥ t *ᵥ v = v ⬝ᵥ t *ᵥ u := fun u v => by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, ts.eq, dotProduct_comm]
  have TQ : ∀ a b, T a b = eu (2 * Real.pi * Complex.I * (co bX a ⬝ᵥ t *ᵥ co bX b)) := by
    intro a b
    refine char_ext bX (fun a => T a b) (fun a => eu (2 * Real.pi * Complex.I * (co bX a ⬝ᵥ t *ᵥ co bX b)))
      (fun _ _ => Tl _ _ _) (fun _ _ => by rw [co_add, add_dotProduct, mul_add, eu_add]) (fun l => ?_) a
    refine char_ext bX (fun b => T (bX l) b) (fun b => eu (2 * Real.pi * Complex.I * (co bX (bX l) ⬝ᵥ t *ᵥ co bX b)))
      (fun _ _ => Tr _ _ _) (fun _ _ => by rw [co_add, Matrix.mulVec_add, dotProduct_add, mul_add, eu_add])
      (fun l' => ?_) b
    ext
    have : Pi.single l 1 ⬝ᵥ t *ᵥ Pi.single l' 1 = t l l' := by simp
    simp only [co_basis, this, eu, Units.val_mk0, t, Matrix.of_apply]
    rw [mul_div_cancel₀ _ hc, Complex.exp_log (Units.ne_zero _)]
  let φ : X → ℂˣ := fun χ => Ψ χ / eu (Real.pi * Complex.I * (co bX χ ⬝ᵥ t *ᵥ co bX χ))
  have φadd : ∀ a b, φ (a + b) = φ a * φ b := by
    intro a b
    have h1 : Ψ (a + b) = T a b * Ψ a * Ψ b := by
      simp only [hT]; rw [mul_right_comm, div_mul_cancel, div_mul_cancel]
    have h2 : (Real.pi * Complex.I * (co bX (a + b) ⬝ᵥ t *ᵥ co bX (a + b)) : ℂ) =
        2 * Real.pi * Complex.I * (co bX a ⬝ᵥ t *ᵥ co bX b) + Real.pi * Complex.I * (co bX a ⬝ᵥ t *ᵥ co bX a) +
          Real.pi * Complex.I * (co bX b ⬝ᵥ t *ᵥ co bX b) := by
      rw [co_add, Matrix.mulVec_add, add_dotProduct, dotProduct_add, dotProduct_add, hs (co bX b) (co bX a)]
      ring
    simp only [φ]
    rw [h1, h2, eu_add, eu_add, ← TQ, _root_.mul_assoc, _root_.mul_assoc, mul_div_mul_left_eq_div, div_mul_div_comm]
  have φev : ∀ a, φ (-a) = φ a := fun a => by
    simp only [φ, hev, co_neg, Matrix.mulVec_neg, neg_dotProduct, dotProduct_neg, neg_neg]
  have φ0 : φ 0 = 1 := by
    have := φadd 0 0
    rw [add_zero] at this
    exact mul_eq_left.1 this.symm
  have φsq : ∀ a, (φ a : ℂ) = 1 ∨ (φ a : ℂ) = -1 := fun a => by
    have := φadd a (-a)
    rw [add_neg_cancel, φ0, φev] at this
    have h2 : (φ a : ℂ) * φ a = 1 := by rw [← Units.val_mul, ← this, Units.val_one]
    exact mul_self_eq_one_iff.1 h2
  let b2 : Fin r → ℂ := fun l => if (φ (bX l) : ℂ) = 1 then 0 else 1 / 2
  refine ⟨t, b2, ts, fun l => ?_, fun χ => ?_⟩
  · simp only [b2]; split_ifs <;> simp
  · have : φ χ = eu (2 * Real.pi * Complex.I * (co bX χ ⬝ᵥ b2)) := by
      refine char_ext bX φ (fun χ => eu (2 * Real.pi * Complex.I * (co bX χ ⬝ᵥ b2))) φadd
        (fun _ _ => by rw [co_add, add_dotProduct, mul_add, eu_add]) (fun l => ?_) χ
      ext
      simp only [co_basis, single_dotProduct, _root_.one_mul, eu, Units.val_mk0, b2]
      split_ifs with h
      · simp [h]
      · rw [(φsq _).resolve_left h, show (2 * Real.pi * Complex.I * (1 / 2) : ℂ) = Real.pi * Complex.I by ring,
          Complex.exp_pi_mul_I]
    have h2 : Ψ χ = eu (Real.pi * Complex.I * (co bX χ ⬝ᵥ t *ᵥ co bX χ) + 2 * Real.pi * Complex.I * (co bX χ ⬝ᵥ b2)) := by
      rw [eu_add, ← this]; simp only [φ]; rw [mul_div_cancel]
    rw [h2]; rfl

theorem exists_cd (N : NumD ℂ) (g' r : ℕ) (bX : Module.Basis (Fin r) ℤ N.X) (e : AB N.toNumB g') (hc : e.Cub) (hs : e.Sym) :
    ∃ d : CD N g' r bX, d.toAB = e := by
  classical
  choose z hz using fun l => e.onto (N.c (bX l))
  let t12 : Matrix (Fin g') (Fin r) ℂ := Matrix.of fun i l => z l i
  let w : N.X → Fin g' → ℂ := fun χ => t12 *ᵥ co bX χ
  have wadd : ∀ a b, w (a + b) = w a + w b := fun a b => by simp only [w, co_add, Matrix.mulVec_add]
  have wneg : ∀ a, w (-a) = - w a := fun a => by simp only [w, co_neg, Matrix.mulVec_neg]
  have ceq : ∀ χ, N.c χ = e.ex (w χ) := by
    refine char_ext bX N.c (fun χ => e.ex (w χ)) N.c_add (fun a b => by rw [wadd, e.ex_add]) (fun l => ?_)
    rw [← hz]; congr 1
    ext i; simp [w, co_basis, t12]
  obtain ⟨t, b2, ht, hb2, h⟩ := exists_quad bX (fun χ => N.ψ χ * e.fr (w χ))
    (fun a => by
      have h1 := N.even a
      have h2 := hs (w a)
      rw [wneg, ← h2, ← h1, ceq, _root_.mul_assoc])
    (fun a a' b => by
      have h1 := congrArg Additive.ofMul (N.bimult a a' b)
      have h2 := congrArg Additive.ofMul (hc (w a) (w a') (w b))
      apply Additive.ofMul.injective
      simp only [ceq, wadd, ofMul_mul, ofMul_div] at h1 h2 ⊢
      linear_combination (norm := abel) h1 - h2)
  exact ⟨{ toAB := e, cub := hc, sym := hs, t12 := t12, t22 := t, b2 := b2, toricPeriodBlock_isSymm := ht, hb2 := hb2, c_eq := ceq,
           ψ_eq := fun χ => by simpa using h χ }, rfl⟩

end GlobalTheory.MBLow.Cl.PsiFrame

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValRPush
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

noncomputable section

namespace GlobalTheory.MBLow.Cl.DZero

theorem valR_push {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) {X : Scheme.{0}} (x : Sp A ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)) : valR (spMap φ ≫ x) U f = φ (valR x U f) := by
  have h' : ⊤ ≤ (spMap φ ≫ x) ⁻¹ᵁ U := fun p _ => h (Set.mem_univ _)
  rw [valR, valR, dite_eq_left h, dite_eq_left h']
  have e1 : (spMap φ ≫ x).appLE U ⊤ h' = x.appLE U ⊤ h ≫ (spMap φ).appTop := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
  have e2 := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ)
  rw [e1]
  exact congrArg (fun k => k.hom ((x.appLE U ⊤ h).hom f)) e2

theorem isD_zero : AllC fun {R} _ _ {D} _ {N} ν => ∀ (g : ℕ) (d : AB N.toNumB g), IsD ν d 0 (DegPre.zeroT D (TE R ℂ)) := by
  intro R _ _ _ _ D _ _ _ N ν g d U f hU
  have h0 : d.ex 0 = 1 := by
    have := d.ex_add 0 0
    rw [add_zero] at this
    exact left_eq_mul.1 this
  have e : (lift (Over.homMk (spMap (algebraMap ℂ (DualNumber ℂ))) rfl : TE R ℂ ⟶ TF (R := R) ℂ)
      (DegPre.zeroT D (TE R ℂ))).left = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ ptB ν d 0 := by
    have : lift (Over.homMk (spMap (algebraMap ℂ (DualNumber ℂ))) rfl : TE R ℂ ⟶ TF (R := R) ℂ)
        (DegPre.zeroT D (TE R ℂ)) =
        (Over.homMk (spMap (algebraMap ℂ (DualNumber ℂ))) rfl : TE R ℂ ⟶ TF (R := R) ℂ) ≫
          lift (𝟙 (TF (R := R) ℂ)) (ν.eA (d.ex 0)) := by
      rw [comp_lift, Category.comp_id, h0, map_one, Hom.one_def, ← Category.assoc, comp_toUnit]
    rw [this, Over.comp_left]
    rfl
  rw [e, valR_push _ _ _ hU, map_zero, TrivSqZeroExt.inr_zero, add_zero]
  rfl

end GlobalTheory.MBLow.Cl.DZero

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKeyInNf
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

namespace GlobalTheory.MBLow.Cl

theorem exists_keyIn_nf :
    ∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (c : ℂ) (Mx : Matrix (Fin g) (Fin g) ℂ), 1 ≤ g → τ.IsSymm → (τ.map Complex.im).PosDef → Half a → Half b → c ≠ 0 → Mx.det ≠ 0 → ∃ (x : KeyIn ℂ) (hg : x.P.g = g) (u : HolUnif x.P.A x.P.L g), NF x hg u τ a b c (fun j => (2 * Real.pi * Complex.I : ℂ)⁻¹ • Mx j) := by
  intro g τ a b c Mx hg hs hp ha hb hc hM
  obtain ⟨x, h, u, τ', a', b', e₁, e₂, e₃, -, -, -, -, h₃, h₄, h₅, h₆⟩ :=
    GlobalTheory.KeyOfPeriod.exists_keyIn_classicalFrame g τ a b hg hs hp ha hb
  subst h
  obtain rfl : τ' = τ := e₁
  obtain rfl : a' = a := e₂
  obtain rfl : b' = b := e₃
  have := x.P.isAb.comm
  obtain ⟨hex, -, -, -, hbas⟩ := LieComb.lieComb_algebra ℂ x.P.A x.P.g x.v x.basis.1
  choose v hv using fun i => (hex (Mx i)).exists
  refine ⟨⟨x.P, x.g_pos, x.rig, x.rig_gen, KeyNormalExists.constMul x.P.A.hom c x.th, fun s => ?_, v,
    (hbas Mx v x.basis hv).2 hM.isUnit⟩, rfl, u, hs, hp, ha, hb, hc, h₃, h₄,
    KeyNormalExists.isFn_constMul u c h₅, fun i => ?_⟩
  · obtain ⟨z, hz, hz'⟩ := x.th_ne s
    exact ⟨z, hz, KeyNormalExists.mem_nonzeroLocus_constMul _ hc.isUnit _ hz'⟩
  · have h1 := UnifDifferential.isDiff_of_isLieComb _ _ _ _ u _ x.v (Mx i) (v i) x.basis.1 h₆ (hv i)
    have e : ∑ j, Mx i j • (Pi.single j (2 * Real.pi * Complex.I : ℂ)⁻¹ : Fin x.P.g → ℂ) =
        (2 * Real.pi * Complex.I : ℂ)⁻¹ • Mx i := by
      funext k
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, mul_ite, MulZeroClass.mul_zero,
        Finset.sum_ite_eq, Finset.mem_univ, if_true]
      ring
    rw [e] at h1
    exact h1

end GlobalTheory.MBLow.Cl
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetEqDetBlock
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

namespace GlobalTheory.MBLow.Cl

theorem det_eq_det_block : ∀ (g' r g : ℕ) (σ : Fin g ≃ Fin g' ⊕ Fin r) (Mx : Matrix (Fin g) (Fin g) ℂ) (MB : Matrix (Fin g') (Fin g') ℂ), (∀ i, zP σ (Mx (σ.symm (Sum.inl i))) = MB i) → (∀ l, zP σ (Mx (σ.symm (Sum.inr l))) = 0 ∧ tP σ (Mx (σ.symm (Sum.inr l))) = Pi.single l 1) → Mx.det = MB.det := by
  intro g' r g σ Mx MB h1 h2
  have key : Mx.submatrix σ.symm σ.symm =
      Matrix.fromBlocks MB (Matrix.of fun i l => Mx (σ.symm (Sum.inl i)) (σ.symm (Sum.inr l))) 0 1 := by
    ext (i | i) (j | j)
    · exact congrFun (h1 i) j
    · rfl
    · exact congrFun (h2 i).1 j
    · have := congrFun (h2 i).2 j
      simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₂₂, Matrix.one_apply]
      rw [Pi.single_apply] at this
      simp only [eq_comm (a := i)]
      exact this
  rw [← Matrix.det_submatrix_equiv_self σ.symm Mx, key, Matrix.det_fromBlocks_zero₂₁,
    Matrix.det_one, _root_.mul_one]

end GlobalTheory.MBLow.Cl
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPosDefFromBlocks
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

namespace GlobalTheory.MBLow.Cl.BlockPos

theorem exists_neg_mul_le {n : Type} [Fintype n] (S : Matrix n n ℝ) :
    ∃ C : ℝ, ∀ x : n → ℝ, -(C * (x ⬝ᵥ x)) ≤ x ⬝ᵥ S *ᵥ x := by
  refine ⟨∑ i, ∑ j, |S i j|, fun x => ?_⟩
  have h : ∀ i, x i * x i ≤ x ⬝ᵥ x := fun i =>
    Finset.single_le_sum (f := fun i => x i * x i) (fun _ _ => mul_self_nonneg _) (Finset.mem_univ i)
  rw [Finset.sum_mul, ← Finset.sum_neg_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Finset.sum_mul, ← Finset.sum_neg_distrib, mulVec, dotProduct, dotProduct, Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  have hi := h i
  have hj := h j
  rw [dotProduct] at hi hj
  rcases abs_cases (S i j) with ⟨e, p⟩ | ⟨e, p⟩ <;> rw [e]
  · nlinarith [mul_nonneg p (sq_nonneg (x i + x j)), mul_le_mul_of_nonneg_left hi p, mul_le_mul_of_nonneg_left hj p]
  · have p' : 0 ≤ -S i j := by linarith
    nlinarith [mul_nonneg p' (sq_nonneg (x i - x j)), mul_le_mul_of_nonneg_left hi p', mul_le_mul_of_nonneg_left hj p']

theorem exists_posDef_fromBlocks {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    {Y : Matrix m m ℝ} (hY : Y.PosDef) (P : Matrix m n ℝ) {Q B : Matrix n n ℝ} (hQ : Q.IsHermitian) (hB : B.PosDef) :
    ∃ T : ℝ, ∀ t : ℝ, T < t → (fromBlocks Y P Pᴴ (Q + t • B)).PosDef := by
  obtain ⟨c, hc, hcB⟩ := posDef_exists_mul_dotProduct_le hB
  obtain ⟨C, hC⟩ := exists_neg_mul_le (Q - Pᴴ * Y⁻¹ * P)
  have : Invertible Y := (isUnit_iff_isUnit_det Y).mpr (hY.det_pos.ne').isUnit |>.invertible
  refine ⟨max 0 (C / c), fun t ht => ?_⟩
  have ht0 : 0 < t := (le_max_left _ _).trans_lt ht
  have htC : C < t * c := (div_lt_iff₀ hc).mp ((le_max_right _ _).trans_lt ht)
  have hH : (Q + t • B).IsHermitian := hQ.add (hB.smul ht0).1
  refine PosDef.of_dotProduct_mulVec_pos (hY.1.fromBlocks rfl hH) fun x hx => ?_
  rw [← Sum.elim_comp_inl_inr x, dotProduct_mulVec, schur_complement_eq₁₁ P _ _ _ hY.1, ← dotProduct_mulVec,
    ← dotProduct_mulVec]
  by_cases h2 : x ∘ Sum.inr = 0
  · have h1 : x ∘ Sum.inl ≠ 0 := fun h1 => hx (by rw [← Sum.elim_comp_inl_inr x, h1, h2]; simp)
    simpa [h2] using hY.dotProduct_mulVec_pos h1
  · refine add_pos_of_nonneg_of_pos (hY.posSemidef.dotProduct_mulVec_nonneg _) ?_
    have e : Q + t • B - Pᴴ * Y⁻¹ * P = (Q - Pᴴ * Y⁻¹ * P) + t • B := by abel
    rw [e, star_trivial, add_mulVec, dotProduct_add, smul_mulVec, dotProduct_smul, smul_eq_mul]
    have a1 := hC (x ∘ Sum.inr)
    have a2 := mul_le_mul_of_nonneg_left (hcB (x ∘ Sum.inr)) ht0.le
    have a3 : 0 < (x ∘ Sum.inr) ⬝ᵥ (x ∘ Sum.inr) := by
      simpa using (dotProduct_star_self_pos_iff (v := x ∘ Sum.inr)).mpr h2
    nlinarith [mul_pos (sub_pos.mpr htC) a3]

theorem full_posDef : AllCD fun {N} {g'} {r} {g} {bX} d σ => ∀ (k : ℕ) (β : N.Form k), ∃ T : ℝ, ∀ w : ℂ, T < w.im →
    (w • bmat bX β).IsSymm ∧ (d.full σ (w • bmat bX β)).IsSymm ∧
      ((d.full σ (w • bmat bX β)).map Complex.im).PosDef := by
  intro N g' r g bX d σ k β
  have hB := (ClassMin.realExtension_posDef_iff _ bX).mp (ClassMin.realExtension_ofIntBilin_posDef β.symm β.pos)
  have hQ : (d.t22.map Complex.im).IsHermitian := by
    ext i j
    simp [d.toricPeriodBlock_isSymm.apply i j]
  obtain ⟨T, hT⟩ := exists_posDef_fromBlocks d.pos (d.t12.map Complex.im) hQ hB
  refine ⟨T, fun w hw => ?_⟩
  have hs : (w • bmat bX β).IsSymm := by
    ext i j
    simp [bmat, β.symm (bX j) (bX i)]
  refine ⟨hs, (IsSymm.fromBlocks d.symm rfl (d.toricPeriodBlock_isSymm.add hs)).submatrix σ, ?_⟩
  convert (hT w.im hw).submatrix σ.injective using 1
  ext i j
  simp only [CD.full, map_apply, submatrix_apply]
  rcases σ i with a | a <;> rcases σ j with b | b <;> simp [bmat, ClassMin.polar_ofIntBilin β.symm]

end GlobalTheory.MBLow.Cl.BlockPos
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeyRuleComplexExistenceJetsKeyValue
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

noncomputable section

namespace GlobalTheory.MBLow.ArchProof

theorem coset_series {X : Type} [AddCommGroup X] [Module.Free ℤ X] {m : ℕ} (hm : 1 ≤ m) (y : X) (A B : X → ℂ)
    (h1 : ∀ χ, A (y + m • χ) = B χ) (h0 : ∀ α, (∀ χ, α ≠ y + m • χ) → A α = 0) (hB : Summable fun χ => ‖B χ‖) :
    (Summable fun α => ‖A α‖) ∧ ∑' α, A α = ∑' χ, B χ := by
  have hi : Function.Injective fun χ : X => y + m • χ := fun a b h => by
    have e : (m : ℤ) • a = (m : ℤ) • b := by simpa only [natCast_zsmul] using add_left_cancel h
    exact smul_right_injective X (by omega : (m : ℤ) ≠ 0) e
  have hz : ∀ α ∉ Set.range fun χ : X => y + m • χ, A α = 0 := fun α hα => h0 α fun χ e => hα ⟨χ, e.symm⟩
  refine ⟨(hi.summable_iff (f := fun α => ‖A α‖) fun α hα => by rw [hz α hα, norm_zero]).1 ?_, ?_⟩
  · simpa only [Function.comp_def, h1] using hB
  · rw [← hi.tsum_eq (f := A) fun α hα => by_contra fun h => hα (hz α h)]
    simp only [h1]

theorem exists_log (T : ℝ) (u : ℂ) (hu : u ≠ 0) (h : ‖u‖ < Real.exp (-(2 * Real.pi * T))) :
    ∃ w : ℂ, T < w.im ∧ Complex.exp ((2 * Real.pi * Complex.I : ℂ) * w) = u := by
  have hne : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
  have e : Complex.exp ((2 * Real.pi * Complex.I : ℂ) * (Complex.log u / (2 * Real.pi * Complex.I))) = u := by
    rw [mul_div_cancel₀ _ hne, Complex.exp_log hu]
  refine ⟨_, ?_, e⟩
  rw [← e, Complex.norm_exp, Real.exp_lt_exp] at h
  generalize Complex.log u / (2 * Real.pi * Complex.I) = w at h ⊢
  have : ((2 * Real.pi * Complex.I : ℂ) * w).re = -(2 * Real.pi * w.im) := by simp
  rw [this] at h
  have := Real.pi_pos
  nlinarith

theorem exists_cd (κ : Rule) (hκ : Rule4 κ) {R : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R]
    {D : DegPre R} (h1 : D.PsiEven) (h2 : D.TauBimult) [Algebra (FractionRing R) ℂ] {N : NumD ℂ} (ν : NumOf D ℂ N)
    {r : ℕ} (bX : Module.Basis (Fin r) ℤ N.X) :
    ∃ (d : CD N D.P.g r bX) (_ : Geo ν d.toAB), KeyOK κ ν d.toAB := by
  have : ∃ (d : AB N.toNumB D.P.g) (_ : Geo ν d), KeyOK κ ν d := by
    rcases Nat.eq_zero_or_pos D.P.g with h | h
    · exact GlobalTheory.MBLow.DimZero.main κ R D h1 h2 N ν h
    · exact GlobalTheory.T.exists_classicalThetaDescription_abelianPart κ hκ R D h1 h2 N ν h
  obtain ⟨e, G, hK⟩ := this
  obtain ⟨d, rfl⟩ := GlobalTheory.MBLow.Cl.PsiFrame.exists_cd N D.P.g r bX e (GlobalTheory.MBLow.Cl.cub_of_geo R D h1 h2 N ν _ e ⟨G⟩) (GlobalTheory.MBLow.Cl.sym_of_geo R D h1 h2 N ν _ e ⟨G⟩)
  exact ⟨d, G, hK⟩

theorem exists_vec (κ : Rule) {R : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R]
    {D : DegPre R} (h1 : D.PsiEven) (h2 : D.TauBimult) [Algebra (FractionRing R) ℂ] {N : NumD ℂ} (ν : NumOf D ℂ N)
    {g r : ℕ} {bX : Module.Basis (Fin r) ℤ N.X} (d : CD N D.P.g r bX) (G : Geo ν d.toAB) (hK : KeyOK κ ν d.toAB)
    (vB : Fin D.P.g → (epsR R ⟶ D.P.A)) (σ : Fin g ≃ Fin D.P.g ⊕ Fin r) (gm : Fin g → GtPt D (TE R ℂ))
    (hA : Adapted ν vB bX σ gm) (k₀ : ℂ) (hk : BKey κ ν vB k₀) :
    ∃ (Mx : Matrix (Fin g) (Fin g) ℂ) (c₀ : Fin g → ℂ), Mx.det ≠ 0 ∧ k₀ * d.c ^ 8 = Mx.det ^ 4 ∧
      ∀ j (k : ℕ) (s : Fam D ℂ k) (f : N.X → N.A → ℂ) (α : N.X) (F : (Fin g → ℂ) → ℂ), ν.FamV s f → Differentiable ℂ F →
        (∀ Y h, d.IsPt σ Y h → f α h.b * h.s α = (d.fr (zP σ Y) : ℂ) ^ k * F Y) →
        (jc ν s (gm j) α).fst / ν.rg ^ k = F 0 ∧ (jc ν s (gm j) α).snd / ν.rg ^ k =
          fderiv ℂ F 0 ((2 * Real.pi * Complex.I : ℂ)⁻¹ • Mx j) + k * c₀ j * F 0 := by
  obtain ⟨hb, ho, hl, hr⟩ := hA
  have hne : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
  have hW : ∀ j, ∃ W, IsD ν d.toAB W (gm j).b ∧ ∀ l, j = σ.symm (Sum.inr l) → W = 0 := by
    intro j
    by_cases h : ∃ l, j = σ.symm (Sum.inr l)
    · obtain ⟨l, rfl⟩ := h
      exact ⟨0, by rw [(hr l).1]; exact GlobalTheory.MBLow.Cl.DZero.isD_zero R D h1 h2 N ν _ d.toAB, fun _ _ => rfl⟩
    · obtain ⟨o, hz, hp⟩ := ho j
      obtain ⟨W, hW⟩ := G.dif (gm j).b (hp.1.symm.trans (congrArg (·.left) hz.1))
      exact ⟨W, hW, fun l e => absurd ⟨l, e⟩ h⟩
  choose W hW hW0 using hW
  choose Z c₀ hZ hT hJ using fun j => GlobalTheory.MBLow.Cl.jet_family_deriv R D h1 h2 N ν _ r g bX d σ G (gm j) (W j) (ho j) (hW j)
  have hs : ∀ {n : ℕ} (v : Fin n → ℂ), (2 * Real.pi * Complex.I : ℂ)⁻¹ • (2 * Real.pi * Complex.I : ℂ) • v = v :=
    fun v => inv_smul_smul₀ hne v
  let Mx : Matrix (Fin g) (Fin g) ℂ := fun j => (2 * Real.pi * Complex.I : ℂ) • Z j
  let MB : Matrix (Fin D.P.g) (Fin D.P.g) ℂ := fun i => (2 * Real.pi * Complex.I : ℂ) • W (σ.symm (Sum.inl i))
  have hdet : Mx.det = MB.det := by
    refine GlobalTheory.MBLow.Cl.det_eq_det_block _ r g σ Mx MB (fun i => ?_) fun l => ⟨?_, ?_⟩
    · exact congrArg (fun v => (2 * Real.pi * Complex.I : ℂ) • v) (hZ (σ.symm (Sum.inl i)))
    · have := congrArg (fun v => (2 * Real.pi * Complex.I : ℂ) • v) ((hZ (σ.symm (Sum.inr l))).trans (hW0 _ l rfl))
      simp only [smul_zero] at this
      exact this
    · funext l'
      have e := congrArg TrivSqZeroExt.snd (((hT _ (hW0 _ l rfl) (bX l')).symm).trans ((hr l).2 (bX l')))
      have hc : co bX (bX l') = Pi.single l' 1 := by
        funext i
        by_cases hi : i = l' <;> simp [co, hi, Finsupp.single_apply, eq_comm]
      rw [hc, single_one_dotProduct] at e
      simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_one, TrivSqZeroExt.snd_inr, zero_add, Module.Basis.repr_self] at e
      refine e.trans ?_
      by_cases hi : l' = l <;> simp [hi, Finsupp.single_apply]
  obtain ⟨hd, hv⟩ := hK vB (fun i => (gm (σ.symm (Sum.inl i))).b) MB k₀ hb hl (fun i => by
    change IsD ν d.toAB ((2 * Real.pi * Complex.I : ℂ)⁻¹ • (2 * Real.pi * Complex.I : ℂ) • W (σ.symm (Sum.inl i))) _
    rw [hs]; exact hW _) hk
  refine ⟨Mx, c₀, hdet ▸ hd, hdet ▸ hv, fun j k s f α F hs' hF hY => ?_⟩
  have : (2 * Real.pi * Complex.I : ℂ)⁻¹ • Mx j = Z j := hs _
  rw [this]
  exact hJ j k s f α F hs' hF hY

theorem arch_of_rule4 : ∀ κ : Rule, Rule4 κ → Arch κ := by
  intro κ hκ R _ _ _ _ D h1 h2 _ N ν g r m k hg hm hmk β ζ q hq s hs vB bX σ gm hA k₀ hk
  have hm1 : 1 ≤ m := hm.pos
  obtain ⟨d, G, hK⟩ := exists_cd κ hκ h1 h2 ν bX
  obtain ⟨Mx, c₀, hdet, hval, hJ⟩ := exists_vec κ h1 h2 ν d G hK vB σ gm hA k₀ hk
  obtain ⟨M, Nn, hrep, hlab⟩ := GlobalTheory.MBLow.Cl.exists_integral_labels N _ r g bX d σ (m ^ 2) (by positivity) ζ q hq
  obtain ⟨T, hT⟩ := GlobalTheory.MBLow.Cl.BlockPos.full_posDef N _ r g bX d σ k β
  obtain ⟨hdiff, htw⟩ := GlobalTheory.MBLow.Cl.term_smul_bmat N _ r g bX d σ
  refine ⟨Real.exp (-(2 * Real.pi * T)), Real.exp_pos _, fun u hu0 hu => ?_⟩
  obtain ⟨w, hw, hwu⟩ := exists_log T u hu0 hu
  obtain ⟨hS, hsym, hpos⟩ := hT w hw
  set S := w • bmat bX β with hSdef
  set V : Fin g → Fin g → ℂ := fun j => (2 * Real.pi * Complex.I : ℂ)⁻¹ • Mx j with hV
  have key : ∀ a j,
      ((Summable fun α => ‖(jc ν (s a) (gm j) α).fst / ν.rg ^ (m ^ 2) * u ^ (β.be α α / (2 * m ^ 2)).toNat‖) ∧
        ∑' α, (jc ν (s a) (gm j) α).fst / ν.rg ^ (m ^ 2) * u ^ (β.be α α / (2 * m ^ 2)).toNat =
          d.c * trF (d.full σ S) (d.aF σ) (d.bF σ) m (M a) (Nn a) 0) ∧
      (Summable fun α => ‖(jc ν (s a) (gm j) α).snd / ν.rg ^ (m ^ 2) * u ^ (β.be α α / (2 * m ^ 2)).toNat‖) ∧
        ∑' α, (jc ν (s a) (gm j) α).snd / ν.rg ^ (m ^ 2) * u ^ (β.be α α / (2 * m ^ 2)).toNat =
          d.c * fderiv ℂ (trF (d.full σ S) (d.aF σ) (d.bF σ) m (M a) (Nn a)) 0 (V j) +
            ((m ^ 2 : ℕ) * c₀ j) * (d.c * trF (d.full σ S) (d.aF σ) (d.bF σ) m (M a) (Nn a) 0) := by
    intro a j
    obtain ⟨f, hf, hf1, hf0⟩ := hs a
    rw [(hrep a).1] at hf1 hf0
    set y := ∑ l, tP σ (Nn a) l • bX l with hy
    obtain ⟨s1, s2, t1, t2⟩ := GlobalTheory.MBLow.Cl.term_sum_and_fderiv N _ r g bX d σ S hS hpos m (M a) (Nn a) (V j)
    have on : ∀ χ, _ := fun χ => hJ j _ (s a) f (y + m • χ) (fun Y => d.c * d.term σ 0 m (M a) (Nn a) χ Y) hf
      ((hdiff _ _ _ _ _).const_mul _) fun Y h hY => by
        rw [hf1, GlobalTheory.MBLow.Cl.evT_eq_term N _ r g bX d σ m hm (M a) (Nn a) (q a) (hrep a) Y h hY χ]; ring
    have off : ∀ α, (∀ χ, α ≠ y + m • χ) → _ := fun α hα => hJ j _ (s a) f α (fun _ => 0) hf
      (differentiable_const _) fun Y h hY => by rw [hf0 α hα]; simp
    have tw : ∀ χ, d.term σ S m (M a) (Nn a) χ = fun Z => d.term σ 0 m (M a) (Nn a) χ Z *
        u ^ (β.be (y + m • χ) (y + m • χ) / (2 * m ^ 2)).toNat := fun χ => funext fun Z => by
      rw [← hwu]; exact htw k m β hm1 hmk w (M a) (Nn a) χ Z
    have A := coset_series hm1 y
      (fun α => (jc ν (s a) (gm j) α).fst / ν.rg ^ (m ^ 2) * u ^ (β.be α α / (2 * m ^ 2)).toNat)
      (fun χ => d.c * d.term σ S m (M a) (Nn a) χ 0)
      (fun χ => by simp only [(on χ).1, tw χ]; ring) (fun α hα => by simp only [(off α hα).1, zero_mul])
      (by simpa only [norm_mul] using s1.mul_left ‖d.c‖)
    have B := coset_series hm1 y
      (fun α => (jc ν (s a) (gm j) α).snd / ν.rg ^ (m ^ 2) * u ^ (β.be α α / (2 * m ^ 2)).toNat)
      (fun χ => d.c * fderiv ℂ (d.term σ S m (M a) (Nn a) χ) 0 (V j) +
        ((m ^ 2 : ℕ) * c₀ j) * (d.c * d.term σ S m (M a) (Nn a) χ 0))
      (fun χ => by
        simp only [(on χ).2, tw χ]
        rw [fderiv_const_mul (hdiff _ _ _ _ _ _), fderiv_mul_const (hdiff _ _ _ _ _ _)]
        simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, hV]
        ring)
      (fun α hα => by simp [(off α hα).2])
      (((s2.of_norm.mul_left d.c).add ((s1.of_norm.mul_left d.c).mul_left _)).norm)
    refine ⟨⟨A.1, ?_⟩, B.1, ?_⟩
    · rw [A.2, tsum_mul_left, t1]
    · rw [B.2, (s2.of_norm.mul_left d.c).tsum_add ((s1.of_norm.mul_left d.c).mul_left _), tsum_mul_left, tsum_mul_left,
        tsum_mul_left, t1, t2]
  have hrg : ν.rg ^ (m ^ 2) ≠ 0 := pow_ne_zero _ (GlobalTheory.Ex.Arch.AbVal.rg_ne_zero ν)
  have hmul : ∀ (x v : N.X → ℂ), (Summable fun α => ‖x α / ν.rg ^ (m ^ 2) * v α‖) → Summable fun α => ‖x α * v α‖ := by
    intro x v h
    refine (h.mul_left ‖ν.rg ^ (m ^ 2)‖).congr fun α => ?_
    rw [← norm_mul, ← _root_.mul_assoc, mul_div_cancel₀ _ hrg]
  refine ⟨fun a j => ⟨hmul _ _ (key a j).1.1, hmul _ _ (key a j).2.1⟩, ?_⟩
  have ha : Half (d.aF σ) := fun i => by
    unfold CD.aF
    rcases σ i with i | i
    · exact d.ha i
    · exact Or.inl rfl
  have hb : Half (d.bF σ) := fun i => by
    unfold CD.bF
    rcases σ i with i | i
    · exact d.hb i
    · exact d.hb2 i
  obtain ⟨x₀, hg₀, U, hNF⟩ := GlobalTheory.MBLow.Cl.exists_keyIn_nf g (d.full σ S) (d.aF σ) (d.bF σ) d.c Mx hg hsym hpos ha hb d.hc hdet
  obtain ⟨lev, hlev⟩ := GlobalTheory.MBLow.LabelLevel.exists_level_of_labels g x₀ hg₀ U _ _ _ _ _ hNF (m ^ 2) (by positivity) ζ hq.1 M Nn hlab
  refine ⟨x₀, hg₀, lev, fun a => d.c * trF (d.full σ S) (d.aF σ) (d.bF σ) m (M a) (Nn a) 0,
    fun a j => (key a j).1.2.symm, ?_, ?_⟩
  · simp only [fun a j => (key a j).2.2]
    exact GlobalTheory.MBLow.Cl.thJet_of_normalForm g x₀ hg₀ U _ _ _ _ _ hNF m hm _ M Nn _ (fun a => by rw [hlev a, Nat.cast_pow]) _
  · exact mul_right_cancel₀ (pow_ne_zero 8 d.hc) ((GlobalTheory.MBLow.Cl.key_value_of_nf κ hκ.1 hκ.2.2.1 g x₀ hg₀ U _ _ _ _ Mx hNF).2.trans hval.symm)

end GlobalTheory.MBLow.ArchProof

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeyRuleComplexExistenceJetsKeyValueStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.keyRule_complex_existence_jets_key_value : ∀ κ : Rule, Rule4 κ → Arch κ := by
  first | exact @GlobalTheory.MBLow.ArchProof.arch_of_rule4 | exact GlobalTheory.MBLow.ArchProof.arch_of_rule4 | (intros; apply GlobalTheory.MBLow.ArchProof.arch_of_rule4 <;> assumption)
end
