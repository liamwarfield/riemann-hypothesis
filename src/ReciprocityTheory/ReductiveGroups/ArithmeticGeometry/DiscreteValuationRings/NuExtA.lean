module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdNeg
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.ClosedPointWeilPower

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.NuExtA
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.DVR

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
  ReciprocityTheory.ChartRestriction.G.Out

section Dvr

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]

theorem exists_pow_le_span {ϖ : V} (hϖ : Irreducible ϖ) {r : V} (hr : r ≠ 0) :
    ∃ n : ℕ, IsLocalRing.maximalIdeal V ^ (n + 1) ≤ Ideal.span {r} := by
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hr hϖ
  refine ⟨n, ?_⟩
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ, Ideal.span_singleton_pow, hu,
    Ideal.span_singleton_mul_left_unit u.isUnit]
  exact Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow ϖ (Nat.le_succ n))

theorem mem_range_of_val_nonneg {ϖ : V} (hϖ : Irreducible ϖ) {v : AddValuation (FractionRing V) (WithTop ℚ)}
    (hv : ValOver ϖ (FractionRing V) v) (c : FractionRing V) (hc : 0 ≤ v c) :
    c ∈ (algebraMap V (FractionRing V)).range := by
  classical
  by_cases hc0 : c = 0
  · exact ⟨0, by rw [hc0, map_zero]⟩
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := V) c
  have ha : a ≠ 0 := by
    rintro rfl
    exact hc0 (by simp)
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  obtain ⟨n1, u1, hu1⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ
  obtain ⟨n2, u2, hu2⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hϖ
  have hϖ0 : algebraMap V (FractionRing V) ϖ ≠ 0 :=
    (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hϖ.ne_zero))
  have hu2' : algebraMap V (FractionRing V) (u2 : V) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero u2.ne_zero)
  set w : Vˣ := u1 * u2⁻¹ with hw
  have hval : HasVal ϖ (algebraMap V (FractionRing V) a / algebraMap V (FractionRing V) b) ((n1 : ℤ) - n2) := by
    refine ⟨w, ?_⟩
    rw [hu1, hu2, hw, zpow_sub₀ hϖ0, zpow_natCast, zpow_natCast]
    simp only [map_mul, map_pow, Units.val_mul]
    have hinv : algebraMap V (FractionRing V) ((u2⁻¹ : Vˣ) : V) = (algebraMap V (FractionRing V) (u2 : V))⁻¹ := by
      exact map_units_inv (algebraMap V (FractionRing V)) u2
    rw [hinv]
    field_simp
  have hv1 := hv _ _ hval
  simp only [Algebra.algebraMap_self, RingHom.id_apply] at hv1
  rw [hv1] at hc
  have hn : (0 : ℤ) ≤ (n1 : ℤ) - n2 := by
    have : ((0 : ℚ) : WithTop ℚ) ≤ (((n1 : ℤ) - n2 : ℤ) : ℚ) := by simpa using hc
    have h2 : (0 : ℚ) ≤ (((n1 : ℤ) - n2 : ℤ) : ℚ) := WithTop.coe_le_coe.mp this
    exact_mod_cast h2
  obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le hn
  obtain ⟨w', hw'⟩ := hval
  refine ⟨ϖ ^ k * (w' : V), ?_⟩
  rw [hw', hk, zpow_natCast, map_mul, map_pow]

variable {X : Scheme.{0}}

theorem isUnit_cst (p : X ⟶ Sp V) (x : X) {r : V} (hx : r ∉ (p x).asIdeal) : IsUnit (cst p x r) := by
  have hmem : p x ∈ (Sp V).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom r) := by
    have e := basicOpen_eq_of_affine (R := CommRingCat.of V) r
    exact (congrArg (fun U : (Sp V).Opens => p x ∈ U) e).mpr hx
  have e2 := Scheme.preimage_basicOpen p ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom r)
  have hx' : x ∈ X.basicOpen ((p.app ⊤).hom ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom r)) := by
    rw [← e2]; exact hmem
  have hu := (Scheme.mem_basicOpen X ((p.app ⊤).hom ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom r)) x
    (show x ∈ p ⁻¹ᵁ ⊤ from trivial)).1 hx'
  rw [cst, gs_eq p x ⊤ (show p x ∈ (⊤ : (Sp V).Opens) from trivial)]
  exact hu

theorem exists_fst_eq (p : X ⟶ Sp V) (J : Ideal V) {r : V} (hJ : J ≤ Ideal.span {r}) (x : X)
    (hx : r ∈ (p x).asIdeal) :
    ∃ x', pullback.fst p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) x' = x := by
  have h1 : x ∈ Set.range (pullback.fst p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))) := by
    rw [Scheme.Pullback.range_fst]
    show p x ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk J))
    rw [range_comap_of_surjective (V ⧸ J) (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective, Ideal.mk_ker]
    exact fun y hy => (Ideal.span_singleton_le_iff_mem _).2 hx (hJ hy)
  exact h1

theorem exists_div_sec_of_thick (p : X ⟶ Sp V) [Flat p] (J : Ideal V) {r : V} (hr : r ≠ 0)
    (hJ : J ≤ Ideal.span {r}) {M : LB X} (s : LB.Sec M)
    (h : ∀ j (x' : ↑(pullback p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))))),
      pullback.fst p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) x' ∈ M.U j →
      cst (pullback.fst p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) ≫ p) x' r ∣
        gs (pullback.fst p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))) x' (M.U j) (s.f j)) :
    ∃ s' : LB.Sec M, ∀ j, s.f j = constFn p _ r * s'.f j := by
  refine exists_div_sec p hr s fun j x hx => ?_
  by_cases hxr : r ∈ (p x).asIdeal
  · obtain ⟨x', rfl⟩ := exists_fst_eq p J hJ x hxr
    exact dvd_germ_of_thick p J hJ (s.f j) x' hx (h j x' hx)
  · exact (isUnit_cst p x hxr).dvd

end Dvr

section Sec

variable {X Y Y' Z : Scheme.{0}} {L : LB X} {K₁ K₂ : Type} [Fintype K₁] [Fintype K₂]

theorem secScal_sval_c {φ₁ : K₁ → (Y' ⟶ X)} {ε₁ : K₁ → ℤ} {s₁ : LB.Sec (LB.LinComb L φ₁ ε₁)}
    {φ₂ : K₂ → (Y ⟶ X)} {ε₂ : K₂ → ℤ} {s₂ : LB.Sec (LB.LinComb L φ₂ ε₂)} {h : Y' ⟶ Y} {c : Γ(Y', ⊤)}
    (H : GeneratorPullback.SecScal L φ₁ ε₁ s₁ φ₂ ε₂ s₂ h c) (r : Z ⟶ Y') (z : Z) {J : (Z ⟶ X) → L.ι}
    (hJ : Good L z J) : sval s₂ (r ≫ h) z J = gs r z ⊤ c * sval s₁ r z J := by
  have hc : LB.Coh L (Sum.elim φ₁ (fun k => h ≫ φ₂ k))
      (Sum.elim (fun k => J (r ≫ φ₁ k)) (fun k => J (r ≫ h ≫ φ₂ k))) := by
    rintro (a | a) (b | b) e <;> exact congrArg (fun q => J (r ≫ q)) e
  have e := H _ _ hc
  have hm : r z ∈ LB.wchart L φ₁ (fun k => J (r ≫ φ₁ k)) ⊓
      LB.wchart L (fun k => h ≫ φ₂ k) (fun k => J (r ≫ h ≫ φ₂ k)) :=
    ⟨hJ.mem φ₁ r, hJ.mem (fun k => h ≫ φ₂ k) r⟩
  have le : LB.wchart L (fun k => h ≫ φ₂ k) (fun k => J (r ≫ h ≫ φ₂ k)) ≤
      h ⁻¹ᵁ LB.wchart L φ₂ (fun k => J (r ≫ h ≫ φ₂ k)) :=
    fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k
  rw [sval_of s₂ (r ≫ h) z J (fun k => J (r ≫ h ≫ φ₂ k)) (fun k => by rw [Category.assoc])]
  have e2 := congrArg (gs r z _) e
  exact ((gs_res r z _ hm _).trans (gs_pull r h z _ (le hm.2) _)).symm.trans (e2.trans
    ((gs_mul r z _ hm _ _).trans (congrArg₂ (· * ·) (gs_res r z le_top hm c) (gs_res r z _ hm _))))

end Sec

end ReciprocityTheory.ChartRestriction.G.DVR
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LiftOUnique
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR.TWM

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor IsLocalRing TWO SectionScalarValuation

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V} (hϖ : Irreducible ϖ)
  {D : DegData V (maximalIdeal V)} {F : Type} [Field F] [Algebra (FractionRing V) F]
  {v : AddValuation F (WithTop ℚ)} (hv : ValOver ϖ F v)

theorem TF_hom : (TF (R := V) F).hom = Spec.map (CommRingCat.ofHom (algVF (F := F) (V := V))) := by
  simp only [TF, jFK, jK]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

theorem exists_liftO (b : TF (R := V) F ⟶ D.toPre.P.A) : ∃ m : TO hϖ hv ⟶ D.toPre.P.A, ιS hϖ hv ≫ m = b := by
  haveI : IsProper D.toPre.P.A.hom := D.toPre.P.isAb.proper
  obtain ⟨x', hx'p, hx'⟩ := TWO.exists_lift v hϖ hv D.toPre.P.A.hom b.left (by rw [Over.w b, TF_hom])
  exact ⟨Over.homMk x' hx'p, Over.OverMorphism.ext hx'⟩

theorem liftO_unique (m₁ m₂ : TO hϖ hv ⟶ D.toPre.P.A) (h : ιS hϖ hv ≫ m₁ = ιS hϖ hv ≫ m₂) : m₁ = m₂ := by
  haveI : IsProper D.toPre.P.A.hom := D.toPre.P.isAb.proper
  apply Over.OverMorphism.ext
  exact TWO.lift_unique v hϖ hv D.toPre.P.A.hom m₁.left m₂.left (Over.w m₁) (Over.w m₂)
    (congrArg (fun g => g.left) h)

def gtφO (m : TO hϖ hv ⟶ D.toPre.P.A) (χ : D.toPre.X) : Fin 4 → ((TO hϖ hv).left ⟶ D.toPre.P.A.left) :=
  ![(cP D.toPre _ χ * m).left, (cP D.toPre _ χ).left, m.left, (1 : TO hϖ hv ⟶ D.toPre.P.A).left]

def lineφO (m : TO hϖ hv ⟶ D.toPre.P.A) : Fin 2 → ((TO hϖ hv).left ⟶ D.toPre.P.A.left) :=
  ![(1 : TO hϖ hv ⟶ D.toPre.P.A).left, m.left]

def trO (m : TO hϖ hv ⟶ D.toPre.P.A) : TO hϖ hv ⊗ D.toPre.P.A ⟶ TO hϖ hv ⊗ D.toPre.P.A :=
  lift (fst _ _) (padd D.toPre.P.A (snd _ _) (fst _ _ ≫ m))

theorem trO_fst (m : TO hϖ hv ⟶ D.toPre.P.A) : trO hϖ hv m ≫ fst _ _ = fst _ _ := by
  unfold trO
  exact lift_fst _ _

theorem trO_snd (m : TO hϖ hv ⟶ D.toPre.P.A) : trO hϖ hv m ≫ snd _ _ = snd _ _ * (fst _ _ ≫ m) := by
  unfold trO
  rw [lift_snd]
  rfl

theorem jO_trO (b : TF (R := V) F ⟶ D.toPre.P.A) (m : TO hϖ hv ⟶ D.toPre.P.A) (hm : ιS hϖ hv ≫ m = b) :
    jO hϖ hv (D := D) ≫ trO hϖ hv m = DegPre.trPt D.toPre F b ≫ jO hϖ hv := by
  have h1 : jO hϖ hv (D := D) ≫ trO hϖ hv m ≫ snd (TO hϖ hv) D.toPre.P.A =
      snd (TF (R := V) F) D.toPre.P.A * (fst (TF (R := V) F) D.toPre.P.A ≫ b) := by
    rw [trO_snd, MonObj.comp_mul, whiskerRight_snd, ← Category.assoc, whiskerRight_fst, Category.assoc, hm]
  have h2 : DegPre.trPt D.toPre F b ≫ jO hϖ hv (D := D) ≫ snd (TO hϖ hv) D.toPre.P.A =
      snd (TF (R := V) F) D.toPre.P.A * (fst (TF (R := V) F) D.toPre.P.A ≫ b) := by
    rw [whiskerRight_snd]
    unfold DegPre.trPt
    rw [lift_snd]
    rfl
  have h3 : jO hϖ hv (D := D) ≫ trO hϖ hv m ≫ fst (TO hϖ hv) D.toPre.P.A =
      fst (TF (R := V) F) D.toPre.P.A ≫ ιS hϖ hv := by
    rw [trO_fst, whiskerRight_fst]
  have h4 : DegPre.trPt D.toPre F b ≫ jO hϖ hv (D := D) ≫ fst (TO hϖ hv) D.toPre.P.A =
      fst (TF (R := V) F) D.toPre.P.A ≫ ιS hϖ hv := by
    rw [whiskerRight_fst, ← Category.assoc, tr_fst]
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc]
    rw [h3, h4]
  · simp only [Category.assoc]
    rw [h1, h2]

theorem gen_uO (k : ℕ) (α α' : D.toPre.X) (m : TO hϖ hv ⟶ D.toPre.P.A)
    (hα : cP D.toPre _ α' = cP D.toPre _ α * m ^ k) {K : Type} [Fintype K]
    {φ : K → ((TO hϖ hv).left ⟶ D.toPre.P.A.left)} {ε : K → ℤ}
    (vO : LB.Gen (LB.LinComb D.toPre.P.L φ ε)) (hvO : vO.IsGen)
    (hF : ∀ (U : Type) [CommGroup U] (h : ((TO hϖ hv).left ⟶ D.toPre.P.A.left) → U), ∏ i, h (φ i) ^ ε i =
      (h (cP D.toPre _ α * m).left)⁻¹ * h (cP D.toPre _ α).left * h m.left * (h (1 : TO hϖ hv ⟶ D.toPre.P.A).left)⁻¹ *
        (h m.left ^ k)⁻¹ * h (1 : TO hϖ hv ⟶ D.toPre.P.A).left ^ k) :
    ∃ u : LB.Gen (LB.LinComb D.toPre.P.L (Sum.elim (fun i => (snd (TO hϖ hv) D.toPre.P.A).left ≫ D.toPre.famφB α' i)
        (fun i => (trO hϖ hv m ≫ snd _ _).left ≫ D.toPre.famφB α i)) (DegPre.deltaε k)), u.IsGen ∧
      ∀ (T : Over (Spec (CommRingCat.of V))) (ρ : T ⟶ TO hϖ hv ⊗ D.toPre.P.A) (z : T.left) (J), Good D.toPre.P.L z J →
        val u ρ.left z J = cubN (th D.toPre z J) k (cP D.toPre T α) (ρ ≫ fst _ _ ≫ m) (ρ ≫ snd _ _) *
          (th D.toPre z J (cP D.toPre T α) (ρ ≫ snd _ _) (ρ ≫ fst _ _ ≫ m))⁻¹ * val vO (ρ ≫ fst _ _).left z J := by
  let a : TO hϖ hv ⊗ D.toPre.P.A ⟶ D.toPre.P.A := cP D.toPre _ α
  let mm : TO hϖ hv ⊗ D.toPre.P.A ⟶ D.toPre.P.A := fst _ _ ≫ m
  let x : TO hϖ hv ⊗ D.toPre.P.A ⟶ D.toPre.P.A := snd _ _
  have hα' : cP D.toPre (TO hϖ hv ⊗ D.toPre.P.A) α' = a * mm ^ k := by
    rw [← comp_cP D.toPre (fst (TO hϖ hv) D.toPre.P.A), hα]
    exact (map_mul (preHom (fst (TO hϖ hv) D.toPre.P.A)) _ _).trans
      (congrArg₂ (· * ·) (comp_cP D.toPre _ α) (map_pow (preHom (fst (TO hϖ hv) D.toPre.P.A)) _ _))
  obtain ⟨N, hN, vN⟩ := exists_cubN D.toPre.cub a mm x k
  obtain ⟨u₀, hu₀, vu₀⟩ := exists_gen D.toPre.P.isLB (φ' := Sum.elim (fun i => (snd (TO hϖ hv) D.toPre.P.A).left ≫ D.toPre.famφB α' i)
      (fun i => (trO hϖ hv m ≫ snd _ _).left ≫ D.toPre.famφB α i)) (ε' := DegPre.deltaε k) (fun U _ h => by
      have p₁ := prod_cub a x mm h
      have p₂ := hF U (fun q => h ((fst (TO hϖ hv) D.toPre.P.A).left ≫ q))
      have p₃ := SectionScalarValuation.prod_famB D.toPre (snd (TO hϖ hv) D.toPre.P.A) α' k h
      have p₄ := SectionScalarValuation.prod_famB D.toPre (trO hϖ hv m ≫ snd _ _) α k h
      have q₁ : (fst (TO hϖ hv) D.toPre.P.A).left ≫ (cP D.toPre _ α * m).left = (a * mm).left :=
        congrArg (fun q : TO hϖ hv ⊗ D.toPre.P.A ⟶ D.toPre.P.A => q.left)
          ((MonObj.comp_mul (fst (TO hϖ hv) D.toPre.P.A) (cP D.toPre _ α) m).trans
            (congrArg (· * mm) (comp_cP D.toPre (fst (TO hϖ hv) D.toPre.P.A) α)))
      have q₂ : (fst (TO hϖ hv) D.toPre.P.A).left ≫ (cP D.toPre _ α).left = a.left :=
        congrArg (fun q : TO hϖ hv ⊗ D.toPre.P.A ⟶ D.toPre.P.A => q.left) (comp_cP D.toPre (fst (TO hϖ hv) D.toPre.P.A) α)
      have q₃ : (fst (TO hϖ hv) D.toPre.P.A).left ≫ (1 : TO hϖ hv ⟶ D.toPre.P.A).left =
          (1 : TO hϖ hv ⊗ D.toPre.P.A ⟶ D.toPre.P.A).left :=
        congrArg (fun q : TO hϖ hv ⊗ D.toPre.P.A ⟶ D.toPre.P.A => q.left) (MonObj.comp_one (M := D.toPre.P.A) (fst (TO hϖ hv) D.toPre.P.A))
      have q₄ : (fst (TO hϖ hv) D.toPre.P.A).left ≫ m.left = mm.left := rfl
      rw [q₁, q₂, q₃, q₄] at p₂
      have c₁ : SectionScalarValuation.cQ D.toPre (TO hϖ hv ⊗ D.toPre.P.A) α' = a * mm ^ k := hα'
      have c₂ : SectionScalarValuation.cQ D.toPre (TO hϖ hv ⊗ D.toPre.P.A) α = a := rfl
      rw [c₁] at p₃
      rw [c₂] at p₄
      conv at p₄ => rhs; rw [trO_snd]
      refine Eq.trans (prod_sum₂ (K := Fin 8 ⊕ thK) (K' := K) (U := U) _
        (prod_sum₂ (K := Fin 8) (K' := thK) (U := U) _ rfl (prod_neg _ _ p₁)) p₂)
        (Eq.trans ?_ (prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _ p₃ (prod_neg _ _ p₄)).symm)
      have r1 : x * (a * mm ^ k) = a * mm ^ k * x := mul_comm _ _
      have r2 : x * mm * a = a * x * mm := by rw [mul_comm, ← _root_.mul_assoc]
      have r3 : mm * x = x * mm := mul_comm _ _
      rw [r1, r2, r3]
      apply Additive.ofMul.injective
      simp [Fin.prod_univ_succ, ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow, a, mm, x]
      module)
    (LB.mulGen D.toPre.P.L _ _ _ _ (LB.mulGen D.toPre.P.L _ _ _ _ N (LB.invGen D.toPre.P.L _ _
      (LB.pullGen D.toPre.P.L (thφ D.toPre.P.A (x3 D.toPre.P.A)) thε D.toPre.cub.t (lift a (lift x mm)).left)))
      (LB.pullGen D.toPre.P.L _ _ vO (fst (TO hϖ hv) D.toPre.P.A).left))
    (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ hN (invGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ D.toPre.cub.isGen _)))
      (pullGen_isGen _ _ _ _ hvO _))
  refine ⟨u₀, hu₀, fun T ρ z J hJ => ?_⟩
  refine (vu₀ _ _ z J hJ).trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
    ((congrArg₂ (· * ·) (vN T ρ z J hJ) ((val_inv _ _).trans (congrArg (·⁻¹) (val_cub D.toPre.cub ρ hJ _ _ _)))).trans ?_))
    (val_pull hJ _ _ _)))
  rw [← comp_cP D.toPre ρ α]

end ReciprocityTheory.ChartRestriction.G.DVR.TWM
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.CubicNormMulIdentity
set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.DVR.UUA

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1

variable {A U : Type} [CommGroup A] [CommGroup U] {θ : A → A → A → U}

theorem four (h : IsCub θ) (P q B b x : A) :
    θ (P * B) (q * b) x * θ P B x * θ q b x = θ (P * q) (B * b) x * θ P q x * θ B b x := by
  have c1 := h.coc P B (q * b) x
  have c2 := h.coc B q b x
  have c3 := h.coc P q (B * b) x
  have c4 := h.coc q B b x
  rw [mul_left_comm B q b] at c1
  rw [mul_comm q B, h.s01 q B x] at c4
  calc θ (P * B) (q * b) x * θ P B x * θ q b x
      = θ P (q * (B * b)) x * (θ B (q * b) x * θ q b x) := by rw [c1, mul_assoc]
    _ = θ P (q * (B * b)) x * (θ q (B * b) x * θ B b x) := by rw [← c2, c4]
    _ = θ (P * q) (B * b) x * θ P q x * θ B b x := by rw [c3, mul_assoc]

theorem cubic_norm_mul_identity (h : IsCub θ) (k : ℕ) (B b x : A) :
    θ (B ^ k) (b ^ k) x * cubN θ k 1 B x * cubN θ k 1 b x = cubN θ k 1 (B * b) x * θ B b x ^ k := by
  induction k with
  | zero => simp [cubN, h.face]
  | succ k ih =>
    have f := four h (B ^ k) (b ^ k) B b x
    simp only [cubN, one_mul] at ih ⊢
    rw [Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ, pow_succ B, pow_succ b,
      pow_succ (θ B b x), mul_pow]
    apply mul_right_cancel (b := θ (B ^ k) (b ^ k) x)
    calc _ = (θ (B ^ k * B) (b ^ k * b) x * θ (B ^ k) B x * θ (b ^ k) b x) *
          (θ (B ^ k) (b ^ k) x * (∏ i ∈ Finset.range k, θ (B ^ i) B x) *
            ∏ i ∈ Finset.range k, θ (b ^ i) b x) := by ac_rfl
      _ = _ := by rw [f, ih]; ac_rfl

theorem cubN_mul (h : IsCub θ) (k : ℕ) (a B b x : A) :
    cubN θ k a B x * cubN θ k (a * B ^ k) b x * (θ B x b ^ k)⁻¹ = cubN θ k a (B * b) x := by
  have e1 := cubic_norm_mul_identity h k B b x
  have c := h.coc a (B ^ k) (b ^ k) x
  rw [h.N_split k a B x, h.N_split k (a * B ^ k) b x, h.N_split k a (B * b) x, mul_pow, h.s12 B x b]
  apply mul_right_cancel (b := θ (B ^ k) (b ^ k) x * θ B b x ^ k)
  calc _ = (θ (a * B ^ k) (b ^ k) x * θ a (B ^ k) x) *
        (θ (B ^ k) (b ^ k) x * cubN θ k 1 B x * cubN θ k 1 b x) * ((θ B b x ^ k)⁻¹ * θ B b x ^ k) := by
        ac_rfl
    _ = (θ a (B ^ k * b ^ k) x * θ (B ^ k) (b ^ k) x) * (cubN θ k 1 (B * b) x * θ B b x ^ k) := by
        rw [c, e1, inv_mul_cancel, mul_one]
    _ = _ := by ac_rfl

theorem hv_comp (h : IsCub θ) (k : ℕ) (a B b x : A) :
    hv θ k a B (x * b) * hv θ k (a * B ^ k) b x = hv θ k a (B * b) x * hv θ k a B b := by
  have n := h.N_add k a B x b
  have m := cubN_mul h k a B b x
  have t : ∀ u v, θ a u v = θ u v a := fun u v => (h.s01 a u v).trans (h.s12 u a v)
  have key : θ a x b * θ a (x * b) B = θ a x (B * b) * θ a b B := by
    have c := h.coc x b B a
    rw [t x b, t (x * b) B, t x (B * b), t b B, mul_comm B b, mul_comm (θ x b a)]
    exact c
  simp only [hv]
  apply mul_right_cancel (b := θ a x b * θ a (x * b) B * θ (a * B ^ k) x b * θ B x b ^ k)
  rw [← m]
  calc _ = (cubN θ k a B (x * b) * θ a x b * θ B x b ^ k) * cubN θ k (a * B ^ k) b x *
        ((θ a (x * b) B)⁻¹ * θ a (x * b) B) * ((θ (a * B ^ k) x b)⁻¹ * θ (a * B ^ k) x b) := by ac_rfl
    _ = θ (a * B ^ k) x b * cubN θ k a B x * cubN θ k a B b * cubN θ k (a * B ^ k) b x := by
        rw [n, inv_mul_cancel, inv_mul_cancel, mul_one, mul_one]
    _ = (cubN θ k a B x * cubN θ k (a * B ^ k) b x * cubN θ k a B b * θ (a * B ^ k) x b) *
        ((θ B x b ^ k)⁻¹ * θ B x b ^ k) * ((θ a x (B * b))⁻¹ * θ a x (B * b)) * ((θ a b B)⁻¹ * θ a b B) := by
        rw [inv_mul_cancel, inv_mul_cancel, inv_mul_cancel, mul_one, mul_one, mul_one]; ac_rfl
    _ = _ := by rw [key]; ac_rfl

end ReciprocityTheory.ChartRestriction.G.DVR.UUA
end
end
