module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompatibleIsometriesCoisotropicKernels

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEquivLatticePartZeroIffMemNsmul
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEquivLatticePartZeroIffMemNsmul
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LowDat GlobalTheory.LowFilt
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LowFilt

theorem exists_equiv_y_eq_zero_iff : ∀ (R : Type) [CommRing R] [IsDomain R] (D₀ : DegPre R), D₀.TauBimult →
    ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (n : ℕ), 0 < n → ∀ p : QkPt D₀ F n,
    (∃ q : QkPt D₀ F n, QkPt.Equiv D₀ F p q ∧ q.y = 0) ↔ ∃ e, p.y = n • e := by
  intro R _ _ D₀ hB F _ _ n _ p
  constructor
  · rintro ⟨q, hq, hy⟩
    obtain ⟨z, hz, -⟩ := (GlobalTheory.TorusExt.equiv_iff hB p q).1 hq
    refine ⟨-z, ?_⟩
    rw [smul_neg, eq_neg_iff_add_eq_zero, ← hz, hy]
  · rintro ⟨e, he⟩
    refine ⟨GlobalTheory.TorusExt.qkShift hB p (-e), GlobalTheory.TorusExt.equiv_qkShift hB p (-e), ?_⟩
    show p.y + n • (-e) = 0
    rw [he, smul_neg, add_neg_cancel]

end GlobalTheory.LowFilt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEquivLatticePartZeroIffMemNsmulStatement
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LowDat GlobalTheory.LowFilt
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_equiv_latticePart_zero_iff_mem_nsmul : ∀ (R : Type) [CommRing R] [IsDomain R] (D₀ : DegPre R), D₀.TauBimult →
    ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (n : ℕ), 0 < n → ∀ p : QkPt D₀ F n,
    (∃ q : QkPt D₀ F n, QkPt.Equiv D₀ F p q ∧ q.y = 0) ↔ ∃ e, p.y = n • e := by
  first | exact @GlobalTheory.LowFilt.exists_equiv_y_eq_zero_iff | exact GlobalTheory.LowFilt.exists_equiv_y_eq_zero_iff | (intros; apply GlobalTheory.LowFilt.exists_equiv_y_eq_zero_iff <;> assumption)
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelIsometryExtensionAlgClosed
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelIsometryExtensionAlgClosed
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LowDat GlobalTheory.LowFilt
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LowDat

theorem exists_xfLevel_ext {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    (Xo : Moduli Dw l) (c : Coeff l) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (hR : GlobalTheory.Mum.Base R)
    (C : GlobalTheory.UChart.Fam Xo c R) (tK : SAB H (Sp (FractionRing R)))
    (m1 : SABMap tK C.t (jK R)) (m2 : SABMap tK Xo.univ.t (C.y ≫ pullback.fst _ _))
    (I₀ : letI := H.starRing; TateIsoQ Dw C.P.D.toPre C.P.oD (AlgebraicClosure (FractionRing R)))
    (hI₀ : GlobalTheory.LowDat.XFLevel C tK m1 m2 (AlgebraicClosure (FractionRing R)) I₀)
    (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] :
    ∃ I : (letI := H.starRing; TateIsoQ Dw C.P.D.toPre C.P.oD F), GlobalTheory.LowDat.XFLevel C tK m1 m2 F I ∧
      ∀ n a, (I.ev n a).y = (I₀.ev n a).y := by
  have hLL := GlobalTheory.firstFiveLaws
  have hL : Laws := hLL.1
  have hL₂ : Laws2 := hLL.2.1
  haveI : CharZero R := hR.2
  haveI : IsNoetherianRing R := hR.1.1
  haveI : CharZero (FractionRing R) := charZero_of_injective_ringHom (IsFractionRing.injective R (FractionRing R))
  haveI : CharZero (AlgebraicClosure (FractionRing R)) :=
    charZero_of_injective_ringHom (algebraMap (FractionRing R) (AlgebraicClosure (FractionRing R))).injective
  have hB := C.P.D.tau_bimult
  have he := C.P.D.psi_even
  let s : AlgebraicClosure (FractionRing R) →ₐ[FractionRing R] F := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  have hs : s.toRingHom.comp (algebraMap (FractionRing R) _) = algebraMap (FractionRing R) F := s.comp_algebraMap
  have hj : spMap s.toRingHom ≫ jFK (R := R) (AlgebraicClosure (FractionRing R)) = jFK (R := R) F := by
    rw [jFK, jFK, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hs]
  let I := GlobalTheory.ArcExt.tateExt s.toRingHom hs hB hL I₀ (GlobalTheory.ArcOfModel.weilQkIs_qkExt hL hL₂ he hB s.toRingHom hs)
  have hext : ∀ n a, QkExt s.toRingHom (I₀.ev n a) (I.ev n a) := fun n a =>
    (GlobalTheory.TorusExt.qkExt_iff hB _ hs _ _).2 rfl
  refine ⟨I, ⟨?_, ?_⟩, fun n a => (hext n a).1⟩
  · show ((Units.map s.toRingHom.toMonoidHom (I₀.ζ l.M') : Fˣ) : F) = _
    rw [Units.coe_map]
    show s.toRingHom ((I₀.ζ l.M' : AlgebraicClosure (FractionRing R))) = _
    rw [hI₀.1]
    simp only [toF, RingHom.comp_apply]
    exact s.commutes _
  · intro k a σ hk x hx
    have hk1 : 1 ≤ k := by
      rcases hk with ⟨rfl, -⟩ | ⟨rfl, -⟩
      · exact l.A_pos
      · have := l.three_le; omega
    have hT := GlobalTheory.FlatTors.torsionIso_holds E H R (maximalIdeal R) hR.1 C.t C.P
    obtain ⟨f₀, f₀₁, -⟩ := hT (AlgebraicClosure (FractionRing R)) k hk1
    obtain ⟨fF, fF₁, -⟩ := hT F k hk1
    obtain ⟨g₀, hg₁, hg₂⟩ := hI₀.2 k a σ hk (f₀ (I₀.ev k a)) ((f₀₁ _ _).2 rfl)
    let x' : TFK (R := R) F ⟶ C.P.A.A :=
      (Over.homMk (spMap s.toRingHom) hj : TFK (R := R) F ⟶ TFK (R := R) (AlgebraicClosure (FractionRing R))) ≫
        f₀ (I₀.ev k a)
    have hx' : C.P.ToA F k (I.ev k a) x' :=
      (GlobalTheory.TorsionExt.qkToAkU_iff_of_qkExt hLL R (maximalIdeal R) hR.1 C.P.D C.P.A C.t.G C.t.semi C.P.U _ F s k hk1
        (I₀.ev k a) (I.ev k a) _ x' (hext k a) rfl).1 ((f₀₁ _ _).2 rfl)
    have hxx : x = x' := ((fF₁ _ _).1 hx).trans ((fF₁ _ _).1 hx').symm
    refine ⟨spMap s.toRingHom ≫ g₀, ?_, ?_⟩
    · rw [Category.assoc, hg₁, hxx]
      simp only [x', Over.comp_left, Over.homMk_left, Category.assoc]
    · rw [Category.assoc, hg₂, ← hj]
      simp only [Category.assoc]

end GlobalTheory.LowDat
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelIsometryExtensionAlgClosedStatement
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LowDat GlobalTheory.LowFilt
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_levelIsometry_extension_algClosed : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) (c : Coeff l) (R : Type) [CommRing R] [IsDomain R]
    [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (C : GlobalTheory.UChart.Fam Xo c R) (tK : SAB H (Sp (FractionRing R)))
    (m1 : SABMap tK C.t (jK R)) (m2 : SABMap tK Xo.univ.t (C.y ≫ pullback.fst _ _))
    (I₀ : letI := H.starRing; TateIsoQ Dw C.P.D.toPre C.P.oD (AlgebraicClosure (FractionRing R))),
    GlobalTheory.LowDat.XFLevel C tK m1 m2 (AlgebraicClosure (FractionRing R)) I₀ →
    ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F],
    ∃ I : (letI := H.starRing; TateIsoQ Dw C.P.D.toPre C.P.oD F), GlobalTheory.LowDat.XFLevel C tK m1 m2 F I ∧
      ∀ n a, (I.ev n a).y = (I₀.ev n a).y := by
  first | exact @GlobalTheory.LowDat.exists_xfLevel_ext | exact GlobalTheory.LowDat.exists_xfLevel_ext | (intros; apply GlobalTheory.LowDat.exists_xfLevel_ext <;> assumption)
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankLeMin
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankLeMin
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LowDat GlobalTheory.LowFilt
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UChart.Fam

open Classical

theorem finrank_le_min : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    (Xo : Moduli Dw l) (c : Coeff l) (R : Type) [CommRing R] [IsDomain R]
    [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ C : GlobalTheory.UChart.Fam Xo c R,
    Module.finrank (𝓞 E) C.P.D.toPre.X ≤ min Dw.p Dw.q := by
  intro E _ _ _ H Dw l Xo c R _ _ _ hB C
  obtain ⟨hadm, hch⟩ := hB
  haveI : IsNoetherianRing R := hadm.1
  haveI : CharZero R := hch
  obtain ⟨tK, ⟨m₁⟩, ⟨m₂⟩⟩ := C.gen
  let K := AlgebraicClosure (FractionRing R)
  let g : FractionRing R →+* K := algebraMap (FractionRing R) K
  let f : R →+* K := g.comp (algebraMap R (FractionRing R))
  have hf : Function.Injective f :=
    (algebraMap (FractionRing R) K).injective.comp (IsFractionRing.injective R (FractionRing R))
  haveI : CharZero K := ⟨fun a b h => Nat.cast_injective (R := R) (hf (by simpa using h))⟩
  let x' : Sp K ⟶ Xo.X := spMap g ≫ C.y ≫ pullback.fst _ _
  obtain ⟨β₀, hβ₀⟩ := Spec.map_surjective (x' ≫ Xo.s)
  have hβ : x' ≫ Xo.s = spMap β₀.hom := hβ₀.symm
  have hdet := (Xo.univ.geom K x' β₀.hom hβ).1
  have hr : (β₀.hom (baseKA l).ρ) ^ 2 = -(H.d : K) := by
    rw [← map_pow, (baseKA l).ρ_sq, map_neg, map_natCast]
  have hjK : spMap g ≫ jK R = spMap f := by
    show Spec.map _ ≫ Spec.map _ = _
    rw [← Spec.map_comp]
    rfl
  have bound : ∀ (τ : 𝓞 E →+* K) (N : ℕ), LieMult Xo.univ.t.act x' τ N →
      Module.finrank (𝓞 E) C.P.D.toPre.X ≤ N := by
    intro τ N hN
    have h₅ := (GlobalTheory.lieMult_iff_of_isGrpPullback m₂.cart tK.act Xo.univ.t.act m₂.act (spMap g) τ N).2 hN
    have h₆ := (GlobalTheory.lieMult_iff_of_isGrpPullback m₁.cart tK.act C.t.act m₁.act (spMap g) τ N).1 h₅
    rw [hjK] at h₆
    obtain ⟨n, -, hn⟩ := GlobalTheory.CharRank.lieMult_unif_loc H R C.t C.P K f hf τ N h₆
    omega
  obtain ⟨τ₁, τ₂, h₁, h₂⟩ := GlobalTheory.CharRank.exists_chars H K _ hr
  exact le_min (bound τ₁ _ ((hdet τ₁).1 h₁)) (bound τ₂ _ ((hdet τ₂).2 h₂))

end GlobalTheory.UChart.Fam
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankLeMinStatement
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LowDat GlobalTheory.LowFilt
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_uChart_le_min_signature : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) (c : Coeff l) (R : Type) [CommRing R] [IsDomain R]
    [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ C : GlobalTheory.UChart.Fam Xo c R,
    Module.finrank (𝓞 E) C.P.D.toPre.X ≤ min Dw.p Dw.q := by
  first | exact @GlobalTheory.UChart.Fam.finrank_le_min | exact GlobalTheory.UChart.Fam.finrank_le_min | (intros; apply GlobalTheory.UChart.Fam.finrank_le_min <;> assumption)
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateIsoLatticePartSurjectiveCoisotropicKernel
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateIsoLatticePartSurjectiveCoisotropicKernel
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LowDat GlobalTheory.LowFilt
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LowFilt

open GlobalTheory.Ex

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem exists_nsmul_of_dvd (D : Datum H) {n : ℕ} (hn : 0 < n) {b : D.La} (h : ∀ a, (n : ℤ) ∣ D.EF b a) :
    ∃ e, b = n • e := by
  choose f hf using h
  have hn' : (n : ℤ) ≠ 0 := Int.natCast_ne_zero.2 hn.ne'
  let g : D.La →ₗ[ℤ] ℤ :=
    { toFun := f
      map_add' := fun a a' => mul_left_cancel₀ hn' (by rw [mul_add, ← hf, ← hf, ← hf, map_add (f := _)])
      map_smul' := fun c a => mul_left_cancel₀ hn' (by
        rw [← hf, map_smul, hf, smul_eq_mul, RingHom.id_apply, smul_eq_mul, mul_left_comm]) }
  obtain ⟨e, he⟩ := D.unimod.2 g
  refine ⟨e, D.unimod.1 (LinearMap.ext fun a => ?_)⟩
  rw [map_nsmul, LinearMap.smul_apply, he, nsmul_eq_mul]
  exact hf a

theorem exists_linear_lift {R M X : Type} [CommRing R] [AddCommGroup M] [Module R M] [Module.Projective R M]
    [AddCommGroup X] [Module R X] (n : ℕ) (Y : M → X) (hadd : ∀ a b, ∃ e, Y (a + b) = Y a + Y b + n • e)
    (hsmul : ∀ (c : R) a, ∃ e, Y (c • a) = c • Y a + n • e) : ∃ y : M →ₗ[R] X, ∀ a, ∃ e, y a = Y a + n • e := by
  let S : Submodule R X := LinearMap.range (n • LinearMap.id : X →ₗ[R] X)
  have mem : ∀ x : X, x ∈ S ↔ ∃ e, n • e = x := fun x => Iff.rfl
  have h0 : ∀ e : X, S.mkQ (n • e) = 0 := fun e => (Submodule.Quotient.mk_eq_zero S).2 ((mem _).2 ⟨e, rfl⟩)
  let g : M →ₗ[R] X ⧸ S :=
    { toFun := fun a => S.mkQ (Y a)
      map_add' := fun a b => by
        obtain ⟨e, he⟩ := hadd a b
        rw [he, map_add (f := _), h0, add_zero, map_add (f := _)]
      map_smul' := fun c a => by
        obtain ⟨e, he⟩ := hsmul c a
        rw [he, map_add (f := _), h0, add_zero, map_smul, RingHom.id_apply] }
  obtain ⟨h, hh⟩ := Module.projective_lifting_property S.mkQ g (Submodule.mkQ_surjective S)
  refine ⟨h, fun a => ?_⟩
  have := congrArg (fun φ : M →ₗ[R] X ⧸ S => φ a) hh
  simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply, g, LinearMap.coe_mk, AddHom.coe_mk] at this
  obtain ⟨e, he⟩ := (mem _).1 ((Submodule.Quotient.eq S).1 this)
  exact ⟨e, by rw [he, add_sub_cancel]⟩

theorem torus_pair (D : Datum H) {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    (D₀ : DegPre R) [Module (𝓞 E) D₀.X] (oa : letI := H.starRing; D₀.OAct (𝓞 E)) (hev : D₀.PsiEven)
    (hB : D₀.TauBimult) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (I : TateIsoQ D D₀ oa F)
    (n : ℕ) (hn : 0 < n) (t t' : Multiplicative D₀.X →* Fˣ) (ht : t ^ n = 1) (ht' : t' ^ n = 1) :
    ∃ b b' : D.La, (∃ e, (I.ev n b).y = n • e) ∧
      (∀ a, I.ζ n ^ D.EF b a = t (Multiplicative.ofAdd (I.ev n a).y)) ∧
      (∀ a, I.ζ n ^ D.EF b' a = t' (Multiplicative.ofAdd (I.ev n a).y)) ∧ ((∃ e, b = b' + n • e) → t = t') := by
  obtain ⟨hL, hL₂, -⟩ := GlobalTheory.firstFiveLaws
  obtain ⟨N, ν, -⟩ := ValuesExist.exists_integral_values hL R D₀ hev hB F ⊤ fun _ => trivial
  have hGt := GtValues.points_correspond R D₀ hev hB F N ν
  have hWp := WeilValues.weil_eq_values GtValues.points_correspond (brFam hL hL₂) R D₀ hev hB F N ν n hn
  have G := hGt.2.2.2.2 n
  choose Q hQ using fun a => (G.1 (I.ev n a)).exists
  let tr : (Multiplicative D₀.X →* Fˣ) → (Multiplicative N.X →* Fˣ) := fun s =>
    s.comp (AddEquiv.toMultiplicative ν.eX).toMonoidHom
  have trn : ∀ s : Multiplicative D₀.X →* Fˣ, s ^ n = 1 → tr s ^ n = 1 := fun s hs => by
    refine MonoidHom.ext fun χ => ?_
    have := congrArg (fun g : Multiplicative D₀.X →* Fˣ => g ((AddEquiv.toMultiplicative ν.eX).toMonoidHom χ)) hs
    rw [MonoidHom.pow_apply, MonoidHom.one_apply] at this ⊢
    exact this
  have one : ∀ (s : Multiplicative D₀.X →* Fˣ) (hs : s ^ n = 1), ∃ b, N.QEq (Q b) (N.qTor (tr s) (trn s hs)) ∧
      ∀ a, I.ζ n ^ D.EF b a = s (Multiplicative.ofAdd (I.ev n a).y) := by
    intro s hs
    obtain ⟨p₀, hp₀⟩ := G.2.1 (N.qTor (tr s) (trn s hs))
    obtain ⟨b, hb⟩ := I.onto n hn p₀
    have hq := (G.2.2 _ _ _ _ (hQ b) hp₀).1 hb
    refine ⟨b, hq, fun a => Units.ext ?_⟩
    have h1 := (hWp _ _ _ _ _ (hQ b) (hQ a)).1 (I.isom n hn b a)
    rw [h1, WpPairing.wp_congr_left N hq, NumD.wp_qTor, ← (hQ a).1]
    rfl
  obtain ⟨b, hq, hb⟩ := one t ht
  obtain ⟨b', hq', hb'⟩ := one t' ht'
  refine ⟨b, b', ?_, hb, hb', fun hbb => ?_⟩
  · obtain ⟨z, hz, -⟩ := hq
    refine ⟨ν.eX (-z), ?_⟩
    rw [← (hQ b).1, map_neg, smul_neg, ← map_nsmul, eq_neg_iff_add_eq_zero, ← map_add (f := _), ← hz]
    exact map_zero _
  · have h₁ := (G.2.2 _ _ _ _ (hQ b) (hQ b')).1 ((I.ker n hn b b').2 hbb)
    have eqv : Equivalence (N.QEq (k := n)) := by
      refine ⟨fun p => ⟨0, by simp, by simp⟩, ?_, ?_⟩
      · rintro p p' ⟨z, h, h'⟩
        exact ⟨-z, by rw [h, smul_neg, add_neg_cancel_right], by rw [h', N.io_neg, mul_inv_cancel_right]⟩
      · rintro p p' p'' ⟨z, h, h'⟩ ⟨w, e, e'⟩
        exact ⟨z + w, by rw [e, h, smul_add, add_assoc], by rw [e', h', N.io_add, _root_.mul_assoc]⟩
    have h₂ := eqv.trans (eqv.trans (eqv.symm hq) h₁) hq'
    obtain ⟨z, hz, hz'⟩ := h₂
    have hz0 : z = 0 := by
      have e : (n : ℤ) • z = 0 := by
        rw [natCast_zsmul]
        have : (0 : N.X) = 0 + n • z := hz
        rw [zero_add] at this
        exact this.symm
      exact (smul_eq_zero.1 e).resolve_left (Int.natCast_ne_zero.2 hn.ne')
    subst hz0
    have e : N.tor (tr t') = N.tor (tr t) := by
      have h := hz'
      rw [NumD.io_zero, _root_.mul_one] at h
      exact h
    have e' := NumD.tor_injective N e
    refine MonoidHom.ext fun χ => ?_
    have := congrArg (fun s : Multiplicative N.X →* Fˣ => s (Multiplicative.ofAdd (ν.eX.symm χ.toAdd))) e'
    simpa [tr] using this.symm

theorem exists_char {X F : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [Field F] {n : ℕ} {ζ : F}
    (hζ : IsPrimitiveRoot ζ n) (hn : 0 < n) (S : AddSubgroup X) (x : X) (hx : ∀ s ∈ S, ∀ e, s ≠ x + n • e) :
    ∃ t : Multiplicative X →* Fˣ, t ^ n = 1 ∧ (∀ s ∈ S, t (Multiplicative.ofAdd s) = 1) ∧ t (Multiplicative.ofAdd x) ≠ 1 := by
  let T : AddSubgroup X := S ⊔ (nsmulAddMonoidHom (α := X) n).range
  have hxT : (QuotientAddGroup.mk x : X ⧸ T) ≠ 0 := by
    rw [Ne, QuotientAddGroup.eq_zero_iff]
    intro h
    obtain ⟨s, hs, z, ⟨w, rfl⟩, hsz⟩ := AddSubgroup.mem_sup.1 h
    exact hx s hs (-w) (by rw [← hsz, nsmulAddMonoidHom_apply, smul_neg, add_neg_cancel_right])
  obtain ⟨c, hc⟩ := CharacterModule.exists_character_apply_ne_zero_of_ne_zero hxT
  let g : X →ₗ[ℤ] AddCircle (1 : ℚ) := c ∘ₗ (QuotientAddGroup.mk' T).toIntLinearMap
  have gS : ∀ v ∈ T, g v = 0 := fun v hv => by
    change c (QuotientAddGroup.mk v) = 0
    rw [(QuotientAddGroup.eq_zero_iff v).2 hv, map_zero]
  have gn : ∀ v, n • g v = 0 := fun v => by
    rw [← map_nsmul]
    exact gS _ (AddSubgroup.mem_sup_right ⟨v, rfl⟩)
  let b := Module.Free.chooseBasis ℤ X
  choose r hr using fun i => QuotientAddGroup.mk_surjective (g (b i))
  have hm : ∀ i, ∃ m : ℤ, (m : ℚ) = n * r i := fun i => by
    have := gn (b i)
    rw [← hr i, ← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_zmultiples_iff] at this
    obtain ⟨m, hm⟩ := this
    exact ⟨m, by rw [← nsmul_eq_mul, ← hm, zsmul_eq_mul, _root_.mul_one]⟩
  choose m hm using hm
  let φ : X →ₗ[ℤ] ℚ := b.constr ℤ r
  let ψ : X →ₗ[ℤ] ℤ := b.constr ℤ m
  have hψ : ∀ v, (ψ v : ℚ) = n * φ v := by
    have : (Int.castAddHom ℚ).toIntLinearMap ∘ₗ ψ = (n : ℤ) • φ := b.ext fun i => by
      simp [ψ, φ, hm]
    intro v
    have := congrArg (fun f : X →ₗ[ℤ] ℚ => f v) this
    simpa using this
  have hφ : ∀ v, (QuotientAddGroup.mk (φ v) : AddCircle (1 : ℚ)) = g v := by
    have : (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℚ))).toIntLinearMap ∘ₗ φ = g := b.ext fun i => by
      simp [φ, hr]
    intro v
    exact congrArg (fun f : X →ₗ[ℤ] AddCircle (1 : ℚ) => f v) this
  have key : ∀ v, g v = 0 ↔ (n : ℤ) ∣ ψ v := fun v => by
    rw [← hφ, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_zmultiples_iff]
    have hn' : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
    constructor
    · rintro ⟨k, hk⟩
      refine ⟨k, ?_⟩
      have : (ψ v : ℚ) = ((n * k : ℤ) : ℚ) := by rw [hψ, ← hk]; push_cast; ring
      exact_mod_cast this
    · rintro ⟨k, hk⟩
      refine ⟨k, ?_⟩
      have := hψ v
      rw [hk] at this
      push_cast at this
      rw [zsmul_eq_mul, _root_.mul_one]
      exact mul_left_cancel₀ hn' this
  let ζu : Fˣ := (hζ.isUnit hn.ne').unit
  have hζu : IsPrimitiveRoot ζu n := IsPrimitiveRoot.coe_units_iff.1 (by simpa [ζu] using hζ)
  let t : Multiplicative X →* Fˣ :=
    { toFun := fun χ => ζu ^ ψ (Multiplicative.toAdd χ)
      map_one' := by simp
      map_mul' := fun a a' => by simp [zpow_add] }
  have tv : ∀ v, t (Multiplicative.ofAdd v) = 1 ↔ (n : ℤ) ∣ ψ v := fun v => hζu.zpow_eq_one_iff_dvd _
  refine ⟨t, MonoidHom.ext fun χ => ?_, fun s hs => (tv s).2 ((key s).1 (gS s (AddSubgroup.mem_sup_left hs))),
    fun h => hc ((key x).2 ((tv x).1 h))⟩
  rw [MonoidHom.pow_apply, MonoidHom.one_apply]
  change (ζu ^ ψ (Multiplicative.toAdd χ)) ^ n = 1
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hζu.pow_eq_one, one_zpow]

theorem tateIsoQ_y_cois : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) (R : Type)
    [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    (D₀ : DegPre R) [Module (𝓞 E) D₀.X] (oa : letI := H.starRing; D₀.OAct (𝓞 E)), D₀.PsiEven → D₀.TauBimult →
    ∀ (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra (FractionRing R) F] (I : TateIsoQ D D₀ oa F),
    ∃ y : ℕ → D.La →ₗ[𝓞 E] D₀.X, (∀ n, 0 < n → ∀ a, ∃ e, y n a = (I.ev n a).y + n • e) ∧
      ∀ n, 0 < n → Cois D (y n) n := by
  intro E _ _ _ H D R _ _ _ _ D₀ _ oa hev hB F _ _ _ _ I
  letI := H.starRing
  haveI := D.proj
  have lift : ∀ n, ∃ y : D.La →ₗ[𝓞 E] D₀.X, 0 < n → ∀ a, ∃ e, y a = (I.ev n a).y + n • e := fun n => by
    by_cases hn : 0 < n
    · have h₁ : ∀ a b, ∃ e, (I.ev n (a + b)).y = (I.ev n a).y + (I.ev n b).y + n • e := fun a b => by
        obtain ⟨q, hq, -, z, hz, -⟩ := I.add n hn a b
        exact ⟨z, by rw [hz, hq]⟩
      have h₂ : ∀ (c : 𝓞 E) a, ∃ e, (I.ev n (c • a)).y = c • (I.ev n a).y + n • e := fun c a => by
        obtain ⟨q, hq, -, z, hz, -⟩ := I.lin n hn c a
        exact ⟨z, by rw [hz, hq]⟩
      obtain ⟨y, hy⟩ := exists_linear_lift (R := 𝓞 E) (M := D.La) n (fun a => (I.ev n a).y) h₁ h₂
      exact ⟨y, fun _ => hy⟩
    · exact ⟨0, fun h => absurd h hn⟩
  choose y hy using lift
  refine ⟨y, hy, fun n hn => ?_⟩
  have hζ : IsPrimitiveRoot ((I.ζ n : Fˣ) : F) n := IsPrimitiveRoot.coe_units_iff.2 (I.ζ_prim n hn)
  have tv : ∀ t : Multiplicative D₀.X →* Fˣ, t ^ n = 1 → ∀ a,
      t (Multiplicative.ofAdd (I.ev n a).y) = t (Multiplicative.ofAdd (y n a)) := by
    intro t ht a
    obtain ⟨e, he⟩ := hy n hn a
    rw [he, ofAdd_add, map_mul, ofAdd_nsmul, map_pow, ← MonoidHom.pow_apply, ht, MonoidHom.one_apply, _root_.mul_one]
  have dv : ∀ c : D.La, (∀ a, I.ζ n ^ D.EF c a = 1) → ∃ e, c = n • e := fun c h =>
    exists_nsmul_of_dvd D hn fun a => ((I.ζ_prim n hn).zpow_eq_one_iff_dvd _).1 (h a)
  refine ⟨fun x => ?_, fun a ha => ?_⟩
  · by_contra hx
    push_neg at hx
    obtain ⟨t, ht, hS, hx'⟩ := exists_char hζ hn (LinearMap.range (y n)).toAddSubgroup x (by
      rintro s ⟨a, rfl⟩ e
      exact hx a e)
    obtain ⟨b, b', -, h1, h2, h3⟩ := torus_pair D D₀ oa hev hB F I n hn t 1 ht (one_pow n)
    obtain ⟨e, he⟩ := dv b fun a => by rw [h1, tv t ht]; exact hS _ ⟨a, rfl⟩
    obtain ⟨e', he'⟩ := dv b' fun a => by rw [h2]; rfl
    exact hx' (by rw [h3 ⟨e - e', by rw [he, he', smul_sub, add_sub_cancel]⟩]; rfl)
  · by_contra hne
    push_neg at hne
    obtain ⟨t, ht, -, hx'⟩ := exists_char hζ hn ⊥ (y n a) (by
      intro s hs e h
      rw [AddSubgroup.mem_bot] at hs
      subst hs
      exact hne (-e) (by rw [smul_neg]; exact eq_neg_of_add_eq_zero_left h.symm))
    obtain ⟨b, -, ⟨e, he⟩, h1, -⟩ := torus_pair D D₀ oa hev hB F I n hn t 1 ht (one_pow n)
    obtain ⟨e', he'⟩ := hy n hn b
    obtain ⟨k, hk⟩ := ha b ⟨e + e', by rw [he', he, smul_add]⟩
    apply hx'
    rw [← tv t ht, ← h1, ef_swap, hk]
    exact ((I.ζ_prim n hn).zpow_eq_one_iff_dvd _).2 ⟨-k, by ring⟩

end GlobalTheory.LowFilt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateIsoLatticePartSurjectiveCoisotropicKernelStatement
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LowDat GlobalTheory.LowFilt
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tateIso_latticePart_surjective_coisotropicKernel : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    (D₀ : DegPre R) [Module (𝓞 E) D₀.X] (oa : letI := H.starRing; D₀.OAct (𝓞 E)), D₀.PsiEven → D₀.TauBimult →
    ∀ (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra (FractionRing R) F] (I : TateIsoQ D D₀ oa F),
    ∃ y : ℕ → D.La →ₗ[𝓞 E] D₀.X, (∀ n, 0 < n → ∀ a, ∃ e, y n a = (I.ev n a).y + n • e) ∧
      ∀ n, 0 < n → Cois D (y n) n := by
  first | exact @GlobalTheory.LowFilt.tateIsoQ_y_cois | exact GlobalTheory.LowFilt.tateIsoQ_y_cois | (intros; apply GlobalTheory.LowFilt.tateIsoQ_y_cois <;> assumption)
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelIsometryGenericFibreBoundaryChart
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelIsometryGenericFibreBoundaryChart
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LowDat GlobalTheory.LowFilt
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LowDat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem exists_tateIso_roots {Dw : Datum H} (l : Level H) {k : Type} [Field k] {Q : Type} [Group Q]
    {act : 𝓞 E → Q → Q} {e : ℕ → Q → Q → kˣ → Prop} (I : TateIso Dw k Q act e) (z : ℕ → kˣ)
    (hz : ∀ n, 0 < n → IsPrimitiveRoot (z n) n) (hzp : ∀ n m, 0 < n → 0 < m → z (n * m) ^ m = z n)
    (hA : z l.A = I.ζ l.A) :
    ∃ I' : TateIso Dw k Q act e, (∀ n, 0 < n → I'.ζ n = z n) ∧ (∀ a, I'.ev l.A a = I.ev l.A a) ∧
      ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La), I'.ev l.M a = I.ev l.M a := by
  rcases Nat.eq_zero_or_pos (Dw.p + Dw.q) with h0 | hpq
  · have hs : Subsingleton Dw.La := AllClasses.subsingleton_of_rank_zero Dw h0
    have hEF : ∀ a b : Dw.La, Dw.EF a b = 0 := fun a b => by
      rw [Subsingleton.elim a 0, map_zero, LinearMap.zero_apply]
    refine ⟨{ I with ζ := z, ζ_prim := hz, ζ_pow := hzp, isom := fun n hn a b => ?_ }, fun _ _ => rfl,
      fun _ => rfl, fun _ _ => rfl⟩
    simpa [hEF] using I.isom n hn a b
  · exact GlobalTheory.LocM.RootsPrescribe.roots E H Dw l k Q act e I z hpq hz hzp hA

theorem exists_genFib {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {t : SAB H (Sp R)} (P : PELUnif I t)
    (tK : SAB H (Sp (FractionRing R))) (m1 : SABMap tK t (jK R)) {S : Scheme.{0}} (t₀ : SAB H S)
    (z : Sp (FractionRing R) ⟶ S) (m2 : SABMap tK t₀ z) : letI := H.starRing;
    ∃ ψ₁ : P.A.A.left ⟶ tK.G.left, ψ₁ ≫ m1.φ = P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R) ∧
      IsGrpPullback P.A.A t₀.G z (ψ₁ ≫ m2.φ) ∧ LBIso P.A.L (t₀.PP.L.pull (ψ₁ ≫ m2.φ)) ∧
      ∀ a : 𝓞 E, (P.oA.act a).left ≫ ψ₁ ≫ m2.φ = (ψ₁ ≫ m2.φ) ≫ (t₀.act.act a).left := by
  letI := H.starRing
  have := P.U.gen_hom
  have : IsMonHom P.U.gen.symm.hom := by show IsMonHom P.U.gen.inv; infer_instance
  set k : P.A.A.left ⟶ t.G.left := P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R) with hk
  have gpG : IsGrpPullback P.A.A t.G (jK R) k :=
    ((isGrpPullback_of_iso P.U.gen.symm).comp (isGrpPullback_pullback t.G (jK R))).congr (Category.id_comp _) rfl
  let ψ₁ : P.A.A.left ⟶ tK.G.left := m1.cart.1.lift k P.A.A.hom gpG.1.w
  have hψ₁ : ψ₁ ≫ m1.φ = k := m1.cart.1.lift_fst _ _ _
  have hψ₂ : ψ₁ ≫ tK.G.hom = P.A.A.hom := m1.cart.1.lift_snd _ _ _
  have n : IsGrpPullback P.A.A t.G (𝟙 _ ≫ jK R) (ψ₁ ≫ m1.φ) :=
    gpG.congr (Category.id_comp _).symm hψ₁.symm
  have cart1 : IsGrpPullback P.A.A tK.G (𝟙 _) ψ₁ := m1.cart.cancel n (hψ₂.trans (Category.comp_id _).symm)
  have cart : IsGrpPullback P.A.A t₀.G z (ψ₁ ≫ m2.φ) := (cart1.comp m2.cart).congr (Category.id_comp _) rfl
  have actA : ∀ x, (P.oA.act x).left ≫ k = k ≫ (t.act.act x).left := by
    intro x
    have e : P.oA.act x ≫ P.U.gen.inv = P.U.gen.inv ≫ (Over.pullback (jK R)).map (t.act.act x) := by
      rw [Iso.comp_inv_eq, Category.assoc]
      exact ((Iso.inv_comp_eq _).2 (P.lin.ext x)).symm
    rw [hk, ← Category.assoc, ← Over.comp_left, e, Over.comp_left, Category.assoc]
    exact congrArg _ (pullback.lift_fst _ _ _)
  have actK : ∀ a : 𝓞 E, (P.oA.act a).left ≫ ψ₁ = ψ₁ ≫ (tK.act.act a).left := by
    intro a
    apply m1.cart.1.hom_ext
    · calc ((P.oA.act a).left ≫ ψ₁) ≫ m1.φ = (P.oA.act a).left ≫ k := by rw [Category.assoc, hψ₁]
        _ = k ≫ (t.act.act a).left := actA a
        _ = (ψ₁ ≫ (tK.act.act a).left) ≫ m1.φ := by rw [Category.assoc ψ₁, m1.act a, ← Category.assoc, hψ₁]
    · rw [Category.assoc, hψ₂, Over.w (P.oA.act a), Category.assoc, Over.w (tK.act.act a), hψ₂]

  have hgi : P.U.gen.inv.left ≫ P.U.gen.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  have B₁ : LBIso (P.A.L.pull (𝟙 _)) (P.U.LG.L.pull k) :=
    LBIso.chartPull (chartPullSame P.A.L (fun _ => 𝟙 _) (fun _ => P.U.gen.hom.left) _ P.U.gen.inv.left
        (fun _ => hgi.symm))
      (chartPullSame P.U.LG.L (fun _ => k) (fun _ => pullback.fst t.G.hom (jK R)) _ P.U.gen.inv.left
        (fun _ => rfl)) P.U.ext
  have B₁' : LBIso P.A.L (t.PP.L.pull k) := by
    rw [← P.bundle]
    exact LBIso.chartPull (chartPullUnpull P.A.L (𝟙 _) rfl) (chartPullId _) B₁
  obtain ⟨w₂, -, g₂, -⟩ := rigIso_congr rfl m1.cm m1.lin rfl rfl
  have B₂ : LBIso (tK.PP.L.pull ψ₁) (t.PP.L.pull k) :=
    LBIso.chartPull (chartPullPull tK.PP.L ψ₁)
      (chartPullSame t.PP.L (fun _ => k) (fun _ => m1.φ) _ ψ₁ (fun _ => hψ₁.symm)) ⟨w₂, g₂⟩
  obtain ⟨w₃, -, g₃, -⟩ := rigIso_congr rfl m2.cm m2.lin rfl rfl
  have B₃ : LBIso (tK.PP.L.pull ψ₁) (t₀.PP.L.pull (ψ₁ ≫ m2.φ)) :=
    LBIso.chartPull (chartPullPull tK.PP.L ψ₁)
      (chartPullSame t₀.PP.L (fun _ => ψ₁ ≫ m2.φ) (fun _ => m2.φ) _ ψ₁ (fun _ => rfl)) ⟨w₃, g₃⟩
  have BL : LBIso P.A.L (t₀.PP.L.pull (ψ₁ ≫ m2.φ)) :=
    LBIso.trans P.A.isLB (pull_isLB tK.PP.isLB _) (pull_isLB t₀.PP.isLB _)
      (LBIso.trans P.A.isLB (pull_isLB t.PP.isLB _) (pull_isLB tK.PP.isLB _) B₁' (LBIso.symm B₂)) B₃
  refine ⟨ψ₁, hψ₁, cart, BL, fun a => ?_⟩
  rw [← Category.assoc, actK, Category.assoc, m2.act a, Category.assoc]

end GlobalTheory.LowDat

namespace GlobalTheory.LowDat

theorem exists_xfLevel : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) (c : Coeff l) (R : Type) [CommRing R] [IsDomain R]
    [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (C : GlobalTheory.UChart.Fam Xo c R) (tK : SAB H (Sp (FractionRing R)))
    (m1 : SABMap tK C.t (jK R)) (m2 : SABMap tK Xo.univ.t (C.y ≫ pullback.fst _ _))
    (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F],
    ∃ I : (letI := H.starRing; TateIsoQ Dw C.P.D.toPre C.P.oD F), GlobalTheory.LowDat.XFLevel C tK m1 m2 F I := by
  intro E _ _ _ H Dw l Xo c R _ _ _ hR C tK m1 m2 F _ _ _
  letI := H.starRing
  have := hR.2
  have hT := GlobalTheory.FlatTors.torsionIso_holds E H R _ hR.1 C.t C.P
  have hM' : 0 < l.M' := Nat.lcm_pos (by have := l.three_le; omega) l.A_pos
  let β : KA l →+* F := (toF C F).comp (IntermediateField.inclusion c.le).toRingHom
  have hx : (jFK (R := R) F ≫ C.y ≫ pullback.fst _ _) ≫ Xo.s = spMap β := by
    rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc C.y, C.y_over]
    simp only [β, toF, spMap_comp, Category.assoc]
  obtain ⟨-, J0, hζ0, jA, jM⟩ := Xo.univ.geom F (jFK (R := R) F ≫ C.y ≫ pullback.fst _ _) β hx
  haveI := c.fin
  obtain ⟨w, hw1, hw2, hw3⟩ := GlobalTheory.HostModel.exists_roots c.F F (toF C F)
  have hwA : w l.A = J0.ζ l.A := Units.ext (by
    rw [hw3 l.A l.A_pos ⟨zeta l.A, c.le (IntermediateField.subset_adjoin _ _ (by simp))⟩ rfl, hζ0]
    rfl)
  obtain ⟨J, hJζ, hJA, hJM⟩ := exists_tateIso_roots l J0 w hw1 hw2 hwA
  obtain ⟨ψ₁, h1, gψ, lψ, aψ⟩ := exists_genFib C.P tK m1 Xo.univ.t (C.y ≫ pullback.fst _ _) m2
  obtain ⟨I, hI, eI⟩ := GlobalTheory.ArcOfPoint.exists_tateIsoQ Dw hR.1 C.P hT Xo.univ.t _ _ gψ lψ aψ F J
  refine ⟨I, ?_, ?_⟩
  · rw [hI, hJζ _ hM', hw3 _ hM' ⟨zeta l.M', c.zeta_mem⟩ rfl]
  · intro k a σ hσ x hx
    have hk : 0 < k := by
      rcases hσ with ⟨rfl, -⟩ | ⟨rfl, -⟩
      exacts [l.A_pos, by have := l.three_le; omega]
    have hJσ : toUnit _ ≫ σ = J.ev k a := by
      rcases hσ with ⟨rfl, rfl⟩ | ⟨rfl, ha, rfl⟩
      · rw [hJA]; exact jA a
      · rw [hJM a ha]; exact jM a ha
    obtain ⟨f, f₁, f₂, f₃, -⟩ := hT F k hk
    obtain ⟨e, he⟩ : ∃ e : (TFK (R := R) F ⟶ C.P.A.A) ≃*
        (Over.mk (jFK (R := R) F ≫ C.y ≫ pullback.fst _ _) ⟶ Xo.univ.t.G),
        ∀ x, (e x).left = x.left ≫ ψ₁ ≫ m2.φ := GlobalTheory.LiePull.exists_pushEquiv gψ (TFK (R := R) F) _ rfl
    have hx' : (e.symm (J.ev k a)).left ≫ ψ₁ ≫ m2.φ = (J.ev k a).left := by
      rw [← he, MulEquiv.apply_symm_apply]
    have hxk : e.symm (J.ev k a) ^ k = 1 := by
      rw [← map_pow, (J.onto k hk _).2 ⟨a, rfl⟩, map_one]
    obtain ⟨p, hp⟩ := f₂ _ hxk
    have hpe := eI k hk a p _ hx' ((f₁ p _).2 hp.symm)
    have hxx : x = e.symm (J.ev k a) := by
      rw [(f₁ _ _).1 hx, ← hp]; exact ((f₃ _ _).2 hpe).symm
    refine ⟨x.left ≫ ψ₁, by rw [Category.assoc, h1], ?_⟩
    rw [Category.assoc, hxx, hx', ← hJσ, Over.comp_left]
    have ht : (toUnit (Over.mk (jFK (R := R) F ≫ C.y ≫ pullback.fst _ _))).left =
        jFK (R := R) F ≫ C.y ≫ pullback.fst _ _ := by
      simpa using Over.w (toUnit (Over.mk (jFK (R := R) F ≫ C.y ≫ pullback.fst _ _)))
    rw [ht]
    simp only [Category.assoc]

end GlobalTheory.LowDat
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelIsometryGenericFibreBoundaryChartStatement
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LowDat GlobalTheory.LowFilt
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_levelIsometry_genericFibre_boundaryChart : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) (c : Coeff l) (R : Type) [CommRing R] [IsDomain R]
    [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (C : GlobalTheory.UChart.Fam Xo c R) (tK : SAB H (Sp (FractionRing R)))
    (m1 : SABMap tK C.t (jK R)) (m2 : SABMap tK Xo.univ.t (C.y ≫ pullback.fst _ _))
    (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F],
    ∃ I : (letI := H.starRing; TateIsoQ Dw C.P.D.toPre C.P.oD F), GlobalTheory.LowDat.XFLevel C tK m1 m2 F I := by
  first | exact @GlobalTheory.LowDat.exists_xfLevel | exact GlobalTheory.LowDat.exists_xfLevel | (intros; apply GlobalTheory.LowDat.exists_xfLevel <;> assumption)
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsotropicSaturatedWeightFiltration
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LowFilt

open GlobalTheory.LowDat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def twistI {D : Datum H} {R : Type} [CommRing R] [IsDomain R] {D₀ : DegPre R} (hB : D₀.TauBimult) [Module (𝓞 E) D₀.X]
    {oa : letI := H.starRing; D₀.OAct (𝓞 E)} {F : Type} [Field F] [Algebra (FractionRing R) F]
    (I : TateIsoQ D D₀ oa F) (g : ℕ → D.La ≃ₗ[𝓞 E] D.La) (hiso : ∀ n a b, D.EF (g n a) (g n b) = D.EF a b)
    (htow : ∀ n m, 0 < n → 0 < m → ∀ a, ∃ e, g (n * m) a = g n a + n • e) : TateIsoQ D D₀ oa F where
  ζ := I.ζ
  ζ_prim := I.ζ_prim
  ζ_pow := I.ζ_pow
  ev n a := I.ev n (g n a)
  add n hn a b := by rw [map_add (f := _)]; exact I.add n hn _ _
  lin n hn x a := by rw [map_smul]; exact I.lin n hn x _
  ker n hn a b := (I.ker n hn _ _).trans
    ⟨fun ⟨e, he⟩ => ⟨(g n).symm e, by
        have := congrArg (g n).symm he
        rwa [LinearEquiv.symm_apply_apply, map_add, LinearEquiv.symm_apply_apply, map_nsmul] at this⟩,
     fun ⟨e, he⟩ => ⟨g n e, by rw [he, map_add (f := _), map_nsmul]⟩⟩
  onto n hn p := by
    obtain ⟨b, hb⟩ := I.onto n hn p
    exact ⟨(g n).symm b, by rw [LinearEquiv.apply_symm_apply]; exact hb⟩
  tower n m hn hm a := by
    obtain ⟨q, h₁, h₂, h₃⟩ := I.tower n m hn hm (g (n * m) a)
    exact ⟨q, h₁, h₂, GlobalTheory.TorusExt.equiv_trans hB h₃ ((I.ker n hn _ _).2 (htow n m hn hm a))⟩
  isom n hn a b := by rw [← hiso n a b]; exact I.isom n hn _ _

end GlobalTheory.LowFilt

open GlobalTheory.LowFilt GlobalTheory.LowDat in
theorem GlobalTheory.LowFilt.exists_filt : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l)
  (c : Coeff l) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ C : GlobalTheory.UChart.Fam Xo c R,
  1 ≤ Module.finrank (𝓞 E) C.P.D.toPre.X →
  ∃ Z : Submodule (𝓞 E) Dw.La, GlobalTheory.LowDat.IsIsoSat Dw Z ∧ Module.finrank (𝓞 E) Z = Module.finrank (𝓞 E) C.P.D.toPre.X ∧
    ∃ (tK : SAB H (Sp (FractionRing R))) (m1 : SABMap tK C.t (jK R)) (m2 : SABMap tK Xo.univ.t (C.y ≫ pullback.fst _ _)),
      ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F],
        ∃ I : (letI := H.starRing; TateIsoQ Dw C.P.D.toPre C.P.oD F),
          GlobalTheory.LowDat.XFLevel C tK m1 m2 F I ∧ GlobalTheory.LowDat.FiltGraded C Z F I := by
  intro E _ _ _ H Dw l Xo c R _ _ _ hR C hr
  obtain ⟨tK, ⟨m1⟩, ⟨m2⟩⟩ := C.gen
  haveI : CharZero R := hR.2
  letI := H.starRing
  have hB := C.P.D.tau_bimult
  have hT : C.P.TorsionIso := GlobalTheory.FlatTors.torsionIso_holds E H R _ hR.1 C.t C.P
  haveI : IsNoetherianRing R := hR.1.1
  let F₀ := AlgebraicClosure (FractionRing R)
  haveI : CharZero (FractionRing R) := charZero_of_injective_algebraMap (IsFractionRing.injective R _)
  haveI : CharZero F₀ := charZero_of_injective_algebraMap (algebraMap (FractionRing R) F₀).injective
  obtain ⟨I₀, hI₀⟩ := GlobalTheory.T.exists_levelIsometry_genericFibre_boundaryChart Xo c R hR C tK m1 m2 F₀
  obtain ⟨y, hy, hcois⟩ := GlobalTheory.T.tateIso_latticePart_surjective_coisotropicKernel Dw R C.P.D.toPre C.P.oD C.P.D.psi_even hB F₀ I₀
  have htow : ∀ n m, 0 < n → 0 < m → ∀ a, ∃ e, y (n * m) a = y n a + n • e := by
    intro n m hn hm a
    obtain ⟨q, h₁, -, z, h₃, -⟩ := I₀.tower n m hn hm a
    obtain ⟨e₁, he₁⟩ := hy (n * m) (Nat.mul_pos hn hm) a
    obtain ⟨e₂, he₂⟩ := hy n hn a
    have e₃ : (q.y : C.P.D.toPre.X) = (I₀.ev (n * m) a).y := h₁
    have e₄ : q.y = (I₀.ev n a).y - n • z := by rw [h₃]; abel
    refine ⟨m • e₁ - e₂ - z, ?_⟩
    rw [he₁, he₂, ← e₃, e₄]
    simp only [smul_sub, smul_smul]
    abel
  have hM : 0 < l.M' := Nat.lcm_pos (by have := l.three_le; omega) l.A_pos
  obtain ⟨Z, hZ, hZr, g, hgi, hgt, hgN, hker⟩ := GlobalTheory.T.exists_compatible_isometries_coisotropic_kernels Dw y hcois htow (GlobalTheory.T.finrank_uChart_le_min_signature Xo c R hR C) l.M' hM
  refine ⟨Z, hZ, hZr, tK, m1, m2, fun F _ _ _ => ?_⟩
  let I₁ := twistI hB I₀ g hgi hgt
  have hI₁ : XFLevel C tK m1 m2 F₀ I₁ := by
    refine ⟨hI₀.1, fun k a σ hk x hx => hI₀.2 k a σ hk x ?_⟩
    have hk1 : 1 ≤ k ∧ k ∣ l.M' := by
      rcases hk with ⟨rfl, -⟩ | ⟨rfl, -⟩
      · exact ⟨l.A_pos, Nat.dvd_lcm_right _ _⟩
      · exact ⟨by have := l.three_le; omega, Nat.dvd_lcm_left _ _⟩
    obtain ⟨f, f₁, -, f₃, -⟩ := hT F₀ k hk1.1
    rw [f₁] at hx ⊢
    rw [hx]
    refine (f₃ _ _).2 ((I₀.ker k hk1.1 _ _).2 ?_)
    obtain ⟨e, he⟩ := hgN k a
    obtain ⟨j, hj⟩ := hk1.2
    exact ⟨j • e, by rw [smul_smul, ← hj]; exact he⟩
  obtain ⟨I, hIl, hIy⟩ := GlobalTheory.T.exists_levelIsometry_extension_algClosed Xo c R hR C tK m1 m2 I₁ hI₁ F
  refine ⟨I, hIl, fun n hn a => ?_⟩
  rw [GlobalTheory.T.exists_equiv_latticePart_zero_iff_mem_nsmul R _ hB F n hn, hIy, ← hker n hn a]
  obtain ⟨e, he⟩ := hy n hn (g n a)
  change (∃ e, (I₀.ev n (g n a)).y = n • e) ↔ _
  constructor
  · rintro ⟨e', he'⟩; exact ⟨e + e', by rw [he, he', smul_add, add_comm]⟩
  · rintro ⟨e', he'⟩; exact ⟨e' - e, by rw [smul_sub, ← he', he, add_sub_cancel_right]⟩
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsotropicSaturatedWeightFiltrationStatement
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isotropic_saturated_weight_filtration : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l)
  (c : Coeff l) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ C : GlobalTheory.UChart.Fam Xo c R,
  1 ≤ Module.finrank (𝓞 E) C.P.D.toPre.X →
  ∃ Z : Submodule (𝓞 E) Dw.La, GlobalTheory.LowDat.IsIsoSat Dw Z ∧ Module.finrank (𝓞 E) Z = Module.finrank (𝓞 E) C.P.D.toPre.X ∧
    ∃ (tK : SAB H (Sp (FractionRing R))) (m1 : SABMap tK C.t (jK R)) (m2 : SABMap tK Xo.univ.t (C.y ≫ pullback.fst _ _)),
      ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F],
        ∃ I : (letI := H.starRing; TateIsoQ Dw C.P.D.toPre C.P.oD F),
          GlobalTheory.LowDat.XFLevel C tK m1 m2 F I ∧ GlobalTheory.LowDat.FiltGraded C Z F I := by
  first | exact @GlobalTheory.LowFilt.exists_filt | exact GlobalTheory.LowFilt.exists_filt | (intros; apply GlobalTheory.LowFilt.exists_filt <;> assumption)
end
end
