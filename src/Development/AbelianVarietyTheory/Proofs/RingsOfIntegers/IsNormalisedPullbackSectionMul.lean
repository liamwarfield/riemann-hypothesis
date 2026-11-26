module

public import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SvalOfIsTwistPull
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSecNeZero
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HalvesFreeAndAdjoint
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsQuotEquiv
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.PlaceIdem
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ChartValJ
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsTautologicalMarking
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.FFVMap
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FramedPointBaseChangeLaws
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.HarmonicValueCopiesGaugeIndependent
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegralChartDirectionsAreEigenvectors

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IsNormalisedPullbackSectionMul
section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IsNormalisedPullbackSectionMul
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

namespace GlobalTheory.PullComp

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] (L : RigLB A)

theorem isNormPull_comp (φ ψ : A ⟶ A) [IsMonHom ψ] (a b c : ℤ) {T : Over S} {s : LB.Sec (LPow A L.L a T)}
    {s' : LB.Sec (LPow A L.L b T)} {s'' : LB.Sec (LPow A L.L c T)} (h : IsNormPull A L φ b a s s')
    (h' : IsNormPull A L ψ c b s' s'') : IsNormPull A L (ψ ≫ φ) c a s s'' := by
  have hL := L.isLB
  have he : eSec A ≫ ψ.left = eSec A := by simp only [eSec, ← Over.comp_left, IsMonHom.one_hom]
  obtain ⟨β₀, β, hβ₀, nβ, cβ, tβ⟩ := h
  obtain ⟨δ₀, δ, hδ₀, nδ, cδ, tδ⟩ := h'
  obtain ⟨α₀, hα₀, hv₀⟩ := exists_gen hL (φ' := ![𝟙 A.left, (ψ ≫ φ).left]) (ε' := ![c, -a])
    (fun U _ f => by
      simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Sum.elim_inl, Sum.elim_inr,
        Matrix.cons_val_zero, Matrix.cons_val_one, Category.comp_id, Over.comp_left, zpow_neg]
      rw [_root_.mul_assoc, inv_mul_cancel_left])
    (LB.mulGen L.L _ _ _ _ δ₀ (LB.pullGen L.L _ _ β₀ ψ.left))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ hδ₀ (DVR.pullGen_isGen _ _ _ _ hβ₀ _))
  obtain ⟨α, hα, hv⟩ := exists_gen hL (φ' := ![(snd T A).left, (snd T A ≫ ψ ≫ φ).left]) (ε' := ![c, -a])
    (fun U _ f => by
      refine Finset.prod_congr rfl fun i _ => ?_
      fin_cases i
      · exact congrArg (fun q => f q ^ c) (Category.comp_id _)
      · rfl)
    (LB.pullGen L.L ![𝟙 A.left, (ψ ≫ φ).left] ![c, -a] α₀ (snd T A).left)
    (DVR.pullGen_isGen _ _ _ _ hα₀ _)
  refine ⟨α₀, α, hα₀, corr_of_val hL fun y J hJ => ?_, corr_of_val hL fun y J hJ => hv _ _ y J hJ,
    ThetaLin.isTwistPull_of_sval A hL hα fun y J hJ => ?_⟩
  · have e₁ := val_corr hJ nβ (𝟙 _)
    have e₂ := val_corr hJ nδ (𝟙 _)
    rw [val_pull hJ, val_mul hJ, UT.PullMul.val_rigPow, UT.PullMul.val_rigPow] at e₁ e₂
    rw [val_pull hJ, hv₀ _ _ y J hJ, val_mul hJ, val_pull hJ, Category.assoc, he, e₁, e₂, val_mul hJ,
      UT.PullMul.val_rigPow, UT.PullMul.val_rigPow, zpow_neg _ b, _root_.mul_assoc, inv_mul_cancel_left]
  · have e₁ : (endOver A T ψ).left ≫ (snd T A).left = (snd T A).left ≫ ψ.left := by
      rw [← Over.comp_left, lift_snd, Over.comp_left]
    have e₂ : (endOver A T ψ).left ≫ (endOver A T φ).left = (endOver A T (ψ ≫ φ)).left := by
      rw [← Over.comp_left, comp_lift, lift_fst, lift_snd_assoc, Category.assoc]
    rw [ThetaLin.sval_of_isTwistPull A tδ _ y hJ, ThetaLin.sval_of_isTwistPull A tβ _ y hJ, val_corr hJ cδ,
      val_corr hJ cβ, hv _ _ y J hJ, val_pull hJ, val_pull hJ, val_pull hJ, hv₀ _ _ y J hJ, val_mul hJ, val_pull hJ,
      Units.val_mul, _root_.mul_assoc]
    simp only [Category.assoc, e₁, e₂]

theorem pulls_mul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S : Type) [CommRing S] (x : Sp S ⟶ Xo.X) (a b : 𝓞 E) (k k' k'' : ℕ) (F : SecN Xo x k) (F' : SecN Xo x k') (F'' : SecN Xo x k''), Pulls Xo a F F' → Pulls Xo b F' F'' → Pulls Xo (a * b) F F'' := by
  intro E _ _ _ H Dw l Xo S _ x a b k k' k'' F F' F'' h h'
  have := Xo.univ.t.act.hom b
  unfold Pulls
  rw [_root_.mul_comm a b, Xo.univ.t.act.mul]
  exact isNormPull_comp _ _ _ _ _ _ h h'

end GlobalTheory.PullComp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IsNormalisedPullbackSectionMulStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isNormalisedPullbackSection_mul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S : Type) [CommRing S] (x : Sp S ⟶ Xo.X) (a b : 𝓞 E) (k k' k'' : ℕ) (F : SecN Xo x k) (F' : SecN Xo x k') (F'' : SecN Xo x k''), Pulls Xo a F F' → Pulls Xo b F' F'' → Pulls Xo (a * b) F F'' := by
  first | exact @GlobalTheory.PullComp.pulls_mul | exact GlobalTheory.PullComp.pulls_mul | (intros; apply GlobalTheory.PullComp.pulls_mul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IsIntegralZpowOfPowEqOne
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

namespace GlobalTheory.PlaceInt

theorem isIntegral_of_pow_eq_one {F : Type} [Field F] {z : F} {N : ℕ} (hN : 0 < N) (hz : z ^ N = 1) :
    IsIntegral ℤ z := by
  refine IsIntegral.of_pow hN ?_
  rw [hz]
  exact isIntegral_one

theorem isIntegral_zpow_of_pow_eq_one {F : Type} [Field F] {z : F} {N : ℕ} (hN : 0 < N) (hz : z ^ N = 1) (a : ℤ) :
    IsIntegral ℤ (z ^ a) := by

  refine GlobalTheory.PlaceInt.isIntegral_of_pow_eq_one hN ?_
  rw [← zpow_natCast, ← zpow_mul, mul_comm a, zpow_mul, zpow_natCast, hz, one_zpow]

private theorem isIntegral_int_ringHom_apply {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) {a : A}
    (h : IsIntegral ℤ a) : IsIntegral ℤ (f a) :=
  h.map f.toIntAlgHom

theorem datum_isIntegral : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n), d.IsLev → ∀ ph ψ x₀, d.PhiPin ph ψ x₀ → ∀ (x0 : Fin n → Dw.La) (q : Fin n → LevQ Dw d.l₂), IsIntegral ℤ (d.w x0 q) := by
  intro E _ _ _ H Dw l Xo c n d hd ph ψ x₀ hpin x0 q
  obtain ⟨-, hM, -, -, hII, -⟩ := id hd
  obtain ⟨hloc, hsupp, hequi, hone, hspan0, hsum⟩ := hpin
  have hpd : 0 < d.pd := by
    rcases Nat.eq_zero_or_pos d.pd with h | h
    · have h3 := d.l₂.three_le
      rw [hM, h, mul_zero] at h3
      omega
    · exact h

  have hI : d.I ≠ ⊥ := by
    intro h
    rw [h, Ideal.map_bot, sup_bot_eq] at hII
    exact bot_ne_top hII
  have : Finite (𝓞 E ⧸ d.I) := Ideal.finiteQuotientOfFreeOfNeBot d.I hI
  have := Dw.fin
  have := Dw.proj
  obtain ⟨eI⟩ := GlobalTheory.HalfPairing.nonempty_equiv_quot (N := Dw.La) d.I (Dw.p + Dw.q) Dw.rank
  have : Finite (LaI Xo c d) := Finite.of_equiv _ eI.symm.toEquiv
  have : Finite (LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d) :=
    Finite.of_injective (fun e : LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d => (e : LaI Xo c d → LaI Xo c d))
      (fun a b h => LinearEquiv.ext (congrFun h))

  have hph : ∀ x, IsIntegral ℤ (ph x) := by
    intro x
    by_cases h0 : ph x = 0
    · rw [h0]
      exact isIntegral_zero
    have hspan := hsupp x h0
    obtain ⟨-, htrans, adj, -, hadj⟩ := GlobalTheory.HalfPairing.halves_free_and_adjoint E H Dw l Xo c n d hd
    let pad : (Fin n → LaJ Xo c d) → Fin (Dw.p + Dw.q) → LaJ Xo c d :=
      fun z i => if h : i.val < n then z ⟨i.val, h⟩ else 0
    have hpadv : ∀ z i (h : i.val < n), pad z i = z ⟨i.val, h⟩ := fun z i h => dif_pos h
    have hpad : ∀ z : Fin n → LaJ Xo c d, Submodule.span (𝓞 E) (z '' {b | b.val < Dw.p + Dw.q}) = ⊤ →
        Submodule.span (𝓞 E) (Set.range (pad z)) = ⊤ := by
      intro z hz
      rw [eq_top_iff, ← hz]
      apply Submodule.span_mono
      rintro _ ⟨b, hb, rfl⟩
      exact ⟨⟨b.val, hb⟩, hpadv z _ b.isLt⟩
    obtain ⟨g, hg, -⟩ := htrans (pad x₀) (pad x) (hpad x₀ hspan0) (hpad x hspan)
    have h1 := hequi (adj g) g ((hadj (adj g) g).mpr rfl) x₀
    rw [hone, _root_.mul_one] at h1
    have h2 : ph x = ph (fun b => g (x₀ b)) := by
      apply hloc
      intro b hb
      have hb' := hg ⟨b.val, hb⟩
      rw [hpadv x₀ _ b.isLt, hpadv x _ b.isLt] at hb'
      exact hb'.symm
    rw [h2, h1]
    obtain ⟨m, hm, hpow⟩ :=
      isOfFinOrder_iff_pow_eq_one.mp (ψ.isOfFinOrder (isOfFinOrder_of_finite (adj g))).inv
    refine GlobalTheory.PlaceInt.isIntegral_of_pow_eq_one hm ?_
    rw [← Units.val_pow_eq_pow_val, hpow, Units.val_one]

  have hz : IsIntegral ℤ (zetaM c ^ pairL (l := l) x0 (fun b => levRep (q b))) :=
    GlobalTheory.PlaceInt.isIntegral_zpow_of_pow_eq_one (N := l.M) (by have := l.three_le; omega)
      (GlobalTheory.DatumInverseCharacter.root_pow c dvd_rfl) _

  have hφ : IsIntegral ℤ (d.φδ q) := by
    have he : IsIntegral ℤ (d.eF (d.φδ q)) := by
      rw [hsum q]
      refine finsum_induction (fun y => IsIntegral ℤ y) isIntegral_zero
        (fun a b ha hb => ha.add hb) (fun x => ?_)
      refine (isIntegral_int_ringHom_apply d.eF.toRingHom (hph x)).mul ?_
      exact GlobalTheory.PlaceInt.isIntegral_zpow_of_pow_eq_one hpd
        (GlobalTheory.DatumInverseCharacter.root_pow d.c₂ (Dvd.intro_left _ hM.symm)) _
    have hb := isIntegral_int_ringHom_apply d.eF.symm.toRingHom he
    simpa using hb
  exact isIntegral_int_ringHom_apply d.eF.toRingHom (hz.mul hφ)

end GlobalTheory.PlaceInt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.MemRangeOfIsIntegral
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

namespace GlobalTheory.PushIntegral

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} (c : Coeff l) {n : ℕ}

theorem push_letB (ga : Matrix (Fin n) (Fin n) E) (σ : E →+* ℂ) (i : Fin (Dw.mult σ)) (v : Fin n → E) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryDetClass.push c ga (letB c σ i v) = letB c σ i (ga.mulVec v) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [letB, map_sum, map_mul, MvPolynomial.algHom_C, MvPolynomial.algebraMap_eq, GlobalTheory.PushHarm.push_X,
    Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem mem_range_of_isIntegral (T : CDVR) (io : c.F →+* T.Fr) {x : c.F} (hi : IsIntegral ℤ x) :
    ∃ y : T.V, algebraMap T.V T.Fr y = io x := by
  obtain ⟨p, hpm, hp⟩ := hi
  have hV : IsIntegral T.V (io x) := by
    refine ⟨p.map (Int.castRingHom T.V), hpm.map _, ?_⟩
    rw [Polynomial.eval₂_map, RingHom.ext_int ((algebraMap T.V T.Fr).comp (Int.castRingHom T.V))
      (io.comp (algebraMap ℤ c.F)), ← Polynomial.hom_eval₂, hp, map_zero]
  exact IsIntegrallyClosed.isIntegral_iff.1 hV

theorem mem_range_of_smul (T : CDVR) (io : c.F →+* T.Fr) {k : ℕ} (hk : IsUnit (k : T.V)) (σ : E →+* ℂ) {x : E}
    (hx : (k : E) * x ∈ (1 : Submodule (𝓞 E) E)) : ∃ y : T.V, algebraMap T.V T.Fr y = io (embF c σ x) := by
  obtain ⟨s, hs⟩ := Submodule.mem_one.1 hx
  have hi : IsIntegral ℤ (embF c σ (algebraMap (𝓞 E) E s)) :=
    map_isIntegral_int (embF c σ) (NumberField.RingOfIntegers.isIntegral_coe s)
  obtain ⟨y, hy⟩ := mem_range_of_isIntegral c T io hi
  obtain ⟨u, hu⟩ := hk.exists_left_inv
  refine ⟨u * y, ?_⟩
  have h1 : algebraMap T.V T.Fr u * (k : T.Fr) = 1 := by
    rw [← map_natCast (algebraMap T.V T.Fr), ← map_mul, hu, map_one]
  rw [map_mul, hy, hs, map_mul, map_mul, map_natCast, map_natCast, ← _root_.mul_assoc, h1, _root_.one_mul]

theorem coeff_mem (Λ : GenLat E n) (T : CDVR) (io : c.F →+* T.Fr) {k : ℕ} (hk : IsUnit (k : T.V))
    (ga : Matrix (Fin n) (Fin n) E) (hin : ∀ v ∈ Λ.La, (k : E) • ga.mulVec v ∈ stdLat E n)
    {P : MvPolynomial (LtN Dw n) c.F} (hP : P ∈ symO c Λ) (m : LtN Dw n →₀ ℕ) :
    (MvPolynomial.map io (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryDetClass.push c ga P)).coeff m ∈ (algebraMap T.V T.Fr).range := by
  have hle : symO (Dw := Dw) c Λ ≤
      (MvPolynomial.map (σ := LtN Dw n) (algebraMap T.V T.Fr)).range.comap
        ((MvPolynomial.map io).comp (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryDetClass.push (Dw := Dw) c ga).toRingHom) := by
    refine Subring.closure_le.2 ?_
    rintro f (⟨o, rfl⟩ | ⟨σ, i, v, hv, rfl⟩)
    · obtain ⟨y, hy⟩ := mem_range_of_isIntegral c T io o.2
      refine ⟨MvPolynomial.C y, ?_⟩
      simp [hy]
    · have h : ∀ j, ∃ y : T.V, algebraMap T.V T.Fr y = io (embF c σ (ga.mulVec v j)) := fun j =>
        mem_range_of_smul c T io hk σ (hin v hv j (Set.mem_univ j))
      choose y hy using h
      refine ⟨∑ j, MvPolynomial.C (y j) * MvPolynomial.X ⟨σ, i, j⟩, ?_⟩
      change _ = MvPolynomial.map io (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryDetClass.push c ga (letB c σ i v))
      rw [push_letB]
      simp [letB, hy]
  obtain ⟨Q, hQ⟩ := hle hP
  change _ = MvPolynomial.map io (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryDetClass.push c ga P) at hQ
  rw [← hQ, MvPolynomial.coeff_map]
  exact ⟨_, rfl⟩

theorem push_one (P : MvPolynomial (LtN Dw n) c.F) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryDetClass.push c (1 : Matrix (Fin n) (Fin n) E) P = P := by
  have h : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryDetClass.push (Dw := Dw) c (1 : Matrix (Fin n) (Fin n) E) = AlgHom.id _ _ := by
    apply MvPolynomial.algHom_ext
    rintro ⟨σ, i, j⟩
    simp [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryDetClass.push, letB, Matrix.one_apply, apply_ite, ite_mul]
  rw [h]; rfl

theorem aeval_smul_of_degree {J K A : Type} [CommRing K] [CommRing A] [Algebra K A] (t : A) (f : J → A)
    (P : MvPolynomial J K) (d : ℕ) (hP : ∀ s ∈ P.support, (s.sum fun _ e => e) = d) :
    MvPolynomial.aeval (fun i => t * f i) P = t ^ d * MvPolynomial.aeval f P := by
  classical
  set_option synthInstance.maxHeartbeats 100000 in
    rw [P.as_sum, map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [MvPolynomial.aeval_monomial, MvPolynomial.aeval_monomial, ← hP s hs]
  simp only [Finsupp.prod, Finsupp.sum, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  ring

theorem degree_eq_totalDegree {a : (E →+* ℂ) → ℕ → ℕ} {P : MvPolynomial (LtN Dw n) c.F}
    (hP : RowDeg Dw.mult n c.F a P) : ∀ s ∈ P.support, (s.sum fun _ e => e) = P.totalDegree := by
  classical
  have h : ∀ s ∈ P.support, (s.sum fun _ e => e) = ∑ σ : E →+* ℂ, ∑ i : Fin (Dw.mult σ), a σ i := by
    intro s hs
    rw [Finsupp.sum_fintype _ _ (by simp), Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun i _ => hP s hs σ i
  intro s hs
  refine le_antisymm (MvPolynomial.le_totalDegree hs) ?_
  exact Finset.sup_le fun s' hs' => ((h s' hs').trans (h s hs).symm).le

end

theorem map_pushL_mem_FFV : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) (n : ℕ) (Λ : GenLat E n) (w : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmL c Λ w → ∀ (T : CDVR) (io : c.F →+* T.Fr) (k : ℕ) (ga : Matrix (Fin n) (Fin n) E), IsUnit (k : T.V) → (∀ i j, ∑ b, IsCMField.complexConj E (ga b i) * ga b j = if i = j then 1 else 0) → (∀ v ∈ Λ.La, (k : E) • ga.mulVec v ∈ stdLat E n) → MvPolynomial.map io (pushL c ga P) ∈ FFV (Dw := Dw) T w n ∧ pushL c 1 P = P ∧ ∀ m : ℕ, pushL c ((m : E) • ga) P = MvPolynomial.C ((m : c.F) ^ P.totalDegree) * pushL c ga P := by
  intro E _ _ _ H Dw l c n Λ w P hP T io k ga hk hu hin
  obtain ⟨⟨h1, h2, h3⟩, h4⟩ := hP
  have hU : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryDetClass.IsUnitary ga := by
    ext i j
    simpa [Matrix.mul_apply, Matrix.one_apply] using hu i j
  have hr := GlobalTheory.Proof.ColumnMapShift.push_rows E H Dw l c n ga P (fun τ i => w (τ, i))
  refine ⟨⟨⟨ReciprocityTheory.ChartRestriction.G.PullbackSections.harmK_map io (GlobalTheory.PushHarm.push_mem_harmK E H Dw l c n ga P hU h1),
    ReciprocityTheory.ChartRestriction.G.PullbackSections.rowInv_map io (hr.1 h2), ReciprocityTheory.ChartRestriction.G.PullbackSections.rowDeg_map io (hr.2 h3)⟩,
    coeff_mem c Λ T io hk ga hin h4⟩, push_one c P, fun m => ?_⟩
  rw [map_pow, pushL, pushL, ← aeval_smul_of_degree _ _ P _ (degree_eq_totalDegree c h3)]
  congr 2
  funext ℓ
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp [_root_.mul_assoc]

end GlobalTheory.PushIntegral
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.InZhIffKillsAdapted
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

set_option autoImplicit false

namespace GlobalTheory.ZPart

section Mod
variable {O : Type} [CommRing O] {M : Type} [AddCommGroup M] [Module O M] {n : ℕ}

def Kl (mu : Matrix (Fin n) (Fin n) O) (u : Fin n → M) : Prop := ∀ i, ∑ j, mu i j • u j = 0

theorem Kl.mul {b : Matrix (Fin n) (Fin n) O} {u : Fin n → M} (h : Kl b u) (a : Matrix (Fin n) (Fin n) O) :
    Kl (a * b) u := by
  intro i
  simp only [Matrix.mul_apply, Finset.sum_smul, mul_smul]
  rw [Finset.sum_comm]
  simp only [← Finset.smul_sum, h _, smul_zero, Finset.sum_const_zero]

theorem Kl.smul {b : Matrix (Fin n) (Fin n) O} {u : Fin n → M} (h : Kl b u) (a : O) : Kl (a • b) u := by
  intro i
  simp only [Matrix.smul_apply, smul_eq_mul, mul_smul, ← Finset.smul_sum, h i, smul_zero]

theorem Kl.cancel {b : Matrix (Fin n) (Fin n) O} {u : Fin n → M} {a ℓ : O} (hc : IsCoprime a ℓ)
    (hu : ∀ j, ∃ e : ℕ, ℓ ^ e • u j = 0) (h : Kl (a • b) u) : Kl b u := by
  obtain ⟨e, he⟩ : ∃ e : ℕ, ∀ j, ℓ ^ e • u j = 0 := by
    choose f hf using hu
    refine ⟨∑ j, f j, fun j => ?_⟩
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le
      (Finset.single_le_sum (fun x _ => Nat.zero_le (f x)) (Finset.mem_univ j))
    rw [hd, pow_add, mul_comm, mul_smul, hf j, smul_zero]
  intro i
  obtain ⟨x, y, hxy⟩ := hc.pow_right (n := e)
  have h1 : a • ∑ j, b i j • u j = 0 := by
    rw [Finset.smul_sum]
    simpa only [Matrix.smul_apply, smul_eq_mul, mul_smul] using h i
  have h2 : ℓ ^ e • ∑ j, b i j • u j = 0 := by
    rw [Finset.smul_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [← mul_smul, mul_comm, mul_smul, he j, smul_zero]
  calc ∑ j, b i j • u j = (x * a + y * ℓ ^ e) • ∑ j, b i j • u j := by rw [hxy, one_smul]
    _ = 0 := by rw [add_smul, mul_smul, mul_smul, h1, h2, smul_zero, smul_zero, add_zero]
end Mod

section Lat
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {Λ : GenLat E n} {N ℓ : ℕ} (A : Adapt Λ N ℓ)

noncomputable def adj : Matrix (Fin n) (Fin n) E := Matrix.of fun i j => IsCMField.complexConj E (A.ga j i)

theorem adj_mul : adj A * A.ga = 1 := by
  ext i j
  simp only [adj, Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply]
  exact A.unitary i j

theorem map_inj {a b : Matrix (Fin n) (Fin n) (𝓞 E)}
    (h : a.map (algebraMap (𝓞 E) E) = b.map (algebraMap (𝓞 E) E)) : a = b := by
  refine Matrix.ext fun i j => ?_
  have h' := congrArg (fun m : Matrix (Fin n) (Fin n) E => m i j) h
  simp only [Matrix.map_apply] at h'
  exact FaithfulSMul.algebraMap_injective (𝓞 E) E h'

theorem exists_adj : ∃ r : Matrix (Fin n) (Fin n) (𝓞 E),
    r * (A.p * A.q) = ((A.k ^ 2 : ℕ) : 𝓞 E) • ((N ^ 2 : ℕ) : 𝓞 E) • (1 : Matrix (Fin n) (Fin n) (𝓞 E)) := by
  let σ : 𝓞 E →+* 𝓞 E := NumberField.RingOfIntegers.mapRingHom (IsCMField.complexConj E).toRingHom
  refine ⟨Matrix.of fun i j => σ ((A.p * A.q) j i), map_inj ?_⟩
  have hr : (Matrix.of fun i j => σ ((A.p * A.q) j i)).map (algebraMap (𝓞 E) E) =
      ((A.k * N : ℕ) : E) • adj A := by
    ext i j
    have hji := congrArg (fun m : Matrix (Fin n) (Fin n) E => m j i) A.prod
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul] at hji
    have hσ : algebraMap (𝓞 E) E (σ ((A.p * A.q) j i)) =
        IsCMField.complexConj E (algebraMap (𝓞 E) E ((A.p * A.q) j i)) := rfl
    simp only [Matrix.map_apply, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, adj, hσ, hji, map_mul,
      map_natCast]
  rw [Matrix.map_mul, hr, A.prod, Matrix.smul_mul, Matrix.mul_smul, adj_mul]
  ext i j
  simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  split_ifs <;> push_cast <;> ring

theorem exists_factor (mu : Matrix (Fin n) (Fin n) E) (hmu : ∀ v ∈ Λ.La, mu.mulVec v ∈ stdLat E n) (c : ℕ)
    (cm : Matrix (Fin n) (Fin n) (𝓞 E)) (hcm : ∀ i j, (cm i j : E) = ((c * N : ℕ) : E) * mu i j) :
    ∃ r : Matrix (Fin n) (Fin n) (𝓞 E), r * (A.p * A.q) = ((A.k ^ 2 : ℕ) : 𝓞 E) • cm := by
  have hW : ∀ j : Fin n, ∃ w ∈ Λ.La, (A.k : E) • (Pi.single j 1 : Fin n → E) = A.ga.mulVec w := by
    intro j
    refine A.onto _ ?_
    simp only [stdLat, Submodule.mem_pi]
    intro i _
    refine Submodule.mem_one.mpr ⟨(Pi.single j (1 : 𝓞 E) : Fin n → 𝓞 E) i, ?_⟩
    rw [Pi.single_apply, Pi.single_apply]
    split_ifs <;> simp
  choose w hwΛ hw using hW
  have hy : ∀ i j, ∃ y : 𝓞 E, algebraMap (𝓞 E) E y = mu.mulVec (w j) i := by
    intro i j
    have hm := hmu _ (hwΛ j)
    simp only [stdLat, Submodule.mem_pi] at hm
    exact Submodule.mem_one.mp (hm i (Set.mem_univ i))
  choose y hy using hy
  refine ⟨Matrix.of fun i j => (c : 𝓞 E) * y i j, map_inj ?_⟩
  have hGW : A.ga * Matrix.of (fun b j => w j b) = (A.k : E) • (1 : Matrix (Fin n) (Fin n) E) := by
    ext b j
    have hb := congrFun (hw j) b
    simp only [Pi.smul_apply, Pi.single_apply, smul_eq_mul, Matrix.mulVec, dotProduct] at hb
    simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    rw [← hb]
  have hWadj : Matrix.of (fun b j => w j b) = (A.k : E) • adj A := by
    calc Matrix.of (fun b j => w j b) = adj A * A.ga * Matrix.of (fun b j => w j b) := by
          rw [adj_mul, Matrix.one_mul]
      _ = (A.k : E) • adj A := by rw [Matrix.mul_assoc, hGW, Matrix.mul_smul, Matrix.mul_one]
  have hr : (Matrix.of fun i j => (c : 𝓞 E) * y i j).map (algebraMap (𝓞 E) E) =
      (c : E) • (mu * Matrix.of (fun b j => w j b)) := by
    ext i j
    simp only [Matrix.map_apply, Matrix.of_apply, map_mul, map_natCast, hy, Matrix.smul_apply, smul_eq_mul,
      Matrix.mul_apply, Matrix.mulVec, dotProduct]
  rw [Matrix.map_mul, hr, A.prod, hWadj]
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc, adj_mul, Matrix.mul_one]
  ext i j
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_natCast, hcm]
  push_cast
  ring
end Lat

section Pts
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  (Xo : Moduli Dw l) (T : Over Xo.X)

@[reducible] noncomputable def ptMod : Module (𝓞 E) (Additive (T ⟶ Xo.univ.t.G)) where
  smul a x := Additive.ofMul (x.toMul ≫ Xo.univ.t.act.act a)
  one_smul x := by
    change Additive.ofMul (x.toMul ≫ Xo.univ.t.act.act 1) = x
    rw [Xo.univ.t.act.one, Category.comp_id]; rfl
  mul_smul a b x := by
    change Additive.ofMul (x.toMul ≫ Xo.univ.t.act.act (a * b)) =
      Additive.ofMul ((x.toMul ≫ Xo.univ.t.act.act b) ≫ Xo.univ.t.act.act a)
    rw [_root_.mul_comm, Xo.univ.t.act.mul, Category.assoc]
  smul_zero a := by
    have := Xo.univ.t.act.hom a
    exact congrArg Additive.ofMul (MonObj.one_comp (Xo.univ.t.act.act a))
  smul_add a x y := by
    have := Xo.univ.t.act.hom a
    exact congrArg Additive.ofMul (MonObj.mul_comp x.toMul y.toMul (Xo.univ.t.act.act a))
  add_smul a b x := by
    change Additive.ofMul (x.toMul ≫ Xo.univ.t.act.act (a + b)) = _
    rw [Xo.univ.t.act.add, MonObj.comp_mul]; rfl
  zero_smul x := by
    change Additive.ofMul (x.toMul ≫ Xo.univ.t.act.act 0) = _
    have h := ZhStable.act_natCast Xo 0
    rw [Nat.cast_zero, pow_zero] at h
    rw [h, MonObj.comp_one]; rfl

variable {T}

theorem kills_iff {n : ℕ} (mu : Matrix (Fin n) (Fin n) (𝓞 E)) (u : Fin n → (T ⟶ Xo.univ.t.G)) :
    letI := ptMod Xo T
    Kills Xo mu u ↔ Kl mu (fun j => Additive.ofMul (u j)) := by
  refine forall_congr' fun i => ?_
  change (List.ofFn fun j => u j ≫ Xo.univ.t.act.act (mu i j)).prod = 1 ↔
    ∑ j, Additive.ofMul (u j ≫ Xo.univ.t.act.act (mu i j)) = 0
  rw [List.prod_ofFn, ← ofMul_prod, ofMul_eq_zero]

theorem pow_iff (m : ℕ) (x : T ⟶ Xo.univ.t.G) :
    letI := ptMod Xo T
    x ^ m = 1 ↔ (m : 𝓞 E) • Additive.ofMul x = 0 := by
  change x ^ m = 1 ↔ Additive.ofMul (x ≫ Xo.univ.t.act.act (m : 𝓞 E)) = 0
  rw [ZhStable.act_natCast Xo m, MonObj.comp_pow, Category.comp_id, ofMul_eq_zero]

theorem inZh_iff {n : ℕ} {Λ : GenLat E n} {N ℓ : ℕ} (A : Adapt Λ N ℓ) (u : Fin n → (T ⟶ Xo.univ.t.G))
    (hu : ∀ b, ∃ j : ℕ, u b ^ (ℓ ^ j) = 1) (c : ℕ) (hc : Nat.Coprime c ℓ) :
    InZh Xo Λ (c * N) u ↔ Kills Xo (A.p * A.q) u := by
  letI := ptMod Xo T
  have tors : ∀ j, ∃ e : ℕ, (ℓ : 𝓞 E) ^ e • Additive.ofMul (u j) = 0 := by
    intro j
    obtain ⟨e, he⟩ := hu j
    have h := (pow_iff Xo (ℓ ^ e) (u j)).mp he
    rw [Nat.cast_pow] at h
    exact ⟨e, h⟩
  have cop : ∀ m : ℕ, Nat.Coprime m ℓ → IsCoprime (m : 𝓞 E) (ℓ : 𝓞 E) := by
    intro m hm
    simpa using (Nat.isCoprime_iff_coprime.mpr hm).map (Int.castRingHom (𝓞 E))
  constructor
  · rintro ⟨-, hZ⟩
    have hK : Kills Xo ((c : 𝓞 E) • (A.p * A.q)) u := by
      refine hZ ((A.k : E) • A.ga) (fun v hv => ?_) _ (fun i j => ?_)
      · rw [Matrix.smul_mulVec]
        exact A.into v hv
      · have hij := congrArg (fun m : Matrix (Fin n) (Fin n) E => m i j) A.prod
        simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul] at hij
        change algebraMap (𝓞 E) E ((c : 𝓞 E) * (A.p * A.q) i j) = _
        rw [map_mul, map_natCast, hij, Matrix.smul_apply, smul_eq_mul]
        push_cast
        ring
    exact (kills_iff Xo _ u).mpr (((kills_iff Xo _ u).mp hK).cancel (cop c hc) tors)
  · intro hK
    have hKl := (kills_iff Xo _ u).mp hK
    refine ⟨fun b => ?_, fun mu hmu cm hcm => ?_⟩
    · obtain ⟨r, hr⟩ := exists_adj A
      have h1 := hKl.mul r
      rw [hr] at h1
      have h2 := (h1.cancel (cop _ (A.cop.pow_left 2)) tors) b
      simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, _root_.mul_one, mul_zero, ite_smul,
        zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true] at h2
      have h3 := (pow_iff Xo (N ^ 2) (u b)).mpr h2
      rw [mul_pow, _root_.mul_comm, pow_mul, h3, one_pow]
    · obtain ⟨r, hr⟩ := exists_factor A mu hmu c cm hcm
      have h1 := hKl.mul r
      rw [hr] at h1
      exact (kills_iff Xo cm u).mpr (h1.cancel (cop _ (A.cop.pow_left 2)) tors)
end Pts

end GlobalTheory.ZPart

namespace GlobalTheory

theorem inZh_iff_kills_adapted :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (n : ℕ) (Λ : GenLat E n) (N ℓ : ℕ), ℓ.Prime → 0 < N → ∀ (A : Adapt Λ N ℓ) (T : Over Xo.X) (u : Fin n → (T ⟶ Xo.univ.t.G)), (∀ b, (∃ j : ℕ, u b ^ (ℓ ^ j) = 1)) → (InZh Xo Λ N u ↔ Kills Xo (A.p * A.q) u) ∧ (InZh Xo Λ (A.k * N) u ↔ Kills Xo (A.p * A.q) u) := by
  intro E _ _ _ H Dw l Xo n Λ N ℓ _ _ A T u hu
  refine ⟨?_, ZPart.inZh_iff Xo A u hu A.k A.cop⟩
  have h1 := ZPart.inZh_iff Xo A u hu 1 (Nat.coprime_one_left ℓ)
  rwa [Nat.one_mul] at h1

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.InvariantsAndTraceFiniteFreeDomainEndomorphisms
section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.InvariantsAndTraceFiniteFreeDomainEndomorphisms
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

namespace GlobalTheory.PlaceInt

theorem invariants_and_trace_of_card_eq_finrank :
    ∀ (A R : Type) [CommRing A] [IsDomain A] [CommRing R] [IsDomain R] [Algebra A R] [Module.Free A R] [Module.Finite A R] (G : Finset (R →ₐ[A] R)), G.card = Module.finrank A R → (∀ x : R, (∀ g ∈ G, g x = x) → x ∈ (algebraMap A R).range) ∧ ∀ x : R, algebraMap A R (Algebra.trace A R x) = ∑ g ∈ G, g x := by
  classical
  intro A R _ _ _ _ _ _ _ G hG
  let b : Module.Basis G A R := (Module.finBasis A R).reindex
    (Fintype.equivOfCardEq (by simp [hG]))
  let M : Matrix G G R := Matrix.of fun g i => g.1 (b i)
  have hdet : M.det ≠ 0 := by
    intro h
    obtain ⟨v, hv, hvM⟩ := Matrix.exists_vecMul_eq_zero_iff.2 h
    have hli : LinearIndependent R (fun g : G => ((g.1 : R →* R) : R → R)) := by
      refine (linearIndependent_monoidHom R R).comp (fun g : G => (g.1 : R →* R)) ?_
      intro g g' hgg
      apply Subtype.ext
      ext x
      exact DFunLike.congr_fun hgg x
    apply hv
    funext g
    refine Fintype.linearIndependent_iff.1 hli v ?_ g
    have hz : (∑ g : G, v g • g.1.toLinearMap) = 0 := by
      apply b.ext
      intro i
      have := congrFun hvM i
      simpa [Matrix.vecMul, dotProduct, M] using this
    funext x
    have := LinearMap.congr_fun hz x
    simpa using this
  have key : ∀ x : R, Matrix.diagonal (fun g : G => g.1 x) * M =
      M * (Algebra.leftMulMatrix b x).map (algebraMap A R) := by
    intro x
    ext g j
    rw [Matrix.diagonal_mul, Matrix.mul_apply]
    simp only [M, Matrix.of_apply, Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul]
    rw [← map_mul]
    conv_lhs => rw [← b.sum_repr (x * b j)]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, Algebra.smul_def, mul_comm]
  have key2 : ∀ x : R, M.adjugate * (Matrix.diagonal (fun g : G => g.1 x) * M) =
      M.det • (Algebra.leftMulMatrix b x).map (algebraMap A R) := by
    intro x
    rw [key, ← Matrix.mul_assoc, Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul]
  refine ⟨fun x hx => ?_, fun x => ?_⟩
  · obtain ⟨i⟩ : Nonempty G := b.index_nonempty
    have h1 : Matrix.diagonal (fun g : G => g.1 x) = x • (1 : Matrix G G R) := by
      rw [Matrix.smul_one_eq_diagonal]
      congr 1
      funext g
      exact hx g.1 g.2
    have h2 := key2 x
    rw [h1, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.adjugate_mul] at h2
    have h3 := congrFun (congrFun h2 i) i
    simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, _root_.mul_one,
      Matrix.map_apply] at h3
    rw [mul_comm] at h3
    exact ⟨_, (mul_left_cancel₀ hdet h3).symm⟩
  · have h2 := congrArg Matrix.trace (key2 x)
    rw [Matrix.trace_mul_comm, Matrix.mul_assoc, Matrix.mul_adjugate, Matrix.mul_smul,
      Matrix.mul_one, Matrix.trace_smul, Matrix.trace_smul, smul_eq_mul, smul_eq_mul,
      Matrix.trace_diagonal] at h2
    have h3 := mul_left_cancel₀ hdet h2
    rw [Algebra.trace_eq_matrix_trace b, ← Finset.sum_coe_sort G (fun g => g x), h3]
    simp [Matrix.trace]

end GlobalTheory.PlaceInt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.InvariantsAndTraceFiniteFreeDomainEndomorphismsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invariants_and_trace_finite_free_domain_endomorphisms : ∀ (A R : Type) [CommRing A] [IsDomain A] [CommRing R] [IsDomain R] [Algebra A R] [Module.Free A R] [Module.Finite A R] (G : Finset (R →ₐ[A] R)), G.card = Module.finrank A R → (∀ x : R, (∀ g ∈ G, g x = x) → x ∈ (algebraMap A R).range) ∧ ∀ x : R, algebraMap A R (Algebra.trace A R x) = ∑ g ∈ G, g x := by
  first | exact @GlobalTheory.PlaceInt.invariants_and_trace_of_card_eq_finrank | exact GlobalTheory.PlaceInt.invariants_and_trace_of_card_eq_finrank | (intros; apply GlobalTheory.PlaceInt.invariants_and_trace_of_card_eq_finrank <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.HarmonicValueBoundOfColumnProducts
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.TotalDegreeLeOfMemFFV
section -- merged from Development.AbelianVarietyTheory.BlockTheory.JetGauges.PlacePartEigenLifts
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.PlacePartEigenLifts

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.TB

section Types

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H}
variable (c : Coeff l) (la : HeightOneSpectrum (𝓞 c.F))

end Types

section Parts

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io}

def chartVal (C : IntegralChartA3 Xo c T io y) (k : ℕ) {n : ℕ} (f : Germ.PS T.Fr n (chD C.ch))
    (P : MvPolynomial (LtN Dw n) T.Fr) : T.Fr :=
  letI := io.toAlgebra
  nabValN C.ch.B T.Fr C.ch.h H.w0 k f (fun ℓ => ℓ.2.2) (fun ℓ => C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩) P

end Parts

end GlobalTheory.IndefiniteRowSideFullHecke.PlacePartEigenLifts
end
end

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RamChartCmp

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.IndefiniteRowSideFullHecke.PlacePartEigenLifts GlobalTheory.PowGerm GlobalTheory.HarmCopies
open Matrix

section Val

variable (T : CDVR) (e : ℕ)

theorem nval_nonneg_of_mem {x : T.Fr} (hx : x ∈ (algebraMap T.V T.Fr).range) : (0 : EReal) ≤ nval T.V e x := by
  obtain ⟨r, rfl⟩ := hx
  by_cases hr : algebraMap T.V T.Fr r = 0
  · rw [hr, nval_zero]; exact le_top
  rw [nval_of_ne hr]
  have h1 := (IsDiscreteValuationRing.maximalIdeal T.V).valuation_le_one (K := T.Fr) r
  have h2 : valV T.V (algebraMap T.V T.Fr r) ≠ 0 := valV_ne_zero hr
  have h3 := (WithZero.log_le_log h2 one_ne_zero).mpr h1
  rw [WithZero.log_one] at h3
  have h4 : (0 : ℝ) ≤ (vV T.V (algebraMap T.V T.Fr r) : ℝ) := by
    have : 0 ≤ vV T.V (algebraMap T.V T.Fr r) := by unfold vV; omega
    exact_mod_cast this
  exact_mod_cast div_nonneg h4 (Nat.cast_nonneg e)

theorem le_nval_int_comb {ι : Type} (s : Finset ι) (cf S : ι → T.Fr) (r : EReal)
    (hc : ∀ i, cf i ∈ (algebraMap T.V T.Fr).range) (hS : ∀ i, r ≤ nval T.V e (S i)) :
    r ≤ nval T.V e (∑ i ∈ s, cf i * S i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [nval_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    refine le_trans (le_min ?_ ih) (nval_add e _ _)
    rw [nval_mul]
    calc r = 0 + r := (zero_add r).symm
      _ ≤ _ := add_le_add (nval_nonneg_of_mem T e (hc a)) (hS a)

theorem isIntPS_iff {n d : ℕ} (f : Germ.PS T.Fr n d) :
    IsIntPS T f ↔ ∃ g : Germ.PS T.V n d, MvPowerSeries.map (algebraMap T.V T.Fr) g = f := by
  constructor
  · intro h
    choose g hg using h
    exact ⟨g, MvPowerSeries.ext fun m => hg m⟩
  · rintro ⟨g, rfl⟩ m
    exact ⟨_, (MvPowerSeries.coeff_map _ _ _).symm⟩

theorem isIntPS_boxSer {n d : ℕ} (f : Fin n → Germ.PS T.Fr 1 d) (hf : ∀ b, IsIntPS T (f b)) :
    IsIntPS T (boxSer f) := by
  choose g hg using fun b => (isIntPS_iff T (f b)).1 (hf b)
  refine (isIntPS_iff T _).2 ⟨boxSer g, ?_⟩
  unfold boxSer
  rw [map_prod]
  refine Finset.prod_congr rfl fun b _ => ?_
  rw [← hg b, MvPowerSeries.rename_map]

end Val

section Values

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io}

def colVal (C : IntegralChartA3 Xo c T io y) (k : ℕ) {n : ℕ} (f : Fin n → Germ.PS T.Fr 1 (chD C.ch))
    (P : MvPolynomial (LtN Dw n) T.Fr) : T.Fr :=
  letI := io.toAlgebra
  ∑ mo ∈ P.support, P.coeff mo *
    ∏ b, C.ch.B.nabVal T.Fr C.ch.h H.w0 k (f b) C.ch.uvec (MvPolynomial.monomial (colOf mo b) 1)

theorem chartVal_boxSer (C : IntegralChartA3 Xo c T io y) (k : ℕ) {n : ℕ} (f : Fin n → Germ.PS T.Fr 1 (chD C.ch))
    (P : MvPolynomial (LtN Dw n) T.Fr) : chartVal C k (boxSer f) P = colVal C k f P := by
  letI := io.toAlgebra
  obtain ⟨Q, rfl⟩ : ∃ Q, MvPolynomial.rename (letterEquiv (E →+* ℂ) Dw.mult n) Q = P :=
    MvPolynomial.rename_surjective _ (letterEquiv _ _ n).surjective P
  unfold chartVal colVal
  rw [nabValN_boxSer T.Fr _ _ C.ch.B T.Fr C.ch.h H.w0 (const_eq_zero C.ch.gauge) k n f _ _
    (letterEquiv (E →+* ℂ) Dw.mult n) _ C.ch.uvec _ (fun _ => rfl) (fun _ => rfl),
    GlobalTheory.NabCol.sum_support_rename (letterEquiv (E →+* ℂ) Dw.mult n) (fun mo =>
      ∏ b, C.ch.B.nabVal T.Fr C.ch.h H.w0 k (f b) C.ch.uvec (MvPolynomial.monomial (colOf mo b) 1))]
  refine Finset.sum_congr rfl fun mo _ => ?_
  congr 1
  refine Finset.prod_congr rfl fun b _ => ?_
  have hc : colM mo b = colOf (Finsupp.mapDomain (letterEquiv (E →+* ℂ) Dw.mult n) mo) b := by
    ext ℓ
    exact (Finsupp.mapDomain_apply_of_injective (letterEquiv (E →+* ℂ) Dw.mult n).injective mo (ℓ, b)).symm
  rw [hc]

theorem bound_all_iff_bound_prod (C : IntegralChartA3 Xo c T io y) (e k : ℕ) {n : ℕ} (P : MvPolynomial (LtN Dw n) T.Fr)
    (r : EReal) :
    (∀ f : Germ.PS T.Fr n (chD C.ch), IsIntPS T f → r ≤ nval T.V e (chartVal C k f P)) ↔
      ∀ f : Fin n → Germ.PS T.Fr 1 (chD C.ch), (∀ b, IsIntPS T (f b)) → r ≤ nval T.V e (colVal C k f P) := by
  letI := io.toAlgebra
  constructor
  · intro h f hf
    rw [← chartVal_boxSer]
    exact h _ (isIntPS_boxSer T f hf)
  · intro h f hf
    obtain ⟨S, hS⟩ := exists_jet P.totalDegree f
    have h1 : chartVal C k f P = ∑ j : S, MvPowerSeries.coeff j.1 f *
        chartVal C k (MvPowerSeries.monomial j.1 1) P := by
      unfold chartVal
      rw [(nabJet T.Fr _ _ C.ch.B T.Fr C.ch.h H.w0 k n _ _ _).1 _ _ _ hS,
        (nabJet T.Fr _ _ C.ch.B T.Fr C.ch.h H.w0 k n _ _ _).2.1]
    rw [h1]
    refine le_nval_int_comb T e _ _ _ r (fun j => hf j.1) fun j => ?_
    rw [monomial_eq_boxSer, chartVal_boxSer]
    refine h _ fun b => (isIntPS_iff T _).2 ⟨∏ i, MvPowerSeries.X ((0 : Fin 1), i) ^ j.1 (b, i), ?_⟩
    simp only [map_prod, map_pow, MvPowerSeries.map_X]

end Values

section Lifts

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io}

end Lifts

end GlobalTheory.RamChartCmp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.HarmonicValueBoundOfColumnProducts
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

namespace GlobalTheory.PlaceInt

theorem chBound_of_columns : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), ∀ (e : ℕ) (ρ : ℝ) (w : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), (∀ (k : ℕ) (P : MvPolynomial (LtN Dw n) T.Fr), P ∈ FFV (Dw := Dw) T w n → ∀ f : Fin n → PS T.Fr 1 (chD C.ch), (∀ b, IsIntPS T (f b)) → letI := io.toAlgebra; ((-ρ : ℝ) : EReal) ≤ nval T.V e (∑ mo ∈ P.support, P.coeff mo * ∏ b, C.ch.B.nabVal T.Fr C.ch.h H.w0 k (f b) C.ch.uvec (MvPolynomial.monomial (colOf mo b) 1))) → ChBound C e ρ w n := by
  intro E _ _ _ H Dw l Xo c _ _ T io y C e ρ w n h k
  unfold nuLocC
  refine le_iInf fun P => le_iInf fun hP => le_iInf fun f => le_iInf fun hf => ?_
  exact (GlobalTheory.RamChartCmp.bound_all_iff_bound_prod C e k P _).2 (h k P hP) f hf

end GlobalTheory.PlaceInt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.HarmonicValueBoundOfColumnProductsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harmonicValue_bound_of_column_products : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), ∀ (e : ℕ) (ρ : ℝ) (w : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), (∀ (k : ℕ) (P : MvPolynomial (LtN Dw n) T.Fr), P ∈ FFV (Dw := Dw) T w n → ∀ f : Fin n → PS T.Fr 1 (chD C.ch), (∀ b, IsIntPS T (f b)) → letI := io.toAlgebra; ((-ρ : ℝ) : EReal) ≤ nval T.V e (∑ mo ∈ P.support, P.coeff mo * ∏ b, C.ch.B.nabVal T.Fr C.ch.h H.w0 k (f b) C.ch.uvec (MvPolynomial.monomial (colOf mo b) 1))) → ChBound C e ρ w n := by
  first | exact @GlobalTheory.PlaceInt.chBound_of_columns | exact GlobalTheory.PlaceInt.chBound_of_columns | (intros; apply GlobalTheory.PlaceInt.chBound_of_columns <;> assumption)
end
end
