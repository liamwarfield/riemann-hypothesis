module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsThetaPointComplexDegenerationSmall
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCountableModel

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsArcFOver
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

noncomputable section
namespace GlobalTheory.ArcExt
open GlobalTheory.TorusExt

theorem exists_arcF_over : Laws → BrGtSt → BrWpSt → AllD fun D => ∀ (R : Type) [CommRing R] [IsDomain R] (F F' : Type) [Field F] [IsAlgClosed F] [CharZero F] [Field F'] [IsAlgClosed F'] [Algebra (FractionRing R) F] [Algebra (FractionRing R) F'] (f : F →+* F'), (∀ x, f (algebraMap (FractionRing R) F x) = algebraMap (FractionRing R) F' x) → ∀ A : ArcF D R F, ∃ A' : ArcF D R F', A'.D₀ = A.D₀ ∧ A.Over f A' := by
  intro hL hGt hWp E _ _ _ H D R _ _ F F' _ _ _ _ _ _ _ f hf₀ A
  have hf : f.comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F' := RingHom.ext hf₀
  obtain ⟨J', hg, hJ₀⟩ := exists_gauge f A.D₀.P.isLB A.ν.good
  obtain ⟨N', ν', e₁, hth⟩ := GlobalTheory.GaugeValues.exists_numOf hL R A.D₀ A.even A.bimult F' J' hg A.ν.th A.ν.th_gen
  have hJ : ∀ ψ, ν'.J (spMap f ≫ ψ) = A.ν.J ψ := e₁ ▸ hJ₀
  have G := (hGt R A.D₀ A.even A.bimult F A.N A.ν).2.2.2.2
  have G' := (hGt R A.D₀ A.even A.bimult F' N' ν').2.2.2.2
  let I := numHom f hf A.ν ν' hJ hth
  have hw : ∀ k, 1 ≤ k → ∀ (p p' : QkPt A.D₀ F k) (z : F), WeilQkIs A.D₀ F k p p' z →
      WeilQkIs A.D₀ F' k (qkExt A.bimult f hf p) (qkExt A.bimult f hf p') (f z) := fun k hk p p' z h => by
    obtain ⟨q, hq, -⟩ := (G k).1 p
    obtain ⟨q', hq', -⟩ := (G k).1 p'
    obtain ⟨r, hr, -⟩ := (G' k).1 (qkExt A.bimult f hf p)
    obtain ⟨r', hr', -⟩ := (G' k).1 (qkExt A.bimult f hf p')
    have a := numHom_qPt f hf A.bimult A.ν ν' hJ hth hq hr
    have a' := numHom_qPt f hf A.bimult A.ν ν' hJ hth hq' hr'
    rw [hWp R A.D₀ A.even A.bimult F' N' ν' k hk _ _ _ _ _ hr hr',
      (GlobalTheory.T.hom_transport_alt F F' f A.N N' I).2.2.2.1 k q q' r r' a.1 a.2 a'.1 a'.2,
      (hWp R A.D₀ A.even A.bimult F A.N A.ν k hk _ _ _ _ _ hq hq').1 h]
    rfl
  choose q' hq' using fun (n : ℕ) (a : D.La) => ((G' n).1 (qkExt A.bimult f hf (A.I.ev n a))).exists
  refine ⟨{ D₀ := A.D₀, oa := A.oa, even := A.even, bimult := A.bimult, w0 := A.w0, ρ := f A.ρ
            ρ_sq := by rw [← map_pow, A.ρ_sq, map_neg]; simp
            det := fun σ => ?_
            I := tateExt f hf A.bimult hL A.I hw, N := N', ν := ν', q := q', hq := hq', closed := inferInstance },
    rfl, I, rfl, fun _ _ => rfl, fun a y => ?_, fun n a _ => ?_⟩
  · obtain ⟨τ, rfl⟩ := DetExtend.exists_factor f σ
    obtain ⟨n, h₁, h₂⟩ := A.det τ
    have := A.D₀.P.isAb.smooth
    refine ⟨n, ?_, h₂.trans (by
      by_cases h : τ H.rt = A.ρ
      · rw [if_pos h, if_pos (show f.comp τ H.rt = f A.ρ from congrArg f h)]
      · rw [if_neg h, if_neg (show ¬ f.comp τ H.rt = f A.ρ from fun e => h (f.injective e))])⟩
    have e : spMap ((algebraMap (FractionRing R) F').comp (algebraMap R _)) =
        spMap f ≫ spMap ((algebraMap (FractionRing R) F).comp (algebraMap R _)) := by
      rw [spMap, spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← RingHom.comp_assoc, hf]
    rw [e]
    exact (DetExtend.lieMult_extend f _ _ τ n).2 h₁
  · refine ν'.eX.injective ((eX_numHom f hf A.ν ν' hJ hth _).trans ?_)
    show A.ν.eX (A.ν.eX.symm _) = ν'.eX (ν'.eX.symm (a • ν'.eX (I.e y)))
    rw [AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, eX_numHom]
  · have h := numHom_qPt f hf A.bimult A.ν ν' hJ hth (A.hq n a) (hq' n a)
    exact ⟨q' n a, h.1, h.2, ⟨0, by simp, by simp⟩⟩

end GlobalTheory.ArcExt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsRingHomComplexOfCountableOfRelations
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

namespace GlobalTheory

theorem isAlgebraic_int_eval₂Hom_of_isAlgebraic {σ : Type} (y : σ → ℂ)
    (hy : ∀ i, IsAlgebraic ℚ (y i)) (c : MvPolynomial σ ℤ) :
    IsAlgebraic ℤ (MvPolynomial.eval₂Hom (Int.castRingHom ℂ) y c) := by
  rw [IsFractionRing.isAlgebraic_iff ℤ ℚ ℂ]
  induction c using MvPolynomial.induction_on with
  | C a =>
    rw [MvPolynomial.eval₂Hom_C]
    simpa using isAlgebraic_algebraMap (R := ℚ) (A := ℂ) (a : ℚ)
  | add p q hp hq => rw [map_add (f := _)]; exact hp.add hq
  | mul_X p i hp => rw [map_mul, MvPolynomial.eval₂Hom_X']; exact hp.mul (hy i)

theorem exists_ringHom_complex_of_countable_of_relations :
    ∀ (F : Type) [Field F] [CharZero F] [Countable F] (x : Fin 2 → F) (y : Fin 2 → ℂ), (∀ i, IsAlgebraic ℚ (y i)) → (∀ c : MvPolynomial (Fin 2) ℤ, MvPolynomial.eval₂Hom (Int.castRingHom ℂ) y c = 0 → MvPolynomial.eval₂Hom (Int.castRingHom F) x c = 0) → ∃ f : F →+* ℂ, ∀ i, f (x i) = y i := by
  intro F _ _ _ x y hy hrel
  set ey := MvPolynomial.eval₂Hom (Int.castRingHom ℂ) y with hey
  set ex := MvPolynomial.eval₂Hom (Int.castRingHom F) x with hex
  let R := MvPolynomial (Fin 2) ℤ ⧸ RingHom.ker ey
  have hprime : (RingHom.ker ey).IsPrime := RingHom.ker_isPrime ey
  have : IsDomain R := Ideal.Quotient.isDomain _
  let em : R →+* ℂ := RingHom.kerLift ey
  have hem : Function.Injective em := RingHom.kerLift_injective ey
  let β : R →+* F := Ideal.Quotient.lift _ ex fun c hc => hrel c hc
  have halg : ∀ r : R, IsAlgebraic ℤ r := by
    intro r
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective r
    refine (isAlgebraic_algHom_iff em.toIntAlgHom hem).1 ?_
    exact isAlgebraic_int_eval₂Hom_of_isAlgebraic y hy c
  have hβ : Function.Injective β := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro r hr
    by_contra h0
    refine Ideal.comap_ne_bot_of_algebraic_mem (R := ℤ) (I := RingHom.ker β) h0 hr (halg r) ?_
    rw [eq_bot_iff]
    intro n hn
    rw [Ideal.mem_comap, RingHom.mem_ker] at hn
    simpa using hn
  have hc : Countable R := hβ.countable
  let : Algebra R F := β.toAlgebra
  let : Algebra R ℂ := em.toAlgebra
  have : FaithfulSMul R F := (faithfulSMul_iff_algebraMap_injective R F).2 hβ
  have : FaithfulSMul R ℂ := (faithfulSMul_iff_algebraMap_injective R ℂ).2 hem
  obtain ⟨j⟩ := nonempty_algHom_complex_of_countable R F
  refine ⟨j.toRingHom, fun i => ?_⟩
  have h := j.commutes (Ideal.Quotient.mk _ (MvPolynomial.X i))
  have h1 : algebraMap R F (Ideal.Quotient.mk _ (MvPolynomial.X i)) = x i :=
    MvPolynomial.eval₂Hom_X' (Int.castRingHom F) x i
  have h2 : algebraMap R ℂ (Ideal.Quotient.mk _ (MvPolynomial.X i)) = y i :=
    MvPolynomial.eval₂Hom_X' (Int.castRingHom ℂ) y i
  rw [h1, h2] at h
  exact h

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AevalArcTxEqZero
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators Topology

namespace GlobalTheory.Ex.ArcForm

theorem hasSum_regroup {X : Type} (e : X → ℤ) (h0 : ∀ χ, 0 ≤ e χ) (hf : ∀ n : ℤ, {χ | e χ = n}.Finite)
    (a : X → ℂ) (u x : ℂ) (h : HasSum (fun χ => u ^ e χ * a χ) x) :
    HasSum (fun n : ℕ => (∑ᶠ (χ : X) (_ : e χ = n), a χ) * u ^ n) x := by
  have h1 := h.tsum_fiberwise fun χ => (e χ).toNat
  refine h1.congr_fun fun n => ?_
  have hs : (fun χ => (e χ).toNat) ⁻¹' {n} = ((hf n).toFinset : Set X) := by
    ext χ
    have := h0 χ
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.Finite.coe_toFinset, Set.mem_setOf_eq]
    omega
  rw [hs, Finset.tsum_subtype' (hf n).toFinset fun χ => u ^ e χ * a χ]
  have h2 : (∑ᶠ (χ : X) (_ : e χ = n), a χ) = ∑ χ ∈ (hf n).toFinset, a χ :=
    finsum_mem_eq_finite_toFinset_sum a (hf n)
  rw [h2, Finset.sum_mul]
  refine Finset.sum_congr rfl fun χ hχ => ?_
  have : e χ = n := by simpa using hχ
  rw [this, zpow_natCast, mul_comm]

theorem finite_fibre {O : Type} [CommRing O] {N : NumD O} {k : ℕ} (β : N.Form k) {m : ℕ} (hm : m ≠ 0)
    (y : N.X) (n : ℤ) : {χ : N.X | β.be (y + m • χ) (y + m • χ) / (2 * m ^ 2) = n}.Finite := by
  have h := GlobalTheory.ClassMin.finite_sublevel
    (GlobalTheory.ClassMin.realExtension_ofIntBilin_posDef β.symm β.pos) (((n + 1) * (2 * m ^ 2) : ℤ) / 2 : ℝ)
  have hinj : Function.Injective fun χ : N.X => y + m • χ := fun a b hab =>
    smul_right_injective N.X (Int.natCast_ne_zero.2 hm) (by
      simpa only [natCast_zsmul] using add_left_cancel hab)
  refine (h.preimage hinj.injOn).subset fun χ hχ => ?_
  have hχ' : β.be (y + m • χ) (y + m • χ) / (2 * m ^ 2) = n := hχ
  have hpos : (0 : ℤ) < 2 * m ^ 2 := by positivity
  have h2 := Int.lt_ediv_add_one_mul_self (β.be (y + m • χ) (y + m • χ)) hpos
  rw [hχ'] at h2
  simp only [Set.mem_preimage, Set.mem_setOf_eq, GlobalTheory.ClassMin.ofIntBilin_apply]
  have h3 : ((β.be (y + m • χ) (y + m • χ) : ℤ) : ℝ) ≤ (((n + 1) * (2 * m ^ 2) : ℤ) : ℝ) := by
    exact_mod_cast h2.le
  linarith

theorem exponent_nonneg {O : Type} [CommRing O] {N : NumD O} {k : ℕ} (β : N.Form k) (m : ℕ) (y : N.X) :
    0 ≤ β.be y y / (2 * m ^ 2) := by
  refine Int.ediv_nonneg ?_ (by positivity)
  by_cases h : y = 0
  · simp [h]
  · exact (β.pos y h).le

theorem hasSum_arcTx (N : NumD ℂ) {k : ℕ} (β : N.Form k) {m : ℕ} (hm : m ^ 2 ∣ k) (ho : Odd m)
    (p : N.QT (m ^ 2)) (u : ℂˣ) (h : Summable fun χ => ‖(N.twist β u).txT m (N.twQ β u hm p) χ‖) :
    HasSum (fun n => PowerSeries.coeff n (N.arcTx β.be m p) * (u : ℂ) ^ n)
      ((N.twist β u).tx m (N.twQ β u hm p)) := by
  have h1 : HasSum (fun χ : N.X => (N.twist β u).txT m (N.twQ β u hm p) χ)
      ((N.twist β u).tx m (N.twQ β u hm p)) := h.of_norm.hasSum
  have h2 := hasSum_regroup _ (fun χ => exponent_nonneg β m (p.1.1.toAdd + m • χ))
    (finite_fibre β ho.pos.ne' p.1.1.toAdd) (N.txT m p) u _ (h1.congr_fun fun χ => by
      rw [(GlobalTheory.Ex.twist_terms ℂ N k β u m hm ho p χ).1, Units.val_zpow_eq_zpow_val])
  simpa only [NumD.arcTx, PowerSeries.coeff_mk] using h2

theorem aeval_eq_zero {ι : Type} (f : ι → PowerSeries ℂ) (F : MvPolynomial ι ℂ) {ε : ℝ} (hε : 0 < ε)
    (v : ℂˣ → ι → ℂ) (hs : ∀ u : ℂˣ, ‖(u : ℂ)‖ < ε → ∀ i,
      HasSum (fun n => PowerSeries.coeff n (f i) * (u : ℂ) ^ n) (v u i))
    (hF : ∀ u : ℂˣ, ‖(u : ℂ)‖ < ε → MvPolynomial.eval (v u) F = 0) : MvPolynomial.aeval f F = 0 := by
  have hmem : ∀ i, f i ∈ GlobalTheory.Conv.discSeries ε := fun i u hu => by
    rcases eq_or_ne u 0 with rfl | h0
    · exact summable_of_ne_finset_zero (s := {0}) fun n hn => by
        simp [show n ≠ 0 by simpa using hn]
    · exact (hs (Units.mk0 u h0) hu i).summable
  set G : GlobalTheory.Conv.discSeries ε := MvPolynomial.aeval (fun i => (⟨f i, hmem i⟩ : GlobalTheory.Conv.discSeries ε)) F with hG
  have hGv : (G : PowerSeries ℂ) = MvPolynomial.aeval f F :=
    MvPolynomial.comp_aeval_apply _ (GlobalTheory.Conv.discSeries ε).val F
  rw [← hGv]
  refine GlobalTheory.Conv.eq_zero_of_frequently_sum_eq_zero (GlobalTheory.Conv.discSeries_le_convSeries hε G.2)
    (Filter.Eventually.frequently ?_)
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds (0 : ℂ) hε)] with u h0 hu
  have h0' : u ≠ 0 := h0
  have hu' : ‖u‖ < ε := by simpa using hu
  rw [← GlobalTheory.Conv.evalDisc_apply hu', hG, MvPolynomial.comp_aeval_apply, ← hF (Units.mk0 u h0') hu',
    MvPolynomial.aeval_eq_eval]
  congr 2
  funext i
  exact (hs (Units.mk0 u h0') hu' i).tsum_eq

theorem aeval_arcTx_eq_zero : ∀ (N : NumD ℂ) (k : ℕ) (β : N.Form k) (m : ℕ) (hm : m ^ 2 ∣ k), Odd m → ∀ (ι : Type) (p : ι → N.QT (m ^ 2)) (F : MvPolynomial ι ℂ) (ε : ℝ), 0 < ε → (∀ u : ℂˣ, ‖(u : ℂ)‖ < ε → (∀ i, Summable fun χ => ‖(N.twist β u).txT m (N.twQ β u hm (p i)) χ‖) ∧ MvPolynomial.eval (fun i => (N.twist β u).tx m (N.twQ β u hm (p i))) F = 0) → MvPolynomial.aeval (fun i => N.arcTx β.be m (p i)) F = 0 :=
  fun N _ β m hm ho _ p F _ hε h =>
    aeval_eq_zero _ F hε (fun u i => (N.twist β u).tx m (N.twQ β u hm (p i)))
      (fun u hu i => hasSum_arcTx N β hm ho (p i) u ((h u hu).1 i)) fun u hu => (h u hu).2

end GlobalTheory.Ex.ArcForm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaSeriesIdentityPrincipleComplexPoints
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

namespace GlobalTheory.ArcIdentity

theorem exists_form {O O' : Type} [CommRing O] [CommRing O'] {N : NumD O} {N' : NumD O'} (e : N.X ≃+ N'.X) {k : ℕ}
    (β : N'.Form k) : ∃ b : N.Form k, ∀ y z, b.be y z = β.be (e y) (e z) := by
  refine ⟨⟨β.be.compl₁₂ e.toIntLinearEquiv.toLinearMap e.toIntLinearEquiv.toLinearMap, fun y z => ?_,
    fun y hy => ?_, fun y z => ?_⟩, fun y z => ?_⟩
  · simpa using β.symm (e y) (e z)
  · simpa using β.pos (e y) (fun h => hy (e.injective (by rw [h, map_zero])))
  · simpa using β.dvd (e y) (e z)
  · simp

theorem arcTx_qEq {O : Type} [CommRing O] (N : NumD O) (be : LinearMap.BilinForm ℤ N.X) {m : ℕ} (ho : Odd m)
    {p p' : N.QT (m ^ 2)} (h : N.QEq p p') : N.arcTx be m p' = N.arcTx be m p := by
  obtain ⟨z, h1, h2⟩ := h
  ext n
  simp only [NumD.arcTx, PowerSeries.coeff_mk]
  conv_rhs => rw [← finsum_comp_equiv (Equiv.addRight (m • z))]
  refine finsum_congr fun χ => ?_
  have hx : p'.1.1.toAdd + m • χ = p.1.1.toAdd + m • (χ + m • z) := by
    rw [h1, smul_add, smul_smul, ← pow_two]
    abel
  simp only [Equiv.coe_addRight, hx, (GlobalTheory.T.thetaConstantTerm_representative_dependence O N m ho p p' χ).1 z h1 h2]

private theorem map_finsum_of_injective' {α M M' : Type*} [AddCommMonoid M] [AddCommMonoid M'] (φ : M →+ M')
    (hφ : Function.Injective φ) (g : α → M) : φ (∑ᶠ a, g a) = ∑ᶠ a, φ (g a) := by
  by_cases h : (Function.support g).Finite
  · exact map_finsum φ h
  · have hs : Function.support (fun a => φ (g a)) = Function.support g := by
      ext a
      simp only [Function.mem_support, ne_eq]
      exact ⟨fun h1 h2 => h1 (by rw [h2, map_zero]), fun h1 h2 => h1 (hφ (by rw [h2, map_zero]))⟩
    have h' : (Function.support (fun a => φ (g a))).Infinite := by
      rw [hs]
      exact h
    rw [finsum_of_infinite_support h, finsum_of_infinite_support h', map_zero]

private theorem unit_mul_map_finsum {α F F' : Type*} [Field F] [Field F'] (f : F →+* F') (c : F'ˣ) (g : α → F) :
    (c : F') * f (∑ᶠ a, g a) = ∑ᶠ a, (c : F') * f (g a) := by
  refine map_finsum_of_injective' ((AddMonoidHom.mulLeft (c : F')).comp f.toAddMonoidHom) ?_ g
  intro a b hab
  have hab' : (c : F') * f a = (c : F') * f b := hab
  exact f.injective (mul_left_cancel₀ c.ne_zero hab')

private theorem unit_mul_map_finsum_prop {F F' : Type*} [Field F] [Field F'] (f : F →+* F') (c : F'ˣ) (P : Prop)
    (x : F) : (c : F') * f (∑ᶠ (_ : P), x) = ∑ᶠ (_ : P), (c : F') * f x := by
  classical
  rw [finsum_eq_if, finsum_eq_if]
  split_ifs <;> simp

theorem arcTx_hom {F F' : Type} [Field F] [Field F'] {f : F →+* F'} {N : NumD F} {N' : NumD F'} (I : NumD.Hom f N N')
    (be : LinearMap.BilinForm ℤ N.X) (be' : LinearMap.BilinForm ℤ N'.X) (hb : ∀ y z, be y z = be' (I.e y) (I.e z))
    {m : ℕ} (ho : Odd m) {p : N.QT (m ^ 2)} {p' : N'.QT (m ^ 2)} (h1 : p'.1.1.toAdd = I.e p.1.1.toAdd)
    (h2 : I.Rel p.1.2 p'.1.2) :
    N'.arcTx be' m p' = PowerSeries.C (I.lam : F') * PowerSeries.map f (N.arcTx be m p) := by
  ext n
  rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_map]
  simp only [NumD.arcTx, PowerSeries.coeff_mk, unit_mul_map_finsum f I.lam, unit_mul_map_finsum_prop f I.lam]
  conv_lhs => rw [← finsum_comp_equiv I.e.toEquiv]
  refine finsum_congr fun χ => ?_
  have hx : p'.1.1.toAdd + m • I.e χ = I.e (p.1.1.toAdd + m • χ) := by
    rw [h1, map_add (f := _), map_nsmul]
  have hχ : I.e.toEquiv χ = I.e χ := rfl
  rw [hχ]
  simp only [hx, ← hb, I.txT_eq ho p p' h1 h2 χ]

private theorem eval2_smul_of_isHomogeneous {J S T : Type*} [CommSemiring S] [CommSemiring T] (g : S →+* T) (c : T)
    (w : J → T) {G : MvPolynomial J S} {d : ℕ} (hG : G.IsHomogeneous d) :
    MvPolynomial.eval₂ g (fun x => c * w x) G = c ^ d * MvPolynomial.eval₂ g w G := by
  simp only [MvPolynomial.eval₂_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [hG.degree_eq_sum_deg_support hs]
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  ring

theorem aeval_smul_map {J S F F' : Type} [CommRing S] [CommRing F] [CommRing F'] (f : F →+* F') (c : S →+* F)
    (l : F') (v : J → PowerSeries F) {G : MvPolynomial J S} {d : ℕ} (hG : G.IsHomogeneous d) :
    MvPolynomial.aeval (fun x => PowerSeries.C l * PowerSeries.map f (v x)) (MvPolynomial.map (f.comp c) G) =
      PowerSeries.C l ^ d * PowerSeries.map f (MvPolynomial.aeval v (MvPolynomial.map c G)) := by
  rw [MvPolynomial.aeval_def, MvPolynomial.aeval_def, MvPolynomial.eval₂_map, MvPolynomial.eval₂_map,
    eval2_smul_of_isHomogeneous _ _ (fun x => PowerSeries.map f (v x)) hG, MvPolynomial.eval₂_comp_left]
  have hr : (PowerSeries.map f).comp ((algebraMap F (PowerSeries F)).comp c) =
      (algebraMap F' (PowerSeries F')).comp (f.comp c) :=
    RingHom.ext fun a => by simp [PowerSeries.map_C]
  rw [hr]
  rfl

theorem cf_comp {F F' : Type} [CommRing F] [CommRing F'] (f : F →+* F') (a b : F) :
    cf (f a) (f b) = f.comp (cf a b) := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp
  · intro i
    fin_cases i <;> simp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
  {R : Type} [CommRing R] [IsDomain R] {F : Type} [Field F] [Algebra (FractionRing R) F]
  {R' : Type} [CommRing R'] [IsDomain R'] {F' : Type} [Field F'] [Algebra (FractionRing R') F']

theorem over_iff {f : F →+* F'} {A : ArcF D R F} {A' : ArcF D R' F'} (h : A.Over f A') :
    ∃ e : A.N.X ≃+ A'.N.X, ∀ (k : ℕ) (β : A.N.Form k) (β' : A'.N.Form k), (∀ y z, β.be y z = β'.be (e y) (e z)) →
      (A.Bal β ↔ A'.Bal β') ∧ ∀ m : ℕ, Odd m → ∀ (G : MvPolynomial D.La (MvPolynomial (Fin 2) ℤ)) (d : ℕ),
        G.IsHomogeneous d →
        (MvPolynomial.aeval (fun x => A.N.arcTx β.be m (A.q _ x))
            (MvPolynomial.map (cf (A.I.ζ (m ^ 2) : F) A.ρ) G) = 0 ↔
          MvPolynomial.aeval (fun x => A'.N.arcTx β'.be m (A'.q _ x))
            (MvPolynomial.map (cf (A'.I.ζ (m ^ 2) : F') A'.ρ) G) = 0) := by
  obtain ⟨I, hρ, hζ, hact, hq⟩ := h
  refine ⟨I.e, fun k β β' hbe => ⟨?_, fun m hm G d hG => ?_⟩⟩
  · constructor
    · intro hB a y' z'
      obtain ⟨y, rfl⟩ := I.e.surjective y'
      obtain ⟨z, rfl⟩ := I.e.surjective z'
      have h1 := hB a y z
      rw [hbe, hbe, hact, hact] at h1
      exact h1
    · intro hB a y z
      rw [hbe, hbe, hact, hact]
      exact hB _ _ _
  · have hpos : 0 < m ^ 2 := pow_pos hm.pos 2
    have hv : ∀ x, A'.N.arcTx β'.be m (A'.q _ x) =
        PowerSeries.C (I.lam : F') * PowerSeries.map f (A.N.arcTx β.be m (A.q (m ^ 2) x)) := by
      intro x
      obtain ⟨p', h1, h2, h3⟩ := hq (m ^ 2) x hpos
      rw [arcTx_qEq A'.N β'.be hm h3]
      exact arcTx_hom I β.be β'.be hbe hm h1 h2
    have hcf : cf (A'.I.ζ (m ^ 2) : F') A'.ρ = f.comp (cf (A.I.ζ (m ^ 2) : F) A.ρ) := by
      rw [← hρ, ← hζ _ hpos, cf_comp]
    simp only [hv, hcf]
    rw [aeval_smul_map f (cf (A.I.ζ (m ^ 2) : F) A.ρ) (I.lam : F') (fun x => A.N.arcTx β.be m (A.q (m ^ 2) x)) hG]
    have hC : PowerSeries.C (I.lam : F') ^ d ≠ 0 :=
      pow_ne_zero _ ((map_ne_zero_iff _ PowerSeries.C_injective).mpr I.lam.ne_zero)
    constructor
    · intro h0
      rw [h0, map_zero, mul_zero]
    · intro h0
      have h0' := (mul_eq_zero.mp h0).resolve_left hC
      exact PowerSeries.map_injective f f.injective (by rw [h0', map_zero])

theorem aeval_arcTx_eq_zero_of_vanishC : HV → Laws6 → GlobalTheory.LN.UDvrSt → GlobalTheory.LN.HomExtSt → ThetaPtDeterminesSt → EndDeterminedOnTorsionSt → ThetaUnifAV → AllD fun {_} _ _ _ {H} D => ∀ (R : Type) [CommRing R] [IsDomain R] (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra (FractionRing R) F] (A : ArcF D R F) (k : ℕ) (β : A.N.Form k), A.Bal β → ∀ m : ℕ, m ^ 2 ∣ k → Odd m → Compat H (m ^ 2) (A.I.ζ (m ^ 2) : F) A.ρ → ∀ G, VanishC D m G → MvPolynomial.aeval (fun x => A.N.arcTx β.be m (A.q _ x)) (MvPolynomial.map (cf (A.I.ζ (m ^ 2) : F) A.ρ) G) = 0 := by
  intro hHV h6 hU hE hT hEnd hTU
  have hHV' := hHV
  obtain ⟨⟨hL, hL2, -⟩, -⟩ := hHV'
  have hGt := GlobalTheory.Ex.GtValues.points_correspond
  have hWp := GlobalTheory.WeilValues.weil_eq_values hGt (GlobalTheory.Ex.brFam hL hL2)
  have hC4400 := GlobalTheory.T.exists_thetaPoint_complexDegeneration_small hHV h6 hU hE hT hEnd hTU
  have hdown := GlobalTheory.FieldPull.exists_countable_model hL hGt hWp
  have hup := GlobalTheory.ArcExt.exists_arcF_over hL hGt hWp
  unfold AllD at hC4400 hdown hup ⊢
  intro E _ _ _ H D R _ _ F _ _ _ _ A k β hB m hmk hm hC G hV
  obtain ⟨-, ⟨d, hG⟩, hVan⟩ := hV
  have hpos : 0 < m ^ 2 := pow_pos hm.pos 2
  obtain ⟨R₁, F₁, _, _, _, _, _, _, f, A₁, hA₁⟩ := hdown E H D R F A
  haveI : CharZero F₁ := A₁.charZero
  obtain ⟨e₁, he₁⟩ := over_iff hA₁
  obtain ⟨β₁, hβ₁⟩ := exists_form e₁ β
  have h1 := he₁ k β₁ β hβ₁
  rw [← h1.2 m hm G d hG]
  obtain ⟨I₁, hρ₁, hζ₁, _, _⟩ := hA₁
  have hC₁ : Compat H (m ^ 2) (A₁.I.ζ (m ^ 2) : F₁) A₁.ρ := by
    intro c hc
    have h0 := hC c hc
    rw [← hρ₁, ← hζ₁ _ hpos, cf_comp, RingHom.comp_apply] at h0
    exact f.injective (by rw [h0, map_zero])
  have halg : ∀ i, IsAlgebraic ℚ (![zeta (m ^ 2), H.rt0] i) := by
    intro i
    fin_cases i
    · show IsAlgebraic ℚ (zeta (m ^ 2))
      have hz : IsPrimitiveRoot (zeta (m ^ 2)) (m ^ 2) := by
        unfold zeta
        exact Complex.isPrimitiveRoot_exp _ hpos.ne'
      refine IsIntegral.isAlgebraic (IsIntegral.of_pow hpos ?_)
      rw [hz.pow_eq_one]
      exact isIntegral_one
    · show IsAlgebraic ℚ H.rt0
      refine IsIntegral.isAlgebraic (IsIntegral.of_pow (n := 2) two_pos ?_)
      rw [H.sqrt_neg_disc_sq]
      have hd := isIntegral_algebraMap (R := ℚ) (A := ℂ) (x := -(H.d : ℚ))
      simpa using hd
  obtain ⟨g, hg⟩ := GlobalTheory.exists_ringHom_complex_of_countable_of_relations F₁
    ![(A₁.I.ζ (m ^ 2) : F₁), A₁.ρ] ![zeta (m ^ 2), H.rt0] halg hC₁
  have hg0 : g (A₁.I.ζ (m ^ 2) : F₁) = zeta (m ^ 2) := by simpa using hg 0
  have hg1 : g A₁.ρ = H.rt0 := by simpa using hg 1
  letI : Algebra (FractionRing R₁) ℂ := (g.comp (algebraMap (FractionRing R₁) F₁)).toAlgebra
  obtain ⟨A₂, -, hA₂⟩ := hup E H D R₁ F₁ ℂ g (fun x => rfl) A₁
  obtain ⟨e₂, he₂⟩ := over_iff hA₂
  obtain ⟨β₂, hβ₂⟩ := exists_form e₂.symm β₁
  have hb12 : ∀ y z, β₁.be y z = β₂.be (e₂ y) (e₂ z) := by
    intro y z
    rw [hβ₂]
    simp
  have h2 := he₂ k β₁ β₂ hb12
  rw [h2.2 m hm G d hG]
  obtain ⟨I₂, hρ₂, hζ₂, _, _⟩ := hA₂
  have hρ₂' : A₂.ρ = H.rt0 := by rw [← hρ₂, hg1]
  have hζ₂' : (A₂.I.ζ (m ^ 2) : ℂ) = zeta (m ^ 2) := by rw [← hζ₂ _ hpos, hg0]
  have hB₂ : A₂.Bal β₂ := h2.1.mp (h1.1.mpr hB)
  obtain ⟨ε, hε, hsmall⟩ := hC4400 E H D R₁ A₂ hρ₂' k β₂ hB₂ m hmk hm
  rw [hζ₂', hρ₂']
  refine GlobalTheory.Ex.ArcForm.aeval_arcTx_eq_zero A₂.N k β₂ m hmk hm D.La (fun x => A₂.q _ x) _ ε hε
    fun u hu => ⟨(hsmall u hu).1, ?_⟩
  obtain ⟨o, hoρ, hoζ, hθ⟩ := (hsmall u hu).2
  rw [MvPolynomial.eval_map]
  exact hVan o hoρ (by rw [hoζ]; exact hζ₂') _ hθ

end GlobalTheory.ArcIdentity
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaSeriesIdentityPrincipleComplexPointsStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_series_identity_principle_complex_points : HV → Laws6 → GlobalTheory.LN.UDvrSt → GlobalTheory.LN.HomExtSt → ThetaPtDeterminesSt → EndDeterminedOnTorsionSt → ThetaUnifAV → AllD fun {_} _ _ _ {H} D => ∀ (R : Type) [CommRing R] [IsDomain R] (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra (FractionRing R) F] (A : ArcF D R F) (k : ℕ) (β : A.N.Form k), A.Bal β → ∀ m : ℕ, m ^ 2 ∣ k → Odd m → Compat H (m ^ 2) (A.I.ζ (m ^ 2) : F) A.ρ → ∀ G, VanishC D m G → MvPolynomial.aeval (fun x => A.N.arcTx β.be m (A.q _ x)) (MvPolynomial.map (cf (A.I.ζ (m ^ 2) : F) A.ρ) G) = 0 := by
  first | exact @GlobalTheory.ArcIdentity.aeval_arcTx_eq_zero_of_vanishC | exact GlobalTheory.ArcIdentity.aeval_arcTx_eq_zero_of_vanishC | (intros; apply GlobalTheory.ArcIdentity.aeval_arcTx_eq_zero_of_vanishC <;> assumption)
end
