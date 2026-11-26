module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.WeightFloorInequalities
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.GCauchyHolds
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.SemicharUnitFrame
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.AppellHumbertSectionEntireWithFactor
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaRuleValuePeriods
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.ExistsTorusOfPeriodHermitian
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IsTorusAtOfIsTorusOf

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.PolyDerivProdFockEqTranslate
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal GlobalTheory.BlockTh GlobalTheory.EtaAn
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnVal

theorem polyDeriv_comp_linear_equiv {σ V W : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [NormedAddCommGroup W] [NormedSpace ℂ W] (e : V ≃L[ℂ] W) (P : MvPolynomial σ ℂ) (u : σ → V)
    (G : W → ℂ) (x : V) :
    I2.polyDeriv P u (fun z => G (e z)) x = I2.polyDeriv P (fun ℓ => e (u ℓ)) G (e x) := by
  unfold I2.polyDeriv
  refine Finset.sum_congr rfl fun m _ => ?_
  have h := e.iteratedFDerivWithin_comp_right G (s := Set.univ) uniqueDiffOn_univ (x := x)
    (Set.mem_univ _) (Multiset.card (Finsupp.toMultiset m))
  rw [Set.preimage_univ, iteratedFDerivWithin_univ, iteratedFDerivWithin_univ] at h
  have h' : (fun z => G (e z)) = G ∘ e := rfl
  rw [h', h]
  rfl

theorem lintor_hf_neg_right {J : Type} [Fintype J] (v w : EuclideanSpace ℂ J) :
    I2.Hf v (-w) = -I2.Hf v w := by
  simp [I2.Hf]

theorem lintor_hf_neg_left {J : Type} [Fintype J] (v w : EuclideanSpace ℂ J) :
    I2.Hf (-v) w = -I2.Hf v w := by
  simp [I2.Hf]

theorem polyDeriv_prod_fock_eq_translate : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (X : I2.PT E) (g : ℕ) (ψ : (Fin g → ℂ) ≃ₗ[ℂ] I2.Vsp X.dim) (Hm : Matrix (Fin g) (Fin g) ℂ) (θ : (Fin g → ℂ) → ℂ), (∀ z w, I2.Hf (ψ z) (ψ w) = hermForm Hm z w) → Differentiable ℂ θ → ∀ (n N : ℕ) (a : Fin n → Fin g → ℂ) (Io : Type) (P : MvPolynomial Io ℂ) (u : Io → Fin n → Fin g → ℂ), I2.polyDeriv P u (fun z => ∏ b, fock Hm ((N : ℤ) ^ 2) (a b) (fun w => θ ((N : ℂ) • w)) (z b)) 0 = I2.polyDeriv P (fun ℓ b => ψ (u ℓ b)) (X.U (N ^ 2) (fun b => -ψ (a b)) (I2.s0 X ((N : ℂ) • LinearMap.id) fun v => θ (ψ.symm (v 0)))) 0 := by
  intro E _ _ _ X g ψ Hm θ hH _ n N a Io P u
  let e : (Fin n → Fin g → ℂ) ≃L[ℂ] (Fin n → I2.Vsp X.dim) :=
    ContinuousLinearEquiv.piCongrRight fun _ => ψ.toContinuousLinearEquiv
  have he : ∀ z, e z = fun b => ψ (z b) := fun _ => rfl
  have key := polyDeriv_comp_linear_equiv e P u (X.U (N ^ 2) (fun b => -ψ (a b))
    (I2.s0 X ((N : ℂ) • LinearMap.id) fun v => θ (ψ.symm (v 0)))) 0
  rw [map_zero] at key
  refine Eq.trans ?_ key
  congr 1
  funext z
  rw [he]
  simp only [fock, I2.PT.U, I2.s0, I2.HC, lintor_hf_neg_right, lintor_hf_neg_left, hH, neg_neg,
    Finset.prod_mul_distrib, ← Complex.exp_sum, Pi.sub_apply, sub_neg_eq_add,
    LinearMap.smul_apply, LinearMap.id_apply, ← map_add, ← map_smul, LinearEquiv.symm_apply_apply]
  congr 2
  simp only [Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_div, mul_neg]
  push_cast
  rfl

end GlobalTheory.AnVal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.DatumNsmulEqZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal GlobalTheory.BlockTh GlobalTheory.EtaAn
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnVal

theorem datum_nsmul_eq_zero {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)
    {k : ℕ} (hk : k ≠ 0) {x : D.La} (h : k • x = 0) : x = 0 := by
  apply D.unimod.1
  ext y
  have h1 : D.EF (k • x) y = 0 := by rw [h, map_zero]; rfl
  rw [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul] at h1
  rw [map_zero, LinearMap.zero_apply]
  exact (mul_eq_zero.1 h1).resolve_left (by exact_mod_cast hk)

theorem marking_iso_mod : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ' : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ' ty) (i : Fin F.n), (∀ a, (∃ b, F.t i a = l.M • b) → ∃ b, a = l.M • b) ∧ ∀ b, ∃ a e, b = F.t i a + l.M • e := by
  intro E _ _ _ H Dw l Xo _ σ' g ty F i
  obtain ⟨k, hk⟩ : l.M ∣ l.M' := Nat.dvd_lcm_left _ _
  have hM : l.M ≠ 0 := by have := l.three_le; omega
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact Nat.lcm_ne_zero hM l.A_pos.ne' (by simpa [Geo.Tor.Level.M'] using hk)
  refine ⟨?_, ?_⟩
  · rintro a ⟨b, hb⟩
    obtain ⟨c, hc⟩ := (F.t_inj i (k • a)).1 ⟨b, by rw [map_nsmul, hb, hk, mul_comm, mul_smul]⟩
    refine ⟨c, sub_eq_zero.1 (datum_nsmul_eq_zero Dw hk0 ?_)⟩
    rw [smul_sub, hc, hk, mul_comm, mul_smul, sub_self]
  · intro b
    obtain ⟨a, e, h⟩ := F.t_surj i b
    exact ⟨a, k • e, by rw [h, hk, mul_smul]⟩

end GlobalTheory.AnVal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IsPiActLOfIsTorusOf
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal GlobalTheory.BlockTh GlobalTheory.EtaAn
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnVal.IsPiAct

theorem negOnePow_natCast_mul (M : ℕ) (k : ℤ) :
    Int.negOnePow ((M : ℤ) * k) = Int.negOnePow k ^ M := by
  induction M with
  | zero => simp
  | succ n ih =>
    push_cast
    rw [add_mul, _root_.one_mul, Int.negOnePow_add, ih, pow_succ]

theorem isPi_actL_of_isTorusOf :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Pm : D.La →+ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ) (T : I2.PT E) (ψ : (Fin g → ℂ) ≃ₗ[ℂ] I2.Vsp T.dim), IsPeriod D ty Pm → IsTorusOf D ty Pm Hm T ψ → ∀ (α : 𝓞 E) (M : ℕ), α * H.bar α = (M : 𝓞 E) → I2.IsPi T M (vspActL α) := by
  intro E _ _ _ H D g ty Pm Hm T ψ hP hT α M hM
  obtain ⟨-, -, -, hL, hact, heps⟩ := hT

  have hnorm : ∀ τ : E →+* ℂ, τ (α : E) * starRingEnd ℂ (τ (α : E)) = (M : ℂ) := by
    intro τ
    have h := congrArg (fun x : 𝓞 E => τ (x : E)) hM
    push_cast at h
    have hb := congrArg τ (H.bar_eq α)
    rw [IsCMField.complexEmbedding_complexConj] at hb
    rw [map_mul, map_natCast] at h
    rw [← hb]
    exact h
  have hcoord : ∀ (u : I2.Vsp T.dim) i, (I2.act α u) i = i.1 (α : E) * u i := fun _ _ => rfl

  have hlat : ∀ a, I2.act α (ψ (Pm a)) = ψ (Pm (α • a)) := by
    intro a
    rw [← hact]
    congr 1
    funext k
    exact (hP.1 α a k).symm
  unfold I2.IsPi
  refine ⟨fun β v => ?_, fun x hx => ?_, fun v w => ?_, fun x hx => ?_⟩ <;>
    simp only [vspActL, LinearMap.coe_mk, AddHom.coe_mk]
  · ext i
    change i.1 (α : E) * (i.1 (β : E) * v i) = i.1 (β : E) * (i.1 (α : E) * v i)
    ring
  · obtain ⟨a, rfl⟩ := (hL x).1 hx
    rw [hlat, hL]
    exact ⟨α • a, rfl⟩
  · unfold I2.Hf
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hcoord, hcoord, map_mul]
    linear_combination (v i * starRingEnd ℂ (w i)) * hnorm i.1
  · obtain ⟨a, rfl⟩ := (hL x).1 hx
    have hEF : D.EF (α • a) (H.w0 • α • a) = (M : ℤ) * D.EF a (H.w0 • a) := by
      have hc : H.bar α * H.w0 * α = (M : 𝓞 E) * H.w0 := by rw [← hM]; ring
      rw [D.adj, smul_smul, smul_smul, hc, mul_smul, Nat.cast_smul_eq_nsmul, map_nsmul, nsmul_eq_mul]
    rw [hlat, heps, heps, hEF, negOnePow_natCast_mul, Units.val_pow_eq_pow_val]

end GlobalTheory.AnVal.IsPiAct
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsTorusOfRows
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal GlobalTheory.BlockTh GlobalTheory.EtaAn
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ScalarTorus

open GlobalTheory.PeriodTorus

private theorem mem_lat_basis_map_iff {J K : Type} [Fintype J] (b : Module.Basis K ℝ (EuclideanSpace ℂ J))
    (f : EuclideanSpace ℂ J ≃ₗ[ℝ] EuclideanSpace ℂ J) (x : EuclideanSpace ℂ J) :
    x ∈ I2.lat (b.map f) ↔ f.symm x ∈ I2.lat b := by
  let fz : EuclideanSpace ℂ J ≃ₗ[ℤ] EuclideanSpace ℂ J := f.toAddEquiv.toIntLinearEquiv
  have hr : Set.range (b.map f) = fz '' Set.range b := by
    rw [Module.Basis.coe_map, Set.range_comp]
    congr 1
  show x ∈ Submodule.span ℤ (Set.range (b.map f)) ↔ f.symm x ∈ Submodule.span ℤ (Set.range b)
  rw [hr, ← LinearEquiv.coe_coe, Submodule.span_image, Submodule.mem_map_equiv]
  rfl


open TorusAtAssembly in
theorem exists_torusOf_rows : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Pm : D.La →+ (Fin g → ℂ)) (t : ℝ) (row : Fin g → ℕ), 0 < t → IsTypeFn H D.p D.q ty → IsPeriod D ty Pm → (∀ a b, (hermForm (Matrix.diagonal fun _ => (t : ℂ)) (Pm a) (Pm b)).im = D.EF a b) → (∀ j, row j < D.mult (ty j)) → (∀ j j', ty j = ty j' → row j = row j' → j = j') → ∃ (T : I2.PT E) (ψ : (Fin g → ℂ) ≃ₗ[ℂ] I2.Vsp T.dim), IsTorusOf D ty Pm (Matrix.diagonal fun _ => (t : ℂ)) T ψ ∧ ∀ j, ∃ h : row j < T.dim (ty j), ψ (Pi.single j 1) = open Classical in (Real.sqrt t : ℂ) • EuclideanSpace.single (⟨ty j, ⟨row j, h⟩⟩ : I2.Idx T.dim) (1 : ℂ) := by
  classical
  intro E _ _ _ H D g ty Pm t row ht hty hP hE hrow hinj
  have hform : ∀ z w : Fin g → ℂ, hermForm (Matrix.diagonal fun _ => (t : ℂ)) z w =
      ∑ j, z j * ((t : ℂ) * (starRingEnd ℂ) (w j)) := by
    intro z w
    simp only [hermForm, dotProduct, Matrix.mulVec_diagonal, Pi.star_apply, Complex.star_def]
  have hH : (Matrix.diagonal fun _ : Fin g => (t : ℂ)).IsHermitian :=
    Matrix.isHermitian_diagonal_of_self_adjoint _ (by
      show star _ = _
      funext i
      simp)
  have hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm (Matrix.diagonal fun _ : Fin g => (t : ℂ)) z z).re := by
    intro z hz
    rw [hform]
    have hterm : ∀ j, z j * ((t : ℂ) * (starRingEnd ℂ) (z j)) = ((t * Complex.normSq (z j) : ℝ) : ℂ) := by
      intro j
      rw [Complex.ofReal_mul, ← Complex.mul_conj]
      ring
    simp only [hterm, ← Complex.ofReal_sum, Complex.ofReal_re]
    obtain ⟨j, hj⟩ := Function.ne_iff.1 hz
    exact Finset.sum_pos' (fun i _ => mul_nonneg ht.le (Complex.normSq_nonneg _))
      ⟨j, Finset.mem_univ _, mul_pos ht (Complex.normSq_pos.2 hj)⟩
  obtain ⟨T₀, ψ₀, hr, hdim, hHf, hL, hact, heps⟩ := exists_torusOf E H D g ty Pm _ hty hP hH hpos hE
  have hrow' : ∀ j, row j < T₀.dim (ty j) := by
    intro j
    rw [hdim]
    exact hrow j
  let f : Fin g → I2.Idx T₀.dim := fun j => ⟨ty j, ⟨row j, hrow' j⟩⟩
  have hfinj : Function.Injective f := by
    have hc : Function.Injective ((fun i : I2.Idx T₀.dim => (i.1, (i.2 : ℕ))) ∘ f) := by
      intro j j' h
      simp only [Function.comp, f, Prod.mk.injEq] at h
      exact hinj j j' h.1 h.2
    exact Function.Injective.of_comp hc
  have hcard : Fintype.card (Fin g) = Fintype.card (I2.Idx T₀.dim) := by
    have h1 : Fintype.card (Fin g) = ∑ τ, Fintype.card {i // ty i = τ} := by
      rw [← Fintype.card_sigma]
      exact Fintype.card_congr (Equiv.sigmaFiberEquiv ty).symm
    rw [h1, Fintype.card_sigma]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [Fintype.card_fin, hdim τ, ← Nat.card_eq_fintype_card, ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum.mult]
    split_ifs with h
    · exact (hty τ).1 h
    · exact (hty τ).2 h
  let e : Fin g ≃ I2.Idx T₀.dim :=
    Equiv.ofBijective f ((Fintype.bijective_iff_injective_and_card f).2 ⟨hfinj, hcard⟩)
  have he_ty : ∀ i, ty (e.symm i) = i.1 := by
    intro i
    exact congrArg Sigma.fst (e.apply_symm_apply i)
  have hs2 : (Real.sqrt t : ℂ) * (Real.sqrt t : ℂ) = t := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt ht.le]
  have hs0 : (Real.sqrt t : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 ht).ne'
  let ψ : (Fin g → ℂ) ≃ₗ[ℂ] I2.Vsp T₀.dim :=
    { toFun := fun z => WithLp.toLp 2 (fun i => (Real.sqrt t : ℂ) * z (e.symm i))
      invFun := fun v j => v (e j) / (Real.sqrt t : ℂ)
      map_add' := by
        intro z w
        ext i
        simp [mul_add]
      map_smul' := by
        intro c z
        ext i
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, PiLp.smul_apply]
        ring
      left_inv := by
        intro z
        funext j
        simp only [Equiv.symm_apply_apply]
        field_simp
      right_inv := by
        intro v
        ext i
        simp only [Equiv.apply_symm_apply]
        field_simp }
  have hψ : ∀ z i, ψ z i = (Real.sqrt t : ℂ) * z (e.symm i) := fun z i => rfl
  have hψHf : ∀ z w, I2.Hf (ψ z) (ψ w) = hermForm (Matrix.diagonal fun _ => (t : ℂ)) z w := by
    intro z w
    rw [hform]
    unfold I2.Hf
    simp only [hψ]
    refine (e.symm.sum_comp (fun j => (Real.sqrt t : ℂ) * z j * (starRingEnd ℂ) ((Real.sqrt t : ℂ) * w j))).trans
      (Finset.sum_congr rfl fun j _ => ?_)
    rw [map_mul, Complex.conj_ofReal]
    linear_combination (z j * (starRingEnd ℂ) (w j)) * hs2
  have hψact : ∀ (α : 𝓞 E) z, ψ (fun k => ty k (α : E) * z k) = I2.act α (ψ z) := by
    intro α z
    ext i
    simp only [hψ, I2.act, PiLp.toLp_apply]
    rw [he_ty]
    ring
  let U : I2.Vsp T₀.dim ≃ₗ[ℂ] I2.Vsp T₀.dim := ψ₀.symm.trans ψ
  have hUHf : ∀ x y, I2.Hf (U x) (U y) = I2.Hf x y := by
    intro x y
    have h1 := hHf (ψ₀.symm x) (ψ₀.symm y)
    simp only [LinearEquiv.apply_symm_apply] at h1
    rw [h1, ← hψHf]
    rfl
  have hUact : ∀ (α : 𝓞 E) x, U (I2.act α x) = I2.act α (U x) := by
    intro α x
    obtain ⟨z, rfl⟩ := ψ₀.surjective x
    rw [← hact α z]
    simp only [U, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
    exact hψact α z
  have hUsymm_act : ∀ (α : 𝓞 E) x, U.symm (I2.act α x) = I2.act α (U.symm x) := by
    intro α x
    apply U.injective
    rw [hUact, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  have hUsymmHf : ∀ x y, I2.Hf (U.symm x) (U.symm y) = I2.Hf x y := by
    intro x y
    rw [← hUHf, U.apply_symm_apply, U.apply_symm_apply]
  have hmem : ∀ x, x ∈ I2.lat (T₀.b.map (U.restrictScalars ℝ)) ↔ U.symm x ∈ I2.lat T₀.b :=
    fun x => mem_lat_basis_map_iff _ _ x
  let T' : I2.PT E :=
    { dim := T₀.dim
      r := T₀.r
      dim_conj := T₀.dim_conj
      b := T₀.b.map (U.restrictScalars ℝ)
      stable := by
        intro α x hx
        rw [hmem] at hx ⊢
        rw [hUsymm_act]
        exact T₀.stable α _ hx
      integral := by
        intro x y hx hy
        rw [hmem] at hx hy
        rw [← hUsymmHf]
        exact T₀.integral _ _ hx hy
      perfect := by
        intro φ
        let m : I2.lat T₀.b →+ I2.lat (T₀.b.map (U.restrictScalars ℝ)) :=
          AddMonoidHom.mk' (fun y => ⟨U y, (hmem _).2 (by rw [U.symm_apply_apply]; exact y.2)⟩)
            (by
              intro a b
              apply Subtype.ext
              simp)
        obtain ⟨x₀, hx₀, hφ⟩ := T₀.perfect (φ.comp m)
        refine ⟨U x₀, (hmem _).2 (by rw [U.symm_apply_apply]; exact hx₀), fun y => ?_⟩
        have hy : U.symm (y : I2.Vsp T₀.dim) ∈ I2.lat T₀.b := (hmem _).1 y.2
        have h1 := hφ ⟨_, hy⟩
        have h2 : m ⟨_, hy⟩ = y := Subtype.ext (U.apply_symm_apply _)
        rw [AddMonoidHom.comp_apply, h2] at h1
        rw [h1, ← hUHf, U.apply_symm_apply]
      eps := fun v => T₀.eps (U.symm v)
      eps_pm := by
        intro x hx
        rw [hmem] at hx
        exact T₀.eps_pm _ hx
      eps_add := by
        intro x hx y hy
        rw [hmem] at hx hy
        rw [map_add (f := _), T₀.eps_add _ hx _ hy, hUsymmHf]
      eps_iso := by
        intro x hx h
        rw [hmem] at hx
        exact T₀.eps_iso _ hx fun α => by rw [← hUsymm_act, hUsymmHf]; exact h α }
  have hTL : ∀ v, v ∈ T'.L ↔ U.symm v ∈ I2.lat T₀.b := hmem
  have hTeps : ∀ v, T'.eps v = T₀.eps (U.symm v) := fun v => rfl
  refine ⟨T', ψ, ⟨hr, hdim, hψHf, ?_, hψact, ?_⟩, ?_⟩
  · intro v
    rw [hTL, hL]
    constructor
    · rintro ⟨a, ha⟩
      refine ⟨a, ?_⟩
      rw [← U.apply_symm_apply v, ← ha]
      simp [U]
    · rintro ⟨a, ha⟩
      refine ⟨a, ?_⟩
      rw [← ha]
      simp [U]
  · intro a
    rw [hTeps, ← heps a]
    congr 1
    simp [U]
  · intro j
    refine ⟨hrow' j, ?_⟩
    ext i
    rw [hψ]
    simp only [PiLp.smul_apply, EuclideanSpace.single, PiLp.ofLp_single, smul_eq_mul, Pi.single_apply]
    have hiff : e.symm i = j ↔ i = ⟨ty j, ⟨row j, hrow' j⟩⟩ := by
      rw [Equiv.symm_apply_eq]
      rfl
    rcases em (i = ⟨ty j, ⟨row j, hrow' j⟩⟩) with h | h
    · rw [if_pos (hiff.2 h), if_pos h]
    · rw [if_neg (mt hiff.1 h), if_neg h]

end GlobalTheory.ScalarTorus
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.PolyDerivLevelSqEqAlpha
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AlphaChain

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal GlobalTheory.BlockTh GlobalTheory.EtaAn
attribute [local instance] Over.cartesianMonoidalCategory

theorem polyDeriv_comp_clm {J V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (Q : MvPolynomial J ℂ) (u : J → V)
    (G : V → ℂ) (hG : ContDiff ℂ ⊤ G) (g : V →L[ℂ] V) (c : J → ℂ) (hg : ∀ l, g (u l) = c l • u l) (κ : ℂ)
    (hκ : ∀ m ∈ Q.support, (m.prod fun l k => c l ^ k) = κ) :
    I2.polyDeriv Q u (G ∘ g) 0 = κ * I2.polyDeriv Q u G 0 := by
  unfold I2.polyDeriv
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have h := ContinuousLinearMap.iteratedFDeriv_comp_right g hG 0
    (i := Multiset.card (Finsupp.toMultiset m)) le_top
  rw [h, map_zero, ContinuousMultilinearMap.compContinuousLinearMap_apply]
  simp only [hg]
  rw [ContinuousMultilinearMap.map_smul_univ, ← hκ m hm, smul_eq_mul]
  have : (∏ k : Fin (Multiset.card (Finsupp.toMultiset m)),
      c ((Finsupp.toMultiset m).toList.get (k.cast (Multiset.length_toList _).symm))) =
      m.prod fun l k => c l ^ k := by
    have e1 : (∏ k : Fin (Multiset.card (Finsupp.toMultiset m)),
      c ((Finsupp.toMultiset m).toList.get (k.cast (Multiset.length_toList _).symm))) =
      ∏ k : Fin (Finsupp.toMultiset m).toList.length, c ((Finsupp.toMultiset m).toList.get k) :=
      Fintype.prod_equiv (finCongr (Multiset.length_toList _).symm) _ _ (fun _ => rfl)
    rw [e1, ← List.prod_ofFn]
    have e2 : (List.ofFn fun k => c ((Finsupp.toMultiset m).toList.get k)) = (Finsupp.toMultiset m).toList.map c := by
      rw [List.ofFn_comp' , List.ofFn_get]
    rw [e2, Multiset.prod_map_toList]
    classical
    rw [Finsupp.toMultiset_map, Finsupp.prod_toMultiset, Finsupp.prod_mapDomain_index (by simp) (by intros; rw [pow_add])]
  rw [this]; ring

theorem hf_act_act {E : Type} [Field E] [NumberField E] {dim : (E →+* ℂ) → ℕ} (β : 𝓞 E) (M : ℂ)
    (h : ∀ τ : E →+* ℂ, τ (β : E) * (starRingEnd ℂ) (τ (β : E)) = M) (v w : I2.Vsp dim) :
    I2.Hf (I2.act β v) (I2.act β w) = M * I2.Hf v w := by
  unfold I2.Hf I2.act
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [map_mul]
  rw [← h i.1]; ring

theorem translate_eq_comp {E : Type} [Field E] [NumberField E] [IsCMField E] (X : I2.PT E) (α β : 𝓞 E) (M n : ℕ)
    (h : ∀ τ : E →+* ℂ, τ (β : E) * (starRingEnd ℂ) (τ (β : E)) = M)
    (h' : ∀ τ : E →+* ℂ, τ (α : E) * τ (β : E) = M) (s : (Fin 1 → I2.Vsp X.dim) → ℂ)
    (a v : Fin n → I2.Vsp X.dim) :
    X.U (M ^ 2) a (I2.s0 X ((M : ℂ) • LinearMap.id) s) v =
      X.U M (fun b => I2.act β (a b)) (I2.s0 X (vspActL α) s) (fun b => I2.act β (v b)) := by
  unfold I2.PT.U I2.HC I2.s0
  simp only [hf_act_act β M h, ← Finset.mul_sum]
  congr 1
  · congr 1; push_cast; ring
  · refine Finset.prod_congr rfl fun k _ => ?_
    congr 1
    funext _
    ext i
    simp [PullbackSections.vspActL, I2.act]
    rw [← h' i.1]; ring

def colMap {E : Type} [Field E] [NumberField E] [IsCMField E] {dim : (E →+* ℂ) → ℕ} (β : 𝓞 E) (n : ℕ) :
    (Fin n → I2.Vsp dim) →L[ℂ] (Fin n → I2.Vsp dim) :=
  LinearMap.toContinuousLinearMap (LinearMap.pi fun b => (vspActL β).comp (LinearMap.proj b))

theorem differentiable_translate {E : Type} [Field E] [NumberField E] (X : I2.PT E) (q n : ℕ)
    (p : I2.Vsp X.dim →ₗ[ℂ] I2.Vsp X.dim) (s : (Fin 1 → I2.Vsp X.dim) → ℂ) (hs : Differentiable ℂ s)
    (a : Fin n → I2.Vsp X.dim) : Differentiable ℂ (X.U q a (I2.s0 X p s)) := by
  have hp : Differentiable ℂ p := (LinearMap.toContinuousLinearMap p).differentiable
  have h1 : Differentiable ℂ (I2.s0 X (n := n) p s) := by
    unfold I2.s0
    have hk : ∀ k : Fin n, Differentiable ℂ fun v : Fin n → I2.Vsp X.dim => s fun _ => p (v k) := fun k =>
      hs.comp (differentiable_pi.2 fun _ => hp.comp (differentiable_apply k))
    exact fun v => (HasFDerivAt.finsetProd (u := Finset.univ) fun k _ => (hk k v).hasFDerivAt).differentiableAt
  have h2 : Differentiable ℂ fun v : Fin n → I2.Vsp X.dim => I2.HC v a := by
    unfold I2.HC I2.Hf
    refine Differentiable.fun_sum fun k _ => Differentiable.fun_sum fun i _ => Differentiable.mul_const ?_ _
    exact (EuclideanSpace.proj (𝕜 := ℂ) i).differentiable.comp (differentiable_apply k)
  unfold I2.PT.U
  exact (((h2.const_mul _).sub_const _).cexp).mul (h1.comp (differentiable_id.sub_const a))

theorem polyDeriv_levelSq_eq_alpha : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (X : I2.PT E) (α β : 𝓞 E) (M n : ℕ), (β : E) = IsCMField.complexConj E (α : E) → α * β = (M : 𝓞 E) → ∀ s : (Fin 1 → I2.Vsp X.dim) → ℂ, Differentiable ℂ s → ∀ (a : Fin n → I2.Vsp X.dim) (Io : Type) (P : MvPolynomial Io ℂ) (u : Io → Fin n → I2.Vsp X.dim) (sc : Io → ℂ) (κ : ℂ), (∀ ℓ b, I2.act β (u ℓ b) = sc ℓ • u ℓ b) → (∀ m ∈ P.support, (m.prod fun ℓ e => sc ℓ ^ e) = κ) → I2.polyDeriv P u (X.U (M ^ 2) a (I2.s0 X ((M : ℂ) • LinearMap.id) s)) 0 = κ * I2.polyDeriv P u (X.U M (fun b => I2.act β (a b)) (I2.s0 X (vspActL α) s)) 0 := by
  intro E _ _ _ X α β M n hβ hα s hs a Io P u sc κ hu hκ
  have hbar : ∀ τ : E →+* ℂ, τ (β : E) = (starRingEnd ℂ) (τ (α : E)) := fun τ => by
    rw [hβ, IsCMField.complexEmbedding_complexConj]
  have h' : ∀ τ : E →+* ℂ, τ (α : E) * τ (β : E) = M := by
    intro τ
    have := congrArg (fun a : 𝓞 E => τ (a : E)) hα
    simpa using this
  have h'' : ∀ τ : E →+* ℂ, τ (β : E) * (starRingEnd ℂ) (τ (β : E)) = M := by
    intro τ
    rw [← h' τ, hbar, Complex.conj_conj, mul_comm]
  have hfun : X.U (M ^ 2) a (I2.s0 X ((M : ℂ) • LinearMap.id) s) =
      (X.U M (fun b => I2.act β (a b)) (I2.s0 X (vspActL α) s)) ∘ colMap β n := by
    funext v
    rw [translate_eq_comp X α β M n h'' h']
    rfl
  rw [hfun]
  refine polyDeriv_comp_clm P u _ ?_ (colMap β n) sc (fun l => funext fun b => hu l b) κ hκ
  exact GlobalTheory.SCV.contDiff_of_differentiable (differentiable_translate X M n (vspActL α) s hs _) ⊤

end GlobalTheory.AlphaChain
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.SumLeFinsumOfSurjectsOntoFinset
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ThetaLower

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal GlobalTheory.BlockTh GlobalTheory.EtaAn
attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem norm_dmin {r : ℕ} (X : FD.Data E r) {x : FD.Frame X.Ψ r} (hx : X.IsOrtho x) (τ : X.Ψ) (i : Fin (r + 1)) :
    ‖FD.dmin X.Gm x τ i‖ = 1 := by
  unfold FD.dmin FD.lminor
  rw [hx τ, Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _), Matrix.det_diagonal, norm_prod]
  refine Finset.prod_eq_one fun a _ => ?_
  simp only [Function.comp, FD.sgn]
  split_ifs <;> simp

theorem finite_levQ {H : Host E} (Dw : Datum H) (l : Geo.Tor.Level H) : Finite (LevQ Dw l) := by
  have hne : l.Mb ≠ ⊥ := by
    intro h
    have hp := l.prod
    rw [h, Ideal.bot_mul, eq_comm, Ideal.span_singleton_eq_bot, Nat.cast_eq_zero] at hp
    have := l.three_le
    omega
  haveI : Finite (𝓞 E ⧸ l.Mb) := Ideal.finiteQuotientOfFreeOfNeBot _ hne
  haveI := Dw.fin
  exact Submodule.finite_quotient_smul l.Mb (N := (⊤ : Submodule (𝓞 E) Dw.La)) Module.Finite.fg_top

theorem exists_mult_le {H : Host E} (Dw : Datum H) (m : ℕ) (h : Dw.p ≤ m ∨ Dw.q ≤ m) : ∃ τ, Dw.mult τ ≤ m := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hsq : ∀ τ : E →+* ℂ, τ (H.rt : E) ^ 2 = H.rt0 ^ 2 := by
    intro τ
    rw [H.sqrt_neg_disc_sq, ← map_pow]
    have : (H.rt : E) ^ 2 = -(H.d : E) := by
      have := congrArg (fun z : 𝓞 E => (z : E)) H.rt_sq
      simpa using this
    rw [this]; simp
  have h0 : H.rt0 ≠ 0 := by
    intro h0
    have := H.sqrt_neg_disc_sq
    rw [h0] at this
    have hd := H.d_prime.pos
    have : (H.d : ℂ) = 0 := by simpa using this
    exact hd.ne' (by exact_mod_cast this)
  have hconj : starRingEnd ℂ H.rt0 = -H.rt0 := by
    have h1 : H.rt0 ^ 2 = -(H.d : ℂ) := H.sqrt_neg_disc_sq
    have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
    have hre := congrArg Complex.re h1
    have him := congrArg Complex.im h1
    simp [pow_two] at hre him
    have : H.rt0.re = 0 := by
      by_contra hne
      have : H.rt0.im = 0 := by
        have : H.rt0.re * H.rt0.im = 0 := by linarith
        exact (mul_eq_zero.1 this).resolve_left hne
      rw [this] at hre
      nlinarith [mul_self_nonneg H.rt0.re]
    apply Complex.ext <;> simp [this]
  have hne : -H.rt0 ≠ H.rt0 := fun h => h0 (by linear_combination -h / 2)
  have key : ∃ τ₁ τ₂ : E →+* ℂ, τ₁ (H.rt : E) = H.rt0 ∧ τ₂ (H.rt : E) = -H.rt0 := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 (hsq τ) with h | h
    · exact ⟨τ, (starRingEnd ℂ).comp τ, h, by simp [h, hconj]⟩
    · exact ⟨(starRingEnd ℂ).comp τ, τ, by simp [h, hconj], h⟩
  obtain ⟨τ₁, τ₂, h₁, h₂⟩ := key
  rcases h with h | h
  · exact ⟨τ₁, by rwa [Datum.mult, if_pos h₁]⟩
  · exact ⟨τ₂, by rwa [Datum.mult, if_neg (by rw [h₂]; exact hne)]⟩

theorem normSq_emb_bar {H : Host E} (α : 𝓞 E) (M : ℕ) (hα : α * H.bar α = (M : 𝓞 E)) (τ : E →+* ℂ) :
    ‖τ ((H.bar α : 𝓞 E) : E)‖ ^ 2 = M := by
  have h1 : τ ((H.bar α : 𝓞 E) : E) = starRingEnd ℂ (τ (α : E)) := by
    rw [H.bar_eq]; exact IsCMField.complexEmbedding_complexConj E τ _
  have h2 : τ (α : E) * τ ((H.bar α : 𝓞 E) : E) = M := by
    rw [← map_mul]
    have := congrArg (fun z : 𝓞 E => (z : E)) hα
    simp only [map_mul, map_natCast] at this
    erw [this]; simp
  rw [h1] at h2 ⊢
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq] at h2
  rw [RCLike.norm_conj]
  exact_mod_cast h2

theorem exists_kappa {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (c : Coeff l) (σ : c.F →+* ℂ)
    {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {P : MvPolynomial (LtN Dw n) c.F} (hP : P ∈ harmA c a n) (h0 : P ≠ 0)
    (hh : P.IsHomogeneous P.totalDegree) (s : (E →+* ℂ) → ℂ) (M : ℝ) (hs : ∀ τ, ‖s τ‖ ^ 2 = M) :
    ∃ κ : ℂ, ‖κ‖ ^ 2 = M ^ P.totalDegree ∧
      ∀ m ∈ (MvPolynomial.map σ P).support, (m.prod fun ℓ e => s ℓ.1 ^ e) = κ := by
  have key : ∀ m ∈ P.support, (m.prod fun ℓ e => s ℓ.1 ^ e) = ∏ τ, ∏ i : Fin (Dw.mult τ), s τ ^ a (τ, i) := by
    intro m hm
    rw [Finsupp.prod_fintype _ _ (by simp), Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun i _ => ?_
    dsimp only
    rw [Finset.prod_pow_eq_pow_sum]
    exact congrArg _ (hP.1.2.2 m hm τ i)
  obtain ⟨m, hm⟩ := Finset.nonempty_iff_ne_empty.2 (mt MvPolynomial.support_eq_empty.1 h0)
  refine ⟨_, ?_, fun m' hm' => key m' (MvPolynomial.support_map_subset _ _ hm')⟩
  rw [← key m hm]
  have hd : ∑ ℓ ∈ m.support, m ℓ = P.totalDegree := by
    have := hh (MvPolynomial.mem_support_iff.1 hm)
    rw [← this]
    simp [Finsupp.weight_apply, Finsupp.sum]
  rw [← hd, Finsupp.prod, norm_prod, ← Finset.prod_pow, ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_congr rfl fun ℓ _ => ?_
  rw [norm_pow, ← pow_mul, mul_comm, pow_mul, hs]

theorem sum_le_finsum {A B : Type} [Finite B] (K : Finset A) (φ : B → A) (u : A → ℝ) (v : B → ℝ)
    (hK : ∀ a ∈ K, ∃ b, a = φ b) (huv : ∀ b, v b = u (φ b)) (hv : ∀ b, 0 ≤ v b) :
    ∑ a ∈ K, u a ≤ ∑ᶠ b, v b := by
  classical
  haveI := Fintype.ofFinite B
  rw [finsum_eq_sum_of_fintype]
  choose ψ hψ using fun a : K => hK a.1 a.2
  have hinj : Function.Injective ψ := fun a a' h => Subtype.ext (by rw [hψ a, hψ a', h])
  calc ∑ a ∈ K, u a = ∑ a : K, v (ψ a) := by
        rw [← Finset.sum_coe_sort K]
        exact Finset.sum_congr rfl fun a _ => by rw [huv, ← hψ]
    _ = ∑ b ∈ Finset.univ.image ψ, v b := (Finset.sum_image fun a _ a' _ h => hinj h).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun b _ _ => hv b

theorem differentiable_translate (X : I2.PT E) (q n : ℕ) (π : I2.Vsp X.dim →ₗ[ℂ] I2.Vsp X.dim)
    (s : (Fin 1 → I2.Vsp X.dim) → ℂ) (hs : Differentiable ℂ s) (b : Fin n → I2.Vsp X.dim) :
    Differentiable ℂ (X.U q b (I2.s0 X π s)) := by
  have hπ : Differentiable ℂ π := (LinearMap.toContinuousLinearMap π).differentiable
  have h0 : Differentiable ℂ (I2.s0 (n := n) X π s) := by
    unfold I2.s0
    have hk : ∀ k : Fin n, Differentiable ℂ fun v : Fin n → I2.Vsp X.dim => s fun _ => π (v k) := fun k =>
      hs.comp (differentiable_pi.2 fun _ => hπ.comp (differentiable_apply k))
    exact fun v => (HasFDerivAt.finsetProd fun k _ => (hk k v).hasFDerivAt).differentiableAt
  have h1 : Differentiable ℂ fun v : Fin n → I2.Vsp X.dim => I2.HC v b := by
    unfold I2.HC I2.Hf
    fun_prop
  unfold I2.PT.U
  exact (((h1.const_mul _).sub_const _).cexp).mul (h0.comp (differentiable_id.sub_const b))

theorem theta_law {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l}
    {σ : c.F →+* ℂ} {r : ℕ} {U : Unf Xo c σ r} (hU : IsUnf U) {k : U.Comp} {x : (U.X k).dom} (W : UnfAt U k x)
    (Wu : UnitAt W) (hu : ∀ τ' i', ‖FD.dmin (U.X k).Gm x.1 τ' i'‖ = 1) :
    Differentiable ℂ Wu.θ ∧ ∀ a z, Wu.θ (z + W.Pm a) =
      (((Int.negOnePow ((W.F.Di (W.ik k)).EF a (H.w0 • a)) : ℤˣ) : ℤ) : ℂ) *
        Complex.exp (Real.pi * hermForm Wu.Hm z (W.Pm a) + Real.pi / 2 * hermForm Wu.Hm (W.Pm a) (W.Pm a)) *
          Wu.θ z := by
  have hF : AHFrame W.F (W.ik k) W.Pm Wu.Hm Wu.χl Wu.fr :=
    ⟨Wu.herm, Wu.pos, Wu.c1, Wu.c2, Wu.c3, Wu.c4, fun j hj => by
      rw [← W.pt]; exact Wu.c5 j hj, Wu.c6⟩
  have gen : ∀ (y : Sp ℂ ⟶ Xo.X) (_ : y = W.F.u (W.ik k) W.Pm) (s : LB.Sec (PPx y)),
      IsFnOf W.F (W.ik k) W.Pm Wu.fr y s Wu.θ → Differentiable ℂ Wu.θ ∧ ∀ a z, Wu.θ (z + W.Pm a) =
        Wu.χl (W.Pm a) * Complex.exp (Real.pi * hermForm Wu.Hm z (W.Pm a) +
          Real.pi / 2 * hermForm Wu.Hm (W.Pm a) (W.Pm a)) * Wu.θ z := by
    rintro y rfl s hs
    exact isFnOf_entire_factor E H Dw l Xo _ _ _ W.F (W.ik k) W.Pm Wu.Hm Wu.χl Wu.fr W.per hF s Wu.θ hs
  obtain ⟨h1, h2⟩ := gen (U.un k x).x W.pt (U.un k x).s Wu.c7
  refine ⟨h1, fun a z => ?_⟩
  rw [h2, GlobalTheory.semichar_unit_frame Xo c σ r U hU k x W Wu hu a, Int.cast_negOnePow]


open Classical in
theorem value_torus {H : Host E} {Dw : Datum H} (T : I2.PT E) {g n : ℕ} (e : Fin g ≃ Lt1 Dw)
    (ψ : (Fin g → ℂ) ≃ₗ[ℂ] I2.Vsp T.dim) (Hm : Matrix (Fin g) (Fin g) ℂ) (θ : (Fin g → ℂ) → ℂ)
    (hH : ∀ z w, I2.Hf (ψ z) (ψ w) = hermForm Hm z w) (hθ : Differentiable ℂ θ)
    (rl : (E →+* ℂ) → (E →+* ℂ)) (hd : ∀ τ, Dw.mult τ ≤ T.dim (rl τ)) (t : ℂ)
    (hrow : ∀ j, ∃ h : ((e j).2 : ℕ) < T.dim (rl (e j).1), ψ (Pi.single j 1) =
      t • EuclideanSpace.single (⟨rl (e j).1, ⟨(e j).2, h⟩⟩ : I2.Idx T.dim) (1 : ℂ))
    (α : 𝓞 E) (M : ℕ) (hα : α * H.bar α = (M : 𝓞 E)) (Q : MvPolynomial (LtN Dw n) ℂ) (κ : ℂ)
    (hκ : ∀ m ∈ Q.support, (m.prod fun ℓ k => rl ℓ.1 ((H.bar α : 𝓞 E) : E) ^ k) = κ)
    (a : Fin n → Fin g → ℂ) :
    I2.polyDeriv Q (letDir e) (fun z => ∏ b, fock Hm ((M : ℤ) ^ 2) (a b) (fun w => θ ((M : ℂ) • w)) (z b)) 0 =
      κ * I2.polyDeriv Q (fun ℓ => t • I2.dir ((ℓ.2.2, ⟨rl ℓ.1, Fin.castLE (hd ℓ.1) ℓ.2.1⟩) : I2.Letter n T.dim))
        (T.U M (fun b => I2.act (H.bar α) (-ψ (a b))) (I2.s0 T (vspActL α) fun v => θ (ψ.symm (v 0)))) 0 := by
  have hdir : (fun (ℓ : LtN Dw n) b => ψ (letDir e ℓ b)) = fun ℓ => t •
      I2.dir ((ℓ.2.2, ⟨rl ℓ.1, Fin.castLE (hd ℓ.1) ℓ.2.1⟩) : I2.Letter n T.dim) := by
    have h1 : ∀ y : Lt1 Dw, ψ (Pi.single (e.symm y) 1) = t •
        EuclideanSpace.single (⟨rl y.1, Fin.castLE (hd y.1) y.2⟩ : I2.Idx T.dim) (1 : ℂ) := by
      intro y
      obtain ⟨j, rfl⟩ := e.surjective y
      obtain ⟨h, hh⟩ := hrow j
      rw [e.symm_apply_apply]
      exact hh
    funext ℓ b
    by_cases hb : b = ℓ.2.2
    · subst hb
      simp only [letDir, I2.dir, Pi.smul_apply, Pi.single_eq_same]
      exact h1 ⟨ℓ.1, ℓ.2.1⟩
    · simp [letDir, I2.dir, hb]
  have hs : Differentiable ℂ fun v : Fin 1 → I2.Vsp T.dim => θ (ψ.symm (v 0)) :=
    hθ.comp ((LinearMap.toContinuousLinearMap ψ.symm.toLinearMap).differentiable.comp (differentiable_apply 0))
  rw [polyDeriv_prod_fock_eq_translate E T g ψ Hm θ hH hθ, hdir]
  refine GlobalTheory.AlphaChain.polyDeriv_levelSq_eq_alpha E T α (H.bar α) M n (H.bar_eq α) hα _ hs _ _ _ _
      (fun ℓ => rl ℓ.1 ((H.bar α : 𝓞 E) : E)) κ ?_ hκ
  intro ℓ b
  ext i
  by_cases hb : b = ℓ.2.2
  · subst hb
    by_cases hi : i = ⟨rl ℓ.1, Fin.castLE (hd ℓ.1) ℓ.2.1⟩
    · subst hi
      simp [I2.act, I2.dir]
    · simp [I2.act, I2.dir, hi]
  · simp [I2.act, I2.dir, hb]

theorem norm_sq_value (v κ D : ℂ) (M d : ℕ) (t : ℝ) (hM : (0 : ℝ) < M) (ht : 0 ≤ t) (hκ : ‖κ‖ ^ 2 = (M : ℝ) ^ d)
    (hv : v = ((M : ℂ)⁻¹) ^ d * (κ * (((Real.sqrt t : ℝ) : ℂ) ^ d * D))) : ‖v‖ ^ 2 = (t / M) ^ d * ‖D‖ ^ 2 := by
  rw [hv, norm_mul, norm_mul, norm_mul, mul_pow, mul_pow, mul_pow, hκ, norm_pow, norm_pow, norm_inv,
    Complex.norm_natCast, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), ← pow_mul, ← pow_mul,
    mul_comm d 2, pow_mul, pow_mul, Real.sq_sqrt ht, ← _root_.mul_assoc, ← _root_.mul_assoc, ← mul_pow, ← mul_pow]
  congr 2
  field_simp

theorem thetaRule_sum_lower : ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r) (k : U.Comp) (x : (U.X k).dom) (xR : ℝ) (nab : NabV Xo c), IsNab Xo c nab → GoodEmb c σ → IsUnf U → FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (U.un k x) → (U.X k).IsOrtho x.1 → (∀ τ : E →+* ℂ, ‖τ (U.X k).ξ0‖ = xR) → ∀ α : 𝓞 E, α * H.bar α = (l.M : 𝓞 E) → l.Mb = Ideal.span {H.bar α} → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (P₁ : MvPolynomial (LtN Dw n) c.F), P₁ ∈ harmA c a n → GlobalTheory.BlockTh.IsBlockProd P₁ → ∀ (R0 : ℝ) (m : ℕ), RunOK E r P₁.totalDegree l.M R0 m → (Dw.p ≤ m ∨ Dw.q ≤ m) → ∃ (T : I2.PT E) (Pr : I2.Par T P₁.totalDegree), T.r = r ∧ Pr.q = l.M ∧ Pr.m = m ∧ Pr.ph = I2.phiFD (U.X k) (I2.th (E := E) l.M R0) x.1 ∧ ∀ f : (Fin n → LevQ Dw l) → Rul Xo c, (∀ q, IsThRule Xo c nab (fun b => levRep (q b)) P₁ (f q)) → (2 * xR / l.M) ^ P₁.totalDegree * Pr.Jbound n ≤ ∑ᶠ q, ‖toC (evR Xo c (f q) (U.un k x))‖ ^ 2 := by
  intro hCI E _ _ _ H Dw l Xo c _ σ r U k x xR nab hnab hσ hU hft hx hxR α hα hMb a n P₁ hP hB R0 m hrun hm
  classical
  obtain ⟨W⟩ := nonempty_unfAt hU k x
  have hu := norm_dmin (U.X k) hx
  obtain ⟨Wu⟩ := nonempty_unitAt W hu
  have hM0 : (0 : ℝ) < l.M := by have := l.three_le; exact_mod_cast (by omega : 0 < l.M)
  have hxR0 : 0 < xR := by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    rw [← hxR τ]
    exact norm_pos_iff.2 ((map_ne_zero τ).2 (U.X k).ξ0_ne)
  have hHm : Wu.Hm = Matrix.diagonal fun _ => ((2 * xR : ℝ) : ℂ) := by
    rw [GlobalTheory.HermDiag.hm_eq_diagonal E H Dw l Xo c σ r U k x W Wu hσ hU hx]
    simp only [hxR]
  obtain ⟨hbij, hmul, hty⟩ := relab_isTypeFn E H Dw l Xo c σ hσ
  change Function.Bijective (relab c σ) at hbij
  change ∀ τ, Dw.mult (relab c σ τ) = Dw.mult τ at hmul
  have hty' : IsTypeFn H (W.F.Di (W.ik k)).p (W.F.Di (W.ik k)).q (fun j => relab c σ (W.e j).1) := by
    rw [(W.F.sig _).1, (W.F.sig _).2]; exact hty W.g W.e
  have hDm : ∀ τ, (W.F.Di (W.ik k)).mult τ = Dw.mult τ := fun τ => by
    simp only [Datum.mult, (W.F.sig _).1, (W.F.sig _).2]
  obtain ⟨T, ψ, hT, hrow⟩ := GlobalTheory.ScalarTorus.exists_torusOf_rows E H (W.F.Di (W.ik k)) W.g
    (fun j => relab c σ (W.e j).1) W.Pm (2 * xR) (fun j => (W.e j).2.1) (by positivity) hty' W.per
    (fun a b => by rw [← hHm]; exact Wu.c1 a b)
    (fun j => by rw [hDm, hmul]; exact (W.e j).2.2)
    (fun j j' h h' => by
      apply W.e.injective
      have h1 := hbij.1 h
      generalize W.e j = y at h1 h'
      generalize W.e j' = y' at h1 h'
      obtain ⟨τ, i⟩ := y
      obtain ⟨τ', i'⟩ := y'
      dsimp only at h1 h'
      subst h1
      rw [Fin.ext h'])
  rw [← hHm] at hT
  obtain ⟨-, hTr, hTph⟩ := GlobalTheory.OrthoPeriodTorus.isTorusAt_of_isTorusOf E H Dw l Xo c σ r U k x W Wu T ψ hσ hU hx hT
  have hdim : ∀ τ, T.dim τ = Dw.mult τ := fun τ => (hT.2.1 τ).trans (hDm τ)
  have hd : ∀ τ, Dw.mult τ ≤ T.dim (relab c σ τ) := fun τ => by rw [hdim, hmul]
  obtain ⟨hP0, hhom, nb, bs, hdisj, hDF, hren⟩ := GlobalTheory.BlockRen.blockProd_rename E H Dw n c.F σ P₁ hB T.dim
    (relab c σ) hd hbij.1
  obtain ⟨hθ, hlaw⟩ := theta_law hU W Wu hu
  obtain ⟨hsec, hl2, -⟩ := ThetaTorus.theta_section_l2_torus E H _ _ _ W.Pm Wu.Hm T ψ Wu.θ Wu.Fd hT hθ hlaw Wu.c8
  rw [Wu.c9] at hl2
  set s : (Fin 1 → I2.Vsp T.dim) → ℂ := fun v => Wu.θ (ψ.symm (v 0)) with hs
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hl2
    simp [I2.PT.l2, I2.PT.ptN2] at hl2
  have hπ := IsPiAct.isPi_actL_of_isTorusOf E H _ _ _ W.Pm Wu.Hm T ψ W.per hT α l.M hα
  choose x2 hx2a hx2b using fun q : LevQ Dw l => Pf.rep_level Dw l (levRep q)
  obtain ⟨hmi, hms⟩ := marking_iso_mod E H Dw l Xo c _ _ _ W.F (W.ik k)
  let mk : Dw.La →+ I2.Vsp T.dim :=
    (ψ.toLinearMap.toAddMonoidHom.comp W.Pm).comp (W.F.t (W.ik k)).toAddMonoidHom
  have hmk : ∀ a, mk a = ψ (W.Pm (W.F.t (W.ik k) a)) := fun _ => rfl
  have hnat : ∀ b, ψ (W.Pm (l.M • b)) = (l.M : ℂ) • ψ (W.Pm b) := fun b => by
    rw [map_nsmul, map_nsmul, Nat.cast_smul_eq_nsmul]
  obtain ⟨K, hK, hKq⟩ := GlobalTheory.isReps_level_translates E H Dw l T mk α hα hMb
    (fun a => (hT.2.2.2.1 _).2 ⟨_, rfl⟩)
    (fun β a => by
      rw [hmk, hmk, map_smul, ← hT.2.2.2.2.1]
      exact congrArg ψ (funext fun j => W.per.1 β _ j))
    (fun a ⟨v, hv, h⟩ => by
      obtain ⟨b, rfl⟩ := (hT.2.2.2.1 v).1 hv
      rw [hmk, ← hnat] at h
      exact hmi a ⟨b, W.per.2.1 (ψ.injective h)⟩)
    (fun v hv => by
      obtain ⟨b, rfl⟩ := (hT.2.2.2.1 v).1 hv
      obtain ⟨a, e, rfl⟩ := hms b
      exact ⟨a, ψ (W.Pm e), (hT.2.2.2.1 _).2 ⟨_, rfl⟩, by rw [map_add (f := _), map_add (f := _), hnat, hmk]⟩)
    x2 hx2a hx2b n
  obtain ⟨κ, hκ, hκm⟩ := exists_kappa c σ hP hP0 hhom (fun τ => relab c σ τ ((H.bar α : 𝓞 E) : E)) l.M
    (fun τ => normSq_emb_bar α l.M hα _)
  obtain ⟨τ0, hτ0⟩ := exists_mult_le Dw m hm
  obtain ⟨Pr, hq, hR, hm'⟩ := hrun T hTr ⟨τ0, by rwa [hdim]⟩
  refine ⟨T, Pr, hTr, hq, hm', by rw [I2.Par.ph, hq, hR, hTph], fun f hf => ?_⟩
  have hI : Pr.Jbound n ≤ ∑ b ∈ K, ‖I2.polyDeriv (I2.P1 bs) I2.dir (T.U l.M b (I2.s0 T (vspActL α) s)) 0‖ ^ 2 := by
    have gen : ∀ (d : ℕ) (_ : I2.DF bs = d) (Pr : I2.Par T d), Pr.q = l.M →
        Pr.Jbound n ≤ ∑ b ∈ K, ‖I2.polyDeriv (I2.P1 bs) I2.dir (T.U l.M b (I2.s0 T (vspActL α) s)) 0‖ ^ 2 := by
      rintro d rfl Pr hq
      have := GlobalTheory.ThetaTorus.I_holds E T n nb bs hdisj Pr (vspActL α) (hq ▸ hπ) s hsec hs0 K (hq ▸ hK)
      rwa [hl2, one_pow, _root_.mul_one, hq] at this
    exact gen _ hDF Pr hq
  haveI := finite_levQ Dw l
  refine le_trans (mul_le_mul_of_nonneg_left hI (pow_nonneg (div_nonneg (by positivity) hM0.le) _)) ?_
  rw [Finset.mul_sum]
  refine sum_le_finsum K (fun q i => I2.act (H.bar α) (-(((l.M : ℂ) ^ 2)⁻¹ • mk (x2 (q i)))))
    (fun b => (2 * xR / l.M) ^ P₁.totalDegree *
      ‖I2.polyDeriv (I2.P1 bs) I2.dir (T.U l.M b (I2.s0 T (vspActL α) s)) 0‖ ^ 2)
    (fun q => ‖toC (evR Xo c (f q) (U.un k x))‖ ^ 2) hKq
    (fun q => ?_) fun _ => sq_nonneg _
  have hv := (GlobalTheory.AnVal.thetaRule_value_periods hCI E H Dw l Xo c σ r U k x W Wu nab hnab hft n (fun b => levRep (q b))
    (fun b => x2 (q b)) (fun b => hx2a _) (fun b => hx2b _) a P₁ hP (f q) (hf q)).2
  have hw := value_torus T W.e ψ Wu.Hm Wu.θ hT.2.2.1 hθ (relab c σ) hd _ hrow α l.M hα _ κ hκm
    (fun b => ((l.M : ℂ) ^ 2)⁻¹ • W.Pm (W.F.t (W.ik k) (x2 (q b))))
  rw [hren _ _ (differentiable_translate T _ _ _ _ hsec.1 _)] at hw
  simp only [map_smul] at hw
  exact norm_sq_value _ κ _ l.M _ (2 * xR) hM0 (by positivity) hκ (hv.trans (congrArg _ hw))

end GlobalTheory.ThetaLower
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.SumLeFinsumOfSurjectsOntoFinsetStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal GlobalTheory.BlockTh GlobalTheory.EtaAn
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unfoldedThetaRule_archimedeanValue_bound : ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r) (k : U.Comp) (x : (U.X k).dom) (xR : ℝ) (nab : NabV Xo c), IsNab Xo c nab → GoodEmb c σ → IsUnf U → FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (U.un k x) → (U.X k).IsOrtho x.1 → (∀ τ : E →+* ℂ, ‖τ (U.X k).ξ0‖ = xR) → ∀ α : 𝓞 E, α * H.bar α = (l.M : 𝓞 E) → l.Mb = Ideal.span {H.bar α} → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (P₁ : MvPolynomial (LtN Dw n) c.F), P₁ ∈ harmA c a n → GlobalTheory.BlockTh.IsBlockProd P₁ → ∀ (R0 : ℝ) (m : ℕ), RunOK E r P₁.totalDegree l.M R0 m → (Dw.p ≤ m ∨ Dw.q ≤ m) → ∃ (T : I2.PT E) (Pr : I2.Par T P₁.totalDegree), T.r = r ∧ Pr.q = l.M ∧ Pr.m = m ∧ Pr.ph = I2.phiFD (U.X k) (I2.th (E := E) l.M R0) x.1 ∧ ∀ f : (Fin n → LevQ Dw l) → Rul Xo c, (∀ q, IsThRule Xo c nab (fun b => levRep (q b)) P₁ (f q)) → (2 * xR / l.M) ^ P₁.totalDegree * Pr.Jbound n ≤ ∑ᶠ q, ‖toC (evR Xo c (f q) (U.un k x))‖ ^ 2 := by
  first | exact @GlobalTheory.ThetaLower.thetaRule_sum_lower | exact GlobalTheory.ThetaLower.thetaRule_sum_lower | (intros; apply GlobalTheory.ThetaLower.thetaRule_sum_lower <;> assumption)
end
