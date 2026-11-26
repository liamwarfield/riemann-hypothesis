module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PGenericProjClosureDivisor
public import Development.WeilBound.CoreStatements.HodgeTatePoints.GdChartFin
public import Development.WeilBound.CoreStatements.HodgeTatePoints.CntCoord
public import Development.WeilBound.CoreStatements.HodgeTatePoints.HasLenOfEquiv

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.HodgeTatePoints.HcptgenRing
noncomputable section

namespace PositivityTheory.HtPt.Hcptgen

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

theorem aeval_scale {σ K R A : Type} [Fintype K] [CommRing R] [CommRing A] [Algebra R A] (w : σ → K → ℕ)
    (c : K → A) (z : σ → A) {f : MvPolynomial σ R} {d : K → ℕ} (hf : IsWeightedHomogeneous w f d) :
    aeval (fun p => (∏ k, c k ^ w p k) * z p) f = (∏ k, c k ^ d k) * aeval z f := by
  induction hf using IsWeightedHomogeneous.induction_on with
  | zero => simp
  | add p q _ _ hp hq => rw [map_add (f := _), map_add (f := _), hp, hq, mul_add]
  | monomial m r hm =>
    rw [aeval_monomial, aeval_monomial, ← hm]
    have e : (∏ k, c k ^ (Finsupp.weight w m) k) = m.prod fun p n => (∏ k, c k ^ w p k) ^ n := by
      rw [Finsupp.weight_apply, Finsupp.sum, Finsupp.prod]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_pow,
        ← pow_mul, mul_comm]
      exact Finset.prod_comm
    rw [e]
    simp only [mul_pow, Finsupp.prod_mul]
    ring

variable {o : Type} [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω] {K : Type} [Fintype K] {J : K → Type}

theorem ratio_eq [DecidableEq K] (y : (Σ k, J k) → Ω) (s : ∀ k, J k) (hs : mseg y s ≠ 0) (k : K) (i : J k) :
    y ⟨k, i⟩ / y ⟨k, s k⟩ = mseg y (Function.update s k i) / mseg y s := by
  have hk : y ⟨k, s k⟩ ≠ 0 := Finset.prod_ne_zero_iff.1 hs k (Finset.mem_univ k)
  rw [div_eq_div_iff hk hs]
  unfold mseg
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ k), ← Finset.mul_prod_erase _ _ (Finset.mem_univ k),
    Function.update_self]
  have e : ∏ j ∈ Finset.univ.erase k, y ⟨j, Function.update s k i j⟩ = ∏ j ∈ Finset.univ.erase k, y ⟨j, s j⟩ :=
    Finset.prod_congr rfl fun j hj => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  rw [e]
  ring


open GroundTheory.Heights₂.Heights.NumbersDVR in
theorem chartRing_mseg (y : (Σ k, J k) → Ω) (s : ∀ k, J k) (hs : mseg y s ≠ 0) :
    chartRing o (mseg y) s = Algebra.adjoin o (Set.range fun j => mseg y j / mseg y s) := by
  classical
  refine le_antisymm (fun u hu => ?_) (Algebra.adjoin_le ?_)
  · have hk : ∀ k, y ⟨k, s k⟩ ≠ 0 := fun k => Finset.prod_ne_zero_iff.1 hs k (Finset.mem_univ k)
    obtain ⟨n, U, hU, hv⟩ := GenericProjClosureDivisor.chart_form (O := o) (Φ := Ω) y (Pi.basisFun Ω (Fin 0))
      (Fin.elim0 : Fin 0 → _) (Fin.elim0 : Fin 0 → _) Fin.elim0 s hs hu
    let c : Option (Option K) → Ω := fun b => b.elim 1 fun b' => b'.elim 1 fun k => y ⟨k, s k⟩
    let z : (Σ b, bundleIdx (bundleIdx J 0) 0 b) → Ω := fun p =>
      pairProjCoord y (Pi.basisFun Ω (Fin 0)) (Fin.elim0 : Fin 0 → _) (Fin.elim0 : Fin 0 → _) Fin.elim0 p / c p.1
    have hc : ∀ b, c b ≠ 0 := by
      rintro (_ | _ | k)
      · exact one_ne_zero
      · exact one_ne_zero
      · exact hk k
    have h := aeval_scale _ c z hU
    have e1 : (fun p => (∏ b, c b ^ blockWeight (bundleIdx (bundleIdx J 0) 0) p b) * z p) =
        pairProjCoord y (Pi.basisFun Ω (Fin 0)) (Fin.elim0 : Fin 0 → _) (Fin.elim0 : Fin 0 → _) Fin.elim0 := by
      funext p
      have : ∏ b, c b ^ blockWeight (bundleIdx (bundleIdx J 0) 0) p b = c p.1 := by
        rw [Finset.prod_eq_single p.1]
        · simp [blockWeight]
        · intro b _ hb
          simp [blockWeight, Pi.single_eq_of_ne hb]
        · simp
      rw [this]
      exact mul_div_cancel₀ _ (hc _)
    have e2 : ∏ b, c b ^ GenericProjClosureDivisor.vdeg (fun _ : K => n) b = segreVec y s ^ n := by
      simp [Fintype.prod_option, c, GenericProjClosureDivisor.vdeg, segreVec, Finset.prod_pow]
    rw [e1, e2, hv, Algebra.algebraMap_self_apply, mul_comm] at h
    have hu' : u = aeval z U := mul_left_cancel₀ (pow_ne_zero n hs) h
    have hz : aeval z U ∈ Algebra.adjoin o (Set.range z) := by
      rw [Algebra.adjoin_range_eq_range_aeval]
      exact ⟨U, rfl⟩
    rw [hu']
    refine Algebra.adjoin_mono ?_ hz
    rintro _ ⟨⟨_ | _ | k, i⟩, rfl⟩
    · exact Fin.elim0 i
    · exact Fin.elim0 i
    · exact ⟨Function.update s k i, (ratio_eq y s hs k i).symm⟩
  · rintro _ ⟨j, rfl⟩
    exact div_mem_chartRing _ _ _

end PositivityTheory.HtPt.Hcptgen
end
end

section -- merged from Development.WeilBound.CoreStatements.HodgeTatePoints.ReTens
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace PositivityTheory.HtPt.Re

theorem tens_hopf : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (N₁ : Type) [AddCommGroup N₁] [Fintype N₁] [DecidableEq N₁], ∀ (N₂ : Type) [AddCommGroup N₂] [Fintype N₂] [DecidableEq N₂], ∀ (A₁ : HopfOrder (C := C) R N₁) (A₂ : HopfOrder (C := C) R N₂), ∃ AA : HopfOrder (C := C) R (N₁ × N₂), AA.carrier = tens A₁.carrier A₂.carrier ∧ AA.carrier.map (LinearMap.funLeft R C (AddMonoidHom.inl N₁ N₂ : N₁ → N₁ × N₂)) = A₁.carrier ∧ AA.carrier.map (LinearMap.funLeft R C (AddMonoidHom.inr N₁ N₂ : N₂ → N₁ × N₂)) = A₂.carrier ∧ (∀ g ∈ AA.carrier, (fun z : N₁ × N₂ => g (z.1, 0)) ∈ AA.carrier) ∧ (∀ g ∈ AA.carrier, (fun z : N₁ × N₂ => g (0, z.2)) ∈ AA.carrier) ∧ ∀ c₁ c₂, HasColen R v A₁.carrier c₁ → HasColen R v A₂.carrier c₂ → HasColen R v AA.carrier (c₁ ^ Fintype.card N₂ * c₂ ^ Fintype.card N₁) := by
  intro p _ C _ _ _ v R _ _ _ _ N₁ _ _ _ N₂ _ _ _ A₁ A₂
  refine ⟨PositivityTheory.HtPt.Re.hopfProd A₁ A₂, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [PositivityTheory.HtPt.Re.hopfProd_carrier]; rfl
  · rw [PositivityTheory.HtPt.Re.hopfProd_carrier]; exact PositivityTheory.HtPt.Re.tn_inl A₁ A₂
  · rw [PositivityTheory.HtPt.Re.hopfProd_carrier]; exact PositivityTheory.HtPt.Re.tn_inr A₁ A₂
  · rw [PositivityTheory.HtPt.Re.hopfProd_carrier]; exact PositivityTheory.HtPt.Re.tn_stab₁ A₁ A₂
  · rw [PositivityTheory.HtPt.Re.hopfProd_carrier]; exact PositivityTheory.HtPt.Re.tn_stab₂ A₁ A₂
  · intro c₁ c₂ h₁ h₂
    rw [PositivityTheory.HtPt.Re.hopfProd_carrier]
    exact PositivityTheory.HtPt.Re.hasColen_tn h₁ h₂

end PositivityTheory.HtPt.Re
end

section -- merged from Development.WeilBound.CoreStatements.HodgeTatePoints.EqOfPowMul
noncomputable section

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace PositivityTheory.HtPt.Re

def splitEquiv {N N₁ N₂ : Type} [AddCommGroup N] [AddCommGroup N₁] [AddCommGroup N₂]
    (ι₁ : N₁ →+ N) (π₁ : N →+ N₁) (ι₂ : N₂ →+ N) (π₂ : N →+ N₂) (h11 : ∀ y, π₁ (ι₁ y) = y)
    (h22 : ∀ y, π₂ (ι₂ y) = y) (hsum : ∀ x, ι₁ (π₁ x) + ι₂ (π₂ x) = x) (h12 : ∀ y, π₁ (ι₂ y) = 0)
    (h21 : ∀ y, π₂ (ι₁ y) = 0) : N₁ × N₂ ≃+ N where
  toFun z := ι₁ z.1 + ι₂ z.2
  invFun x := (π₁ x, π₂ x)
  left_inv z := by simp [h11, h22, h12, h21]
  right_inv x := hsum x
  map_add' a b := by simp only [Prod.fst_add, Prod.snd_add, map_add (f := _)]; abel

theorem ret_colen {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R]
    [Algebra R C] {N : Type} [AddCommGroup N] [Fintype N] [DecidableEq N]
    (AA : HopfOrder (C := C) R N) {N₁ : Type} [AddCommGroup N₁] [Fintype N₁] [DecidableEq N₁]
    {N₂ : Type} [AddCommGroup N₂] [Fintype N₂] [DecidableEq N₂]
    (ι₁ : N₁ →+ N) (π₁ : N →+ N₁) (ι₂ : N₂ →+ N) (π₂ : N →+ N₂) (h11 : ∀ y, π₁ (ι₁ y) = y)
    (h22 : ∀ y, π₂ (ι₂ y) = y) (hsum : ∀ x, ι₁ (π₁ x) + ι₂ (π₂ x) = x) (h12 : ∀ y, π₁ (ι₂ y) = 0)
    (h21 : ∀ y, π₂ (ι₁ y) = 0) (hs₁ : ∀ g ∈ AA.carrier, (fun x => g (ι₁ (π₁ x))) ∈ AA.carrier)
    (a b : NNReal)
    (ha : HasColen R v (AA.carrier.map (LinearMap.funLeft R C (ι₁ : N₁ → N))) a)
    (hb : HasColen R v (AA.carrier.map (LinearMap.funLeft R C (ι₂ : N₂ → N))) b) :
    HasColen R v AA.carrier (a ^ Fintype.card N₂ * b ^ Fintype.card N₁) := by
  let e := splitEquiv ι₁ π₁ ι₂ π₂ h11 h22 hsum h12 h21
  have e1 : (fun y : N₁ => e (y, 0)) = ι₁ := by
    funext y
    show ι₁ y + ι₂ 0 = ι₁ y
    simp
  have e2 : (fun y : N₂ => e (0, y)) = ι₂ := by
    funext y
    show ι₁ 0 + ι₂ y = ι₂ y
    simp
  have h := tn_char AA e (fun g hg => by
    convert hs₁ g hg using 3 with x
    exact congrFun e1 _)
  rw [e1, e2] at h
  have h2 := hasColen_tn ha hb
  rw [← h] at h2
  have h3 := hasColen_map v e.symm _ _ h2
  rwa [show AA.carrier.map (LinearMap.funLeft R C (e : N₁ × N₂ → N)) =
    AA.carrier.map (pbE (C := C) (R := R) e : (N → C) →ₗ[R] (N₁ × N₂ → C)) from rfl,
    map_pbE_symm] at h3

theorem eq_of_pow_mul {x₁ y₁ x₂ y₂ : NNReal} {m n : ℕ} (hm : m ≠ 0) (h₁ : x₁ ≤ y₁) (h₂ : x₂ ≤ y₂)
    (hy : y₂ ≠ 0) (h : x₁ ^ m * x₂ ^ n = y₁ ^ m * y₂ ^ n) : x₁ = y₁ := by
  refine le_antisymm h₁ (not_lt.1 fun hlt => ?_)
  have a : x₁ ^ m < y₁ ^ m := pow_lt_pow_left₀ hlt zero_le hm
  have b : x₂ ^ n ≤ y₂ ^ n := pow_le_pow_left₀ zero_le h₂ n
  have c : 0 < y₂ ^ n := pow_pos (pos_iff_ne_zero.2 hy) n
  exact absurd h (ne_of_lt (lt_of_le_of_lt (mul_le_mul_of_nonneg_left b zero_le)
    (mul_lt_mul_of_pos_right a c)))

theorem ret_tight : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N], (∀ x : N, p • x = 0) → ∀ AA : HopfOrder (C := C) R N, ∀ (N' : Type) [AddCommGroup N'] [Fintype N'] [DecidableEq N'], ∀ (ι : N' →+ N) (π : N →+ N'), (∀ y, π (ι y) = y) → (∀ g ∈ AA.carrier, (fun x => g (ι (π x))) ∈ AA.carrier) → IsTight v p AA.carrier → IsTight v p (AA.carrier.map (LinearMap.funLeft R C (ι : N' → N))) := by
  intro p _ C _ _ _ v R _ _ hv hp N _ _ _ hN AA N' _ _ _ ι π hπ hst hT
  classical
  have hcnt := @PositivityTheory.HtPt.Ra.cnt
  have hlens := @PositivityTheory.HtPt.Rc.lens
  let ι₂ : π.ker →+ N := π.ker.subtype
  let π₂ : N →+ π.ker := (AddMonoidHom.id N - ι.comp π).codRestrict π.ker (fun x => by
    simp [AddMonoidHom.mem_ker, hπ])
  have hπ₂ : ∀ x, ι₂ (π₂ x) = x - ι (π x) := fun _ => rfl
  have h12 : ∀ y, π (ι₂ y) = 0 := fun y => y.2
  have h22 : ∀ y, π₂ (ι₂ y) = y := fun y => Subtype.ext (by
    show ι₂ (π₂ (ι₂ y)) = ι₂ y
    rw [hπ₂, h12]; simp)
  have h21 : ∀ y, π₂ (ι y) = 0 := fun y => Subtype.ext (by
    show ι₂ (π₂ (ι y)) = 0
    rw [hπ₂, hπ]; simp)
  have hsum : ∀ x, ι (π x) + ι₂ (π₂ x) = x := fun x => by rw [hπ₂]; simp
  have hs₂ : ∀ g ∈ AA.carrier, (fun x => g (ι₂ (π₂ x))) ∈ AA.carrier :=
    (stabadd C R N N AA AA (AddMonoidHom.id N) (ι.comp π) (fun g hg => hg) hst).2
  obtain ⟨⟨A₁, hA₁⟩, -⟩ := ret_hopf p C v R hv hp N AA N' ι π hπ hst
  obtain ⟨⟨A₂, hA₂⟩, -⟩ := ret_hopf p C v R hv hp N AA π.ker ι₂ π₂ h22 hs₂
  have hN₁ : ∀ y : N', p • y = 0 := fun y => by rw [← hπ y, ← map_nsmul, hN, map_zero]
  have hN₂ : ∀ y : π.ker, p • y = 0 := fun y => by rw [← h22 y, ← map_nsmul, hN, map_zero]
  obtain ⟨a₁, c₁, o₁, -, hc₁0, -, ha₁, hc₁, ho₁⟩ := hlens p C v R hv hp N' hN₁ A₁
  obtain ⟨a₂, c₂, o₂, -, hc₂0, ho₂0, ha₂, hc₂, ho₂⟩ := hlens p C v R hv hp π.ker hN₂ A₂
  have l₁ := (hcnt p C v R hv hp N' hN₁ A₁ _ _ ha₁ hc₁).1
  have l₂ := (hcnt p C v R hv hp π.ker hN₂ A₂ _ _ ha₂ hc₂).1
  have m₁ := u4 p C v R hv hp N' hN₁ A₁ _ _ hc₁ ho₁
  have m₂ := u4 p C v R hv hp π.ker hN₂ A₂ _ _ hc₂ ho₂
  rw [hA₁] at ha₁ hc₁ ho₁
  rw [hA₂] at ha₂ hc₂ ho₂
  obtain ⟨a, c, o, ha, hc, ho, ea, eo⟩ := hT
  obtain rfl := hasLen_unique hv ha
    (ret_af p C v R hv hp N AA N' π.ker ι π ι₂ π₂ hπ h22 hsum h12 h21 hst hs₂ _ _ ha₁ ha₂)
  obtain rfl := hasLen_unique hv ho
    (ret_om hv AA ι π ι₂ π₂ hπ h22 hsum h12 h21 hst hs₂ _ _ ho₁ ho₂)
  obtain rfl := hasColen_unique hv AA.lat hc
    (ret_colen AA ι π ι₂ π₂ hπ h22 hsum h12 h21 hst _ _ hc₁ hc₂)
  have hcard : Fintype.card N = Fintype.card N' * Fintype.card π.ker := by
    rw [← Fintype.card_prod]
    exact (Fintype.card_congr (splitEquiv ι π ι₂ π₂ hπ h22 hsum h12 h21).toEquiv).symm
  rw [hcard] at ea eo
  refine ⟨a₁, c₁, o₁, ha₁, hc₁, ho₁, ?_, ?_⟩
  · refine eq_of_pow_mul (m := Fintype.card π.ker) (n := Fintype.card N') Fintype.card_ne_zero
      l₁ l₂ (pow_ne_zero _ hc₂0) ?_
    calc _ = (a₁ * a₂) ^ (Fintype.card N' * Fintype.card π.ker * (p - 1)) := by ring
      _ = _ := by rw [ea]; ring
  · refine (eq_of_pow_mul (m := Fintype.card π.ker) (n := Fintype.card N') Fintype.card_ne_zero
      m₁ m₂ (pow_ne_zero _ ho₂0) ?_).symm
    calc _ = (c₁ ^ Fintype.card π.ker * c₂ ^ Fintype.card N') ^ 2 := by ring
      _ = _ := by rw [← eo]; ring

end PositivityTheory.HtPt.Re
end
end
