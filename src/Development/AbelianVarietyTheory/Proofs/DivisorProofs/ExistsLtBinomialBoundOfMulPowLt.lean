module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppTopBijectiveAndSurjectiveNormalDomain
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
public import Development.WeilBound.CoreStatements.PublishedTheorems.NefNumerics.NefRiemannRoch.NefRiemannRochAsymptotic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineCocycleFirstOrderTaylorSqZero

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLtBinomialBoundOfMulPowLt
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLtBinomialBoundOfMulPowLt
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep GlobalTheory.FieldPair

namespace GlobalTheory

theorem elementary_binom_bound : ∀ (c k : ℕ) (h d : ℚ), 1 ≤ k → 0 < h → (c : ℚ) * (k : ℚ) ^ k < h ^ k * d →
  ∃ q : ℚ, q < d ∧ ∀ l₀ : ℕ, ∃ l M : ℕ, l₀ ≤ l ∧ 1 ≤ M ∧ (k : ℚ) * l < h * M ∧ h < l ∧
    ((c * (M + k - 1).choose k : ℕ) : ℚ) < q * (l : ℚ) ^ k / k.factorial := by
  intro c k h d hk hh hcd
  have hhk : 0 < h ^ k := pow_pos hh k
  set a : ℚ := (c : ℚ) * ((k : ℚ) / h) ^ k with ha
  have had : a < d := by
    rw [ha, div_pow, ← mul_div_assoc, div_lt_iff₀ hhk]; linarith
  refine ⟨(a + d) / 2, by linarith, ?_⟩
  intro l₀
  have hlim : Tendsto (fun l : ℕ => (c : ℚ) * ((k : ℚ) / h + (k : ℚ) / (l : ℚ)) ^ k) atTop
      (nhds ((c : ℚ) * ((k : ℚ) / h + 0) ^ k)) :=
    ((tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat (k : ℚ))).pow k).const_mul _
  rw [add_zero] at hlim
  have hev1 : ∀ᶠ l : ℕ in atTop, (c : ℚ) * ((k : ℚ) / h + (k : ℚ) / (l : ℚ)) ^ k < (a + d) / 2 :=
    hlim.eventually (gt_mem_nhds (by rw [← ha]; linarith))
  have hev2 : ∀ᶠ l : ℕ in atTop, h < (l : ℚ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop h)
  obtain ⟨l, hl1, hl2, hl0⟩ := (hev1.and (hev2.and (eventually_ge_atTop l₀))).exists
  have hlpos : (0 : ℚ) < l := lt_trans hh hl2
  set x : ℚ := (k : ℚ) * l / h with hx
  have hx0 : 0 ≤ x := by positivity
  refine ⟨l, ⌊x⌋₊ + 1, hl0, by omega, ?_, hl2, ?_⟩
  · have := Nat.lt_floor_add_one x
    push_cast
    rw [hx, div_lt_iff₀ hh] at this
    linarith
  · have hfl : ((⌊x⌋₊ : ℕ) : ℚ) ≤ x := Nat.floor_le hx0
    have hcast : (((⌊x⌋₊ + 1 + k - 1 : ℕ)) : ℚ) = (⌊x⌋₊ : ℚ) + k := by
      have : ⌊x⌋₊ + 1 + k - 1 = ⌊x⌋₊ + k := by omega
      rw [this]; push_cast; ring
    have hch : (((⌊x⌋₊ + 1 + k - 1).choose k : ℕ) : ℚ) ≤ (((⌊x⌋₊ + 1 + k - 1 : ℕ)) : ℚ) ^ k / k.factorial :=
      Nat.choose_le_pow_div k _
    have hfact : (0 : ℚ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
    have hbase : (((⌊x⌋₊ + 1 + k - 1 : ℕ)) : ℚ) ≤ (l : ℚ) * ((k : ℚ) / h + (k : ℚ) / (l : ℚ)) := by
      rw [hcast, mul_add, hx]
      have e1 : (l : ℚ) * ((k : ℚ) / h) = (k : ℚ) * l / h := by ring
      have e2 : (l : ℚ) * ((k : ℚ) / l) = k := by field_simp
      rw [e1, e2]; linarith [hfl]
    have hpow : (((⌊x⌋₊ + 1 + k - 1 : ℕ)) : ℚ) ^ k ≤ ((l : ℚ) * ((k : ℚ) / h + (k : ℚ) / (l : ℚ))) ^ k :=
      pow_le_pow_left₀ (by positivity) hbase k
    have hlk : (0 : ℚ) < (l : ℚ) ^ k := pow_pos hlpos k
    push_cast
    calc (c : ℚ) * (((⌊x⌋₊ + 1 + k - 1).choose k : ℕ) : ℚ)
        ≤ (c : ℚ) * ((((⌊x⌋₊ + 1 + k - 1 : ℕ)) : ℚ) ^ k / k.factorial) :=
          mul_le_mul_of_nonneg_left hch (by positivity)
      _ ≤ (c : ℚ) * (((l : ℚ) * ((k : ℚ) / h + (k : ℚ) / (l : ℚ))) ^ k / k.factorial) := by
          gcongr
      _ = ((c : ℚ) * ((k : ℚ) / h + (k : ℚ) / (l : ℚ)) ^ k) * (l : ℚ) ^ k / k.factorial := by
          rw [mul_pow]; ring
      _ < (a + d) / 2 * (l : ℚ) ^ k / k.factorial := by
          apply div_lt_div_of_pos_right _ hfact
          exact mul_lt_mul_of_pos_right hl1 hlk

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLtBinomialBoundOfMulPowLtStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep GlobalTheory.FieldPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lt_binomial_bound_of_mul_pow_lt : ∀ (c k : ℕ) (h d : ℚ), 1 ≤ k → 0 < h → (c : ℚ) * (k : ℚ) ^ k < h ^ k * d →
  ∃ q : ℚ, q < d ∧ ∀ l₀ : ℕ, ∃ l M : ℕ, l₀ ≤ l ∧ 1 ≤ M ∧ (k : ℚ) * l < h * M ∧ h < l ∧
    ((c * (M + k - 1).choose k : ℕ) : ℚ) < q * (l : ℚ) ^ k / k.factorial := by
  first | exact @GlobalTheory.elementary_binom_bound | exact GlobalTheory.elementary_binom_bound | (intros; apply GlobalTheory.elementary_binom_bound <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalSquareFactorizationSections
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.SquareSpread

theorem germ_res_hom {X : Scheme.{0}} {U V : X.Opens} (h : V ≤ U) {x : X} (hx : x ∈ V) (s : Γ(X, U)) :
    (X.presheaf.germ V x hx).hom ((X.presheaf.map (homOfLE h).op).hom s) =
      (X.presheaf.germ U x (h hx)).hom s :=
  TopCat.Presheaf.germ_res_apply _ (homOfLE h) x hx s

theorem res_res_hom {X : Scheme.{0}} {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (s : Γ(X, U)) :
    (X.presheaf.map (homOfLE h₂).op).hom ((X.presheaf.map (homOfLE h₁).op).hom s) =
      (X.presheaf.map (homOfLE (h₂.trans h₁)).op).hom s := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem exists_res_eq {X : Scheme.{0}} {U : X.Opens} {x : X} (hx : x ∈ U) (s t : Γ(X, U))
    (h : (X.presheaf.germ U x hx).hom s = (X.presheaf.germ U x hx).hom t) :
    ∃ W : X.Opens, ∃ hW : W ≤ U, x ∈ W ∧
      (X.presheaf.map (homOfLE hW).op).hom s = (X.presheaf.map (homOfLE hW).op).hom t := by
  obtain ⟨W, hxW, iU, iV, e⟩ := TopCat.Presheaf.germ_eq X.presheaf x hx hx s t h
  refine ⟨W, iU.le, hxW, ?_⟩
  have h1 : iU = homOfLE iU.le := rfl
  have h2 : iV = homOfLE iU.le := Subsingleton.elim _ _
  rw [h1] at e
  rw [h2] at e
  exact e

end GlobalTheory.Mum.SquareSpread


open GlobalTheory.Mum.SquareSpread in
theorem GlobalTheory.Mum.unit_mul_sq_spread : ∀ (X : Scheme.{0}) (L2 : LB X) (h : L2.Sec) (x : X) (j₀ : L2.ι) (hx : x ∈ L2.U j₀) (u : (X.presheaf.stalk x)ˣ) (a : X.presheaf.stalk x), a ≠ 0 → (X.presheaf.germ (L2.U j₀) x hx).hom (h.f j₀) = u * a ^ 2 → ∃ V : X.Opens, x ∈ V ∧ ∃ a : Γ(X, V), a ≠ 0 ∧ ∀ j, ∃ u : Γ(X, V ⊓ L2.U j)ˣ, (X.presheaf.map (homOfLE inf_le_right).op).hom (h.f j) = (u : Γ(X, V ⊓ L2.U j)) * (X.presheaf.map (homOfLE inf_le_left).op).hom a ^ 2 := by
  intro X L2 h x j₀ hx u a ha hh

  obtain ⟨W₁, hW₁, hx₁, a', ha'⟩ := TopCat.Presheaf.exists_le_germ_eq X.presheaf a hx
  obtain ⟨W₂, hW₂, hx₂, u', hu'⟩ := TopCat.Presheaf.exists_le_germ_eq X.presheaf (u : X.presheaf.stalk x) hx₁
  obtain ⟨W₃, hW₃, hx₃, v', hv'⟩ := TopCat.Presheaf.exists_le_germ_eq X.presheaf ((u⁻¹ : (X.presheaf.stalk x)ˣ) : X.presheaf.stalk x) hx₂
  have l31 : W₃ ≤ W₁ := hW₃.trans hW₂
  have l30 : W₃ ≤ L2.U j₀ := l31.trans hW₁
  set A : Γ(X, W₃) := (X.presheaf.map (homOfLE l31).op).hom a' with hA
  set U' : Γ(X, W₃) := (X.presheaf.map (homOfLE hW₃).op).hom u' with hU'
  set H : Γ(X, W₃) := (X.presheaf.map (homOfLE l30).op).hom (h.f j₀) with hH
  have gA : (X.presheaf.germ W₃ x hx₃).hom A = a := by rw [hA, germ_res_hom]; exact ha'
  have gU : (X.presheaf.germ W₃ x hx₃).hom U' = u := by rw [hU', germ_res_hom]; exact hu'
  have gV : (X.presheaf.germ W₃ x hx₃).hom v' = ((u⁻¹ : (X.presheaf.stalk x)ˣ) : X.presheaf.stalk x) := hv'
  have gH : (X.presheaf.germ W₃ x hx₃).hom H = u * a ^ 2 := by rw [hH, germ_res_hom]; exact hh
  obtain ⟨W₄, hW₄, hx₄, e₄⟩ := exists_res_eq hx₃ (U' * v') 1 (by
    rw [map_mul, map_one, gU, gV, Units.mul_inv])
  obtain ⟨W₅, hW₅, hx₅, e₅⟩ := exists_res_eq hx₃ H (U' * A ^ 2) (by
    rw [map_mul, map_pow, gU, gA, gH])

  have lV3 : W₄ ⊓ W₅ ≤ W₃ := inf_le_left.trans hW₄
  have hxV : x ∈ W₄ ⊓ W₅ := ⟨hx₄, hx₅⟩
  have e₄' : (X.presheaf.map (homOfLE lV3).op).hom U' * (X.presheaf.map (homOfLE lV3).op).hom v' = 1 := by
    rw [← map_mul, ← map_one (X.presheaf.map (homOfLE lV3).op).hom, ← res_res_hom hW₄ (inf_le_left : W₄ ⊓ W₅ ≤ W₄),
      ← res_res_hom hW₄ (inf_le_left : W₄ ⊓ W₅ ≤ W₄) 1, e₄]
  have e₅' : (X.presheaf.map (homOfLE lV3).op).hom H = (X.presheaf.map (homOfLE lV3).op).hom U' *
      ((X.presheaf.map (homOfLE lV3).op).hom A) ^ 2 := by
    rw [← map_pow, ← map_mul, ← res_res_hom hW₅ (inf_le_right : W₄ ⊓ W₅ ≤ W₅),
      ← res_res_hom hW₅ (inf_le_right : W₄ ⊓ W₅ ≤ W₅) (U' * A ^ 2), e₅]
  let uV : Γ(X, W₄ ⊓ W₅)ˣ := ⟨_, _, e₄', by rw [mul_comm]; exact e₄'⟩
  refine ⟨W₄ ⊓ W₅, hxV, (X.presheaf.map (homOfLE lV3).op).hom A, ?_, ?_⟩
  · intro h0
    apply ha
    rw [← gA, ← germ_res_hom lV3 hxV, h0, map_zero]
  · intro j
    have k : W₄ ⊓ W₅ ⊓ L2.U j ≤ L2.U j ⊓ L2.U j₀ := le_inf inf_le_right (inf_le_left.trans (lV3.trans l30))
    refine ⟨res k (L2.g j j₀) * Units.map (X.presheaf.map (homOfLE (inf_le_left : W₄ ⊓ W₅ ⊓ L2.U j ≤ W₄ ⊓ W₅)).op).hom uV, ?_⟩
    have c := congrArg (X.presheaf.map (homOfLE k).op).hom (h.compat j j₀)
    rw [map_mul, res_res_hom, res_res_hom] at c
    have e6 := congrArg (X.presheaf.map (homOfLE (inf_le_left : W₄ ⊓ W₅ ⊓ L2.U j ≤ W₄ ⊓ W₅)).op).hom e₅'
    rw [map_mul, map_pow, hH, res_res_hom, res_res_hom, res_res_hom] at e6
    rw [Units.val_mul, Units.coe_map, res, Units.coe_map]
    simp only [MonoidHom.coe_coe, hA, res_res_hom] at e6 ⊢
    rw [c, e6, _root_.mul_assoc]
    congr 2
    exact (res_res_hom lV3 _ U').symm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSectionSquareUnitsLocal
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.SqHorizontal

theorem exists_of_atPrime {C S : Type} [CommRing C] [CommRing S] [Algebra C S] (p : Ideal C) [p.IsPrime]
    [IsLocalization.AtPrime S p] (H : C) (T W : S) (hW : IsUnit W) (e : T ^ 2 = W * algebraMap C S H) :
    ∃ a b c : C, b ∉ p ∧ c ∉ p ∧ b * H = c * a ^ 2 := by
  obtain ⟨⟨a, s⟩, ha⟩ := IsLocalization.surj p.primeCompl T
  obtain ⟨⟨d, t⟩, hd⟩ := IsLocalization.surj p.primeCompl W
  dsimp only at ha hd
  have hdu : d ∈ p.primeCompl := by
    rw [← IsLocalization.AtPrime.isUnit_to_map_iff S p, ← hd]
    exact hW.mul (IsLocalization.map_units S t)
  have key : algebraMap C S (d * (s : C) ^ 2 * H) = algebraMap C S ((t : C) * a ^ 2) := by
    simp only [map_mul, map_pow]
    rw [← ha, ← hd, mul_pow, e]
    ring
  obtain ⟨u, hu⟩ := (IsLocalization.eq_iff_exists p.primeCompl S).1 key
  refine ⟨a, u * (d * (s : C) ^ 2), u * t, ?_, ?_, ?_⟩
  · exact p.primeCompl.mul_mem u.2 (p.primeCompl.mul_mem hdu (p.primeCompl.pow_mem s.2 2))
  · exact p.primeCompl.mul_mem u.2 t.2
  · linear_combination hu

theorem isIso_stalkMap {X Y : Scheme.{0}} (φ : X ⟶ Y) [Flat φ] [SurjectiveOnStalks φ] (x : X) :
    IsIso (φ.stalkMap x) := by
  have h1 := Flat.stalkMap φ x
  have h2 := φ.stalkMap_surjective x
  algebraize [(φ.stalkMap x).hom]
  have : IsLocalHom (algebraMap (Y.presheaf.stalk (φ x)) (X.presheaf.stalk x)) :=
    inferInstanceAs (IsLocalHom (φ.stalkMap x).hom)
  have := Module.FaithfullyFlat.of_flat_of_isLocalHom (A := Y.presheaf.stalk (φ x))
    (B := X.presheaf.stalk x)
  exact (ConcreteCategory.isIso_iff_bijective _).2
    ⟨FaithfulSMul.algebraMap_injective (Y.presheaf.stalk (φ x)) (X.presheaf.stalk x), h2⟩

theorem exists_of_stalk {X Y : Scheme.{0}} (f : Y ⟶ X) (x : X) (q : Spec (X.presheaf.stalk x)) (y : Y)
    [IsIso (f.stalkMap y)] (hy : X.fromSpecStalk x q = f y) (U : X.Opens) (hx : x ∈ U) (hyU : f y ∈ U)
    (h : Γ(X, U)) (T W : Y.presheaf.stalk y) (hW : IsUnit W)
    (e : T ^ 2 = W * (Y.presheaf.germ (f ⁻¹ᵁ U) y hyU).hom ((f.app U).hom h)) :
    ∃ a b c : X.presheaf.stalk x, b ∉ q.asIdeal ∧ c ∉ q.asIdeal ∧
      b * (X.presheaf.germ U x hx).hom h = c * a ^ 2 := by
  let ψ : Y.presheaf.stalk y ⟶ (Spec (X.presheaf.stalk x)).presheaf.stalk q :=
    inv (f.stalkMap y) ≫ X.presheaf.stalkSpecializes (specializes_of_eq hy) ≫ (X.fromSpecStalk x).stalkMap q
  have hψ : f.app U ≫ Y.presheaf.germ (f ⁻¹ᵁ U) y hyU ≫ ψ =
      X.presheaf.germ U x hx ≫ StructureSheaf.toStalk (X.presheaf.stalk x) q := by
    rw [← Category.assoc, ← Scheme.Hom.germ_stalkMap f U y hyU]
    simp only [ψ, Category.assoc, IsIso.hom_inv_id_assoc, TopCat.Presheaf.germ_stalkSpecializes_assoc]
    rw [Scheme.Hom.germ_stalkMap, Scheme.fromSpecStalk_app hx]
    simp only [Category.assoc, TopCat.Presheaf.germ_res]
    rfl
  letI : Algebra (X.presheaf.stalk x) ((Spec (X.presheaf.stalk x)).presheaf.stalk q) :=
    (StructureSheaf.toStalk (X.presheaf.stalk x) q).hom.toAlgebra
  have hl : IsLocalization.AtPrime ((Spec (X.presheaf.stalk x)).presheaf.stalk q) q.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk (X.presheaf.stalk x) q
  refine exists_of_atPrime (S := (Spec (X.presheaf.stalk x)).presheaf.stalk q) q.asIdeal _
    (ψ.hom T) (ψ.hom W) (hW.map ψ.hom) ?_
  rw [← map_pow, e, map_mul]
  congr 1
  exact congrArg (fun k => k.hom h) hψ

theorem horizontal : ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'], AdmBase R' (maximalIdeal R') → ∀ (G₁ : Over (Sp R')) [GrpObj G₁] [IsCommMonObj G₁], IsSemiAbelian G₁ → ∀ (L2 : LB G₁.left) (h : L2.Sec) (Lθ : LB (pullback G₁.hom (jK R'))), Lθ.IsLB → ∀ θ : Lθ.Sec, (∀ j i, ∃ w : Γ(pullback G₁.hom (jK R'), pullback.fst G₁.hom (jK R') ⁻¹ᵁ L2.U j ⊓ Lθ.U i)ˣ, ((pullback G₁.hom (jK R')).presheaf.map (homOfLE inf_le_right).op).hom (θ.f i) ^ 2 = (w : Γ(pullback G₁.hom (jK R'), pullback.fst G₁.hom (jK R') ⁻¹ᵁ L2.U j ⊓ Lθ.U i)) * ((pullback G₁.hom (jK R')).presheaf.map (homOfLE inf_le_left).op).hom (((pullback.fst G₁.hom (jK R')).app (L2.U j)).hom (h.f j))) → ∀ x : G₁.left, ∀ j (hx : x ∈ L2.U j), ∀ p : Ideal (G₁.left.presheaf.stalk x), p.IsPrime → Ideal.comap ((G₁.left.presheaf.germ ⊤ x trivial).hom.comp ((G₁.hom.appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R')).inv.hom)) p = ⊥ → ∃ a b c : G₁.left.presheaf.stalk x, b ∉ p ∧ c ∉ p ∧ b * (G₁.left.presheaf.germ (L2.U j) x hx).hom (h.f j) = c * a ^ 2 := by
  intro R' _ _ _ _ G₁ _ _ _ L2 h Lθ hL θ hθ x j hx p hp hc
  have : IsPreimmersion (jK R') := IsPreimmersion.of_isLocalization (nonZeroDivisors R') (S := FractionRing R')
  have : Flat (jK R') := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.2 (IsLocalization.flat (FractionRing R') (nonZeroDivisors R'))
  let q : Spec (G₁.left.presheaf.stalk x) := ⟨p, hp⟩
  have e₁ : G₁.left.fromSpecStalk x ≫ G₁.hom = Spec.map ((Scheme.ΓSpecIso (CommRingCat.of R')).inv ≫
      G₁.hom.appTop ≫ G₁.left.presheaf.germ ⊤ x trivial) := by
    apply ext_of_isAffine
    rw [Scheme.Hom.comp_appTop, Scheme.fromSpecStalk_appTop,
      ← cancel_epi (Scheme.ΓSpecIso (CommRingCat.of R')).inv, ← Scheme.ΓSpecIso_inv_naturality]
    simp
  have e₂ : G₁.hom (G₁.left.fromSpecStalk x q) = jK R' (⊥ : PrimeSpectrum (FractionRing R')) := by
    rw [← Scheme.Hom.comp_apply, e₁]
    apply PrimeSpectrum.ext
    refine hc.trans ?_
    exact (Ideal.comap_bot_of_injective (algebraMap R' (FractionRing R'))
      (IsFractionRing.injective R' (FractionRing R'))).symm
  obtain ⟨y, hy, -⟩ := Scheme.Pullback.exists_preimage_pullback _ _ e₂
  have hs : SurjectiveOnStalks (pullback.fst G₁.hom (jK R')) :=
    MorphismProperty.of_isPullback (P := @SurjectiveOnStalks) (IsPullback.of_hasPullback _ _).flip inferInstance
  have := isIso_stalkMap (pullback.fst G₁.hom (jK R')) y
  have hyU : pullback.fst G₁.hom (jK R') y ∈ L2.U j := by
    rw [hy]
    have : G₁.left.fromSpecStalk x q ∈ Set.range (G₁.left.fromSpecStalk x) := ⟨q, rfl⟩
    rw [Scheme.range_fromSpecStalk] at this
    exact Specializes.mem_open this (L2.U j).isOpen hx
  obtain ⟨i, hi⟩ : ∃ i, y ∈ Lθ.U i := by
    have : y ∈ ⨆ i, Lθ.U i := by rw [hL.cover]; trivial
    exact TopologicalSpace.Opens.mem_iSup.1 this
  obtain ⟨w, hw⟩ := hθ j i
  have hm : y ∈ pullback.fst G₁.hom (jK R') ⁻¹ᵁ L2.U j ⊓ Lθ.U i := ⟨hyU, hi⟩
  have hw' := congrArg ((pullback G₁.hom (jK R')).presheaf.germ _ y hm).hom hw
  rw [map_pow, map_mul] at hw'
  refine exists_of_stalk (pullback.fst G₁.hom (jK R')) x q y hy.symm (L2.U j) hx hyU (h.f j) _ _
    (w.isUnit.map ((pullback G₁.hom (jK R')).presheaf.germ _ y hm).hom) (hw'.trans ?_)
  congr 1
  exact TopCat.Presheaf.germ_res_apply _ _ _ _ _

end GlobalTheory.SqHorizontal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivationContractionLieDerivativeDeRhamRules
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivationContractionLieDerivativeDeRhamRules
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.PDForm

variable {R B : Type} [CommRing R] [CommRing B] [Algebra R B] (v : Derivation R B B)

theorem indLeft {P : DR R B → Prop} (h : ∀ b : B, P (algebraMap B _ b)) (ha : ∀ x y, P x → P y → P (x + y))
    (hm : ∀ (ω : Ω[B⁄R]) x, P x → P (ι1 ω * x)) (x : DR R B) : P x :=
  CliffordAlgebra.left_induction (P := P) 0 h ha (fun x m hx ↦ hm m x hx) x

theorem ctr_algebraMap (b : B) : ctr v (algebraMap B (DR R B) b) = 0 := by
  simp [ctr]

theorem ctr_ι (ω : Ω[B⁄R]) : ctr v (ι1 ω) = algebraMap B (DR R B) (v.liftKaehlerDifferential ω) := by
  simp [ctr]

theorem ctr_ι_mul (ω : Ω[B⁄R]) (x : DR R B) :
    ctr v (ι1 ω * x) = v.liftKaehlerDifferential ω • x - ι1 ω * ctr v x :=
  CliffordAlgebra.contractLeft_ι_mul _ _ _

theorem ctr_mul (x y : DR R B) : ctr v (x * y) = ctr v x * y + sgn x * ctr v y := by
  induction x using indLeft with
  | h b =>
    rw [← Algebra.smul_def, map_smul, ctr_algebraMap, zero_mul, zero_add, AlgHom.commutes, Algebra.smul_def]
  | ha x x' hx hx' => rw [add_mul, map_add (f := _), hx, hx', map_add (f := _), map_add (f := _), add_mul, add_mul]; abel
  | hm ω x ih =>
    rw [mul_assoc, ctr_ι_mul, ih, ctr_ι_mul, map_mul, sgn_ι]
    simp only [mul_add, sub_mul, smul_mul_assoc, mul_assoc, neg_mul]
    abel

theorem ctr_ctr (x : DR R B) : ctr v (ctr v x) = 0 :=
  CliffordAlgebra.contractLeft_contractLeft _ _

theorem ctr_sgn (x : DR R B) : ctr v (sgn x) = -sgn (ctr v x) := by
  induction x using indLeft with
  | h b => rw [AlgHom.commutes, ctr_algebraMap, map_zero, neg_zero]
  | ha x x' hx hx' => rw [map_add (f := _), map_add (f := _), hx, hx', map_add (f := _), map_add (f := _), neg_add]
  | hm ω x ih =>
    rw [map_mul, sgn_ι, neg_mul, map_neg, ctr_ι_mul, ih, ctr_ι_mul, map_sub, map_smul, map_mul, sgn_ι, mul_neg, neg_mul]

theorem ctr_mem_pred {n : ℕ} {x : DR R B} (hx : x ∈ ⋀[B]^n Ω[B⁄R]) : ctr v x ∈ ⋀[B]^(n - 1) Ω[B⁄R] := by
  induction hx using Submodule.pow_induction_on_left' with
  | algebraMap b => rw [ctr_algebraMap]; exact zero_mem _
  | add x y i _ _ hx hy => rw [map_add (f := _)]; exact add_mem hx hy
  | mem_mul m hm i x hx ih =>
    obtain ⟨ω, rfl⟩ := hm
    change ctr v (ι1 ω * x) ∈ _
    rw [ctr_ι_mul, Nat.succ_sub_one]
    refine sub_mem (Submodule.smul_mem _ _ hx) ?_
    cases i with
    | zero =>
      change x ∈ LinearMap.range _ ^ 0 at hx
      rw [pow_zero] at hx
      obtain ⟨b, rfl⟩ := Submodule.mem_one.1 hx
      rw [ctr_algebraMap, mul_zero]; exact zero_mem _
    | succ k =>
      have := mul_mem (ι_mem ω) ih
      rwa [Nat.add_sub_cancel, add_comm] at this

theorem ctr_mem {j : ℕ} {x : DR R B} (hx : x ∈ ⋀[B]^(j + 1) Ω[B⁄R]) : ctr v x ∈ ⋀[B]^j Ω[B⁄R] := by
  simpa using ctr_mem_pred v hx

theorem lie_apply (x : DR R B) : lie v x = dDR R B (ctr v x) + ctr v (dDR R B x) := rfl

theorem lie_mul (x y : DR R B) : lie v (x * y) = lie v x * y + x * lie v y := by
  simp only [lie_apply, ctr_mul, dDR_mul, map_add (f := _), ctr_sgn, dDR_sgn, sgn_sgn, neg_mul, add_mul, mul_add]
  abel

theorem lie_algebraMap (b : B) : lie v (algebraMap B (DR R B) b) = algebraMap B (DR R B) (v b) := by
  rw [lie_apply, ctr_algebraMap, map_zero, zero_add, dDR_algebraMap, ctr_ι,
    Derivation.liftKaehlerDifferential_comp_D]

theorem lie_D (b : B) : lie v (ι1 (D R B b)) = ι1 (D R B (v b)) := by
  rw [lie_apply, ctr_ι, Derivation.liftKaehlerDifferential_comp_D, dDR_algebraMap, dDR_D, map_zero, add_zero]

theorem lie_dDR (x : DR R B) : lie v (dDR R B x) = dDR R B (lie v x) := by
  rw [lie_apply, lie_apply, dDR_dDR, map_zero, add_zero, map_add (f := _), dDR_dDR, zero_add]

theorem lie_ctr (x : DR R B) : lie v (ctr v x) = ctr v (lie v x) := by
  rw [lie_apply, lie_apply, ctr_ctr, map_zero, zero_add, map_add (f := _), ctr_ctr, add_zero]

theorem lie_mem {j : ℕ} {x : DR R B} (hx : x ∈ ⋀[B]^j Ω[B⁄R]) : lie v x ∈ ⋀[B]^j Ω[B⁄R] := by
  cases j with
  | zero =>
    have hx' := hx
    change x ∈ LinearMap.range _ ^ 0 at hx'
    rw [pow_zero] at hx'
    obtain ⟨b, rfl⟩ := Submodule.mem_one.1 hx'
    rw [lie_algebraMap]
    change _ ∈ LinearMap.range _ ^ 0
    rw [pow_zero]; exact Submodule.algebraMap_mem _
  | succ k =>
    rw [lie_apply]
    exact add_mem (dDR_mem (ctr_mem v hx)) (ctr_mem v (dDR_mem hx))

theorem ctr_lie_rules : (∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (v : Derivation R B B), (∀ b, ctr v (algebraMap B (DR R B) b) = 0) ∧ (∀ ω, ctr v (ι1 ω) = algebraMap B (DR R B) (v.liftKaehlerDifferential ω)) ∧ (∀ x y, ctr v (x * y) = ctr v x * y + sgn x * ctr v y) ∧ (∀ x, ctr v (ctr v x) = 0) ∧ (∀ x, ctr v (sgn x) = -sgn (ctr v x)) ∧ ∀ (j : ℕ), ∀ x ∈ ⋀[B]^(j + 1) Ω[B⁄R], ctr v x ∈ ⋀[B]^j Ω[B⁄R]) ∧ ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (v : Derivation R B B), (∀ x y, lie v (x * y) = lie v x * y + x * lie v y) ∧ (∀ b, lie v (algebraMap B (DR R B) b) = algebraMap B (DR R B) (v b)) ∧ (∀ b, lie v (ι1 (D R B b)) = ι1 (D R B (v b))) ∧ (∀ x, lie v (dDR R B x) = dDR R B (lie v x)) ∧ (∀ x, lie v (ctr v x) = ctr v (lie v x)) ∧ ∀ (j : ℕ), ∀ x ∈ ⋀[B]^j Ω[B⁄R], lie v x ∈ ⋀[B]^j Ω[B⁄R] :=
  ⟨fun _ _ _ _ _ v ↦ ⟨ctr_algebraMap v, ctr_ι v, ctr_mul v, ctr_ctr v, ctr_sgn v, fun _ _ hx ↦ ctr_mem v hx⟩,
    fun _ _ _ _ _ v ↦ ⟨lie_mul v, lie_algebraMap v, lie_D v, lie_dDR v, lie_ctr v, fun _ _ hx ↦ lie_mem v hx⟩⟩

end GlobalTheory.PDForm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivationContractionLieDerivativeDeRhamRulesStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.derivationContraction_lieDerivative_deRham_rules : (∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (v : Derivation R B B), (∀ b, ctr v (algebraMap B (DR R B) b) = 0) ∧ (∀ ω, ctr v (ι1 ω) = algebraMap B (DR R B) (v.liftKaehlerDifferential ω)) ∧ (∀ x y, ctr v (x * y) = ctr v x * y + sgn x * ctr v y) ∧ (∀ x, ctr v (ctr v x) = 0) ∧ (∀ x, ctr v (sgn x) = -sgn (ctr v x)) ∧ ∀ (j : ℕ), ∀ x ∈ ⋀[B]^(j + 1) Ω[B⁄R], ctr v x ∈ ⋀[B]^j Ω[B⁄R]) ∧ ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (v : Derivation R B B), (∀ x y, lie v (x * y) = lie v x * y + x * lie v y) ∧ (∀ b, lie v (algebraMap B (DR R B) b) = algebraMap B (DR R B) (v b)) ∧ (∀ b, lie v (ι1 (D R B b)) = ι1 (D R B (v b))) ∧ (∀ x, lie v (dDR R B x) = dDR R B (lie v x)) ∧ (∀ x, lie v (ctr v x) = ctr v (lie v x)) ∧ ∀ (j : ℕ), ∀ x ∈ ⋀[B]^j Ω[B⁄R], lie v x ∈ ⋀[B]^j Ω[B⁄R] := by
  first | exact @GlobalTheory.PDForm.ctr_lie_rules | exact GlobalTheory.PDForm.ctr_lie_rules | (intros; apply GlobalTheory.PDForm.ctr_lie_rules <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.H0LowerBoundIntersectionNumberClosure
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.H0LowerBoundIntersectionNumberClosure
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep GlobalTheory.FieldPair

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ClosureRR

theorem eventually_le_of_abs_sub_le (k C : ℕ) (T : ℤ) (q : ℚ) (hq : q < T) (h : ℕ → ℕ)
    (hC : ∀ m : ℕ, |(k.factorial : ℤ) * (h m : ℤ) - T * (m : ℤ) ^ k| ≤
      C * ((k : ℤ) * ((m : ℤ) + 1) ^ (k - 1))) :
    ∃ l₁ : ℕ, ∀ l, l₁ ≤ l → q * (l : ℚ) ^ k / k.factorial ≤ (h l : ℚ) := by
  have hf : (0 : ℚ) < k.factorial := by exact_mod_cast k.factorial_pos
  have hε : (0 : ℚ) < (T : ℚ) - q := sub_pos.2 hq
  obtain ⟨N, hN⟩ := exists_nat_ge ((C : ℚ) * k * 2 ^ (k - 1) / ((T : ℚ) - q))
  refine ⟨N + 1, fun l hl => ?_⟩
  have hm : (1 : ℚ) ≤ l := by exact_mod_cast (show 1 ≤ l by omega)
  have hNl : (N : ℚ) ≤ l := by exact_mod_cast (show N ≤ l by omega)
  have hB : (C : ℚ) * k * 2 ^ (k - 1) ≤ ((T : ℚ) - q) * l := by
    have := (div_le_iff₀ hε).1 (hN.trans hNl)
    linarith
  have a := hC l
  rw [abs_le] at a
  have a' : (T : ℚ) * (l : ℚ) ^ k - (C : ℚ) * ((k : ℚ) * ((l : ℚ) + 1) ^ (k - 1)) ≤
      (k.factorial : ℚ) * (h l : ℚ) := by
    have := a.1
    have e : ((T * (l : ℤ) ^ k - C * ((k : ℤ) * ((l : ℤ) + 1) ^ (k - 1)) : ℤ) : ℚ) ≤
        (((k.factorial : ℤ) * (h l : ℤ) : ℤ) : ℚ) := Int.cast_le.2 (by linarith)
    push_cast at e
    exact e
  rw [div_le_iff₀ hf]
  rcases k with _ | j
  · simp only [pow_zero, mul_one, Nat.factorial_zero, Nat.cast_one, CharP.cast_eq_zero, zero_mul,
      mul_zero, sub_zero, one_mul] at a' ⊢
    linarith
  · simp only [Nat.add_sub_cancel] at a' hB
    have h2 : ((l : ℚ) + 1) ^ j ≤ 2 ^ j * (l : ℚ) ^ j := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) (by linarith) j
    have hl0 : (0 : ℚ) ≤ (l : ℚ) ^ j := by positivity
    have hCk : (0 : ℚ) ≤ (C : ℚ) * ((j + 1 : ℕ) : ℚ) := by positivity
    have e1 : (C : ℚ) * (((j + 1 : ℕ) : ℚ) * ((l : ℚ) + 1) ^ j) ≤
        (C : ℚ) * ((j + 1 : ℕ) : ℚ) * 2 ^ j * (l : ℚ) ^ j := by
      have := mul_le_mul_of_nonneg_left h2 hCk
      nlinarith
    have e2 : (C : ℚ) * ((j + 1 : ℕ) : ℚ) * 2 ^ j * (l : ℚ) ^ j ≤ ((T : ℚ) - q) * l * (l : ℚ) ^ j :=
      mul_le_mul_of_nonneg_right hB hl0
    rw [pow_succ] at a' ⊢
    nlinarith

end GlobalTheory.ClosureRR

namespace GlobalTheory.ClosureRR

theorem h0_ge_of_lt_interNumRed : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ), IsProjOver p → ∀ (A : CartierDiv X) (z : X) (k : ℕ) (q : ℚ),
  IsAmpleLB (toLB A) → letI := algebraΓOfHom p; topologicalKrullDim (closure ({z} : Set X)) = k →
  q < (interNumRed ℂ (Closeds.closure ({z} : Set X)) fun _ : Fin k => toLB A : ℤ) →
  ∃ l₁ : ℕ, ∀ l, l₁ ≤ l → q * (l : ℚ) ^ k / k.factorial ≤
    (letI := algebraΓOfHom (redι (Closeds.closure ({z} : Set X)) ≫ p);
      lbH0 ℂ ((toLB (l • A)).pull (redι (Closeds.closure ({z} : Set X)))) : ℚ) := by
  intro X _ _ p hp A z k q hA
  letI := algebraΓOfHom p
  intro hdim hq
  haveI : IsIntegral (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({z} : Set X))).subscheme :=
    isIntegral_red isIrreducible_singleton.closure
  letI := algebraΓOfHom (redι (Closeds.closure ({z} : Set X)) ≫ p)
  have hi : ∀ r : ℂ, (redι (Closeds.closure ({z} : Set X))).appTop (algebraMap ℂ Γ(X, ⊤) r) =
      algebraMap ℂ Γ((Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({z} : Set X))).subscheme, ⊤) r :=
    fun r => rfl
  have hpq : IsProjOver (redι (Closeds.closure ({z} : Set X)) ≫ p) := by
    obtain ⟨n, f, hf, hs⟩ := hp
    exact ⟨n, redι (Closeds.closure ({z} : Set X)) ≫ f, inferInstance, by rw [Category.assoc, hs]⟩
  have hstr : strHom ℂ (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({z} : Set X))).subscheme =
      redι (Closeds.closure ({z} : Set X)) ≫ p := strHom_eq fun _ => rfl
  have hD : topologicalKrullDim (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({z} : Set X))).subscheme = k :=
    (topologicalKrullDim_red _).trans hdim
  have hNef : IsNef ℂ ((toLB A).pull (redι (Closeds.closure ({z} : Set X)))) :=
    (IsAmpleLB.isNef (k := ℂ) hA).pull_of_isClosedImmersion _ hi
  obtain ⟨C, hC⟩ := NefRiemannRoch.abs_factorial_mul_sections_sub_top_le ℂ _ (hstr ▸ hpq) k hD.le _ hNef
  have heq : interNumRed ℂ (Closeds.closure ({z} : Set X)) (fun _ : Fin k => toLB A) =
      topSelfIntersection ℂ ((toLB A).pull (redι (Closeds.closure ({z} : Set X)))) k :=
    interNumOn_const_eq_topSelf hi (isLB_toLB A) k
  have hH : ∀ l : ℕ, lbH0 ℂ ((toLB (l • A)).pull (redι (Closeds.closure ({z} : Set X)))) =
      lbH0 ℂ (lbPow ((toLB A).pull (redι (Closeds.closure ({z} : Set X)))) l) := fun l =>
    lineBundleGlobalSectionsDim_congr_picardClass (pull_isLB (isLB_toLB _) _) (isLB_lbPow (pull_isLB (isLB_toLB A) _) l)
      (by rw [cls_lbPow (pull_isLB (isLB_toLB A) _), cls_pull (isLB_toLB _), cls_pull (isLB_toLB A),
        ← toPic_apply, ← toPic_apply, map_nsmul, map_nsmul])
  rw [heq] at hq
  obtain ⟨l₁, hl₁⟩ := eventually_le_of_abs_sub_le k C _ q hq _ hC
  exact ⟨l₁, fun l hl => by rw [hH l]; exact hl₁ l hl⟩

end GlobalTheory.ClosureRR
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.H0LowerBoundIntersectionNumberClosureStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep GlobalTheory.FieldPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.h0_lower_bound_of_isAmple_cartierDiv : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ), IsProjOver p → ∀ (A : CartierDiv X) (z : X) (k : ℕ) (q : ℚ),
  IsAmpleLB (toLB A) → letI := algebraΓOfHom p; topologicalKrullDim (closure ({z} : Set X)) = k →
  q < (interNumRed ℂ (Closeds.closure ({z} : Set X)) fun _ : Fin k => toLB A : ℤ) →
  ∃ l₁ : ℕ, ∀ l, l₁ ≤ l → q * (l : ℚ) ^ k / k.factorial ≤
    (letI := algebraΓOfHom (redι (Closeds.closure ({z} : Set X)) ≫ p);
      lbH0 ℂ ((toLB (l • A)).pull (redι (Closeds.closure ({z} : Set X)))) : ℚ) := by
  first | exact @GlobalTheory.ClosureRR.h0_ge_of_lt_interNumRed | exact GlobalTheory.ClosureRR.h0_ge_of_lt_interNumRed | (intros; apply GlobalTheory.ClosureRR.h0_ge_of_lt_interNumRed <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineClassSecondSystemEqNegDefect
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineClassSecondSystemEqNegDefect
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LiftSys

theorem connForm_sub_eq {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} {π : R →+* R₀} {X₀ : Scheme.{0}}
    {s₀ : X₀ ⟶ Sp R₀} (hI : I ^ 2 = 0) (hk : RingHom.ker π = I) (hC : Const s₀) (S : Sys I π s₀)
    (Q : ∀ U : AffOp X₀, S.thickObj hI U ⟶
      (redMor hI hk s₀).obj (Thick.triv (Sec s₀ U.unop.1) (affPt s₀ U.unop) (affPt_w s₀ U.unop)))
    (hQ : ∀ U b, (Q U).φ b = S.p U b) (f : Z1 (O (divided₂ hI) (s₀ ≫ spMap π))) (g : C0 S.F)
    (hg : d0 S.F g = ((S.coef hI).pullbackOneCocycle f).1) (F : Form s₀) (h : C0 (O (dp0 R₀) s₀))
    (hh : d0 _ h = ((redMor hI hk s₀).coef.pullbackOneCocycle f).1 - F.1.1) (U : AffOp X₀) :
    connForm ((redMor hI hk s₀).coef.pullbackOneCocycle f) (affPt s₀ U.unop) (affPt_w s₀ U.unop) -
        D R₀ (Sec s₀ U.unop.1) (ev f (Q U) : Sec s₀ U.unop.1) =
      connForm F.1 (affPt s₀ U.unop) (affPt_w s₀ U.unop) + D R₀ (Sec s₀ U.unop.1) (S.p U (g U)) := by
  set f₀ := (redMor hI hk s₀).coef.pullbackOneCocycle f with hf₀
  have e : f₀ = F.1 + ⟨d0 _ h, commAlgFunctorCoboundaryZero_mem_cocyclesOne _ h⟩ := by
    apply Subtype.ext
    change f₀.1 = F.1.1 + d0 _ h
    rw [hh]; abel
  let hU : ∀ U : AffOp X₀, Sec s₀ U.unop.1 := fun U ↦
    @id (Sec s₀ U.unop.1) <| h (Thick.triv (Sec s₀ U.unop.1) (affPt s₀ U.unop) (affPt_w s₀ U.unop))
  let qU : ∀ U : AffOp X₀, Sec s₀ U.unop.1 := fun U ↦ @id (Sec s₀ U.unop.1) <| ev f (Q U)
  let k : C0 (OAff s₀) := fun U ↦ hU U - S.p U (g U) - qU U
  have hk0 : d0 _ k = 0 := by
    funext U V a
    let tr := Thick.trivHom (hx := affPt_w s₀ U.unop) (T := Thick.triv _ _ (affPt_w s₀ V.unop))
      (Sec.res s₀ (leOfHom a.unop)) (affPt_res s₀ (leOfHom a.unop))
    have h1 := congrArg (fun q ↦ q _ _ tr) hh
    simp only [amitsur_d0_apply, Pi.sub_apply] at h1
    have h0 : F.1.1 _ _ tr = 0 := F.2 tr rfl rfl
    rw [h0, sub_zero] at h1
    have h1' : hU V - Sec.res s₀ (leOfHom a.unop) (hU U) = (f₀.1 _ _ tr : Sec s₀ V.unop.1) := h1
    have h2 := ev_sq f (Q U) ((redMor hI hk s₀).functor.map tr) ((S.thick hI).map a) (Q V) fun c ↦ by
      change Sec.res s₀ (leOfHom a.unop) ((Q U).φ c) = (Q V).φ (mp S.F a c)
      rw [hQ, hQ, S.nat]; rfl
    have h3 : ev f ((S.thick hI).map a) = g V - mp S.F a (g U) := by
      have := congrArg (fun q ↦ q U V a) hg
      simp only [amitsur_d0_apply] at this
      exact this.symm
    have h2' : Sec.res s₀ (leOfHom a.unop) (qU U) + (f₀.1 _ _ tr : Sec s₀ V.unop.1) =
        @id (Sec s₀ V.unop.1) ((Q V).φ (ev f ((S.thick hI).map a))) + qU V := h2
    rw [hQ, id] at h2'
    erw [h3] at h2'
    have nat' : S.p V (mp S.F a (g U)) = Sec.res s₀ (leOfHom a.unop) (S.p U (g U)) := S.nat a (g U)
    rw [map_sub, nat'] at h2'
    change k V - Sec.res s₀ (leOfHom a.unop) (k U) = 0
    simp only [k, map_sub]
    linear_combination h1' + h2'
  obtain ⟨r, hr⟩ := hC k hk0
  have hD : D R₀ (Sec s₀ U.unop.1) (k U) = 0 := by rw [hr U]; exact (D R₀ _).map_algebraMap r
  simp only [k, map_sub] at hD
  rw [e, connForm_add, crystallineConnectionForm_coboundaryZero, ← sub_eq_zero]
  change connForm F.1 _ _ + D R₀ (Sec s₀ U.unop.1) (hU U) - D R₀ (Sec s₀ U.unop.1) (qU U) -
    (connForm F.1 _ _ + D R₀ (Sec s₀ U.unop.1) (S.p U (g U))) = 0
  rw [← hD]; abel

theorem r_eq_neg_defect : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), Const s₀ → ∀ (S S' : Sys I π s₀) (Φ : S.LocIso S') (θ : ∀ (U V : AffOp X₀) (_ : U ⟶ V), Ω[Sec s₀ U.unop.1⁄R₀] →+ S'.F.obj V), Φ.IsDefect θ → ∀ c ∈ S.K hI, ∀ w, FormOf hI hk c w → ∀ z : Z1 S'.F, (∀ U V a, z.1 U V a = θ U V a (w.1 U)) → S'.r hI c = -H1.mk _ z := by
  intro R R₀ _ _ I hI π hπ hk X₀ s₀ hC S S' Φ θ hΘ c hc w hw z hz
  have T := fun (U V : AffOp X₀) ↦ GlobalTheory.T.crystallineCocycle_firstOrder_taylor_sqZero R R₀ I hI π hπ hk X₀ s₀ S S' U V
  choose Q hQ using fun U ↦ (T U U).1
  obtain ⟨f, rfl⟩ := H1.mk_surjective _ c
  obtain ⟨g, hg⟩ := H1.mk_eq_zero.1 (LinearMap.mem_ker.1 hc)
  obtain ⟨F, hF, hFw⟩ := hw
  obtain ⟨h, hh⟩ := H1.mk_eq_mk.1
    (show H1.mk _ ((redMor hI hk s₀).coef.pullbackOneCocycle f) = H1.mk _ F.1 from hF.symm)
  let ΦU : ∀ U : AffOp X₀, S.thickObj hI U ⟶ S'.thickObj hI U := fun U ↦
    S.thickHom S' hI (𝟙 U) (Φ.φ U : S.F.obj U →ₐ[R] S'.F.obj U) fun b ↦
      (Φ.red U b).trans (mp_id (OAff s₀) U (S.p U b)).symm
  change H1.mk _ ((S'.coef hI).pullbackOneCocycle f) = -H1.mk _ z
  rw [← map_neg, H1.mk_eq_mk]
  refine ⟨fun U ↦ Φ.φ U (g U) + ev f (ΦU U), ?_⟩
  funext U V a
  let α : S.thickObj hI U ⟶ S'.thickObj hI V := ΦU U ≫ (S'.thick hI).map a
  let β : S.thickObj hI U ⟶ S'.thickObj hI V := (S.thick hI).map a ≫ ΦU V
  have hθ : IsTheta I (S.p U) α.φ β.φ (θ U V a) := hΘ U V a
  have tay := (T U V).2 (Q U) (hQ U) α β (θ U V a) hθ f
  rw [connForm_sub_eq hI hk hC S Q hQ f g hg F h hh U, map_add (f := _)] at tay
  erw [hθ.der (g U)] at tay
  have hw' : connForm F.1 (affPt s₀ U.unop) (affPt_w s₀ U.unop) = w.1 U := by
    rw [← hFw, cmpForm_apply]
  rw [hw', ← hz] at tay
  have E1 : ev f α = mp S'.F a (ev f (ΦU U)) + @id (S'.F.obj V) (ev f ((S'.thick hI).map a)) := ev_comp f _ _
  have E2 : ev f β = Φ.φ V (ev f ((S.thick hI).map a)) + ev f (ΦU V) := ev_comp f _ _
  have h3 : ev f ((S.thick hI).map a) = g V - mp S.F a (g U) := by
    have := congrArg (fun q ↦ q U V a) hg
    simp only [amitsur_d0_apply] at this
    exact this.symm
  rw [h3, map_sub] at E2
  have E3 : α.φ (g U) = mp S'.F a (Φ.φ U (g U)) := rfl
  have E4 : β.φ (g U) = Φ.φ V (mp S.F a (g U)) := rfl
  erw [E3, E4] at tay
  change Φ.φ V (g V) + ev f (ΦU V) - mp S'.F a (Φ.φ U (g U) + ev f (ΦU U)) =
    @id (S'.F.obj V) (ev f ((S'.thick hI).map a)) - -z.1 U V a
  rw [map_add (f := _)]
  have key : ∀ x y z' p q r s t u : S'.F.obj V, x - y = z' + (p - q) → y = r + s → x = t - q + u →
      t + u - (p + r) = s - -z' := by
    intro x y z' p q r s t u h₁ h₂ h₃
    linear_combination h₁ + h₂ - h₃
  exact key _ _ _ _ _ _ _ _ _ tay E1 E2

end GlobalTheory.LiftSys
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineClassSecondSystemEqNegDefectStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystallineClass_secondSystem_eq_neg_defect : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), Const s₀ → ∀ (S S' : Sys I π s₀) (Φ : S.LocIso S') (θ : ∀ (U V : AffOp X₀) (_ : U ⟶ V), Ω[Sec s₀ U.unop.1⁄R₀] →+ S'.F.obj V), Φ.IsDefect θ → ∀ c ∈ S.K hI, ∀ w, FormOf hI hk c w → ∀ z : Z1 S'.F, (∀ U V a, z.1 U V a = θ U V a (w.1 U)) → S'.r hI c = -H1.mk _ z := by
  first | exact @GlobalTheory.LiftSys.r_eq_neg_defect | exact GlobalTheory.LiftSys.r_eq_neg_defect | (intros; apply GlobalTheory.LiftSys.r_eq_neg_defect <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftToProjectiveBaseInjectiveOverClosedFibre
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftToProjectiveBaseInjectiveOverClosedFibre
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem Emb.chart_injective : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (M : Modif R) (G' : Over M.S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ E : Emb M.π G', ∀ z w : E.H.toScheme, M.π (G'.hom (E.H.ι z)) = closedPoint R → pullback.lift E.f (E.H.ι ≫ G'.hom) E.f_over w = pullback.lift E.f (E.H.ι ≫ G'.hom) E.f_over z → w = z := by
  intro R _ _ _ _ M G' _ _ _ E z w hz hwz

  set p := PSpace.str R E.N
  set Φ : E.H.toScheme ⟶ pullback p M.π := pullback.lift E.f (E.H.ι ≫ G'.hom) E.f_over with hΦ
  set s := G'.hom (E.H.ι z) with hs

  let Ω := M.S.residueField s
  let x : Sp Ω ⟶ M.S := M.S.fromSpecResidueField s
  let φ : R →+* Ω := (Spec.preimage (x ≫ M.π)).hom
  have hφ : spMap φ = x ≫ M.π := by unfold spMap; simp [φ]
  have hker : ∀ r ∈ maximalIdeal R, φ r = 0 := by
    intro r hr
    obtain ⟨pt⟩ : Nonempty (Sp Ω) := inferInstance
    have h1 : (x ≫ M.π) pt = closedPoint R := by
      rw [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]; exact hz
    rw [← hφ] at h1
    have h2 : (spMap φ) pt = PrimeSpectrum.comap φ pt := rfl
    have h3 : pt.asIdeal = ⊥ := by haveI := pt.isPrime; exact Ideal.eq_bot_of_prime _
    have h4 : r ∈ ((spMap φ) pt).asIdeal := by rw [h1]; exact hr
    rw [h2] at h4
    change φ r ∈ pt.asIdeal at h4
    rw [h3] at h4
    exact h4
  let κ : ResidueField R →+* Ω := Ideal.Quotient.lift (maximalIdeal R) φ hker
  have hκ : κ.comp (residue R) = φ := by ext r; rfl
  have hx : x ≫ M.π = spMap (κ.comp (residue R)) := by rw [hκ, hφ]
  obtain ⟨Ω', _, io, e, l, -, hl, hlf⟩ := E.fib Ω x κ hx

  have hx'π : (spMap io ≫ x) ≫ M.π = spMap (io.comp κ) ≫ spMap (residue R) := by
    rw [Category.assoc, hx]; unfold spMap; rw [← Spec.map_comp, ← Spec.map_comp]; rfl
  have hψ : (l ≫ Φ) ≫ pullback.snd p M.π = pullback.snd G'.hom (spMap io ≫ x) ≫ (spMap io ≫ x) := by
    have : Φ ≫ pullback.snd p M.π = E.H.ι ≫ G'.hom := by rw [hΦ]; exact pullback.lift_snd _ _ _
    rw [Category.assoc, this, ← Category.assoc, hl]; exact pullback.condition
  let ψ : pullback G'.hom (spMap io ≫ x) ⟶ pullback (pullback.snd p M.π) (spMap io ≫ x) :=
    pullback.lift (l ≫ Φ) (pullback.snd _ _) hψ

  have hψinj : Function.Injective ψ := by
    haveI : IsImmersion E.j := E.imm
    let h : pullback (pullback.snd p M.π) (spMap io ≫ x) ⟶ PSpace R E.N := pullback.fst _ _ ≫ pullback.fst _ _
    have hΦf : Φ ≫ pullback.fst p M.π = E.f := by rw [hΦ]; exact pullback.lift_fst _ _ _
    have hψ1 : ψ ≫ pullback.fst _ _ = l ≫ Φ := pullback.lift_fst _ _ _
    have hψh : ψ ≫ h = l ≫ E.f := by
      show ψ ≫ pullback.fst _ _ ≫ pullback.fst _ _ = _
      rw [← Category.assoc, hψ1, Category.assoc, hΦf]
    have hθ : (e.hom.left ≫ pullback.fst E.Y.hom (spMap (io.comp κ))) ≫ E.j = ψ ≫ h := by
      rw [hψh, hlf, Category.assoc]
    let θ : pullback G'.hom (spMap io ≫ x) ⟶ pullback E.j h := pullback.lift _ _ hθ
    haveI : Mono (spMap (residue R)) := by
      have : IsClosedImmersion (spMap (residue R)) := IsClosedImmersion.spec_of_surjective _ residue_surjective
      infer_instance
    have hΦs : Φ ≫ pullback.snd p M.π = E.H.ι ≫ G'.hom := by rw [hΦ]; exact pullback.lift_snd _ _ _
    have hρ : pullback.fst E.j h ≫ E.Y.hom = (pullback.snd E.j h ≫ pullback.snd _ _) ≫ spMap (io.comp κ) := by
      rw [← cancel_mono (spMap (residue R))]
      calc pullback.fst E.j h ≫ E.Y.hom ≫ spMap (residue R) = pullback.fst E.j h ≫ E.j ≫ p := by rw [E.j_over]
        _ = pullback.snd E.j h ≫ h ≫ p := by rw [← Category.assoc, pullback.condition, Category.assoc]
        _ = pullback.snd E.j h ≫ pullback.fst _ _ ≫ pullback.snd p M.π ≫ M.π := by
          simp only [h, Category.assoc]; rw [pullback.condition]
        _ = pullback.snd E.j h ≫ pullback.snd _ _ ≫ (spMap io ≫ x) ≫ M.π := by
          rw [← Category.assoc (pullback.fst _ _), pullback.condition, Category.assoc]
        _ = ((pullback.snd E.j h ≫ pullback.snd _ _) ≫ spMap (io.comp κ)) ≫ spMap (residue R) := by
          rw [hx'π]; simp only [Category.assoc]
    let ρ : pullback E.j h ⟶ pullback E.Y.hom (spMap (io.comp κ)) := pullback.lift _ _ hρ
    have hθ1 : θ ≫ pullback.fst E.j h = e.hom.left ≫ pullback.fst _ _ := pullback.lift_fst _ _ _
    have hθ2 : θ ≫ pullback.snd E.j h = ψ := pullback.lift_snd _ _ _
    have hρ1 : ρ ≫ pullback.fst _ _ = pullback.fst E.j h := pullback.lift_fst _ _ _
    have hρ2 : ρ ≫ pullback.snd _ _ = pullback.snd E.j h ≫ pullback.snd _ _ := pullback.lift_snd _ _ _
    have hψ2 : ψ ≫ pullback.snd _ _ = pullback.snd G'.hom (spMap io ≫ x) := pullback.lift_snd _ _ _
    have hθρ : θ ≫ ρ = e.hom.left := by
      apply pullback.hom_ext
      · rw [Category.assoc, hρ1, hθ1]
      · rw [Category.assoc, hρ2, ← Category.assoc, hθ2, hψ2]
        exact (Over.w e.hom).symm
    intro a b hab
    have h1 : θ a = θ b := by
      apply (pullback.snd E.j h).isEmbedding.injective
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.lift_snd]; exact hab
    have h2 : e.hom.left a = e.hom.left b := by
      rw [← hθρ, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, h1]
    have h3 := congrArg e.inv.left h2
    rwa [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← Over.comp_left, e.hom_inv_id, Over.id_left] at h3

  obtain ⟨τ⟩ : Nonempty (Sp Ω') := inferInstance
  have hτ : (spMap io ≫ x) τ = s := by
    rw [Scheme.Hom.comp_apply]; exact Scheme.fromSpecResidueField_apply _ _
  have hΦs : Φ ≫ pullback.snd p M.π = E.H.ι ≫ G'.hom := by rw [hΦ]; exact pullback.lift_snd _ _ _
  have hq : pullback.snd p M.π (Φ z) = (spMap io ≫ x) τ := by
    rw [hτ, ← Scheme.Hom.comp_apply, hΦs, Scheme.Hom.comp_apply]
  obtain ⟨c, hc1, hc2⟩ := Scheme.Pullback.exists_preimage_pullback (f := pullback.snd p M.π) (g := spMap io ≫ x) _ _ hq

  have hm : (pullback.fst Φ (pullback.fst (pullback.snd p M.π) (spMap io ≫ x)) ≫ E.H.ι) ≫ G'.hom =
      (pullback.snd Φ (pullback.fst (pullback.snd p M.π) (spMap io ≫ x)) ≫ pullback.snd _ _) ≫ (spMap io ≫ x) := by
    rw [Category.assoc, ← hΦs, ← Category.assoc, pullback.condition, Category.assoc, pullback.condition,
      Category.assoc]
  let m : pullback Φ (pullback.fst (pullback.snd p M.π) (spMap io ≫ x)) ⟶ pullback G'.hom (spMap io ≫ x) :=
    pullback.lift _ _ hm
  have hm1 : m ≫ l = pullback.fst _ _ := by
    rw [← cancel_mono E.H.ι, Category.assoc, hl]; exact pullback.lift_fst _ _ _
  have hm2 : m ≫ ψ = pullback.snd _ _ := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, hm1, pullback.condition]
    · rw [Category.assoc, pullback.lift_snd]; exact pullback.lift_snd _ _ _
  have lift_pt : ∀ u : E.H.toScheme, Φ u = Φ z → ∃ a, l a = u ∧ ψ a = c := by
    intro u hu
    obtain ⟨pu, h1, h2⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := Φ) (g := pullback.fst (pullback.snd p M.π) (spMap io ≫ x)) u c (hu.trans hc1.symm)
    exact ⟨m pu, by rw [← Scheme.Hom.comp_apply, hm1, h1], by rw [← Scheme.Hom.comp_apply, hm2, h2]⟩
  obtain ⟨a, ha1, ha2⟩ := lift_pt w hwz
  obtain ⟨b, hb1, hb2⟩ := lift_pt z rfl
  rw [← ha1, ← hb1, hψinj (ha2.trans hb2.symm)]

end GlobalTheory.Mum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftToProjectiveBaseInjectiveOverClosedFibreStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lift_to_projective_base_injective_over_closedFibre : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (M : Modif R) (G' : Over M.S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ E : Emb M.π G', ∀ z w : E.H.toScheme, M.π (G'.hom (E.H.ι z)) = closedPoint R → pullback.lift E.f (E.H.ι ≫ G'.hom) E.f_over w = pullback.lift E.f (E.H.ι ≫ G'.hom) E.f_over z → w = z := by
  first | exact @GlobalTheory.Mum.Emb.chart_injective | exact GlobalTheory.Mum.Emb.chart_injective | (intros; apply GlobalTheory.Mum.Emb.chart_injective <;> assumption)
end
end
