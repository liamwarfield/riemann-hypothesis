module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.NadelVanishing.TopPointSep

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDivisorNonKltPointsNumericallyMultiple
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep GlobalTheory.FieldPair

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AmpleStep

variable {X : Scheme.{0}} [IsIntegral X]

theorem generatesAt_add_vanishesAt {D : CartierDiv X} {x : X} {f u : X.functionField}
    (hf : D.GeneratesAt x f) (hu : D.VanishesAt x u) : D.GeneratesAt x (f + u) := by
  obtain ⟨e, he⟩ := D.exists_isEqn x
  rw [he.generatesAt_iff] at hf ⊢
  rw [he.vanishesAt_iff] at hu
  obtain ⟨a, ha, hae⟩ := hf
  obtain ⟨b, hb, hbe⟩ := hu
  refine ⟨a + b, ?_, by rw [map_add (f := _), hae, hbe, add_mul]⟩
  by_contra hn
  have h1 : a + b ∈ IsLocalRing.maximalIdeal _ := (IsLocalRing.mem_maximalIdeal _).2 hn
  have h2 : a ∈ IsLocalRing.maximalIdeal _ := by
    have := Ideal.sub_mem _ h1 hb
    simpa using this
  exact (IsLocalRing.mem_maximalIdeal _).1 h2 ha

theorem eff_nsmul {D : CartierDiv X} (hD : D.Eff) (r : ℕ) : (r • D).Eff := by
  induction r with
  | zero => rw [zero_nsmul]; exact CartierDiv.eff_zero
  | succ r ih => rw [succ_nsmul]; exact ih.add hD

variable [IsLocallyNoetherian X]

theorem mult_nsmul (E : CartierDiv X) (r : ℕ) (z : X) : (r • E).mult z = r * E.mult z := by
  induction r with
  | zero =>
    have h₀ := CartierDiv.mult_add (0 : CartierDiv X) 0 z
    rw [add_zero] at h₀
    rw [zero_nsmul]
    push_cast
    omega
  | succ r ih => rw [succ_nsmul, CartierDiv.mult_add, ih]; push_cast; ring

end GlobalTheory.AmpleStep


open GlobalTheory.AmpleStep in
theorem GlobalTheory.AmpleStep.exists_divisor : GlobalTheory.Published.Principalisation → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X]
    (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → letI := algebraΓOfHom p;
    ∀ (Δ : X → ℚ) (m : ℕ) (G A : CartierDiv X) (D : X → ℚ) (P : Finset X) (z : X) (k : ℕ) (h : ℚ),
      IsEffQDiv Δ → (∀ y, KltAt p n Δ y) → 0 < m → IsLogCanonicalMultiple p n Δ m G → IsAmpleLB (toLB A) →
      IsQCart D → (∀ x ∈ P, IsClosed ({x} : Set X) ∧ z ⤳ x) → 1 ≤ k →
      topologicalKrullDim (closure ({z} : Set X)) = k → (z = genericPoint X ∨ IsNkltCentre p n (Δ + D) z) → 0 < h →
      (P.card : ℚ) * (k : ℚ) ^ k < h ^ k * (interNumRed ℂ (Closeds.closure ({z} : Set X)) fun _ : Fin k => toLB A : ℤ) →
      ∃ (B : X → ℚ) (δ₀ : ℚ), 0 < δ₀ ∧ δ₀ ≤ 1 ∧ QNum p (toLB A) h B ∧ Off B z ∧
        (∀ δ : ℚ, 0 ≤ δ → δ ≤ δ₀ → ∀ x ∈ P, ¬ KltAt p n (Δ + (1 - δ) • D + B) x) ∧
        (∀ y, ¬ z ⤳ y → ∀ a : ℚ, 0 ≤ a → KltAt p n (Δ + a • D) y → KltAt p n (Δ + a • D + B) y) := by
  intro hP X _ _ _ p n hp hn Δ m G A D P z k h hΔ hklt hm hG hA hD hPz hk hdim hz hh hnum
  obtain ⟨l₁, hl₁⟩ := GlobalTheory.GeneralLift.exists_lift_klt hP X p n hp hn Δ D m G A z hm hG hD hA
  obtain ⟨l, hll, hhl, f₀, hf₀, hgen, δ₀, hδ0, hδ1, hnk⟩ :=
    GlobalTheory.T.exists_global_section_angehrnSiu_inductive_step hP X p n hp hn Δ m G A D P z k h hΔ hklt hm hG hA hD hPz hk hdim hz hh hnum l₁
  obtain ⟨u, hu, huz, hukl⟩ := hl₁ l hll f₀ hf₀
  have hgz : (l • A).GeneratesAt z (f₀ + u) := generatesAt_add_vanishesAt hgen huz
  let g : X.functionFieldˣ := Units.mk0 (f₀ + u) hgz.ne_zero
  have hgv : (g : X.functionField) = f₀ + u := rfl
  have hEeff : (CartierDiv.principal g + l • A).Eff :=
    CartierDiv.mem_sections_iff_eff.1 (hgv ▸ Submodule.add_mem _ hf₀ hu)
  have hl0 : (0 : ℚ) < l := hh.trans hhl
  have hlpos : 0 < l := by exact_mod_cast hl0
  refine ⟨(h / l) • qWeil (CartierDiv.principal g + l • A) 1, δ₀, hδ0, hδ1, ?_, ?_,
    fun δ hδ hδ' x hx => hnk u hu huz g hgv δ hδ hδ' x hx, ?_⟩
  · obtain ⟨a, b, ha0, hb0, hab⟩ : ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ h = a / b := by
      have hnum0 : 0 < h.num := Rat.num_pos.2 hh
      refine ⟨h.num.toNat, h.den, by omega, h.den_pos, ?_⟩
      have e1 : ((h.num.toNat : ℕ) : ℚ) = (h.num : ℚ) := by
        have : ((h.num.toNat : ℕ) : ℤ) = h.num := Int.toNat_of_nonneg hnum0.le
        exact_mod_cast this
      rw [e1, Rat.num_div_den]
    refine ⟨b * l, a • (CartierDiv.principal g + l • A), Nat.mul_pos hb0 hlpos, eff_nsmul hEeff a,
      ?_, fun C hC => ?_⟩
    · funext x
      simp only [Pi.smul_apply, smul_eq_mul, qWeil, mult_nsmul, hab]
      push_cast
      field_simp
    · have hcls : cls (toLB (a • (CartierDiv.principal g + l • A))) (isLB_toLB _) =
          (a * l) • cls (toLB A) (isLB_toLB A) + 0 • cls (toLB A) (isLB_toLB A) := by
        rw [← toPic_apply, ← toPic_apply]
        simp [map_nsmul, toPic_principal, smul_smul, mul_comm]
      have e := interNumRed_of_cls_eq_nsmul_add ℂ X p hp _ _ _ (isLB_toLB _) (isLB_toLB A)
        (isLB_toLB A) (a * l) 0 C hC hcls
      rw [e, hab]
      push_cast
      field_simp
      ring
  · have hoff : Off (qWeil (CartierDiv.principal g + l • A) 1) z :=
      (off_qWeil_iff_notMem_supp X _ 1 z hEeff one_pos).2 (by
        obtain ⟨e, he⟩ := (l • A).exists_isEqn z
        rw [CartierDiv.notMem_supp_iff, ((CartierDiv.isEqn_principal g z).add he).generatesAt_iff,
          one_mul, Units.val_mul, hgv]
        exact (he.generatesAt_iff).1 hgz)
    intro w hw
    simp [hoff w hw]
  · intro y hy a ha hk'
    exact hukl g hgv y hy a (h / l) ha ((div_lt_one hl0).2 hhl) hk'
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartierDivToWeilQDivisorAddOfEffective
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep GlobalTheory.FieldPair

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.QDivSum

theorem sum_eq : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ), IsProjOver p → letI := algebraΓOfHom p; ∀ (D E : CartierDiv X) (a b : ℕ), 0 < a → 0 < b → D.Eff → E.Eff → (b • D + a • E).Eff ∧ qWeil (b • D + a • E) (a * b) = qWeil D a + qWeil E b ∧ ∀ C : Closeds X, IsCompleteCurve ℂ C → (interNumRed ℂ C ![toLB (b • D + a • E)] : ℚ) / ((a * b : ℕ) : ℚ) = (interNumRed ℂ C ![toLB D] : ℚ) / a + (interNumRed ℂ C ![toLB E] : ℚ) / b := by
  intro X _ _ p hp
  letI := algebraΓOfHom p
  intro D E a b ha hb hD hE
  refine ⟨(BoundaryFibre.eff_nsmul hD b).add (BoundaryFibre.eff_nsmul hE a), ?_, ?_⟩
  · funext z
    simp only [qWeil, Pi.add_apply, CartierDiv.mult_add, SmallSecHeight.mult_nsmul]
    have ha' : (a : ℚ) ≠ 0 := by exact_mod_cast ha.ne'
    have hb' : (b : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
    push_cast
    field_simp
  · intro C hC
    have e : cls (toLB (b • D + a • E)) (isLB_toLB _) = b • cls (toLB D) (isLB_toLB D) + a • cls (toLB E) (isLB_toLB E) := by
      rw [← toPic_apply, ← toPic_apply, ← toPic_apply, map_add (f := _), map_nsmul, map_nsmul]
    rw [interNumRed_of_cls_eq_nsmul_add ℂ X p hp _ _ _ (isLB_toLB _) (isLB_toLB D) (isLB_toLB E) b a C hC e]
    have ha' : (a : ℚ) ≠ 0 := by exact_mod_cast ha.ne'
    have hb' : (b : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
    push_cast
    field_simp

end GlobalTheory.QDivSum
end
end

section IsolatedNonKltDivisorRestore
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep GlobalTheory.FieldPair GlobalTheory.LogPair

set_option autoImplicit false
noncomputable section

private theorem exists_isFrame_genericPoint' {k : Type} [Field k] [PerfectField k] {X : Scheme.{0}}
    [IsIntegral X] (p : X ⟶ Sp k) [LocallyOfFiniteType p] (n : ℕ)
    (hn : topologicalKrullDim X = n) :
    ∃ (U : X.Opens) (ω : FormsOn p n U), genericPoint X ∈ U ∧ IsFrame ω := by
  obtain ⟨V, hV, hgV, -⟩ := exists_isAffineOpen_mem_and_subset (x := genericPoint X) (U := ⊤) trivial
  haveI : Nonempty V := ⟨⟨_, hgV⟩⟩
  letI := (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p V).toAlgebra
  have h1 : (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p V).FiniteType :=
    (p.finiteType_appLE (isAffineOpen_top _) hV _).comp
      (.of_surjective _ (ConcreteCategory.bijective_of_isIso _).2)
  haveI : Algebra.FiniteType k Γ(X, V) := h1
  have hd : ringKrullDim Γ(X, V) = n := by
    have h2 := GlobalTheory.OpenDim.topologicalKrullDim_open k p V ⟨_, hgV⟩
    rw [hn] at h2
    rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim, ← h2]
    exact (topologicalKrullDim_eq_of_isEmbedding hV.fromSpec.isOpenEmbedding.isEmbedding
      hV.range_fromSpec).symm
  obtain ⟨s, hs, hsm⟩ := GlobalTheory.AffinePoints.exists_ne_zero_isStandardSmoothOfRelativeDimension
    (K := k) (A := Γ(X, V)) hd
  have hloc := hV.isLocalization_basicOpen s
  have h₁ : (algebraMap k (Localization.Away s)).IsStandardSmoothOfRelativeDimension n :=
    (RingHom.isStandardSmoothOfRelativeDimension_algebraMap n).2 hsm
  have h₂ := RingHom.isStandardSmoothOfRelativeDimension_respectsIso.1 _
    (IsLocalization.algEquiv (Submonoid.powers s) (Localization.Away s)
      Γ(X, X.basicOpen s)).toRingEquiv h₁
  have e : ((IsLocalization.algEquiv (Submonoid.powers s) (Localization.Away s)
      Γ(X, X.basicOpen s)).toRingEquiv.toRingHom.comp (algebraMap k (Localization.Away s))) =
      ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p (X.basicOpen s) := by
    rw [← resG_comp_algX p (X.basicOpen_le s)]
    ext a
    simp [IsScalarTower.algebraMap_apply k Γ(X, V) (Localization.Away s)]
    rfl
  rw [e] at h₂
  obtain ⟨ω, hω⟩ := GlobalTheory.TopForm.exists_isFreeGen h₂
  have hne : X.basicOpen s ≠ ⊥ := fun h => hs ((AlgebraicGeometry.basicOpen_eq_bot_iff s).1 h)
  obtain ⟨x, hx⟩ := (TopologicalSpace.Opens.ne_bot_iff_nonempty _).1 hne
  exact ⟨X.basicOpen s, ω, gen_mem hx, hV.basicOpen s, hω⟩

private theorem finite_setOf_formOrd_ne_zero' : ∀ (k : Type) [Field k] [CharZero k] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp k) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ η : RatForms p n, η ≠ 0 → {z : X | ∃ E : DivOver p, E.IsAt z ∧ (fun ω => @dite ℤ (∃ a, E.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) η ≠ 0}.Finite := by
  intro k _ _ X _ _ _ p n hp hn η hη
  haveI : IsProper p := ((isProjOver_iff_isProper_and_exists_isAmpleLB _).1 hp).1
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  haveI : IsNoetherian X := {}
  obtain ⟨U, ω, hU, hω⟩ := exists_isFrame_genericPoint' p n hn
  have hgen := isFreeGen_formOf hU hω
  have h0 : formOf U hU ω ≠ 0 := fun h =>
    one_ne_zero (hgen.1 (a₁ := 1) (a₂ := 0) (by simp [h]))
  obtain ⟨c, hc⟩ := hgen.2 η
  replace hc : c • formOf U hU ω = η := hc
  have hc0 : c ≠ 0 := fun h => hη (by rw [← hc, h, zero_smul])
  obtain ⟨W, hW, hWu⟩ := (unitAt_genericPoint hc0).exists_nhds
  let B : Closeds X := ⟨((U ⊓ W : X.Opens) : Set X)ᶜ, (U ⊓ W).isOpen.isClosed_compl⟩
  have hB : B ≠ ⊤ := fun h => by
    have hm : genericPoint X ∈ (B : Set X) := by rw [h]; trivial
    exact hm ⟨hU, hW⟩
  refine (GlobalTheory.T.finite_codim_one_points_closed X B hB).subset ?_
  rintro z ⟨E, hE, hne⟩
  refine ⟨hE.coheight_eq_one, fun hz => hne ?_⟩
  obtain ⟨hzU, hzW⟩ := hz
  obtain ⟨a, ha, e⟩ := hWu z hzW
  have hord : E.ord (Units.mk0 c hc0) = 0 :=
    E.ord_eq_zero (u := hE.equiv a) (ha.map hE.equiv) e
  have h1 := E.formOrd_smul hn h0 (Units.mk0 c hc0)
  rw [Units.val_mk0, hc, hord, DivOver.formOrd_formOf_eq_zero hzU hE hω] at h1
  change E.formOrd η = 0
  simpa using h1

section KltGlobalRestore

variable {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} {n : ℕ}
  {Δ : X → ℚ} {η : RatForms p n} {x y : X} {m : ℕ} {g h : X.functionFieldˣ}

private theorem compactSpace_of_isProjOver' {R : Type} [CommRing R] {Y : Scheme.{0}} {f : Y ⟶ Sp R}
    (hf : IsProjOver f) : CompactSpace Y := by
  obtain ⟨N, i, hi, rfl⟩ := hf
  have := isProper_str R N
  have : IsProper (i ≫ PSpace.str R N) := inferInstance
  exact QuasiCompact.compactSpace_of_compactSpace (i ≫ PSpace.str R N)

private theorem unitAt_of_specializes' {z : X} {f : X.functionField} (hz : z ⤳ y) (hf : UnitAt y f) :
    UnitAt z f :=
  (unitAt_iff hf.ne_zero).2 ⟨regAt_of_specializes hz hf.regAt, regAt_of_specializes hz hf.inv.regAt⟩

private theorem ord_eq_zero_of_unitAt' {E : DivOver p} {z : X} (hE : E.IsAt z) {u : X.functionFieldˣ}
    (hu : UnitAt z (u : X.functionField)) : E.ord u = 0 := by
  have h1 := (E.ord_nonneg_iff u).2 ((hE _).2 hu.regAt)
  have h2 := (E.ord_nonneg_iff u⁻¹).2 ((hE _).2 (by rw [Units.val_inv_eq_inv_val]; exact hu.inv.regAt))
  rw [E.ord_inv] at h2
  omega

private theorem isLogEqn_pow' (hg : IsLogEqn p Δ η x m g) (r : ℕ) : IsLogEqn p Δ η x (m * r) (g ^ r) := by
  intro z hz E hE
  rw [E.ord_pow]
  push_cast
  rw [← hg z hz E hE]
  ring

private theorem isLogEqn_of_unitAt' (hg : IsLogEqn p Δ η y m g)
    (hu : UnitAt y ((h : X.functionField) / g)) : IsLogEqn p Δ η y m h := by
  intro z hz E hE
  have h0 : E.ord (h * g⁻¹) = 0 := ord_eq_zero_of_unitAt' hE (by
    rw [Units.val_mul, Units.val_inv_eq_inv_val, ← div_eq_mul_inv]
    exact unitAt_of_specializes' hz hu)
  have e : E.ord h = E.ord g := by
    have := E.ord_mul (h * g⁻¹) g
    rwa [inv_mul_cancel_right, h0, zero_add] at this
  rw [hg z hz E hE, e]

private theorem unitAt_of_isLogEqn' [LocallyOfFiniteType p] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X]
    (hg : IsLogEqn p Δ η y m g) (hh : IsLogEqn p Δ η y m h) :
    UnitAt y ((h : X.functionField) / g) := by
  have h0 : ∀ z, z ⤳ y → ∀ F : DivOver p, F.IsAt z → F.ord (h * g⁻¹) = 0 := by
    intro z hz F hF
    have a := hg z hz F hF
    have b := hh z hz F hF
    rw [F.ord_mul, F.ord_inv]
    have : (F.ord g : ℚ) = F.ord h := a.symm.trans b
    have : F.ord g = F.ord h := by exact_mod_cast this
    omega
  have reg : ∀ v : X.functionFieldˣ, (∀ z, z ⤳ y → ∀ F : DivOver p, F.IsAt z → F.ord v = 0) →
      RegAt y (v : X.functionField) := fun v hv =>
    regAt_of_forall_coheight_eq_one fun z hz h1 =>
      have ⟨F, hF⟩ := DivOver.exists_isAt_of_coheight_eq_one (p := p) h1
      (hF _).1 ((F.ord_nonneg_iff v).1 (hv z hz F hF).ge)
  have hne : (h : X.functionField) / g ≠ 0 := div_ne_zero h.ne_zero g.ne_zero
  have e1 : ((h * g⁻¹ : X.functionFieldˣ) : X.functionField) = h / g := by
    rw [Units.val_mul, Units.val_inv_eq_inv_val, div_eq_mul_inv]
  have e2 : (((h * g⁻¹)⁻¹ : X.functionFieldˣ) : X.functionField) = ((h : X.functionField) / g)⁻¹ := by
    rw [Units.val_inv_eq_inv_val, e1]
  refine (unitAt_iff hne).2 ⟨e1 ▸ reg _ h0, e2 ▸ reg _ fun z hz F hF => ?_⟩
  rw [F.ord_inv, h0 z hz F hF, neg_zero]

private theorem exists_isLogEqn_of_form' [PerfectField k] [LocallyOfFiniteType p]
    (hn : topologicalKrullDim X = n) {η₀ : RatForms p n} (hη₀ : η₀ ≠ 0) (hη : η ≠ 0)
    (hg : IsLogEqn p Δ η x m g) : ∃ g' : X.functionFieldˣ, IsLogEqn p Δ η₀ x m g' := by
  by_cases hE : Nonempty (DivOver p)
  · obtain ⟨E⟩ := hE
    obtain ⟨ω, hω, f₀, e₀, -⟩ := E.isFormOrd_formOrd hn hη₀
    obtain ⟨f, e⟩ := (E.isFreeGen_toRat hω).2 η
    have hf : f ≠ 0 := fun h0 => hη (by rw [← e, h0]; exact zero_smul _ _)
    obtain ⟨c, hc⟩ : ∃ c : X.functionFieldˣ, η = (c : X.functionField) • η₀ :=
      ⟨Units.mk0 f hf * f₀⁻¹, by rw [e₀, smul_smul, ← e]; simp⟩
    refine ⟨g * (c ^ m)⁻¹, fun z hz F hF => ?_⟩
    have a := hg z hz F hF
    rw [hc, F.formOrd_smul hn hη₀] at a
    rw [F.ord_mul, F.ord_inv, F.ord_pow]
    push_cast at a ⊢
    linear_combination a
  · exact ⟨1, fun z _ F _ => (hE ⟨F⟩).elim⟩

private theorem exists_nhds_isLogEqn' [IsLocallyNoetherian X] [CompactSpace X]
    (hfin : {z : X | ∃ E : DivOver p, E.IsAt z ∧ (fun ω => @dite ℤ (∃ a, E.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) η ≠ 0}.Finite)
    (hΔ : (Function.support Δ).Finite) (hg : IsLogEqn p Δ η x m g) :
    ∃ U : X.Opens, x ∈ U ∧ ∀ y ∈ U, IsLogEqn p Δ η y m g := by
  set B : Set X := {z | ∃ E : DivOver p, E.IsAt z ∧ (m : ℚ) * (E.formOrd η + Δ z) ≠ E.ord g}
    with hB
  have hBf : B.Finite := by
    refine ((hfin.union hΔ).union (CartierDiv.principal g).finite_support_mult).subset ?_
    rintro z ⟨E, hE, hne⟩
    by_cases h1 : E.formOrd η = 0
    · by_cases h2 : Δ z = 0
      · right
        show (CartierDiv.principal g).mult z ≠ 0
        rw [(CartierDiv.isEqn_principal g z).mult_eq, ← hE.ord_eq]
        intro h3
        apply hne
        rw [h1, h2, h3]
        simp
      · exact Or.inl (Or.inr h2)
    · exact Or.inl (Or.inl ⟨E, hE, h1⟩)
  have key : ∀ y, y ∈ closure B → ∃ z ∈ B, z ⤳ y := by
    intro y hy
    have hc : closure B = ⋃ z ∈ B, closure {z} := by
      conv_lhs => rw [← Set.biUnion_of_singleton B]
      exact hBf.closure_biUnion _
    rw [hc] at hy
    simp only [Set.mem_iUnion] at hy
    obtain ⟨z, hz, hy⟩ := hy
    exact ⟨z, hz, specializes_iff_mem_closure.2 hy⟩
  refine ⟨⟨(closure B)ᶜ, isClosed_closure.isOpen_compl⟩, show x ∉ closure B from fun hx => ?_,
    fun y hy z hz E hE => ?_⟩
  · obtain ⟨z, ⟨E, hE, hne⟩, hzx⟩ := key x hx
    exact hne (hg z hzx E hE)
  · have hy' : y ∉ closure B := hy
    by_contra hne
    exact hy' (closure_mono (Set.singleton_subset_iff.2 (show z ∈ B from ⟨E, hE, hne⟩))
      (specializes_iff_mem_closure.1 hz))

end KltGlobalRestore

private theorem exists_isLogCanonicalMultiple_of_kltAt' :
    ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X]
      (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p →
      topologicalKrullDim X = n → ∀ Δ : X → ℚ, IsEffQDiv Δ → (∀ y, KltAt p n Δ y) →
      ∃ (m : ℕ) (G : CartierDiv X), 0 < m ∧ IsLogCanonicalMultiple p n Δ m G := by
  intro X _ _ _ p n hP hn Δ hΔ hklt
  classical
  haveI : CompactSpace X := compactSpace_of_isProjOver' hP
  haveI : LocallyOfFiniteType p := isProjOver_locallyOfFiniteType ℂ X p hP
  obtain ⟨η₀, -, -, hη₀, -, -, -⟩ := hklt (genericPoint X)
  have hfin := finite_setOf_formOrd_ne_zero' ℂ X p n hP hn η₀ hη₀
  have h1 : ∀ x, ∃ (m : ℕ) (g : X.functionFieldˣ) (U : X.Opens), 0 < m ∧ x ∈ U ∧
      ∀ y ∈ U, IsLogEqn p Δ η₀ y m g := by
    intro x
    obtain ⟨η, m, g, hη, hm, hg, -⟩ := hklt x
    obtain ⟨g', hg'⟩ := exists_isLogEqn_of_form' hn hη₀ hη hg
    obtain ⟨U, hU, hy⟩ := exists_nhds_isLogEqn' hfin hΔ.finite hg'
    exact ⟨m, g', U, hm, hU, hy⟩
  choose mm gg UU hm hU hy using h1
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x => (UU x : Set X))
    (fun x => (UU x).isOpen) (fun x _ => Set.mem_iUnion.2 ⟨x, hU x⟩)
  set M := ∏ i ∈ t, mm i with hM
  have hM0 : 0 < M := Finset.prod_pos fun i _ => hm i
  have hMd : ∀ i ∈ t, mm i * (M / mm i) = M := fun i hi =>
    Nat.mul_div_cancel' (Finset.dvd_prod_of_mem _ hi)
  have sel : ∀ y : X, ∃ i ∈ t, y ∈ UU i := fun y => by
    have := ht (Set.mem_univ y)
    simpa using this
  choose s hs hsy using sel
  let e : X → X.functionFieldˣ := fun y => gg (s y) ^ (M / mm (s y))
  have he : ∀ y, ∀ w ∈ UU (s y), IsLogEqn p Δ η₀ w M (e y) := fun y w hw => by
    have := isLogEqn_pow' (hy (s y) w hw) (M / mm (s y))
    rwa [hMd _ (hs y)] at this
  let G : CartierDiv X := show cartierGroup X from
    ⟨fun y => germOf y (e y), fun x => ⟨UU (s x), hsy x, e x, fun y hy' =>
      germOf_eq_iff.2 (unitAt_of_isLogEqn' (he y y (hsy y)) (he x y hy'))⟩⟩
  refine ⟨M, G, hM0, η₀, hη₀, fun x g hg => ?_⟩
  have h0 : G.IsEqn x (e x) := rfl
  exact isLogEqn_of_unitAt' (he x x (hsy x)) (h0.iff_unitAt.1 hg)

private theorem isOpen_setOf_forall_specializes_of_finite' {X Y : Type} [TopologicalSpace X] (s : Y → X)
    (P : Y → Prop) (hP : {w | ¬ P w}.Finite) :
    IsOpen {x : X | ∀ w : Y, s w ⤳ x → P w} := by
  have h : {x : X | ∀ w : Y, s w ⤳ x → P w} = (⋃ w ∈ {w | ¬ P w}, closure {s w})ᶜ := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_iUnion, not_exists,
      ← specializes_iff_mem_closure]
    exact ⟨fun h w hw hx => hw (h w hx), fun h w hx => by_contra fun hw => h w hw hx⟩
  rw [h]
  exact (hP.isClosed_biUnion fun w _ => isClosed_closure).isOpen_compl

private theorem isOpen_kltAt_and_lcAt_of_isLogRes' : ∀ (k : Type) [Field k] [CharZero k] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp k) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (Δ : X → ℚ) (η : RatForms p n) (m : ℕ) (G : CartierDiv X) (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (s : Y ⟶ X) [IsDominant s] (K : CartierDiv Y) (B : Closeds Y), IsLogMult p n Δ η m G → IsLogRes p n η m G s K B → IsOpen {x : X | KltAt p n Δ x} ∧ IsOpen {x : X | LcAt p n Δ x} := by
  intro k _ _ X _ _ _ p n hproj hn Δ η m G Y _ _ s _ K B hlm hres
  obtain ⟨N, i, hi, hpi⟩ := hres.proj
  haveI : QuasiCompact (s ≫ p) := hpi ▸ inferInstance
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (s ≫ p)
  have hfin := (pullCart s G - m • K).finite_support_mult
  have hm : (0 : ℤ) < m := by exact_mod_cast hlm.pos
  have hiff := kltAt_lcAt_iff_of_isLogRes k X p n hproj hn Δ η m G Y s K B hlm hres
  constructor
  · have : {x : X | KltAt p n Δ x} =
        {x : X | ∀ w : Y, s w ⤳ x → (pullCart s G - m • K).mult w < m} := by
      ext x
      exact (hiff x).1
    rw [this]
    refine isOpen_setOf_forall_specializes_of_finite' _ _ (hfin.subset fun w hw => ?_)
    simp only [Set.mem_setOf_eq, not_lt] at hw
    simp only [Function.mem_support]
    omega
  · have : {x : X | LcAt p n Δ x} =
        {x : X | ∀ w : Y, s w ⤳ x → (pullCart s G - m • K).mult w ≤ m} := by
      ext x
      exact (hiff x).2
    rw [this]
    refine isOpen_setOf_forall_specializes_of_finite' _ _ (hfin.subset fun w hw => ?_)
    simp only [Set.mem_setOf_eq, not_le] at hw
    simp only [Function.mem_support]
    omega

private theorem isOpen_kltLocus_lcLocus' : GlobalTheory.Published.Principalisation → ∀ (k : Type) [Field k] [CharZero k] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp k) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (Δ : X → ℚ) (m : ℕ) (G : CartierDiv X), 0 < m → IsLogCanonicalMultiple p n Δ m G → IsOpen {x : X | KltAt p n Δ x} ∧ IsOpen {x : X | LcAt p n Δ x} := by
  intro hP k _ _ X _ _ _ p n hp hdim Δ m G hm hG
  obtain ⟨η, hη⟩ := hG.exists_isLogMult hm
  have hZ : (⊥ : Closeds X) ≠ ⊤ := by
    intro h
    obtain ⟨x⟩ := (inferInstance : Nonempty X)
    have : x ∈ ((⊤ : Closeds X) : Set X) := trivial
    rw [← h] at this
    exact this
  obtain ⟨Y, hY, s, hs, K, B, hres, -⟩ := GlobalTheory.T.exists_log_resolution hP k X p n hp hdim η m G hη.ne_zero ⊥ hZ
  haveI := hres.smooth
  haveI : Smooth (s ≫ p) := hres.smooth.smooth
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (s ≫ p)
  exact isOpen_kltAt_and_lcAt_of_isLogRes' k X p n hp hdim Δ η m G Y s K B hη hres

private theorem exists_open_lc_klt_off_point' :
    GlobalTheory.Published.Principalisation → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (Γ : X → ℚ) (m : ℕ) (G : CartierDiv X) (x : X), 0 < m → IsLogCanonicalMultiple p n Γ m G → IsClosed ({x} : Set X) → LcCut p n Γ x 0 → ∃ U : X.Opens, x ∈ U ∧ (∀ y ∈ U, LcAt p n Γ y) ∧ (∀ y ∈ U, y ≠ x → KltAt p n Γ y) := by
  intro hPr X _ _ _ p n hp hdim Γ m G x hm hlc hx hcut
  obtain ⟨hlcx, hnk, hdimz⟩ := hcut
  haveI : AlgebraicGeometry.IsNoetherian X := isNoetherian_of_isProjOver hp
  have hopen := (isOpen_kltLocus_lcLocus' hPr ℂ X p n hp hdim Γ m G hm hlc).1
  set T : Set X := {y | ¬ KltAt p n Γ y} with hT
  have hTc : IsClosed T := by
    rw [← isOpen_compl_iff]
    convert hopen using 1
    ext y; simp [T]
  have hgen : ∀ z ∈ T, z ⤳ x → z = x := by
    intro z hzT hzx
    by_contra hne
    have h0 := hdimz z hzx hzT
    obtain ⟨e, _, he, h1⟩ := GlobalTheory.closure_point_topologicalKrullDim X n z hdim
    have h1' := h1 x hzx (Ne.symm hne)
    rw [he] at h0
    have : (e : WithBot ℕ∞) ≤ ((0 : ℕ) : WithBot ℕ∞) := by exact_mod_cast h0
    have : e ≤ 0 := by exact_mod_cast this
    omega
  obtain ⟨U, hxU, hU⟩ :=
    GlobalTheory.exists_open_inter_eq_singleton_of_no_generisation X T x hTc hx hnk hgen
  refine ⟨U, hxU, ?_, ?_⟩
  · intro y hy
    by_cases hyx : y = x
    · subst hyx; exact hlcx
    · have : y ∉ T := fun h => hyx ((hU y hy).1 h)
      have : KltAt p n Γ y := by simpa [T] using this
      exact this.lcAt
  · intro y hy hyx
    have : y ∉ T := fun h => hyx ((hU y hy).1 h)
    simpa [T] using this

private theorem exists_common_den_nonneg' (q₁ q₂ : ℚ) (h₁ : 0 ≤ q₁) (h₂ : 0 ≤ q₂) :
    ∃ a b M : ℕ, 0 < M ∧ q₁ = a / M ∧ q₂ = b / M := by
  refine ⟨q₁.num.toNat * q₂.den, q₂.num.toNat * q₁.den, q₁.den * q₂.den,
    Nat.mul_pos q₁.den_pos q₂.den_pos, ?_, ?_⟩
  · have e : ((q₁.num.toNat : ℕ) : ℚ) = q₁.num := by
      exact_mod_cast Int.toNat_of_nonneg (Rat.num_nonneg.2 h₁)
    have hd : (q₂.den : ℚ) ≠ 0 := by exact_mod_cast q₂.den_ne_zero
    push_cast
    rw [e, mul_div_mul_right _ _ hd, Rat.num_div_den]
  · have e : ((q₂.num.toNat : ℕ) : ℚ) = q₂.num := by
      exact_mod_cast Int.toNat_of_nonneg (Rat.num_nonneg.2 h₂)
    have hd : (q₁.den : ℚ) ≠ 0 := by exact_mod_cast q₁.den_ne_zero
    push_cast
    rw [e, mul_comm (q₁.den : ℚ) (q₂.den : ℚ), mul_div_mul_right _ _ hd, Rat.num_div_den]

private theorem exists_eff_off_pt_ample_class' : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ), IsProjOver p → letI := algebraΓOfHom p; ∀ (N₀ : LB X) (A : CartierDiv X) (x : X) (r : ℕ) (lam μ : ℚ), N₀.IsLB → IsNef ℂ N₀ → IsAmpleLB (toLB A) → 0 < r → lam ≤ 1 → 0 < μ → ∃ (M : ℕ) (E : CartierDiv X), 0 < M ∧ E.Eff ∧ x ∉ E.supp ∧ ∀ C : Closeds X, IsCompleteCurve ℂ C → (interNumRed ℂ C ![toLB E] : ℚ) / M = (1 - lam) * interNumRed ℂ C ![N₀] / r + μ * interNumRed ℂ C ![toLB A] := by
  intro X _ _ p hp
  letI := algebraΓOfHom p
  intro N₀ A x r lam μ hN₀ hNef hA hr hlam hμ
  have hr' : (0 : ℚ) < r := by exact_mod_cast hr
  obtain ⟨a, b, M, hM, ha, hb⟩ :=
    exists_common_den_nonneg' ((1 - lam) / r) μ (div_nonneg (by linarith) hr'.le) hμ.le
  have hb1 : 1 ≤ b := by
    rcases Nat.eq_zero_or_pos b with h | h
    · rw [h] at hb; simp at hb; linarith
    · exact h
  have hAb : IsAmpleLB (lbPow (toLB A) b) := (isAmpleLB_pow_iff hA.isLB hb1).2 hA
  have hNa : IsNef ℂ (lbPow N₀ a) := hNef.pow hA a
  have hP : (tens (lbPow (toLB A) b) (lbPow N₀ a)).IsLB := isLB_tens hAb.isLB hNa.isLB
  have hPa : IsAmpleLB (tens (lbPow (toLB A) b) (lbPow N₀ a)) :=
    isAmpleLB_of_cls_eq_ample_add_nef ℂ X p hp _ _ _ hAb hNa hP
      (cls_tens hAb.isLB hNa.isLB hP)
  obtain ⟨n, hn, s, hx, -, -⟩ := hPa.exists_affine_le (x := x) (U := ⊤) trivial
  have hgen : genericPoint X ∈ nonzeroLocus s :=
    (genericPoint_specializes x).mem_open (nonzeroLocus s).isOpen hx
  have hLn := isLB_lbPow hPa.isLB n
  refine ⟨M * n, divOfSec hLn s hgen, Nat.mul_pos hM hn, eff_divOfSec_of_sec hLn s hgen,
    notMem_supp_divOfSec.2 hx, fun C hC => ?_⟩
  have hcls : toPic (divOfSec hLn s hgen) = cls _ hLn :=
    (presents_divOfRatSec hLn (isRatSec_ratOfSec s hgen)).toPic_eq
  have e : cls (toLB (divOfSec hLn s hgen)) (isLB_toLB _) =
      (n * a) • cls N₀ hN₀ + (n * b) • cls (toLB A) (isLB_toLB A) := by
    change toPic (divOfSec hLn s hgen) = _
    rw [hcls, cls_lbPow hPa.isLB, cls_tens hAb.isLB hNa.isLB, cls_lbPow (isLB_toLB A),
      cls_lbPow hN₀]
    rw [smul_add, smul_smul, smul_smul, add_comm]
  rw [interNumRed_of_cls_eq_nsmul_add ℂ X p hp _ N₀ (toLB A) (isLB_toLB _) hN₀ (isLB_toLB A)
    (n * a) (n * b) C hC e]
  have hMn : (M : ℚ) ≠ 0 := by exact_mod_cast hM.ne'
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast (Nat.pos_of_ne_zero (by omega)).ne'
  rw [hb, mul_div_right_comm, ha]
  push_cast
  field_simp

private theorem exists_nat_div_of_nonneg' (q : ℚ) (hq : 0 ≤ q) : ∃ a b : ℕ, 0 < b ∧ q = a / b := by
  refine ⟨q.num.toNat, q.den, q.den_pos, ?_⟩
  have h1 : ((q.num.toNat : ℕ) : ℚ) = q.num := by
    exact_mod_cast Int.toNat_of_nonneg (Rat.num_nonneg.2 hq)
  rw [h1]
  exact (Rat.num_div_den q).symm

private theorem exists_qWeil_eq_comb' (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X]
    (p : X ⟶ Sp ℂ) (hp : IsProjOver p) (D E : CartierDiv X) (m k : ℕ) (hm : 0 < m) (hk : 0 < k)
    (hD : D.Eff) (hE : E.Eff) (s t : ℚ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    letI := algebraΓOfHom p
    ∃ (F : CartierDiv X) (M : ℕ), 0 < M ∧ F.Eff ∧ s • qWeil D m + t • qWeil E k = qWeil F M ∧
      ∀ C : Closeds X, IsCompleteCurve ℂ C → (interNumRed ℂ C ![toLB F] : ℚ) / M =
        s * ((interNumRed ℂ C ![toLB D] : ℚ) / m) + t * ((interNumRed ℂ C ![toLB E] : ℚ) / k) := by
  letI := algebraΓOfHom p
  obtain ⟨a, b, hb, rfl⟩ := exists_nat_div_of_nonneg' s hs
  obtain ⟨a', b', hb', rfl⟩ := exists_nat_div_of_nonneg' t ht
  have hm0 : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
  have hk0 : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  have hb0 : (b : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hb.ne'
  have hb0' : (b' : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hb'.ne'
  refine ⟨(a * b' * k) • D + (a' * b * m) • E, b * b' * m * k,
    Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hb hb') hm) hk,
    (GlobalTheory.AmpleStep.eff_nsmul hD _).add (GlobalTheory.AmpleStep.eff_nsmul hE _), ?_, ?_⟩
  · funext z
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, qWeil, CartierDiv.mult_add,
      GlobalTheory.AmpleStep.mult_nsmul]
    push_cast
    field_simp
  · intro C hC
    have e := interNumRed_of_cls_eq_nsmul_add ℂ X p hp (toLB ((a * b' * k) • D + (a' * b * m) • E))
      (toLB D) (toLB E) (isLB_toLB _) (isLB_toLB D) (isLB_toLB E) (a * b' * k) (a' * b * m) C hC
      (by rw [← toPic_apply, ← toPic_apply, ← toPic_apply, map_add (f := _), map_nsmul, map_nsmul])
    rw [e]
    push_cast
    field_simp

private theorem logCanonicalCut_lowers_centre_dimension' : GlobalTheory.Published.Principalisation → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X]
    (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n →
    letI := algebraΓOfHom p;
    ∀ (Δ : X → ℚ) (m : ℕ) (G : CartierDiv X) (r : ℕ) (N₀ : LB X) (hN₀ : N₀.IsLB) (A F : CartierDiv X) (a : ℕ)
      (x z : X) (e : ℕ) (c' : ℝ) (lam μ : ℚ) (m' : ℕ) (D₀ : CartierDiv X),
      IsEffQDiv Δ → (∀ y, KltAt p n Δ y) → 0 < m → IsLogCanonicalMultiple p n Δ m G → 0 < r → IsNef ℂ N₀ →
      IsAmpleLB (toLB A) → 0 < a → toPic F = a • cls N₀ hN₀ →
      IsClosed ({x} : Set X) → z ⤳ x → 1 ≤ e → topologicalKrullDim (closure ({z} : Set X)) = e →
      (z = genericPoint X ∨ IsNkltCentre p n (Δ + qWeil D₀ m') z) → 0 < c' →
      c' ^ e < (interNumRed ℂ (Closeds.closure ({z} : Set X)) (fun _ : Fin e => N₀) : ℝ) / (r : ℝ) ^ e →
      0 < m' → D₀.Eff → 0 < μ → (∀ C : Closeds X, IsCompleteCurve ℂ C → (interNumRed ℂ C ![toLB D₀] : ℚ) / m' = lam * interNumRed ℂ C ![N₀] / r - μ * interNumRed ℂ C ![toLB A]) → LcAt p n (Δ + qWeil D₀ m') x →
      ∃ (lam' μ' : ℚ) (m'' : ℕ) (D₁ : CartierDiv X), 0 < m'' ∧ D₁.Eff ∧ 0 < μ' ∧ (lam' : ℝ) < lam + e / c' ∧
        (∀ C : Closeds X, IsCompleteCurve ℂ C → (interNumRed ℂ C ![toLB D₁] : ℚ) / m'' = lam' * interNumRed ℂ C ![N₀] / r - μ' * interNumRed ℂ C ![toLB A]) ∧ LcCut p n (Δ + qWeil D₁ m'') x (e - 1) := by
  intro hPr X _ _ _ p n hp hn
  intro Δ m G r N₀ hN₀ A F a x z e c' lam μ m' D₀ hΔ hklt hm hG hr hNnef hA ha hF hx hzx he hdim
    hcen hc' hv hm' hD₀ hμ hcurve hlc
  letI := algebraΓOfHom p
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hre : (0 : ℝ) < (r : ℝ) ^ e := pow_pos hr0 e
  have hc'e : (0 : ℝ) < c' ^ e := pow_pos hc' e
  have hIr : c' ^ e * (r : ℝ) ^ e <
      ((interNumRed ℂ (Closeds.closure ({z} : Set X)) fun _ : Fin e => N₀ : ℤ) : ℝ) := by
    rwa [lt_div_iff₀ hre] at hv
  have hIpos : (0 : ℝ) <
      ((interNumRed ℂ (Closeds.closure ({z} : Set X)) fun _ : Fin e => N₀ : ℤ) : ℝ) :=
    lt_trans (mul_pos hc'e hre) hIr
  have he0 : e ≠ 0 := by omega
  have hee : (0 : ℝ) < (e : ℝ) ^ e := pow_pos (by exact_mod_cast (show 0 < e by omega)) e
  obtain ⟨κ, hκ0, hκc, hκI⟩ : ∃ κ : ℚ, (0 : ℝ) < κ ∧ (κ : ℝ) < e / c' ∧
      (e : ℝ) ^ e * (r : ℝ) ^ e < (κ : ℝ) ^ e *
        ((interNumRed ℂ (Closeds.closure ({z} : Set X)) fun _ : Fin e => N₀ : ℤ) : ℝ) := by
    set I : ℝ := ((interNumRed ℂ (Closeds.closure ({z} : Set X)) fun _ : Fin e => N₀ : ℤ) : ℝ)
      with hIdef
    have hx0 : 0 ≤ (e : ℝ) ^ e * (r : ℝ) ^ e / I := by positivity
    have hy0 : 0 ≤ ((e : ℝ) ^ e * (r : ℝ) ^ e / I) ^ ((e : ℝ)⁻¹) := Real.rpow_nonneg hx0 _
    have hye : (((e : ℝ) ^ e * (r : ℝ) ^ e / I) ^ ((e : ℝ)⁻¹)) ^ e = (e : ℝ) ^ e * (r : ℝ) ^ e / I :=
      Real.rpow_inv_natCast_pow hx0 he0
    have hyc : ((e : ℝ) ^ e * (r : ℝ) ^ e / I) ^ ((e : ℝ)⁻¹) < e / c' := by
      by_contra hcon
      push_neg at hcon
      have h1 := pow_le_pow_left₀ (by positivity) hcon e
      rw [hye, div_pow, div_le_div_iff₀ hc'e hIpos] at h1
      nlinarith [mul_lt_mul_of_pos_left hIr hee]
    obtain ⟨κ, hyκ, hκc⟩ := exists_rat_btwn hyc
    refine ⟨κ, lt_of_le_of_lt hy0 hyκ, hκc, ?_⟩
    have h2 := pow_lt_pow_left₀ hyκ hy0 he0
    rw [hye, div_lt_iff₀ hIpos] at h2
    exact h2
  have hκq : (0 : ℚ) < κ := by exact_mod_cast hκ0
  have hκIq : (e : ℚ) ^ e * (r : ℚ) ^ e < κ ^ e *
      ((interNumRed ℂ (Closeds.closure ({z} : Set X)) fun _ : Fin e => N₀ : ℤ) : ℚ) := by
    exact_mod_cast hκI
  have hrq : (0 : ℚ) < r := by exact_mod_cast hr
  have haq : (0 : ℚ) < a := by exact_mod_cast ha
  obtain ⟨s, hs⟩ := exists_nat_gt (2 * κ / (μ * a * r))
  have hsq : (0 : ℚ) < s := lt_trans (by positivity) hs
  have hs0 : 0 < s := by exact_mod_cast hsq
  set h : ℚ := κ / ((s : ℚ) * a * r) with hhdef
  have hh : 0 < h := by positivity
  have hhμ : h < μ / 2 := by
    rw [hhdef, div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ (by positivity)] at hs
    nlinarith
  set A' : CartierDiv X := s • F + A with hA'def
  have hclsA' : cls (toLB A') (isLB_toLB A') = (s * a) • cls N₀ hN₀ + 1 • cls (toLB A) (isLB_toLB A) := by
    rw [← toPic_apply, ← toPic_apply, hA'def, map_add (f := _), map_nsmul, hF, one_nsmul, smul_smul]
  have hA'amp : IsAmpleLB (toLB A') := by
    refine isAmpleLB_of_cls_eq_ample_add_nef ℂ X p hp (toLB A) (lbPow N₀ (s * a)) (toLB A') hA
      (hNnef.pow hA (s * a)) (isLB_toLB A') ?_
    rw [cls_lbPow hN₀, hclsA', one_nsmul, add_comm]
  have hmix := mixExp_interNumRed nefNumerics_outright ℂ X p hp N₀ (toLB A) (toLB A') hN₀
    (isLB_toLB A) (isLB_toLB A') (s * a) 1 (Closeds.closure {z}) e hNnef (IsAmpleLB.isNef (k := ℂ) hA)
    hclsA' (by rw [Closeds.coe_closure]; exact hdim)
  have hmixQ : ((s : ℚ) * a) ^ e *
      ((interNumRed ℂ (Closeds.closure ({z} : Set X)) fun _ : Fin e => N₀ : ℤ) : ℚ) ≤
      ((interNumRed ℂ (Closeds.closure ({z} : Set X)) fun _ : Fin e => toLB A' : ℤ) : ℚ) := by
    exact_mod_cast hmix
  have hcard : (({x} : Finset X).card : ℚ) * (e : ℚ) ^ e < h ^ e *
      ((interNumRed ℂ (Closeds.closure ({z} : Set X)) fun _ : Fin e => toLB A' : ℤ) : ℚ) := by
    rw [Finset.card_singleton, Nat.cast_one, one_mul]
    have hhs : h * ((s : ℚ) * a) = κ / r := by
      rw [hhdef]; field_simp
    calc (e : ℚ) ^ e < (κ / r) ^ e *
          ((interNumRed ℂ (Closeds.closure ({z} : Set X)) fun _ : Fin e => N₀ : ℤ) : ℚ) := by
          rw [div_pow, div_mul_eq_mul_div, lt_div_iff₀ (by positivity)]
          exact hκIq
      _ = h ^ e * (((s : ℚ) * a) ^ e *
          ((interNumRed ℂ (Closeds.closure ({z} : Set X)) fun _ : Fin e => N₀ : ℤ) : ℚ)) := by
          rw [← mul_assoc, ← mul_pow, hhs]
      _ ≤ _ := mul_le_mul_of_nonneg_left hmixQ (by positivity)
  have hDq : IsQCart (qWeil D₀ m') := ⟨m', D₀, hm', hD₀, rfl⟩
  obtain ⟨B, δ₀, hδ₀, -, hBnum, hOff, hnk, hsep⟩ := GlobalTheory.AmpleStep.exists_divisor hPr X p n hp hn Δ m G A'
    (qWeil D₀ m') {x} z e h hΔ hklt hm hG hA'amp hDq
    (fun y hy => by rw [Finset.mem_singleton] at hy; subst hy; exact ⟨hx, hzx⟩) he hdim hcen hh hcard
  obtain ⟨ε, hε0, hεb⟩ := exists_rat_btwn (show (0 : ℝ) < ((e : ℝ) / c' - κ) / (|(lam : ℝ)| + 1) from
    div_pos (by linarith) (by positivity))
  set δ : ℚ := min (min δ₀ (1 / 2)) ε with hδdef
  have hδ0 : 0 < δ := lt_min (lt_min hδ₀ (by norm_num)) (by exact_mod_cast hε0)
  have hδε : δ ≤ ε := min_le_right _ _
  have hδh : δ ≤ 1 / 2 := (min_le_left _ _).trans (min_le_right _ _)
  have hδδ₀ : δ ≤ δ₀ := (min_le_left _ _).trans (min_le_left _ _)
  have hδ1 : δ ≤ 1 := by linarith
  have hδlam : (δ : ℝ) * |(lam : ℝ)| < e / c' - κ := by
    have h1 : (δ : ℝ) ≤ ε := by exact_mod_cast hδε
    have h2 := (lt_div_iff₀ (by positivity : (0 : ℝ) < |(lam : ℝ)| + 1)).1 hεb
    nlinarith [abs_nonneg (lam : ℝ)]
  have hxk : KltAt p n Δ x := hklt x
  have hk1 : KltAt p n (Δ + (1 - δ) • qWeil D₀ m') x :=
    kltAt_add_smul_of_lcAt X p n hp hn Δ (qWeil D₀ m') δ x hDq hxk hlc hδ0 hδ1
  have hnk1 := hnk δ hδ0.le hδδ₀ x (Finset.mem_singleton_self x)
  have hsDq : IsQCart ((1 - δ) • qWeil D₀ m') := by
    obtain ⟨F₁, M₁, hM₁, hF₁, heq, -⟩ := exists_qWeil_eq_comb' X p hp D₀ D₀ m' m' hm' hm' hD₀ hD₀
      (1 - δ) 0 (by linarith) le_rfl
    exact ⟨M₁, F₁, hM₁, hF₁, by rw [← heq, zero_smul, add_zero]⟩
  have hBq : IsQCart B := hBnum.isQCart
  obtain ⟨c, hc0, hc1, hlcc, hnkc⟩ := GlobalTheory.T.exists_rational_logCanonicalThreshold_at_point hPr X p n hp hn Δ m G ((1 - δ) • qWeil D₀ m') B x
    hm hG hsDq hBq hk1 hnk1
  have hcut := logCanonicalCut_of_step X p n hp hn Δ (qWeil D₀ m') B δ c x z (e - 1) hxk hDq hBq hlc hδ0 hδ1
    hc1 hOff hsep (by rw [Nat.sub_add_cancel he]; exact hdim) hlcc hnkc
  obtain ⟨m₁, B₀, hm₁, hB₀, rfl, hBn⟩ := hBnum
  obtain ⟨D₂, m'', hm'', hD₂, heq, hnum⟩ := exists_qWeil_eq_comb' X p hp D₀ B₀ m' m₁ hm' hm₁ hD₀ hB₀
    (1 - δ) c (by linarith) hc0.le
  refine ⟨(1 - δ) * lam + c * κ, (1 - δ) * μ - c * h, m'', D₂, hm'', hD₂, ?_, ?_, ?_, ?_⟩
  · nlinarith
  · have t1 : -((δ : ℝ) * lam) ≤ δ * |(lam : ℝ)| := by
      rw [← mul_neg]; exact mul_le_mul_of_nonneg_left (neg_le_abs _) (by exact_mod_cast hδ0.le)
    have t2 : (c : ℝ) * κ ≤ κ := by
      have : (c : ℝ) ≤ 1 := by exact_mod_cast hc1
      nlinarith
    push_cast
    nlinarith
  · intro C hC
    have eA' := interNumRed_of_cls_eq_nsmul_add ℂ X p hp (toLB A') N₀ (toLB A) (isLB_toLB A') hN₀
      (isLB_toLB A) (s * a) 1 C hC hclsA'
    rw [hnum C hC, hcurve C hC, hBn C hC, eA']
    have hr0' : (r : ℚ) ≠ 0 := hrq.ne'
    have hs0' : (s : ℚ) ≠ 0 := hsq.ne'
    have ha0' : (a : ℚ) ≠ 0 := haq.ne'
    rw [hhdef]
    push_cast
    field_simp
    ring
  · rw [← heq, ← add_assoc]
    exact hcut

set_option maxHeartbeats 1000000 in
private theorem exists_ample_eff_kltAt_start' : GlobalTheory.Published.Principalisation → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X]
    (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n →
    letI := algebraΓOfHom p;
    ∀ (Δ : X → ℚ) (r : ℕ) (N₀ : LB X) (hN₀ : N₀.IsLB) (β : ℚ),
      IsEffQDiv Δ → (∀ y, KltAt p n Δ y) → 0 < r → IsNef ℂ N₀ → IsBig ℂ N₀ → 0 < β →
      ∃ (A F : CartierDiv X) (a : ℕ), IsAmpleLB (toLB A) ∧ 0 < a ∧ toPic F = a • cls N₀ hN₀ ∧
        ∃ (lam μ : ℚ) (m' : ℕ) (D₀ : CartierDiv X), 0 < m' ∧ D₀.Eff ∧ 0 < μ ∧ lam < β ∧
          (∀ C : Closeds X, IsCompleteCurve ℂ C → (interNumRed ℂ C ![toLB D₀] : ℚ) / m' = lam * interNumRed ℂ C ![N₀] / r - μ * interNumRed ℂ C ![toLB A]) ∧ ∀ y, KltAt p n (Δ + qWeil D₀ m') y := by
  intro hPr X _ _ _ p n hp hn
  letI := algebraΓOfHom p
  intro Δ r N₀ hN₀ β hΔ hklt hr hnef hbig hβ
  obtain ⟨H, hH⟩ := exists_isAmpleLB_of_isProjOver hp
  obtain ⟨A, hA⟩ := toPic_surjective (cls H hH.isLB)
  have hAamp : IsAmpleLB (toLB A) := by
    rw [toPic_apply] at hA
    exact hH.of_lbIso (isLB_toLB A) ((cls_eq_iff (isLB_toLB A) hH.isLB).1 hA)
  obtain ⟨a, E₀, ha, hE₀, hKod⟩ := GlobalTheory.KodairaLemma.exists_nsmul_cls_eq_add_toPic_of_isBig ℂ X p hp N₀ (toLB A) hbig hAamp
  obtain ⟨F, hF⟩ := toPic_surjective (a • cls N₀ hN₀)
  obtain ⟨m, G, hm, hG⟩ := exists_isLogCanonicalMultiple_of_kltAt' X p n hp hn Δ hΔ hklt
  have hB : IsQCart (qWeil E₀ 1) := ⟨1, E₀, one_pos, hE₀, rfl⟩
  obtain ⟨c₀, hc₀, hc₀k⟩ := GlobalTheory.T.exists_pos_klt_add_smul_effective_divisor hPr X p n hp hn Δ m G (qWeil E₀ 1) hm hG hklt hB
  set q : ℕ := ⌈1 / c₀ + (a : ℚ) * r / β⌉₊ + 1 with hq
  have hqpos : (0 : ℚ) < q := by positivity
  have hqgt : 1 / c₀ + (a : ℚ) * r / β < q := by
    have := Nat.le_ceil (1 / c₀ + (a : ℚ) * r / β)
    rw [hq]; push_cast; linarith
  have hara : (0 : ℚ) ≤ (a : ℚ) * r / β := by positivity
  have hinv : (0 : ℚ) < 1 / c₀ := by positivity
  have h1 : 1 / (q : ℚ) ≤ c₀ := by
    rw [div_le_iff₀ hqpos]
    have : 1 / c₀ < q := by linarith
    rw [div_lt_iff₀ hc₀] at this
    linarith
  have h2 : (a : ℚ) * r / q < β := by
    have : (a : ℚ) * r / β < q := by linarith
    rw [div_lt_iff₀ hβ] at this
    rw [div_lt_iff₀ hqpos]
    linarith
  refine ⟨A, F, a, hAamp, ha, hF, (a : ℚ) * r / q, 1 / q, q, E₀, by omega, hE₀, by positivity, h2, ?_, ?_⟩
  · intro C hC
    have e1 := interNumRed_of_cls_eq_nsmul_add ℂ X p hp (lbPow N₀ a) (toLB A) (toLB E₀)
      (isLB_lbPow hN₀ a) (isLB_toLB A) (isLB_toLB E₀) 1 1 C hC (by
        rw [cls_lbPow hN₀ a, one_smul, one_smul, ← toPic_apply]
        exact hKod)
    have e2 := interNumRed_of_cls_eq_nsmul_add ℂ X p hp (lbPow N₀ a) N₀ N₀
      (isLB_lbPow hN₀ a) hN₀ hN₀ a 0 C hC (by rw [cls_lbPow hN₀ a, zero_smul, add_zero])
    have e3 : (interNumRed ℂ C ![toLB E₀] : ℚ) = a * interNumRed ℂ C ![N₀] - interNumRed ℂ C ![toLB A] := by
      have : interNumRed ℂ C ![toLB E₀] = a * interNumRed ℂ C ![N₀] - interNumRed ℂ C ![toLB A] := by
        rw [e2] at e1; push_cast at e1; linarith
      exact_mod_cast this
    rw [e3]
    have hr' : (r : ℚ) ≠ 0 := by exact_mod_cast hr.ne'
    field_simp
  · intro y
    have k := (kltAt_lcAt_of_le_coeff X p n hp hn Δ (qWeil E₀ 1) (1 / q) c₀ y hB h1).1 (hc₀k y)
    convert k using 2
    ext z
    simp [qWeil, div_eq_mul_inv, mul_comm]

private theorem exists_lcCut_induction' : GlobalTheory.Published.Principalisation → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X]
    (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → 1 ≤ n →
    letI := algebraΓOfHom p;
    ∀ (Δ : X → ℚ) (r : ℕ) (N₀ : LB X) (x : X) (c : ℕ → ℝ),
      IsEffQDiv Δ → (∀ y, KltAt p n Δ y) → 0 < r → N₀.IsLB → IsNef ℂ N₀ → IsBig ℂ N₀ →
      IsClosed ({x} : Set X) → (∀ e ∈ Finset.Icc 1 n, 0 < c e) →
      (∀ (Z : Closeds X) (e : ℕ), IsIrreducible (Z : Set X) → x ∈ Z → 1 ≤ e →
        topologicalKrullDim (Z : Set X) = e →
        c e ^ e < (interNumRed ℂ Z fun _ : Fin e => N₀ : ℝ) / (r : ℝ) ^ e) →
      ∃ A : CartierDiv X, IsAmpleLB (toLB A) ∧ ∀ j, j < n → ∃ (j' : ℕ) (lam μ : ℚ) (m' : ℕ) (D₀ : CartierDiv X),
        j' ≤ j ∧ 0 < m' ∧ D₀.Eff ∧ 0 < μ ∧ (lam : ℝ) < ∑ e ∈ Finset.Icc (j' + 1) n, (e : ℝ) / c e ∧
        (∀ C : Closeds X, IsCompleteCurve ℂ C → (interNumRed ℂ C ![toLB D₀] : ℚ) / m' =
          lam * interNumRed ℂ C ![N₀] / r - μ * interNumRed ℂ C ![toLB A]) ∧
        LcCut p n (Δ + qWeil D₀ m') x j' := by
  intro hPr X _ _ _ p n hP hn hn1
  letI := algebraΓOfHom p
  intro Δ r N₀ x c hΔ hklt hr hN₀ hnef hbig hx hc hZ
  obtain ⟨m, G, hm, hG⟩ := exists_isLogCanonicalMultiple_of_kltAt' X p n hP hn Δ hΔ hklt
  have hcpos : ∀ e, 1 ≤ e → e ≤ n → 0 < c e := fun e h1 h2 => hc e (Finset.mem_Icc.2 ⟨h1, h2⟩)
  have hgen : closure ({genericPoint X} : Set X) = Set.univ := (genericPoint_spec X).def
  have hdimX : topologicalKrullDim (closure ({genericPoint X} : Set X)) = n := by
    rw [hgen, ← hn]
    exact ((Homeomorph.Set.univ X).isHomeomorph).topologicalKrullDim_eq
  have hcn := hZ (Closeds.closure ({genericPoint X} : Set X)) n isIrreducible_singleton.closure
    (by simpa using specializes_iff_mem_closure.1 (genericPoint_specializes x)) hn1 hdimX
  obtain ⟨c', hc'v, hc'gt⟩ : ∃ c' : ℝ, c' ^ n < (interNumRed ℂ (Closeds.closure ({genericPoint X} : Set X))
      (fun _ : Fin n => N₀) : ℝ) / (r : ℝ) ^ n ∧ c n < c' := by
    have hev := ((continuous_pow n).tendsto (c n)).eventually_lt_const hcn
    exact ((hev.filter_mono nhdsWithin_le_nhds).and
      (self_mem_nhdsWithin : Set.Ioi (c n) ∈ nhdsWithin (c n) (Set.Ioi (c n)))).exists
  have hcn0 := hcpos n hn1 le_rfl
  have hc'0 : 0 < c' := hcn0.trans hc'gt
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have hlt : (n : ℝ) / c' < n / c n := div_lt_div_of_pos_left hnpos hcn0 hc'gt
  obtain ⟨β, hβ0, hβ⟩ := exists_rat_btwn (sub_pos.2 hlt)
  have hβ0' : (0 : ℚ) < β := by exact_mod_cast hβ0
  obtain ⟨A, F, a, hA, ha, hF, lam₀, μ₀, m₀, D₀, hm₀, hD₀, hμ₀, hlam₀, hnum₀, hklt₀⟩ :=
    exists_ample_eff_kltAt_start' hPr X p n hP hn Δ r N₀ hN₀ β hΔ hklt hr hnef hbig hβ0'
  refine ⟨A, hA, ?_⟩
  have key : ∀ a : WithBot ℕ∞, ∀ j : ℕ, (j : WithBot ℕ∞) < a → a ≤ ((j + 1 : ℕ) : WithBot ℕ∞) →
      a = ((j + 1 : ℕ) : WithBot ℕ∞) := by
    intro a j h1 h2
    induction a using WithBot.recBotCoe with
    | bot => simp at h1
    | coe a =>
      induction a using ENat.recTopCoe with
      | top =>
        exfalso
        have h3 : ((⊤ : ℕ∞) : WithBot ℕ∞) ≤ (((j + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := h2
        exact absurd (WithBot.coe_le_coe.1 h3) (by simp)
      | coe k =>
        have h1' : j < k := by exact_mod_cast h1
        have h2' : k ≤ j + 1 := by exact_mod_cast h2
        have : k = j + 1 := by omega
        subst this; rfl
  have hsplit : ∀ j, j + 1 ≤ n → ∑ e ∈ Finset.Icc (j + 1) n, (e : ℝ) / c e =
      (j + 1 : ℕ) / c (j + 1) + ∑ e ∈ Finset.Icc (j + 2) n, (e : ℝ) / c e := by
    intro j hj
    rw [← Finset.insert_Icc_add_one_left_eq_Icc hj, Finset.sum_insert (by simp)]
    first | rfl | (push_cast; ring_nf) | simp [add_assoc]
  let S : ℕ → Prop := fun j => ∃ (j' : ℕ) (lam μ : ℚ) (m' : ℕ) (D₀ : CartierDiv X),
        j' ≤ j ∧ 0 < m' ∧ D₀.Eff ∧ 0 < μ ∧ (lam : ℝ) < ∑ e ∈ Finset.Icc (j' + 1) n, (e : ℝ) / c e ∧
        (∀ C : Closeds X, IsCompleteCurve ℂ C → (interNumRed ℂ C ![toLB D₀] : ℚ) / m' =
          lam * interNumRed ℂ C ![N₀] / r - μ * interNumRed ℂ C ![toLB A]) ∧
        LcCut p n (Δ + qWeil D₀ m') x j'
  have first : S (n - 1) := by
    obtain ⟨lam₁, μ₁, m₁, D₁, hm₁, hD₁, hμ₁, hlam₁, hnum₁, hcut₁⟩ :=
      logCanonicalCut_lowers_centre_dimension' hPr X p n hP hn Δ m G r N₀ hN₀ A F a x (genericPoint X) n c' lam₀ μ₀ m₀ D₀ hΔ hklt hm hG hr
        hnef hA ha hF hx (genericPoint_specializes x) hn1 hdimX (Or.inl rfl) hc'0 hc'v hm₀ hD₀ hμ₀
        hnum₀ (hklt₀ x).lcAt
    refine ⟨n - 1, lam₁, μ₁, m₁, D₁, le_rfl, hm₁, hD₁, hμ₁, ?_, hnum₁, hcut₁⟩
    rw [Nat.sub_add_cancel hn1, Finset.Icc_self, Finset.sum_singleton]
    have : (lam₀ : ℝ) < β := by exact_mod_cast hlam₀
    linarith
  have step : ∀ j, j + 1 < n → S (j + 1) → S j := by
    intro j hj ⟨j', lam, μ, m', D₁, hj', hm', hD₁, hμ, hlam, hnum, hcut⟩
    by_cases hle : j' ≤ j
    · exact ⟨j', lam, μ, m', D₁, hle, hm', hD₁, hμ, hlam, hnum, hcut⟩
    obtain rfl : j' = j + 1 := by omega
    have hsj := hsplit j (by omega)
    have hcj := hcpos (j + 1) (by omega) (by omega)
    have hpos : (0 : ℝ) < ((j + 1 : ℕ) : ℝ) / c (j + 1) := div_pos (by positivity) hcj
    obtain ⟨hlc, hnk, hdim⟩ := hcut
    by_cases hall : ∀ z, z ⤳ x → ¬ KltAt p n (Δ + qWeil D₁ m') z →
        topologicalKrullDim (closure ({z} : Set X)) ≤ j
    · refine ⟨j, lam, μ, m', D₁, le_rfl, hm', hD₁, hμ, ?_, hnum, hlc, hnk, hall⟩
      rw [hsj]; linarith
    push_neg at hall
    obtain ⟨z, hzx, hzk, hzd⟩ := hall
    have hq : IsQCart (qWeil D₁ m') := ⟨m', D₁, hm', hD₁, rfl⟩
    obtain ⟨w, hwz, hw⟩ := GlobalTheory.T.exists_nonKltCentre_of_not_klt_after_adding X p n hP hn Δ (qWeil D₁ m') z hq (hklt z) hzk
    have hwx : w ⤳ x := hwz.trans hzx
    have hwk : ¬ KltAt p n (Δ + qWeil D₁ m') w :=
      GlobalTheory.PairStep.not_kltAt_of_isNkltCentre X p n hP hn _ w w hw specializes_rfl
    have hsub : closure ({z} : Set X) ⊆ closure ({w} : Set X) := specializes_iff_closure_subset.1 hwz
    have hmono : topologicalKrullDim (closure ({z} : Set X)) ≤ topologicalKrullDim (closure ({w} : Set X)) :=
      (Topology.IsEmbedding.inclusion hsub).isInducing.topologicalKrullDim_le
    have hwd : topologicalKrullDim (closure ({w} : Set X)) = ((j + 1 : ℕ) : WithBot ℕ∞) :=
      key _ j (hzd.trans_le hmono) (hdim w hwx hwk)
    have hZw := hZ (Closeds.closure ({w} : Set X)) (j + 1) isIrreducible_singleton.closure
      (by simpa using specializes_iff_mem_closure.1 hwx) (by omega) hwd
    obtain ⟨lam', μ', m'', D₂, hm'', hD₂, hμ', hlam', hnum', hcut'⟩ :=
      logCanonicalCut_lowers_centre_dimension' hPr X p n hP hn Δ m G r N₀ hN₀ A F a x w (j + 1) (c (j + 1)) lam μ m' D₁ hΔ hklt hm hG hr
        hnef hA ha hF hx hwx (by omega) hwd (Or.inr hw) hcj hZw hm' hD₁ hμ hnum hlc
    refine ⟨j, lam', μ', m'', D₂, le_rfl, hm'', hD₂, hμ', ?_, hnum', by simpa using hcut'⟩
    rw [hsj]
    push_cast at hlam' ⊢
    linarith
  have hall : ∀ i, i < n → S (n - 1 - i) := by
    intro i
    induction i with
    | zero => intro _; simpa using first
    | succ i ih =>
      intro hi
      have h := ih (by omega)
      rw [show n - 1 - i = (n - 1 - (i + 1)) + 1 by omega] at h
      exact step _ (by omega) h
  intro j hj
  have h := hall (n - 1 - j) (by omega)
  rwa [show n - 1 - (n - 1 - j) = j by omega] at h

private theorem exists_isolated_of_lcCut_zero' : GlobalTheory.Published.Principalisation → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X]
    (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → 1 ≤ n →
    letI := algebraΓOfHom p;
    ∀ (Δ : X → ℚ) (r : ℕ) (N₀ : LB X) (x : X) (c : ℕ → ℝ),
      IsEffQDiv Δ → (∀ y, KltAt p n Δ y) → 0 < r → N₀.IsLB → IsNef ℂ N₀ → IsBig ℂ N₀ →
      IsClosed ({x} : Set X) → (∀ e ∈ Finset.Icc 1 n, 0 < c e) →
      (∀ (Z : Closeds X) (e : ℕ), IsIrreducible (Z : Set X) → x ∈ Z → 1 ≤ e →
        topologicalKrullDim (Z : Set X) = e →
        c e ^ e < (interNumRed ℂ Z fun _ : Fin e => N₀ : ℝ) / (r : ℝ) ^ e) →
      ∑ e ∈ Finset.Icc 1 n, (e : ℝ) / c e ≤ 1 →
      ∀ (A : CartierDiv X) (lam μ : ℚ) (m' : ℕ) (D₀ : CartierDiv X), IsAmpleLB (toLB A) → 0 < m' → D₀.Eff → 0 < μ →
        (lam : ℝ) < ∑ e ∈ Finset.Icc 1 n, (e : ℝ) / c e →
        (∀ C : Closeds X, IsCompleteCurve ℂ C → (interNumRed ℂ C ![toLB D₀] : ℚ) / m' =
          lam * interNumRed ℂ C ![N₀] / r - μ * interNumRed ℂ C ![toLB A]) →
        LcCut p n (Δ + qWeil D₀ m') x 0 →
      ∃ (m : ℕ) (D₀ : CartierDiv X) (U : X.Opens), 0 < m ∧ D₀.Eff ∧
        (∀ C : Closeds X, IsCompleteCurve ℂ C →
          (interNumRed ℂ C ![toLB D₀] : ℚ) / m = interNumRed ℂ C ![N₀] / r) ∧
        x ∈ U ∧ (∀ y ∈ U, LcAt p n (Δ + qWeil D₀ m) y) ∧
        (∀ y ∈ U, y ≠ x → KltAt p n (Δ + qWeil D₀ m) y) ∧ ¬ KltAt p n (Δ + qWeil D₀ m) x := by
  intro hPr X _ _ _ p n hp hn hn1
  letI := algebraΓOfHom p
  intro Δ r N₀ x c hΔ hklt hr hN₀ hnef hbig hx hc hcZ hsum A lam μ m' D₀ hA hm' hD₀ hμ hlam hnum hcut
  obtain ⟨m, G, hm, hG⟩ := exists_isLogCanonicalMultiple_of_kltAt' X p n hp hn Δ hΔ hklt
  have hG' := GlobalTheory.isLogCanonicalMultiple_add_qWeil X p n Δ m m' G D₀ hm hm' hG
  obtain ⟨U, hxU, hlc, hkl⟩ := exists_open_lc_klt_off_point' hPr X p n hp hn (Δ + qWeil D₀ m') (m * m') (m' • G + m • D₀) x
    (Nat.mul_pos hm hm') hG' hx hcut
  have hlam1 : lam ≤ 1 := by
    have : (lam : ℝ) ≤ 1 := (hlam.trans_le hsum).le
    exact_mod_cast this
  obtain ⟨M, E, hM, hE, hxE, hEnum⟩ := exists_eff_off_pt_ample_class' X p hp N₀ A x r lam μ hN₀ hnef hA hr hlam1 hμ
  obtain ⟨hD, hqW, hDnum⟩ := GlobalTheory.QDivSum.sum_eq X p hp D₀ E m' M hm' hM hD₀ hE
  have hoff : ∀ y, y ∉ E.supp → Off (qWeil E M) y := fun y hy =>
    (GlobalTheory.T.weilQDivisorAvoidsPoint_cartier_iff_notMem_supp X E M y hE hM).2 hy
  have heq : Δ + qWeil (M • D₀ + m' • E) (m' * M) = (Δ + qWeil D₀ m') + (1 : ℚ) • qWeil E M := by
    rw [hqW, one_smul, add_assoc]
  let V : X.Opens := ⟨(E.supp : Set X)ᶜ, E.supp.isClosed.isOpen_compl⟩
  refine ⟨m' * M, M • D₀ + m' • E, U ⊓ V, Nat.mul_pos hm' hM, hD, ?_, ⟨hxU, hxE⟩, ?_, ?_, ?_⟩
  · intro C hC
    have h1 := hDnum C hC
    have h2 := hnum C hC
    have h3 := hEnum C hC
    push_cast at h1 ⊢
    rw [h1, h2, h3]
    ring
  · intro y hy
    rw [heq]
    exact ((GlobalTheory.PairStep.off_add_smul X p n _ _ 1 y (hoff y hy.2)).2.1).2 (hlc y hy.1)
  · intro y hy hyx
    rw [heq]
    exact ((GlobalTheory.PairStep.off_add_smul X p n _ _ 1 y (hoff y hy.2)).1).2 (hkl y hy.1 hyx)
  · rw [heq]
    exact fun h => hcut.2.1 (((GlobalTheory.PairStep.off_add_smul X p n _ _ 1 x (hoff x hxE)).1).1 h)

private theorem isolatedNonKltDivisor_of_principalisation' :
    GlobalTheory.Published.Principalisation → GlobalTheory.Published.IsolatedNonKltDivisor := by
  intro hP X _ _ _ p n hproj hdim hn Δ r N₀ x c hΔ hklt hr hnef hbig hx hc hvol hsum
  letI := algebraΓOfHom p
  have hLB : N₀.IsLB := hnef.isLB
  obtain ⟨A, hA, hj⟩ := exists_lcCut_induction' hP X p n hproj hdim hn Δ r N₀ x c hΔ hklt hr hLB hnef hbig hx hc hvol
  obtain ⟨j', lam, μ, m', D₀, hj', hm', hD₀, hμ, hlam, hnum, hcut⟩ := hj 0 (by omega)
  obtain rfl : j' = 0 := Nat.le_zero.mp hj'
  exact exists_isolated_of_lcCut_zero' hP X p n hproj hdim hn Δ r N₀ x c hΔ hklt hr hLB hnef hbig hx hc hvol hsum
    A lam μ m' D₀ hA hm' hD₀ hμ (by simpa using hlam) hnum hcut

end
end IsolatedNonKltDivisorRestore

namespace NadelVanishingSeparation.NSI

theorem nadelVanishingPair : GlobalTheory.Published.NadelVanishingPair :=
  GlobalTheory.T.nadel_vanishing_pairs_of_principalisation PositivityTheory.ResPlug.WeightsCompactStabilizer.principalisation_closed

theorem isolatedNonKltDivisor : GlobalTheory.Published.IsolatedNonKltDivisor :=
  isolatedNonKltDivisor_of_principalisation' PositivityTheory.ResPlug.WeightsCompactStabilizer.principalisation_closed

theorem nadelVanishingAndNonKltDivisor : GlobalTheory.Published.NadelVanishingAndNonKltDivisor :=
  ⟨nadelVanishingPair, isolatedNonKltDivisor⟩

end NadelVanishingSeparation.NSI
