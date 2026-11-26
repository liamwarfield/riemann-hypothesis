module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBertiniPolyDiscrepancySncBoundary
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.ExistsLogResolution

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KawamataLogTerminalAddGeneralMemberLinearSystem
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KawamataLogTerminalAddGeneralMemberLinearSystem
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GeneralMember

variable {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]

theorem regAt_functionFieldMap (q : Y ⟶ X) [IsDominant q] (y : Y) {f : X.functionField}
    (h : RegAt (q y) f) : RegAt y (functionFieldMap q f) := by
  obtain ⟨a, rfl⟩ := h
  exact ⟨q.stalkMap y a, (functionFieldMap_algebraMap q y a).symm⟩

theorem unitAt_functionFieldMap (q : Y ⟶ X) [IsDominant q] (y : Y) {f : X.functionField}
    (h : UnitAt (q y) f) : UnitAt y (functionFieldMap q f) := by
  obtain ⟨a, ha, rfl⟩ := h
  exact ⟨q.stalkMap y a, ha.map _, (functionFieldMap_algebraMap q y a).symm⟩

theorem supp_nsmul_le (D : CartierDiv X) (r : ℕ) : (r • D).supp ≤ D.supp := by
  induction r with
  | zero => rw [zero_smul, CartierDiv.supp_eq_bot_iff.2 rfl]; exact bot_le
  | succ r ih => rw [succ_nsmul]; exact (CartierDiv.supp_add_le _ _).trans (sup_le ih le_rfl)

theorem functionFieldMap_mem_sections (q : Y ⟶ X) [IsDominant q] {A : CartierDiv X}
    {f : X.functionField} (h : f ∈ A.sections) : functionFieldMap q f ∈ (pullCart q A).sections := by
  refine CartierDiv.mem_sections.2 fun y => ?_
  obtain ⟨g, hg⟩ := A.exists_isEqn (q y)
  have h1 := hg.regularAt_iff.1 (CartierDiv.mem_sections.1 h (q y))
  refine ⟨fnPull q g, isEqn_pullCart q hg, ?_⟩
  have := regAt_functionFieldMap q y h1
  rwa [map_mul] at this

theorem generatesAt_pullCart (q : Y ⟶ X) [IsDominant q] {A : CartierDiv X} {y : Y}
    {f : X.functionField} (h : A.GeneratesAt (q y) f) :
    (pullCart q A).GeneratesAt y (functionFieldMap q f) := by
  obtain ⟨g, hg⟩ := A.exists_isEqn (q y)
  refine ⟨fnPull q g, isEqn_pullCart q hg, ?_⟩
  have := unitAt_functionFieldMap q y (hg.generatesAt_iff.1 h)
  rwa [map_mul] at this

variable [IsLocallyNoetherian X]

theorem isLogMult_add {p : X ⟶ Sp ℂ} {n : ℕ} {Δ : X → ℚ} {η : RatForms p n} {m m' b e : ℕ}
    {G D₀ : CartierDiv X} {a : ℚ} (hG : IsLogMult p n Δ η m G) (hm' : 0 < m') (he : 0 < e)
    (hab : a = b / e) :
    IsLogMult p n (Δ + a • qWeil D₀ m') η (m * (e * m')) ((e * m') • G + m • (b • D₀)) := by
  refine ⟨hG.ne_zero, Nat.mul_pos hG.pos (Nat.mul_pos he hm'), fun x g hg z hz E hE => ?_⟩
  obtain ⟨V, hV, hgV⟩ := hg.exists_nhds
  obtain ⟨g₁, hg₁⟩ := G.exists_isEqn z
  obtain ⟨d, hd⟩ := D₀.exists_isEqn z
  have h3 := ((hgV z (hz.mem_open V.isOpen hV)).mult_eq.symm.trans
    ((hg₁.nsmul (e * m')).add ((hd.nsmul b).nsmul m)).mult_eq)
  rw [← hE.ord_eq, ← hE.ord_eq, E.ord_mul, E.ord_pow, E.ord_pow, E.ord_pow] at h3
  have h4 := hG.eqn z g₁ hg₁ z specializes_rfl E hE
  have hd' := hd.mult_eq
  rw [← hE.ord_eq] at hd'
  have h1 : (m' : ℚ) ≠ 0 := by exact_mod_cast hm'.ne'
  have h2 : (e : ℚ) ≠ 0 := by exact_mod_cast he.ne'
  rw [Pi.add_apply, Pi.smul_apply, smul_eq_mul, qWeil, hd', h3, hab]
  push_cast
  rw [← h4]
  field_simp
  ring

end GlobalTheory.GeneralMember


open GlobalTheory.GeneralMember in
theorem GlobalTheory.PairStep.kltAt_add_general_member : GlobalTheory.Published.Principalisation → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (Δ D : X → ℚ) (m : ℕ) (G A : CartierDiv X) (ι : Type) [Fintype ι] (s : ι → X.functionField), 0 < m → IsLogCanonicalMultiple p n Δ m G → IsQCart D → (∀ i, s i ∈ A.sections) → ∃ Q : MvPolynomial ι ℂ, Q ≠ 0 ∧ ∀ u : ι → ℂ, MvPolynomial.eval u Q ≠ 0 → ∀ t : X.functionFieldˣ, (t : X.functionField) = ∑ i, Cartier.constFn p (u i) * s i → ∀ y : X, (∃ i, A.GeneratesAt y (s i)) → ∀ a c : ℚ, 0 ≤ a → c < 1 → KltAt p n (Δ + a • D) y → KltAt p n (Δ + a • D + c • qWeil (GlobalTheory.Cartier.CartierDiv.principal t + A) 1) y := by
  intro hP X _ _ _ p n hproj hn Δ D m G A ι _ s hm hG hD hs
  obtain ⟨η, hη⟩ := hG.exists_isLogMult hm
  obtain ⟨m', D₀, hm', -, rfl⟩ := hD
  obtain ⟨Y, hY, π, hπ, K, B, hres, hB⟩ :=
    GlobalTheory.T.exists_log_resolution hP ℂ X p n hproj hn η m G hη.ne_zero D₀.supp D₀.supp_ne_top
  haveI : IsNoetherian Y := isNoetherian_of_isProjOver hres.proj
  haveI := hres.smooth
  haveI : IsProper p := ((isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hproj).1
  haveI : IsProper (π ≫ p) := ((isProjOver_iff_isProper_and_exists_isAmpleLB _).1 hres.proj).1
  haveI : IsProper π := IsProper.of_comp π p
  obtain ⟨Q, hQ0, hQ⟩ := GlobalTheory.T.exists_bertini_poly_discrepancy_snc_boundary Y (π ≫ p) n hres.proj B hres.snc (pullCart π A) ι
    (fun i => functionFieldMap π (s i)) fun i => functionFieldMap_mem_sections π (hs i)
  refine ⟨Q, hQ0, fun u hu t ht y ⟨i, hi⟩ a c ha hc hklt => ?_⟩

  set b : ℕ := a.num.toNat with hb
  set e : ℕ := a.den with he
  have hepos : 0 < e := a.den_pos
  have hab : a = b / e := by
    have h0 : (0 : ℤ) ≤ a.num := Rat.num_nonneg.2 ha
    have h1 : ((a.num.toNat : ℕ) : ℚ) = (a.num : ℚ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg h0]
    rw [hb, he, h1]
    exact (Rat.num_div_den a).symm
  set m'' := m * (e * m') with hm''
  set G' := (e * m') • G + m • (b • D₀) with hG'
  have hm''pos : 0 < m'' := Nat.mul_pos hm (Nat.mul_pos hepos hm')
  have hmult : IsLogMult p n (Δ + a • qWeil D₀ m') η m'' G' := isLogMult_add hη hm' hepos hab

  have hΘ : pullCart π G' - m'' • K = (e * m') • (pullCart π G - m • K) + (m * b) • pullCart π D₀ := by
    have hn1 : ∀ (r : ℕ) (D : CartierDiv X), pullCart π (r • D) = r • pullCart π D :=
      fun r D => map_nsmul (pullCartHom π) r D
    rw [hG', pullCart_add, hn1, hn1, hn1, hm'']
    module
  have hsupp : (pullCart π G' - m'' • K).supp ≤ B := by
    rw [hΘ]
    refine (CartierDiv.supp_add_le _ _).trans (sup_le ((supp_nsmul_le _ _).trans hres.supp)
      ((supp_nsmul_le _ _).trans fun w hw => hB w ((GlobalTheory.T.cartierDivisorPullback_support_and_effective X Y π D₀).1 w hw)))
  have hres' : IsLogRes p n η m'' G' π K B := { hres with supp := hsupp }

  obtain ⟨g'', hg''⟩ := G'.exists_isEqn y
  have hL := hmult.eqn y g'' hg''
  obtain ⟨ya, hya⟩ := A.exists_isEqn y
  have hH : (CartierDiv.principal t + A).IsEqn y (t * ya) := (CartierDiv.isEqn_principal t y).add hya
  have hHz : ∀ z, z ⤳ y → ∀ E : DivOver p, E.IsAt z →
      qWeil (CartierDiv.principal t + A) 1 z = (E.ord (t * ya) : ℚ) / (1 : ℕ) := by
    intro z hz E hE
    obtain ⟨V, hV, hHV⟩ := hH.exists_nhds
    rw [qWeil, (hHV z (hz.mem_open V.isOpen hV)).mult_eq, ← hE.ord_eq]
  obtain ⟨m₂, g₂, hm₂, hL₂, hdisc⟩ := isLogEqn_add_smul X p n (Δ + a • qWeil D₀ m')
    (qWeil (CartierDiv.principal t + A) 1) η y m'' 1 g'' (t * ya) c hm''pos one_pos hL hHz
  rw [hL₂.kltAt_iff hn hη.ne_zero hm₂]
  intro E hE
  rw [hdisc]

  obtain ⟨E', hE'⟩ := GlobalTheory.T.exists_primeDivisor_over_source_birational ℂ X Y p π hres.bir E
  obtain ⟨y', rfl, hy'⟩ := GlobalTheory.T.divisor_center_proper_lift ℂ X Y p π hres.bir inferInstance E' E hE' y hE
  have hη' : EtaleKlt.ratPull p π n η ≠ 0 := fun h =>
    hη.ne_zero ((GlobalTheory.T.rationalTopFormPullback_bijective_birational ℂ X Y p π hres.bir n).1 (h.trans (map_zero _).symm))
  have hΘm : ∀ w, w ⤳ y' → (pullCart π G' - m'' • K).mult w < m'' := fun w hw =>
    ((GlobalTheory.T.log_resolution_multiplier_local ℂ X p n hproj hn _ η m'' G' Y π K B hmult hres' (π y')).1.1 hklt) w
      (hw.map π.continuous)
  have hΘe : (pullCart π G' - m'' • K + m'' • K).IsEqn y' (fnPull π g'') := by
    rw [sub_add_cancel]; exact isEqn_pullCart π hg''
  have ht' : ((fnPull π t : Y.functionFieldˣ) : Y.functionField) =
      ∑ i, Cartier.constFn (π ≫ p) (u i) * functionFieldMap π (s i) := by
    change functionFieldMap π (t : X.functionField) = _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [ht, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, ← EtaleKlt.functionFieldMap_comp_constFn p π, RingHom.comp_apply]
  have hH' : (CartierDiv.principal (fnPull π t) + pullCart π A).IsEqn y' (fnPull π (t * ya)) := by
    rw [map_mul]; exact (CartierDiv.isEqn_principal _ y').add (isEqn_pullCart π hya)
  have key := hQ u hu (fnPull π t) ht' y' ⟨i, generatesAt_pullCart π hi⟩ (EtaleKlt.ratPull p π n η)
    K (pullCart π G' - m'' • K) m'' c (fnPull π g'') (fnPull π (t * ya)) hη' hres.div hm''pos
    hsupp hc hΘm hΘe hH' E' hy'
  have e1 := GlobalTheory.T.form_order_birational_pullback ℂ X Y p π hres.bir E' E hE' n η hη.ne_zero
  change E'.formOrd (EtaleKlt.ratPull p π n η) = E.formOrd η at e1
  have e2 := GlobalTheory.T.ord_functionField_pullback_primeDivisor_over ℂ X Y p π hres.bir E' E hE' g''
  have e3 := GlobalTheory.T.ord_functionField_pullback_primeDivisor_over ℂ X Y p π hres.bir E' E hE' (t * ya)
  simp only [discrep, e1, e2, e3] at key
  simpa [discrep] using key
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KawamataLogTerminalAddGeneralMemberLinearSystemStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kawamataLogTerminal_add_generalMember_linearSystem : GlobalTheory.Published.Principalisation → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (Δ D : X → ℚ) (m : ℕ) (G A : CartierDiv X) (ι : Type) [Fintype ι] (s : ι → X.functionField), 0 < m → IsLogCanonicalMultiple p n Δ m G → IsQCart D → (∀ i, s i ∈ A.sections) → ∃ Q : MvPolynomial ι ℂ, Q ≠ 0 ∧ ∀ u : ι → ℂ, MvPolynomial.eval u Q ≠ 0 → ∀ t : X.functionFieldˣ, (t : X.functionField) = ∑ i, Cartier.constFn p (u i) * s i → ∀ y : X, (∃ i, A.GeneratesAt y (s i)) → ∀ a c : ℚ, 0 ≤ a → c < 1 → KltAt p n (Δ + a • D) y → KltAt p n (Δ + a • D + c • qWeil (GlobalTheory.Cartier.CartierDiv.principal t + A) 1) y := by
  first | exact @GlobalTheory.PairStep.kltAt_add_general_member | exact GlobalTheory.PairStep.kltAt_add_general_member | (intros; apply GlobalTheory.PairStep.kltAt_add_general_member <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAmpleMultipleSectionsVanishGenerate
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAmpleMultipleSectionsVanishGenerate
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
namespace GlobalTheory.IdGenRat

theorem presents_lbPow_toLB {X : Scheme.{0}} [IsIntegral X] (A : CartierDiv X) (l : ℕ) :
    ∃ r, Presents (l • A) (lbPow (toLB A) l) r := by
  have h := GlobalTheory.CombChern.presents_zpow (presents_toLB A) (l : ℤ)
  rw [natCast_zsmul] at h
  exact ⟨_, h⟩

theorem exists_sections_vanish_generate : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ), IsProjOver p → ∀ (A : CartierDiv X) (z : X), IsAmpleLB (toLB A) → ∃ l₁ : ℕ, ∀ l, l₁ ≤ l → ∃ (r : ℕ) (κ : Fin r → X.functionField), (∀ i, κ i ∈ (l • A).sections) ∧ (∀ i, (l • A).VanishesAt z (κ i)) ∧ ∀ y, ¬ z ⤳ y → ∃ i, (l • A).GeneratesAt y (κ i) := by
  intro X _ _ p hp A z hA
  obtain ⟨l₁, hl₁⟩ := Filter.eventually_atTop.1
    (GlobalTheory.T.eventually_exists_ample_pow_sections_cutting_out_closed X p hp (toLB A) (Closeds.closure {z}) hA)
  refine ⟨l₁, fun l hl => ?_⟩
  obtain ⟨r, κ, -, hz, hy⟩ := hl₁ l hl
  obtain ⟨ρ, hρ⟩ := presents_lbPow_toLB A l
  refine ⟨r, fun i => hρ.rat (κ i), fun i => hρ.rat_mem _, fun i => ?_, fun y hy' => ?_⟩
  · exact (hρ.vanishesAt_rat_iff _).2 (hz i z (subset_closure rfl))
  · have hyZ : y ∉ Closeds.closure ({z} : Set X) := fun h => hy' (specializes_iff_mem_closure.2 h)
    obtain ⟨i, hi⟩ := hy y hyZ
    exact ⟨i, (hρ.generatesAt_rat_iff _).2 hi⟩

end GlobalTheory.IdGenRat
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAmpleMultipleSectionsVanishGenerateStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ampleMultiple_sections_vanish_generate : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ), IsProjOver p → ∀ (A : CartierDiv X) (z : X), IsAmpleLB (toLB A) → ∃ l₁ : ℕ, ∀ l, l₁ ≤ l → ∃ (r : ℕ) (κ : Fin r → X.functionField), (∀ i, κ i ∈ (l • A).sections) ∧ (∀ i, (l • A).VanishesAt z (κ i)) ∧ ∀ y, ¬ z ⤳ y → ∃ i, (l • A).GeneratesAt y (κ i) := by
  first | exact @GlobalTheory.IdGenRat.exists_sections_vanish_generate | exact GlobalTheory.IdGenRat.exists_sections_vanish_generate | (intros; apply GlobalTheory.IdGenRat.exists_sections_vanish_generate <;> assumption)
end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory.GeneralLift

theorem unitAt_constFn {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ Sp ℂ) {a : ℂ} (ha : a ≠ 0) (x : X) :
    GlobalTheory.Cartier.UnitAt x (GlobalTheory.Cartier.constFn p a) :=
  GlobalTheory.Cartier.unitAt_fnOf (U := ⊤) trivial trivial
    (Units.map (algX p ⊤ : ℂ →+* Γ(X, ⊤)).toMonoidHom (Units.mk0 a ha))

theorem regAt_constFn {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ Sp ℂ) (a : ℂ) (x : X) :
    GlobalTheory.Cartier.RegAt x (GlobalTheory.Cartier.constFn p a) :=
  GlobalTheory.Cartier.regAt_fnOf (U := ⊤) trivial trivial (algX p ⊤ a)

theorem principal_const {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ Sp ℂ) {a : ℂ} (ha : a ≠ 0)
    (w : X.functionFieldˣ) (hw : (w : X.functionField) = GlobalTheory.Cartier.constFn p a) :
    GlobalTheory.Cartier.CartierDiv.principal w = 0 :=
  GlobalTheory.Cartier.CartierDiv.ext_of_isEqn fun x =>
    ⟨1, (GlobalTheory.Cartier.CartierDiv.isEqn_principal w x).iff_unitAt.2 (by
      rw [Units.val_one, one_div, hw]; exact (unitAt_constFn p ha x).inv),
      GlobalTheory.Cartier.CartierDiv.isEqn_zero x⟩

end GlobalTheory.GeneralLift


open GlobalTheory.GeneralLift in
theorem GlobalTheory.GeneralLift.exists_lift_klt : GlobalTheory.Published.Principalisation → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (Δ D : X → ℚ) (m : ℕ) (G A : CartierDiv X) (z : X), 0 < m → IsLogCanonicalMultiple p n Δ m G → IsQCart D → IsAmpleLB (toLB A) → ∃ l₁ : ℕ, ∀ l, l₁ ≤ l → ∀ f₀ ∈ (l • A).sections, ∃ u : X.functionField, u ∈ (l • A).sections ∧ (l • A).VanishesAt z u ∧ ∀ g : X.functionFieldˣ, (g : X.functionField) = f₀ + u → ∀ y, ¬ z ⤳ y → ∀ a t : ℚ, 0 ≤ a → t < 1 → KltAt p n (Δ + a • D) y → KltAt p n (Δ + a • D + t • qWeil (GlobalTheory.Cartier.CartierDiv.principal g + l • A) 1) y := by
  intro hP X _ _ _ p n hp hn Δ D m G A z hm hG hD hA
  obtain ⟨l₁, hl₁⟩ := GlobalTheory.T.exists_ampleMultiple_sections_vanish_generate X p hp A z hA
  refine ⟨l₁, fun l hl f₀ hf₀ => ?_⟩
  obtain ⟨r, κ, hκs, hκv, hκg⟩ := hl₁ l hl
  let s : Option (Fin r) → X.functionField := fun i => Option.elim i f₀ κ
  have hs : ∀ i, s i ∈ (l • A).sections := by
    rintro (_ | i)
    exacts [hf₀, hκs i]
  obtain ⟨Q, hQ, hQe⟩ := GlobalTheory.T.kawamataLogTerminal_add_generalMember_linearSystem hP X p n hp hn Δ D m G (l • A) (Option (Fin r)) s hm hG hD hs
  obtain ⟨v, hv⟩ : ∃ v : Option (Fin r) → ℂ, MvPolynomial.eval v (Q * MvPolynomial.X none) ≠ 0 := by
    by_contra h
    push_neg at h
    exact mul_ne_zero hQ (MvPolynomial.X_ne_zero _) (MvPolynomial.funext fun v => by rw [h v, map_zero])
  rw [map_mul, MvPolynomial.eval_X] at hv
  have hv0 : v none ≠ 0 := right_ne_zero_of_mul hv
  have hvQ : MvPolynomial.eval v Q ≠ 0 := left_ne_zero_of_mul hv
  refine ⟨∑ i : Fin r, GlobalTheory.Cartier.constFn p (v (some i) / v none) * κ i, ?_, ?_, ?_⟩
  · refine Submodule.sum_mem _ fun i _ => ?_
    exact GlobalTheory.Cartier.CartierDiv.mem_sections.2 fun x =>
      (GlobalTheory.Cartier.CartierDiv.mem_sections.1 (hκs i) x).regAt_mul (regAt_constFn p _ x)
  · refine Finset.sum_induction _ (fun f => (l • A).VanishesAt z f)
      (fun _ _ h h' => h.add h') ((l • A).vanishesAt_zero z) fun i _ => ?_
    obtain ⟨g, hg, hz⟩ := hκv i
    exact ⟨g, hg, by convert hz.mul (regAt_constFn p (v (some i) / v none) z) using 1; ring⟩
  · intro g hg y hy a t ha ht hk
    have hc : GlobalTheory.Cartier.constFn p (v none) ≠ 0 := (map_ne_zero _).2 hv0
    have key := hQe v hvQ (Units.mk0 _ hc * g) (by
      rw [Units.val_mul, Units.val_mk0, hg, Fintype.sum_option, mul_add, Finset.mul_sum]
      refine congrArg₂ (· + ·) rfl (Finset.sum_congr rfl fun i _ => ?_)
      rw [← mul_assoc, ← map_mul, mul_div_cancel₀ _ hv0]
      rfl) y (have ⟨i, hi⟩ := hκg y hy; ⟨some i, hi⟩) a t ha ht hk
    rwa [GlobalTheory.Cartier.CartierDiv.principal_mul, principal_const p hv0 _ (Units.val_mk0 hc),
      zero_add] at key
