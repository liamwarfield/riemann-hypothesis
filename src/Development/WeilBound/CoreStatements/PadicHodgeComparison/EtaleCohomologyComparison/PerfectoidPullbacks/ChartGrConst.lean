module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechRefinementCohomologyBijective
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FilteredCohomologyRestrictionBijective
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DividedPowerEnvelopeExpansion
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.DatPull
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.PolynomialSiteTraces.PolyAll

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ChartGrConst
section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.PolynomialSiteTraces.PolyTf
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.PDA

namespace CrystallineSemistableComparison.Pb.Site

variable {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} {γ : DividedPowers I} {X : Scheme.{0}}
  {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I}

theorem trAdm (T : Thick (nlFun γ 0 X q κ)) (l s : ℕ) (hT : TF l s T) :
    (0 ≠ 0 → IsNilpotent ((0 : ℕ) : trB T s)) ∧ (0 = 0 → IsNilpotent (trJ T s)) :=
  ⟨fun h => absurd rfl h, fun _ => (GlobalTheory.T.truncated_envelope_torsion_free T.δ l s (trD T s) (trD_spec T s).1 hT.1 hT.2).2.2⟩

def trH (T : Thick (nlFun γ 0 X q κ)) (s : ℕ)
    (adm : (0 ≠ 0 → IsNilpotent ((0 : ℕ) : trB T s)) ∧ (0 = 0 → IsNilpotent (trJ T s))) : T ⟶ polyTr T s adm :=
  homOf T (trF T s) (trJ T s) (trD T s) (trF_le T s) (trF_dp T s) adm

def trDesc (T : Thick (nlFun γ 0 X q κ)) (s : ℕ)
    (adm : (0 ≠ 0 → IsNilpotent ((0 : ℕ) : trB T s)) ∧ (0 = 0 → IsNilpotent (trJ T s))) {T' : Thick (nlFun γ 0 X q κ)} (φ : T ⟶ T')
    (G : trB T s →+* T'.B) (hG : G.comp (trF T s) = φ.φ) (hGd : IsDPMorphism (trD T s) T'.δ G)
    (hle : trJ T s ≤ T'.J.comap G) : polyTr T s adm ⟶ T' :=
  descOf φ G hG hGd hle

theorem trSum (T : Thick (nlFun γ 0 X q κ)) (s : ℕ) (b : ℕ →₀ T.B) :
    (b.sum fun k c => trF T s c * (trD T s).dpow k (Ideal.Quotient.mk (trI T s) ((pq T.B).e 1))) =
      Ideal.Quotient.mk (trI T s) (b.sum fun k c => algebraMap T.B (pq T.B).P c * (eta T.δ).dpow k ((pq T.B).e 1)) := by
  rw [map_finsuppSum]
  refine Finsupp.sum_congr fun k _ => ?_
  rw [map_mul, (trD_spec T s).1.2 _ (Ideal.mem_sup_right (Ideal.subset_span ⟨0, rfl⟩))]
  rfl

theorem polyTr_mem (l s : ℕ) (𝒱 : Set X.Opens)
    (T : (St (γ := γ) (p := 0) (q := q) (κ := κ) (TF l s) 𝒱).FullSubcategory) :
    St (TF l s) 𝒱 (polyTr T.obj s (trAdm T.obj l s T.property.1)) := by
  have h := GlobalTheory.T.truncated_envelope_torsion_free T.obj.δ l s (trD T.obj s) (trD_spec T.obj s).1 T.property.1.1 T.property.1.2
  refine ⟨⟨h.1, h.2.1⟩, ?_⟩
  obtain ⟨V, hV, hT⟩ := T.property.2
  exact ⟨V, hV, inU_hom (trH T.obj s _) hT⟩

def polyTf (l s : ℕ) (𝒱 : Set X.Opens) : Poly (sP (St (γ := γ) (p := 0) (q := q) (κ := κ) (TF l s) 𝒱)) where
  P T := ⟨polyTr T.obj s (trAdm T.obj l s T.property.1), polyTr_mem l s 𝒱 T⟩
  j T := ObjectProperty.homMk (trH T.obj s _)
  X T := Ideal.Quotient.mk (trI T.obj s) ((pq T.obj.B).e 1)
  X_mem T := Ideal.mem_map_of_mem _ (Ideal.mem_sup_right (Ideal.subset_span ⟨0, rfl⟩))
  univ {T T'} φ x hx := by
    obtain ⟨F, ⟨hF, hF1, hFd⟩, hFu⟩ := GlobalTheory.T.divided_power_envelope_universal T.obj.δ T'.obj.δ φ.hom.φ φ.hom.dp x hx
    have hK : ∀ a ∈ trI T.obj s, F a = 0 := by
      intro a ha
      have h1 : F a ∈ fil T'.obj.δ (max s 1) := FubiniStudyChowHeightFormula₂.Adr.Fil.map_fil_le _ _ F hFd _ (Ideal.mem_map_of_mem F ha)
      have h2 : T'.obj.pdPow (max s 1) ≤ T'.obj.pdPow s := T'.obj.pdPow_anti (le_max_left _ _)
      have h3 := h2 h1
      rw [T'.property.1.1, Ideal.mem_bot] at h3
      exact h3
    let G : trB T.obj s →+* T'.obj.B := Ideal.Quotient.lift _ F hK
    have hGF : G.comp (Ideal.Quotient.mk (trI T.obj s)) = F := Ideal.Quotient.lift_comp_mk _ _ _
    have hGd : IsDPMorphism (trD T.obj s) T'.obj.δ G := (trD_spec T.obj s).2 _ _ _ G (by rw [hGF]; exact hFd)
    have hG : G.comp (trF T.obj s) = φ.hom.φ := by
      rw [← hF, ← hGF]
      rfl
    have hle : trJ T.obj s ≤ T'.obj.J.comap G := Ideal.map_le_iff_le_comap.1 hGd.1
    refine ⟨ObjectProperty.homMk (trDesc T.obj s _ φ.hom G hG hGd hle), ?_, ?_⟩
    · refine And.intro ?_ ?_
      · ext1
        exact CrystallineSemistableComparison.Pb.hom_ext hG
      · exact hF1
    · rintro ψ ⟨h1, h2⟩
      ext1
      refine CrystallineSemistableComparison.Pb.hom_ext ?_
      change ψ.hom.φ = G
      refine Ideal.Quotient.ringHom_ext ?_
      rw [hGF]
      refine hFu _ ⟨?_, h2, ?_⟩
      · exact congrArg (fun f => f.hom.φ) h1
      · exact IsDPMorphism.comp _ ψ.hom.dp (trD_spec T.obj s).1
  span T z := by
    obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨b, rfl⟩ := GlobalTheory.T.divided_power_envelope_expansion T.obj.δ w
    exact ⟨b, (trSum T.obj s b).symm⟩

theorem poly_tf' : ∀ {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} (γ : DividedPowers I) {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of O)) (κ : O →+* R ⧸ I) (l s : ℕ) (𝒱 : Set X.Opens),
    ∃ Q : Poly (sP (St (γ := γ) (p := 0) (q := q) (κ := κ) (TF l s) 𝒱)),
      ∀ r : ℤ, r ≤ s → Q.Crit (sFil _) r ∧ ∀ c : R, Q.Crit (fun r => stdI _ (some r) c) r := by
  intro O R _ _ I γ X q κ l s 𝒱
  refine ⟨polyTf l s 𝒱, fun r hr => ⟨?_, fun c => ?_⟩⟩
  · intro T b
    have e := trSum T.obj s b
    refine Iff.trans ?_ (Iff.trans ((GlobalTheory.T.truncated_envelope_filtration_quotient T.obj.δ s (trD T.obj s) (trD_spec T.obj s).1 b r.toNat
      (by omega) 0).1) (forall_congr' fun k => ?_))
    · change (b.sum fun k c => trF T.obj s c * (trD T.obj s).dpow k (Ideal.Quotient.mk (trI T.obj s) ((pq T.obj.B).e 1)))
        ∈ fil (trD T.obj s) r.toNat ↔ _
      exact Iff.of_eq (congrArg (fun z => z ∈ fil (trD T.obj s) r.toNat) e)
    · change _ ↔ b k ∈ fil T.obj.δ (r - k).toNat
      rw [show (r - k).toNat = r.toNat - k by omega]
      exact Iff.rfl
  · intro T b
    have e := trSum T.obj s b
    refine Iff.trans ?_ (Iff.trans ((GlobalTheory.T.truncated_envelope_filtration_quotient T.obj.δ s (trD T.obj s) (trD_spec T.obj s).1 b r.toNat
      (by omega) (T.obj.i c)).2) (forall_congr' fun k => ?_))
    · change (b.sum fun k c => trF T.obj s c * (trD T.obj s).dpow k (Ideal.Quotient.mk (trI T.obj s) ((pq T.obj.B).e 1)))
        ∈ fil (trD T.obj s) r.toNat ⊔ Ideal.span {trF T.obj s (T.obj.i c)} ↔ _
      exact Iff.of_eq (congrArg (fun z => z ∈ fil (trD T.obj s) r.toNat ⊔ Ideal.span {trF T.obj s (T.obj.i c)}) e)
    · change _ ↔ b k ∈ fil T.obj.δ (r - k).toNat ⊔ Ideal.span {T.obj.i c}
      rw [show (r - k).toNat = r.toNat - k by omega]
      exact Iff.rfl

end CrystallineSemistableComparison.Pb.Site
end
end

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.Pb

theorem isFil : ∀ {b : Base} {L : b.Fun} (Q : ObjectProperty (Thick L)), IsFil (sP Q) (sFil Q) := @GlobalTheory.T.sheaf_filtration_property

theorem poly_tf : ∀ {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} (γ : DividedPowers I) {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of O)) (κ : O →+* R ⧸ I) (l s : ℕ) (𝒱 : Set X.Opens),
    ∃ Q : Poly (sP (St (γ := γ) (p := 0) (q := q) (κ := κ) (TF l s) 𝒱)),
      ∀ r : ℤ, r ≤ s → Q.Crit (sFil _) r ∧ ∀ c : R, Q.Crit (fun r => stdI _ (some r) c) r := @Site.poly_tf'

theorem poly_all : ∀ {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} (γ : DividedPowers I) (p : ℕ) (hp : p ≠ 0) {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of O)) (κ : O →+* R ⧸ I) (Q₀ : ObjectProperty (Thick (nlFun γ p X q κ))) (h : Q₀ = ⊤ ∨ Q₀ = FlatT)
    (𝒱 : Set X.Opens), ∃ Q : Poly (sP (St Q₀ 𝒱)), ∀ r : ℤ, Q.Crit (sFil _) r ∧ Q.Crit (fun _ => IdF.bot _) r ∧
      ∀ c : R, Q.Crit (fun r => stdI _ (some r) c) r ∧ Q.Crit (fun _ => stdI _ none c) r ∧ Q.Crit (fun _ => IdF.span _ c) r := @Site.poly_all'

theorem zar : ∀ {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ} {X : Scheme.{0}}
    {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} (Q₀ : ObjectProperty (Thick (nlFun γ p X q κ))) (hQ : Used Q₀)
    (𝒱 𝒲 : Set X.Opens) (h : St Q₀ 𝒱 ≤ St Q₀ 𝒲) (hc : ∀ W ∈ 𝒲, W ≤ sSup 𝒱) (j : ℕ),
    (∀ r r' : ℤ, Function.Bijective (((incl h).sq (incl_fil h r) (incl_fil h r')).pull j)) ∧
    (∀ (r r' : Option ℤ) (c c' : R), Function.Bijective (((incl h).sq (incl_std h r c) (incl_std h r' c')).pull j)) ∧
    Function.Bijective ((incl h).o.pull j) := @GlobalTheory.CompanionTheory.NlZar.zariski_descent

theorem refl : ∀ {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} {γ : DividedPowers I} {X : Scheme.{0}}
    {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} (Q₀ : ObjectProperty (Thick (nlFun γ 0 X q κ))) (l s : ℕ)
    (hQ : (Q₀ = ⊤ ∧ l = 1) ∨ ∃ s', s ≤ s' ∧ Q₀ = TF l s') (𝒱 : Set X.Opens) (h : St (TF l s) 𝒱 ≤ St Q₀ 𝒱) (r r' : ℤ) (hr : r' ≤ s) (j : ℕ),
    Function.Bijective (((incl h).sq (incl_fil h r) (incl_fil h r')).pull j) := @GlobalTheory.CompanionTheory.PDTrunc.pull_incl_bijective

theorem cov_ex : ∀ {O : Type} [CommRing O] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) [IsSeparated q] [QuasiCompact q],
    (Smooth q → Nonempty (Cov q)) ∧ ∀ d, SmoothOfRelativeDimension d q → ∃ U : Cov q, ∀ α, U.d α = d := @GlobalTheory.T.exists_smooth_coordinate_cover

theorem coord_res : ∀ {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {V W : X.Opens} {d : ℕ}
    (c : Coord q V d) (h : W ≤ V) (hW : IsAffineOpen W), ∃ c' : Coord q W d, ∀ i, c'.t i = rs h (c.t i) := @GlobalTheory.T.coordinates_restrict_affine_open

end CrystallineSemistableComparison.Pb
end
end

section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LieComplementChartContDiffAt
section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.Lin
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris

namespace CrystallineSemistableComparison.Pb

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

structure KapL (Amp : ∀ M : Model l K, E.LineData M.X → Prop) where
  κ : ∀ {M : Model l K} (a : (dat Amp).Ch M) (j : ℕ), ((dat Amp).H a).N j →+ (Module.Dual K (HdR M.q j) →+ (per l K).B)
  lin : ∀ {M : Model l K} (a : (dat Amp).Ch M), M.Sm → ∀ (j : ℕ) (c : (per l K).A) (x : ((dat Amp).H a).N j)
    (φ : Module.Dual K (HdR M.q j)), κ a j (c • x) φ = (per l K).i c * κ a j x φ
  lin' : ∀ {M : Model l K} (a : (dat Amp).Ch M), M.Sm → ∀ (j : ℕ) (k : K) (x : ((dat Amp).H a).N j)
    (φ : Module.Dual K (HdR M.q j)), κ a j x (k • φ) = (per l K).o k * κ a j x φ
  act : ∀ {M : Model l K} (a : (dat Amp).Ch M), M.Sm → ∀ (j : ℕ) (σ : K.fixingSubgroup) (x : ((dat Amp).H a).N j)
    (φ : Module.Dual K (HdR M.q j)), κ a j (((dat Amp).H a).act j σ x) φ = (per l K).σ σ (κ a j x φ)
  nat : ∀ {M N : Model l K} {u : M.X ⟶ N.X} {hu : u ≫ N.p = M.p} {a : (dat Amp).Ch M} {b : (dat Amp).Ch N}
    (m : (dat Amp).Mo u hu a b), M.Sm → N.Sm → ∀ (j : ℕ) (x : ((dat Amp).H b).N j) (φ : Module.Dual K (HdR M.q j)),
    κ a j ((dat Amp).pullH m j x) φ = κ b j x (φ ∘ₗ pullR j (Model.genMap u hu) (Model.genMap_q u hu))
  fil : ∀ {M : Model l K} (a : (dat Amp).Ch M), M.Sm → ∀ (j n r : ℕ) (x : ((dat Amp).H a).N j)
    (φ : Module.Dual K (HdR M.q j)), (dat Amp).fil a j n x → (∀ h ∈ FilR M.q j (r + 1), φ h = 0) →
    ∃ y ∈ (per l K).P, (per l K).tB ^ r * κ a j x φ = (per l K).tB ^ n * y
  cup : ∀ {M : Model l K} (a : (dat Amp).Ch M), M.Sm → ∀ {i j : ℕ} (x : ((dat Amp).H a).N i) (y : ((dat Amp).H a).N j)
    (z : ((dat Amp).H a).N (i + j)), ((dat Amp).H a).cup x y z →
    ∀ {m m' : ℕ} (b : Module.Basis (Fin m) K (HdR M.q i)) (b' : Module.Basis (Fin m') K (HdR M.q j))
      (φ : Module.Dual K (HdR M.q (i + j))),
      κ a (i + j) z φ = ∑ s, ∑ s', κ a i x (b.coord s) * κ a j y (b'.coord s') * (per l K).o (φ (cupK M.q rfl (b s) (b' s')))
  one : ∀ {M : Model l K} (a : (dat Amp).Ch M), M.Sm → ∀ x : ((dat Amp).H a).N 0, ((dat Amp).H a).one x →
    ∀ φ : Module.Dual K (HdR M.q 0), κ a 0 x φ = (per l K).o (φ (oneK M.q))

end CrystallineSemistableComparison.Pb
end
end

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Limits GlobalTheory.LogCris GroundTheory.PAdicHodge

namespace CrystallineSemistableComparison.Pb

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

abbrev Amp (M : Model l K) (D : E.LineData M.X) : Prop := IsTautologicalLine M.p D

abbrev lineK {M : Model l K} (D : E.LineData M.X) : E.LineData M.gen := D.pb (pullback.fst _ _)

def LieComplementChartContDiffAt (L : KapL (l := l) (K := K) Amp) : Prop :=
  ∀ {M : Model l K} (a : (dat Amp).Ch M), M.Sm → ∀ (x : ((dat Amp).H a).N 2) (c : HdR M.q 2), (dat Amp).c1H a x →
    IsFirstChernDeRham M.q (lineK a.1) c → ∀ φ : Module.Dual K (HdR M.q 2), L.κ a 2 x φ = (per l K).o (φ c)

end CrystallineSemistableComparison.Pb
end
end
