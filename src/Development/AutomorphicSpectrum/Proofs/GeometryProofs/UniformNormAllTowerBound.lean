module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.UniformNormTowerBound
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.MemPtsOverOfMemMcPts
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.WeightSectionComponentValue
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TraceIntegralSubringExtension
public import Development.WeilBound.CoreStatements.CommonZeroEvaluation.AevalRatioForm
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CompLawsTowerBound

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.UniformAllTowerBound
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.UniformAllRootOriginBound
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.UniformAllRootOriginBound
open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi

set_option maxHeartbeats 1600000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.uniform_all_root_origin_bound : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsGalois ℚ E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (h : GenFrEx Xo c) (e : Comp Xo c → Rul Xo c), CompLaws U h e → Ref.UnifAll Xo c → ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx) (Fr : Small.GenFrame Or) (Z : Comp Xo c) (Rd : Reading Fr h Z), Or.𝔐.OmVB → (∀ p : ℕ, p.Prime → (p : ℤ) ∣ discr E → p ∈ SS) → FinTr.Linked Rd → ∀ B₁ : Finset RM.Ω, ∃ (B₂ : Finset RM.Ω) (B₃ : Finset (Om Z)), ∀ (A : Subring RM.Ω), (↑B₁ : Set RM.Ω) ⊆ A → (↑B₂ : Set RM.Ω) ⊆ A → ∀ (A' : Subring (Om Z)), (↑B₃ : Set (Om Z)) ⊆ A' → ∀ (p : ℕ) [Fact p.Prime] (ev₁ : A →+* PadicAlgCl p), (∀ x, IsAlgebraic ℤ (ev₁ x)) → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e₀ : ℕ) (y : IntFr Xo c T io) (ι : T.Fr →+* PadicAlgCl p) (ev : A' →+* T.Fr), (p : 𝓞 c.F) ∈ la.asIdeal → OverLa la T.V io e₀ → y.IsAlg → (∀ x, ‖ι x‖ = FinRd.absT p la T e₀ x) → FinTr.RegAt h Z io A' ev y.1 → (∀ a : A', ∃ ha : Rd.φ a ∈ A, ev₁ ⟨_, ha⟩ = ι (ev a)) → ∃ z ∈ Small.algPts p (mCoordIdeal RM.y), ∃ rec : RootIx Dw → ℝ, (∀ b (hb : b ∈ A), b ∈ B₁ → Small.HasVal RM.y 0 b z (ev₁ ⟨b, hb⟩)) ∧ (∀ r', 0 < rec r' ∧ |Real.log (Small.supMet (RM.xdeg r') z) - Real.log (rec r')| ≤ (if p ∈ SS then 1 / ((p : ℝ) - 1) + (if p = 2 then 1 else 0) + (padicValInt p (discr E) : ℝ) / Module.finrank ℚ E else 0) * Real.log p) ∧ ∀ (a : WZ E) (n' : Option (RootIx Dw) → ℤ), (∀ j, (n' j : ℝ) = RM.coef (towerWt Dw a) 0 j) → ∀ f ∈ Rec.secZ Xo c a, ∃ v, Small.HasVal RM.y (Top.combLine (RM.line 1) n').a (Fr.rd f * (∏ r', Or.e r' ^ (-n' (some r')))) z v ∧ ∀ s : ℝ, nval T.V e₀ (evI y f) = ((ramOverZ la * s : ℝ) : EReal) → ‖v‖ = (p : ℝ) ^ (-s) * ∏ r', rec r' ^ n' (some r') := by
  intro hG E _ _ _ _ H Dw l Xo c r U h e hL hUn O _ β Y SS RM Sys Fx Or Fr Z Rd hOm hram hLk B₁
  classical
  haveI : CharZero RM.Ω := charZero_of_injective_ringHom Or.𝔐.cst.injective
  letI aΩ : Algebra c.F RM.Ω := Small.cstAlg Or
  obtain ⟨B, hB⟩ := GlobalTheory.T.root_origin_frame_height E H Dw l Xo c O β Y SS RM Sys Fx Or Fr
  obtain ⟨w, tl, hw, htl⟩ := hLk
  have hy0 : ∀ k, ∃ i, RM.y ⟨k, i⟩ ≠ 0 := fun k => by
    obtain ⟨i, hi⟩ := RM.arith.2.1.2.2 k
    refine ⟨i, fun h0 => hi ?_⟩
    show mConeMap RM.y _ = 0
    simp [mConeMap, h0]
  obtain ⟨B₂, hB₂⟩ := ModelDimension.Read.point RM.y RM.birational hy0 (B₁ ∪ B ∪
    Finset.univ.image (fun x : Σ k : RM.K, RM.ι k × RM.ι k => RM.y ⟨x.1, x.2.1⟩ / RM.y ⟨x.1, x.2.2⟩) ∪
    Finset.univ.image fun k => (((tl k)⁻¹ : RM.Ωˣ) : RM.Ω))
  refine ⟨B₂, ∅, fun A _ hA A' _ p _ ev₁ halg la T io e₀ y ι ev hp ho hy hι hReg hφ => ?_⟩
  letI aT : Algebra c.F T.Fr := io.toAlgebra
  obtain ⟨hcst, q', φ', ψ', yq', z', t', hq1, hq2, hq3, hq4⟩ := hReg
  have hcA : ∀ a : c.F, ∃ ha : Or.𝔐.cst a ∈ A, ev₁ ⟨_, ha⟩ = ι (io a) := fun a => by
    obtain ⟨ha, e1⟩ := hcst a
    obtain ⟨hb, e2⟩ := hφ ⟨_, ha⟩
    have e3 := Rd.φ_cst a
    refine ⟨e3 ▸ hb, ?_⟩
    rw [← e1, ← e2]
    exact congrArg ev₁ (Subtype.ext e3.symm)
  have hn : ∀ n : ℕ, n ≠ 0 → ((n : RM.Ω))⁻¹ ∈ A := fun n _ => by
    have := (hcA ((n : c.F))⁻¹).1
    rwa [map_inv₀, map_natCast] at this
  obtain ⟨z, hz, hzA, A₂, hle, hBA, hn₂, hev⟩ := hB₂ A hA hn (PadicAlgCl p) ev₁
  have hzalg : z ∈ Small.algPts p (mCoordIdeal RM.y) := ⟨hz, fun q => by
    obtain ⟨a, ha⟩ := hzA q
    rw [ha]
    exact (halg a).extendScalars (algebraMap ℤ ℚ).injective_int⟩
  have hGood := hB A₂ (fun x hx => hBA (by simp [Finset.mem_coe.1 hx])) hn₂
  have hrat : ∀ (k : RM.K) (i j : RM.ι k), RM.y ⟨k, j⟩ ≠ 0 → RM.y ⟨k, i⟩ / RM.y ⟨k, j⟩ ∈ A₂ := fun k i j _ =>
    hBA (Finset.mem_coe.2 (Finset.mem_union_left _ (Finset.mem_union_right _
      (Finset.mem_image.2 ⟨⟨k, i, j⟩, Finset.mem_univ _, rfl⟩))))
  have htA : ∀ k, (((tl k)⁻¹ : RM.Ωˣ) : RM.Ω) ∈ A₂ := fun k =>
    hBA (Finset.mem_coe.2 (Finset.mem_union_right _ (Finset.mem_image.2 ⟨k, Finset.mem_univ _, rfl⟩)))
  have hram0 := FinRd.ram_pos hp
  have hN : (0 : ℝ) < (e₀ : ℝ) * (ramOverZ la : ℝ) :=
    mul_pos (by exact_mod_cast ho.1) (by exact_mod_cast hram0)
  obtain ⟨T₀, j, iT, r₀, L, hfin, hr₀, hj, hv₀, hzL, hLj, hnorm⟩ := ModelDimension.Read.ext T hy ι _ hN
    (fun x hx => by rw [hι]; unfold FinRd.absT; rw [if_neg hx]) z
  let A₃ : Subring RM.Ω := (j.range.comap ev₁).map A.subtype
  have hA₃ : ∀ x, x ∈ A₃ ↔ ∃ hx : x ∈ A, ∃ b, j b = ev₁ ⟨x, hx⟩ := fun x =>
    ⟨by rintro ⟨a, ⟨b, hb⟩, rfl⟩; exact ⟨a.2, b, hb⟩, fun ⟨hx, b, hb⟩ => ⟨⟨x, hx⟩, ⟨b, hb⟩, rfl⟩⟩
  choose h3A f hf using fun x : A₃ => (hA₃ x).1 x.2
  have hinj : Function.Injective j := j.injective
  let ev₀ : A₃ →+* T₀.Fr :=
    { toFun := f
      map_one' := hinj (by rw [hf, map_one]; exact map_one ev₁)
      map_mul' := fun a b => hinj (by rw [hf, map_mul, hf, hf]; exact map_mul ev₁ ⟨_, h3A a⟩ ⟨_, h3A b⟩)
      map_zero' := hinj (by rw [hf, map_zero]; exact map_zero ev₁)
      map_add' := fun a b => hinj (by rw [hf, map_add (f := _), hf, hf]; exact map_add ev₁ ⟨_, h3A a⟩ ⟨_, h3A b⟩) }
  have hev₀ : ∀ x : A₃, j (ev₀ x) = ev₁ ⟨x, h3A x⟩ := hf
  have h23 : A₂ ≤ A₃ := fun x hx => (hA₃ x).2 ⟨hle hx, hLj _ (FinRd.Pt.hasVal_mem hzL (hev ⟨x, hx⟩))⟩
  obtain ⟨y₀, φT, hφT, hy₀⟩ := GlobalTheory.T.integralFramedPoint_baseChange_stable E H Dw l Xo c T T₀ io y iT r₀ hr₀ (fun a _ => hv₀ a)
  have ho₀ : OverLa la T₀.V (iT.comp io) (r₀ * e₀) := ho.bc iT hr₀ hv₀
  obtain ⟨T₂, φV, φ₂, r₂, yy, τ, hfe, hbc, hyA, hτ⟩ := hUn la T₀ (iT.comp io) _ ho₀ y₀ hfin
  letI a0 : Algebra c.F T₀.Fr := (iT.comp io).toAlgebra
  letI a2 : Algebra c.F T₂.Fr := (φ₂.comp (iT.comp io)).toAlgebra
  have hφT' : ∀ x, φT x = iT x := fun x => RingHom.congr_fun hφT x
  let φ₂A : T₀.Fr →ₐ[c.F] T₂.Fr := { φ₂ with commutes' := fun _ => rfl }
  have hLaw := (GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c).1
  obtain ⟨hc1, ⟨q, φq, yq, hyq, hφA⟩, -, -⟩ := id hGood
  have hc0 : ∀ (a : c.F) (ha : algebraMap c.F RM.Ω a ∈ A₃), ev₀ ⟨_, ha⟩ = algebraMap c.F T₀.Fr a := fun a ha =>
    hinj (by rw [hev₀]; exact (hcA a).2.trans (hj _).symm)
  let ψ₀ : q.R →ₐ[c.F] T₀.Fr := ModelDimension.Spread.evAlg φq A₃ (fun r => h23 (hφA r)) ev₀ hc0
  obtain ⟨w₂, hw₂⟩ := hLaw.bc _ _ ψ₀ yq
  obtain ⟨w₁, hw₁⟩ := hLaw.bc _ _ φT z'
  have hmem : ∀ r, ∃ hr : ((FinTr.phiAlg Rd).comp φ') r ∈ A₃, (φT.comp ψ') r = ev₀ ⟨_, hr⟩ := fun r => by
    obtain ⟨h1, e1⟩ := hq3 r
    obtain ⟨h2, e2⟩ := hφ ⟨_, h1⟩
    have e3 : j (iT (ψ' r)) = ev₁ ⟨_, h2⟩ := by rw [hj, e1, e2]
    refine ⟨(hA₃ _).2 ⟨h2, _, e3⟩, hinj ?_⟩
    rw [hev₀, AlgHom.comp_apply, hφT', e3]
    rfl
  obtain ⟨t₁, ht₁⟩ := ModelDimension.Spread.spec_bor ((FinTr.phiAlg Rd).comp φ') φq
    (ReciprocityTheory.ChartRestriction.G.PullbackSections.frMap_trans _ _ hq1 hw) hyq htl A₃ (fun r => (hmem r).1) (fun r => h23 (hφA r))
    (fun k => h23 (htA k)) ev₀ (φT.comp ψ') ψ₀ (fun r => (hmem r).2) (fun _ => rfl)
    (ReciprocityTheory.ChartRestriction.G.PullbackSections.frMap_trans _ _ hq2 hw₁) hw₂
  obtain ⟨-, gmul, ginv, -⟩ := GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H Dw l Xo c T₀.Fr
  have hb₀ := gmul _ _ _ _ _ (ginv _ _ _ ht₁) (frBorBC _ _ φT _ _ _ _ _ hq4 hw₁ hy₀)
  obtain ⟨zT, hzT⟩ := hLaw.bc _ _ φ₂A w₂
  obtain ⟨t, hFB⟩ : ∃ t, FrBor t zT yy.1 := ⟨_, frBorBC _ _ φ₂A _ _ _ _ _ hb₀ hzT hbc⟩
  let ev₂ : A₂ →+* PadicAlgCl p := ev₁.comp (Subring.inclusion hle)
  let evT : A₂ →+* T₂.Fr := φ₂.comp (ev₀.comp (Subring.inclusion h23))
  have ho₂ := hfe.overLa ho₀
  have hI : FinRd.IsIntPt Fr A₂ ev₂ la T₂ (φ₂.comp (iT.comp io)) (r₂ * (r₀ * e₀)) yy evT zT t := by
    unfold FinRd.IsIntPt
    refine ⟨hp, ho₂, hyA, ⟨τ, hτ⟩, fun a ha => congrArg φ₂ (hc0 a (h23 ha)), fun x => ?_,
      ⟨q, φq, φ₂A.comp ψ₀, yq, hyq, ReciprocityTheory.ChartRestriction.G.PullbackSections.frMap_trans _ _ hw₂ hzT, fun r => ⟨hφA r, rfl⟩⟩, hFB⟩
    have e1 : ev₂ x = j (ev₀ ⟨x, h23 x.2⟩) := (hev₀ ⟨x, h23 x.2⟩).symm
    have e2 : evT x = φ₂ (ev₀ ⟨x, h23 x.2⟩) := rfl
    rw [e1, e2]
    unfold FinRd.absT
    by_cases hx : ev₀ ⟨x, h23 x.2⟩ = 0
    · rw [hx, map_zero, map_zero, norm_zero, if_pos rfl]
    · rw [if_neg ((map_ne_zero φ₂).2 hx), hnorm _ hx, hfe.2.2.2.2.2]
      have hr2 : (r₂ : ℝ) ≠ 0 := by exact_mod_cast hfe.2.2.2.2.1.ne'
      push_cast
      congr 2
      rw [mul_assoc (r₂ : ℝ), mul_div_mul_left _ _ hr2, mul_assoc]
  let x : (Ref.pjSys Xo c).Pt la := (show Ref.PtU Xo c la from PtV.mk la ho₂ yy hyA τ hτ)
  have hval : ∀ f, (Ref.pjSys Xo c).val x f = nval T₂.V (r₂ * (r₀ * e₀)) (evI yy f) :=
    fun f => Ref.pjSys_val_mk Xo c la ho₂ yy hyA τ hτ f
  have hS := GlobalTheory.T.root_origin_frame_section_bound E H Dw l Xo c O β Y SS RM Sys Fx Or Fr A₂ p z ev₂ hzalg hev la T₂ _ _ yy evT zT t hI x hval
  have hR := GlobalTheory.T.root_origin_frame_degree_bound hG E H Dw l Xo c O β Y SS RM Sys Fx Or Fr hOm hram A₂ p z ev₂ hzalg hev hGood hrat
    la T₂ _ _ yy evT zT t hI
  obtain ⟨rec, h1, h2⟩ := FinRd.read_of_reads hz x (FinRd.tOf_pos la T₂ _ t) hS hR
  refine ⟨z, hzalg, rec, fun b hb hb1 => hev ⟨b, hBA (by simp [hb1])⟩, fun r' => ⟨(h1 r').1, ?_⟩,
    fun a n' hn' g hg => ?_⟩
  · rw [← latExp_eq]
    exact (h1 r').2
  obtain ⟨v, hv1, -, hv2⟩ := h2 a n' hn' g hg
  refine ⟨v, hv1, fun s hs => hv2 s ?_⟩
  obtain ⟨pq, χ, u, hu⟩ := y.2.1
  have k1 : evI y g = χ (g pq u) := Formalism.L2.Pj.evR_of_frMap hLaw.wd hg.1 hu
  have k2 : evI yy g = φ₂ (iT (χ (g pq u))) := by
    rw [← hφT']
    exact Formalism.L2.Pj.evR_of_frMap hLaw.wd hg.1
      (ReciprocityTheory.ChartRestriction.G.PullbackSections.frMap_trans _ φ₂A (ReciprocityTheory.ChartRestriction.G.PullbackSections.frMap_trans _ _ hu hy₀) hbc)
  rw [hval, k2, nval_bc φ₂ hfe.2.2.2.2.1 hfe.2.2.2.2.2, nval_bc iT hr₀ hv₀, ← k1, hs]
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.UniformAllRootOriginBoundStatement
open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniform_all_root_origin_bound : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsGalois ℚ E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (h : GenFrEx Xo c) (e : Comp Xo c → Rul Xo c), CompLaws U h e → Ref.UnifAll Xo c → ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx) (Fr : Small.GenFrame Or) (Z : Comp Xo c) (Rd : Reading Fr h Z), Or.𝔐.OmVB → (∀ p : ℕ, p.Prime → (p : ℤ) ∣ discr E → p ∈ SS) → FinTr.Linked Rd → ∀ B₁ : Finset RM.Ω, ∃ (B₂ : Finset RM.Ω) (B₃ : Finset (Om Z)), ∀ (A : Subring RM.Ω), (↑B₁ : Set RM.Ω) ⊆ A → (↑B₂ : Set RM.Ω) ⊆ A → ∀ (A' : Subring (Om Z)), (↑B₃ : Set (Om Z)) ⊆ A' → ∀ (p : ℕ) [Fact p.Prime] (ev₁ : A →+* PadicAlgCl p), (∀ x, IsAlgebraic ℤ (ev₁ x)) → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e₀ : ℕ) (y : IntFr Xo c T io) (ι : T.Fr →+* PadicAlgCl p) (ev : A' →+* T.Fr), (p : 𝓞 c.F) ∈ la.asIdeal → OverLa la T.V io e₀ → y.IsAlg → (∀ x, ‖ι x‖ = FinRd.absT p la T e₀ x) → FinTr.RegAt h Z io A' ev y.1 → (∀ a : A', ∃ ha : Rd.φ a ∈ A, ev₁ ⟨_, ha⟩ = ι (ev a)) → ∃ z ∈ Small.algPts p (mCoordIdeal RM.y), ∃ rec : RootIx Dw → ℝ, (∀ b (hb : b ∈ A), b ∈ B₁ → Small.HasVal RM.y 0 b z (ev₁ ⟨b, hb⟩)) ∧ (∀ r', 0 < rec r' ∧ |Real.log (Small.supMet (RM.xdeg r') z) - Real.log (rec r')| ≤ (if p ∈ SS then 1 / ((p : ℝ) - 1) + (if p = 2 then 1 else 0) + (padicValInt p (discr E) : ℝ) / Module.finrank ℚ E else 0) * Real.log p) ∧ ∀ (a : WZ E) (n' : Option (RootIx Dw) → ℤ), (∀ j, (n' j : ℝ) = RM.coef (towerWt Dw a) 0 j) → ∀ f ∈ Rec.secZ Xo c a, ∃ v, Small.HasVal RM.y (Top.combLine (RM.line 1) n').a (Fr.rd f * (∏ r', Or.e r' ^ (-n' (some r')))) z v ∧ ∀ s : ℝ, nval T.V e₀ (evI y f) = ((ramOverZ la * s : ℝ) : EReal) → ‖v‖ = (p : ℝ) ^ (-s) * ∏ r', rec r' ^ n' (some r') := by
  first | exact @GlobalTheory.CompanionTheory.Relay.uniform_all_root_origin_bound | exact GlobalTheory.CompanionTheory.Relay.uniform_all_root_origin_bound | (intros; apply GlobalTheory.CompanionTheory.Relay.uniform_all_root_origin_bound <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntegralFrameComponentValue
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntegralFrameComponentValue
open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Plug.FinTr

theorem ev_genValue_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (h : GenFrEx Xo c) (e : Comp Xo c → Rul Xo c), CompLaws U h e → ∀ (Z : Comp Xo c) (ex : Ix Dw → ℤ) (f : Rul Xo c), f ∈ GlobalTheory.AllWt.secZ Xo c ex → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (A : Subring (Om Z)) (ev : A →+* T.Fr), FinTr.RegAt h Z io A ev y.1 → evI y f ≠ 0 → ∀ hb : evC h Z f ∈ A, ev ⟨_, hb⟩ ≠ 0 := by
  intro E _ _ _ H Dw l Xo c r U h e hL Z ex f hf T io y A ev hR hy hb h0
  letI := io.toAlgebra
  obtain ⟨-, q, φ, ψ, yq, z, t, h1, h2, h3, h4⟩ := hR
  have hg : evC h Z f = φ (f q yq) :=
    ReciprocityTheory.ChartRestriction.G.PullbackSections.evalAt_eq_of _ _ hL.evalWD f hf.1 q φ yq (genFr h Z) h1
  have hz : evR Xo c f z = ψ (f q yq) :=
    ReciprocityTheory.ChartRestriction.G.PullbackSections.evalAt_eq_of _ _ hL.evalWD f hf.1 q ψ yq z h2
  obtain ⟨hr, hψ⟩ := h3 (f q yq)
  have hψ0 : ψ (f q yq) = 0 := by
    rw [hψ, ← h0]
    exact congrArg ev (Subtype.ext hg.symm)
  have hS : Out.SecBaseChangeSt := GlobalTheory.abelianSchemeLaws_all.1.secBaseChange
  have hw := GlobalTheory.evR_frBor_of_mem_secZ hS Xo c ex hf T.Fr t z y.1 h4
  apply hy
  show evR Xo c f y.1 = 0
  rw [hw, hz, hψ0, mul_zero]

end GlobalTheory.CompanionTheory.Ar.Plug.FinTr
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntegralFrameComponentValueStatement
open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_frame_component_value : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (h : GenFrEx Xo c) (e : Comp Xo c → Rul Xo c), CompLaws U h e → ∀ (Z : Comp Xo c) (ex : Ix Dw → ℤ) (f : Rul Xo c), f ∈ GlobalTheory.AllWt.secZ Xo c ex → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (A : Subring (Om Z)) (ev : A →+* T.Fr), FinTr.RegAt h Z io A ev y.1 → evI y f ≠ 0 → ∀ hb : evC h Z f ∈ A, ev ⟨_, hb⟩ ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Plug.FinTr.ev_genValue_ne_zero | exact GlobalTheory.CompanionTheory.Ar.Plug.FinTr.ev_genValue_ne_zero | (intros; apply GlobalTheory.CompanionTheory.Ar.Plug.FinTr.ev_genValue_ne_zero <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CompleteDvrPadicEmbedding
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CompleteDvrPadicEmbedding
open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Embed

private theorem norm_le_one_of_isIntegral_int' {q : ℕ} [Fact q.Prime]
    (K₀ : IntermediateField ℚ_[q] (PadicAlgCl q)) (z : K₀) (hz : IsIntegral ℤ_[q] z) :
    ‖(z : PadicAlgCl q)‖ ≤ 1 := by
  obtain ⟨g, hmo, hg⟩ := hz
  have hc : ∀ a : ℤ_[q], ‖((K₀.val : K₀ →+* PadicAlgCl q).comp (algebraMap ℤ_[q] K₀)) a‖ ≤ 1 := by
    intro a
    have h1 : ((K₀.val : K₀ →+* PadicAlgCl q).comp (algebraMap ℤ_[q] K₀)) a
        = algebraMap ℚ_[q] (PadicAlgCl q) (a : ℚ_[q]) := rfl
    rw [h1, PadicAlgCl.norm_extends]
    exact a.2
  have hg' : Polynomial.eval₂ ((K₀.val : K₀ →+* PadicAlgCl q).comp (algebraMap ℤ_[q] K₀))
      (z : PadicAlgCl q) g = 0 := by
    have h := congrArg (fun w => (K₀.val : K₀ →+* PadicAlgCl q) w) hg
    simp only [Polynomial.hom_eval₂, map_zero] at h
    exact h
  by_contra hlt
  push_neg at hlt
  rw [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, hmo.coeff_natDegree, map_one,
    one_mul] at hg'
  have hn : g.natDegree ≠ 0 := by
    intro h0
    rw [h0, Finset.sum_range_zero, pow_zero, zero_add] at hg'
    exact one_ne_zero hg'
  have hsum : ‖∑ i ∈ Finset.range g.natDegree,
      ((K₀.val : K₀ →+* PadicAlgCl q).comp (algebraMap ℤ_[q] K₀)) (g.coeff i) * (z : PadicAlgCl q) ^ i‖
      ≤ ‖(z : PadicAlgCl q)‖ ^ (g.natDegree - 1) := by
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
    intro i hi
    rw [norm_mul, norm_pow]
    have hi' : i ≤ g.natDegree - 1 := by
      have := Finset.mem_range.mp hi
      omega
    calc _ ≤ 1 * ‖(z : PadicAlgCl q)‖ ^ (g.natDegree - 1) :=
          mul_le_mul (hc _) (pow_le_pow_right₀ hlt.le hi') (by positivity) zero_le_one
      _ = _ := one_mul _
  have hyn : (z : PadicAlgCl q) ^ g.natDegree = -∑ i ∈ Finset.range g.natDegree,
      ((K₀.val : K₀ →+* PadicAlgCl q).comp (algebraMap ℤ_[q] K₀)) (g.coeff i) * (z : PadicAlgCl q) ^ i := by
    rw [eq_neg_iff_add_eq_zero, add_comm]
    exact hg'
  have h1 : ‖(z : PadicAlgCl q)‖ ^ g.natDegree ≤ ‖(z : PadicAlgCl q)‖ ^ (g.natDegree - 1) := by
    rw [← norm_pow, hyn, norm_neg]
    exact hsum
  have h2 : ‖(z : PadicAlgCl q)‖ ^ (g.natDegree - 1) < ‖(z : PadicAlgCl q)‖ ^ g.natDegree :=
    pow_lt_pow_right₀ hlt (by omega)
  linarith

theorem exists_isometric_embedding : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : Level H) (c : Coeff l) (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e₀ : ℕ) (p : ℕ) [Fact p.Prime], OverLa la T.V io e₀ → T.FinRes → (p : 𝓞 c.F) ∈ la.asIdeal → ∃ ι : T.Fr →+* PadicAlgCl p, ∀ x, ‖ι x‖ = FinRd.absT p la T e₀ x := by
  intro E _ _ _ H l c la T io e₀ p _ hOver hFin hp
  haveI : Finite (IsLocalRing.ResidueField T.V) := hFin
  obtain ⟨q, hq, K₀, eK, eV, hfin, he⟩ := GlobalTheory.exists_ringEquiv_integralClosure_padicInt T.V T.Fr
  let ι : T.Fr →+* PadicAlgCl q := (K₀.val : K₀ →+* PadicAlgCl q).comp eK.toRingHom
  have hιapp : ∀ x, ι x = ((eK x : K₀) : PadicAlgCl q) := fun x => rfl
  have hV : ∀ v : T.V, ‖ι (algebraMap T.V T.Fr v)‖ ≤ 1 := by
    intro v
    rw [hιapp, he v]
    exact norm_le_one_of_isIntegral_int' K₀ _ (eV v).2
  have hram : 0 < ramOverZ la := GlobalTheory.CompanionTheory.Ar.Rec.FinRd.ram_pos hp
  have he0 : 0 < e₀ := (show 0 < e₀ ∧ _ from hOver).1
  obtain ⟨hmul, hone, hpos, hrange⟩ := GlobalTheory.CompanionTheory.Ar.Rec.FinRd.absT_facts E H l c p la T e₀ he0 hram
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hp0r : (p : ℝ) ≠ 0 := by positivity
  have hN : (0 : ℝ) < (e₀ : ℝ) * (ramOverZ la : ℝ) :=
    mul_pos (Nat.cast_pos.mpr he0) (Nat.cast_pos.mpr hram)
  have hpF : GlobalTheory.CompanionTheory.Ar.Rec.FinRd.absT p la T e₀ (p : T.Fr) = (p : ℝ)⁻¹ := by
    have h := GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.OnW.absT_natCast p la T io e₀ hp hOver
    rwa [map_natCast] at h
  have hpF0 : (p : T.Fr) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hpm : (p : T.V) ∈ IsLocalRing.maximalIdeal T.V := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    rintro ⟨u, hu⟩
    have h1 : GlobalTheory.CompanionTheory.Ar.Rec.FinRd.absT p la T e₀ (algebraMap T.V T.Fr ↑u⁻¹) ≤ 1 :=
      (hrange _).mpr ⟨_, rfl⟩
    have h2 : algebraMap T.V T.Fr ↑u⁻¹ * (p : T.Fr) = 1 := by
      rw [← map_natCast (algebraMap T.V T.Fr) p, ← hu, ← map_mul, Units.inv_mul, map_one]
    have h3 := hmul (algebraMap T.V T.Fr ↑u⁻¹) (p : T.Fr)
    rw [h2, hone, hpF] at h3
    have h4 : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp1
    have h5 : (0 : ℝ) < (p : ℝ)⁻¹ := by positivity
    have h6 := GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.OnW.absT_nonneg p la T e₀ (algebraMap T.V T.Fr ↑u⁻¹)
    nlinarith
  have hqN : ‖ι (q : T.Fr)‖ = (q : ℝ)⁻¹ := by
    rw [map_natCast, ← map_natCast (algebraMap ℚ_[q] (PadicAlgCl q)) q, PadicAlgCl.norm_extends,
      Padic.norm_p]
  have hqm : (q : T.V) ∈ IsLocalRing.maximalIdeal T.V := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    rintro ⟨u, hu⟩
    have h1 := hV ↑u⁻¹
    have h2 : ι (algebraMap T.V T.Fr ↑u⁻¹) * ι (q : T.Fr) = 1 := by
      rw [← map_natCast (algebraMap T.V T.Fr) q, ← hu, ← map_mul ι, ← map_mul (algebraMap T.V T.Fr),
        Units.inv_mul, map_one, map_one]
    have h3 := congrArg norm h2
    rw [norm_mul, norm_one, hqN] at h3
    have hq1 : (1 : ℝ) < q := by exact_mod_cast hq.out.one_lt
    have h4 : (q : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hq1
    have h5 : (0 : ℝ) < (q : ℝ)⁻¹ := by positivity
    have h6 := norm_nonneg (ι (algebraMap T.V T.Fr ↑u⁻¹))
    nlinarith
  have hqp : p = q := by
    by_contra hne
    have hcop : Nat.Coprime q p := (Nat.coprime_primes hq.out (Fact.out)).mpr (Ne.symm hne)
    obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.mpr hcop
    have h1 : (1 : T.V) ∈ IsLocalRing.maximalIdeal T.V := by
      have h := congrArg (Int.cast : ℤ → T.V) hab
      push_cast at h
      rw [← h]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hqm) (Ideal.mul_mem_left _ _ hpm)
    exact (IsLocalRing.maximalIdeal.isMaximal T.V).ne_top ((Ideal.eq_top_iff_one _).mpr h1)
  subst hqp
  have hpN : ‖ι (p : T.Fr)‖ = (p : ℝ)⁻¹ := hqN
  have hpowA : ∀ (y : T.Fr) (n : ℕ), GlobalTheory.CompanionTheory.Ar.Rec.FinRd.absT p la T e₀ (y ^ n)
      = GlobalTheory.CompanionTheory.Ar.Rec.FinRd.absT p la T e₀ y ^ n := by
    intro y n
    induction n with
    | zero => rw [pow_zero, pow_zero, hone]
    | succ n ih => rw [pow_succ, hmul, ih, pow_succ]
  have hpinv : GlobalTheory.CompanionTheory.Ar.Rec.FinRd.absT p la T e₀ (p : T.Fr)⁻¹ = p := by
    have h := hmul (p : T.Fr) (p : T.Fr)⁻¹
    rw [mul_inv_cancel₀ hpF0, hone, hpF, eq_comm, inv_mul_eq_one₀ hp0r] at h
    exact h.symm
  have hiff : ∀ x : T.Fr, ‖ι x‖ ≤ 1 ↔ GlobalTheory.GoodPts.InV T x := by
    intro x
    constructor
    · intro hx
      by_contra hxV
      have hxV' : x ∉ (algebraMap T.V T.Fr).range := hxV
      have hx0 : x ≠ 0 := by
        rintro rfl
        exact hxV' ⟨0, map_zero _⟩
      have hA : 1 < GlobalTheory.CompanionTheory.Ar.Rec.FinRd.absT p la T e₀ x :=
        lt_of_not_ge (fun h => hxV' ((hrange x).mp h))
      have hy0 : x⁻¹ ≠ 0 := inv_ne_zero hx0
      have hAy : GlobalTheory.CompanionTheory.Ar.Rec.FinRd.absT p la T e₀ x⁻¹ < 1 := by
        have h := hmul x x⁻¹
        rw [mul_inv_cancel₀ hx0, hone] at h
        have := hpos _ hy0
        nlinarith
      have hk : (1 : ℝ) ≤ (vV T.V x⁻¹ : ℝ) := by
        have h := hAy
        simp only [GlobalTheory.CompanionTheory.Ar.Rec.FinRd.absT, if_neg hy0] at h
        by_contra hlt
        push_neg at hlt
        have hk0 : vV T.V x⁻¹ ≤ 0 := by
          have : vV T.V x⁻¹ < 1 := by exact_mod_cast hlt
          omega
        have hk0' : (vV T.V x⁻¹ : ℝ) ≤ 0 := by exact_mod_cast hk0
        have hexp : 0 ≤ -((vV T.V x⁻¹ : ℝ) / ((e₀ : ℝ) * (ramOverZ la : ℝ))) := by
          have := div_nonpos_iff.mpr (Or.inr ⟨hk0', hN.le⟩)
          linarith
        have := Real.one_le_rpow hp1.le hexp
        linarith
      have hAN : GlobalTheory.CompanionTheory.Ar.Rec.FinRd.absT p la T e₀ x⁻¹ ^ (e₀ * ramOverZ la) ≤ (p : ℝ)⁻¹ := by
        simp only [GlobalTheory.CompanionTheory.Ar.Rec.FinRd.absT, if_neg hy0]
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), ← Real.rpow_neg_one]
        apply Real.rpow_le_rpow_of_exponent_le hp1.le
        have : -((vV T.V x⁻¹ : ℝ) / ((e₀ : ℝ) * (ramOverZ la : ℝ))) * ((e₀ * ramOverZ la : ℕ) : ℝ)
            = -(vV T.V x⁻¹ : ℝ) := by
          push_cast
          field_simp
        rw [this]
        linarith
      have hz_mem : x⁻¹ ^ (e₀ * ramOverZ la) * (p : T.Fr)⁻¹ ∈ (algebraMap T.V T.Fr).range := by
        apply (hrange _).mp
        rw [hmul, hpowA, hpinv]
        calc GlobalTheory.CompanionTheory.Ar.Rec.FinRd.absT p la T e₀ x⁻¹ ^ (e₀ * ramOverZ la) * (p : ℝ)
            ≤ (p : ℝ)⁻¹ * p := mul_le_mul_of_nonneg_right hAN (by positivity)
          _ = 1 := inv_mul_cancel₀ hp0r
      obtain ⟨w, hw⟩ := hz_mem
      have h1 := hV w
      rw [hw, map_mul, map_pow, map_inv₀, map_inv₀, norm_mul, norm_pow, norm_inv, norm_inv, hpN,
        inv_inv] at h1
      have hxpos : 0 < ‖ι x‖ := norm_pos_iff.mpr ((map_ne_zero ι).mpr hx0)
      have h2 : 1 ≤ ‖ι x‖⁻¹ := (one_le_inv₀ hxpos).mpr hx
      have h4 : 1 ≤ ‖ι x‖⁻¹ ^ (e₀ * ramOverZ la) := one_le_pow₀ h2
      have h5 : 1 * (p : ℝ) ≤ ‖ι x‖⁻¹ ^ (e₀ * ramOverZ la) * p :=
        mul_le_mul_of_nonneg_right h4 (by positivity)
      linarith
    · rintro ⟨v, rfl⟩
      exact hV v
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible T.V
  have hz := GlobalTheory.GeoTie.ReadExt.norm_eq_zpow T ι hiff hπ
  have hvp : (vV T.V (p : T.Fr) : ℝ) = (e₀ : ℝ) * (ramOverZ la : ℝ) := by
    have h := hpF
    simp only [GlobalTheory.CompanionTheory.Ar.Rec.FinRd.absT, if_neg hpF0] at h
    have h2 := congrArg Real.log h
    rw [Real.log_rpow (by positivity), Real.log_inv] at h2
    have hlog : 0 < Real.log p := Real.log_pos hp1
    have h3 : (vV T.V (p : T.Fr) : ℝ) / ((e₀ : ℝ) * (ramOverZ la : ℝ)) = 1 := by
      have h4 : ((vV T.V (p : T.Fr) : ℝ) / ((e₀ : ℝ) * (ramOverZ la : ℝ))) * Real.log p
          = 1 * Real.log p := by linarith
      exact mul_right_cancel₀ hlog.ne' h4
    rwa [div_eq_one_iff_eq hN.ne'] at h3
  have hvpZ : vV T.V (p : T.Fr) = ((e₀ * ramOverZ la : ℕ) : ℤ) := by
    have : (vV T.V (p : T.Fr) : ℝ) = (((e₀ * ramOverZ la : ℕ) : ℤ) : ℝ) := by
      rw [hvp]
      push_cast
      ring
    exact_mod_cast this
  have hrp : ‖ι (algebraMap T.V T.Fr π)‖ ^ (e₀ * ramOverZ la) = (p : ℝ)⁻¹ := by
    rw [← zpow_natCast, ← hvpZ, ← hz _ hpF0, hpN]
  have hNne : e₀ * ramOverZ la ≠ 0 := (Nat.mul_pos he0 hram).ne'
  have hrval : ‖ι (algebraMap T.V T.Fr π)‖ = (p : ℝ) ^ (-(1 / ((e₀ : ℝ) * (ramOverZ la : ℝ)))) := by
    refine (pow_left_inj₀ (n := e₀ * ramOverZ la) (norm_nonneg _) (by positivity) hNne).mp ?_
    rw [hrp, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    have : -(1 / ((e₀ : ℝ) * (ramOverZ la : ℝ))) * ((e₀ * ramOverZ la : ℕ) : ℝ) = -1 := by
      push_cast
      field_simp
    rw [this, Real.rpow_neg_one]
  refine ⟨ι, fun x => ?_⟩
  by_cases hx : x = 0
  · subst hx
    simp [GlobalTheory.CompanionTheory.Ar.Rec.FinRd.absT]
  · rw [hz x hx, hrval]
    simp only [GlobalTheory.CompanionTheory.Ar.Rec.FinRd.absT, if_neg hx]
    rw [← Real.rpow_intCast, ← Real.rpow_mul (by positivity)]
    congr 1
    ring

end GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Embed
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CompleteDvrPadicEmbeddingStatement
open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complete_dvr_padic_embedding : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : Level H) (c : Coeff l) (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e₀ : ℕ) (p : ℕ) [Fact p.Prime], OverLa la T.V io e₀ → T.FinRes → (p : 𝓞 c.F) ∈ la.asIdeal → ∃ ι : T.Fr →+* PadicAlgCl p, ∀ x, ‖ι x‖ = FinRd.absT p la T e₀ x := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Embed.exists_isometric_embedding | exact GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Embed.exists_isometric_embedding | (intros; apply GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Embed.exists_isometric_embedding <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ChartLatticeSpecializationValue
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ChartLatticeSpecializationValue
open ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Rec.FinRd.ChartPt

open MvPolynomial

theorem norm_le_one_of_monic_eval₂ {𝕜 : Type} [NormedField 𝕜] [IsUltrametricDist 𝕜] {R : Type} [CommRing R]
    (φ : R →+* 𝕜) (hφ : ∀ r, ‖φ r‖ ≤ 1) {f : Polynomial R} (hmon : f.Monic) {x : 𝕜}
    (hf : f.eval₂ φ x = 0) : ‖x‖ ≤ 1 := by
  by_contra! h
  rw [hmon.as_sum] at hf
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_finsetSum,
    Polynomial.eval₂_mul, Polynomial.eval₂_C] at hf
  have hsum : x ^ f.natDegree = -∑ i ∈ Finset.range f.natDegree, φ (f.coeff i) * x ^ i :=
    eq_neg_of_add_eq_zero_left hf
  have hpos : 0 < f.natDegree := by
    rcases Nat.eq_zero_or_pos f.natDegree with h0 | h0
    · rw [h0] at hsum
      simp at hsum
    · exact h0
  have hle : ‖∑ i ∈ Finset.range f.natDegree, φ (f.coeff i) * x ^ i‖ ≤ ‖x‖ ^ (f.natDegree - 1) := by
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun i hi => ?_
    rw [norm_mul, norm_pow]
    have hi' : i ≤ f.natDegree - 1 := by
      have := Finset.mem_range.mp hi
      omega
    calc ‖φ (f.coeff i)‖ * ‖x‖ ^ i ≤ 1 * ‖x‖ ^ (f.natDegree - 1) :=
          mul_le_mul (hφ _) (pow_le_pow_right₀ h.le hi') (by positivity) zero_le_one
      _ = ‖x‖ ^ (f.natDegree - 1) := one_mul _
  have h1 : ‖x‖ ^ f.natDegree ≤ ‖x‖ ^ (f.natDegree - 1) := by
    rw [← norm_pow, hsum, norm_neg]
    exact hle
  have h2 : ‖x‖ ^ (f.natDegree - 1) < ‖x‖ ^ f.natDegree := pow_lt_pow_right₀ h (by omega)
  linarith

section Ring

variable {Ω : Type} [Field Ω] {𝕜 : Type} [NormedField 𝕜] [IsUltrametricDist 𝕜]

def unitBall (A : Subring Ω) (ev : A →+* 𝕜) : Subring Ω where
  carrier := {x | ∃ h : x ∈ A, ‖ev ⟨x, h⟩‖ ≤ 1}
  mul_mem' := by
    rintro a b ⟨ha, ha1⟩ ⟨hb, hb1⟩
    refine ⟨A.mul_mem ha hb, ?_⟩
    have e : (⟨a * b, A.mul_mem ha hb⟩ : A) = ⟨a, ha⟩ * ⟨b, hb⟩ := rfl
    rw [e, map_mul, norm_mul]
    exact mul_le_one₀ ha1 (norm_nonneg _) hb1
  one_mem' := by
    refine ⟨A.one_mem, ?_⟩
    have e : (⟨1, A.one_mem⟩ : A) = 1 := rfl
    rw [e, map_one, norm_one]
  add_mem' := by
    rintro a b ⟨ha, ha1⟩ ⟨hb, hb1⟩
    refine ⟨A.add_mem ha hb, ?_⟩
    have e : (⟨a + b, A.add_mem ha hb⟩ : A) = ⟨a, ha⟩ + ⟨b, hb⟩ := rfl
    rw [e, map_add (f := _)]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha1 hb1)
  zero_mem' := by
    refine ⟨A.zero_mem, ?_⟩
    have e : (⟨0, A.zero_mem⟩ : A) = 0 := rfl
    rw [e, map_zero, norm_zero]
    exact zero_le_one
  neg_mem' := by
    rintro a ⟨ha, ha1⟩
    refine ⟨A.neg_mem ha, ?_⟩
    have e : (⟨-a, A.neg_mem ha⟩ : A) = -⟨a, ha⟩ := rfl
    rw [e, map_neg, norm_neg]
    exact ha1

theorem norm_ev_le_one (A : Subring Ω) (ev : A →+* 𝕜) (R : Subalgebra ℤ Ω)
    (hR : ∀ x ∈ R, ∃ h : x ∈ A, ‖ev ⟨x, h⟩‖ ≤ 1) {t : Ω} (ht : t ∈ integralClosure R Ω) (hb : t ∈ A) :
    ‖ev ⟨t, hb⟩‖ ≤ 1 := by
  obtain ⟨f, hmon, hf⟩ := ht
  let ψ : R →+* A :=
    { toFun := fun r => ⟨r, (hR r r.2).1⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have h1 : f.eval₂ ψ ⟨t, hb⟩ = 0 := by
    apply Subtype.ext
    exact (Polynomial.hom_eval₂ f ψ A.subtype ⟨t, hb⟩).trans hf
  have h2 : f.eval₂ (ev.comp ψ) (ev ⟨t, hb⟩) = 0 := by
    rw [← Polynomial.hom_eval₂, h1, map_zero]
  exact norm_le_one_of_monic_eval₂ (ev.comp ψ) (fun r => (hR r r.2).2) hmon h2

end Ring

section Pt

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
  {y : (Σ k, ι k) → Ω} {𝕜 : Type} [Field 𝕜] {z : (Σ k, ι k) → 𝕜}

theorem isMultiHomog_X_single [DecidableEq K] (k : K) (i : ι k) :
    IsMultiHomog (X ⟨k, i⟩ : MRing ι) (Pi.single k 1) := by
  classical
  intro m hm b
  rw [support_X, Finset.mem_singleton] at hm
  subst hm
  by_cases hb : b = k
  · subst hb
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      rw [Finsupp.single_apply, if_neg]
      intro h
      exact hj (by simpa using h.symm)
    · simp
  · rw [Pi.single_eq_of_ne hb]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [Finsupp.single_apply, if_neg]
    intro h
    exact hb (congrArg Sigma.fst h).symm

theorem hasVal_coord [DecidableEq K] (k : K) (i : ι k) :
    Small.HasVal y (Pi.single k 1) (y ⟨k, i⟩) z (z ⟨k, i⟩) := by
  refine ⟨Pi.single k 1, 0, X ⟨k, i⟩, 1, isMultiHomog_X_single k i, ?_, fun b => ?_, by simp, by simp, by simp⟩
  · exact ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_one
  · by_cases hb : b = k
    · subst hb
      simp
    · simp [Pi.single_eq_of_ne hb]

theorem hasVal_ratio_coord {k : K} (i c : ι k) (hy : y ⟨k, c⟩ ≠ 0) (hz : z ⟨k, c⟩ ≠ 0) :
    Small.HasVal y 0 (y ⟨k, i⟩ / y ⟨k, c⟩) z (z ⟨k, i⟩ / z ⟨k, c⟩) := by
  classical
  refine ⟨Pi.single k 1, Pi.single k 1, X ⟨k, i⟩, X ⟨k, c⟩, isMultiHomog_X_single k i, isMultiHomog_X_single k c,
    fun b => by simp, ?_, by simpa using hz, ?_⟩
  · simp only [aeval_X]
    field_simp
  · simp only [aeval_X]
    field_simp

theorem coord_ne_zero (hz : z ∈ Small.ptsOver 𝕜 (mCoordIdeal y)) (p : Σ k, ι k) (h : z p ≠ 0) : y p ≠ 0 := by
  intro h0
  have hm : (X p : MRing ι) ∈ mCoordIdeal y := by
    show mConeMap y (X p) = 0
    simp [mConeMap, h0]
  exact h (by simpa using hz.2 _ hm)

end Pt

theorem exists_hasVal_norm_le_supMet :
    ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (𝕜 : Type) [NormedField 𝕜] [IsUltrametricDist 𝕜] (z : (Σ k, ι k) → 𝕜), z ∈ Small.ptsOver 𝕜 (mCoordIdeal y) → ∀ (A : Subring Ω) (ev : A →+* 𝕜) (a : K → ℤ), ∀ s ∈ chartLatNm y a 1, (∀ (c : ∀ k, ι k), (∀ k, y ⟨k, c k⟩ ≠ 0) → (∀ k i, ∃ hb : y ⟨k, i⟩ / y ⟨k, c k⟩ ∈ A, Small.HasVal y 0 (y ⟨k, i⟩ / y ⟨k, c k⟩) z (ev ⟨_, hb⟩)) ∧ ∃ hb : s * ∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * a k)) ∈ A, Small.HasVal y 0 (s * ∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * a k))) z (ev ⟨_, hb⟩)) → ∃ w, Small.HasVal y a s z w ∧ ‖w‖ ≤ Small.supMet a z := by
  classical
  intro K _ ι _ Ω _ y 𝕜 _ _ z hz A ev a s hs H
  have hc : ∀ k, ∃ c : ι k, ∀ i, ‖z ⟨k, i⟩‖ ≤ ‖z ⟨k, c⟩‖ := fun k => by
    obtain ⟨i0, -⟩ := hz.1 k
    haveI : Nonempty (ι k) := ⟨i0⟩
    exact Finite.exists_max (fun i => ‖z ⟨k, i⟩‖)
  choose c hc using hc
  have hzc : ∀ k, z ⟨k, c k⟩ ≠ 0 := fun k h0 => by
    obtain ⟨i0, hi0⟩ := hz.1 k
    have h1 := hc k i0
    rw [h0, norm_zero] at h1
    exact hi0 (norm_le_zero_iff.1 h1)
  have hyc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => coord_ne_zero hz _ (hzc k)
  obtain ⟨hr, hb, hv⟩ := H c hyc
  have hle : chartRingZ y c ≤ subalgebraOfSubring (unitBall A ev) := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨⟨k, i⟩, rfl⟩
    obtain ⟨hb', hv'⟩ := hr k i
    have e := Small.ReadFinTest.hasVal_unique hz hv' (hasVal_ratio_coord i (c k) (hyc k) (hzc k))
    refine ⟨hb', ?_⟩
    rw [e, norm_div]
    exact div_le_one_of_le₀ (hc k i) (norm_nonneg _)
  have hn : ‖ev ⟨_, hb⟩‖ ≤ 1 := norm_ev_le_one A ev _ (fun x hx => hle hx) (hs c hyc) hb
  refine ⟨ev ⟨_, hb⟩ * ∏ k, z ⟨k, c k⟩ ^ a k, ?_, ?_⟩
  · have hp : ∀ k ∈ (Finset.univ : Finset K), Small.HasVal y (a k • (Pi.single k 1 : K → ℤ)) (y ⟨k, c k⟩ ^ a k) z
        (z ⟨k, c k⟩ ^ a k) := fun k _ => hv_zpow hz (hasVal_coord k (c k)) (hyc k) (hzc k) (a k)
    have h3 := hv_mul hv (hv_prod Finset.univ hp)
    have e1 : (0 : K → ℤ) + ∑ k, a k • (Pi.single k 1 : K → ℤ) = a := by
      funext b
      simp [Finset.sum_apply, Pi.single_apply]
    have e2 : (s * ∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * a k))) * ∏ k, y ⟨k, c k⟩ ^ a k = s := by
      rw [mul_assoc, ← Finset.prod_mul_distrib]
      have : ∀ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * a k)) * y ⟨k, c k⟩ ^ a k = 1 := fun k => by
        rw [← zpow_add₀ (hyc k)]
        simp
      rw [Finset.prod_congr rfl fun k _ => this k, Finset.prod_const_one, mul_one]
    rw [e1, e2] at h3
    exact h3
  · have hm : Small.supMet a z = ∏ k, ‖z ⟨k, c k⟩‖ ^ a k := by
      unfold Small.supMet
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [le_antisymm ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 (hc k))
        (norm_le_pi_norm (fun i => z ⟨k, i⟩) (c k))]
    rw [norm_mul, norm_prod, hm]
    simp only [norm_zpow]
    exact mul_le_of_le_one_left (Finset.prod_nonneg fun k _ => by positivity) hn

end GlobalTheory.CompanionTheory.Ar.Rec.FinRd.ChartPt
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ChartLatticeSpecializationValueStatement
open ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_lattice_specialization_value : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (𝕜 : Type) [NormedField 𝕜] [IsUltrametricDist 𝕜] (z : (Σ k, ι k) → 𝕜), z ∈ Small.ptsOver 𝕜 (mCoordIdeal y) → ∀ (A : Subring Ω) (ev : A →+* 𝕜) (a : K → ℤ), ∀ s ∈ chartLatNm y a 1, (∀ (c : ∀ k, ι k), (∀ k, y ⟨k, c k⟩ ≠ 0) → (∀ k i, ∃ hb : y ⟨k, i⟩ / y ⟨k, c k⟩ ∈ A, Small.HasVal y 0 (y ⟨k, i⟩ / y ⟨k, c k⟩) z (ev ⟨_, hb⟩)) ∧ ∃ hb : s * ∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * a k)) ∈ A, Small.HasVal y 0 (s * ∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * a k))) z (ev ⟨_, hb⟩)) → ∃ w, Small.HasVal y a s z w ∧ ‖w‖ ≤ Small.supMet a z := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Rec.FinRd.ChartPt.exists_hasVal_norm_le_supMet | exact GlobalTheory.CompanionTheory.Ar.Rec.FinRd.ChartPt.exists_hasVal_norm_le_supMet | (intros; apply GlobalTheory.CompanionTheory.Ar.Rec.FinRd.ChartPt.exists_hasVal_norm_le_supMet <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.UniformAllTowerBound
open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi

namespace GlobalTheory.CompanionTheory.Ar.Plug
open FinTr

theorem vs_fin : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsGalois ℚ E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (h : GenFrEx Xo c) (e : Comp Xo c → Rul Xo c), CompLaws U h e → Ref.UnifAll Xo c → ∀ (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : Top.RootTower (CMType H) (Dw.p + Dw.q)) (o : Top.GoodOrigin Y T) (B : ℕ) (b : T.Comp) (Fr : Small.GenFrame (o.toTowerOrigin.Or B b)) (Z : Comp Xo c) (Rd : Reading Fr h Z) (u : GlobalTheory.AllWt.Weight Dw), ∀ s ∈ chartLatNm (T.M B b).y (degOf (T.M B b) u) 1, ∀ f ∈ GlobalTheory.AllWt.secZ Xo c (GlobalTheory.AllWt.exOf Dw u 0), f ∈ GlobalTheory.AllWt.suppOn Z → evC h Z f = trOf Rd u s → ∀ (p : ℕ) (la : HeightOneSpectrum (𝓞 c.F)), p.Prime → ((p : ℕ) : 𝓞 c.F) ∈ la.asIdeal → ∀ v ∈ (GlobalTheory.CompHt.recVals Xo c).1 la, ((-((vLa la (p : c.F) : ℝ) * (if p ∈ o.toTowerOrigin.S B then exTwo E p else 0) * GlobalTheory.CovHt.l1 u) : ℝ) : EReal) ≤ v f := by
  intro hG E _ _ _ _ H Dw l Xo c r U h e hL hUn Y _ T o B b Fr Z Rd u s hs f hf hfZ hev p la hp hla v hv
  obtain ⟨⟨q, T₀, io, e₀, ho, y, hy, η, hη, rfl⟩, rfl⟩ := hv
  show _ ≤ nval T₀.V e₀ (evI y f)
  haveI hpf : Fact p.Prime := ⟨hp⟩
  by_cases hy0 : evI y f = 0
  · rw [hy0, nval_zero]; exact le_top
  have hon : (letI := io.toAlgebra; GlobalTheory.AllWt.LiesOn Z y.1) := by
    letI := io.toAlgebra
    by_contra hc
    exact hy0 (GlobalTheory.AllWt.mem_suppOn.1 hfZ T₀.Fr y.1 ((GlobalTheory.AllWt.liesOff_iff Z y.1).2 hc))
  have hLk := GlobalTheory.T.good_origin_model_component_bound hG E H Dw l Xo c r U h e hL Y T o _ _ Y _ _ _ _ (o.toTowerOrigin.Or B b) Fr Z Rd
  have hram : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ discr E → p ∈ o.toTowerOrigin.S B := fun p hp hd => by
    rw [o.toTowerOrigin.S_iff]
    refine ⟨hp, Or.inr ((o.toTowerOrigin.bad_iff p).2 ⟨hp, ?_⟩)⟩
    exact Dvd.dvd.mul_right (Dvd.dvd.mul_left hd 2) _
  classical
  let RM := T.M B b
  let Ow := o.toTowerOrigin.Or B b
  let x : RM.Ω := s / gauge Rd u
  let sc : (∀ k, RM.ι k) → RM.Ω := fun c' => s * ∏ k, RM.y ⟨k, c' k⟩ ^ (-(((1 : ℕ) : ℤ) * degOf RM u k))
  let rt : (∀ k, RM.ι k) × (Σ k, RM.ι k) → RM.Ω := fun q => RM.y q.2 / RM.y ⟨q.2.1, q.1 q.2.1⟩
  let B₁ : Finset RM.Ω := {x, Rd.φ (evC h Z f)} ∪ Finset.univ.image sc ∪ Finset.univ.image rt
  obtain ⟨B₂, B₃, hR⟩ := GlobalTheory.T.uniform_all_root_origin_bound hG E H Dw l Xo c r U h e hL hUn _ _ Y _ RM _ _ Ow Fr Z Rd (o.omVB B b) hram hLk B₁
  have hfinr : 0 < (letI := Rd.φ.toAlgebra; Module.finrank (Om Z) RM.Ω) := by
    rw [Rd.deg]; exact Test.deg_pos Ow
  have hfin : (letI := Rd.φ.toAlgebra; FiniteDimensional (Om Z) RM.Ω) := by
    letI := Rd.φ.toAlgebra
    exact Module.finite_of_finrank_pos hfinr
  haveI : CharZero (Om Z) := charZero_of_injective_algebraMap (algebraMap c.F (Om Z)).injective
  obtain ⟨Btr, hTr⟩ := GlobalTheory.T.trace_integral_subring_extension (Om Z) RM.Ω Rd.φ (B₁ ∪ B₂) x hfin
  obtain ⟨T', io', e', y', A', ev, ho', hy', hval, hB, -, halg, hreg⟩ :=
    GlobalTheory.T.weight_section_component_value hG E H Dw l Xo c r U h e hL Y Z u f hf (Btr ∪ B₃) la T₀ io e₀ ho y hy hon hy0

  have hB3 : (↑B₃ : Set (Om Z)) ⊆ A' := fun b hb =>
    hB (Finset.mem_coe.2 (Finset.mem_union_right _ (Finset.mem_coe.1 hb)))
  obtain ⟨ι, hι⟩ := GlobalTheory.T.complete_dvr_padic_embedding E H l c la T' io' e' p ho' hy' hla
  obtain ⟨A, hA, hB0, hx, ht, hspec⟩ := hTr A' (fun b hb =>
    hB (Finset.mem_coe.2 (Finset.mem_union_left _ (Finset.mem_coe.1 hb))))
  have halgC : ∀ a, IsAlgebraic ℤ ((ι.comp ev) a) := fun a => by
    obtain ⟨P, hP0, hP⟩ := halg a
    refine ⟨P, hP0, ?_⟩
    rw [Polynomial.aeval_def] at hP ⊢
    have e2 : ι.comp (algebraMap ℤ T'.Fr) = algebraMap ℤ (PadicAlgCl p) := RingHom.ext_int _ _
    show Polynomial.eval₂ (algebraMap ℤ (PadicAlgCl p)) (ι (ev a)) P = 0
    rw [← e2, ← Polynomial.hom_eval₂, hP, map_zero]
  obtain ⟨n, ev', h1, h2, h3⟩ := hspec (PadicAlgCl p) (ι.comp ev) halgC
  have hcf : evC h Z f ∈ A' := by
    have e1 : evC h Z f = (letI := Rd.φ.toAlgebra; Algebra.trace (Om Z) RM.Ω x) := hev
    rw [e1]; exact ht
  have hy'0 : evI y' f ≠ 0 := fun h0 => by
    rw [h0, nval_zero, nval_of_ne hy0] at hval
    exact EReal.coe_ne_top _ hval.symm
  have hW0 := GlobalTheory.T.integral_frame_component_value E H Dw l Xo c r U h e hL Z _ f hf T' io' y' A' ev hreg hy'0 hcf
  obtain ⟨W, hWdef⟩ : ∃ W, W = ι (ev ⟨_, hcf⟩) := ⟨_, rfl⟩
  have hW : W ≠ 0 := by rw [hWdef]; exact (map_ne_zero ι).2 hW0
  have hWsum : W = ∑ j, ev' j ⟨x, hx⟩ := by
    have e1 : (⟨evC h Z f, hcf⟩ : A') = ⟨_, ht⟩ := Subtype.ext hev
    rw [hWdef, e1]
    exact h3
  have hra : 0 < ramOverZ la := FinRd.ram_pos hla
  have hra' : (0 : ℝ) < ramOverZ la := by exact_mod_cast hra
  obtain ⟨s₀, hs₀⟩ : ∃ s₀ : ℝ, nval T'.V e' (evI y' f) = ((ramOverZ la * s₀ : ℝ) : EReal) :=
    ⟨((vV T'.V (evI y' f) : ℝ) / e') / ramOverZ la, by
      rw [nval_of_ne hy'0]; congr 1; field_simp⟩
  obtain ⟨hw1, -, -, hw4, hw5, -⟩ := GlobalTheory.T.tower_weight_of_zero E H Dw l Xo c RM u
  have hn : ∀ j, (nOf u j : ℝ) = RM.coef (towerWt Dw (GlobalTheory.AllWt.wtOf Dw u 0).1) 0 j := by
    rw [hw1]; exact hw4
  have hL1 : ∑ r : RootIx Dw, |((-u r.1 r.2 : ℤ) : ℝ)| = GlobalTheory.CovHt.l1 u := by
    rw [hw5]
    simp [Top.l1, reW, Fintype.sum_prod_type]
  have hfsec : f ∈ Rec.secZ Xo c (GlobalTheory.AllWt.wtOf Dw u 0).1 := by
    rw [← Test.secZ_eq]; exact hf
  have hpp : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hlog : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  obtain ⟨Cθ, hCθ⟩ : ∃ Cθ : ℝ, Cθ = if p ∈ o.toTowerOrigin.S B then 1 / ((p : ℝ) - 1) + (if p = 2 then 1 else 0) +
      (padicValInt p (discr E) : ℝ) / Module.finrank ℚ E else 0 := ⟨_, rfl⟩
  obtain ⟨Ee, hEe⟩ : ∃ Ee : ℝ, Ee = Real.exp (GlobalTheory.CovHt.l1 u * (Cθ * Real.log p)) := ⟨_, rfl⟩
  have hEp : 0 < Ee := by rw [hEe]; exact Real.exp_pos _
  have hAB1 : ∀ b ∈ B₁, b ∈ A := fun b hb => hB0 (Finset.mem_coe.2 (Finset.mem_union_left _ hb))
  have hmx : x ∈ B₁ := Finset.mem_union_left _ (Finset.mem_union_left _ (by simp))
  have hmφ : Rd.φ (evC h Z f) ∈ B₁ := Finset.mem_union_left _ (Finset.mem_union_left _ (by simp))
  have hmsc : ∀ c', sc c' ∈ B₁ := fun c' =>
    Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image_of_mem sc (Finset.mem_univ c')))
  have hmrt : ∀ q, rt q ∈ B₁ := fun q =>
    Finset.mem_union_right _ (Finset.mem_image_of_mem rt (Finset.mem_univ q))
  have hj : ∀ j, ‖ev' j ⟨x, hx⟩‖ ≤ (p : ℝ) ^ s₀ * (Ee * ‖W‖) := by
    intro j
    obtain ⟨z, hz, rec, hHV, hrec, hrd⟩ := hR A (fun b hb => hAB1 b (Finset.mem_coe.1 hb))
      (fun b hb => hB0 (Finset.mem_coe.2 (Finset.mem_union_right _ (Finset.mem_coe.1 hb)))) A' hB3 p (ev' j) (h2 j)
      la T' io' e' y' ι ev hla ho' hy' hι hreg (fun a' => ⟨hA a', h1 j a'⟩)
    have hHV' : ∀ b (hb : b ∈ B₁), Small.HasVal RM.y 0 b z (ev' j ⟨b, hAB1 b hb⟩) := fun b hb => hHV b _ hb
    obtain ⟨w, hw, hwle⟩ := GlobalTheory.T.chart_lattice_specialization_value RM.K RM.ι RM.Ω RM.y (PadicAlgCl p) z hz.1 A (ev' j) (degOf RM u) s hs
      (fun c' _ => ⟨fun k i => ⟨hAB1 _ (hmrt (c', ⟨k, i⟩)), hHV' _ (hmrt (c', ⟨k, i⟩))⟩,
        ⟨hAB1 _ (hmsc c'), hHV' _ (hmsc c')⟩⟩)
    obtain ⟨v, hv, hvn⟩ := hrd _ (nOf u) hn f hfsec
    have hx1 := hHV' x hmx
    have hφ := hHV' _ hmφ
    have hW' : ev' j ⟨Rd.φ (evC h Z f), hAB1 _ hmφ⟩ = W := by rw [hWdef]; exact h1 j ⟨_, hcf⟩
    rw [hW'] at hφ
    have hid : s * Rd.φ (evC h Z f) = x * (Fr.rd f * ∏ r, Ow.e r ^ (-nOf u (some r))) := by
      rw [← Test.gauge_mul Rd u hf]
      have hg := Test.gauge_ne_zero Rd u
      simp only [x]
      field_simp
    have ha := FinRd.hv_mul hw hφ
    have hb := FinRd.hv_mul hx1 hv
    rw [add_zero] at ha
    rw [zero_add, ← hid] at hb
    have heq : w * W = ev' j ⟨x, hAB1 x hmx⟩ * v := Small.ReadFinTest.hasVal_unique hz.1 ha hb
    have hsp : ∀ a : RM.K → ℤ, 0 < Small.supMet a z := fun a =>
      Finset.prod_pos fun k _ => zpow_pos (norm_pos_iff.2 fun h0 => by
        obtain ⟨i, hi⟩ := hz.1.1 k
        exact hi (congrFun h0 i)) _
    have hsup : Small.supMet (degOf RM u) z ≤ (∏ r, rec r ^ nOf u (some r)) * Ee := by
      rw [Test.degOf_eq, supMet_sum _ _ z hz.1.1, hEe, ← hL1]
      exact prod_zpow_le (fun r => Small.supMet (RM.xdeg r) z) rec (fun r => -u r.1 r.2) _ (fun r => hsp _)
        (fun r => (hrec r).1) (fun r => by rw [← hCθ] at *; exact (hrec r).2)
    have hP : 0 < ∏ r, rec r ^ nOf u (some r) := Finset.prod_pos fun r _ => zpow_pos (hrec r).1 _
    have hvv := hvn s₀ hs₀
    have h5 : ‖ev' j ⟨x, hx⟩‖ * ((p : ℝ) ^ (-s₀) * ∏ r, rec r ^ nOf u (some r)) ≤
        ((∏ r, rec r ^ nOf u (some r)) * Ee) * ‖W‖ := by
      rw [← hvv, ← norm_mul, ← heq, norm_mul]
      exact mul_le_mul_of_nonneg_right (hwle.trans hsup) (norm_nonneg _)
    have h6 : ‖ev' j ⟨x, hx⟩‖ * (p : ℝ) ^ (-s₀) ≤ Ee * ‖W‖ := by
      refine le_of_mul_le_mul_right ?_ hP
      calc _ = ‖ev' j ⟨x, hx⟩‖ * ((p : ℝ) ^ (-s₀) * ∏ r, rec r ^ nOf u (some r)) := by ring
        _ ≤ _ := h5
        _ = _ := by ring
    have h7 : (p : ℝ) ^ s₀ * (p : ℝ) ^ (-s₀) = 1 := by
      rw [← Real.rpow_add hpp]; simp
    calc ‖ev' j ⟨x, hx⟩‖ = (p : ℝ) ^ s₀ * (‖ev' j ⟨x, hx⟩‖ * (p : ℝ) ^ (-s₀)) := by
          linear_combination (-‖ev' j ⟨x, hx⟩‖) * h7
      _ ≤ _ := mul_le_mul_of_nonneg_left h6 (Real.rpow_pos_of_pos hpp _).le
  have hWle : ‖W‖ ≤ (p : ℝ) ^ s₀ * (Ee * ‖W‖) := by
    have h0 : 0 ≤ (p : ℝ) ^ s₀ * (Ee * ‖W‖) := by positivity
    have := IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg h0 (fun j (_ : j ∈ Finset.univ) => hj j)
    rwa [← hWsum] at this
  have hWp : 0 < ‖W‖ := norm_pos_iff.2 hW
  have h8 : 1 ≤ (p : ℝ) ^ s₀ * Ee := by
    refine le_of_mul_le_mul_right ?_ hWp
    calc 1 * ‖W‖ = ‖W‖ := one_mul _
      _ ≤ _ := hWle
      _ = _ := by ring
  have h9 : 0 ≤ s₀ + GlobalTheory.CovHt.l1 u * Cθ := by
    rw [Real.rpow_def_of_pos hpp, hEe, ← Real.exp_add] at h8
    have h10 := Real.exp_le_exp.1 (by simpa using h8 : Real.exp 0 ≤ _)
    have h11 : 0 ≤ Real.log p * (s₀ + GlobalTheory.CovHt.l1 u * Cθ) := by linarith
    exact (mul_nonneg_iff_of_pos_left hlog).1 h11
  have hres : Formalism.L2.Pj.resCharOf la = p := by
    by_contra hne
    refine Formalism.L2.Pj.Crude.crv_not_mem la (fun hd => hne ?_) hla
    exact (Nat.prime_dvd_prime_iff_eq (Formalism.L2.Pj.Crude.resCharOf_prime la) hp).1 hd
  have hvp : (vLa la (p : c.F) : ℝ) = ramOverZ la := by
    have := Formalism.L2.Pj.Crude.crv_vLa_char la
    rw [hres] at this
    exact_mod_cast this
  have hl0 : 0 ≤ GlobalTheory.CovHt.l1 u := by
    rw [← hL1]; exact Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hex : Cθ ≤ if p ∈ o.toTowerOrigin.S B then exTwo E p else 0 := by
    rw [hCθ]
    split_ifs with h1' h2'
    · simp only [exTwo, GlobalTheory.CovHt.htEx, if_pos h2', padicValInt, Nat.padicValNat_def]
      have : (0 : ℝ) ≤ (multiplicity p (discr E).natAbs : ℝ) / Module.finrank ℚ E := by positivity
      linarith
    · simp only [exTwo, GlobalTheory.CovHt.htEx, if_neg h2', padicValInt, Nat.padicValNat_def]
      have : (0 : ℝ) ≤ (multiplicity p (discr E).natAbs : ℝ) / Module.finrank ℚ E := by positivity
      linarith
    · exact le_rfl
  rw [← hval, hs₀]
  refine EReal.coe_le_coe_iff.2 ?_
  rw [hvp]
  have h12 := mul_nonneg hra'.le h9
  have h13 := mul_nonneg (mul_nonneg hra'.le hl0) (sub_nonneg.2 hex)
  nlinarith [h12, h13]

end GlobalTheory.CompanionTheory.Ar.Plug
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.UniformAllTowerBoundStatement
open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniform_all_tower_bound : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsGalois ℚ E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (h : GenFrEx Xo c) (e : Comp Xo c → Rul Xo c), CompLaws U h e → Ref.UnifAll Xo c → ∀ (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : Top.RootTower (CMType H) (Dw.p + Dw.q)) (o : Top.GoodOrigin Y T) (B : ℕ) (b : T.Comp) (Fr : Small.GenFrame (o.toTowerOrigin.Or B b)) (Z : Comp Xo c) (Rd : Reading Fr h Z) (_ : GeoRead Rd) (u : GlobalTheory.AllWt.Weight Dw), ∀ s ∈ chartLatNm (T.M B b).y (degOf (T.M B b) u) 1, ∀ f ∈ GlobalTheory.AllWt.secZ Xo c (GlobalTheory.AllWt.exOf Dw u 0), f ∈ GlobalTheory.AllWt.suppOn Z → evC h Z f = trOf Rd u s → ∀ (p : ℕ) (la : HeightOneSpectrum (𝓞 c.F)), p.Prime → ((p : ℕ) : 𝓞 c.F) ∈ la.asIdeal → ∀ v ∈ (GlobalTheory.CompHt.recVals Xo c).1 la, ((-((vLa la (p : c.F) : ℝ) * (if p ∈ o.toTowerOrigin.S B then exTwo E p else 0) * GlobalTheory.CovHt.l1 u) : ℝ) : EReal) ≤ v f := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Plug.vs_fin | exact GlobalTheory.CompanionTheory.Ar.Plug.vs_fin | (intros; apply GlobalTheory.CompanionTheory.Ar.Plug.vs_fin <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.UniformNormAllTowerBound
open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi

namespace GlobalTheory.CompanionTheory.Ar.Plug

theorem descent_small : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsGalois ℚ E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (h : GenFrEx Xo c) (e : Comp Xo c → Rul Xo c), CompLaws U h e → Ref.UnifAll Xo c → ∀ x : ℝ, (∀ σ, GoodEmb c σ → ∀ k (τ : E →+* ℂ), ‖τ ((U σ).X k).ξ0‖ = x) → ∀ (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : Top.RootTower (CMType H) (Dw.p + Dw.q)) (o : Top.GoodOrigin Y T) (B : ℕ) (b : T.Comp) (Fr : Small.GenFrame (o.toTowerOrigin.Or B b)) (Z : Comp Xo c) (Rd : Reading Fr h Z) (_ : GeoRead Rd) (u : GlobalTheory.AllWt.Weight Dw) (R : ℝ), (∀ τ, StrictAnti (u τ)) → 0 ≤ R → ∀ s ∈ modelSmall (o.toTowerOrigin.Or B b) u R, ∃ f ∈ GlobalTheory.AllWt.cuspOn U Z (GlobalTheory.AllWt.wtOf Dw u 0), evC h Z f = trOf Rd u s ∧ (∀ σ, GoodEmb c σ → ∀ z ∈ GlobalTheory.AllWt.framesOn (U σ) Z, GlobalTheory.AllWt.homN (U σ) x (GlobalTheory.AllWt.wtOf Dw u 0) f z ≤ (o.toTowerOrigin.Or B b).Fl.deg * R) ∧ ∀ (p : ℕ) (la : HeightOneSpectrum (𝓞 c.F)), p.Prime → ((p : ℕ) : 𝓞 c.F) ∈ la.asIdeal → ∀ v ∈ (GlobalTheory.CompHt.recVals Xo c).1 la, ((-((vLa la (p : c.F) : ℝ) * (if p ∈ o.toTowerOrigin.S B then exTwo E p else 0) * GlobalTheory.CovHt.l1 u) : ℝ) : EReal) ≤ v f := by
  intro hG E _ _ _ _ H Dw l Xo c r U h e hL hU x hx Y _ T o B b Fr Z Rd hGR u R hu hR s hs
  have hp : 1 ≤ Dw.p ∧ 1 ≤ Dw.q := by
    have h1 := o.toTowerOrigin.j_eq
    have h2 := T.j_pos
    have h3 := T.j_lt
    omega
  obtain ⟨f, hfS, hfZ, hev⟩ := GlobalTheory.T.comp_laws_tower_bound hG E H Dw l Xo c r U h e hL Y T o B b Fr Z Rd hGR u s hs.1
  have harch := GlobalTheory.T.uniform_norm_tower_bound hG E H Dw l Xo c r U h e hL x hx Y T o B b Fr Z Rd hGR u s R hR hs.2 f hfS hev
  refine ⟨f, GlobalTheory.CompanionTheory.Ar.Plug.bdd_mem_cuspOn E H Dw l Xo c r U h e hL hp.1 hp.2 x Z u hu f hfS hfZ
      (fun σ hσ => ⟨_, harch σ hσ⟩), hev, harch, ?_⟩
  exact GlobalTheory.T.uniform_all_tower_bound hG E H Dw l Xo c r U h e hL hU Y T o B b Fr Z Rd hGR u s hs.1 f hfS hfZ hev

end GlobalTheory.CompanionTheory.Ar.Plug
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.UniformNormAllTowerBoundStatement
open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniform_norm_all_tower_bound : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsGalois ℚ E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (h : GenFrEx Xo c) (e : Comp Xo c → Rul Xo c), CompLaws U h e → Ref.UnifAll Xo c → ∀ x : ℝ, (∀ σ, GoodEmb c σ → ∀ k (τ : E →+* ℂ), ‖τ ((U σ).X k).ξ0‖ = x) → ∀ (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : Top.RootTower (CMType H) (Dw.p + Dw.q)) (o : Top.GoodOrigin Y T) (B : ℕ) (b : T.Comp) (Fr : Small.GenFrame (o.toTowerOrigin.Or B b)) (Z : Comp Xo c) (Rd : Reading Fr h Z) (_ : GeoRead Rd) (u : GlobalTheory.AllWt.Weight Dw) (R : ℝ), (∀ τ, StrictAnti (u τ)) → 0 ≤ R → ∀ s ∈ modelSmall (o.toTowerOrigin.Or B b) u R, ∃ f ∈ GlobalTheory.AllWt.cuspOn U Z (GlobalTheory.AllWt.wtOf Dw u 0), evC h Z f = trOf Rd u s ∧ (∀ σ, GoodEmb c σ → ∀ z ∈ GlobalTheory.AllWt.framesOn (U σ) Z, GlobalTheory.AllWt.homN (U σ) x (GlobalTheory.AllWt.wtOf Dw u 0) f z ≤ (o.toTowerOrigin.Or B b).Fl.deg * R) ∧ ∀ (p : ℕ) (la : HeightOneSpectrum (𝓞 c.F)), p.Prime → ((p : ℕ) : 𝓞 c.F) ∈ la.asIdeal → ∀ v ∈ (GlobalTheory.CompHt.recVals Xo c).1 la, ((-((vLa la (p : c.F) : ℝ) * (if p ∈ o.toTowerOrigin.S B then exTwo E p else 0) * GlobalTheory.CovHt.l1 u) : ℝ) : EReal) ≤ v f := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Plug.descent_small | exact GlobalTheory.CompanionTheory.Ar.Plug.descent_small | (intros; apply GlobalTheory.CompanionTheory.Ar.Plug.descent_small <;> assumption)
end
