module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.PolynomialSiteTraces.AdmissibleMap
public import Development.WeilBound.CoreStatements.AbelianHeightsDuality.DividedPowerAlgebras.RingTrunc
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RepUnique
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.DividedPowerReduction.IsFirstChernThickening

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DividedPowerEnvelopeExpansion
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DividedPowerEnvelopeExpansion
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Site

namespace GlobalTheory.CompanionTheory.PDSpanning

theorem exists_sum_dpow : ∀ {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (z : (pq B).P), ∃ b : ℕ →₀ B, z = b.sum fun k c => algebraMap B (pq B).P c * (eta δ).dpow k ((pq B).e 1) := by
  intro B _ J δ z
  refine ⟨(pq B).e.repr z, ?_⟩
  have h := (pq B).e.linearCombination_repr z
  rw [Finsupp.linearCombination_apply] at h
  refine h.symm.trans (Finsupp.sum_congr fun k _ => ?_)
  rw [(eta_std δ).var k, Algebra.smul_def]

end GlobalTheory.CompanionTheory.PDSpanning
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DividedPowerEnvelopeExpansionStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Site
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.divided_power_envelope_expansion : ∀ {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (z : (pq B).P), ∃ b : ℕ →₀ B, z = b.sum fun k c => algebraMap B (pq B).P c * (eta δ).dpow k ((pq B).e 1) := by
  first | exact @GlobalTheory.CompanionTheory.PDSpanning.exists_sum_dpow | exact GlobalTheory.CompanionTheory.PDSpanning.exists_sum_dpow | (intros; apply GlobalTheory.CompanionTheory.PDSpanning.exists_sum_dpow <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DividedPowerEnvelopeUniversal
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DividedPowerEnvelopeUniversal
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Site

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.PDUniv

theorem pdPoly_universal : ∀ {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) {C : Type} [CommRing C] {J'' : Ideal C} (δ'' : DividedPowers J'') (f : B →+* C), IsDPMorphism δ δ'' f → ∀ x ∈ J'', ∃! F : (pq B).P →+* C, F.comp (algebraMap B (pq B).P) = f ∧ F ((pq B).e 1) = x ∧ IsDPMorphism (eta δ) δ'' F := by
  intro B _ J δ C _ J'' δ'' f hf x hx
  have hη : (pq B).IsStd δ (eta δ) := by
    unfold eta
    exact Classical.choose_spec (FubiniStudyChowHeightFormula₂.Adr.exists_std B J δ (pq B))
  letI : Algebra B C := f.toAlgebra
  let L : (pq B).P →ₗ[B] C := (pq B).e.constr ℕ fun n => δ''.dpow n x
  have hL : ∀ n, L ((pq B).e n) = δ''.dpow n x := fun n => (pq B).e.constr_basis ℕ _ n
  have h1 : L 1 = 1 := by
    rw [← (pq B).e_zero, hL, δ''.dpow_zero hx]
  have hbil : (LinearMap.mul B (pq B).P).compr₂ L = (LinearMap.mul B C).compl₁₂ L L := by
    refine (pq B).e.ext fun m => (pq B).e.ext fun n => ?_
    show L ((pq B).e m * (pq B).e n) = L ((pq B).e m) * L ((pq B).e n)
    rw [(pq B).e_mul, ← nsmul_eq_mul, map_nsmul]
    simp only [hL]
    rw [nsmul_eq_mul, δ''.mul_dpow hx]
  have hmul : ∀ a b, L (a * b) = L a * L b := fun a b => LinearMap.congr_fun₂ hbil a b
  let F : (pq B).P →+* C := (AlgHom.ofLinearMap L h1 hmul).toRingHom
  have hFL : ∀ p, F p = L p := fun p => rfl
  have hFe : ∀ n, F ((pq B).e n) = δ''.dpow n x := fun n => (hFL _).trans (hL n)
  have hFa : ∀ b, F (algebraMap B (pq B).P b) = f b := fun b =>
    (AlgHom.ofLinearMap L h1 hmul).commutes b
  have hcomp : F.comp (algebraMap B (pq B).P) = f := RingHom.ext hFa
  have he1 : F ((pq B).e 1) = x := by rw [hFe, δ''.dpow_one hx]
  have he1mem : (pq B).e 1 ∈ (pq B).ext J := by
    unfold PDPoly.ext PDPoly.aug
    exact Ideal.mem_sup_right (Ideal.subset_span ⟨0, rfl⟩)
  have hSspan : (pq B).ext J = Ideal.span ((algebraMap B (pq B).P '' (J : Set B)) ∪
      Set.range fun n : ℕ => (pq B).e (n + 1)) := by
    rw [Ideal.span_union]
    rfl
  have hS' : ∀ s ∈ (algebraMap B (pq B).P '' (J : Set B)) ∪ Set.range fun n : ℕ => (pq B).e (n + 1),
      F s ∈ J'' := by
    rintro s (⟨j, hj, rfl⟩ | ⟨n, rfl⟩)
    · rw [hFa]
      exact hf.ideal_comp (Ideal.mem_map_of_mem f hj)
    · rw [hFe]
      exact δ''.dpow_mem (Nat.succ_ne_zero n) hx
  have hdpS : ∀ {n : ℕ}, ∀ a ∈ (algebraMap B (pq B).P '' (J : Set B)) ∪
      Set.range fun n : ℕ => (pq B).e (n + 1), F ((eta δ).dpow n a) = δ''.dpow n (F a) := by
    intro n a ha
    rcases ha with ⟨j, hj, rfl⟩ | ⟨m, rfl⟩
    · rw [hη.dp.dpow_comp j hj, hFa, hFa, hf.dpow_comp j hj]
    · dsimp only
      have hv : (pq B).e (m + 1) = (eta δ).dpow (m + 1) ((pq B).e 1) := (hη.var (m + 1)).symm
      rw [hv, (eta δ).dpow_comp (Nat.succ_ne_zero m) he1mem]
      simp only [hη.var, map_mul, map_natCast, hFe]
      rw [δ''.dpow_comp (Nat.succ_ne_zero m) hx]
  have hdp : IsDPMorphism (eta δ) δ'' F := IsDPMorphism.on_span (eta δ) δ'' hSspan hS' hdpS
  refine ⟨F, ⟨hcomp, he1, hdp⟩, ?_⟩
  rintro G ⟨hG1, hG2, hG3⟩
  have hGa : ∀ b, G (algebraMap B (pq B).P b) = f b := fun b => RingHom.congr_fun hG1 b
  have hGe : ∀ n, G ((pq B).e n) = δ''.dpow n x := by
    intro n
    rw [← hη.var n, ← hG3.dpow_comp _ he1mem, hG2]
  let Ga : (pq B).P →ₐ[B] C := { G with commutes' := hGa }
  have hlin : Ga.toLinearMap = L := (pq B).e.ext fun n => by
    show G ((pq B).e n) = L ((pq B).e n)
    rw [hGe, hL]
  ext p
  exact LinearMap.congr_fun hlin p

end GlobalTheory.CompanionTheory.PDUniv
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DividedPowerEnvelopeUniversalStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Site
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.divided_power_envelope_universal : ∀ {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) {C : Type} [CommRing C] {J'' : Ideal C} (δ'' : DividedPowers J'') (f : B →+* C), IsDPMorphism δ δ'' f → ∀ x ∈ J'', ∃! F : (pq B).P →+* C, F.comp (algebraMap B (pq B).P) = f ∧ F ((pq B).e 1) = x ∧ IsDPMorphism (eta δ) δ'' F := by
  first | exact @GlobalTheory.CompanionTheory.PDUniv.pdPoly_universal | exact GlobalTheory.CompanionTheory.PDUniv.pdPoly_universal | (intros; apply GlobalTheory.CompanionTheory.PDUniv.pdPoly_universal <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TruncatedEnvelopeFiltrationQuotient
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TruncatedEnvelopeFiltrationQuotient
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Site

namespace GlobalTheory.CompanionTheory.SiteTrCrit

variable {B : Type} [CommRing B] {J : Ideal B}

theorem sum_eq (δ : DividedPowers J) (b : ℕ →₀ B) :
    (b.sum fun k c => algebraMap B (pq B).P c * (eta δ).dpow k ((pq B).e 1)) =
      Finsupp.linearCombination B (pq B).e b := by
  rw [Finsupp.linearCombination_apply]
  refine Finsupp.sum_congr fun k _ => ?_
  rw [(eta_std δ).var k, Algebra.smul_def]

theorem repr_sum (δ : DividedPowers J) (b : ℕ →₀ B) :
    (pq B).e.repr (b.sum fun k c => algebraMap B (pq B).P c * (eta δ).dpow k ((pq B).e 1)) = b := by
  rw [sum_eq]
  exact (pq B).e.repr_linearCombination b

theorem crit_sup (δ : DividedPowers J) (r : ℕ) (z : (pq B).P) (c : B) :
    z ∈ fil (eta δ) r ⊔ Ideal.span {algebraMap B (pq B).P c} ↔
      ∀ k, (pq B).e.repr z k ∈ fil δ (r - k) ⊔ Ideal.span {c} := by
  have crit := (GlobalTheory.CompanionTheory.PDFil.fil_pdPoly δ (pq B) (eta δ) (eta_std δ)).2.2.2 r
  constructor
  · intro hz k
    obtain ⟨f, hf, g, hg, rfl⟩ := Submodule.mem_sup.1 hz
    obtain ⟨w, rfl⟩ := Ideal.mem_span_singleton'.1 hg
    have e : w * algebraMap B (pq B).P c = c • w := by rw [Algebra.smul_def, mul_comm]
    rw [e, map_add (f := _), map_smul, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
    exact Ideal.add_mem _ (Ideal.mem_sup_left ((crit f).1 hf k))
      (Ideal.mem_sup_right (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self c)))
  · intro h
    rw [← (pq B).e.linearCombination_repr z, Finsupp.linearCombination_apply]
    refine Ideal.sum_mem _ fun k _ => ?_
    obtain ⟨f, hf, g, hg, e⟩ := Submodule.mem_sup.1 (h k)
    obtain ⟨w, rfl⟩ := Ideal.mem_span_singleton'.1 hg
    rw [← e]
    beta_reduce
    rw [add_smul]
    refine Ideal.add_mem _ (Ideal.mem_sup_left ((crit _).2 fun j => ?_)) (Ideal.mem_sup_right ?_)
    · rw [map_smul, (pq B).e.repr_self, Finsupp.smul_single, smul_eq_mul, mul_one, Finsupp.single_apply]
      split_ifs with hj
      · rw [← hj]; exact hf
      · exact Ideal.zero_mem _
    · rw [mul_comm w c, mul_smul, Algebra.smul_def c]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

end GlobalTheory.CompanionTheory.SiteTrCrit


open GlobalTheory.CompanionTheory.SiteTrCrit in
theorem GlobalTheory.CompanionTheory.SiteTrCrit.tr_crit : ∀ {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (s : ℕ) (δ' : DividedPowers (((pq B).ext J).map (Ideal.Quotient.mk (fil (eta δ) (max s 1))))), IsDPMorphism (eta δ) δ' (Ideal.Quotient.mk (fil (eta δ) (max s 1))) → ∀ (b : ℕ →₀ B) (r : ℕ), r ≤ s → ∀ c : B, (Ideal.Quotient.mk (fil (eta δ) (max s 1)) (b.sum fun k c => algebraMap B (pq B).P c * (eta δ).dpow k ((pq B).e 1)) ∈ fil δ' r ↔ ∀ k, b k ∈ fil δ (r - k)) ∧ (Ideal.Quotient.mk (fil (eta δ) (max s 1)) (b.sum fun k c => algebraMap B (pq B).P c * (eta δ).dpow k ((pq B).e 1)) ∈ fil δ' r ⊔ Ideal.span {Ideal.Quotient.mk (fil (eta δ) (max s 1)) (algebraMap B (pq B).P c)} ↔ ∀ k, b k ∈ fil δ (r - k) ⊔ Ideal.span {c}) := by
  intro B _ J δ s δ' hδ' b r hr c
  have hK : fil (eta δ) (max s 1) ≤ fil (eta δ) r :=
    GlobalTheory.Cris.ExpBij.dpFil_anti (eta δ) (le_max_of_le_left hr)
  have hfil : fil δ' r = (fil (eta δ) r).map (Ideal.Quotient.mk (fil (eta δ) (max s 1))) :=
    le_antisymm (FubiniStudyChowHeightFormula₂.Adr.Fil.fil_le_map_fil _ _ (eta δ) _ _ δ' _ hδ' rfl r)
      (FubiniStudyChowHeightFormula₂.Adr.Fil.map_fil_le (eta δ) δ' _ hδ' r)
  have hsup : (fil (eta δ) r).map (Ideal.Quotient.mk (fil (eta δ) (max s 1))) ⊔
      Ideal.span {Ideal.Quotient.mk (fil (eta δ) (max s 1)) (algebraMap B (pq B).P c)} =
      (fil (eta δ) r ⊔ Ideal.span {algebraMap B (pq B).P c}).map
        (Ideal.Quotient.mk (fil (eta δ) (max s 1))) := by
    rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton]
  rw [hfil, hsup, Ideal.mem_quotient_iff_mem hK, Ideal.mem_quotient_iff_mem (hK.trans le_sup_left),
    crit_sup, (GlobalTheory.CompanionTheory.PDFil.fil_pdPoly δ (pq B) (eta δ) (eta_std δ)).2.2.2, repr_sum]
  exact ⟨Iff.rfl, Iff.rfl⟩
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TruncatedEnvelopeFiltrationQuotientStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Site
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.truncated_envelope_filtration_quotient : ∀ {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (s : ℕ) (δ' : DividedPowers (((pq B).ext J).map (Ideal.Quotient.mk (fil (eta δ) (max s 1))))), IsDPMorphism (eta δ) δ' (Ideal.Quotient.mk (fil (eta δ) (max s 1))) → ∀ (b : ℕ →₀ B) (r : ℕ), r ≤ s → ∀ c : B, (Ideal.Quotient.mk (fil (eta δ) (max s 1)) (b.sum fun k c => algebraMap B (pq B).P c * (eta δ).dpow k ((pq B).e 1)) ∈ fil δ' r ↔ ∀ k, b k ∈ fil δ (r - k)) ∧ (Ideal.Quotient.mk (fil (eta δ) (max s 1)) (b.sum fun k c => algebraMap B (pq B).P c * (eta δ).dpow k ((pq B).e 1)) ∈ fil δ' r ⊔ Ideal.span {Ideal.Quotient.mk (fil (eta δ) (max s 1)) (algebraMap B (pq B).P c)} ↔ ∀ k, b k ∈ fil δ (r - k) ⊔ Ideal.span {c}) := by
  first | exact @GlobalTheory.CompanionTheory.SiteTrCrit.tr_crit | exact GlobalTheory.CompanionTheory.SiteTrCrit.tr_crit | (intros; apply GlobalTheory.CompanionTheory.SiteTrCrit.tr_crit <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsLocalFrameOfCoords
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsLocalFrameOfCoords
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb GlobalTheory.CompanionTheory.ConeLocal
open GlobalTheory.CatH (face toLast)
open TensorProduct DividedPowers

namespace GlobalTheory.CompanionTheory.ConeLocal

theorem dividedPowerFiltration_dividedPowersBot_of_one_le {K : Type} [CommRing K] {r : ℕ} (hr : 1 ≤ r) : pdP (dividedPowersBot K) r = ⊥ := by
  refine Ideal.span_eq_bot.2 ?_
  rintro _ ⟨l, hl, hs, rfl⟩
  have h : ∃ p ∈ l, p.1 ≠ 0 := by
    by_contra h
    push Not at h
    have : (l.map Prod.fst).sum = 0 := List.sum_eq_zero (by simpa using h)
    omega
  obtain ⟨p, hp, h0⟩ := h
  refine List.prod_eq_zero (List.mem_map.2 ⟨p, hp, ?_⟩)
  have e : p.2 = 0 := hl p hp
  rw [e]
  exact (dividedPowersBot K).dpow_eval_zero h0

theorem tfBase_dpBot {K : Type} [Field K] [CharZero K] {s : ℕ} (hs : 1 ≤ s) : TFBase (dividedPowersBot K) 1 s := by
  refine ⟨dividedPowerFiltration_dividedPowersBot_of_one_le hs, ?_, ?_⟩
  · intro r x h
    simpa only [Nat.cast_one, one_mul] using h
  · intro n hn
    refine ⟨0, (n : K)⁻¹, ?_⟩
    rw [pow_zero, mul_inv_cancel₀ (Nat.cast_ne_zero.2 hn)]

theorem exists_loc : ∀ {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) {W : X.Opens} {d : ℕ} (c : Coord q W d) (s : ℕ), 1 ≤ s →
    ∃ (E : Frame (sP (KS q s {W})) d) (ε : Γ(X, W) ≃+* (sP (KS q s {W})).A.obj E.D), IsLoc q s c.t E ε := by
  intro K _ _ X q W d c s hs
  have hb : TFBase (dividedPowersBot K) 1 s := tfBase_dpBot hs
  obtain ⟨c', e, hTF, he1, he2, he3⟩ := GlobalTheory.CompanionTheory.ChartAlg.chart_exists (O := K) (R := K) (dividedPowersBot K) 1 s hb q
    (Ideal.Quotient.mk ⊥) (fun a => rfl) c
  letI := (strV q W).toAlgebra
  have hg := GlobalTheory.CompanionTheory.ChartMaps.good c'
  have hD : KS q s {W} c'.D := ⟨hTF, W, rfl, c'.inV⟩
  let E := c'.frame hg (KS q s {W}) (ks_in q s W) hD
  have hpow (r : ℕ) : c'.D.pdPow r = (pdP (dividedPowersBot K) r).map c'.D.i :=
    GlobalTheory.CompanionTheory.ChartFil.dividedPowerFiltration_eq_map _ _ _ c'.D.compat c'.J_eq r
  have hc : E.GrConst (sFil (KS q s {W})) := by
    intro n T u v x hx
    have hx' : (show c'.D.B from x) ∈ c'.D.pdPow ((n : ℤ).toNat) := hx
    rw [Int.toNat_natCast, hpow] at hx'
    change _ ∈ T.obj.pdPow (((n : ℤ) + 1).toNat)
    rw [show ((n : ℤ) + 1).toNat = n + 1 by omega]
    exact GlobalTheory.CompanionTheory.ChartFil.sub_mem_pdP c' (ks_in q s W _ T.property) u.hom v.hom n hx'
  let ε : Γ(X, W) ≃+* c'.D.B := (Algebra.TensorProduct.lid K Γ(X, W)).symm.toRingEquiv.trans e
  have hε : ∀ f, ε f = e ((1 : K) ⊗ₜ[K] f) := fun f => rfl
  refine ⟨E, ε, hc, fun x hx => ?_, fun a => ?_, fun T u g => ?_, fun i T u v => ?_⟩
  · have h2 : (show c'.D.B from x) ∈ c'.D.pdPow 1 := hx
    rw [hpow, dividedPowerFiltration_dividedPowersBot_of_one_le le_rfl, Ideal.map_bot] at h2
    exact Ideal.mem_bot.1 h2
  · have e1 : (1 : K) ⊗ₜ[K] (strV q W a) = a ⊗ₜ[K] (1 : Γ(X, W)) := by
      have : strV q W a = a • (1 : Γ(X, W)) := by
        rw [Algebra.smul_def, mul_one]; rfl
      rw [this, TensorProduct.tmul_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    change ε (strV q W a) = c'.D.i a
    rw [hε, e1, he1]
  · have h1 := GlobalTheory.CompanionTheory.GrForm.ev_nat (q := q) u.hom c'.inV (ks_in q s W _ T.property) g
    exact h1.trans ((congrArg (Ideal.quotientMap T.obj.J u.hom.φ u.hom.hle) (he3 g)).trans rfl)
  · change (v.hom.φ (c'.t i) - u.hom.φ (c'.t i) : T.obj.B) = v.hom.φ (ε (c.t i)) - u.hom.φ (ε (c.t i))
    rw [hε, he2]

end GlobalTheory.CompanionTheory.ConeLocal
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsLocalFrameOfCoordsStatement
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb GlobalTheory.CompanionTheory.ConeLocal
open GlobalTheory.CatH (face toLast)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_frame_of_coords : ∀ {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) {W : X.Opens} {d : ℕ} (c : Coord q W d) (s : ℕ), 1 ≤ s →
    ∃ (E : Frame (sP (KS q s {W})) d) (ε : Γ(X, W) ≃+* (sP (KS q s {W})).A.obj E.D), IsLoc q s c.t E ε := by
  first | exact @GlobalTheory.CompanionTheory.ConeLocal.exists_loc | exact GlobalTheory.CompanionTheory.ConeLocal.exists_loc | (intros; apply GlobalTheory.CompanionTheory.ConeLocal.exists_loc <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsConeLift
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThickJIsNilpotent
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Site

namespace GlobalTheory.CompanionTheory.SiteNil

theorem thick_J_isNilpotent : ∀ {O R : Type} [CommRing O] [CommRing R] {I : Ideal R}
    {γ : DividedPowers I} {p : ℕ} {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)}
    {κ : O →+* R ⧸ I} (T : Thick (nlFun γ p X q κ)), ∀ x ∈ T.J, IsNilpotent x := by
  intro O R _ _ I γ p X q κ T x hx
  by_cases hp : p = 0
  · obtain ⟨n, hn⟩ := T.adm.2 hp
    refine ⟨n, ?_⟩
    have h : x ^ n ∈ T.J ^ n := Ideal.pow_mem_pow hx n
    rw [hn] at h
    exact h
  · obtain ⟨n, hn⟩ : IsNilpotent ((p : ℕ) : T.B) := T.adm.1 hp
    refine ⟨p * n, ?_⟩
    have h1 : x ^ p = (p.factorial : T.B) * T.δ.dpow p x := (T.δ.factorial_mul_dpow_eq_pow hx).symm
    have h2 : (p.factorial : T.B) = (p : T.B) * ((p - 1).factorial : T.B) := by
      rw [← Nat.cast_mul, Nat.mul_factorial_pred hp]
    rw [pow_mul, h1, h2, mul_assoc, mul_pow, hn, zero_mul]

end GlobalTheory.CompanionTheory.SiteNil
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsConeLift
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.ConeLiftEx

theorem exists_unit_lift {B : Type} [CommRing B] (J : Ideal B) (hJ : ∀ x ∈ J, IsNilpotent x) (u : (B ⧸ J)ˣ) :
    ∃ w : Bˣ, Ideal.Quotient.mk J (w : B) = (u : B ⧸ J) := by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (u : B ⧸ J)
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective ((u⁻¹ : (B ⧸ J)ˣ) : B ⧸ J)
  have hmem : a * b - 1 ∈ J := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, ha, hb, Units.mul_inv, map_one, sub_self]
  have hu : IsUnit (a * b) := by
    have := (hJ _ hmem).isUnit_one_add
    simpa using this
  exact ⟨(isUnit_of_mul_isUnit_left hu).unit, by simpa using ha⟩

theorem nonempty_cLiftK : ∀ {K : Type} [CommRing K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (D : E.LineData X) (s : ℕ), Nonempty (CLiftK (KS q s (𝒱D D)).ι D) := by
  intro K _ X q D s
  have hp : ∀ c : (KS q s (𝒱D D)).FullSubcategory,
      ∃ p : Spec (CommRingCat.of (c.obj.B ⧸ c.obj.J)) ⟶ D.Y, p ≫ D.f = pt c.obj := by
    intro c
    obtain ⟨V, ⟨σ, hσ⟩, hV⟩ := c.property.2
    have hr : Set.range (pt c.obj) ⊆ Set.range V.ι := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨x, rfl⟩
      exact hV (show x ∈ (⊤ : Scheme.Opens _) from trivial)
    refine ⟨IsOpenImmersion.lift V.ι (pt c.obj) hr ≫ σ, ?_⟩
    rw [Category.assoc, hσ, IsOpenImmersion.lift_fac]
  choose p hp using hp
  have hw : ∀ {c c' : (KS q s (𝒱D D)).FullSubcategory} (φ : c ⟶ c'),
      ∃ w : (((KS q s (𝒱D D)).ι).obj c').Bˣ, ∀ (h : (Spec.map (CommRingCat.ofHom (Ideal.quotientMap (((KS q s (𝒱D D)).ι).obj c').J (((KS q s (𝒱D D)).ι).map φ).φ (((KS q s (𝒱D D)).ι).map φ).hle)) ≫ p c) ≫ D.f = p c' ≫ D.f),
        Ideal.Quotient.mk (((KS q s (𝒱D D)).ι).obj c').J w = (Scheme.ΓSpecIso (CommRingCat.of ((((KS q s (𝒱D D)).ι).obj c').B ⧸ (((KS q s (𝒱D D)).ι).obj c').J))).hom.hom
          (D.u (Spec.map (CommRingCat.ofHom (Ideal.quotientMap (((KS q s (𝒱D D)).ι).obj c').J (((KS q s (𝒱D D)).ι).map φ).φ (((KS q s (𝒱D D)).ι).map φ).hle)) ≫ p c) (p c') h) := by
    intro c c' φ
    by_cases h : (Spec.map (CommRingCat.ofHom (Ideal.quotientMap (((KS q s (𝒱D D)).ι).obj c').J (((KS q s (𝒱D D)).ι).map φ).φ (((KS q s (𝒱D D)).ι).map φ).hle)) ≫ p c) ≫ D.f = p c' ≫ D.f
    · obtain ⟨w, hw⟩ := exists_unit_lift (((KS q s (𝒱D D)).ι).obj c').J
        (fun x hx => GlobalTheory.CompanionTheory.SiteNil.thick_J_isNilpotent _ x hx)
        (Units.map (Scheme.ΓSpecIso (CommRingCat.of ((((KS q s (𝒱D D)).ι).obj c').B ⧸ (((KS q s (𝒱D D)).ι).obj c').J))).hom.hom.toMonoidHom
          (D.u _ _ h))
      exact ⟨w, fun _ => hw⟩
    · exact ⟨1, fun h' => absurd h' h⟩
  choose w hw using @hw
  exact ⟨{ p := p, hp := hp, w := fun φ => w φ, hw := fun φ h => hw φ h }⟩

end GlobalTheory.CompanionTheory.ConeLiftEx
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsConeLiftStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cone_lift : ∀ {K : Type} [CommRing K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (D : E.LineData X) (s : ℕ), Nonempty (CLiftK (KS q s (𝒱D D)).ι D) := by
  first | exact @GlobalTheory.CompanionTheory.ConeLiftEx.nonempty_cLiftK | exact GlobalTheory.CompanionTheory.ConeLiftEx.nonempty_cLiftK | (intros; apply GlobalTheory.CompanionTheory.ConeLiftEx.nonempty_cLiftK <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousSingleV
noncomputable section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.SaGen

structure PlaceMap (F K : Type) [Field F] [NumberField F] [Field K] [Algebra F K] [TopologicalSpace K] where

  proj : AF F →ₐ[F] K

  inj : K →ₙₐ[F] AF F
  proj_inj : ∀ x, proj (inj x) = x
  inj_proj : ∀ a, inj (proj a) = inj 1 * a
  cont_proj : Continuous proj
  cont_inj : Continuous inj

section Inhabitants

variable {F : Type} [Field F] [NumberField F]

theorem adele_ext {a b : AF F} (h1 : fstA F a = fstA F b) (h2 : sndA F a = sndA F b) : a = b :=
  Prod.ext h1 h2

theorem finAdele_ext {x y : Af F} (h : ∀ w, evalV F w x = evalV F w y) : x = y :=
  RestrictedProduct.ext _ _ h

theorem fstA_pairA (x : Ainf F) (y : Af F) : fstA F (pairA F x y) = x := rfl

theorem sndA_pairA (x : Ainf F) (y : Af F) : sndA F (pairA F x y) = y := rfl

theorem continuous_singleV' (v : HeightOneSpectrum (𝓞 F)) : Continuous (singleV F v) := by
  classical
  have hS : Filter.cofinite ≤ Filter.principal ({v}ᶜ : Set (HeightOneSpectrum (𝓞 F))) :=
    Filter.le_principal_iff.2 (Set.finite_singleton v).compl_mem_cofinite
  let f : v.adicCompletion F → RestrictedProduct (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F)
      (fun w : HeightOneSpectrum (𝓞 F) => (w.adicCompletionIntegers F : Set (w.adicCompletion F)))
      (Filter.principal ({v}ᶜ : Set _)) :=
    fun x => ⟨Pi.single (M := fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F) v x, by
      intro w hw
      have hw' : w ≠ v := hw
      simp only [Set.mem_ofPred_eq, Pi.single_eq_of_ne hw', SetLike.mem_coe]
      exact zero_mem _⟩
  have hf : Continuous f := RestrictedProduct.continuous_rng_of_principal.2 (continuous_single v)
  exact (RestrictedProduct.continuous_inclusion hS).comp hf

theorem evalV_singleV_eq (v w : HeightOneSpectrum (𝓞 F)) (y : Fv F v) (f : ∀ u, Fv F u → Fv F u)
    (h0 : ∀ u, f u 0 = 0) :
    f w (evalV F w (singleV F v y)) = evalV F w (singleV F v (f v y)) := by
  by_cases h : w = v
  · subst h
    rw [StrongApprox.evalV_single_same, StrongApprox.evalV_single_same]
  · rw [StrongApprox.evalV_single_ne h, StrongApprox.evalV_single_ne h, h0]

def placeMapFin (v : HeightOneSpectrum (𝓞 F)) : PlaceMap F (Fv F v) where
  proj := (evalV F v).comp (sndA F)
  inj :=
    { toFun := fun y => pairA F 0 (singleV F v y)
      map_smul' := by
        intro c y
        refine adele_ext ?_ (finAdele_ext fun w => ?_)
        · rw [map_smul, fstA_pairA, fstA_pairA, smul_zero]
        · rw [map_smul, sndA_pairA, sndA_pairA, map_smul]
          exact (evalV_singleV_eq v w y (fun u t => c • t) (fun u => smul_zero c)).symm ▸ rfl
      map_zero' := by
        refine adele_ext rfl (finAdele_ext fun w => ?_)
        rw [sndA_pairA, map_zero, map_zero]
        by_cases h : w = v
        · subst h
          rw [StrongApprox.evalV_single_same]
        · rw [StrongApprox.evalV_single_ne h]
      map_add' := by
        intro x y
        refine adele_ext ?_ (finAdele_ext fun w => ?_)
        · rw [map_add (f := _), fstA_pairA, fstA_pairA, fstA_pairA, add_zero]
        · rw [map_add (f := _), sndA_pairA, sndA_pairA, sndA_pairA, map_add (f := _)]
          by_cases h : w = v
          · subst h
            simp only [StrongApprox.evalV_single_same]
          · simp only [StrongApprox.evalV_single_ne h, add_zero]
      map_mul' := by
        intro x y
        refine adele_ext ?_ (finAdele_ext fun w => ?_)
        · rw [map_mul, fstA_pairA, fstA_pairA, fstA_pairA, mul_zero]
        · rw [map_mul, sndA_pairA, sndA_pairA, sndA_pairA, map_mul]
          by_cases h : w = v
          · subst h
            simp only [StrongApprox.evalV_single_same]
          · simp only [StrongApprox.evalV_single_ne h, mul_zero] }
  proj_inj := fun x => StrongApprox.evalV_single_same v x
  inj_proj := by
    intro a
    refine adele_ext ?_ (finAdele_ext fun w => ?_)
    · change (0 : Ainf F) = fstA F (pairA F 0 (singleV F v 1) * a)
      rw [map_mul, fstA_pairA, zero_mul]
    · change evalV F w (singleV F v (evalV F v (sndA F a))) = evalV F w (sndA F (pairA F 0 (singleV F v 1) * a))
      rw [map_mul, map_mul, sndA_pairA]
      by_cases h : w = v
      · subst h
        simp only [StrongApprox.evalV_single_same, one_mul]
      · simp only [StrongApprox.evalV_single_ne h, zero_mul]
  cont_proj := StrongApprox.continuous_evalV v
  cont_inj := continuous_const.prodMk (continuous_singleV' v)


open Classical in
def singleI (w : InfinitePlace F) (y : w.Completion) : Ainf F :=
  (Pi.single (M := fun u : InfinitePlace F => u.Completion) w y : ∀ u : InfinitePlace F, u.Completion)

open Classical in
theorem singleI_self (w : InfinitePlace F) (y : w.Completion) : (singleI w y : ∀ u : InfinitePlace F, u.Completion) w = y :=
  Pi.single_eq_same (M := fun u : InfinitePlace F => u.Completion) w y

open Classical in
theorem singleI_ne {w u : InfinitePlace F} (h : u ≠ w) (y : w.Completion) :
    (singleI w y : ∀ u : InfinitePlace F, u.Completion) u = 0 :=
  Pi.single_eq_of_ne (M := fun u : InfinitePlace F => u.Completion) h y

theorem ainf_ext {x y : Ainf F} (h : ∀ u, (x : ∀ u : InfinitePlace F, u.Completion) u = (y : ∀ u : InfinitePlace F, u.Completion) u) : x = y :=
  funext h


open Classical in
def placeMapInf (w : InfinitePlace F) : PlaceMap F w.Completion where
  proj := (Pi.evalAlgHom F (fun u : InfinitePlace F => u.Completion) w).comp (fstA F)
  inj :=
    { toFun := fun y => pairA F (singleI w y) 0
      map_smul' := by
        intro c y
        refine adele_ext ?_ ?_
        · rw [map_smul, fstA_pairA, fstA_pairA]
          exact Pi.single_smul (f := fun u : InfinitePlace F => u.Completion) w c y
        · rw [map_smul, sndA_pairA, sndA_pairA, smul_zero]
      map_zero' := by
        refine adele_ext ?_ rfl
        rw [fstA_pairA, map_zero]
        exact Pi.single_zero (M := fun u : InfinitePlace F => u.Completion) w
      map_add' := by
        intro x y
        refine adele_ext ?_ ?_
        · rw [map_add (f := _), fstA_pairA, fstA_pairA, fstA_pairA]
          exact Pi.single_add (f := fun u : InfinitePlace F => u.Completion) w x y
        · rw [map_add (f := _), sndA_pairA, sndA_pairA, sndA_pairA, add_zero]
      map_mul' := by
        intro x y
        refine adele_ext ?_ ?_
        · rw [map_mul, fstA_pairA, fstA_pairA, fstA_pairA]
          exact Pi.single_mul (α := fun u : InfinitePlace F => u.Completion) w x y
        · rw [map_mul, sndA_pairA, sndA_pairA, sndA_pairA, mul_zero] }
  proj_inj := fun x => singleI_self w x
  inj_proj := by
    intro a
    refine adele_ext ?_ ?_
    · change singleI w (fstA F a w) = fstA F (pairA F (singleI w 1) 0 * a)
      rw [map_mul, fstA_pairA]
      refine ainf_ext fun u => ?_
      change (singleI w (fstA F a w) : ∀ u : InfinitePlace F, u.Completion) u =
        (singleI w 1 : ∀ u : InfinitePlace F, u.Completion) u * fstA F a u
      by_cases h : u = w
      · subst h
        rw [singleI_self, singleI_self, one_mul]
      · rw [singleI_ne h, singleI_ne h, zero_mul]
    · change (0 : Af F) = sndA F (pairA F (singleI w 1) 0 * a)
      rw [map_mul, sndA_pairA, zero_mul]
  cont_proj := (continuous_apply w).comp continuous_fst
  cont_inj := (continuous_single w).prodMk continuous_const

end Inhabitants

section Ring

variable {R : Type} [CommRing R] {M : ℕ}

end Ring

section Lift

variable {F E K : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [Field K] [Algebra F K]
  [TopologicalSpace K]

def iB (P : PlaceMap F K) : K ⊗[F] E →ₗ[F] AF F ⊗[F] E :=
  TensorProduct.map { toFun := P.inj, map_add' := map_add _, map_smul' := map_smul _ } LinearMap.id

end Lift

section Iso

variable {F E : Type} [Field F] [Field E] [Algebra F E]

end Iso

end GlobalTheory.CompanionTheory.SaGen
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TruncatedEnvelopeTorsionFree
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TruncatedEnvelopeTorsionFree
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Site

namespace GlobalTheory.CompanionTheory.SiteTr

theorem tr_tf : ∀ {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (l s : ℕ) (δ' : DividedPowers (((pq B).ext J).map (Ideal.Quotient.mk (fil (eta δ) (max s 1))))), IsDPMorphism (eta δ) δ' (Ideal.Quotient.mk (fil (eta δ) (max s 1))) → fil δ s = ⊥ → (∀ (r : ℕ) (x : B), (l : B) * x ∈ fil δ r → x ∈ fil δ r) → fil δ' s = ⊥ ∧ (∀ (r : ℕ) (x : (pq B).P ⧸ fil (eta δ) (max s 1)), (l : (pq B).P ⧸ fil (eta δ) (max s 1)) * x ∈ fil δ' r → x ∈ fil δ' r) ∧ IsNilpotent (((pq B).ext J).map (Ideal.Quotient.mk (fil (eta δ) (max s 1)))) := by
  intro B _ J δ l s δ' hδ' hs ht
  obtain ⟨-, hanti, h0, crit⟩ := GlobalTheory.T.divided_power_polynomial_filtration δ (pq B) (eta δ) (eta_std δ)
  have hanti' : ∀ a c, a ≤ c → fil (eta δ) c ≤ fil (eta δ) a := fun a c h =>
    GlobalTheory.Cris.ExpBij.dpFil_anti (eta δ) h
  have hmap : ∀ r, fil δ' r = (fil (eta δ) r).map (Ideal.Quotient.mk (fil (eta δ) (max s 1))) := fun r =>
    le_antisymm (FubiniStudyChowHeightFormula₂.Adr.Fil.fil_le_map_fil _ _ (eta δ) _ _ δ' _ hδ' rfl r)
      (FubiniStudyChowHeightFormula₂.Adr.Fil.map_fil_le (eta δ) δ' _ hδ' r)
  have htop : fil δ' (max s 1) = ⊥ := by rw [hmap, Ideal.map_quotient_self]
  refine ⟨?_, ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos s with rfl | hpos
    · have h10 : (1 : B) = 0 := by
        have : (1 : B) ∈ fil δ 0 := by rw [h0]; trivial
        rwa [hs, Ideal.mem_bot] at this
      haveI : Subsingleton B := subsingleton_of_zero_eq_one h10.symm
      haveI : Subsingleton (pq B).P := Module.subsingleton B (pq B).P
      haveI : Subsingleton ((pq B).P ⧸ fil (eta δ) (max 0 1)) :=
        Ideal.Quotient.mk_surjective.subsingleton
      exact eq_bot_iff.2 fun x _ => (Ideal.mem_bot).2 (Subsingleton.elim x 0)
    · have e : fil (eta δ) s = fil (eta δ) (max s 1) := by rw [max_eq_left hpos]
      rw [hmap, e, Ideal.map_quotient_self]
  · intro r x hx
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective x
    have key : ∀ y : (pq B).P, Ideal.Quotient.mk (fil (eta δ) (max s 1)) y ∈ fil δ' r ↔
        y ∈ fil (eta δ) (min r (max s 1)) := by
      intro y
      rw [hmap, Ideal.mem_quotient_iff_mem_sup]
      rcases le_total r (max s 1) with h | h
      · rw [min_eq_left h, sup_eq_left.2 (hanti' _ _ h)]
      · rw [min_eq_right h, sup_eq_right.2 (hanti' _ _ h)]
    have hz : (l : (pq B).P) * z ∈ fil (eta δ) (min r (max s 1)) :=
      (key _).1 (by simpa only [map_mul, map_natCast] using hx)
    refine (key z).2 ((crit _ z).2 fun k => ht _ _ ?_)
    have h1 := (crit _ _).1 hz k
    have e : (pq B).e.repr ((l : (pq B).P) * z) k = (l : B) * (pq B).e.repr z k := by
      rw [← nsmul_eq_mul, map_nsmul, Finsupp.smul_apply, nsmul_eq_mul]
    rwa [e] at h1
  · have hp : ∀ n, (((pq B).ext J).map (Ideal.Quotient.mk (fil (eta δ) (max s 1)))) ^ n ≤ fil δ' n := by
      intro n
      induction n with
      | zero =>
        intro a _
        exact GlobalTheory.Cris.ExpBij.mem_dpFil_zero δ' a
      | succ n ih =>
        rw [pow_succ]
        exact Ideal.mul_le.2 fun a ha b hb =>
          GlobalTheory.Cris.ExpBij.mul_mem_dpFil δ' (ih ha) (GlobalTheory.Cris.ExpBij.mem_dpFil_one δ' hb)
    exact ⟨max s 1, le_bot_iff.1 ((hp _).trans htop.le)⟩

end GlobalTheory.CompanionTheory.SiteTr
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TruncatedEnvelopeTorsionFreeStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Site
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.truncated_envelope_torsion_free : ∀ {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (l s : ℕ) (δ' : DividedPowers (((pq B).ext J).map (Ideal.Quotient.mk (fil (eta δ) (max s 1))))), IsDPMorphism (eta δ) δ' (Ideal.Quotient.mk (fil (eta δ) (max s 1))) → fil δ s = ⊥ → (∀ (r : ℕ) (x : B), (l : B) * x ∈ fil δ r → x ∈ fil δ r) → fil δ' s = ⊥ ∧ (∀ (r : ℕ) (x : (pq B).P ⧸ fil (eta δ) (max s 1)), (l : (pq B).P ⧸ fil (eta δ) (max s 1)) * x ∈ fil δ' r → x ∈ fil δ' r) ∧ IsNilpotent (((pq B).ext J).map (Ideal.Quotient.mk (fil (eta δ) (max s 1)))) := by
  first | exact @GlobalTheory.CompanionTheory.SiteTr.tr_tf | exact GlobalTheory.CompanionTheory.SiteTr.tr_tf | (intros; apply GlobalTheory.CompanionTheory.SiteTr.tr_tf <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DividedPowerEnvelopeFiltration
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Site

namespace GlobalTheory.CompanionTheory.PDCrit

private theorem pq_isStd_eta {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) :
    (pq B).IsStd δ (eta δ) :=
  Classical.choose_spec (FubiniStudyChowHeightFormula₂.Adr.exists_std B J δ (pq B))

theorem repr_sum {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (b : ℕ →₀ B) :
    (pq B).e.repr (b.sum fun k c => algebraMap B (pq B).P c * (eta δ).dpow k ((pq B).e 1)) = b := by
  have hs := pq_isStd_eta δ
  have h1 : (b.sum fun k c => algebraMap B (pq B).P c * (eta δ).dpow k ((pq B).e 1)) =
      Finsupp.linearCombination B (pq B).e b := by
    rw [Finsupp.linearCombination_apply]
    refine Finsupp.sum_congr fun k _ => ?_
    rw [hs.var k, Algebra.smul_def]
  rw [h1, (pq B).e.repr_linearCombination]

theorem mem_span_iff {B : Type} [CommRing B] (c : B) (z : (pq B).P) :
    z ∈ Ideal.span {algebraMap B (pq B).P c} ↔ ∀ k, (pq B).e.repr z k ∈ Ideal.span {c} := by
  constructor
  · intro hz k
    obtain ⟨w, rfl⟩ := Ideal.mem_span_singleton'.1 hz
    rw [mul_comm, ← Algebra.smul_def, map_smul, Finsupp.smul_apply, smul_eq_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self c)
  · intro h
    choose d hd using fun k => Ideal.mem_span_singleton'.1 (h k)
    rw [Ideal.mem_span_singleton']
    refine ⟨∑ k ∈ ((pq B).e.repr z).support, d k • (pq B).e k, ?_⟩
    conv_rhs => rw [← (pq B).e.linearCombination_repr z]
    rw [Finsupp.linearCombination_apply, Finsupp.sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← hd k, mul_comm (d k • (pq B).e k), ← Algebra.smul_def, smul_smul, mul_comm c (d k)]

private theorem sum_finsupp_single_apply_eq_ite {B : Type} [CommRing B] (s : Finset ℕ) (a : ℕ → B) (k : ℕ) :
    (∑ i ∈ s, Finsupp.single i (a i)) k = if k ∈ s then a k else 0 := by
  simp [Finsupp.finsetSum_apply, Finsupp.single_apply]

theorem mem_fil_sup_iff {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (r : ℕ) (c : B)
    (z : (pq B).P) :
    z ∈ fil (eta δ) r ⊔ Ideal.span {algebraMap B (pq B).P c} ↔
      ∀ k, (pq B).e.repr z k ∈ fil δ (r - k) ⊔ Ideal.span {c} := by
  have hT := (GlobalTheory.T.divided_power_polynomial_filtration δ (pq B) (eta δ) (pq_isStd_eta δ)).2.2.2
  constructor
  · intro hz k
    obtain ⟨a, ha, s, hs, rfl⟩ := Submodule.mem_sup.1 hz
    rw [map_add (f := _), Finsupp.add_apply]
    exact Submodule.add_mem_sup ((hT r a).1 ha k) ((mem_span_iff c s).1 hs k)
  · intro h
    choose a ha s hs hsum using fun k => Submodule.mem_sup.1 (h k)
    have hF : (∑ i ∈ ((pq B).e.repr z).support, Finsupp.single i (a i)) +
        (∑ i ∈ ((pq B).e.repr z).support, Finsupp.single i (s i)) = (pq B).e.repr z := by
      ext k
      rw [Finsupp.add_apply, sum_finsupp_single_apply_eq_ite, sum_finsupp_single_apply_eq_ite]
      split_ifs with hk
      · exact hsum k
      · rw [add_zero]
        exact (Finsupp.notMem_support_iff.1 hk).symm
    have hz : z = (pq B).e.repr.symm (∑ i ∈ ((pq B).e.repr z).support, Finsupp.single i (a i)) +
        (pq B).e.repr.symm (∑ i ∈ ((pq B).e.repr z).support, Finsupp.single i (s i)) := by
      rw [← map_add (f := _), hF, LinearEquiv.symm_apply_apply]
    rw [hz]
    refine Submodule.add_mem_sup ((hT r _).2 fun k => ?_) ((mem_span_iff c _).2 fun k => ?_)
    · rw [LinearEquiv.apply_symm_apply, sum_finsupp_single_apply_eq_ite]
      split_ifs
      · exact ha k
      · exact Submodule.zero_mem _
    · rw [LinearEquiv.apply_symm_apply, sum_finsupp_single_apply_eq_ite]
      split_ifs
      · exact hs k
      · exact Submodule.zero_mem _

theorem coeff_criteria : ∀ {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (b : ℕ →₀ B) (r : ℕ) (c : B), ((b.sum fun k c => algebraMap B (pq B).P c * (eta δ).dpow k ((pq B).e 1)) ∈ fil (eta δ) r ↔ ∀ k, b k ∈ fil δ (r - k)) ∧ ((b.sum fun k c => algebraMap B (pq B).P c * (eta δ).dpow k ((pq B).e 1)) ∈ fil (eta δ) r ⊔ Ideal.span {algebraMap B (pq B).P c} ↔ ∀ k, b k ∈ fil δ (r - k) ⊔ Ideal.span {c}) ∧ ((b.sum fun k c => algebraMap B (pq B).P c * (eta δ).dpow k ((pq B).e 1)) ∈ Ideal.span {algebraMap B (pq B).P c} ↔ ∀ k, b k ∈ Ideal.span {c}) ∧ ((b.sum fun k c => algebraMap B (pq B).P c * (eta δ).dpow k ((pq B).e 1)) = 0 ↔ ∀ k, b k = 0) := by
  intro B _ J δ b r c
  have hT := (GlobalTheory.T.divided_power_polynomial_filtration δ (pq B) (eta δ) (pq_isStd_eta δ)).2.2.2
  have hr := repr_sum δ b
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hT, hr]
  · rw [mem_fil_sup_iff, hr]
  · rw [mem_span_iff, hr]
  · rw [← LinearEquiv.map_eq_zero_iff (pq B).e.repr, hr]
    simp only [Finsupp.ext_iff, Finsupp.coe_zero, Pi.zero_apply]

end GlobalTheory.CompanionTheory.PDCrit
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DPullCEqZero
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

noncomputable section
namespace GlobalTheory.CompanionTheory.MuThick

universe w w' v u v' u'

theorem d_pullC_eq_zero {R R' : Type} [CommRing R] [CommRing R'] {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C']
    {F : C ⥤ ModuleCat.{w} R} {F' : C' ⥤ ModuleCat.{w'} R'} {σ : R →+* R'} (m : CH.Mor F F' σ) (n : ℕ) (b : CH.Cn F n)
    (hb : CH.d F n b = 0) : CH.d F' n (m.pullC n b) = 0 := by
  rw [m.d_pullC, hb, map_zero]

theorem muB_incl {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {I : Ideal A} (γ : DividedPowers I) {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of O)) (l s s' : ℕ) (𝒱 : Set X.Opens) (h : TS γ q l s 𝒱 ≤ TS γ q l s' 𝒱) (j : ℕ) (x : HdR q j) :
    (incl h).o.pull j (muB γ q l s' 𝒱 j x) = muB γ q l s 𝒱 j x := by
  obtain ⟨a, ha, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (CH.cx (GlobalTheory.LogCris.O (smFun X q))) j).1 x
  have d1 : ∀ (s₀ : ℕ), CH.d _ j ((CH.Mor.restrict (GlobalTheory.LogCris.O (smFun X q)) (TO q l s₀ 𝒱).ι).pullC j a) = 0 := fun s₀ =>
    d_pullC_eq_zero _ j a ha
  have d2 : ∀ (s₀ : ℕ), CH.d _ j ((smO γ q l s₀ 𝒱).o.pullC j ((CH.Mor.restrict (GlobalTheory.LogCris.O (smFun X q)) (TO q l s₀ 𝒱).ι).pullC j a)) = 0 := fun s₀ =>
    d_pullC_eq_zero _ j _ (d1 s₀)
  have d3 : CH.d _ j ((incl h).o.pullC j ((smO γ q l s' 𝒱).o.pullC j ((CH.Mor.restrict (GlobalTheory.LogCris.O (smFun X q)) (TO q l s' 𝒱).ι).pullC j a))) = 0 :=
    d_pullC_eq_zero _ j _ (d2 s')
  have e : ∀ s₀ : ℕ, muB γ q l s₀ 𝒱 j ((CH.cx (GlobalTheory.LogCris.O (smFun X q))).cls a ha) =
      (CH.cx _).cls _ (d2 s₀) := fun s₀ =>
    (congrArg ((smO γ q l s₀ 𝒱).o.pull j) (CrystallineSemistableComparison.P.mapH_cls (CH.Mor.restrict (GlobalTheory.LogCris.O (smFun X q)) (TO q l s₀ 𝒱).ι).hom j a ha (d1 s₀))).trans
      (CrystallineSemistableComparison.P.mapH_cls (smO γ q l s₀ 𝒱).o.hom j _ (d1 s₀) (d2 s₀))
  rw [e s', e s]
  refine (CrystallineSemistableComparison.P.mapH_cls (incl h).o.hom j _ (d2 s') d3).trans ?_
  have key : ∀ (b : CH.Cn (CH.modF (sP (TS γ q l s 𝒱)).A) j) (hb : CH.d _ j b = 0),
      b = (smO γ q l s 𝒱).o.pullC j ((CH.Mor.restrict (GlobalTheory.LogCris.O (smFun X q)) (TO q l s 𝒱).ι).pullC j a) →
      (CH.cx (CH.modF (sP (TS γ q l s 𝒱)).A)).cls b hb = (CH.cx _).cls _ (d2 s) := by
    rintro _ _ rfl
    rfl
  refine key _ d3 ?_
  funext t
  rfl

end GlobalTheory.CompanionTheory.MuThick
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClsEqOfEq
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

universe w

namespace GlobalTheory.CompanionTheory.RedPull

theorem cls_eq_of_eq {R : Type} [CommRing R] {K : Cx.{w} R} {n : ℕ} {a b : K.X n} (e : a = b)
    (ha : K.d n a = 0) (hb : K.d n b = 0) : K.cls a ha = K.cls b hb := by
  subst e
  rfl

theorem pull_square {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'} {C C' : Type 1} [Category.{0} C]
    [Category.{0} C'] {F G : C ⥤ ModuleCat.{0} R} {F' G' : C' ⥤ ModuleCat.{0} R'}
    (a : CH.Mor F G (RingHom.id R)) (b : CH.Mor G G' σ) (c : CH.Mor F F' σ) (d : CH.Mor F' G' (RingHom.id R'))
    (j : ℕ) (h : ∀ x : CH.Cn F j, b.pullC j (a.pullC j x) = d.pullC j (c.pullC j x)) (z : CH.H F j) :
    b.pull j (a.pull j z) = d.pull j (c.pull j z) := by
  obtain ⟨x, hx, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (CH.cx F) j).1 z
  have h1 := CrystallineSemistableComparison.CechClassBoundaries.cyc a.hom x hx
  have h2 := CrystallineSemistableComparison.CechClassBoundaries.cyc b.hom _ h1
  have h3 := CrystallineSemistableComparison.CechClassBoundaries.cyc c.hom x hx
  have h4 := CrystallineSemistableComparison.CechClassBoundaries.cyc d.hom _ h3
  change b.hom.mapH j (a.hom.mapH j _) = d.hom.mapH j (c.hom.mapH j _)
  rw [CrystallineSemistableComparison.CechClassBoundaries.mapH_cls' a.hom x hx h1, CrystallineSemistableComparison.CechClassBoundaries.mapH_cls' b.hom _ h1 h2,
    CrystallineSemistableComparison.CechClassBoundaries.mapH_cls' c.hom x hx h3, CrystallineSemistableComparison.CechClassBoundaries.mapH_cls' d.hom _ h3 h4]
  exact cls_eq_of_eq (h x) h2 h4

theorem sq_toSq {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'} {C C' : Type 1} [Category.{0} C]
    [Category.{0} C'] {Φ : PDF R C} {Φ' : PDF R' C'} (mm : SMor Φ Φ' σ) (b : IdF Φ.A) (b' : IdF Φ'.A)
    (ha : mm.Le (IdF.top _) (IdF.top _)) (hb : mm.Le b b') (j : ℕ) (z : CH.H (CH.modF Φ.A) j) :
    (mm.sq ha hb).pull j ((toSq (IdF.top _) b fun _ => rfl).pull j z) =
      (toSq (IdF.top _) b' fun _ => rfl).pull j (mm.o.pull j z) := by
  refine pull_square _ _ _ _ j (fun x => ?_) z
  funext t
  exact Subtype.ext Ideal.quotientMap_mk

theorem nmHM_redM : ∀ {O A A' : Type} [CommRing O] [CommRing A] [CommRing A'] [Algebra O A] [Algebra O A'] {I : Ideal A} {I' : Ideal A'}
    {γ : DividedPowers I} {γ' : DividedPowers I'} {X X' : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {q' : X' ⟶ Spec (CommRingCat.of O)}
    {σ : A →+* A'} (m : NMor γ q (κA O I) γ' q' (κA O I') σ) (l s : ℕ) (r : Option ℤ) (n j : ℕ) (z : HO (TS γ q l s {⊤}) j),
    nmHM m l s r n j (redM (TS γ q l s {⊤}) r ((l : A) ^ n) j z) = redM (TS γ' q' l s {⊤}) r ((l : A') ^ n) j (nmHO m l s j z) := by
  intro O A A' _ _ _ _ _ I I' γ γ' X X' q q' σ m l s r n j z
  exact sq_toSq (nmS m l s) _ _ (fun _ _ _ => trivial) (nm_std m l s r n) j z

end GlobalTheory.CompanionTheory.RedPull
end
