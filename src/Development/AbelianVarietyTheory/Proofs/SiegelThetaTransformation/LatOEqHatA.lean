module

public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFramedPointBaseChangeAlgebraMap
public import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.LocClauseOfUnifPlaces

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LatOEqHatA
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Ker.LatTens

noncomputable def gen {D : D7} (S T : HSp D) (α : Af D.host.F) :
    Matrix (Fin S.rank) (Fin T.rank) D.host.E →+ WO S T :=
  AddMonoidHom.mk' (fun y => Matrix.of fun a k => (pairA D.host.F 0 α) ⊗ₜ[D.host.F] y k a)
    fun y y' => Matrix.ext fun a k => TensorProduct.tmul_add _ (y k a) (y' k a)

def vmv {E : Type} [Field E] {n r : ℕ} (v : Fin n → E) : (Fin r → E) →+ Matrix (Fin n) (Fin r) E :=
  AddMonoidHom.mk' (fun u => vecMulVec v u)
    fun u u' => Matrix.ext fun k a => mul_add (v k) (u a) (u' a)

theorem gen_eq {D : D7} (S T : HSp D) (hS : S.gram = 1) (α : Af D.host.F) (a : D.host.E)
    (s : Fin S.rank → D.host.E) (t : Fin T.rank → D.host.E) :
    (Matrix.of fun i j => (pairA D.host.F 0 α) ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j) : WO S T)
      = gen S T α (vecMulVec (star s) (a • t)) := by
  refine Matrix.ext fun i j => ?_
  simp only [gen, AddMonoidHom.mk'_apply, Matrix.of_apply]
  congr 1
  rw [hS]
  simp only [Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, vecMulVec_apply, Pi.star_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem latO_eq_hatA : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), ∀ (LS Λ : Lt D.host.E S.rank) (LT L : Lt D.host.E T.rank), (∀ v, v ∈ Λ ↔ star v ∈ LS) → IsAA L LT → latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (fun _ => True) = hatA S T (tens Λ L) := by
  intro D S T C LS Λ LT L hΛ hL
  have hS : S.gram = 1 := C.m.gS

  have hmem : ∀ α : Af D.host.F, α ∈ intAf D.host.F → ∀ a : D.host.E, a ∈ D.host.AA →
      ∀ v : Fin S.rank → D.host.E, v ∈ Λ → ∀ t : Fin T.rank → D.host.E, t ∈ LT →
      gen S T α (vecMulVec v (a • t)) ∈ latO S T (LS : Set (Fin S.rank → D.host.E))
        (LT : Set (Fin T.rank → D.host.E)) (fun _ => True) := by
    intro α hα a ha v hv t ht
    unfold latO
    apply AddSubgroup.subset_closure
    refine ⟨α, hα, fun _ h => absurd trivial h, a, ha, star v, (hΛ v).1 hv, t, ht, ?_⟩
    rw [gen_eq S T hS α a (star v) t, star_star]
  apply le_antisymm
  · unfold latO
    rw [AddSubgroup.closure_le]
    rintro w ⟨α, hα, -, a, ha, s, hs, t, ht, rfl⟩
    rw [gen_eq S T hS α a s t]
    unfold hatA
    apply AddSubgroup.subset_closure
    have hsΛ : star s ∈ Λ := (hΛ (star s)).2 (by rw [star_star]; exact hs)
    have htL : a • t ∈ L := (hL (a • t)).2 (AddSubgroup.subset_closure ⟨a, ha, t, ht, rfl⟩)
    exact ⟨α, hα, vecMulVec (star s) (a • t),
      AddSubgroup.subset_closure ⟨star s, hsΛ, a • t, htL, rfl⟩, rfl⟩
  · unfold hatA
    rw [AddSubgroup.closure_le]
    rintro w ⟨α, hα, y, hy, rfl⟩

    have hT : tens Λ L ≤ (latO S T (LS : Set (Fin S.rank → D.host.E))
        (LT : Set (Fin T.rank → D.host.E)) (fun _ => True)).comap (gen S T α) := by
      unfold tens
      rw [AddSubgroup.closure_le]
      rintro _ ⟨v, hv, u, hu, rfl⟩
      have hL' : AddSubgroup.closure {u | ∃ a : D.host.E, a ∈ D.host.AA ∧ ∃ t ∈ LT, u = a • t} ≤
          (latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
            (fun _ => True)).comap ((gen S T α).comp (vmv v)) := by
        rw [AddSubgroup.closure_le]
        rintro _ ⟨a, ha, t, ht, rfl⟩
        exact hmem α hα a ha v hv t ht
      exact hL' ((hL u).1 hu)
    exact hT hy

end GlobalTheory.Ker.LatTens
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AdelicCuspFormAutomorphicBoundedSquareIntegrable
section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AdelicCuspFormAutomorphicBoundedSquareIntegrable
open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct Topology

namespace GlobalTheory.AdelicCusp

theorem adel_muPin_automorphic {D : D7} {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Comp : Type}
    {V : HSp D} {X : Comp → Data E r} {dict : GA D V → Σ k, Frame (X k).Ψ r} {Kf : Subgroup (GA D V)}
    {th : ∀ c, (X c).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {hr : V.rank = r}
    (hd : DictIsUnif V dict Kf th hr) (hloc : GlobalTheory.DictLocTest.LocClause V dict) {mu : GA D V → ℂ}
    (hmu : MuUnit V dict mu) (hmc : Continuous mu) {c : Comp → ℂ} (hc : CUnit c) (s : ℂ)
    (la : ∀ k, Wt (X k).Ψ r) (P : FDSec X) (hPc : ∀ k, ContinuousOn (P k) (X k).dom)
    (hΓ : ∀ k, ∀ γ ∈ (X k).Γ, ∀ x ∈ (X k).dom, P k (lact γ x) = P k x) (hfin : supE X la P ≠ ⊤)
    (φ : GA D V → ℂ) (hφ : ∀ g, φ g = s * (c (dict g).1 * mu g * P (dict g).1 (dict g).2)) :
    (∀ γ ∈ GQ V, ∀ g, φ (γ * g) = φ g) ∧ (∀ k ∈ Kf, ∀ g, φ (g * k) = mu k * φ g) ∧ Continuous φ ∧
      (∃ C : ℝ, ∀ g, ‖φ g‖ ≤ C) ∧ MemLp (onQ V φ) 2 (muQ1 V) := by
  obtain ⟨hQ, hK, -, hdom, -, -⟩ := hd
  obtain ⟨hmul, hnorm, hQ1, hunit⟩ := hmu

  have key : ∀ g g' : GA D V, ∀ γ' ∈ (X (dict g).1).Γ, dict g' = ⟨(dict g).1, lact γ' (dict g).2⟩ →
      c (dict g').1 * P (dict g').1 (dict g').2 = c (dict g).1 * P (dict g).1 (dict g).2 := by
    intro g g' γ' hγ' he
    rw [he]
    show c (dict g).1 * P (dict g).1 (lact γ' (dict g).2) = _
    rw [hΓ _ γ' hγ' _ (hdom g)]
  have hφ' : ∀ g, φ g = s * mu g * (c (dict g).1 * P (dict g).1 (dict g).2) := fun g => by
    rw [hφ]; ring
  have hL : ∀ γ ∈ GQ V, ∀ g, φ (γ * g) = φ g := by
    intro γ hγ g
    obtain ⟨γ', hγ', he⟩ := hQ γ hγ g
    rw [hφ', hφ', key g _ γ' hγ' he, hmul, hQ1 γ hγ, one_mul]
  have hR : ∀ k ∈ Kf, ∀ g, φ (g * k) = mu k * φ g := by
    intro k hk g
    obtain ⟨γ', hγ', he⟩ := hK k hk g
    rw [hφ', hφ', key g _ γ' hγ' he, hmul]
    ring

  have hC : Continuous φ := by
    rw [continuous_iff_continuousAt]
    intro g₀
    obtain ⟨N, hN, k, x, hxc, hx⟩ := hloc g₀
    have hloc' : ∀ g ∈ N, c (dict g).1 * P (dict g).1 (dict g).2 = c k * P k (x g) := by
      intro g hg
      obtain ⟨hxd, γ, hγ, he⟩ := hx g hg
      rw [he]
      show c k * P k (lact γ (x g)) = _
      rw [hΓ k γ hγ (x g) hxd]
    have hcont : ContinuousOn (fun g => s * mu g * (c k * P k (x g))) N :=
      (continuousOn_const.mul hmc.continuousOn).mul
        (continuousOn_const.mul ((hPc k).comp hxc fun g hg => (hx g hg).1))
    have heq : (fun g => s * mu g * (c k * P k (x g))) =ᶠ[𝓝 g₀] φ := by
      filter_upwards [hN] with g hg
      rw [hφ', hloc' g hg]
    exact (hcont.continuousAt hN).congr heq

  have hB : ∀ g, ‖φ g‖ ≤ ‖s‖ * (supE X la P).toReal := by
    intro g
    have hw : (X (dict g).1).pnorm (la (dict g).1) (P (dict g).1) (dict g).2 = ‖P (dict g).1 (dict g).2‖ := by
      unfold ReciprocityTheory.ChartRestriction.G.FD.Data.pnorm
      simp [hunit g]
    have hle : ENNReal.ofReal ((X (dict g).1).pnorm (la (dict g).1) (P (dict g).1) (dict g).2) ≤ supE X la P := by
      unfold Formalism.L2.Pj.supE
      exact le_iSup_of_le ⟨(dict g).1, ⟨(dict g).2, hdom g⟩⟩ le_rfl
    have hP : ‖P (dict g).1 (dict g).2‖ ≤ (supE X la P).toReal := by
      rw [← hw]
      exact (ENNReal.ofReal_le_iff_le_toReal hfin).mp hle
    rw [hφ, norm_mul, norm_mul, norm_mul, hc (dict g).1, hnorm g, one_mul, one_mul]
    exact mul_le_mul_of_nonneg_left hP (norm_nonneg s)
  refine ⟨hL, hR, hC, ⟨_, hB⟩, ?_⟩

  have hinv : ∀ g, onQ V φ (autMk V g) = φ g := by
    intro g
    show φ (Quotient.out (autMk V g)) = φ g
    have h1 := Quotient.exact (Quotient.out_eq (autMk V g))
    have h2 : g * (Quotient.out (autMk V g))⁻¹ ∈ GQ V := QuotientGroup.rightRel_apply.mp h1
    have h3 := hL _ h2 (Quotient.out (autMk V g))
    rw [inv_mul_cancel_right] at h3
    exact h3.symm
  have hmeas : Measurable (onQ V φ) := by
    have : BorelSpace (GA D V) := ⟨rfl⟩
    rw [measurable_from_quotient]
    have : onQ V φ ∘ Quotient.mk'' = φ := funext hinv
    rw [this]
    exact hC.measurable
  refine MemLp.of_bound hmeas.aestronglyMeasurable (‖s‖ * (supE X la P).toReal)
    (Filter.Eventually.of_forall fun q => ?_)
  show ‖φ (Quotient.out q)‖ ≤ _
  exact hB _


set_option maxHeartbeats 1000000 in
theorem phiJ_automorphic : ∀ (D : D7) (T : CoreJ D) (h : LawsJ T) (j : ℕ) (hj : InR D j) (σ : T.Q.c.F →+* ℂ) (hσ : GoodEmb T.Q.c σ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (hD : Dom a n), ∀ f ∈ T.cuspA j a n, (∀ γ ∈ GQ (T.V j σ), ∀ g, T.phiJ j σ a f (γ * g) = T.phiJ j σ a f g) ∧ (∀ k ∈ T.Kf j σ, ∀ g, T.phiJ j σ a f (g * k) = T.mu j σ k * T.phiJ j σ a f g) ∧ Continuous (T.phiJ j σ a f) ∧ (∃ C : ℝ, ∀ g, ‖T.phiJ j σ a f g‖ ≤ C) ∧ MemLp (onQ (T.V j σ) (T.phiJ j σ a f)) 2 (muQ1 (T.V j σ)) := by
  intro D T h j hj σ hσ a n hD f hf
  obtain ⟨th, hr, hth, hd⟩ := h.dictU j hj σ hσ
  have hU := h.unf j hj σ hσ
  have hLK := h.levelK j hj σ hσ
  have hK : T.Kf j σ ≤ GfC (T.V j σ) := fun k hk => ((hLK k).mp hk).1
  have hpos : 0 < D.host.g 0 * D.host.g 1 := Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos
  have hN : ∀ g₀ : GA D (T.V j σ), {g : GA D (T.V j σ) | ∃ k ∈ T.Kf j σ, ∃ h ∈ GinfC (T.V j σ), g = g₀ * k * h} ∈ 𝓝 g₀ :=
    fun g₀ => LevelOpen.level_mem_nhds D (T.V j σ) (D.host.g 0 * D.host.g 1) (T.Kf j σ) hpos hLK g₀
  have hloc := GlobalTheory.DictLocTest.locClause_of_unif_places hd hK hN (fun k τ => ⟨τ.1, hth k τ⟩)
  have hmem : rdU (T.U j σ) f ∈ holSub (T.U j σ).X (laU (T.U j σ) a n) := by
    have h1 := (Submodule.mem_inf.mp hf).2
    rw [Submodule.mem_iInf] at h1
    have h2 := h1 σ
    rw [Submodule.mem_iInf] at h2
    exact h2 hσ

  have hΓ : ∀ P ∈ holSub (T.U j σ).X (laU (T.U j σ) a n), ∀ k, ∀ γ ∈ ((T.U j σ).X k).Γ,
      ∀ x ∈ ((T.U j σ).X k).dom, P k (lact γ x) = P k x := by
    intro P hP
    unfold Formalism.L2.Pj.holSub at hP
    induction hP using Submodule.span_induction with
    | mem Q hQ =>
      intro k γ hγ x hx
      have hQ' : IsHolCusp (T.U j σ).X (laU (T.U j σ) a n) Q := hQ
      unfold Formalism.L2.Pj.IsHolCusp at hQ'
      obtain ⟨⟨⟨-, -, hsec⟩, -⟩, -⟩ := hQ' k
      rw [hsec γ hγ x hx, h.chiTriv j hj σ hσ a n hD k γ hγ, one_mul]
    | zero => intro k γ hγ x hx; rfl
    | add Q R _ _ hQ hR =>
      intro k γ hγ x hx
      simp only [Pi.add_apply, hQ k γ hγ x hx, hR k γ hγ x hx]
    | smul t Q _ hQ =>
      intro k γ hγ x hx
      simp only [Pi.smul_apply, hQ k γ hγ x hx]
  refine adel_muPin_automorphic (hd := hd) (hloc := hloc) (hmu := h.muUnit j hj σ hσ)
    (hmc := h.muCont j hj σ hσ) (hc := h.cUnit j hj σ hσ) (s := (lieFac (T.Q.Dw j) (xiR D) a : ℂ))
    (la := laU (T.U j σ) a n) (P := rdU (T.U j σ) f) (hPc := fun k => rdC_continuousOn hU hD ⟨f, hf⟩ k)
    (hΓ := hΓ _ hmem) (hfin := supE_cusp_ne_top hσ hf) (φ := T.phiJ j σ a f) (hφ := ?_)
  intro g
  simp only [Formalism.L2.Pj.CoreJ.phiJ, Pi.smul_apply, smul_eq_mul, Formalism.L2.Pj.adel_muPin]

end GlobalTheory.AdelicCusp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AdelicCuspFormAutomorphicBoundedSquareIntegrableStatement
open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_cuspForm_automorphic_bounded_square_integrable : ∀ (D : D7) (T : CoreJ D) (h : LawsJ T) (j : ℕ) (hj : InR D j) (σ : T.Q.c.F →+* ℂ) (hσ : GoodEmb T.Q.c σ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (hD : Dom a n), ∀ f ∈ T.cuspA j a n, (∀ γ ∈ GQ (T.V j σ), ∀ g, T.phiJ j σ a f (γ * g) = T.phiJ j σ a f g) ∧ (∀ k ∈ T.Kf j σ, ∀ g, T.phiJ j σ a f (g * k) = T.mu j σ k * T.phiJ j σ a f g) ∧ Continuous (T.phiJ j σ a f) ∧ (∃ C : ℝ, ∀ g, ‖T.phiJ j σ a f g‖ ≤ C) ∧ MemLp (onQ (T.V j σ) (T.phiJ j σ a f)) 2 (muQ1 (T.V j σ)) := by
  first | exact @GlobalTheory.AdelicCusp.phiJ_automorphic | exact GlobalTheory.AdelicCusp.phiJ_automorphic | (intros; apply GlobalTheory.AdelicCusp.phiJ_automorphic <;> assumption)
end
end
