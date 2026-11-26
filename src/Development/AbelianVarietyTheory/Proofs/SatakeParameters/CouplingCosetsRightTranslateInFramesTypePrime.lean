module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartPointRightTranslateByLevelCoupledStep
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteImageHeckeSetSplitPlaceCosets
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicFormsFiniteGL

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CouplingCosetsRightTranslateInFramesTypePrime
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CouplingCosetsRightTranslateInFramesTypePrime
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.MainNotions Formalism.L2.Ker GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwTop GlobalTheory.TopStep
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CplCosetPt

section Gen

variable {E : Type} [Field E] [NumberField E]

theorem intAt_of_val_le (P : HeightOneSpectrum (𝓞 E)) (x : E) (h : P.valuation E x ≤ 1) :
    Formalism.L2.Col.IntAt P x := by
  obtain ⟨n, d, h⟩ := P.exists_primeCompl_mul_eq_of_integer x h
  exact ⟨n, d, d.2, by rw [mul_comm]; exact h⟩

theorem lin_apply_eq_sum {n : ℕ} (g : (Fin n → E) →ₗ[E] (Fin n → E)) (w : Fin n → E) (l : Fin n) :
    g w l = ∑ k, w k * g (Pi.single k 1) l := by
  conv_lhs => rw [LinearMap.pi_apply_eq_sum_univ g w]
  rw [Finset.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Pi.smul_apply, smul_eq_mul]
  rw [show (fun j => if k = j then (1 : E) else 0) = Pi.single k 1 by funext j; simp [Pi.single_apply, eq_comm]]

theorem exists_approx_at (T : Finset (HeightOneSpectrum (𝓞 E))) {n : ℕ} (g : T → (Fin n → E) →ₗ[E] (Fin n → E))
    (c : T → E) (t : T → Fin n → E) :
    ∃ d : Fin n → E, ∀ P : T, ∀ l, (P.1).valuation E (c P * g P (d - t P) l) ≤ 1 := by
  classical
  have hb : ∀ P : T, ∃ b : WithZero (Multiplicative ℤ), 1 ≤ b ∧
      ∀ l k, (P.1).valuation E (c P * g P (Pi.single k 1) l) ≤ b := by
    intro P
    obtain ⟨b, hb⟩ := (Set.finite_range fun lk : Fin n × Fin n =>
      (P.1).valuation E (c P * g P (Pi.single lk.2 1) lk.1)).bddAbove
    exact ⟨max b 1, le_max_right _ _, fun l k => (hb ⟨(l, k), rfl⟩).trans (le_max_left _ _)⟩
  choose B hB1 hBle using hb
  have hB0 : ∀ P, B P ≠ 0 := fun P => (lt_of_lt_of_le zero_lt_one (hB1 P)).ne'
  have hk : ∀ k : Fin n, ∃ a : E, ∀ P : T, (P.1).valuation E (a - t P k) < (B P)⁻¹ := by
    intro k
    obtain ⟨a, -, ha, -⟩ := PI.FinOrdValD.WA.weakApprox T
      (fun v => if h : v ∈ T then algebraMap E (v.adicCompletion E) (t ⟨v, h⟩ k) else 0)
      (fun v => if h : v ∈ T then (B ⟨v, h⟩)⁻¹ else 1)
      (fun v hv => by simp only [dif_pos hv]; exact inv_ne_zero (hB0 _))
    refine ⟨a, fun P => ?_⟩
    have h := ha P.1 P.2
    simp only [dif_pos P.2, Subtype.coe_eta] at h
    rw [← map_sub, PI.FinOrdValD.WA.val_alg] at h
    exact h
  choose a ha using hk
  refine ⟨a, fun P l => ?_⟩
  rw [lin_apply_eq_sum, Finset.mul_sum]
  refine Valuation.map_sum_le _ fun k _ => ?_
  rw [show c P * ((a - t P) k * g P (Pi.single k 1) l) = (a - t P) k * (c P * g P (Pi.single k 1) l) by ring,
    map_mul, Pi.sub_apply]
  calc (P.1).valuation E (a k - t P k) * (P.1).valuation E (c P * g P (Pi.single k 1) l)
      ≤ (B P)⁻¹ * B P := mul_le_mul' (ha k P).le (hBle P l k)
    _ = 1 := inv_mul_cancel₀ (hB0 P)

end Gen

theorem exists_sameCoset_frames {X : Fields} {Pr : Primes X} (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
    (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) {n : ℕ} (f : rowSG Pr sel mu → (Sp X.E n ≃ₗ[X.E] Sp X.E n))
    (y0 : rowSG Pr sel mu → Sp X.E n) :
    ∃ y : Sp X.E n, ∀ P, SameCoset sel mu cst P ((f P).symm y) (y0 P) := by
  classical
  obtain ⟨d, hd⟩ := exists_approx_at (rowSG Pr sel mu) (fun P => ((f P).symm : Sp X.E n →ₗ[X.E] Sp X.E n))
    (fun P => (((qOf P.1 : ℕ) : X.E) ^ (if P.1 ∈ Pr.vGs then 0 else cst.M))⁻¹) (fun P => f P (y0 P))
  refine ⟨d, fun P l => intAt_of_val_le _ _ ?_⟩
  have h := hd P l
  have e : (f P).symm d - y0 P = (f P).symm (d - f P (y0 P)) := by
    rw [map_sub, LinearEquiv.symm_apply_apply]
  rw [e]
  exact h

end GlobalTheory.CplCosetPt

namespace GlobalTheory.CplCosetPt

theorem sameCoset_loc {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E)) {n : ℕ}
    (e₀ e D : ℕ) (c g : Sp E n ≃ₗ[E] Sp E n) (k : GLint E n P) (hc : c ∈ GLint E n P) (hg : g ∈ GLint E n P)
    (hk : k ∈ GlobalTheory.TopStep.prinCong n P D) (hck : c⁻¹ = g * k.1) (hD : e + e₀ ≤ D) (y₀ : Sp E n)
    (hy₀ : ∀ l, IntAt P ((qOf P : E) ^ e * y₀ l)) (hgy : ∀ l, IntAt P (((qOf P : E) ^ e₀)⁻¹ * (g y₀ - y₀) l)) (y : Sp E n) :
    (∀ l, IntAt P (((qOf P : E) ^ e₀)⁻¹ * (c y - y₀) l)) ↔ (∀ l, IntAt P (((qOf P : E) ^ e₀)⁻¹ * (y - y₀) l)) := by
  have hq : ((qOf P : ℕ) : E) ≠ 0 := by
    have : qOf P ≠ 0 := fun h0 => P.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
    exact_mod_cast this
  set q : E := ((qOf P : ℕ) : E) with hqdef
  have hsm : ∀ (a : E) (v : Sp E n), (∀ l, IntAt P (a * v l)) ↔ a • v ∈ stdAt E n P := by
    intro a v
    rw [GlobalTheory.TopStep.mem_stdAt]
    rfl
  have hpow : ∀ (m : ℕ) (v : Sp E n), v ∈ stdAt E n P → q ^ m • v ∈ stdAt E n P := by
    intro m v hv
    have : q ^ m • v = ((qOf P : 𝓞 E) ^ m) • v := by
      rw [← algebraMap_smul E ((qOf P : 𝓞 E) ^ m) v]
      congr 1 <;> simp [hqdef]
    rw [this]
    exact Submodule.smul_mem _ _ hv
  have hw : q ^ e • y₀ ∈ stdAt E n P := (hsm _ _).1 hy₀
  have hkw := hk _ hw
  have hky : (q ^ e₀)⁻¹ • (k.1 y₀ - y₀) ∈ stdAt E n P := by
    obtain ⟨d, hd⟩ : ∃ d, D = d + e + e₀ := ⟨D - e - e₀, by omega⟩
    have e1 : (q ^ e₀)⁻¹ • (k.1 y₀ - y₀) = q ^ d • ((q ^ D)⁻¹ • (k.1 (q ^ e • y₀) - q ^ e • y₀)) := by
      rw [map_smul, ← smul_sub, smul_smul, smul_smul]
      congr 1
      rw [hd, pow_add, pow_add]
      field_simp
    rw [e1]
    exact hpow _ _ hkw
  have hcy : (q ^ e₀)⁻¹ • (c⁻¹ y₀ - y₀) ∈ stdAt E n P := by
    have e2 : c⁻¹ y₀ - y₀ = g (k.1 y₀ - y₀) + (g y₀ - y₀) := by
      rw [hck, LinearEquiv.mul_apply, map_sub]
      abel
    rw [e2, smul_add, ← map_smul]
    exact add_mem ((hg _).2 hky) ((hsm _ _).1 hgy)
  have hcc : ∀ x, c (c⁻¹ x) = x := fun x => by
    rw [← LinearEquiv.mul_apply, mul_inv_cancel]
    rfl
  rw [hsm, hsm]
  have e3 : (q ^ e₀)⁻¹ • (c y - y₀) = c ((q ^ e₀)⁻¹ • (y - y₀) - (q ^ e₀)⁻¹ • (c⁻¹ y₀ - y₀)) := by
    rw [← smul_sub, map_smul]
    simp only [map_sub, hcc]
    congr 1
    abel
  rw [e3, hc]
  exact Submodule.sub_mem_iff_left _ hcy

theorem mem_prinCong_one_of_redGL {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {P : HeightOneSpectrum (𝓞 E)}
    (hq : ((qOf P : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) (j : GLint E n P) (hj : redGL n P j = 1) : j ∈ prinCong n P 1 := by
  intro x hx
  rw [mem_stdAt]
  intro i
  have hjx := mem_stdAt.1 (glint_mem j hx) i
  have hxi := mem_stdAt.1 hx i
  have hr : redP P (j.1 x i) = redP P (x i) := by
    have h := congrFun (redV_redGL j hx) i
    rw [hj, Units.val_one, Matrix.one_mulVec] at h
    exact h
  have hred : redP P (j.1 x i - x i) = 0 := by
    rw [reduction_sub hjx hxi, hr, sub_self]
  have h := intAt_div_of_redP hq (intAt_sub hjx hxi) hred
  have e : (((qOf P : E) ^ 1)⁻¹ • (j.1 x - x)) i = (j.1 x i - x i) / (qOf P : E) := by
    simp [div_eq_inv_mul]
  rw [e]
  exact h

theorem cosetOf_frames_vG : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
  ∀ (hi : t.m2 + 1 ≤ D.R.m) (β : (St (t.m2 + 1) hi).Ch) (p p₁ : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) (t.m2 + 1))
    (P : SB t μ), P.1 ∈ t.Pr.vGs → ∀ (Gg k : GLint t.X.E (D.R.N (t.m2 + 1)) P.1) z, A.cplRel β P Gg.1 z →
    redGL _ P.1 k = redGL _ P.1 Gg → frsF t.sel (t.tup μ) p₁ P = frsF t.sel (t.tup μ) p P * k.1 →
    (∀ l, IntAt P.1 ((qOf P.1 : t.X.E) * (frsF t.sel (t.tup μ) p P).symm (repY (cosetOf A (t.m2 + 1) hi β p)) l)) ∧
    (∀ l, IntAt P.1 ((qOf P.1 : t.X.E) * (frsF t.sel (t.tup μ) p₁ P).symm (repY (cosetOf A (t.m2 + 1) hi β p₁)) l)) ∧
    k.1 ((frsF t.sel (t.tup μ) p₁ P).symm (repY (cosetOf A (t.m2 + 1) hi β p₁))) -
      (frsF t.sel (t.tup μ) p P).symm (repY (cosetOf A (t.m2 + 1) hi β p)) ∈ stdAt t.X.E _ P.1) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hPin H hi β p p₁ P hP Gg k z hrel hred _hfr
  classical
  have hne : ∀ q : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) (t.m2 + 1),
      repY (cosetOf A (t.m2 + 1) hi β q) ∈ cosetOf A (t.m2 + 1) hi β q := by
    intro q
    obtain ⟨y, hy⟩ := exists_sameCoset_frames t.sel (t.tup μ) (t.cst μ) (fun P => frsF t.sel (t.tup μ) q P)
      (fun P => y0At A (t.m2 + 1) hi β P)
    exact Classical.epsilon_spec (p := fun y => y ∈ cosetOf A (t.m2 + 1) hi β q) ⟨y, hy⟩
  have hyy : y0At A (t.m2 + 1) hi β P = A.y0 β P := by
    unfold y0At
    rw [dif_pos rfl]
  have hloc : ∀ q : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) (t.m2 + 1), ∀ l,
      IntAt P.1 (((qOf P.1 : t.X.E) ^ 0)⁻¹ * ((frsF t.sel (t.tup μ) q P).symm (repY (cosetOf A (t.m2 + 1) hi β q)) - A.y0 β P) l) := by
    intro q
    have h := hne q P
    unfold SameCoset at h
    simpa only [hP, if_true, hyy] using h
  have hy₀ : ∀ l, IntAt P.1 ((qOf P.1 : t.X.E) ^ 1 * A.y0 β P l) := by
    intro l
    have h := GlobalTheory.T.intAt_scaled_baseCosetRep_of_adTie D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hPin H β P l
    simpa only [hP, if_true] using h
  have hqI : IntAt P.1 (qOf P.1 : t.X.E) := by
    simpa using IntAt.coe P.1 ((qOf P.1 : ℕ) : 𝓞 t.X.E)
  have hint : ∀ q : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) (t.m2 + 1), ∀ l,
      IntAt P.1 ((qOf P.1 : t.X.E) * (frsF t.sel (t.tup μ) q P).symm (repY (cosetOf A (t.m2 + 1) hi β q)) l) := by
    intro q l
    have h1 := hqI.mul (hloc q l)
    have e : (qOf P.1 : t.X.E) * (frsF t.sel (t.tup μ) q P).symm (repY (cosetOf A (t.m2 + 1) hi β q)) l =
        (qOf P.1 : t.X.E) * (((qOf P.1 : t.X.E) ^ 0)⁻¹ * ((frsF t.sel (t.tup μ) q P).symm (repY (cosetOf A (t.m2 + 1) hi β q)) - A.y0 β P) l) +
          (qOf P.1 : t.X.E) ^ 1 * A.y0 β P l := by
      simp only [pow_zero, inv_one, one_mul, pow_one, Pi.sub_apply]
      ring
    rw [e]
    exact h1.add (hy₀ l)
  refine ⟨hint p, hint p₁, ?_⟩
  have hgy : ∀ l, IntAt P.1 (((qOf P.1 : t.X.E) ^ 0)⁻¹ * (Gg.1 (A.y0 β P) - A.y0 β P) l) := by
    have h := hrel.2
    unfold SameCoset at h
    simpa only [hP, if_true] using h
  have hj : Gg⁻¹ * k ∈ prinCong _ P.1 1 := by
    refine mem_prinCong_one_of_redGL (qOf_notMem_sq hPin.fields.ok t.pr_ok hP) _ ?_
    rw [map_mul, map_inv, hred, inv_mul_cancel]
  have hck : (k.1⁻¹)⁻¹ = Gg.1 * (Gg⁻¹ * k).1 := by
    rw [inv_inv, Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left]
  have key := (sameCoset_loc P.1 0 1 1 k.1⁻¹ Gg.1 (Gg⁻¹ * k) (inv_mem k.2) Gg.2 hj hck (by omega) (A.y0 β P) hy₀ hgy
    (k.1 ((frsF t.sel (t.tup μ) p₁ P).symm (repY (cosetOf A (t.m2 + 1) hi β p₁))))).1 (by
      intro l
      have e : (k.1⁻¹) (k.1 ((frsF t.sel (t.tup μ) p₁ P).symm (repY (cosetOf A (t.m2 + 1) hi β p₁)))) =
          (frsF t.sel (t.tup μ) p₁ P).symm (repY (cosetOf A (t.m2 + 1) hi β p₁)) := k.1.symm_apply_apply _
      rw [e]
      exact hloc p₁ l)
  rw [mem_stdAt]
  intro l
  have e : (k.1 ((frsF t.sel (t.tup μ) p₁ P).symm (repY (cosetOf A (t.m2 + 1) hi β p₁))) -
      (frsF t.sel (t.tup μ) p P).symm (repY (cosetOf A (t.m2 + 1) hi β p))) l =
      ((qOf P.1 : t.X.E) ^ 0)⁻¹ * (k.1 ((frsF t.sel (t.tup μ) p₁ P).symm (repY (cosetOf A (t.m2 + 1) hi β p₁))) - A.y0 β P) l -
      ((qOf P.1 : t.X.E) ^ 0)⁻¹ * ((frsF t.sel (t.tup μ) p P).symm (repY (cosetOf A (t.m2 + 1) hi β p)) - A.y0 β P) l := by
    simp only [pow_zero, inv_one, one_mul, Pi.sub_apply]
    ring
  rw [e]
  exact intAt_sub (key l) (hloc p l)

end GlobalTheory.CplCosetPt

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CouplingCosetsRightTranslateInFramesTypePrimeStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.MainNotions Formalism.L2.Ker GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwTop GlobalTheory.TopStep
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coupling_cosets_right_translate_in_frames_type_prime : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
  ∀ (hi : t.m2 + 1 ≤ D.R.m) (β : (St (t.m2 + 1) hi).Ch) (p p₁ : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) (t.m2 + 1))
    (P : SB t μ), P.1 ∈ t.Pr.vGs → ∀ (Gg k : GLint t.X.E (D.R.N (t.m2 + 1)) P.1) z, A.cplRel β P Gg.1 z →
    redGL _ P.1 k = redGL _ P.1 Gg → frsF t.sel (t.tup μ) p₁ P = frsF t.sel (t.tup μ) p P * k.1 →
    (∀ l, IntAt P.1 ((qOf P.1 : t.X.E) * (frsF t.sel (t.tup μ) p P).symm (repY (cosetOf A (t.m2 + 1) hi β p)) l)) ∧
    (∀ l, IntAt P.1 ((qOf P.1 : t.X.E) * (frsF t.sel (t.tup μ) p₁ P).symm (repY (cosetOf A (t.m2 + 1) hi β p₁)) l)) ∧
    k.1 ((frsF t.sel (t.tup μ) p₁ P).symm (repY (cosetOf A (t.m2 + 1) hi β p₁))) -
      (frsF t.sel (t.tup μ) p P).symm (repY (cosetOf A (t.m2 + 1) hi β p)) ∈ stdAt t.X.E _ P.1) := by
  first | exact @GlobalTheory.CplCosetPt.cosetOf_frames_vG | exact GlobalTheory.CplCosetPt.cosetOf_frames_vG | (intros; apply GlobalTheory.CplCosetPt.cosetOf_frames_vG <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GoodPlaceSplitCondition
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.ValInert

theorem conjSelf (D : D7) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hI : Formalism.UG.IsInertAt D.host.F D.host.E (w.under (𝓞 D.host.F)) w) : IsConjPl D.host w w := by
  intro x y hxy
  have hw : Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (w.under (𝓞 D.host.F)).asIdeal = w.asIdeal := hI
  let σ : 𝓞 D.host.E →+* 𝓞 D.host.E := RingOfIntegers.mapRingHom (D.host.conj : D.host.E →+* D.host.E)
  have hσ : ∀ z : 𝓞 D.host.E, ((σ z : 𝓞 D.host.E) : D.host.E) = D.host.conj (z : D.host.E) := fun z => rfl
  have key : w.asIdeal ≤ Ideal.comap σ w.asIdeal := by
    conv_lhs => rw [← hw]
    rw [Ideal.map_le_iff_le_comap]
    intro s hs
    rw [Ideal.mem_comap, Ideal.mem_comap]
    have e : σ (algebraMap _ _ s) = algebraMap (𝓞 D.host.F) (𝓞 D.host.E) s := by
      apply RingOfIntegers.ext
      rw [hσ]
      have hm : ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) s : 𝓞 D.host.E) : D.host.E) ∈ D.host.F := by
        show ((s : D.host.F) : D.host.E) ∈ D.host.F
        exact (s : D.host.F).2
      exact (GlobalTheory.DesignBC.mem_F_iff D _).1 hm
    rw [e, ← hw]
    exact Ideal.mem_map_of_mem _ hs
  have hy : y = σ x := RingOfIntegers.ext (hxy.trans (hσ x).symm)
  have hx : x = σ y := RingOfIntegers.ext (by rw [hσ, hxy, GlobalTheory.DesignBC.conj_conj])
  exact ⟨fun h => hy ▸ key h, fun h => hx ▸ key h⟩

theorem notSplit (D : D7) (w : HeightOneSpectrum (𝓞 D.host.E)) (h : IsConjPl D.host w w) : ¬ IsSplitPl D.host w := by
  rintro ⟨x, hx, hy⟩
  obtain ⟨y, hy'⟩ : ∃ y : 𝓞 D.host.E, (y : D.host.E) = D.host.conj (x : D.host.E) :=
    ⟨RingOfIntegers.mapRingHom (D.host.conj : D.host.E →+* D.host.E) x, rfl⟩
  exact hy y hy' ((h x y hy').1 hx)

theorem xi_eq {D : D7} {nch : NChoice D} {C C' : CharFrame D} (h : C = C') (T : TupTied D C nch) (T' : TupTied D C' nch)
    (h' : HEq T T') : T.xi = T'.xi := by
  subst h
  cases h'
  rfl

end GlobalTheory.ValInert
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsUnitaryAutColumnFieldOfStandardUnitaryMatr
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsUnitaryAutColumnFieldOfStandardUnitaryMatr
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct

namespace GlobalTheory.TwU.UnitaryFrom

theorem exists_uf_seamGL_eq : ∀ {D : D7} {X : Fields} (s : Seam D X), s.Ok → ∀ {n : ℕ} (G : GL (Fin n) D.host.E), cT (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) (G : Matrix (Fin n) (Fin n) D.host.E) * (G : Matrix (Fin n) (Fin n) D.host.E) = 1 → ∃ g : UF X.E n, seamGL s g.1 = G := by
  intro D X s hs n G hG
  have hconj : ∀ a : D.host.E, s.iE.symm (D.host.conj a) = star (s.iE.symm a) := by
    intro a
    apply s.iE.injective
    rw [RingEquiv.apply_symm_apply, hs.2, RingEquiv.apply_symm_apply]
  have hsig : ∀ a : D.host.E, (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) a = D.host.conj a :=
    fun a => Formalism.MainNotions.GlobalTheoryTheory.jnt_sig_eq_conj D a
  let Gx : GL (Fin n) X.E := bc (s.iE.symm : D.host.E →+* X.E) G
  let M : Matrix (Fin n) (Fin n) X.E := (G : Matrix (Fin n) (Fin n) D.host.E).map s.iE.symm
  have hMM : Mᴴ * M = 1 := by
    ext i j
    have h := congrArg s.iE.symm (congrFun (congrFun hG i) j)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mul_apply, cT, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul,
      hsig, hconj] at h
    rw [Matrix.mul_apply]
    simp only [Matrix.conjTranspose_apply, M, Matrix.map_apply]
    rw [h]
    by_cases hij : i = j
    · subst hij; simp
    · simp [Matrix.one_apply, hij]
  let g : Sp X.E n ≃ₗ[X.E] Sp X.E n :=
    LinearMap.GeneralLinearGroup.generalLinearEquiv X.E (Fin n → X.E) (Matrix.GeneralLinearGroup.toLin Gx)
  have hg : ∀ x, g x = M *ᵥ x := by
    intro x
    rfl
  refine ⟨⟨g, ?_⟩, ?_⟩
  · intro x y
    rw [hStd_apply, hStd_apply, hg, hg]
    have h1 : (∑ i, star ((M *ᵥ x) i) * (M *ᵥ y) i) = star (M *ᵥ x) ⬝ᵥ (M *ᵥ y) := rfl
    have h2 : (∑ i, star (x i) * y i) = star x ⬝ᵥ y := rfl
    rw [h1, h2, Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, hMM,
      Matrix.vecMul_one]
  · apply Units.ext
    show (((seamGL s) g : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) = G
    ext i j
    simp [seamGL, bc, g, Gx]

end GlobalTheory.TwU.UnitaryFrom
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsUnitaryAutColumnFieldOfStandardUnitaryMatrStatement
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitaryAut_columnField_of_standard_unitary_matrix : ∀ {D : D7} {X : Fields} (s : Seam D X), s.Ok → ∀ {n : ℕ} (G : GL (Fin n) D.host.E), cT (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) (G : Matrix (Fin n) (Fin n) D.host.E) * (G : Matrix (Fin n) (Fin n) D.host.E) = 1 → ∃ g : UF X.E n, seamGL s g.1 = G := by
  first | exact @GlobalTheory.TwU.UnitaryFrom.exists_uf_seamGL_eq | exact GlobalTheory.TwU.UnitaryFrom.exists_uf_seamGL_eq | (intros; apply GlobalTheory.TwU.UnitaryFrom.exists_uf_seamGL_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SatakeMultisetAtInertPlaces
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.UbcString

theorem not_isSplitPl_of_inert {R : Ranks} (H : Host R) (w : HeightOneSpectrum (𝓞 H.E))
    (hw : Formalism.UG.IsInertAt H.F H.E (w.under (𝓞 H.F)) w) : ¬ IsSplitPl H w := by
  rintro ⟨x, hx, hy⟩
  let c : 𝓞 H.E ≃+* 𝓞 H.E := RingOfIntegers.mapRingEquiv (H.conj : H.E ≃+* H.E)
  have hc : ∀ z : 𝓞 H.E, ((c z : 𝓞 H.E) : H.E) = H.conj (z : H.E) := fun z => rfl
  have hfix : ∀ a : 𝓞 H.F, c (algebraMap (𝓞 H.F) (𝓞 H.E) a) = algebraMap (𝓞 H.F) (𝓞 H.E) a := by
    intro a
    apply RingOfIntegers.ext
    rw [hc]
    have e : ((algebraMap (𝓞 H.F) (𝓞 H.E) a : 𝓞 H.E) : H.E) = ((a : H.F) : H.E) := rfl
    rw [e]
    exact (H.conjE_mem_hostF_iff _).1 (a : H.F).2
  have hle : w.asIdeal ≤ w.asIdeal.comap (c : 𝓞 H.E →+* 𝓞 H.E) := by
    unfold Formalism.UG.IsInertAt at hw
    rw [← hw, Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, Ideal.mem_comap]
    change c (algebraMap (𝓞 H.F) (𝓞 H.E) a) ∈ _
    rw [hfix]
    exact Ideal.mem_map_of_mem _ ha
  exact hy (c x) (hc x) (hle hx)

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} (A : NAut N)

theorem unr_of_foldr {w : PlE H} (a : A.LP w) (f : ℝ → ℝ) (L : List ℝ) (k : ℝ) (hk : k ∈ L)
    (h : A.unr (L.foldr (fun k acc => A.lpSum (A.lpTw a (f k)) acc) (A.lpZero w))) : A.unr a := by
  induction L with
  | nil => simp at hk
  | cons j L ih =>
    rw [List.foldr_cons, A.unr_sum] at h
    rcases List.mem_cons.1 hk with rfl | hk
    · exact (A.unr_tw a _).1 h.1
    · exact ih hk h.2

theorem frobEig_foldr {w : PlE H} (a : A.LP w) (ha : A.unr a) (f : ℝ → ℝ) (L : List ℝ) :
    A.unr (L.foldr (fun k acc => A.lpSum (A.lpTw a (f k)) acc) (A.lpZero w)) ∧
    A.frobEig (L.foldr (fun k acc => A.lpSum (A.lpTw a (f k)) acc) (A.lpZero w)) =
      (L.map fun k => (A.frobEig a).map (· * ((normV w : ℕ) : ℂ) ^ ((f k : ℝ) : ℂ))).sum := by
  induction L with
  | nil => exact ⟨A.lpZero_unr w, A.frobEig_zero w⟩
  | cons k L ih =>
    have hk := (A.unr_tw a (f k)).2 ha
    refine ⟨(A.unr_sum _ _).2 ⟨hk, ih.1⟩, ?_⟩
    simp only [List.foldr_cons, List.map_cons, List.sum_cons]
    rw [A.frobEig_sum _ _ hk ih.1, A.frobEig_tw a _ ha, ih.2]

theorem sum_singletons {ι : Type} (g : ι → ℂ) (L : List ι) :
    (L.map fun k => ({g k} : Multiset ℂ)).sum = ((L.map g : List ℂ) : Multiset ℂ) := by
  induction L with
  | nil => simp
  | cons k L ih => simp [ih]

end GlobalTheory.UbcString
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAutomorphicVectorSatake
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section

namespace GlobalTheory.IsoComp

open GlobalTheory.CompRed

section Gen

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem isoTyp_indep (a : NG.AlgWt L n) {ι : Type} (S : ι → Submodule ℂ (GAf L n → a.W))
    (hS : ∀ i, NG.IsIrrRep a.ρ (S i)) (hinj : ∀ i j, NG.IsoRep (S i) (S j) → i = j) :
    iSupIndep fun i => NG.isoTyp a.ρ (S i) := by
  classical
  haveI hW : FiniteDimensional ℂ a.W := a.alg.1
  have hT := GlobalTheory.T.finite_doubleCosets_definiteUnitary_maximalLevel L n
  have hfin : ∀ N : ℕ, 0 < N → FiniteDimensional ℂ ↥(Submodule.span ℂ
      {f | f ∈ NG.AFall L n a.ρ ∧ ∀ κ, NG.Cong L n N κ → ∀ g, f (g * κ) = f g}) := by
    intro M hM
    haveI := GlobalTheory.AlgFormsFin.fixedForms_finite L n a.ρ hT hM
    refine Submodule.finiteDimensional_of_le (S₂ := GlobalTheory.AlgFormsFin.fixedForms L n a.ρ M) (Submodule.span_le.2 ?_)
    rintro f ⟨hf, hκ⟩
    exact ⟨hf.1, hκ⟩
  obtain ⟨β, hβ⟩ := GlobalTheory.T.algWt_exists_invForm' L n a
  obtain ⟨B, hB, -⟩ := GlobalTheory.T.class_sum_eq_const_mul_petersson L n a β hβ
  have hG : GlobalTheory.TypeOrthogonality.Good a.ρ B := hB
  exact indep_of_orth (fun x => B x) _ (fun i x hx h0 => pos_zero hG (isoTyp_le _ hx) h0)
    (fun i j hij => isoTyp_orth hG hfin (hS i) (hS j) (fun h => hij (hinj i j h)))

variable {W : Type} [AddCommGroup W] [Module ℂ W]

theorem heckeD_mem_isoTyp {ρ : Representation ℂ (GQ L n) W} (S : Submodule ℂ (GAf L n → W))
    (J : Subgroup (GAf L n)) (Dset : Set (GAf L n))
    (hfin : ((fun x : GAf L n => (x : GAf L n ⧸ J)) '' Dset).Finite) (f : GAf L n → W)
    (hf : f ∈ NG.isoTyp ρ S) : NG.heckeD J Dset f ∈ NG.isoTyp ρ S := by
  classical
  rw [GlobalTheory.HeckeScalarAll.heckeD_eq_sum J Dset hfin]
  refine Submodule.sum_mem _ fun c _ => ?_
  split_ifs with hc
  · exact isoTyp_stable S _ f hf
  · exact Submodule.zero_mem _

theorem heckeD_finset_sum {ι : Type} (J : Subgroup (GAf L n)) (Dset : Set (GAf L n))
    (hfin : ((fun x : GAf L n => (x : GAf L n ⧸ J)) '' Dset).Finite) (s : Finset ι) (F : ι → GAf L n → W) :
    NG.heckeD J Dset (∑ i ∈ s, F i) = ∑ i ∈ s, NG.heckeD J Dset (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [GlobalTheory.HeckeScalarAll.heckeD_zero J Dset hfin]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, GlobalTheory.HeckeScalarAll.heckeD_add' J Dset hfin, ih]

end Gen

end GlobalTheory.IsoComp

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsInertLocalDatumAtInertPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsInertLocalDatumAtInertPlace
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.InertDatumAtInert

open scoped TensorProduct

theorem exists_inertDatum_of_isInertAt (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ)
    (Pp : HeightOneSpectrum (𝓞 E))
    (hw : Formalism.UG.IsInertAt (maximalRealSubfield E) E (Pp.under (𝓞 (maximalRealSubfield E))) Pp) :
    Nonempty (InertDatum E n (Pp.under (𝓞 (maximalRealSubfield E))) Pp) := by
  classical
  set v := Pp.under (𝓞 (maximalRealSubfield E)) with hv
  have hunder : Pp.under (𝓞 (maximalRealSubfield E)) = v := rfl
  obtain ⟨c, hc, -⟩ := GlobalTheory.LFun.InertChart.existsUnique_isConjAt
    (IsCMField.complexConj E).toAlgHom hw hunder
  obtain ⟨ϖ, hU⟩ := GlobalTheory.LFun.InertChart.exists_isUnramInv (GlobalTheory.InertDatumExist.isCMExt E) hw hc
  obtain ⟨k, hk, hke⟩ := GlobalTheory.LFun.InertChart.exists_congr_antiJ (n := n) hU (B := 1) (one_mem _)
    (by simp [Formalism.UG.cT, Matrix.map_one])
  have hO : Formalism.UG.Ov E Pp = Formalism.UG.intL (Pp.adicCompletion E) := Subring.ext fun _ => Iff.rfl
  let e := (Algebra.TensorProduct.comm (maximalRealSubfield E) E
    (v.adicCompletion (maximalRealSubfield E))).toRingEquiv.trans (GlobalTheory.LFun.InertChart.complEquiv hw hunder)
  refine ⟨⟨e, c, ϖ, k, ?_, hU, ?_, ?_, ?_⟩⟩
  · intro x
    show GlobalTheory.LFun.toCompl hunder (Algebra.TensorProduct.comm _ _ _
        (Formalism.UG.sigR (IsCMField.complexConj E).toAlgHom _ x)) =
      c (GlobalTheory.LFun.toCompl hunder (Algebra.TensorProduct.comm _ _ _ x))
    rw [hc]
    congr 1
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => rfl
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  · intro x
    rw [GlobalTheory.InertDatumExist.mem_tensInt_iff, GlobalTheory.LFun.InertChart.mem_intLoc_iff hw hunder, hO]
    exact Iff.rfl
  · rw [← hO]; exact hk
  · simpa using hke

theorem main : ∀ (D : D7), D.host.F = maximalRealSubfield D.host.E → ∀ (Pp : HeightOneSpectrum (𝓞 D.host.E)),
    Formalism.UG.IsInertAt D.host.F D.host.E (Pp.under (𝓞 D.host.F)) Pp →
    ∃ (v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E))) (_ : InertDatum D.host.E D.R.nV v Pp),
      NG.OverPl Pp v := by
  intro D hF Pp hI
  obtain ⟨Dv⟩ := exists_inertDatum_of_isInertAt D.host.E D.R.nV Pp hI
  exact ⟨_, Dv, rfl⟩

end GlobalTheory.InertDatumAtInert

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsInertLocalDatumAtInertPlaceStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_inertLocalDatum_at_inertPlace : ∀ (D : D7), D.host.F = maximalRealSubfield D.host.E → ∀ (Pp : HeightOneSpectrum (𝓞 D.host.E)), Formalism.UG.IsInertAt D.host.F D.host.E (Pp.under (𝓞 D.host.F)) Pp → ∃ (v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E))) (_ : InertDatum D.host.E D.R.nV v Pp), NG.OverPl Pp v := by
  first | exact @GlobalTheory.InertDatumAtInert.main | exact GlobalTheory.InertDatumAtInert.main | (intros; apply GlobalTheory.InertDatumAtInert.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteOrderHeckeCharGalois
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

noncomputable section

namespace GlobalTheory.HeckeToGal

theorem exists_galChar_of_finite_order : ∀ (Ω : Type) [Field Ω] (K : Type) [Field K] [NumberField K] [Algebra K Ω]
    [IsAlgClosure K Ω] (η : HChar K) (n : ℕ), 0 < n → η ^ n = 1 → ∃ χ : G K Ω →* ℂˣ,
      IsOpen (χ.ker : Set (G K Ω)) ∧ (χ = 1 → η = 1) ∧
      ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, ∀ (A : ValuationSubring Ω) (σ : G K Ω),
        IsPlaceOver A v → IsFrob A (normV v) σ → χ σ = η.val v := by
  intro Ω _ K _ _ _ _ η n hn hη
  obtain ⟨art, ha⟩ := GlobalTheory.globalArtinReciprocity_holds K Ω
  have hηn : ∀ x, η.1 x ^ n = 1 := fun x => congrArg (fun ξ : HChar K => ξ.1 x) hη
  have hopen : IsOpen (η.1.ker : Set (Ideles K)) := isOpen_ker_of_pow η.1 η.2.1 hn hηn
  have hinf : infConn K ≤ η.1.ker := by
    rintro _ ⟨y, hy, rfl⟩
    let φ : (InfiniteAdeleRing K)ˣ →* ℂˣ :=
      η.1.comp (Units.map (MonoidHom.inl (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K)))
    have hc : Continuous fun z : InfiniteAdeleRing K => (z, (1 : FiniteAdeleRing (𝓞 K) K)) :=
      continuous_id.prodMk continuous_const
    have hφ : Continuous φ := η.2.1.comp (Continuous.units_map _ hc)
    have hop : IsOpen (φ.ker : Set (InfiniteAdeleRing K)ˣ) := isOpen_ker_of_pow φ hφ hn (fun x => hηn _)
    have hcl : IsClopen (φ.ker : Set (InfiniteAdeleRing K)ˣ) := ⟨Subgroup.isClosed_of_isOpen _ hop, hop⟩
    exact hcl.connectedComponent_subset (one_mem φ.ker) hy
  have hker : art.ker ≤ η.1.ker := by
    rw [ha.ker]
    refine Subgroup.topologicalClosure_minimal _ (sup_le ?_ hinf) (Subgroup.isClosed_of_isOpen _ hopen)
    rintro _ ⟨k, rfl⟩
    exact MonoidHom.mem_ker.mpr (η.2.2 k)
  have hs : Function.Surjective art := ha.quot.surjective
  let ηb : Gab K Ω →* ℂˣ :=
    art.liftOfRightInverse (Function.surjInv hs) (Function.rightInverse_surjInv hs) ⟨η.1, hker⟩
  have hηb : ∀ x, ηb (art x) = η.1 x := fun x =>
    MonoidHom.liftOfRightInverse_comp_apply art (Function.surjInv hs) (Function.rightInverse_surjInv hs) ⟨η.1, hker⟩ x
  have hηbc : Continuous ηb := by
    refine ha.quot.isQuotientMap.continuous_iff.mpr ?_
    have e : (ηb ∘ art) = η.1 := funext hηb
    rw [e]
    exact η.2.1
  let χ : G K Ω →* ℂˣ := (ηb.comp (toAb K Ω))⁻¹
  have hχ : ∀ σ, χ σ = (ηb (toAb K Ω σ))⁻¹ := fun σ => rfl
  have hχc : Continuous χ := by
    have ht : Continuous (toAb K Ω) := (QuotientGroup.isQuotientMap_mk _).continuous
    exact (hηbc.comp ht).inv
  have hχn : ∀ σ, χ σ ^ n = 1 := fun σ => by
    obtain ⟨x, hx⟩ := hs (toAb K Ω σ)
    rw [hχ, ← hx, hηb, inv_pow, hηn, inv_one]
  refine ⟨χ, isOpen_ker_of_pow χ hχc hn hχn, fun h1 => ?_, ?_⟩
  · apply Subtype.ext
    refine MonoidHom.ext fun x => ?_
    obtain ⟨σ, hσ⟩ := toAb_surjective (E := K) (Ω := Ω) (art x)
    have e := DFunLike.congr_fun h1 σ
    rw [hχ, hσ, hηb, MonoidHom.one_apply, inv_eq_one] at e
    exact e
  · filter_upwards [(GlobalTheory.Mem.UnrAe.unr_ae_and_level K η).1.compl_mem_cofinite] with v hv
    have hv : η.UnrAt v := by simpa using hv
    intro A σ hA hσ
    obtain ⟨x, hx, e⟩ := (ha.frob v A hA _).mpr ⟨σ, hσ, rfl⟩
    rw [hχ, ← map_inv, ← map_inv, ← e, hηb, ← η.val_eq hv x hx]
    rfl

end GlobalTheory.HeckeToGal

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.OperatorEigenGoodPlaceFirst
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem GlobalTheory.InertFormFix.mul_idem_of_trivOutside {E : Type} [Field E] [NumberField E] [IsCMField E] (F : Subfield E)
    (hF : F = maximalRealSubfield E) (P : HeightOneSpectrum (𝓞 E))
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) (hv : NG.OverPl P v) (x : AL E)
    (hx : ∀ w, w ≠ v → compAt E w x = 0) :
    ((GlobalTheory.AdelicU.singleFin (P.under (𝓞 F)) 1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (1 : E)) *
      (Formalism.IndefR.principalLevelFrame.tensCastR hF).symm x = (Formalism.IndefR.principalLevelFrame.tensCastR hF).symm x := by
  subst hF
  have hvv : P.under (𝓞 (maximalRealSubfield E)) = v := HeightOneSpectrum.ext hv
  subst hvv
  have hx' : x = GlobalTheory.CongSplit.idemAt E (P.under (𝓞 (maximalRealSubfield E))) * x := by
    have h0 := GlobalTheory.AL_eq_zero_of_compAt E (x - GlobalTheory.CongSplit.idemAt E (P.under (𝓞 (maximalRealSubfield E))) * x)
      (fun w => by
        rw [RingHom.map_sub, RingHom.map_mul]
        by_cases hw : w = P.under (𝓞 (maximalRealSubfield E))
        · rw [hw, GlobalTheory.CongSplit.compAt_idemAt_self, one_mul, sub_self]
        · rw [GlobalTheory.CongSplit.compAt_idemAt_ne E _ hw, hx w hw, zero_mul, sub_zero])
    exact (sub_eq_zero.1 h0)
  conv_rhs => rw [hx']
  rw [RingEquiv.map_mul]
  congr 1

theorem GlobalTheory.InertFormFix.finPart_mul_of_trivOutside : ∀ (D : D7) (hF : D.host.F = maximalRealSubfield D.host.E) (P : HeightOneSpectrum (𝓞 D.host.E)) (e f : Formalism.L2.Theta.AE D), Formalism.IndefR.Mult.IsPrimeIdem P e f → ∀ (v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E))), NG.OverPl P v → ∀ x : AL D.host.E, (∀ w, w ≠ v → compAt D.host.E w x = 0) → Formalism.L2.Theta.finPart D f * (Formalism.IndefR.principalLevelFrame.tensCastR hF).symm x = (Formalism.IndefR.principalLevelFrame.tensCastR hF).symm x := by
  intro D hF P e f hP v hv x hx
  have hf := GlobalTheory.AdelicU.Supp.eq_placeIdem_of_isPrimeIdem hP rfl
  subst hf
  exact GlobalTheory.InertFormFix.mul_idem_of_trivOutside D.host.F hF P v hv x hx


set_option maxHeartbeats 2000000 in
theorem GlobalTheory.InertFormFix.suppF_of_trivOutside : ∀ (D : D7) (hF : D.host.F = maximalRealSubfield D.host.E) (V : Formalism.BasicNotions.TH.HSp D) (n : ℕ) (Q : Formalism.IndefR.principalLevelFrame.RowPsi V n), Formalism.IndefR.principalLevelFrame.StdPsi hF Q → ∀ (P : HeightOneSpectrum (𝓞 D.host.E)) (e f : Formalism.L2.Theta.AE D), Formalism.IndefR.Mult.IsPrimeIdem P e f → ∀ (v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E))), NG.OverPl P v → ∀ κ : GAf D.host.E n, TrivOutside {v} κ → Formalism.IndefR.Mult.SuppF V f (Q.ψ κ) := by
  intro D hF V n Q hQ P e f hP v hv κ hT
  obtain ⟨⟨β, β', hββ', hβ'β, hmat⟩, -⟩ := hQ
  rw [GlobalTheory.SphTrans.suppF_iff f (Q.into κ), hmat κ]
  have hT' : ∀ w, w ≠ v → (κ.1.1 : Matrix (Fin n) (Fin n) (AL D.host.E)).map (compAt D.host.E w) = 1 :=
    fun w hw => hT w (by simpa using hw)
  change Formalism.L2.Theta.finPart D f • (β * (κ.1.1 : Matrix (Fin n) (Fin n) (AL D.host.E)).map
      (Formalism.IndefR.principalLevelFrame.tensCastR hF).symm * β' - 1) = β * (κ.1.1 : Matrix (Fin n) (Fin n) (AL D.host.E)).map
      (Formalism.IndefR.principalLevelFrame.tensCastR hF).symm * β' - 1
  set M : Matrix (Fin n) (Fin n) (AL D.host.E) := κ.1.1 with hMdef
  set K := M.map (Formalism.IndefR.principalLevelFrame.tensCastR hF).symm with hKdef
  have hcore : ∀ a b, Formalism.L2.Theta.finPart D f * (K - 1) a b = (K - 1) a b := by
    intro a b
    have hx : ∀ w, w ≠ v → compAt D.host.E w (M a b - (1 : Matrix (Fin n) (Fin n) (AL D.host.E)) a b) = 0 := by
      intro w hw
      have h1 := congrFun (congrFun (hT' w hw) a) b
      rw [Matrix.map_apply] at h1
      rw [RingHom.map_sub, h1]
      by_cases hab : a = b
      · rw [hab, Matrix.one_apply_eq, Matrix.one_apply_eq, RingHom.map_one, sub_self]
      · rw [Matrix.one_apply_ne hab, Matrix.one_apply_ne hab, RingHom.map_zero, sub_zero]
    have h2 := GlobalTheory.InertFormFix.finPart_mul_of_trivOutside D hF P e f hP v hv _ hx
    have e3 : (K - 1) a b = (Formalism.IndefR.principalLevelFrame.tensCastR hF).symm (M a b -
        (1 : Matrix (Fin n) (Fin n) (AL D.host.E)) a b) := by
      rw [Matrix.sub_apply, hKdef, Matrix.map_apply, RingEquiv.map_sub]
      by_cases hab : a = b
      · rw [hab, Matrix.one_apply_eq, Matrix.one_apply_eq, RingEquiv.map_one]
      · rw [Matrix.one_apply_ne hab, Matrix.one_apply_ne hab, RingEquiv.map_zero]
    rw [e3, h2]
  have hK : Formalism.L2.Theta.finPart D f • (K - 1) = K - 1 := by
    ext a b
    rw [Matrix.smul_apply, smul_eq_mul, hcore]
  have e1 : β * K * β' - 1 = β * (K - 1) * β' := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hββ']
  rw [e1]
  conv_rhs => rw [← hK]
  rw [Matrix.mul_smul, Matrix.smul_mul]

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdelicMatrixCongruentOneAtPrimeMulOfBoth
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdelicMatrixCongruentOneAtPrimeMulOfBoth
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.CongProd

open _root_.Formalism.L2.Col GlobalTheory.TwU
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {P : HeightOneSpectrum (𝓞 E)}

theorem intAtA_add₁ {a b : E ⊗[F] FiniteAdeleRing (𝓞 F) F} (ha : IntAtA (F := F) P a) (hb : IntAtA (F := F) P b) :
    IntAtA (F := F) P (a + b) := by
  obtain ⟨s, hs, h1⟩ := ha
  obtain ⟨r, hr, h2⟩ := hb
  have hi : ∀ x : 𝓞 E, iA F E (algebraMap (𝓞 E) E x) ∈ _root_.Formalism.L2.Herm.intAf F E := fun x => (_root_.Formalism.L2.DIV.toRInt F E x).2
  refine ⟨s * r, fun h => (P.isPrime.mem_or_mem h).elim hs hr, ?_⟩
  have e : iA F E (algebraMap (𝓞 E) E (s * r)) * (a + b) =
      iA F E (algebraMap (𝓞 E) E r) * (iA F E (algebraMap (𝓞 E) E s) * a) +
        iA F E (algebraMap (𝓞 E) E s) * (iA F E (algebraMap (𝓞 E) E r) * b) := by
    rw [map_mul, map_mul]; ring
  rw [e]
  exact add_mem (mul_mem (hi r) h1) (mul_mem (hi s) h2)

theorem intAtA_mul₁ {a b : E ⊗[F] FiniteAdeleRing (𝓞 F) F} (ha : IntAtA (F := F) P a) (hb : IntAtA (F := F) P b) :
    IntAtA (F := F) P (a * b) := by
  obtain ⟨s, hs, h1⟩ := ha
  obtain ⟨r, hr, h2⟩ := hb
  refine ⟨s * r, fun h => (P.isPrime.mem_or_mem h).elim hs hr, ?_⟩
  have e : iA F E (algebraMap (𝓞 E) E (s * r)) * (a * b) =
      (iA F E (algebraMap (𝓞 E) E s) * a) * (iA F E (algebraMap (𝓞 E) E r) * b) := by
    rw [map_mul, map_mul]; ring
  rw [e]
  exact mul_mem h1 h2

theorem intAtA_int₁ (x : 𝓞 E) : IntAtA (F := F) P (iA F E (algebraMap (𝓞 E) E x)) :=
  ⟨1, fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), by
    rw [map_one, map_one, one_mul]; exact (_root_.Formalism.L2.DIV.toRInt F E x).2⟩

theorem intAtA_sum₁ {ι : Type} (s : Finset ι) (f : ι → E ⊗[F] FiniteAdeleRing (𝓞 F) F)
    (h : ∀ i ∈ s, IntAtA (F := F) P (f i)) : IntAtA (F := F) P (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using intAtA_int₁ (F := F) (P := P) 0
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact intAtA_add₁ (h a (Finset.mem_insert_self _ _)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem congAt_mul_prod : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (Q : HeightOneSpectrum (𝓞 E)) (n N : ℕ) (k k' : GL (Fin N) (TensorProduct F E (FiniteAdeleRing (𝓞 F) F))),
    GlobalTheory.TwU.CongAt Q n k → GlobalTheory.TwU.CongAt Q n k' → GlobalTheory.TwU.CongAt Q n (k * k') := by
  intro F E _ _ _ _ _ Q n N k k' h h' a b
  have hq : ((qOf Q : ℕ) : E) ≠ 0 := by
    have : qOf Q ≠ 0 := fun h0 => Q.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
    exact_mod_cast this
  set c := iA F E (((qOf Q : ℕ) : E) ^ n)⁻¹ with hc
  set d := iA F E (algebraMap (𝓞 E) E (((qOf Q : ℕ) : 𝓞 E) ^ n)) with hd
  have hcd : d * c = 1 := by
    rw [hc, hd, ← map_mul, map_pow, map_natCast, mul_inv_cancel₀ (pow_ne_zero _ hq), map_one]
  have e : ((k * k' : GL (Fin N) _) : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) - 1 =
      ((k : Matrix (Fin N) (Fin N) _) - 1) * ((k' : Matrix (Fin N) (Fin N) _) - 1) +
        (((k : Matrix (Fin N) (Fin N) _) - 1) + ((k' : Matrix (Fin N) (Fin N) _) - 1)) := by
    rw [Units.val_mul]; noncomm_ring
  rw [e, Matrix.add_apply, Matrix.add_apply, mul_add, mul_add, Matrix.mul_apply, Finset.mul_sum]
  refine intAtA_add₁ (intAtA_sum₁ _ _ fun l _ => ?_) (intAtA_add₁ (h a b) (h' a b))
  have e2 : ∀ x y : E ⊗[F] FiniteAdeleRing (𝓞 F) F, c * (x * y) = d * ((c * x) * (c * y)) := by
    intro x y
    linear_combination (-(c * (x * y))) * hcd
  rw [e2]
  exact intAtA_mul₁ (intAtA_int₁ _) (intAtA_mul₁ (h a l) (h' l b))

end GlobalTheory.CongProd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdelicMatrixCongruentOneAtPrimeMulOfBothStatement
open NumberField IsDedekindDomain

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicMatrixCongruentOneAtPrime_mul_of_both : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (Q : HeightOneSpectrum (𝓞 E)) (n N : ℕ) (k k' : GL (Fin N) (TensorProduct F E (FiniteAdeleRing (𝓞 F) F))), GlobalTheory.TwU.CongAt Q n k → GlobalTheory.TwU.CongAt Q n k' → GlobalTheory.TwU.CongAt Q n (k * k') := by
  first | exact @GlobalTheory.CongProd.congAt_mul_prod | exact GlobalTheory.CongProd.congAt_mul_prod | (intros; apply GlobalTheory.CongProd.congAt_mul_prod <;> assumption)
end
end
