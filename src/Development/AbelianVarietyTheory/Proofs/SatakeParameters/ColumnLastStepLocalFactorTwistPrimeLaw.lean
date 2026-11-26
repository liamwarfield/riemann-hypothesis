module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftAutomorphicForm
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsVectorPrescribedCosetsBadPrimesFrames
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepDatumTwistPrimeInvariantCongruentFrames

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CouplingCosetRepresentativesCongrAtTwistPrime
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CouplingCosetRepresentativesCongrAtTwistPrime
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.MainNotions Formalism.L2.Ker GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwTop
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LocQCoset

open GlobalTheory.TopInv

variable {E : Type} [Field E] [NumberField E] {P : HeightOneSpectrum (𝓞 E)} {n : ℕ}

theorem core (q : E) (hq : q ≠ 0) (hqi : IntAt P q) (M Dd : ℕ) (hD : 2 * M ≤ Dd) (y0 V₀ V₁ : Sp E n) (g k : Sp E n →ₗ[E] Sp E n)
    (hgI : ∀ x : Sp E n, (∀ l, IntAt P (x l)) → ∀ l, IntAt P (g x l))
    (hkI : ∀ x : Sp E n, (∀ l, IntAt P (x l)) → ∀ l, IntAt P (k x l))
    (hkD : ∀ w : Sp E n, (∀ l, IntAt P (w l)) → ∀ l, IntAt P ((q ^ Dd)⁻¹ * (k w - w) l))
    (hgy : ∀ l, IntAt P ((q ^ M)⁻¹ * (g y0 - y0) l)) (hy0 : ∀ l, IntAt P (q ^ M * y0 l))
    (h0 : ∀ l, IntAt P ((q ^ M)⁻¹ * (V₀ - y0) l)) (h1 : ∀ l, IntAt P ((q ^ M)⁻¹ * (V₁ - y0) l)) :
    ∀ l, IntAt P ((q ^ M)⁻¹ * (g (k V₁) - V₀) l) := by
  have hqpow : ∀ m : ℕ, IntAt P (q ^ m) := fun m => mem_intS.1 ((intS P).pow_mem (mem_intS.2 hqi) m)
  obtain ⟨s, hs⟩ : ∃ s, Dd = 2 * M + s := ⟨Dd - 2 * M, by omega⟩

  have hA : ∀ l, IntAt P ((q ^ M)⁻¹ * (k y0 - y0) l) := by
    intro l
    have h := hkD ((q ^ M) • y0) (fun l => by simpa [smul_eq_mul] using hy0 l) l
    have e : (q ^ M)⁻¹ * (k y0 - y0) l = q ^ s * ((q ^ Dd)⁻¹ * (k ((q ^ M) • y0) - (q ^ M) • y0) l) := by
      simp only [map_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      rw [hs, pow_add, pow_mul]
      field_simp
      ring
    rw [e]
    exact mem_intS.1 ((intS P).mul_mem (mem_intS.2 (hqpow s)) (mem_intS.2 h))

  have hB : ∀ l, IntAt P ((q ^ M)⁻¹ * (k V₁ - k y0) l) := by
    intro l
    have h := hkI ((q ^ M)⁻¹ • (V₁ - y0)) (fun l => by simpa [smul_eq_mul] using h1 l) l
    rwa [map_smul, map_sub, Pi.smul_apply, smul_eq_mul] at h
  have hC : ∀ l, IntAt P ((q ^ M)⁻¹ * (k V₁ - y0) l) := by
    intro l
    have e : (q ^ M)⁻¹ * (k V₁ - y0) l = (q ^ M)⁻¹ * (k V₁ - k y0) l + (q ^ M)⁻¹ * (k y0 - y0) l := by
      simp only [Pi.sub_apply]; ring
    rw [e]; exact (hB l).add (hA l)
  have hE : ∀ l, IntAt P ((q ^ M)⁻¹ * (g (k V₁) - g y0) l) := by
    intro l
    have h := hgI ((q ^ M)⁻¹ • (k V₁ - y0)) (fun l => by simpa [smul_eq_mul] using hC l) l
    rwa [map_smul, map_sub, Pi.smul_apply, smul_eq_mul] at h
  intro l
  have e : (q ^ M)⁻¹ * (g (k V₁) - V₀) l =
      (q ^ M)⁻¹ * (g (k V₁) - g y0) l + (q ^ M)⁻¹ * (g y0 - y0) l + (-1 : E) * ((q ^ M)⁻¹ * (V₀ - y0) l) := by
    simp only [Pi.sub_apply]; ring
  rw [e]
  exact mem_intS.1 ((intS P).add_mem ((intS P).add_mem (mem_intS.2 (hE l)) (mem_intS.2 (hgy l)))
    ((intS P).mul_mem ((intS P).neg_mem (intS P).one_mem) (mem_intS.2 (h0 l))))

end GlobalTheory.LocQCoset

namespace GlobalTheory.LocQCoset

open GlobalTheory.TopInv

theorem coset_agree : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
  ∀ (hi : t.m2 + 1 ≤ D.R.m) (β : (St (t.m2 + 1) hi).Ch) (P : SB t μ), P.1 ∉ t.Pr.vGs →
  ∀ (p p₁ : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) (t.m2 + 1)) (g k : Sp t.X.E (D.R.N (t.m2 + 1)) ≃ₗ[t.X.E] Sp t.X.E (D.R.N (t.m2 + 1))),
    g ∈ GLint t.X.E (D.R.N (t.m2 + 1)) P.1 →
    SameCoset t.sel (t.tup μ) (t.cst μ) P (g (y0At A (t.m2 + 1) hi β P)) (y0At A (t.m2 + 1) hi β P) →
    k ∈ GLint t.X.E (D.R.N (t.m2 + 1)) P.1 →
    (∀ w ∈ stdAt t.X.E (D.R.N (t.m2 + 1)) P.1, ((qOf P.1 : t.X.E) ^ (t.cst μ).D P)⁻¹ • (k w - w) ∈ stdAt t.X.E (D.R.N (t.m2 + 1)) P.1) →
    (∀ w, frsF t.sel (t.tup μ) p₁ P w = frsF t.sel (t.tup μ) p P (g (k w))) →
    ((qOf P.1 : t.X.E) ^ (t.cst μ).M) • (frsF t.sel (t.tup μ) p P).symm (repY (cosetOf A (t.m2 + 1) hi β p)) ∈ stdAt t.X.E (D.R.N (t.m2 + 1)) P.1 ∧
    ((qOf P.1 : t.X.E) ^ (t.cst μ).M) • (frsF t.sel (t.tup μ) p₁ P).symm (repY (cosetOf A (t.m2 + 1) hi β p₁)) ∈ stdAt t.X.E (D.R.N (t.m2 + 1)) P.1 ∧
    ((qOf P.1 : t.X.E) ^ (t.cst μ).M)⁻¹ • ((frsF t.sel (t.tup μ) p P).symm (repY (cosetOf A (t.m2 + 1) hi β p₁)) -
      (frsF t.sel (t.tup μ) p P).symm (repY (cosetOf A (t.m2 + 1) hi β p))) ∈ stdAt t.X.E (D.R.N (t.m2 + 1)) P.1) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hP hTie hi β P hPG p p₁ g k hg hgy hk hkD hF
  have hok := t.idx_ok μ
  have hq := qOf_ne (E := t.X.E) P.1
  have hqi : IntAt P.1 ((qOf P.1 : ℕ) : t.X.E) := intAt_nat (P := P.1) _
  have memS : ∀ x : Sp t.X.E (D.R.N (t.m2 + 1)), x ∈ stdAt t.X.E (D.R.N (t.m2 + 1)) P.1 ↔ ∀ l, IntAt P.1 (x l) :=
    fun x => mem_localization_standardLattice P.1 x
  have rep : ∀ p' : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) (t.m2 + 1),
      SameCoset t.sel (t.tup μ) (t.cst μ) P ((frsF t.sel (t.tup μ) p' P).symm (repY (cosetOf A (t.m2 + 1) hi β p')))
        (y0At A (t.m2 + 1) hi β P) := by
    intro p'
    obtain ⟨r, hr⟩ := GlobalTheory.T.exists_vector_prescribed_cosets_badPrimes_frames t.sel (t.tup μ) (t.cst μ) (frsF t.sel (t.tup μ) p') (fun P => y0At A (t.m2 + 1) hi β P)
    have hrep : repY (cosetOf A (t.m2 + 1) hi β p') ∈ cosetOf A (t.m2 + 1) hi β p' :=
      Classical.epsilon_spec (p := fun y => y ∈ cosetOf A (t.m2 + 1) hi β p') ⟨r, hr⟩
    exact hrep P
  have unf : ∀ y y' : Sp t.X.E (D.R.N (t.m2 + 1)), SameCoset t.sel (t.tup μ) (t.cst μ) P y y' →
      ∀ l, IntAt P.1 ((((qOf P.1 : ℕ) : t.X.E) ^ (t.cst μ).M)⁻¹ * (y - y') l) := by
    intro y y' h
    unfold SameCoset at h
    simpa only [if_neg hPG] using h
  have bnd : ∀ y : Sp t.X.E (D.R.N (t.m2 + 1)), SameCoset t.sel (t.tup μ) (t.cst μ) P y (y0At A (t.m2 + 1) hi β P) →
      ∀ l, IntAt P.1 (((qOf P.1 : ℕ) : t.X.E) ^ (t.cst μ).M * y l) :=
    fun y h => (GlobalTheory.T.chartBaseCoset_bounded_typePrimes_and_twist A dtU a hP hTie hi β P y h).2 hPG
  refine ⟨(memS _).2 fun l => ?_, (memS _).2 fun l => ?_, (memS _).2 fun l => ?_⟩
  · simpa only [Pi.smul_apply, smul_eq_mul] using bnd _ (rep p) l
  · simpa only [Pi.smul_apply, smul_eq_mul] using bnd _ (rep p₁) l
  · have hW : (frsF t.sel (t.tup μ) p P).symm (repY (cosetOf A (t.m2 + 1) hi β p₁)) =
        g (k ((frsF t.sel (t.tup μ) p₁ P).symm (repY (cosetOf A (t.m2 + 1) hi β p₁)))) := by
      apply (frsF t.sel (t.tup μ) p P).injective
      rw [LinearEquiv.apply_symm_apply, ← hF, LinearEquiv.apply_symm_apply]
    have hgI : ∀ x : Sp t.X.E (D.R.N (t.m2 + 1)), (∀ l, IntAt P.1 (x l)) → ∀ l, IntAt P.1 (g.toLinearMap x l) :=
      fun x hx => (memS _).1 ((hg x).2 ((memS x).2 hx))
    have hkI : ∀ x : Sp t.X.E (D.R.N (t.m2 + 1)), (∀ l, IntAt P.1 (x l)) → ∀ l, IntAt P.1 (k.toLinearMap x l) :=
      fun x hx => (memS _).1 ((hk x).2 ((memS x).2 hx))
    have hkD' : ∀ w : Sp t.X.E (D.R.N (t.m2 + 1)), (∀ l, IntAt P.1 (w l)) →
        ∀ l, IntAt P.1 ((((qOf P.1 : ℕ) : t.X.E) ^ (t.cst μ).D P)⁻¹ * (k.toLinearMap w - w) l) := by
      intro w hw l
      simpa only [Pi.smul_apply, smul_eq_mul, LinearEquiv.coe_coe] using (memS _).1 (hkD w ((memS w).2 hw)) l
    have hrefl : SameCoset t.sel (t.tup μ) (t.cst μ) P (y0At A (t.m2 + 1) hi β P) (y0At A (t.m2 + 1) hi β P) := by
      unfold SameCoset
      intro l
      rw [sub_self, Pi.zero_apply, mul_zero]
      simpa using intAt_nat (E := t.X.E) (P := P.1) 0
    have hy0 := bnd _ hrefl
    have := core _ hq hqi (t.cst μ).M ((t.cst μ).D P) (hok.depthQ P hPG) (y0At A (t.m2 + 1) hi β P) _ _
      g.toLinearMap k.toLinearMap hgI hkI hkD' (unf _ _ hgy) hy0 (unf _ _ (rep p)) (unf _ _ (rep p₁)) l
    rw [hW]
    simpa only [Pi.smul_apply, smul_eq_mul, LinearEquiv.coe_coe] using this

end GlobalTheory.LocQCoset

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CouplingCosetRepresentativesCongrAtTwistPrimeStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.MainNotions Formalism.L2.Ker GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwTop
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.couplingCoset_representatives_congr_at_twistPrime : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
  ∀ (hi : t.m2 + 1 ≤ D.R.m) (β : (St (t.m2 + 1) hi).Ch) (P : SB t μ), P.1 ∉ t.Pr.vGs →
  ∀ (p p₁ : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) (t.m2 + 1)) (g k : Sp t.X.E (D.R.N (t.m2 + 1)) ≃ₗ[t.X.E] Sp t.X.E (D.R.N (t.m2 + 1))),
    g ∈ GLint t.X.E (D.R.N (t.m2 + 1)) P.1 →
    SameCoset t.sel (t.tup μ) (t.cst μ) P (g (y0At A (t.m2 + 1) hi β P)) (y0At A (t.m2 + 1) hi β P) →
    k ∈ GLint t.X.E (D.R.N (t.m2 + 1)) P.1 →
    (∀ w ∈ stdAt t.X.E (D.R.N (t.m2 + 1)) P.1, ((qOf P.1 : t.X.E) ^ (t.cst μ).D P)⁻¹ • (k w - w) ∈ stdAt t.X.E (D.R.N (t.m2 + 1)) P.1) →
    (∀ w, frsF t.sel (t.tup μ) p₁ P w = frsF t.sel (t.tup μ) p P (g (k w))) →
    ((qOf P.1 : t.X.E) ^ (t.cst μ).M) • (frsF t.sel (t.tup μ) p P).symm (repY (cosetOf A (t.m2 + 1) hi β p)) ∈ stdAt t.X.E (D.R.N (t.m2 + 1)) P.1 ∧
    ((qOf P.1 : t.X.E) ^ (t.cst μ).M) • (frsF t.sel (t.tup μ) p₁ P).symm (repY (cosetOf A (t.m2 + 1) hi β p₁)) ∈ stdAt t.X.E (D.R.N (t.m2 + 1)) P.1 ∧
    ((qOf P.1 : t.X.E) ^ (t.cst μ).M)⁻¹ • ((frsF t.sel (t.tup μ) p P).symm (repY (cosetOf A (t.m2 + 1) hi β p₁)) -
      (frsF t.sel (t.tup μ) p P).symm (repY (cosetOf A (t.m2 + 1) hi β p))) ∈ stdAt t.X.E (D.R.N (t.m2 + 1)) P.1) := by
  first | exact @GlobalTheory.LocQCoset.coset_agree | exact GlobalTheory.LocQCoset.coset_agree | (intros; apply GlobalTheory.LocQCoset.coset_agree <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepDatumFixedCongruentFrameChangeTwistPrime
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepDatumFixedCongruentFrameChangeTwistPrime
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.MainNotions Formalism.L2.Ker GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwTop
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TopStep GlobalTheory.TopLaw GlobalTheory.TopFrameQ

namespace GlobalTheory.TopFrameQM

section Main

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (cst : LocCst X (rowSG Pr sel mu))

theorem topDat_frames_qM {m2 : ℕ} (hm : R.m = m2 + 2) (hc : cst.Ok) (P : rowSG Pr sel mu) (hP : P.1 ∉ Pr.vGs)
    (hD : 2 * cst.M ≤ cst.D P)
    (κ : Sp X.E (R.N (m2 + 1)) ≃ₗ[X.E] Sp X.E (R.N (m2 + 1)))
    (κ' : Sp X.E (R.N (m2 + 1 + 1)) ≃ₗ[X.E] Sp X.E (R.N (m2 + 1 + 1)))
    (hκ : κ ∈ GLint X.E _ P.1)
    (hκc : ∀ w ∈ stdAt X.E _ P.1, ((qOf P.1 : X.E) ^ cst.D P)⁻¹ • (κ w - w) ∈ stdAt X.E _ P.1)
    (hκ' : κ' ∈ GLint X.E _ P.1)
    (hκ'c : ∀ w ∈ stdAt X.E _ P.1, ((qOf P.1 : X.E) ^ (2 * cst.M))⁻¹ • (κ' w - w) ∈ stdAt X.E _ P.1)
    (y : HomE X.E (R.N (m2 + 1)) (R.N (m2 + 1 + 1))) (y'' : Sp X.E (R.N (m2 + 1)))
    (hy'' : ∀ l, IntAt P.1 ((qOf P.1 : X.E) ^ cst.M * y'' l)) :
    topDat Ch sel mu cst (m2 + 1) P (κ'.symm.toLinearMap ∘ₗ y ∘ₗ κ.toLinearMap) (κ.symm y'') =
      topDat Ch sel mu cst (m2 + 1) P y y'' := by
  have hM1 : 1 ≤ cst.M := hc.M_pos
  have hMD : cst.M + 1 ≤ cst.D P := by omega
  have hMD' : cst.M + 1 ≤ 2 * cst.M := by omega
  have hq : (qOf P.1 : X.E) ≠ 0 := qOf_ne_zero
  have hκ's : κ'.symm ∈ GLint X.E _ P.1 := (GLint X.E _ P.1).inv_mem hκ'
  have hκs : κ.symm ∈ GLint X.E _ P.1 := (GLint X.E _ P.1).inv_mem hκ
  have hκ'sc := cong_symm hκ' hκ'c
  by_cases hg : ∀ j, abelian₂ P.1 (R.N (m2 + 1 + 1)) cst.M (y (Pi.single j 1))
  · unfold topDat
    congr 1
    · unfold PhiTopG
      rw [if_neg hP]
      have hc0 : cOf R (m2 + 1) = 0 := cOf_topB hm
      have hw : ∀ w ∈ stdAt X.E (R.N (m2 + 1)) P.1, ∀ l : Fin (R.N (m2 + 1 + 1)), l.1 + 1 < R.N (m2 + 1 + 1) →
          IntAt P.1 ((κ'.symm (y (κ w)) - y w) l / (qOf P.1 : X.E)) := by
        intro w hw l hl
        have hu := abelian₂.of_basis y hg (glint_mem (⟨κ, hκ⟩ : GLint X.E _ P.1) hw)
        have d1 := mem_stdAt.1 (abelian₂.move hκ's hκ'sc hMD' hu).2 l
        have e1 := intAt_inv_pow_le (a := 1) (by omega) d1
        have hu' : ((qOf P.1 : X.E) ^ cst.D P)⁻¹ • (κ w - w) ∈ stdAt X.E _ P.1 := hκc w hw
        have hyu := (abelian₂.of_basis y hg hu').2 l hl
        rw [map_smul, map_sub, Pi.smul_apply, smul_eq_mul] at hyu
        have e2 := intAt_inv_pow_le (a := 1) (by omega) hyu
        rw [pow_one] at e1 e2
        have e3 := e1.add e2
        rw [← add_div] at e3
        convert e3 using 2
        simp only [Pi.sub_apply]
        ring
      have key := fun z hz => GlobalTheory.TopInv.PhiQ_add (K := X.K) (GlobalTheory.TopInv.qOf_mem P.1) hq
        (resChar (mu : Chr X.F X.E X.K) P.1) R.k R.r (cOf R (m2 + 1)) (R.N (m2 + 1)) (R.N (m2 + 1 + 1) - 1) hc0
        (prXpG X.E (R.N (m2 + 1 + 1)) ∘ₗ y ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1)))) z hz
      refine (congrArg _ (add_sub_cancel _ _)).symm.trans (key _ ?_)
      intro s l
      have hws : (LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1))) (Pi.single s (1 : X.E)) : Sp X.E _) ∈
          stdAt X.E (R.N (m2 + 1)) P.1 :=
        mem_stdAt.2 fun a => GlobalTheory.TopInv.single_int s (Fin.castAdd _ a)
      have := hw _ hws ⟨l.1, by omega⟩ (by show l.1 + 1 < _; omega)
      exact this
    · have h1 := ftY_comp_glint sel mu cst hc P (fun _ => hD) ⟨κ, hκ⟩
          (atNL X.E (R.N (m2 + 1 + 1)) (R.N (m2 + 1 + 1) - 1) ∘ₗ κ'.symm.toLinearMap ∘ₗ y) y'' (κ.symm y'')
          (fun h => absurd h hP) (fun _ => hy'') (fun h => absurd h hP)
          (fun _ => by
            show ((qOf P.1 : X.E) ^ cst.M)⁻¹ • (κ (κ.symm y'') - y'') ∈ _
            rw [LinearEquiv.apply_symm_apply, sub_self, smul_zero]
            exact zero_mem _)
      refine h1.trans ?_
      have hy''s : ((qOf P.1 : X.E) ^ cst.M) • y'' ∈ stdAt X.E _ P.1 :=
        mem_stdAt.2 fun l => by simpa only [Pi.smul_apply, smul_eq_mul] using hy'' l
      have hδ : ∀ i, IntAt P.1 (((qOf P.1 : X.E) ^ cst.M)⁻¹ *
          ((atNL X.E (R.N (m2 + 1 + 1)) (R.N (m2 + 1 + 1) - 1) ∘ₗ κ'.symm.toLinearMap ∘ₗ y) -
            atNL X.E (R.N (m2 + 1 + 1)) (R.N (m2 + 1 + 1) - 1) ∘ₗ y) (Pi.single i 1)) := by
        intro i
        have d1 := mem_stdAt.1 (abelian₂.move hκ's hκ'sc (v := y (Pi.single i 1)) hMD' (hg i)).2
        have e1 : ∀ l, IntAt P.1 ((κ'.symm (y (Pi.single i 1)) - y (Pi.single i 1)) l / (qOf P.1 : X.E) ^ cst.M) :=
          fun l => intAt_inv_pow_le (by omega) (d1 l)
        have e2 := GlobalTheory.TopInv.atNL_int (R.N (m2 + 1 + 1) - 1) _ _ e1
        rw [inv_mul_eq_div]
        convert e2 using 2
        simp only [LinearMap.sub_apply, LinearMap.comp_apply, map_sub]
        rfl
      have h2 := GlobalTheory.ftY_pert_qM sel mu cst hc P hP hD (atNL X.E (R.N (m2 + 1 + 1)) (R.N (m2 + 1 + 1) - 1) ∘ₗ y)
        _ y'' hδ hy''s
      rw [add_sub_cancel] at h2
      exact h2
  · have h0 : topDat Ch sel mu cst (m2 + 1) P y y'' = 0 := by
      by_contra hne
      exact hg (lam_of_topDat_ne Ch sel mu cst _ P hP y y'' hne)
    rw [h0]
    by_contra hne
    apply hg
    have h1 := lam_of_topDat_ne Ch sel mu cst _ P hP _ _ hne
    have h2 := lam_comp hκs hκ' hκ'c hMD' _ h1
    intro j
    have := h2 j
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] using this

end Main

end GlobalTheory.TopFrameQM
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepDatumFixedCongruentFrameChangeTwistPrimeStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.MainNotions Formalism.L2.Ker GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwTop
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lastStepDatum_fixed_congruentFrameChange_twistPrime : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (cst : LocCst X (rowSG Pr sel mu)) {m2 : ℕ}, R.m = m2 + 2 → cst.Ok → ∀ (P : rowSG Pr sel mu), P.1 ∉ Pr.vGs →
  2 * cst.M ≤ cst.D P →
  ∀ (κ : Sp X.E (R.N (m2 + 1)) ≃ₗ[X.E] Sp X.E (R.N (m2 + 1)))
    (κ' : Sp X.E (R.N (m2 + 1 + 1)) ≃ₗ[X.E] Sp X.E (R.N (m2 + 1 + 1))),
  κ ∈ GLint X.E (R.N (m2 + 1)) P.1 →
  (∀ w ∈ stdAt X.E (R.N (m2 + 1)) P.1, ((qOf P.1 : X.E) ^ cst.D P)⁻¹ • (κ w - w) ∈ stdAt X.E (R.N (m2 + 1)) P.1) →
  κ' ∈ GLint X.E (R.N (m2 + 1 + 1)) P.1 →
  (∀ w ∈ stdAt X.E (R.N (m2 + 1 + 1)) P.1, ((qOf P.1 : X.E) ^ (2 * cst.M))⁻¹ • (κ' w - w) ∈ stdAt X.E (R.N (m2 + 1 + 1)) P.1) →
  ∀ (y : HomE X.E (R.N (m2 + 1)) (R.N (m2 + 1 + 1))) (y'' : Sp X.E (R.N (m2 + 1))),
  (∀ l, IntAt P.1 ((qOf P.1 : X.E) ^ cst.M * y'' l)) →
  topDat Ch sel mu cst (m2 + 1) P (κ'.symm.toLinearMap ∘ₗ y ∘ₗ κ.toLinearMap) (κ.symm y'') =
    topDat Ch sel mu cst (m2 + 1) P y y'' := by
  intro X Pr R Ch sel S mu cst m2 hm hc P hP hD κ κ' hκ hκc hκ' hκ'c y y'' hy''
  exact GlobalTheory.TopFrameQM.topDat_frames_qM Ch sel mu cst hm hc P hP hD κ κ' hκ hκc hκ' hκ'c y y'' hy''
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TopLevelDatumTransformAtTwistPrimeUnderLevels
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TopLevelDatumTransformAtTwistPrimeUnderLevels
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.MainNotions Formalism.L2.Ker GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwTop
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwTopLaw

open Matrix

section Alg

variable {k K : Type} [CommRing k] [Field K]

theorem br_mul_of_LLz {n r d : ℕ} (hn : n = r + d) (A B : Matrix (Fin n) (Fin n) k) (hA : LLz r A) :
    (A * B).submatrix (brI hn) (brI hn) = A.submatrix (brI hn) (brI hn) * B.submatrix (brI hn) (brI hn) := by
  subst hn
  ext s t
  rw [Matrix.submatrix_apply, Matrix.mul_apply, Fin.sum_univ_add, Matrix.mul_apply]
  have h0 : ∑ i : Fin r, A (brI rfl s) (Fin.castAdd d i) * B (Fin.castAdd d i) (brI rfl t) = 0 :=
    Finset.sum_eq_zero fun i _ => by
      rw [hA _ _ (show r ≤ (brI (rfl : r + d = r + d) s).1 from Nat.le_add_right _ _) (show (Fin.castAdd d i).1 < r from i.2), zero_mul]
  rw [h0, zero_add]
  rfl

theorem xiZ_one_val (ξ : kˣ →* Kˣ) : xiZ ξ (1 : k) = 1 := by
  have h := xiZ_unit ξ 1
  simpa using h

theorem xiZ_br_inv (ξ : kˣ →* Kˣ) {n r d : ℕ} (hn : n = r + d) (A B : Matrix (Fin n) (Fin n) k) (hA : LLz r A) (h : A * B = 1) :
    xiZ ξ (A.submatrix (brI hn) (brI hn)).det * xiZ ξ (B.submatrix (brI hn) (brI hn)).det = 1 := by
  have hinj : Function.Injective (brI (r := r) hn) := fun a b hab => Fin.ext (by
    have := congrArg Fin.val hab
    simp only [brI] at this
    omega)
  rw [← xiZ_mul, ← Matrix.det_mul, ← br_mul_of_LLz hn A B hA, h, Matrix.submatrix_one _ hinj, Matrix.det_one, xiZ_one_val]

theorem fin_alg {K : Type} [Field K] (a bb x y s1 s2 XA XB c d : K) (hS : s1 * s2 * (XA * XB) = x⁻¹ * y) (k1 : x * a = 1)
    (k2 : y * bb = 1) : a⁻¹ * (XA * XB * c * d) * s1 * s2 = bb⁻¹ * (c * d) := by
  have ha : a ≠ 0 := right_ne_zero_of_mul_eq_one k1
  have hx : x⁻¹ = a := inv_eq_of_mul_eq_one_right k1
  have hy : y = bb⁻¹ := eq_inv_of_mul_eq_one_left k2
  rw [hx, hy] at hS
  have key : s1 * s2 * (XA * XB) * a⁻¹ = bb⁻¹ := by rw [hS, mul_comm a, mul_assoc, mul_inv_cancel₀ ha, mul_one]
  linear_combination (c * d) * key

end Alg

section Det

variable {E : Type} [Field E]

theorem det_eq_of_blk {N : ℕ} (hN : 1 ≤ N) (G : Sp E N ≃ₗ[E] Sp E N) (J : Sp E ((N - 1) + 0) ≃ₗ[E] Sp E ((N - 1) + 0))
    (h1 : prXpG E N ∘ₗ G.toLinearMap = J.toLinearMap ∘ₗ prXpG E N)
    (h2 : atNL E N (N - 1) ∘ₗ G.toLinearMap = atNL E N (N - 1)) :
    (LinearEquiv.det G : E) = (LinearEquiv.det J : E) := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have hpr : ∀ (v : Sp E (n + 1)) (i : Fin n), J (prXpG E (n + 1) v) i = G v (Fin.castSucc i) := by
    intro v i
    have := congrArg (fun f => f i) (LinearMap.congr_fun h1 v)
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at this
    rw [← this]
    rfl
  have hat : ∀ v : Sp E (n + 1), G v (Fin.last n) = v (Fin.last n) := by
    intro v
    have := LinearMap.congr_fun h2 v
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, atNL, show n + 1 - 1 < n + 1 by omega, dif_pos] at this
    exact this
  have hsingle : ∀ k : Fin n, prXpG E (n + 1) (Pi.single (Fin.castSucc k) 1) = (Pi.single k 1 : Sp E n) := by
    intro k
    funext l
    show (Pi.single (Fin.castSucc k) (1 : E) : Sp E (n + 1)) (Fin.castSucc l) = (Pi.single k (1 : E) : Sp E n) l
    by_cases hl : l = k
    · subst hl
      simp
    · rw [Pi.single_eq_of_ne (fun h => hl (Fin.castSucc_injective _ h)), Pi.single_eq_of_ne hl]
  have hlast : prXpG E (n + 1) (Pi.single (Fin.last n) 1) = 0 := by
    funext l
    show (Pi.single (Fin.last n) (1 : E) : Sp E (n + 1)) (Fin.castSucc l) = 0
    exact Pi.single_eq_of_ne (Fin.castSucc_ne_last l) _
  set M := LinearMap.toMatrix' G.toLinearMap with hM
  have hMe : ∀ i k, M i k = G (Pi.single k 1) i := fun i k => by
    simp [hM, LinearMap.toMatrix'_apply]
  have hB : LastRowColIdentity M := by
    refine ⟨fun k => ?_, fun i => ?_, ?_⟩
    · rw [hMe, hat]
      exact Pi.single_eq_of_ne (Fin.castSucc_ne_last k).symm _
    · rw [hMe, ← hpr, hlast, map_zero]
      rfl
    · rw [hMe, hat]
      simp
  have hsub : M.submatrix Fin.castSucc Fin.castSucc = LinearMap.toMatrix' J.toLinearMap := by
    ext i k
    rw [Matrix.submatrix_apply, hMe, ← hpr, hsingle]
    simp [LinearMap.toMatrix'_apply]
  rw [LinearEquiv.coe_det, LinearEquiv.coe_det, ← LinearMap.det_toMatrix', ← LinearMap.det_toMatrix' J.toLinearMap, ← hM,
    blk_det M hB, hsub]

end Det


set_option maxHeartbeats 4000000 in
theorem topLawQ_midTop : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) {G : ChGlob X R.m} {m2 : ℕ},
  ChIdx.Ok Ch sel mu cst L G m2 → QUnif sel mu → ∀ (b : L.β (m2 + 1)) (P : rowSG Pr sel mu), P.1 ∉ Pr.vGs →
  ∀ (g : Sp X.E (R.N (m2 + 1)) ≃ₗ[X.E] Sp X.E (R.N (m2 + 1))) (z : X.K), MidLev Ch sel mu cst (m2 + 1) P (L.h (m2 + 1) b P) g z →
  ∀ (g' : Sp X.E (R.N (m2 + 1 + 1)) ≃ₗ[X.E] Sp X.E (R.N (m2 + 1 + 1))) (z' : X.K), TopLev Ch sel mu cst (m2 + 1 + 1) P g' z' →
  ∀ (y : HomE X.E (R.N (m2 + 1)) (R.N (m2 + 1 + 1))) (y₁ y₂ : Sp X.E (R.N (m2 + 1))),
  ((qOf P.1 : X.E) ^ cst.M)⁻¹ • (y₁ - y₂) ∈ stdAt X.E (R.N (m2 + 1)) P.1 →
  ((qOf P.1 : X.E) ^ cst.M) • y₂ ∈ stdAt X.E (R.N (m2 + 1)) P.1 →
  z' * topDat Ch sel mu cst (m2 + 1) P (g'.symm.toLinearMap ∘ₗ y ∘ₗ g.toLinearMap) (g.symm y₁) *
      rhoS Ch sel mu (m2 + 1) P ((LinearEquiv.det g : X.Eˣ) : X.E) * rhoT Ch sel mu (m2 + 1) P ((LinearEquiv.det g' : X.Eˣ) : X.E) =
    z * topDat Ch sel mu cst (m2 + 1) P y y₂ := by
  intro X Pr R Ch sel S mu cst L G m2 hOk hU b P hP g z hmid g' z' htop y y₁ y₂ hδ hq
  classical
  have hm := hOk.hm
  have hcst := hOk.cst_ok
  have hD := hOk.depthQ P hP
  have hwQ : P.1 ∈ QE sel (mu : Chr X.F X.E X.K) := (Finset.mem_union.mp P.2).resolve_left hP
  have hqm : ((qOf P.1 : ℕ) : 𝓞 X.E) ∈ P.1.asIdeal := qOf_memB P.1
  have hu := hU P.1 hwQ
  have hq0 := ciQ_ne_zero hu
  have hNpos := R.N_pos (m2 + 1 + 1)
  have hNm : R.N (m2 + 1 + 1) = R.N R.m := by rw [hm]
  have hn' : R.N (m2 + 1) = R.r + (m2 + 1) * R.t := rank_midQ (R := R) hm
  have hr' : R.r ≤ R.N (m2 + 1) := by rw [hn']; exact Nat.le_add_right _ _
  have hnA : R.N (m2 + 1 + 1) - 1 + 0 = R.r + R.m * R.t := by rw [hNm, Nat.add_zero]; exact rank_X'_eq R
  have hrA : R.r ≤ R.N (m2 + 1 + 1) - 1 + 0 := by rw [hnA]; exact Nat.le_add_right _ _
  have hc0 : cOf R (m2 + 1) = 0 := cOf_topB hm
  have hkj := kj_midQ (R := R) hm
  set ξ := resChar (mu : Chr X.F X.E X.K) P.1 with hξ

  have hgC : g ∈ prCat (Pr := Pr) cst.sharp (m2 + 1) P.1 (L.h (m2 + 1) b P) :=
    (exists_midLev_iff Ch sel mu cst (m2 + 1) P (L.h (m2 + 1) b P) g).1 ⟨z, hmid⟩
  have hgI : g ∈ GLint X.E (R.N (m2 + 1)) P.1 := hOk.int (m2 + 1) b P hgC
  have hgiI : g⁻¹ ∈ GLint X.E (R.N (m2 + 1)) P.1 := (GLint X.E (R.N (m2 + 1)) P.1).inv_mem hgI
  have hJ : ∀ rr : AutY X R (m2 + 1), rr ∈ Loc.Cbe (Jat (Pr := Pr) cst.sharp (m2 + 1) P.1) (L.h (m2 + 1) b P) →
      rr ∈ LocE.JQ P.1 (qOf P.1) (R.k + (m2 + 1)) (R.N (m2 + 1)) (cOf R (m2 + 1)) := by
    intro rr hrr
    have h2 := hrr.2
    rw [hOk.last_h] at h2
    have h3 : rr ∈ Jat (Pr := Pr) (R := R) cst.sharp (m2 + 1) P.1 := by simpa [MulAut.conj_apply] using h2
    unfold Jat at h3
    rwa [if_neg hP] at h3
  obtain ⟨rc, hrc, hxc, rfl⟩ := hmid
  have hgiC : g⁻¹ ∈ prCat (Pr := Pr) cst.sharp (m2 + 1) P.1 (L.h (m2 + 1) b P) := Subgroup.inv_mem _ hgC
  unfold prCat at hgiC
  obtain ⟨ri, hri, hxi⟩ := hgiC
  have lB : LLz R.r (redMQ P.1 g.toLinearMap) := by
    have := jq_LLz hqm hq0 (hJ rc hrc) hxc
    rwa [hkj] at this
  have lC : LLz R.r (redMQ P.1 (g⁻¹ : Sp X.E (R.N (m2 + 1)) ≃ₗ[X.E] Sp X.E (R.N (m2 + 1))).toLinearMap) := by
    have := jq_LLz hqm hq0 (hJ ri hri) hxi
    rwa [hkj] at this

  obtain ⟨j, hj, hpr, hat, rfl⟩ := htop
  unfold rowLevTop at hj
  rw [if_neg hP] at hj
  have hjI : j ∈ GLint X.E (R.N (m2 + 1 + 1) - 1 + 0) P.1 := hj.1
  have hjiI : j⁻¹ ∈ GLint X.E (R.N (m2 + 1 + 1) - 1 + 0) P.1 := (GLint X.E _ P.1).inv_mem hjI
  have hji : j⁻¹ ∈ LocE.JQ P.1 (qOf P.1) R.r (R.N (m2 + 1 + 1) - 1) 0 := Subgroup.inv_mem _ hj
  have lAi : LLz R.r (redMQ P.1 j.toLinearMap) :=
    jq_LLz (n := R.N (m2 + 1 + 1) - 1) (c := 0) (g := j) (rr := j) hqm hq0 hj (fun x => by rw [tlq_inX_zero, tlq_inX_zero])
  have lA : LLz R.r (redMQ P.1 (j⁻¹ : Sp X.E (R.N (m2 + 1 + 1) - 1 + 0) ≃ₗ[X.E] Sp X.E (R.N (m2 + 1 + 1) - 1 + 0)).toLinearMap) :=
    jq_LLz (n := R.N (m2 + 1 + 1) - 1) (c := 0) (g := j⁻¹) (rr := j⁻¹) hqm hq0 hji (fun x => by rw [tlq_inX_zero, tlq_inX_zero])

  have hpr' : ∀ v, prXpG X.E (R.N (m2 + 1 + 1)) (g'.symm v) = j⁻¹ (prXpG X.E (R.N (m2 + 1 + 1)) v) := by
    intro v
    have := LinearMap.congr_fun hpr (g'.symm v)
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at this
    rw [this]
    show _ = j.symm (j _)
    rw [LinearEquiv.symm_apply_apply]
  have hat' : ∀ v, atNL X.E (R.N (m2 + 1 + 1)) (R.N (m2 + 1 + 1) - 1) (g'.symm v) = atNL X.E (R.N (m2 + 1 + 1)) (R.N (m2 + 1 + 1) - 1) v := by
    intro v
    have := LinearMap.congr_fun hat (g'.symm v)
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at this
    exact this.symm
  have eX : prXpG X.E (R.N (m2 + 1 + 1)) ∘ₗ (g'.symm.toLinearMap ∘ₗ y ∘ₗ g.toLinearMap) ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1))) =
      (j⁻¹ : Sp X.E (R.N (m2 + 1 + 1) - 1 + 0) ≃ₗ[X.E] Sp X.E (R.N (m2 + 1 + 1) - 1 + 0)).toLinearMap ∘ₗ (prXpG X.E (R.N (m2 + 1 + 1)) ∘ₗ y) ∘ₗ
        g.toLinearMap ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1))) := by
    refine LinearMap.ext fun v => ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    exact hpr' _
  have eT : atNL X.E (R.N (m2 + 1 + 1)) (R.N (m2 + 1 + 1) - 1) ∘ₗ (g'.symm.toLinearMap ∘ₗ y ∘ₗ g.toLinearMap) =
      (atNL X.E (R.N (m2 + 1 + 1)) (R.N (m2 + 1 + 1) - 1) ∘ₗ y) ∘ₗ ((⟨g, hgI⟩ : ↥(GLint X.E (R.N (m2 + 1)) P.1)) : Sp X.E (R.N (m2 + 1)) ≃ₗ[X.E] Sp X.E (R.N (m2 + 1))).toLinearMap := by
    refine LinearMap.ext fun v => ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    exact hat' _
  have hδ' : ((qOf P.1 : X.E) ^ cst.M)⁻¹ • ((⟨g, hgI⟩ : ↥(GLint X.E (R.N (m2 + 1)) P.1)).1 (g.symm y₁) - y₂) ∈ stdAt X.E (R.N (m2 + 1)) P.1 := by
    show ((qOf P.1 : X.E) ^ cst.M)⁻¹ • (g (g.symm y₁) - y₂) ∈ _
    rw [LinearEquiv.apply_symm_apply]
    exact hδ
  have hft := ftY_moveQ sel mu cst hcst P hP hD ⟨g, hgI⟩ (atNL X.E (R.N (m2 + 1 + 1)) (R.N (m2 + 1 + 1) - 1) ∘ₗ y) y₂ (g.symm y₁) hδ' hq
  have h1 : redMQ P.1 j.toLinearMap * redMQ P.1 (j⁻¹ : Sp X.E (R.N (m2 + 1 + 1) - 1 + 0) ≃ₗ[X.E] Sp X.E (R.N (m2 + 1 + 1) - 1 + 0)).toLinearMap = 1 := by
    have := redMQ_mul_inv P.1 hjiI
    rwa [inv_inv] at this
  have h2 : redMQ P.1 g.toLinearMap * redMQ P.1 (g⁻¹ : Sp X.E (R.N (m2 + 1)) ≃ₗ[X.E] Sp X.E (R.N (m2 + 1))).toLinearMap = 1 := by
    have := redMQ_mul_inv P.1 hgiI
    rwa [inv_inv] at this
  have hphi : PhiTopG Ch mu cst.sharp (m2 + 1) (m2 + 1 + 1) (R.N (m2 + 1 + 1)) P.1
      ((j⁻¹ : Sp X.E (R.N (m2 + 1 + 1) - 1 + 0) ≃ₗ[X.E] Sp X.E (R.N (m2 + 1 + 1) - 1 + 0)).toLinearMap ∘ₗ (prXpG X.E (R.N (m2 + 1 + 1)) ∘ₗ y) ∘ₗ
        g.toLinearMap ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1)))) =
      xiZ ξ ((redMQ P.1 (j⁻¹ : Sp X.E (R.N (m2 + 1 + 1) - 1 + 0) ≃ₗ[X.E] Sp X.E (R.N (m2 + 1 + 1) - 1 + 0)).toLinearMap).submatrix (Fin.castLE hrA) (Fin.castLE hrA)).det *
        xiZ ξ ((redMQ P.1 g.toLinearMap).submatrix (Fin.castLE hr') (Fin.castLE hr')).det *
        PhiTopG Ch mu cst.sharp (m2 + 1) (m2 + 1 + 1) (R.N (m2 + 1 + 1)) P.1
          (prXpG X.E (R.N (m2 + 1 + 1)) ∘ₗ y ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1)))) := by
    unfold PhiTopG
    rw [if_neg hP]
    exact phiQ_law hqm hu ξ R.k R.r (cOf R (m2 + 1)) (R.N (m2 + 1)) (R.N (m2 + 1 + 1) - 1) hc0 hr' hrA hgI hjiI _ _ _
      (fun v hv => redV_map P.1 _ (glint_int P.1 hjiI) hv) lA lAi lB lC h1 h2 (prXpG X.E (R.N (m2 + 1 + 1)) ∘ₗ y)

  have hs1 : rhoS Ch sel mu (m2 + 1) P ((LinearEquiv.det g : X.Eˣ) : X.E) = xiZ ξ⁻¹ (redMQ P.1 g.toLinearMap).det := by
    unfold rhoS
    rw [if_neg hP, unitV_eq, redP_detEquiv P.1 hgI]
  have hdet : ((LinearEquiv.det g' : X.Eˣ) : X.E) = ((LinearEquiv.det j : X.Eˣ) : X.E) :=
    det_eq_of_blk (by omega) g' j hpr hat
  have hs2 : rhoT Ch sel mu (m2 + 1) P ((LinearEquiv.det g' : X.Eˣ) : X.E) = xiZ ξ (redMQ P.1 j.toLinearMap).det := by
    unfold rhoT
    rw [if_neg hP, unitV_eq, hdet, redP_detEquiv P.1 hjI]
  have hz' : rowChrTop Ch mu cst.sharp (m2 + 1 + 1) (R.N (m2 + 1 + 1)) P.1 j.toLinearMap =
      (xiZ ξ ((redMQ P.1 j.toLinearMap).submatrix (brI hnA) (brI hnA)).det)⁻¹ := by
    unfold rowChrTop
    rw [if_neg hP]
    exact lamQB_eq ξ (kj := R.r) (r := R.r) (n := R.N (m2 + 1 + 1) - 1 + 0) (c := 0) (d := R.m * R.t) rfl hnA hjI (rr := j)
      (fun x => by rw [tlq_inX_zero, tlq_inX_zero])
  have hz : chiInv Ch sel mu cst (m2 + 1) P (L.h (m2 + 1) b P) rc =
      (xiZ ξ ((redMQ P.1 g.toLinearMap).submatrix (brI hn') (brI hn')).det)⁻¹ := by
    unfold chiInv
    rw [hOk.last_h]
    have hrange : Finset.range (cOf R (m2 + 1) - 1) = ∅ := by
      rw [cOf_topB hm]
      rfl
    have hn1 : Loc.n1Arg rc = 0 := by
      unfold Loc.n1Arg
      rw [hrange, Finset.sum_empty]
    have hone : ((1 : AutY X R (m2 + 1))⁻¹ * rc * 1 : AutY X R (m2 + 1)) = rc := by simp
    rw [hn1, hcst.psi_int _ 0 ciIntAt_zero, inv_one, one_mul, hone]
    unfold lamRow
    rw [if_neg hP, lamQB_eq _ hkj hn' hgI hxc]
  have hS := scal_law ξ hnA hn' hrA hr' (redMQ P.1 (j⁻¹ : Sp X.E (R.N (m2 + 1 + 1) - 1 + 0) ≃ₗ[X.E] Sp X.E (R.N (m2 + 1 + 1) - 1 + 0)).toLinearMap)
    (redMQ P.1 j.toLinearMap) (redMQ P.1 g.toLinearMap) (redMQ P.1 (g⁻¹ : Sp X.E (R.N (m2 + 1)) ≃ₗ[X.E] Sp X.E (R.N (m2 + 1))).toLinearMap) lA lC h1 h2
  have k1 := xiZ_br_inv ξ hnA _ _ lA (redMQ_mul_inv P.1 hjI)
  have k2 := xiZ_br_inv ξ hn' _ _ lC (redMQ_mul_inv P.1 hgI)
  unfold topDat
  rw [eX, hphi, hz', hz, hs1, hs2, eT, hft]
  exact fin_alg _ _ _ _ _ _ _ _ _ _ hS k1 k2

end GlobalTheory.TwTopLaw
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TopLevelDatumTransformAtTwistPrimeUnderLevelsStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.MainNotions Formalism.L2.Ker GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwTop
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.topLevelDatum_transform_at_twist_prime_under_levels : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) {G : ChGlob X R.m} {m2 : ℕ},
  ChIdx.Ok Ch sel mu cst L G m2 → QUnif sel mu → ∀ (b : L.β (m2 + 1)) (P : rowSG Pr sel mu), P.1 ∉ Pr.vGs →
  ∀ (g : Sp X.E (R.N (m2 + 1)) ≃ₗ[X.E] Sp X.E (R.N (m2 + 1))) (z : X.K), MidLev Ch sel mu cst (m2 + 1) P (L.h (m2 + 1) b P) g z →
  ∀ (g' : Sp X.E (R.N (m2 + 1 + 1)) ≃ₗ[X.E] Sp X.E (R.N (m2 + 1 + 1))) (z' : X.K), TopLev Ch sel mu cst (m2 + 1 + 1) P g' z' →
  ∀ (y : HomE X.E (R.N (m2 + 1)) (R.N (m2 + 1 + 1))) (y₁ y₂ : Sp X.E (R.N (m2 + 1))),
  ((qOf P.1 : X.E) ^ cst.M)⁻¹ • (y₁ - y₂) ∈ stdAt X.E (R.N (m2 + 1)) P.1 →
  ((qOf P.1 : X.E) ^ cst.M) • y₂ ∈ stdAt X.E (R.N (m2 + 1)) P.1 →
  z' * topDat Ch sel mu cst (m2 + 1) P (g'.symm.toLinearMap ∘ₗ y ∘ₗ g.toLinearMap) (g.symm y₁) *
      rhoS Ch sel mu (m2 + 1) P ((LinearEquiv.det g : X.Eˣ) : X.E) * rhoT Ch sel mu (m2 + 1) P ((LinearEquiv.det g' : X.Eˣ) : X.E) =
    z * topDat Ch sel mu cst (m2 + 1) P y y₂ := by
  first | exact @GlobalTheory.TwTopLaw.topLawQ_midTop | exact GlobalTheory.TwTopLaw.topLawQ_midTop | (intros; apply GlobalTheory.TwTopLaw.topLawQ_midTop <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TopRankLevelMemIntegralGLAtTwistPrime
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TopRankLevelMemIntegralGLAtTwistPrime
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.MainNotions Formalism.L2.Ker GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwTop
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TopLevInt

theorem mem_GLint_of_topLev : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (cst : LocCst X (rowSG Pr sel mu)) (j : ℕ) (P : rowSG Pr sel mu), P.1 ∉ Pr.vGs →
  ∀ (g : Sp X.E (R.N j) ≃ₗ[X.E] Sp X.E (R.N j)) (z : X.K), TopLev Ch sel mu cst j P g z → g ∈ GLint X.E (R.N j) P.1 := by
  intro X Pr R Ch sel S mu cst j P hP g z hT
  obtain ⟨g', hg', hpr, hat, -⟩ := hT
  unfold rowLevTop at hg'
  rw [if_neg hP] at hg'
  have hst : g' ∈ stabL X.E _ (stdAt X.E _ P.1) := (Subgroup.mem_inf.1 hg').1
  show ∀ x, g x ∈ stdAt X.E (R.N j) P.1 ↔ x ∈ stdAt X.E (R.N j) P.1
  intro x
  have h1 : prXpG X.E (R.N j) (g x) = g' (prXpG X.E (R.N j) x) := LinearMap.congr_fun hpr x
  have h2 : atNL X.E (R.N j) (R.N j - 1) (g x) = atNL X.E (R.N j) (R.N j - 1) x := LinearMap.congr_fun hat x
  have h3 := hst (prXpG X.E (R.N j) x)
  rw [ciMem_stdAt, ciMem_stdAt] at h3 ⊢
  rw [xt_split j (g x), xt_split j x, h1, h2, h3]

end GlobalTheory.TopLevInt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TopRankLevelMemIntegralGLAtTwistPrimeStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.MainNotions Formalism.L2.Ker GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwTop
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.topRankLevel_mem_integralGL_at_twist_prime : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (cst : LocCst X (rowSG Pr sel mu)) (j : ℕ) (P : rowSG Pr sel mu), P.1 ∉ Pr.vGs →
  ∀ (g : Sp X.E (R.N j) ≃ₗ[X.E] Sp X.E (R.N j)) (z : X.K), TopLev Ch sel mu cst j P g z → g ∈ GLint X.E (R.N j) P.1 := by
  first | exact @GlobalTheory.TopLevInt.mem_GLint_of_topLev | exact GlobalTheory.TopLevInt.mem_GLint_of_topLev | (intros; apply GlobalTheory.TopLevInt.mem_GLint_of_topLev <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ColumnLastStepLocalFactorTwistPrimeLaw
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.MainNotions Formalism.L2.Ker GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwTop
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.TwTopQ

theorem topF_eq {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) {u : Pr.Word} (i : ℕ) (P : rowSG Pr sel mu) (p : ChPt (R := R) sel mu u i) (Y : Set (Sp X.E (R.N i)))
    (p' : ChPt (R := R) sel mu u (i + 1)) (x : HomE X.E (R.N i) (R.N (i + 1))) :
  topF Ch sel mu cst i P p Y p' x = topDat Ch sel mu cst i P (inFr (frsF sel mu p P) (frsF sel mu p' P) x) ((frsF sel mu p P).symm (repY Y)) := rfl

theorem locq_twist : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
  ∀ (hi : t.m2 + 1 + 1 ≤ D.R.m) (β : (St (t.m2 + 1) (Nat.le_of_succ_le hi)).Ch) (β' : (St (t.m2 + 1 + 1) hi).Ch)
    (x x₁ : UA D (t.m2 + 1) (Nat.le_of_succ_le hi)) (x' x₁' : UA D (t.m2 + 1 + 1) hi)
    (κ : ((St (t.m2 + 1) (Nat.le_of_succ_le hi)).K β).lev.U) (κ' : ((St (t.m2 + 1 + 1) hi).K β').lev.U),
    x₁.1 = x.1 * κ.1 → x₁'.1 = x'.1 * κ'.1 →
    ∀ p p' p₁ p₁', IsPtAd A a (t.m2 + 1) (Nat.le_of_succ_le hi) β x p → IsPtAd A a (t.m2 + 1 + 1) hi β' x' p' →
      IsPtAd A a (t.m2 + 1) (Nat.le_of_succ_le hi) β x₁ p₁ → IsPtAd A a (t.m2 + 1 + 1) hi β' x₁' p₁' →
    ∀ (P : SB t μ), P.1 ∉ t.Pr.vGs → ∀ g z g' z', A.cplRel β P g z →
      InFrame t.seam (A.fb (t.m2 + 1) (Nat.le_of_succ_le hi) β) (t.cst μ).D P κ.1 g →
      TopLev t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1 + 1) P g' z' →
      InFrame t.seam (A.fb (t.m2 + 1 + 1) hi β') (topDep t.sel (t.tup μ) (t.cst μ)) P κ'.1 g' →
    ∀ Z, z' * topF t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P p₁ (cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β p₁) p₁' Z *
        rhoS t.Ch t.sel (t.tup μ) (t.m2 + 1) P ((LinearEquiv.det g : t.X.Eˣ) : t.X.E) *
        rhoT t.Ch t.sel (t.tup μ) (t.m2 + 1) P ((LinearEquiv.det g' : t.X.Eˣ) : t.X.E) =
      z * topF t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P p (cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β p) p' Z) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hPin hTie hi β β' x x₁ x' x₁' κ κ' hx hx' p p' p₁ p₁' hp hp' hp₁ hp₁' P hP g z g' z' hcpl hfr htop hfr' Z
  have hok := t.idx_ok μ
  have hc := hok.cst_ok
  have hD := hok.depthQ P hP
  have hM := hc.M_pos
  have hX : t.X.Ok := hPin.fields.ok
  have hU := qUnif_of t.sel (t.tup μ) hX t.pr_ok hPin.sel
  have hgI : g ∈ GLint t.X.E _ P.1 :=
    hok.int (t.m2 + 1) (A.ib (t.m2 + 1) (cpl_lt t μ) β) P ((exists_midLev_iff _ _ _ _ _ _ _ _).1 ⟨z, hcpl.1⟩)
  have hg'I : g' ∈ GLint t.X.E _ P.1 := GlobalTheory.T.topRankLevel_mem_integralGL_at_twist_prime _ _ _ _ _ P hP g' z' htop
  have hdep : topDep t.sel (t.tup μ) (t.cst μ) P = 2 * (t.cst μ).M := if_neg hP
  obtain ⟨hk, hkc⟩ := GlobalTheory.T.chartFrames_mul_adele_at_badPrime A dtU a hPin hTie (t.m2 + 1) (Nat.le_of_succ_le hi) β x x₁ κ.1 p p₁ hx hp hp₁ P (t.cst μ).D g
    (hc.D_pos P) le_rfl hgI hfr
  obtain ⟨hk', hkc'⟩ := GlobalTheory.T.chartFrames_mul_adele_at_badPrime A dtU a hPin hTie (t.m2 + 1 + 1) hi β' x' x₁' κ'.1 p' p₁' hx' hp' hp₁' P
    (topDep t.sel (t.tup μ) (t.cst μ)) g' (by rw [hdep]; omega) (by rw [hdep]; exact hD) hg'I hfr'
  rw [hdep] at hkc'
  have hy0 : y0At A (t.m2 + 1) (Nat.le_of_succ_le hi) β P = A.y0 β P := by
    unfold y0At
    rw [dite_eq_left rfl]
  obtain ⟨hW0, hV1, hW⟩ := GlobalTheory.T.couplingCoset_representatives_congr_at_twistPrime A dtU a hPin hTie (Nat.le_of_succ_le hi) β P hP p p₁ g
    ((frsF t.sel (t.tup μ) p₁ P).trans ((frsF t.sel (t.tup μ) p P).symm.trans g.symm)) hgI (by rw [hy0]; exact hcpl.2) hk hkc
    (fun w => by simp)
  rw [topF_eq, topF_eq]
  have e1 : inFr (frsF t.sel (t.tup μ) p₁ P) (frsF t.sel (t.tup μ) p₁' P) Z =
      ((frsF t.sel (t.tup μ) p₁' P).trans ((frsF t.sel (t.tup μ) p' P).symm.trans g'.symm)).symm.toLinearMap ∘ₗ
        (g'.symm.toLinearMap ∘ₗ inFr (frsF t.sel (t.tup μ) p P) (frsF t.sel (t.tup μ) p' P) Z ∘ₗ g.toLinearMap) ∘ₗ
        ((frsF t.sel (t.tup μ) p₁ P).trans ((frsF t.sel (t.tup μ) p P).symm.trans g.symm)).toLinearMap := by
    refine LinearMap.ext fun w => ?_
    simp [inFr, LinearEquiv.trans_symm]
  have e2 : (frsF t.sel (t.tup μ) p₁ P).symm (repY (cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β p₁)) =
      ((frsF t.sel (t.tup μ) p₁ P).trans ((frsF t.sel (t.tup μ) p P).symm.trans g.symm)).symm
        (g.symm ((frsF t.sel (t.tup μ) p P).symm (repY (cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β p₁)))) := by
    simp [LinearEquiv.trans_symm]
  have hy'' : ∀ l, IntAt P.1 (((qOf P.1 : t.X.E) ^ (t.cst μ).M) *
      g.symm ((frsF t.sel (t.tup μ) p P).symm (repY (cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β p₁))) l) := by
    have h1 := (hk _).2 hV1
    rw [map_smul] at h1
    have e3 : ((frsF t.sel (t.tup μ) p₁ P).trans ((frsF t.sel (t.tup μ) p P).symm.trans g.symm))
        ((frsF t.sel (t.tup μ) p₁ P).symm (repY (cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β p₁))) =
        g.symm ((frsF t.sel (t.tup μ) p P).symm (repY (cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β p₁))) := by
      simp
    rw [e3] at h1
    intro l
    simpa using (ciMem_stdAt _ _).1 h1 l
  rw [e1, e2, GlobalTheory.T.lastStepDatum_fixed_congruentFrameChange_twistPrime t.Ch t.sel (t.tup μ) (t.cst μ) (m_eq t μ) hc P hP hD _ _ hk hkc hk' hkc' _ _ hy'']
  exact GlobalTheory.T.topLevelDatum_transform_at_twist_prime_under_levels t.Ch t.sel (t.tup μ) (t.cst μ) (t.idx μ) hok hU (A.ib (t.m2 + 1) (cpl_lt t μ) β) P hP g z hcpl.1 g' z' htop _ _ _ hW hW0

end GlobalTheory.TwTopQ
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ColumnLastStepLocalFactorTwistPrimeLawStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.MainNotions Formalism.L2.Ker GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.columnLastStep_localFactor_twist_prime_law : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
  ∀ (hi : t.m2 + 1 + 1 ≤ D.R.m) (β : (St (t.m2 + 1) (Nat.le_of_succ_le hi)).Ch) (β' : (St (t.m2 + 1 + 1) hi).Ch)
    (x x₁ : UA D (t.m2 + 1) (Nat.le_of_succ_le hi)) (x' x₁' : UA D (t.m2 + 1 + 1) hi)
    (κ : ((St (t.m2 + 1) (Nat.le_of_succ_le hi)).K β).lev.U) (κ' : ((St (t.m2 + 1 + 1) hi).K β').lev.U),
    x₁.1 = x.1 * κ.1 → x₁'.1 = x'.1 * κ'.1 →
    ∀ p p' p₁ p₁', IsPtAd A a (t.m2 + 1) (Nat.le_of_succ_le hi) β x p → IsPtAd A a (t.m2 + 1 + 1) hi β' x' p' →
      IsPtAd A a (t.m2 + 1) (Nat.le_of_succ_le hi) β x₁ p₁ → IsPtAd A a (t.m2 + 1 + 1) hi β' x₁' p₁' →
    ∀ (P : SB t μ), P.1 ∉ t.Pr.vGs → ∀ g z g' z', A.cplRel β P g z →
      InFrame t.seam (A.fb (t.m2 + 1) (Nat.le_of_succ_le hi) β) (t.cst μ).D P κ.1 g →
      TopLev t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1 + 1) P g' z' →
      InFrame t.seam (A.fb (t.m2 + 1 + 1) hi β') (topDep t.sel (t.tup μ) (t.cst μ)) P κ'.1 g' →
    ∀ Z, z' * topF t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P p₁ (cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β p₁) p₁' Z *
        rhoS t.Ch t.sel (t.tup μ) (t.m2 + 1) P ((LinearEquiv.det g : t.X.Eˣ) : t.X.E) *
        rhoT t.Ch t.sel (t.tup μ) (t.m2 + 1) P ((LinearEquiv.det g' : t.X.Eˣ) : t.X.E) =
      z * topF t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P p (cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β p) p' Z) := by
  first | exact @GlobalTheory.TwTopQ.locq_twist | exact GlobalTheory.TwTopQ.locq_twist | (intros; apply GlobalTheory.TwTopQ.locq_twist <;> assumption)
end
