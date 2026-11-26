module

public import Formalism.LocalToGlobal.Columns.ThetaOpenTwLevQ

@[expose] public section

section -- merged from Formalism.LocalToGlobal.Columns.ChainFrmOk
open NumberField IsDedekindDomain Module Matrix

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section Gen

variable {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))}

theorem frm_exists_c (p p0 : DecoF X.E n ST SG Q) (h : p.deco = p0.deco) :
    ∃ c : GLQ X.E n Q, p = ((1, 1, c) : UF X.E n × GLG (E := X.E) (n := n) (SG := SG) × GLQ X.E n Q) • p0 := by
  refine ⟨fun P => ⟨(p.fr P)⁻¹ * p0.fr P, ?_⟩, ?_⟩
  · show ∀ x, ((p.fr P)⁻¹ * p0.fr P) x ∈ stdAt X.E n P.1 ↔ x ∈ stdAt X.E n P.1
    intro x
    have hx : p.1.2 P (((p.fr P)⁻¹ * p0.fr P) x) = p0.1.2 P x := LinearEquiv.apply_symm_apply _ _
    have h' : p.1.1 = p0.1.1 := h
    rw [← p.2 P, hx, h', p0.2 P]
  · apply Subtype.ext
    simp only [HSMul.hSMul, SMul.smul]
    refine Prod.ext ?_ ?_
    · have h1 := one_smul (UF X.E n × GLG (E := X.E) (n := n) (SG := SG)) p0.1.1
      simp only [HSMul.hSMul, SMul.smul] at h1
      exact h.trans h1.symm
    · funext P
      simp only [DecoF.fr, OneMemClass.coe_one, one_mul, InvMemClass.coe_inv, _root_.mul_inv_rev, inv_inv,
        ← mul_assoc, mul_inv_cancel]

variable (Λ : LevFam X.E X.K n SG) (Θ : LevQFam X.E X.K n Q)

theorem frm_root (hroot : ∀ c : ↥Θ.grp, ∃ m : ℕ, 0 < m ∧ ((Θ.chr c : X.Kˣ) : X.K) ^ m = 1) (g : FrmG Λ Θ) :
    ∃ m : ℕ, 0 < m ∧ (((Λ.chr g.2.1 * Θ.chr g.2.2 : X.Kˣ)) : X.K) ^ m = 1 := by
  haveI : ∀ w : SG, Finite (𝓞 X.E ⧸ w.1.asIdeal) := fun w =>
    Ideal.finiteQuotientOfFreeOfNeBot _ w.1.ne_bot
  obtain ⟨m2, hm2, h2⟩ := hroot g.2.2
  have hfo : IsOfFinOrder g.2.1 := isOfFinOrder_of_finite _
  have ha : ((Λ.chr g.2.1 : X.Kˣ) : X.K) ^ orderOf g.2.1 = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_orderOf_eq_one, map_one, Units.val_one]
  refine ⟨orderOf g.2.1 * m2, Nat.mul_pos hfo.orderOf_pos hm2, ?_⟩
  rw [Units.val_mul, mul_pow, pow_mul, ha, one_pow, one_mul, mul_comm (orderOf _) m2, pow_mul, h2,
    one_pow]


open Classical in
theorem frmGSD_ok_of_finIdx (hX : X.Ok) (C : CoefPk X n (DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG))) (hC : C.Eqv)
    (hfi : ∀ P : Q, Finite (↥(GLint X.E n P.1) ⧸ (Θ P).H))
    (hroot : ∀ c : ↥Θ.grp, ∃ m : ℕ, 0 < m ∧ ((Θ.chr c : X.Kˣ) : X.K) ^ m = 1) : (frmGSD (C.pull DecoF.deco) Λ Θ).Ok := by
  refine { fin_orb := ?_, fin_stab := ?_, nab_smul := ?_, del_smul := ?_, inv := ?_ }
  · obtain ⟨s, hs, hrep⟩ := DecoSet.finite_reps (ST := ST) (SG := SG) (n := n) (posStar_of_conj hX.conjE)
    have : Finite s := hs

    let pt : s → (∀ P : Q, ↥(GLint X.E n P.1) ⧸ (Θ P).H) → Option (DecoF X.E n ST SG Q) := fun d cb =>
      if h : ∃ p0 : DecoF X.E n ST SG Q, p0.deco = d.1 then
        some (((1, 1, fun P => ((cb P).out)⁻¹) : UF X.E n × GLG (E := X.E) (n := n) (SG := SG) × GLQ X.E n Q) • h.choose) else none
    have hfin : Finite (Option (s × (∀ P : Q, ↥(GLint X.E n P.1) ⧸ (Θ P).H))) := inferInstance
    by_cases hne : Nonempty (frmGSD (C.pull DecoF.deco) Λ Θ).Cl
    swap
    · have := not_nonempty_iff.1 hne
      exact inferInstance
    obtain ⟨c00⟩ := hne
    refine Finite.of_surjective (fun a : s × (∀ P : Q, ↥(GLint X.E n P.1) ⧸ (Θ P).H) =>
      match pt a.1 a.2 with
      | some p => (frmGSD (C.pull DecoF.deco) Λ Θ).cls p
      | none => c00) ?_
    intro c
    induction c using Quotient.inductionOn' with
    | h p =>
      obtain ⟨d0, hd0, g, hg⟩ := hrep (DecoF.deco p)

      let p1 : DecoF X.E n ST SG Q := ((g, 1, 1) : UF X.E n × GLG (E := X.E) (n := n) (SG := SG) × GLQ X.E n Q)⁻¹ • p
      have hp1 : p1.deco = d0 := by
        show ((g, (1 : GLG (E := X.E) (n := n) (SG := SG))) : UF X.E n × GLG (E := X.E) (n := n) (SG := SG))⁻¹ • p.deco = d0
        rw [hg, inv_smul_smul]
      have hex : ∃ p0 : DecoF X.E n ST SG Q, p0.deco = d0 := ⟨p1, hp1⟩
      obtain ⟨c, hc⟩ := frm_exists_c p1 hex.choose (hp1.trans hex.choose_spec.symm)

      let cb : ∀ P : Q, ↥(GLint X.E n P.1) ⧸ (Θ P).H := fun P => QuotientGroup.mk ((c P)⁻¹)
      have hout : ∀ P : Q, ((c P)⁻¹)⁻¹ * (cb P).out ∈ (Θ P).H := fun P => QuotientGroup.eq.1 (QuotientGroup.out_eq' (cb P)).symm
      refine ⟨(⟨d0, hd0⟩, cb), ?_⟩
      have hpt : pt ⟨d0, hd0⟩ cb = some (((1, 1, fun P => ((cb P).out)⁻¹) : UF X.E n × GLG (E := X.E) (n := n) (SG := SG) × GLQ X.E n Q) • hex.choose) := dif_pos hex
      show (match pt ⟨d0, hd0⟩ cb with
        | some p => (frmGSD (C.pull DecoF.deco) Λ Θ).cls p
        | none => c00) = _
      rw [hpt]
      let θ : ↥Θ.grp := ⟨fun P => ((c P)⁻¹)⁻¹ * (cb P).out, fun P _ => hout P⟩
      refine ((frmGSD (C.pull DecoF.deco) Λ Θ).cls_eq_iff _ p).mpr ⟨((g, 1, θ) : FrmG Λ Θ)⁻¹, ?_⟩
      refine inv_smul_eq_iff.2 (Eq.symm ?_)
      show ((g, (1 : GLG (E := X.E) (n := n) (SG := SG)), (θ : GLQ X.E n Q)) : UF X.E n × GLG (E := X.E) (n := n) (SG := SG) × GLQ X.E n Q) •
        (((1, 1, fun P => ((cb P).out)⁻¹) : UF X.E n × GLG (E := X.E) (n := n) (SG := SG) × GLQ X.E n Q) • hex.choose) = p
      rw [← mul_smul]
      have e : ((g, (1 : GLG (E := X.E) (n := n) (SG := SG)), (θ : GLQ X.E n Q)) : UF X.E n × GLG (E := X.E) (n := n) (SG := SG) × GLQ X.E n Q) * (1, 1, fun P => ((cb P).out)⁻¹) =
          (g, 1, 1) * (1, 1, c) := by
        refine Prod.ext (by simp) (Prod.ext (by simp) ?_)
        funext P
        show ((c P)⁻¹)⁻¹ * (cb P).out * ((cb P).out)⁻¹ = 1 * c P
        group
      rw [e, mul_smul, ← hc]
      exact smul_inv_smul _ p
  · intro p
    have := DecoSet.finite_stabilizer (posStar_of_conj hX.conjE) (DecoF.deco p : DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG))
    refine Finite.of_injective
      (fun a : MulAction.stabilizer (frmGSD (C.pull DecoF.deco) Λ Θ).G p =>
        (⟨(a.1.1, (a.1.2.1 : GLG (E := X.E) (n := n) (SG := SG))), congrArg DecoF.deco a.2⟩ :
          MulAction.stabilizer (UF X.E n × GLG (E := X.E) (n := n) (SG := SG)) (DecoF.deco p : DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG)))) ?_
    intro a b hab
    have h0 : ((a.1.1, (a.1.2.1 : GLG (E := X.E) (n := n) (SG := SG))) : UF X.E n × GLG (E := X.E) (n := n) (SG := SG)) = (b.1.1, (b.1.2.1 : GLG (E := X.E) (n := n) (SG := SG))) :=
      congrArg Subtype.val hab
    exact Subtype.ext (dga_frm_stab_inj Λ Θ p a.2 b.2 (Prod.mk.inj h0).1)
  · intro g d
    obtain ⟨m, hm, hc⟩ := frm_root Λ Θ hroot g
    exact (hC.nab_smul (g.1, (g.2.1 : GLG (E := X.E) (n := n) (SG := SG))) (DecoF.deco d)).trans (map_root_smul _ _ hm hc).symm
  · intro g d
    obtain ⟨m, hm, hc⟩ := frm_root Λ Θ hroot g
    exact (hC.del_smul (g.1, (g.2.1 : GLG (E := X.E) (n := n) (SG := SG))) (DecoF.deco d)).trans (map_root_smul _ _ hm hc).symm
  · intro g (x : C.V) (y : C.V)
    obtain ⟨m, hm, hc⟩ := frm_root Λ Θ hroot g
    show C.pair ((((Λ.chr g.2.1 * Θ.chr g.2.2 : X.Kˣ)) : X.K) • C.rho g.1 x)
      ((((Λ.chr g.2.1 * Θ.chr g.2.2 : X.Kˣ)) : X.K) • C.rho g.1 y) = C.pair x y
    rw [LinearMap.map_smulₛₗ₂, map_smul, hC.inv, smul_smul]
    show (star (((Λ.chr g.2.1 * Θ.chr g.2.2 : X.Kˣ)) : X.K) * _) • _ = _
    rw [star_mul_root hX.conjK hm hc, one_smul]

end Gen

section Chain

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))

theorem chF_ok_of_finIdx (hX : X.Ok) (u : Pr.Word) (j : ℕ)
    (hfi : ∀ (b : L.β j) (P : QE sel (mu : Chr X.F X.E X.K)), Finite (↥(GLint X.E (R.N j) P.1) ⧸ (L.levQ j b P).H))
    (hroot : ∀ (b : L.β j) (c : ↥(L.levQ j b).grp), ∃ m : ℕ, 0 < m ∧ (((L.levQ j b).chr c : X.Kˣ) : X.K) ^ m = 1) :
    (chF W sel mu L u j).Ok := by
  intro b
  have hC : (colVal W u j (Pr.vT u) Pr.vGs).Eqv :=
    ⟨colVal_nab_smul W u j, colVal_del_smul W u j, roundPk_inv X _ _ hX.emb_star⟩
  exact frmGSD_ok_of_finIdx (L.levG j b) (L.levQ j b) hX (colVal W u j (Pr.vT u) Pr.vGs)
    hC (hfi b) (hroot b)

end Chain

end Formalism.L2.Col
end
end

open NumberField IsDedekindDomain Module Matrix

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section Approx

variable {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E))

theorem tfVal_mem {u : 𝓞 E} {N : ℕ} (hu : u ∈ P.asIdeal ^ N) : P.valuation E (algebraMap (𝓞 E) E u) ≤ WithZero.exp (-(N : ℤ)) := by
  rw [HeightOneSpectrum.valuation_of_algebraMap]
  exact (HeightOneSpectrum.intValuation_le_pow_iff_mem P u N).mpr hu

theorem tfApprox (a : E) (ha : P.valuation E a ≤ 1) (N : ℕ) : ∃ r : 𝓞 E, P.valuation E (a - algebraMap (𝓞 E) E r) ≤ WithZero.exp (-(N : ℤ)) := by
  have hPN : P.asIdeal ^ N ≠ ⊥ := by
    first
      | exact pow_ne_zero _ P.ne_bot
  obtain ⟨t, htP, ht0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hPN
  have hc : algebraMap E (P.adicCompletion E) a ∈ P.adicCompletionIntegers E := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    erw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact ha
  obtain ⟨r, hr⟩ := Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.AdeleIntA.exists_approx_local P
    (algebraMap E (P.adicCompletion E) a) hc t ht0
  refine ⟨r, ?_⟩
  rw [← map_sub] at hr
  erw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at hr
  exact hr.trans ((HeightOneSpectrum.intValuation_le_pow_iff_mem P t N).mpr htP)

end Approx

section Idx

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {n : ℕ} (P : HeightOneSpectrum (𝓞 E)) (N : ℕ)

def tfRed (g : ↥(GLint E n P)) : Fin n → Fin n → 𝓞 E ⧸ P.asIdeal ^ N := fun i j =>
  Ideal.Quotient.mk _ (tfApprox P _ (qsp_entry_int P g i j) N).choose

theorem tfRed_eq {g g' : ↥(GLint E n P)} (h : tfRed P N g = tfRed P N g') : lqPrinc P N ((g⁻¹ * g' : ↥(GLint E n P)) : Sp E n ≃ₗ[E] Sp E n) := by
  classical
  have hmat : ∀ x : ↥(GLint E n P), ((toGLm E n x.1 : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) =
      LinearMap.toMatrix' ((x.1 : Sp E n ≃ₗ[E] Sp E n) : Sp E n →ₗ[E] Sp E n) := fun x => rfl
  have hclose : ∀ l k, P.valuation E (((toGLm E n g'.1 : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) l k -
      ((toGLm E n g.1 : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) l k) ≤ WithZero.exp (-(N : ℤ)) := by
    intro l k
    have hr := (tfApprox P _ (qsp_entry_int P g l k) N).choose_spec
    have hr' := (tfApprox P _ (qsp_entry_int P g' l k) N).choose_spec
    have hmk := congrFun (congrFun h l) k
    simp only [tfRed] at hmk
    have hrr := tfVal_mem P (Ideal.Quotient.eq.mp hmk)
    rw [map_sub] at hrr
    have e : ((toGLm E n g'.1 : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) l k -
        ((toGLm E n g.1 : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) l k =
        (((toGLm E n g'.1 : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) l k -
          algebraMap (𝓞 E) E (tfApprox P _ (qsp_entry_int P g' l k) N).choose) +
        (-(algebraMap (𝓞 E) E (tfApprox P _ (qsp_entry_int P g l k) N).choose -
            algebraMap (𝓞 E) E (tfApprox P _ (qsp_entry_int P g' l k) N).choose) +
          -(((toGLm E n g.1 : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) l k -
            algebraMap (𝓞 E) E (tfApprox P _ (qsp_entry_int P g l k) N).choose)) := by ring
    rw [e]
    refine Valuation.map_add_le _ hr' (Valuation.map_add_le _ ?_ ?_)
    · rw [Valuation.map_neg]
      exact hrr
    · rw [Valuation.map_neg]
      exact hr
  have hM1 : ((toGLm E n (g⁻¹ * g').1 : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) =
      ((toGLm E n (g⁻¹).1 : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *
        ((toGLm E n g'.1 : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) := by
    rw [Subgroup.coe_mul, map_mul, Units.val_mul]
  have hM2 : ((toGLm E n (g⁻¹).1 : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *
      ((toGLm E n g.1 : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) = 1 := by
    rw [← Units.val_mul, ← map_mul, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one, map_one,
      Units.val_one]
  intro i j
  rw [← hmat (g⁻¹ * g'), hM1, ← hM2, ← Matrix.mul_sub, Matrix.mul_apply]
  refine Valuation.map_sum_le _ fun l _ => ?_
  rw [Valuation.map_mul, Matrix.sub_apply]
  exact le_trans (mul_le_of_le_one_left' (qsp_entry_int P g⁻¹ i l)) (hclose l j)

theorem tfFinite_quot (hN : 0 < N) : Finite (𝓞 E ⧸ P.asIdeal ^ N) := by
  have hPN : P.asIdeal ^ N ≠ ⊥ := pow_ne_zero _ P.ne_bot
  first
    | exact @Finite.of_fintype _ (Ideal.fintypeQuotientOfFreeOfNeBot _ hPN)
    | exact Ideal.finiteQuotientOfFreeOfNeBot _ hPN

theorem tfFinite_of_princ (hN : 0 < N) (H : Subgroup ↥(GLint E n P)) (hH : ∀ g : ↥(GLint E n P), lqPrinc P N (g : Sp E n ≃ₗ[E] Sp E n) → g ∈ H) :
    Finite (↥(GLint E n P) ⧸ H) := by
  classical
  haveI := tfFinite_quot P N hN
  let q : Set.range (tfRed P N) → (↥(GLint E n P) ⧸ H) := fun v => QuotientGroup.mk v.2.choose
  refine Finite.of_surjective q ?_
  intro x
  induction x using QuotientGroup.induction_on with
  | H g =>
    refine ⟨⟨tfRed P N g, g, rfl⟩, ?_⟩
    show QuotientGroup.mk _ = QuotientGroup.mk g
    rw [QuotientGroup.eq]
    apply hH
    exact tfRed_eq P N (⟨tfRed P N g, g, rfl⟩ : Set.range (tfRed P N)).2.choose_spec

theorem tfRoot_of_princ (hN : 0 < N) (H : Subgroup ↥(GLint E n P)) (lam : ↥H →* Kˣ)
    (hH : ∀ g : ↥(GLint E n P), lqPrinc P N (g : Sp E n ≃ₗ[E] Sp E n) → ∃ h : g ∈ H, lam ⟨g, h⟩ = 1) (x : ↥H) :
    ∃ m : ℕ, 0 < m ∧ lam x ^ m = 1 := by
  classical
  haveI := tfFinite_quot P N hN
  have key : ∀ k1 k2 : ℕ, k1 < k2 →
      tfRed P N ((x : ↥(GLint E n P)) ^ k1) = tfRed P N ((x : ↥(GLint E n P)) ^ k2) →
      ∃ m : ℕ, 0 < m ∧ lam x ^ m = 1 := by
    intro k1 k2 hlt heq
    have hp := tfRed_eq P N heq
    have hpow : ((x : ↥(GLint E n P)) ^ k1)⁻¹ * (x : ↥(GLint E n P)) ^ k2 =
        (x : ↥(GLint E n P)) ^ (k2 - k1) := by
      rw [inv_mul_eq_iff_eq_mul, ← pow_add, Nat.add_sub_cancel' hlt.le]
    rw [hpow] at hp
    obtain ⟨hmem, hlam⟩ := hH _ hp
    refine ⟨k2 - k1, by omega, ?_⟩
    have hx : (⟨(x : ↥(GLint E n P)) ^ (k2 - k1), hmem⟩ : ↥H) = x ^ (k2 - k1) := by
      apply Subtype.ext
      simp
    rw [← map_pow, ← hx, hlam]
  obtain ⟨k1, k2, hne, heq⟩ := Finite.exists_ne_map_eq_of_infinite
    (fun k : ℕ => tfRed P N ((x : ↥(GLint E n P)) ^ k))
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact key k1 k2 hlt heq
  · exact key k2 k1 hlt heq.symm

end Idx

section Pi

theorem tfPiChar {K : Type} [Field K] {ι : Type} [Fintype ι] {G : ι → Type} [∀ i, Group (G i)] (H : ∀ i, Subgroup (G i))
    (lam : ∀ i, ↥(H i) →* Kˣ) (x : ↥(Subgroup.pi Set.univ H)) :
    piChar H lam x = ∏ i, lam i ⟨x.1 i, x.2 i (Set.mem_univ i)⟩ := by
  simp only [piChar, MonoidHom.finsetProd_apply, MonoidHom.comp_apply]
  rfl

end Pi

section Fam

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {n : ℕ} {Q : Finset (HeightOneSpectrum (𝓞 E))} (Θ : LevQFam E K n Q)

theorem thetaOpen_finIdx (h : ThetaOpen Θ) (P : Q) : Finite (↥(GLint E n P.1) ⧸ (Θ P).H) := by
  obtain ⟨N, hN, hg⟩ := h P
  exact tfFinite_of_princ P.1 N hN (Θ P).H (fun g hgp => (hg g hgp).1)

theorem thetaOpen_root (h : ThetaOpen Θ) (c : ↥Θ.grp) : ∃ m : ℕ, 0 < m ∧ ((Θ.chr c : Kˣ) : K) ^ m = 1 := by
  classical
  have hP : ∀ P : Q, ∃ m : ℕ, 0 < m ∧ (Θ P).lam ⟨c.1 P, c.2 P (Set.mem_univ P)⟩ ^ m = 1 := by
    intro P
    obtain ⟨N, hN, hg⟩ := h P
    exact tfRoot_of_princ P.1 N hN (Θ P).H (Θ P).lam hg _
  choose m hm0 hm using hP
  have key : (Θ.chr c) ^ (∏ P, m P) = 1 := by
    have hc : Θ.chr c = ∏ P, (Θ P).lam ⟨c.1 P, c.2 P (Set.mem_univ P)⟩ :=
      tfPiChar (fun P => (Θ P).H) (fun P => (Θ P).lam) c
    rw [hc, ← Finset.prod_pow]
    refine Finset.prod_eq_one fun P _ => ?_
    obtain ⟨d, hd⟩ : m P ∣ ∏ Q, m Q := Finset.dvd_prod_of_mem _ (Finset.mem_univ P)
    rw [hd, pow_mul, hm P, one_pow]
  refine ⟨∏ P, m P, Finset.prod_pos fun P _ => hm0 P, ?_⟩
  rw [← Units.val_pow_eq_pow_val, key, Units.val_one]

end Fam

section Tw

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (m2 : ℕ)
  (Λt : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs) (Θt : ∀ j, LevQFam X.E X.K (R.N j) (QE sel (mu : Chr X.F X.E X.K)))

end Tw

end Formalism.L2.Col
