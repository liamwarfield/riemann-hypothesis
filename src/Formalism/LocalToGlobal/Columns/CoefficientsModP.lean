module

public import Formalism.LocalToGlobal.Columns.CoefficientsModP.BaseCh
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.StdDual
public import Formalism.LocalToGlobal.Columns.RecLevelSym

@[expose] public section

section -- merged from Formalism.LocalToGlobal.Columns.CoefficientsModP
section -- merged from Formalism.LocalToGlobal.Columns.CoefficientsModP.NabDual
open MvPolynomial NumberField IsDedekindDomain
open scoped Matrix

noncomputable section

namespace Formalism.L2.DIV

open Formalism.BasicNotions

section

variable {K : Type} [Field K] [NumberField K] [StarRing K] {ι : Type} [Fintype ι] {n : ℕ}

theorem nd_map_star_star {σ : Type} (F : MvPolynomial σ K) :
    MvPolynomial.map (starRingEnd K) (MvPolynomial.map (starRingEnd K) F) = F := by
  rw [MvPolynomial.map_map]
  have e : (starRingEnd K).comp (starRingEnd K) = RingHom.id K := RingHom.ext fun a => star_star a
  rw [e, MvPolynomial.map_id]

theorem nd_mem_dual {lam : ι → DomWeight n} (h : VV K lam →ₗ⋆[K] VV K lam →ₗ[K] K) (L : Submodule (𝓞 K) (VV K lam)) (x : VV K lam) :
    x ∈ Formalism.HermitianLatticesTheory.dual h L ↔ ∀ y ∈ L, h y x ∈ (1 : Submodule (𝓞 K) K) := by
  unfold Formalism.HermitianLatticesTheory.dual Formalism.E.hdual
  simp only [Submodule.mem_iInf, Submodule.mem_comap, LinearMap.coe_restrictScalars]

theorem nd_half (lam : ι → DomWeight n) (T T' : Submodule (𝓞 K) (Pol K ι n))
    (G : ι → GL (Fin n) K) (M : ι → Submodule (𝓞 K) (Fin n → K))
    (hdesc : ∀ F : Pol K ι n, F ∈ transLat lam T M ↔
      MvPolynomial.map (starRingEnd K) F ∈ transLat lam T (fun τ => bcLat (starRingEnd K) (M τ)))
    (hdual : ∀ x : Pol K ι n, x ∈ VV K lam →
      (x ∈ transLat lam T' (fun τ => dualFr (bcLat (starRingEnd K) (M τ))) ↔
        ∀ y ∈ transLat lam T (fun τ => bcLat (starRingEnd K) (M τ)), y ∈ VV K lam →
          pairB lam x y ∈ (1 : Submodule (𝓞 K) K)))
    (x : VV K lam) :
    x ∈ Formalism.HermitianLatticesTheory.dual (pairK lam fun τ => ((G τ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
        ((transLat lam T M).comap ((VV K lam).subtype.restrictScalars (𝓞 K))) ↔
      (x : Pol K ι n) ∈ transLat lam T' (fun τ => hdualFr ((G τ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) (M τ)) := by
  have hsp := (baseChangeSpace_holds K K (starRingEnd K) ι n lam).1
  have e1 : (fun τ => hdualFr ((G τ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) (M τ)) =
      fun τ => gLat (G⁻¹ τ) (dualFr (bcLat (starRingEnd K) (M τ))) := funext fun τ => du_hdualFr_eq (G τ) (M τ)
  rw [nd_mem_dual, e1, transLat_gLat]
  have e2 : (x : Pol K ι n) ∈ (transLat lam T' fun τ => dualFr (bcLat (starRingEnd K) (M τ))).map
      ((actP lam G⁻¹).restrictScalars (𝓞 K)) ↔
      actP lam G (x : Pol K ι n) ∈ transLat lam T' fun τ => dualFr (bcLat (starRingEnd K) (M τ)) := by
    constructor
    · rintro ⟨z, hz, hzx⟩
      rw [← hzx, LinearMap.coe_restrictScalars, ← polyAction_mul, mul_inv_cancel, polyAction_one₂]
      exact hz
    · intro h
      refine ⟨_, h, ?_⟩
      rw [LinearMap.coe_restrictScalars, ← polyAction_mul, inv_mul_cancel, polyAction_one₂]
  rw [e2, hdual _ (polyAction_mem_VV lam G x.2)]
  constructor
  · intro h y hy hyV
    have hy' : MvPolynomial.map (starRingEnd K) y ∈ transLat lam T M := by
      rw [hdesc, nd_map_star_star]; exact hy
    have hyV' : MvPolynomial.map (starRingEnd K) y ∈ VV K lam := (hsp y).1 hyV
    have := h ⟨_, hyV'⟩ hy'
    rw [pairK_apply, pairP_eq_pairB, nd_map_star_star] at this
    rwa [pairingBSymm_holds]
  · intro h y hy
    rw [pairK_apply, pairP_eq_pairB, pairingBSymm_holds]
    exact h _ ((hdesc _).1 hy) ((hsp _).1 y.2)

end

theorem nabDelDual_of (hD : NabDelDescent) (hK : PairBDualK) : NabDelDual := by
  intro K _ _ _ ι _ n lam G M _ hG hM
  have hMc : ∀ τ, Submodule.IsFullLattice K (bcLat (starRingEnd K) (M τ)) := fun τ =>
    bc_bcLat_lattice (j := starRingEnd K) tauLatticeLattice_holds (M τ) (hM τ)
  let GG : ι → GL (Fin n) K := fun τ => Matrix.GeneralLinearGroup.mkOfDetNeZero (G τ) (hG τ).ne_zero
  constructor
  · ext x
    have h := nd_half lam (nabStd K lam) (delStd K lam) GG M
      (fun F => (hD K K (starRingEnd K) ι n lam M hM F).1)
      (fun x hx => by
        have h1 := (hK K ι n lam (fun τ => bcLat (starRingEnd K) (M τ)) hMc ⟨x, hx⟩).1
        simp only [delK, nabK, delP, nabP, Submodule.mem_comap, LinearMap.coe_restrictScalars,
          Submodule.coe_subtype] at h1
        rw [h1]
        constructor
        · intro H y hy hyV
          exact H ⟨y, hyV⟩ hy
        · intro H y hy
          exact H y hy y.2)
      x
    exact h
  · ext x
    have h := nd_half lam (delStd K lam) (nabStd K lam) GG M
      (fun F => (hD K K (starRingEnd K) ι n lam M hM F).2)
      (fun x hx => by
        have h1 := (hK K ι n lam (fun τ => bcLat (starRingEnd K) (M τ)) hMc ⟨x, hx⟩).2
        simp only [delK, nabK, delP, nabP, Submodule.mem_comap, LinearMap.coe_restrictScalars,
          Submodule.coe_subtype] at h1
        rw [h1]
        constructor
        · intro H y hy hyV
          exact H ⟨y, hyV⟩ hy
        · intro H y hy
          exact H y hy y.2)
      x
    exact h

end Formalism.L2.DIV
end
end

namespace Formalism.L2.DIV

theorem fockSTen : FockSTen := fockSymTensor_holds
theorem pairRat : PairRat := pairingRational_holds
theorem actRat : ActRat := actionRational_holds
theorem pairNondeg : PairNondeg := pairingNondegenerate_holds
theorem pairPos : PairPos := pairingPositive_holds
theorem basisAtEx : BasisAtEx := latticeBasisExists_holds
theorem nabDelLoc : NabDelLoc := nablaDeltaLocal_holds
theorem nabDelLattice : NabDelLattice := nablaDeltaLattice_holds
theorem tauLatLattice : TauLatLattice := tauLatticeLattice_holds
theorem dualFrLattice : DualFrLattice := dualFrameLattice_holds
theorem dualFrHdual : DualFrHdual := dualFrameHdual_holds
theorem tauLatDual : TauLatDual := tauLatticeDual_holds
theorem roundLat : RoundLat := roundLattice_holds
theorem weylEqDualNabla : Formalism.GradedWeylDivisibility.WeylEqDualNabla := weyl_eq_dual_nabla_holds
theorem pairBDualStd : PairBDualStd := pairBDualStd_of weyl_eq_dual_nabla_holds
theorem pairBDualK : PairBDualK := pairBDualK_of pairBDualStd
theorem pairBDual : PairBDual := pairBDual_of pairBDualStd
theorem nabDelDual : NabDelDual := nabDelDual_of nablaDeltaDescent_holds pairBDualK

end Formalism.L2.DIV
end

section -- merged from Formalism.LocalToGlobal.Columns.TwQDefs
open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.L2.DIV (Pl kP underPl)

section QDict

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] (ST SG Q : Finset (Pl E))


variable (F) in
abbrev qv (P : Pl E) : HeightOneSpectrum (𝓞 F) := underPl F P

abbrev qGL (g : Sp E n ≃ₗ[E] Sp E n) : GL (Fin n) E := toGLm E n g

instance qdAct {K : Type} [Field K] (H : Subgroup (GLG (E := E) (n := n) (SG := SG))) (Θ : LevQFam E K n Q) :
    MulAction (UF E n × H × Θ.grp) (DecoF E n ST SG Q) :=
  MulAction.compHom _ (MonoidHom.prodMap (MonoidHom.id _) (MonoidHom.prodMap H.subtype Θ.grp.subtype))

structure QLoc {K : Type} [Field K] (Θ : LevQFam E K n Q) where
  sp : ∀ P : Q, E ⊗[F] (qv F P.1).adicCompletion F ≃+* (qv F P.1).adicCompletion F × (qv F P.1).adicCompletion F
  sp_sig : ∀ P x, sp P (Formalism.UG.sigR hc.sig ((qv F P.1).adicCompletion F) x) = Formalism.UG.swapR _ (sp P x)
  sp_alg : ∀ P (a : (qv F P.1).adicCompletion F), sp P ((1 : E) ⊗ₜ[F] a) = (a, a)

  sp_int : ∀ (P : Q) (x : E ⊗[F] (qv F P.1).adicCompletion F), x ∈ Formalism.BasicNotions.intV E (qv F P.1) ↔
    (sp P x).1 ∈ (qv F P.1).adicCompletionIntegers F ∧ (sp P x).2 ∈ (qv F P.1).adicCompletionIntegers F

  sp_P : ∀ (P : Q) (r : 𝓞 E), Valued.v (sp P (Formalism.UG.inclE (F := F) ((qv F P.1).adicCompletion F) (r : E))).1 < 1 ↔ r ∈ P.1.asIdeal

  U : ∀ P : Q, Subgroup (GL (Fin n) ((qv F P.1).adicCompletion F))
  U_int : ∀ P : Q, ∀ k ∈ U P, ∀ i j, ((k : Matrix (Fin n) (Fin n) _) i j) ∈ (qv F P.1).adicCompletionIntegers F

  U_rat : ∀ (P : Q) (g : GLint E n P.1),
    Formalism.UG.bc ((RingHom.fst _ _).comp ((sp P).toRingHom.comp (Formalism.UG.inclE (F := F) ((qv F P.1).adicCompletion F)))) (qGL n g.1) ∈ U P ↔
      g ∈ (Θ P).H

  U_dense : ∀ (P : Q) (k : GL (Fin n) ((qv F P.1).adicCompletion F)),
    (∀ i j, ((k : Matrix (Fin n) (Fin n) _) i j) ∈ (qv F P.1).adicCompletionIntegers F) →
    (∀ i j, (((k⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) i j) ∈ (qv F P.1).adicCompletionIntegers F) →
    ∃ g : GLint E n P.1,
      (Formalism.UG.bc ((RingHom.fst _ _).comp ((sp P).toRingHom.comp (Formalism.UG.inclE (F := F) ((qv F P.1).adicCompletion F)))) (qGL n g.1))⁻¹ * k ∈ U P
  chr : ∀ P : Q, U P →* Kˣ
  chr_rat : ∀ (P : Q) (g : GLint E n P.1) (hg : g ∈ (Θ P).H)
    (h : Formalism.UG.bc ((RingHom.fst _ _).comp ((sp P).toRingHom.comp (Formalism.UG.inclE (F := F) ((qv F P.1).adicCompletion F)))) (qGL n g.1) ∈ U P),
    chr P ⟨_, h⟩ = (Θ P).lam ⟨g, hg⟩

variable {K : Type} [Field K] {Θ : LevQFam E K n Q}


variable {hc n Q} in
abbrev QLoc.phi (q : QLoc hc n Q Θ) (P : Q) : E →+* (qv F P.1).adicCompletion F :=
  (RingHom.fst _ _).comp ((q.sp P).toRingHom.comp (Formalism.UG.inclE (F := F) ((qv F P.1).adicCompletion F)))


variable {hc n Q} in
abbrev QLoc.at (q : QLoc hc n Q Θ) (P : Q) (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : GL (Fin n) ((qv F P.1).adicCompletion F) :=
  Formalism.UG.bc ((RingHom.fst _ _).comp (q.sp P).toRingHom) (Formalism.UG.bc (Formalism.UG.prV (E := E) (qv F P.1)) x)

def levUQ (H : Subgroup (GLG (E := E) (n := n) (SG := SG))) (q : QLoc hc n Q Θ) : Subgroup (GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) :=
  levU hc n ST SG H ⊓ ⨅ P : Q, (q.U P).comap ((Formalism.UG.bc ((RingHom.fst _ _).comp (q.sp P).toRingHom)).comp
    (Formalism.UG.bc (Formalism.UG.prV (E := E) (qv F P.1))))

variable {hc n ST SG Q}

def FrOver (q : QLoc hc n Q Θ) (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (p : DecoF E n ST SG Q) : Prop :=
  decoOf ST SG x = p.deco ∧ ∀ P : Q, (Formalism.UG.bc (q.phi P) (qGL n (p.fr P)))⁻¹ * q.at P x ∈ q.U P

variable (hc n ST SG Q)

abbrev DecoFCl (H : Subgroup (GLG (E := E) (n := n) (SG := SG))) (Θ' : LevQFam E K n Q) : Type :=
  MulAction.orbitRel.Quotient (UF E n × H × Θ'.grp) (DecoF E n ST SG Q)

abbrev RecClsF (H : Subgroup (GLG (E := E) (n := n) (SG := SG))) (q : QLoc hc n Q Θ) (s : DecoFCl (K := K) n ST SG Q H Θ → DecoF E n ST SG Q) : Type :=
  RecCls hc (1 : Matrix (Fin n) (Fin n) E) (baseLb E n ST) (levUQ hc n ST SG Q H q)
    (fun c => MulAction.stabilizer (UF E n × H × Θ.grp) (s c)) (fun c => (s c).deco.1.L)

end QDict

end Formalism.L2.Col
end
end

section -- merged from Formalism.LocalToGlobal.Columns.RecLevelSymF
open NumberField Matrix

noncomputable section

namespace Formalism.L2.Col
section TieFormsSym

variable {κ : Type} [CommRing κ] {k' : Type} [Field k']

theorem blkIdx_replicate_top {t : ℕ} (_ht : 0 < t) (j : ℕ) : blkIdx (List.replicate j t) (j * t) = j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [List.replicate_succ, blkIdx, if_neg (by rw [Nat.succ_mul]; omega), show (j + 1) * t - t = j * t by rw [Nat.succ_mul]; omega, ih]

theorem coarse_rep {r t j x : ℕ} (ht : 0 < t) (hx : x ≤ r + j * t) :
    coarse r (List.replicate j t) x = if x < r then 0 else (x - r) / t + 1 := by
  split_ifs with h
  · exact coarse_of_lt h
  · rw [coarse_of_le (Nat.not_lt.mp h)]
    by_cases h2 : x - r < j * t
    · rw [blkIdx_replicate ht j (x - r) h2]
    · have e : x - r = j * t := by omega
      rw [e, blkIdx_replicate_top ht, Nat.mul_div_cancel _ ht]

theorem posSym_eq_symIdx (k rS x : ℕ) : Formalism.L2.Forms.posSym k rS x = symIdx k rS x := by
  unfold Formalism.L2.Forms.posSym symIdx
  split_ifs <;> omega

theorem mem_HJsym_iff_InJSym (e : κ ≃+* k') {n k rS t j : ℕ} (ht : 0 < t) (hn : n ≤ k + 2 * rS + 1 + j * t + 1)
    (h : k + 2 * rS + 1 ≤ n) (M : GL (Fin n) κ) :
    M ∈ HJsym κ n k (k + 2 * rS + 1) t j rS h ↔
      Formalism.L2.Forms.InJSym k rS t false ((M : Matrix (Fin n) (Fin n) κ).map e) := by
  have hrS : k + rS ≤ k + 2 * rS + 1 := by omega
  have hlv : ∀ x : Fin n, Formalism.L2.Forms.lvSym k rS t x.val =
      if x.val < k + 2 * rS + 1 then symIdx k rS x.val else k + 2 * rS + 1 + (x.val - (k + 2 * rS + 1)) / t := by
    intro x
    unfold Formalism.L2.Forms.lvSym Formalism.L2.Forms.rSym
    rw [posSym_eq_symIdx]
  have hco : ∀ x : Fin n, coarse (k + 2 * rS + 1) (List.replicate j t) x.val =
      if x.val < k + 2 * rS + 1 then 0 else (x.val - (k + 2 * rS + 1)) / t + 1 := fun x => coarse_rep ht (by have := x.2; omega)
  have hsym : ∀ x : ℕ, x < k + 2 * rS + 1 → symIdx k rS x < k + 2 * rS + 1 := fun x hx => symIdx_lt hrS hx
  have z0 : ∀ a : κ, e a = 0 ↔ a = 0 := fun a => EmbeddingLike.map_eq_zero_iff
  have z1 : ∀ a : κ, e a = 1 ↔ a = 1 := fun a => ⟨fun h' => e.injective (by rw [h', map_one]), fun h' => by rw [h', map_one]⟩
  unfold HJsym
  rw [mem_HPar]
  constructor
  · rintro ⟨hB, h0⟩
    rw [mem_HPsymF_iff hrS] at h0
    obtain ⟨h1, h2, h3⟩ := h0
    refine ⟨fun x y hxy => ?_, fun x hx => ?_, fun x y hx hy => ?_, fun h' => absurd h' (by simp)⟩
    · rw [Matrix.map_apply, z0]
      rw [hlv, hlv] at hxy
      by_cases hx : x.val < k + 2 * rS + 1
      · by_cases hy : y.val < k + 2 * rS + 1
        · rw [if_pos hx, if_pos hy] at hxy
          have := h1 ⟨x.val, hx⟩ ⟨y.val, hy⟩ hxy
          rwa [blockZero_val] at this
        · rw [if_pos hx, if_neg hy] at hxy
          have := hsym x.val hx
          generalize (y.val - (k + 2 * rS + 1)) / t = q at hxy
          omega
      · apply hB
        show coarse (k + 2 * rS + 1) (List.replicate j t) y.val < coarse (k + 2 * rS + 1) (List.replicate j t) x.val
        rw [hco, hco, if_neg hx]
        rw [if_neg hx] at hxy
        by_cases hy : y.val < k + 2 * rS + 1
        · rw [if_pos hy]; generalize (x.val - (k + 2 * rS + 1)) / t = qx; omega
        · rw [if_neg hy] at hxy ⊢
          generalize (y.val - (k + 2 * rS + 1)) / t = qy at hxy ⊢
          generalize (x.val - (k + 2 * rS + 1)) / t = qx at hxy ⊢
          omega
    · rw [Matrix.map_apply, z1]
      have := h2 ⟨x.val, hx⟩
      rwa [blockZero_val] at this
    · rw [Matrix.map_apply, z0]
      have := h3 ⟨x.val, by omega⟩ ⟨y.val, by omega⟩ hx hy
      rwa [blockZero_val] at this
  · rintro ⟨h1, h2, h3, _⟩
    have h1' : ∀ x y : Fin n, Formalism.L2.Forms.lvSym k rS t y.val < Formalism.L2.Forms.lvSym k rS t x.val →
        (M : Matrix (Fin n) (Fin n) κ) x y = 0 := fun x y hxy => (z0 _).mp (by rw [← Matrix.map_apply (f := e)]; exact h1 x y hxy)
    have hB : M ∈ blockUT n κ (k + 2 * rS + 1) (List.replicate j t) := by
      intro x y hxy
      apply h1'
      have hxy' : coarse (k + 2 * rS + 1) (List.replicate j t) y.val < coarse (k + 2 * rS + 1) (List.replicate j t) x.val := hxy
      rw [hco, hco] at hxy'
      rw [hlv, hlv]
      generalize hqy : (y.val - (k + 2 * rS + 1)) / t = qy at hxy' ⊢
      generalize hqx : (x.val - (k + 2 * rS + 1)) / t = qx at hxy' ⊢
      by_cases hx : x.val < k + 2 * rS + 1
      · rw [if_pos hx] at hxy'; split_ifs at hxy' <;> omega
      · rw [if_neg hx] at hxy' ⊢
        by_cases hy : y.val < k + 2 * rS + 1
        · rw [if_pos hy]; have := hsym y.val hy; omega
        · rw [if_neg hy] at hxy' ⊢
          omega
    refine ⟨hB, ?_⟩
    rw [mem_HPsymF_iff hrS]
    refine ⟨fun a b hab => ?_, fun a => ?_, fun a b ha hb => ?_⟩
    · rw [blockZero_val]
      apply h1'
      show Formalism.L2.Forms.lvSym k rS t b.val < Formalism.L2.Forms.lvSym k rS t a.val
      unfold Formalism.L2.Forms.lvSym Formalism.L2.Forms.rSym
      rw [if_pos b.2, if_pos a.2, posSym_eq_symIdx, posSym_eq_symIdx]
      exact hab
    · rw [blockZero_val]
      exact (z1 _).mp (by rw [← Matrix.map_apply (f := e)]; exact h2 (Fin.castLE h a) a.2)
    · rw [blockZero_val]
      exact (z0 _).mp (by rw [← Matrix.map_apply (f := e)]; exact h3 (Fin.castLE h a) (Fin.castLE h b) ha hb)

theorem HJsym_eq_JSymG {κ : Type} [Field κ] {n k rS t j : ℕ} (ht : 0 < t) (hn : n ≤ k + 2 * rS + 1 + j * t + 1)
    (h : k + 2 * rS + 1 ≤ n) :
    HJsym κ n k (k + 2 * rS + 1) t j rS h = Formalism.L2.Forms.JSymG (κ := κ) (n := n) k rS t false := by
  ext M
  have e1 := mem_HJsym_iff_InJSym (RingEquiv.refl κ) ht hn h M
  have e2 := mem_HJsym_iff_InJSym (RingEquiv.refl κ) ht hn h M⁻¹
  rw [show ((M : Matrix (Fin n) (Fin n) κ).map (RingEquiv.refl κ)) = M from by ext; rfl] at e1
  rw [show (((M⁻¹ : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ).map (RingEquiv.refl κ)) = ((M⁻¹ : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ) from by ext; rfl] at e2
  constructor
  · intro hM
    exact ⟨e1.mp hM, e2.mp (Subgroup.inv_mem _ hM)⟩
  · rintro ⟨h1, _⟩
    exact e1.mpr h1

end TieFormsSym

section TieLamSym

variable {κ : Type} [CommRing κ] {k' : Type} [Field k'] {K : Type} [Field K]

theorem supSum_map_eq (e : κ ≃+* k') {n a skip : ℕ} (S : Finset ℕ) (hS : ∀ x, x + 1 < a → (x ∈ S ↔ x + 1 ≠ skip))
    (M : Matrix (Fin n) (Fin n) κ) :
    e (supSum a S M) = ∑ x : Fin n, ∑ y : Fin n, if (x : ℕ) + 1 = y ∧ (y : ℕ) < a ∧ (y : ℕ) ≠ skip then (M.map e) x y else 0 := by
  unfold supSum
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  by_cases h : (x : ℕ) + 1 = y ∧ (y : ℕ) < a
  · have h2 : ((x : ℕ) ∈ S ↔ (y : ℕ) ≠ skip) := by rw [← h.1]; exact hS x (by omega)
    by_cases h3 : (x : ℕ) ∈ S
    · rw [if_pos ⟨h.1, h.2, h3⟩, if_pos ⟨h.1, h.2, h2.1 h3⟩]; rfl
    · rw [if_neg (fun h' => h3 h'.2.2), if_neg (fun h' => h3 (h2.2 h'.2.2)), map_zero]
  · rw [if_neg (fun h' => h ⟨h'.1, h'.2.1⟩), if_neg (fun h' => h ⟨h'.1, h'.2.1⟩), map_zero]

theorem lamJsym_eq_lamSym (e : κ ≃+* k') (σ₀ : K →+* ℂ) (ψ : AddChar κ K) (χ : ℕ → κˣ →* Kˣ) {n k rS t j : ℕ} (ht : 0 < t)
    (hn : k + 2 * rS + 1 + j * t ≤ n) (h : k + 2 * rS + 1 ≤ n) (M : ↥(HJsym κ n k (k + 2 * rS + 1) t j rS h)) :
    σ₀ ((lamJsym ψ χ n k (k + 2 * rS + 1) t j rS h M : Kˣ) : K) =
      Formalism.L2.Forms.lamSym (glmPsi e σ₀ ψ) (fun s => glmChi e σ₀ (χ s)) k rS t j ((M.1 : Matrix (Fin n) (Fin n) κ).map e) := by
  unfold lamJsym lamPar Formalism.L2.Forms.lamSym Formalism.L2.Forms.lamJ Formalism.L2.Forms.rSym
  rw [MonoidHom.mul_apply, Units.val_mul, map_mul]
  congr 1
  · rw [MonoidHom.comp_apply, chiSymF_val rfl]
    have e1 : ((HPar0 h (List.replicate j t) (HPsymF κ (k + 2 * rS + 1) k rS) M).1 : Matrix (Fin (k + 2 * rS + 1)) (Fin (k + 2 * rS + 1)) κ) =
        restr h (M.1 : Matrix (Fin n) (Fin n) κ) := rfl
    rw [e1, supSum_restr, ← glmPsi_apply e σ₀ ψ]
    congr 1
    refine supSum_map_eq e _ (fun x hx => ?_) _
    unfold SPsymF
    rw [Finset.mem_filter, Finset.mem_range]
    constructor
    · exact fun h' => h'.2
    · exact fun h' => ⟨by omega, h'⟩
  · rw [MonoidHom.comp_apply, detChar_apply, List.length_replicate, Units.coe_prod, map_prod]
    refine Finset.prod_congr rfl fun s hs => ?_
    have h2 := glm_blkDet e ht (Finset.mem_range.1 hs) hn (Subgroup.inclusion (HPar_le h (List.replicate j t) _) M)
    have h3 : (((Subgroup.inclusion (HPar_le h (List.replicate j t) (HPsymF κ (k + 2 * rS + 1) k rS)) M).1 : GL (Fin n) κ) :
        Matrix (Fin n) (Fin n) κ) = (M.1 : Matrix (Fin n) (Fin n) κ) := rfl
    rw [h3] at h2
    rw [← h2]
    exact (glmChi_apply e σ₀ (χ s) _).symm

end TieLamSym

section MidTie

end MidTie

section MidSteps

open Formalism.BasicNotions (Ranks)

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) {k' : Type} [Field k']

end MidSteps

end Formalism.L2.Col
end
end
