module

public import Formalism.LocalToGlobal.GlobalTheory.ColValOfTiedSOfFin
public import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ExistsPrimeToLe
public import Formalism.LocalToGlobal.GlobalTheory.CoordinateLengths.DuCount
public import Formalism.LocalToGlobal.GlobalTheory.CoordinateLengths.RatStab
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CrossDiagonalMatching.UpMatch
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CrossDiagonalMatching.DnDiaMatch0FHolds
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.IntegralAtT0Lattice

@[expose] public section

section -- merged from Formalism.LocalToGlobal.GlobalTheory.TransposeBaseMatrixInfinity
section -- merged from Formalism.LocalToGlobal.GlobalTheory.NatInvMemIntW
section -- merged from Formalism.LocalToGlobal.GlobalTheory.ColMemOfIsLocBasis
noncomputable section

open NumberField Matrix

namespace Formalism.L2.GlobalTheoryTheory.ColValS

section Dual

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

theorem hform_eq (σ : K →+* K) (J : Matrix (Fin n) (Fin n) K) (x y : Fin n → K) :
    Formalism.UG.hform σ J x y = (fun i => σ (x i)) ⬝ᵥ (J *ᵥ y) := by
  simp only [Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem hform_mulVec (σ : K →+* K) (J M : Matrix (Fin n) (Fin n) K) (v y : Fin n → K) :
    Formalism.UG.hform σ J (M *ᵥ v) y = ∑ a, σ (v a) * ((Formalism.UG.cT σ M * J) *ᵥ y) a := by
  rw [hform_eq]
  have e1 : (fun i => σ ((M *ᵥ v) i)) = M.map σ *ᵥ fun a => σ (v a) := by
    funext i
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply]
  rw [e1, dotProduct_comm, Matrix.dotProduct_mulVec, dotProduct_comm, ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec]
  rfl

variable (l : ℕ) [hl : Fact l.Prime]

theorem col_mem_of_isLocBasis {L : Set (Fin n → K)} {Y : GL (Fin n) K} (hY : Formalism.L2.Forms.IsLocBasis l L Y) (a : Fin n) :
    ∃ t : ℕ, ¬ l ∣ t ∧ (t : K) • (fun r => (Y : Matrix (Fin n) (Fin n) K) r a) ∈ L := by
  refine (hY _).2 ⟨1, hl.out.not_dvd_one, fun b => ?_⟩
  have e : (((Y⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ fun r => (Y : Matrix (Fin n) (Fin n) K) r a) b =
      (((Y⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (Y : Matrix (Fin n) (Fin n) K)) b a := rfl
  rw [Nat.cast_one, one_mul, e, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_apply]
  split_ifs
  · exact ⟨1, map_one _⟩
  · exact ⟨0, map_zero _⟩

theorem den_of_isLocBasis {L : Submodule (𝓞 K) (Fin n → K)} (hfg : L.FG) {Y : GL (Fin n) K}
    (hY : Formalism.L2.Forms.IsLocBasis l (L : Set (Fin n → K)) Y) :
    ∃ d : ℕ, ¬ l ∣ d ∧ ∀ x ∈ L, ∀ a, (d : K) * ((((Y⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x) a) ∈
      (algebraMap (𝓞 K) K).range := by
  classical
  obtain ⟨S, hS⟩ := hfg
  have ht : ∀ g ∈ S, ∃ t : ℕ, ¬ l ∣ t ∧ ∀ a, (t : K) * ((((Y⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ g) a) ∈
      (algebraMap (𝓞 K) K).range := fun g hg =>
    (hY g).1 ⟨1, hl.out.not_dvd_one, by
      rw [Nat.cast_one, one_smul, SetLike.mem_coe, ← hS]; exact Submodule.subset_span hg⟩
  let t : (Fin n → K) → ℕ := fun g => if h : g ∈ S then (ht g h).choose else 1
  have htS : ∀ g ∈ S, ¬ l ∣ t g ∧ ∀ a, (t g : K) * ((((Y⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ g) a) ∈
      (algebraMap (𝓞 K) K).range := fun g hg => by
    simp only [t, dif_pos hg]; exact (ht g hg).choose_spec
  refine ⟨∏ g ∈ S, t g, ?_, fun x hx => ?_⟩
  · rw [Prime.dvd_finsetProd_iff hl.out.prime]
    rintro ⟨g, hg, hdvd⟩
    exact (htS g hg).1 hdvd
  · rw [← hS] at hx
    induction hx using Submodule.span_induction with
    | mem g hg =>
      intro a
      rw [← Finset.mul_prod_erase S t hg, Nat.cast_mul, mul_comm ((t g : ℕ) : K), mul_assoc]
      exact Subring.mul_mem _ ⟨(∏ g' ∈ S.erase g, t g' : ℕ), map_natCast _ _⟩ ((htS g hg).2 a)
    | zero =>
      intro a
      rw [Matrix.mulVec_zero, Pi.zero_apply, mul_zero]
      exact Subring.zero_mem _
    | add x y _ _ hx hy =>
      intro a
      rw [Matrix.mulVec_add, Pi.add_apply, mul_add]
      exact Subring.add_mem _ (hx a) (hy a)
    | smul r x _ hx =>
      intro a
      rw [← algebraMap_smul K r x, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, mul_left_comm]
      exact Subring.mul_mem _ ⟨r, rfl⟩ (hx a)

theorem sig_range (σ : K →+* K) {y : K} (hy : y ∈ (algebraMap (𝓞 K) K).range) : σ y ∈ (algebraMap (𝓞 K) K).range := by
  obtain ⟨r, rfl⟩ := hy
  obtain ⟨r', hr'⟩ := Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.LocB.sig_int σ r
  exact ⟨r', hr'⟩

theorem isLocBasis_dual (σ : K →+* K) (J : Matrix (Fin n) (Fin n) K) {L : Submodule (𝓞 K) (Fin n → K)} (hfg : L.FG)
    {Y : GL (Fin n) K} (hY : Formalism.L2.Forms.IsLocBasis l (L : Set (Fin n → K)) Y) (B0 : GL (Fin n) K)
    (hB0 : ((B0⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = Formalism.UG.cT σ (Y : Matrix (Fin n) (Fin n) K) * J) :
    Formalism.L2.Forms.IsLocBasis l (Formalism.BasicNotions.dualSet σ J L) B0 := by
  intro x
  rw [hB0]
  constructor
  · rintro ⟨s, hs, hx⟩
    choose t ht htL using col_mem_of_isLocBasis l hY
    refine ⟨s * ∏ b, t b, ?_, fun a => ?_⟩
    · rw [Nat.Prime.dvd_mul hl.out, not_or]
      refine ⟨hs, ?_⟩
      rw [Prime.dvd_finsetProd_iff hl.out.prime]
      rintro ⟨b, -, hb⟩
      exact ht b hb
    · have h1 := hx _ (htL a)
      have e1 : (t a : K) • (fun r => (Y : Matrix (Fin n) (Fin n) K) r a) =
          (Y : Matrix (Fin n) (Fin n) K) *ᵥ ((t a : K) • Pi.single a (1 : K)) := by
        rw [Matrix.mulVec_smul, Matrix.mulVec_single_one]
        rfl
      rw [e1, hform_mulVec, Finset.sum_eq_single a (fun b _ hb => by simp [hb])
        (fun h => absurd (Finset.mem_univ a) h)] at h1
      simp only [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one, map_natCast, Matrix.mulVec_smul] at h1
      rw [← Finset.mul_prod_erase Finset.univ t (Finset.mem_univ a)]
      have e2 : ((s * (t a * ∏ b ∈ Finset.univ.erase a, t b) : ℕ) : K) *
          ((Formalism.UG.cT σ (Y : Matrix (Fin n) (Fin n) K) * J) *ᵥ x) a =
          ((∏ b ∈ Finset.univ.erase a, t b : ℕ) : K) *
            ((t a : K) * ((s : K) * ((Formalism.UG.cT σ (Y : Matrix (Fin n) (Fin n) K) * J) *ᵥ x) a)) := by
        push_cast; ring
      rw [e2]
      exact Subring.mul_mem _ ⟨_, map_natCast _ _⟩ h1
  · rintro ⟨s', hs', h'⟩
    obtain ⟨d, hd, hdL⟩ := den_of_isLocBasis l hfg hY
    refine ⟨d * s', ?_, ?_⟩
    · rw [Nat.Prime.dvd_mul hl.out, not_or]; exact ⟨hd, hs'⟩
    · intro z hz
      have hz' : z = (Y : Matrix (Fin n) (Fin n) K) *ᵥ ((((Y⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) *ᵥ z) := by
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
      rw [hz', hform_mulVec]
      refine Subring.sum_mem _ fun b _ => ?_
      rw [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
      have e : σ (((((Y⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) *ᵥ z) b) *
          (((d * s' : ℕ) : K) * ((Formalism.UG.cT σ (Y : Matrix (Fin n) (Fin n) K) * J) *ᵥ x) b) =
          σ ((d : K) * ((((Y⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) *ᵥ z) b) *
            ((s' : K) * ((Formalism.UG.cT σ (Y : Matrix (Fin n) (Fin n) K) * J) *ᵥ x) b) := by
        rw [map_mul, map_natCast]; push_cast; ring
      rw [e]
      exact Subring.mul_mem _ (sig_range σ (hdL z hz b)) (h' b)

end Dual

section Ten

variable {ι : Type} [Fintype ι] {n : ℕ}

theorem ten_map {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (f : ι → MvPolynomial (Fin n × Fin n) R) :
    Formalism.MainNotions.flipTwoThree.ten (fun τ => MvPolynomial.map φ (f τ)) = MvPolynomial.map φ (Formalism.MainNotions.flipTwoThree.ten f) := by
  unfold Formalism.MainNotions.flipTwoThree.ten
  rw [map_prod]
  exact Finset.prod_congr rfl fun τ _ => (MvPolynomial.map_rename _ _ _).symm

end Ten

variable (D : Formalism.BasicNotions.D7)

theorem map_gen {n : ℕ} (r : D.what₂.LL) (f : D.what₂.Tau → MvPolynomial (Fin n × Fin n) ℤ) :
    MvPolynomial.map D.what₂.embLL (r • Formalism.MainNotions.flipTwoThree.ten (fun τ => MvPolynomial.map (Int.castRingHom D.what₂.LL) (f τ))) =
      D.what₂.embLL r • Formalism.MainNotions.flipTwoThree.ten (fun τ => MvPolynomial.map (Int.castRingHom ℂ) (f τ)) := by
  rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, ← MvPolynomial.smul_eq_C_mul, ten_map, ten_map,
    MvPolynomial.map_map, RingHom.ext_int (D.what₂.embLL.comp (Int.castRingHom D.what₂.LL)) (Int.castRingHom ℂ)]

theorem mem_intSpanAt_iff_map (w : D.what₂.places.Pl) {n : ℕ} (lam : D.what₂.Tau → Formalism.BasicNotions.DomWeight n)
    (p : MvPolynomial (D.what₂.Tau × Fin n × Fin n) D.what₂.LL) :
    p ∈ Formalism.MainNotions.flipTwoThree.IntSpanAt D w lam ↔ MvPolynomial.map D.what₂.embLL p ∈ Formalism.L2.Forms.IntSpan D w lam := by
  constructor
  · intro hp
    induction hp using AddSubgroup.closure_induction with
    | mem q hq =>
      obtain ⟨r, f, hr, hf, rfl⟩ := hq
      exact AddSubgroup.subset_closure ⟨r, f, hr, hf, map_gen D r f⟩
    | zero => rw [map_zero]; exact AddSubgroup.zero_mem _
    | add q q' _ _ h1 h2 => rw [map_add (f := _)]; exact AddSubgroup.add_mem _ h1 h2
    | neg q _ h1 => rw [map_neg]; exact AddSubgroup.neg_mem _ h1
  · intro hp
    have hle : Formalism.L2.Forms.IntSpan D w lam ≤
        (Formalism.MainNotions.flipTwoThree.IntSpanAt D w lam).map (MvPolynomial.map D.what₂.embLL).toAddMonoidHom := by
      unfold Formalism.L2.Forms.IntSpan
      rw [AddSubgroup.closure_le]
      rintro _ ⟨r, f, hr, hf, rfl⟩
      exact ⟨_, AddSubgroup.subset_closure ⟨r, f, hr, hf, rfl⟩, map_gen D r f⟩
    obtain ⟨q, hq, hqe⟩ := hle hp
    have : q = p := MvPolynomial.map_injective _ D.what₂.embLL.injective hqe
    rwa [← this]

theorem embT_mem_Ow (w : D.what₂.places.Pl) (τ : D.what₂.Tau) (y : D.host.E) (s : ℕ)
    (hs : ¬ D.what₂.places.resChar w ∣ s) (hy : (s : D.host.E) * y ∈ (algebraMap (𝓞 D.host.E) D.host.E).range) :
    Formalism.L2.Forms.embT D τ y ∈ Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwA_Ow D w := by
  rw [Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwA_embT_eq]
  exact Subring.mem_map.2 ⟨_, Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwA_val_locInt D w
    ((D.host.sigmaOf (D.eTau τ : D.R.GG) : D.host.E →+* D.host.E)) y s hs hy, rfl⟩

theorem change_mem (w : D.what₂.places.Pl) (τ : D.what₂.Tau) {n : ℕ} {L : Set (Fin n → D.host.E)}
    {B B₂ : GL (Fin n) D.host.E} (hB : Formalism.L2.Forms.IsLocBasis (D.what₂.places.resChar w) L B)
    (hB₂ : Formalism.L2.Forms.IsLocBasis (D.what₂.places.resChar w) L B₂) (a b : Fin n) :
    Formalism.L2.Forms.atInf (Formalism.L2.Forms.embT D) ((B₂⁻¹ * B : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) τ a b ∈
      Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwA_Ow D w := by
  have : Fact (D.what₂.places.resChar w).Prime := ⟨D.what₂.places.resChar_prime w⟩
  obtain ⟨s, hs, hx⟩ := col_mem_of_isLocBasis (D.what₂.places.resChar w) hB b
  obtain ⟨s', hs', h⟩ := (hB₂ _).1 ⟨s, hs, hx⟩
  have e : (((B₂⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) *ᵥ
      fun r => (B : Matrix (Fin n) (Fin n) D.host.E) r b) a =
      ((B₂⁻¹ * B : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) a b := by
    rw [Units.val_mul]; rfl
  have h2 := embT_mem_Ow D w τ _ s' hs' (h a)
  rw [e] at h2
  exact h2

theorem basis_change (w : D.what₂.places.Pl) {n : ℕ} (lam : D.what₂.Tau → Formalism.BasicNotions.DomWeight n)
    (G : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) (s : D.what₂.Tau → ℤ) {L : Set (Fin n → D.host.E)}
    {B B₂ : GL (Fin n) D.host.E} (hB : Formalism.L2.Forms.IsLocBasis (D.what₂.places.resChar w) L B)
    (hB₂ : Formalism.L2.Forms.IsLocBasis (D.what₂.places.resChar w) L B₂)
    (Q : MvPolynomial (D.what₂.Tau × Fin n × Fin n) ℂ) (hQ : Q ∈ Formalism.L2.Forms.IntSpan D w lam) :
    ∃ Q₂ ∈ Formalism.L2.Forms.IntSpan D w lam,
      Formalism.L2.Forms.fnOf G s (Formalism.L2.Forms.atInf (Formalism.L2.Forms.embT D) ((B⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E)) Q =
        Formalism.L2.Forms.fnOf G s (Formalism.L2.Forms.atInf (Formalism.L2.Forms.embT D) ((B₂⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E)) Q₂ := by
  set N : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ :=
    fun τ => Formalism.L2.Forms.atInf (Formalism.L2.Forms.embT D) ((B⁻¹ * B₂ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) τ with hN
  set N' : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ :=
    fun τ => Formalism.L2.Forms.atInf (Formalism.L2.Forms.embT D) ((B₂⁻¹ * B : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) τ with hN'
  have hNN' : ∀ τ, N τ * N' τ = 1 := fun τ => by
    simp only [hN, hN', Formalism.L2.Forms.atInf]
    rw [← Matrix.map_mul, ← Units.val_mul]
    have : (B⁻¹ * B₂ * (B₂⁻¹ * B) : GL (Fin n) D.host.E) = 1 := by group
    rw [this, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]
  refine ⟨MvPolynomial.C (∏ τ, (N τ).det ^ s τ) * Formalism.L2.Forms.subP N Q,
    Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwG_intSpan_allSubP D w _ N _ (fun τ g hg => Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.local_GL_stabilises_lattice D w _ _ _ (N τ) (N' τ) (hNN' τ)
      (change_mem D w τ hB₂ hB) (change_mem D w τ hB hB₂) g hg) Q hQ, ?_⟩
  rw [← Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.fnOf_mul]
  have hM : Formalism.L2.Forms.atInf (Formalism.L2.Forms.embT D) ((B⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) =
      fun τ => N τ * Formalism.L2.Forms.atInf (Formalism.L2.Forms.embT D) ((B₂⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) τ := by
    funext τ
    simp only [hN, Formalism.L2.Forms.atInf]
    rw [← Matrix.map_mul, ← Units.val_mul]
    congr 2
    group
  rw [hM]

end Formalism.L2.GlobalTheoryTheory.ColValS
end
end

noncomputable section

open Matrix NumberField

namespace Formalism.L2.GlobalTheoryTheory.ColValS

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.Inhab

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def eqv (D : D7) : (D.sp.X 0).V ≃ₗ[D.host.E] (Fin (D.R.N 0) → D.host.E) :=
  (D.sp.X 0).frame.equivFun.trans
    (LinearEquiv.funCongrLeft D.host.E D.host.E (finCongr (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _))).symm)

theorem mem_clsCrd_iff {u : D.what₂.Word} (c : (D.mem u).C.cls 0) (z : Fin (D.R.N 0) → D.host.E) :
    z ∈ Formalism.L2.Forms.clsCrd D u 0 (Nat.zero_le _) c ↔ (eqv D).symm z ∈ D.clsLat u 0 c := by
  unfold Formalism.L2.Forms.clsCrd
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    convert hy using 1
    exact (eqv D).symm_apply_apply y
  · intro h
    exact ⟨_, h, (eqv D).apply_symm_apply z⟩

def vcol (Y : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (a : Fin (D.R.N 0)) : (D.sp.X 0).V :=
  (eqv D).symm fun r => Y r a

variable {u : D.what₂.Word} (B : ColBase D u)

theorem sum_gamma (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau) (Y : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E)
    (a : Fin (D.R.N 0)) :
    ∑ i, (Mb B c τ * Y.map (B.rho τ)) i a • (B.Q c τ).b ((B.eQ c τ).symm i) = B.bc c τ (vcol Y a) := by
  have hfr : ∀ r : Fin (D.R.N 0), (eqv D).symm (Pi.single r 1) =
      (D.sp.X 0).frame ((finCongr (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _))).symm r) := by
    intro r
    rw [LinearEquiv.symm_apply_eq]
    ext r'
    simp [eqv, Pi.single_apply]
    rw [Finsupp.single_apply]
    split_ifs <;> simp_all [Fin.cast_inj]
  have hz : (fun r => Y r a) = ∑ r, Y r a • (Pi.single r (1 : D.host.E) : Fin (D.R.N 0) → D.host.E) := by
    ext r'
    simp [Finset.sum_apply, Pi.single_apply]
  have hbc : B.bc c τ (vcol Y a) = ∑ r, B.rho τ (Y r a) •
      B.bc c τ ((D.sp.X 0).frame ((finCongr (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _))).symm r)) := by
    unfold vcol
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hz, map_sum, map_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [map_smul, B.bc_smul, hfr]
  have hexp : ∀ v : (B.Q c τ).V,
      v = ∑ i, (B.Q c τ).b.repr v ((B.eQ c τ).symm i) • (B.Q c τ).b ((B.eQ c τ).symm i) := by
    intro v
    rw [Equiv.sum_comp (B.eQ c τ).symm (fun j => (B.Q c τ).b.repr v j • (B.Q c τ).b j)]
    exact ((B.Q c τ).b.sum_repr v).symm
  rw [hbc]
  simp only [Matrix.mul_apply, Matrix.map_apply, Mb, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => ?_
  conv_rhs => rw [hexp (B.bc c τ ((D.sp.X 0).frame ((finCongr (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _))).symm r)))]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_smul, mul_comm]

theorem rhoC_mem_intW (w : D.what₂.places.Pl) (τ : D.what₂.Tau) (y : D.host.E) (s : ℕ)
    (hs : ¬ D.what₂.places.resChar w ∣ s) (hy : (s : D.host.E) * y ∈ (algebraMap (𝓞 D.host.E) D.host.E).range) :
    rhoC D τ y ∈ intW D.what₂.places w := by
  obtain ⟨k, hk⟩ := hy
  have hint : IsIntegral ℤ (rhoC D τ (k : D.host.E)) :=
    (RingOfIntegers.isIntegral_coe k).map (rhoC D τ).toIntAlgHom
  have hk' : (s : D.what₂.LL) * rhoC D τ y ∈ intW D.what₂.places w := by
    have h1 : rhoC D τ ((s : D.host.E) * y) = (s : D.what₂.LL) * rhoC D τ y := by
      rw [map_mul, map_natCast]
    rw [← h1, ← hk]
    exact Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwG_int_mem D w ⟨_, hint⟩
  have hinv : ((s : D.what₂.LL))⁻¹ ∈ intW D.what₂.places w := by
    change (0 : WithTop ℤ) ≤ D.what₂.places.val w ((s : D.what₂.LL))⁻¹
    have h0 : D.what₂.places.val w ((s : D.what₂.LL)) = 0 :=
      Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwA_val_nat_eq_zero (s := s) (hs := hs)
    rw [AddValuation.map_inv, h0, neg_zero]
  have hs0 : (s : D.what₂.LL) ≠ 0 := by
    intro h
    apply hs
    have h2 : s = 0 := by exact_mod_cast h
    rw [h2]
    exact dvd_zero _
  have h3 := (intW D.what₂.places w).mul_mem hinv hk'
  rwa [← mul_assoc, inv_mul_cancel₀ hs0, one_mul] at h3

theorem natInv_mem_intW (w : D.what₂.places.Pl) (t : ℕ) (ht : ¬ D.what₂.places.resChar w ∣ t) :
    ((t : D.what₂.LL))⁻¹ ∈ intW D.what₂.places w := by
  change (0 : WithTop ℤ) ≤ D.what₂.places.val w ((t : D.what₂.LL))⁻¹
  have h0 : D.what₂.places.val w ((t : D.what₂.LL)) = 0 :=
    Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwA_val_nat_eq_zero (s := t) (hs := ht)
  rw [AddValuation.map_inv, h0, neg_zero]

theorem locBasis_gamma (hB : B.rho = rhoC D) (w : D.what₂.places.Pl) (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau)
    (Y : GL (Fin (D.R.N 0)) D.host.E)
    (hY : Formalism.L2.Forms.IsLocBasis (D.what₂.places.resChar w)
      (Formalism.L2.Forms.clsCrd D u 0 (Nat.zero_le _) c : Set (Fin (D.R.N 0) → D.host.E)) Y) :
    Formalism.MainNotions.flipTwoThree.LocBasis D w (B.Q c τ) (B.eQ c τ)
      (Mb B c τ * (Y : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E).map (B.rho τ)) := by
  have hp1 : ¬ D.what₂.places.resChar w ∣ 1 := (D.what₂.places.resChar_prime w).not_dvd_one
  have hg : ∀ a, ∑ i, (Mb B c τ * (Y : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E).map (B.rho τ)) i a •
      (B.Q c τ).b ((B.eQ c τ).symm i) = B.bc c τ (vcol (Y : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) a) :=
    fun a => sum_gamma B c τ _ a
  have hsmul : ∀ (r : D.what₂.LL) (hr : r ∈ intW D.what₂.places w) (v : (B.Q c τ).V),
      r • v = (⟨r, hr⟩ : intW D.what₂.places w) • v := fun r hr v => by rw [Subring.smul_def]
  have hcolv : ∀ v : Fin (D.R.N 0) → D.host.E, (Y : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ v =
      ∑ a, v a • (fun r => (Y : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) r a) := by
    intro v
    ext r
    simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  refine ⟨?_, ?_⟩
  · rw [Matrix.det_mul]
    refine IsUnit.mul (isUnit_iff_ne_zero.2 (Mb_det_ne B c τ)) ?_
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact ((Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit Y)).map _
  · simp only [hg]
    apply le_antisymm
    · unfold locW
      rw [Submodule.span_le]
      intro x hx
      rw [SetLike.mem_coe, B.bc_L c τ] at hx
      refine Submodule.span_induction (p := fun x _ => x ∈ Submodule.span (intW D.what₂.places w)
        (Set.range fun a => B.bc c τ (vcol (Y : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) a))) ?_ ?_ ?_ ?_ hx
      · rintro _ ⟨y, hy, rfl⟩
        have hz : eqv D y ∈ Formalism.L2.Forms.clsCrd D u 0 (Nat.zero_le _) c := by
          rw [mem_clsCrd_iff, LinearEquiv.symm_apply_apply]
          exact hy
        obtain ⟨s, hs, hint⟩ := (hY (eqv D y)).1 ⟨1, hp1, by rw [Nat.cast_one, one_smul]; exact hz⟩
        have h1 : (Y : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ
            ((((Y⁻¹ : GL (Fin (D.R.N 0)) D.host.E)) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ eqv D y) =
            eqv D y := by
          rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
        have hyz : y = ∑ a, ((((Y⁻¹ : GL (Fin (D.R.N 0)) D.host.E)) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ
            eqv D y) a • vcol (Y : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) a := by
          set_option synthInstance.maxHeartbeats 100000 in
            conv_lhs => rw [← (eqv D).symm_apply_apply y, ← h1, hcolv, map_sum]
          simp only [LinearEquiv.map_smul]
          rfl
        set_option synthInstance.maxHeartbeats 100000 in
          rw [hyz, map_sum]
        refine Submodule.sum_mem _ fun a _ => ?_
        rw [B.bc_smul, hB, hsmul _ (rhoC_mem_intW w τ _ s hs (hint a))]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
      · exact zero_mem _
      · intro x y _ _ hx hy
        exact add_mem hx hy
      · intro r x _ hx
        have hr : r • x = (⟨_, Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwG_int_mem D w r⟩ : intW D.what₂.places w) • x := by
          rw [Subring.smul_def]
          exact (algebraMap_smul D.what₂.LL r x).symm
        rw [hr]
        exact Submodule.smul_mem _ _ hx
    · unfold locW
      rw [Submodule.span_le]
      rintro _ ⟨a, rfl⟩
      have hcol : (fun r => (Y : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) r a) =
          (Y : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ Pi.single a 1 := by
        ext r
        simp [Matrix.mulVec, dotProduct, Pi.single_apply]
      obtain ⟨s, hs, hsm⟩ := (hY (fun r => (Y : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) r a)).2 ⟨1, hp1, fun b => by
        rw [hcol, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec, Nat.cast_one, one_mul]
        by_cases hb : b = a
        · subst hb
          exact ⟨1, by simp⟩
        · exact ⟨0, by simp [Pi.single_apply, hb]⟩⟩
      rw [SetLike.mem_coe, mem_clsCrd_iff, LinearEquiv.map_smul] at hsm
      have hQ : B.bc c τ ((s : D.host.E) • vcol (Y : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) a) ∈
          (B.Q c τ).L := by
        rw [B.bc_L c τ]
        exact Submodule.subset_span ⟨_, hsm, rfl⟩
      rw [B.bc_smul, map_natCast] at hQ
      have hs0 : (s : D.what₂.LL) ≠ 0 := by
        intro h
        apply hs
        have h2 : s = 0 := by exact_mod_cast h
        rw [h2]
        exact dvd_zero _
      have h4 : B.bc c τ (vcol (Y : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) a) =
          (⟨_, natInv_mem_intW w s hs⟩ : intW D.what₂.places w) •
            ((s : D.what₂.LL) • B.bc c τ (vcol (Y : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) a)) := by
        rw [Subring.smul_def, smul_smul, inv_mul_cancel₀ hs0, one_smul]
      rw [SetLike.mem_coe]
      beta_reduce
      rw [h4]
      exact Submodule.smul_mem _ _ (Submodule.subset_span hQ)

end Formalism.L2.GlobalTheoryTheory.ColValS
end
end

noncomputable section

open Matrix NumberField

namespace Formalism.L2.GlobalTheoryTheory.ColValS

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.Inhab

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem embT_sigD (τ : D.what₂.Tau) (a : D.host.E) :
    Formalism.L2.Forms.embT D τ (Formalism.L2.Forms.sigD D a) = starRingEnd ℂ (Formalism.L2.Forms.embT D τ a) := by
  haveI := D.host.isCMField_hostE
  show D.host.emb (D.eTau τ : D.R.GG) (Formalism.L2.Forms.sigD D a) = starRingEnd ℂ (D.host.emb (D.eTau τ : D.R.GG) a)
  exact NumberField.IsCMField.complexEmbedding_complexConj D.host.E _ a

theorem embLL_rhoC (τ : D.what₂.Tau) (a : D.host.E) :
    D.what₂.embLL (rhoC D τ a) = starRingEnd ℂ (Formalism.L2.Forms.embT D τ a) := by
  rw [rhoC_conj D.what₂.embLL τ a]
  congr 1
  exact (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwA_embT_eq D τ a).symm

theorem gramN_sig (i j : Fin (D.R.N 0)) :
    Formalism.L2.Forms.gramN D 0 (Nat.zero_le _) i j = Formalism.L2.Forms.sigD D (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _) j i) := by
  letI := D.host.cmStar
  simp only [Formalism.L2.Forms.gramN, Matrix.reindex_apply, Matrix.submatrix_apply, Formalism.BasicNotions.HSpace.gram]
  first
  | exact ((D.sp.X 0).herm _ _).symm
  | exact ((D.sp.X 0).herm.eq _ _).symm

def BaseBlockInverse (Y : GL (Fin (D.R.N 0)) D.host.E) : GL (Fin (D.R.N 0)) D.host.E :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero
    (Formalism.UG.cT (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) (Y : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *
      Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (by
    rw [Matrix.det_mul, Formalism.UG.cT, Matrix.det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact mul_ne_zero ((map_ne_zero _).2 (Matrix.isUnits_det_units Y).ne_zero) gramN_det_ne)

theorem B0inv_coe (Y : GL (Fin (D.R.N 0)) D.host.E) :
    ((BaseBlockInverse Y : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) =
      Formalism.UG.cT (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) (Y : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *
        Formalism.L2.Forms.gramN D 0 (Nat.zero_le _) := rfl

theorem transpose_base_matrix_infinity (Y : GL (Fin (D.R.N 0)) D.host.E) (τ : D.what₂.Tau) :
    (((Formalism.L2.Forms.gramN D 0 (Nat.zero_le _) * (Y : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E)).map (rhoC D τ)).map
      D.what₂.embLL)ᵀ =
      Formalism.L2.Forms.atInf (Formalism.L2.Forms.embT D) ((BaseBlockInverse Y : GL (Fin (D.R.N 0)) D.host.E) :
        Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) τ := by
  rw [B0inv_coe]
  ext i j
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.transpose_apply, Matrix.map_apply, Formalism.L2.Forms.atInf, Formalism.UG.cT, Matrix.mul_apply, map_sum, map_mul,
    AlgHom.coe_toRingHom]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [embLL_rhoC, embLL_rhoC, gramN_sig j k, embT_sigD, embT_sigD, starRingEnd_self_apply, mul_comm]

variable {u : D.what₂.Word} (B : ColBase D u)

theorem h_T_mul (hB : B.rho = rhoC D) (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau) (Y : GL (Fin (D.R.N 0)) D.host.E) :
    (((Mb B c τ * (Y : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E).map (B.rho τ))⁻¹ *
        ((gC B c τ : GL (Fin (D.R.N 0)) D.what₂.LL) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL)).map D.what₂.embLL)ᵀ *
      Formalism.L2.Forms.atInf (Formalism.L2.Forms.embT D) ((BaseBlockInverse Y : GL (Fin (D.R.N 0)) D.host.E) :
        Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) τ = 1 := by
  have hMb : IsUnit (Mb B c τ).det := isUnit_iff_ne_zero.mpr (Mb_det_ne B c τ)
  have hGY : ((Formalism.L2.Forms.gramN D 0 (Nat.zero_le _) *
      (Y : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E)).map (rhoC D τ)).det ≠ 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, Matrix.det_mul]
    exact (map_ne_zero _).2 (mul_ne_zero gramN_det_ne (Matrix.isUnits_det_units Y).ne_zero)
  have hA : (Mb B c τ * (Y : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E).map (rhoC D τ))⁻¹ *
      (Mb B c τ * ((Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)).map (rhoC D τ))⁻¹) =
      ((Formalism.L2.Forms.gramN D 0 (Nat.zero_le _) *
        (Y : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E)).map (rhoC D τ))⁻¹ := by
    rw [Matrix.map_mul, Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.mul_assoc,
      ← Matrix.mul_assoc (Mb B c τ)⁻¹, Matrix.nonsing_inv_mul _ hMb, Matrix.one_mul]
  rw [gC_coe, hB, hA, ← transpose_base_matrix_infinity Y τ, ← Matrix.transpose_mul, ← Matrix.map_mul,
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hGY)]
  simp

theorem isUnit_base_inverse_infinity (Y : GL (Fin (D.R.N 0)) D.host.E) (τ : D.what₂.Tau) :
    IsUnit (Formalism.L2.Forms.atInf (Formalism.L2.Forms.embT D) ((BaseBlockInverse Y : GL (Fin (D.R.N 0)) D.host.E) :
      Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) τ).det := by
  unfold Formalism.L2.Forms.atInf
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact (Matrix.isUnits_det_units (BaseBlockInverse Y)).map _

theorem clause_iff (T0 : Formalism.L2.Forms.Forms0 D u) (hB : B.rho = rhoC D) (w : D.what₂.places.Pl) (c : (D.mem u).C.cls 0)
    (Y : GL (Fin (D.R.N 0)) D.host.E)
    (hY : Formalism.L2.Forms.IsLocBasis (D.what₂.places.resChar w)
      (Formalism.L2.Forms.clsCrd D u 0 (Nat.zero_le _) c : Set (Fin (D.R.N 0) → D.host.E)) Y)
    (x : ((D.fm u).lat 0).V) :
    (∀ Bb : GL (Fin (D.R.N 0)) D.host.E,
      Formalism.L2.Forms.IsLocBasis (D.what₂.places.resChar w)
        (dualSet (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _))
          (Formalism.L2.Forms.clsCrd D u 0 (Nat.zero_le _) c)) Bb →
      ∃ P ∈ Formalism.L2.Forms.IntSpan D w ((D.fm u).lam 0),
        ∀ z, (D.fm u).emb 0 x c z =
          Formalism.L2.Forms.fnOf _ (Formalism.L2.Forms.shiftOf (Formalism.L2.Forms.lamT u 0))
            (Formalism.L2.Forms.atInf (Formalism.L2.Forms.embT D) (Bb⁻¹ : GL (Fin (D.R.N 0)) D.host.E).1) P (T0.val0.eY z)) ↔
    Formalism.MainNotions.flipTwoThree.actAll ((D.fm u).lam 0)
      (fun τ => (Mb B c τ * (Y : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E).map (B.rho τ))⁻¹)
      (coT T0 (gC B) x c) ∈ Formalism.MainNotions.flipTwoThree.IntSpanAt D w ((D.fm u).lam 0) := by
  have : Fact (D.what₂.places.resChar w).Prime := ⟨D.what₂.places.resChar_prime w⟩
  set p := co0 T0 x c with hp
  set lam := (D.fm u).lam 0 with hlam
  set Gf := Formalism.L2.Forms.gramC (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Formalism.L2.Forms.embT D) with hGf
  set s0 := Formalism.L2.Forms.shiftOf (Formalism.L2.Forms.lamT u 0) with hs0
  set hh : D.what₂.Tau → Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) ℂ := fun τ =>
    ((Mb B c τ * (Y : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E).map (B.rho τ))⁻¹ *
      ((gC B c τ : GL (Fin (D.R.N 0)) D.what₂.LL) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL)).map D.what₂.embLL with hhh
  set N0 : D.what₂.Tau → Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) ℂ :=
    Formalism.L2.Forms.atInf (Formalism.L2.Forms.embT D) ((BaseBlockInverse Y : GL (Fin (D.R.N 0)) D.host.E) :
      Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) with hN0
  have hK : (fun τ => (hh τ)ᵀ * N0 τ) = 1 := funext fun τ => h_T_mul B hB c τ Y
  have hs : ∀ τ, s0 τ = (lam τ).detShift := fun τ => by rw [hs0, Formalism.L2.Forms.lamT_zero]; rfl
  have hemb : ∀ z, (D.fm u).emb 0 x c z =
      Formalism.L2.Forms.fnOf Gf s0 1 (MvPolynomial.map D.what₂.embLL p) (T0.val0.eY z) := fun z => pol_spec T0 x c z
  have hRHS : Formalism.MainNotions.flipTwoThree.actAll lam
      (fun τ => (Mb B c τ * (Y : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E).map (B.rho τ))⁻¹)
      (coT T0 (gC B) x c) ∈ Formalism.MainNotions.flipTwoThree.IntSpanAt D w lam ↔
      Formalism.MainNotions.flipTwoThree.actAll lam hh (MvPolynomial.map D.what₂.embLL p) ∈ Formalism.L2.Forms.IntSpan D w lam := by
    rw [coT_apply, actAll_comp, mem_intSpanAt_iff_map, map_actAll]
  have hfn : Formalism.L2.Forms.fnOf Gf s0 N0 (Formalism.MainNotions.flipTwoThree.actAll lam hh (MvPolynomial.map D.what₂.embLL p)) =
      Formalism.L2.Forms.fnOf Gf s0 1 (MvPolynomial.map D.what₂.embLL p) := by
    have h1 := Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.fnOf_mul Gf s0 (fun τ => (hh τ)ᵀ) N0 (MvPolynomial.map D.what₂.embLL p)
    rw [hK] at h1
    rw [h1, actAll_eq_subP, MvPolynomial.smul_eq_C_mul]
    congr 3
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [Matrix.det_transpose, hs]
  have hB0 : Formalism.L2.Forms.IsLocBasis (D.what₂.places.resChar w)
      (dualSet (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _))
        (Formalism.L2.Forms.clsCrd D u 0 (Nat.zero_le _) c)) (BaseBlockInverse Y)⁻¹ :=
    isLocBasis_dual (D.what₂.places.resChar w) _ _ (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwB_clsCrd_lat D u 0 (Nat.zero_le _) c).fg hY _
      (by rw [inv_inv]; rfl)
  have hN0' : Formalism.L2.Forms.atInf (Formalism.L2.Forms.embT D) ((((BaseBlockInverse Y)⁻¹)⁻¹ : GL (Fin (D.R.N 0)) D.host.E) :
      Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) = N0 := by
    rw [inv_inv]
  rw [hRHS]
  constructor
  · intro hAll
    obtain ⟨P, hP, hPz⟩ := hAll _ hB0
    rw [hN0'] at hPz
    have hPe : Formalism.L2.Forms.fnOf Gf s0 N0 P =
        Formalism.L2.Forms.fnOf Gf s0 N0 (Formalism.MainNotions.flipTwoThree.actAll lam hh (MvPolynomial.map D.what₂.embLL p)) := by
      funext y
      obtain ⟨z, rfl⟩ := T0.val0.eY.surjective y
      rw [hfn, ← hemb, hPz]
    have := Formalism.L2.Col.fnOf_injective Gf s0 N0 (isUnit_base_inverse_infinity Y) (Formalism.MainNotions.Ext.Lw.frOne Gf) hPe
    rw [← this]
    exact hP
  · intro hQ Bb hBb
    obtain ⟨Q₂, hQ₂, hQe⟩ := basis_change D w lam Gf s0 hB0 hBb _ hQ
    rw [hN0'] at hQe
    refine ⟨Q₂, hQ₂, fun z => ?_⟩
    rw [hemb, ← hfn, hQe]

theorem finCo_of (T : ∀ u : D.what₂.Word, Formalism.L2.Forms.Forms0 D u) (u : D.what₂.Word) (B : ColBase D u)
    (hB : B.rho = rhoC D) : FinCo (T u) B := by
  intro w
  have : Fact (D.what₂.places.resChar w).Prime := ⟨D.what₂.places.resChar_prime w⟩
  have hex : ∀ c : (D.mem u).C.cls 0, ∃ Y : GL (Fin (D.R.N 0)) D.host.E,
      Formalism.L2.Forms.IsLocBasis (D.what₂.places.resChar w)
        (Formalism.L2.Forms.clsCrd D u 0 (Nat.zero_le _) c : Set (Fin (D.R.N 0) → D.host.E)) Y := by
    intro c
    refine Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.LocB.exists_isLocBasis
      (l := D.what₂.places.resChar w) (K := D.host.E) _
      (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwB_clsCrd_lat D u 0 (Nat.zero_le _) c).fg ?_
    have hLat := D.clsLat_lat u 0 c
    unfold Formalism.L2.Forms.clsCrd
    rw [Submodule.map_coe, LinearMap.coe_restrictScalars, Submodule.span_image, hLat.span_eq_top,
      Submodule.map_top, LinearEquiv.range]
  choose Y hY using hex
  refine ⟨fun c τ => Mb B c τ * (Y c : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E).map (B.rho τ),
    fun c τ => locBasis_gamma B hB w c τ (Y c) (hY c), fun x => ?_⟩
  rw [Formalism.L2.G.Cmp.locWCrit_proved T u w x]
  exact forall_congr' fun c => clause_iff B (T u) hB w c (Y c) (hY c) x

theorem colValOfTiedS_holds : Formalism.MainNotions.RT.ColumnValuationFromTwistCompatibility :=
  colValOfTiedS_of_fin fun _ F _ u B hB => finCo_of (fun u => (F.forms u).to0) u B hB

end Formalism.L2.GlobalTheoryTheory.ColValS
end
end

section -- merged from Formalism.LocalToGlobal.GlobalTheory.CoordinateLengths.SecondBranchAllMembers
section -- merged from Formalism.LocalToGlobal.GlobalTheory.CoordinateLengths.SecondBranchOfRationality
section -- merged from Formalism.LocalToGlobal.GlobalTheory.CoordinateLengths.MixedChange
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LemB

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms NumberField MvPolynomial Formalism.L2.GlobalTheoryTheory.LocalLatticeBases Classical

variable {D : D7} {u : D.what₂.Word}

def mixF (τ₀ : D.what₂.Tau) (B B' : GL (Fin (D.R.N 0)) D.host.E) : D.what₂.Tau → Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) ℂ :=
  fun τ => if τ = τ₀ then atInf (embT D) (B'⁻¹ : GL (Fin (D.R.N 0)) D.host.E).1 τ
    else atInf (embT D) (B⁻¹ : GL (Fin (D.R.N 0)) D.host.E).1 τ

private theorem atInf_mul' (X Y : GL (Fin (D.R.N 0)) D.host.E) (τ : D.what₂.Tau) :
    atInf (embT D) (X * Y : GL (Fin (D.R.N 0)) D.host.E).1 τ =
      atInf (embT D) X.1 τ * atInf (embT D) Y.1 τ := by
  simp only [atInf, Units.val_mul, Matrix.map_mul]

private theorem atInf_one' (τ : D.what₂.Tau) :
    atInf (embT D) (1 : GL (Fin (D.R.N 0)) D.host.E).1 τ = 1 := by
  simp only [atInf, Units.val_one]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem mixed_change (w : D.what₂.places.Pl) (hw : OverT D u w) (τ₀ : D.what₂.Tau)
    {L L' : Set (Fin (D.R.N 0) → D.host.E)} {B B₁ B' B₁' : GL (Fin (D.R.N 0)) D.host.E}
    (hB : IsLocBasis (D.mem u).A.T L B) (hB₁ : IsLocBasis (D.mem u).A.T L B₁)
    (hB' : IsLocBasis (D.mem u).A.T L' B') (hB₁' : IsLocBasis (D.mem u).A.T L' B₁')
    (P : MvPolynomial (D.what₂.Tau × Fin (D.R.N 0) × Fin (D.R.N 0)) ℂ)
    (hP : P ∈ Formalism.L2.Forms.IntSpan D w ((D.fm u).lam 0)) :
    ∃ P₁ ∈ Formalism.L2.Forms.IntSpan D w ((D.fm u).lam 0), ∀ y,
      fnOf (gramC (gramN D 0 (Nat.zero_le _)) (embT D)) (shiftOf (lamT u 0)) (mixF τ₀ B B') P y =
        fnOf (gramC (gramN D 0 (Nat.zero_le _)) (embT D)) (shiftOf (lamT u 0)) (mixF τ₀ B₁ B₁') P₁ y := by
  let N : D.what₂.Tau → Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) ℂ := fun τ =>
    if τ = τ₀ then atInf (embT D) (B'⁻¹ * B₁' : GL (Fin (D.R.N 0)) D.host.E).1 τ
    else atInf (embT D) (B⁻¹ * B₁ : GL (Fin (D.R.N 0)) D.host.E).1 τ
  let N' : D.what₂.Tau → Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) ℂ := fun τ =>
    if τ = τ₀ then atInf (embT D) (B₁'⁻¹ * B' : GL (Fin (D.R.N 0)) D.host.E).1 τ
    else atInf (embT D) (B₁⁻¹ * B : GL (Fin (D.R.N 0)) D.host.E).1 τ
  have hmul : ∀ τ, N τ * N' τ = 1 := by
    intro τ
    by_cases hτ : τ = τ₀
    · simp only [N, N', if_pos hτ]
      rw [← atInf_mul', show B'⁻¹ * B₁' * (B₁'⁻¹ * B') = 1 by group, atInf_one']
    · simp only [N, N', if_neg hτ]
      rw [← atInf_mul', show B⁻¹ * B₁ * (B₁⁻¹ * B) = 1 by group, atInf_one']
  have hN : ∀ τ a b, N τ a b ∈ bwA_Ow D w := by
    intro τ a b
    by_cases hτ : τ = τ₀
    · simp only [N, if_pos hτ]
      exact bwG_change_mem D u w hw τ hB₁' hB' a b
    · simp only [N, if_neg hτ]
      exact bwG_change_mem D u w hw τ hB₁ hB a b
  have hN' : ∀ τ a b, N' τ a b ∈ bwA_Ow D w := by
    intro τ a b
    by_cases hτ : τ = τ₀
    · simp only [N', if_pos hτ]
      exact bwG_change_mem D u w hw τ hB' hB₁' a b
    · simp only [N', if_neg hτ]
      exact bwG_change_mem D u w hw τ hB hB₁ a b
  have hfac : mixF τ₀ B B' = fun τ => N τ * mixF τ₀ B₁ B₁' τ := by
    funext τ
    by_cases hτ : τ = τ₀
    · simp only [mixF, N, if_pos hτ]
      rw [← atInf_mul', show B'⁻¹ * B₁' * B₁'⁻¹ = B'⁻¹ by group]
    · simp only [mixF, N, if_neg hτ]
      rw [← atInf_mul', show B⁻¹ * B₁ * B₁⁻¹ = B⁻¹ by group]
  refine ⟨MvPolynomial.C (∏ τ, (N τ).det ^ shiftOf (lamT u 0) τ) * subP N P,
    bwG_intSpan_allSubP D w _ N _
      (fun τ => local_GL_stabilises_lattice D w _ _ _ (N τ) (N' τ) (hmul τ) (hN τ) (hN' τ)) P hP, fun y => ?_⟩
  rw [hfac, fnOf_mul]

end Formalism.L2.GlobalTheoryTheory.LemB
end
end

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LemB

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms NumberField MvPolynomial Formalism.L2.GlobalTheoryTheory.LocalLatticeBases Classical

variable {D : D7} {u : D.what₂.Word}

theorem onto_Bw (hRC : RatInC D u) (hRG : RatGL D u) (T : Forms0 D u) (hA : admS D u) (w : D.what₂.places.Pl)
    (hw : OverT D u w) (hs : (D.fm u).seenP w = true) (v : (D.mem u).A.vT)
    (B B' : (D.mem u).C.cls 0 → GL (Fin (D.R.N 0)) D.host.E)
    (hB : ∀ c, IsLocBasis (D.mem u).A.T (Ld D u 0 (Nat.zero_le _) c : Set _) (B c))
    (hB' : ∀ c, IsLocBasis (D.mem u).A.T (Lk T.atT 0 (Nat.zero_le _) v c : Set _) (B' c)) :
    (Submodule.pi Set.univ fun c =>
      ((intSubm D w ((D.fm u).lam 0)).map
            ((Formalism.L2.Forms.subP (bwA_N D ((D.fm u).tauOf w v) (B c) (B' c))).toLinearMap.restrictScalars (bwA_Ow D w))).map
          (scO (bwA_Ow D w) _ ((bwA_N D ((D.fm u).tauOf w v) (B c) (B' c) ((D.fm u).tauOf w v)).det ^
            ((D.fm u).lam 0 ((D.fm u).tauOf w v)).detShift))) ≤ ((D.fm u).Bw 0 w v).map (crdL T B w) := by
  intro y hy
  have hy' := fun c => hy c (Set.mem_univ c)
  choose q hq hqy using hy'
  choose Q hQ hQq using hq
  have hQI : ∀ c, Q c ∈ Formalism.L2.Forms.IntSpan D w ((D.fm u).lam 0) := fun c => mem_intSubm w _ _ (hQ c)
  let γ : (D.mem u).C.cls 0 → D.what₂.Tau → GL (Fin (D.R.N 0)) D.host.E := fun c τ =>
    if τ = (D.fm u).tauOf w v then (B' c)⁻¹ * B c else 1
  have hγ : ∀ c, (fun τ => atInf (Formalism.L2.Forms.embT D) ((γ c τ : GL (Fin (D.R.N 0)) D.host.E) :
      Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) τ) = bwA_N D ((D.fm u).tauOf w v) (B c) (B' c) := by
    intro c
    funext τ
    simp only [γ]
    unfold bwA_N
    split_ifs
    · rfl
    · simp [atInf]
  have ho : ∀ c τ, τ ≠ (D.fm u).tauOf w v → bwA_N D ((D.fm u).tauOf w v) (B c) (B' c) τ = 1 := by
    intro c τ h
    unfold bwA_N
    rw [if_neg h]
  have hprod : ∀ c, ∏ τ, (bwA_N D ((D.fm u).tauOf w v) (B c) (B' c) τ).det ^ shiftOf (lamT u 0) τ =
      (bwA_N D ((D.fm u).tauOf w v) (B c) (B' c) ((D.fm u).tauOf w v)).det ^
        ((D.fm u).lam 0 ((D.fm u).tauOf w v)).detShift := by
    intro c
    rw [Fintype.prod_eq_single ((D.fm u).tauOf w v) (fun τ h => by rw [ho c τ h, Matrix.det_one, one_zpow]), lamT_zero]
    rfl
  have hyc : ∀ c, y c = MvPolynomial.C (∏ τ, (bwA_N D ((D.fm u).tauOf w v) (B c) (B' c) τ).det ^ shiftOf (lamT u 0) τ) *
      Formalism.L2.Forms.subP (bwA_N D ((D.fm u).tauOf w v) (B c) (B' c)) (Q c) := by
    intro c
    rw [hprod c, MvPolynomial.C_mul', ← hqy c, ← hQq c]
    rfl
  have hyR : ∀ c, y c ∈ RatSpan D ((D.fm u).lam 0) := by
    intro c
    have h := hRG (γ c) (Q c) (intSpan_le_rat w _ (hQI c))
    have hpt : ∀ τ, atInf (embT D) ((γ c τ : GL (Fin (D.R.N 0)) D.host.E) :
        Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) τ = bwA_N D ((D.fm u).tauOf w v) (B c) (B' c) τ :=
      fun τ => congrFun (hγ c) τ
    simp only [hpt] at h
    rw [hyc c]
    exact h
  obtain ⟨x, hx⟩ := crd_surj T hA B y fun c =>
    ⟨_, hRG (fun _ => (B c)⁻¹) _ (hyR c), hRC _ (hRG (fun _ => (B c)⁻¹) _ (hyR c)), fun z => fnOf_frame (B c) (y c) z⟩
  refine ⟨x, (T.bw0 w hw hs v x).2 fun c B₁ B₁' hB₁ hB₁' => ?_, funext fun c => crd_eq T B (hx c)⟩
  obtain ⟨P₁, hP₁, he⟩ := mixed_change w hw ((D.fm u).tauOf w v) (hB c) hB₁ (hB' c) hB₁' (Q c) (hQI c)
  refine ⟨P₁, hP₁, fun z => ?_⟩
  rw [hx c z, hyc c, ← fnOf_mul, bwA_N_mul]
  exact he _

theorem ontoAll_of (hRC : RatInC D u) (hRG : RatGL D u) : OntoAll D u :=
  fun T hA w hw hs v _ B B' hB hB' => ⟨onto_Bw hRC hRG T hA w hw hs v B B' hB hB', onto_tL hRC hRG T hA w hw B hB _⟩

theorem second_branch_of_rationality (hRC : ∀ (D : D7) (u : D.what₂.Word), RatInC D u) (hRG : ∀ (D : D7) (u : D.what₂.Word), RatGL D u) :
    ∀ (D : D7) (u : D.what₂.Word), Formalism.MainNotions.RT.SecondBranchIntegralityUnderForms D u :=
  second_branch_of_surjectivity (fun D u => ontoAll_of (hRC D u) (hRG D u)) duCount_holds

end Formalism.L2.GlobalTheoryTheory.LemB
end
end

namespace Formalism.L2.GlobalTheoryTheory.LemB

theorem second_branch_all_members : ∀ (D : Formalism.BasicNotions.D7) (u : D.what₂.Word), Formalism.MainNotions.RT.SecondBranchIntegralityUnderForms D u :=
  second_branch_of_rationality ratInC_holds ratGL_holds

end Formalism.L2.GlobalTheoryTheory.LemB
end

noncomputable section

namespace Formalism.MainNotions

open Formalism.BasicNotions Formalism.MainNotions.Lnk Formalism.MainNotions.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory Formalism.MainNotions.RT

variable {eps : ℝ}

theorem tCV_of_ties (Fm : FamP eps) (tCl : tCVTies Fm) :
    ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (i : Fm.Ix x) u, Nonempty (flipTwoThree.ColVal (Fm.D x i) u) :=
  tCV_of_tied Fm ColValS.colValOfTiedS_holds tCl

end Formalism.MainNotions

end
