module

public import Formalism.SharpRestriction.GrowthBounds.DataG
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WittUnramified.GhostComponentG

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.DataGChain
open MvPolynomial

noncomputable section

namespace Formalism.MainNotions.G

namespace Places

variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  (P : Places p O Kf)

def Tminus (v : Fin P.nV) (i : ℕ) (F : P.Tup → P.Xsp) : P.Tup → P.Xsp :=
  fun L => ∑ᶠ (L'' : Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) (_ : IsEdge p (P.n' v) i ⟨L'', L v⟩),
    F (Function.update L v L'')

def withWt (m' : ℕ) (lam0' : ∀ v, Fin (P.n' v) → Fin (m' + 1) → ℤ) (dom' : ∀ v, IsDominant (lam0' v)) :
    Places p O Kf :=
  { P with m := m', lam0 := lam0', dom := dom' }

end Places

def liftWt (t m : ℕ) (lam : Fin (m + 1) → ℤ) (w : ℕ → ℤ) (j : ℕ) : Fin (m + j * (t + 1) + 1) → ℤ :=
  fun i => if h : i.val < m + 1 then lam ⟨i.val, h⟩ else -(w ((i.val - (m + 1)) / (t + 1) + 1))

structure Fills {p : ℕ} (G : GAtP p) where
  TT : ∀ v : Fin G.P.nV, Finset (Fin (G.P.n' v))
  a : ∀ v : Fin G.P.nV, Fin (G.P.n' v) → ℤ
  b : ∀ v : Fin G.P.nV, Fin (G.P.n' v) → ℤ
  c : ℕ
  base : ∀ v, IsBaseWeight (TT v) (a v) (b v) c (G.P.lam0 v)
  t : ℕ
  mm : ℕ
  w : ∀ v : Fin G.P.nV, ℕ → Fin (G.P.n' v) → ℤ
  w_ge : ∀ v s, max (c : ℤ) (-(G.P.lam0 v s (Fin.last G.P.m))) ≤ w v 1 s
  w_mono : ∀ v s j, 1 ≤ j → w v j s ≤ w v (j + 1) s
  domJ : ∀ j v, IsDominant fun s => liftWt t G.P.m (G.P.lam0 v s) (fun i => w v i s) j

namespace Fills

variable {p : ℕ} {G : GAtP p} (Fl : Fills G)

def Pj : ℕ → Places p G.O G.Kf
  | 0 => G.P
  | j + 1 => G.P.withWt (G.P.m + (j + 1) * (Fl.t + 1))
      (fun v s => liftWt Fl.t G.P.m (G.P.lam0 v s) (fun i => Fl.w v i s) (j + 1)) (Fl.domJ (j + 1))

end Fills

structure Levels {p : ℕ} {G : GAtP p} (Fl : Fills G) where
  compS : ℕ → Type
  [finS : ∀ j, Fintype (compS j)]
  levS : ∀ j, compS j → Level (Fl.Pj (j + 1))

attribute [instance] Levels.finS

namespace Levels

variable {p : ℕ} {G : GAtP p} {Fl : Fills G} (Lv : Levels Fl)

def comp : ℕ → Type
  | 0 => G.comp
  | j + 1 => Lv.compS j

def lev : (j : ℕ) → Lv.comp j → Level (Fl.Pj j)
  | 0 => G.lev
  | j + 1 => Lv.levS j

abbrev Fm (j : ℕ) : Type := Lv.comp j → (Fl.Pj j).Tup → (Fl.Pj j).Xsp

def Int (j : ℕ) : Submodule G.O (Lv.Fm j) := Submodule.pi Set.univ fun i => (Lv.lev j i).M

def Tm (j : ℕ) (v : Fin (Fl.Pj j).nV) (i : ℕ) (F : Lv.Fm j) : Lv.Fm j := fun c => (Fl.Pj j).Tminus v i (F c)

end Levels

structure Chain {p : ℕ} {G : GAtP p} {Fl : Fills G} (Lv : Levels Fl) where
  Kz : ∀ j, Lv.Fm j →ₗ[G.Kf] Lv.Fm (j + 1)

namespace Chain

variable {p : ℕ} {G : GAtP p} {Fl : Fills G} {Lv : Levels Fl} (Ch : Chain Lv)

def chainK : (j : ℕ) → Lv.Fm 0 →ₗ[G.Kf] Lv.Fm j
  | 0 => LinearMap.id
  | j + 1 => (Ch.Kz j).comp (chainK j)

end Chain

end Formalism.MainNotions.G
end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.WittIdentPI
section -- merged from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.WittUnram
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WittUnramified.WittUnramMain
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WittUnramified.PsiStep
noncomputable section

namespace PI.WittUnramWork

open WittVector Finset

variable {p : ℕ} [hp : Fact p.Prime] {W k : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
  [Field k] [CharP k p] [PerfectRing k p]

theorem psi_injective (ψ : W →+* WittVector p k) (hirr : Irreducible (p : W)) :
    Function.Injective ψ := by
  refine (injective_iff_map_eq_zero ψ).2 ?_
  intro x hx
  by_contra hne
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible hne hirr
  obtain ⟨u, hu⟩ := hn
  have h2 : ψ ((p : W) ^ n) = 0 := by rw [← hu, map_mul, hx, zero_mul]
  rw [map_pow, map_natCast] at h2
  exact pow_ne_zero n (WittVector.p_nonzero p k) h2

theorem psi_step (ψ : W →+* WittVector p k) (res : W →+* k) (hres : Function.Surjective res)
    (h0 : ∀ x, (ψ x).coeff 0 = res x) (w : WittVector p k) :
    ∃ a : W, ∃ b : WittVector p k, w = ψ a + (p : WittVector p k) * b := by
  obtain ⟨a, ha⟩ := hres (w.coeff 0)
  refine ⟨a, ?_⟩
  by_cases hz : w - ψ a = 0
  · exact ⟨0, by rw [mul_zero, add_zero]; exact sub_eq_zero.mp hz⟩
  · obtain ⟨m, b, hb0, hb⟩ := WittVector.exists_eq_pow_p_mul (w - ψ a) hz
    have hc : (w - ψ a).coeff 0 = 0 := by
      have h3 := WittVector.add_coeff_zero (ψ a) (w - ψ a)
      rw [show ψ a + (w - ψ a) = w by abel, h0, ha] at h3
      linear_combination -h3
    have hm : m ≠ 0 := by
      rintro rfl
      apply hb0
      rw [pow_zero, one_mul] at hb
      rw [← hb]
      exact hc
    refine ⟨(p : WittVector p k) ^ (m - 1) * b, ?_⟩
    rw [← mul_assoc, ← pow_succ', Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hm), ← hb]
    ring

theorem psi_surjective (ψ : W →+* WittVector p k) (res : W →+* k) (hres : Function.Surjective res)
    (h0 : ∀ x, (ψ x).coeff 0 = res x) (hC : IsAdicComplete (Ideal.span {(p : W)}) W) :
    Function.Surjective ψ := by
  intro w
  choose A B hAB using psi_step ψ res hres h0
  obtain ⟨r, hr0, hrs⟩ : ∃ r : ℕ → WittVector p k, r 0 = w ∧ ∀ n, r (n + 1) = B (r n) :=
    ⟨fun n => B^[n] w, rfl, fun n => Function.iterate_succ_apply' B n w⟩
  obtain ⟨s, hs0, hss⟩ : ∃ s : ℕ → W, s 0 = 0 ∧ ∀ n, s (n + 1) = s n + A (r n) * (p : W) ^ n :=
    ⟨fun n => ∑ i ∈ Finset.range n, A (r i) * (p : W) ^ i, by simp, fun n => Finset.sum_range_succ _ _⟩
  have hinv : ∀ n, w = ψ (s n) + (p : WittVector p k) ^ n * r n := by
    intro n
    induction n with
    | zero => rw [hs0, hr0, map_zero, pow_zero, one_mul, zero_add]
    | succ n ih =>
      calc w = ψ (s n) + (p : WittVector p k) ^ n * r n := ih
        _ = ψ (s n) + (p : WittVector p k) ^ n * (ψ (A (r n)) + (p : WittVector p k) * B (r n)) := by
          rw [← hAB (r n)]
        _ = ψ (s (n + 1)) + (p : WittVector p k) ^ (n + 1) * r (n + 1) := by
          rw [hss, hrs, map_add (f := _), map_mul, map_pow, map_natCast]
          ring
  have hdiv : ∀ m n, m ≤ n → (p : W) ^ m ∣ s n - s m := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
      rw [hss, add_sub_right_comm]
      exact dvd_add ih (Dvd.dvd.mul_left (pow_dvd_pow _ hmn) _)
  have hI : ∀ n (x : W), x ∈ (Ideal.span {(p : W)} ^ n • ⊤ : Submodule W W) ↔ (p : W) ^ n ∣ x := by
    intro n x
    rw [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  obtain ⟨L, hL⟩ := hC.toIsPrecomplete.prec (f := s) (fun {m n} hmn => by
    rw [SModEq.sub_mem, hI]
    exact dvd_sub_comm.mp (hdiv m n hmn))
  have hw : ∀ n, (p : WittVector p k) ^ n ∣ w - ψ L := by
    intro n
    obtain ⟨c, hc⟩ := (hI n _).1 (SModEq.sub_mem.1 (hL n))
    refine ⟨ψ c + r n, ?_⟩
    have h2 : ψ (s n) - ψ L = (p : WittVector p k) ^ n * ψ c := by
      rw [← map_sub, hc, map_mul, map_pow, map_natCast]
    calc w - ψ L = ψ (s n) + (p : WittVector p k) ^ n * r n - ψ L := by rw [← hinv n]
      _ = (p : WittVector p k) ^ n * (ψ c + r n) := by linear_combination h2
  have hzero : w - ψ L = 0 := by
    by_contra hne
    obtain ⟨m, b, hb0, hb⟩ := WittVector.exists_eq_pow_p_mul (w - ψ L) hne
    obtain ⟨c, hc⟩ := hw (m + 1)
    rw [hb, pow_succ, mul_assoc] at hc
    have hp : (p : WittVector p k) ^ m ≠ 0 := pow_ne_zero m (WittVector.p_nonzero p k)
    have hbc := mul_left_cancel₀ hp hc
    apply hb0
    rw [hbc]
    first
    | rw [WittVector.mul_coeff_zero, WittVector.coeff_p_zero, zero_mul]
    | simp
  exact ⟨L, (sub_eq_zero.mp hzero).symm⟩

end PI.WittUnramWork
end
end

noncomputable section

namespace PI.WittUnramWork

open WittVector

private theorem map_frobenius' {p : ℕ} [Fact p.Prime] {R S : Type*} [CommRing R] [CommRing S]
    (g : R →+* S) (x : WittVector p R) :
    WittVector.map g (WittVector.frobenius x) = WittVector.frobenius (WittVector.map g x) := by
  ext n
  simp only [WittVector.map_coeff, WittVector.coeff_frobenius, MvPolynomial.aeval_def,
    MvPolynomial.eval₂_comp_left]
  congr 1
  exact RingHom.ext_int _ _

theorem wittUnram_main : PI.WittUnram := by
  intro p f _ W Qq _ _ _ _ _ σ hfrac hirr hcard hcomp hσ
  have hinj : Function.Injective (algebraMap W Qq) := IsFractionRing.injective W Qq
  have hF : ∀ x : W, ∃ y : W, sigW hinj σ hσ x = x ^ p + (p : W) * y := sigW_lift hinj σ hσ
  set I : Ideal W := Ideal.span {(p : W)} with hI
  haveI hmax : I.IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hirr
  letI : Field (W ⧸ I) := Ideal.Quotient.field I
  have hp0 : ((p : ℕ) : W ⧸ I) = 0 := by
    have h : Ideal.Quotient.mk I (p : W) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
    rwa [map_natCast] at h
  haveI hchar : CharP (W ⧸ I) p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr hp0
  haveI hfin : Finite (W ⧸ I) := Nat.finite_of_card_ne_zero (by
    rw [hcard]; exact pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
  obtain ⟨e⟩ : Nonempty ((W ⧸ I) ≃+* GaloisField p f) := by
    letI : Algebra (ZMod p) (W ⧸ I) := (ZMod.castHom (dvd_refl p) (W ⧸ I)).toAlgebra
    exact ⟨(GaloisField.algEquivGaloisField p f hcard).toRingEquiv⟩
  have hpQ : ((p : ℕ) : Qq) ≠ 0 := by
    rw [← map_natCast (algebraMap W Qq) p]
    exact fun h => hirr.ne_zero (hinj (h.trans (map_zero _).symm))
  letI : Invertible ((p : ℕ) : Qq) := invertibleOfNonzero hpQ
  let ψ : W →+* WittVector p (W ⧸ I) :=
    (WittVector.map (Ideal.Quotient.mk I)).comp (sHom p Qq (sigW hinj σ hσ) hF hinj)
  have h0 : ∀ x, (ψ x).coeff 0 = Ideal.Quotient.mk I x := by
    intro x
    show (WittVector.map (Ideal.Quotient.mk I) (sHom p Qq (sigW hinj σ hσ) hF hinj x)).coeff 0 = _
    rw [WittVector.map_coeff, sHom_coeff_zero]
  have hψi : Function.Injective ψ := psi_injective ψ hirr
  have hψs : Function.Surjective ψ :=
    psi_surjective ψ (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective h0 hcomp
  let χ : W →+* WittVector p (GaloisField p f) := (WittVector.map (e : (W ⧸ I) →+* GaloisField p f)).comp ψ
  have hχ : Function.Bijective χ :=
    ⟨(WittVector.map_injective _ e.injective).comp hψi, (WittVector.map_surjective _ e.surjective).comp hψs⟩
  have hφ : ∀ w, (RingEquiv.ofBijective χ hχ).symm (χ w) = w := by
    intro w
    have h := (RingEquiv.ofBijective χ hχ).symm_apply_apply w
    rwa [RingEquiv.ofBijective_apply] at h
  have hfrob : ∀ w, WittVector.frobenius (χ w) = χ (sigW hinj σ hσ w) := by
    intro w
    show _ = WittVector.map (e : (W ⧸ I) →+* GaloisField p f)
      (WittVector.map (Ideal.Quotient.mk I) (sHom p Qq (sigW hinj σ hσ) hF hinj (sigW hinj σ hσ w)))
    rw [sHom_frob, map_frobenius', map_frobenius']
    rfl
  refine ⟨(RingEquiv.ofBijective χ hχ).symm, ?_⟩
  intro x
  obtain ⟨w, rfl⟩ := hχ.2 x
  rw [hfrob, hφ, hφ]
  exact (sigW_spec hinj σ hσ w).symm

end PI.WittUnramWork
end
end

theorem witt_unramified : PI.WittUnram :=
  PI.WittUnramWork.wittUnram_main
end

namespace Formalism.MainNotions.G.WittPI

theorem wittIdent_of (H : PI.WittUnram) : Formalism.MainNotions.G.WittIdent :=
  fun p n' _ W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w hS =>
    H p n' W Qq σ hS.frac_alt hS.p_unif hS.res_card hS.eq_sum_herm_smul_frame_of_inW hS.frob

theorem wittIdentity_holds : Formalism.MainNotions.G.WittIdent := wittIdent_of witt_unramified

end Formalism.MainNotions.G.WittPI
end
