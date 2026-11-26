module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DominantWeightPolynomialFunctionalMinors
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.XiTopEqProd

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DualLatticeClassLocalizationEqUnimodularCompanio
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DualLatticeClassLocalizationEqUnimodularCompanio
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.LshOffLevel

theorem mem_divs_of' {A : Type} [CommRing A] [IsDedekindDomain A] {a : A} {P : HeightOneSpectrum A}
    (h : P ∈ divs a) : a ∈ P.asIdeal := by
  unfold divs at h
  split_ifs at h with hf
  · exact (hf.mem_toFinset.1 h)
  · simp at h

theorem lsh_lattice_and_loc_eq : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (Y : DivX (I.rec7 l Z)) (u : B.Word) (μ : I.ι) (w : (I.rec7 l Z).what₂.places.Pl), LevFree Y u μ w → ∀ (j : ℕ), j ≤ B.R.m → ∀ (c : (I.stp u μ j).Cl), Submodule.IsLattice B.fields.E ((I.stp u μ j).Lsh c.1 ((I.stp u μ j).rep c)) ∧ ∀ x : Fin (B.R.N j) → B.fields.E, (∃ s : ℕ, ¬ (I.rec7 l Z).what₂.places.resChar w ∣ s ∧ (s : B.fields.E) • x ∈ (I.stp u μ j).Lsh c.1 ((I.stp u μ j).rep c)) ↔ (∃ s : ℕ, ¬ (I.rec7 l Z).what₂.places.resChar w ∣ s ∧ (s : B.fields.E) • x ∈ ((I.stp u μ j).rep c).1.1.deco.1.N) := by
  intro B X I hOk hPins l Z Y u μ w hw j hj c
  classical
  have hpP : ((I.rec7 l Z).what₂.places.resChar w).Prime := (I.rec7 l Z).what₂.places.resChar_prime w
  have hTP : (B.T u).Prime := l.pr.T_prime u
  have hpT : ¬ (I.rec7 l Z).what₂.places.resChar w ∣ B.T u := fun h => hw.1 ((Nat.prime_dvd_prime_iff_eq hpP hTP).1 h)
  set d := ((I.stp u μ j).rep c).1.1.deco with hd
  have hE : (I.stp u μ j).Lsh c.1 ((I.stp u μ j).rep c) = d.1.Lsh := rfl
  rw [hE]
  have hTP' : ∀ P : (B.primes X).vT u, (((B.T u : ℕ) : 𝓞 B.fields.E)) ∈ (P : HeightOneSpectrum (𝓞 B.fields.E)).asIdeal := by
    intro P
    have hpi := mem_divs_of' P.2
    rw [← l.pr.piT_norm u]
    exact Ideal.mul_mem_right _ _ hpi
  have hLN : ∀ x ∈ d.1.Lsh, ((B.T u : ℕ) : B.fields.E) • x ∈ d.1.N := by
    intro x hx
    have := d.2.smul_Lsh_mem_N (a := ((B.T u : ℕ) : 𝓞 B.fields.E)) (fun P => by rw [map_natCast]; exact hTP' P) hx
    rwa [Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul B.fields.E] at this
  refine ⟨d.2.Lsh_lattice, fun x => ⟨?_, ?_⟩⟩
  · rintro ⟨s, hs, hx⟩
    refine ⟨B.T u * s, fun h => (hpP.dvd_mul.1 h).elim hpT hs, ?_⟩
    have h3 := hLN _ hx
    have e : ((B.T u * s : ℕ) : B.fields.E) • x = ((B.T u : ℕ) : B.fields.E) • ((s : B.fields.E) • x) := by
      rw [smul_smul, ← Nat.cast_mul]
    exact e ▸ h3
  · rintro ⟨s, hs, hx⟩
    exact ⟨s, hs, d.2.N_le_Lsh hx⟩

end GlobalTheory.LshOffLevel
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DualLatticeClassLocalizationEqUnimodularCompanioStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualLattice_class_localization_eq_unimodularCompanion : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (Y : DivX (I.rec7 l Z)) (u : B.Word) (μ : I.ι) (w : (I.rec7 l Z).what₂.places.Pl), LevFree Y u μ w → ∀ (j : ℕ), j ≤ B.R.m → ∀ (c : (I.stp u μ j).Cl), Submodule.IsLattice B.fields.E ((I.stp u μ j).Lsh c.1 ((I.stp u μ j).rep c)) ∧ ∀ x : Fin (B.R.N j) → B.fields.E, (∃ s : ℕ, ¬ (I.rec7 l Z).what₂.places.resChar w ∣ s ∧ (s : B.fields.E) • x ∈ (I.stp u μ j).Lsh c.1 ((I.stp u μ j).rep c)) ↔ (∃ s : ℕ, ¬ (I.rec7 l Z).what₂.places.resChar w ∣ s ∧ (s : B.fields.E) • x ∈ ((I.stp u μ j).rep c).1.1.deco.1.N) := by
  first | exact @GlobalTheory.LshOffLevel.lsh_lattice_and_loc_eq | exact GlobalTheory.LshOffLevel.lsh_lattice_and_loc_eq | (intros; apply GlobalTheory.LshOffLevel.lsh_lattice_and_loc_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeylLatticeDualInvariantUnitIff
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeylLatticeDualInvariantUnitIff
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.DelWSub

def intBall (p : ℕ) [Fact p.Prime] : Subring ℂ_[p] := GlobalTheory.ClosedBallValuationSubring.closedBallSubring ℂ_[p]

theorem eval_rowAct {R : Type} [CommRing R] {N : ℕ} (G Y : Matrix (Fin N) (Fin N) R)
    (P : MvPolynomial (Fin N × Fin N) R) :
    MvPolynomial.eval (fun k => Y k.1 k.2) (Formalism.GradedWeylDivisibility.rowAct R G P) =
      MvPolynomial.eval (fun k => (G * Y) k.1 k.2) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [Formalism.GradedWeylDivisibility.rowAct]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p v hp =>
    rw [map_mul, MvPolynomial.eval_mul, MvPolynomial.eval_mul, hp]
    simp [Formalism.GradedWeylDivisibility.rowAct, Matrix.mul_apply]

theorem weyl_eq (N : ℕ) (ν : Fin N → ℕ) :
    WeylLatticeDuality.weyl ℤ N N le_rfl ν = Formalism.GradedWeylDivisibility.weyl ℤ N N le_rfl ν := rfl

theorem rowSub_expand (p : ℕ) [Fact p.Prime] {N : ℕ} (ν : Fin N → ℕ)
    (g : Matrix (Fin N) (Fin N) ℂ_[p]) (hg : ∀ a b, ‖g a b‖ ≤ 1)
    (f : MvPolynomial (Fin N × Fin N) ℤ) (hf : f ∈ WeylLatticeDuality.weyl ℤ N N le_rfl ν) :
    ∃ (s : Finset (List (Fin N × Fin N × ℕ))) (o : List (Fin N × Fin N × ℕ) → ℂ_[p]),
      (∀ w, ‖o w‖ ≤ 1) ∧ ∀ Y : Matrix (Fin N) (Fin N) ℂ_[p],
        MvPolynomial.eval (fun k => (g * Y) k.1 k.2) (MvPolynomial.map (Int.castRingHom ℂ_[p]) f) =
          ∑ w ∈ s, o w * MvPolynomial.eval (fun k => Y k.1 k.2) (MvPolynomial.map (Int.castRingHom ℂ_[p])
            (WeylLatticeDuality.applyWord ℤ w (WeylLatticeDuality.hw ℤ le_rfl ν))) := by
  classical
  let O := intBall p
  let gO : Matrix (Fin N) (Fin N) O := fun a b => ⟨g a b, hg a b⟩
  have hgO : gO.map O.subtype = g := by ext a b; rfl
  have hfO : MvPolynomial.map (Int.castRingHom O) f ∈ Formalism.GradedWeylDivisibility.weyl O N N le_rfl ν :=
    GlobalTheory.WeylRowAll.map_mem_weyl (Int.castRingHom O) le_rfl ν f (by rw [← weyl_eq]; exact hf)
  have hQ := GlobalTheory.WeylRowAll.rowAct_mem_weyl O le_rfl ν gO _ hfO
  unfold Formalism.GradedWeylDivisibility.weyl at hQ
  obtain ⟨c, hc⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).1 hQ
  refine ⟨c.support, fun w => (c w : ℂ_[p]), fun w => (c w).2, fun Y => ?_⟩
  have h1 : MvPolynomial.map (Int.castRingHom ℂ_[p]) f =
      MvPolynomial.map O.subtype (MvPolynomial.map (Int.castRingHom O) f) := by
    rw [MvPolynomial.map_map]; congr 1
  have hterm : ∀ w, MvPolynomial.map O.subtype (Formalism.GradedWeylDivisibility.applyWord O w (Formalism.GradedWeylDivisibility.hw O le_rfl ν)) =
      MvPolynomial.map (Int.castRingHom ℂ_[p])
        (WeylLatticeDuality.applyWord ℤ w (WeylLatticeDuality.hw ℤ le_rfl ν)) := by
    intro w
    rw [← Formalism.GradedWeylDivisibility.lclosedeq_applyWord_map, Formalism.GradedWeylDivisibility.lclosedeq_hw_map]
    show _ = MvPolynomial.map _ (Formalism.GradedWeylDivisibility.applyWord ℤ w (Formalism.GradedWeylDivisibility.hw ℤ le_rfl ν))
    rw [← Formalism.GradedWeylDivisibility.lclosedeq_applyWord_map, Formalism.GradedWeylDivisibility.lclosedeq_hw_map]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h1, ← eval_rowAct, ← hgO, ← GlobalTheory.WeylRowAll.map_rowAct, ← hc, Finsupp.sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, MvPolynomial.eval_mul,
    MvPolynomial.eval_C, hterm]
  rfl

def act (p : ℕ) [Fact p.Prime] (T : Type) (N : ℕ) (g : T → Matrix (Fin N) (Fin N) ℂ_[p]) (c : ℂ_[p]) :
    ((T → Matrix (Fin N) (Fin N) ℂ_[p]) → ℂ_[p]) →+ ((T → Matrix (Fin N) (Fin N) ℂ_[p]) → ℂ_[p]) where
  toFun F := fun y => c * F (fun τ => g τ * y τ)
  map_zero' := by funext y; simp
  map_add' F G := by funext y; simp [mul_add]

theorem mem_delW_act (p : ℕ) [Fact p.Prime] (T : Type) [Fintype T] (N : ℕ) (ν : T → Fin N → ℕ)
    (g : T → Matrix (Fin N) (Fin N) ℂ_[p]) (c : ℂ_[p]) (hg : ∀ τ a b, ‖g τ a b‖ ≤ 1) (hc : ‖c‖ ≤ 1)
    (F : (T → Matrix (Fin N) (Fin N) ℂ_[p]) → ℂ_[p]) (hF : F ∈ WeylLatticeDuality.DelW p T N ν) :
    (fun y => c * F (fun τ => g τ * y τ)) ∈ WeylLatticeDuality.DelW p T N ν := by
  classical
  refine (AddSubgroup.closure_le ((WeylLatticeDuality.DelW p T N ν).comap (act p T N g c))).2 ?_ hF
  rintro _ ⟨r, f, hr, hf, rfl⟩
  rw [SetLike.mem_coe, AddSubgroup.mem_comap]
  choose s o ho hexp using fun τ => rowSub_expand p (ν τ) (g τ) (hg τ) (f τ) (hf τ)
  have heq : act p T N g c (fun y => r * ∏ τ, MvPolynomial.eval (fun k : Fin N × Fin N => y τ k.1 k.2)
      (MvPolynomial.map (Int.castRingHom ℂ_[p]) (f τ))) =
      ∑ x ∈ Fintype.piFinset s, fun y => (c * r * ∏ τ, o τ (x τ)) *
        ∏ τ, MvPolynomial.eval (fun k : Fin N × Fin N => y τ k.1 k.2) (MvPolynomial.map (Int.castRingHom ℂ_[p])
          (WeylLatticeDuality.applyWord ℤ (x τ) (WeylLatticeDuality.hw ℤ le_rfl (ν τ)))) := by
    funext y
    rw [Finset.sum_apply]
    show c * (r * ∏ τ, MvPolynomial.eval (fun k : Fin N × Fin N => (g τ * y τ) k.1 k.2)
      (MvPolynomial.map (Int.castRingHom ℂ_[p]) (f τ))) = _
    simp only [hexp]
    rw [Finset.prod_univ_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.prod_mul_distrib]; ring
  rw [heq]
  refine AddSubgroup.sum_mem _ fun x _ => AddSubgroup.subset_closure
    ⟨c * r * ∏ τ, o τ (x τ), fun τ => WeylLatticeDuality.applyWord ℤ (x τ) (WeylLatticeDuality.hw ℤ le_rfl (ν τ)),
      ?_, fun τ => Submodule.subset_span ⟨x τ, rfl⟩, rfl⟩
  rw [norm_mul, norm_mul, norm_prod]
  exact mul_le_one₀ (mul_le_one₀ hc (norm_nonneg _) hr) (Finset.prod_nonneg fun _ _ => norm_nonneg _)
    (Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun τ _ => ho τ _)

theorem exists_int_inv (p : ℕ) [Fact p.Prime] {N : ℕ} (g : Matrix (Fin N) (Fin N) ℂ_[p])
    (hg : ∀ a b, ‖g a b‖ ≤ 1) (hdet : ‖g.det‖ = 1) :
    ∃ h : Matrix (Fin N) (Fin N) ℂ_[p], (∀ a b, ‖h a b‖ ≤ 1) ∧ g * h = 1 := by
  classical
  let O := intBall p
  let gO : Matrix (Fin N) (Fin N) O := fun a b => ⟨g a b, hg a b⟩
  have hmap : gO.map O.subtype = g := by ext a b; rfl
  have hd : O.subtype gO.det = g.det := by rw [RingHom.map_det]; rfl
  have hdne : g.det ≠ 0 := norm_ne_zero_iff.1 (by rw [hdet]; exact one_ne_zero)
  have hu : IsUnit gO.det := by
    refine IsUnit.of_mul_eq_one (⟨g.det⁻¹, ?_⟩ : O) ?_
    · show ‖g.det⁻¹‖ ≤ 1
      rw [norm_inv, hdet, inv_one]
    · apply Subtype.ext
      show O.subtype gO.det * g.det⁻¹ = 1
      rw [hd, mul_inv_cancel₀ hdne]
  refine ⟨gO⁻¹.map O.subtype, fun a b => (gO⁻¹ a b).2, ?_⟩
  rw [← hmap, ← Matrix.map_mul, Matrix.mul_nonsing_inv _ hu, Matrix.map_one _ (map_zero _) (map_one _)]

theorem delW_rowSub : ∀ (p : ℕ) [Fact p.Prime] (T : Type) [Fintype T] (N : ℕ) (ν : T → Fin N → ℕ) (g : T → Matrix (Fin N) (Fin N) ℂ_[p]) (c : ℂ_[p]), (∀ τ a b, ‖g τ a b‖ ≤ 1) → (∀ τ, ‖(g τ).det‖ = 1) → ‖c‖ = 1 → ∀ F : (T → Matrix (Fin N) (Fin N) ℂ_[p]) → ℂ_[p], F ∈ WeylLatticeDuality.DelW p T N ν ↔ (fun y => c * F (fun τ => g τ * y τ)) ∈ WeylLatticeDuality.DelW p T N ν := by
  intro p _ T _ N ν g c hg hdet hc F
  constructor
  · exact mem_delW_act p T N ν g c hg hc.le F
  · intro h
    have hinv := fun τ => exists_int_inv p (g τ) (hg τ) (hdet τ)
    choose hm hmI hmul using hinv
    have hc0 : c ≠ 0 := norm_ne_zero_iff.1 (by rw [hc]; exact one_ne_zero)
    have := mem_delW_act p T N ν hm c⁻¹ hmI (by rw [norm_inv, hc, inv_one]) _ h
    convert this using 1
    funext y
    rw [inv_mul_cancel_left₀ hc0]
    congr 1
    funext τ
    simp [← Matrix.mul_assoc, hmul]

end GlobalTheory.DelWSub
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeylLatticeDualInvariantUnitIffStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weyl_lattice_dual_invariant_unit_iff : ∀ (p : ℕ) [Fact p.Prime] (T : Type) [Fintype T] (N : ℕ) (ν : T → Fin N → ℕ) (g : T → Matrix (Fin N) (Fin N) ℂ_[p]) (c : ℂ_[p]), (∀ τ a b, ‖g τ a b‖ ≤ 1) → (∀ τ, ‖(g τ).det‖ = 1) → ‖c‖ = 1 → ∀ F : (T → Matrix (Fin N) (Fin N) ℂ_[p]) → ℂ_[p], F ∈ WeylLatticeDuality.DelW p T N ν ↔ (fun y => c * F (fun τ => g τ * y τ)) ∈ WeylLatticeDuality.DelW p T N ν := by
  first | exact @GlobalTheory.DelWSub.delW_rowSub | exact GlobalTheory.DelWSub.delW_rowSub | (intros; apply GlobalTheory.DelWSub.delW_rowSub <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalBasisAndEmbeddedBasisDifferByUnimodularInte
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalBasisAndEmbeddedBasisDifferByUnimodularInte
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.LocBasisBasR

open Matrix

theorem norm_det_le_one {K : Type*} [NormedField K] [IsUltrametricDist K] {N : ℕ}
    (g : Matrix (Fin N) (Fin N) K) (hg : ∀ a b, ‖g a b‖ ≤ 1) : ‖g.det‖ ≤ 1 := by
  rw [Matrix.det_apply']
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun σ _ => ?_
  have hs : ‖(((Equiv.Perm.sign σ : ℤˣ) : ℤ) : K)‖ ≤ 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  rw [norm_mul, norm_prod]
  exact mul_le_one₀ hs (Finset.prod_nonneg fun _ _ => norm_nonneg _) (Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun i _ => hg _ _)

theorem main : ∀ (D : D7) {p : ℕ} [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) (τ : D.what₂.Tau) {N : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (Bm : GL (Fin N) D.host.E) (M : Matrix (Fin N) (Fin N) ℂ_[p]), Formalism.L2.Forms.IsLocBasis p (L : Set (Fin N → D.host.E)) Bm → GL3Columns.BasR D lam τ L M → ∃ g : Matrix (Fin N) (Fin N) ℂ_[p], (∀ a b, ‖g a b‖ ≤ 1) ∧ ‖g.det‖ = 1 ∧ M = (Bm : Matrix (Fin N) (Fin N) D.host.E).map (TaylorLogMetric.tauEmb D lam τ) * g := by
  intro D p _ lam τ N L Bm M hL hM
  obtain ⟨ρ, hρ⟩ := GlobalTheory.JetTieCompare.exists_tauHom D lam τ
  have hp : p.Prime := Fact.out
  have hns : ∀ s : ℕ, ¬ p ∣ s → ‖ρ (s : D.host.E)‖ = 1 := fun s hs => by
    rw [map_natCast]; exact GlobalTheory.KapSplitNorm.norm_natCast_eq_one p s hs
  set A : Matrix (Fin N) (Fin N) ℂ_[p] := (Bm : Matrix (Fin N) (Fin N) D.host.E).map ρ with hAdef
  set Ai : Matrix (Fin N) (Fin N) ℂ_[p] := ((Bm⁻¹ : GL (Fin N) D.host.E) : Matrix (Fin N) (Fin N) D.host.E).map ρ with hAidef
  have hAAi : A * Ai = 1 := by
    rw [hAdef, hAidef, ← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero ρ) (map_one ρ)]
  have hAiA : Ai * A = 1 := by
    rw [hAdef, hAidef, ← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero ρ) (map_one ρ)]
  have hMu : IsUnit M.det := Ne.isUnit hM.1

  have hcoord : ∀ x ∈ L, ∀ a, ‖(Ai *ᵥ fun i => ρ (x i)) a‖ ≤ 1 := by
    intro x hx a
    obtain ⟨s, hs, hint⟩ := (hL x).1 ⟨1, hp.not_dvd_one, by simpa using hx⟩
    obtain ⟨c, hc⟩ := hint a
    have e : (Ai *ᵥ fun i => ρ (x i)) a = ρ ((((Bm⁻¹ : GL (Fin N) D.host.E) : Matrix (Fin N) (Fin N) D.host.E) *ᵥ x) a) := by
      rw [RingHom.map_mulVec]; rfl
    have hs1 := hns s hs
    have hs0 : ρ (s : D.host.E) ≠ 0 := by intro h; rw [h, norm_zero] at hs1; exact zero_ne_one hs1
    have e2 : ρ ((((Bm⁻¹ : GL (Fin N) D.host.E) : Matrix (Fin N) (Fin N) D.host.E) *ᵥ x) a) =
        (ρ (s : D.host.E))⁻¹ * ρ (algebraMap (𝓞 D.host.E) D.host.E c) := by
      rw [hc, map_mul]; field_simp
    rw [e, e2, norm_mul, norm_inv, hs1, inv_one, one_mul]
    exact GlobalTheory.JetTieCompare.norm_int_le ρ c
  have hg : ∀ a b, ‖(Ai * M) a b‖ ≤ 1 := by
    intro a b
    obtain ⟨n, r, x, hr, hx, hcol⟩ := hM.2.2 b
    have : (Ai * M) a b = ∑ k, r k * (Ai *ᵥ fun i => ρ (x k i)) a := by
      simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, hcol, hρ, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => by ring
    rw [this]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun k _ => ?_
    rw [norm_mul]
    exact mul_le_one₀ (hr k) (norm_nonneg _) (hcoord _ (hx k) a)
  refine ⟨Ai * M, hg, ?_, ?_⟩
  · have hh : ∀ b a, ‖(M⁻¹ * A) b a‖ ≤ 1 := by
      intro b a
      let x : Fin N → D.host.E := fun j => (Bm : Matrix (Fin N) (Fin N) D.host.E) j a
      have hxe : x = (Bm : Matrix (Fin N) (Fin N) D.host.E) *ᵥ Pi.single a 1 := by
        funext j; simp [x, Matrix.mulVec_single]
      have hrhs : ∃ s : ℕ, ¬ p ∣ s ∧ ∀ c, (s : D.host.E) *
          (((Bm⁻¹ : GL (Fin N) D.host.E) : Matrix (Fin N) (Fin N) D.host.E) *ᵥ x) c ∈ (algebraMap (𝓞 D.host.E) D.host.E).range := by
        refine ⟨1, hp.not_dvd_one, fun c => ?_⟩
        rw [hxe, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec,
          Nat.cast_one, one_mul, Pi.single_apply]
        split_ifs
        · exact ⟨1, map_one _⟩
        · exact ⟨0, map_zero _⟩
      obtain ⟨s, hs, hmem⟩ := (hL x).2 hrhs
      have h := hM.2.1 _ hmem b
      rw [hρ] at h
      have e : (fun j => ρ (((s : D.host.E) • x) j)) = ρ (s : D.host.E) • fun j => ρ (x j) := by
        funext j
        change ρ ((s : D.host.E) * x j) = ρ (s : D.host.E) * ρ (x j)
        rw [map_mul]
      rw [e, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, norm_mul, hns s hs, one_mul] at h
      convert h using 2
      simp [A, x, Matrix.mul_apply, Matrix.mulVec, dotProduct]
    have hprod : (Ai * M) * (M⁻¹ * A) = 1 := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc M, Matrix.mul_nonsing_inv _ hMu, Matrix.one_mul, hAiA]
    have hd := congrArg Matrix.det hprod
    rw [Matrix.det_mul, Matrix.det_one] at hd
    have hn := congrArg norm hd
    rw [norm_mul, norm_one] at hn
    have h1 := norm_det_le_one _ hg
    have h2 := norm_det_le_one _ (fun b a => hh b a)
    by_contra hne
    have hlt : ‖(Ai * M).det‖ < 1 := lt_of_le_of_ne h1 hne
    have : ‖(Ai * M).det‖ * ‖(M⁻¹ * A).det‖ < 1 :=
      lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) h2) hlt
    linarith
  · rw [hρ, ← Matrix.mul_assoc]
    change M = A * Ai * M
    rw [hAAi, Matrix.one_mul]

end GlobalTheory.LocBasisBasR
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalBasisAndEmbeddedBasisDifferByUnimodularInteStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localBasis_and_embeddedBasis_differ_by_unimodular_integral : ∀ (D : D7) {p : ℕ} [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) (τ : D.what₂.Tau) {N : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (Bm : GL (Fin N) D.host.E) (M : Matrix (Fin N) (Fin N) ℂ_[p]), Formalism.L2.Forms.IsLocBasis p (L : Set (Fin N → D.host.E)) Bm → GL3Columns.BasR D lam τ L M → ∃ g : Matrix (Fin N) (Fin N) ℂ_[p], (∀ a b, ‖g a b‖ ≤ 1) ∧ ‖g.det‖ = 1 ∧ M = (Bm : Matrix (Fin N) (Fin N) D.host.E).map (TaylorLogMetric.tauEmb D lam τ) * g := by
  first | exact @GlobalTheory.LocBasisBasR.main | exact GlobalTheory.LocBasisBasR.main | (intros; apply GlobalTheory.LocBasisBasR.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemWeylLatticeIntegralSpanIffPadicFunction
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemWeylLatticeIntegralSpanIffPadicFunction
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.Mem.IntSpanDelW

open _root_.Formalism.L2.GlobalTheoryTheory.TraceIntegrality

variable {ι : Type} [Fintype ι] {n : ℕ}

def evM {p : ℕ} [Fact p.Prime] (P : MvPolynomial (ι × Fin n × Fin n) ℂ_[p]) :
    (ι → Matrix (Fin n) (Fin n) ℂ_[p]) → ℂ_[p] :=
  fun y => MvPolynomial.eval (fun k : ι × Fin n × Fin n => y k.1 k.2.1 k.2.2) P

theorem ten_int_map (R : Type) [CommRing R] (f : ι → MvPolynomial (Fin n × Fin n) ℤ) :
    Formalism.L2.Forms.ten (fun τ => MvPolynomial.map (Int.castRingHom R) (f τ)) =
      MvPolynomial.map (Int.castRingHom R) (Formalism.MainNotions.flipTwoThree.ten f) := by
  unfold Formalism.L2.Forms.ten Formalism.MainNotions.flipTwoThree.ten
  rw [map_prod]
  exact Finset.prod_congr rfl fun τ _ => (MvPolynomial.map_rename _ _ _).symm

theorem prod_eval_eq_evM {p : ℕ} [Fact p.Prime] (f : ι → MvPolynomial (Fin n × Fin n) ℤ)
    (y : ι → Matrix (Fin n) (Fin n) ℂ_[p]) :
    ∏ τ, MvPolynomial.eval (fun k : Fin n × Fin n => y τ k.1 k.2) (MvPolynomial.map (Int.castRingHom ℂ_[p]) (f τ)) =
      evM (MvPolynomial.map (Int.castRingHom ℂ_[p]) (Formalism.MainNotions.flipTwoThree.ten f)) y := by
  unfold evM Formalism.MainNotions.flipTwoThree.ten
  rw [map_prod, map_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [MvPolynomial.map_rename, MvPolynomial.eval_rename]
  rfl

theorem mem_vlIntSpan_iff {K : Type} [Field K] (σ : K →+* ℂ) (Pl : Rows.Places K) (w : Pl.Pl)
    (lam : ι → DomWeight n) (Z : ZBasis lam) (P : MvPolynomial (ι × Fin n × Fin n) ℂ) :
    P ∈ vlIntSpan σ Pl w lam ↔ ∃ c : Z.J0 → K, (∀ i, c i ∈ intW Pl w) ∧
      P = ∑ i, σ (c i) • MvPolynomial.map (Int.castRingHom ℂ) (Z.bZ i) := by
  constructor
  · intro hP
    induction hP using AddSubgroup.closure_induction with
    | mem P hP =>
      obtain ⟨r, f, hr, hf, rfl⟩ := hP
      have hx : Formalism.MainNotions.flipTwoThree.ten f ∈ Submodule.span ℤ (Set.range Z.bZ) := by
        rw [Z.span_eq]
        exact Submodule.subset_span ⟨f, hf, rfl⟩
      obtain ⟨z, hz⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hx
      refine ⟨fun i => r * (z i : K), fun i => mul_mem hr (intCast_mem _ _), ?_⟩
      set_option synthInstance.maxHeartbeats 100000 in
        rw [ten_int_map, ← hz, map_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_zsmul, map_mul, map_intCast, mul_smul, Int.cast_smul_eq_zsmul]
    | zero => exact ⟨0, fun _ => zero_mem _, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨c, hc, rfl⟩ := hx
      obtain ⟨c', hc', rfl⟩ := hy
      refine ⟨c + c', fun i => add_mem (hc i) (hc' i), ?_⟩
      simp [add_smul, Finset.sum_add_distrib]
    | neg x _ hx =>
      obtain ⟨c, hc, rfl⟩ := hx
      refine ⟨-c, fun i => neg_mem (hc i), ?_⟩
      simp [neg_smul, Finset.sum_neg_distrib]
  · rintro ⟨c, hc, rfl⟩
    have key : ∀ x ∈ Submodule.span ℤ {p | ∃ f : ι → MvPolynomial (Fin n × Fin n) ℤ,
        (∀ τ, f τ ∈ delSq ℤ n (lam τ)) ∧ p = Formalism.MainNotions.flipTwoThree.ten f}, ∀ r ∈ intW Pl w,
        σ r • MvPolynomial.map (Int.castRingHom ℂ) x ∈ vlIntSpan σ Pl w lam := by
      intro x hx r hr
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨f, hf, rfl⟩ := hx
        refine AddSubgroup.subset_closure ⟨r, f, hr, hf, ?_⟩
        rw [ten_int_map]
      | zero =>
        rw [map_zero, smul_zero]
        exact zero_mem _
      | add x y _ _ hx hy =>
        rw [map_add (f := _), smul_add]
        exact add_mem hx hy
      | smul a x _ hx =>
        rw [map_zsmul, smul_comm]
        exact zsmul_mem hx a
    refine sum_mem fun i _ => key _ ?_ _ (hc i)
    rw [← Z.span_eq]
    exact Submodule.subset_span ⟨i, rfl⟩

theorem mem_delW_iff {p : ℕ} [Fact p.Prime] (lam : ι → DomWeight n) (Z : ZBasis lam)
    (F : (ι → Matrix (Fin n) (Fin n) ℂ_[p]) → ℂ_[p]) :
    F ∈ WeylLatticeDuality.DelW p ι n (fun τ => (lam τ).natW) ↔ ∃ d : Z.J0 → ℂ_[p], (∀ i, ‖d i‖ ≤ 1) ∧
      F = fun y => ∑ i, d i * evM (MvPolynomial.map (Int.castRingHom ℂ_[p]) (Z.bZ i)) y := by
  constructor
  · intro hF
    induction hF using AddSubgroup.closure_induction with
    | mem F hF =>
      obtain ⟨r, f, hr, hf, rfl⟩ := hF
      have hx : Formalism.MainNotions.flipTwoThree.ten f ∈ Submodule.span ℤ (Set.range Z.bZ) := by
        rw [Z.span_eq]
        exact Submodule.subset_span ⟨f, fun τ => hf τ, rfl⟩
      obtain ⟨z, hz⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hx
      refine ⟨fun i => r * (z i : ℂ_[p]), fun i => ?_, ?_⟩
      · rw [norm_mul]
        exact mul_le_one₀ hr (norm_nonneg _) (IsUltrametricDist.norm_intCast_le_one _ _)
      · funext y
        rw [prod_eval_eq_evM, ← hz]
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [evM, map_sum, map_zsmul, zsmul_eq_mul, map_mul, map_intCast, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
    | zero => exact ⟨0, fun _ => by simp, by funext y; simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨d, hd, rfl⟩ := hx
      obtain ⟨d', hd', rfl⟩ := hy
      refine ⟨d + d', fun i => (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hd i) (hd' i)), ?_⟩
      funext v
      simp [add_mul, Finset.sum_add_distrib]
    | neg x _ hx =>
      obtain ⟨d, hd, rfl⟩ := hx
      refine ⟨-d, fun i => by rw [Pi.neg_apply, norm_neg]; exact hd i, ?_⟩
      funext v
      simp [neg_mul, Finset.sum_neg_distrib]
  · rintro ⟨d, hd, rfl⟩
    have key : ∀ x ∈ Submodule.span ℤ {p | ∃ f : ι → MvPolynomial (Fin n × Fin n) ℤ,
        (∀ τ, f τ ∈ delSq ℤ n (lam τ)) ∧ p = Formalism.MainNotions.flipTwoThree.ten f}, ∀ a : ℂ_[p], ‖a‖ ≤ 1 →
        (fun y => a * evM (MvPolynomial.map (Int.castRingHom ℂ_[p]) x) y) ∈
          WeylLatticeDuality.DelW p ι n (fun τ => (lam τ).natW) := by
      intro x hx a ha
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨f, hf, rfl⟩ := hx
        refine AddSubgroup.subset_closure ⟨a, f, ha, fun τ => hf τ, ?_⟩
        funext y
        rw [prod_eval_eq_evM]
      | zero =>
        have e : (fun y : ι → Matrix (Fin n) (Fin n) ℂ_[p] =>
            a * evM (MvPolynomial.map (Int.castRingHom ℂ_[p]) 0) y) = 0 := by
          funext y
          simp [evM]
        rw [e]
        exact zero_mem _
      | add x y _ _ hx hy =>
        have e : (fun v : ι → Matrix (Fin n) (Fin n) ℂ_[p] =>
            a * evM (MvPolynomial.map (Int.castRingHom ℂ_[p]) (x + y)) v) =
            (fun v => a * evM (MvPolynomial.map (Int.castRingHom ℂ_[p]) x) v) +
              (fun v => a * evM (MvPolynomial.map (Int.castRingHom ℂ_[p]) y) v) := by
          funext v
          simp [evM, mul_add]
        rw [e]
        exact add_mem hx hy
      | smul z x _ hx =>
        have e : (fun v : ι → Matrix (Fin n) (Fin n) ℂ_[p] =>
            a * evM (MvPolynomial.map (Int.castRingHom ℂ_[p]) (z • x)) v) =
            z • (fun v => a * evM (MvPolynomial.map (Int.castRingHom ℂ_[p]) x) v) := by
          funext v
          simp only [evM, map_zsmul, zsmul_eq_mul, map_mul, map_intCast, Pi.smul_apply, smul_eq_mul]
          ring
        rw [e]
        exact zsmul_mem hx z
    have e : (fun y => ∑ i, d i * evM (MvPolynomial.map (Int.castRingHom ℂ_[p]) (Z.bZ i)) y) =
        ∑ i, (fun y => d i * evM (MvPolynomial.map (Int.castRingHom ℂ_[p]) (Z.bZ i)) y) := by
      funext y
      simp [Finset.sum_apply]
    rw [e]
    refine sum_mem fun i _ => key _ ?_ _ (hd i)
    rw [← Z.span_eq]
    exact Submodule.subset_span ⟨i, rfl⟩

theorem map_mem_vlIntSpan_iff_delW : ∀ {K ι : Type} [Field K] [NumberField K] [Fintype ι] (σ : K →+* ℂ) (Pl : Rows.Places K) (w : Pl.Pl) {p : ℕ} [Fact p.Prime] (φ : K →+* ℂ_[p]), (∀ x, x ∈ intW Pl w ↔ ‖φ x‖ ≤ 1) → ∀ {n : ℕ} (lam : ι → DomWeight n) (G : MvPolynomial (ι × Fin n × Fin n) K), G ∈ Formalism.L2.DIV.VV K lam → (MvPolynomial.map σ G ∈ vlIntSpan σ Pl w lam ↔ (fun y : ι → Matrix (Fin n) (Fin n) ℂ_[p] => MvPolynomial.eval (fun k : ι × Fin n × Fin n => y k.1 k.2.1 k.2.2) (MvPolynomial.map φ G)) ∈ WeylLatticeDuality.DelW p ι n (fun τ => (lam τ).natW)) := by
  classical
  intro K ι _ _ _ σ Pl w p _ φ hφ n lam G hG
  choose r e hr using fun τ => exists_weylBasis n (lam τ).natW (Formalism.L2.Col.natW_anti (lam τ))
  set Z := zOf lam e with hZ
  have hG' : G ∈ Submodule.span K (Set.range fun i => MvPolynomial.map (Int.castRingHom K) (Z.bZ i)) := by
    rw [Z.span_F K]
    exact hG
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hG'
  have hmap : ∀ (L : Type) [Field L] (s : K →+* L), MvPolynomial.map s G =
      ∑ i, s (c i) • MvPolynomial.map (Int.castRingHom L) (Z.bZ i) := by
    intro L _ s
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hc, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, MvPolynomial.map_map, ← MvPolynomial.smul_eq_C_mul]
    have h : s.comp (Int.castRingHom K) = Int.castRingHom L := RingHom.ext_int _ _
    rw [h]
  show _ ↔ evM (MvPolynomial.map φ G) ∈ _
  rw [mem_vlIntSpan_iff σ Pl w lam Z, mem_delW_iff lam Z]
  constructor
  · rintro ⟨c', hc', he⟩
    have hcc : c = c' := by
      rw [hmap ℂ σ] at he
      have h0 : ∑ i, (σ (c i) - σ (c' i)) • MvPolynomial.map (Int.castRingHom ℂ) (Z.bZ i) = 0 := by
        simp only [sub_smul, Finset.sum_sub_distrib, he, sub_self]
      funext i
      exact σ.injective (sub_eq_zero.1 (Fintype.linearIndependent_iff.1 (Z.li ℂ) _ h0 i))
    subst hcc
    refine ⟨fun i => φ (c i), fun i => (hφ _).1 (hc' i), ?_⟩
    funext y
    rw [hmap ℂ_[p] φ]
    simp [evM, MvPolynomial.smul_eval]
  · rintro ⟨d, hd, he⟩
    have hpoly : MvPolynomial.map φ G = ∑ i, d i • MvPolynomial.map (Int.castRingHom ℂ_[p]) (Z.bZ i) := by
      apply MvPolynomial.funext
      intro x
      have h1 := congrFun he (fun τ a b => x (τ, a, b))
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      simp only [MvPolynomial.smul_eval]
      exact h1
    rw [hmap ℂ_[p] φ] at hpoly
    have hcd : ∀ i, φ (c i) = d i := by
      have h0 : ∑ i, (φ (c i) - d i) • MvPolynomial.map (Int.castRingHom ℂ_[p]) (Z.bZ i) = 0 := by
        simp only [sub_smul, Finset.sum_sub_distrib, hpoly, sub_self]
      exact fun i => sub_eq_zero.1 (Fintype.linearIndependent_iff.1 (Z.li ℂ_[p]) _ h0 i)
    exact ⟨c, fun i => (hφ _).2 ((hcd i).symm ▸ hd i), hmap ℂ σ⟩

end GlobalTheory.Mem.IntSpanDelW
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemWeylLatticeIntegralSpanIffPadicFunctionStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_weylLatticeIntegralSpan_iff_padic_function : ∀ {K ι : Type} [Field K] [NumberField K] [Fintype ι] (σ : K →+* ℂ) (Pl : Rows.Places K) (w : Pl.Pl) {p : ℕ} [Fact p.Prime] (φ : K →+* ℂ_[p]), (∀ x, x ∈ intW Pl w ↔ ‖φ x‖ ≤ 1) → ∀ {n : ℕ} (lam : ι → DomWeight n) (G : MvPolynomial (ι × Fin n × Fin n) K), G ∈ Formalism.L2.DIV.VV K lam → (MvPolynomial.map σ G ∈ vlIntSpan σ Pl w lam ↔ (fun y : ι → Matrix (Fin n) (Fin n) ℂ_[p] => MvPolynomial.eval (fun k : ι × Fin n × Fin n => y k.1 k.2.1 k.2.2) (MvPolynomial.map φ G)) ∈ WeylLatticeDuality.DelW p ι n (fun τ => (lam τ).natW)) := by
  first | exact @GlobalTheory.Mem.IntSpanDelW.map_mem_vlIntSpan_iff_delW | exact GlobalTheory.Mem.IntSpanDelW.map_mem_vlIntSpan_iff_delW | (intros; apply GlobalTheory.Mem.IntSpanDelW.map_mem_vlIntSpan_iff_delW <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemLocalizedWeylLatticeIffDetTwistedEval
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.LocDictT

theorem eval_map_actP {K S ι : Type} [Field K] [CommRing S] [Fintype ι] {n : ℕ} (φ : K →+* S)
    (lam : ι → DomWeight n) (g : ι → GL (Fin n) K) (P : Pol K ι n) (y : ι → Matrix (Fin n) (Fin n) S) :
    MvPolynomial.eval (fun k : ι × Fin n × Fin n => y k.1 k.2.1 k.2.2) (MvPolynomial.map φ (actP lam g P)) =
      φ (detTwK lam g) * MvPolynomial.eval (fun k : ι × Fin n × Fin n =>
        (((((g k.1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ).map φ) * y k.1) k.2.1 k.2.2) (MvPolynomial.map φ P) := by
  have key : ((MvPolynomial.eval (fun k : ι × Fin n × Fin n => y k.1 k.2.1 k.2.2)).comp
      ((MvPolynomial.map φ).comp (trAct g).toRingHom)) =
      (MvPolynomial.eval (fun k : ι × Fin n × Fin n =>
        (((((g k.1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ).map φ) * y k.1) k.2.1 k.2.2)).comp (MvPolynomial.map φ) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [trAct]
    · intro v
      simp [trAct, Formalism.GradedWeylDivisibility.blockAct, Matrix.mul_apply]
  unfold actP
  rw [LinearMap.smul_apply, MvPolynomial.smul_eq_C_mul, map_mul, map_mul, MvPolynomial.map_C, MvPolynomial.eval_C]
  congr 1
  exact RingHom.congr_fun key P

theorem invTr_bc_inv_transpose {E K : Type} [Field E] [Field K] {n : ℕ} (φ : E →+* K) (Bm : GL (Fin n) E) :
    ((((inside₂ K n (bc φ Bm))⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))ᵀ = (Bm : Matrix (Fin n) (Fin n) E).map φ := by
  rfl

theorem iL_emb {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l))
    (Pl : Examples₂.EntPl (I.rec7 l Z)) (w : (I.rec7 l Z).what₂.places.Pl) (τ : (I.rec7 l Z).what₂.Tau) (x : B.fields.E) :
    Pl.iL w (B.fields.emb τ x) = TaylorLogMetric.tauEmb (I.rec7 l Z) (Pl.lam w) τ x := by
  refine (Pl.iL_lam w (B.fields.emb τ x)).trans ?_
  have h : TaylorLogMetric.embT (I.rec7 l Z) τ x = B.embLL (B.fields.emb τ x) := by
    rw [GlobalTheory.Pdv.FormsStd.embT_eq I l Z]
    rfl
  unfold TaylorLogMetric.tauEmb
  rw [h]
  rfl

theorem detPow_map {K S : Type} [Field K] [Field S] {n : ℕ} (φ : K →+* S) (g : GL (Fin n) K) (e : ℤ) :
    φ (detPow K n g e) = ((((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ).map φ).det ^ e := by
  unfold detPow
  rw [Units.val_zpow_eq_zpow_val, map_zpow₀]
  congr 1
  show φ (g : Matrix (Fin n) (Fin n) K).det = _
  rw [RingHom.map_det, RingHom.mapMatrix_apply, ← Matrix.det_transpose]
  rfl

theorem atBas_apply {D : D7} (P : Examples₂.EntPl D) (w : D.what₂.places.Pl) {N : ℕ}
    (M : D.what₂.Tau → Matrix (Fin N) (Fin N) (Cw D w)) (Q : MvPolynomial (GL3Theta.FrV D N) D.what₂.LL) (y : FrP D w N) :
    atBas P w M Q y = MvPolynomial.eval (fun k : GL3Theta.FrV D N => (M k.1 * y k.1) k.2.1 k.2.2) (MvPolynomial.map (P.iL w) Q) := rfl

theorem final_eq {S T LL : Type} [Field S] [CommRing LL] [Fintype T] {N : ℕ} (φ : LL →+* S)
    (P : MvPolynomial (T × Fin N × Fin N) LL) (A g M y : T → Matrix (Fin N) (Fin N) S) (e : T → ℤ)
    (hM : ∀ τ, M τ = A τ * g τ) :
    (∏ τ, (g τ).det ^ e τ) * ((∏ τ, (A τ).det ^ e τ) *
      MvPolynomial.eval (fun k : T × Fin N × Fin N => (A k.1 * (g k.1 * y k.1)) k.2.1 k.2.2) (MvPolynomial.map φ P)) =
    (∏ τ, (M τ).det ^ e τ) * MvPolynomial.eval (fun k : T × Fin N × Fin N => (M k.1 * y k.1) k.2.1 k.2.2) (MvPolynomial.map φ P) := by
  simp only [hM, Matrix.det_mul, mul_zpow, Finset.prod_mul_distrib, Matrix.mul_assoc]
  ring

theorem detTwisted_polyEval_mul_factor_eq_of_eq {S T LL : Type} [Field S] [CommRing LL] [Fintype T] {N : ℕ} (φ : LL →+* S)
    (P : MvPolynomial (T × Fin N × Fin N) LL) (A G g M y : T → Matrix (Fin N) (Fin N) S) (e e' : T → ℤ)
    (hA : ∀ τ, G τ = A τ) (he : ∀ τ, e' τ = e τ) (hM : ∀ τ, M τ = A τ * g τ) :
    (∏ τ, (g τ).det ^ e τ) * ((∏ τ, (A τ).det ^ e' τ) *
      MvPolynomial.eval (fun k : T × Fin N × Fin N => (G k.1 * (g k.1 * y k.1)) k.2.1 k.2.2) (MvPolynomial.map φ P)) =
    (∏ τ, (M τ).det ^ e τ) * MvPolynomial.eval (fun k : T × Fin N × Fin N => (M k.1 * y k.1) k.2.1 k.2.2) (MvPolynomial.map φ P) := by
  have h1 : G = A := funext hA
  have h2 : e' = e := funext he
  subst h1 h2
  exact final_eq φ P G g M y e' hM


set_option maxHeartbeats 1000000 in
theorem mem_locW_iff_delW : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (l0 : I.Law0 l) (Y : DivX (I.rec7 l Z)) (O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)) (Pl : Examples₂.EntPl (I.rec7 l Z)) (Bs : PlaceMatrixFamily (I.rec7 l Z)), I.QpIs Y.Qp → I.StdO l Z Y.Qp O → BasOk Pl O Bs → (∀ u a w, LevFree Y u a w → ∀ i, i ≤ B.R.m → ∀ c τ j k, ∃ x : (I.rec7 l Z).what₂.LL, Bs u a w i c τ j k = Pl.iL w x) → (∀ u a i, i < B.R.m → UnfIsAll (O u a) i) → ColIn.JetsIn I → ∀ (u : B.Word) (μ : I.ι) (w : (I.rec7 l Z).what₂.places.Pl), LevFree Y u μ w → ∀ i, i < (I.rec7 l Z).R.m → ∀ (c' : (I.stp u μ (i + 1)).Cl) (z : VV B.LL (lamT (B.hcW u) (i + 1))), (z ∈ locW B.places w (delAtr B.fields.emb (lamT (B.hcW u) (i + 1)) ((I.stp u μ (i + 1)).Lsh c'.1 ((I.stp u μ (i + 1)).rep c'))) ↔ (fun y => (∏ τ, (Bs u μ w (i + 1) c' τ).det ^ (-((I.rec7 l Z).chTw u μ).sDiv i τ)) * atBas Pl w (Bs u μ w (i + 1) c') (show MvPolynomial (GL3Theta.FrV (I.rec7 l Z) ((I.rec7 l Z).R.N (i + 1))) (I.rec7 l Z).what₂.LL from z.1) y) ∈ WeylLatticeDuality.DelW ((I.rec7 l Z).what₂.places.resChar w) (I.rec7 l Z).what₂.Tau ((I.rec7 l Z).R.N (i + 1)) (extNu ((I.rec7 l Z).R.N (i + 1)) (nuT (I.rec7 l Z) u i))) := by
  intro B X I hOk hPins l Z l0 Y O Pl Bs hQp hStd hBas hEnt hUnf hJets u μ w hLF i hi c' z
  obtain ⟨hlat, hloc⟩ := GlobalTheory.T.dualLattice_class_localization_eq_unimodularCompanion I hOk hPins l Z Y u μ w hLF (i + 1) hi c'
  haveI : Fact (B.places.resChar w).Prime := ⟨B.places.resChar_prime w⟩
  have hspanN : Submodule.span B.fields.E
      (((I.stp u μ (i + 1)).rep c').1.1.deco.1.N : Set (Fin (B.R.N (i + 1)) → B.fields.E)) = ⊤ := by
    open Formalism.HermitianLatticesTheory Module in
    let L := ((I.stp u μ (i + 1)).rep c').1.1.deco.1.N
    have hL := ((I.stp u μ (i + 1)).rep c').1.1.deco.2.lat
    have hu : IsUnimodular (Formalism.L2.Col.hStd B.fields.E (B.R.N (i + 1))) L :=
      ((I.stp u μ (i + 1)).rep c').1.1.deco.2.uni
    let W := Submodule.span B.fields.E (L : Set (Sp B.fields.E (B.R.N (i + 1))))
    change W = ⊤
    by_contra h
    let e : Sp B.fields.E (B.R.N (i + 1)) ≃ₗ⋆[B.fields.E] Sp B.fields.E (B.R.N (i + 1)) := starLinearEquiv B.fields.E
    let g : Sp B.fields.E (B.R.N (i + 1)) →ₗ[B.fields.E] Module.Dual B.fields.E W :=
      (LinearMap.domRestrict' W).comp ((Formalism.L2.Col.hStd B.fields.E (B.R.N (i + 1))).comp e.toLinearMap)
    have hdim : finrank B.fields.E (Module.Dual B.fields.E W) <
        finrank B.fields.E (Sp B.fields.E (B.R.N (i + 1))) := by
      rw [Subspace.dual_finrank_eq]
      exact Submodule.finrank_lt h
    obtain ⟨x, hx, hx₀⟩ :=
      Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := g) hdim)
    have hsmul (a : B.fields.E) : a • e x ∈ L := by
      rw [← hu, dualBasic_mem_dual]
      intro y hy
      apply hStd_mem_one_symm
      have hxy : Formalism.L2.Col.hStd B.fields.E (B.R.N (i + 1)) (e x) y = 0 :=
        congrArg (fun f : Module.Dual B.fields.E W => f ⟨y, Submodule.subset_span hy⟩)
          (LinearMap.mem_ker.mp hx)
      simp [LinearMap.map_smulₛₗ, LinearMap.smul_apply, hxy]
    let j : B.fields.E →ₗ[𝓞 B.fields.E] L :=
      ((LinearMap.toSpanSingleton B.fields.E _ (e x)).restrictScalars (𝓞 B.fields.E)).codRestrict L hsmul
    let : Module.Finite (𝓞 B.fields.E) L := Module.Finite.iff_fg.mpr hL.fg
    let : Module.Finite (𝓞 B.fields.E) B.fields.E := Module.Finite.of_injective j fun a b hab =>
      smul_left_injective B.fields.E (fun hz => hx₀ (e.map_eq_zero_iff.mp hz)) (congrArg Subtype.val hab)
    exact RingOfIntegers.not_isField B.fields.E
      (isField_of_isIntegral_of_isField (IsFractionRing.injective (𝓞 B.fields.E) B.fields.E) (Field.toIsField B.fields.E))
  have hfull : Submodule.IsFullLattice B.fields.E
      ((I.stp u μ (i + 1)).Lsh c'.1 ((I.stp u μ (i + 1)).rep c')) := by
    letI := hlat
    refine ⟨?_⟩
    apply top_unique
    rw [← hspanN]
    apply Submodule.span_le.mpr
    intro x hx
    obtain ⟨s, hs, hmem⟩ := (hloc x).mpr ⟨1, by simpa using ((I.rec7 l Z).what₂.places.resChar_prime w).ne_one, by simpa using hx⟩
    have hs0 : (s : B.fields.E) ≠ 0 := by
      intro hz
      have : s = 0 := Nat.cast_eq_zero.mp hz
      subst s
      exact hs (dvd_zero _)
    have hm : (s : B.fields.E) • x ∈ Submodule.span B.fields.E
        (((I.stp u μ (i + 1)).Lsh c'.1 ((I.stp u μ (i + 1)).rep c')) : Set _) := Submodule.subset_span hmem
    have := (Submodule.span B.fields.E
      (((I.stp u μ (i + 1)).Lsh c'.1 ((I.stp u μ (i + 1)).rep c')) : Set (Fin (B.R.N (i + 1)) → B.fields.E))).smul_mem (s : B.fields.E)⁻¹ hm
    simpa [smul_smul, hs0] using this
  obtain ⟨Bm, hBm0⟩ := Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.LocB.exists_isLocBasis (B.places.resChar w) B.fields.E _
    ((I.stp u μ (i + 1)).rep c').1.1.deco.2.lat.fg hspanN
  have hBm : Formalism.L2.Forms.IsLocBasis (B.places.resChar w) (((I.stp u μ (i + 1)).Lsh c'.1 ((I.stp u μ (i + 1)).rep c')) : Set _) Bm := by
    intro x
    exact (hloc x).trans (hBm0 x)
  have hBmN : Formalism.L2.Forms.IsLocBasis (B.places.resChar w) (((O u μ).lat (i + 1) c').1 : Set (Fin ((I.rec7 l Z).R.N (i + 1)) → (I.rec7 l Z).host.E)) Bm := by
    intro x
    rw [hStd.lat u μ (i + 1) c']
    exact (hloc x).symm.trans (hBm x)
  rw [GlobalTheory.WeylLocOnePlace.mem_locW_delAtr_iff B.fields.emb B.embLL B.places (I.rec7 l Z).plEq
    (fun w x hx => (I.rec7 l Z).val_eq w x hx)
    (lamT (B.hcW u) (i + 1)) (lamT (B.hcW u) (i + 1)) (fun _ => rfl) _ hfull w Bm hBm z]
  rw [GlobalTheory.T.mem_weylLatticeIntegralSpan_iff_padic_function B.embLL B.places w (Pl.iL w) (Pl.iL_int w) (lamT (B.hcW u) (i + 1)) _
    (((rhoVr B.fields.emb (lamT (B.hcW u) (i + 1))) Bm⁻¹) z).2]
  obtain ⟨n, hw, hn, hnat, hds⟩ := GlobalTheory.KerWtStep.trueWt_step (I.rec7 l Z) u _ _ _ ((I.tw l l0 Z).fm u μ) i hi
  have hlam := GlobalTheory.Pdv.FormsStd.lamTG_eq I l Z l0 u μ
  have e : (fun τ => (lamT (B.hcW u) (i + 1) τ).natW) = extNu ((I.rec7 l Z).R.N (i + 1)) (nuT (I.rec7 l Z) u i) := by
    funext τ r
    rw [← hlam]
    refine (hnat τ r).trans ?_
    congr 1
    funext τ' r'
    exact hw τ' r'
  have eds : ∀ τ, (lamT (B.hcW u) (i + 1) τ).detShift = -((I.rec7 l Z).chTw u μ).sDiv i τ := fun τ => by
    rw [← hlam]
    exact hds τ
  rw [e]
  choose g hg1 hg2 hg3 using fun τ => GlobalTheory.T.localBasis_and_embeddedBasis_differ_by_unimodular_integral (I.rec7 l Z) (Pl.lam w) τ _ Bm (Bs u μ w (i + 1) c' τ) hBmN
    (hBas u μ w (i + 1) hi c' τ)
  refine (GlobalTheory.T.weyl_lattice_dual_invariant_unit_iff _ _ _ _ g (∏ τ, (g τ).det ^ (-((I.rec7 l Z).chTw u μ).sDiv i τ)) hg1 hg2 ?_ _).trans ?_
  · rw [norm_prod]
    exact Finset.prod_eq_one fun τ _ => by rw [norm_zpow, hg2, _root_.one_zpow]
  · apply iff_of_eq
    congr 1
    funext y
    have hM : ∀ τ, ((((vlBdF B.fields.emb fun _ => Bm)⁻¹ τ : GL (Fin (B.R.N (i + 1))) B.LL) :
        Matrix (Fin (B.R.N (i + 1))) (Fin (B.R.N (i + 1))) B.LL)ᵀ).map (Pl.iL w) =
        (Bm : Matrix (Fin (B.R.N (i + 1))) (Fin (B.R.N (i + 1))) B.fields.E).map (TaylorLogMetric.tauEmb (I.rec7 l Z) (Pl.lam w) τ) := by
      intro τ
      rw [show (vlBdF B.fields.emb fun _ => Bm)⁻¹ τ = (inside₂ _ _ (bc (B.fields.emb τ) Bm))⁻¹ from rfl,
        invTr_bc_inv_transpose]
      ext a b
      exact iL_emb I l Z Pl w τ _
    have hdet : Pl.iL w (detTwK (lamT (B.hcW u) (i + 1)) (vlBdF B.fields.emb fun _ => Bm)⁻¹) =
        ∏ τ, ((Bm : Matrix (Fin (B.R.N (i + 1))) (Fin (B.R.N (i + 1))) B.fields.E).map
          (TaylorLogMetric.tauEmb (I.rec7 l Z) (Pl.lam w) τ)).det ^ (lamT (B.hcW u) (i + 1) τ).detShift := by
      unfold detTwK
      rw [map_prod]
      refine Finset.prod_congr rfl fun τ _ => ?_
      rw [detPow_map]
      exact congrArg (fun M => Matrix.det M ^ (lamT (B.hcW u) (i + 1) τ).detShift) (hM τ)
    beta_reduce
    rw [GlobalTheory.WeylLocOnePlace.rhoVr_inv_coe]
    have hev := eval_map_actP (Pl.iL w) (lamT (B.hcW u) (i + 1)) (vlBdF B.fields.emb fun _ => Bm)⁻¹ z.1 (fun τ => g τ * y τ)
    beta_reduce at hev
    erw [hev]
    erw [atBas_apply, hdet]
    exact detTwisted_polyEval_mul_factor_eq_of_eq (Pl.iL w) z.1
      (fun τ => (Bm : Matrix (Fin (B.R.N (i + 1))) (Fin (B.R.N (i + 1))) B.fields.E).map (TaylorLogMetric.tauEmb (I.rec7 l Z) (Pl.lam w) τ))
      (fun τ => ((((vlBdF B.fields.emb fun _ => Bm)⁻¹ τ : GL (Fin (B.R.N (i + 1))) B.LL) :
        Matrix (Fin (B.R.N (i + 1))) (Fin (B.R.N (i + 1))) B.LL)ᵀ).map (Pl.iL w))
      g (Bs u μ w (i + 1) c') y (fun τ => -((I.rec7 l Z).chTw u μ).sDiv i τ)
      (fun τ => (lamT (B.hcW u) (i + 1) τ).detShift) hM eds hg3

end GlobalTheory.Mem.LocDictT
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemLocalizedWeylLatticeIffDetTwistedEvalStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_localizedWeylLattice_iff_detTwisted_eval : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (l0 : I.Law0 l) (Y : DivX (I.rec7 l Z)) (O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)) (Pl : Examples₂.EntPl (I.rec7 l Z)) (Bs : PlaceMatrixFamily (I.rec7 l Z)), I.QpIs Y.Qp → I.StdO l Z Y.Qp O → BasOk Pl O Bs → (∀ u a w, LevFree Y u a w → ∀ i, i ≤ B.R.m → ∀ c τ j k, ∃ x : (I.rec7 l Z).what₂.LL, Bs u a w i c τ j k = Pl.iL w x) → (∀ u a i, i < B.R.m → UnfIsAll (O u a) i) → ColIn.JetsIn I → ∀ (u : B.Word) (μ : I.ι) (w : (I.rec7 l Z).what₂.places.Pl), LevFree Y u μ w → ∀ i, i < (I.rec7 l Z).R.m → ∀ (c' : (I.stp u μ (i + 1)).Cl) (z : VV B.LL (lamT (B.hcW u) (i + 1))), (z ∈ locW B.places w (delAtr B.fields.emb (lamT (B.hcW u) (i + 1)) ((I.stp u μ (i + 1)).Lsh c'.1 ((I.stp u μ (i + 1)).rep c'))) ↔ (fun y => (∏ τ, (Bs u μ w (i + 1) c' τ).det ^ (-((I.rec7 l Z).chTw u μ).sDiv i τ)) * atBas Pl w (Bs u μ w (i + 1) c') (show MvPolynomial (GL3Theta.FrV (I.rec7 l Z) ((I.rec7 l Z).R.N (i + 1))) (I.rec7 l Z).what₂.LL from z.1) y) ∈ WeylLatticeDuality.DelW ((I.rec7 l Z).what₂.places.resChar w) (I.rec7 l Z).what₂.Tau ((I.rec7 l Z).R.N (i + 1)) (extNu ((I.rec7 l Z).R.N (i + 1)) (nuT (I.rec7 l Z) u i))) := by
  first | exact @GlobalTheory.Mem.LocDictT.mem_locW_iff_delW | exact GlobalTheory.Mem.LocDictT.mem_locW_iff_delW | (intros; apply GlobalTheory.Mem.LocDictT.mem_locW_iff_delW <;> assumption)
end
