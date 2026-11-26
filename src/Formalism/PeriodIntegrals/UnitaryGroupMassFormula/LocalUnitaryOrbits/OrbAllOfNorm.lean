module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.OrbAllOfOrthoB

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.OrbAllOfUnitV
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.GenSmulMem
noncomputable section

namespace PI.OmLocU.Orb

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : ℕ} (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

theorem gen_mem (a : 𝓞 E) : inclR (F := F) (Fv F v) (a : E) ∈ OEv (E := E) v :=
  Submodule.subset_span ⟨a, Set.mem_univ _, rfl⟩

theorem gen_mul_mem (a : 𝓞 E) (y : Fv F v ⊗[F] E) (hy : y ∈ OEv (E := E) v) :
    inclR (F := F) (Fv F v) (a : E) * y ∈ OEv (E := E) v := by
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, -, rfl⟩ := hx
    rw [← map_mul]
    exact_mod_cast gen_mem v (a * b)
  | zero => rw [mul_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [mul_add]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ r hx

theorem oSub : OSub (E := E) v := by
  refine ⟨?_, ?_⟩
  · have := gen_mem (E := E) v 1
    simpa using this
  · intro x hx y hy
    induction hx using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨b, -, rfl⟩ := hz
      exact gen_mul_mem v b y hy
    | zero => rw [zero_mul]; exact Submodule.zero_mem _
    | add x x' _ _ hx hx' => rw [add_mul]; exact Submodule.add_mem _ hx hx'
    | smul r x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ r hx

theorem gen_smul_mem (hL : ∃ L : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E L ∧ (L : Set (Fin n → E)) = Λ)
    (a : 𝓞 E) (x : Fin n → Fv F v ⊗[F] E) (hx : x ∈ latLoc (E := E) v Λ) :
    inclR (F := F) (Fv F v) (a : E) • x ∈ latLoc (E := E) v Λ := by
  obtain ⟨L, -, rfl⟩ := hL
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, hl, rfl⟩ := hx
    have hal : a • l ∈ L := L.smul_mem a hl
    have : inclR (F := F) (Fv F v) (a : E) • ratV (F := F) (Fv F v) l = ratV (F := F) (Fv F v) (a • l) := by
      funext i
      simp only [ratV, Pi.smul_apply, smul_eq_mul, ← map_mul]
      rfl
    rw [this]
    exact Submodule.subset_span ⟨_, hal, rfl⟩
  | zero => rw [smul_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ r hx

theorem oSmul : OSmul v Λ := by
  intro hL c hc x hx
  induction hc using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨b, -, rfl⟩ := hz
    exact gen_smul_mem v Λ hL b x hx
  | zero => rw [zero_smul]; exact Submodule.zero_mem _
  | add c c' _ _ hc hc' => rw [add_smul]; exact Submodule.add_mem _ hc hc'
  | smul r c _ hc => rw [smul_assoc]; exact Submodule.smul_mem _ r hc

end PI.OmLocU.Orb
end
end

noncomputable section

namespace PI.OmLocU.Orb

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

def PerpG {ι : Type} (X : ι → Fin n → Fv F v ⊗[F] E) : Set (Fin n → Fv F v ⊗[F] E) :=
  {w | w ∈ latLoc (E := E) v Λ ∧ ∀ i, hR (Fv F v) σ J (X i) w = 0}

def gramG {ι : Type} (X : ι → Fin n → Fv F v ⊗[F] E) : Matrix ι ι (Fv F v ⊗[F] E) :=
  fun a b => hR (Fv F v) σ J (X a) (X b)

def UniG {ι : Type} [Fintype ι] [DecidableEq ι] (X : ι → Fin n → Fv F v ⊗[F] E) : Prop :=
  ∃ w ∈ OEv (E := E) v, (gramG σ J v X).det * w = 1

def UnitV : Prop :=
  StdHyp σ J ψ → (∃ L : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E L ∧ (L : Set (Fin n → E)) = Λ) →
    IsSDLoc σ J v Λ → UnramAt (E := E) v →
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (X : ι → Fin n → Fv F v ⊗[F] E), (∀ i, X i ∈ latLoc (E := E) v Λ) →
      UniG σ J v X → Fintype.card ι < n →
      ∃ p ∈ PerpG σ J v Λ X, hR (Fv F v) σ J p p = 1 ∧ ∀ i, hR (Fv F v) σ J p (X i) = 0

theorem hR_smul_right (x y : Fin n → Fv F v ⊗[F] E) (c : Fv F v ⊗[F] E) :
    hR (Fv F v) σ J x (c • y) = c * hR (Fv F v) σ J x y := by
  simp only [hR, hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem perp_full {ι : Type} [Fintype ι] [DecidableEq ι] (X : ι → Fin n → Fv F v ⊗[F] E)
    (hU : UniG σ J v X) (hc : Fintype.card ι = n) (w : Fin n → Fv F v ⊗[F] E)
    (hw : ∀ i, hR (Fv F v) σ J (X i) w = 0) : w = 0 := by
  obtain ⟨u, -, hu⟩ := hU
  have hG : IsUnit (gramG σ J v X).det := ⟨⟨_, u, hu, by rw [mul_comm]; exact hu⟩, rfl⟩
  let eq : ι ≃ Fin n := Fintype.equivFinOfCardEq hc
  let M : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) := Matrix.of fun i m => X (eq.symm m) i
  have hA : cT (sigR (Fv F v) σ) M * JR (Fv F v) J * M = (gramG σ J v X).submatrix eq.symm eq.symm := by
    ext p q
    simp only [cT, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
    simp only [M, Matrix.of_apply, gramG, hR, hform, Matrix.submatrix_apply]
    exact Finset.sum_comm
  have hdA : IsUnit (cT (sigR (Fv F v) σ) M * JR (Fv F v) J).det := by
    have h1 := congrArg det hA
    rw [det_submatrix_equiv_self, det_mul] at h1
    rw [← h1] at hG
    exact isUnit_of_mul_isUnit_left hG
  have hB : (cT (sigR (Fv F v) σ) M * JR (Fv F v) J) *ᵥ w = 0 := by
    funext m
    have h2 := hw (eq.symm m)
    simp only [hR, hform] at h2
    simp only [Matrix.mulVec, dotProduct, cT, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Pi.zero_apply, Finset.sum_mul]
    simp only [M, Matrix.of_apply]
    rw [Finset.sum_comm]
    exact h2
  have h3 := congrArg (fun y => (cT (sigR (Fv F v) σ) M * JR (Fv F v) J)⁻¹ *ᵥ y) hB
  simpa [mulVec_mulVec, nonsing_inv_mul _ hdA] using h3

theorem orthoGen (hU : UnitV σ J ψ v Λ) (hstd : StdHyp σ J ψ)
    (hL : ∃ L : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E L ∧ (L : Set (Fin n → E)) = Λ)
    (hsd : IsSDLoc σ J v Λ) (hun : UnramAt (E := E) v) :
    ∀ (k : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (X : ι → Fin n → Fv F v ⊗[F] E),
      Fintype.card ι + k = n → (∀ i, X i ∈ latLoc (E := E) v Λ) → UniG σ J v X →
      ∃ e : Fin k → Fin n → Fv F v ⊗[F] E, (∀ j, e j ∈ PerpG σ J v Λ X) ∧
        (∀ i j, hR (Fv F v) σ J (e j) (X i) = 0) ∧ gramR (Fv F v) σ J e = 1 ∧
        ∀ w ∈ PerpG σ J v Λ X, ∃ d : Fin k → Fv F v ⊗[F] E, (∀ j, d j ∈ OEv (E := E) v) ∧
          w = ∑ j, d j • e j := by
  intro k
  induction k with
  | zero =>
    intro ι _ _ X hc hX hUX
    refine ⟨Fin.elim0, fun j => j.elim0, fun i j => j.elim0, ?_, ?_⟩
    · ext i
      exact i.elim0
    · intro w hw
      refine ⟨Fin.elim0, fun j => j.elim0, ?_⟩
      rw [Finset.univ_eq_empty, Finset.sum_empty]
      exact perp_full σ J v X hUX (by omega) w hw.2
  | succ k ih =>
    intro ι _ _ X hc hX hUX
    obtain ⟨p, hp, hpp, hpX⟩ := hU hstd hL hsd hun ι X hX hUX (by omega)
    let X' : ι ⊕ Unit → Fin n → Fv F v ⊗[F] E := Sum.elim X (fun _ => p)
    have hG' : gramG σ J v X' = Matrix.fromBlocks (gramG σ J v X) 0 0 1 := by
      ext s t
      rcases s with i | ⟨⟩ <;> rcases t with j | ⟨⟩
      · rfl
      · simp [gramG, X', hp.2 i]
      · simp [gramG, X', hpX j]
      · simp [gramG, X', hpp]
    have hU' : UniG σ J v X' := by
      obtain ⟨u, hu0, hu⟩ := hUX
      refine ⟨u, hu0, ?_⟩
      rw [hG', det_fromBlocks_zero₂₁, det_one, mul_one, hu]
    have hX' : ∀ s, X' s ∈ latLoc (E := E) v Λ := by
      rintro (i | ⟨⟩)
      · exact hX i
      · exact hp.1
    obtain ⟨e', he'P, he'X, he'e, he'span⟩ :=
      ih (ι ⊕ Unit) X' (by rw [Fintype.card_sum, Fintype.card_unit]; omega) hX' hU'
    refine ⟨Fin.cons p e', ?_, ?_, ?_, ?_⟩
    · intro j
      refine Fin.cases hp (fun j => ⟨(he'P j).1, fun i => (he'P j).2 (Sum.inl i)⟩) j
    · intro i j
      refine Fin.cases (hpX i) (fun j => he'X (Sum.inl i) j) j
    · ext i j
      refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
      · simpa [gramR] using hpp
      · have h1 : hR (Fv F v) σ J p (e' j) = 0 := (he'P j).2 (Sum.inr ())
        simpa [gramR, Matrix.one_apply, (Fin.succ_ne_zero j).symm] using h1
      · have h1 : hR (Fv F v) σ J (e' i) p = 0 := he'X (Sum.inr ()) i
        simpa [gramR, Matrix.one_apply, Fin.succ_ne_zero] using h1
      · simpa [gramR, Matrix.one_apply] using congrFun (congrFun he'e i) j
    · intro w hw
      set c := hR (Fv F v) σ J p w with hcdef
      have hc0 : c ∈ OEv (E := E) v := (hsd w).1 hw.1 p hp.1
      have hw' : w - c • p ∈ PerpG σ J v Λ X' := by
        refine ⟨Submodule.sub_mem _ hw.1 (oSmul v Λ hL c hc0 p hp.1), ?_⟩
        rintro (i | ⟨⟩)
        · show hR (Fv F v) σ J (X i) (w - c • p) = 0
          rw [hR_sub_right, hR_smul_right, hw.2 i, hp.2 i, mul_zero, sub_zero]
        · show hR (Fv F v) σ J p (w - c • p) = 0
          rw [hR_sub_right, hR_smul_right, hpp, mul_one, ← hcdef, sub_self]
      obtain ⟨d', hd'O, hd'⟩ := he'span _ hw'
      refine ⟨Fin.cons c d', fun j => Fin.cases hc0 hd'O j, ?_⟩
      rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      rw [← hd']
      abel

theorem orthoB_of (a : ℕ) (Y : TupV (E := E) v n a) (hU : UnitV σ J ψ v Λ) : OrthoB σ J ψ v Λ a Y := by
  intro h hG X hX hXY
  obtain ⟨w, hw0, -, hw⟩ := hG.2.2.2.2.2.2
  rw [← hXY] at hw
  exact orthoGen σ J ψ v Λ hU hG.1 hG.2.1 hG.2.2.1 hG.2.2.2.1 (n - a) (Fin a) X
    (by rw [Fintype.card_fin]; omega) hX ⟨w, hw0, hw⟩

theorem orbAll_of_unitV (a : ℕ) (Y : TupV (E := E) v n a) (hU : UnitV σ J ψ v Λ) : OrbAll σ J ψ v Λ a Y :=
  orbAll_of_orthoB σ J ψ v Λ a Y (oSub v) (oSmul v Λ) (orthoB_of σ J ψ v Λ a Y hU)

end PI.OmLocU.Orb
end
end

noncomputable section

namespace PI.OmLocU.Orb

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

theorem sigma_invol (hcm : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  let τ : E →ₐ[ℚ] ℂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  apply τ.toRingHom.injective
  have h1 := hcm.2.2.2 τ.toRingHom (σ x)
  have h2 := hcm.2.2.2 τ.toRingHom x
  rw [h1, h2, star_star]

theorem sigR_invol (hcm : IsCMExt F E σ) (z : Fv F v ⊗[F] E) : sigR (Fv F v) σ (sigR (Fv F v) σ z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => simp [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, Algebra.TensorProduct.map_tmul, sigma_invol σ hcm]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

theorem sigR_inclR (e : E) : sigR (Fv F v) σ (inclR (F := F) (Fv F v) e) = inclR (F := F) (Fv F v) (σ e) := by
  simp [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR, Algebra.TensorProduct.map_tmul]

theorem hR_conj (hcm : IsCMExt F E σ) (hJ : ∀ i j, σ (J j i) = J i j) (x y : Fin n → Fv F v ⊗[F] E) :
    sigR (Fv F v) σ (hR (Fv F v) σ J x y) = hR (Fv F v) σ J y x := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hR, hform, map_sum, map_mul, sigR_invol σ v hcm, JR, Matrix.map_apply, sigR_inclR, hJ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

def NormOne : Prop :=
  StdHyp σ J ψ → UnramAt (E := E) v → ∀ u ∈ OEv (E := E) v, sigR (Fv F v) σ u = u →
    (∃ u' ∈ OEv (E := E) v, u * u' = 1) →
    ∃ l ∈ OEv (E := E) v, sigR (Fv F v) σ l * l * u = 1

def UnitNorm : Prop :=
  StdHyp σ J ψ → (∃ L : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E L ∧ (L : Set (Fin n → E)) = Λ) →
    IsSDLoc σ J v Λ → UnramAt (E := E) v →
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (X : ι → Fin n → Fv F v ⊗[F] E), (∀ i, X i ∈ latLoc (E := E) v Λ) →
      UniG σ J v X → Fintype.card ι < n →
      ∃ p ∈ PerpG σ J v Λ X, ∃ u' ∈ OEv (E := E) v, hR (Fv F v) σ J p p * u' = 1

theorem unitV_of (hN : NormOne σ J ψ v) (hUN : UnitNorm σ J ψ v Λ) : UnitV σ J ψ v Λ := by
  intro hstd hL hsd hun ι _ _ X hX hUX hc
  obtain ⟨p, hp, u', hu'0, hu'⟩ := hUN hstd hL hsd hun ι X hX hUX hc
  have hcm := hstd.1
  have hJ := hstd.2.1.1
  have hu0 : hR (Fv F v) σ J p p ∈ OEv (E := E) v := (hsd p).1 hp.1 p hp.1
  obtain ⟨l, hl0, hl⟩ := hN hstd hun _ hu0 (hR_conj σ J v hcm hJ p p) ⟨u', hu'0, hu'⟩
  have hXl : ∀ i, hR (Fv F v) σ J (X i) (l • p) = 0 := by
    intro i
    rw [hR_smul_right, hp.2 i, mul_zero]
  refine ⟨l • p, ⟨oSmul v Λ hL l hl0 p hp.1, hXl⟩, ?_, ?_⟩
  · rw [hR_smul_left, hR_smul_right, ← mul_assoc]
    exact hl
  · intro i
    rw [← hR_conj σ J v hcm hJ, hXl i, map_zero]

theorem orbAll_of_norm (a : ℕ) (Y : TupV (E := E) v n a) (hN : NormOne σ J ψ v)
    (hUN : UnitNorm σ J ψ v Λ) : OrbAll σ J ψ v Λ a Y :=
  orbAll_of_unitV σ J ψ v Λ a Y (unitV_of σ J ψ v Λ hN hUN)

end PI.OmLocU.Orb
