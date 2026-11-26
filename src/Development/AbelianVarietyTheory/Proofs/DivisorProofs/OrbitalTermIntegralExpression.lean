module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexifiedDerivedActionIsLieAction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtLevi
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransvectionSubgroupCocompactHaarFundamentalDoma
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitalTermIntegralExpression
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitalTermPointSum
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnnihilatorOfAnnihilatorLe
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory

theorem LKMid.Pair.term_one_eq_pointSum : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G) (Kf : Subgroup G.GAf) (f : G.GAf → ℂ) (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), (∀ k ∈ Kf, ∀ g, f (k⁻¹ * g * k) = f g) → (∀ k ∈ K', ∀ g, f' (k⁻¹ * g * sigG G 1 k) = f' g) → ∀ (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) P.β x t), P.term Kf f 1 K' f' = pointSum (P.toAf x t hx) (P.toQr 1 1) (MonoidHom.id (Gr G 1)) Kf K' (P.toAf x t hx P.self) (inclG G 1 P.atP) f f' := by
  intro p _ G P Kf f K' f' hf hf' x t hx
  have hN : IsNrm G 1 P.atP (inclG G 1 P.atP) 1 := (GlobalTheory.nrm_exact p G).2 P.atP
  have hsig : sigG G 1 = MonoidHom.id (Gr G 1) := by
    ext1 g
    exact (GlobalTheory.LKMid.SigIter.main p G 1 Nat.one_pos).1 g
  rw [GlobalTheory.T.kottwitzPair_term_eq_pointSum_any_trivialisation p G P Kf f 1 K' f' Nat.one_pos hf hf' x t hx (inclG G 1 P.atP) 1 hN]
  unfold Pair.termAt
  rw [hsig]

end GlobalTheory
end

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orbital_term_point_sum : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G) (Kf : Subgroup G.GAf) (f : G.GAf → ℂ) (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), (∀ k ∈ Kf, ∀ g, f (k⁻¹ * g * k) = f g) → (∀ k ∈ K', ∀ g, f' (k⁻¹ * g * sigG G 1 k) = f' g) → ∀ (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) P.β x t), P.term Kf f 1 K' f' = pointSum (P.toAf x t hx) (P.toQr 1 1) (MonoidHom.id (Gr G 1)) Kf K' (P.toAf x t hx P.self) (inclG G 1 P.atP) f f' := by
  first | (exact @GlobalTheory.LKMid.Pair.term_one_eq_pointSum) | (exact GlobalTheory.LKMid.Pair.term_one_eq_pointSum) | (intros; apply GlobalTheory.LKMid.Pair.term_one_eq_pointSum <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelesSelfDual
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory.LKMid.CentPos

theorem eq_smul_of_eigen {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (Z : GL (Fin n) ℂ) (lam : Fin n → ℂ)
    (hlam : Function.Injective lam) (hZ : M * (Z : Matrix (Fin n) (Fin n) ℂ) = (Z : Matrix (Fin n) (Fin n) ℂ) * diagonal lam)
    (μ : ℂ) (u w : Fin n → ℂ) (hu : M *ᵥ u = μ • u) (hw : M *ᵥ w = μ • w) (hu0 : u ≠ 0) :
    ∃ l : ℂ, w = l • u := by
  set Zm : Matrix (Fin n) (Fin n) ℂ := (Z : Matrix (Fin n) (Fin n) ℂ)
  set Zi : Matrix (Fin n) (Fin n) ℂ := ((Z⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)
  have h1 : Zi * Zm = 1 := by simp [Zi, Zm, ← Units.val_mul]
  have h2 : Zm * Zi = 1 := by simp [Zi, Zm, ← Units.val_mul]
  have hD : Zi * M = diagonal lam * Zi := by
    calc Zi * M = Zi * (M * Zm) * Zi := by rw [Matrix.mul_assoc, Matrix.mul_assoc, h2, Matrix.mul_one]
      _ = Zi * (Zm * diagonal lam) * Zi := by rw [hZ]
      _ = diagonal lam * Zi := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  have hcoord : ∀ a : Fin n → ℂ, M *ᵥ a = μ • a → ∀ j, lam j * (Zi *ᵥ a) j = μ * (Zi *ᵥ a) j := by
    intro a ha j
    have e : diagonal lam *ᵥ (Zi *ᵥ a) = μ • (Zi *ᵥ a) := by
      rw [mulVec_mulVec, ← hD, ← mulVec_mulVec, ha, mulVec_smul]
    have := congrFun e j
    rwa [mulVec_diagonal, Pi.smul_apply, smul_eq_mul] at this
  have hback : ∀ a : Fin n → ℂ, Zm *ᵥ (Zi *ᵥ a) = a := by
    intro a; rw [mulVec_mulVec, h2, one_mulVec]
  set u' := Zi *ᵥ u
  set w' := Zi *ᵥ w
  have hu'0 : u' ≠ 0 := by
    intro h; apply hu0; rw [← hback u]; show Zm *ᵥ u' = 0; rw [h, mulVec_zero]
  obtain ⟨i0, hi0⟩ : ∃ i0, u' i0 ≠ 0 := by
    by_contra h; push_neg at h; exact hu'0 (funext h)
  have hlam0 : lam i0 = μ := mul_right_cancel₀ hi0 (hcoord u hu i0)
  refine ⟨w' i0 / u' i0, ?_⟩
  have hw' : w' = (w' i0 / u' i0) • u' := by
    funext j
    rw [Pi.smul_apply, smul_eq_mul]
    by_cases hj : j = i0
    · subst hj; field_simp
    · have hne : lam j - μ ≠ 0 := by
        intro h; apply hj; apply hlam; rw [hlam0]; exact sub_eq_zero.1 h
      have hu0j : u' j = 0 := by
        have := hcoord u hu j
        have h' : (lam j - μ) * u' j = 0 := by rw [sub_mul]; exact sub_eq_zero.2 this
        exact (mul_eq_zero.1 h').resolve_left hne
      have hw0j : w' j = 0 := by
        have := hcoord w hw j
        have h' : (lam j - μ) * w' j = 0 := by rw [sub_mul]; exact sub_eq_zero.2 this
        exact (mul_eq_zero.1 h').resolve_left hne
      rw [hu0j, hw0j, mul_zero]
  calc w = Zm *ᵥ w' := (hback w).symm
    _ = Zm *ᵥ ((w' i0 / u' i0) • u') := by rw [← hw']
    _ = (w' i0 / u' i0) • u := by rw [mulVec_smul, hback u]

theorem cent_form_law {p : ℕ} [Fact p.Prime] (G : HTGroup p) (P : Pair G) (v : InfinitePlace G.F)
    (y : G.Cˣ × ℚˣ) (hy : y ∈ P.cent) :
    (G.psi v (y.1 : G.C))ᴴ * (G.gram v * G.psi v ((P.β⁻¹ : G.Cˣ) : G.C)) * G.psi v (y.1 : G.C) =
      (((y.2 : ℚˣ) : ℚ) : ℂ) • (G.gram v * G.psi v ((P.β⁻¹ : G.Cˣ) : G.C)) := by
  have hsim : (y.1 : G.C) * P.β * sh G y.1 = algebraMap ℚ G.C (y.2 : ℚ) * P.β := hy.2
  have hgu : IsUnit (G.gram v).det := isUnit_iff_ne_zero.mpr (G.gram_det v)
  have hgg : G.gram v * (G.gram v)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hgu
  have hgg' : (G.gram v)⁻¹ * G.gram v = 1 := Matrix.nonsing_inv_mul _ hgu
  have hH : ∀ x : G.C, (G.psi v x)ᴴ = G.gram v * G.psi v (sh G x) * (G.gram v)⁻¹ := by
    intro x
    have e : G.psi v (sh G x) = (G.gram v)⁻¹ * (G.psi v x)ᴴ * G.gram v := G.psi_star v x
    rw [e, ← mul_assoc, ← mul_assoc, hgg, one_mul, mul_assoc, hgg, mul_one]
  have hu : sh G (y.1 : G.C) * ((P.β⁻¹ : G.Cˣ) : G.C) * y.1 =
      algebraMap ℚ G.C (y.2 : ℚ) * ((P.β⁻¹ : G.Cˣ) : G.C) := by
    apply (Units.mul_right_inj (y.1 * P.β)).mp
    rw [Units.val_mul, ← Algebra.smul_def]
    calc (y.1 : G.C) * P.β * (sh G (y.1 : G.C) * ((P.β⁻¹ : G.Cˣ) : G.C) * y.1)
        = ((y.1 : G.C) * P.β * sh G (y.1 : G.C)) * ((P.β⁻¹ : G.Cˣ) : G.C) * y.1 := by
          simp only [mul_assoc]
      _ = (y.2 : ℚ) • ((P.β : G.C) * ((P.β⁻¹ : G.Cˣ) : G.C) * y.1) := by
          rw [hsim, ← Algebra.smul_def]; simp only [smul_mul_assoc]
      _ = (y.2 : ℚ) • ((y.1 : G.C) * P.β * ((P.β⁻¹ : G.Cˣ) : G.C)) := by
          rw [Units.mul_inv, one_mul, mul_assoc, Units.mul_inv, mul_one]
      _ = _ := by rw [mul_smul_comm, mul_assoc]
  rw [hH]
  calc G.gram v * G.psi v (sh G (y.1 : G.C)) * (G.gram v)⁻¹ * (G.gram v * G.psi v ((P.β⁻¹ : G.Cˣ) : G.C)) *
        G.psi v (y.1 : G.C)
      = G.gram v * (G.psi v (sh G (y.1 : G.C)) * ((G.gram v)⁻¹ * G.gram v) *
          G.psi v ((P.β⁻¹ : G.Cˣ) : G.C) * G.psi v (y.1 : G.C)) := by simp only [mul_assoc]
    _ = G.gram v * G.psi v (sh G (y.1 : G.C) * ((P.β⁻¹ : G.Cˣ) : G.C) * y.1) := by
        rw [hgg', mul_one, map_mul, map_mul]
    _ = G.gram v * (((y.2 : ℚˣ) : ℚ) • G.psi v ((P.β⁻¹ : G.Cˣ) : G.C)) := by
        rw [hu, map_mul, RingHom.map_rat_algebraMap, ← Algebra.smul_def]
    _ = _ := by rw [mul_smul_comm, Rat.cast_smul_eq_qsmul]

end GlobalTheory.LKMid.CentPos

namespace GlobalTheory.LKMid


open GlobalTheory.LKMid.CentPos in
theorem cent_sim_pos : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G) (μ : ℂ), G.a = 1 → P.Mark μ →
    ∀ y ∈ P.cent, 0 < ((y.2 : ℚˣ) : ℚ) := by
  intro p _ G P μ _ hm y hy
  obtain ⟨v, -, x, hx, hpos⟩ := hm
  set H := G.gram v * G.psi v ((P.β⁻¹ : G.Cˣ) : G.C) with hHdef
  set M := G.psi v (P.γ : G.C) with hMdef
  set Y := G.psi v (y.1 : G.C) with hYdef
  have hc : (y.1 : G.C) * P.γ = P.γ * y.1 := by
    have := congrArg Units.val hy.1; simpa using this
  have hMY : M * Y = Y * M := by rw [hMdef, hYdef, ← map_mul, ← map_mul, hc]
  have hform : Yᴴ * H * Y = (((y.2 : ℚˣ) : ℚ) : ℂ) • H := cent_form_law G P v y hy
  obtain ⟨Z, lam, hinj, -, hZ⟩ := psi_eigenbasis p G P v
  have hx0 : x ≠ 0 := by rintro rfl; simp at hpos
  have hYx : M *ᵥ (Y *ᵥ x) = μ • (Y *ᵥ x) := by
    rw [mulVec_mulVec, hMY, ← mulVec_mulVec, hx, mulVec_smul]
  obtain ⟨l, hl⟩ := eq_smul_of_eigen M Z lam hinj hZ μ x (Y *ᵥ x) hx hYx hx0
  have key : star (Y *ᵥ x) ⬝ᵥ (H *ᵥ (Y *ᵥ x)) = star x ⬝ᵥ ((Yᴴ * H * Y) *ᵥ x) := by
    rw [star_mulVec, mulVec_mulVec, dotProduct_mulVec, dotProduct_mulVec, vecMul_vecMul]
    simp only [hHdef, Matrix.mul_assoc]
  rw [hform, hl] at key
  simp only [Matrix.smul_mulVec, mulVec_smul, star_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul] at key
  set q := star x ⬝ᵥ (H *ᵥ x) with hq
  have hq0 : q ≠ 0 := by intro h; rw [h] at hpos; simp at hpos
  have hs : star l * l = (((y.2 : ℚˣ) : ℚ) : ℂ) := by
    rw [← mul_assoc] at key; have := mul_right_cancel₀ hq0 key; rw [mul_comm] at this; exact this
  have hsre : ((((y.2 : ℚˣ) : ℚ) : ℂ)).re = ((y.2 : ℚˣ) : ℚ) := by simp
  have hnn : (0 : ℝ) ≤ (((y.2 : ℚˣ) : ℚ) : ℝ) := by
    have : (star l * l).re = Complex.normSq l := by
      rw [mul_comm, Complex.star_def, Complex.mul_conj]; simp
    rw [hs] at this
    have h2 : ((((y.2 : ℚˣ) : ℚ) : ℂ)).re = (((y.2 : ℚˣ) : ℚ) : ℝ) := by simp
    rw [← h2, this]; exact Complex.normSq_nonneg l
  have hnn' : (0 : ℚ) ≤ ((y.2 : ℚˣ) : ℚ) := by exact_mod_cast hnn
  exact lt_of_le_of_ne hnn' (Ne.symm (y.2.ne_zero))

end GlobalTheory.LKMid
end

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory.LKCx.Regroup

variable {p : ℕ} [Fact p.Prime]

noncomputable def centEquiv (G : HTGroup p) (P : Pair G) (hpos : ∀ y ∈ P.cent, 0 < ((y.2 : ℚˣ) : ℚ))
    (r : grp G P.β) (hr : (r : G.Cˣ × ℚˣ) = (P.γ, P.c)) :
    Subgroup.centralizer ({r} : Set (grp G P.β)) ≃* P.cent where
  toFun y := ⟨y.1.1, by
    have h := congrArg (fun a : grp G P.β => (a : G.Cˣ × ℚˣ).1)
      (Subgroup.mem_centralizer_singleton_iff.1 y.2)
    simp only [Subgroup.coe_mul, hr, Prod.fst_mul] at h
    exact h, y.1.2.1⟩
  invFun y := ⟨⟨y.1, y.2.2, hpos y.1 y.2⟩, by
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    simp only [Subgroup.coe_mul, hr]
    exact Prod.ext y.2.1 (mul_comm _ _)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem fix_iff_mark (G : HTGroup p) (hG : G.a = 1) (v : InfinitePlace G.F) (hv : sigPosH (G.gram_herm v) = 1)
    (P : Pair G) (r : grp G P.β) (hr : (r : G.Cˣ × ℚˣ) = (P.γ, P.c)) :
    (∃ z : Fin G.n → ℂ, 0 < (star z ⬝ᵥ (herm G v P.β *ᵥ z)).re ∧ FixL G v P.β r z) ↔ ∃ μ, P.Mark μ := by
  have hV : (toV G v P.β r : Matrix (Fin G.n) (Fin G.n) ℂ) = G.psi v (P.γ : G.C) := by
    show G.psi v (((r : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) = _
    rw [hr]
  constructor
  · rintro ⟨z, hz, c, hc⟩
    rw [hV] at hc
    exact ⟨c, v, hv, z, hc, hz⟩
  · rintro ⟨μ, w, hw, z, hz, hpos⟩
    have h1 : Fintype.card {v : InfinitePlace G.F // sigPosH (G.gram_herm v) = 1} ≤ 1 := hG.le
    have hvv : w = v := congrArg Subtype.val (Fintype.card_le_one_iff.1 h1 ⟨w, hw⟩ ⟨v, hv⟩)
    subst hvv
    exact ⟨z, hpos, μ, by rw [hV]; exact hz⟩

end GlobalTheory.LKCx.Regroup
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalLevelEigenpartsAndConjugateCharacters
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SphericalOperatorCommuteLevelFiniteGroup
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta
open Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Lev
open scoped TensorProduct

namespace GlobalTheory.HeckeKeepsGood

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

variable {V : HSp D} {β : GL (Fin V.rank) (EAf D)} {L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank}

theorem levChi_mul {k k' : GA D V} (hk : k ∈ levG V β L) (hk' : k' ∈ levG V β L) :
    levChi V β L (k * k') = levChi V β L k * levChi V β L k' := by
  unfold levChi
  rw [← Units.val_mul, MonoidHom.map_mul]
  exact congrArg Units.val ((Formalism.L2.DIV.levChar D.sp.cm V.gram β L).map_mul ⟨_, hk.2⟩ ⟨_, hk'.2⟩)

variable {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} {N : ℕ}
  {Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))} {P : HeightOneSpectrum (𝓞 D.host.E)} {d : List ℤ} {R : Finset (GA D V)}

theorem hasType_heckeLin (hB : IsBaseFrame V β Λ N) (hN : ((N : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal)
    (hPP : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → PP ≠ P ∧ ¬ IsConjPl PP P)
    (hR : Hecke₂ V (levG V β L : Set (GA D V)) (levChi V β L) Sb P d R) {F : GA D V → ℂ}
    (hF : HasType V β L F) : HasType V β L (heckeLin V R F) :=
  GlobalTheory.SphericalOps.level_heckeLin (fun _ hk _ hk' => levChi_mul hk hk')
    (fun e f _ hI => ((GlobalTheory.LevSplit.lev_split V β Λ N L hB).2 P e f hI hN hPP).2.2) hR hF

theorem sphericalOperator_commute_levelFiniteGroup (hB : IsBaseFrame V β Λ N) (hN : ((N : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal)
    (hPP : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → PP ≠ P ∧ ¬ IsConjPl PP P)
    (hR : Hecke₂ V (levG V β L : Set (GA D V)) (levChi V β L) Sb P d R) {F : GA D V → ℂ}
    (hF : HasType V β L F) (x : Formalism.L2.DIV.G0 L.Pg L.r) :
    actG0 V β L x (heckeLin V R F) = heckeLin V R (actG0 V β L x F) := by
  have hG := hasType_heckeLin hB hN hPP hR hF
  obtain ⟨e, f, ϖ, α, -, hI, -, -, -, hJ, hχ, -, -, hRs, -⟩ := hR
  unfold actG0
  split_ifs with hk
  swap
  · exact (map_zero _).symm
  have hκ := hk.choose_spec
  generalize hk.choose = κ at hκ ⊢
  obtain ⟨a1, -, a3⟩ := (GlobalTheory.LevSplit.lev_split V β Λ N (flagL L) hB).2 P e f hI hN hPP
  obtain ⟨k₁, m₁, k₂, -, s₁, s₂, rfl⟩ := a3 κ ⟨hκ.1, hκ.2.1, Subgroup.mem_top _⟩
  have m : k₁ ∈ levG V β L := (hJ k₁ s₁).2 ((a1 k₁ s₁).1 m₁)
  obtain ⟨hff, hcf, -⟩ := (GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents V).2.2.1 P e f hI
  have hc : ∀ a, SuppF V f a → Commute a k₂ := fun a ha =>
    ((GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents V).1 f hff hcf).2.2 (1 - f) a k₂ (by rw [mul_sub, mul_one, hff, sub_self]) ha s₂
  have key : ∀ G : GA D V → ℂ, HasType V β L G → ∀ h, G (h * (k₁ * k₂)) = G (h * k₂) := fun G hG h => by
    rw [(hc k₁ s₁).eq, ← mul_assoc, hG k₁ m, hχ k₁ m s₁, one_mul]
  funext h
  rw [key _ hG]
  show _ * ∑ γ ∈ R, F (h * k₂ * γ) = ∑ γ ∈ R, _ * F (h * γ * (k₁ * k₂))
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun γ hγ => ?_
  rw [key F hF, mul_assoc h γ, (hc γ (hRs γ hγ)).eq, mul_assoc h]

end GlobalTheory.HeckeKeepsGood
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalLevelEigenpartsAndConjugateCharacters
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
open GlobalTheory.LiftLower
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PrincipalDecomp

open GlobalTheory.SphericalOps GlobalTheory.HeckeAdjoint GlobalTheory.HeckeOrthSum

theorem iSup_partH_eq_top_five : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), SchurMult R.θ (R.MW i σ) (levSW R i) (chiW R i) (R.νW i) (R.fdW i) → (⨆ (c : GlobalTheory.IndefiniteRowSideFullHecke.PolarisedDualSystem.Sys D) (_ : IsNormSys R i c), partH R i σ c) = ⊤ := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC i σ hS
  classical
  obtain ⟨hinj, hrange, -⟩ := hC.models.HW i σ
  have hrange' : LinearMap.range (R.HW i σ).e =
      Mult R.θ (R.MW i σ) (Lev.levG _ (R.βW i) (R.datWp i R.triv) : Set (GA D (Wc D i))) (chiW R i) := hrange
  haveI : FiniteDimensional ℂ
      (Mult R.θ (R.MW i σ) (Lev.levG _ (R.βW i) (R.datWp i R.triv) : Set (GA D (Wc D i))) (chiW R i)) := by
    rw [← hrange']; infer_instance
  obtain ⟨n, hB⟩ := hC.lev.βW i
  have key := mult_le_of_parts (J := Lev.levG _ (R.βW i) (R.datWp i R.triv)) (Sb := GlobalTheory.IndefiniteRowSideFullHecke.PolarisedDualSystem.badF R)
    hC.models.inf (hC.models.νW i).1.1 (hC.models.νW i).2 hS (fun P d Rp h T hT => ?_)
    ((⨆ (c : GlobalTheory.IndefiniteRowSideFullHecke.PolarisedDualSystem.Sys D) (_ : IsNormSys R i c), partH R i σ c).map (R.HW i σ).e) (fun c hc T hT => ?_)
  · rw [eq_top_iff]
    intro x _
    obtain ⟨y, hy, e⟩ := key (hrange' ▸ LinearMap.mem_range_self _ x)
    exact hinj e ▸ hy
  · have hN : (((1 ^ n : ℕ) : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
      rw [one_pow, Nat.cast_one]
      exact (Ideal.ne_top_iff_one _).1 P.isPrime.ne_top
    have hO : OffS D (GlobalTheory.IndefiniteRowSideFullHecke.PolarisedDualSystem.badF R) P := by
      obtain ⟨_, _, _, _, hO, -⟩ := h
      exact hO
    have hP : ∀ PP, PP ∈ (R.datWp i R.triv).Pg ∨ PP ∈ (R.datWp i R.triv).Q → PP ≠ P ∧ ¬ Lev.IsConjPl PP P := by
      rintro PP (hP | hP)
      · exact GlobalTheory.HeckeOffLevel.sep_of_offS hO (by
          unfold GlobalTheory.IndefiniteRowSideFullHecke.PolarisedDualSystem.badF
          exact Finset.mem_image.2 ⟨PP, hP, rfl⟩)
      · exact absurd hP (Finset.notMem_empty _)
    rw [GlobalTheory.MultMem.mem_mult_iff] at hT ⊢
    refine isMultMap_heckeOn hT (fun k hk => ?_) fun v => GlobalTheory.HeckeOffLevel.hasType_heckeLin hB hN hP h (hT.lev v)
    obtain ⟨_, _, _, _, -, -, -, -, -, -, -, -, -, -, hc⟩ := h
    exact (hc.1 k hk).1
  · obtain ⟨y, rfl⟩ : T ∈ LinearMap.range (R.HW i σ).e := hrange' ▸ hT.1
    exact Submodule.mem_map_of_mem
      (le_iSup₂_of_le (f := fun (c : GlobalTheory.IndefiniteRowSideFullHecke.PolarisedDualSystem.Sys D) (_ : IsNormSys R i c) => partH R i σ c) c hc le_rfl hT)

end GlobalTheory.PrincipalDecomp

namespace GlobalTheory.LiftLower

theorem gW_mem_partH_five : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (c : GlobalTheory.IndefiniteRowSideFullHecke.PolarisedDualSystem.Sys D) (g : G), ∀ x ∈ partH R i σ c, R.gW i σ g x ∈ partH R i σ c := by
  classical
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC i σ c g x hx
  unfold partH at hx ⊢
  rw [Submodule.mem_comap, mem_partFull] at hx ⊢
  refine ⟨?_, fun P d Rp hR v => ?_⟩
  · have h : (R.HW i σ).e (R.gW i σ g x) ∈ LinearMap.range (R.HW i σ).e := LinearMap.mem_range_self _ _
    rw [(hC.models.HW i σ).2.1] at h
    exact h
  have hO : OffS D (GlobalTheory.IndefiniteRowSideFullHecke.PolarisedDualSystem.badF R) P := by
    obtain ⟨_, _, _, _, h, -⟩ := hR
    exact h
  obtain ⟨-, h2⟩ := GlobalTheory.offS_not_type_places R.C.P R.Pg (GlobalTheory.IndefiniteRowSideFullHecke.PolarisedDualSystem.badF R) P hC.lev.Pg
    (fun PP hPP => by unfold GlobalTheory.IndefiniteRowSideFullHecke.PolarisedDualSystem.badF; exact Finset.mem_image.2 ⟨PP, hPP, rfl⟩) hO
  obtain ⟨a, hB⟩ := hC.lev.βW i
  have hN : (((1 ^ a : ℕ)) : 𝓞 D.host.E) ∉ P.asIdeal := fun h =>
    P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using h))
  have hPP : ∀ PP, PP ∈ (R.datWp i R.triv).Pg ∨ PP ∈ (R.datWp i R.triv).Q → PP ≠ P ∧ ¬ Lev.IsConjPl PP P := by
    rintro PP (h | h)
    · exact h2 PP h
    · exact absurd h (Finset.notMem_empty _)
  have hT := ((GlobalTheory.MultMem.mem_mult_iff ..).1 hx.1).lev v
  rw [hC.models.gW i σ g x, postOn_apply, ← map_smul, ← hx.2 P d Rp hR v]
  exact (GlobalTheory.HeckeKeepsGood.sphericalOperator_commute_levelFiniteGroup hB hN hPP hR hT (R.eG g)).symm

end GlobalTheory.LiftLower

namespace GlobalTheory.ConjMuChar

theorem exists_galConj_chrEq_five : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (s : ℂ ≃+* ℂ), GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.IsEmbOverK D σ s → ∀ μ' : (AE D)ˣ →* Circle, ChiAt R i σ μ' → ∃ μH : Formalism.L2.Host.HChar D.host.E, GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.IsGalConj s 0 (R.C.mu0 i * R.xiH A.μ0) μH ∧ ChrEq μ' μH := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC i σ s hσ μ' hμ
  obtain ⟨μH, hH⟩ := GlobalTheory.HeckeTensorRead.exists_hchar_chrEq D μ' hμ.1
  refine ⟨μH, fun P k => ?_, hH⟩
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨e, he, hinf, -⟩ := GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3 P
  have hx : infPart D ((Formalism.L2.JoinChr.locU he.1 k : (AE D)ˣ) : AE D) = 1 := by
    rw [Formalism.L2.JoinChr.locU_val, Formalism.L2.JoinChr.locE, RingHom.map_add (f := _), RingHom.map_mul, hinf, zero_mul, add_zero,
      RingHom.map_one]
  obtain ⟨y, hy0, hy⟩ := hμ.2.2.2.1 _ hx
  have a1 := hH.2 P e he k _ (Formalism.L2.JoinChr.locU_val he.1 k)
  have a2 := (hC.lev.mu0 i).2 P e he k _ (Formalism.L2.JoinChr.locU_val he.1 k)
  rw [hC.lev.xi_base, mul_one]
  unfold GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.twVal
  simp only [Complex.ofReal_zero, zero_mul, neg_zero, Complex.cpow_zero, mul_one]
  rw [← a1, ← a2, hy, hy0, hσ.1]

end GlobalTheory.ConjMuChar

namespace GlobalTheory.EtaConjChar

open Formalism.L2.Host Formalism.L2.JoinChr

theorem exists_galConj_eta_five : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (σ : D.what₂.LL →+* ℂ) (s : ℂ ≃+* ℂ), GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.IsEmbOverK D σ s → ∀ η' : (AE D)ˣ →* Circle, GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.IsEtaConj σ R.eta η' → ∃ ηH : Formalism.L2.Host.HChar D.host.E, GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.IsGalConj s (1 / 2) R.C.eta ηH ∧ ChrEq η' ηH := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hR σ s hσ η' hη
  obtain ⟨ηH, hH⟩ := GlobalTheory.HeckeTensorRead.exists_hchar_chrEq D η' hη.1
  refine ⟨ηH, fun P k => ?_, hH⟩
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨e, he, -⟩ := GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3 P
  obtain ⟨y, hy1, hy2⟩ := hη.2.2 P e he (locU he.1 (unif P)) rfl
  have h0 : ∀ u : D.host.Eˣ, P.valuation D.host.E (u : D.host.E) = 1 → R.C.eta.locK P u = 1 := fun u hu =>
    R.C.isEta.unr P _ ((P.valuedAdicCompletion_eq_valuation' (u : D.host.E)).trans hu)
  rw [twVal_half _ P (locK_eq_one hH hη.2.1 P), twVal_half _ P h0, map_zpow₀,
    ← hH.2 P e he _ (locU he.1 (unif P)) rfl, ← hR.lev.eta.2 P e he _ (locU he.1 (unif P)) rfl, ← hy1, ← hy2, hσ.1]

end GlobalTheory.EtaConjChar

namespace GlobalTheory.FiveClauseParts

theorem parts_conj_five : (∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), SchurMult R.θ (R.MW i σ) (levSW R i) (chiW R i) (R.νW i) (R.fdW i) → (⨆ (c : GlobalTheory.IndefiniteRowSideFullHecke.PolarisedDualSystem.Sys D) (_ : IsNormSys R i c), partH R i σ c) = ⊤) ∧ (∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (c : GlobalTheory.IndefiniteRowSideFullHecke.PolarisedDualSystem.Sys D) (g : G), ∀ x ∈ partH R i σ c, R.gW i σ g x ∈ partH R i σ c) ∧ (∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (s : ℂ ≃+* ℂ), GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.IsEmbOverK D σ s → ∀ μ' : (AE D)ˣ →* Circle, ChiAt R i σ μ' → ∃ μH : Formalism.L2.Host.HChar D.host.E, GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.IsGalConj s 0 (R.C.mu0 i * R.xiH A.μ0) μH ∧ ChrEq μ' μH) ∧ (∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (σ : D.what₂.LL →+* ℂ) (s : ℂ ≃+* ℂ), GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.IsEmbOverK D σ s → ∀ η' : (AE D)ˣ →* Circle, GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.IsEtaConj σ R.eta η' → ∃ ηH : Formalism.L2.Host.HChar D.host.E, GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.IsGalConj s (1 / 2) R.C.eta ηH ∧ ChrEq η' ηH) :=
  ⟨GlobalTheory.PrincipalDecomp.iSup_partH_eq_top_five, GlobalTheory.LiftLower.gW_mem_partH_five,
    GlobalTheory.ConjMuChar.exists_galConj_chrEq_five, GlobalTheory.EtaConjChar.exists_galConj_eta_five⟩

end GlobalTheory.FiveClauseParts

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalLevelEigenpartsAndConjugateCharactersStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
open GlobalTheory.LiftLower
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principalLevel_eigenparts_and_conjugate_characters : (∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), SchurMult R.θ (R.MW i σ) (levSW R i) (chiW R i) (R.νW i) (R.fdW i) → (⨆ (c : GlobalTheory.IndefiniteRowSideFullHecke.PolarisedDualSystem.Sys D) (_ : IsNormSys R i c), partH R i σ c) = ⊤) ∧ (∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (c : GlobalTheory.IndefiniteRowSideFullHecke.PolarisedDualSystem.Sys D) (g : G), ∀ x ∈ partH R i σ c, R.gW i σ g x ∈ partH R i σ c) ∧ (∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (s : ℂ ≃+* ℂ), GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.IsEmbOverK D σ s → ∀ μ' : (AE D)ˣ →* Circle, ChiAt R i σ μ' → ∃ μH : Formalism.L2.Host.HChar D.host.E, GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.IsGalConj s 0 (R.C.mu0 i * R.xiH A.μ0) μH ∧ ChrEq μ' μH) ∧ (∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (σ : D.what₂.LL →+* ℂ) (s : ℂ ≃+* ℂ), GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.IsEmbOverK D σ s → ∀ η' : (AE D)ˣ →* Circle, GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.IsEtaConj σ R.eta η' → ∃ ηH : Formalism.L2.Host.HChar D.host.E, GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.IsGalConj s (1 / 2) R.C.eta ηH ∧ ChrEq η' ηH) := by
  first | exact @GlobalTheory.FiveClauseParts.parts_conj_five | exact GlobalTheory.FiveClauseParts.parts_conj_five | (intros; apply GlobalTheory.FiveClauseParts.parts_conj_five <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRescalePrimitiveInLatticeAtSplitPrimes
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsExtraLast
namespace GlobalTheory.NonzeroSmulMembership

theorem exists_ne_zero_smul_mem {E : Type} [inst : Field E] [NumberField E] {n : ℕ}
    (L : Submodule (NumberField.RingOfIntegers E) (Fin n → E)) (hL : Submodule.IsFullLattice E L)
    (x : Fin n → E) :
    ∃ (d : NumberField.RingOfIntegers E), d ≠ (0 : NumberField.RingOfIntegers E) ∧ d • x ∈ L := by
  have hx : x ∈ Submodule.span E (L : Set (Fin n → E)) := by
    rw [hL.span_eq_top]; trivial
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨b, hb, hbz⟩ := hz
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    have h1 : (a * b) • y = b • a • y := by rw [mul_comm, mul_smul]
    rw [smul_add, h1, mul_smul]
    exact L.add_mem (L.smul_mem b hay) (L.smul_mem a hbz)
  | smul c y _ hy =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := NumberField.RingOfIntegers E) c
    have hq0 : q ≠ 0 := nonZeroDivisors.ne_zero hq
    have hq1 : algebraMap (NumberField.RingOfIntegers E) E q ≠ 0 := by
      intro h
      exact hq0 (IsFractionRing.injective (NumberField.RingOfIntegers E) E (by simpa using h))
    refine ⟨q * a, mul_ne_zero hq0 ha, ?_⟩
    have key : (q * a) • ((algebraMap (NumberField.RingOfIntegers E) E p /
        algebraMap (NumberField.RingOfIntegers E) E q) • y) = p • a • y := by
      funext i
      simp only [Pi.smul_apply, smul_eq_mul]
      simp only [Algebra.smul_def, map_mul]
      field_simp
    rw [key]
    exact L.smul_mem p hay

end GlobalTheory.NonzeroSmulMembership
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRescalePrimitiveInLatticeAtSplitPrimes
open scoped TensorProduct Matrix nonZeroDivisors
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.PlaneSkew

noncomputable section
namespace GlobalTheory.PlaneSkewScale

variable {E : Type} [Field E] [NumberField E]

theorem exists_intValuation_eq {ι : Type} [Fintype ι] (w : ι → HeightOneSpectrum (𝓞 E))
    (hw : Function.Injective w) (k : ι → ℕ) :
    ∃ a : 𝓞 E, ∀ i, (w i).intValuation a = WithZero.exp (-(k i : ℤ)) := by
  classical
  choose π hπ using fun i => (w i).intValuation_exists_uniformizer
  obtain ⟨a, ha⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := (Finset.univ : Finset ι))
    (fun i => (w i).asIdeal) (fun i => k i + 1) (fun i _ => (w i).prime)
    (fun i _ j _ hij e => hij (hw (HeightOneSpectrum.ext e))) (fun i => π i.1 ^ k i.1)
  refine ⟨a, fun i => ?_⟩
  have h1 : (w i).intValuation (π i ^ k i) = WithZero.exp (-(k i : ℤ)) := by
    rw [map_pow, hπ, ← WithZero.exp_nsmul]; congr 1; simp
  have h2 := ((w i).intValuation_le_pow_iff_mem _ _).2 (ha i (Finset.mem_univ i))
  rw [← h1]
  apply Valuation.map_eq_of_sub_lt
  rw [h1]
  refine lt_of_le_of_lt h2 ?_
  rw [WithZero.exp_lt_exp]
  push_cast
  omega

theorem exists_valuation_eq {ι : Type} [Fintype ι] (w : ι → HeightOneSpectrum (𝓞 E))
    (hw : Function.Injective w) (t : ι → WithZero (Multiplicative ℤ)) (ht : ∀ i, t i ≠ 0) :
    ∃ c : E, c ≠ 0 ∧ ∀ i, (w i).valuation E c = t i := by
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨i₀⟩⟩
  · exact ⟨1, one_ne_zero, fun i => isEmptyElim i⟩
  obtain ⟨a, ha⟩ := exists_intValuation_eq w hw (fun i => (-(t i).log).toNat)
  obtain ⟨b, hb⟩ := exists_intValuation_eq w hw (fun i => ((t i).log).toNat)
  have hne : ∀ r : 𝓞 E, (w i₀).intValuation r ≠ 0 → algebraMap (𝓞 E) E r ≠ 0 := fun r hr e => by
    apply hr
    rw [(map_eq_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).1 e, map_zero]
  have ha0 := hne a (by rw [ha]; exact WithZero.exp_ne_zero)
  have hb0 := hne b (by rw [hb]; exact WithZero.exp_ne_zero)
  refine ⟨algebraMap (𝓞 E) E a / algebraMap (𝓞 E) E b, div_ne_zero ha0 hb0, fun i => ?_⟩
  rw [map_div₀, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap, ha, hb,
    ← WithZero.exp_sub]
  conv_rhs => rw [← WithZero.exp_log (ht i)]
  congr 1
  omega

end GlobalTheory.PlaneSkewScale

namespace GlobalTheory.PlaneSkewScale

variable {E : Type} [Field E] [NumberField E]

theorem exists_smul_mem {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) (hL : L.IsFullLattice E) (x : Fin n → E) :
    ∃ d : 𝓞 E, d ≠ 0 ∧ d • x ∈ L := by
  exact GlobalTheory.NonzeroSmulMembership.exists_ne_zero_smul_mem L hL x

theorem exists_max {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) (hL : L.IsFullLattice E) {x : Fin n → E} (hx : x ≠ 0)
    (w : HeightOneSpectrum (𝓞 E)) :
    ∃ s₀ : E, s₀ ≠ 0 ∧ s₀ • x ∈ L ∧ ∀ s : E, s • x ∈ L → w.valuation E s ≤ w.valuation E s₀ := by
  classical
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hx
  obtain ⟨G, hG⟩ := hL.fg
  set B := G.sup fun g => w.valuation E (g j)
  have hB : ∀ z ∈ L, w.valuation E (z j) ≤ B := by
    intro z hz
    rw [← hG] at hz
    induction hz using Submodule.span_induction with
    | mem z hz => exact Finset.le_sup (f := fun g => w.valuation E (g j)) hz
    | zero => simp
    | add z₁ z₂ _ _ h₁ h₂ => rw [Pi.add_apply]; exact Valuation.map_add_le _ h₁ h₂
    | smul a z _ h =>
      rw [Pi.smul_apply, Algebra.smul_def, map_mul]
      exact mul_le_of_le_one_left' (w.valuation_le_one a) |>.trans h
  have hxj : w.valuation E (x j) ≠ 0 := (map_ne_zero _).2 (by simpa using hj)
  have hbound : ∀ s : E, s • x ∈ L → w.valuation E s ≤ B * (w.valuation E (x j))⁻¹ := fun s hs => by
    have := hB _ hs
    rw [Pi.smul_apply, smul_eq_mul, map_mul] at this
    exact (le_mul_inv_iff₀ (zero_lt_iff.2 hxj)).2 this
  obtain ⟨K, hK⟩ : ∃ K : ℤ, B * (w.valuation E (x j))⁻¹ ≤ WithZero.exp K := by
    by_cases h0 : B * (w.valuation E (x j))⁻¹ = 0
    · exact ⟨0, by rw [h0]; exact zero_le'⟩
    · exact ⟨_, (WithZero.exp_log h0).ge⟩
  obtain ⟨d, hd, hdx⟩ := exists_smul_mem L hL x
  have hd' : algebraMap (𝓞 E) E d ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).2 hd
  let S : ℤ → Prop := fun k => ∃ s : E, s ≠ 0 ∧ s • x ∈ L ∧ w.valuation E s = WithZero.exp k
  obtain ⟨k₀, ⟨s₀, hs₀, hs₀L, hs₀v⟩, hmax⟩ := Int.exists_greatest_of_bdd (P := S)
    ⟨K, fun k ⟨s, _, hs, hv⟩ => by
      have := (hbound s hs).trans hK
      rwa [hv, WithZero.exp_le_exp] at this⟩
    ⟨_, algebraMap (𝓞 E) E d, hd', by rwa [algebraMap_smul],
      (WithZero.exp_log ((map_ne_zero _).2 hd')).symm⟩
  refine ⟨s₀, hs₀, hs₀L, fun s hs => ?_⟩
  by_cases h0 : s = 0
  · rw [h0, map_zero]; exact zero_le'
  · have hv := (WithZero.exp_log ((map_ne_zero (w.valuation E)).2 h0)).symm
    rw [hv, hs₀v, WithZero.exp_le_exp]
    exact hmax _ ⟨s, h0, hs, hv⟩

theorem primAt_smul {w : HeightOneSpectrum (𝓞 E)} {n : ℕ} {L : Submodule (𝓞 E) (Fin n → E)} {x : Fin n → E}
    {c s₀ : E} (hc : c ≠ 0) (hs₀ : s₀ • x ∈ L) (hmax : ∀ s : E, s • x ∈ L → w.valuation E s ≤ w.valuation E s₀)
    (he : w.valuation E c = w.valuation E s₀) : PrimAt w L (c • x) := by
  have hc' : w.valuation E c ≠ 0 := (map_ne_zero _).2 hc
  refine ⟨fun s hs => ?_, s₀ * c⁻¹, ?_, ?_⟩
  · rw [smul_smul] at hs
    have h1 := hmax _ hs
    rw [map_mul, ← he] at h1
    have h2 : w.valuation E s * w.valuation E c ≤ 1 * w.valuation E c := by rwa [one_mul]
    have h3 : w.valuation E s ≤ 1 * w.valuation E c * (w.valuation E c)⁻¹ := (le_mul_inv_iff₀ (zero_lt_iff.2 hc')).2 h2
    rwa [one_mul, mul_inv_cancel₀ hc'] at h3
  · rwa [smul_smul, mul_assoc, inv_mul_cancel₀ hc, mul_one]
  · rw [map_mul, map_inv₀, ← he, mul_inv_cancel₀ hc']

end GlobalTheory.PlaneSkewScale

namespace GlobalTheory.PlaneSkewScale

theorem exists_rescale_primAt : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)), L.IsFullLattice E → ∀ x y : Fin n → E, x ≠ 0 → y ≠ 0 →
    ∀ (P : Finset (HeightOneSpectrum (𝓞 F))) (τ : ∀ v : P, E →ₐ[F] Fv F v.1), ∃ c : E, c ≠ 0 ∧
      ∀ v : P, PrimAt (GlobalTheory.AdelicU.splitPrime (τ v)) L (c • x) ∧ PrimAt (GlobalTheory.AdelicU.splitPrime (τ v)) L ((σ c)⁻¹ • y) := by
  intro F E _ _ _ _ _ σ hσ n L hL x y hx hy P τ
  classical
  choose sx hsx0 hsxL hsxmax using fun v : P => exists_max L hL hx (GlobalTheory.AdelicU.splitPrime (τ v))
  choose sy hsy0 hsyL hsymax using fun v : P => exists_max L hL hy (GlobalTheory.AdelicU.splitPrime (τ v))
  let w : P ⊕ P → HeightOneSpectrum (𝓞 E) :=
    Sum.elim (fun v => GlobalTheory.AdelicU.splitPrime (τ v)) (fun v => GlobalTheory.AdelicU.splitPrime ((τ v).comp σ))
  have hunder : ∀ i, (w i).under (𝓞 F) = (Sum.elim (fun v : P => v.1) (fun v : P => v.1) i) := by
    rintro (v | v) <;> exact GlobalTheory.AdelicU.splitPrime_under _
  have hw : Function.Injective w := by
    intro i j e
    have hv := (hunder i).symm.trans ((congrArg (fun u => u.under (𝓞 F)) e).trans (hunder j))
    rcases i with ⟨a, ha⟩ | ⟨a, ha⟩ <;> rcases j with ⟨b, hb⟩ | ⟨b, hb⟩ <;>
      simp only [Sum.elim_inl, Sum.elim_inr] at hv <;> subst hv
    · rfl
    · exact absurd e.symm (GlobalTheory.AdelicU.splitPrime_comp_ne hσ _)
    · exact absurd e (GlobalTheory.AdelicU.splitPrime_comp_ne hσ _)
    · rfl
  let t : P ⊕ P → WithZero (Multiplicative ℤ) :=
    Sum.elim (fun v => (GlobalTheory.AdelicU.splitPrime (τ v)).valuation E (sx v))
      (fun v => ((GlobalTheory.AdelicU.splitPrime (τ v)).valuation E (sy v))⁻¹)
  obtain ⟨c, hc0, hc⟩ := exists_valuation_eq w hw t (by
    rintro (v | v)
    · exact (map_ne_zero _).2 (hsx0 v)
    · exact inv_ne_zero ((map_ne_zero _).2 (hsy0 v)))
  refine ⟨c, hc0, fun v => ⟨primAt_smul hc0 (hsxL v) (hsxmax v) (hc (Sum.inl v)),
    primAt_smul (inv_ne_zero ((map_ne_zero σ).2 hc0)) (hsyL v) (hsymax v) ?_⟩⟩
  have h1 := hc (Sum.inr v)
  simp only [w, t, Sum.elim_inr] at h1
  rw [← GlobalTheory.AdelicU.valued_apply_eq_valuation, AlgHom.comp_apply, GlobalTheory.AdelicU.valued_apply_eq_valuation] at h1
  rw [map_inv₀, h1, inv_inv]

end GlobalTheory.PlaneSkewScale
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRescalePrimitiveInLatticeAtSplitPrimesStatement
open scoped TensorProduct Matrix nonZeroDivisors
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.PlaneSkew
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rescale_primitive_in_lattice_at_split_primes : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)), L.IsFullLattice E → ∀ x y : Fin n → E, x ≠ 0 → y ≠ 0 →
    ∀ (P : Finset (HeightOneSpectrum (𝓞 F))) (τ : ∀ v : P, E →ₐ[F] Fv F v.1), ∃ c : E, c ≠ 0 ∧
      ∀ v : P, PrimAt (GlobalTheory.AdelicU.splitPrime (τ v)) L (c • x) ∧ PrimAt (GlobalTheory.AdelicU.splitPrime (τ v)) L ((σ c)⁻¹ • y) := by
  first | exact @GlobalTheory.PlaneSkewScale.exists_rescale_primAt | exact GlobalTheory.PlaneSkewScale.exists_rescale_primAt | (intros; apply GlobalTheory.PlaneSkewScale.exists_rescale_primAt <;> first | assumption | exact (by assumption : Submodule.IsFullLattice _ _).toIsLattice)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TermEqOfSimilitudeRel
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TermEqOfSimilitudeRel
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.LKMid.RelMove

section Generic

variable {S A : Type*} [Ring S] [CommRing A] [Algebra A S]

theorem triv_move (σ : S →+* Sᵐᵒᵖ) (b : S) (x Y : Sˣ) (t s : A)
    (hx : (x : S) * b * (σ x).unop = algebraMap A S t) :
    ((x * Y⁻¹ : Sˣ) : S) * (algebraMap A S s * ((Y : S) * b * (σ Y).unop)) * (σ ((x * Y⁻¹ : Sˣ) : S)).unop =
      algebraMap A S (s * t) := by
  have h1 : (σ Y).unop * (σ ((Y⁻¹ : Sˣ) : S)).unop = 1 := by
    rw [← MulOpposite.unop_mul, ← map_mul, Units.inv_mul, map_one, MulOpposite.unop_one]
  calc ((x * Y⁻¹ : Sˣ) : S) * (algebraMap A S s * ((Y : S) * b * (σ Y).unop)) * (σ ((x * Y⁻¹ : Sˣ) : S)).unop
      = s • ((x : S) * ((((Y⁻¹ : Sˣ) : S) * Y) * b * ((σ Y).unop * (σ ((Y⁻¹ : Sˣ) : S)).unop)) * (σ x).unop) := by
        simp only [Units.val_mul, map_mul, MulOpposite.unop_mul, ← Algebra.smul_def, mul_smul_comm,
          smul_mul_assoc, mul_assoc]
    _ = algebraMap A S (s * t) := by
        rw [Units.inv_mul, h1, one_mul, mul_one, hx, map_mul, Algebra.smul_def]

end Generic

variable {p : ℕ} [Fact p.Prime] {G : HTGroup p}

theorem sh_mul (a b : G.C) : sh G (a * b) = sh G b * sh G a := by
  simp only [sh, map_mul, MulOpposite.unop_mul]

theorem sh_units (y : G.Cˣ) : sh G (y : G.C) * sh G ((y⁻¹ : G.Cˣ) : G.C) = 1 := by
  rw [← sh_mul, Units.inv_mul]; simp [sh]

theorem key (y v : G.Cˣ) (β : G.C) (s : ℚ) :
    ((y * v * y⁻¹ : G.Cˣ) : G.C) * (algebraMap ℚ G.C s * (y * β * sh G y)) * sh G ((y * v * y⁻¹ : G.Cˣ) : G.C) =
      algebraMap ℚ G.C s * (y * ((v : G.C) * β * sh G v) * sh G y) := by
  calc ((y * v * y⁻¹ : G.Cˣ) : G.C) * (algebraMap ℚ G.C s * (y * β * sh G y)) * sh G ((y * v * y⁻¹ : G.Cˣ) : G.C)
      = s • ((y : G.C) * v * (((y⁻¹ : G.Cˣ) : G.C) * y) * β * (sh G y * sh G ((y⁻¹ : G.Cˣ) : G.C)) *
          sh G v * sh G y) := by
        simp only [Units.val_mul, sh_mul, ← Algebra.smul_def, mul_smul_comm, smul_mul_assoc, mul_assoc]
    _ = _ := by
        rw [Units.inv_mul, sh_units, mul_one, mul_one, Algebra.smul_def]; simp only [mul_assoc]

theorem scal (y : G.Cˣ) (β : G.C) (s u : ℚ) :
    algebraMap ℚ G.C u * (algebraMap ℚ G.C s * (y * β * sh G y)) =
      algebraMap ℚ G.C s * (y * (algebraMap ℚ G.C u * β) * sh G y) := by
  simp only [← Algebra.smul_def, mul_smul_comm, smul_mul_assoc, smul_smul, mul_comm u s]

theorem cancel (y : G.Cˣ) (X Z : G.C) (s : ℚ) (hs : s ≠ 0)
    (h : algebraMap ℚ G.C s * (y * X * sh G y) = algebraMap ℚ G.C s * (y * Z * sh G y)) : X = Z := by
  have h' : (y : G.C) * X * sh G y = y * Z * sh G y := by
    have := congrArg (fun w => algebraMap ℚ G.C s⁻¹ * w) h
    simpa only [← mul_assoc, ← map_mul, inv_mul_cancel₀ hs, map_one, one_mul] using this
  have e : ∀ W : G.C, W = ((y⁻¹ : G.Cˣ) : G.C) * (y * W * sh G y) * sh G ((y⁻¹ : G.Cˣ) : G.C) := by
    intro W
    rw [mul_assoc, mul_assoc, sh_units, mul_one, ← mul_assoc, Units.inv_mul, one_mul]
  rw [e X, e Z, h']

def cj (y : G.Cˣ) : G.Cˣ × ℚˣ ≃* G.Cˣ × ℚˣ := (MulAut.conj y).prodCongr (MulEquiv.refl ℚˣ)

theorem cj_apply (y : G.Cˣ) (v : G.Cˣ × ℚˣ) : cj y v = (y * v.1 * y⁻¹, v.2) := rfl

theorem mem_of (P Q : Pair G) (y : G.Cˣ) (s : ℚ) (hβ : (Q.β : G.C) = algebraMap ℚ G.C s * (y * P.β * sh G y))
    (hγ : Q.γ = y * P.γ * y⁻¹) (v : G.Cˣ × ℚˣ) (hv : v ∈ P.cent) : cj y v ∈ Q.cent := by
  obtain ⟨h1, h2⟩ := hv
  change v.1 * P.γ = P.γ * v.1 at h1
  change (v.1 : G.C) * P.β * sh G v.1 = algebraMap ℚ G.C v.2 * P.β at h2
  refine ⟨?_, ?_⟩
  · change y * v.1 * y⁻¹ * Q.γ = Q.γ * (y * v.1 * y⁻¹)
    rw [hγ]
    calc y * v.1 * y⁻¹ * (y * P.γ * y⁻¹) = y * (v.1 * P.γ) * y⁻¹ := by group
      _ = y * (P.γ * v.1) * y⁻¹ := by rw [h1]
      _ = _ := by group
  · change ((y * v.1 * y⁻¹ : G.Cˣ) : G.C) * Q.β * sh G ((y * v.1 * y⁻¹ : G.Cˣ) : G.C) =
      algebraMap ℚ G.C v.2 * Q.β
    rw [hβ, key, h2, scal]

theorem mem_back (P Q : Pair G) (y : G.Cˣ) (s : ℚ) (hs : s ≠ 0)
    (hβ : (Q.β : G.C) = algebraMap ℚ G.C s * (y * P.β * sh G y))
    (hγ : Q.γ = y * P.γ * y⁻¹) (w : G.Cˣ × ℚˣ) (hw : w ∈ Q.cent) : (cj y).symm w ∈ P.cent := by
  obtain ⟨h1, h2⟩ := hw
  set v := (cj y).symm w with hv
  have hw' : w = cj y v := by rw [hv, MulEquiv.apply_symm_apply]
  rw [hw', cj_apply] at h1 h2
  change y * v.1 * y⁻¹ * Q.γ = Q.γ * (y * v.1 * y⁻¹) at h1
  change ((y * v.1 * y⁻¹ : G.Cˣ) : G.C) * Q.β * sh G ((y * v.1 * y⁻¹ : G.Cˣ) : G.C) =
      algebraMap ℚ G.C v.2 * Q.β at h2
  refine ⟨?_, ?_⟩
  · change v.1 * P.γ = P.γ * v.1
    rw [hγ] at h1
    have : y * (v.1 * P.γ) * y⁻¹ = y * (P.γ * v.1) * y⁻¹ := by
      calc y * (v.1 * P.γ) * y⁻¹ = y * v.1 * y⁻¹ * (y * P.γ * y⁻¹) := by group
        _ = (y * P.γ * y⁻¹) * (y * v.1 * y⁻¹) := h1
        _ = _ := by group
    simpa using this
  · change (v.1 : G.C) * P.β * sh G v.1 = algebraMap ℚ G.C v.2 * P.β
    rw [hβ, key, scal] at h2
    exact cancel y _ _ s hs h2

theorem cent_map (P Q : Pair G) (y : G.Cˣ) (s : ℚ) (hs : s ≠ 0)
    (hβ : (Q.β : G.C) = algebraMap ℚ G.C s * (y * P.β * sh G y))
    (hγ : Q.γ = y * P.γ * y⁻¹) : P.cent.map (cj y).toMonoidHom = Q.cent := by
  ext w
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact mem_of P Q y s hβ hγ v hv
  · intro hw
    exact ⟨(cj y).symm w, mem_back P Q y s hs hβ hγ w hw, by simp⟩

theorem toAf_val (P : Pair G) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) P.β x t) (v : P.cent) :
    ((P.toAf x t hx v : G.GAf) : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ) =
      (x * Units.map (inC G (AfP p)).toMonoidHom v.1.1 * x⁻¹, Units.map (algebraMap ℚ (AfP p)).toMonoidHom v.1.2) :=
  rfl

theorem toQr_val (P : Pair G) (r : ℕ) (z : Gr G r) (v : P.cent) :
    P.toQr r z v = z⁻¹ * inclG G r (locC G v.1) * z := by
  simp [Pair.toQr, carry, MulAut.conj_apply]

theorem locC_conj (y : G.Cˣ) (v : G.Cˣ × ℚˣ) :
    locC G (y * v.1 * y⁻¹, v.2) = locC G (y, 1) * locC G v * (locC G (y, 1))⁻¹ := by
  rw [← map_inv, ← map_mul, ← map_mul]
  congr 1
  ext <;> simp

theorem triv_rel (P Q : Pair G) (y : G.Cˣ) (s : ℚ) (hs : s ≠ 0)
    (hβ : (Q.β : G.C) = algebraMap ℚ G.C s * (y * P.β * sh G y))
    (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) P.β x t) :
    Triv G (AfP p) Q.β (x * (Units.map (inC G (AfP p)).toMonoidHom y)⁻¹)
      (Units.map (algebraMap ℚ (AfP p)).toMonoidHom (Units.mk0 s hs) * t) := by
  have e1 : inC G (AfP p) (sh G y) = (starT G.star (AfP p) (inC G (AfP p) y)).unop :=
    (starT_tmul G.star (AfP p) 1 _).symm
  have e2 : inC G (AfP p) (algebraMap ℚ G.C s) =
      algebraMap (AfP p) (AfP p ⊗[ℚ] G.C) (algebraMap ℚ (AfP p) s) := by
    rw [← IsScalarTower.algebraMap_apply]
    exact (Algebra.TensorProduct.includeRight : G.C →ₐ[ℚ] AfP p ⊗[ℚ] G.C).commutes _
  unfold Triv
  rw [hβ, map_mul, map_mul, map_mul, e1, e2]
  have := triv_move (starT G.star (AfP p)) (inC G (AfP p) P.β) x (Units.map (inC G (AfP p)).toMonoidHom y)
    (t : AfP p) (algebraMap ℚ (AfP p) s) hx
  simpa [mul_assoc] using this

end GlobalTheory.LKMid.RelMove

namespace GlobalTheory.LKMid.Pair


open GlobalTheory.LKMid.RelMove in
theorem term_eq_of_rel : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P Q : Pair G) (Kf : Subgroup G.GAf)
    (f : G.GAf → ℂ) (r : ℕ) (K : Subgroup (Gr G r)) (φ : Gr G r → ℂ), 0 < r →
    (∀ k ∈ Kf, ∀ g, f (k⁻¹ * g * k) = f g) → (∀ k ∈ K, ∀ g, φ (k⁻¹ * g * sigG G r k) = φ g) →
    P.Rel Q → Q.term Kf f r K φ = P.term Kf f r K φ := by
  intro p _ G P Q Kf f r K φ hr hf hφ hPQ
  obtain ⟨y, s, hs, hβ, hγ⟩ := hPQ
  have hc : Q.c = P.c := (GlobalTheory.T.related_pairs_same_polarization p G P Q ⟨y, s, hs, hβ, hγ⟩).2
  have hat : Q.atP = locC G (y, 1) * P.atP * (locC G (y, 1))⁻¹ := by
    have := locC_conj y (P.γ, P.c)
    simp only [Pair.atP, hγ, hc]
    exact this
  have hnrm : ∀ δ z, IsNrm G r P.atP δ z → IsNrm G r Q.atP δ (inclG G r (locC G (y, 1)) * z) := by
    intro δ z h
    unfold IsNrm at h ⊢
    rw [h, hat, map_mul, map_mul, map_inv]
    group
  by_cases hP : ∃ dz : Gr G r × Gr G r, IsNrm G r P.atP dz.1 dz.2
  · obtain ⟨⟨δ, z⟩, hδ⟩ := hP
    obtain ⟨x, t, hx⟩ := P.trivAf
    have hx' := triv_rel P Q y s hs.ne' hβ x t hx
    rw [GlobalTheory.T.kottwitzPair_term_eq_pointSum_any_trivialisation p G P Kf f r K φ hr hf hφ x t hx δ z hδ,
      GlobalTheory.T.kottwitzPair_term_eq_pointSum_any_trivialisation p G Q Kf f r K φ hr hf hφ _ _ hx' δ _ (hnrm δ z hδ)]
    let e : P.cent ≃* Q.cent := ((cj y).subgroupMap P.cent).trans
      (MulEquiv.subgroupCongr (cent_map P Q y s hs.ne' hβ hγ))
    have he : ∀ v : P.cent, ((e v : Q.cent) : G.Cˣ × ℚˣ) = cj y v := fun v => rfl
    have hA : (Q.toAf _ _ hx').comp e.toMonoidHom = P.toAf x t hx := by
      ext v : 1
      apply Subtype.ext
      rw [MonoidHom.comp_apply, toAf_val, toAf_val]
      simp only [MulEquiv.coe_toMonoidHom, he, cj_apply]
      refine Prod.ext ?_ rfl
      simp only [map_mul, map_inv]
      group
    have hQr : (Q.toQr r (inclG G r (locC G (y, 1)) * z)).comp e.toMonoidHom = P.toQr r z := by
      ext v : 1
      rw [MonoidHom.comp_apply, toQr_val, toQr_val]
      simp only [MulEquiv.coe_toMonoidHom, he, cj_apply]
      rw [locC_conj, map_mul, map_mul, map_inv]
      group
    have hS : Q.self = e P.self := by
      apply Subtype.ext
      rw [he, cj_apply]
      exact Prod.ext hγ hc
    unfold termAt
    have hS' : Q.toAf _ _ hx' (e P.self) = P.toAf x t hx P.self := by rw [← hA]; rfl
    rw [hS, ← GlobalTheory.T.kottwitzIsogenyClassPointSum_comp_mulEquiv e, hS', hA, hQr]
  · have hQ : ¬ ∃ dz : Gr G r × Gr G r, IsNrm G r Q.atP dz.1 dz.2 := by
      rintro ⟨⟨δ, z⟩, h⟩
      apply hP
      refine ⟨(δ, (inclG G r (locC G (y, 1)))⁻¹ * z), ?_⟩
      unfold IsNrm at h ⊢
      rw [h, hat, map_mul, map_mul, map_inv]
      group
    unfold term
    rw [dite_eq_right hP, dite_eq_right hQ]

end GlobalTheory.LKMid.Pair
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TermEqOfSimilitudeRelStatement
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.term_eq_of_similitude_rel : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P Q : Pair G) (Kf : Subgroup G.GAf) (f : G.GAf → ℂ) (r : ℕ) (K : Subgroup (Gr G r)) (φ : Gr G r → ℂ), 0 < r → (∀ k ∈ Kf, ∀ g, f (k⁻¹ * g * k) = f g) → (∀ k ∈ K, ∀ g, φ (k⁻¹ * g * sigG G r k) = φ g) → P.Rel Q → Q.term Kf f r K φ = P.term Kf f r K φ := by
  first | (exact @GlobalTheory.LKMid.Pair.term_eq_of_rel) | (exact GlobalTheory.LKMid.Pair.term_eq_of_rel) | (intros; apply GlobalTheory.LKMid.Pair.term_eq_of_rel <;> assumption)
end
end
