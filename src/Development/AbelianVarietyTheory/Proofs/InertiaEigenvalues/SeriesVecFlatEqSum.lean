module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjThetaClassSumEqRootOfUnityConjTuple
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeChoiceFlatScalarConjTwist

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugateThetaLiftsIsConjugateCuspExpansion
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugateThetaLiftsIsConjugateCuspExpansion
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ConjCombine

variable {X B : Type} (φ : B → X → ℂ) (τ : ℂ ≃+* ℂ)

def Exp (Φ : X → ℂ) {n : ℕ} (a : Fin n → ℂ) (F : Fin n → B) : Prop :=
  ∀ g, Φ g = ∑ k, a k * φ (F k) g

def CF (ζ : ℂ) (Φ Φ' : X → ℂ) : Prop :=
  (∃ (n : ℕ) (a : Fin n → ℂ) (F : Fin n → B), Exp φ Φ a F) ∧
    ∀ (n : ℕ) (a : Fin n → ℂ) (F : Fin n → B), Exp φ Φ a F → Exp φ Φ' (fun k => ζ * τ (a k)) F

variable {φ τ}

theorem conj_wd {Ψ Ψ' : X → ℂ} (h0 : CF φ τ 1 Ψ Ψ') {Φ : X → ℂ} {n m : ℕ} {a : Fin n → ℂ} {F : Fin n → B}
    {b : Fin m → ℂ} {G : Fin m → B} (ha : Exp φ Φ a F) (hb : Exp φ Φ b G) (g : X) :
    ∑ k, τ (a k) * φ (F k) g = ∑ k, τ (b k) * φ (G k) g := by
  obtain ⟨p, c, H, hc⟩ := h0.1
  have hall : Exp φ Ψ (Fin.append c (Fin.append a (-b))) (Fin.append H (Fin.append F G)) := by
    intro x
    rw [Fin.sum_univ_add, Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]
    rw [hc x, ← ha x, ← hb x]
    ring
  have e1 := h0.2 _ _ _ hc g
  have e2 := h0.2 _ _ _ hall g
  rw [Fin.sum_univ_add, Fin.sum_univ_add] at e2
  simp only [Fin.append_left, Fin.append_right, Pi.neg_apply, map_neg, one_mul, neg_mul,
    Finset.sum_neg_distrib] at e1 e2
  rw [e1] at e2
  linear_combination -e2

theorem conj_comb {Ψ Ψ' : X → ℂ} (h0 : CF φ τ 1 Ψ Ψ') {m : ℕ} (β : Fin m → ℂ) (Φs Φs' : Fin m → X → ℂ)
    (h : ∀ k, CF φ τ 1 (Φs k) (Φs' k)) (c : ℂ) :
    CF φ τ c (fun g => ∑ k, β k * Φs k g) (fun g => c * ∑ k, τ (β k) * Φs' k g) := by
  choose n b G hG using fun k => (h k).1
  let e := (finSigmaFinEquiv (n := n)).symm
  have hflat : Exp φ (fun g => ∑ k, β k * Φs k g) (fun q => β (e q).1 * b (e q).1 (e q).2)
      (fun q => G (e q).1 (e q).2) := by
    intro g
    rw [Fintype.sum_equiv e (fun q => β (e q).1 * b (e q).1 (e q).2 * φ (G (e q).1 (e q).2) g)
      (fun p => β p.1 * b p.1 p.2 * φ (G p.1 p.2) g) (fun _ => rfl), Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hG k g, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  refine ⟨⟨_, _, _, hflat⟩, fun N a F ha g => ?_⟩
  have hw := conj_wd h0 ha hflat g
  rw [Fintype.sum_equiv e (fun q => τ (β (e q).1 * b (e q).1 (e q).2) * φ (G (e q).1 (e q).2) g)
      (fun p => τ (β p.1 * b p.1 p.2) * φ (G p.1 p.2) g) (fun _ => rfl), Fintype.sum_sigma] at hw
  have hc : ∀ k, Φs' k g = ∑ j, τ (b k j) * φ (G k j) g := fun k => by
    rw [(h k).2 _ _ _ (hG k) g]
    simp only [one_mul]
  show c * ∑ k, τ (β k) * Φs' k g = ∑ k, c * τ (a k) * φ (F k) g
  simp only [hc, map_mul] at hw ⊢
  have e3 : ∑ k, c * τ (a k) * φ (F k) g = c * ∑ k, τ (a k) * φ (F k) g := by
    rw [Finset.mul_sum]; simp only [mul_assoc]
  rw [e3, hw]
  simp only [Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring

end GlobalTheory.ConjCombine

namespace GlobalTheory.ConjClassSum

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {i : Fin D.R.m}

theorem conjFun_iff {Tp : Type} {tup : Tp → T0} (O : OMDat T.toCore R i Tp tup) (κ : WeightFamilies.Wt D ((i : ℕ) + 1))
    (τ : ℂ ≃+* ℂ) (ζ : ℂ) (Φ Φ' : GA D (Wc D i) → ℂ) :
    ConjFun O κ τ ζ Φ Φ' ↔ GlobalTheory.ConjCombine.CF (fun (F : T.toCore.cuspA ((i : ℕ) + 1) (wtA κ) κ.n) g =>
      (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA κ) : ℂ) * O.phi (T.cE ((i : ℕ) + 1) O.s0) (F : T.toCore.R ((i : ℕ) + 1)) g)
      τ ζ Φ Φ' := Iff.rfl

theorem conjFun_congr {Tp Tp' : Type} {tup : Tp → T0} {tup' : Tp' → T0} (O : OMDat T.toCore R i Tp tup)
    (O' : OMDat T.toCore R i Tp' tup') (κ : WeightFamilies.Wt D ((i : ℕ) + 1)) (τ : ℂ ≃+* ℂ) (ζ : ℂ) (Φ Φ' : GA D (Wc D i) → ℂ) :
    ConjFun O κ τ ζ Φ Φ' ↔ ConjFun O' κ τ ζ Φ Φ' := by
  unfold ConjFun Expands
  rw [GlobalTheory.OneMapAll.phi_eq O O' (T.cE ((i : ℕ) + 1))]

def psi {Tp : Type} {tup : Tp → T0} (M : OMDat T.toCore R i Tp tup) (κ : WeightFamilies.Wt D ((i : ℕ) + 1)) (z : G)
    (f : Rul (T.Q.Xo ((i : ℕ) + 1)) M.c') (g : GA D (Wc D i)) : ℂ :=
  T.cE ((i : ℕ) + 1) M.s0 (M.dict g).1 * (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA κ) : ℂ) * M.mu g *
    rdU (unfBC M.hle (T.U ((i : ℕ) + 1)) (inC M.c')) (actLev M.c' M.lev2 z f) (M.dict g).1 (M.dict g).2

theorem psi_smul {Tp : Type} {tup : Tp → T0} (M : OMDat T.toCore R i Tp tup) (κ : WeightFamilies.Wt D ((i : ℕ) + 1)) (z : G)
    (u : M.c'.F) (f : Rul (T.Q.Xo ((i : ℕ) + 1)) M.c') (g : GA D (Wc D i)) :
    psi M κ z (u • f) g = (u : ℂ) * psi M κ z f g := by
  unfold psi
  rw [map_smul, map_smulₛₗ]
  show _ * ((u : ℂ) * _) = _
  ring


set_option maxHeartbeats 8000000 in
theorem conj_lifts : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : Fin D.R.m → ℂ), 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → GlobalTheory.Hk3.Core R F → Finite T0 → Nonempty (FWTie T R κ v₀) → IoExt R → QGuard R → ∀ i : Fin D.R.m, OMPins T R κ v₀ O i → PhaseTie T R κ v₀ O ph i → ∀ (c : VsV D i ℂ →ₗ[ℂ] (R.cV i).W), ExtC R i (inC (O i).c') (O i).c0' c → ∀ τ : ℂ ≃+* ℂ, FixBase T R i τ → ∃ ζ0 : ℂ, IsRoot1 ζ0 ∧ ∀ t t' : T0, ConjTup R τ t t' → ∃ s : (AE D)ˣ, ∀ (y : (R.HV i t).H) (y' : (R.HV i t').H), ConjForm R i τ c t t' y y' → ConjFun (O i) (κ i) τ (ζ0 * ((R.xi t' s : Circle) : ℂ)) (fun g => ph i * R.thF i t y (v₀ i (sg0 D A)) g) (fun g => ph i * R.thF i t' y' (v₀ i (sg0 D A)) g) := by
  intro hCI D G _ _ Pl0 T0 A T _ R F κ v₀ O ph hsz hC hT0 hFW hio hQ i hOP hPT c hc τ hτ
  obtain ⟨fw⟩ := hFW
  have hTie : TieIn T R κ v₀ := ⟨fw.laws, fw.alg_eq, fw.kap, fw.hv₀, fw.chiR, fw.x0⟩
  obtain ⟨M, hMP, hlev, hext, hnorm, hcurve, hxiF, hcov⟩ :=
    GlobalTheory.T.exists_normalisedData_normalCoefficientField D G Pl0 T0 A T R F κ v₀ O hC hT0 ⟨fw⟩ hQ i hOP

  let τQ : ℂ ≃ₐ[ℚ] ℂ := AlgEquiv.ofRingEquiv (f := τ) (fun q => map_ratCast τ q)
  let ta : M.c'.F ≃+* M.c'.F := (τQ.restrictNormal M.c'.F).toRingEquiv
  have hta : ∀ a : M.c'.F, ((ta a : M.c'.F) : ℂ) = τ (a : ℂ) := fun a => τQ.restrictNormal_commutes M.c'.F a

  have hEq0 : (O i).EquivAt (κ i) (T.cE ((i : ℕ) + 1) (O i).s0) :=
    (hPT (GlobalTheory.T.thetaOneMap_baseTuple_of_characterisation_extremal hCI D G Pl0 T0 A T R F κ v₀ hC hTie hio O i hOP)).1
  have hlev2 : M.lev2 = (O i).lev2 := by funext g; simp only [OMDat.lev2, hlev]
  have hEqM : M.EquivAt (κ i) (T.cE ((i : ℕ) + 1) M.s0) := by
    unfold OMDat.EquivAt at hEq0 ⊢
    rw [GlobalTheory.OneMapAll.phi_eq M (O i) (T.cE ((i : ℕ) + 1)), hlev2]
    exact hEq0
  have hcM : ExtC R i (inC M.c') M.c0' c := (hext c).1 hc

  obtain ⟨ζ, z, hζ, -, hser⟩ := GlobalTheory.T.oneMap_every_normalisedFamily_at_coreConstants hCI D G Pl0 T0 A T R F κ v₀ O ph hsz hC hT0 ⟨fw⟩ hio hQ i hOP hPT T0 id M hMP
    hlev hext
  obtain ⟨hf, k0, hk0, hgal⟩ := GlobalTheory.T.conj_thetaClassSum_eq_rootOfUnity_conjTuple hCI D G Pl0 T0 A T R F κ v₀ hC ⟨fw⟩ i T0 id M hMP τ ta hta hτ hcurve hxiF
  obtain ⟨a0, ha0, hza⟩ := hζ
  obtain ⟨b0, hb0, hkb⟩ := hk0
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    rw [zero_pow ha0.ne'] at hza
    exact zero_ne_one hza
  have hτζ : τ ζ ≠ 0 := (map_ne_zero τ).2 hζ0
  refine ⟨ζ * k0 / τ ζ, ⟨a0 * b0, Nat.mul_pos ha0 hb0, ?_⟩, fun t t' hct => ?_⟩
  · rw [div_pow, mul_pow, ← map_pow, pow_mul ζ a0 b0, hza, one_pow, pow_mul' k0 a0 b0, hkb, one_pow, map_one, div_one,
      one_mul]
  obtain ⟨e, hsame⟩ := hcov t t' hct.1
  obtain ⟨u, s, hu, hgal'⟩ := hgal t t' e hsame hct
  refine ⟨s, fun y y' hcf => ?_⟩
  obtain ⟨n, α, ys, ys', hy, hy', hval⟩ :=
    GlobalTheory.T.conjugate_definiteForms_descend_numberField D G Pl0 T0 A T R F κ v₀ hC ⟨fw⟩ i T0 id M hMP τ ta hta hτ c hcM hxiF t t' hct y y' hcf
  obtain ⟨h, J', hR, -⟩ := (hMP.tuple t).reps
  have hlevJ := ((GlobalTheory.T.conjugate_tuples_conjugate_residue_levels D G Pl0 T0 A T R F κ v₀ hC τ t t' hct).2.2.2 i hτ).1
  have hR' : RepsR R i t' (fun j => h (e.symm j)) (M.bad t') J' (M.Lh t') (M.gam t') (M.vol t') := by
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hR
    obtain ⟨-, -, -, hbad, hvol, hk⟩ := hsame
    have hQ' : R.Q t' = R.Q t := hct.1
    refine ⟨hbad ▸ h1, fun PP hPP => ?_, ?_, ?_, ?_, fun g => ?_, fun j => ?_⟩
    · rw [hbad]; exact h2 PP (hQ' ▸ hPP)
    · rw [hlevJ]; exact h3
    · rw [hlevJ]; exact h4
    · rw [hlevJ, hvol]; exact h5
    · obtain ⟨p, hp, huniq⟩ := h6 g
      refine ⟨e p, by simpa using hp, fun j hj => ?_⟩
      have := huniq (e.symm j) hj
      rw [← this]
      simp
    · obtain ⟨a1, a2, a3⟩ := h7 (e.symm j)
      have hkj := hk (e.symm j)
      simp only [Equiv.apply_symm_apply] at hkj
      exact ⟨hbad ▸ a1, hkj.1.trans a2, hkj.2.2.2.trans a3⟩

  choose xv xv' hxv using hval
  let xs : Fin n → M.Cl' t → VsV D i M.c'.F := fun k p => xv k (h p)
  let xs' : Fin n → M.Cl' t' → VsV D i M.c'.F := fun k j => xv' k (h (e.symm j))
  choose f hfc hfs using fun k => GlobalTheory.ClassSumRule.exists_cusp_isThClsD_core hCI D G Pl0 T0 A T R F κ v₀ hC hTie i T0 id M
    hMP t (xs k)
  have hsec : ∀ k, f k ∈ sec (T.Q.Xo ((i : ℕ) + 1)) M.c' (wtA (κ i)) (Vc D i).rank := fun k =>
    cusp_le_sec _ _ _ _ _ (hfc k)
  have hA : ∀ k g, ph i * R.thF i t (ys k) (v₀ i (sg0 D A)) g = ζ * psi M (κ i) z (f k) g := fun k g => by
    refine (hser t h J' hR (ys k) (xs k) (fun p => (hxv k (h p)).2.1) (f k) (hsec k) (hfs k) g).trans ?_
    unfold psi
    ring
  have hG : ∀ k, u • galRul hf (f k) ∈ sec (T.Q.Xo ((i : ℕ) + 1)) M.c' (wtA (κ i)) (Vc D i).rank ∧
      GlobalTheory.OneMapAll.IsSum M t' (xs' k) (u • galRul hf (f k)) := fun k =>
    hgal' (xs k) (xs' k) (fun p => by simp only [xs, xs', Equiv.symm_apply_apply]; exact (hxv k (h p)).1) (f k) (hsec k)
      (hfs k)
  have hB : ∀ k g, ph i * R.thF i t' (ys' k) (v₀ i (sg0 D A)) g = ζ * (u : ℂ) * psi M (κ i) z (galRul hf (f k)) g :=
    fun k g => by
    refine (hser t' (fun j => h (e.symm j)) J' hR' (ys' k) (xs' k) (fun j => (hxv k (h (e.symm j))).2.2)
      (u • galRul hf (f k)) (hG k).1 (hG k).2 g).trans ?_
    rw [show ζ * (u : ℂ) * psi M (κ i) z (galRul hf (f k)) g = ζ * ((u : ℂ) * psi M (κ i) z (galRul hf (f k)) g) by ring,
      ← psi_smul]
    unfold psi
    ring
  have hbc : ∀ k, ConjFun M (κ i) τ 1 (psi M (κ i) z (f k)) (psi M (κ i) z (galRul hf (f k))) := fun k =>
    GlobalTheory.T.cuspFormReading_galoisConj_expansion D G Pl0 T0 A T R F κ v₀ hC ⟨fw⟩ i T0 id M hMP τ ta hta hτ hf z (f k) (hfc k) hEqM
  have hbc0 : ConjFun M (κ i) τ 1 (psi M (κ i) z 0) (psi M (κ i) z (galRul hf 0)) :=
    GlobalTheory.T.cuspFormReading_galoisConj_expansion D G Pl0 T0 A T R F κ v₀ hC ⟨fw⟩ i T0 id M hMP τ ta hta hτ hf z 0 (Submodule.zero_mem _) hEqM
  have hcomb := GlobalTheory.ConjCombine.conj_comb ((conjFun_iff M (κ i) τ 1 _ _).1 hbc0) (fun k => ζ * α k)
    (fun k => psi M (κ i) z (f k)) (fun k => psi M (κ i) z (galRul hf (f k)))
    (fun k => (conjFun_iff M (κ i) τ 1 _ _).1 (hbc k)) (ζ * k0 / τ ζ * ((R.xi t' s : Circle) : ℂ))
  have hΦ : (fun g => ph i * R.thF i t y (v₀ i (sg0 D A)) g) =
      fun g => ∑ k, (ζ * α k) * psi M (κ i) z (f k) g := by
    funext g
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hy, map_sum]
    simp only [map_smul, MultilinearMap.sum_apply, MultilinearMap.smul_apply, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_left_comm, hA k g]
    ring
  have hΦ' : (fun g => ph i * R.thF i t' y' (v₀ i (sg0 D A)) g) =
      fun g => ζ * k0 / τ ζ * ((R.xi t' s : Circle) : ℂ) * ∑ k, τ (ζ * α k) * psi M (κ i) z (galRul hf (f k)) g := by
    funext g
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hy', map_sum]
    simp only [map_smul, MultilinearMap.sum_apply, MultilinearMap.smul_apply, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hu' : (u : ℂ) = k0 * ((R.xi t' s : Circle) : ℂ) := hu
    have hcan : ζ * k0 / τ ζ * τ ζ = ζ * k0 := div_mul_cancel₀ _ hτζ
    rw [mul_left_comm, hB k g, hu', map_mul]
    linear_combination (-(τ (α k) * ((R.xi t' s : Circle) : ℂ) * psi M (κ i) z (galRul hf (f k)) g)) * hcan
  rw [conjFun_congr (O i) M, conjFun_iff, hΦ, hΦ']
  exact hcomb

end GlobalTheory.ConjClassSum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugateThetaLiftsIsConjugateCuspExpansionStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugate_thetaLifts_isConjugateCuspExpansion : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : Fin D.R.m → ℂ), 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → GlobalTheory.Hk3.Core R F → Finite T0 → Nonempty (FWTie T R κ v₀) → IoExt R → QGuard R → ∀ i : Fin D.R.m, OMPins T R κ v₀ O i → PhaseTie T R κ v₀ O ph i → ∀ (c : VsV D i ℂ →ₗ[ℂ] (R.cV i).W), ExtC R i (inC (O i).c') (O i).c0' c → ∀ τ : ℂ ≃+* ℂ, FixBase T R i τ → ∃ ζ0 : ℂ, IsRoot1 ζ0 ∧ ∀ t t' : T0, ConjTup R τ t t' → ∃ s : (AE D)ˣ, ∀ (y : (R.HV i t).H) (y' : (R.HV i t').H), ConjForm R i τ c t t' y y' → ConjFun (O i) (κ i) τ (ζ0 * ((R.xi t' s : Circle) : ℂ)) (fun g => ph i * R.thF i t y (v₀ i (sg0 D A)) g) (fun g => ph i * R.thF i t' y' (v₀ i (sg0 D A)) g) := by
  first | exact @GlobalTheory.ConjClassSum.conj_lifts | exact GlobalTheory.ConjClassSum.conj_lifts | (intros; apply GlobalTheory.ConjClassSum.conj_lifts <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugateThetaSeriesFlatDatumRootOfUnity
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugateTuplesTwistedThetaSeriesConjugate
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugateTuplesTwistedThetaSeriesConjugate
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical


set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem GlobalTheory.ConjTwist.conjFun_ser : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : Fin D.R.m → ℂ), 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → GlobalTheory.Hk3.Core R F → Finite T0 → Nonempty (FWTie T R κ v₀) → IoExt R → QGuard R → ∀ i : Fin D.R.m, OMPins T R κ v₀ O i → PhaseTie T R κ v₀ O ph i → ∀ (c : VsV D i ℂ →ₗ[ℂ] (R.cV i).W), ExtC R i (inC (O i).c') (O i).c0' c → ∀ u : (∀ ρ, lowT (R.MW i (sg0 D A)) ρ), (∀ ρ, (u ρ : (R.MW i (sg0 D A)).sm ρ) = v₀ i (sg0 D A) ρ) → ∀ τ : ℂ ≃+* ℂ, FixBase T R i τ → ∃ ζ0 : ℂ, IsRoot1 ζ0 ∧ ∀ t t' : T0, ConjTup R τ t t' → ∃ s : (AE D)ˣ, ∀ h ∈ GfC (Vc D i), ∀ x x' : VsV D i ℂ, ConjVec i τ x x' → ConjFun (O i) (κ i) τ (ζ0 * ((R.xi t' s : Circle) : ℂ)) (fun g => ph i * ser R i t (R.vP i t) u h (c x) g) (fun g => ph i * ser R i t' (R.vP i t') u h (c x') g) := by
  intro hCI D G _ _ Pl0 T0 A T _ R F κ v₀ O ph hn hC hT0 hFW hIo hQ i hP hPh c hc u hu τ hfix
  obtain ⟨ζ0, hζ, H⟩ := GlobalTheory.T.conjugate_thetaLifts_isConjugateCuspExpansion hCI D G Pl0 T0 A T R F κ v₀ O ph hn hC hT0 hFW hIo hQ i hP hPh c hc τ hfix
  refine ⟨ζ0, hζ, fun t t' ht => ?_⟩
  obtain ⟨s, Hs⟩ := H t t' ht
  refine ⟨s, fun h hh x x' hx => ?_⟩
  obtain ⟨y, y', hy, he⟩ := GlobalTheory.T.exists_conjugateForms_thetaLift_eq_thetaSeries D G Pl0 T0 A T R F κ v₀ hC hFW i Unit (fun _ => A.μ0) (O i) hP.2 c hc τ t t' hfix ht h hh x x' hx
  have hv : (fun ρ => (u ρ : (R.MW i (sg0 D A)).sm ρ)) = v₀ i (sg0 D A) := funext hu
  have e1 : (fun g => ph i * ser R i t (R.vP i t) u h (c x) g) = fun g => ph i * R.thF i t y (v₀ i (sg0 D A)) g := by
    funext g
    rw [← (he u g).1, hv]
  have e2 : (fun g => ph i * ser R i t' (R.vP i t') u h (c x') g) = fun g => ph i * R.thF i t' y' (v₀ i (sg0 D A)) g := by
    funext g
    rw [← (he u g).2, hv]
  rw [e1, e2]
  exact Hs y y' hy
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugateTuplesTwistedThetaSeriesConjugateStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugate_tuples_twisted_thetaSeries_conjugate : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : Fin D.R.m → ℂ), 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → GlobalTheory.Hk3.Core R F → Finite T0 → Nonempty (FWTie T R κ v₀) → IoExt R → QGuard R → ∀ i : Fin D.R.m, OMPins T R κ v₀ O i → PhaseTie T R κ v₀ O ph i → ∀ (c : VsV D i ℂ →ₗ[ℂ] (R.cV i).W), ExtC R i (inC (O i).c') (O i).c0' c → ∀ u : (∀ ρ, lowT (R.MW i (sg0 D A)) ρ), (∀ ρ, (u ρ : (R.MW i (sg0 D A)).sm ρ) = v₀ i (sg0 D A) ρ) → ∀ τ : ℂ ≃+* ℂ, FixBase T R i τ → ∃ ζ0 : ℂ, IsRoot1 ζ0 ∧ ∀ t t' : T0, ConjTup R τ t t' → ∃ s : (AE D)ˣ, ∀ h ∈ GfC (Vc D i), ∀ x x' : VsV D i ℂ, ConjVec i τ x x' → ConjFun (O i) (κ i) τ (ζ0 * ((R.xi t' s : Circle) : ℂ)) (fun g => ph i * ser R i t (R.vP i t) u h (c x) g) (fun g => ph i * ser R i t' (R.vP i t') u h (c x') g) := by
  first | exact @GlobalTheory.ConjTwist.conjFun_ser | exact GlobalTheory.ConjTwist.conjFun_ser | (intros; apply GlobalTheory.ConjTwist.conjFun_ser <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugateThetaSeriesFlatDatumRootOfUnity
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

set_option autoImplicit false

namespace GlobalTheory.ConjTwist.FlatSeries

theorem scale {X B : Type} (J : B → X → ℂ) (τ : ℂ ≃+* ℂ) (ζ η C C' : ℂ) (Φ Φ' : X → ℂ)
    (h1 : ∃ (n : ℕ) (a : Fin n → ℂ) (f : Fin n → B), ∀ g, Φ g = ∑ k, a k * J (f k) g)
    (h2 : ∀ (n : ℕ) (a : Fin n → ℂ) (f : Fin n → B), (∀ g, Φ g = ∑ k, a k * J (f k) g) →
      ∀ g, Φ' g = ∑ k, ζ * τ (a k) * J (f k) g)
    (hC : C' = η * τ C) :
    (∃ (n : ℕ) (a : Fin n → ℂ) (f : Fin n → B), ∀ g, C * Φ g = ∑ k, a k * J (f k) g) ∧
      ∀ (n : ℕ) (a : Fin n → ℂ) (f : Fin n → B), (∀ g, C * Φ g = ∑ k, a k * J (f k) g) →
        ∀ g, C' * Φ' g = ∑ k, ζ * η * τ (a k) * J (f k) g := by
  refine ⟨?_, ?_⟩
  · obtain ⟨n, a, f, h⟩ := h1
    refine ⟨n, fun k => C * a k, f, fun g => ?_⟩
    rw [h g, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  · intro n a f ha g
    by_cases hC0 : C = 0
    · subst hC0
      obtain ⟨n₀, b, e, hb⟩ := h1
      have hC' : C' = 0 := by simp [hC]
      have hz : ∀ g, ∑ k, a k * J (f k) g = 0 := fun g => by simpa using (ha g).symm
      have hcat : ∀ g, Φ g = ∑ k, (Fin.append b a) k * J ((Fin.append e f) k) g := fun g => by
        rw [Fin.sum_univ_add]
        simp only [Fin.append_left, Fin.append_right]
        rw [hz g, add_zero, hb g]
      have e1 := h2 _ _ _ hcat g
      have e2 := h2 _ _ _ hb g
      rw [Fin.sum_univ_add] at e1
      simp only [Fin.append_left, Fin.append_right] at e1
      rw [e2] at e1
      have e3 : ∑ k, ζ * τ (a k) * J (f k) g = 0 := by simpa using e1.symm
      have e4 : ∑ k, ζ * η * τ (a k) * J (f k) g = η * ∑ k, ζ * τ (a k) * J (f k) g := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring
      rw [e4, e3, hC']
      simp
    · have hτ : τ C ≠ 0 := fun h => hC0 ((map_eq_zero_iff τ τ.injective).1 h)
      have hexp : ∀ g, Φ g = ∑ k, (C⁻¹ * a k) * J (f k) g := fun g => by
        have : Φ g = C⁻¹ * (C * Φ g) := by field_simp
        rw [this, ha g, Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring
      rw [h2 _ _ _ hexp g, hC, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_mul, map_inv₀]
      field_simp

end GlobalTheory.ConjTwist.FlatSeries

section
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0}

theorem GlobalTheory.ConjTwist.FlatSeries.conjFun_scale (O : OMDat T.toCore R i Tp tup) (κ : WeightFamilies.Wt D ((i : ℕ) + 1)) (τ : ℂ ≃+* ℂ) {ζ η C C' : ℂ}
    {Φ Φ' : GA D (Wc D i) → ℂ} (h : ConjFun O κ τ ζ Φ Φ') (hC : C' = η * τ C) :
    ConjFun O κ τ (ζ * η) (fun g => C * Φ g) (fun g => C' * Φ' g) := by
  have key := GlobalTheory.ConjTwist.FlatSeries.scale
    (fun (b : T.toCore.cuspA ((i : ℕ) + 1) (wtA κ) κ.n) (g : GA D (Wc D i)) =>
      ((lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA κ) : ℂ) *
        O.phi (T.cE ((i : ℕ) + 1) O.s0) (b : T.toCore.R ((i : ℕ) + 1)) g))
    τ ζ η C C' Φ Φ' h.1 (fun n a f ha g => h.2 n a f ha g) hC
  exact ⟨key.1, fun n a f ha g => key.2 n a f ha g⟩
end


set_option maxHeartbeats 2000000 in
theorem GlobalTheory.ConjTwist.FlatSeries.conj_flat_series : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : Fin D.R.m → ℂ), 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → GlobalTheory.Hk3.Core R F → Finite T0 → Nonempty (FWTie T R κ v₀) → IoExt R → QGuard R → ∀ i : Fin D.R.m, OMPins T R κ v₀ O i → PhaseTie T R κ v₀ O ph i → ∀ (c : VsV D i ℂ →ₗ[ℂ] (R.cV i).W), ExtC R i (inC (O i).c') (O i).c0' c → ∀ u : (∀ ρ, lowT (R.MW i (sg0 D A)) ρ), (∀ ρ, (u ρ : (R.MW i (sg0 D A)).sm ρ) = v₀ i (sg0 D A) ρ) → ∀ τ : ℂ ≃+* ℂ, FixBase T R i τ → ∃ ζ0 : ℂ, IsRoot1 ζ0 ∧ ∀ t t' : T0, ConjTup R τ t t' → ∀ f f', IsFlatVec R i t f → IsFlatVec R i t' f' → ∃ s : (AE D)ˣ, ∀ h ∈ GfC (Vc D i), ∀ x x' : VsV D i ℂ, ConjVec i τ x x' → ConjFun (O i) (κ i) τ (ζ0 * ((R.xi t' s : Circle) : ℂ)) (fun g => ph i * ser R i t f u h (c x) g) (fun g => ph i * ser R i t' f' u h (c x') g) := by
  intro hCI D G _ _ Pl0 T0 A T _ R F κ v₀ O ph hn hCore hT0 hFW hIo hQ i hPins hPh cc hcc u hu τ hFix
  obtain ⟨ζ0, hζ0, hser⟩ := GlobalTheory.T.conjugate_tuples_twisted_thetaSeries_conjugate hCI D G Pl0 T0 A T R F κ v₀ O ph hn hCore hT0 hFW hIo hQ i hPins hPh cc hcc u hu τ hFix
  refine ⟨ζ0, hζ0, fun t t' hConj f f' hf hf' => ?_⟩
  obtain ⟨s, hs⟩ := hser t t' hConj
  obtain ⟨z, C, C', s₂, hz, rfl, rfl, hC⟩ :=
    GlobalTheory.T.heckeChoice_flatScalar_conj_twist D G Pl0 T0 A T R F κ v₀ hCore hQ i τ t t' hPins.2.lift.std hFix hConj f f' hf hf'
  refine ⟨s * s₂, fun h hh x x' hx => ?_⟩
  have hzG : z ∈ GfC (Vc D i) := hz.2.1
  have base := hs (h * z) ((GfC (Vc D i)).mul_mem hh hzG) x x' hx
  have sc := GlobalTheory.ConjTwist.FlatSeries.conjFun_scale (O i) (κ i) τ base hC
  have e1 : (fun g => ph i * ser R i t (C • R.ωP i t (z, 1) (R.vP i t)) u h (cc x) g) =
      fun g => C * (ph i * ser R i t (R.vP i t) u (h * z) (cc x) g) := funext fun g => by
    rw [GlobalTheory.T.thetaSeries_translated_datum_at_translated_class D G Pl0 T0 A T.Q.c.F R F hCore i t z C hzG u h (cc x) g]
    ring
  have e2 : (fun g => ph i * ser R i t' (C' • R.ωP i t' (z, 1) (R.vP i t')) u h (cc x') g) =
      fun g => C' * (ph i * ser R i t' (R.vP i t') u (h * z) (cc x') g) := funext fun g => by
    rw [GlobalTheory.T.thetaSeries_translated_datum_at_translated_class D G Pl0 T0 A T.Q.c.F R F hCore i t' z C' hzG u h (cc x') g]
    ring
  rw [e1, e2]
  have e3 : ζ0 * ((R.xi t' (s * s₂) : Circle) : ℂ) = ζ0 * ((R.xi t' s : Circle) : ℂ) * ((R.xi t' s₂ : Circle) : ℂ) := by
    rw [map_mul, Circle.coe_mul, mul_assoc]
  rw [e3]
  exact sc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugateThetaSeriesFlatDatumRootOfUnityStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugate_thetaSeries_flatDatum_rootOfUnity : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : Fin D.R.m → ℂ), 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → GlobalTheory.Hk3.Core R F → Finite T0 → Nonempty (FWTie T R κ v₀) → IoExt R → QGuard R → ∀ i : Fin D.R.m, OMPins T R κ v₀ O i → PhaseTie T R κ v₀ O ph i → ∀ (c : VsV D i ℂ →ₗ[ℂ] (R.cV i).W), ExtC R i (inC (O i).c') (O i).c0' c → ∀ u : (∀ ρ, lowT (R.MW i (sg0 D A)) ρ), (∀ ρ, (u ρ : (R.MW i (sg0 D A)).sm ρ) = v₀ i (sg0 D A) ρ) → ∀ τ : ℂ ≃+* ℂ, FixBase T R i τ → ∃ ζ0 : ℂ, IsRoot1 ζ0 ∧ ∀ t t' : T0, ConjTup R τ t t' → ∀ f f', IsFlatVec R i t f → IsFlatVec R i t' f' → ∃ s : (AE D)ˣ, ∀ h ∈ GfC (Vc D i), ∀ x x' : VsV D i ℂ, ConjVec i τ x x' → ConjFun (O i) (κ i) τ (ζ0 * ((R.xi t' s : Circle) : ℂ)) (fun g => ph i * ser R i t f u h (c x) g) (fun g => ph i * ser R i t' f' u h (c x') g) := by
  first | exact @GlobalTheory.ConjTwist.FlatSeries.conj_flat_series | exact GlobalTheory.ConjTwist.FlatSeries.conj_flat_series | (intros; apply GlobalTheory.ConjTwist.FlatSeries.conj_flat_series <;> assumption)
end
end

set_option autoImplicit false

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ExportSeries (Base Twist PairRep detChar twistBy series)

noncomputable section

namespace GlobalTheory.ConjGen

open GlobalTheory.ConjCombine

section CFAux

variable {X Bt : Type} {φ : Bt → X → ℂ} {τ : ℂ ≃+* ℂ}

theorem cf_one_of {ζ : ℂ} (hζ : ζ ≠ 0) {Φ Φ' : X → ℂ} (h : CF φ τ ζ Φ Φ') :
    CF φ τ 1 Φ (fun g => ζ⁻¹ * Φ' g) := by
  refine ⟨h.1, fun n a F ha g => ?_⟩
  show ζ⁻¹ * Φ' g = _
  rw [h.2 n a F ha g, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  beta_reduce
  rw [one_mul, ← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hζ, one_mul]

theorem cf_of_exp {Ψ Ψ' : X → ℂ} (h0 : CF φ τ 1 Ψ Ψ') (ζ : ℂ) {Φ Φ' : X → ℂ} {n : ℕ} {b : Fin n → ℂ} {F : Fin n → Bt}
    (hb : Exp φ Φ b F) (hb' : Exp φ Φ' (fun k => ζ * τ (b k)) F) : CF φ τ ζ Φ Φ' := by
  refine ⟨⟨n, b, F, hb⟩, fun m a G ha g => ?_⟩
  rw [hb' g]
  have hw := conj_wd h0 ha hb g
  simp only [mul_assoc, ← Finset.mul_sum]
  rw [hw]

theorem cf_comp {ζ : ℂ} (hζ : ζ ≠ 0) {Φ Φ' : X → ℂ} (h : CF φ τ ζ Φ Φ') (r : X → X) (M : Bt → Bt) {χ : ℂ}
    (hχ : τ χ = χ) (hr : ∀ F x, φ F (r x) = χ⁻¹ * φ (M F) x) : CF φ τ ζ (fun x => Φ (r x)) (fun x => Φ' (r x)) := by
  obtain ⟨n, a, F, ha⟩ := h.1
  refine cf_of_exp (cf_one_of hζ h) ζ (b := fun k => χ⁻¹ * a k) (F := fun k => M (F k)) (fun x => ?_) (fun x => ?_)
  · rw [ha (r x)]
    refine Finset.sum_congr rfl fun k _ => ?_
    beta_reduce
    rw [hr]
    ring
  · rw [h.2 n a F ha (r x)]
    refine Finset.sum_congr rfl fun k _ => ?_
    beta_reduce
    rw [hr, map_mul, map_inv₀, hχ]
    ring

theorem cf_sum {ζ : ℂ} (hζ : ζ ≠ 0) {Ψ Ψ' : X → ℂ} (h0 : CF φ τ ζ Ψ Ψ') {ι : Type} [Fintype ι] (β : ι → ℂ)
    (Φs Φs' : ι → X → ℂ) (h : ∀ p, CF φ τ ζ (Φs p) (Φs' p)) :
    CF φ τ ζ (fun g => ∑ p, β p * Φs p g) (fun g => ∑ p, τ (β p) * Φs' p g) := by
  let e := (Fintype.equivFin ι).symm
  have hc := conj_comb (cf_one_of hζ h0) (fun j => β (e j)) (fun j => Φs (e j)) (fun j g => ζ⁻¹ * Φs' (e j) g)
    (fun j => cf_one_of hζ (h (e j))) ζ
  have e1 : (fun g => ∑ j, β (e j) * Φs (e j) g) = fun g => ∑ p, β p * Φs p g :=
    funext fun g => Equiv.sum_comp e (fun p => β p * Φs p g)
  have e2 : (fun g => ζ * ∑ j, τ (β (e j)) * (ζ⁻¹ * Φs' (e j) g)) = fun g => ∑ p, τ (β p) * Φs' p g := by
    funext g
    rw [Equiv.sum_comp e (fun p => τ (β p) * (ζ⁻¹ * Φs' p g)), Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [mul_left_comm, ← mul_assoc ζ, mul_inv_cancel₀ hζ, one_mul]
  rw [e1, e2] at hc
  exact hc

end CFAux

section Rt

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0}

theorem conjFun_mul_right (O : OMDat T.toCore R i Tp tup) (κ : WeightFamilies.Wt D ((i : ℕ) + 1)) {τ : ℂ ≃+* ℂ} (hτ : FixBase T R i τ)
    (hE : O.EquivAt κ (T.cE ((i : ℕ) + 1) O.s0)) {g : G} {k : GA D (Wc D i)}
    (hk : Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) k) {ζ : ℂ} (hζ : ζ ≠ 0)
    {Φ Φ' : GA D (Wc D i) → ℂ} (h : ConjFun O κ τ ζ Φ Φ') :
    ConjFun O κ τ ζ (fun x => Φ (x * k)) (fun x => Φ' (x * k)) := by
  rw [GlobalTheory.ConjClassSum.conjFun_iff] at h ⊢
  set χ : ℂ := ∏ PP : R.Pg, ((R.chi ((i : ℕ) + 1) PP.1 (Matrix.GeneralLinearGroup.det (R.eG g PP)) : ℂˣ) : ℂ) with hχd
  have hχ0 : χ ≠ 0 := Finset.prod_ne_zero_iff.2 fun PP _ => Units.ne_zero _
  have hτχ : τ χ = χ := by
    rw [hχd, map_prod]
    exact Finset.prod_congr rfl fun PP _ => hτ.chi PP.1 PP.2 _
  refine cf_comp hζ h (fun x => x * k)
    (fun F => ⟨actLev T.toCore.Q.c O.lev2 g (F : T.toCore.R ((i : ℕ) + 1)), (hE g k hk F F.2).1⟩) hτχ fun F x => ?_
  have e := (hE g k hk F F.2).2 x
  change _ = χ⁻¹ * (_ * O.phi _ (actLev T.toCore.Q.c O.lev2 g (F : T.toCore.R ((i : ℕ) + 1))) x)
  rw [e, ← hχd]
  field_simp

end Rt

section Gen

variable {D : D7} {S T : HSp D}

theorem gen_eq_series {B : Base S T} (hB : B.Good) {ψ : Twist D Circle} (hψ : ψ.Good) (hQ : B.admitted ψ.Q) {ω ω' : PairRep S T}
    (hω : B.IsWeil 1 ω) (hω' : B.IsWeil ψ.chi ω') (h : GA D S) (P : PolF D T.rank S.rank) (g : GA D T) :
    B.gen ω ψ h P g = ((detChar S ψ.chi h : Circle) : ℂ) * series B.F ω' (B.vecFlat ψ) h P g := by
  have hf : IsThetaFunO B.F.ψ S T (B.F.fock (B.vecFlat ψ) P) := GlobalTheory.ExportSeries.Base.isThetaFunO_fock_vecAt hB hQ _ P
  have ho : IsWeilDatumO B.F.ψ S T (B.mu * 1) (B.mu * 1 * B.eta⁻¹) ω := hω
  have ho' : IsWeilDatumO B.F.ψ S T (B.mu * 1 * ψ.chi) (B.mu * 1 * B.eta⁻¹ * ψ.chi) ω' := by
    have e1 : B.mu * 1 * ψ.chi = B.mu * ψ.chi := by rw [mul_one]
    have e2 : B.mu * 1 * B.eta⁻¹ * ψ.chi = B.mu * ψ.chi * B.eta⁻¹ := by rw [mul_one, mul_right_comm]
    rw [e1, e2]
    exact hω'
  have key := GlobalTheory.SplitChange.twist_eq ho hψ.isHeckeChar hψ.real ho' (GlobalTheory.ExportSeries.muVal_detChar S hψ.real)
    (GlobalTheory.ExportSeries.muVal_detChar T hψ.real) h g hf
  have hS : ((detChar S ψ.chi h : Circle) : ℂ) ≠ 0 := Circle.coe_ne_zero _
  simp only [GlobalTheory.ExportSeries.Base.gen, LinearMap.comp_apply, GlobalTheory.ExportSeries.twistBy_apply, GlobalTheory.ExportSeries.series_apply]
  rw [key, Pi.smul_apply, smul_eq_mul]
  field_simp

theorem levJ_eq (B : Base S T) {ψ ψ' : Twist D Circle} (hQ : ψ'.Q = ψ.Q) : B.levJ ψ' = B.levJ ψ := by
  unfold GlobalTheory.ExportSeries.Base.levJ GlobalTheory.ExportSeries.Base.levS
  rw [hQ]
  rfl

theorem series_weil {B : Base S T} (hB : B.Good) {ψ : Twist D Circle} (hQ : B.admitted ψ.Q) {ω ω' : PairRep S T}
    (hω : B.IsWeil ψ.chi ω) (hω' : B.IsWeil ψ.chi ω') (h : GA D S) (P : PolF D T.rank S.rank) :
    series B.F ω (B.vecFlat ψ) h P = series B.F ω' (B.vecFlat ψ) h P := by
  funext g
  have hf : IsThetaFunO B.F.ψ S T (B.F.fock (B.vecFlat ψ) P) := GlobalTheory.ExportSeries.Base.isThetaFunO_fock_vecAt hB hQ _ P
  rw [GlobalTheory.ExportSeries.series_apply, GlobalTheory.ExportSeries.series_apply,
    GlobalTheory.WeilUniq.weilDatum_unique D _ hB.frame.vac.1 S T _ _ ω ω' hω hω' (h, g) _ hf]

end Gen

section Sum

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {i : Fin D.R.m}

theorem isThetaFunO_flat {F : Face D A} (hC : GlobalTheory.Hk3.Core R F) {B : Base (Vc D i) (Wc D i)} (hB : B.Good) (hBo : BaseOf R i B)
    {ψ : Twist D Circle} {t : T0} (hψ : ψ.Good) (hQ : B.admitted ψ.Q) (ht : IsTupOf R B ψ t) {f : WO (Vc D i) (Wc D i) → ℂ}
    (hf : IsFlatVec R i t f) : IsThetaFunO B.F.ψ (Vc D i) (Wc D i) f := by
  rw [GlobalTheory.FlatVecSum.eq_vecFlat_princ hBo ht hC.lev hB hψ hQ hf]
  exact GlobalTheory.GalLift.Vec.theta_of_thetaAt hB.frame.vac.1 hB.frame.vac.2.inf
    (GlobalTheory.ExportSeries.Base.isThetaAt_vecAt (GlobalTheory.FlatVecSum.princ_good hB) hQ _) hB.frame.vac.2.theta

theorem series_vecFlat_eq_sum {F : Face D A} (hC : GlobalTheory.Hk3.Core R F) {B : Base (Vc D i) (Wc D i)} (hB : B.Good)
    (hBo : BaseOf R i B) [Fintype B.G.P.H] (k : B.G.P.H → GA D (Wc D i))
    (hk : ∀ p, Lev.IsLevelLift (Wc D i) B.F.βT B.G.levT p.1 (k p)) {ψ : Twist D Circle} {t : T0} (hψ : ψ.Good)
    (hQ : B.admitted ψ.Q) (ht : IsTupOf R B ψ t) {f : WO (Vc D i) (Wc D i) → ℂ} (hf : IsFlatVec R i t f)
    (u : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (h : GA D (Vc D i)) (w : (R.cV i).W) (g : GA D (Wc D i)) :
    series B.F (R.ωP i t) (B.vecFlat ψ) h (R.ioP i (PiTensorProduct.tprod ℂ u) w) g =
      ∑ p, (((B.G.P.chi p)⁻¹ : ℂˣ) : ℂ) * ser R i t f u h w (g * k p) := by
  have hω : B.IsWeil ψ.chi (R.ωP i t) := hBo.isWeil hC.thP.ωP ht
  have ho : IsWeilDatumO B.F.ψ (Vc D i) (Wc D i) (B.mu * ψ.chi) (B.mu * ψ.chi * B.eta⁻¹) (R.ωP i t) := hω
  have hθ := hB.frame.vac.2.inf
  have hstd : IsStdChar D B.F.ψ (-1) := hB.frame.vac.1
  have hft := isThetaFunO_flat hC hB hBo hψ hQ ht hf
  have hv := ((GlobalTheory.FlatVecSum.vecFlat_eq_sum D G Pl0 T0 A Ks R F hC i B hB hBo).2.2 k hk).2 ψ t f hψ hQ ht hf
  set P := R.ioP i (PiTensorProduct.tprod ℂ u) w with hP
  have hmove : ∀ p, (R.ωP i t) (1, k p) (B.F.fock f P) = B.F.fock ((R.ωP i t) (1, k p) f) P := fun p => by
    have hkf : k p ∈ GfC (Wc D i) := (hk p).1
    exact (GlobalTheory.OrientedHeis.om_pureTensorO D _ _ (Vc D i) (Wc D i) _ _ (R.ωP i t) ho hθ (fun _ => 1) (fun _ => 1)
      (fun τ => (B.F.BS τ).val) (fun τ => (B.F.BS τ).val) B.F.sT B.F.sT B.F.BT B.F.BT 1 (k p)
      (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite B.F.θ τ (one_mem (GfC (Vc D i)))])
      (fun τ => by simp [GlobalTheory.FiniteFock.compAt_mt_of_finite _ τ hkf])
      (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite B.F.θ τ (one_mem (GfC (Vc D i))), Matrix.one_mul])
      (fun τ => by simp [GlobalTheory.FiniteFock.compAt_mt_of_finite _ τ hkf]) _ hft P).2
  have hsum := (GlobalTheory.SingleDatum.pureTensorO_finsetSum hstd hθ (fun _ => 1) (fun τ => (B.F.BS τ).val) B.F.sT B.F.BT
    Finset.univ (fun p => (((B.G.P.chi p)⁻¹ : ℂˣ) : ℂ)) (fun p => (R.ωP i t) (1, k p) f)
    (fun p => ho.om_pres _ f hft) P).2
  rw [GlobalTheory.ExportSeries.series_apply, hv]
  change (R.ωP i t) (h, g) (B.F.fock (∑ p, (((B.G.P.chi p)⁻¹ : ℂˣ) : ℂ) • (R.ωP i t) (1, k p) f) P) 0 = _
  rw [show B.F.fock (∑ p, (((B.G.P.chi p)⁻¹ : ℂˣ) : ℂ) • (R.ωP i t) (1, k p) f) P =
      ∑ p, (((B.G.P.chi p)⁻¹ : ℂˣ) : ℂ) • B.F.fock ((R.ωP i t) (1, k p) f) P from hsum]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← hmove p, ← hBo.series_eq_ser t f u (h) w, GlobalTheory.ExportSeries.series_apply, ← Module.End.mul_apply, ← map_mul,
    Prod.mk_mul_mk, mul_one]

end Sum


set_option maxHeartbeats 4000000 in
theorem conj_gen : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type)
    (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
    (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)
    (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : Fin D.R.m → ℂ), 8 * D.R.f * D.R.r + 4 ≤ D.R.nV →
    GlobalTheory.Hk3.Core R F → Finite T0 → Nonempty (FWTie T R κ v₀) → IoExt R → QGuard R → ∀ i : Fin D.R.m, OMPins T R κ v₀ O i →
    PhaseTie T R κ v₀ O ph i → ∀ (c : VsV D i ℂ →ₗ[ℂ] (R.cV i).W), ExtC R i (inC (O i).c') (O i).c0' c →
    ∀ u : (∀ ρ, lowT (R.MW i (sg0 D A)) ρ), (∀ ρ, (u ρ : (R.MW i (sg0 D A)).sm ρ) = v₀ i (sg0 D A) ρ) →
    ∀ (B : Base (Vc D i) (Wc D i)), B.Good → BaseOf R i B → ∀ ω : PairRep (Vc D i) (Wc D i), B.IsWeil 1 ω →
    ∀ τ : ℂ ≃+* ℂ, FixBase T R i τ → FixDat B τ → ∃ ζ0 : ℂ, IsRoot1 ζ0 ∧
    ∀ (ψ ψ' : Twist D Circle) (t t' : T0), ψ.Good → ψ'.Good → B.admitted ψ.Q → B.admitted ψ'.Q → IsTupOf R B ψ t → IsTupOf R B ψ' t' →
    ConjChar τ ψ ψ' → ∃ s : (AE D)ˣ, (∀ h ∈ GfC (Vc D i), ∀ x x' : VsV D i ℂ, ConjVec i τ x x' →
      ConjFun (O i) (κ i) τ (ζ0 * ((R.xi t' s : Circle) : ℂ))
        (ph i • B.gen ω ψ h (R.ioP i (PiTensorProduct.tprod ℂ u) (c x)))
        (ph i • B.gen ω ψ' h (R.ioP i (PiTensorProduct.tprod ℂ u) (c x')))) ∧
    ∀ ω₁ ω₁' : PairRep (Vc D i) (Wc D i), B.IsWeil ψ.chi ω₁ → B.IsWeil ψ'.chi ω₁' →
    ∀ {I : Type} [Fintype I] (hs : I → GA D (Vc D i)), (∀ j, hs j ∈ GfC (Vc D i)) →
    ∀ Fm Fm' : Bridge.Gf (Vc D i) → PolF D (Wc D i).rank (Vc D i).rank,
    (∀ j, ∃ x x' : VsV D i ℂ, ConjVec i τ x x' ∧
      Fm (GlobalTheory.ExportSeries.finPt (Vc D i) (hs j)) = R.ioP i (PiTensorProduct.tprod ℂ u) (c x) ∧
      Fm' (GlobalTheory.ExportSeries.finPt (Vc D i) (hs j)) = R.ioP i (PiTensorProduct.tprod ℂ u) (c x')) →
    ConjFun (O i) (κ i) τ (ζ0 * ((R.xi t' s : Circle) : ℂ))
      (ph i • B.classSum ω₁ ψ hs Fm) (ph i • B.classSum ω₁' ψ' hs Fm') := by
  intro hCI D G _ _ Pl0 T0 A T _ R F κ v₀ O ph hnV hC hT0 hFW hio hQG i hOP hPT c hc u hu B hB hBo ω hω τ hτ hfix
  obtain ⟨fw⟩ := hFW
  have hTie : TieIn T R κ v₀ := ⟨fw.laws, fw.alg_eq, fw.kap, fw.hv₀, fw.chiR, fw.x0⟩
  have hE : (O i).EquivAt (κ i) (T.cE ((i : ℕ) + 1) (O i).s0) :=
    (hPT (GlobalTheory.T.thetaOneMap_baseTuple_of_characterisation_extremal hCI D G Pl0 T0 A T R F κ v₀ hC hTie hio O i hOP)).1
  obtain ⟨ζ0, hζ0, hgb⟩ := GlobalTheory.T.conjugate_thetaSeries_flatDatum_rootOfUnity hCI D G Pl0 T0 A T R F κ v₀ O ph hnV hC hT0 ⟨fw⟩ hio hQG i hOP hPT c hc u hu τ hτ
  refine ⟨ζ0, hζ0, fun ψ ψ' t t' hψ hψ' hQ hQ' ht ht' hcc => ?_⟩
  obtain ⟨f, hf⟩ := (GlobalTheory.FlatVecExist.flatVec_existsUnique D G Pl0 T0 A _ R F hC hQG i t).1
  obtain ⟨f', hf'⟩ := (GlobalTheory.FlatVecExist.flatVec_existsUnique D G Pl0 T0 A _ R F hC hQG i t').1
  obtain ⟨s, hs⟩ := hgb t t' (conjTup_of R ht ht' hcc hfix) f f' hf hf'
  set ζ := ζ0 * ((R.xi t' s : Circle) : ℂ) with hζd
  have hζ : ζ ≠ 0 := by
    obtain ⟨n, hn, hpow⟩ := hζ0
    refine mul_ne_zero (fun h0 => ?_) (Circle.coe_ne_zero _)
    rw [h0, zero_pow hn.ne'] at hpow
    exact zero_ne_one hpow
  obtain ⟨hfin, ⟨k, hk⟩, hsum⟩ := GlobalTheory.FlatVecSum.vecFlat_eq_sum D G Pl0 T0 A _ R F hC i B hB hBo
  haveI : Fintype B.G.P.H := Fintype.ofFinite _
  obtain ⟨hk0, -⟩ := hsum k fun p => (hk p).1
  choose g0 hg0 using hk0
  have hlift : ∀ p, Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG (R.eG.symm (g0 p))) (k p) := fun p => by
    exact (congrArg (fun z => Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) z (k p))
      (R.eG.apply_symm_apply (g0 p))).mpr (hg0 p)
  have hrt : ∀ h ∈ GfC (Vc D i), ∀ x x' : VsV D i ℂ, ConjVec i τ x x' → ∀ p, ConjFun (O i) (κ i) τ ζ
      (fun g => ph i * ser R i t f u h (c x) (g * k p)) (fun g => ph i * ser R i t' f' u h (c x') (g * k p)) :=
    fun h hh x x' hx p => conjFun_mul_right (O i) (κ i) hτ hE (hlift p) hζ (hs h hh x x' hx)
  have hcp : ∀ p, τ ((((B.G.P.chi p)⁻¹ : ℂˣ) : ℂ)) = (((B.G.P.chi p)⁻¹ : ℂˣ) : ℂ) := fun p => by
    rw [Units.val_inv_eq_inv_val, map_inv₀, hfix.2.1 p]
  obtain ⟨h₀, x₀, hh₀, hx₀⟩ : ∃ (h₀ : GA D (Vc D i)) (x₀ : VsV D i ℂ), h₀ ∈ GfC (Vc D i) ∧ ConjVec i τ x₀ x₀ := by
    refine ⟨1, 0, one_mem _, ?_⟩
    unfold ConjVec
    simp
  have hCF0 := (GlobalTheory.ConjClassSum.conjFun_iff _ _ _ _ _ _).1 (hs h₀ hh₀ x₀ x₀ hx₀)
  refine ⟨s, fun h hh x x' hx => ?_, fun ω₁ ω₁' hω₁ hω₁' I _ hs' hfs Fm Fm' hFm => ?_⟩
  · set dS : ℂ := ((detChar (Vc D i) ψ.chi h : Circle) : ℂ) with hdS
    set dS' : ℂ := ((detChar (Vc D i) ψ'.chi h : Circle) : ℂ) with hdS'
    have e1 : (ph i • B.gen ω ψ h (R.ioP i (PiTensorProduct.tprod ℂ u) (c x))) =
        fun g => ∑ p, (dS * (((B.G.P.chi p)⁻¹ : ℂˣ) : ℂ)) * (ph i * ser R i t f u h (c x) (g * k p)) := by
      funext g
      rw [Pi.smul_apply, smul_eq_mul, gen_eq_series hB hψ hQ hω (hBo.isWeil hC.thP.ωP ht),
        series_vecFlat_eq_sum hC hB hBo k (fun p => (hk p).1) hψ hQ ht hf, Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun p _ => by ring
    have e2 : (ph i • B.gen ω ψ' h (R.ioP i (PiTensorProduct.tprod ℂ u) (c x'))) =
        fun g => ∑ p, τ (dS * (((B.G.P.chi p)⁻¹ : ℂˣ) : ℂ)) * (ph i * ser R i t' f' u h (c x') (g * k p)) := by
      have hd : τ dS = dS' := (hcc.2 _).symm
      funext g
      rw [Pi.smul_apply, smul_eq_mul, gen_eq_series hB hψ' hQ' hω (hBo.isWeil hC.thP.ωP ht'),
        series_vecFlat_eq_sum hC hB hBo k (fun p => (hk p).1) hψ' hQ' ht' hf', Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [map_mul, hd, hcp]
      ring
    rw [e1, e2, GlobalTheory.ConjClassSum.conjFun_iff]
    exact cf_sum hζ hCF0 _ _ _ fun p => (GlobalTheory.ConjClassSum.conjFun_iff _ _ _ _ _ _).1 (hrt h hh x x' hx p)
  · choose x x' hx hFx hFx' using hFm
    have hJ : B.levJ ψ' = B.levJ ψ := levJ_eq B hcc.1
    set n : I → ℂ := fun j => ((Nat.card (Bridge.stab (Bridge.ratF (Vc D i)) (B.levJ ψ)
      (GlobalTheory.ExportSeries.finPt (Vc D i) (hs' j))) : ℕ) : ℂ) with hn
    have e1 : (ph i • B.classSum ω₁ ψ hs' Fm) = fun g => ∑ q : I × B.G.P.H,
        ((n q.1)⁻¹ * (((B.G.P.chi q.2)⁻¹ : ℂˣ) : ℂ)) * (ph i * ser R i t f u (hs' q.1) (c (x q.1)) (g * k q.2)) := by
      funext g
      rw [Pi.smul_apply, smul_eq_mul, GlobalTheory.ExportSeries.Base.classSum_apply, Fintype.sum_prod_type, Finset.sum_apply,
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Pi.smul_apply, smul_eq_mul, hFx j, series_weil hB hQ hω₁ (hBo.isWeil hC.thP.ωP ht),
        series_vecFlat_eq_sum hC hB hBo k (fun p => (hk p).1) hψ hQ ht hf, Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun p _ => by ring
    have e2 : (ph i • B.classSum ω₁' ψ' hs' Fm') = fun g => ∑ q : I × B.G.P.H,
        τ ((n q.1)⁻¹ * (((B.G.P.chi q.2)⁻¹ : ℂˣ) : ℂ)) * (ph i * ser R i t' f' u (hs' q.1) (c (x' q.1)) (g * k q.2)) := by
      funext g
      rw [Pi.smul_apply, smul_eq_mul, GlobalTheory.ExportSeries.Base.classSum_apply, Fintype.sum_prod_type, Finset.sum_apply,
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Pi.smul_apply, smul_eq_mul, hFx' j, series_weil hB hQ' hω₁' (hBo.isWeil hC.thP.ωP ht'),
        series_vecFlat_eq_sum hC hB hBo k (fun p => (hk p).1) hψ' hQ' ht' hf', Finset.mul_sum, Finset.mul_sum, hJ]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [map_mul, map_inv₀, map_natCast, hcp]
      ring
    rw [e1, e2, GlobalTheory.ConjClassSum.conjFun_iff]
    exact cf_sum hζ hCF0 _ _ _ fun q => (GlobalTheory.ConjClassSum.conjFun_iff _ _ _ _ _ _).1
      (hrt (hs' q.1) (hfs q.1) (x q.1) (x' q.1) (hx q.1) q.2)

end GlobalTheory.ConjGen
