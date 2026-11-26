module

public import Development.WeilBound.RepresentationTheoryGL.GaloisPermutationReps.SubquotientEquivalence.IsTypeMap
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalLabelUnique

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.GaloisPermutationReps.SubquotientEquivalence.FiniteCuspidalOfIsCuspidal
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.DzCount

private theorem exists_block_lt_unipotent_lemma {K : Type} [Field K] {n s : ℕ} {d : Fin s → ℕ}
    (e : (Σ a, Fin (d a)) ≃ Fin n) {g : GL (Fin n) K} (hg : g ∈ GlobalTheory.SmGL.unipRad K e) (i j : Fin n)
    (hij : GlobalTheory.SmGL.blk e i = GlobalTheory.SmGL.blk e j) :
    (g : Matrix (Fin n) (Fin n) K) i j = if i = j then 1 else 0 := by
  obtain ⟨⟨y, hy⟩, hk, rfl⟩ := Subgroup.mem_map.1 hg
  rw [MonoidHom.mem_ker] at hk
  obtain ⟨a, i', hi⟩ : ∃ a i', e.symm i = ⟨a, i'⟩ := ⟨_, _, rfl⟩
  obtain ⟨b, j', hj⟩ : ∃ b j', e.symm j = ⟨b, j'⟩ := ⟨_, _, rfl⟩
  have hab : a = b := by
    simp only [GlobalTheory.SmGL.blk, hi, hj] at hij
    exact hij
  subst hab
  have hi2 : i = e ⟨a, i'⟩ := by
    rw [← hi, Equiv.apply_symm_apply]
  have hj2 : j = e ⟨a, j'⟩ := by
    rw [← hj, Equiv.apply_symm_apply]
  have h3 := congrArg (fun u => ((u a : GL (Fin (d a)) K) : Matrix (Fin (d a)) (Fin (d a)) K) i' j') hk
  simp [GlobalTheory.SmGL.leviProj, GlobalTheory.SmGL.diagBlock, Matrix.one_apply] at h3
  subst hi2 hj2
  simp [h3]

theorem exists_block_lt_unipotent {K : Type} [Field K] {n s : ℕ} {d : Fin s → ℕ}
    (e : (Σ a, Fin (d a)) ≃ Fin n) (h : GlobalTheory.SmGL.unipRad K e ≠ ⊥) :
    ∃ i j : Fin n, GlobalTheory.SmGL.blk e i < GlobalTheory.SmGL.blk e j := by
  by_contra hcon
  push_neg at hcon
  apply h
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_bot]
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [exists_block_lt_unipotent_lemma e hg i j (le_antisymm (hcon j i) (hcon i j))]
  simp [Matrix.one_apply]

private theorem finite_cuspidal_of_isCuspidal_lemma {K : Type} [Field K] {n s : ℕ} {d : Fin s → ℕ}
    (e : (Σ a, Fin (d a)) ≃ Fin n) (g : GL (Fin n) K)
    (h1 : (g : Matrix (Fin n) (Fin n) K).BlockTriangular (GlobalTheory.SmGL.blk e))
    (h2 : ∀ i j, GlobalTheory.SmGL.blk e i = GlobalTheory.SmGL.blk e j → (g : Matrix (Fin n) (Fin n) K) i j = if i = j then 1 else 0) :
    g ∈ GlobalTheory.SmGL.unipRad K e := by
  refine Subgroup.mem_map.2 ⟨⟨g, h1⟩, ?_, rfl⟩
  rw [MonoidHom.mem_ker]
  funext a
  refine Units.ext ?_
  ext i' j'
  have h3 := h2 (e ⟨a, i'⟩) (e ⟨a, j'⟩) (by simp [GlobalTheory.SmGL.blk])
  simp [GlobalTheory.SmGL.leviProj, GlobalTheory.SmGL.diagBlock, Matrix.one_apply, h3]

private theorem finite_cuspidal_of_isCuspidal_lemma_2 {K : Type} [Field K] [Fintype K] [DecidableEq K] {n s : ℕ}
    {d : Fin s → ℕ} (e : (Σ a, Fin (d a)) ≃ Fin n) (t : Fin s) (u : GL (Fin n) K)
    (hu : u ∈ Formalism.IrreducibleCountingLemmas.TYPES.unip K (fun i => if GlobalTheory.SmGL.blk e i < t then (0 : Fin 2) else 1)) :
    u ∈ GlobalTheory.SmGL.unipRad K e := by
  obtain ⟨⟨hut, -⟩, hud⟩ := hu
  refine finite_cuspidal_of_isCuspidal_lemma e u ?_ ?_
  · intro i j hji
    by_cases hb : (if GlobalTheory.SmGL.blk e j < t then (0 : Fin 2) else 1) <
        (if GlobalTheory.SmGL.blk e i < t then (0 : Fin 2) else 1)
    · exact hut i j hb
    · have hne : i ≠ j := by
        intro h
        subst h
        exact lt_irrefl _ hji
      rw [hud i j ?_, if_neg hne]
      by_cases h1 : GlobalTheory.SmGL.blk e i < t
      · have h2 : GlobalTheory.SmGL.blk e j < t := lt_trans hji h1
        simp [h1, h2]
      · by_cases h2 : GlobalTheory.SmGL.blk e j < t
        · simp [h1, h2] at hb
        · simp [h1, h2]
  · intro i j hij
    rw [hud i j (by simp [hij])]

theorem finite_cuspidal_of_isCuspidal {K : Type} [Field K] [Fintype K] [DecidableEq K] {n : ℕ}
    (τ : FDRep ℂ (GL (Fin n) K)) (h : Formalism.IrreducibleCountingLemmas.TYPES.IsCuspidal K τ) : FinCusp τ.ρ := by
  unfold FinCusp
  intro s d e hne v hv
  obtain ⟨i0, j0, hlt⟩ := exists_block_lt_unipotent e hne
  refine h 2 (fun i => if GlobalTheory.SmGL.blk e i < GlobalTheory.SmGL.blk e j0 then 0 else 1) ?_ le_rfl v ?_
  · intro k
    fin_cases k
    · exact ⟨i0, by simp [hlt]⟩
    · exact ⟨j0, by simp⟩
  · intro u hu
    exact hv u (finite_cuspidal_of_isCuspidal_lemma_2 e _ u hu)

theorem hasCuspLabel_of_equiv {K : Type} [Field K] [Fintype K] [DecidableEq K]
    (C : Formalism.IrreducibleCountingLemmas.TYPES.LabelConv K) {n : ℕ} {τ τ' : FDRep ℂ (GL (Fin n) K)} (e : τ ≃ₗ[ℂ] τ')
    (he : ∀ g v, e (τ.ρ g v) = τ'.ρ g (e v)) {P : K[X]} (h : Formalism.IrreducibleCountingLemmas.TYPES.HasCuspLabel C τ P) :
    Formalism.IrreducibleCountingLemmas.TYPES.HasCuspLabel C τ' P := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨h1, h2, h3, h4, fun x hx γ hγ z hz m hm => ?_⟩
  rw [← h5 x hx γ hγ z hz m hm]
  have hc : τ'.ρ γ = (e.toLinearMap ∘ₗ τ.ρ γ) ∘ₗ e.symm.toLinearMap := by
    ext v
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, he, LinearEquiv.apply_symm_apply]
  rw [hc, ← LinearEquiv.conj_apply, LinearMap.trace_conj']

theorem st7 : St7 := by
  intro K _ _ n hn
  classical
  letI : Fintype K := Fintype.ofFinite K
  obtain ⟨C⟩ := GlobalTheory.CompanionTheory.Hypotheses₂.CuspExists.nonempty_labelConv K
  obtain ⟨P0, a0, b0, c0, d0⟩ := GlobalTheory.CompanionTheory.Hypotheses₂.CuspExists.exists_monic_irreducible K n hn
  obtain ⟨τ0, -⟩ := GlobalTheory.T.exists_cuspidal_with_label K C n hn P0 a0 b0 c0 d0
  have hex : ∀ P : K[X], ∃ τ : FDRep ℂ (GL (Fin n) K), P ∈ Lab K n →
      CategoryTheory.Simple τ ∧ Formalism.IrreducibleCountingLemmas.TYPES.IsCuspidal K τ ∧ Formalism.IrreducibleCountingLemmas.TYPES.HasCuspLabel C τ P := by
    intro P
    by_cases hP : P ∈ Lab K n
    · obtain ⟨p1, p2, p3, p4⟩ := hP
      obtain ⟨τ, hs, hc, hl⟩ := GlobalTheory.T.exists_cuspidal_with_label K C n hn P p1 p2 p3 p4
      exact ⟨τ, fun _ => ⟨hs, hc, hl⟩⟩
    · exact ⟨τ0, fun h' => absurd h' hP⟩
  choose τ hτ using hex
  refine ⟨τ, fun P hP => ⟨GlobalTheory.SerOSys.ZSum.isIrreducible_of_simple _ (hτ P hP).1,
    finite_cuspidal_of_isCuspidal _ (hτ P hP).2.1⟩, ?_⟩
  rintro P hP P' hP' ⟨e, he⟩
  exact GlobalTheory.T.cuspidal_label_unique K C (Fin n) (τ P') P P' (hasCuspLabel_of_equiv C e he (hτ P hP).2.2)
    (hτ P' hP').2.2

end PositivityTheory.Rg.DzCount

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.GaloisPermutationReps.SubquotientEquivalence.IsUnitRho
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.DzCount

namespace DepthZeroEigenvalues

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem exists_good {y : WD h} (hi : IsIrrWD y) (ht : IsTameWD y) :
    ∃ (m : ℕ) (a : WDRep h (Fin m → ℂ)), WD.mk a = y ∧ a.ρ.IsIrreducible ∧
      ∀ σ : Weil h, Formalism.MainNotions.BlochKatoReduction.IsWild A (σ : G E Ω) → a.ρ σ = 1 := by
  obtain ⟨m, a, rfl, ha⟩ := hi
  obtain ⟨m', b, hb, hbt⟩ := ht
  have hba : b.Iso a := WD.mk_eq_mk.mp hb
  exact ⟨m, a, rfl, ha, fun σ hσ => hba.ρ_eq_one (hbt σ hσ)⟩

theorem isUnit_rho {m : ℕ} (a : WDRep h (Fin m → ℂ)) (σ : Weil h) : IsUnit (a.ρ σ) :=
  (Group.isUnit σ).map a.ρ

theorem eig_prod {m : ℕ} (a : WDRep h (Fin m → ℂ)) (σ : Weil h) :
    ((WD.mk a).eig σ).prod = LinearMap.det (a.ρ σ) := by
  rw [WD.eig_mk, Module.End.det_eq_prod_roots_charpoly_of_splits (IsAlgClosed.splits _)]

theorem card_res (w : HeightOneSpectrum (𝓞 E)) : Nat.card 𝓀[w.adicCompletion E] = normV w :=
  resCard_eq_normV w

end DepthZeroEigenvalues

open DepthZeroEigenvalues in
theorem st3 : St1a → St1b → St2 → St3a → St3 := by
  intro h1a h1b h2 h3a E Ω _ _ _ _ _ A w h φ hφ n c hn
  obtain ⟨γ, hγ1, hγ2⟩ := h2 E Ω A w h φ hφ
  have hq : Nat.card 𝓀[w.adicCompletion E] = normV w := card_res w
  have : Finite 𝓀[w.adicCompletion E] := inferInstance
  obtain ⟨lab, hlab1, hlab2⟩ := h3a 𝓀[w.adicCompletion E] n hn
  set q := Nat.card 𝓀[w.adicCompletion E] with hqdef

  let Pz : WD h → ℂ → Prop := fun y z => ∃ (m : ℕ) (a : WDRep h (Fin m → ℂ)), WD.mk a = y ∧
    a.ρ.IsIrreducible ∧ (∀ σ : Weil h, Formalism.MainNotions.BlochKatoReduction.IsWild A (σ : G E Ω) → a.ρ σ = 1) ∧
    Module.End.HasEigenvalue (a.ρ γ) z ∧ ExactPer q n z
  have hex : ∀ y ∈ TameSet φ n c, ∃ z, Pz y z := by
    intro y hy
    obtain ⟨m, a, rfl, hai, hat⟩ := exists_good hy.1 hy.2.1
    have hm : Module.finrank ℂ (Fin m → ℂ) = n := by
      have := hy.2.2.1
      rwa [WD.lpDim_mk] at this
    obtain ⟨hc, hirr⟩ := hγ1 m a hat
    obtain ⟨z, hz1, hz2⟩ := h1a (Fin m → ℂ) (normV w) (a.ρ γ) (a.ρ φ) (isUnit_rho a γ)
      (isUnit_rho a φ) hc (hirr hai)
    refine ⟨z, m, a, rfl, hai, hat, hz1, ?_⟩
    rw [hm] at hz2
    rw [hq]; exact hz2
  let zf : WD h → ℂ := fun y => Classical.epsilon (Pz y)
  have hzf : ∀ y ∈ TameSet φ n c, Pz y (zf y) := fun y hy => Classical.epsilon_spec (hex y hy)
  refine ⟨fun y => lab (zf y), ?_, ?_⟩
  · intro y hy
    obtain ⟨_, _, _, _, _, _, hz⟩ := hzf y hy
    exact hlab1 _ hz
  · intro y hy y' hy' heq
    obtain ⟨m, a, rfl, hai, hat, hz1, hz2⟩ := hzf y hy
    obtain ⟨m', a', rfl, hai', hat', hz1', hz2'⟩ := hzf y' hy'
    obtain ⟨i, hi⟩ := hlab2 _ _ hz2 hz2' heq
    have hm : Module.finrank ℂ (Fin m → ℂ) = n := by
      have := hy.2.2.1
      rwa [WD.lpDim_mk] at this
    have hm' : Module.finrank ℂ (Fin m' → ℂ) = n := by
      have := hy'.2.2.1
      rwa [WD.lpDim_mk] at this
    have hdet : LinearMap.det (a.ρ φ) = LinearMap.det (a'.ρ φ) := by
      rw [← eig_prod, ← eig_prod, hy.2.2.2, hy'.2.2.2]
    obtain ⟨hc, -⟩ := hγ1 m a hat
    obtain ⟨hc', -⟩ := hγ1 m' a' hat'
    rw [← hq] at hc hc'
    obtain ⟨e, he1, he2⟩ := h1b (Fin m → ℂ) (Fin m' → ℂ) q n i (a.ρ γ) (a.ρ φ) (a'.ρ γ) (a'.ρ φ)
      (zf (WD.mk a)) hn hm hm' (isUnit_rho a φ) (isUnit_rho a' φ) hc hc' hz2 hz1 (hi ▸ hz1') hdet
    exact WD.mk_eq_mk.mpr (hγ2 m m' a a' hat hat' hai hai' e he1 he2)

end PositivityTheory.Rg.DzCount
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.GaloisPermutationReps.SubquotientEquivalence.EquivariantPartsOfFiniteType
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.DzCount

lemma pow_pow_pow_add (z : ℂ) (q a b : ℕ) : (z ^ q ^ a) ^ q ^ b = z ^ q ^ (a + b) := by
  rw [← pow_mul, ← pow_add]

lemma eigenvector_maps_power {V : Type} [AddCommGroup V] [Module ℂ V] (q : ℕ) (M G : Module.End ℂ V)
    (hMG : M * G = G * M ^ q) (z : ℂ) (v : V) (hv : M v = z • v) : M (G v) = z ^ q • G v := by
  have hpow : ∀ k : ℕ, (M ^ k) v = z ^ k • v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', Module.End.mul_apply, ih, map_smul, hv, smul_smul, pow_succ]
  have h := congrArg (fun T : Module.End ℂ V => T v) hMG
  simp only [Module.End.mul_apply] at h
  rw [h, hpow, map_smul]

lemma eigenvector_iterate_power {V : Type} [AddCommGroup V] [Module ℂ V] (q : ℕ) (M G : Module.End ℂ V)
    (hMG : M * G = G * M ^ q) (z : ℂ) (v : V) (hv : M v = z • v) :
    ∀ i : ℕ, M ((G ^ i) v) = z ^ q ^ i • (G ^ i) v := by
  intro i
  induction i with
  | zero => simpa using hv
  | succ i ih =>
    rw [pow_succ', Module.End.mul_apply, eigenvector_maps_power q M G hMG _ _ ih, ← pow_mul, ← pow_succ]

theorem st1a : St1a := by
  classical
  intro V _ _ _ q M G hM hG hMG hirr
  obtain ⟨hnt, hU⟩ := hirr
  have hGinj : ∀ i : ℕ, Function.Injective (G ^ i) := fun i =>
    ((Module.End.isUnit_iff _).mp (hG.pow i)).1
  have hMinj : Function.Injective M := ((Module.End.isUnit_iff _).mp hM).1
  have hfin : Set.Finite {μ | M.HasEigenvalue μ} := M.finite_hasEigenvalue
  have hstep : ∀ μ, M.HasEigenvalue μ → M.HasEigenvalue (μ ^ q) := by
    intro μ hμ
    obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
    have hv' : M v = μ • v := Module.End.mem_eigenspace_iff.mp hv.1
    refine Module.End.hasEigenvalue_of_hasEigenvector (x := G v) ⟨?_, ?_⟩
    · exact Module.End.mem_eigenspace_iff.mpr (eigenvector_maps_power q M G hMG μ v hv')
    · intro h0
      apply hv.2
      have h1 := hGinj 1
      rw [pow_one] at h1
      exact h1 (by rw [h0, map_zero])
  obtain ⟨z0, hz0⟩ := M.exists_eigenvalue
  have hall : ∀ i : ℕ, M.HasEigenvalue (z0 ^ q ^ i) := by
    intro i
    induction i with
    | zero => simpa using hz0
    | succ i ih =>
      have h := hstep _ ih
      rwa [← pow_mul, ← pow_succ] at h
  obtain ⟨a, b, hab, heq⟩ := Set.Finite.exists_lt_map_eq_of_forall_mem
    (f := fun i : ℕ => z0 ^ q ^ i) (t := {μ | M.HasEigenvalue μ}) (fun i => hall i) hfin
  have hzE : M.HasEigenvalue (z0 ^ q ^ a) := hall a
  have hper : (z0 ^ q ^ a) ^ q ^ (b - a) = z0 ^ q ^ a := by
    rw [pow_pow_pow_add, show a + (b - a) = b by omega, ← heq]
  generalize z0 ^ q ^ a = z at hzE hper
  have hP : ∃ e : ℕ, 0 < e ∧ z ^ q ^ e = z := ⟨b - a, by omega, hper⟩
  obtain ⟨d, ⟨hd0, hzd⟩, hdmin⟩ : ∃ d : ℕ, (0 < d ∧ z ^ q ^ d = z) ∧
      ∀ e < d, ¬ (0 < e ∧ z ^ q ^ e = z) :=
    ⟨Nat.find hP, Nat.find_spec hP, fun e he => Nat.find_min hP he⟩

  have hmaps : ∀ x ∈ M.eigenspace z, (G ^ d) x ∈ M.eigenspace z := by
    intro x hx
    rw [Module.End.mem_eigenspace_iff] at hx ⊢
    rw [eigenvector_iterate_power q M G hMG z x hx d, hzd]
  have hne : M.eigenspace z ≠ ⊥ := hzE
  have : Nontrivial (M.eigenspace z) := Submodule.nontrivial_iff_ne_bot.mpr hne
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue (LinearMap.restrict (G ^ d) hmaps)
  obtain ⟨w, hw⟩ := hμ.exists_hasEigenvector
  have hw1 : LinearMap.restrict (G ^ d) hmaps w = μ • w := Module.End.mem_eigenspace_iff.mp hw.1
  set v : V := (w : V) with hv_def
  have hGd : (G ^ d) v = μ • v := by
    have h := congrArg Subtype.val hw1
    simpa [LinearMap.restrict_apply] using h
  have hvE : M v = z • v := Module.End.mem_eigenspace_iff.mp w.2
  have hv0 : v ≠ 0 := by
    intro h
    apply hw.2
    exact Subtype.ext h

  let bb : Fin d → V := fun i => (G ^ (i : ℕ)) v
  have hb_eig : ∀ i : Fin d, M (bb i) = z ^ q ^ (i : ℕ) • bb i := fun i =>
    eigenvector_iterate_power q M G hMG z v hvE i
  have hb_ne : ∀ i : Fin d, bb i ≠ 0 := by
    intro i h
    apply hv0
    exact hGinj i (by rw [map_zero]; exact h)
  have key : ∀ i j : ℕ, i < j → j < d → z ^ q ^ i = z ^ q ^ j → False := by
    intro i j hij hjd hij'
    have h1 : z ^ q ^ (j - i) = z := by
      calc z ^ q ^ (j - i) = (z ^ q ^ d) ^ q ^ (j - i) := by rw [hzd]
        _ = (z ^ q ^ j) ^ q ^ (d - i) := by
          rw [pow_pow_pow_add, pow_pow_pow_add, show j + (d - i) = d + (j - i) by omega]
        _ = (z ^ q ^ i) ^ q ^ (d - i) := by rw [hij']
        _ = z ^ q ^ d := by rw [pow_pow_pow_add, show i + (d - i) = d by omega]
        _ = z := hzd
    exact hdmin (j - i) (by omega) ⟨by omega, h1⟩
  have hinj : Function.Injective (fun i : Fin d => z ^ q ^ (i : ℕ)) := by
    intro i j hij
    simp only at hij
    rcases lt_trichotomy (i : ℕ) (j : ℕ) with h | h | h
    · exact (key i j h j.2 hij).elim
    · exact Fin.ext h
    · exact (key j i h i.2 hij.symm).elim
  have hli : LinearIndependent ℂ bb :=
    Module.End.eigenvectors_linearIndependent' M (fun i : Fin d => z ^ q ^ (i : ℕ)) hinj bb
      (fun i => ⟨Module.End.mem_eigenspace_iff.mpr (hb_eig i), hb_ne i⟩)
  set W : Submodule ℂ V := Submodule.span ℂ (Set.range bb) with hW_def
  have hvW : v ∈ W := Submodule.subset_span ⟨⟨0, hd0⟩, by simp [bb]⟩
  have hMW : ∀ x ∈ W, M x ∈ W := by
    have hle : W ≤ W.comap M := by
      rw [hW_def, Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap, hb_eig i]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    exact fun x hx => hle hx
  have hGW : ∀ x ∈ W, G x ∈ W := by
    have hle : W ≤ W.comap G := by
      rw [hW_def, Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap]
      show G ((G ^ (i : ℕ)) v) ∈ W
      rw [← Module.End.mul_apply, ← pow_succ']
      by_cases h : (i : ℕ) + 1 < d
      · exact Submodule.subset_span ⟨⟨(i : ℕ) + 1, h⟩, rfl⟩
      · rw [show (i : ℕ) + 1 = d by omega, hGd]
        exact Submodule.smul_mem _ _ hvW
    exact fun x hx => hle hx
  have hWtop : W = ⊤ := by
    rcases hU W hMW hGW with h | h
    · exfalso
      apply hv0
      have := hvW
      rw [h] at this
      exact (Submodule.mem_bot ℂ).mp this
    · exact h
  have hfr : Module.finrank ℂ V = d := by
    have h := finrank_span_eq_card hli
    rw [← hW_def, hWtop, finrank_top, Fintype.card_fin] at h
    exact h
  refine ⟨z, hzE, ?_⟩
  rw [hfr]
  refine ⟨?_, hzd, fun e he0 hed h => hdmin e hed ⟨he0, h⟩⟩
  intro hz
  apply hv0
  apply hMinj
  rw [hvE, hz, zero_smul, map_zero]

end PositivityTheory.Rg.DzCount

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.GaloisPermutationReps.SubquotientEquivalence.PairingFactorsThroughPeriods
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

namespace PositivityTheory.Rg.DzCount

namespace PairingFactorsThroughPeriods

theorem exactPer_per {q n : ℕ} {z : ℂ} (h : ExactPer q n z) : z ^ q ^ n = z := by
  unfold ExactPer at h
  exact h.2.1

theorem per_mul {q n : ℕ} {z : ℂ} (h : z ^ q ^ n = z) (k : ℕ) : z ^ q ^ (n * k) = z := by
  induction k with
  | zero => simp
  | succ k ih => rw [Nat.mul_succ, pow_add, pow_mul, ih, h]

theorem per_inj {q n : ℕ} {z : ℂ} (hz : ExactPer q n z) {a b : ℕ} (ha : a < n) (hb : b < n)
    (h : z ^ q ^ a = z ^ q ^ b) : a = b := by
  have key : ∀ a b : ℕ, a < b → b < n → z ^ q ^ a = z ^ q ^ b → False := by
    intro a b hab hbn h
    apply hz.2.2 (b - a) (by omega) (by omega)
    have h1 : (z ^ q ^ a) ^ q ^ (n - a) = (z ^ q ^ b) ^ q ^ (n - a) := by rw [h]
    rw [← pow_mul, ← pow_mul, ← pow_add, ← pow_add, Nat.add_sub_cancel' (by omega : a ≤ n),
      hz.2.1] at h1
    have h2 : b + (n - a) = n + (b - a) := by omega
    rw [h2, pow_add, pow_mul, hz.2.1] at h1
    exact h1.symm
  rcases lt_trichotomy a b with hab | hab | hab
  · exact (key a b hab hb h).elim
  · exact hab
  · exact (key b a hab ha h.symm).elim

theorem pow_apply_eig {V : Type} [AddCommGroup V] [Module ℂ V] (M : Module.End ℂ V) {v : V} {c : ℂ}
    (hv : M v = c • v) (k : ℕ) : (M ^ k) v = c ^ k • v := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ' M k, Module.End.mul_apply, ih, map_smul, hv, smul_smul, pow_succ c k]

theorem eig_G {V : Type} [AddCommGroup V] [Module ℂ V] {q : ℕ} (M G : Module.End ℂ V)
    (hMG : M * G = G * M ^ q) {v : V} {c : ℂ} (hv : M v = c • v) (k : ℕ) :
    M ((G ^ k) v) = c ^ q ^ k • (G ^ k) v := by
  induction k with
  | zero => simpa using hv
  | succ k ih =>
    have h1 : M (G ((G ^ k) v)) = G ((M ^ q) ((G ^ k) v)) := by
      rw [← Module.End.mul_apply M G, hMG, Module.End.mul_apply]
    rw [pow_succ' G k, Module.End.mul_apply, h1, pow_apply_eig M ih q, map_smul, ← pow_mul,
      ← pow_succ]

theorem basis_side {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {q m : ℕ} (M G : Module.End ℂ V) (hG : IsUnit G) (hMG : M * G = G * M ^ q) {z : ℂ}
    (hz : ExactPer q (m + 1) z) (hr : Module.finrank ℂ V = m + 1) {v : V} (hv0 : v ≠ 0)
    (hv : M v = z • v) :
    ∃ b : Module.Basis (Fin (m + 1)) ℂ V, (∀ j : Fin (m + 1), M (b j) = z ^ q ^ (j : ℕ) • b j) ∧
      (∀ k : Fin m, G (b k.castSucc) = b k.succ) ∧
      ∃ μ : ℂ, μ ≠ 0 ∧ G (b (Fin.last m)) = μ • b 0 := by
  have hGinj : ∀ k : ℕ, Function.Injective (G ^ k) := fun k =>
    ((Module.End.isUnit_iff _).mp (hG.pow k)).injective
  obtain ⟨f, hf⟩ : ∃ f : Fin (m + 1) → V, ∀ j, f j = (G ^ (j : ℕ)) v := ⟨_, fun _ => rfl⟩
  have hMf : ∀ j : Fin (m + 1), M (f j) = z ^ q ^ (j : ℕ) • f j := fun j => by
    rw [hf]; exact eig_G M G hMG hv j
  have hfne : ∀ j, f j ≠ 0 := fun j h =>
    hv0 (hGinj (j : ℕ) (by rw [map_zero, ← hf]; exact h))
  have hinj : Function.Injective (fun j : Fin (m + 1) => z ^ q ^ (j : ℕ)) :=
    fun a b h => Fin.ext (per_inj hz a.2 b.2 h)
  have hli : LinearIndependent ℂ f :=
    Module.End.eigenvectors_linearIndependent' M _ hinj f
      (fun j => ⟨Module.End.mem_eigenspace_iff.mpr (hMf j), hfne j⟩)
  obtain ⟨b, hb⟩ : ∃ b : Module.Basis (Fin (m + 1)) ℂ V, ∀ j, b j = f j :=
    ⟨basisOfLinearIndependentOfCardEqFinrank hli (by rw [Fintype.card_fin, hr]),
      fun j => congrFun (coe_basisOfLinearIndependentOfCardEqFinrank hli _) j⟩
  refine ⟨b, fun j => by rw [hb]; exact hMf j, fun k => ?_, ?_⟩
  · rw [hb, hb, hf, hf, Fin.val_succ, Fin.coe_castSucc, pow_succ', Module.End.mul_apply]
  · obtain ⟨x, hxdef⟩ : ∃ x, x = G (b (Fin.last m)) := ⟨_, rfl⟩
    have hxG : x = (G ^ (m + 1)) v := by
      rw [hxdef, hb, hf, Fin.val_last, pow_succ', Module.End.mul_apply]
    have hx : M x = z • x := by
      rw [hxG, eig_G M G hMG hv, hz.2.1]
    obtain ⟨c, hcdef⟩ : ∃ c, c = b.repr x := ⟨_, rfl⟩
    have hsum : x = ∑ j, c j • b j := by rw [hcdef]; exact (b.sum_repr x).symm
    have hcoef : ∀ j, c j * z ^ q ^ (j : ℕ) = z * c j := by
      intro j
      have e1 : M x = ∑ j, (c j * z ^ q ^ (j : ℕ)) • b j := by
        conv_lhs => rw [hsum]
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [map_smul, hb j, hMf j, smul_smul]
      have e2 : z • x = ∑ j, (z * c j) • b j := by
        conv_lhs => rw [hsum]
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [smul_smul]
      have e3 : (∑ j, (c j * z ^ q ^ (j : ℕ)) • b j) = ∑ j, (z * c j) • b j :=
        e1.symm.trans (hx.trans e2)
      have e4 := congrArg (fun y => b.repr y j) e3
      simp only [Module.Basis.repr_sum_self] at e4
      exact e4
    have hc0 : ∀ j : Fin (m + 1), j ≠ 0 → c j = 0 := by
      intro j hj
      have hjpos : 0 < (j : ℕ) := Nat.pos_of_ne_zero (fun h => hj (Fin.ext h))
      have hne : z ^ q ^ (j : ℕ) ≠ z := hz.2.2 j hjpos j.2
      have h2 : c j * (z ^ q ^ (j : ℕ) - z) = 0 := by
        rw [mul_sub, hcoef j]
        ring
      rcases mul_eq_zero.mp h2 with h | h
      · exact h
      · exact absurd (sub_eq_zero.mp h) hne
    have hx0 : x = c 0 • b 0 := by
      conv_lhs => rw [hsum]
      rw [Finset.sum_eq_single 0 (fun j _ hj => by rw [hc0 j hj, zero_smul]) (by simp)]
    refine ⟨c 0, fun h => ?_, ?_⟩
    · have hx00 : G (b (Fin.last m)) = 0 := by rw [← hxdef, hx0, h, zero_smul]
      exact b.ne_zero (Fin.last m)
        (((Module.End.isUnit_iff _).mp hG).injective (by rw [map_zero]; exact hx00))
    · rw [← hxdef]
      exact hx0

end PairingFactorsThroughPeriods

open PairingFactorsThroughPeriods in
theorem st1b : St1b := by
  unfold St1b
  intro V V' _ _ _ _ _ _ q n i M G M' G' z hn hr hr' hG hG' hMG hMG' hz hzM hzM' hdet
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨v, hv⟩ := hzM.exists_hasEigenvector
  obtain ⟨v1, hv1⟩ := hzM'.exists_hasEigenvector
  have hG'inj : ∀ k : ℕ, Function.Injective (G' ^ k) := fun k =>
    ((Module.End.isUnit_iff _).mp (hG'.pow k)).injective
  have hv1' : M' v1 = z ^ q ^ i • v1 := Module.End.mem_eigenspace_iff.mp hv1.1
  have hle : i ≤ (m + 1) * i := by
    rw [add_mul, one_mul]
    exact Nat.le_add_left i (m * i)
  have hw : M' ((G' ^ ((m + 1) * i - i)) v1) = z • (G' ^ ((m + 1) * i - i)) v1 := by
    rw [eig_G M' G' hMG' hv1', ← pow_mul, ← pow_add, Nat.add_sub_cancel' hle,
      per_mul (exactPer_per hz)]
  obtain ⟨b, hbM, hbG, μ, hμ, hbl⟩ :=
    basis_side M G hG hMG hz hr hv.2 (Module.End.mem_eigenspace_iff.mp hv.1)
  obtain ⟨b', hbM', hbG', μ', hμ', hbl'⟩ :=
    basis_side M' G' hG' hMG' hz hr'
      (fun h => hv1.2 (hG'inj _ (by rw [map_zero]; exact h))) hw
  obtain ⟨T, hT⟩ : ∃ T : V ≃ₗ[ℂ] V', ∀ j, T (b j) = b' j :=
    ⟨b.equiv b' (Equiv.refl _), fun j => by simp⟩
  have hTs : ∀ j, T.symm (b' j) = b j := fun j => by rw [← hT j, LinearEquiv.symm_apply_apply]
  obtain ⟨G'', hG''⟩ : ∃ G'' : Module.End ℂ V,
      G'' = T.symm.toLinearMap ∘ₗ G' ∘ₗ T.toLinearMap := ⟨_, rfl⟩
  have hdet'' : LinearMap.det G'' = LinearMap.det G' := by
    rw [hG'']
    have h := LinearMap.det_conj G' T.symm
    simpa using h
  obtain ⟨d, hd⟩ : ∃ d : Fin (m + 1) → ℂ, d = fun j => if j = Fin.last m then μ / μ' else 1 :=
    ⟨_, rfl⟩
  obtain ⟨D, hDdef⟩ : ∃ D : Module.End ℂ V, D = Matrix.toLin b b (Matrix.diagonal d) := ⟨_, rfl⟩
  have hD : ∀ j, D (b j) = d j • b j := fun j => by
    rw [hDdef, Matrix.toLin_self]
    simp [Matrix.diagonal_apply]
  have hGD : G = G'' ∘ₗ D := by
    apply b.ext
    intro j
    rw [LinearMap.comp_apply, hD j, map_smul, hG'']
    rcases Fin.eq_castSucc_or_eq_last j with ⟨k, rfl⟩ | rfl
    · have h1 : d k.castSucc = 1 := by
        rw [hd]
        simp [Fin.castSucc_lt_last k |>.ne]
      rw [h1, one_smul]
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [hT, hbG', hTs, hbG]
    · have h1 : d (Fin.last m) = μ / μ' := by rw [hd]; simp
      rw [h1]
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [hT, hbl', map_smul, hTs, smul_smul, div_mul_cancel₀ μ hμ', hbl]
  have hdetD : LinearMap.det D = μ / μ' := by
    rw [hDdef, LinearMap.det_toLin, Matrix.det_diagonal, hd]
    simp
  have hμμ : μ = μ' := by
    have h1 : LinearMap.det G = LinearMap.det G' * (μ / μ') := by
      rw [hGD, LinearMap.det_comp, hdet'', hdetD]
    have hne : LinearMap.det G' ≠ 0 := (hG'.map LinearMap.det).ne_zero
    rw [hdet] at h1
    have h2 : μ / μ' = 1 := mul_left_cancel₀ hne (by rw [mul_one]; exact h1.symm)
    exact (div_eq_one_iff_eq hμ').mp h2
  refine ⟨T, fun v => ?_, fun v => ?_⟩
  · have h : T.toLinearMap ∘ₗ M = M' ∘ₗ T.toLinearMap := by
      apply b.ext
      intro j
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [hbM, map_smul, hT, hbM']
    exact LinearMap.congr_fun h v
  · have h : T.toLinearMap ∘ₗ G = G' ∘ₗ T.toLinearMap := by
      apply b.ext
      intro j
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
      rcases Fin.eq_castSucc_or_eq_last j with ⟨k, rfl⟩ | rfl
      · rw [hbG, hT, hT, hbG']
      · rw [hbl, map_smul, hT, hT, hbl', hμμ]
    exact LinearMap.congr_fun h v

end PositivityTheory.Rg.DzCount

end
end
