module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselThetaContractionExtendByZeroVacuumSmooth
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ValuationEqZeroOfRootOfSUnitRatio
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationTwoVariableModelAndLineExte
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsFinCombOfIsThetaAt

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistPrimeRationalCosetSameOrbitIffLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistPrimeRationalCosetSameOrbitIffLevel
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge
open GlobalTheory.SymBridge (toLoc IsOrd yPos xPos IsCompl)

noncomputable section
namespace GlobalTheory.TwBridge.LevOrb
open GlobalTheory.TwBridge.Lev

theorem inX_zero {E : Type} [Field E] (n : ℕ) (x : Fin n → E) : Loc.inX E n 0 x = x := by
  funext l
  simp [Loc.inX, show l.1 < n from l.2]

theorem mem_prX_zero {E : Type} [Field E] {n : ℕ} (J : Subgroup ((Fin (n + 0) → E) ≃ₗ[E] (Fin (n + 0) → E)))
    (κ : (Fin n → E) ≃ₗ[E] (Fin n → E)) : κ ∈ Loc.prX (Loc.Cbe J 1) ↔ (show (Fin (n + 0) → E) ≃ₗ[E] (Fin (n + 0) → E) from κ) ∈ J := by
  have hR : ∀ γ : (Fin (n + 0) → E) ≃ₗ[E] (Fin (n + 0) → E), Loc.R1cond E n 0 γ := fun γ => by
    rw [r1cond_iff]
    intro l l' h
    have := l.2
    have := l'.2
    omega
  constructor
  · rintro ⟨r, hr, hx⟩
    have h2 : r ∈ J := by simpa [MulAut.conj_apply] using hr.2
    have : r = κ := LinearEquiv.ext fun x => by simpa only [inX_zero] using hx x
    exact this ▸ h2
  · intro h
    refine ⟨κ, ⟨⟨hR _, hR _⟩, ?_⟩, fun x => by rw [inX_zero, inX_zero]⟩
    simpa [MulAut.conj_apply] using h

section Orb
variable {E k : Type} [Field E] [NumberField E] [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {P : HeightOneSpectrum (𝓞 E)} {q : ℕ} {ι : E →+* k} {ϖ : kˣ} {A : Type} [Fintype A] [DecidableEq A] {n : ℕ}

omit [Fintype A] [DecidableEq A] in
theorem mem_box_iff (hc : IsCompl P q ι ϖ) (e : A ≃ Fin n) (M : ℕ) (v : Sp E n) :
    (fun r => ι (v (e r))) ∈ box A (ϖ ^ M) ↔ ((q : E) ^ M)⁻¹ • v ∈ stdAt E n P := by
  rw [stdAt, StabRef.mem_locStd, mem_box]
  have key : ∀ a : E, valuation k (ι a) ≤ valuation k ((ϖ ^ M : kˣ) : k) ↔ IntAt P (((q : E) ^ M)⁻¹ * a) := fun a => by
    rw [← hc.int, map_mul, map_inv₀, map_pow, ← hc.unif, Valuation.mem_integer_iff, map_mul, map_inv₀, Units.val_pow_eq_pow_val,
      inv_mul_le_iff₀ (zero_lt_iff.2 (by simp)), mul_one]
  refine ⟨fun h l => ?_, fun h r => (key _).2 (h (e r))⟩
  obtain ⟨r, rfl⟩ := e.surjective l
  exact (key _).1 (h r)

omit [NumberField E] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem phi_mulVec (e : A ≃ Fin n) (e' : A ⊕ Fin 0 ≃ Fin n) (he : ∀ a, e' (.inl a) = e a) (γ : (Fin n → E) ≃ₗ[E] (Fin n → E))
    (z : Fin n → E) : (phi ι e' γ).val.toBlocks₁₁ *ᵥ (fun r => ι (z (e r))) = fun r => ι (γ z (e r)) := by
  funext r
  set_option synthInstance.maxHeartbeats 100000 in
    rw [apply_sum γ z, map_sum, ← e.sum_comp]
  simp [mulVec, dotProduct, toBlocks₁₁, phi_val, toLoc, he]

theorem mulVec_mem_box {g : GL (A ⊕ Fin 0) k} (hg : g ∈ KO k _) (a : kˣ) {y : A → k} (hy : y ∈ box A a) :
    g.val.toBlocks₁₁ *ᵥ y ∈ box A a := fun i => by
  refine Valuation.map_sum_le _ fun j _ => ?_
  rw [map_mul]
  exact mul_le_of_le_one_of_le ((mem_KO.1 hg).1 (Sum.inl i) (Sum.inl j)) (hy j)

theorem sameOrb_iff (hc : IsCompl P q ι ϖ) (e : A ≃ Fin n) (e' : A ⊕ Fin 0 ≃ Fin n) (he : ∀ a, e' (.inl a) = e a)
    (J : Subgroup (GL (A ⊕ Fin 0) k)) (h1 : KOne k _ ≤ J) (h2 : J ≤ KO k _) (M : ℕ) (z z' : Sp E n) :
    GlobalTheory.QPl.SameOrb J (box _ (ϖ ^ M)) (Submodule.Quotient.mk fun r => ι (z (e r))) (Submodule.Quotient.mk fun r => ι (z' (e r))) ↔
      ∃ γ : Sp E n ≃ₗ[E] Sp E n, phi ι e' γ ∈ J ∧ ((q : E) ^ M)⁻¹ • (γ z - z') ∈ stdAt E n P := by
  have hsub : ∀ γ : Sp E n ≃ₗ[E] Sp E n, (phi ι e' γ).val.toBlocks₁₁ *ᵥ (fun r => ι (z (e r))) - (fun r => ι (z' (e r))) =
      fun r => ι ((γ z - z') (e r)) := fun γ => by
    rw [phi_mulVec e e' he]
    funext r
    simp
  constructor
  · rintro ⟨g, hg, y, hy, hy'⟩
    rw [Submodule.Quotient.eq] at hy hy'
    have h0 : g.val.toBlocks₁₁ *ᵥ (fun r => ι (z (e r))) - (fun r => ι (z' (e r))) ∈ box A (ϖ ^ M) := by
      have := sub_mem hy' (mulVec_mem_box (h2 hg) _ hy)
      rw [mulVec_sub] at this
      convert this using 1
      abel
    have hU1 : IsOpen {N : Matrix (A ⊕ Fin 0) (A ⊕ Fin 0) k | MaxM ((g⁻¹).val * N - 1)} := by
      simp only [MaxM, Set.setOf_forall]
      refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
      exact IsOpen.preimage (f := fun N : Matrix (A ⊕ Fin 0) (A ⊕ Fin 0) k => ((g⁻¹).val * N - 1) i j)
        (t := {z | valuation k z < 1}) (by fun_prop) (by simpa using (valuation k).isOpen_ball 1)
    have ho : IsOpen ((box A (ϖ ^ M) : Submodule 𝒪[k] (A → k)) : Set (A → k)) := by
      convert (isOpen_set_pi Set.finite_univ fun (_ : A) _ => isOpen_cball (ϖ ^ M)) using 1
      ext z; simp [mem_box, cball]
    have hU2 : IsOpen {N : Matrix (A ⊕ Fin 0) (A ⊕ Fin 0) k |
        N.toBlocks₁₁ *ᵥ (fun r => ι (z (e r))) - (fun r => ι (z' (e r))) ∈ box A (ϖ ^ M)} := by
      refine ho.preimage (f := fun N : Matrix (A ⊕ Fin 0) (A ⊕ Fin 0) k =>
        N.toBlocks₁₁ *ᵥ (fun r => ι (z (e r))) - (fun r => ι (z' (e r)))) ?_
      have hb : Continuous fun N : Matrix (A ⊕ Fin 0) (A ⊕ Fin 0) k => N.toBlocks₁₁ :=
        continuous_pi fun i => continuous_pi fun j => continuous_apply_apply (Sum.inl i) (Sum.inl j)
      exact (hb.matrix_mulVec continuous_const).sub continuous_const
    obtain ⟨M₀, ⟨a1, a2⟩, -⟩ := exists_approx ι hc.dense g.val (hU1.inter hU2) ⟨by
      change MaxM _
      rw [Units.inv_mul, sub_self]
      exact maxM_zero, h0⟩
    obtain ⟨u, hu, eu⟩ := exists_mem_KOne a1
    have ev : (g * u).val = M₀.map ι := by
      rw [Units.val_mul, eu, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
    obtain ⟨γ, hγ⟩ := exists_phi ι e' M₀ _ ev
    refine ⟨γ, hγ ▸ mul_mem hg (h1 hu), (mem_box_iff hc e M _).1 ?_⟩
    rw [← hsub, hγ, ev]
    exact a2
  · rintro ⟨γ, hγ, h⟩
    refine ⟨_, hγ, _, rfl, (Submodule.Quotient.eq _).2 ?_⟩
    rw [hsub]
    exact (mem_box_iff hc e M _).2 h

end Orb

theorem mem_prX_JQ {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E)) (q kj n c : ℕ) (hc : c = 0)
    (κ : Sp E n ≃ₗ[E] Sp E n) : κ ∈ Loc.prX (Loc.Cbe (LocE.JQ P q kj n c) 1) ↔
      (show Sp E (n + 0) ≃ₗ[E] Sp E (n + 0) from κ) ∈ LocE.JQ P q kj n 0 := by
  subst hc
  exact mem_prX_zero _ κ

theorem sameOrb_iff_level : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (s : ℕ) (W : TwData k), AtTwist (R := R) sel mu cst σ₀ P ι s W → ∀ (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m), L.Ok Ch sel mu cst G s → ∀ (b : L.β (s + 1)) (hQ : P.1 ∈ QE sel (mu : Chr X.F X.E X.K)) (e : XIx (Fin R.k) (Fin R.t) (s + 1) ≃ Fin (R.N (s + 1))), GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.xPos e → ∀ z z' : Sp X.E (R.N (s + 1)), (GlobalTheory.QPl.SameOrb ((W.T s R).lev (s + 1) 0 rfl).J (box _ (W.ϖ ^ cst.M)) (Submodule.Quotient.mk fun r => ι (z (e r))) (Submodule.Quotient.mk fun r => ι (z' (e r))) ↔ ∃ κ ∈ (L.levQ (s + 1) b ⟨P.1, hQ⟩).H, ((qOf P.1 : X.E) ^ cst.M)⁻¹ • (κ.1 z - z') ∈ stdAt X.E (R.N (s + 1)) P.1) := by
  intro X Pr R Ch sel S₀ mu cst σ₀ P k _ _ _ _ ι s W hA L G hL b hQ e he z z'
  have hc : cOf R (s + 1) = 0 := by have := hA.steps; unfold cOf; omega
  have hn : R.N (s + 1) = R.k + (s + 1) * (R.t + 1) := rfl
  let e' : XIx (Fin R.k) (Fin R.t) (s + 1) ⊕ Fin 0 ≃ Fin (R.N (s + 1) + 0) := (Equiv.sumEmpty _ _).trans e
  have he' : IsOrd (yPos xPos (R.N (s + 1))) e' := by
    rintro (a | a)
    · exact he a
    · exact a.elim0
  set o := stdOrd (Fin R.k) (Fin R.t) (s + 1) 0 (rfl : s + 1 + 0 = s + 1) with ho
  have hconj : ∀ g : GL _ k, (plainFrame (k := k) o).conj.symm g = (reGL o).symm g := fun g => by
    rw [MulEquiv.symm_apply_eq, LatFrame.conj_apply, show (plainFrame (k := k) o).bas = 1 from rfl,
      show (plainFrame (k := k) o).ord = o from rfl, MulEquiv.apply_symm_apply]
    simp
  have hJ : ∀ g, g ∈ ((W.T s R).lev (s + 1) 0 rfl).J ↔ (reGL o).symm g ∈ (parahoric _ (Fin (s + 1) × Fin R.t) W.δ W.tame).J :=
    fun g => by rw [← hconj]; rfl
  have hmem : ∀ γ : Sp X.E (R.N (s + 1)) ≃ₗ[X.E] Sp X.E (R.N (s + 1)), phi ι e' γ ∈ ((W.T s R).lev (s + 1) 0 rfl).J ↔
      γ ∈ prCat (Pr := Pr) cst.sharp (s + 1) P.1 (L.h (s + 1) b P) := fun γ => by
    rw [hJ, hL.last_h, prCat, Jat, if_neg hA.nmem, mem_prX_JQ _ _ _ _ _ hc]
    exact mem_par_iff (c := 0) (s := s) hA.compl W.unif rfl hn he' W.tame γ
  have hle : ((W.T s R).lev (s + 1) 0 rfl).J ≤ KO k _ := fun g hg => by
    have h := (mem_parahoric.1 ((hJ g).1 hg)).1
    rw [mem_KO] at h ⊢
    rw [← map_inv] at h
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · simpa [reGL_symm_val] using h.1 (o.symm i) (o.symm j)
    · simpa [reGL_symm_val] using h.2 (o.symm i) (o.symm j)
  rw [sameOrb_iff hA.compl e e' (fun _ => rfl) _
    (fun u hu => (hJ u).2 (((parahoric _ (Fin (s + 1) × Fin R.t) W.δ W.tame).reindex o).KOne_le hu)) hle, hL.grpQ]
  constructor
  · rintro ⟨γ, h1, h2⟩
    have h3 := (hmem γ).1 h1
    exact ⟨⟨γ, hL.int _ b P h3⟩, h3, h2⟩
  · rintro ⟨κ, h1, h2⟩
    exact ⟨κ.1, (hmem _).2 h1, h2⟩

end GlobalTheory.TwBridge.LevOrb
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistPrimeRationalCosetSameOrbitIffLevelStatement
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistPrime_rational_coset_sameOrbit_iff_level : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (s : ℕ) (W : TwData k), AtTwist (R := R) sel mu cst σ₀ P ι s W → ∀ (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m), L.Ok Ch sel mu cst G s → ∀ (b : L.β (s + 1)) (hQ : P.1 ∈ QE sel (mu : Chr X.F X.E X.K)) (e : XIx (Fin R.k) (Fin R.t) (s + 1) ≃ Fin (R.N (s + 1))), GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.xPos e → ∀ z z' : Sp X.E (R.N (s + 1)), (GlobalTheory.QPl.SameOrb ((W.T s R).lev (s + 1) 0 rfl).J (box _ (W.ϖ ^ cst.M)) (Submodule.Quotient.mk fun r => ι (z (e r))) (Submodule.Quotient.mk fun r => ι (z' (e r))) ↔ ∃ κ ∈ (L.levQ (s + 1) b ⟨P.1, hQ⟩).H, ((qOf P.1 : X.E) ^ cst.M)⁻¹ • (κ.1 z - z') ∈ stdAt X.E (R.N (s + 1)) P.1) := by
  first | exact @GlobalTheory.TwBridge.LevOrb.sameOrb_iff_level | exact GlobalTheory.TwBridge.LevOrb.sameOrb_iff_level | (intros; apply GlobalTheory.TwBridge.LevOrb.sameOrb_iff_level <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawCommonRealDatumBiThetaVacuumContraction
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawCommonRealDatumBiThetaVacuumContraction
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.VReal

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

theorem biTheta_add {A S A' : HSp D} {f g : WO A S → WO S A' → ℂ} (hf : IsBiTheta ψ A S A' f)
    (hg : IsBiTheta ψ A S A' g) : IsBiTheta ψ A S A' (f + g) := by
  refine ⟨hf.cont.add hg.cont, ?_, fun γ u v => ?_, fun γ u v => ?_, ?_, ?_⟩
  · intro n L L' hL hL' hLf hL'f u v
    exact (hf.smooth n L L' hL hL' hLf hL'f u v).add (hg.smooth n L L' hL hL' hLf hL'f u v)
  · simp only [Pi.add_apply]; rw [hf.quasiL, hg.quasiL]; ring
  · simp only [Pi.add_apply]; rw [hf.quasiR, hg.quasiR]; ring
  · obtain ⟨U, hU, hUf⟩ := hf.levL
    obtain ⟨V, hV, hVf⟩ := hg.levL
    refine ⟨U ⊓ V, hU.inter hV, fun a ha ha' v => ?_⟩
    funext u
    have h1 := congrFun (hUf a ha.1 ha' v) u
    have h2 := congrFun (hVf a ha.2 ha' v) u
    simp only [heisO, Pi.add_apply] at h1 h2 ⊢
    rw [mul_add, h1, h2]
  · obtain ⟨U, hU, hUf⟩ := hf.levR
    obtain ⟨V, hV, hVf⟩ := hg.levR
    refine ⟨U ⊓ V, hU.inter hV, fun a ha ha' u => ?_⟩
    funext v
    have h1 := congrFun (hUf a ha.1 ha' u) v
    have h2 := congrFun (hVf a ha.2 ha' u) v
    simp only [heisO, Pi.add_apply] at h1 h2 ⊢
    rw [mul_add, h1, h2]

theorem biTheta_zero {A S A' : HSp D} : IsBiTheta ψ A S A' 0 := by
  refine ⟨?_, fun n L L' _ _ _ _ u v => ?_, fun γ u v => by simp, fun γ u v => by simp, ⟨⊤, by rw [AddSubgroup.coe_top]; exact isOpen_univ, fun a _ _ v => ?_⟩,
    ⟨⊤, by rw [AddSubgroup.coe_top]; exact isOpen_univ, fun a _ _ u => ?_⟩⟩
  · simp only [Pi.zero_apply]; exact continuous_const
  · simp only [Pi.zero_apply]; exact contDiff_const
  · funext x; simp [heisO]
  · funext x; simp [heisO]

theorem biTheta_app (hψ : IsStdChar D ψ (-1)) {A S A' : HSp D} (o : BiOp A S A')
    (ho : ∀ i, IsFinComb (o.u i) ∧ IsFinComb (o.u' i)) {C : WO A S → WO S A' → ℂ} (hC : IsBiTheta ψ A S A' C) :
    IsBiTheta ψ A S A' (o.app ψ C) := by
  unfold BiOp.app
  exact Finset.sum_induction _ (IsBiTheta ψ A S A') (fun f g hf hg => biTheta_add hf hg) biTheta_zero
    fun i _ => GlobalTheory.FrComb.biTheta_combL hψ (GlobalTheory.FrComb.biTheta_combR hψ hC (ho i).2) (ho i).1

theorem heisO_add {S T : HSp D} (w : WO S T) (f g : WO S T → ℂ) :
    heisO ψ S T w (f + g) = heisO ψ S T w f + heisO ψ S T w g := by
  funext x; simp only [heisO, Pi.add_apply, mul_add]

theorem heisO_zero {S T : HSp D} (w : WO S T) : heisO ψ S T w 0 = 0 := by
  funext x; simp [heisO]

theorem latVac_add {S T : HSp D} {Λ : AddSubgroup (WO S T)} {f g : WO S T → ℂ} (hf : IsLatVac (heisO ψ S T) Λ f)
    (hg : IsLatVac (heisO ψ S T) Λ g) : IsLatVac (heisO ψ S T) Λ (f + g) :=
  ⟨fun u hu => by rw [heisO_add, hf.1 u hu, hg.1 u hu],
    fun e he u hu hh => by rw [heisO_add, hf.2 e he u hu hh, hg.2 e he u hu hh]⟩

theorem latVac_zero {S T : HSp D} {Λ : AddSubgroup (WO S T)} : IsLatVac (heisO ψ S T) Λ 0 :=
  ⟨fun u _ => heisO_zero _, fun _ _ u _ _ => heisO_zero u⟩

theorem latVac_sum {S T : HSp D} {Λ : AddSubgroup (WO S T)} {ι : Type} (s : Finset ι) (F : ι → WO S T → ℂ)
    (h : ∀ i ∈ s, IsLatVac (heisO ψ S T) Λ (F i)) : IsLatVac (heisO ψ S T) Λ (∑ i ∈ s, F i) :=
  Finset.sum_induction _ _ (fun _ _ hf hg => latVac_add hf hg) latVac_zero h

def combEnd (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (c : WO S T →₀ ℂ) : Module.End ℂ (WO S T → ℂ) where
  toFun := comb ψ S T c
  map_add' f g := by
    funext u; simp only [GlobalTheory.FrComb.comb_apply, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' a f := by
    funext u
    simp only [GlobalTheory.FrComb.comb_apply, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by ring

theorem vac_of_true {S T : HSp D} {LS : Lat S} {LT : Lat T} {P : Pl D → Prop} {f : WO S T → ℂ}
    (h : Vac ψ S T LS LT (fun _ => True) f) : Vac ψ S T LS LT P f := by
  have hle : latO S T (LS : Set _) (LT : Set _) P ≤ latO S T (LS : Set _) (LT : Set _) fun _ => True := by
    apply AddSubgroup.closure_mono
    rintro w ⟨α, hα, -, rest⟩
    exact ⟨α, hα, fun v hv => absurd trivial hv, rest⟩
  unfold Vac IsLatVac at h ⊢
  exact ⟨h.1, fun u hu => h.2.1 u (hle hu), fun e he u hu hh => h.2.2 e he u (hle hu) hh⟩

theorem vac_union (hψ : IsStdChar D ψ (-1)) (S T : HSp D) (P : Pl D → Prop) (LS : Lat S) (LT : Lat T) (f : WO S T → ℂ)
    (hS : IsSelfDualC S LS) (hT : IsSelfDualC T LT) (h1 : Vac ψ S T LS LT P f) (h2 : Vac ψ S T LS LT (fun p => ¬ P p) f) :
    Vac ψ S T LS LT (fun _ => True) f := by
  have H := (GlobalTheory.DisjComb.main D ψ hψ S T P (fun p => ¬ P p) (fun p hp hq => hq hp)).2.2.2.2 LS LT f hS hT
  have e : (fun p => P p ∨ ¬ P p) = fun _ => True := funext fun p => propext ⟨fun _ => trivial, fun _ => em _⟩
  have h3 := H.2 ⟨h1, h2⟩
  rwa [e] at h3

theorem real_of (hψ : IsStdChar D ψ (-1)) (P : Pl D → Prop)
    (hcomb : ∀ (S T : HSp D) (e : WO S T →₀ ℂ), CombAt P e → IsFinComb e ∧
      ∀ LS LT f, Vac ψ S T LS LT (fun p => ¬ P p) f → Vac ψ S T LS LT (fun p => ¬ P p) (comb ψ S T e f))
    {A S A' : HSp D} {LA : Lat A} {LS : Lat S} {LA' : Lat A'} (hA : IsSelfDualC A LA) (hS : IsSelfDualC S LS)
    (hA' : IsSelfDualC A' LA') (o : BiOp A S A') (ho : ∀ i, CombAt P (o.u i) ∧ CombAt P (o.u' i))
    {C : WO A S → WO S A' → ℂ} (hC : IsBiTheta ψ A S A' C) (hoff : BiVacAt ψ LA LS LA' (fun p => ¬ P p) C)
    (hon : BiVacAt ψ LA LS LA' P (o.app ψ C)) :
    IsBiTheta ψ A S A' (o.app ψ C) ∧ IsBiVac ψ A S A' LA LS LA' (o.app ψ C) ∧ IsBiSmooth (o.app ψ C) := by
  have hfin : ∀ i, IsFinComb (o.u i) ∧ IsFinComb (o.u' i) :=
    fun i => ⟨(hcomb _ _ _ (ho i).1).1, (hcomb _ _ _ (ho i).2).1⟩
  have hB := biTheta_app hψ o hfin hC
  have hoffApp : BiVacAt ψ LA LS LA' (fun p => ¬ P p) (o.app ψ C) := by
    refine ⟨fun v => ⟨GlobalTheory.FrComb.slice_left hB v, ?_⟩, fun u => ⟨GlobalTheory.FrComb.slice_right hB u, ?_⟩⟩
    · have e : (fun u => o.app ψ C u v) = ∑ i, fun u => biComb ψ A S A' (o.u i) (o.u' i) C u v := by
        funext u; simp only [BiOp.app, Finset.sum_apply]
      rw [e]
      refine latVac_sum _ _ fun i _ => ?_
      have hR := GlobalTheory.FrComb.biTheta_combR hψ hC (hfin i).2
      have hg : Vac ψ A S LA LS (fun p => ¬ P p) (fun u' => comb ψ S A' (o.u' i) (C u') v) :=
        ⟨GlobalTheory.FrComb.slice_left hR v, GlobalTheory.FrComb.latVac_opR (fun v => (hoff.1 v).2) (combEnd ψ S A' (o.u' i)) v⟩
      exact ((hcomb _ _ _ (ho i).1).2 LA LS _ hg).2
    · have e : o.app ψ C u = ∑ i, fun v => biComb ψ A S A' (o.u i) (o.u' i) C u v := by
        funext v; simp only [BiOp.app, Finset.sum_apply]
      rw [e]
      refine latVac_sum _ _ fun i _ => ?_
      exact GlobalTheory.FrComb.latVac_opL (K := fun u' => comb ψ S A' (o.u' i) (C u'))
        (fun u' => ((hcomb _ _ _ (ho i).2).2 LS LA' _ (hoff.2 u')).2) (combEnd ψ A S (o.u i)) u
  have hT : BiVacAt ψ LA LS LA' (fun _ => True) (o.app ψ C) :=
    ⟨fun v => vac_union hψ _ _ P _ _ _ hA hS (hon.1 v) (hoffApp.1 v),
      fun u => vac_union hψ _ _ P _ _ _ hS hA' (hon.2 u) (hoffApp.2 u)⟩
  exact ⟨hB, ⟨hB.cont, fun v => hT.1 v, fun u => hT.2 u⟩, hB.smooth⟩

theorem v_real : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t), c.Is → v.Is → t.Is → VacLaw (t := t) v → TLaw v w → FlatLaw D → (∀ j σ h Ψ₁ Ψ₂, Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (fun _ => True) Ψ₁ → Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (fun _ => True) Ψ₂ → IsBiTheta c.ψ _ _ _ (c.ctr j σ h (t.sBF j (σ + 1) h) (t.sFB j σ h) Ψ₁ Ψ₂) ∧ c.IsReal j ((v.op j).app c.ψ (c.ctr j σ h (t.sBF j (σ + 1) h) (t.sFB j σ h) Ψ₁ Ψ₂))) ∧ ∀ j h Ψ₁ Ψ₂, WeilOK (t := t) v → Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (fun _ => True) Ψ₁ → Vac c.ψ _ _ (v.N (j + 1)) v.NT (fun _ => True) Ψ₂ → IsBiTheta c.ψ _ _ _ (c.lst j h (v.τ j h) (t.sBF j 0 h) Ψ₁ Ψ₂) ∧ c.IsReal j ((v.op j).app c.ψ (c.lst j h (v.τ j h) (t.sBF j 0 h) Ψ₁ Ψ₂)) := by
  intro D c v t w hc hv ht hV hT hF
  have hψ := hc.std
  have hfl := GlobalTheory.Unf.FlatTheta.flat_isThetaFun D hF c.ψ
  have hcomb : ∀ (S T : HSp D) (e : WO S T →₀ ℂ), CombAt (· ∈ v.tP) e → IsFinComb e ∧
      ∀ LS LT f, Vac c.ψ S T LS LT (fun p => ¬ p ∈ v.tP) f → Vac c.ψ S T LS LT (fun p => ¬ p ∈ v.tP) (comb c.ψ S T e f) :=
    fun S T e he => (GlobalTheory.DisjComb.main D c.ψ hψ S T (· ∈ v.tP) (fun p => ¬ p ∈ v.tP) (fun p hp hq => hq hp)).2.1 e he
  refine ⟨fun j σ h Ψ₁ Ψ₂ h1 h2 => ?_, fun j h Ψ₁ Ψ₂ hW h1 h2 => ?_⟩
  · have hC : IsBiTheta c.ψ _ _ _ (c.ctr j σ h (t.sBF j (σ + 1) h) (t.sFB j σ h) Ψ₁ Ψ₂) :=
      (GlobalTheory.ContrComb.contr_comb_main D c.ψ hψ (σ + 1) σ (c.B j (σ + 1) h) (c.B (j + 1 + 1) σ (idx_step h)) (c.lnk j σ h) (c.X (j + 1))
        (c.vL j σ h) (flatBF (t.sBF j (σ + 1) h) Ψ₁) (flatFB (t.sFB j σ h) Ψ₂)
        (hfl.1 (σ + 1) (c.B j (σ + 1) h) (c.J j (σ + 1) h) (t.sBF j (σ + 1) h) Ψ₁ h1.1)
        (hfl.2 σ (c.J j (σ + 1) h) (c.B (j + 1 + 1) σ (idx_step h)) (t.sFB j σ h) Ψ₂ h2.1)).1
    have R := real_of hψ (· ∈ v.tP) hcomb (hc.x j (by omega)).sd (hc.x (j + 1) (by omega)).sd
      (hc.x (j + 1 + 1) (by omega)).sd (v.op j) (hv.atT j).2 hC (hV.1 j σ h Ψ₁ Ψ₂ (vac_of_true h1) (vac_of_true h2))
      (hT.1 j σ h Ψ₁ Ψ₂ (vac_of_true h1) (vac_of_true h2)).1
    exact ⟨hC, R.2.1, R.2.2⟩
  · have hC : IsBiTheta c.ψ _ _ _ (c.lst j h (v.τ j h) (t.sBF j 0 h) Ψ₁ Ψ₂) :=
      GlobalTheory.LastBiTheta.isBiTheta_lastBi D c.ψ hψ _ _ _ _ _ _ _ (c.bes j 0 h).o (c.oT (j + 1 + 1) h) (v.τ j h) (hW.tau j h).2 (flatBF (t.sBF j 0 h) Ψ₁) (fun w => Ψ₂ ((c.jac j 0 h).d.ext0 c.T w))
        (hfl.1 0 (c.B j 0 h) (c.J j 0 h) (t.sBF j 0 h) Ψ₁ h1.1) ((GlobalTheory.WeilSrc.Zero.theta_iff (c.jac j 0 h).d Ψ₂).2 h2.1)
    have R := real_of hψ (· ∈ v.tP) hcomb (hc.x j (by omega)).sd (hc.x (j + 1) (by omega)).sd
      (hc.x (j + 1 + 1) (by omega)).sd (v.op j) (hv.atT j).2 hC (hV.2 j h Ψ₁ Ψ₂ (vac_of_true h1) (vac_of_true h2))
      (hT.2 j h Ψ₁ Ψ₂ (vac_of_true h1) (vac_of_true h2)).1
    exact ⟨hC, R.2.1, R.2.2⟩

end GlobalTheory.VReal

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawCommonRealDatumBiThetaVacuumContractionStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seeSaw_commonRealDatum_biTheta_vacuum_contraction : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t), c.Is → v.Is → t.Is → VacLaw (t := t) v → TLaw v w → FlatLaw D → (∀ j σ h Ψ₁ Ψ₂, Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (fun _ => True) Ψ₁ → Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (fun _ => True) Ψ₂ → IsBiTheta c.ψ _ _ _ (c.ctr j σ h (t.sBF j (σ + 1) h) (t.sFB j σ h) Ψ₁ Ψ₂) ∧ c.IsReal j ((v.op j).app c.ψ (c.ctr j σ h (t.sBF j (σ + 1) h) (t.sFB j σ h) Ψ₁ Ψ₂))) ∧ ∀ j h Ψ₁ Ψ₂, WeilOK (t := t) v → Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (fun _ => True) Ψ₁ → Vac c.ψ _ _ (v.N (j + 1)) v.NT (fun _ => True) Ψ₂ → IsBiTheta c.ψ _ _ _ (c.lst j h (v.τ j h) (t.sBF j 0 h) Ψ₁ Ψ₂) ∧ c.IsReal j ((v.op j).app c.ψ (c.lst j h (v.τ j h) (t.sBF j 0 h) Ψ₁ Ψ₂)) := by
  exact GlobalTheory.VReal.v_real
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsAdeleEquivFin
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.Th
open Formalism.L2.JoinChr Formalism.L2.Host Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR

namespace GlobalTheory.DetRootRead

theorem exists_adele_equiv_fin (D : D7)
    (ι : (Af D.host.F ⊗[D.host.F] D.host.E) ≃+* FiniteAdeleRing (𝓞 D.host.E) D.host.E)
    (hι : ∀ x : D.host.E, ι ((1 : Af D.host.F) ⊗ₜ[D.host.F] x) =
      algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) x)
    (hint : ∀ y, y ∈ intAE D ↔ ∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v (ι y P) ≤ 1) :
    ∃ Φ : AE D ≃+* AdeleRing (𝓞 D.host.E) D.host.E, Continuous Φ ∧ Continuous Φ.symm ∧
      (∀ x : D.host.E, Φ (incA D x) = algebraMap D.host.E (AdeleRing (𝓞 D.host.E) D.host.E) x) ∧
      (∀ (P : HeightOneSpectrum (𝓞 D.host.E)) (e : AE D), IsPlIdem D e P → ∀ k : D.host.Eˣ,
        Φ (locE D e (k : D.host.E)) =
          ((localIdele D.host.E P (atFin P k) : Ideles D.host.E) : AdeleRing (𝓞 D.host.E) D.host.E)) ∧
      ∀ z : AE D, ((Φ z).1 = 1 → infPart D z = 1) ∧ (Φ z).2 = ι (finPart D z) := by
  obtain ⟨hιc, hιc'⟩ := GlobalTheory.HeckeTensorRead.continuous_finite_equiv D ι hint
  obtain ⟨j, hjc, hjc', hj⟩ := GlobalTheory.HeckeTensorRead.exists_infinite_equiv D.host.F D.host.E D.sp.cm.sig
    ⟨D.sp.cm.totReal, D.sp.cm.cmUnram.1, D.sp.cm.deg2, D.sp.cm.cmUnram.2.1⟩
  obtain ⟨s, hs, hsc, hsc'⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  let Φ : AE D ≃+* AdeleRing (𝓞 D.host.E) D.host.E := s.trans (j.prodCongr ι)
  have hΦ : ∀ z, Φ z = (j (infPart D z), ι (finPart D z)) := fun z =>
    Prod.ext (congrArg j (hs z).1) (congrArg ι (hs z).2)
  refine ⟨Φ, (hjc.prodMap hιc).comp hsc, hsc'.comp (hjc'.prodMap hιc'), fun x => ?_, fun P e he k => ?_,
    fun z => ⟨fun h => ?_, by rw [hΦ]⟩⟩
  · rw [hΦ]
    exact Prod.ext (hj x) (hι x)
  · obtain ⟨h1, h2, h3⟩ := GlobalTheory.HeckeTensorRead.isPlIdem_parts D ι hι hint he
    rw [hΦ]
    refine Prod.ext ?_ ?_
    · have h5 : j (infPart D e) = 0 := by rw [h1]; exact j.map_zero
      exact (GlobalTheory.HeckeTensorRead.map_loc (j.toRingHom.comp (infPart D)) e _).trans (by
        change 1 + j (infPart D e) * _ = 1
        rw [h5, zero_mul, add_zero])
    · have h4 : ι (finPart D (incA D (k : D.host.E))) = algebraMap D.host.E _ (k : D.host.E) := hι k
      refine (GlobalTheory.HeckeTensorRead.map_loc (ι.toRingHom.comp (finPart D)) e _).trans ?_
      exact GlobalTheory.HeckeTensorRead.loc_eq_finSingle P _ _ _ h4 h2 h3
  · rw [hΦ] at h
    exact j.injective (h.trans j.map_one.symm)

theorem read_of_equiv (D : D7) (c : (AE D)ˣ →* Circle) (χ : HChar D.host.E) (h : ChrEq c χ)
    (Φ : AE D ≃+* AdeleRing (𝓞 D.host.E) D.host.E) (hΦ : Continuous Φ.symm)
    (h1 : ∀ x : D.host.E, Φ (incA D x) = algebraMap D.host.E (AdeleRing (𝓞 D.host.E) D.host.E) x)
    (h2 : ∀ (P : HeightOneSpectrum (𝓞 D.host.E)) (e : AE D), IsPlIdem D e P → ∀ k : D.host.Eˣ,
        Φ (locE D e (k : D.host.E)) =
          ((localIdele D.host.E P (atFin P k) : Ideles D.host.E) : AdeleRing (𝓞 D.host.E) D.host.E))
    (z : (AE D)ˣ) : ((c z : Circle) : ℂ) = ((χ.1 (Units.map Φ.toRingHom.toMonoidHom z) : ℂˣ) : ℂ) := by
  let u : Ideles D.host.E →* (AE D)ˣ := Units.map Φ.symm.toRingHom.toMonoidHom
  have hu : Continuous u := Continuous.units_map _ hΦ
  have ht : Continuous (Circle.toUnits : Circle →* ℂˣ) :=
    Units.continuous_iff.2 ⟨continuous_subtype_val, by
      have h : Continuous fun z : Circle => ((z⁻¹ : Circle) : ℂ) := continuous_subtype_val.comp continuous_inv
      refine h.congr fun z => ?_
      simp⟩
  let χ' : HChar D.host.E := ⟨Circle.toUnits.comp (MonoidHom.comp c u), ht.comp (h.1.1.comp hu), fun k => by
    have : u (diagUnits D.host.E k) = Units.map (incA D).toMonoidHom k :=
      Units.ext (Φ.symm_apply_eq.2 (h1 k).symm)
    change Circle.toUnits (c (u _)) = 1
    rw [this, h.1.2, map_one]⟩
  have h' : ChrEq c χ' := ⟨h.1, fun P e he k x hx => by
    have : x = u (localIdele D.host.E P (atFin P k)) :=
      Units.ext (Φ.eq_symm_apply.2 (by rw [hx, h2 P e he k]))
    rw [this]
    rfl⟩
  rw [GlobalTheory.ChrEqUnique.hchar_unique D c χ χ' h h']
  have : u (Units.map Φ.toRingHom.toMonoidHom z) = z := Units.ext (Φ.symm_apply_apply _)
  show ((c z : Circle) : ℂ) = ((Circle.toUnits (c (u (Units.map Φ.toRingHom.toMonoidHom z))) : ℂˣ) : ℂ)
  rw [this]
  rfl

theorem comm_sigR (D : D7) (w : Af D.host.F ⊗[D.host.F] D.host.E) :
    Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E (sigR (Af D.host.F) D.sp.cm.sig w) =
      Formalism.UG.sigR D.sp.cm.sig (Af D.host.F) (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E w) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => rfl
  | add v w hv hw => rw [RingHom.map_add (f := _), map_add (f := _), hv, hw, map_add (f := _), RingHom.map_add (f := _)]

end GlobalTheory.DetRootRead

namespace GlobalTheory.DetRootRead


set_option maxHeartbeats 1000000 in
theorem chr_at_detRoot : ∀ (D : D7) (c : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E), ChrEq c χ → χ.TrivOn D.host.F →
  ∀ (V : HSp D) {n : ℕ} (hn : V.rank = n) (g : GA D V) (y : GL (Fin n) (Formalism.L2.DIV.AfE D.host.F D.host.E)), g ∈ GfC V →
    finM V hn g = (y : Matrix (Fin n) (Fin n) (Formalism.L2.DIV.AfE D.host.F D.host.E)) → ∀ x, IsDetRoot V g x → ∀ a : Neutral.B1.Ideles D.host.E,
      IsDetLift (host_cmData D.R D.host) y a → (c x : ℂ) = ((χ.1 (Chr.finPartI D.host.E a) : ℂˣ) : ℂ) := by
  intro D c χ hc ht V n hn g y hg hy x hx a ha
  let ι : (Af D.host.F ⊗[D.host.F] D.host.E) ≃+* FiniteAdeleRing (𝓞 D.host.E) D.host.E :=
    (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).toRingEquiv.trans (afIso D.host.F D.host.E)
  have hι : ∀ x : D.host.E, ι ((1 : Af D.host.F) ⊗ₜ[D.host.F] x) =
      algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) x := fun x => afIso_tmul_one _ _ x
  have hint : ∀ y, y ∈ intAE D ↔ ∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v (ι y P) ≤ 1 := fun y =>
    (GlobalTheory.HostAdeleIso.mem_intAE_iff_comm D y).trans (mem_rInt_iff _ _ _)
  obtain ⟨Φ, -, hΦ', h1, h2, h3⟩ := exists_adele_equiv_fin D ι hι hint
  let b : (AE D)ˣ := Units.map Φ.symm.toRingHom.toMonoidHom (Chr.finPartI D.host.E a)
  have hbΦ : Φ (b : AE D) = ((Chr.finPartI D.host.E a : Ideles D.host.E) : AdeleRing (𝓞 D.host.E) D.host.E) :=
    Φ.apply_symm_apply _
  have hbinf : infPart D (b : AE D) = 1 := (h3 _).1 (by rw [hbΦ]; rfl)
  have hbfin : Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E (finPart D (b : AE D)) =
      (finAf D.host.F D.host.E a : Formalism.L2.DIV.AfE D.host.F D.host.E) := by
    apply (afIso D.host.F D.host.E).injective
    rw [afIso_finAf]
    have := (h3 (b : AE D)).2
    rw [hbΦ] at this
    exact this.symm
  have hcb : ((c b : Circle) : ℂ) = ((χ.1 (Chr.finPartI D.host.E a) : ℂˣ) : ℂ) := by
    rw [read_of_equiv D c χ hc Φ hΦ' h1 h2 b]
    have hb' : Units.map Φ.toRingHom.toMonoidHom b = Chr.finPartI D.host.E a := Units.ext hbΦ
    rw [hb']
  rw [← hcb]
  obtain ⟨d, hd_def⟩ : ∃ d : AE D, d = ((matHom V g).1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)).det := ⟨_, rfl⟩
  have hdinf : infPart D d = 1 := by rw [hd_def]; exact GlobalTheory.DetOnto.infPart_det V g hg
  have hdfin : Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E (finPart D d) =
      ((Matrix.GeneralLinearGroup.det y : (Formalism.L2.DIV.AfE D.host.F D.host.E)ˣ) : Formalism.L2.DIV.AfE D.host.F D.host.E) := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, ← hy]
    unfold GlobalTheory.AdForm.finM
    rw [Matrix.det_reindex_self, hd_def]
    exact (Formalism.IndefR.Datum.toEAf D).map_det (mt V g)
  have hfa : (finAf D.host.F D.host.E a : Formalism.L2.DIV.AfE D.host.F D.host.E) =
      ((Matrix.GeneralLinearGroup.det y : (Formalism.L2.DIV.AfE D.host.F D.host.E)ˣ) : Formalism.L2.DIV.AfE D.host.F D.host.E) *
        Formalism.UG.sigR D.sp.cm.sig (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (finAf D.host.F D.host.E a : Formalism.L2.DIV.AfE D.host.F D.host.E) := by
    unfold IsDetLift Formalism.L2.DIV.h90 at ha
    rw [MonoidHom.div_apply, div_eq_iff_eq_mul] at ha
    exact congrArg Units.val ha
  have hbfin' : finPart D (b : AE D) = finPart D d * sigR (Af D.host.F) D.sp.cm.sig (finPart D (b : AE D)) := by
    apply (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).injective
    have e1 := comm_sigR D (finPart D (b : AE D))
    rw [hbfin] at e1
    refine hbfin.trans (hfa.trans ?_)
    refine Eq.trans ?_ (map_mul (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E) _ _).symm
    rw [hdfin, e1]
  obtain ⟨s, hs, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  have split : ∀ z w : AE D, infPart D z = infPart D w → finPart D z = finPart D w → z = w := fun z w hi hf =>
    s.injective (Prod.ext ((hs z).1.trans (hi.trans (hs w).1.symm)) ((hs z).2.trans (hf.trans (hs w).2.symm)))
  have hbd : (b : AE D) = d * sigR (AF D.host.F) D.sp.cm.sig (b : AE D) := by
    refine split _ _ ?_ ?_
    · rw [RingHom.map_mul, GlobalTheory.DetOnto.infPart_sigR, hbinf, hdinf, map_one, one_mul]
    · rw [RingHom.map_mul, GlobalTheory.DetRootChar.finPart_sigR]
      exact hbfin'
  let σU : (AE D)ˣ →* (AE D)ˣ := Units.map (sigR (AF D.host.F) D.sp.cm.sig).toMonoidHom
  have key : x * σU b = σU x * b := by
    apply Units.ext
    change (x : AE D) * sigR (AF D.host.F) D.sp.cm.sig (b : AE D) = sigR (AF D.host.F) D.sp.cm.sig (x : AE D) * (b : AE D)
    have hx' : (x : AE D) = d * sigR (AF D.host.F) D.sp.cm.sig (x : AE D) := by rw [hd_def]; exact hx
    conv_lhs => rw [hx']
    conv_rhs => rw [hbd]
    ring
  let q : (AE D)ˣ := x * b⁻¹
  have hq : σU q = q := by
    change σU (x * b⁻¹) = x * b⁻¹
    rw [map_mul, map_inv, mul_inv_eq_iff_eq_mul, mul_right_comm, eq_mul_inv_iff_mul_eq]
    exact key.symm
  have hσ : ∀ x, D.sp.cm.sig (D.sp.cm.sig x) = x := fun x => star_star x
  have htr : ∀ x : D.host.E, ∃ t : D.host.F, algebraMap _ _ t = x + D.sp.cm.sig x := by
    intro x
    apply (D.sp.cm.fixed _).1
    change D.sp.cm.sig _ = _
    rw [map_add (f := _), hσ, add_comm]
  obtain ⟨t, htq⟩ := GlobalTheory.Member.exists_unit_of_sigR_fixed (AF D.host.F) D.sp.cm.sig htr q (congrArg Units.val hq)
  have hcq : c q = 1 := by
    rw [← htq]
    exact GlobalTheory.GridWeil.triv_base hc ht t
  have hxq : x = q * b := by simp [q]
  rw [hxq, map_mul, hcq, one_mul]

end GlobalTheory.DetRootRead
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HomLatticeCompletionMovesByTranslatePair
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HomLatticeCompletionMovesByTranslatePair
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LatPairMove

variable {D : D7}

def finGL (V : HSp D) (g : GA D V) : GL (Fin V.rank) (EAf D) where
  val := (mt V g).map (toEAf D)
  inv := (mt V g⁻¹).map (toEAf D)
  val_inv := by
    rw [← Matrix.map_mul, ← GlobalTheory.AdelicLatMove.mt_mul, mul_inv_cancel, GlobalTheory.AdelicLatMove.mt_one,
      Matrix.map_one _ (map_zero _) (map_one _)]
  inv_val := by
    rw [← Matrix.map_mul, ← GlobalTheory.AdelicLatMove.mt_mul, inv_mul_cancel, GlobalTheory.AdelicLatMove.mt_one,
      Matrix.map_one _ (map_zero _) (map_one _)]

theorem finGL_mul (V : HSp D) (g h : GA D V) :
    (finGL V (g * h)).val = (mt V g).map (toEAf D) * (finGL V h).val := by
  change (mt V (g * h)).map (toEAf D) = _
  rw [GlobalTheory.AdelicLatMove.mt_mul, Matrix.map_mul]
  rfl

theorem latFr_rfl (V : HSp D) (N : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) :
    GlobalTheory.AdForm.latFr V rfl N = (N : Set (Fin V.rank → D.host.E)) := by
  ext x
  exact Iff.rfl

theorem eq_lat_of_moves (V : HSp D) (g : GA D V) (N : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (hN : Moves V rfl g N) : N = GlobalTheory.NormSum.AdLattice.lat (finGL V g) := by
  ext x
  rw [GlobalTheory.NormSum.AdLattice.mem_lat, hN x]
  rfl

theorem latO_move : ∀ (D : D7) (S T : HSp D) (a b : ℕ) (hS : S.rank = a) (hT : T.rank = b) (g s : GA D S) (h s' : GA D T) N N' N₁ N₁', Moves S hS g N → Moves T hT h N' → Moves S hS (s * g) N₁ → Moves T hT (s' * h) N₁' → ∀ u : WO S T, u ∈ (latO S T (latFr S hS N₁) (latFr T hT N₁') fun _ => True) ↔ ∃ u₀ ∈ (latO S T (latFr S hS N) (latFr T hT N') fun _ => True), u = actO S T s s' u₀ := by
  intro D S T a b hS hT g s h s' N N' N₁ N₁' hN hN' hN₁ hN₁' u
  subst hS hT
  rw [latFr_rfl, latFr_rfl, latFr_rfl, latFr_rfl]
  obtain rfl := eq_lat_of_moves S g N hN
  obtain rfl := eq_lat_of_moves T h N' hN'
  obtain rfl := eq_lat_of_moves S (s * g) N₁ hN₁
  obtain rfl := eq_lat_of_moves T (s' * h) N₁' hN₁'
  exact GlobalTheory.AdelicLatMove.mem_latO_iff_exists_actO D S T s s' _ _ _ _ (finGL S g) (finGL S (s * g)) (finGL T h)
    (finGL T (s' * h)) (GlobalTheory.StdFrames.isFrame_lat _) (GlobalTheory.StdFrames.isFrame_lat _) (GlobalTheory.StdFrames.isFrame_lat _)
    (GlobalTheory.StdFrames.isFrame_lat _) (GlobalTheory.NormSum.AdLattice.lat_isLattice _).toIsLattice (GlobalTheory.NormSum.AdLattice.lat_isLattice _).toIsLattice
    (GlobalTheory.NormSum.AdLattice.lat_isLattice _).toIsLattice (GlobalTheory.NormSum.AdLattice.lat_isLattice _).toIsLattice (finGL_mul S s g)
    (finGL_mul T s' h) u

end GlobalTheory.LatPairMove
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HomLatticeCompletionMovesByTranslatePairStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.homLatticeCompletion_moves_by_translatePair : ∀ (D : D7) (S T : HSp D) (a b : ℕ) (hS : S.rank = a) (hT : T.rank = b) (g s : GA D S) (h s' : GA D T) N N' N₁ N₁', Moves S hS g N → Moves T hT h N' → Moves S hS (s * g) N₁ → Moves T hT (s' * h) N₁' → ∀ u : WO S T, u ∈ (latO S T (latFr S hS N₁) (latFr T hT N₁') fun _ => True) ↔ ∃ u₀ ∈ (latO S T (latFr S hS N) (latFr T hT N') fun _ => True), u = actO S T s s' u₀ := by
  first | exact @GlobalTheory.LatPairMove.latO_move | exact GlobalTheory.LatPairMove.latO_move | (intros; apply GlobalTheory.LatPairMove.latO_move <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LawsRescaleWithS
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Core.Rk ValuativeRel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw.Resc

variable {D : D7}

theorem heisO_smul (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (w : WO S T) (s : ℂ) (f : WO S T → ℂ) :
    heisO ψ S T w (s • f) = s • heisO ψ S T w f := by
  funext x; simp only [heisO, Pi.smul_apply, smul_eq_mul]; ring

end GlobalTheory.SeeSaw.Resc

namespace GlobalTheory.SeeSaw.Resc

variable {D : D7} {m n : ℕ}

theorem dRho_smul (hs : Mx D m n → (Mx D m n → ℂ) → (Mx D m n → ℂ))
    (hh : ∀ w (s : ℂ) f, hs w (s • f) = s • hs w f) (θ : InfFam D) (τ : D.what₂.Tau)
    (z : Matrix (Fin m) (Fin n) ℂ) (s : ℂ) (f : Mx D m n → ℂ) :
    Datum.dRho hs θ τ z (s • f) = s • Datum.dRho hs θ τ z f := by
  funext x
  simp only [Datum.dRho, hh, Pi.smul_apply, smul_eq_mul]
  exact deriv_const_mul_field _

theorem aPlusAll_smul (hs : Mx D m n → (Mx D m n → ℂ) → (Mx D m n → ℂ))
    (hh : ∀ w (s : ℂ) f, hs w (s • f) = s • hs w f) (θ : InfFam D)
    (J : D.what₂.Tau → Matrix (Fin m) (Fin n) ℂ → Matrix (Fin m) (Fin n) ℂ)
    (B : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) (B' : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ) (k) (s : ℂ) (f : Mx D m n → ℂ) :
    aPlusAll hs θ J B B' k (s • f) = s • aPlusAll hs θ J B B' k f := by
  simp only [aPlusAll, aPlus, crea, dRho_smul hs hh, smul_sub, smul_comm s]

theorem opPow_smul {ι X : Type} (A : ι → (X → ℂ) → (X → ℂ)) (hA : ∀ i (s : ℂ) f, A i (s • f) = s • A i f)
    (k : ι →₀ ℕ) (s : ℂ) (f : X → ℂ) : opPow A k (s • f) = s • opPow A k f := by
  unfold opPow
  induction (Multiset.toList (Finsupp.toMultiset k)) with
  | nil => rfl
  | cons i l ih => simp only [List.foldr_cons, ih, hA]

theorem pureTensorL_smul {ι X : Type} (A : ι → (X → ℂ) → (X → ℂ)) (hA : ∀ i (s : ℂ) f, A i (s • f) = s • A i f)
    (s : ℂ) (f : X → ℂ) : pureTensorL A (s • f) = s • pureTensorL A f := by
  unfold pureTensorL
  have : (fun k : ι →₀ ℕ => opPow A k (s • f)) = s • fun k => opPow A k f := by
    funext k; exact opPow_smul A hA k s f
  rw [this, map_smul]

end GlobalTheory.SeeSaw.Resc

namespace GlobalTheory.SeeSaw.Resc

variable {D : D7}

theorem pureTensorO_smul (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D)
    (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (s : ℂ) (f : WO S T → ℂ) :
    pureTensorO ψ θ S T sS sT BS BT (s • f) = s • pureTensorO ψ θ S T sS sT BS BT f :=
  pureTensorL_smul _ (aPlusAll_smul _ (heisO_smul ψ S T) _ _ _ _) s f

end GlobalTheory.SeeSaw.Resc

namespace GlobalTheory.SeeSaw.Resc

end GlobalTheory.SeeSaw.Resc

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OmegaQEmpty
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto.StepLevLaw

theorem omegaQ_empty {D : D7} {a b : ℕ} (r : ℕ) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (k : ℤ)
    (y : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP)) : omegaQ ∅ r ξ k y = 1 := by
  unfold omegaQ
  rw [dite_eq_left (fun PP hP => absurd hP (Finset.notMem_empty PP))]
  simp


set_option maxHeartbeats 1000000 in
open Classical in
theorem stepLevLaw : ∀ (D : D7) (c : Com D), c.Is → ∀ (k : Fin D.R.m) (s s' : PiLocalization₂ D), s.Is c k → s'.Is c (k + 1) → ∀ ω, IsWeilDatumO c.ψ s.V s'.V (c.chS (k + 1)) (c.chT (k + 1)) ω → ∀ ξ f₀ f, IsStepVecOf c.ψ c.θ s.V s'.V (cart s.M) (cart s'.M) s.Λ s'.Λ s.β s'.β s.L (c.chi (k + 1)) ∅ ξ f₀ f → ∀ κ ∈ levS s.V s.β s.L, κ ∈ GfC s.V ∧ ω (κ, 1) f = Lev.levChi s.V s.β s.L κ • f := by
  intro D c hc k s s' hs hs' ω hW ξ f₀ f hv κ hκ
  refine ⟨hκ.1, ?_⟩
  have hPg : s.L.Pg = c.Pg := by
    obtain ⟨hr, ξ', hL⟩ := hs.lev
    rw [hL]; rfl
  have hQ : s.L.Q = ∅ := by
    obtain ⟨hr, ξ', hL⟩ := hs.lev
    rw [hL]; rfl
  obtain ⟨hf, e, he, hΘ⟩ := hv
  have he' : IsIdemSum e c.Pg := by rw [← hPg, ← Finset.union_empty s.L.Pg]; exact he
  obtain ⟨hres, uS, uT⟩ := GlobalTheory.T.thetaLiftChain_splittingCharacters_residue_unramified D c hc k k.isLt
  have hlev : Lev.finE s.V κ ∈ lev D.sp.cm s.V.gram s.β s.L := hκ.2
  have sg : Lev.finE s.V κ ∈ St s.β := parLev_St hlev.1
  have sh : Lev.finE s'.V 1 ∈ St s'.β := by rw [map_one]; exact Subgroup.one_mem _
  have h1 := GlobalTheory.StepVecLaw.om_vac hW hs.sigOK hs'.sigOK (GlobalTheory.Chain.VacVec.cart_isCartanInv s.M) (GlobalTheory.Chain.VacVec.cart_isCartanInv s'.M)
    hs.selfDual hs'.selfDual hs.frame hs'.frame hf he' (fun PP hP => (hres PP hP).1) (fun PP hP => (hres PP hP).2) uS uT
    hκ.1 (Subgroup.one_mem _) sg sh
  set G : ∀ PP : Pl D.host.E, GL (Fin s.V.rank) (kP PP) := fun PP => redFn s.β PP (Lev.finE s.V κ) with hG
  have h1' : ω (κ, 1) f₀ = ((∏ PP ∈ c.Pg, c.chi (↑k + 1) PP (GeneralLinearGroup.det (G PP)) : ℂˣ) : ℂ) • f₀ := by
    rw [h1]
    congr 2
    refine Finset.prod_congr rfl fun PP _ => ?_
    simp only [map_one, redFn_one, MonoidHom.inv_apply, inv_inv, mul_one, hG]
  have hoG := GlobalTheory.T.levelPlacesDatum_mul_right_source_level D s.V.rank s'.V.rank s.L (c.chi (↑k + 1)) G (fun PP hP => parLev_g hlev.1 hP) hlev.2
  have h2 := GlobalTheory.T.weilRep_theta_datum_half_eq_smul D c.ψ s.V s'.V _ _ ω hW e _ f₀ _ f
    (GlobalTheory.T.schrodingerIntertwiner_schwartzBruhat_isTheta D c.ψ hW.std s.V s'.V s.Λ s'.Λ hs.selfDual hs'.selfDual e (GlobalTheory.PlaceDatum.idemSum_mul_self he)
      (GlobalTheory.PlaceDatum.infPart_idemSum he) f₀ hf.2.theta) hΘ κ 1
    (GlobalTheory.T.mem_homLattice_iff_frameStabilizer_act_mem D s.V s'.V s.Λ s'.Λ s.β s'.β hs.selfDual hs'.selfDual hs.frame hs'.frame κ 1 sg sh) _
    ((s.L.P.chi ⟨_, hlev.2⟩ * (∏ PP ∈ s.L.Pg, ∏ i ∈ Finset.range s.L.s, s.L.cg (i + 1) PP (dBlk (blkOf s.L.r s.L.t) (i + 1) (G PP))) *
      ∏ PP ∈ s.L.Pg, (c.chi (↑k + 1) PP (GeneralLinearGroup.det (G PP)))⁻¹ : ℂˣ) : ℂ) (Units.ne_zero _) h1' (fun x => by
      obtain ⟨i1, i2⟩ := GlobalTheory.T.frameMatrix_movedHom_integral_reductions D s.V s'.V s.β s'.β κ 1 sg sh x
      have i0 : IsHalf e (actO s.V s'.V κ⁻¹ 1⁻¹ x) ↔ IsHalf e x :=
        ⟨fun H => GlobalTheory.AdelicLatMove.actO_actO_inv s.V s'.V κ 1 x ▸ GlobalTheory.SplitHecke.isHalf_actO κ 1 H,
          fun H => GlobalTheory.SplitHecke.isHalf_actO _ _ H⟩
      by_cases hx : IsHalf e x ∧ IsIntM (frMapO s.V s'.V s.β s'.β x)
      · beta_reduce
        rw [if_pos hx, if_pos ⟨i0.2 hx.1, i1.2 hx.2⟩, funext (i2 hx.2), omegaQ_empty, omegaQ_empty, mul_one, mul_one]
        simp only [map_one, redFn_one, inv_one, Units.val_one, Matrix.one_mul]
        exact hoG (fun PP => redM PP (frMapO s.V s'.V s.β s'.β x))
      · beta_reduce
        rw [if_neg hx, if_neg fun H => hx ⟨i0.1 H.1, i1.1 H.2⟩, mul_zero])
  rw [h2]
  congr 1
  unfold Lev.levChi levFn
  rw [hQ, Finset.prod_empty, mul_one, extendOne_of_mem _ hlev.2, ← Units.val_mul, ← hPg, Finset.prod_inv_distrib]
  congr 1
  rw [mul_comm, mul_assoc, inv_mul_cancel, mul_one]

end GlobalTheory.ChainOnto.StepLevLaw

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleStepIntegrandRightInvariantSecondFixedLeve
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleStepIntegrandRightInvariantSecondFixedLeve
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DStepCell

namespace GlobalTheory.DStepLev

theorem comm_inf_fin {D : D7} (V : HSp D) {a b : GA D V} (ha : a ∈ GinfC V) (hb : b ∈ GfC V) : a * b = b * a := by
  have ha' : finHom V a = 1 := ha
  have hb' : infHom V b = 1 := hb
  have h := GlobalTheory.LevelCut.eq_one_of_parts V (a * b * (b * a)⁻¹)
    (show infHom V _ = 1 by simp [hb']) (show finHom V _ = 1 by simp [ha'])
  exact mul_inv_eq_one.mp h

theorem per_hand_mul {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {σ : ℕ} {B : BesLev D (σ + 1)} {J : JacLev D (σ + 1)}
    {B' : BesLev D σ} (s₁ : StepBF ψ B J) (s₂ : StepFB ψ J B') (l : Link B B'.L B'.ζ) (vL : VolM D B'.L.rank J.W₀.rank)
    (Φ₁ : WO B.V J.W → ℂ) (Φ₂ : WO J.W B'.V → ℂ) (φ : GA D B.A → ℂ) (g : GA D B.V) (q₁ : GA D J.W) (q₂ k : GA D B'.V)
    (s : ℂ) (hs : s ≠ 0) (hom : s₂.om (1, k) Φ₂ = s⁻¹ • Φ₂) (f f' : GA D B'.V → ℂ) (hf : f' = s • f) :
    B'.per ψ (Chain.hand s₁ s₂ l vL Φ₁ Φ₂ φ g q₁ (q₂ * k)) f' = B'.per ψ (Chain.hand s₁ s₂ l vL Φ₁ Φ₂ φ g q₁ q₂) f := by
  have e : ((q₁, q₂ * k) : GA D J.W × GA D B'.V) = (q₁, q₂) * (1, k) := by simp
  have hh := GlobalTheory.HandHom.handFB_smul s₂ vL 1 s⁻¹
  simp only [one_smul, star_one, one_mul] at hh
  unfold Chain.hand
  rw [hf, e, map_mul, Module.End.mul_apply, hom, LinearMap.map_smul, GlobalTheory.HandHom.flatFB_smul, hh, GlobalTheory.HandHom.per_smul,
    inv_mul_cancel₀ hs, one_mul]

theorem rTrans_eigen {G : Type} [Group G] (a b k q : G) (F : G → ℂ) (s : ℂ) (hcm : a * k = k * a)
    (h : rTrans k (rTrans b F) = s • rTrans b F) :
    rTrans (q * k) (rTrans (a * b) F) = s • rTrans q (rTrans (a * b) F) := by
  funext g
  have := congrFun h (g * q * a)
  simp only [rTrans, Pi.smul_apply] at this ⊢
  rw [show g * (q * k) * (a * b) = g * q * a * k * b by
    rw [mul_assoc (g * q) a k, hcm]; simp only [mul_assoc], this]
  simp only [mul_assoc]

theorem vac_comb {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (S T : HSp D) (LS : Lat S) (LT : Lat T)
    (hS : IsSelfDualC S LS) (hT : IsSelfDualC T LT) (P Q : Pl D → Prop) (hPQ : ∀ p, Q p → ¬ P p) (e : WO S T →₀ ℂ)
    (he : CombAt Q e) (f : WO S T → ℂ) (hf : Vac ψ S T LS LT (fun _ => True) f) : Vac ψ S T LS LT P (comb ψ S T e f) := by
  have h0 : Vac ψ S T LS LT P f := by
    have e : (fun p : Pl D => P p ∨ ¬ P p) = fun _ => True := by
      funext p; exact propext ⟨fun _ => trivial, fun _ => em _⟩
    refine (((GlobalTheory.DisjComb.main D ψ hψ S T P (fun p => ¬ P p) (fun p hp hq => hq hp)).2.2.2.2 LS LT f hS hT).1 ?_).1
    rw [e]; exact hf
  exact ((GlobalTheory.DisjComb.main D ψ hψ S T Q P hPQ).2.1 e he).2 _ _ _ h0


set_option maxHeartbeats 1000000 in
theorem integ_mul_level : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t), c.Is → v.Is → t.Is → VForm v w → WeilOK (t := t) v → OffLaw v w → GSupp (t := t) v → QFin v w → ContrLaw D → FlatLaw D → ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m) Ψ₁ Ψ₂, Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (fun _ => True) Ψ₁ → Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (fun _ => True) Ψ₂ → ∀ φ : t.Ch j → GA D (c.X j) → ℂ, (∀ α, φ α ∈ v.RamAd j) → ∀ (G : t.CC (j + 1 + 1)) x, ∀ a ∈ GinfC _, ∀ f, f = rTrans (a * v.b (j + 1 + 1)) (G.1 x) → ∀ k ∈ v.JG (j + 1 + 1), ∀ q₁ q₂, integ v w j σ h Ψ₁ Ψ₂ φ f q₁ (q₂ * k) = integ v w j σ h Ψ₁ Ψ₂ φ f q₁ q₂ := by
  intro D c v t w hc hv ht hF _ _ _ _ _ _ j σ h Ψ₁ Ψ₂ _ hΨ₂ φ _ G x a ha f hf k hk q₁ q₂
  have hlt : j + 1 + 1 < D.R.m := by omega
  obtain ⟨s, hs, h1, -, h3⟩ := hF.lawG (j + 1) hlt k hk
  have hom := h1 _ (vac_comb c.ψ hc.std _ _ _ _ (hv.sd (j + 1) (by omega)) (hv.sd (j + 1 + 1) hlt) (· ∈ v.gP) (· ∈ w.Q)
    (fun p hp => Finset.disjoint_left.1 hF.disjG hp) _ (hF.atQ (j + 1)).1 Ψ₂ hΨ₂)
  have hkf : k ∈ GfC _ := GlobalTheory.LevelCut.mem_GfC_of_grpAt _ _ k ((hv.JG _ hlt).1 hk)
  have hr : rTrans (q₂ * k) f = s • rTrans q₂ f := by
    rw [hf]; exact rTrans_eigen a _ k q₂ _ s (comm_inf_fin _ ha hkf) (h3 G x)
  rw [← (ht.sFB j σ h).1] at hom
  unfold integ
  refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun g _ => ?_
  exact congrArg (w.ε j α g * ·) (per_hand_mul (t.sBF j (σ + 1) h) (t.sFB j σ h) (c.lnk j σ h) (c.vL j σ h) _ _ (φ α) g q₁ q₂ k
    s hs hom _ _ hr)

end GlobalTheory.DStepLev
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleStepIntegrandRightInvariantSecondFixedLeveStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DStepCell
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubleStepIntegrand_rightInvariant_second_fixedLevel : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t), c.Is → v.Is → t.Is → VForm v w → WeilOK (t := t) v → OffLaw v w → GSupp (t := t) v → QFin v w → ContrLaw D → FlatLaw D → ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m) Ψ₁ Ψ₂, Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (fun _ => True) Ψ₁ → Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (fun _ => True) Ψ₂ → ∀ φ : t.Ch j → GA D (c.X j) → ℂ, (∀ α, φ α ∈ v.RamAd j) → ∀ (G : t.CC (j + 1 + 1)) x, ∀ a ∈ GinfC _, ∀ f, f = rTrans (a * v.b (j + 1 + 1)) (G.1 x) → ∀ k ∈ v.JG (j + 1 + 1), ∀ q₁ q₂, integ v w j σ h Ψ₁ Ψ₂ φ f q₁ (q₂ * k) = integ v w j σ h Ψ₁ Ψ₂ φ f q₁ q₂ := by
  first | exact @GlobalTheory.DStepLev.integ_mul_level | exact GlobalTheory.DStepLev.integ_mul_level | (intros; apply GlobalTheory.DStepLev.integ_mul_level <;> assumption)
end
end
