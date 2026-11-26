module

public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.SegmentDerivatives.DerivJac
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductTransposeInverseDualReverse
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.CProps
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DiagTMemIwGL
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairInvolutionContinuous
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DeltaEqLatticeIndex
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianMatrixDiagonalizable
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SwMeasPlaneOfNotRepresented

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JmThetaHolds
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JmThetaHolds
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos GlobalTheory.CompanionTheory.ThetaProd
open scoped Matrix

namespace GlobalTheory.CompanionTheory.JmThetaInv

section Ring

variable {A : Type} [CommRing A]

theorem thetaL_eq_one {h : ℕ} (d : Fin h → ℕ) {x : Levi A (fun a => Fin (d a))} (hx : thetaL d x = 1) : x = 1 := by
  funext b
  obtain ⟨c, rfl⟩ := Fin.rev_surjective b
  have h1 : thetaW A (d (Fin.rev c)) (x (Fin.rev c)) = 1 := congrFun hx c
  have h2 := GlobalTheory.CompanionTheory.ThetaInv.thetaW_thetaW_ring _ (x (Fin.rev c))
  rw [h1, map_one] at h2
  exact h2.symm

theorem thetaL_surjective {h : ℕ} (d : Fin h → ℕ) : Function.Surjective (thetaL (A := A) d) := by
  intro y
  refine ⟨fun b => thetaW A (d b) (cast (by show GL (Fin (d (Fin.rev (Fin.rev b)))) A = _; rw [Fin.rev_rev]) (y (Fin.rev b))), ?_⟩
  funext a
  show thetaW A (d (Fin.rev a)) (thetaW A (d (Fin.rev a)) (cast _ (y (Fin.rev (Fin.rev a))))) = y a
  rw [GlobalTheory.CompanionTheory.ThetaInv.thetaW_thetaW_ring]
  have : ∀ (c : Fin h) (hc : c = a) (hh : GL (Fin (d (Fin.rev c))) A = GL (Fin (d (Fin.rev a))) A),
      cast hh (y c) = y a := by
    rintro c rfl hh
    rfl
  exact this _ (Fin.rev_rev a) _

theorem thetaW_mem_unipRad_iff {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) (hd' : ∑ a, d (Fin.rev a) = N)
    (g : GL (Fin N) A) :
    thetaW A N g ∈ unipRad A (stdBlocks (fun a => d (Fin.rev a)) hd') ↔ g ∈ unipRad A (stdBlocks d hd) := by
  constructor
  · intro H
    have hp : g ∈ parab A (stdBlocks d hd) :=
      (thetaW_mem_parab_iff d hd hd' g).1 (unipRad_le_parab A _ H)
    refine (coe_mem_unipRad A (⟨g, hp⟩ : parab A (stdBlocks d hd))).2 (thetaL_eq_one d ?_)
    rw [← leviProj_thetaW d hd hd' ⟨g, hp⟩]
    exact (coe_mem_unipRad A _).1 H
  · intro H
    have hp : g ∈ parab A (stdBlocks d hd) := unipRad_le_parab A _ H
    have h1 : leviProj A (stdBlocks d hd) ⟨g, hp⟩ = 1 := (coe_mem_unipRad A _).1 H
    refine (coe_mem_unipRad A (⟨thetaW A N g, (thetaW_mem_parab_iff d hd hd' g).2 hp⟩ :
      parab A (stdBlocks (fun a => d (Fin.rev a)) hd'))).2 ?_
    rw [leviProj_thetaW d hd hd' ⟨g, hp⟩, h1, map_one]

theorem thetaW_leviEmb {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) (hd' : ∑ a, d (Fin.rev a) = N)
    (g : Levi A (fun a => Fin (d a))) :
    thetaW A N (leviEmb A (stdBlocks d hd) g) =
      leviEmb A (stdBlocks (fun a => d (Fin.rev a)) hd') (thetaL d g) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  obtain ⟨⟨a, i⟩, rfl⟩ := (stdBlocks (fun a => d (Fin.rev a)) hd').surjective i
  obtain ⟨⟨b, j⟩, rfl⟩ := (stdBlocks (fun a => d (Fin.rev a)) hd').surjective j
  rw [GlobalTheory.CompanionTheory.ThetaInv.thetaW_val_apply, rev_stdBlocks d hd hd', rev_stdBlocks d hd hd', ← map_inv]
  by_cases hab : a = b
  · subst hab
    rw [leviEmb_apply_same, leviEmb_apply_same]
    show _ = (thetaW A (d (Fin.rev a)) (g (Fin.rev a))).1 i j
    rw [GlobalTheory.CompanionTheory.ThetaInv.thetaW_val_apply]
    rfl
  · rw [leviEmb_apply_ne A _ _ (fun hh => hab (Fin.rev_injective hh).symm), leviEmb_apply_ne A _ _ hab]

end Ring

section Jacquet

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {V : Type} [AddCommGroup V] [Module ℂ V]

theorem twKer_comp_thetaW {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) (hd' : ∑ a, d (Fin.rev a) = N)
    (π : Representation ℂ (GL (Fin N) k) V) :
    twKer (π.comp (thetaW k N)) (unipRad k (stdBlocks d hd)) 1 =
      twKer π (unipRad k (stdBlocks (fun a => d (Fin.rev a)) hd')) 1 := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨u, v, rfl⟩
    exact Submodule.subset_span ⟨⟨thetaW k N u, (thetaW_mem_unipRad_iff d hd hd' _).2 u.2⟩, v, rfl⟩
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨u, v, rfl⟩
    have hu : thetaW k N (u : GL (Fin N) k) ∈ unipRad k (stdBlocks d hd) :=
      (thetaW_mem_unipRad_iff d hd hd' _).1 (by rw [GlobalTheory.CompanionTheory.ThetaInv.thetaW_thetaW]; exact u.2)
    refine Submodule.subset_span ⟨⟨_, hu⟩, v, ?_⟩
    simp [GlobalTheory.CompanionTheory.ThetaInv.thetaW_thetaW]

def jacCompThetaW {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) (hd' : ∑ a, d (Fin.rev a) = N)
    (π : Representation ℂ (GL (Fin N) k) V) :
    (GlobalTheory.SmGL.jac (stdBlocks d hd) (π.comp (thetaW k N))).Equiv
      ((GlobalTheory.SmGL.jac (stdBlocks (fun a => d (Fin.rev a)) hd') π).comp (thetaL d)) :=
  .mk (Submodule.quotEquivOfEq _ _ (twKer_comp_thetaW d hd hd' π)) fun g => by
    refine LinearMap.ext fun v => ?_
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ v
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, MonoidHom.comp_apply]
    rw [Submodule.quotEquivOfEq_mk, jac_mk, jac_mk, map_smul, Submodule.quotEquivOfEq_mk, deltaHalf_thetaL]
    simp only [MonoidHom.comp_apply, thetaW_leviEmb d hd hd' g]

theorem jm_comp_theta_eq_dual_reverse (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hGK : GKLocal k) {h N : ℕ}
    (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N) (π : Representation ℂ (GL (Fin N) k) V) :
    jm x hd (π.comp (thetaW k N)) = jm (dualRev hA x) (sum_dualRev hA x hd) π := by
  have hd' : ∑ a, (x (Fin.rev a)).1 = N := sum_dualRev hA x hd
  have T1 := piTensorRevEquiv (fun a => (x a).rep)
  have T2 := compEquiv (piTensorEquiv fun a => blockEquiv hA hGK x a) (revPi fun a => GL (Fin (x a).1) k)
  have T3 := equivOfEq (piTensor_comp_thetaL (k := k) (fun a => (x a).1) fun a => (dualRev hA x a).rep)
  have T := (T1.trans T2).trans T3
  unfold jm
  rw [jhMult_congr_right _ (jacCompThetaW (fun a => (x a).1) hd hd' π), jhMult_congr_left T]
  exact GlobalTheory.SmGL.EmptyBlocks.jhMult_comp_surjective (thetaL fun a => (x a).1) (thetaL_surjective _) _ _

theorem jm_comp_thetaW (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hGK : GKLocal k) {h N : ℕ}
    (x y : Fin h → IrrGL (k := k)) (hy : y = fun a => dualCl (x (Fin.rev a))) (hd : ∑ a, (x a).1 = N)
    (hd' : ∑ a, (y a).1 = N) (π : Representation ℂ (GL (Fin N) k) V) :
    jm x hd (π.comp (thetaW k N)) = jm y hd' π := by
  rw [← dualRev_eq hA x] at hy
  subst hy
  exact jm_comp_theta_eq_dual_reverse hA hGK x hd π

end Jacquet

theorem jmTheta : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    GlobalTheory.Published.IrreducibleAdmissibleGL → GlobalTheory.BZSeg.JmTheta k := by
  intro k _ _ _ _ hA N V _ _ π _ _ a b hd hd'
  refine jm_comp_thetaW hA (GlobalTheory.CompanionTheory.GKLocalProof.gkLocal hA) _ _ ?_ hd hd' π
  funext i
  fin_cases i <;> rfl

end GlobalTheory.CompanionTheory.JmThetaInv

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JmThetaHoldsStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jm_theta_holds : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → GlobalTheory.BZSeg.JmTheta k := by
  first | exact @GlobalTheory.CompanionTheory.JmThetaInv.jmTheta | exact GlobalTheory.CompanionTheory.JmThetaInv.jmTheta | (intros; apply GlobalTheory.CompanionTheory.JmThetaInv.jmTheta <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelCharactersUnramified
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelCharactersUnramified
noncomputable section

namespace GlobalTheory.CompanionTheory.GunrLevChars

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain PositivityTheory.PfSWUS.Loc PositivityTheory.SiegelWeilFormula.Gunr
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {M n d : ℕ} {J : Matrix (Fin M) (Fin M) E} {T : Matrix (Fin n) (Fin n) E}
  {bs : Module.Basis (Fin d) F E} {v : HeightOneSpectrum (𝓞 F)} {ψv : Fv F v → ℂ}
  {S : Subring (Fv F v ⊗[F] E)} {σS : S →+* S} {ϖ : Fv F v} {ε : ℤ}

theorem sigR_algebraMap (c : Fv F v) :
    sigR (Fv F v) σ (algebraMap (Fv F v) (Fv F v ⊗[F] E) c) = algebraMap (Fv F v) (Fv F v ⊗[F] E) c := by
  rw [Algebra.algebraMap_eq_smul_one, sigR_smul, map_one]

theorem smul_mem (hG : GoodLoc σ J T bs v ψv S σS ϖ ε) {β : Fv F v} (hβ : β ∈ v.adicCompletionIntegers F)
    {x : Fv F v ⊗[F] E} (hx : x ∈ S) : β • x ∈ S := by
  have h1 : x ∈ Rv bs v := by
    rw [← hG.carrier]
    exact hx
  have h2 : β • x ∈ Rv bs v := fun k => by
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
    exact mul_mem hβ (h1 k)
  rw [← hG.carrier] at h2
  exact h2

theorem fixed_eq (hG : GoodLoc σ J T bs v ψv S σS ϖ ε) (a : S) (ha : σS a = a) :
    ∃ α : Fv F v, (a : Fv F v ⊗[F] E) = algebraMap (Fv F v) (Fv F v ⊗[F] E) α :=
  hG.fixed a (by rw [← hG.sig, ha])

theorem basis_mem (hG : GoodLoc σ J T bs v ψv S σS ϖ ε) (i : Fin d) :
    Algebra.TensorProduct.basis (Fv F v) bs i ∈ S := by
  have h : Algebra.TensorProduct.basis (Fv F v) bs i ∈ Rv bs v := fun k => by
    rw [Module.Basis.repr_self, Finsupp.single_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  rw [← hG.carrier] at h
  exact h

theorem nontrivial_S (hG : GoodLoc σ J T bs v ψv S σS ϖ ε) : Nontrivial S := by
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  exact hG.quad.notUnit (isUnit_of_subsingleton _)

theorem card_eq_two (hG : GoodLoc σ J T bs v ψv S σS ϖ ε) : d = 2 := by
  obtain ⟨u, hu, hb⟩ := hG.quad.basis
  have : Nontrivial S := nontrivial_S hG
  have : Nontrivial (Fv F v ⊗[F] E) := (Subtype.val_injective (p := fun x => x ∈ S)).nontrivial
  have hinj := (algebraMap (Fv F v) (Fv F v ⊗[F] E)).injective
  have hli : LinearIndependent (Fv F v) ![(1 : Fv F v ⊗[F] E), (u : Fv F v ⊗[F] E)] := by
    rw [LinearIndependent.pair_iff]
    intro s t h
    have ht : t = 0 := by
      by_contra ht
      have e : (u : Fv F v ⊗[F] E) = algebraMap (Fv F v) (Fv F v ⊗[F] E) (-(t⁻¹ * s)) := by
        have h3 : t • (u : Fv F v ⊗[F] E) = -(s • (1 : Fv F v ⊗[F] E)) := eq_neg_of_add_eq_zero_right h
        have h4 : (u : Fv F v ⊗[F] E) = t⁻¹ • (t • (u : Fv F v ⊗[F] E)) := by
          rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
        rw [h4, h3, Algebra.algebraMap_eq_smul_one, smul_neg, neg_smul, smul_smul]
      have hfix : σS u = u := Subtype.ext (by rw [hG.sig, e, sigR_algebraMap])
      rw [hfix, sub_self, isUnit_zero_iff] at hu
      exact zero_ne_one hu
    subst ht
    refine ⟨?_, rfl⟩
    rw [zero_smul, add_zero, ← Algebra.algebraMap_eq_smul_one] at h
    exact hinj (by rw [h, map_zero])
  have hsp : ⊤ ≤ Submodule.span (Fv F v) (Set.range ![(1 : Fv F v ⊗[F] E), (u : Fv F v ⊗[F] E)]) := by
    rw [← (Algebra.TensorProduct.basis (Fv F v) bs).span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    obtain ⟨x, y, hx, hy, e⟩ := hb ⟨_, basis_mem hG i⟩
    obtain ⟨α, hα⟩ := fixed_eq hG x hx
    obtain ⟨β, hβ⟩ := fixed_eq hG y hy
    have e2 : Algebra.TensorProduct.basis (Fv F v) bs i =
        α • (1 : Fv F v ⊗[F] E) + β • (u : Fv F v ⊗[F] E) := by
      have e3 := congrArg Subtype.val e
      simp only [Subring.coe_add, Subring.coe_mul] at e3
      rw [e3, hα, hβ, Algebra.smul_def, Algebra.smul_def, mul_one]
    rw [SetLike.mem_coe, e2]
    exact add_mem (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))
  have h1 := Module.finrank_eq_card_basis (Module.Basis.mk hli hsp)
  have h2 := Module.finrank_eq_card_basis (Algebra.TensorProduct.basis (Fv F v) bs)
  simpa using h2.symm.trans h1

theorem trace_algebraMap_eq (hG : GoodLoc σ J T bs v ψv S σS ϖ ε) (x : Fv F v) :
    Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (algebraMap (Fv F v) (Fv F v ⊗[F] E) x) = 2 * x := by
  rw [Algebra.trace_algebraMap_of_basis (Algebra.TensorProduct.basis (Fv F v) bs), Fintype.card_fin,
    card_eq_two hG, two_nsmul, two_mul]

theorem psiF_compat (hG : GoodLoc σ J T bs v ψv S σS ϖ ε) (c : Fv F v) (k : ℕ) (a : Fv F v ⊗[F] E) :
    psiF ψv ϖ c (k + 1) (algebraMap (Fv F v) (Fv F v ⊗[F] E) ϖ * a) = psiF ψv ϖ c k a := by
  unfold psiF
  rw [← Algebra.smul_def, map_smul, smul_eq_mul, ← mul_assoc ((ϖ ^ (k + 1))⁻¹), pow_succ, mul_inv,
    mul_assoc (ϖ ^ k)⁻¹, inv_mul_cancel₀ hG.unif_ne, mul_one]

theorem mem_level_of_character_trivial (hG : GoodLoc σ J T bs v ψv S σS ϖ ε) {c : Fv F v} (hc : c ∈ v.adicCompletionIntegers F)
    (hc1 : ‖c‖ = 1) (a : S) (ha : σS a = a)
    (hb : ∀ b, σS b = b → hG.psiLev hc 1 (Ideal.Quotient.mk _ (a * b)) = 1) : a ∈ lev hG.pS 1 := by
  have h20 : (2 : Fv F v) ≠ 0 := by
    intro h
    have := hG.two
    rw [h, norm_zero] at this
    exact zero_ne_one this
  obtain ⟨α, hα⟩ := fixed_eq hG a ha
  have hαO : α ∈ v.adicCompletionIntegers F := by
    have h2 := hG.trace_mem a.2
    rw [hα, trace_algebraMap_eq hG] at h2
    have h3 := mul_mem hG.half_mem h2
    rwa [← mul_assoc, inv_mul_cancel₀ h20, one_mul] at h3
  have hkey : c * (ϖ⁻¹ * α) ∈ v.adicCompletionIntegers F := by
    refine (hG.psi_cond _).1 fun β hβ => ?_
    have hbS : algebraMap (Fv F v) (Fv F v ⊗[F] E) β ∈ S := by
      have h1 := smul_mem hG hβ (one_mem S)
      rwa [← Algebra.algebraMap_eq_smul_one] at h1
    have hfix : σS ⟨_, hbS⟩ = ⟨_, hbS⟩ := Subtype.ext (by rw [hG.sig]; exact sigR_algebraMap β)
    have h1 := hb _ hfix
    rw [hG.psiLev_mk] at h1
    have e : ((a * ⟨_, hbS⟩ : S) : Fv F v ⊗[F] E) = algebraMap (Fv F v) (Fv F v ⊗[F] E) (α * β) := by
      rw [Subring.coe_mul, hα, map_mul]
    rw [e] at h1
    unfold psiF at h1
    rw [trace_algebraMap_eq hG] at h1
    rw [← h1]
    congr 1
    have := hG.unif_ne
    field_simp
  have hγ : ϖ⁻¹ * α ∈ v.adicCompletionIntegers F := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, ← Valued.toNormedField.norm_le_one_iff] at hkey ⊢
    rw [norm_mul, hc1, one_mul] at hkey
    exact hkey
  have hgS : algebraMap (Fv F v) (Fv F v ⊗[F] E) (ϖ⁻¹ * α) ∈ S := by
    have h1 := smul_mem hG hγ (one_mem S)
    rwa [← Algebra.algebraMap_eq_smul_one] at h1
  refine Ideal.mem_span_singleton'.2 ⟨⟨_, hgS⟩, Subtype.ext ?_⟩
  rw [pow_one, Subring.coe_mul, hα]
  show algebraMap (Fv F v) (Fv F v ⊗[F] E) (ϖ⁻¹ * α) * algebraMap (Fv F v) (Fv F v ⊗[F] E) ϖ = _
  rw [← map_mul]
  congr 1
  have := hG.unif_ne
  field_simp

theorem levChars : PositivityTheory.SiegelWeilFormula.Gunr.LevChars := by
  intro F E _ _ _ _ _ σ M n d J T bs v ψv S σS ϖ ε hG c hc hc1
  refine ⟨fun k a => ?_, fun a ha hb => mem_level_of_character_trivial hG hc hc1 a ha hb⟩
  rw [GoodLoc.psiLev_mk, GoodLoc.psiLev_mk]
  exact psiF_compat hG c k a

end GlobalTheory.CompanionTheory.GunrLevChars

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelCharactersUnramifiedStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_characters_unramified : PositivityTheory.SiegelWeilFormula.Gunr.LevChars := by
  first | exact @GlobalTheory.CompanionTheory.GunrLevChars.levChars | exact GlobalTheory.CompanionTheory.GunrLevChars.levChars | (intros; apply GlobalTheory.CompanionTheory.GunrLevChars.levChars <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DominantCosetTwistedConjugacy
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DiagRigid
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.DiagRigid

theorem diag_rigid : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (n : ℕ) (y : Fin n → ℤ), Function.Injective y → ∀ (d d' : Fin n → Lˣ), (∀ i, ordL (d i : L) = y i) → (∀ i, ordL (d' i : L) = y i) → ∀ h : GL (Fin n) L, h⁻¹ * GlobalTheory.SmGL.diagT L (Fin n) d * h = GlobalTheory.SmGL.diagT L (Fin n) d' → d = d' ∧ ∃ s : Fin n → Lˣ, h = GlobalTheory.SmGL.diagT L (Fin n) s := by
  intro L _ _ n y hy d d' hd hd' h hh
  have key : GlobalTheory.SmGL.diagT L (Fin n) d * h = h * GlobalTheory.SmGL.diagT L (Fin n) d' := by
    rw [← hh]; simp only [mul_assoc, mul_inv_cancel_left]
  have key' : (Matrix.diagonal fun i => (d i : L)) * (h : Matrix (Fin n) (Fin n) L)
      = (h : Matrix (Fin n) (Fin n) L) * Matrix.diagonal fun i => (d' i : L) := by
    have := congrArg (fun g : GL (Fin n) L => (g : Matrix (Fin n) (Fin n) L)) key
    simpa only [Units.val_mul, GlobalTheory.SmGL.val_diagT] using this
  have ent : ∀ i j, (d i : L) * (h : Matrix (Fin n) (Fin n) L) i j
      = (h : Matrix (Fin n) (Fin n) L) i j * (d' j : L) := by
    intro i j
    have := congrFun (congrFun key' i) j
    rwa [Matrix.diagonal_mul, Matrix.mul_diagonal] at this
  have off : ∀ i j, i ≠ j → (h : Matrix (Fin n) (Fin n) L) i j = 0 := by
    intro i j hij
    by_contra hne
    have e : (d i : L) = (d' j : L) := by
      have := ent i j
      rw [mul_comm] at this
      exact mul_left_cancel₀ hne this
    apply hij
    apply hy
    rw [← hd i, ← hd' j, e]
  have hdiag : (h : Matrix (Fin n) (Fin n) L)
      = Matrix.diagonal fun i => (h : Matrix (Fin n) (Fin n) L) i i := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp
    · rw [Matrix.diagonal_apply_ne _ hij]; exact off i j hij
  have hdet : ∏ i, (h : Matrix (Fin n) (Fin n) L) i i ≠ 0 := by
    have h1 : IsUnit (h : Matrix (Fin n) (Fin n) L).det :=
      (Matrix.isUnit_iff_isUnit_det _).1 h.isUnit
    rw [hdiag, Matrix.det_diagonal] at h1
    simpa [Matrix.diagonal_apply_eq] using h1.ne_zero
  have hii : ∀ i, (h : Matrix (Fin n) (Fin n) L) i i ≠ 0 := fun i =>
    (Finset.prod_ne_zero_iff.1 hdet) i (Finset.mem_univ i)
  refine ⟨?_, fun i => Units.mk0 _ (hii i), ?_⟩
  · funext i
    apply Units.ext
    have := ent i i
    rw [mul_comm] at this
    exact mul_left_cancel₀ (hii i) this
  · apply Units.ext
    rw [GlobalTheory.SmGL.val_diagT]
    simpa using hdiag

end GlobalTheory.CompanionTheory.DiagRigid
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CptPartEqInf
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.CptGen

theorem cptPart_eq_inf : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] (T C : Subgroup G), IsCompact (C : Set G) → (∀ t ∈ T, IsCompact (closure (Subgroup.zpowers t : Set G)) → t ∈ C) → cptPart T = T ⊓ C := by
  intro G _ _ _ _ T C hC h
  apply le_antisymm
  · refine (Subgroup.closure_le _).2 ?_
    intro x hx
    exact ⟨hx.1, h x hx.1 hx.2⟩
  · intro x hx
    apply Subgroup.subset_closure
    refine ⟨hx.1, hC.of_isClosed_subset isClosed_closure ?_⟩
    exact closure_minimal (fun y hy => (Subgroup.zpowers_le.2 hx.2) hy) hC.isClosed

end GlobalTheory.CompanionTheory.CptGen
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DominantCosetTwistedConjugacy
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.SuppCent

theorem comm_of_conj {G : Type} [Group G] (γ p₀ q : G)
    (h : q⁻¹ * (p₀⁻¹ * γ * p₀) * q = p₀⁻¹ * γ * p₀) :
    (p₀ * q * p₀⁻¹) * γ = γ * (p₀ * q * p₀⁻¹) := by
  calc (p₀ * q * p₀⁻¹) * γ = p₀ * q * (p₀⁻¹ * γ * p₀) * p₀⁻¹ := by group
    _ = p₀ * q * (q⁻¹ * (p₀⁻¹ * γ * p₀) * q) * p₀⁻¹ := by rw [h]
    _ = γ * (p₀ * q * p₀⁻¹) := by group

theorem conj_comm {G : Type} [Group G] (γ p₀ t : G) (h : t * γ = γ * t) :
    (p₀⁻¹ * t * p₀)⁻¹ * (p₀⁻¹ * γ * p₀) * (p₀⁻¹ * t * p₀) = p₀⁻¹ * γ * p₀ := by
  calc _ = p₀⁻¹ * t⁻¹ * (γ * t) * p₀ := by group
    _ = p₀⁻¹ * t⁻¹ * (t * γ) * p₀ := by rw [h]
    _ = _ := by group

theorem isCompact_closure_zpowers_conj {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] (c t : G)
    (h : IsCompact (closure (Subgroup.zpowers t : Set G))) :
    IsCompact (closure (Subgroup.zpowers (c⁻¹ * t * c) : Set G)) := by
  have hφ : Continuous fun x : G => c⁻¹ * x * c := by fun_prop
  have hK := h.image hφ
  refine hK.of_isClosed_subset isClosed_closure (closure_minimal ?_ hK.isClosed)
  rintro _ ⟨k, rfl⟩
  refine ⟨t ^ k, subset_closure (Subgroup.zpow_mem_zpowers t k), ?_⟩
  have e : c⁻¹ * t * c = MulAut.conj c⁻¹ t := by simp [MulAut.conj_apply]
  have e' : ∀ x : G, c⁻¹ * x * c = MulAut.conj c⁻¹ x := fun x => by simp [MulAut.conj_apply]
  simp only [e', map_zpow]

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (n : ℕ) (b : GLw n w), IsWitt n w b → ∀ (ϖ : (w.adicCompletion E)ˣ), IsUnifAt ϖ → ∀ (l : Fin (n / 2) → ℤ), Cone l → (∀ (y : Fin n → ℤ), StrictAnti y → ∀ δ : GLw n w, dcos n w (tdiag ϖ y) δ ≠ 0 → ∃ m ∈ iwGL n w, ∃ τ : GLw n w, ((∀ i j : Fin n, i ≠ j → τ.val i j = 0) ∧ ∀ i, Valued.v (τ.val i i) = 1) ∧ m⁻¹ * δ * m = tdiag ϖ y * τ) → ∀ γ : UL n w, (∃ p : UL n w, fU n w b ϖ l (p⁻¹ * γ * p) ≠ 0) → ∃ (p₀ : UL n w) (u : Fin n → (w.adicCompletion E)ˣ), (∀ i, ordL (u i : w.adicCompletion E) = wexp n l i) ∧ (p₀⁻¹ * γ * p₀).1 = b * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) u * b⁻¹ ∧ (∀ p : UL n w, fU n w b ϖ l (p⁻¹ * γ * p) ≠ 0 ↔ ∃ z ∈ twCent (MonoidHom.id (UL n w)) γ, ∃ i ∈ iwU n w b, p = z * p₀ * i) ∧ cptPart (twCent (MonoidHom.id (UL n w)) γ) = twCent (MonoidHom.id (UL n w)) γ ⊓ (iwU n w b).map (MulAut.conj p₀).toMonoidHom := by
  intro E _ _ _ hU w hw n b hb ϖ hϖ l hl hyp γ ⟨p1, hp1⟩
  obtain ⟨hW1, hW2, hWc, -⟩ := GlobalTheory.CompanionTheory.UnitaryWitt.unitary_hyperbolic_basis E hU w hw n b hb
  have hinj : Function.Injective (wexp n l) :=
    (GlobalTheory.CompanionTheory.Wexp.wexp_strictAnti_rev n l hl).1.injective
  have huc := GlobalTheory.CompanionTheory.UnitaryContraction.main E hU w hw n b hb ϖ hϖ l hl hyp
  obtain ⟨m, hm, u, hu, hmu⟩ := huc _ hp1
  obtain ⟨p₀, hp₀⟩ : ∃ p₀ : UL n w, p₀ = p1 * m := ⟨_, rfl⟩
  have hγ0 : (p₀⁻¹ * γ * p₀).1 = b * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) u * b⁻¹ := by
    rw [← hmu]
    congr 1
    rw [hp₀]
    group

  have key : ∀ (q : UL n w) (u' : Fin n → (w.adicCompletion E)ˣ),
      (∀ i, ordL (u' i : w.adicCompletion E) = wexp n l i) →
      (q⁻¹ * (p₀⁻¹ * γ * p₀) * q).1 = b * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) u' * b⁻¹ →
      u = u' ∧ ∃ s : Fin n → (w.adicCompletion E)ˣ,
        q.1 = b * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) s * b⁻¹ := by
    intro q u' hu' e
    have e' : q.1⁻¹ * (b * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) u * b⁻¹) * q.1 =
        b * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) u' * b⁻¹ := by
      rw [← hγ0, ← e]
      rfl
    have hh : (b⁻¹ * q.1 * b)⁻¹ * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) u * (b⁻¹ * q.1 * b) =
        GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) u' := by
      calc _ = b⁻¹ * (q.1⁻¹ * (b * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) u * b⁻¹) * q.1) * b := by
            group
        _ = _ := by rw [e']; group
    obtain ⟨h1, s, hs⟩ := GlobalTheory.CompanionTheory.DiagRigid.diag_rigid (w.adicCompletion E) n (wexp n l) hinj u u'
      hu hu' _ hh
    refine ⟨h1, s, ?_⟩
    rw [← hs]
    group
  refine ⟨p₀, u, hu, hγ0, fun p => ⟨fun hp => ?_, ?_⟩, ?_⟩
  ·
    obtain ⟨m', hm', u', hu', e⟩ := huc _ hp
    have e2 : (p₀⁻¹ * p * m')⁻¹ * (p₀⁻¹ * γ * p₀) * (p₀⁻¹ * p * m') = m'⁻¹ * (p⁻¹ * γ * p) * m' := by
      group
    obtain ⟨rfl, -⟩ := key (p₀⁻¹ * p * m') u' hu' (by rw [e2]; exact e)
    have hq : (p₀⁻¹ * p * m')⁻¹ * (p₀⁻¹ * γ * p₀) * (p₀⁻¹ * p * m') = p₀⁻¹ * γ * p₀ := by
      apply Subtype.ext
      rw [e2, e, hγ0]
    refine ⟨p₀ * (p₀⁻¹ * p * m') * p₀⁻¹, comm_of_conj γ p₀ _ hq, m'⁻¹, inv_mem hm', ?_⟩
    group
  ·
    rintro ⟨z, hz, i, hi, rfl⟩
    have hz' : z * γ = γ * z := hz
    have e : (z * p₀ * i)⁻¹ * γ * (z * p₀ * i) = i⁻¹ * (p₀⁻¹ * γ * p₀) * i := by
      calc _ = i⁻¹ * p₀⁻¹ * z⁻¹ * (γ * z) * p₀ * i := by group
        _ = i⁻¹ * p₀⁻¹ * z⁻¹ * (z * γ) * p₀ * i := by rw [hz']
        _ = _ := by group
    rw [e, GlobalTheory.CompanionTheory.DiagCoset.fU_diag E hU w hw n b hb ϖ hϖ l hl _ u hu hγ0 _ (inv_mem hi) _ hi]
    exact one_ne_zero
  ·
    refine GlobalTheory.CompanionTheory.CptGen.cptPart_eq_inf (UL n w) _ _ ?_ ?_
    · rw [Subgroup.coe_map]
      refine hWc.image ?_
      change Continuous fun x : UL n w => p₀ * x * p₀⁻¹
      fun_prop
    · intro t ht hc
      have ht' : t * γ = γ * t := ht
      obtain ⟨-, s, hs⟩ := key (p₀⁻¹ * t * p₀) u hu (by rw [conj_comm γ p₀ t ht']; exact hγ0)
      have hv := GlobalTheory.CompanionTheory.DiagBd.valued_eq_one_of_isCompact_closure_zpowers E w n (UL n w)
        (p₀⁻¹ * t * p₀) b s hs (isCompact_closure_zpowers_conj p₀ t hc)
      have hmem : p₀⁻¹ * t * p₀ ∈ iwU n w b := by
        rw [hW2]
        have : b⁻¹ * (p₀⁻¹ * t * p₀).1 * b = GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) s := by
          rw [hs]
          group
        rw [this]
        exact GlobalTheory.CompanionTheory.DiagCoset.diagT_mem_iwGL w n s hv
      refine Subgroup.mem_map.2 ⟨_, hmem, ?_⟩
      simp [MulAut.conj_apply, mul_assoc]

end GlobalTheory.CompanionTheory.SuppCent
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DominantCosetTwistedConjugacyStatement
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dominant_coset_twisted_conjugacy : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (n : ℕ) (b : GLw n w), IsWitt n w b → ∀ (ϖ : (w.adicCompletion E)ˣ), IsUnifAt ϖ → ∀ (l : Fin (n / 2) → ℤ), Cone l → (∀ (y : Fin n → ℤ), StrictAnti y → ∀ δ : GLw n w, dcos n w (tdiag ϖ y) δ ≠ 0 → ∃ m ∈ iwGL n w, ∃ τ : GLw n w, ((∀ i j : Fin n, i ≠ j → τ.val i j = 0) ∧ ∀ i, Valued.v (τ.val i i) = 1) ∧ m⁻¹ * δ * m = tdiag ϖ y * τ) → ∀ γ : UL n w, (∃ p : UL n w, fU n w b ϖ l (p⁻¹ * γ * p) ≠ 0) → ∃ (p₀ : UL n w) (u : Fin n → (w.adicCompletion E)ˣ), (∀ i, ordL (u i : w.adicCompletion E) = wexp n l i) ∧ (p₀⁻¹ * γ * p₀).1 = b * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) u * b⁻¹ ∧ (∀ p : UL n w, fU n w b ϖ l (p⁻¹ * γ * p) ≠ 0 ↔ ∃ z ∈ twCent (MonoidHom.id (UL n w)) γ, ∃ i ∈ iwU n w b, p = z * p₀ * i) ∧ cptPart (twCent (MonoidHom.id (UL n w)) γ) = twCent (MonoidHom.id (UL n w)) γ ⊓ (iwU n w b).map (MulAut.conj p₀).toMonoidHom := by
  first | exact @GlobalTheory.CompanionTheory.SuppCent.main | exact GlobalTheory.CompanionTheory.SuppCent.main | (intros; apply GlobalTheory.CompanionTheory.SuppCent.main <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeightEqOfFullIntersectionSystem
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeightEqOfFullIntersectionSystem
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace

open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsMultiHomog HermLine IsSmoothHerm IsHorizontal divSupp multAt geoNum charOf ptsIntegral
  IsIntersectionFamily IntersectionSystem IsFullIntersectionSystem)
open ReciprocityTheory.ChartRestriction.G.AI.I2 (IsRatSectionOn logNormRat RatRStatement)
open GlobalTheory.CompanionTheory.MPDict

namespace GlobalTheory.CompanionTheory.MixZ

variable {m : ℕ} {n : Fin (m + 1) → ℕ}

theorem dim_of_generic {X Z : Scheme.{0}} [IsIntegral Z] (j : Z ⟶ X) [IsClosedImmersion j] :
    topologicalKrullDim (closure ({j (genericPoint Z)} : Set X)) = topologicalKrullDim Z := by
  have hrange : Set.range j = closure {j (genericPoint Z)} := by
    have h₁ := (genericPoint_spec Z).image j.continuous
    rw [Set.image_univ, j.isClosedEmbedding.isClosed_range.closure_eq] at h₁
    exact h₁.def.symm
  exact topologicalKrullDim_eq_of_isEmbedding j.isClosedEmbedding.isEmbedding hrange

theorem dim_closure_image {X Y : Scheme.{0}} (j : Y ⟶ X) [IsClosedImmersion j] (z : Y) :
    topologicalKrullDim (closure ({j z} : Set X)) = topologicalKrullDim (closure ({z} : Set Y)) := by
  obtain ⟨Z, k, _, _, rfl⟩ := GlobalTheory.exists_isClosedImmersion_genericPoint z
  exact (dim_of_generic (k ≫ j)).trans (dim_of_generic k).symm

theorem isometric_restr_restr {X Z : Scheme.{0}} (N : HermLB (mpStr ℤ m n)) (i : X ⟶ MP ℤ m n) (j : Z ⟶ X) :
    ((N.restr i).restr j).Isometric (N.pull (j ≫ i) (Category.assoc _ _ _)) := by
  have hm : ∀ (c : ((N.restr i).restr j).B.ι) (x : Z), x ∈ ((N.restr i).restr j).B.U c →
      x ∈ (N.pull (j ≫ i) (Category.assoc _ _ _)).B.U (fun _ => c PUnit.unit PUnit.unit) := fun c x h =>
    (mem_pull (F := j ≫ i) (x := x)).2 ((mem_pull (F := i) (x := j x)).1 ((mem_pull (F := j) (x := x)).1 h))
  refine HermLB.isometric_of_chart (fun c _ => c PUnit.unit PUnit.unit) (fun c x h => hm c x h) (fun x c c' h h' => ?_)
    fun σ c y hy => ?_
  · have h₁ := (mem_pull (F := j) (x := x)).1 h
    have h₁' := (mem_pull (F := j) (x := x)).1 h'
    refine (gm_pull_g (N.B.pull i) j (𝟙 Z) x c c' h h').trans ?_
    refine (gm_pull_g N.B i (𝟙 Z ≫ j) x _ _ h₁ h₁').trans ?_
    refine Eq.trans ?_ (gm_pull_g N.B (j ≫ i) (𝟙 Z) x _ _ (hm c x h) (hm c' x h')).symm
    simp only [Category.assoc]
  · refine ((N.φ σ).pull_φ (j ≫ i) (Category.assoc _ _ _) _ y).trans ?_
    refine Eq.trans ?_ ((((N.φ σ).pull i rfl).pull_φ j rfl c y)).symm
    refine Eq.trans ?_ ((N.φ σ).pull_φ i rfl _ _).symm
    congr 1

theorem archInt_transport {Z : Scheme.{0}} [IsIntegral Z] {q : Z ⟶ Sp ℤ} {L M : HermLB q} (iso : L.Isometric M)
    {r : L.B.ι → Z.functionFieldˣ} (hr : IsRatSec L.B r) :
    ∃ (r' : M.B.ι → Z.functionFieldˣ) (hr' : IsRatSec M.B r'), M.div hr' = L.div hr ∧
      (∀ e, M.archInt M e hr' = L.archInt L e hr) ∧
      ∀ σ, Set.EqOn (GlobalTheory.Cartier.logNorm (M.φ σ) r') (GlobalTheory.Cartier.logNorm (L.φ σ) r) (GlobalTheory.Cartier.offSupp q σ (L.div hr)) := by
  obtain ⟨r', hr', h₁, h₂⟩ := iso.exists_isRatSec hr
  refine ⟨r', hr', h₁, fun e => ?_, h₂⟩
  simp only [HermLB.archInt, h₁, iso.chernInt_eq]
  exact finsum_congr fun σ => Weight.chernInt_congr (isOpen_offSupp _).measurableSet (h₂ σ)

theorem rec_eq (h₅ : ExistsRat) (h₆ : CycleOfRat) (h₇ : ArchIntEq) (hR : RatRStatement)
    (II : IntersectionSystem) (hII : IsFullIntersectionSystem II) (N : HermLB (mpStr ℤ m n)) (A : HermLine (Bk n))
    (hN : IsHermRep N A) (hA : IsSmoothHerm A) (Z : Scheme.{0}) [IsIntegral Z] [IsLocallyNoetherian Z]
    (i : Z ⟶ MP ℤ m n) [IsClosedImmersion i] (e : ℕ) (hZ : GlobalTheory.IsArithVar (i ≫ mpStr ℤ m n) e)
    (hP : Geo.IsArithVar (ptIdeal (i (genericPoint Z))) (e + 1))
    (r : (N.restr i).B.ι → Z.functionFieldˣ) (hr : IsRatSec (N.restr i).B r) :
    cycVal II A (e + 1) (ptIdeal (i (genericPoint Z))) =
      ∑ᶠ z, (((N.restr i).div hr).mult z : ℝ) * cycVal II A e (ptIdeal (i z)) -
        (N.restr i).archInt (N.restr i) e hr := by
  obtain ⟨f, g, hfg, hrat⟩ := h₅ m n N A hN Z i r hr
  have hcyc := h₆ m n N A hN Z i e hZ r hr f g hfg hrat (cycVal II A e)
  have hint := h₇ m n N N A A hN hN Z i e hZ hA hA r hr f g hfg hrat
  have hrr := hR _ _ (II _ (Bk n)) (hII.1 _ _) _ e (fun _ => A) A f g hP (fun _ => hA) hA hfg
  have hs : (Fin.snoc (fun _ : Fin e => A) A : Fin (e + 1) → HermLine (Bk n)) = fun _ => A := by
    funext j
    refine Fin.lastCases ?_ (fun j => ?_) j <;> simp
  rw [hs] at hrr
  rw [hint, hcyc, cycVal, if_pos hP.2.2.1, hrr]
  rfl

theorem mp_var (m : ℕ) (n : Fin (m + 1) → ℕ) : GlobalTheory.IsArithVar (mpStr ℤ m n) (∑ i, n i) :=
  GlobalTheory.Amb.isArithVar_mp ℤ inferInstance m n

theorem not_horizontal_of_dim_zero (h₃ : PtDict) {X : Scheme.{0}} (i : X ⟶ MP ℤ m n) [IsClosedImmersion i] (z : X)
    (hz : topologicalKrullDim (closure ({z} : Set X)) = (0 : ℕ)) : ¬ IsHorizontal (ptIdeal (i z)) := by
  obtain ⟨Z, k, _, _, rfl⟩ := GlobalTheory.exists_isClosedImmersion_genericPoint z
  have hd : topologicalKrullDim Z = (0 : ℕ) := (dim_of_generic k).symm.trans hz
  obtain ⟨-, h2, -, -⟩ := h₃ m n Z (k ≫ i) 0 hd
  intro hh
  have hc : CharZero Γ(Z, ⊤) := h2.1 hh
  exact (mp_var m n).dim_ne_zero (k ≫ i) hc (by exact_mod_cast hd)

theorem curve_eq (h₃ : PtDict) (h₄ : CodimOne) (h₅ : ExistsRat) (h₆ : CycleOfRat) (h₇ : ArchIntEq) (hPt : PtLen)
    (hC : CurveInt) (hR : RatRStatement)
    (II : IntersectionSystem) (hII : IsFullIntersectionSystem II) (N : HermLB (mpStr ℤ m n)) (A : HermLine (Bk n))
    (hN : IsHermRep N A) (hA : IsSmoothHerm A) (Z : Scheme.{0}) [IsIntegral Z] [IsLocallyNoetherian Z]
    (i : Z ⟶ MP ℤ m n) [IsClosedImmersion i] (hZ : GlobalTheory.IsArithVar (i ≫ mpStr ℤ m n) 0)
    (hP : Geo.IsArithVar (ptIdeal (i (genericPoint Z))) 1)
    (r : (N.restr i).B.ι → Z.functionFieldˣ) (hr : IsRatSec (N.restr i).B r) :
    cycVal II A 1 (ptIdeal (i (genericPoint Z))) =
      ∑ᶠ z, (((N.restr i).div hr).mult z : ℝ) * Real.log (Nat.card (Z.residueField z)) -
        ∑ᶠ σ, ∑ᶠ y : CxPts (i ≫ mpStr ℤ m n) σ, logNorm ((N.restr i).φ σ) r y := by
  rw [rec_eq h₅ h₆ h₇ hR II hII N A hN hA Z i 0 hZ hP r hr, (hC Z _ hZ (N.restr i) (N.restr i) r hr).2]
  refine congrArg (· - _) (finsum_congr fun z => ?_)
  by_cases hz : ((N.restr i).div hr).mult z = 0
  · simp [hz]
  have hd := h₄ Z _ 0 hZ z (CartierDiv.coheight_eq_one_of_mult_ne_zero hz)
  rw [cycVal, if_neg (not_horizontal_of_dim_zero h₃ i z hd), hPt m n Z i z hd]

theorem rec_eq' (h₅ : ExistsRat) (h₆ : CycleOfRat) (h₇ : ArchIntEq) (hR : RatRStatement)
    (II : IntersectionSystem) (hII : IsFullIntersectionSystem II) (N : HermLB (mpStr ℤ m n)) (A : HermLine (Bk n))
    (hN : IsHermRep N A) (hA : IsSmoothHerm A) (Z : Scheme.{0}) [IsIntegral Z] [IsLocallyNoetherian Z]
    (i : Z ⟶ MP ℤ m n) [IsClosedImmersion i] {q : Z ⟶ Sp ℤ} (hq : i ≫ mpStr ℤ m n = q) (e : ℕ)
    (hZ : GlobalTheory.IsArithVar q e) (hP : Geo.IsArithVar (ptIdeal (i (genericPoint Z))) (e + 1))
    (r : (N.pull i hq).B.ι → Z.functionFieldˣ) (hr : IsRatSec (N.pull i hq).B r) :
    cycVal II A (e + 1) (ptIdeal (i (genericPoint Z))) =
      ∑ᶠ z, (((N.pull i hq).div hr).mult z : ℝ) * cycVal II A e (ptIdeal (i z)) -
        (N.pull i hq).archInt (N.pull i hq) e hr := by
  subst hq
  exact rec_eq h₅ h₆ h₇ hR II hII N A hN hA Z i e hZ hP r hr

theorem curve_eq' (h₃ : PtDict) (h₄ : CodimOne) (h₅ : ExistsRat) (h₆ : CycleOfRat) (h₇ : ArchIntEq) (hPt : PtLen)
    (hC : CurveInt) (hR : RatRStatement)
    (II : IntersectionSystem) (hII : IsFullIntersectionSystem II) (N : HermLB (mpStr ℤ m n)) (A : HermLine (Bk n))
    (hN : IsHermRep N A) (hA : IsSmoothHerm A) (Z : Scheme.{0}) [IsIntegral Z] [IsLocallyNoetherian Z]
    (i : Z ⟶ MP ℤ m n) [IsClosedImmersion i] {q : Z ⟶ Sp ℤ} (hq : i ≫ mpStr ℤ m n = q)
    (hZ : GlobalTheory.IsArithVar q 0) (hP : Geo.IsArithVar (ptIdeal (i (genericPoint Z))) 1)
    (r : (N.pull i hq).B.ι → Z.functionFieldˣ) (hr : IsRatSec (N.pull i hq).B r) :
    cycVal II A 1 (ptIdeal (i (genericPoint Z))) =
      ∑ᶠ z, (((N.pull i hq).div hr).mult z : ℝ) * Real.log (Nat.card (Z.residueField z)) -
        ∑ᶠ σ, ∑ᶠ y : CxPts q σ, logNorm ((N.pull i hq).φ σ) r y := by
  subst hq
  exact curve_eq h₃ h₄ h₅ h₆ h₇ hPt hC hR II hII N A hN hA Z i hZ hP r hr

theorem charP_of_cast {R : Type} [CommRing R] [IsDomain R] {p : ℕ} (hp : p.Prime) (h : (p : R) = 0) : CharP R p := by
  obtain ⟨ℓ, hℓ⟩ := CharP.exists R
  rcases (Nat.dvd_prime hp).1 ((CharP.cast_eq_zero_iff R ℓ p).1 h) with rfl | rfl
  · exact absurd ((Nat.cast_one (R := R)).symm.trans ((CharP.cast_eq_zero_iff R 1 1).2 dvd_rfl)) one_ne_zero
  · exact hℓ

theorem heightEq_of (h₃ : PtDict) (h₄ : CodimOne) (h₅ : ExistsRat) (h₆ : CycleOfRat) (h₇ : ArchIntEq) (hV : VertEq)
    (hPt : PtLen) (hC : CurveInt) (hR : RatRStatement) (II : IntersectionSystem) (hII : IsFullIntersectionSystem II) :
    HeightEq II := by
  intro m n N A hN hA X _ _ i _ h H z d hd
  induction d using Nat.strong_induction_on generalizing z with
  | _ d ih =>
  obtain ⟨Z, j, _, _, rfl⟩ := GlobalTheory.exists_isClosedImmersion_genericPoint z
  have hZd : topologicalKrullDim Z = d := (dim_of_generic j).symm.trans hd
  have hmp := mp_var m n
  have hnoeth := hmp.isNoetherian_sub (j ≫ i)
  have hln : IsLocallyNoetherian Z := hnoeth.toIsLocallyNoetherian
  have hcomp : ∀ x, (j ≫ i) x = i (j x) := fun x => by simp
  obtain ⟨-, hp₃, hp₄, hp₅⟩ := h₃ m n Z (j ≫ i) d hZd
  simp only [hcomp] at hp₃ hp₄ hp₅
  by_cases hW : IsHorizontal (ptIdeal (i (j (genericPoint Z))))
  · have hc : CharZero Γ(Z, ⊤) := hp₃.1 hW
    have hP := hp₄ hW
    obtain ⟨r₀, hr₀⟩ := exists_isRatSec ((N.restr i).restr j).isLB
    obtain ⟨r, hr, e₁, e₂, e₃⟩ := archInt_transport (isometric_restr_restr N i j) hr₀
    cases d with
    | zero => exact absurd (by exact_mod_cast hZd) (hmp.dim_ne_zero (j ≫ i) hc)
    | succ e =>
      have hZ₀ : GlobalTheory.IsArithVar ((j ≫ i) ≫ mpStr ℤ m n) e := hmp.of_isClosedImmersion (j ≫ i) hc hZd
      have hZ : GlobalTheory.IsArithVar (j ≫ i ≫ mpStr ℤ m n) e := by
        rw [← Category.assoc]
        exact hZ₀
      rcases Nat.eq_zero_or_pos e with rfl | he
      · have hcv := curve_eq' h₃ h₄ h₅ h₆ h₇ hPt hC hR II hII N A hN hA Z (j ≫ i) (Category.assoc _ _ _) hZ
          (by simpa only [hcomp] using hP) r hr
        simp only [hcomp] at hcv
        rw [H.point Z j hc hZd r₀ hr₀, hcv, HermLB.curveDeg, e₁]
        refine congrArg _ (finsum_congr fun σ => finsum_congr fun y => (e₃ σ (mem_offSupp.2 ?_)).symm)
        rw [hZ.under_eq_genericPoint]
        exact CartierDiv.genericPoint_notMem_supp _
      · have hrc := rec_eq' h₅ h₆ h₇ hR II hII N A hN hA Z (j ≫ i) (Category.assoc _ _ _) e hZ
          (by simpa only [hcomp] using hP) r hr
        simp only [hcomp] at hrc
        rw [(H.recursion_one j hc he hZd hr₀).2, hrc, e₂, e₁]
        refine congrArg (· - _) (finsum_congr fun z' => ?_)
        by_cases hz : (((N.restr i).restr j).div hr₀).mult z' = 0
        · simp [hz]
        have hdz := h₄ Z _ e hZ z' (CartierDiv.coheight_eq_one_of_mult_ne_zero hz)
        rw [ih e (Nat.lt_succ_self e) (j z') ((dim_closure_image j z').trans hdz)]
  · obtain ⟨hpr, hz⟩ := hp₅ hW
    have key : ∀ p : ℕ, p.Prime → ((p : ℕ) : Γ(Z, ⊤)) = 0 → h (j (genericPoint Z)) =
        (geoNum d (ptIdeal (i (j (genericPoint Z)))) (fun _ => A.a) : ℝ) * Real.log p := by
      intro p hp h0
      haveI : Fact p.Prime := ⟨hp⟩
      haveI : CharP Γ(Z, ⊤) p := charP_of_cast hp h0
      letI : Algebra (ZMod p) Γ(Z, ⊤) := ZMod.algebra _ p
      have e₁ := H.vertical Z j (ZMod p) d hZd
      have e₂ : topSelfIntersection (ZMod p) ((N.restr i).B.pull j) d = _ := hV m n N A hN X i Z j p d hZd
      rw [e₁, e₂, Nat.card_zmod]
    rw [key _ hpr hz, cycVal, if_neg hW]

theorem heightEq_holds : PtDict → CodimOne → ExistsRat → CycleOfRat → ArchIntEq → VertEq → PtLen → CurveInt →
    RatRStatement → ∀ II : IntersectionSystem, IsFullIntersectionSystem II → HeightEq II :=
  fun h₃ h₄ h₅ h₆ h₇ hV hPt hC hR II hII => heightEq_of h₃ h₄ h₅ h₆ h₇ hV hPt hC hR II hII

end GlobalTheory.CompanionTheory.MixZ
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeightEqOfFullIntersectionSystemStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.height_eq_of_full_intersection_system : GlobalTheory.CompanionTheory.MixZ.PtDict → GlobalTheory.CompanionTheory.MixZ.CodimOne → GlobalTheory.CompanionTheory.MixZ.ExistsRat → GlobalTheory.CompanionTheory.MixZ.CycleOfRat → GlobalTheory.CompanionTheory.MixZ.ArchIntEq → GlobalTheory.CompanionTheory.MixZ.VertEq → GlobalTheory.CompanionTheory.MixZ.PtLen → GlobalTheory.CompanionTheory.MixZ.CurveInt → ReciprocityTheory.ChartRestriction.G.AI.I2.RatRStatement → ∀ II : ReciprocityTheory.ChartRestriction.G.Geo.IntersectionSystem, ReciprocityTheory.ChartRestriction.G.Geo.IsFullIntersectionSystem II → GlobalTheory.CompanionTheory.MixZ.HeightEq II := by
  first | exact @GlobalTheory.CompanionTheory.MixZ.heightEq_holds | exact GlobalTheory.CompanionTheory.MixZ.heightEq_holds | (intros; apply GlobalTheory.CompanionTheory.MixZ.heightEq_holds <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultiplicityPowerFormula
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultiplicityPowerFormula
noncomputable section

open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.SiegLoc

namespace GlobalTheory.CompanionTheory.GunrNu

theorem card_range_pow {R : Type} [CommRing R] {σ : R →+* R} {ϖ : R} {q : ℕ} {ε : ℤ}
    (hR : IsUnrQuad R σ ϖ q ε) (k : ℕ) (d : R) (hd : σ d = d) :
    ∃ e : ℕ, Nat.card (Set.range fun w : R ⧸ lev ϖ k => w * Ideal.Quotient.mk (lev ϖ k) d) =
      (q ^ 2) ^ e := by
  rcases Scaled.fixed_decomp hR k d hd with h0 | ⟨a₀, e, c, rfl, hc, hc1, rfl⟩
  · have hz : Ideal.Quotient.mk (lev ϖ k) d = 0 := Ideal.Quotient.eq_zero_iff_mem.2 h0
    have hr : (Set.range fun w : R ⧸ lev ϖ k => w * Ideal.Quotient.mk (lev ϖ k) d) = {0} := by
      ext z
      simp [hz]
    exact ⟨0, by rw [hr]; simp⟩
  · exact ⟨e, by
      rw [Scaled.card_range_mul hR.reg (hR.fixLocal c hc hc1) e a₀,
        GlobalTheory.T.unramified_quotient_card R σ ϖ q ε hR e, pow_mul]⟩

theorem nuPow : PositivityTheory.SiegelWeilFormula.Gunr.NuPow := by
  intro R _ σ ϖ q ε hR n k B hB
  obtain ⟨h, hh, rfl⟩ := hB
  have hq := hR.one_lt
  have hfin : Finite (R ⧸ lev ϖ k) := Nat.finite_of_card_ne_zero (by
    rw [GlobalTheory.T.unramified_quotient_card R σ ϖ q ε hR k]
    exact pow_ne_zero _ (by omega))
  let _ : Fintype (R ⧸ lev ϖ k) := Fintype.ofFinite _
  obtain ⟨g, g', d, hgg, hgg', hd, hgd⟩ := GlobalTheory.T.hermitian_matrix_diagonalizable R σ ϖ q ε hR n h hh
  choose eI hcard using fun i => card_range_pow hR k (d i) (hd i)
  have hnu : nuAt ϖ (red ϖ k h) = (q ^ 2) ^ (∑ i, eI i) := by
    rw [GlobalTheory.T.multiplicity_reduction_diagonal_prod R σ ϖ hR.fix_ϖ hR.inv k n h g g' d hgg hgg' hgd,
      Finset.prod_congr rfl (fun i _ => hcard i), Finset.prod_pow_eq_pow_sum]
  rw [hnu, Nat.log_pow (Nat.one_lt_pow (by norm_num) hq)]

end GlobalTheory.CompanionTheory.GunrNu

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultiplicityPowerFormulaStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multiplicity_power_formula : PositivityTheory.SiegelWeilFormula.Gunr.NuPow := by
  first | exact @GlobalTheory.CompanionTheory.GunrNu.nuPow | exact GlobalTheory.CompanionTheory.GunrNu.nuPow | (intros; apply GlobalTheory.CompanionTheory.GunrNu.nuPow <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HassePrinciple
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HassePrinciple
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology PositivityTheory.Rg.Mass
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.MassHasse

theorem hasse : Hasse := by
  intro F E _ _ _ _ _ σ J d b li lam μ 𝓕 mi m hCM hJ _ _ _ _ _ hmi _ β hβ hne
  by_contra hS
  have hnot : ∀ x : Fin 2 → E, hE σ J x x ≠ algebraMap F E β := fun x hx =>
    hS ⟨fun _ => x, by
      funext a c
      simpa [gramE] using hx⟩
  obtain ⟨τ, c, hc0, hc, hw⟩ := Plane.exists_place hCM J hJ β hβ hnot
  obtain ⟨Φ, hΦ, hΦσ⟩ := Plane.exists_hom hCM τ
  have hscal : algebraMap F (Ainf F) β ⊗ₜ[F] (1 : E) = inclR (Ainf F) (algebraMap F E β) := by
    simp only [inclR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.includeRight_apply,
      Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  have hempty : (gramR (Ainf F) σ J ⁻¹' {(hermScal (Ainf F) σ (algebraMap F (Ainf F) β)).1} ∩
      {X | IsUnit (gramR (Ainf F) σ J X).det}) = ∅ := by
    ext Y
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq,
      Set.mem_empty_iff_false, iff_false, not_and]
    intro hY _
    have h00 : hR (Ainf F) σ J (Y 0) (Y 0) = inclR (Ainf F) (algebraMap F E β) :=
      (congrFun (congrFun hY 0) 0).trans hscal
    have h1 := congrArg Φ h00
    rw [hΦ, hc] at h1
    let w : Fin 2 → ℂ := fun i => Φ (Y 0 i)
    have key : Φ (hR (Ainf F) σ J (Y 0) (Y 0)) = star w ⬝ᵥ (J.map τ *ᵥ w) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [hR, hform, JR, map_sum, map_mul, hΦσ, Matrix.map_apply, hΦ, dotProduct, Matrix.mulVec,
        Pi.star_apply, Finset.mul_sum, w, mul_assoc]
    have h2 := hw w
    rw [← key, h1, Complex.ofReal_re] at h2
    exact absurd (mul_self_pos.2 hc0) (not_lt.2 h2)
  apply hne
  have h1 := hmi.1 (hermScal (Ainf F) σ (algebraMap F (Ainf F) β))
  rw [hempty, Set.compl_empty] at h1
  exact Measure.measure_univ_eq_zero.1 h1

end GlobalTheory.CompanionTheory.SW.MassHasse
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HassePrincipleStatement
open PositivityTheory.Rg.Mass
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasse_principle : Hasse := by
  first | exact @GlobalTheory.CompanionTheory.SW.MassHasse.hasse | exact GlobalTheory.CompanionTheory.SW.MassHasse.hasse | (intros; apply GlobalTheory.CompanionTheory.SW.MassHasse.hasse <;> assumption)
end
end
