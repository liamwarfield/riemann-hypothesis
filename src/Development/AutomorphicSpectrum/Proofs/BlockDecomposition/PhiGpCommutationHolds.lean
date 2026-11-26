module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuotientMapIntertwinesRestriction
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenCellParabolicNearIdentity
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermAutomorphicCriterion
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CongruenceSubgroupsBasisNhds
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EqZeroOfEigOfMemTwKer
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalHermitianRing
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MaxEvenLatticeAdaptedBasis
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DerivativeTwistedIso

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicProjUnipotentCharacterCompat
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicProjUnipotentCharacterCompat
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.LeibPhi

theorem gpProj_mirUin_char : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (m j : ℕ) (u : MirUin k (m + (j + 1)))
    (hh : (u : Mir k (m + (j + 1))) ∈ MirabolicParabolic k m (j + 1)),
    (gpProj k m (j + 1) ⟨u, hh⟩).1 = 1 ∧ ∃ hv : (gpProj k m (j + 1) ⟨u, hh⟩).2 ∈ MirUin k (j + 1),
      mirChar k ψ j ⟨_, hv⟩ = mirChar k ψ (m + j) u := by
  intro k _ _ _ _ ψ m j u hh
  obtain ⟨h1, hv⟩ := GlobalTheory.CompanionTheory.GpUnip.gpProj_unip k m (j + 1) ⟨u, hh⟩ u.2
  refine ⟨h1, hv, ?_⟩
  obtain ⟨w', hw'⟩ := id (id hv : (((gpProj k m (j + 1) ⟨u, hh⟩).2 : Mir k (j + 1)) : GL (Fin (j + 1 + 1)) k) ∈ MirU k (j + 1))
  obtain ⟨w, hw⟩ := (u.2 : ((u : Mir k (m + j + 1)) : GL (Fin (m + j + 1 + 1)) k) ∈ MirU k (m + j + 1))
  rw [mirChar_eq k ψ j ⟨_, hv⟩ w' hw'.symm, mirChar_eq k ψ (m + j) u w hw.symm]
  have hent : ((((gpProj k m (j + 1) ⟨u, hh⟩).2 : Mir k (j + 1)) : GL (Fin (j + 1 + 1)) k) : Matrix _ _ k)
      (Fin.castSucc (Fin.last j)) (Fin.last (j + 1)) =
      (((u : Mir k (m + (j + 1))) : GL (Fin (m + (j + 1) + 1)) k) : Matrix _ _ k)
        (eGP m (j + 1) ⟨true, Fin.castSucc (Fin.last j)⟩) (eGP m (j + 1) ⟨true, Fin.last (j + 1)⟩) := by
    show (leviProj k (eGP m (j + 1)) (hgpIncl k m (j + 1) ⟨u, hh⟩) true).val _ _ = _
    rw [leviProj_apply]
    rfl
  have e : eGP m (j + 1) ⟨true, Fin.castSucc (Fin.last j)⟩ = Fin.castSucc (Fin.last (m + j)) :=
    Fin.ext (by rw [blockIndex_true_val]; simp)
  rw [blockIndex_true_last, e, ← hw'] at hent
  have a1 := unip_apply_castSucc_last k (j + 1) w' (Fin.last j)
  have a2 := unip_apply_castSucc_last k (m + j + 1) w (Fin.last (m + j))
  have : w'.toAdd (Fin.last j) = w.toAdd (Fin.last (m + j)) := by
    rw [← a1, ← a2]
    refine hent.trans ?_
    exact congrArg (fun g : GL (Fin (m + j + 1 + 1)) k => (g : Matrix (Fin (m + j + 1 + 1)) (Fin (m + j + 1 + 1)) k)
      (Fin.castSucc (Fin.last (m + j))) (Fin.last (m + j + 1))) hw.symm
  rw [this]

end GlobalTheory.CompanionTheory.LeibPhi

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicProjUnipotentCharacterCompatStatement
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parabolic_proj_unipotent_character_compat : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (m j : ℕ) (u : MirUin k (m + (j + 1)))
    (hh : (u : Mir k (m + (j + 1))) ∈ MirabolicParabolic k m (j + 1)),
    (gpProj k m (j + 1) ⟨u, hh⟩).1 = 1 ∧ ∃ hv : (gpProj k m (j + 1) ⟨u, hh⟩).2 ∈ MirUin k (j + 1),
      mirChar k ψ j ⟨_, hv⟩ = mirChar k ψ (m + j) u := by
  first | exact @GlobalTheory.CompanionTheory.LeibPhi.gpProj_mirUin_char | exact GlobalTheory.CompanionTheory.LeibPhi.gpProj_mirUin_char | (intros; apply GlobalTheory.CompanionTheory.LeibPhi.gpProj_mirUin_char <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicProjEmbeddingCompat
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicProjEmbeddingCompat
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.LeibPhi.IotaProj

theorem blockIndex_succ_false (m j : ℕ) (a : Fin m) :
    eGP m (j + 1) ⟨false, a⟩ = (Fin.castSucc (eGP m j ⟨false, a⟩) : Fin (m + j + 1 + 1)) := by
  apply Fin.ext
  first
    | rfl
    | simp [GlobalTheory.BZMir.Leib.eGP, GlobalTheory.SmGL.two, GlobalTheory.SmGL.stdSum]

theorem blockIndex_succ_true_castSucc (m j : ℕ) (b : Fin (j + 1)) :
    eGP m (j + 1) ⟨true, Fin.castSucc b⟩ = (Fin.castSucc (eGP m j ⟨true, b⟩) : Fin (m + j + 1 + 1)) := by
  apply Fin.ext
  first
    | rfl
    | simp [GlobalTheory.BZMir.Leib.eGP, GlobalTheory.SmGL.two, GlobalTheory.SmGL.stdSum]
    | (simp [GlobalTheory.BZMir.Leib.eGP, GlobalTheory.SmGL.two, GlobalTheory.SmGL.stdSum]; omega)

theorem blockIndex_succ_true_last (m j : ℕ) :
    eGP m (j + 1) ⟨true, Fin.last (j + 1)⟩ = (Fin.last (m + j + 1) : Fin (m + j + 1 + 1)) := by
  exact GlobalTheory.BZMir.Leib.blockIndex_true_last m (j + 1)

theorem glEmbMat_castSucc (k : Type) [Field k] (n : ℕ) (A : Matrix (Fin n) (Fin n) k) (a b : Fin n) :
    glEmbMat k n A (Fin.castSucc a) (Fin.castSucc b) = A a b := by
  simp [GlobalTheory.BZMir.glEmbMat]

theorem glEmbMat_last_castSucc (k : Type) [Field k] (n : ℕ) (A : Matrix (Fin n) (Fin n) k) (b : Fin n) :
    glEmbMat k n A (Fin.last n) (Fin.castSucc b) = 0 := by
  simp [GlobalTheory.BZMir.glEmbMat]

theorem glEmbMat_castSucc_last (k : Type) [Field k] (n : ℕ) (A : Matrix (Fin n) (Fin n) k) (a : Fin n) :
    glEmbMat k n A (Fin.castSucc a) (Fin.last n) = 0 := by
  simp [GlobalTheory.BZMir.glEmbMat]

theorem glEmbMat_last_last (k : Type) [Field k] (n : ℕ) (A : Matrix (Fin n) (Fin n) k) :
    glEmbMat k n A (Fin.last n) (Fin.last n) = 1 := by
  simp [GlobalTheory.BZMir.glEmbMat]

theorem gpProj_iotaM : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (m j : ℕ) (y : GlobalTheory.BZMir.Leib.MirabolicParabolic k m j)
    (hh : embedding₂ k (m + j) y ∈ GlobalTheory.BZMir.Leib.MirabolicParabolic k m (j + 1)),
    GlobalTheory.BZMir.Leib.gpProj k m (j + 1) ⟨_, hh⟩ =
      ((GlobalTheory.BZMir.Leib.gpProj k m j y).1,
        embedding₂ k j (GlobalTheory.BZMir.Leib.gpProj k m j y).2) := by
  intro k _ _ _ _ m j y hh
  refine Prod.ext ?_ ?_
  · refine Units.ext (Matrix.ext fun a b => ?_)
    refine (GlobalTheory.SmGL.leviProj_apply k (GlobalTheory.BZMir.Leib.eGP m (j + 1))
      (GlobalTheory.BZMir.Leib.hgpIncl k m (j + 1) ⟨_, hh⟩) false a b).trans
      (Eq.trans ?_ (GlobalTheory.SmGL.leviProj_apply k (GlobalTheory.BZMir.Leib.eGP m j)
        (GlobalTheory.BZMir.Leib.hgpIncl k m j y) false a b).symm)
    rw [GlobalTheory.CompanionTheory.LeibPhi.IotaProj.blockIndex_succ_false m j a, GlobalTheory.CompanionTheory.LeibPhi.IotaProj.blockIndex_succ_false m j b]
    exact GlobalTheory.CompanionTheory.LeibPhi.IotaProj.glEmbMat_castSucc k (m + j + 1)
      ((((y : GlobalTheory.BZMir.Mir k (m + j)) : GL (Fin (m + j + 1)) k)) :
        Matrix (Fin (m + j + 1)) (Fin (m + j + 1)) k) _ _
  · apply Subtype.ext
    refine Units.ext (Matrix.ext fun a b => ?_)
    refine (GlobalTheory.SmGL.leviProj_apply k (GlobalTheory.BZMir.Leib.eGP m (j + 1))
      (GlobalTheory.BZMir.Leib.hgpIncl k m (j + 1) ⟨_, hh⟩) true a b).trans ?_
    have hR := fun a b => GlobalTheory.SmGL.leviProj_apply k (GlobalTheory.BZMir.Leib.eGP m j)
      (GlobalTheory.BZMir.Leib.hgpIncl k m j y) true a b
    induction a using Fin.lastCases with
    | last =>
      induction b using Fin.lastCases with
      | last =>
        rw [GlobalTheory.CompanionTheory.LeibPhi.IotaProj.blockIndex_succ_true_last]
        exact (GlobalTheory.CompanionTheory.LeibPhi.IotaProj.glEmbMat_last_last k (m + j + 1)
          ((((y : GlobalTheory.BZMir.Mir k (m + j)) : GL (Fin (m + j + 1)) k)) :
            Matrix (Fin (m + j + 1)) (Fin (m + j + 1)) k)).trans
          (GlobalTheory.CompanionTheory.LeibPhi.IotaProj.glEmbMat_last_last k (j + 1)
            ((((GlobalTheory.BZMir.Leib.gpProj k m j y).2 : GL (Fin (j + 1)) k)) :
              Matrix (Fin (j + 1)) (Fin (j + 1)) k)).symm
      | cast b =>
        rw [GlobalTheory.CompanionTheory.LeibPhi.IotaProj.blockIndex_succ_true_last, GlobalTheory.CompanionTheory.LeibPhi.IotaProj.blockIndex_succ_true_castSucc]
        exact (GlobalTheory.CompanionTheory.LeibPhi.IotaProj.glEmbMat_last_castSucc k (m + j + 1)
          ((((y : GlobalTheory.BZMir.Mir k (m + j)) : GL (Fin (m + j + 1)) k)) :
            Matrix (Fin (m + j + 1)) (Fin (m + j + 1)) k) _).trans
          (GlobalTheory.CompanionTheory.LeibPhi.IotaProj.glEmbMat_last_castSucc k (j + 1)
            ((((GlobalTheory.BZMir.Leib.gpProj k m j y).2 : GL (Fin (j + 1)) k)) :
              Matrix (Fin (j + 1)) (Fin (j + 1)) k) b).symm
    | cast a =>
      induction b using Fin.lastCases with
      | last =>
        rw [GlobalTheory.CompanionTheory.LeibPhi.IotaProj.blockIndex_succ_true_last, GlobalTheory.CompanionTheory.LeibPhi.IotaProj.blockIndex_succ_true_castSucc]
        exact (GlobalTheory.CompanionTheory.LeibPhi.IotaProj.glEmbMat_castSucc_last k (m + j + 1)
          ((((y : GlobalTheory.BZMir.Mir k (m + j)) : GL (Fin (m + j + 1)) k)) :
            Matrix (Fin (m + j + 1)) (Fin (m + j + 1)) k) _).trans
          (GlobalTheory.CompanionTheory.LeibPhi.IotaProj.glEmbMat_castSucc_last k (j + 1)
            ((((GlobalTheory.BZMir.Leib.gpProj k m j y).2 : GL (Fin (j + 1)) k)) :
              Matrix (Fin (j + 1)) (Fin (j + 1)) k) a).symm
      | cast b =>
        rw [GlobalTheory.CompanionTheory.LeibPhi.IotaProj.blockIndex_succ_true_castSucc, GlobalTheory.CompanionTheory.LeibPhi.IotaProj.blockIndex_succ_true_castSucc]
        exact (GlobalTheory.CompanionTheory.LeibPhi.IotaProj.glEmbMat_castSucc k (m + j + 1)
          ((((y : GlobalTheory.BZMir.Mir k (m + j)) : GL (Fin (m + j + 1)) k)) :
            Matrix (Fin (m + j + 1)) (Fin (m + j + 1)) k) _ _).trans
          ((hR a b).symm.trans
            (GlobalTheory.CompanionTheory.LeibPhi.IotaProj.glEmbMat_castSucc k (j + 1)
              ((((GlobalTheory.BZMir.Leib.gpProj k m j y).2 : GL (Fin (j + 1)) k)) :
                Matrix (Fin (j + 1)) (Fin (j + 1)) k) a b).symm)

end GlobalTheory.CompanionTheory.LeibPhi.IotaProj

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicProjEmbeddingCompatStatement
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parabolic_proj_embedding_compat : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m j : ℕ) (y : MirabolicParabolic k m j) (hh : embedding₂ k (m + j) y ∈ MirabolicParabolic k m (j + 1)),
    gpProj k m (j + 1) ⟨_, hh⟩ = ((gpProj k m j y).1, embedding₂ k j (gpProj k m j y).2) := by
  first | exact @GlobalTheory.CompanionTheory.LeibPhi.IotaProj.gpProj_iotaM | exact GlobalTheory.CompanionTheory.LeibPhi.IotaProj.gpProj_iotaM | (intros; apply GlobalTheory.CompanionTheory.LeibPhi.IotaProj.gpProj_iotaM <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicUnipotentLeParabolicStatement
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mirabolic_unipotent_le_parabolic :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
      [IsNonarchimedeanLocalField k] (m j : ℕ),
      MirUin k (m + j) ≤ GlobalTheory.BZMir.Leib.MirabolicParabolic k m j := by
  intro k _ _ _ _ m j g hg
  unfold GlobalTheory.BZMir.MirUin at hg
  rw [Subgroup.mem_subgroupOf] at hg
  obtain ⟨v, hv⟩ := hg
  change (g : GL (Fin (m + j + 1)) k) ∈ parab k (eGP m j)
  rw [GlobalTheory.SmGL.mem_parab_iff]
  intro x y b a hxy
  obtain ⟨rfl, rfl⟩ := Bool.lt_iff.mp hxy
  have hmat : ((g : GL (Fin (m + j + 1)) k) : Matrix (Fin (m + j + 1)) (Fin (m + j + 1)) k) =
      1 + GlobalTheory.BZMir.colMat k (m + j) (Multiplicative.toAdd v) := by
    rw [← hv]
    rfl
  have hne : eGP m j ⟨true, b⟩ ≠ eGP m j ⟨false, a⟩ := by
    intro h
    have hval := congrArg Fin.val h
    rw [GlobalTheory.CompanionTheory.LeibPhi.blockIndex_true_val,
      GlobalTheory.CompanionTheory.LeibPhi.blockIndex_false_val] at hval
    have ha := a.isLt
    omega
  rw [hmat]
  simp only [Matrix.add_apply, Matrix.one_apply, GlobalTheory.BZMir.colMat,
    ite_eq_right (GlobalTheory.BZMir.Leib.blockIndex_false_ne_last m j a), ite_eq_right hne,
    add_zero]
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactInductionCongrEquiv
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactInductionCongrEquiv
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.CIndCongr

variable {G W W' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']

def mapFun (H : Subgroup G) {σ : Representation ℂ H W} {σ' : Representation ℂ H W'}
    (L : W ≃ₗ[ℂ] W') (hL : ∀ (h : H) (w : W), L (σ h w) = σ' h (L w))
    (f : cIndSpace H σ) : cIndSpace H σ' :=
  have hind : (fun g => L (f.1.1.1 g)) ∈ indSpace H σ' := by
    intro h g
    have e : f.1.1.1 ((h : G) * g) = σ h (f.1.1.1 g) := f.1.1.2 h g
    show L (f.1.1.1 ((h : G) * g)) = σ' h (L (f.1.1.1 g))
    rw [e, hL]
  have hsm : (⟨fun g => L (f.1.1.1 g), hind⟩ : indSpace H σ') ∈ smoothPart (ind H σ') := by
    obtain ⟨K, hK, hKi⟩ := cInd_right_inv H σ f
    refine GlobalTheory.CompanionTheory.BZMirOnto.isOpen_fixed_of_subgroup (ind H σ') K hK _ fun x hx => ?_
    apply Subtype.ext
    funext g
    show L (f.1.1.1 (g * x)) = L (f.1.1.1 g)
    rw [hKi g x hx]
  have hc : (⟨⟨fun g => L (f.1.1.1 g), hind⟩, hsm⟩ : smoothPart (ind H σ')) ∈ cIndSpace H σ' := by
    obtain ⟨C, hC, hf⟩ := f.2
    refine ⟨C, hC, fun g hg => hf g fun h0 => hg ?_⟩
    show L (f.1.1.1 g) = 0
    rw [h0, map_zero]
  ⟨⟨⟨fun g => L (f.1.1.1 g), hind⟩, hsm⟩, hc⟩

theorem ext_fun {H : Subgroup G} {σ : Representation ℂ H W} {f f' : cIndSpace H σ}
    (h : ∀ g, f.1.1.1 g = f'.1.1.1 g) : f = f' :=
  Subtype.ext (Subtype.ext (Subtype.ext (funext h)))

theorem nonempty_equiv_cInd :
    ∀ {G W W' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup W'] [Module ℂ W'] (H : Subgroup G) (σ : Representation ℂ H W) (σ' : Representation ℂ H W'),
    σ.Equiv σ' → Nonempty ((cInd H σ).Equiv (cInd H σ')) := by
  intro G W W' _ _ _ _ _ _ _ H σ σ' e
  let L : W ≃ₗ[ℂ] W' := e.toLinearEquiv
  have hL : ∀ (h : H) (w : W), L (σ h w) = σ' h (L w) := fun h w =>
    LinearMap.congr_fun (e.isIntertwining' h) w
  have hL' : ∀ (h : H) (w : W'), L.symm (σ' h w) = σ h (L.symm w) := fun h w => by
    apply L.injective
    rw [L.apply_symm_apply, hL, L.apply_symm_apply]
  let T : cIndSpace H σ ≃ₗ[ℂ] cIndSpace H σ' :=
    { toFun := mapFun H L hL
      map_add' := fun f f' => ext_fun fun g => map_add L (f.1.1.1 g) (f'.1.1.1 g)
      map_smul' := fun c f => ext_fun fun g => map_smul L c (f.1.1.1 g)
      invFun := mapFun H L.symm hL'
      left_inv := fun f => ext_fun fun g => L.symm_apply_apply (f.1.1.1 g)
      right_inv := fun f => ext_fun fun g => L.apply_symm_apply (f.1.1.1 g) }
  refine ⟨Representation.Equiv.mk T fun x => LinearMap.ext fun f => ext_fun fun g => ?_⟩
  rfl

end GlobalTheory.CompanionTheory.CIndCongr

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactInductionCongrEquivStatement
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compactInduction_congr_equiv : ∀ {G W W' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup W'] [Module ℂ W'] (H : Subgroup G) (σ : Representation ℂ H W) (σ' : Representation ℂ H W'),
    σ.Equiv σ' → Nonempty ((cInd H σ).Equiv (cInd H σ')) := by
  first | exact @GlobalTheory.CompanionTheory.CIndCongr.nonempty_equiv_cInd | exact GlobalTheory.CompanionTheory.CIndCongr.nonempty_equiv_cInd | (intros; apply GlobalTheory.CompanionTheory.CIndCongr.nonempty_equiv_cInd <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetKernelSpanTwistedCharacter
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetKernelSpanTwistedCharacter
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.LeibPhi.Kernel

section Abstract

variable {G W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup W] [Module ℂ W]

theorem cInd_ext {H : Subgroup G} {σ : Representation ℂ H W} {a b : cIndSpace H σ}
    (h : ∀ g, a.1.1.1 g = b.1.1.1 g) : a = b :=
  Subtype.ext (Subtype.ext (Subtype.ext (funext h)))

theorem cInd_left {H : Subgroup G} {σ : Representation ℂ H W} (a : cIndSpace H σ) {h : G}
    (hh : h ∈ H) (g : G) : a.1.1.1 (h * g) = σ ⟨h, hh⟩ (a.1.1.1 g) :=
  a.1.1.2 ⟨h, hh⟩ g

theorem indicator_mem (H U : Subgroup G) (hUH : U ≤ H) (hU : U.Normal) (θ : U →* ℂˣ)
    (σ : Representation ℂ H W) {E : Set G} (hE : IsHK H E) (a : cIndSpace H σ)
    (ha : a ∈ twKer (cInd H σ) U θ) :
    ∀ a' : cIndSpace H σ, (∀ g ∈ E, a'.1.1.1 g = a.1.1.1 g) → (∀ g, g ∉ E → a'.1.1.1 g = 0) →
      a' ∈ twKer (cInd H σ) U θ := by
  have hR : ∀ (g : G) (u : U), g * (u : G) ∈ E ↔ g ∈ E := by
    intro g u
    have e : g * (u : G) = (g * (u : G) * g⁻¹) * g := by group
    rw [e]
    exact hE.1 _ (hUH (hU.conj_mem _ u.2 g)) g
  unfold twKer at ha
  induction ha using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u, v, rfl⟩ := hx
    intro a' h1 h2
    obtain ⟨v', hv1, hv2⟩ := exists_indicator H σ hE v
    have e : a' = cInd H σ (u : G) v' - (θ u : ℂ) • v' := by
      apply cInd_ext
      intro g
      by_cases hg : g ∈ E
      · rw [h1 g hg]
        show v.1.1.1 (g * u) - (θ u : ℂ) • v.1.1.1 g = v'.1.1.1 (g * u) - (θ u : ℂ) • v'.1.1.1 g
        rw [hv1 g hg, hv1 _ ((hR g u).2 hg)]
      · rw [h2 g hg]
        show (0 : W) = v'.1.1.1 (g * u) - (θ u : ℂ) • v'.1.1.1 g
        rw [hv2 g hg, hv2 _ (fun c => hg ((hR g u).1 c))]
        simp
    rw [e]
    exact Submodule.subset_span ⟨u, v', rfl⟩
  | zero =>
    intro a' h1 h2
    have e : a' = 0 := by
      apply cInd_ext
      intro g
      by_cases hg : g ∈ E
      · exact h1 g hg
      · exact h2 g hg
    rw [e]
    exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    intro a' h1 h2
    obtain ⟨x', hx1, hx2⟩ := exists_indicator H σ hE x
    obtain ⟨y', hy1, hy2⟩ := exists_indicator H σ hE y
    have e : a' = x' + y' := by
      apply cInd_ext
      intro g
      by_cases hg : g ∈ E
      · rw [h1 g hg]
        show x.1.1.1 g + y.1.1.1 g = x'.1.1.1 g + y'.1.1.1 g
        rw [hx1 g hg, hy1 g hg]
      · rw [h2 g hg]
        show (0 : W) = x'.1.1.1 g + y'.1.1.1 g
        rw [hx2 g hg, hy2 g hg, add_zero]
    rw [e]
    exact Submodule.add_mem _ (hx x' hx1 hx2) (hy y' hy1 hy2)
  | smul c x _ hx =>
    intro a' h1 h2
    obtain ⟨x', hx1, hx2⟩ := exists_indicator H σ hE x
    have e : a' = c • x' := by
      apply cInd_ext
      intro g
      by_cases hg : g ∈ E
      · rw [h1 g hg]
        show c • x.1.1.1 g = c • x'.1.1.1 g
        rw [hx1 g hg]
      · rw [h2 g hg]
        show (0 : W) = c • x'.1.1.1 g
        rw [hx2 g hg, smul_zero]
    rw [e]
    exact Submodule.smul_mem _ c (hx x' hx1 hx2)

theorem exists_local (H U : Subgroup G) (hUH : U ≤ H) (hU : U.Normal) (θ : U →* ℂˣ)
    (σ : Representation ℂ H W) (f f' : cIndSpace H σ) (hf' : f' ∈ twKer (cInd H σ) U θ) (g₀ : G)
    (he : f'.1.1.1 g₀ = f.1.1.1 g₀) :
    ∃ E : Set G, g₀ ∈ E ∧ IsHK H E ∧ ∃ b ∈ twKer (cInd H σ) U θ,
      (∀ g ∈ E, b.1.1.1 g = f.1.1.1 g) ∧ (∀ g, g ∉ E → b.1.1.1 g = 0) := by
  obtain ⟨K, hK, hKi⟩ := cInd_right_inv H σ (f - f')
  have hE := isHK_doubleCoset H K hK g₀
  refine ⟨{g | ∃ a ∈ H, ∃ x ∈ K, g = a * g₀ * x}, ⟨1, one_mem H, 1, one_mem K, by simp⟩, hE, ?_⟩
  obtain ⟨b, hb1, hb2⟩ := exists_indicator H σ hE f'
  refine ⟨b, indicator_mem H U hUH hU θ σ hE f' hf' b hb1 hb2, ?_, hb2⟩
  rintro g ⟨a, ha, x, hx, rfl⟩
  rw [hb1 _ ⟨a, ha, x, hx, rfl⟩]
  have h0 : (f - f').1.1.1 g₀ = 0 := by
    show f.1.1.1 g₀ - f'.1.1.1 g₀ = 0
    rw [he, sub_self]
  have h1 : (f - f').1.1.1 (a * g₀ * x) = 0 := by
    rw [hKi _ x hx, cInd_left (f - f') ha, h0, map_zero]
  have h2 : f.1.1.1 (a * g₀ * x) - f'.1.1.1 (a * g₀ * x) = 0 := h1
  exact (sub_eq_zero.1 h2).symm

theorem mem_of_local (H U : Subgroup G) (hUH : U ≤ H) (hU : U.Normal) (θ : U →* ℂˣ)
    (σ : Representation ℂ H W) (f : cIndSpace H σ)
    (hloc : ∀ g₀ : G, ∃ E : Set G, g₀ ∈ E ∧ IsHK H E ∧ ∃ b ∈ twKer (cInd H σ) U θ,
      (∀ g ∈ E, b.1.1.1 g = f.1.1.1 g) ∧ (∀ g, g ∉ E → b.1.1.1 g = 0)) :
    f ∈ twKer (cInd H σ) U θ := by
  obtain ⟨C, hC, hf⟩ := f.2
  have key : ∃ E : Set G, C ⊆ E ∧ IsHK H E ∧ ∃ b ∈ twKer (cInd H σ) U θ,
      (∀ g ∈ E, b.1.1.1 g = f.1.1.1 g) ∧ (∀ g, g ∉ E → b.1.1.1 g = 0) := by
    refine hC.induction_on (p := fun S => ∃ E : Set G, S ⊆ E ∧ IsHK H E ∧
      ∃ b ∈ twKer (cInd H σ) U θ,
        (∀ g ∈ E, b.1.1.1 g = f.1.1.1 g) ∧ (∀ g, g ∉ E → b.1.1.1 g = 0)) ?_ ?_ ?_ ?_
    · refine ⟨∅, subset_rfl, ⟨by simp, ⊤, isOpen_univ, by simp⟩, 0, Submodule.zero_mem _, by simp,
        fun g _ => rfl⟩
    · rintro S T hST ⟨E, hTE, r⟩
      exact ⟨E, hST.trans hTE, r⟩
    · rintro S T ⟨E, hSE, hE, b, hb, hb1, hb2⟩ ⟨E', hTE, hE', b', hb', hb1', hb2'⟩
      obtain ⟨c, hc1, hc2⟩ := exists_indicator H σ hE.compl b'
      refine ⟨E ∪ E', Set.union_subset_union hSE hTE, hE.union hE', b + c,
        Submodule.add_mem _ hb (indicator_mem H U hUH hU θ σ hE.compl b' hb' c hc1 hc2), ?_, ?_⟩
      · intro g hg
        show b.1.1.1 g + c.1.1.1 g = f.1.1.1 g
        by_cases h : g ∈ E
        · rw [hb1 g h, hc2 g (fun c => c h), add_zero]
        · rw [hb2 g h, hc1 g h, zero_add]
          exact hb1' g (hg.resolve_left h)
      · intro g hg
        show b.1.1.1 g + c.1.1.1 g = 0
        have h : g ∉ E := fun c => hg (Or.inl c)
        have h' : g ∉ E' := fun c => hg (Or.inr c)
        rw [hb2 g h, hc1 g h, hb2' g h', add_zero]
    · intro x _
      obtain ⟨E, hx, hE, r⟩ := hloc x
      exact ⟨E, mem_nhdsWithin_of_mem_nhds (hE.isOpen.mem_nhds hx), E, subset_rfl, hE, r⟩
  obtain ⟨E, hCE, hE, b, hb, hb1, hb2⟩ := key
  have e : f = b := by
    apply cInd_ext
    intro g
    by_cases hg : g ∈ E
    · exact (hb1 g hg).symm
    · rw [hb2 g hg]
      by_contra h0
      obtain ⟨h, hh, c, hc, rfl⟩ := hf g h0
      exact hg ((hE.1 h hh c).2 (hCE hc))
  rw [e]
  exact hb

end Abstract

theorem mem_twKer_of_restrict_zero {G G' W W' : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [Group G']
    [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    (H U : Subgroup G) (hUH : U ≤ H) (hU : U.Normal) (θ : U →* ℂˣ) (ι : G' →* G)
    (hst : ∀ (m : G') (n : U), ∃ h : ι m * (n : G) * (ι m)⁻¹ ∈ U, θ ⟨_, h⟩ = θ n)
    (σ : Representation ℂ H W) (q : W →ₗ[ℂ] W') (hσ : IsSmooth σ)
    (hq : ∀ w, q w = 0 ↔ w ∈ Submodule.span ℂ {y | ∃ (u : U) (v : W), y = σ ⟨u, hUH u.2⟩ v - (θ u : ℂ) • v})
    (hdich : ∀ g : G, (∃ h ∈ H, ∃ x : G', g = h * ι x) ∨
      ∃ u : U, ∃ hx : g * (u : G) * g⁻¹ ∈ H, (∀ w, σ ⟨_, hx⟩ w = w) ∧ θ u ≠ 1)
    (hbase : ∀ O ∈ 𝓝 (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ O)
    (f : cIndSpace H σ) (hf : ∀ x, q (f.1.1.1 (ι x)) = 0) : f ∈ twKer (cInd H σ) U θ := by
  refine mem_of_local H U hUH hU θ σ f fun g₀ => ?_
  suffices hp : ∃ f' ∈ twKer (cInd H σ) U θ, f'.1.1.1 g₀ = f.1.1.1 g₀ by
    obtain ⟨f', hf', he⟩ := hp
    exact exists_local H U hUH hU θ σ f f' hf' g₀ he
  rcases hdich g₀ with ⟨h, hh, x, rfl⟩ | ⟨u, hx, hfix, hθ⟩
  · have hval : ∀ y ∈ Submodule.span ℂ {y | ∃ (u : U) (v : W), y = σ ⟨u, hUH u.2⟩ v - (θ u : ℂ) • v},
        ∃ f' ∈ twKer (cInd H σ) U θ, f'.1.1.1 (ι x) = y := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨v, w, rfl⟩ := hy
        obtain ⟨hm, hθ⟩ := hst x⁻¹ v
        obtain ⟨e, he⟩ := exists_cInd_value H σ hσ hbase (ι x) w
        refine ⟨cInd H σ _ e - (θ ⟨_, hm⟩ : ℂ) • e, Submodule.subset_span ⟨⟨_, hm⟩, e, rfl⟩, ?_⟩
        have e1 : ι x * (ι x⁻¹ * (v : G) * (ι x⁻¹)⁻¹) = (v : G) * ι x := by
          simp only [map_inv]
          group
        show e.1.1.1 (ι x * (ι x⁻¹ * (v : G) * (ι x⁻¹)⁻¹)) - (θ ⟨_, hm⟩ : ℂ) • e.1.1.1 (ι x) = _
        rw [e1, cInd_left e (hUH v.2), he, hθ]
      | zero => exact ⟨0, Submodule.zero_mem _, rfl⟩
      | add a b _ _ ha hb =>
        obtain ⟨a', ha', ea⟩ := ha
        obtain ⟨b', hb', eb⟩ := hb
        refine ⟨a' + b', Submodule.add_mem _ ha' hb', ?_⟩
        show a'.1.1.1 (ι x) + b'.1.1.1 (ι x) = _
        rw [ea, eb]
      | smul c a _ ha =>
        obtain ⟨a', ha', ea⟩ := ha
        refine ⟨c • a', Submodule.smul_mem _ c ha', ?_⟩
        show c • a'.1.1.1 (ι x) = _
        rw [ea]
    obtain ⟨f', hf', he⟩ := hval _ ((hq _).1 (hf x))
    exact ⟨f', hf', by rw [cInd_left f' hh, cInd_left f hh, he]⟩
  · have hne : (1 : ℂ) - (θ u : ℂ) ≠ 0 := by
      intro h0
      apply hθ
      apply Units.ext
      simpa using (sub_eq_zero.1 h0).symm
    obtain ⟨e, he⟩ := exists_cInd_value H σ hσ hbase g₀ (((1 : ℂ) - (θ u : ℂ))⁻¹ • f.1.1.1 g₀)
    refine ⟨cInd H σ (u : G) e - (θ u : ℂ) • e, Submodule.subset_span ⟨u, e, rfl⟩, ?_⟩
    have e1 : g₀ * (u : G) = (g₀ * (u : G) * g₀⁻¹) * g₀ := by group
    show e.1.1.1 (g₀ * u) - (θ u : ℂ) • e.1.1.1 g₀ = _
    rw [e1, cInd_left e hx, hfix, he]
    have e2 : ∀ y : W, y - (θ u : ℂ) • y = ((1 : ℂ) - (θ u : ℂ)) • y := fun y => by
      rw [sub_smul, one_smul]
    rw [e2, smul_smul, mul_inv_cancel₀ hne, one_smul]

end GlobalTheory.CompanionTheory.LeibPhi.Kernel

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetKernelSpanTwistedCharacterStatement
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquet_kernel_span_twisted_character : ∀ {G G' W W' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group G']
    [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    (H U : Subgroup G) (hUH : U ≤ H) (_ : U.Normal) (θ : U →* ℂˣ) (ι : G' →* G)
    (_ : ∀ (m : G') (n : U), ∃ h : ι m * (n : G) * (ι m)⁻¹ ∈ U, θ ⟨_, h⟩ = θ n)
    (σ : Representation ℂ H W) (q : W →ₗ[ℂ] W'), IsSmooth σ →
    (∀ w, q w = 0 ↔ w ∈ Submodule.span ℂ {y | ∃ (u : U) (v : W), y = σ ⟨u, hUH u.2⟩ v - (θ u : ℂ) • v}) →
    (∀ g : G, (∃ h ∈ H, ∃ x : G', g = h * ι x) ∨
      ∃ u : U, ∃ hx : g * (u : G) * g⁻¹ ∈ H, (∀ w, σ ⟨_, hx⟩ w = w) ∧ θ u ≠ 1) →
    (∀ O ∈ 𝓝 (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ O) →
    ∀ f : cIndSpace H σ, (∀ x, q (f.1.1.1 (ι x)) = 0) → f ∈ twKer (cInd H σ) U θ := by
  first | exact @GlobalTheory.CompanionTheory.LeibPhi.Kernel.mem_twKer_of_restrict_zero | exact GlobalTheory.CompanionTheory.LeibPhi.Kernel.mem_twKer_of_restrict_zero | (intros; apply GlobalTheory.CompanionTheory.LeibPhi.Kernel.mem_twKer_of_restrict_zero <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUnipotentLiftParabolicProj
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUnipotentLiftParabolicProj
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.LeibPhi

theorem exists_mirUin_gpProj_lift : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m j : ℕ) (n : MirUin k (j + 1)),
    ∃ (u : MirUin k (m + (j + 1))) (hh : (u : Mir k (m + (j + 1))) ∈ MirabolicParabolic k m (j + 1)),
      gpProj k m (j + 1) ⟨u, hh⟩ = (1, (n : Mir k (j + 1))) := by
  intro k _ _ _ _ m j n
  obtain ⟨v, hv, e⟩ := GlobalTheory.CompanionTheory.BZMir.exists_gpProj_unip k m (j + 1) (n : Mir k (j + 1)) n.2
  exact ⟨⟨v, hv⟩, v.2, e⟩

end GlobalTheory.CompanionTheory.LeibPhi

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUnipotentLiftParabolicProjStatement
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unipotent_lift_parabolic_proj : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m j : ℕ) (n : MirUin k (j + 1)),
    ∃ (u : MirUin k (m + (j + 1))) (hh : (u : Mir k (m + (j + 1))) ∈ MirabolicParabolic k m (j + 1)),
      gpProj k m (j + 1) ⟨u, hh⟩ = (1, (n : Mir k (j + 1))) := by
  first | exact @GlobalTheory.CompanionTheory.LeibPhi.exists_mirUin_gpProj_lift | exact GlobalTheory.CompanionTheory.LeibPhi.exists_mirUin_gpProj_lift | (intros; apply GlobalTheory.CompanionTheory.LeibPhi.exists_mirUin_gpProj_lift <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PhiGpCommutationHolds
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib Topology
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.LeibPhi

section AbsMain
variable {G G' W W' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group G'] [TopologicalSpace G']
    [IsTopologicalGroup G'] [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']

theorem coinv_cInd (H U : Subgroup G) (hUH : U ≤ H) (hUn : U.Normal) (θ : U →* ℂˣ) (ι : G' →* G)
    (hι : Continuous ι) (hstab : ∀ (m : G') (n : U), ∃ h : ι m * (n : G) * (ι m)⁻¹ ∈ U, θ ⟨_, h⟩ = θ n)
    (H' : Subgroup G') (hH' : ∀ x, x ∈ H' ↔ ι x ∈ H)
    (σ : Representation ℂ H W) (hσ : IsSmooth σ) (σ' : Representation ℂ H' W') (q : W →ₗ[ℂ] W')
    (hqs : Function.Surjective q)
    (hq : ∀ (h : H') (hh : ι h ∈ H) (w : W), q (σ ⟨ι h, hh⟩ w) = σ' h (q w))
    (hker : ∀ w, q w = 0 ↔ w ∈ Submodule.span ℂ {y | ∃ (u : U) (v : W), y = σ ⟨u, hUH u.2⟩ v - (θ u : ℂ) • v})
    (hD : ∀ g : G, (∃ h ∈ H, ∃ x : G', g = h * ι x) ∨
      ∃ u : U, ∃ hx : g * (u : G) * g⁻¹ ∈ H, (∀ w, σ ⟨_, hx⟩ w = w) ∧ θ u ≠ 1)
    (hcl : IsClosed {g : G | ∃ h ∈ H, ∃ x : G', g = h * ι x})
    (hemb : ∀ K' ∈ 𝓝 (1 : G'), ∃ K ∈ 𝓝 (1 : G), ∀ x : G', ∀ h ∈ H, ∀ κ ∈ K, ι x = h * κ →
      ∃ h' ∈ H', ∃ κ' ∈ K', x = h' * κ')
    (hbase : ∀ O ∈ 𝓝 (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ O)
    (hcomp : ∃ K' ∈ 𝓝 (1 : G'), IsCompact K') :
    Nonempty ((twAct (cInd H σ) U θ ι hstab).Equiv (cInd H' σ')) := by
  classical
  have hex := GlobalTheory.T.quotient_map_intertwines_restriction H H' ι σ σ' q hι hH' hq hcl hemb hcomp
  choose T hT using hex
  have hext : ∀ F F' : cIndSpace H' σ', (∀ x, F.1.1.1 x = F'.1.1.1 x) → F = F' := fun F F' h =>
    Subtype.ext (Subtype.ext (Subtype.ext (funext h)))
  let Tl : cIndSpace H σ →ₗ[ℂ] cIndSpace H' σ' :=
    { toFun := T
      map_add' := fun a b => hext _ _ fun x => by
        rw [hT]
        show _ = (T a).1.1.1 x + (T b).1.1.1 x
        rw [hT, hT, ← map_add (f := _)]
        rfl
      map_smul' := fun c a => hext _ _ fun x => by
        rw [hT]
        show _ = c • (T a).1.1.1 x
        rw [hT, ← map_smul]
        rfl }
  have hTl : ∀ f x, (Tl f).1.1.1 x = q (f.1.1.1 (ι x)) := hT
  have hkill : twKer (cInd H σ) U θ ≤ LinearMap.ker Tl := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨u, e, rfl⟩
    show Tl _ = 0
    refine hext _ _ fun x => ?_
    rw [hTl]
    obtain ⟨hv, hθ⟩ := hstab x u
    have hvH : ι x * (u : G) * (ι x)⁻¹ ∈ H := hUH hv
    have e1 : (cInd H σ (u : G) e - (θ u : ℂ) • e).1.1.1 (ι x) =
        σ ⟨_, hvH⟩ (e.1.1.1 (ι x)) - (θ ⟨_, hv⟩ : ℂ) • e.1.1.1 (ι x) := by
      rw [hθ]
      show e.1.1.1 (ι x * (u : G)) - (θ u : ℂ) • e.1.1.1 (ι x) = _
      have e2 := e.1.1.2 ⟨_, hvH⟩ (ι x)
      have e3 : e.1.1.1 (ι x * (u : G)) = e.1.1.1 (ι x * (u : G) * (ι x)⁻¹ * ι x) := by
        congr 1; group
      rw [e3]
      exact congrArg (· - _) e2
    rw [e1]
    show _ = (0 : W')
    exact (hker _).2 (Submodule.subset_span ⟨⟨_, hv⟩, _, rfl⟩)
  let Tq := (twKer (cInd H σ) U θ).liftQ Tl hkill
  have hinj : Function.Injective Tq := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro y hy
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    have h0 : Tl f = 0 := hy
    refine (Submodule.Quotient.mk_eq_zero _).2 (GlobalTheory.T.jacquet_kernel_span_twisted_character H U hUH hUn θ ι hstab σ q hσ hker hD hbase f fun x => ?_)
    rw [← hTl, h0]
    rfl
  have hsurj : Function.Surjective Tq := by
    intro F
    obtain ⟨f, hf⟩ := GlobalTheory.T.quotient_map_induced_surjective_intertwiner H H' ι σ σ' q hι hσ hqs hH' hq hemb hbase F
    refine ⟨Submodule.Quotient.mk f, ?_⟩
    show Tl f = F
    exact hext _ _ fun x => by rw [hTl, hf]
  refine ⟨Representation.Equiv.mk (LinearEquiv.ofBijective Tq ⟨hinj, hsurj⟩) fun y => ?_⟩
  refine LinearMap.ext fun z => ?_
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  refine hext _ _ fun x => ?_
  have e1 : (twAct (cInd H σ) U θ ι hstab y) (Submodule.Quotient.mk f) =
      Submodule.Quotient.mk (cInd H σ (ι y) f) := rfl
  show (Tq (twAct (cInd H σ) U θ ι hstab y (Submodule.Quotient.mk f))).1.1.1 x =
    (Tq (Submodule.Quotient.mk f)).1.1.1 (x * y)
  rw [e1]
  show (Tl _).1.1.1 x = (Tl f).1.1.1 (x * y)
  rw [hTl, hTl, map_mul]
  rfl

end AbsMain

section PhiProd
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem phiMinus_prodGP (ψ : AddChar k Circle) (hψ1 : ψ ≠ 1) {m j : ℕ}
    (a : Representation ℂ (GL (Fin m) k) V) (b : Representation ℂ (Mir k (j + 1)) W)
    (ha : IsSmooth a) (hb : IsSmooth b) :
    Nonempty ((phiMinus k ψ (n := m + j) (prodGP a b)).Equiv (prodGP a (phiMinus k ψ b))) := by
  classical
  have hsm : IsSmooth ((extTensor a b).comp (gpProj k m (j + 1))) := by
    intro w
    exact (isSmooth_extTensor ha hb w).preimage (GlobalTheory.T.continuous_parabolic_proj k m (j + 1))
  have hUH : MirUin k (m + (j + 1)) ≤ MirabolicParabolic k m (j + 1) := GlobalTheory.T.mirabolic_unipotent_le_parabolic k m (j + 1)
  let q : V ⊗[ℂ] W →ₗ[ℂ] V ⊗[ℂ] (TwJacquet b (MirUin k (j + 1)) (mirChar k ψ j)) :=
    LinearMap.lTensor V (twKer b (MirUin k (j + 1)) (mirChar k ψ j)).mkQ
  have hqs : Function.Surjective q := LinearMap.lTensor_surjective _ (Submodule.mkQ_surjective _)
  have hq : ∀ (h : MirabolicParabolic k m j) (hh : embedding₂ k (m + j) h ∈ MirabolicParabolic k m (j + 1)) (w : V ⊗[ℂ] W),
      q (((extTensor a b).comp (gpProj k m (j + 1))) ⟨embedding₂ k (m + j) h, hh⟩ w) =
        ((extTensor a (phiMinus k ψ b)).comp (gpProj k m j)) h (q w) := by
    intro h hh w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | tmul v w =>
      have e := GlobalTheory.T.parabolic_proj_embedding_compat k m j h hh
      show q (extTensor a b (gpProj k m (j + 1) ⟨_, hh⟩) (v ⊗ₜ w)) =
        extTensor a (phiMinus k ψ b) (gpProj k m j h) (q (v ⊗ₜ w))
      rw [e]
      simp only [q, LinearMap.lTensor_tmul, extTensor_tmul]
      rfl
  have hker : ∀ w, q w = 0 ↔ w ∈ Submodule.span ℂ {y | ∃ (u : MirUin k (m + (j + 1))) (v : V ⊗[ℂ] W),
      y = ((extTensor a b).comp (gpProj k m (j + 1))) ⟨u, hUH u.2⟩ v - (mirChar k ψ (m + j) u : ℂ) • v} := by
    intro w
    constructor
    · intro hw
      have hex := lTensor_exact V (LinearMap.exact_subtype_mkQ
        (twKer b (MirUin k (j + 1)) (mirChar k ψ j))) (Submodule.mkQ_surjective _)
      obtain ⟨t, rfl⟩ := (hex w).1 hw
      clear hw
      induction t using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy =>
        rw [map_add (f := _)]
        exact Submodule.add_mem _ hx hy
      | tmul v x =>
        obtain ⟨x, hx⟩ := x
        simp only [LinearMap.lTensor_tmul, Submodule.subtype_apply]
        induction hx using Submodule.span_induction with
        | zero => simp
        | add x y _ _ hx hy =>
          rw [TensorProduct.tmul_add]
          exact Submodule.add_mem _ hx hy
        | smul c x _ hx =>
          rw [TensorProduct.tmul_smul]
          exact Submodule.smul_mem _ c hx
        | mem x hx =>
          obtain ⟨n, w', rfl⟩ := hx
          obtain ⟨u, hh, e⟩ := GlobalTheory.T.exists_unipotent_lift_parabolic_proj k m j n
          obtain ⟨-, hv, hθ⟩ := GlobalTheory.T.parabolic_proj_unipotent_character_compat k ψ m j u hh
          refine Submodule.subset_span ⟨u, v ⊗ₜ w', ?_⟩
          have e2 : (⟨_, hv⟩ : MirUin k (j + 1)) = n := Subtype.ext (congrArg Prod.snd e)
          rw [e2] at hθ
          show _ = extTensor a b (gpProj k m (j + 1) ⟨u, hh⟩) (v ⊗ₜ w') - _
          rw [e, hθ, extTensor_tmul, TensorProduct.tmul_sub, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
          simp
    · intro hw
      induction hw using Submodule.span_induction with
      | zero => simp
      | add x y _ _ hx hy => rw [map_add (f := _), hx, hy, add_zero]
      | smul c x _ hx => rw [map_smul, hx, smul_zero]
      | mem x hx =>
        obtain ⟨u, y, rfl⟩ := hx
        obtain ⟨e1, hv, hθ⟩ := GlobalTheory.T.parabolic_proj_unipotent_character_compat k ψ m j u (hUH u.2)
        induction y using TensorProduct.induction_on with
        | zero => simp
        | add x y hx hy =>
          have := congrArg₂ (· + ·) hx hy
          simp only [add_zero, ← map_add (f := _)] at this
          rw [← this]
          congr 1
          simp only [map_add (f := _), smul_add]
          abel
        | tmul v w =>
          show q (extTensor a b (gpProj k m (j + 1) ⟨u, hUH u.2⟩) (v ⊗ₜ w) - _) = 0
          rw [extTensor_tmul, e1, ← hθ, map_one, Module.End.one_apply, map_sub, map_smul]
          simp only [q, LinearMap.lTensor_tmul]
          rw [← TensorProduct.tmul_smul, ← TensorProduct.tmul_sub, ← map_smul, ← map_sub]
          have : (twKer b (MirUin k (j + 1)) (mirChar k ψ j)).mkQ
              (b (gpProj k m (j + 1) ⟨u, hUH u.2⟩).2 w - (mirChar k ψ j ⟨_, hv⟩ : ℂ) • w) = 0 := by
            rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
            exact Submodule.subset_span ⟨⟨_, hv⟩, w, rfl⟩
          rw [this, TensorProduct.tmul_zero]
  refine coinv_cInd (MirabolicParabolic k m (j + 1)) (MirUin k (m + (j + 1))) hUH (GlobalTheory.T.mirabolic_unipotent_normal k _) (mirChar k ψ (m + j))
    (embedding₂ k (m + j)) (GlobalTheory.T.continuous_mirabolic_embedding k _) (levi_stab ψ (m + j)) (MirabolicParabolic k m j) (GlobalTheory.T.mem_parabolic_iff_mem_embedded k m j)
    ((extTensor a b).comp (gpProj k m (j + 1))) hsm ((extTensor a (phiMinus k ψ b)).comp (gpProj k m j)) q
    hqs hq hker ?_ (GlobalTheory.T.isClosed_parabolic_mul_embedded_mirabolic k m j) (GlobalTheory.T.embedded_small_neighbourhood_factor k m j) (GlobalTheory.CompanionTheory.BZMirOnto.exists_compactOpen k _) ?_
  · intro g
    rcases GlobalTheory.T.mirabolic_double_coset_dichotomy k ψ hψ1 m j g with h | ⟨u, hx, h1, h2⟩
    · exact Or.inl h
    · refine Or.inr ⟨u, hx, fun w => ?_, h2⟩
      simp [h1]
  · obtain ⟨K, hKo, hKc, -⟩ := GlobalTheory.CompanionTheory.BZMirOnto.exists_compactOpen k (m + j) Set.univ Filter.univ_mem
    exact ⟨K, hKo.mem_nhds (one_mem K), hKc⟩

end PhiProd

section Final

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def twistEquiv {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {ρ' : Representation ℂ G W} (e : ρ.Equiv ρ') (χ : G →* ℂˣ) :
    (GlobalTheory.SmGL.twist ρ χ).Equiv (GlobalTheory.SmGL.twist ρ' χ) :=
  Representation.Equiv.mk e.toLinearEquiv fun g => by
    refine LinearMap.ext fun v => ?_
    have h := LinearMap.congr_fun (e.isIntertwining' g) v
    show e.toLinearEquiv ((χ g : ℂ) • ρ g v) = (χ g : ℂ) • ρ' g (e.toLinearEquiv v)
    rw [map_smul]
    exact congrArg _ h

def extEquiv {G₁ G₂ M V V' W W' : Type} [Group G₁] [Group G₂] [Group M] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup V'] [Module ℂ V'] [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    {a : Representation ℂ G₁ V} {a' : Representation ℂ G₁ V'} {b : Representation ℂ G₂ W}
    {b' : Representation ℂ G₂ W'} (e : a.Equiv a') (f : b.Equiv b') (s : M →* G₁ × G₂) :
    Representation.Equiv ((extTensor a b).comp s) ((extTensor a' b').comp s) :=
  Representation.Equiv.mk (TensorProduct.congr e.toLinearEquiv f.toLinearEquiv) fun g => by
    refine TensorProduct.ext' fun v w => ?_
    have h1 := LinearMap.congr_fun (e.isIntertwining' (s g).1) v
    have h2 := LinearMap.congr_fun (f.isIntertwining' (s g).2) w
    show TensorProduct.congr e.toLinearEquiv f.toLinearEquiv (extTensor a b (s g) (v ⊗ₜ w)) =
      extTensor a' b' (s g) (TensorProduct.congr e.toLinearEquiv f.toLinearEquiv (v ⊗ₜ w))
    rw [extTensor_tmul, TensorProduct.congr_tmul, TensorProduct.congr_tmul, extTensor_tmul]
    exact congrArg₂ _ h1 h2

theorem isOpen_ker_dpowM (n : ℕ) (s : ℝ) :
    IsOpen (((dpowM (k := k) n s).ker : Subgroup (Mir k n)) : Set (Mir k n)) :=
  (isOpen_ker_dpow k (n + 1) s).preimage continuous_subtype_val

theorem prodGP_congr {m j : ℕ} {V V' W W' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
    [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    {a : Representation ℂ (GL (Fin m) k) V} {a' : Representation ℂ (GL (Fin m) k) V'}
    {c : Representation ℂ (Mir k j) W} {c' : Representation ℂ (Mir k j) W'} (e : a.Equiv a') (f : c.Equiv c') :
    Nonempty ((prodGP a c).Equiv (prodGP a' c')) :=
  GlobalTheory.T.compactInduction_congr_equiv (MirabolicParabolic k m j) _ _ (extEquiv e f (gpProj k m j))

theorem tw_rep {m j : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (a : Representation ℂ (GL (Fin m) k) V) (c : Representation ℂ (Mir k j) W) (r : ℝ) :
    GlobalTheory.SmGL.twist ((extTensor a c).comp (gpProj k m j)) ((dpowM (m + j) r).comp (MirabolicParabolic k m j).subtype) =
      (extTensor (GlobalTheory.SmGL.twist a (dpow m r)) (GlobalTheory.SmGL.twist c (dpowM j r))).comp (gpProj k m j) := by
  refine MonoidHom.ext fun h => LinearMap.ext fun x => ?_
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul v w =>
    show (dpowM (m + j) r (h : Mir k (m + j)) : ℂ) • extTensor a c (gpProj k m j h) (v ⊗ₜ w) =
      extTensor (GlobalTheory.SmGL.twist a (dpow m r)) (GlobalTheory.SmGL.twist c (dpowM j r)) (gpProj k m j h) (v ⊗ₜ w)
    rw [extTensor_tmul, extTensor_tmul, twist_apply, twist_apply, GlobalTheory.T.modulus_parabolic_proj_factor k m j r h, Units.val_mul,
      TensorProduct.smul_tmul_smul]

theorem cInd_of_eq {G W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup W] [Module ℂ W]
    (H : Subgroup G) {σ σ' : Representation ℂ H W} (h : σ = σ') : Nonempty ((cInd H σ).Equiv (cInd H σ')) := by
  subst h; exact ⟨Representation.Equiv.refl _⟩

theorem twist_prodGP {m j : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (a : Representation ℂ (GL (Fin m) k) V) (c : Representation ℂ (Mir k j) W) (r : ℝ) :
    Nonempty ((GlobalTheory.SmGL.twist (prodGP a c) (dpowM (m + j) r)).Equiv (prodGP (GlobalTheory.SmGL.twist a (dpow m r)) (GlobalTheory.SmGL.twist c (dpowM j r)))) := by
  have A2 := GlobalTheory.T.compactInduction_twist_equiv (MirabolicParabolic k m j) ((extTensor a c).comp (gpProj k m j)) (dpowM (m + j) r) (isOpen_ker_dpowM _ _)
  have B := cInd_of_eq (MirabolicParabolic k m j) (tw_rep a c r)
  obtain ⟨A2⟩ := A2
  obtain ⟨B⟩ := B
  have C := A2.trans B
  unfold prodGP
  exact ⟨C⟩

def eqvOfEq {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {ρ ρ' : Representation ℂ G V} (h : ρ = ρ') :
    ρ.Equiv ρ' := h ▸ Representation.Equiv.refl ρ

set_option synthInstance.maxHeartbeats 100000 in
theorem main_twisted (ψ : AddChar k Circle) (hψ1 : ψ ≠ 1) {m j : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (GL (Fin m) k) V)
    (τ : Representation ℂ (Mir k (j + 1)) W) (hρ : IsSmooth ρ) (hτ : IsSmooth τ) (s₀ s₁ t r : ℝ) (hs : r + s₀ = s₁) :
    Nonempty ((GlobalTheory.SmGL.twist (phiMinus k ψ (n := m + j) (prodGP (GlobalTheory.SmGL.twist ρ (dpow m s₀)) (GlobalTheory.SmGL.twist τ (dpowM (j + 1) t))))
      (dpowM (m + j) r)).Equiv
      (prodGP (GlobalTheory.SmGL.twist ρ (dpow m s₁)) (GlobalTheory.SmGL.twist (GlobalTheory.SmGL.twist (phiMinus k ψ τ) (dpowM j r)) (dpowM j t)))) := by
  have ha : IsSmooth (GlobalTheory.SmGL.twist ρ (dpow (k := k) m s₀)) := isSmooth_twist hρ (isOpen_ker_dpow k m s₀)
  have hb : IsSmooth (GlobalTheory.SmGL.twist τ (dpowM (k := k) (j + 1) t)) := isSmooth_twist hτ (isOpen_ker_dpowM _ _)
  have E0 := phiMinus_prodGP ψ hψ1 (GlobalTheory.SmGL.twist ρ (dpow (k := k) m s₀)) (GlobalTheory.SmGL.twist τ (dpowM (k := k) (j + 1) t)) ha hb
  have A2 := twist_prodGP (GlobalTheory.SmGL.twist ρ (dpow (k := k) m s₀)) (phiMinus k ψ (GlobalTheory.SmGL.twist τ (dpowM (k := k) (j + 1) t))) r
  obtain ⟨E0⟩ := E0
  obtain ⟨A2⟩ := A2
  have A4 : GlobalTheory.SmGL.twist (GlobalTheory.SmGL.twist ρ (dpow (k := k) m s₀)) (dpow m r) = GlobalTheory.SmGL.twist ρ (dpow m s₁) := by
    rw [twist_twist, ← dpow_add, hs]
  have E3 := GlobalTheory.T.derivative_functor_twist_equiv k ψ j W τ t
  obtain ⟨E3⟩ := E3
  have A5 : (GlobalTheory.SmGL.twist (GlobalTheory.SmGL.twist (phiMinus k ψ τ) (dpowM j t)) (dpowM j r)) =
      GlobalTheory.SmGL.twist (GlobalTheory.SmGL.twist (phiMinus k ψ τ) (dpowM j r)) (dpowM j t) := by
    rw [twist_twist, twist_twist, mul_comm]
  have E5 := (twistEquiv E3 (dpowM j r)).trans (eqvOfEq A5)
  have E7 := prodGP_congr (eqvOfEq A4) E5
  obtain ⟨E7⟩ := E7
  exact ⟨(twistEquiv E0 _).trans (A2.trans E7)⟩

end Final

theorem phiGP : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.RgGu.Leib.PhiGP k := by
  intro k _ _ _ _ ψ _ hψ1 m j ρ τ hρ hτ
  have X := main_twisted ψ hψ1 ρ.ρ τ.ρ hρ hτ (((j + 1 + 1 : ℕ) : ℝ) / 2) (((j + 1 : ℕ) : ℝ) / 2) (-((m : ℕ) : ℝ) / 2)
    (-1 / 2) (by push_cast; ring)
  unfold MIso
  have e : ∀ h : m + (j + 1) = m + j + 1, mcast h (prodGPn ρ τ) = prodGPn ρ τ := fun _ => rfl
  rw [e]
  unfold phiN prodGPn mtw MRep.phiM GRep.tw
  exact X

end GlobalTheory.CompanionTheory.LeibPhi

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PhiGpCommutationHoldsStatement
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.phi_gp_commutation_holds : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], PhiGP k := by
  first | exact @GlobalTheory.CompanionTheory.LeibPhi.phiGP | exact GlobalTheory.CompanionTheory.LeibPhi.phiGP | (intros; apply GlobalTheory.CompanionTheory.LeibPhi.phiGP <;> assumption)
end
