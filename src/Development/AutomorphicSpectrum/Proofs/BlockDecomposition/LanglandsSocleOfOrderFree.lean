module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductTransposeInverseDualReverse
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductIrreducibleFiniteLength
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TransportKeepsProductsCosocles
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfIsSmoothModerate
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnlinkedCommuteOfIrreducible
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsAutFunOfMemCusp
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityConcat
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviIrreducibleTensorDecomposition
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.ReadMod
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalComparisonInert
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LanglandsSocleOfOrderFree
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LanglandsSocleOfOrderFree
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos

namespace GlobalTheory.CompanionTheory.LSocle

section General

variable {G V W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem isSmooth_of_surjective {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (hρ : IsSmooth ρ)
    (f : ρ.IntertwiningMap σ) (hf : Function.Surjective f) : IsSmooth σ := by
  intro w
  obtain ⟨v, rfl⟩ := hf w
  let S : Subgroup G :=
    { carrier := {g | σ g (f v) = f v}
      one_mem' := by simp
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [map_mul, Module.End.mul_apply, hb, ha]
      inv_mem' := fun {a} ha => by
        simp only [Set.mem_setOf_eq] at ha ⊢
        have h1 : σ a⁻¹ (σ a (f v)) = f v := by
          rw [← Module.End.mul_apply, ← map_mul]; simp
        rwa [ha] at h1 }
  let T : Subgroup G :=
    { carrier := {g | ρ g v = v}
      one_mem' := by simp
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [map_mul, Module.End.mul_apply, hb, ha]
      inv_mem' := fun {a} ha => by
        simp only [Set.mem_setOf_eq] at ha ⊢
        have h1 : ρ a⁻¹ (ρ a v) = v := by
          rw [← Module.End.mul_apply, ← map_mul]; simp
        rwa [ha] at h1 }
  have hT : IsOpen (T : Set G) := hρ v
  have hTS : T ≤ S := fun g hg => by
    have hg' : ρ g v = v := hg
    show σ g (f v) = f v
    rw [← f.isIntertwining, hg']
  exact Subgroup.isOpen_mono hTS hT

end General

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem thetaW_surjective (N : ℕ) : Function.Surjective (thetaW k N) :=
  fun g => ⟨thetaW k N g, GlobalTheory.T.transpose_inverse_involution_apply N g⟩

theorem comp_thetaW_thetaW {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V) : (π.comp (thetaW k N)).comp (thetaW k N) = π :=
  MonoidHom.ext fun g => by
    show π (thetaW k N (thetaW k N g)) = π g
    rw [GlobalTheory.T.transpose_inverse_involution_apply N g]

theorem isCosocle_comp_thetaW {N : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {σ : Representation ℂ (GL (Fin N) k) W} {π : Representation ℂ (GL (Fin N) k) V}
    (h : IsCosocle σ (π.comp (thetaW k N))) : IsCosocle (σ.comp (thetaW k N)) π := by
  apply GlobalTheory.FieldTransport.isCosocle_of_comp (thetaW_surjective N)
  show IsCosocle ((σ.comp (thetaW k N)).comp (thetaW k N)) _
  rw [comp_thetaW_thetaW σ]
  exact h

theorem equiv_contra_comp_thetaW (hGK : GKLocal k) {N : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]
    (σ : Representation ℂ (GL (Fin N) k) W) (hs : IsSmooth (σ.comp (thetaW k N)))
    (hi : Representation.IsIrreducible (σ.comp (thetaW k N))) : Nonempty (σ.Equiv (contra (σ.comp (thetaW k N)))) := by
  have E := GlobalTheory.T.gelfand_kazhdan_contragredient hGK N (σ.comp (thetaW k N)) hs hi
  rwa [comp_thetaW_thetaW σ] at E

theorem prodIrr_congr {h N : ℕ} {x y : Fin h → IrrGL (k := k)} (e : x = y) (hx : ∑ a, (x a).1 = N)
    (hy : ∑ a, (y a).1 = N) : Nonempty ((prodIrr x hx).Equiv (prodIrr y hy)) := by
  subst e
  exact ⟨Representation.Equiv.refl _⟩


set_option maxHeartbeats 2000000 in
theorem isSocle_rev_of_isCosocle (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hGK : GKLocal k) {h N : ℕ}
    (x y : Fin h → IrrGL (k := k)) (hd0 : ∑ a, (x a).1 = N) (hd : ∑ a, ((x ∘ Fin.rev) a).1 = N) (hdy : ∑ a, (y a).1 = N)
    (e3 : (fun a => dualCl (y (Fin.rev a))) = x) (e6 : (fun a => dualCl (y a)) = x ∘ Fin.rev)
    {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V)
    (hc : IsCosocle π (prodIrr x hd0)) : IsSocle π (prodIrr (x ∘ Fin.rev) hd) := by
  obtain ⟨hd2, ⟨E2⟩⟩ := GlobalTheory.T.product_transpose_inverse_dual_reverse hA hGK y hdy
  obtain ⟨E3⟩ := prodIrr_congr e3 hd2 hd0
  have hc1 : IsCosocle π ((prodIrr y hdy).comp (thetaW k N)) :=
    hc.of_equiv (Representation.Equiv.refl _) (E2.trans E3).symm
  have hc2 : IsCosocle (π.comp (thetaW k N)) (prodIrr y hdy) := isCosocle_comp_thetaW hc1
  have hs : IsSmooth (π.comp (thetaW k N)) := by
    obtain ⟨-, f, hf, -⟩ := hc2
    exact isSmooth_of_surjective (isSmooth_prodIrr y hdy) f hf
  have hsoc := GlobalTheory.T.cosocle_contragredient_socle hA (π.comp (thetaW k N)) (prodIrr y hdy) (isSmooth_prodIrr y hdy)
    (GlobalTheory.T.product_irreducible_finite_length hA y hdy) hc2
  obtain ⟨E4⟩ := equiv_contra_comp_thetaW hGK π hs hc2.1
  obtain ⟨hd5, ⟨E5⟩⟩ := GlobalTheory.T.contragredient_product_irreducible hA y hdy
  obtain ⟨E6⟩ := prodIrr_congr e6 hd5 hd
  exact hsoc.of_equiv E4.symm (E5.trans E6)

theorem lSocleGL : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    GlobalTheory.Published.IrreducibleAdmissibleGL → GKLocal k → LOrderFree k → LSocleGL k := by
  intro k _ _ _ _ hA hGK hLO 𝔪 h N x hd hx V _ _ π hπ
  have hd0 : ∑ a, (x a).1 = N := by
    rw [← hd]
    exact (Equiv.sum_comp Fin.revPerm (fun a => (x a).1)).symm
  have hc := hLO 𝔪 h N x hd0 hx π hπ
  obtain ⟨hdy, -⟩ := GlobalTheory.T.contragredient_product_irreducible hA (x ∘ Fin.rev) hd
  exact isSocle_rev_of_isCosocle hA hGK x (fun a => dualCl ((x ∘ Fin.rev) a)) hd0 hd hdy
    (funext fun a => by
      simp only [Function.comp_apply, Fin.rev_rev]
      exact GlobalTheory.T.dual_class_involutive hA (x a))
    (funext fun a => GlobalTheory.T.dual_class_involutive hA (x (Fin.rev a))) π hc

end GlobalTheory.CompanionTheory.LSocle
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LanglandsSocleOfOrderFreeStatement
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.langlands_socle_of_order_free : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → GKLocal k → LOrderFree k → LSocleGL k := by
  first | exact @GlobalTheory.CompanionTheory.LSocle.lSocleGL | exact GlobalTheory.CompanionTheory.LSocle.lSocleGL | (intros; apply GlobalTheory.CompanionTheory.LSocle.lSocleGL <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EGPgTrueEqLastIff
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib Topology
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZRes

section Abstract

variable {G : Type} [Group G]

def dcos (Q P : Subgroup G) (x : G) : Set G := {g | ∃ q ∈ Q, ∃ p ∈ P, g = q * x * p}

def LocSec [TopologicalSpace G] (Q P : Subgroup G) (x : G) : Prop :=
  ∀ OQ ∈ 𝓝 (1 : G), ∀ OP ∈ 𝓝 (1 : G), ∃ O ∈ 𝓝 (1 : G), ∀ u ∈ O, x * u ∈ dcos Q P x →
    ∃ s ∈ Q, s ∈ OQ ∧ ∃ p ∈ P, p ∈ OP ∧ x * u = s * x * p

variable [TopologicalSpace G] [IsTopologicalGroup G]
  {W₁ W₂ : Type} [AddCommGroup W₁] [Module ℂ W₁] [AddCommGroup W₂] [Module ℂ W₂]

def resInd {Q P : Subgroup G} {x : G} (σ : Representation ℂ Q W₁) (H : Subgroup P)
    (hH : ∀ p : P, p ∈ H ↔ x * (p : G) * x⁻¹ ∈ Q) (τ : Representation ℂ H W₂) (E : W₁ ≃ₗ[ℂ] W₂)
    (hE : ∀ (h : H) (hq : x * ((h : P) : G) * x⁻¹ ∈ Q) (v : W₁), τ h (E v) = E (σ ⟨_, hq⟩ v)) :
    smoothPart (ind Q σ) →ₗ[ℂ] smoothPart (ind H τ) where
  toFun f := ⟨⟨fun p => E (f.1.1 (x * (p : G))), by
      intro h p
      have hq := (hH h).1 h.2
      have e : x * (((h * p : P)) : G) = (⟨_, hq⟩ : Q) * (x * (p : G)) := by
        simp [mul_assoc]
      show E (f.1.1 (x * (((h : P) * p : P) : G))) = τ h (E (f.1.1 (x * (p : G))))
      rw [hE h hq, show x * (((h : P) * p : P) : G) = ((⟨_, hq⟩ : Q) : G) * (x * (p : G)) from e]
      exact congrArg E (f.1.2 _ _)⟩, by
      have hf : IsOpen {g : G | ind Q σ g f.1 = f.1} := f.2
      have hopen : IsOpen {p : P | ind Q σ (p : G) f.1 = f.1} := hf.preimage continuous_subtype_val
      refine mem_smoothPart_of_nhds ?_
      filter_upwards [hopen.mem_nhds (by simp)] with p hp
      refine Subtype.ext (funext fun y => ?_)
      have := congrArg (fun F : indSpace Q σ => F.1 (x * (y : G))) hp
      show E (f.1.1 (x * ((y * p : P) : G))) = E (f.1.1 (x * (y : G)))
      rw [show x * ((y * p : P) : G) = x * (y : G) * (p : G) by simp [mul_assoc]]
      exact congrArg E this⟩
  map_add' a b := by
    refine Subtype.ext (Subtype.ext (funext fun p => ?_))
    exact map_add E _ _
  map_smul' c a := by
    refine Subtype.ext (Subtype.ext (funext fun p => ?_))
    exact map_smul E _ _

end Abstract

section Concrete

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def eGPg {m j n : ℕ} (h : m + j = n) : (Σ x, Two (Fin m) (Fin (j + 1)) x) ≃ Fin (n + 1) :=
  two (stdSum (by omega))

def HGPg {m j n : ℕ} (h : m + j = n) : Subgroup (Mir k n) := (parab k (eGPg h)).comap (Mir k n).subtype

def hgpInclg {m j n : ℕ} (h : m + j = n) : HGPg k h →* parab k (eGPg h) where
  toFun g := ⟨((g : Mir k n) : GL (Fin (n + 1)) k), g.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem hgpg_block_mem {m j n : ℕ} (h : m + j = n) (g : HGPg k h) :
    (leviProj k (eGPg h) (hgpInclg k h g) true : GL (Fin (j + 1)) k) ∈ Mir k j := by
  subst h
  exact hgp_block_mem _ _ g

def gpProjg {m j n : ℕ} (h : m + j = n) : HGPg k h →* GL (Fin m) k × Mir k j :=
  MonoidHom.prod ((Pi.evalMonoidHom (fun x => GL (Two (Fin m) (Fin (j + 1)) x) k) false).comp
      ((leviProj k (eGPg h)).comp (hgpInclg k h)))
    (((Pi.evalMonoidHom (fun x => GL (Two (Fin m) (Fin (j + 1)) x) k) true).comp
      ((leviProj k (eGPg h)).comp (hgpInclg k h))).codRestrict (Mir k j) (hgpg_block_mem k h))

def wPerm {i t : ℕ} (h : (i + 1) + t = i + t + 1) : Equiv.Perm (Fin (i + t + 1)) :=
  (two (stdSum h)).symm.trans (ePG i t)

def wGL {i t : ℕ} (h : (i + 1) + t = i + t + 1) : GL (Fin (i + t + 1)) k where
  val := (1 : Matrix _ _ k).submatrix (wPerm h) id
  inv := (1 : Matrix _ _ k).submatrix id (wPerm h)
  val_inv := by
    rw [← Matrix.submatrix_mul _ _ _ id _ Function.bijective_id, mul_one]
    exact Matrix.submatrix_one_equiv (wPerm h)
  inv_val := by
    rw [← Matrix.submatrix_mul _ _ _ (wPerm h) _ (wPerm h).bijective, mul_one]
    exact Matrix.submatrix_one_equiv (Equiv.refl _)

end Concrete

section Inducing

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

abbrev sQ {r t N : ℕ} (h : r + t = N) (π₁ : Representation ℂ (GL (Fin r) k) V)
    (π₂ : Representation ℂ (GL (Fin t) k) W) :
    Representation ℂ (parab k (two (stdSum h))) (⨂[ℂ] x, TwoT V W x) :=
  (GlobalTheory.SmGL.twist (piTensor (twoRep π₁ π₂)) (deltaHalf k (Two (Fin r) (Fin t)))).comp (leviProj k (two (stdSum h)))

abbrev tE (V W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] :
    (⨂[ℂ] x, TwoT V W x) ≃ₗ[ℂ] V ⊗[ℂ] W :=
  Exponents.boolTensorEquiv (X := TwoT V W)

end Inducing

section Row

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem det_updateRow_one {N : ℕ} (a : Fin N) (y : Fin N → k) :
    ((1 : Matrix (Fin N) (Fin N) k).updateRow a y).det = y a := by
  have h := Matrix.cramer_apply (1 : Matrix (Fin N) (Fin N) k) y a
  rw [Matrix.cramer_one] at h
  have e : ((1 : Matrix (Fin N) (Fin N) k).updateCol a y) = ((1 : Matrix (Fin N) (Fin N) k).updateRow a y)ᵀ := by
    rw [← Matrix.updateCol_transpose, Matrix.transpose_one]
  rw [e, Matrix.det_transpose] at h
  simpa using h.symm

theorem exists_rowSec {N : ℕ} (a : Fin N) : ∃ b : (Fin N → k) → GL (Fin N) k,
    ContinuousAt b (Pi.single a 1) ∧ b (Pi.single a 1) = 1 ∧
      ∀ y : Fin N → k, y a ≠ 0 → (b y : Matrix (Fin N) (Fin N) k) = (1 : Matrix (Fin N) (Fin N) k).updateRow a y := by
  classical
  let M : (Fin N → k) → Matrix (Fin N) (Fin N) k := fun y => (1 : Matrix (Fin N) (Fin N) k).updateRow a y
  have hM : Continuous M := by
    refine continuous_matrix fun c d => ?_
    by_cases h : c = a
    · subst h
      simpa [M] using continuous_apply d
    · simpa [M, Matrix.updateRow_ne h] using continuous_const
  have hdet : ∀ y, (M y).det = y a := fun y => det_updateRow_one a y
  let b : (Fin N → k) → GL (Fin N) k := fun y =>
    if h : y a ≠ 0 then Matrix.GeneralLinearGroup.mkOfDetNeZero (M y) (by rw [hdet]; exact h) else 1
  have hb : ∀ y : Fin N → k, y a ≠ 0 → (b y : Matrix (Fin N) (Fin N) k) = M y := fun y h => by
    simp only [b, dif_pos h]
    rfl
  have h0 : (Pi.single a 1 : Fin N → k) a ≠ 0 := by simp
  have hne : ∀ᶠ y : Fin N → k in 𝓝 (Pi.single a 1), y a ≠ 0 :=
    (continuous_apply a).continuousAt.eventually_ne h0
  refine ⟨b, ?_, ?_, hb⟩
  · rw [Units.isInducing_embedProduct.continuousAt_iff]
    have h1 : ContinuousAt (fun y => (b y : Matrix (Fin N) (Fin N) k)) (Pi.single a 1) :=
      hM.continuousAt.congr (hne.mono fun y h => (hb y h).symm)
    have h2 : ContinuousAt (fun y => (((b y)⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k)) (Pi.single a 1) := by
      have h3 : ContinuousAt (fun y : Fin N → k => (y a)⁻¹ • (M y).adjugate) (Pi.single a 1) :=
        ((continuous_apply a).continuousAt.inv₀ h0).smul hM.matrix_adjugate.continuousAt
      refine h3.congr (hne.mono fun y h => ?_)
      show (y a)⁻¹ • (M y).adjugate = (((b y)⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k)
      rw [Matrix.coe_units_inv, hb y h, Matrix.inv_def, hdet, Ring.inverse_eq_inv]
    exact h1.prodMk (MulOpposite.continuous_op.continuousAt.comp h2)
  · ext1
    rw [hb _ h0]
    show (1 : Matrix (Fin N) (Fin N) k).updateRow a (Pi.single a 1) = 1
    ext c d
    by_cases h : c = a
    · subst h
      simp [Matrix.one_apply, Pi.single_apply, eq_comm]
    · simp [Matrix.updateRow_ne h]

end Row

end GlobalTheory.CompanionTheory.BZRes

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsIrrRepInjective
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsIrrRepInjective
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir Zc

noncomputable section

namespace GlobalTheory.CompanionTheory.IrrSub

def subIncl {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
    (S : Subrepresentation ρ) : S.toRepresentation.IntertwiningMap ρ :=
  ⟨S.toSubmodule.subtype, fun _ => rfl⟩

theorem subIncl_injective {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ G V} (S : Subrepresentation ρ) : Function.Injective (subIncl S) :=
  Subtype.val_injective

theorem hasFiniteLength_of_isSubquotient {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ G W} {ρ : Representation ℂ G V}
    (h : IsSubquotient σ ρ) (hρ : HasFiniteLength ρ) : HasFiniteLength σ := by
  obtain ⟨T, f, hf⟩ := h
  exact GlobalTheory.JacquetBlocks.hasFiniteLength_of_surjective f hf
    (GlobalTheory.ProdLength.hasFiniteLength_of_injective (subIncl T) (subIncl_injective T) hρ)

theorem exists_isAtom {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ G V} [Nontrivial V] (h : HasFiniteLength ρ) :
    ∃ S : Subrepresentation ρ, IsAtom S := by
  have hbt : (⊤ : Subrepresentation ρ) ≠ ⊥ := by
    intro e
    obtain ⟨x, hx⟩ := exists_ne (0 : V)
    have hmem : x ∈ (⊤ : Subrepresentation ρ).toSubmodule := Submodule.mem_top
    rw [e] at hmem
    exact hx ((Submodule.mem_bot ℂ).1 hmem)
  obtain ⟨S, hS, -⟩ := GlobalTheory.CompanionTheory.JacExp.exists_atom_le h hbt
  exact ⟨S, hS⟩

theorem exists_irrRep_injective : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n : ℕ) (V W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (A : Representation ℂ (GL (Fin n) k) V) (A₀ : Representation ℂ (GL (Fin n) k) W),
    IsSmooth A → Nontrivial V → IsSubquotient A A₀ → HasFiniteLength A₀ →
    ∃ (S : IrrRep (GL (Fin n) k)) (f : S.ρ.IntertwiningMap A), Function.Injective f := by
  intro k _ _ _ _ n V W _ _ _ _ A A₀ hsm hnt hsub hfl
  obtain ⟨S, hS⟩ := exists_isAtom (hasFiniteLength_of_isSubquotient hsub hfl)
  exact ⟨⟨S.toSubmodule, S.toRepresentation, GlobalTheory.CompanionTheory.JacExp.isSmooth_sub hsm S,
    GlobalTheory.ClassFin.isIrreducible_toRepresentation_of_isAtom S hS⟩, subIncl S, subIncl_injective S⟩

end GlobalTheory.CompanionTheory.IrrSub
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsIrrRepInjectiveStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir Zc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_injective_irreducible_subrepresentation : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n : ℕ) (V W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (A : Representation ℂ (GL (Fin n) k) V) (A₀ : Representation ℂ (GL (Fin n) k) W),
    IsSmooth A → Nontrivial V → IsSubquotient A A₀ → HasFiniteLength A₀ →
    ∃ (S : IrrRep (GL (Fin n) k)) (f : S.ρ.IntertwiningMap A), Function.Injective f := by
  first | exact @GlobalTheory.CompanionTheory.IrrSub.exists_irrRep_injective | exact GlobalTheory.CompanionTheory.IrrSub.exists_irrRep_injective | (intros; apply GlobalTheory.CompanionTheory.IrrSub.exists_irrRep_injective <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConcatenatedJacquetMultiplicityFactorization
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConcatenatedJacquetMultiplicityFactorization
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg GlobalTheory.JacStages

namespace GlobalTheory.CompanionTheory.CoarseOcc

theorem nontrivial_of_isSubquotient {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (hσ : σ.IsIrreducible)
    (h : IsSubquotient σ ρ) : Nontrivial V := by
  obtain ⟨S, f, hf⟩ := h
  haveI : Nontrivial W := Model.nontrivial_of_isIrreducible hσ
  obtain ⟨u, hu⟩ := exists_ne (0 : W)
  obtain ⟨v, rfl⟩ := hf u
  refine ⟨(v : V), 0, fun h0 => hu ?_⟩
  have hv0 : v = 0 := Subtype.ext h0
  rw [hv0, map_zero]

theorem sum_concat {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {s : ℕ}
    (c : Fin s → ℕ) (x : ∀ a, Fin (c a) → IrrGL (k := k)) :
    ∑ i, (concat c x i).1 = ∑ a, ∑ i, (x a i).1 := by
  calc ∑ i, (concat c x i).1 = ∑ p : Σ a, Fin (c a), (x p.1 p.2).1 :=
        Fintype.sum_equiv finSigmaFinEquiv.symm _ _ fun _ => rfl
    _ = ∑ a, ∑ i, (x a i).1 := Fintype.sum_sigma _

theorem exists_one_le_jm_coarse : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {s N : ℕ} (c : Fin s → ℕ) (x : ∀ a, Fin (c a) → IrrGL (k := k)) (hpos : ∀ a, 0 < ∑ i, (x a i).1) (hcat : ∑ i, (concat c x i).1 = N) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) (hs : IsSmooth π) (hfl : HasFiniteLength π), 1 ≤ jm (concat c x) hcat π → ∃ (σ : Fin s → IrrGL (k := k)) (hσ : ∑ a, (σ a).1 = N), (∀ a, (σ a).1 = ∑ i, (x a i).1) ∧ 1 ≤ jm σ hσ π := by
  intro k _ _ _ _ hA s N c x _ hcat V _ _ π hs _ h1
  let d : Fin s → ℕ := fun a => ∑ i, (x a i).1
  have hd : ∑ a, d a = N := (sum_concat c x).symm.trans hcat
  let e := stdBlocks d hd
  let e' : ∀ a, (Σ b, Fin ((x a b).1)) ≃ Fin (d a) := fun a => stdBlocks (fun i => (x a i).1) rfl
  have hE : refinePlace e e' = stdBlocks (fun a => (concat c x a).1) hcat :=
    GlobalTheory.CompanionTheory.JmTrans.refinePlace_stdBlocks (x := fun a i => (x a i).1) hd (fun _ => rfl) hcat
  obtain ⟨φS⟩ := GlobalTheory.T.jacquetModule_in_stages_refined_blocks k s N d e c (fun a b => (x a b).1) e' V π
  have hsub : IsSubquotient (piTensor fun l => (concat c x l).rep) (GlobalTheory.SmGL.jac (refinePlace e e') π) := by
    rw [hE]
    exact jhMult_ne_zero_iff.1 (ENat.one_le_iff_ne_zero.1 h1)
  have hnt := nontrivial_of_isSubquotient (GlobalTheory.CompanionTheory.SocleJm.isIrreducible_piTensor hA (concat c x)) hsub
  have hnt2 := @Function.Surjective.nontrivial _ _ hnt _ φS.symm.surjective
  have hnt3 := @Function.Surjective.nontrivial _ _ hnt2 _
    (Submodule.Quotient.mk_surjective (twKer (GlobalTheory.SmGL.jac e π) (relUnipD k e') 1))
  obtain ⟨Y, _, _, τ, hτ, hτs⟩ := GlobalTheory.IrrSubquot.exists_irreducible_subquotient _ _ (GlobalTheory.SmGL.jac e π) hnt3
  let T : IrrRep (Levi k fun a => Fin (d a)) := ⟨Y, τ, hτs.isSmooth (isSmooth_jac e hs), hτ⟩
  obtain ⟨σ, ⟨φ⟩⟩ := GlobalTheory.CompanionTheory.LeviTensor.nonempty_equiv_piTensor hA d T
  refine ⟨fun a => ⟨d a, σ a⟩, hd, fun _ => rfl, ENat.one_le_iff_ne_zero.2 (jhMult_ne_zero_iff.2 ?_)⟩
  exact (isSubquotient_of_equiv φ.symm).trans hτs

end GlobalTheory.CompanionTheory.CoarseOcc

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConcatenatedJacquetMultiplicityFactorizationStatement
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.concatenated_jacquet_multiplicity_factorization : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {s N : ℕ} (c : Fin s → ℕ) (x : ∀ a, Fin (c a) → IrrGL (k := k)) (hpos : ∀ a, 0 < ∑ i, (x a i).1) (hcat : ∑ i, (concat c x i).1 = N) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) (hs : IsSmooth π) (hfl : HasFiniteLength π), 1 ≤ jm (concat c x) hcat π → ∃ (σ : Fin s → IrrGL (k := k)) (hσ : ∑ a, (σ a).1 = N), (∀ a, (σ a).1 = ∑ i, (x a i).1) ∧ 1 ≤ jm σ hσ π := by
  first | exact @GlobalTheory.CompanionTheory.CoarseOcc.exists_one_le_jm_coarse | exact GlobalTheory.CompanionTheory.CoarseOcc.exists_one_le_jm_coarse | (intros; apply GlobalTheory.CompanionTheory.CoarseOcc.exists_one_le_jm_coarse <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsIntZero
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.CtS

def IsInt {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) {r s : Type}
    (M : Matrix r s (w.adicCompletion E)) : Prop :=
  ∀ i j, M i j ∈ Ov E w

def coef (q : ℕ) (c : ℂˣ) (a b i j : ℕ) : ℂ :=
  (c : ℂ) ^ (i * b + j * a) * (q : ℂ) ^ (((i : ℂ) * b + (j : ℂ) * a) / 2 - (i : ℂ) * j)

def pairs (a b k : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.HasAntidiagonal.antidiagonal k).filter fun p => p.1 ≤ a ∧ p.2 ≤ b

theorem mem_pairs {a b k : ℕ} {p : ℕ × ℕ} : p ∈ pairs a b k ↔ p.1 + p.2 = k ∧ p.1 ≤ a ∧ p.2 ≤ b := by
  simp [pairs, Finset.mem_filter]

theorem IsInt.add {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {r s : Type}
    {M N : Matrix r s (w.adicCompletion E)} (hM : IsInt w M) (hN : IsInt w N) : IsInt w (M + N) :=
  fun i j => (Ov E w).add_mem (hM i j) (hN i j)

theorem IsInt.neg {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {r s : Type}
    {M : Matrix r s (w.adicCompletion E)} (hM : IsInt w M) : IsInt w (-M) :=
  fun i j => (Ov E w).neg_mem (hM i j)

theorem isInt_zero {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (r s : Type) :
    IsInt w (0 : Matrix r s (w.adicCompletion E)) :=
  fun _ _ => (Ov E w).zero_mem

def intSub {E : Type} [Field E] [NumberField E] (a b : ℕ) (w : HeightOneSpectrum (𝓞 E)) :
    AddSubgroup (Matrix (Fin a) (Fin b) (w.adicCompletion E)) where
  carrier := {X | IsInt w X}
  zero_mem' := isInt_zero w _ _
  add_mem' := fun h h' => h.add h'
  neg_mem' := fun h => h.neg

def latM {E : Type} [Field E] [NumberField E] {a b : ℕ} {w : HeightOneSpectrum (𝓞 E)} (ϖ : w.adicCompletion E)
    (m : GL (Fin a) (w.adicCompletion E) × GL (Fin b) (w.adicCompletion E)) :
    AddSubgroup (Matrix (Fin a) (Fin b) (w.adicCompletion E)) where
  carrier := {X | IsInt w (m.1.val * X) ∧ IsInt w (ϖ • (X * (m.2⁻¹).val))}
  zero_mem' := by
    refine ⟨?_, ?_⟩ <;> simpa using isInt_zero w _ _
  add_mem' := by
    rintro X Y ⟨h1, h2⟩ ⟨h3, h4⟩
    refine ⟨?_, ?_⟩
    · rw [Matrix.mul_add]; exact h1.add h3
    · rw [Matrix.add_mul, smul_add]; exact h2.add h4
  neg_mem' := by
    rintro X ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · rw [Matrix.mul_neg]; exact h1.neg
    · rw [Matrix.neg_mul, smul_neg]; exact h2.neg

def latD {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} (ϖ : w.adicCompletion E) (a b i j : ℕ) :
    AddSubgroup (Matrix (Fin a) (Fin b) (w.adicCompletion E)) where
  carrier := {W | ∀ (r : Fin a) (s : Fin b), (if (r : ℕ) < i ∧ j ≤ (s : ℕ) then ϖ * W r s else W r s) ∈ Ov E w}
  zero_mem' := by
    intro r s
    simp only [Matrix.zero_apply, mul_zero, ite_self]
    exact (Ov E w).zero_mem
  add_mem' := by
    intro X Y h1 h2 r s
    have e1 := h1 r s
    have e2 := h2 r s
    simp only [Matrix.add_apply]
    split_ifs at e1 e2 ⊢
    · rw [mul_add]; exact (Ov E w).add_mem e1 e2
    · exact (Ov E w).add_mem e1 e2
  neg_mem' := by
    intro X h1 r s
    have e1 := h1 r s
    simp only [Matrix.neg_apply]
    split_ifs at e1 ⊢
    · rw [mul_neg]; exact (Ov E w).neg_mem e1
    · exact (Ov E w).neg_mem e1

end GlobalTheory.CompanionTheory.CtS
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentRepSplitIntertwiner
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosocleSurjectionFactor
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosocleSurjectionFactor
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg

namespace GlobalTheory.CompanionTheory.Segments

theorem exists_coatom_ge_of_hasFiniteLength {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    {P : Representation ℂ G V} (hfl : HasFiniteLength P) (S : Subrepresentation P) (hS : S ≠ ⊤) :
    ∃ C : Subrepresentation P, IsCoatom C ∧ S ≤ C := by
  obtain ⟨hN, -⟩ := isFiniteLength_iff_isNoetherian_isArtinian.1 hfl
  have : IsCoatomic (Submodule (MonoidAlgebra ℂ G) P.asModule) := inferInstance
  have hc : IsCoatomic (Subrepresentation P) :=
    (Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := P)).isCoatomic_iff.2 this
  obtain h | ⟨C, hC, hle⟩ := hc.eq_top_or_exists_le_coatom S
  · exact absurd h hS
  · exact ⟨C, hC, hle⟩

theorem cosocle_quotient_of_quotient : ∀ {G V W X : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] [AddCommGroup X] [Module ℂ X] (σ : Representation ℂ G W) (P : Representation ℂ G V)
    (Q : Representation ℂ G X) (hc : IsCosocle σ P) (hfl : HasFiniteLength P) (f : P.IntertwiningMap Q)
    (hf : Function.Surjective f) (hQ : Nontrivial X), ∃ g : Q.IntertwiningMap σ, Function.Surjective g := by
  intro G V W X _ _ _ _ _ _ _ σ P Q hc hfl f hf hQ
  obtain ⟨-, f0, hf0, hco⟩ := hc
  have hne : Representation.IntertwiningMap.ker P Q f ≠ ⊤ := by
    intro h
    obtain ⟨x, hx⟩ := exists_ne (0 : X)
    obtain ⟨v, rfl⟩ := hf x
    have hv : v ∈ (⊤ : Subrepresentation P) := trivial
    rw [← h] at hv
    exact hx hv
  obtain ⟨C, hC, hle⟩ := exists_coatom_ge_of_hasFiniteLength hfl _ hne
  have hk : ∀ v : V, f v = 0 → f0 v = 0 := by
    intro v hv
    have h1 : v ∈ Representation.IntertwiningMap.ker P Q f := hv
    have h2 : v ∈ C := hle h1
    rw [hco C hC] at h2
    exact h2
  let e := LinearMap.quotKerEquivOfSurjective f.toLinearMap hf
  let gl : X →ₗ[ℂ] W :=
    (LinearMap.ker f.toLinearMap).liftQ f0.toLinearMap (fun v hv => hk v hv) ∘ₗ e.symm.toLinearMap
  have hgl : ∀ v : V, gl (f v) = f0 v := by
    intro v
    have h1 : e.symm (f v) = Submodule.Quotient.mk v := by
      rw [LinearEquiv.symm_apply_eq]
      rfl
    simp only [gl, LinearMap.comp_apply, LinearEquiv.coe_coe, h1, Submodule.liftQ_apply]
    rfl
  refine ⟨⟨gl, fun h => ?_⟩, ?_⟩
  · refine LinearMap.ext fun x => ?_
    obtain ⟨v, rfl⟩ := hf x
    have h2 : Q h (f v) = f (P h v) := by
      have := congrArg (fun m => m v) (f.isIntertwining' h)
      exact this.symm
    have h3 : f0 (P h v) = σ h (f0 v) := congrArg (fun m => m v) (f0.isIntertwining' h)
    simp only [LinearMap.comp_apply]
    rw [h2, hgl, hgl, h3]
  · intro w
    obtain ⟨v, rfl⟩ := hf0 w
    exact ⟨f v, hgl v⟩

end GlobalTheory.CompanionTheory.Segments
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosocleSurjectionFactorStatement
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cosocle_surjection_factor : ∀ {G V W X : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [AddCommGroup X] [Module ℂ X] (σ : Representation ℂ G W) (P : Representation ℂ G V) (Q : Representation ℂ G X) (hc : IsCosocle σ P) (hfl : HasFiniteLength P) (f : P.IntertwiningMap Q) (hf : Function.Surjective f) (hQ : Nontrivial X), ∃ g : Q.IntertwiningMap σ, Function.Surjective g := by
  first | exact @GlobalTheory.CompanionTheory.Segments.cosocle_quotient_of_quotient | exact GlobalTheory.CompanionTheory.Segments.cosocle_quotient_of_quotient | (intros; apply GlobalTheory.CompanionTheory.Segments.cosocle_quotient_of_quotient <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentRepSplitIntertwiner
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg

namespace GlobalTheory.CompanionTheory.SegQuotTwo

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem parIndMap_surjective {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)]
    [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n) {V W : Type} [AddCommGroup V]
    [Module ℂ V] [AddCommGroup W] [Module ℂ W] {ρ : Representation ℂ (Levi k m) V}
    {ρ' : Representation ℂ (Levi k m) W} (f : ρ.IntertwiningMap ρ') (hρ : IsSmooth ρ)
    (hf : Function.Surjective f) : Function.Surjective (parIndMap e f) := by
  obtain ⟨-, -, -, -, -, hcont, hP, -, hPK⟩ := GlobalTheory.SmGL.LeviInt.levi_integral_facts k α n m e
  obtain ⟨_, _⟩ := SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  let σ₀ : Representation ℂ (parab k e) V := (GlobalTheory.SmGL.twist ρ (deltaHalf k m)).comp (leviProj k e)
  let z : Representation.IntertwiningMap σ₀ σ₀ :=
    { toLinearMap := 0, isIntertwining' := fun _ => by ext; simp }
  refine (GlobalTheory.SmGL.IndCoinv.smInd_coinvariants (GL n k) (parab k e) (KO k n) hP SplitFlip.isCompact_KO
    hPK (GlobalTheory.SmGL.exists_open_normalised_subgroup_subset k n) _ _ _ _
    (isSmooth_comp (isSmooth_twist hρ (isSmoothChar_deltaHalf k)) _ hcont)
    (compMap (twistMap f _) _) Unit (fun _ => z) hf ?_).1
  intro x _
  refine Submodule.subset_span ⟨(), -x, ?_⟩
  show x = (0 : _) - -x
  simp

theorem prod₂_map_surjective {r t : ℕ} {U U' W W' : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup U'] [Module ℂ U']
    [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W'] {σ : Representation ℂ (GL (Fin r) k) U}
    {σ' : Representation ℂ (GL (Fin r) k) U'} {ρ : Representation ℂ (GL (Fin t) k) W}
    {ρ' : Representation ℂ (GL (Fin t) k) W'} (hσ : IsSmooth σ) (hρ : IsSmooth ρ) (f : σ.IntertwiningMap σ')
    (g : ρ.IntertwiningMap ρ') (hf : Function.Surjective f) (hg : Function.Surjective g) :
    ∃ F : (prod₂ σ ρ).IntertwiningMap (prod₂ σ' ρ'), Function.Surjective F := by
  have hσ' : IsSmooth σ' := (IsSubquotient.of_surjective f hf).isSmooth hσ
  have hc : Continuous fun h : Levi k (Two (Fin r) (Fin t)) => (h false, h true) :=
    (continuous_apply false).prodMk (continuous_apply true)
  have h1 : Function.Surjective (GlobalTheory.ParIndExact.extTensorMapLeft ρ f) := LinearMap.rTensor_surjective W hf
  have h2 : Function.Surjective (GlobalTheory.ParIndExact.extTensorMapRight σ' g) := LinearMap.lTensor_surjective U' hg
  have h1' : Function.Surjective (compMap (GlobalTheory.ParIndExact.extTensorMapLeft ρ f)
      (leviTwo k (Fin r) (Fin t)).symm.toMonoidHom) := h1
  have h2' : Function.Surjective (compMap (GlobalTheory.ParIndExact.extTensorMapRight σ' g)
      (leviTwo k (Fin r) (Fin t)).symm.toMonoidHom) := h2
  have s1 := parIndMap_surjective (two (stdSum (rfl : r + t = r + t))) _
    (isSmooth_comp (isSmooth_extTensor hσ hρ) _ hc) h1'
  have s2 := parIndMap_surjective (two (stdSum (rfl : r + t = r + t))) _
    (isSmooth_comp (isSmooth_extTensor hσ' hρ) _ hc) h2'
  exact ⟨(parIndMap (two (stdSum (rfl : r + t = r + t))) (compMap (GlobalTheory.ParIndExact.extTensorMapRight σ' g)
      (leviTwo k (Fin r) (Fin t)).symm.toMonoidHom)).comp (parIndMap (two (stdSum (rfl : r + t = r + t)))
      (compMap (GlobalTheory.ParIndExact.extTensorMapLeft ρ f) (leviTwo k (Fin r) (Fin t)).symm.toMonoidHom)), s2.comp s1⟩

theorem nonempty_prodIrr_equiv_of_cast {c c' N : ℕ} (h : c = c') (x : Fin c → IrrGL (k := k)) (x' : Fin c' → IrrGL (k := k))
    (hx : ∀ i, x i = x' (Fin.cast h i)) (hd : ∑ a, (x a).1 = N) (hd' : ∑ a, (x' a).1 = N) :
    Nonempty ((prodIrr x hd).Equiv (prodIrr x' hd')) := by
  subst h
  obtain rfl : x = x' := funext fun i => by simpa using hx i
  exact ⟨.refl _⟩

theorem append_term (Δ : Segment k) (a : ℕ) (h0 : 0 < a) (h1 : a < Δ.len)
    (hlen : (segLow Δ a h0).len + (segHigh Δ a h1).len = Δ.len)
    (i : Fin ((segLow Δ a h0).len + (segHigh Δ a h1).len)) :
    Fin.append (segLow Δ a h0).term (segHigh Δ a h1).term i = Δ.term (Fin.cast hlen i) := by
  induction i using Fin.addCases with
  | left i =>
    rw [Fin.append_left]
    rfl
  | right j =>
    rw [Fin.append_right]
    show (Δ.first.nu ((a : ℕ) : ℂ)).nu ((j : ℕ) : ℂ) = Δ.first.nu (((segLow Δ a h0).len + (j : ℕ) : ℕ) : ℂ)
    rw [IrrGL.nu_nu]
    show _ = Δ.first.nu ((a + (j : ℕ) : ℕ) : ℂ)
    push_cast
    rfl

theorem hasFiniteLength_prodIrr (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {h N : ℕ} (x : Fin h → IrrGL (k := k))
    (hd : ∑ a, (x a).1 = N) : HasFiniteLength (prodIrr x hd) :=
  GlobalTheory.CompanionTheory.BZInd.inductionFiniteLength k _ _ _ _ _ _ (isSmooth_piTensor fun a => (x a).2.rep.smooth)
    (hasFiniteLength_of_isIrreducible (GlobalTheory.CompanionTheory.SocleJm.isIrreducible_piTensor hA x))

theorem nontrivial_prodIrr (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {h N : ℕ} (x : Fin h → IrrGL (k := k))
    (hd : ∑ a, (x a).1 = N) : Nontrivial (IndSp (stdBlocks (fun a => (x a).1) hd) (piTensor fun a => (x a).rep)) :=
  GlobalTheory.CompanionTheory.SocleJm.nontrivial_indSp _ (GlobalTheory.CompanionTheory.SocleJm.isIrreducible_piTensor hA x)
    (isSmooth_piTensor fun a => (x a).2.rep.smooth)

theorem exists_surjective_of_equiv {G A B C D : Type} [Group G] [AddCommGroup A] [Module ℂ A] [AddCommGroup B]
    [Module ℂ B] [AddCommGroup C] [Module ℂ C] [AddCommGroup D] [Module ℂ D] {α : Representation ℂ G A}
    {β : Representation ℂ G B} {γ : Representation ℂ G C} {δ : Representation ℂ G D} (E : Nonempty (β.Equiv α))
    (F : ∃ f : β.IntertwiningMap γ, Function.Surjective f) (H : Nonempty (γ.Equiv δ)) :
    ∃ f : α.IntertwiningMap δ, Function.Surjective f := by
  obtain ⟨E⟩ := E
  obtain ⟨F, hF⟩ := F
  obtain ⟨H⟩ := H
  exact ⟨H.toIntertwiningMap.comp (F.comp E.symm.toIntertwiningMap),
    H.toLinearEquiv.surjective.comp (hF.comp E.symm.toLinearEquiv.surjective)⟩

theorem exists_surjective_of_prod₂_equiv {r t : ℕ} {U U' W W' A D : Type} [AddCommGroup U] [Module ℂ U]
    [AddCommGroup U'] [Module ℂ U'] [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W'] [AddCommGroup A]
    [Module ℂ A] [AddCommGroup D] [Module ℂ D] {σ : Representation ℂ (GL (Fin r) k) U}
    {σ' : Representation ℂ (GL (Fin r) k) U'} {ρ : Representation ℂ (GL (Fin t) k) W}
    {ρ' : Representation ℂ (GL (Fin t) k) W'} {α : Representation ℂ (GL (Fin (r + t)) k) A}
    {δ : Representation ℂ (GL (Fin (r + t)) k) D} (hσ : IsSmooth σ) (hρ : IsSmooth ρ) (f : σ.IntertwiningMap σ')
    (g : ρ.IntertwiningMap ρ') (hf : Function.Surjective f) (hg : Function.Surjective g)
    (E : Nonempty ((prod₂ σ ρ).Equiv α)) (H : Nonempty ((prod₂ σ' ρ').Equiv δ)) :
    ∃ F : α.IntertwiningMap δ, Function.Surjective F :=
  exists_surjective_of_equiv E (prod₂_map_surjective hσ hρ f g hf hg) H

theorem exists_surjective_append {p q : ℕ} (x : Fin p → IrrGL (k := k)) (y : Fin q → IrrGL (k := k)) (u v : IrrGL (k := k))
    (hx : ∑ a, (x a).1 = u.1) (hy : ∑ a, (y a).1 = v.1) (h : ∑ a, (Fin.append x y a).1 = u.1 + v.1)
    (hd : ∑ i, (![u, v] i).1 = u.1 + v.1)
    (fu : (prodIrr x hx).IntertwiningMap u.rep) (hfu : Function.Surjective fu)
    (fv : (prodIrr y hy).IntertwiningMap v.rep) (hfv : Function.Surjective fv) :
    ∃ F : (prodIrr (Fin.append x y) h).IntertwiningMap (prodIrr ![u, v] hd), Function.Surjective F :=
  exists_surjective_of_prod₂_equiv (isSmooth_prodIrr x hx) (isSmooth_prodIrr y hy) fu fv hfu hfv
    (GlobalTheory.T.product_irreducible_append_equiv k p q u.1 v.1 x y hx hy h) (nonempty_prod₂_equiv_prodIrr_pair u v hd)

theorem quotient_of_quotient {G V W X : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup X] [Module ℂ X] (σ : Representation ℂ G W) (P : Representation ℂ G V) (Q : Representation ℂ G X)
    (hc : IsCosocle σ P) (hfl : HasFiniteLength P) (hf : ∃ f : P.IntertwiningMap Q, Function.Surjective f)
    (hQ : Nontrivial X) : ∃ g : Q.IntertwiningMap σ, Function.Surjective g := by
  obtain ⟨f, hf⟩ := hf
  exact GlobalTheory.T.cosocle_surjection_factor σ P Q hc hfl f hf hQ

theorem quottwo : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Δ : Segment k) {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V) (hπ : IsLSeg Δ π) (a : ℕ) (h0 : 0 < a) (h1 : a < Δ.len) (u v : IrrGL (k := k))
    (hu : IsLSeg (segLow Δ a h0) u.rep) (hv : IsLSeg (segHigh Δ a h1) v.rep) (hd : ∑ i, (![u, v] i).1 = N),
    ∃ f : (prodIrr ![u, v] hd).IntertwiningMap π, Function.Surjective f := by
  intro k _ _ _ _ hA Δ N V _ _ π hπ a h0 h1 u v hu hv hd
  have hN : u.1 + v.1 = N := hd.symm ▸ (Fin.sum_univ_two (fun i => (![u, v] i).1)).symm
  subst hN
  obtain ⟨hx, -, fu, hfu, -⟩ := hu
  obtain ⟨hy, -, fv, hfv, -⟩ := hv
  obtain ⟨hΔ, hc⟩ := hπ
  have hlen : (segLow Δ a h0).len + (segHigh Δ a h1).len = Δ.len := by
    show a + (Δ.len - a) = Δ.len
    omega
  have hsum : ∑ i, (Fin.append (segLow Δ a h0).term (segHigh Δ a h1).term i).1 = u.1 + v.1 := by
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    exact congrArg₂ (· + ·) hx hy
  exact quotient_of_quotient π _ _ hc (hasFiniteLength_prodIrr hA _ hΔ)
    (exists_surjective_of_equiv (nonempty_prodIrr_equiv_of_cast hlen _ Δ.term (append_term Δ a h0 h1 hlen) hsum hΔ)
      (exists_surjective_append _ _ u v hx hy hsum hd fu hfu fv hfv) ⟨.refl _⟩) (nontrivial_prodIrr hA _ hd)

end GlobalTheory.CompanionTheory.SegQuotTwo

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentRepSplitIntertwinerStatement
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.segment_rep_split_intertwiner : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Δ : Segment k) {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) (hπ : IsLSeg Δ π) (a : ℕ) (h0 : 0 < a) (h1 : a < Δ.len) (u v : IrrGL (k := k)) (hu : IsLSeg (segLow Δ a h0) u.rep) (hv : IsLSeg (segHigh Δ a h1) v.rep) (hd : ∑ i, (![u, v] i).1 = N), ∃ f : (prodIrr ![u, v] hd).IntertwiningMap π, Function.Surjective f := by
  first | exact @GlobalTheory.CompanionTheory.SegQuotTwo.quottwo | exact GlobalTheory.CompanionTheory.SegQuotTwo.quottwo | (intros; apply GlobalTheory.CompanionTheory.SegQuotTwo.quottwo <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SupportSubschemeEmbedding
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SupportSubschemeEmbedding
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult GlobalTheory.SmGL.Exponents

namespace GlobalTheory.CompanionTheory.SubEmb

theorem subEmbedding : Ysupp.SubEmbedding :=
  subEmbedding_of_stage GlobalTheory.T.product_irreducible_append_equiv

end GlobalTheory.CompanionTheory.SubEmb
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SupportSubschemeEmbeddingStatement
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult GlobalTheory.SmGL.Exponents
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.support_subscheme_embedding : Ysupp.SubEmbedding := by
  first | exact @GlobalTheory.CompanionTheory.SubEmb.subEmbedding | exact GlobalTheory.CompanionTheory.SubEmb.subEmbedding | (intros; apply GlobalTheory.CompanionTheory.SubEmb.subEmbedding <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RatiosEqOfSameOrbit
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit segre fibre IsGoodProj IsSheet HermLine IsSmoothHerm sheetDensity maDensity ptsIntegral ptsIntegralAt pot)
open ReciprocityTheory.ChartRestriction.G.AI.I2 (IsRatSectionOn logNormRat)

noncomputable section

namespace GlobalTheory.CompanionTheory.MixZ.ArchEq

variable {m : ℕ} {n : Fin (m + 1) → ℕ} {D : ℕ}

abbrev Over {X : Scheme.{0}} (i : X ⟶ MP ℤ m n) (y : GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀)
    (z : (Σ k, Bk n k) → ℂ) : Prop :=
  IsUnder (PtsOver.map i rfl _ y) z

abbrev LinProj (n : Fin (m + 1) → ℕ) (D : ℕ) := (((k : Fin (m + 1)) → Bk n k) → ℂ) →ₗ[ℂ] (Fin (D + 1) → ℂ)

def ratios (Ψ : LinProj n D) (z : (Σ k, Bk n k) → ℂ) : Fin D → ℂ :=
  fun a => Ψ (segre z) a.succ / Ψ (segre z) 0


open Classical in
def liftOf {X : Scheme.{0}} (i : X ⟶ MP ℤ m n) (y : GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀) : (Σ k, Bk n k) → ℂ :=
  if h : ∃ z, Over i y z then h.choose else 0

def projCoord {X : Scheme.{0}} (i : X ⟶ MP ℤ m n) (Ψ : LinProj n D) (y : GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀) :
    Fin D → ℂ :=
  ratios Ψ (liftOf i y)

def IsRegAt {X : Scheme.{0}} (i : X ⟶ MP ℤ m n) (Ψ : LinProj n D) (c : GlobalTheory.AlgChart (i ≫ mpStr ℤ m n) σ₀ D)
    (y : GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀) : Prop :=
  LinearMap.det (fderiv ℂ (projCoord i Ψ ∘ c.finChart.symm) (c.finChart y) :
    (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ)) ≠ 0

def IsPiece {X : Scheme.{0}} [IsIntegral X] (i : X ⟶ MP ℤ m n) (Ψ : LinProj n D) (N : Pol n)
    (e : OpenPartialHomeomorph (GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀) (Fin D → ℂ))
    (Γ : (Fin D → ℂ) → (Σ k, Bk n k) → ℂ) : Prop :=
  (∃ c : GlobalTheory.AlgChart (i ≫ mpStr ℤ m n) σ₀ D, e.source ⊆ c.e.source) ∧ DifferentiableOn ℂ Γ e.target ∧
    ∀ v ∈ e.target, Over i (e.symm v) (Γ v) ∧ Γ v ∈ mcPts (ptIdeal (i (genericPoint X))) ∧
      Ψ (segre (Γ v)) = Fin.cons 1 v ∧ eval (Γ v) (map (Int.castRingHom ℂ) N) ≠ 0

def pieceSet {X : Scheme.{0}} [IsIntegral X] (i : X ⟶ MP ℤ m n) (Ψ : LinProj n D) (N : Pol n) :
    Set (GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀) :=
  {y | ∃ e Γ, IsPiece i Ψ N e Γ ∧ y ∈ e.source}

theorem isOpen_pieceSet {X : Scheme.{0}} [IsIntegral X] (i : X ⟶ MP ℤ m n) (Ψ : LinProj n D) (N : Pol n) :
    IsOpen (pieceSet i Ψ N) := isOpen_iff_forall_mem_open.mpr fun _ ⟨e, Γ, hp, hy⟩ =>
  ⟨e.source, fun _ hy' => ⟨e, Γ, hp, hy'⟩, e.open_source, hy⟩

theorem segre_orbit {z z' : (Σ k, Bk n k) → ℂ} {c : Fin (m + 1) → ℂ} (h : z = fun p => c p.1 * z' p) :
    segre z = (∏ k, c k) • segre z' := by
  subst h
  funext a
  simp [ReciprocityTheory.ChartRestriction.G.Geo.segre, Finset.prod_mul_distrib]

theorem ratios_eq_of_sameOrbit (Ψ : LinProj n D) {z z' : (Σ k, Bk n k) → ℂ} (h : SameOrbit z z')
    (h0 : Ψ (segre z') 0 ≠ 0) : ratios Ψ z = ratios Ψ z' := by
  obtain ⟨c, hc, rfl⟩ := h
  have hprod : (∏ k, c k) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hc k
  funext a
  simp only [ratios, segre_orbit (c := c) rfl, map_smul, Pi.smul_apply, smul_eq_mul]
  exact mul_div_mul_left _ _ hprod

theorem ratios_of_proj (Ψ : LinProj n D) {z : (Σ k, Bk n k) → ℂ} {v : Fin D → ℂ}
    (h : Ψ (segre z) = Fin.cons 1 v) : ratios Ψ z = v := by
  funext a
  simp [ratios, h]

theorem homog_mul {f g : Pol n} {a b : Fin (m + 1) → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g b) :
    IsMultiHomog (f * g) (a + b) := by
  classical
  intro d hd k
  obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_add.1 (MvPolynomial.support_mul f g hd)
  simp only [Finsupp.add_apply, Finset.sum_add_distrib, hf x hx k, hg y hy k, Pi.add_apply]

end GlobalTheory.CompanionTheory.MixZ.ArchEq
end
end
