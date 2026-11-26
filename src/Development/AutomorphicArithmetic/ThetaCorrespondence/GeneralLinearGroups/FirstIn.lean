module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.CasselmanSuffTemp

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.FirstIn
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult UpperTheory.Lit.Cas

namespace UpperTheory.Lit.Red

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def FirstIn (x : IrrGL (k := k)) (P : Set (IrrGL (k := k))) : Prop :=
  ∀ (q : Fin 2 → IrrGL (k := k)) (hq : ∑ a, (q a).1 = x.1), (q 0).IsCusp → jm q hq x.rep ≠ 0 → q 0 ∈ P

def LastIn (x : IrrGL (k := k)) (P : Set (IrrGL (k := k))) : Prop :=
  ∀ (q : Fin 2 → IrrGL (k := k)) (hq : ∑ a, (q a).1 = x.1), (q 1).IsCusp → jm q hq x.rep ≠ 0 → q 1 ∈ P

def SuppIn (x : IrrGL (k := k)) (P : Set (IrrGL (k := k))) : Prop :=
  ∃ A : Multiset (IrrGL (k := k)), HasSupport x.rep A ∧ ∀ y ∈ A, y ∈ P

def Emb (x y z : IrrGL (k := k)) : Prop :=
  ∃ (hd : ∑ a, (![y, z] a).1 = x.1) (f : x.rep.IntertwiningMap (prodIrr ![y, z] hd)), Function.Injective f

def Occ (x y z : IrrGL (k := k)) : Prop :=
  ∃ hd : ∑ a, (![y, z] a).1 = x.1, jhMult x.rep (prodIrr ![y, z] hd) ≠ 0

def up (ρ : IrrGL (k := k)) : Set (IrrGL (k := k)) := {y | ∃ n : ℕ, y = ρ.nu (n : ℂ)}

end UpperTheory.Lit.Red

end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.TScalarFull
open Filter Topology GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult UpperTheory.Lit.Cas

private theorem sum_card_mul_modExp {α : Type} [Fintype α] [LinearOrder α] (m : α → Type) [∀ a, Fintype (m a)] :
    ∑ a, (Fintype.card (m a) : ℤ) * modExp m a = 0 := by
  simp only [modExp, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_filter]
  rw [sub_eq_zero, Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  split_ifs <;> ring

private theorem deltaHalf_scalar (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {α : Type} [Fintype α] [LinearOrder α] (m : α → Type) [∀ a, Fintype (m a)]
    [∀ a, DecidableEq (m a)] (t : kˣ) :
    (deltaHalf k m (fun a => Matrix.GeneralLinearGroup.scalar (m a) t) : ℂ) = 1 := by
  rw [val_deltaHalf]
  have hx : nabs k t ≠ 0 := (nabs_pos' k t).ne'
  have hn : ∀ a, nabs k (Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (m a) t)) =
      nabs k t ^ ((Fintype.card (m a) : ℤ)) := by
    intro a
    rw [Matrix.GeneralLinearGroup.det_scalar, zpow_natCast]
    simp [nabs, map_pow]
  have key : ∀ (s : Finset α) (f : α → ℤ), ∏ a ∈ s, nabs k t ^ f a = nabs k t ^ (∑ a ∈ s, f a) := by
    intro s f
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add₀ hx]
  have hmod : modulus k m (fun a => Matrix.GeneralLinearGroup.scalar (m a) t) = 1 := by
    simp only [modulus, hn, ← zpow_mul]
    rw [key, sum_card_mul_modExp, zpow_zero]
  rw [hmod]
  simp

private theorem parInd_scalar {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {α n W : Type} [Fintype α] [LinearOrder α] {m : α → Type} [∀ a, Fintype (m a)]
    [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] [AddCommGroup W] [Module ℂ W]
    (e : (Σ a, m a) ≃ n) (ρ : Representation ℂ (Levi k m) W) (t : kˣ) (c : ℂ)
    (hρ : ∀ w, ρ (fun a => Matrix.GeneralLinearGroup.scalar (m a) t) w = c • w) (v : IndSp e ρ) :
    parInd e ρ (Matrix.GeneralLinearGroup.scalar n t) v = c • v := by
  have hmem : Matrix.GeneralLinearGroup.scalar n t ∈ parab k e := by
    rw [mem_parab]
    intro i j hij
    have hne : i ≠ j := by
      rintro rfl
      exact lt_irrefl _ hij
    simp [Matrix.GeneralLinearGroup.scalar, hne]
  have hproj : leviProj k e ⟨_, hmem⟩ = fun a => Matrix.GeneralLinearGroup.scalar (m a) t := by
    funext a
    ext i j
    simp [leviProj, diagBlock, Matrix.GeneralLinearGroup.scalar, Matrix.one_apply, e.injective.eq_iff,
      Matrix.diagonal_apply, Sigma.mk.inj_iff]
  have hcomm : ∀ x : GL n k, x * Matrix.GeneralLinearGroup.scalar n t = Matrix.GeneralLinearGroup.scalar n t * x := by
    intro x
    ext i j
    simp [Matrix.GeneralLinearGroup.scalar, mul_comm]
  apply Subtype.ext
  apply Subtype.ext
  funext x
  show v.1.1 (x * Matrix.GeneralLinearGroup.scalar n t) = (c • v).1.1 x
  rw [hcomm x]
  have hlaw := parInd_law e ρ v ⟨_, hmem⟩ x
  simp only at hlaw
  rw [hlaw, hproj, deltaHalf_scalar, hρ, one_smul]
  rfl

private theorem piTensor_scalar {α : Type} [Fintype α] {Γ X : α → Type} [∀ a, Group (Γ a)] [∀ a, AddCommGroup (X a)]
    [∀ a, Module ℂ (X a)] (ρ : ∀ a, Representation ℂ (Γ a) (X a)) (g : ∀ a, Γ a) (c : α → ℂ)
    (hc : ∀ a v, ρ a (g a) v = c a • v) : ∀ w, piTensor ρ g w = (∏ i, c i) • w := by
  intro w
  induction w using PiTensorProduct.induction_on with
  | smul_tprod r x =>
    rw [LinearMap.map_smul, piTensor_tprod]
    simp only [hc]
    rw [MultilinearMap.map_smul_univ, smul_comm]
    simp only [RingHom.id_apply]
  | add x y hx hy =>
    rw [map_add (f := _), hx, hy, smul_add]

theorem UpperTheory.Lit.Cas.scalarFull :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (h N : ℕ) (y : Fin h → IrrGL (k := k)) (hc : ∑ i, (y i).1 = N) (t : kˣ) (c : Fin h → ℂ), (∀ i, ScalarBy (y i) t (c i)) → ∀ v, prodIrr y hc (Matrix.GeneralLinearGroup.scalar (Fin N) t) v = (∏ i, c i) • v := by
  intro k _ _ _ _ h N y hc t c hy v
  exact parInd_scalar (stdBlocks (fun a => (y a).1) hc) (piTensor fun a => (y a).rep) t (∏ i, c i)
    (piTensor_scalar (fun a => (y a).rep) (fun a => Matrix.GeneralLinearGroup.scalar (Fin (y a).1) t) c
      (fun a w => hy a w)) v
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.TSchur
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.AdmissibleSchurLemma
noncomputable def UpperTheory.Reformulated.B.AdmissibleSchurLemma.IsSmooth :
    {k G V : Type} →
      [inst : Field k] →
        [inst_1 : Group G] →
          [inst_2 : AddCommGroup V] → [inst_3 : _root_.Module k V] → [TopologicalSpace G] → Representation k G V → Prop :=
    fun {k G V : Type} [Field k] [Group G] [AddCommGroup V] [_root_.Module k V] [TopologicalSpace G]
        (ρ : Representation k G V) ↦
      ∀ (v : V), IsOpen {g : G | ((ρ : G → V →ₗ[k] V) g : V → V) v = v}

theorem UpperTheory.Reformulated.B.AdmissibleSchurLemma.aux2 :
    ∀ {k G V : Type} [inst : Field k] [inst_1 : Group G] [inst_2 : AddCommGroup V] [inst_3 : _root_.Module k V]
      (ρ : Representation k G V) (H : Subgroup G) (χ : ↥H →* kˣ) {a b : V},
      a ∈ {v : V | ∀ (h : ↥H), ((ρ : G → V →ₗ[k] V) (↑h : G) : V → V) v = (↑((χ : ↥H → kˣ) h) : k) • v} →
        b ∈ {v : V | ∀ (h : ↥H), ((ρ : G → V →ₗ[k] V) (↑h : G) : V → V) v = (↑((χ : ↥H → kˣ) h) : k) • v} →
          ∀ (h : ↥H), ((ρ : G → V →ₗ[k] V) (↑h : G) : V → V) (a + b) = (↑((χ : ↥H → kˣ) h) : k) • (a + b) := by
  intro k G V _ _ _ _ ρ H χ a b ha hb h
  rw [map_add (f := _), ha h, hb h, smul_add]

theorem UpperTheory.Reformulated.B.AdmissibleSchurLemma.aux3 :
    ∀ {k G V : Type} [inst : Field k] [inst_1 : Group G] [inst_2 : AddCommGroup V] [inst_3 : _root_.Module k V]
      (ρ : Representation k G V) (H : Subgroup G) (χ : ↥H →* kˣ) (h : ↥H),
      ((ρ : G → V →ₗ[k] V) (↑h : G) : V → V) (0 : V) = (↑((χ : ↥H → kˣ) h) : k) • (0 : V) := by
  intro k G V _ _ _ _ ρ H χ h
  rw [map_zero, smul_zero]

theorem UpperTheory.Reformulated.B.AdmissibleSchurLemma.aux4 :
    ∀ {k G V : Type} [inst : Field k] [inst_1 : Group G] [inst_2 : AddCommGroup V] [inst_3 : _root_.Module k V]
      (ρ : Representation k G V) (H : Subgroup G) (χ : ↥H →* kˣ) (c : k) {v : V},
      v ∈ {v : V | ∀ (h : ↥H), ((ρ : G → V →ₗ[k] V) (↑h : G) : V → V) v = (↑((χ : ↥H → kˣ) h) : k) • v} →
        ∀ (h : ↥H), ((ρ : G → V →ₗ[k] V) (↑h : G) : V → V) (c • v) = (↑((χ : ↥H → kˣ) h) : k) • c • v := by
  intro k G V _ _ _ _ ρ H χ c v hv h
  rw [map_smul, hv h, smul_comm]

noncomputable def UpperTheory.Reformulated.B.AdmissibleSchurLemma.eig :
    {k G V : Type} →
      [inst : Field k] →
        [inst_1 : Group G] →
          [inst_2 : AddCommGroup V] →
            [inst_3 : _root_.Module k V] → Representation k G V → (H : Subgroup G) → (↥H →* kˣ) → Submodule k V :=
    fun {k G V : Type} [inst : Field k] [inst_1 : Group G] [inst_2 : AddCommGroup V] [inst_3 : _root_.Module k V]
        (ρ : Representation k G V) (H : Subgroup G) (χ : ↥H →* kˣ) ↦
      { carrier := {v : V | ∀ (h : ↥H), ((ρ : G → V →ₗ[k] V) (↑h : G) : V → V) v = (↑((χ : ↥H → kˣ) h) : k) • v},
        add_mem' := @UpperTheory.Reformulated.B.AdmissibleSchurLemma.aux2 k G V inst inst_1 inst_2 inst_3 ρ H χ, zero_mem' := UpperTheory.Reformulated.B.AdmissibleSchurLemma.aux3 ρ H χ,
        smul_mem' := UpperTheory.Reformulated.B.AdmissibleSchurLemma.aux4 ρ H χ : Submodule k V }

noncomputable def UpperTheory.Reformulated.B.AdmissibleSchurLemma.fixed :
    {k G V : Type} →
      [inst : Field k] →
        [inst_1 : Group G] →
          [inst_2 : AddCommGroup V] → [inst_3 : _root_.Module k V] → Representation k G V → Subgroup G → Submodule k V :=
    fun {k G V : Type} [Field k] [Group G] [AddCommGroup V] [_root_.Module k V] (ρ : Representation k G V)
        (H : Subgroup G) ↦
      UpperTheory.Reformulated.B.AdmissibleSchurLemma.eig ρ H (1 : ↥H →* kˣ)

noncomputable def UpperTheory.Reformulated.B.AdmissibleSchurLemma.IsAdmissible :
    {k G V : Type} →
      [inst : Field k] →
        [inst_1 : Group G] →
          [inst_2 : AddCommGroup V] → [inst_3 : _root_.Module k V] → [TopologicalSpace G] → Representation k G V → Prop :=
    fun {k G V : Type} [Field k] [Group G] [AddCommGroup V] [_root_.Module k V] [TopologicalSpace G]
        (ρ : Representation k G V) ↦
      UpperTheory.Reformulated.B.AdmissibleSchurLemma.IsSmooth ρ ∧
        ∀ (K : Subgroup G), IsOpen (↑K : Set G) → IsCompact (↑K : Set G) → FiniteDimensional k ↥(UpperTheory.Reformulated.B.AdmissibleSchurLemma.fixed ρ K)

private theorem UpperTheory.Reformulated.B.AdmissibleSchurLemma.mem_fixed_iff {k G V : Type} [Field k] [Group G] [AddCommGroup V]
    [_root_.Module k V] (ρ : Representation k G V) (H : Subgroup G) (v : V) :
    v ∈ UpperTheory.Reformulated.B.AdmissibleSchurLemma.fixed ρ H ↔ ∀ g ∈ H, ρ g v = v := by
  change (∀ h : H, ρ (h : G) v = (((1 : H →* kˣ) h : kˣ) : k) • v) ↔ _
  simp

theorem UpperTheory.Reformulated.B.AdmissibleSchurLemma.schur_adm :
    ∀ (G : Type) [inst : Group G] [inst_1 : TopologicalSpace G] [IsTopologicalGroup G] (K : Subgroup G),
      IsOpen (↑K : Set G) →
        IsCompact (↑K : Set G) →
          ∀ (N : Type) [inst_3 : AddCommGroup N] [inst_4 : _root_.Module ℂ N] (π : Representation ℂ G N),
            π.IsIrreducible →
              UpperTheory.Reformulated.B.AdmissibleSchurLemma.IsAdmissible π →
                ∀ (φ : N →ₗ[ℂ] N),
                  (∀ (g : G) (x : N),
                      (φ : N → N) (((π : G → N →ₗ[ℂ] N) g : N → N) x) = ((π : G → N →ₗ[ℂ] N) g : N → N) ((φ : N → N) x)) →
                    ∃ (c : ℂ), φ = c • LinearMap.id := by
  intro G _ _ _ K hKo hKc N _ _ π hirr hadm φ hφ
  obtain ⟨hsm, hfd⟩ := hadm
  rcases subsingleton_or_nontrivial N with hN | hN
  · exact ⟨0, Subsingleton.elim _ _⟩
  obtain ⟨v, hv⟩ := exists_ne (0 : N)
  let S : Subgroup G :=
    { carrier := {g | π g v = v}
      one_mem' := by simp
      mul_mem' := by
        intro a b ha hb
        have ha' : π a v = v := ha
        have hb' : π b v = v := hb
        change π (a * b) v = v
        rw [map_mul, Module.End.mul_apply, hb', ha']
      inv_mem' := by
        intro a ha
        have ha' : π a v = v := ha
        change π a⁻¹ v = v
        calc π a⁻¹ v = π a⁻¹ (π a v) := by rw [ha']
          _ = v := by rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
              Module.End.one_apply] }
  have hSo : IsOpen (S : Set G) := hsm v
  have hSc : IsClosed (S : Set G) := S.isClosed_of_isOpen hSo
  have hfin : FiniteDimensional ℂ (UpperTheory.Reformulated.B.AdmissibleSchurLemma.fixed π (K ⊓ S)) :=
    hfd (K ⊓ S) (hKo.inter hSo) (hKc.inter_right hSc)
  have hvU : v ∈ UpperTheory.Reformulated.B.AdmissibleSchurLemma.fixed π (K ⊓ S) :=
    (UpperTheory.Reformulated.B.AdmissibleSchurLemma.mem_fixed_iff π _ v).2 fun g hg => hg.2
  have hnt : Nontrivial (UpperTheory.Reformulated.B.AdmissibleSchurLemma.fixed π (K ⊓ S)) :=
    ⟨⟨⟨v, hvU⟩, 0, fun h => hv (congrArg Subtype.val h)⟩⟩
  have hst : ∀ x ∈ UpperTheory.Reformulated.B.AdmissibleSchurLemma.fixed π (K ⊓ S), φ x ∈ UpperTheory.Reformulated.B.AdmissibleSchurLemma.fixed π (K ⊓ S) := by
    intro x hx
    rw [UpperTheory.Reformulated.B.AdmissibleSchurLemma.mem_fixed_iff] at hx ⊢
    intro g hg
    rw [← hφ, hx g hg]
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (φ.restrict hst)
  obtain ⟨w, hw⟩ := hc.exists_hasEigenvector
  have hw0 : (w : N) ≠ 0 := fun h => hw.2 (Subtype.ext h)
  have hwc : φ w = c • (w : N) := congrArg Subtype.val hw.apply_eq_smul
  let E : Subrepresentation π :=
    { toSubmodule := Module.End.eigenspace φ c
      apply_mem_toSubmodule := by
        intro g x hx
        rw [Module.End.mem_eigenspace_iff] at hx ⊢
        rw [hφ, hx, map_smul] }
  refine ⟨c, ?_⟩
  rcases hirr.eq_bot_or_eq_top E with hE | hE
  · have h1 : Module.End.eigenspace φ c = ⊥ := congrArg Subrepresentation.toSubmodule hE
    have h2 : (w : N) ∈ Module.End.eigenspace φ c := Module.End.mem_eigenspace_iff.2 hwc
    rw [h1] at h2
    exact absurd ((Submodule.mem_bot ℂ).1 h2) hw0
  · have h1 : Module.End.eigenspace φ c = ⊤ := congrArg Subrepresentation.toSubmodule hE
    ext x
    have h2 : x ∈ Module.End.eigenspace φ c := h1 ▸ Submodule.mem_top
    simpa using Module.End.mem_eigenspace_iff.1 h2
end

open Filter Topology GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult UpperTheory.Lit.Cas

private theorem UpperTheory.Lit.Cas.schur_adm : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K : Subgroup G), IsOpen (K : Set G) → IsCompact (K : Set G) → ∀ (N : Type) [AddCommGroup N] [Module ℂ N] (π : Representation ℂ G N), π.IsIrreducible → GlobalTheory.PRep.IsAdmissible π → ∀ φ : N →ₗ[ℂ] N, (∀ g x, φ (π g x) = π g (φ x)) → ∃ c : ℂ, φ = c • LinearMap.id :=
  _root_.UpperTheory.Reformulated.B.AdmissibleSchurLemma.schur_adm

private theorem UpperTheory.Lit.Cas.exists_ne_zero_of_irr {G N : Type} [Group G] [AddCommGroup N] [Module ℂ N]
    (π : Representation ℂ G N) (hirr : π.IsIrreducible) : ∃ x : N, x ≠ 0 := by
  have hne : (⊥ : Subrepresentation π) ≠ ⊤ := bot_ne_top
  by_contra h
  push Not at h
  apply hne
  ext v
  simp [h v]

theorem UpperTheory.Lit.Cas.schur :
    GlobalTheory.Published.IrreducibleAdmissibleGL → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (x : IrrGL (k := k)) (t : kˣ), (∃ c, ScalarBy x t c) ∧ (∀ c c', ScalarBy x t c → ScalarBy x t c' → c = c') ∧ ∀ c, x.1 = 0 → ScalarBy x t c → c = 1 := by
  intro H k _ _ _ _ x t
  obtain ⟨v, hv⟩ := UpperTheory.Lit.Cas.exists_ne_zero_of_irr x.rep x.2.rep.irr
  have uniq : ∀ c c', ScalarBy x t c → ScalarBy x t c' → c = c' := fun c c' h h' =>
    smul_left_injective ℂ hv ((h v).symm.trans (h' v))
  refine ⟨?_, uniq, fun c h0 hc => uniq _ _ hc fun w => ?_⟩
  · obtain ⟨c, hc⟩ := UpperTheory.Lit.Cas.schur_adm (GL (Fin x.1) k) (KO k (Fin x.1)) GlobalTheory.SplitFlip.isOpen_KO
      GlobalTheory.SplitFlip.isCompact_KO _ x.rep x.2.rep.irr (H k x.1 _ x.rep x.2.rep.smooth x.2.rep.irr)
      (x.rep (Matrix.GeneralLinearGroup.scalar (Fin x.1) t)) (fun g w => by
        have hcomm : Matrix.GeneralLinearGroup.scalar (Fin x.1) t * g =
            g * Matrix.GeneralLinearGroup.scalar (Fin x.1) t := by
          apply Units.ext
          exact (Matrix.scalar_commute (n := Fin x.1) (t : k) (fun r => Commute.all _ _) (g : Matrix _ _ k)).eq
        rw [← Module.End.mul_apply, ← map_mul, hcomm, map_mul, Module.End.mul_apply])
    exact ⟨c, fun w => by rw [hc]; rfl⟩
  · haveI : IsEmpty (Fin x.1) := by rw [h0]; infer_instance
    have h1 : Matrix.GeneralLinearGroup.scalar (Fin x.1) t = 1 :=
      Units.ext (Matrix.ext fun i => isEmptyElim i)
    rw [h1, map_one, one_smul]; rfl
end
