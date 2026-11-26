module

public import CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.SegmentSubquotients.HasFiniteLengthJacSub
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeftInvSubtypeSum
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WordOccursProductInterleave

@[expose] public section

section -- merged from CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.SegmentSubquotients.IsSubquotientJacMultiProdOfSub
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.JHMult GlobalTheory.Published GlobalTheory.SegmentRepModel

namespace CompanionTheory.Pf1.SegRepC.Lift

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isSmooth_multiProd_segTerm {d : ℕ} (σ : IrrRep (GL (Fin d) k)) (l : ℕ) :
    IsSmooth (multiProd (consecBlocks l d) (segTerm σ.ρ l)) :=
  isSmooth_parInd _ _


set_option synthInstance.maxHeartbeats 400000 in
theorem isSubquotient_jac_multiProd_of_sub {d l : ℕ} (σ : IrrRep (GL (Fin d) k))
    (S : Subrepresentation (multiProd (consecBlocks l d) (segTerm σ.ρ l)))
    {X : Type} [AddCommGroup X] [Module ℂ X] {π : Representation ℂ (Levi k fun _ : Fin l => Fin d) X}
    (h : IsSubquotient π (jac (consecBlocks l d) S.toRepresentation)) :
    IsSubquotient π (jac (consecBlocks l d) (multiProd (consecBlocks l d) (segTerm σ.ρ l))) :=
  h.trans (GlobalTheory.JacquetExact.isSubquotient_jac (d := fun _ => d) (consecBlocks l d)
    (isSmooth_multiProd_segTerm σ l)
    (IsSubquotient.of_injective ⟨S.toSubmodule.subtype, fun _ => rfl⟩ Subtype.val_injective))

theorem perm_eq_one_of_lt_succ {l : ℕ} (w : Equiv.Perm (Fin l))
    (h : ∀ (i : ℕ) (hi : i + 1 < l), w.symm ⟨i, by omega⟩ < w.symm ⟨i + 1, hi⟩) : w = 1 := by
  cases l with
  | zero => exact Subsingleton.elim _ _
  | succ n =>
    have hm : StrictMono w.symm := Fin.strictMono_iff_lt_succ.2 fun i => h i.1 (by omega)
    have he : ∀ y, w.symm y = y := fun y => by
      have := congrArg (fun e : Fin (n + 1) ≃o Fin (n + 1) => e y)
        (Subsingleton.elim (hm.orderIsoOfSurjective _ w.symm.surjective) (OrderIso.refl _))
      simpa using this
    ext x
    have hx := he (w x)
    simp only [Equiv.symm_apply_apply] at hx
    simp [← hx]

end CompanionTheory.Pf1.SegRepC.Lift

end
end

section -- merged from CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.SegmentSubquotients.JhMultRevJacSub
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult GlobalTheory.Published GlobalTheory.SegmentRepModel Zc
open CompanionTheory.Pf1.SegRepC.SegTwo

namespace CompanionTheory.RgGu.SRC

namespace SrRev

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem transfer {N : ℕ} {v w : Fin 2 → IrrGL (k := k)} (h : v = w) (hv : ∑ a, (v a).1 = N) {W : Type}
    [AddCommGroup W] [Module ℂ W] {ω : Representation ℂ (GL (Fin N) k) W} (f : ω.IntertwiningMap (prodIrr v hv)) :
    ∃ (hw : ∑ a, (w a).1 = N) (f' : ω.IntertwiningMap (prodIrr w hw)),
      (Function.Injective f → Function.Injective f') ∧ (Function.Surjective f' → Function.Surjective f) := by
  subst h
  exact ⟨hv, f, id, id⟩

theorem jmc {h N : ℕ} {x x' : Fin h → IrrGL (k := k)} (e : x = x') (hd : ∑ a, (x a).1 = N) (hd' : ∑ a, (x' a).1 = N)
    {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) : jm x hd π = jm x' hd' π := by
  subst e
  rfl

end SrRev

open SrRev

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem jhMult_rev_jac_sub (hG : GeometricLemma) (hR : RhoNuRhoReducible) {d : ℕ} (hd : 0 < d)
    (σ : IrrRep (GL (Fin d) k)) (hσ : IsCuspidal σ.ρ)
    (S : Subrepresentation (multiProd (consecBlocks 2 d) (segTerm σ.ρ 2)))
    (hS : S.toRepresentation.IsIrreducible)
    (h1 : jhMult (piTensor (segTerm σ.ρ 2)) (jac (consecBlocks 2 d) S.toRepresentation) = 1) :
    jhMult (revTensor σ) (jac (consecBlocks 2 d) S.toRepresentation) = 0 := by
  by_contra h2
  have hA := GlobalTheory.CompanionTheory.BZCuspPair.irrAdm
  let x : IrrGL (k := k) := IrrGL.of σ.ρ σ.smooth σ.irr
  have hx : x.IsCusp := ⟨hd, isCuspidal_of_equiv (IrrGL.equivOf σ.ρ σ.smooth σ.irr) hσ⟩
  let u : Fin 2 → IrrGL (k := k) := fun a => x.nu ((a : ℕ) : ℂ)
  have hu1 : ∀ a, (u a).1 = d := fun _ => rfl
  have hu : ∑ a, (u a).1 = 2 * d := by simp only [hu1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  have hu' : ∑ a, (u (Fin.rev a)).1 = 2 * d := by
    simp only [hu1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  have he : stdBlocks (fun a => (u a).1) hu = consecBlocks 2 d := by
    refine Equiv.ext ?_
    rintro ⟨a, j⟩
    refine Fin.ext ?_
    refine (Eq.trans ?_ (consecBlocks_val 2 d a j).symm)
    rw [stdBlocks_val]
    fin_cases a <;> simp [hu1, Fin.sum_univ_two, mul_comm, add_comm]
  have he' : stdBlocks (fun a => (u (Fin.rev a)).1) hu' = consecBlocks 2 d := by
    refine Equiv.ext ?_
    rintro ⟨a, j⟩
    refine Fin.ext ?_
    refine (Eq.trans ?_ (consecBlocks_val 2 d a j).symm)
    rw [stdBlocks_val]
    fin_cases a <;> simp [hu1, Fin.sum_univ_two, mul_comm, add_comm]
  let φ : ∀ a, (segTerm σ.ρ 2 a).Equiv (u a).rep := fun a =>
    (twistEquiv (IrrGL.equivOf σ.ρ σ.smooth σ.irr) _).trans (x.twEquiv _ (isSmoothChar_absPow _))
  have Φ : (multiProd (consecBlocks 2 d) (segTerm σ.ρ 2)).Equiv (prodIrr u hu) := by
    unfold prodIrr
    rw [he]
    exact multiProdEquiv (consecBlocks 2 d) φ
  let ι : S.toRepresentation.IntertwiningMap (multiProd (consecBlocks 2 d) (segTerm σ.ρ 2)) :=
    ⟨S.toSubmodule.subtype, fun _ => rfl⟩
  let f : S.toRepresentation.IntertwiningMap (prodIrr u hu) := Φ.toIntertwiningMap.comp ι
  have hf : Function.Injective f := Φ.toLinearEquiv.injective.comp Subtype.val_injective
  have j1 : 1 ≤ jm u hu S.toRepresentation := by
    have : jm u hu S.toRepresentation = 1 := by
      unfold jm
      rw [he]
      exact (jhMult_congr_left (piTensorEquiv φ) _).symm.trans h1
    rw [this]
  have j2 : 1 ≤ jm (fun a => u (Fin.rev a)) hu' S.toRepresentation := by
    have : jm (fun a => u (Fin.rev a)) hu' S.toRepresentation ≠ 0 := by
      unfold jm
      rw [he']
      exact fun h => h2 ((jhMult_congr_left (piTensorEquiv fun a => φ (Fin.rev a)) _).trans h)
    exact Order.one_le_iff_ne_zero.2 this
  have hux : u = ![x, x.nu 1] := by
    funext a
    fin_cases a
    · simp [u]
    · simp [u]
  have hux' : (fun a => u (Fin.rev a)) = ![x.nu 1, x] := by
    funext a
    fin_cases a
    · simp [u]
    · simp [u]
  obtain ⟨hw, f', hf', hs'⟩ := transfer hux hu f
  have hw' : ∑ a, (![x.nu 1, x] a).1 = 2 * d := by rw [← hux']; exact hu'
  have hnx : x ≠ x.nu 1 := by
    intro h
    have h0 : x.nu ((0 : ℕ) : ℂ) = x.nu ((1 : ℕ) : ℂ) := by simpa using h
    exact absurd ((GlobalTheory.LocGL.IrrGL.nu_natCast_inj hd).1 h0) (by decide)
  have hsurj := GlobalTheory.CompanionTheory.CuspPairSub.surjective_of_jm hA hx (hx.nu 1) hnx hw hw' f' (hf' hf)
    (by rw [← jmc hux hu hw]; exact j1) (by rw [← jmc hux' hu' hw']; exact j2)
  have hsf := hs' hsurj
  have hι : Function.Surjective ι := by
    intro v
    obtain ⟨w, hw⟩ := hsf (Φ v)
    exact ⟨w, Φ.toLinearEquiv.injective hw⟩
  have htop : S = ⊤ := by
    refine eq_top_iff.2 fun v _ => ?_
    obtain ⟨w, rfl⟩ := hι v
    exact w.2
  subst htop
  exact hR k d hd σ hσ (GlobalTheory.Parabolic.isIrreducible_of_equiv (topEquiv _) hS)

end CompanionTheory.RgGu.SRC

end
end

section -- merged from CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.SegmentSubquotients.SrMult
section -- merged from CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.SegmentSubquotients.ExistsNabsNeOne
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.JHMult GlobalTheory.Published GlobalTheory.SegmentRepModel Matrix

namespace CompanionTheory.Pf1.SegRepC.Twist

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_ne_zero_irr {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (hi : ρ.IsIrreducible) : ∃ v : V, v ≠ 0 := by
  have := hi
  have : Nontrivial ρ.asModule := IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) _
  exact exists_ne (0 : ρ.asModule)

theorem exists_nabs_ne_one : ∃ x : kˣ, nabs k x ≠ 1 := by
  obtain ⟨ϖ, hϖ⟩ := GlobalTheory.LocGL.exists_uniformizer (k := k)
  exact ⟨ϖ, fun e => ValuativeRel.uniformizer_lt_one.ne (hϖ ▸ (nabs_eq_one_iff ϖ).1 e)⟩

theorem not_equiv_segTerm {d : ℕ} (hd : 0 < d) (σ : IrrRep (GL (Fin d) k)) (l : ℕ) {a b : Fin l}
    (hab : a ≠ b) : IsEmpty ((segTerm σ.ρ l a).Equiv (segTerm σ.ρ l b)) := by
  refine ⟨fun φ => ?_⟩
  obtain ⟨x, hx⟩ := exists_nabs_ne_one (k := k)
  let z : GL (Fin d) k := GeneralLinearGroup.scalar (Fin d) x
  have hz : ∀ g : GL (Fin d) k, z * g = g * z := fun g => by
    ext i j
    simp [z, GeneralLinearGroup.scalar, Matrix.diagonal_mul, Matrix.mul_diagonal, mul_comm]
  have hdet : GeneralLinearGroup.det z = x ^ d := by
    ext
    simp [z, GeneralLinearGroup.scalar]
  obtain ⟨c, hc⟩ := GlobalTheory.CompanionTheory.SocleFrob.exists_eq_smul_id σ.ρ σ.smooth σ.irr (σ.ρ z) fun g y => by
    rw [← Module.End.mul_apply, ← map_mul, hz g, map_mul, Module.End.mul_apply]
  have hcz : ∀ y, σ.ρ z y = c • y := fun y => by
    rw [hc]; rfl
  obtain ⟨v, hv⟩ := exists_ne_zero_irr σ.ρ σ.irr
  have hc0 : c ≠ 0 := fun e => hv (by
    have h2 : σ.ρ z⁻¹ (σ.ρ z v) = v := by
      rw [← Module.End.mul_apply, ← map_mul]
      simp
    rw [hcz, e, zero_smul, map_zero] at h2
    exact h2.symm)
  have hφv : φ.toLinearEquiv v ≠ 0 := fun e => hv (φ.toLinearEquiv.map_eq_zero_iff.1 e)
  have h3 : φ.toLinearEquiv ((segTerm σ.ρ l a) z v) = (segTerm σ.ρ l b) z (φ.toLinearEquiv v) :=
    Representation.IntertwiningMap.isIntertwining _ _ φ.toIntertwiningMap z v
  simp only [segTerm, twist_apply, detChar_apply, hdet, map_smul, hcz, smul_smul] at h3
  have h4 := mul_right_cancel₀ hc0 (smul_left_injective ℂ hφv h3)
  rw [val_absPow, val_absPow, Complex.cpow_natCast, Complex.cpow_natCast] at h4
  have h5 : nabs k (x ^ d) ^ (a : ℕ) = nabs k (x ^ d) ^ (b : ℕ) := by exact_mod_cast h4
  have hpos : 0 < nabs k (x ^ d) := nabs_pos' k _
  have hne : nabs k (x ^ d) ≠ 1 := by
    have hpow : nabs k (x ^ d) = nabs k x ^ d := by simp [nabs]
    rw [hpow]
    exact fun e => hx ((pow_eq_one_iff_of_nonneg (nabs_pos' k x).le hd.ne').1 e)
  exact hab (Fin.ext (pow_right_injective₀ hpos hne h5))

end CompanionTheory.Pf1.SegRepC.Twist

end
end

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.JHMult GlobalTheory.Published GlobalTheory.SegmentRepModel GlobalTheory.LocGL

namespace CompanionTheory.RgGu.SRC

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

namespace SrMult

theorem irrAdm : GlobalTheory.Published.IrreducibleAdmissibleGL := fun k _ _ _ _ n V _ _ π hs hi =>
  (GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness k).1 (Fin n) V π hs hi

theorem isSmooth_segTerm' {d l : ℕ} (σ : IrrRep (GL (Fin d) k)) (a : Fin l) :
    IsSmooth (segTerm σ.ρ l a) :=
  isSmooth_twist σ.smooth (isSmoothChar_of_isUnram (isUnram_absPow k _)).detChar

theorem isIrreducible_segTerm' {d l : ℕ} (σ : IrrRep (GL (Fin d) k)) (a : Fin l) :
    (segTerm σ.ρ l a).IsIrreducible :=
  GlobalTheory.LocGL.isIrreducible_twist σ.irr _

def cl {d : ℕ} (σ : IrrRep (GL (Fin d) k)) (l : ℕ) (a : Fin l) : IrrGL (k := k) :=
  IrrGL.of (segTerm σ.ρ l a) (isSmooth_segTerm' σ a) (isIrreducible_segTerm' σ a)

theorem cl_injective {d l : ℕ} (hd : 0 < d) (σ : IrrRep (GL (Fin d) k)) : Function.Injective (cl σ l) := by
  intro a b h
  by_contra hab
  obtain ⟨φ⟩ := IrrGL.of_eq_of.1 h
  exact (CompanionTheory.Pf1.SegRepC.Twist.not_equiv_segTerm hd σ l hab).false φ

theorem cl_cusp {d l : ℕ} (hd : 0 < d) (σ : IrrRep (GL (Fin d) k)) (hσ : IsCuspidal σ.ρ) (a : Fin l) :
    (cl σ l a).IsCusp := by
  have h0 : (IrrGL.of σ.ρ σ.smooth σ.irr).IsCusp := ⟨hd, isCuspidal_of_equiv (IrrGL.equivOf _ _ _) hσ⟩
  have h1 := h0.nu ((a : ℕ) : ℂ)
  have e : (IrrGL.of σ.ρ σ.smooth σ.irr).nu ((a : ℕ) : ℂ) = cl σ l a := by
    unfold IrrGL.nu cl segTerm
    rw [IrrGL.tw_of]
  rwa [e] at h1

def jacEquivOf {α : Type} [Fintype α] [LinearOrder α] {m : α → Type} [∀ a, Fintype (m a)]
    [∀ a, DecidableEq (m a)] {N : ℕ} (e : (Σ a, m a) ≃ Fin N) {V W : Type} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] {π : Representation ℂ (GL (Fin N) k) V} {τ : Representation ℂ (GL (Fin N) k) W}
    (φ : π.Equiv τ) : (jac e π).Equiv (jac e τ) :=
  equivOfBijective (jacMap e φ.toIntertwiningMap) (Function.bijective_iff_has_inverse.2
    ⟨jacMap e φ.symm.toIntertwiningMap,
      fun q => Submodule.Quotient.induction_on _ q fun v => by
        show (Submodule.Quotient.mk (φ.symm (φ v)) : _) = _
        rw [φ.symm_apply_apply],
      fun q => Submodule.Quotient.induction_on _ q fun v => by
        show (Submodule.Quotient.mk (φ (φ.symm v)) : _) = _
        rw [φ.apply_symm_apply]⟩)

def cl' {d : ℕ} (σ : IrrRep (GL (Fin d) k)) (l : ℕ) (a : Fin l) : IrrGL (k := k) := ⟨d, (cl σ l a).2⟩

end SrMult


open SrMult in
set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem jhMult_jac_multiProd (hG : GeometricLemma) {d l : ℕ} (hd : 0 < d) (hl : 0 < l)
    (σ : IrrRep (GL (Fin d) k)) (hσ : IsCuspidal σ.ρ) :
    jhMult (piTensor (segTerm σ.ρ l))
      (jac (consecBlocks l d) (multiProd (consecBlocks l d) (segTerm σ.ρ l))) = 1 := by
  classical
  have hx : ∑ a, (cl' σ l a).1 = l * d := by
    simp [cl', mul_comm]
  have hinj : Function.Injective (cl' σ l) := fun a b h => cl_injective hd σ h
  have hc : ∀ a, (cl' σ l a).IsCusp := fun a => cl_cusp hd σ hσ a
  have key := GlobalTheory.T.jacquet_multiplicity_cuspidal_product irrAdm (cl' σ l) (cl' σ l) hx hx hc hc
  have hset : {e : Fin l ≃ Fin l | ∀ a, cl' σ l a = cl' σ l (e a)} = {Equiv.refl _} := by
    ext e
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · intro h
      ext a
      exact congrArg Fin.val (hinj (h a)).symm
    · rintro rfl a
      rfl
  rw [hset, Set.ncard_singleton] at key
  have h1 : jhMult (piTensor fun a => (cl' σ l a).rep)
      (jac (stdBlocks (fun _ : Fin l => d) hx)
        (multiProd (stdBlocks (fun _ : Fin l => d) hx) fun a => (cl' σ l a).rep)) = 1 := by
    have h := key
    exact_mod_cast h
  have hblk0 : ∀ h : ∑ _a : Fin l, d = l * d, stdBlocks (fun _ : Fin l => d) h = consecBlocks l d := by
    intro h
    ext ⟨a, i⟩
    rw [stdBlocks_val, consecBlocks_val]
    simp [mul_comm, add_comm]
  rw [hblk0 hx] at h1
  calc jhMult (piTensor (segTerm σ.ρ l)) (jac (consecBlocks l d) (multiProd (consecBlocks l d) (segTerm σ.ρ l)))
      = jhMult (piTensor fun a => (cl' σ l a).rep)
          (jac (consecBlocks l d) (multiProd (consecBlocks l d) (segTerm σ.ρ l))) :=
        jhMult_congr_left (piTensorEquiv fun a => IrrGL.equivOf (segTerm σ.ρ l a) (isSmooth_segTerm' σ a)
          (isIrreducible_segTerm' σ a)) _
    _ = jhMult (piTensor fun a => (cl' σ l a).rep)
          (jac (consecBlocks l d) (multiProd (consecBlocks l d) fun a => (cl' σ l a).rep)) :=
        jhMult_congr_right _ (jacEquivOf (consecBlocks l d)
          (multiProdEquiv (consecBlocks l d) fun a => IrrGL.equivOf (segTerm σ.ρ l a) (isSmooth_segTerm' σ a)
            (isIrreducible_segTerm' σ a)))
    _ = 1 := h1

end CompanionTheory.RgGu.SRC

end
end

section -- merged from CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.SegmentSubquotients.SrPerm
section -- merged from CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.SegmentSubquotients.ExistsPermOfIsSubquotientJac
section -- merged from CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.SegmentSubquotients.MultOne
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.JHMult GlobalTheory.Published GlobalTheory.SegmentRepModel

namespace CompanionTheory.Pf1.SegRepC.MultOne

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem entry_le {d l : ℕ} (b : SizeMatrix (fun _ : Fin l => Fin d) (fun _ : Fin l => Fin d))
    (i j : Fin l) : b.1 i j ≤ d := by
  calc b.1 i j ≤ ∑ j, b.1 i j :=
        Finset.single_le_sum (f := b.1 i) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    _ = d := by simpa using b.2.1 i

theorem isSmooth_segTerm {d l : ℕ} (σ : IrrRep (GL (Fin d) k)) (a : Fin l) :
    IsSmooth (segTerm σ.ρ l a) :=
  isSmooth_twist σ.smooth (GlobalTheory.SmGL.isSmoothChar_of_isUnram (isUnram_absPow k _)).detChar

theorem isIrreducible_segTerm {d l : ℕ} (σ : IrrRep (GL (Fin d) k)) (a : Fin l) :
    (segTerm σ.ρ l a).IsIrreducible :=
  GlobalTheory.LocGL.isIrreducible_twist σ.irr _

theorem hasFiniteLength_segTerm {d l : ℕ} (σ : IrrRep (GL (Fin d) k)) (a : Fin l) :
    HasFiniteLength (segTerm σ.ρ l a) :=
  (⟨_, segTerm σ.ρ l a, isSmooth_segTerm σ a, isIrreducible_segTerm σ a⟩ :
    IrrRep (GL (Fin d) k)).hasFiniteLength

theorem exists_other {d l : ℕ} (b : SizeMatrix (fun _ : Fin l => Fin d) (fun _ : Fin l => Fin d))
    {i j : Fin l} (h : b.1 i j < d) : ∃ j', j' ≠ j ∧ 0 < b.1 i j' := by
  by_contra hc
  push Not at hc
  have h2 := b.2.1 i
  simp only [Fintype.card_fin] at h2
  rw [Finset.sum_eq_single j (fun j' _ hj' => Nat.le_zero.1 (hc j' hj')) (by simp)] at h2
  omega

end CompanionTheory.Pf1.SegRepC.MultOne

end
end

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.JHMult GlobalTheory.Published GlobalTheory.SegmentRepModel

namespace CompanionTheory.Pf1.SegRepC.Perm

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem entries_zero_or_d {d l : ℕ} (hd : 0 < d) (σ : IrrRep (GL (Fin d) k)) (hσ : IsCuspidal σ.ρ)
    (b : SizeMatrix (fun _ : Fin l => Fin d) (fun _ : Fin l => Fin d))
    (f : ∀ i, (Σ j, Fin (b.1 i j)) ≃ Fin d)
    (s : ∀ i j, IrrRep (GL (Fin (b.1 i j)) k))
    (hs : ∀ i, IsSubquotient (piTensor fun j => (s i j).ρ) (jac (f i) (segTerm σ.ρ l i))) :
    ∀ i j, b.1 i j = 0 ∨ b.1 i j = d := by
  intro i j₀
  by_contra hc
  push Not at hc
  have h0 : 0 < b.1 i j₀ := Nat.pos_of_ne_zero hc.1
  have h1 : b.1 i j₀ < d := lt_of_le_of_ne (MultOne.entry_le b i j₀) hc.2
  obtain ⟨j₁, hj, h2⟩ := MultOne.exists_other b h1
  have hcu : IsCuspidal (segTerm σ.ρ l i) :=
    GlobalTheory.LocGL.isCuspidal_twist hσ (isSmoothChar_of_isUnram (isUnram_absPow k _))
  have hne : unipRad k (f i) ≠ ⊥ := by
    refine GlobalTheory.SmGL.CuspMax.unipRad_ne_bot_iff.2 ?_
    have e0 : blk (f i) (f i ⟨j₀, ⟨0, h0⟩⟩) = j₀ := by simp [blk]
    have e1 : blk (f i) (f i ⟨j₁, ⟨0, h2⟩⟩) = j₁ := by simp [blk]
    rcases lt_or_gt_of_ne hj with hlt | hlt
    · exact ⟨_, _, e1.symm ▸ e0.symm ▸ hlt⟩
    · exact ⟨_, _, e0.symm ▸ e1.symm ▸ hlt⟩
  haveI := hcu.2 l (fun j => b.1 i j) (f i) hne
  have hirr : (piTensor fun j => (s i j).ρ).IsIrreducible :=
    GlobalTheory.ProdFiniteLength.piTensor_isIrreducible_of_schur _ (fun j => (s i j).irr)
      fun j φ hφ => GlobalTheory.CompanionTheory.SocleFrob.exists_eq_smul_id _ (s i j).smooth (s i j).irr φ hφ
  exact jhMult_ne_zero_iff.2 (hs i) (jhMult_of_subsingleton hirr _)





end CompanionTheory.Pf1.SegRepC.Perm

end
end

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult GlobalTheory.Published GlobalTheory.SegmentRepModel

namespace CompanionTheory.RgGu.SRC

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

namespace SrPerm

theorem sq_right {G V W U : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup U] [Module ℂ U] {σ : Representation ℂ G W} {ρ : Representation ℂ G V} {ρ' : Representation ℂ G U}
    (h : IsSubquotient σ ρ) (E : ρ.Equiv ρ') : IsSubquotient σ ρ' :=
  h.trans (IsSubquotient.of_surjective E.symm.toIntertwiningMap E.symm.surjective)

theorem sq_left {G V W U : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] [AddCommGroup U] [Module ℂ U] {σ : Representation ℂ G W} {τ : Representation ℂ G U}
    {ρ : Representation ℂ G V} (E : σ.Equiv τ) (h : IsSubquotient σ ρ) : IsSubquotient τ ρ :=
  (IsSubquotient.of_surjective E.toIntertwiningMap E.surjective).trans h

theorem equiv_parInd_jac {β : Type} [Fintype β] [LinearOrder β] (c : β → ℕ) (j₀ : β)
    (h0 : ∀ j, j ≠ j₀ → c j = 0) (f : (Σ j, Fin (c j)) ≃ Fin (c j₀)) {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GL (Fin (c j₀)) k) V) (hρ : IsSmooth ρ) :
    Nonempty (ρ.Equiv (parInd f (jac f ρ))) := by
  have hU : ∀ u ∈ unipRad k f, u = 1 := fun u hu => GlobalTheory.OneBlockCell.eq_one_of_mem_unipRad_single f j₀ h0 hu
  have hK : twKer ρ (unipRad k f) 1 = ⊥ := by
    refine le_bot_iff.1 (Submodule.span_le.2 ?_)
    rintro _ ⟨n, v, rfl⟩
    rw [hU n n.2]
    simp
  let L : V ≃ₗ[ℂ] Jacquet ρ (unipRad k f) := (Submodule.quotEquivOfEqBot _ hK).symm
  have hP : ∀ g : GL (Fin (c j₀)) k, g ∈ parab k f := fun g => GlobalTheory.OneBlockCell.mem_parab_of_single f j₀ h0 g
  refine GlobalTheory.CompanionTheory.WordProd.OneBlockProd.nonempty_equiv_parInd f hρ hP
    (GlobalTheory.OneBlockCell.deltaHalf_eq_one_of_single j₀ h0) L (fun p v => ?_)
  obtain ⟨u, hu, hp⟩ := exists_levi_mul_unip k f p
  rw [hU u hu, mul_one] at hp
  have hd : deltaHalf k (fun j => Fin (c j)) (leviProj k f p) = 1 :=
    GlobalTheory.OneBlockCell.deltaHalf_eq_one_of_single j₀ h0 _
  show (twist (jacU f ρ) (deltaHalf k fun j => Fin (c j))⁻¹) (leviProj k f p)
    (Submodule.Quotient.mk v) = Submodule.Quotient.mk (ρ p v)
  rw [twist_apply, MonoidHom.inv_apply, hd, inv_one, Units.val_one, one_smul]
  simp only [jacU, jacquet, MonoidHom.coe_mk, OneHom.coe_mk, Submodule.mapQ_apply]
  rw [← hp]

theorem row_class {β : Type} [Fintype β] [LinearOrder β] {N : ℕ} (c : β → ℕ) (j₀ : β) (hN : c j₀ = N)
    (h0 : ∀ j, j ≠ j₀ → c j = 0) (f : (Σ j, Fin (c j)) ≃ Fin N) (ρ : IrrRep (GL (Fin N) k))
    (s : ∀ j, IrrRep (GL (Fin (c j)) k)) (hs : IsSubquotient (piTensor fun j => (s j).ρ) (jac f ρ.ρ)) :
    (⟨c j₀, (s j₀).cl⟩ : IrrGL (k := k)) = ⟨N, ρ.cl⟩ := by
  subst hN
  obtain ⟨e1⟩ := GlobalTheory.CompanionTheory.WordProd.OneBlockProd.multiProd_single c j₀ h0 s f
  obtain ⟨e2⟩ := equiv_parInd_jac c j₀ h0 f ρ.ρ ρ.smooth
  have h3 : IsSubquotient (multiProd f fun j => (s j).ρ) (parInd f (jac f ρ.ρ)) :=
    GlobalTheory.ParIndSubquot.parInd_isSubquotient k β (Fin (c j₀)) (fun j => Fin (c j)) f _ _ _ _
      (isSmooth_jac f ρ.smooth) hs
  have h4 : IsSubquotient (s j₀).ρ ρ.ρ := sq_right (sq_left e1 h3) e2.symm
  obtain ⟨φ⟩ := h4.nonempty_equiv (s j₀).irr ρ.irr
  exact congrArg (Sigma.mk (c j₀)) (IrrRep.cl_eq_iff.2 ⟨φ.symm⟩)

theorem col_class {α : Type} [Fintype α] [LinearOrder α] {N : ℕ} (b : α → ℕ) (i₀ : α) (hN : b i₀ = N)
    (h0 : ∀ i, i ≠ i₀ → b i = 0) (σ : ∀ i, IrrRep (GL (Fin (b i)) k)) (g : (Σ i, Fin (b i)) ≃ Fin N) :
    ∃ τ : IrrRep (GL (Fin N) k), Nonempty ((multiProd g fun i => (σ i).ρ).Equiv τ.ρ) ∧
      (⟨N, τ.cl⟩ : IrrGL (k := k)) = ⟨b i₀, (σ i₀).cl⟩ := by
  subst hN
  exact ⟨σ i₀, GlobalTheory.CompanionTheory.WordProd.OneBlockProd.multiProd_single b i₀ h0 σ g, rfl⟩

def segIrr {d : ℕ} (σ : IrrRep (GL (Fin d) k)) (l : ℕ) (a : Fin l) : IrrRep (GL (Fin d) k) :=
  ⟨σ.V, segTerm σ.ρ l a, CompanionTheory.Pf1.SegRepC.MultOne.isSmooth_segTerm σ a,
    CompanionTheory.Pf1.SegRepC.MultOne.isIrreducible_segTerm σ a⟩

theorem exists_perm_of_cell {d l : ℕ} (hd : 0 < d) (σ : IrrRep (GL (Fin d) k))
    (b : SizeMatrix (fun _ : Fin l => Fin d) (fun _ : Fin l => Fin d))
    (h01 : ∀ i j, b.1 i j = 0 ∨ b.1 i j = d)
    (f : ∀ i, (Σ j, Fin (b.1 i j)) ≃ Fin d) (g : ∀ j, (Σ i, Fin (b.1 i j)) ≃ Fin d)
    (s : ∀ i j, IrrRep (GL (Fin (b.1 i j)) k))
    (hs : ∀ i, IsSubquotient (piTensor fun j => (s i j).ρ) (jac (f i) (segTerm σ.ρ l i)))
    {X : Type} [AddCommGroup X] [Module ℂ X] (π : Representation ℂ (Levi k fun _ : Fin l => Fin d) X)
    (hπ : π.IsIrreducible)
    (h : IsSubquotient π (piTensor fun j => multiProd (g j) fun i => (s i j).ρ)) :
    ∃ w : Equiv.Perm (Fin l), Nonempty (π.Equiv (piTensor fun a => segTerm σ.ρ l (w a))) := by
  classical
  have hr : ∀ i, ∑ j, b.1 i j = d := fun i => by simpa using b.2.1 i
  have hc : ∀ j, ∑ i, b.1 i j = d := fun j => by simpa using b.2.2 j
  have two : ∀ (F : Fin l → ℕ), ∑ j, F j = d → ∀ j j', F j = d → F j' = d → j = j' := by
    intro F hF j j' h1 h2
    by_contra hne
    have : F j + F j' ≤ ∑ x, F x := by
      rw [← Finset.sum_pair hne]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => Nat.zero_le _)
    omega
  have one : ∀ (F : Fin l → ℕ), (∀ j, F j = 0 ∨ F j = d) → ∑ j, F j = d → ∃ j, F j = d := by
    intro F h0 hF
    by_contra hne
    push Not at hne
    have : ∑ j, F j = 0 := Finset.sum_eq_zero fun j _ => (h0 j).resolve_right (hne j)
    omega
  have zero : ∀ (F : Fin l → ℕ), (∀ j, F j = 0 ∨ F j = d) → ∑ j, F j = d → ∀ j, F j = d →
      ∀ j', j' ≠ j → F j' = 0 := fun F h0 hF j hj j' hj' =>
    (h0 j').resolve_right fun e => hj' (two F hF j' j e hj)
  choose q hq using fun j => one (fun i => b.1 i j) (fun i => h01 i j) (hc j)
  have qinj : Function.Injective q := fun j j' e =>
    two (fun x => b.1 (q j) x) (hr (q j)) j j' (hq j) (e ▸ hq j')
  let w : Equiv.Perm (Fin l) := Equiv.ofBijective q (Finite.injective_iff_bijective.1 qinj)
  have hcol : ∀ j, Nonempty ((multiProd (g j) fun i => (s i j).ρ).Equiv (segTerm σ.ρ l (w j))) := by
    intro j
    obtain ⟨τ, ⟨E⟩, hτ⟩ := col_class (fun i => b.1 i j) (q j) (hq j)
      (zero (fun i => b.1 i j) (fun i => h01 i j) (hc j) (q j) (hq j)) (fun i => s i j) (g j)
    have hrow := row_class (fun x => b.1 (q j) x) j (hq j)
      (zero (fun x => b.1 (q j) x) (fun x => h01 (q j) x) (hr (q j)) j (hq j)) (f (q j))
      (segIrr σ l (q j)) (s (q j)) (hs (q j))
    have e := hτ.trans hrow
    have e' : τ.cl = (segIrr σ l (q j)).cl := eq_of_heq (Sigma.mk.inj_iff.1 e).2
    obtain ⟨φ⟩ := IrrRep.cl_eq_iff.1 e'
    exact ⟨E.trans φ⟩
  have hT : (piTensor fun a => segTerm σ.ρ l (w a)).IsIrreducible :=
    GlobalTheory.ProdFiniteLength.piTensor_isIrreducible_of_schur _
      (fun a => CompanionTheory.Pf1.SegRepC.MultOne.isIrreducible_segTerm σ (w a))
      fun a φ hφ => GlobalTheory.CompanionTheory.SocleFrob.exists_eq_smul_id _ (CompanionTheory.Pf1.SegRepC.MultOne.isSmooth_segTerm σ (w a))
        (CompanionTheory.Pf1.SegRepC.MultOne.isIrreducible_segTerm σ (w a)) φ hφ
  have h2 : IsSubquotient π (piTensor fun a => segTerm σ.ρ l (w a)) :=
    sq_right h (GlobalTheory.LocGL.piTensorEquiv fun j => (hcol j).some)
  obtain ⟨φ⟩ := h2.nonempty_equiv hπ hT
  exact ⟨w, ⟨φ.symm⟩⟩

end SrPerm


set_option synthInstance.maxHeartbeats 400000 in
theorem exists_perm_of_isSubquotient_jac (hG : GeometricLemma) {d l : ℕ} (hd : 0 < d) (hl : 0 < l)
    (σ : IrrRep (GL (Fin d) k)) (hσ : IsCuspidal σ.ρ)
    {X : Type} [AddCommGroup X] [Module ℂ X] (π : Representation ℂ (Levi k fun _ : Fin l => Fin d) X)
    (hπ : π.IsIrreducible)
    (h : IsSubquotient π (jac (consecBlocks l d) (multiProd (consecBlocks l d) (segTerm σ.ρ l)))) :
    ∃ w : Equiv.Perm (Fin l), Nonempty (π.Equiv (piTensor fun a => segTerm σ.ρ l (w a))) := by
  obtain ⟨b, f, g, s, hs, hπs⟩ := exists_cell_of_isSubquotient (hG k).1 (hG k).2
    (consecBlocks l d) (consecBlocks l d) (CompanionTheory.Pf1.SegRepC.MultOne.isSmooth_segTerm σ)
    (CompanionTheory.Pf1.SegRepC.MultOne.hasFiniteLength_segTerm σ) hπ h
  exact SrPerm.exists_perm_of_cell hd σ b (CompanionTheory.Pf1.SegRepC.Perm.entries_zero_or_d hd σ hσ b f s hs) f g s hs
    π hπ hπs


set_option synthInstance.maxHeartbeats 400000 in
theorem constituents_jac_sub (hG : GeometricLemma) {d : ℕ} (hd : 0 < d)
    (σ : IrrRep (GL (Fin d) k)) (hσ : IsCuspidal σ.ρ)
    (S : Subrepresentation (multiProd (consecBlocks 2 d) (segTerm σ.ρ 2)))
    {X : Type} [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ (Levi k fun _ : Fin 2 => Fin d) X)
    (hρ : ρ.IsIrreducible) (hs : IsSubquotient ρ (jac (consecBlocks 2 d) S.toRepresentation)) :
    Nonempty (ρ.Equiv (piTensor (segTerm σ.ρ 2))) ∨
      Nonempty (ρ.Equiv (CompanionTheory.Pf1.SegRepC.SegTwo.revTensor σ)) := by
  obtain ⟨w, ⟨φ⟩⟩ := exists_perm_of_isSubquotient_jac hG hd (by decide) σ hσ ρ hρ
    (CompanionTheory.Pf1.SegRepC.Lift.isSubquotient_jac_multiProd_of_sub σ S hs)
  have hne : w 1 ≠ w 0 := fun e => absurd (w.injective e) (by decide)
  rcases Fin.exists_fin_two.1 ⟨w 0, rfl⟩ with h0 | h0
  · have h1 : w 1 = 1 := by
      rw [h0] at hne
      rcases Fin.exists_fin_two.1 ⟨w 1, rfl⟩ with h | h
      · exact absurd h hne
      · exact h
    have e : (fun a => segTerm σ.ρ 2 (w a)) = segTerm σ.ρ 2 := by
      funext a
      fin_cases a
      · simp [h0]
      · simp [h1]
    rw [e] at φ
    exact Or.inl ⟨φ⟩
  · have h1 : w 1 = 0 := by
      rw [h0] at hne
      rcases Fin.exists_fin_two.1 ⟨w 1, rfl⟩ with h | h
      · exact h
      · exact absurd h hne
    have e : (fun a => segTerm σ.ρ 2 (w a)) = fun a : Fin 2 => segTerm σ.ρ 2 a.rev := by
      funext a
      fin_cases a
      · simp [h0]
      · simp [h1]
    rw [e] at φ
    exact Or.inr ⟨φ⟩

end CompanionTheory.RgGu.SRC

end
end

section -- merged from CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.SegmentSubquotients.SrEasy
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.JHMult GlobalTheory.LocGL GlobalTheory.Published GlobalTheory.SegmentRepModel

namespace CompanionTheory.RgGu.SRC

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

namespace SrEasy

theorem isSmooth_prod {d l : ℕ} (σ : IrrRep (GL (Fin d) k)) :
    IsSmooth (multiProd (consecBlocks l d) (segTerm σ.ρ l)) := isSmooth_parInd _ _

theorem hasFiniteLength_prod {d l : ℕ} (σ : IrrRep (GL (Fin d) k)) :
    HasFiniteLength (multiProd (consecBlocks l d) (segTerm σ.ρ l)) := by
  have hρ := CompanionTheory.Lit1.SegRep.PIrr.isIrreducible_piTensor_segTerm σ l
  have hsρ : IsSmooth (piTensor (segTerm σ.ρ l)) := isSmooth_piTensor fun a =>
    isSmooth_twist σ.smooth (IsSmoothChar.detChar (GlobalTheory.LocGL.isSmoothChar_absPow _))
  exact GlobalTheory.CompanionTheory.BZInd.inductionFiniteLength k _ _ _ _ _ _ hsρ (hasFiniteLength_of_isIrreducible hρ)

theorem isSmooth_sub {G V : Type} [Group G] [TopologicalSpace G] [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ G V} (hπ : IsSmooth π) (S : Subrepresentation π) : IsSmooth S.toRepresentation := by
  intro v
  have : {g : G | S.toRepresentation g v = v} = {g : G | π g v.1 = v.1} := by
    ext g; exact Subtype.ext_iff
  rw [this]; exact hπ v.1

end SrEasy

open SrEasy


set_option synthInstance.maxHeartbeats 400000 in
theorem exists_irred_le {d l : ℕ} (hd : 0 < d) (hl : 0 < l) (σ : IrrRep (GL (Fin d) k))
    (hσ : IsCuspidal σ.ρ) (T : Subrepresentation (multiProd (consecBlocks l d) (segTerm σ.ρ l)))
    (hT : T.toSubmodule ≠ ⊥) :
    ∃ S' : Subrepresentation (multiProd (consecBlocks l d) (segTerm σ.ρ l)),
      S'.toRepresentation.IsIrreducible ∧ S'.toSubmodule ≤ T.toSubmodule := by
  let ι : T.toRepresentation.IntertwiningMap (multiProd (consecBlocks l d) (segTerm σ.ρ l)) :=
    ⟨T.toSubmodule.subtype, fun _ => rfl⟩
  have hnt : Nontrivial T.toSubmodule := Submodule.nontrivial_iff_ne_bot.2 hT
  obtain ⟨S, f, hf⟩ := GlobalTheory.T.exists_injective_irreducible_subrepresentation k _ _ _ T.toRepresentation (multiProd (consecBlocks l d) (segTerm σ.ρ l))
    (isSmooth_sub (isSmooth_prod σ) T) hnt (IsSubquotient.of_injective ι Subtype.val_injective)
    (hasFiniteLength_prod σ)
  let g : S.ρ.IntertwiningMap (multiProd (consecBlocks l d) (segTerm σ.ρ l)) := ι.comp f
  have hg : Function.Injective g := Subtype.val_injective.comp hf
  have hat : IsAtom g.range := isAtom_range S.irr g hg
  refine ⟨g.range, GlobalTheory.ClassFin.isIrreducible_toRepresentation_of_isAtom _ hat, ?_⟩
  rintro _ ⟨x, rfl⟩
  exact (f x).2


set_option synthInstance.maxHeartbeats 400000 in
theorem isIrreducible_segTensor {d : ℕ} (hd : 0 < d) (σ : IrrRep (GL (Fin d) k)) :
    (piTensor (segTerm σ.ρ 2)).IsIrreducible :=
  CompanionTheory.Lit1.SegRep.PIrr.isIrreducible_piTensor_segTerm σ 2


set_option synthInstance.maxHeartbeats 400000 in
theorem hasFiniteLength_jac_sub {d : ℕ} (hd : 0 < d)
    (σ : IrrRep (GL (Fin d) k)) (hσ : IsCuspidal σ.ρ)
    (S : Subrepresentation (multiProd (consecBlocks 2 d) (segTerm σ.ρ 2))) :
    HasFiniteLength (jac (consecBlocks 2 d) S.toRepresentation) := by
  let ι : S.toRepresentation.IntertwiningMap (multiProd (consecBlocks 2 d) (segTerm σ.ρ 2)) :=
    ⟨S.toSubmodule.subtype, fun _ => rfl⟩
  have hS : HasFiniteLength S.toRepresentation :=
    GlobalTheory.ProdLength.hasFiniteLength_of_injective ι Subtype.val_injective (hasFiniteLength_prod σ)
  exact GlobalTheory.CompanionTheory.JacquetBridge.jacquetFiniteLength k _ _ _ (consecBlocks 2 d) _ S.toRepresentation
    (isSmooth_sub (isSmooth_prod σ) S) hS

end CompanionTheory.RgGu.SRC

end
end

section -- merged from CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.SegmentSubquotients.ExistsUniqueIrredSub
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.JHMult GlobalTheory.LocGL GlobalTheory.Published

namespace CompanionTheory.Pf1.SegRepC.Uniq

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]


set_option synthInstance.maxHeartbeats 400000 in
theorem exists_unique_irred_sub {d l : ℕ} (hd : 0 < d) (hl : 0 < l) (σ : IrrRep (GL (Fin d) k))
    (hσ : IsCuspidal σ.ρ)
    (h1 : jhMult (piTensor (segTerm σ.ρ l))
      (jac (consecBlocks l d) (multiProd (consecBlocks l d) (segTerm σ.ρ l))) = 1) :
    ∃ S : Subrepresentation (multiProd (consecBlocks l d) (segTerm σ.ρ l)),
      S.toRepresentation.IsIrreducible ∧
      (∀ S' : Subrepresentation (multiProd (consecBlocks l d) (segTerm σ.ρ l)),
        S'.toRepresentation.IsIrreducible → S' = S) ∧
      jhMult (piTensor (segTerm σ.ρ l)) (jac (consecBlocks l d) S.toRepresentation) = 1 := by
  have hρ := CompanionTheory.Lit1.SegRep.PIrr.isIrreducible_piTensor_segTerm σ l
  have hsρ : IsSmooth (piTensor (segTerm σ.ρ l)) := isSmooth_piTensor fun a =>
    isSmooth_twist σ.smooth (IsSmoothChar.detChar (GlobalTheory.LocGL.isSmoothChar_absPow _))
  have hsπ : IsSmooth (multiProd (consecBlocks l d) (segTerm σ.ρ l)) := isSmooth_parInd _ _
  have := GlobalTheory.CompanionTheory.SocleJm.nontrivial_indSp (consecBlocks l d) hρ hsρ
  have hfl : HasFiniteLength (multiProd (consecBlocks l d) (segTerm σ.ρ l)) :=
    GlobalTheory.CompanionTheory.BZInd.inductionFiniteLength k _ _ _ _ _ _ hsρ (hasFiniteLength_of_isIrreducible hρ)
  have hone : ∀ T : Subrepresentation (multiProd (consecBlocks l d) (segTerm σ.ρ l)), IsAtom T →
      1 ≤ jhMult (piTensor (segTerm σ.ρ l)) (jac (consecBlocks l d) T.toRepresentation) :=
    GlobalTheory.CompanionTheory.SocleJm.one_le_jhMult_jac_atom _ hρ
  have hjm : jhMult (piTensor (segTerm σ.ρ l)) (jac (consecBlocks l d) (multiProd (consecBlocks l d) (segTerm σ.ρ l))) ≤ 1 := h1.le
  have hsoc : ∃ τ : IrrRep (GL (Fin (l * d)) k), IsSocle τ.ρ (multiProd (consecBlocks l d) (segTerm σ.ρ l)) :=
    GlobalTheory.CompanionTheory.SocleJm.exists_isSocle_of_forall_isAtom (π := multiProd (consecBlocks l d) (segTerm σ.ρ l)) (consecBlocks l d) hρ hsπ hfl hone hjm
  obtain ⟨τ, hτ, f, hf, hS⟩ := hsoc
  have hat : IsAtom f.range := isAtom_range hτ f hf
  have hatom : ∀ S' : Subrepresentation (multiProd (consecBlocks l d) (segTerm σ.ρ l)),
      S'.toRepresentation.IsIrreducible → IsAtom S' := fun S' hS' => by
    let g : S'.toRepresentation.IntertwiningMap (multiProd (consecBlocks l d) (segTerm σ.ρ l)) := ⟨S'.toSubmodule.subtype, fun _ => rfl⟩
    have hr : g.range = S' := Subrepresentation.toSubmodule_injective (Submodule.range_subtype _)
    have h := isAtom_range hS' g Subtype.val_injective
    rwa [hr] at h
  refine ⟨f.range, GlobalTheory.ClassFin.isIrreducible_toRepresentation_of_isAtom _ hat,
    fun S' hS' => hS S' (hatom S' hS'), le_antisymm ?_ ?_⟩
  · let ι : f.range.toRepresentation.IntertwiningMap (multiProd (consecBlocks l d) (segTerm σ.ρ l)) := ⟨f.range.toSubmodule.subtype, fun _ => rfl⟩
    have hinj : Function.Injective (jacMap (consecBlocks l d) ι) :=
      GlobalTheory.JacInj.jacMap_injective k _ _ _ (consecBlocks l d) _ _ f.range.toRepresentation (multiProd (consecBlocks l d) (segTerm σ.ρ l)) ι hsπ
        Subtype.val_injective
    exact (GlobalTheory.CompanionTheory.SocleJm.jhMult_le_of_injective hρ (jacMap (consecBlocks l d) ι) hinj).trans hjm
  · exact hone _ hat

end CompanionTheory.Pf1.SegRepC.Uniq

end
end

section -- merged from CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.SegmentSubquotients.IsSubquotientJacOfLe
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.JHMult GlobalTheory.Published GlobalTheory.SegmentRepModel

namespace CompanionTheory.Pf1.SegRepC.PiLocalization₂

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]



set_option synthInstance.maxHeartbeats 400000 in
theorem isSubquotient_jac_of_le {d l : ℕ} (σ : IrrRep (GL (Fin d) k))
    {S T : Subrepresentation (multiProd (consecBlocks l d) (segTerm σ.ρ l))} (hST : S.toSubmodule ≤ T.toSubmodule)
    {X : Type} [AddCommGroup X] [Module ℂ X] {π : Representation ℂ (Levi k fun _ : Fin l => Fin d) X}
    (h : IsSubquotient π (jac (consecBlocks l d) S.toRepresentation)) :
    IsSubquotient π (jac (consecBlocks l d) T.toRepresentation) :=
  h.trans (GlobalTheory.JacquetExact.isSubquotient_jac (d := fun _ => d) (consecBlocks l d)
    (GlobalTheory.CompanionTheory.JacExp.isSmooth_sub (isSmooth_parInd _ _) T)
    (IsSubquotient.of_injective ⟨Submodule.inclusion hST, fun _ => rfl⟩ (Submodule.inclusion_injective hST)))

end CompanionTheory.Pf1.SegRepC.PiLocalization₂

end
end

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.JHMult GlobalTheory.Published GlobalTheory.SegmentRepModel
open CompanionTheory.Pf1.SegRepC CompanionTheory.Pf1.SegRepC.SegTwo

namespace CompanionTheory.RgGu.SRC


set_option synthInstance.maxHeartbeats 400000 in
def StageP : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    GeometricLemma → CompanionTheory.Pf1.SegRepC.SegTwo → ∀ {d l : ℕ}, 0 < d → 0 < l → ∀ (σ : IrrRep (GL (Fin d) k)),
    IsCuspidal σ.ρ → ∀ (i : ℕ) (hi : i + 1 < l),
    ∃ T : Subrepresentation (multiProd (consecBlocks l d) (segTerm σ.ρ l)), T.toSubmodule ≠ ⊥ ∧
      ∀ {X : Type} [AddCommGroup X] [Module ℂ X] (π : Representation ℂ (Levi k fun _ : Fin l => Fin d) X),
        π.IsIrreducible → IsSubquotient π (jac (consecBlocks l d) T.toRepresentation) →
        ∀ (w : Equiv.Perm (Fin l)), π.Equiv (piTensor fun a => segTerm σ.ρ l (w a)) →
        w.symm ⟨i, by omega⟩ < w.symm ⟨i + 1, hi⟩

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem segTwo_of (hG : GeometricLemma) (hR : RhoNuRhoReducible) : CompanionTheory.Pf1.SegRepC.SegTwo := by
  intro k _ _ _ _ d hd σ hσ
  have h2 : (0 : ℕ) < 2 := by decide
  obtain ⟨S, hS, hU, h1⟩ := Uniq.exists_unique_irred_sub hd h2 σ hσ (SRC.jhMult_jac_multiProd hG hd h2 σ hσ)
  refine ⟨S, hS, hU, ?_⟩
  refine GlobalTheory.CompanionTheory.FineStep.nonempty_equiv_of_jhMult_eq_one _ _ (SRC.isIrreducible_segTensor hd σ) (SRC.hasFiniteLength_jac_sub hd σ hσ S) h1 fun X _ _ ρ hρ hs => ?_
  rcases SRC.constituents_jac_sub hG hd σ hσ S ρ hρ hs with h | h'
  · exact h
  · obtain ⟨φ⟩ := h'
    exfalso
    refine jhMult_ne_zero_iff.2 ?_ (SRC.jhMult_rev_jac_sub hG hR hd σ hσ S hS h1)
    exact (IsSubquotient.of_surjective φ.toIntertwiningMap fun w => ⟨φ.symm w, φ.apply_symm_apply w⟩).trans hs

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem segRep_of (hT : StageP) (hG : GeometricLemma) (h2 : CompanionTheory.Pf1.SegRepC.SegTwo) : SegmentRepresentation := by
  intro k _ _ _ _ d l hd hl σ hσ
  obtain ⟨S, hS, huniq, h1⟩ := Uniq.exists_unique_irred_sub hd hl σ hσ (SRC.jhMult_jac_multiProd hG hd hl σ hσ)
  refine ⟨S, hS, huniq, ?_⟩
  have hfl : HasFiniteLength (jac (consecBlocks l d) S.toRepresentation) :=
    GlobalTheory.CompanionTheory.JacquetBridge.jacquetFiniteLength k _ _ _ (consecBlocks l d) _ S.toRepresentation
      (GlobalTheory.CompanionTheory.JacExp.isSmooth_sub (Lift.isSmooth_multiProd_segTerm σ l) S) (hasFiniteLength_of_isIrreducible hS)
  refine GlobalTheory.CompanionTheory.FineStep.nonempty_equiv_of_jhMult_eq_one _ _
    (CompanionTheory.Lit1.SegRep.PIrr.isIrreducible_piTensor_segTerm σ l) hfl h1 fun X _ _ π hπ h => ?_
  obtain ⟨w, ⟨φ⟩⟩ := SRC.exists_perm_of_isSubquotient_jac hG hd hl σ hσ π hπ (Lift.isSubquotient_jac_multiProd_of_sub σ S h)
  obtain rfl : w = 1 := Lift.perm_eq_one_of_lt_succ w fun i hi => by
    obtain ⟨T, hT0, hTw⟩ := hT k hG h2 hd hl σ hσ i hi
    obtain ⟨S', hS', hle⟩ := SRC.exists_irred_le hd hl σ hσ T hT0
    obtain rfl := huniq S' hS'
    exact hTw π hπ (PiLocalization₂.isSubquotient_jac_of_le σ hle h) w φ
  exact ⟨φ⟩

end CompanionTheory.RgGu.SRC

end
