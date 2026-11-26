module

public import Development.WeilBound.ThetaLifts.Reductions.SiegelCore
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsWeilGroupRestrictExtension
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AvgVanish
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothPsiMinus

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsHermRingRat
set_option linter.unusedSectionVars false

noncomputable section

open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR
open Formalism.UG (cT)
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.KFin

section Abstract

variable {R : Type} [CommRing R] (c : R →+* R) (𝔬 : Subring R)
  {V : Type} [AddCommGroup V] [Module R V]

structure IsHermRing : Prop where
  invol : ∀ a, c (c a) = a
  conj_mem : ∀ a ∈ 𝔬, c a ∈ 𝔬
  nontrivial : Nontrivial R
  artinian : IsArtinianRing R
  noeth : IsNoetherianRing 𝔬
  two : IsUnit (2 : R)
  denom : ∀ a : R, ∃ s ∈ 𝔬, IsUnit s ∧ s * a ∈ 𝔬
  principal : ∀ I : Submodule 𝔬 R, I.FG → (∃ u ∈ I, IsUnit u) → ∃ u : R, IsUnit u ∧ I = Submodule.span 𝔬 {u}

structure IsHerm (h : V → V → R) : Prop where
  add_right : ∀ x y z, h x (y + z) = h x y + h x z
  smul_right : ∀ (a : R) (x y : V), h x (a • y) = a * h x y
  symm : ∀ x y, h y x = c (h x y)

structure IsPerfect (h : V → V → R) : Prop where
  nondeg : ∀ x, (∀ y, h x y = 0) → x = 0
  repr : ∀ f : V →ₗ[R] R, ∃ x, ∀ y, h x y = f y

def IsLat (L : Submodule 𝔬 V) : Prop :=
  L.FG ∧ Submodule.span R (L : Set V) = ⊤

def IsEvenInt (h : V → V → R) (L : Submodule 𝔬 V) : Prop :=
  (∀ x ∈ L, ∀ y ∈ L, h x y ∈ 𝔬) ∧ ∀ x ∈ L, ∃ a ∈ 𝔬, h x x = a + c a

def IsMaxEven (h : V → V → R) (L : Submodule 𝔬 V) : Prop :=
  IsLat 𝔬 L ∧ IsEvenInt c 𝔬 h L ∧ ∀ L' : Submodule 𝔬 V, IsEvenInt c 𝔬 h L' → L ≤ L' → L' ≤ L

structure IsFrame {r : ℕ} (h : V → V → R) (x y : Fin r → V) : Prop where
  xx : ∀ i j, h (x i) (x j) = 0
  yy : ∀ i j, h (y i) (y j) = 0
  xy : ∀ i j, h (x i) (y j) = if i = j then 1 else 0

def IsIsomOnto (h : V → V → R) (p : V ≃ₗ[R] V) (L L' : Submodule 𝔬 V) : Prop :=
  (∀ x y, h (p x) (p y) = h x y) ∧ ∀ z, z ∈ L ↔ p z ∈ L'

def HasBase : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module R V] [Module.Finite R V] (h : V → V → R), IsHerm c h → IsPerfect h →
    (∀ x y, h x x = 0 → h x y ≠ 1) → ∀ L L' : Submodule 𝔬 V, IsMaxEven c 𝔬 h L → IsMaxEven c 𝔬 h L' →
      ∃ p : V ≃ₗ[R] V, IsIsomOnto 𝔬 h p L L'

def FlagTransitive : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module R V] [Module.Finite R V] (h : V → V → R), IsHerm c h → IsPerfect h →
    ∀ (r : ℕ) (x y : Fin r → V), IsFrame h x y → ∀ L L' : Submodule 𝔬 V, IsMaxEven c 𝔬 h L → IsMaxEven c 𝔬 h L' →
      ∃ p : V ≃ₗ[R] V, IsIsomOnto 𝔬 h p L L' ∧
        ∀ j, p (x j) ∈ Submodule.span R (x '' {i | i ≤ j})

def IsAdapted {r : ℕ} (h : V → V → R) (x y : Fin r → V) (L : Submodule 𝔬 V) : Prop :=
  ∀ z, z ∈ L ↔ (∀ i, h (x i) z ∈ 𝔬) ∧ (∀ i, h (y i) z ∈ 𝔬) ∧
    z - ∑ i, h (y i) z • x i - ∑ i, h (x i) z • y i ∈ L

end Abstract

section Place

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {r : ℕ}

def colV (v : HeightOneSpectrum (𝓞 F)) (X : Matrix (Fin n) (Fin r) E) (i : Fin r) : Fin n → Fv F v ⊗[F] E :=
  fun a => inclR (F := F) (Fv F v) (X a i)

def stabLat {v : HeightOneSpectrum (𝓞 F)} (Λ : Submodule (intLoc F E v) (Fin n → Fv F v ⊗[F] E)) :
    Subgroup (GLoc σ J v) where
  carrier := {g | ∀ y, y ∈ Λ ↔ (matHom _ σ J g).1 *ᵥ y ∈ Λ}
  one_mem' := fun y => by simp
  mul_mem' := fun {a b} ha hb y => by
    rw [hb y, ha, map_mul, Units.val_mul, Matrix.mulVec_mulVec]
  inv_mem' := fun {a} ha y => by
    rw [ha ((matHom _ σ J a⁻¹).1 *ᵥ y), Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul]
    simp

theorem mem_stabLat {v : HeightOneSpectrum (𝓞 F)} {Λ : Submodule (intLoc F E v) (Fin n → Fv F v ⊗[F] E)}
    {g : GLoc σ J v} : g ∈ stabLat σ J Λ ↔ ∀ y, y ∈ Λ ↔ (matHom _ σ J g).1 *ᵥ y ∈ Λ := Iff.rfl

def leviMat (A : Type) [CommRing A] [Algebra F A] (X Y : Matrix (Fin n) (Fin r) E)
    (M : Matrix (Fin n) (Fin n) (A ⊗[F] E)) : Matrix (Fin n) (Fin n) (A ⊗[F] E) :=
  let Xa := X.map (inclR (F := F) A)
  let Ya := Y.map (inclR (F := F) A)
  let Xd := (cT (σ : E →+* E) X * J).map (inclR (F := F) A)
  let Yd := (cT (σ : E →+* E) Y * J).map (inclR (F := F) A)
  let P := 1 - Xa * Yd - Ya * Xd
  Xa * diagonal (fun i => (Yd * M * Xa) i i) * Yd + Ya * diagonal (fun i => (Xd * M * Ya) i i) * Xd + P * M * P

end Place

end GlobalTheory.CompanionTheory.KFin

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DualClassTwistNeg
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DualClassTwistNeg
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc

noncomputable section

namespace GlobalTheory.CompanionTheory.ZcDual

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isIrreducible_contra (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) k) V) (hs : IsSmooth π) (hi : π.IsIrreducible) : (contra π).IsIrreducible := by
  exact GlobalTheory.ContraRefl.contra_isIrreducible (GlobalTheory.SqIntUnit.compactOpen_basis k n) (hA k n V π hs hi) hi

theorem dualCl_eq (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (x : IrrGL (k := k)) :
    dualCl x = IrrGL.of (contra x.rep) (isSmooth_contra _) (isIrreducible_contra hA _ x.2.rep.smooth x.2.rep.irr) := by
  unfold dualCl
  rw [dite_eq_left (isIrreducible_contra hA _ x.2.rep.smooth x.2.rep.irr)]

theorem nonempty_equiv_contra_twist (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {n : ℕ} {V : Type} [AddCommGroup V]
    [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V) (hs : IsSmooth π) (hi : π.IsIrreducible)
    {χ χ' : kˣ →* ℂˣ} (hχ : IsSmoothChar χ) (hχ' : IsSmoothChar χ') (h : χ * χ' = 1) :
    Nonempty ((GlobalTheory.SmGL.twist (contra π) (detChar (Fin n) χ')).Equiv (contra (GlobalTheory.SmGL.twist π (detChar (Fin n) χ)))) := by
  have hψ : IsSmoothChar (detChar (Fin n) χ) := hχ.detChar
  have hinv : ∀ g : GL (Fin n) k,
      ((detChar (Fin n) χ' g : ℂˣ) : ℂ) = ((detChar (Fin n) χ g⁻¹ : ℂˣ) : ℂ) := by
    intro g
    have h1 : χ (Matrix.GeneralLinearGroup.det g) * χ' (Matrix.GeneralLinearGroup.det g) = 1 := by
      rw [← MonoidHom.mul_apply, h, MonoidHom.one_apply]
    have h2 : χ' (Matrix.GeneralLinearGroup.det g) = (χ (Matrix.GeneralLinearGroup.det g))⁻¹ :=
      eq_inv_of_mul_eq_one_right h1
    show ((χ' (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) =
      ((χ (Matrix.GeneralLinearGroup.det g⁻¹) : ℂˣ) : ℂ)
    rw [h2, map_inv, map_inv]
  have hdual : ∀ (g : GL (Fin n) k) (l : Module.Dual ℂ V),
      (GlobalTheory.SmGL.twist π (detChar (Fin n) χ)).dual g l = ((detChar (Fin n) χ g⁻¹ : ℂˣ) : ℂ) • π.dual g l := by
    intro g l
    apply LinearMap.ext
    intro v
    show l (((detChar (Fin n) χ g⁻¹ : ℂˣ) : ℂ) • π g⁻¹ v) = ((detChar (Fin n) χ g⁻¹ : ℂˣ) : ℂ) • l (π g⁻¹ v)
    exact map_smul l _ _
  have hker : ∀ g : GL (Fin n) k, g ∈ (detChar (Fin n) χ).ker →
      ((detChar (Fin n) χ g⁻¹ : ℂˣ) : ℂ) = 1 := by
    intro g hg
    rw [MonoidHom.mem_ker] at hg
    rw [map_inv, hg, inv_one, Units.val_one]
  have hkn : ((detChar (Fin n) χ).ker : Set (GL (Fin n) k)) ∈ nhds (1 : GL (Fin n) k) :=
    IsOpen.mem_nhds hψ (Subgroup.one_mem _)
  have heq : smoothPart π.dual = smoothPart (GlobalTheory.SmGL.twist π (detChar (Fin n) χ)).dual := by
    ext l
    constructor
    · intro hl
      apply mem_smoothPart_of_nhds
      refine Filter.mem_of_superset (Filter.inter_mem (IsOpen.mem_nhds hl (by
        show π.dual 1 l = l
        rw [map_one]
        rfl)) hkn) ?_
      rintro g ⟨hg1, hg2⟩
      have h3 : π.dual g l = l := hg1
      show (GlobalTheory.SmGL.twist π (detChar (Fin n) χ)).dual g l = l
      rw [hdual, hker g hg2, one_smul]
      exact h3
    · intro hl
      apply mem_smoothPart_of_nhds
      refine Filter.mem_of_superset (Filter.inter_mem (IsOpen.mem_nhds hl (by
        show (GlobalTheory.SmGL.twist π (detChar (Fin n) χ)).dual 1 l = l
        rw [map_one]
        rfl)) hkn) ?_
      rintro g ⟨hg1, hg2⟩
      have h3 : (GlobalTheory.SmGL.twist π (detChar (Fin n) χ)).dual g l = l := hg1
      rw [hdual, hker g hg2, one_smul] at h3
      show π.dual g l = l
      exact h3
  have htw : ∀ (g : GL (Fin n) k) (l : smoothPart π.dual),
      ((GlobalTheory.SmGL.twist (contra π) (detChar (Fin n) χ') g l : smoothPart π.dual) : Module.Dual ℂ V) =
        ((detChar (Fin n) χ' g : ℂˣ) : ℂ) • ((contra π g l : smoothPart π.dual) : Module.Dual ℂ V) :=
    fun _ _ => rfl
  have htw2 : ∀ (g : GL (Fin n) k) (v : V),
      (GlobalTheory.SmGL.twist π (detChar (Fin n) χ)) g v = ((detChar (Fin n) χ g : ℂˣ) : ℂ) • π g v :=
    fun _ _ => rfl
  exact ⟨{ toLinearEquiv := LinearEquiv.ofEq _ _ heq
           isIntertwining' := fun g => by
             apply LinearMap.ext
             intro l
             apply Subtype.ext
             apply LinearMap.ext
             intro v
             simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.coe_ofEq_apply, htw,
               LinearMap.smul_apply, contra_apply, htw2, map_smul, smul_eq_mul, hinv] }⟩

private theorem comp_intertwiningMap_mem_smoothPart_dual {G V W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (f : ρ.IntertwiningMap σ)
    (l : Module.Dual ℂ W) (hl : l ∈ smoothPart σ.dual) : l ∘ₗ f.toLinearMap ∈ smoothPart ρ.dual := by
  apply mem_smoothPart_of_nhds
  refine Filter.mem_of_superset (IsOpen.mem_nhds hl (by
    show σ.dual 1 l = l
    rw [map_one]
    rfl)) ?_
  intro g hg
  have h : σ.dual g l = l := hg
  show ρ.dual g (l ∘ₗ f.toLinearMap) = l ∘ₗ f.toLinearMap
  refine LinearMap.ext fun v => ?_
  calc (ρ.dual g (l ∘ₗ f.toLinearMap)) v = l (f.toLinearMap (ρ g⁻¹ v)) := rfl
    _ = l (σ g⁻¹ (f v)) := by
      rw [Representation.IntertwiningMap.toLinearMap_apply, Representation.IntertwiningMap.isIntertwining]
    _ = σ.dual g l (f v) := rfl
    _ = (l ∘ₗ f.toLinearMap) v := by
      rw [h, LinearMap.comp_apply, Representation.IntertwiningMap.toLinearMap_apply]

private theorem nonempty_contra_equiv_of_equiv {G V W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (e : ρ.Equiv σ) :
    Nonempty ((contra σ).Equiv (contra ρ)) := by
  refine ⟨{ toFun := fun l => ⟨l.1 ∘ₗ e.toIntertwiningMap.toLinearMap,
              comp_intertwiningMap_mem_smoothPart_dual e.toIntertwiningMap l.1 l.2⟩
            map_add' := fun _ _ => rfl
            map_smul' := fun _ _ => rfl
            invFun := fun l => ⟨l.1 ∘ₗ e.symm.toIntertwiningMap.toLinearMap,
              comp_intertwiningMap_mem_smoothPart_dual e.symm.toIntertwiningMap l.1 l.2⟩
            left_inv := fun l => Subtype.ext (LinearMap.ext fun w => by
              show l.1 (e.toIntertwiningMap.toLinearMap (e.symm.toIntertwiningMap.toLinearMap w)) = l.1 w
              simp only [Representation.IntertwiningMap.toLinearMap_apply,
                Representation.Equiv.coe_toIntertwiningMap, Representation.Equiv.apply_symm_apply])
            right_inv := fun l => Subtype.ext (LinearMap.ext fun v => by
              show l.1 (e.symm.toIntertwiningMap.toLinearMap (e.toIntertwiningMap.toLinearMap v)) = l.1 v
              simp only [Representation.IntertwiningMap.toLinearMap_apply,
                Representation.Equiv.coe_toIntertwiningMap, Representation.Equiv.symm_apply_apply])
            isIntertwining' := fun g => by
              apply LinearMap.ext
              intro l
              apply Subtype.ext
              apply LinearMap.ext
              intro v
              simp only [LinearMap.comp_apply, LinearMap.coe_mk, AddHom.coe_mk, contra_apply,
                Representation.IntertwiningMap.toLinearMap_apply,
                Representation.IntertwiningMap.isIntertwining] }⟩

theorem dualCl_nu : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (x : IrrGL (k := k)) (s : ℂ), dualCl (x.nu s) = (dualCl x).nu (-s) := by
  intro k _ _ _ _ hA x s
  have hs' : IsSmoothChar (absPow k s) := isSmoothChar_of_isUnram (isUnram_absPow k s)
  have hn' : IsSmoothChar (absPow k (-s)) := isSmoothChar_of_isUnram (isUnram_absPow k (-s))
  have hmul : absPow k s * absPow k (-s) = 1 := by
    rw [absPow_neg, mul_inv_cancel]
  have hψ : IsSmoothChar (detChar (Fin x.fst) (absPow k s)) := hs'.detChar
  have hψn : IsSmoothChar (detChar (Fin x.fst) (absPow k (-s))) := hn'.detChar
  obtain ⟨e1⟩ : Nonempty ((x.nu s).rep.Equiv (GlobalTheory.SmGL.twist x.rep (detChar (Fin x.fst) (absPow k s)))) :=
    IrrRep.nonempty_equiv_rep (irrTwist x.snd.rep (detChar (Fin x.fst) (absPow k s)) hψ)
  obtain ⟨e2⟩ := nonempty_contra_equiv_of_equiv e1
  obtain ⟨e3⟩ := nonempty_equiv_contra_twist hA x.rep x.2.rep.smooth x.2.rep.irr hs' hn' hmul
  have hc := isIrreducible_contra hA _ x.2.rep.smooth x.2.rep.irr
  obtain ⟨e4⟩ := IrrRep.nonempty_equiv_rep
    (⟨_, contra x.rep, isSmooth_contra _, hc⟩ : IrrRep (GL (Fin x.fst) k))
  have e5 := twistEquiv e4 (detChar (Fin x.fst) (absPow k (-s)))
  rw [dualCl_eq hA, dualCl_eq hA]
  refine Sigma.ext ?_ ?_
  · rfl
  apply heq_of_eq
  exact IrrRep.cl_eq_iff.mpr ⟨(e2.symm.trans e3.symm).trans e5.symm⟩

end GlobalTheory.CompanionTheory.ZcDual

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DualClassTwistNegStatement
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dual_class_twist_neg : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (x : IrrGL (k := k)) (s : ℂ), dualCl (x.nu s) = (dualCl x).nu (-s) := by
  first | exact @GlobalTheory.CompanionTheory.ZcDual.dualCl_nu | exact GlobalTheory.CompanionTheory.ZcDual.dualCl_nu | (intros; apply GlobalTheory.CompanionTheory.ZcDual.dualCl_nu <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwasawaDecompParabolicMaximalCompact
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwasawaDecompParabolicMaximalCompact
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPsiPG

theorem exists_Qp_mul_KO : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (g : GL (Fin (i + t)) k), ∃ q : Qp k i t, ∃ κ ∈ GlobalTheory.SplitWeil.KO k (Fin (i + t)), g = (q : GL (Fin (i + t)) k) * κ := by
  intro k _ _ _ _ i t g
  obtain ⟨u, l, w, hw, hg⟩ := GlobalTheory.SmGL.UnitInd.exists_iwasawa
    (GlobalTheory.SmGL.two (GlobalTheory.SmGL.stdSum (rfl : i + t = i + t))) g
  refine ⟨⟨(u : GL (Fin (i + t)) k) * GlobalTheory.SmGL.leviEmb k _ l, ?_⟩, w, hw, hg⟩
  exact Subgroup.mul_mem _ (GlobalTheory.SmGL.unipRad_le_parab k _ u.2)
    (GlobalTheory.SmGL.leviEmb_mem_parab k _ l)

end GlobalTheory.CompanionTheory.BZPsiPG
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwasawaDecompParabolicMaximalCompactStatement
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iwasawa_decomp_parabolic_maximal_compact : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (g : GL (Fin (i + t)) k), ∃ q : Qp k i t, ∃ κ ∈ GlobalTheory.SplitWeil.KO k (Fin (i + t)), g = (q : GL (Fin (i + t)) k) * κ := by
  first | exact @GlobalTheory.CompanionTheory.BZPsiPG.exists_Qp_mul_KO | exact GlobalTheory.CompanionTheory.BZPsiPG.exists_Qp_mul_KO | (intros; apply GlobalTheory.CompanionTheory.BZPsiPG.exists_Qp_mul_KO <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MulVecMidBlockDecomp
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MulVecMidBlockDecomp
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPsiPG

theorem qp_mulVec_midV_exists_top (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (i t : ℕ) (q : Qp k i t) (v : Fin t → k) :
    ∃ x : Fin i → k, ((q : GL (Fin (i + t)) k) : Matrix (Fin (i + t)) (Fin (i + t)) k).mulVec (midV k i t v) =
      topV k i t x + midV k i t ((((qBlocks k i t q).2 : GL (Fin t) k) : Matrix (Fin t) (Fin t) k).mulVec v) := by
  refine ⟨fun r => ((q : GL (Fin (i + t)) k) : Matrix (Fin (i + t)) (Fin (i + t)) k).mulVec
    (GlobalTheory.CompanionTheory.BZPsiPG.midV k i t v) (Fin.castAdd t r), ?_⟩
  rw [GlobalTheory.CompanionTheory.BZPsiPG.topV_add_midV]
  funext r
  refine Fin.addCases (fun a => ?_) (fun b => ?_) r
  · rw [Fin.append_left]
  · rw [Fin.append_right]
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_add, GlobalTheory.CompanionTheory.BZPsiPG.midV, Fin.append_left,
      Fin.append_right, Pi.zero_apply, mul_zero, Finset.sum_const_zero, zero_add]
    rfl

end GlobalTheory.CompanionTheory.BZPsiPG
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MulVecMidBlockDecompStatement
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mulVec_mid_block_decomp : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (q : Qp k i t) (v : Fin t → k), ∃ x : Fin i → k, ((q : GL (Fin (i + t)) k) : Matrix (Fin (i + t)) (Fin (i + t)) k).mulVec (midV k i t v) = topV k i t x + midV k i t ((((qBlocks k i t q).2 : GL (Fin t) k) : Matrix (Fin t) (Fin t) k).mulVec v) := by
  first | exact @GlobalTheory.CompanionTheory.BZPsiPG.qp_mulVec_midV_exists_top | exact GlobalTheory.CompanionTheory.BZPsiPG.qp_mulVec_midV_exists_top | (intros; apply GlobalTheory.CompanionTheory.BZPsiPG.qp_mulVec_midV_exists_top <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousLeviUnipotentProj
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousLeviUnipotentProj
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPsiPG.Cont

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem continuous_colMat_entry (n : ℕ) (a b : Fin (n + 1)) :
    Continuous fun y : Fin n → k => colMat k n y a b := by
  unfold colMat
  split_ifs
  · induction a using Fin.lastCases with
    | last => simp only [Fin.lastCases_last]; exact continuous_const
    | cast i => simp only [Fin.lastCases_castSucc]; exact continuous_apply i
  · exact continuous_const

theorem continuous_uM_val (n : ℕ) : Continuous fun y : Fin n → k =>
    (((uM k n y : Mir k n) : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) := by
  have h : (fun y : Fin n → k =>
      (((uM k n y : Mir k n) : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k)) =
      fun y => 1 + colMat k n y := by
    funext y
    rfl
  rw [h]
  refine continuous_const.add (continuous_matrix fun a b => ?_)
  exact continuous_colMat_entry k n a b

theorem uM_inv (n : ℕ) (y : Fin n → k) : (uM k n y)⁻¹ = uM k n (-y) := by
  have h : uM k n (-y) * uM k n y = 1 := by
    rw [← uM_add, neg_add_cancel, uM_zero]
  exact (eq_inv_of_mul_eq_one_left h).symm

theorem continuous_uM (n : ℕ) : Continuous (uM k n) := by
  apply continuous_induced_rng.2
  refine Units.continuous_iff.2 ⟨continuous_uM_val k n, ?_⟩
  have h : ∀ y : Fin n → k, ((uM k n y : GL (Fin (n + 1)) k))⁻¹ =
      (uM k n (-y) : GL (Fin (n + 1)) k) := by
    intro y
    rw [← uM_inv k n y, Subgroup.coe_inv]
  simp only [Function.comp_apply, h]
  exact (continuous_uM_val k n).comp continuous_neg

end GlobalTheory.CompanionTheory.BZPsiPG.Cont

namespace GlobalTheory.CompanionTheory.BZPsiPG

theorem continuous_levi_uM_mirProj : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ), Continuous (levi k n) ∧ Continuous (uM k n) ∧ Continuous (mirabolicProjection k n) := by
  intro k _ _ _ _ n
  exact ⟨GlobalTheory.CompanionTheory.BZMirFun.continuous_levi k n, Cont.continuous_uM k n,
    GlobalTheory.CompanionTheory.BZMirFun.continuous_mirProj k n⟩

end GlobalTheory.CompanionTheory.BZPsiPG
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousLeviUnipotentProjStatement
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_levi_unipotent_proj : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ), Continuous (levi k n) ∧ Continuous (uM k n) ∧ Continuous (mirabolicProjection k n) := by
  first | exact @GlobalTheory.CompanionTheory.BZPsiPG.continuous_levi_uM_mirProj | exact GlobalTheory.CompanionTheory.BZPsiPG.continuous_levi_uM_mirProj | (intros; apply GlobalTheory.CompanionTheory.BZPsiPG.continuous_levi_uM_mirProj <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SumOverCompactCosetsJacquetKernel
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SumOverCompactCosetsJacquetKernel
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.TwistedAverage

theorem sum_reps_eq_sum_out {H V : Type} [Group H] [AddCommGroup V] (K : Subgroup H)
    [Fintype (H ⧸ K)] (T : Finset H) (hT : ∀ x : H, ∃! t, t ∈ T ∧ t⁻¹ * x ∈ K) (f : H → V)
    (hf : ∀ x, ∀ k ∈ K, f (x * k) = f x) :
    ∑ t ∈ T, f t = ∑ q : H ⧸ K, f q.out := by
  refine Finset.sum_bij (fun t _ => (QuotientGroup.mk t : H ⧸ K)) (fun _ _ => Finset.mem_univ _)
    ?_ ?_ ?_
  · intro a ha b hb hab
    exact (hT b).unique ⟨ha, QuotientGroup.eq.1 hab⟩ ⟨hb, by simp⟩
  · intro q _
    obtain ⟨t, ⟨ht, hx⟩, -⟩ := hT q.out
    refine ⟨t, ht, ?_⟩
    rw [← QuotientGroup.out_eq' q]
    exact QuotientGroup.eq.2 hx
  · intro t _
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul K t
    rw [hh, hf _ _ h.2]

theorem sum_reps_eq_zero_of_mem_twKer :
    ∀ {G Z : Type} [Group G] [AddCommGroup Z] [Module ℂ Z] [TopologicalSpace G] [IsTopologicalGroup G] (ρ : Representation ℂ G Z), IsSmooth ρ → ∀ (L : Subgroup G), IsCompact (L : Set G) → ∀ v : Z, v ∈ twKer ρ L 1 → ∀ (K : Subgroup L) (T : Finset L), IsOpen (K : Set L) → (∀ x ∈ K, ρ (x : G) v = v) → (∀ x : L, ∃! t, t ∈ T ∧ t⁻¹ * x ∈ K) → ∑ t ∈ T, ρ (t : G) v = 0 := by
  intro G Z _ _ _ _ _ ρ hρ L hL v hv K T hKo hKv hT
  classical
  haveI : CompactSpace L := isCompact_iff_compactSpace.mp hL
  have hθ : IsOpen (((1 : L →* ℂˣ).ker : Subgroup L) : Set L) := by
    rw [MonoidHom.ker_one]
    exact isOpen_univ
  obtain ⟨M, hM, hsum⟩ := exists_sum_eq_zero hρ hL (1 : L →* ℂˣ) hθ hv
  haveI : Finite (L ⧸ K) := Subgroup.quotient_finite_of_isOpen _ hKo
  haveI hKf : K.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  haveI : Fintype (L ⧸ K) := Fintype.ofFinite _
  set C : Subgroup L := (M ⊓ K).normalCore with hC
  haveI : C.Normal := Subgroup.normalCore_normal _
  haveI : C.FiniteIndex := inferInstance
  haveI : Fintype (L ⧸ C) := Fintype.ofFinite _
  have hCM : C ≤ M ⊓ K := Subgroup.normalCore_le _
  haveI : Finite (K ⧸ C.subgroupOf K) := inferInstance
  haveI : Fintype (K ⧸ C.subgroupOf K) := Fintype.ofFinite _
  have hf : ∀ x : L, ∀ k ∈ K, twOrbit ρ L 1 v (x * k) = twOrbit ρ L 1 v x := by
    intro x k hk
    simp only [twOrbit, MonoidHom.one_apply, mul_one, inv_one, Units.val_one, one_smul,
      Subgroup.coe_mul, map_mul, Module.End.mul_apply, hKv k hk]
  have h0 := hsum C (hCM.trans inf_le_left)
  rw [sum_out_refine (hCM.trans inf_le_right) (twOrbit ρ L 1 v) hf] at h0
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_eq_zero] at h0
  have h1 : ∑ q : L ⧸ K, twOrbit ρ L 1 v q.out = 0 := by
    rcases h0 with h0 | h0
    · exact absurd h0 (Nat.cast_ne_zero.2 Fintype.card_ne_zero)
    · exact h0
  have h2 := sum_reps_eq_sum_out K T hT (twOrbit ρ L 1 v) hf
  rw [h1] at h2
  simpa [twOrbit] using h2

end GlobalTheory.CompanionTheory.TwistedAverage
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SumOverCompactCosetsJacquetKernelStatement
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_over_compact_cosets_jacquet_kernel : ∀ {G Z : Type} [Group G] [AddCommGroup Z] [Module ℂ Z] [TopologicalSpace G] [IsTopologicalGroup G] (ρ : Representation ℂ G Z), IsSmooth ρ → ∀ (L : Subgroup G), IsCompact (L : Set G) → ∀ v : Z, v ∈ twKer ρ L 1 → ∀ (K : Subgroup L) (T : Finset L), IsOpen (K : Set L) → (∀ x ∈ K, ρ (x : G) v = v) → (∀ x : L, ∃! t, t ∈ T ∧ t⁻¹ * x ∈ K) → ∑ t ∈ T, ρ (t : G) v = 0 := by
  first | exact @GlobalTheory.CompanionTheory.TwistedAverage.sum_reps_eq_zero_of_mem_twKer | exact GlobalTheory.CompanionTheory.TwistedAverage.sum_reps_eq_zero_of_mem_twKer | (intros; apply GlobalTheory.CompanionTheory.TwistedAverage.sum_reps_eq_zero_of_mem_twKer <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsInducedSectionSupportedOpen
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsInducedSectionSupportedOpen
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.HBBump

theorem exists_bump : ∀ {G Z : Type} [Group G] [AddCommGroup Z] [Module ℂ Z] [TopologicalSpace G]
    [IsTopologicalGroup G] (H : Subgroup G) (ρ : Representation ℂ H Z) (B : Subgroup G),
    IsOpen (B : Set G) → IsCompact (B : Set G) → ∀ z : Z, (∀ h : H, (h : G) ∈ B → ρ h z = z) →
    ∃ b : cIndSpace H ρ, (∀ (h : H) (β : G), β ∈ B → b.1.1.1 ((h : G) * β) = ρ h z) ∧
      ∀ p : G, (¬ ∃ h : H, ∃ β ∈ B, p = (h : G) * β) → b.1.1.1 p = 0 := by
  intro G Z _ _ _ _ _ H ρ B hBo hBc z hz
  classical

  have hwell : ∀ (h h' : H) (β β' : G), β ∈ B → β' ∈ B → (h : G) * β = (h' : G) * β' →
      ρ h z = ρ h' z := by
    intro h h' β β' hβ hβ' e
    have ha : ((h'⁻¹ * h : H) : G) ∈ B := by
      have : ((h'⁻¹ * h : H) : G) = β' * β⁻¹ := by
        push_cast
        rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← e]
        group
      rw [this]
      exact B.mul_mem hβ' (B.inv_mem hβ)
    have h1 := hz _ ha
    have h2 : h = h' * (h'⁻¹ * h) := by group
    rw [h2, map_mul, Module.End.mul_apply, h1]
  let P : G → Prop := fun p => ∃ h : H, ∃ β ∈ B, p = (h : G) * β
  let f : G → Z := fun p => if hp : P p then ρ hp.choose z else 0
  have hval : ∀ (h : H) (β : G), β ∈ B → f ((h : G) * β) = ρ h z := by
    intro h β hβ
    have hp : P ((h : G) * β) := ⟨h, β, hβ, rfl⟩
    obtain ⟨β', hβ', e⟩ := hp.choose_spec
    simp only [f, dif_pos hp]
    exact hwell _ _ _ _ hβ' hβ e.symm
  have hzero : ∀ p, ¬ P p → f p = 0 := fun p hp => by simp only [f, dif_neg hp]
  have hleft : ∀ (h : H) (g : G), f ((h : G) * g) = ρ h (f g) := by
    intro h g
    by_cases hg : P g
    · obtain ⟨h', β, hβ, rfl⟩ := hg
      have : (h : G) * ((h' : G) * β) = ((h * h' : H) : G) * β := by push_cast; group
      rw [this, hval _ _ hβ, hval _ _ hβ, map_mul, Module.End.mul_apply]
    · have hn : ¬ P ((h : G) * g) := by
        rintro ⟨h', β, hβ, e⟩
        refine hg ⟨h⁻¹ * h', β, hβ, ?_⟩
        push_cast
        rw [mul_assoc, ← e]
        group
      rw [hzero _ hn, hzero _ hg, map_zero]
  have hright : ∀ (p : G), ∀ x ∈ B, f (p * x) = f p := by
    intro p x hx
    by_cases hp : P p
    · obtain ⟨h, β, hβ, rfl⟩ := hp
      rw [mul_assoc, hval _ _ (B.mul_mem hβ hx), hval _ _ hβ]
    · have hn : ¬ P (p * x) := by
        rintro ⟨h, β, hβ, e⟩
        refine hp ⟨h, β * x⁻¹, B.mul_mem hβ (B.inv_mem hx), ?_⟩
        rw [← mul_assoc, ← e]
        group
      rw [hzero _ hn, hzero _ hp]
  let F : indSpace H ρ := ⟨f, hleft⟩
  have hsm : F ∈ smoothPart (ind H ρ) := by
    let T : Subgroup G :=
      { carrier := {g | ind H ρ g F = F}
        mul_mem' := by
          intro a b ha hb
          simp only [Set.mem_setOf_eq, map_mul, Module.End.mul_apply] at *
          rw [hb, ha]
        one_mem' := by simp
        inv_mem' := by
          intro a ha
          simp only [Set.mem_setOf_eq] at *
          conv_lhs => rw [← ha]
          rw [← Module.End.mul_apply, ← map_mul]
          simp }
    have hBT : (B : Set G) ⊆ T := by
      intro x hx
      show ind H ρ x F = F
      apply Subtype.ext
      funext p
      exact hright p x hx
    exact T.isOpen_of_mem_nhds (g := 1)
      (Filter.mem_of_superset (hBo.mem_nhds B.one_mem) hBT)
  refine ⟨⟨⟨F, hsm⟩, ⟨(B : Set G), hBc, ?_⟩⟩, hval, hzero⟩
  intro g hg
  by_contra hc
  refine hg (hzero g ?_)
  rintro ⟨h, β, hβ, e⟩
  exact hc ⟨h, h.2, β, hβ, e⟩

end GlobalTheory.CompanionTheory.HBBump
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsInducedSectionSupportedOpenStatement
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_induced_section_supported_open : ∀ {G Z : Type} [Group G] [AddCommGroup Z] [Module ℂ Z] [TopologicalSpace G] [IsTopologicalGroup G] (H : Subgroup G) (ρ : Representation ℂ H Z) (B : Subgroup G), IsOpen (B : Set G) → IsCompact (B : Set G) → ∀ z : Z, (∀ h : H, (h : G) ∈ B → ρ h z = z) → ∃ b : cIndSpace H ρ, (∀ (h : H) (β : G), β ∈ B → b.1.1.1 ((h : G) * β) = ρ h z) ∧ ∀ p : G, (¬ ∃ h : H, ∃ β ∈ B, p = (h : G) * β) → b.1.1.1 p = 0 := by
  first | exact @GlobalTheory.CompanionTheory.HBBump.exists_bump | exact GlobalTheory.CompanionTheory.HBBump.exists_bump | (intros; apply GlobalTheory.CompanionTheory.HBBump.exists_bump <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentTopMemParabolic
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentTopMemParabolic
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPsiPG.TopCol

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem entry (n : ℕ) (w : Fin n → k) (a b : Fin (n + 1)) :
    ((uM k n w : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) a b =
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) a b + colMat k n w a b := rfl

theorem ePG_true_eq (i t : ℕ) (b : Fin t) :
    ePG i t ⟨true, b⟩ = Fin.castSucc (Fin.natAdd i b) := by
  first
  | rfl
  | (ext; simp [GlobalTheory.BZMir.Leib.ePG])

theorem ePG_false_eq (i t : ℕ) (a : Fin i) :
    ePG i t ⟨false, Fin.castSucc a⟩ = Fin.castSucc (Fin.castAdd t a) := by
  have h : GlobalTheory.BZMir.Leib.ePG i t ⟨false, Fin.castSucc a⟩ =
      ((Equiv.sumCongr (finSumFinEquiv.symm : Fin (i + 1) ≃ Fin i ⊕ Fin 1) (Equiv.refl (Fin t))).trans
        ((Equiv.sumAssoc (Fin i) (Fin 1) (Fin t)).trans
          ((Equiv.sumCongr (Equiv.refl (Fin i)) (Equiv.sumComm (Fin 1) (Fin t))).trans
            ((Equiv.sumAssoc (Fin i) (Fin t) (Fin 1)).symm.trans
              ((Equiv.sumCongr finSumFinEquiv (Equiv.refl (Fin 1))).trans finSumFinEquiv)))))
        (Sum.inl (Fin.castSucc a)) := rfl
  rw [h]
  ext
  simp [finSumFinEquiv_symm_apply_castSucc]

theorem ePG_true_ne_last (i t : ℕ) (b : Fin t) : ePG i t ⟨true, b⟩ ≠ Fin.last (i + t) := by
  rw [GlobalTheory.CompanionTheory.BZPsiPG.TopCol.ePG_true_eq]
  exact Fin.castSucc_ne_last _

theorem mem (i t : ℕ) (x : Fin i → k) : uM k (i + t) (topV k i t x) ∈ HPG k i t := by
  show ((GlobalTheory.CompanionTheory.BZPsiPG.uM k (i + t) (GlobalTheory.CompanionTheory.BZPsiPG.topV k i t x) : GL (Fin (i + t + 1)) k)) ∈
    GlobalTheory.SmGL.parab k (GlobalTheory.BZMir.Leib.ePG i t)
  rw [GlobalTheory.SmGL.mem_parab_iff]
  intro a b p q hba
  cases a <;> cases b
  all_goals first
    | exact absurd hba (by decide)
    | (simp at hba; done)
    | skip
  have hne : GlobalTheory.BZMir.Leib.ePG i t ⟨true, p⟩ ≠ GlobalTheory.BZMir.Leib.ePG i t ⟨false, q⟩ := by
    intro h
    have h' : true = false := congrArg Sigma.fst ((GlobalTheory.BZMir.Leib.ePG i t).injective h)
    cases h'
  have hr := GlobalTheory.CompanionTheory.BZPsiPG.TopCol.ePG_true_eq i t p
  rw [GlobalTheory.CompanionTheory.BZPsiPG.TopCol.entry, Matrix.one_apply_ne hne, zero_add, hr]
  simp only [GlobalTheory.BZMir.colMat]
  split_ifs
  · rw [Fin.lastCases_castSucc]
    simp [GlobalTheory.CompanionTheory.BZPsiPG.topV]
  · rfl

theorem fst (i t : ℕ) (x : Fin i → k) :
    (pgProj k i t ⟨uM k (i + t) (topV k i t x), mem i t x⟩).1 = uM k i x := by
  apply Subtype.ext
  apply Units.ext
  ext a b
  change ((GlobalTheory.CompanionTheory.BZPsiPG.uM k (i + t) (GlobalTheory.CompanionTheory.BZPsiPG.topV k i t x) : GL (Fin (i + t + 1)) k) :
      Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k)
      (GlobalTheory.BZMir.Leib.ePG i t ⟨false, a⟩) (GlobalTheory.BZMir.Leib.ePG i t ⟨false, b⟩) = _
  have h1 : (1 : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k)
      (GlobalTheory.BZMir.Leib.ePG i t ⟨false, a⟩) (GlobalTheory.BZMir.Leib.ePG i t ⟨false, b⟩) =
      (1 : Matrix (Fin (i + 1)) (Fin (i + 1)) k) a b := by
    simp [Matrix.one_apply]
  have h2 : GlobalTheory.BZMir.colMat k (i + t) (GlobalTheory.CompanionTheory.BZPsiPG.topV k i t x)
      (GlobalTheory.BZMir.Leib.ePG i t ⟨false, a⟩) (GlobalTheory.BZMir.Leib.ePG i t ⟨false, b⟩) =
      GlobalTheory.BZMir.colMat k i x a b := by
    simp only [GlobalTheory.BZMir.colMat, GlobalTheory.BZMir.Leib.ePG_false_eq_last_iff]
    split_ifs with hb
    · induction a using Fin.lastCases with
      | last => rw [GlobalTheory.BZMir.Leib.ePG_false_last, Fin.lastCases_last, Fin.lastCases_last]
      | cast c =>
        rw [GlobalTheory.CompanionTheory.BZPsiPG.TopCol.ePG_false_eq, Fin.lastCases_castSucc,
          Fin.lastCases_castSucc]
        simp [GlobalTheory.CompanionTheory.BZPsiPG.topV]
    · rfl
  rw [GlobalTheory.CompanionTheory.BZPsiPG.TopCol.entry,
    GlobalTheory.CompanionTheory.BZPsiPG.TopCol.entry, h1, h2]

theorem snd (i t : ℕ) (x : Fin i → k) :
    (pgProj k i t ⟨uM k (i + t) (topV k i t x), mem i t x⟩).2 = 1 := by
  apply Units.ext
  ext a b
  change ((GlobalTheory.CompanionTheory.BZPsiPG.uM k (i + t) (GlobalTheory.CompanionTheory.BZPsiPG.topV k i t x) : GL (Fin (i + t + 1)) k) :
      Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k)
      (GlobalTheory.BZMir.Leib.ePG i t ⟨true, a⟩) (GlobalTheory.BZMir.Leib.ePG i t ⟨true, b⟩) =
      (1 : Matrix (Fin t) (Fin t) k) a b
  rw [GlobalTheory.CompanionTheory.BZPsiPG.TopCol.entry]
  simp only [GlobalTheory.BZMir.colMat, if_neg (GlobalTheory.CompanionTheory.BZPsiPG.TopCol.ePG_true_ne_last i t b), add_zero]
  simp [Matrix.one_apply]

theorem main : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ)
    (x : Fin i → k), ∃ h : uM k (i + t) (topV k i t x) ∈ HPG k i t, pgProj k i t ⟨_, h⟩ = (uM k i x, 1) := by
  intro k _ _ _ _ i t x
  exact ⟨GlobalTheory.CompanionTheory.BZPsiPG.TopCol.mem i t x,
    Prod.ext (GlobalTheory.CompanionTheory.BZPsiPG.TopCol.fst i t x)
      (GlobalTheory.CompanionTheory.BZPsiPG.TopCol.snd i t x)⟩

end GlobalTheory.CompanionTheory.BZPsiPG.TopCol

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentTopMemParabolicStatement
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotent_top_mem_parabolic : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (x : Fin i → k), ∃ h : uM k (i + t) (topV k i t x) ∈ HPG k i t, pgProj k i t ⟨_, h⟩ = (uM k i x, 1) := by
  first | exact @GlobalTheory.CompanionTheory.BZPsiPG.TopCol.main | exact GlobalTheory.CompanionTheory.BZPsiPG.TopCol.main | (intros; apply GlobalTheory.CompanionTheory.BZPsiPG.TopCol.main <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviBlockMemParabolic
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviBlockMemParabolic
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPsiPG.QLevi

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem ePG_true_eq (i t : ℕ) (b : Fin t) :
    ePG i t ⟨true, b⟩ = Fin.castSucc (Fin.natAdd i b) := by
  apply Fin.ext
  simp [ePG]

theorem ePG_false_eq (i t : ℕ) (a : Fin i) :
    ePG i t ⟨false, Fin.castSucc a⟩ = Fin.castSucc (Fin.castAdd t a) := by
  apply Fin.ext
  simp [ePG, finSumFinEquiv_symm_apply_castSucc]

theorem two_true_eq (i t : ℕ) (b : Fin t) :
    two (stdSum (rfl : i + t = i + t)) ⟨true, b⟩ = Fin.natAdd i b := by
  apply Fin.ext
  simp

theorem two_false_eq (i t : ℕ) (a : Fin i) :
    two (stdSum (rfl : i + t = i + t)) ⟨false, a⟩ = Fin.castAdd t a := by
  apply Fin.ext
  simp

theorem levi_entry (n : ℕ) (g : GL (Fin n) k) (a b : Fin n) :
    ((levi k n g : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.castSucc a) (Fin.castSucc b) =
      (g : Matrix (Fin n) (Fin n) k) a b := by
  show glEmbMat k n (g : Matrix (Fin n) (Fin n) k) _ _ = _
  simp [glEmbMat]

theorem levi_entry_last_col (n : ℕ) (g : GL (Fin n) k) (a : Fin n) :
    ((levi k n g : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.castSucc a) (Fin.last n) = 0 := by
  show glEmbMat k n (g : Matrix (Fin n) (Fin n) k) _ _ = _
  simp [glEmbMat]

theorem levi_entry_last_row (n : ℕ) (g : GL (Fin n) k) (b : Fin n) :
    ((levi k n g : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) (Fin.castSucc b) = 0 := by
  show glEmbMat k n (g : Matrix (Fin n) (Fin n) k) _ _ = _
  simp [glEmbMat]

theorem levi_entry_last (n : ℕ) (g : GL (Fin n) k) :
    ((levi k n g : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) (Fin.last n) = 1 := by
  show glEmbMat k n (g : Matrix (Fin n) (Fin n) k) _ _ = _
  simp [glEmbMat]

theorem levi_mem_HPG (i t : ℕ) (q : Qp k i t) : levi k (i + t) (q : GL (Fin (i + t)) k) ∈ HPG k i t := by
  show ((levi k (i + t) (q : GL (Fin (i + t)) k) : Mir k (i + t)) : GL (Fin (i + t + 1)) k) ∈ parab k (ePG i t)
  refine mem_parab_iff.2 ?_
  intro a c x y hac
  obtain ⟨rfl, rfl⟩ : a = true ∧ c = false := by
    revert hac; cases a <;> cases c <;> decide
  have hx : ePG i t ⟨true, x⟩ = Fin.castSucc (Fin.natAdd i (x : Fin t)) := ePG_true_eq i t x
  rw [hx]
  induction (y : Fin (i + 1)) using Fin.lastCases with
  | last =>
    rw [ePG_false_last]
    exact levi_entry_last_col _ _ _
  | cast y =>
    rw [ePG_false_eq, levi_entry]
    have := mem_parab_iff.1 q.2 true false (x : Fin t) (y : Fin i) (by decide)
    rwa [two_true_eq, two_false_eq] at this

theorem pgProj_levi (i t : ℕ) (q : Qp k i t) (h : levi k (i + t) (q : GL (Fin (i + t)) k) ∈ HPG k i t) :
    pgProj k i t ⟨_, h⟩ = (levi k i (qBlocks k i t q).1, (qBlocks k i t q).2) := by
  apply Prod.ext
  · apply Subtype.ext
    apply Units.ext
    ext a b
    show (leviProj k (ePG i t) (hpgIncl k i t ⟨_, h⟩) false : GL (Fin (i + 1)) k).val a b =
      ((levi k i (qBlocks k i t q).1 : GL (Fin (i + 1)) k) : Matrix (Fin (i + 1)) (Fin (i + 1)) k) a b
    rw [leviProj_apply]
    show ((levi k (i + t) (q : GL (Fin (i + t)) k) : GL (Fin (i + t + 1)) k) : Matrix _ _ k)
      (ePG i t ⟨false, a⟩) (ePG i t ⟨false, b⟩) = _
    induction a using Fin.lastCases with
    | last =>
      rw [ePG_false_last]
      induction b using Fin.lastCases with
      | last => rw [ePG_false_last, levi_entry_last, levi_entry_last]
      | cast b => rw [ePG_false_eq, levi_entry_last_row, levi_entry_last_row]
    | cast a =>
      rw [ePG_false_eq]
      induction b using Fin.lastCases with
      | last => rw [ePG_false_last, levi_entry_last_col, levi_entry_last_col]
      | cast b =>
        rw [ePG_false_eq, levi_entry, levi_entry]
        show _ = (leviProj k (two (stdSum (rfl : i + t = i + t))) q false : GL (Fin i) k).val a b
        rw [leviProj_apply, two_false_eq, two_false_eq]
  · apply Units.ext
    ext a b
    show (leviProj k (ePG i t) (hpgIncl k i t ⟨_, h⟩) true : GL (Fin t) k).val a b =
      (leviProj k (two (stdSum (rfl : i + t = i + t))) q true : GL (Fin t) k).val a b
    rw [leviProj_apply, leviProj_apply]
    show ((levi k (i + t) (q : GL (Fin (i + t)) k) : GL (Fin (i + t + 1)) k) : Matrix _ _ k)
      (ePG i t ⟨true, a⟩) (ePG i t ⟨true, b⟩) = _
    rw [ePG_true_eq, ePG_true_eq, levi_entry, two_true_eq, two_true_eq]

end GlobalTheory.CompanionTheory.BZPsiPG.QLevi

namespace GlobalTheory.CompanionTheory.BZPsiPG

theorem levi_Qp_mem_pgProj (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (i t : ℕ) (q : Qp k i t) :
    ∃ h : levi k (i + t) (q : GL (Fin (i + t)) k) ∈ HPG k i t,
      pgProj k i t ⟨_, h⟩ = (levi k i (qBlocks k i t q).1, (qBlocks k i t q).2) :=
  ⟨QLevi.levi_mem_HPG i t q, QLevi.pgProj_levi i t q _⟩

end GlobalTheory.CompanionTheory.BZPsiPG

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviBlockMemParabolicStatement
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levi_block_mem_parabolic : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (q : Qp k i t), ∃ h : levi k (i + t) (q : GL (Fin (i + t)) k) ∈ HPG k i t, pgProj k i t ⟨_, h⟩ = (levi k i (qBlocks k i t q).1, (qBlocks k i t q).2) := by
  first | exact @GlobalTheory.CompanionTheory.BZPsiPG.levi_Qp_mem_pgProj | exact GlobalTheory.CompanionTheory.BZPsiPG.levi_Qp_mem_pgProj | (intros; apply GlobalTheory.CompanionTheory.BZPsiPG.levi_Qp_mem_pgProj <;> assumption)
end
end
