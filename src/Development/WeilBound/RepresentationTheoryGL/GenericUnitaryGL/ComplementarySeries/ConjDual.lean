module

public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.Complementary
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsHermRingRat
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.BernsteinZelevinskyFiniteness
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumThEmptyNeZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OrdSubConjEqNeg

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.ConjDual
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil

namespace PositivityTheory.RgGu.NR

namespace ConjDual

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem irrAdm' : GlobalTheory.Published.IrreducibleAdmissibleGL := by
  intro k _ _ _ _ n V _ _ π hs hi
  exact GlobalTheory.CompanionTheory.SmGLBridge.irreducibleAdmissible k (Fin n) V π hs hi

theorem conj_chi (n : ℕ) (s : ℝ) (g : GL (Fin n) k) :
    starRingEnd ℂ ((detChar (Fin n) (absPow k (s : ℂ)) g : ℂˣ) : ℂ) =
      ((detChar (Fin n) (absPow k (s : ℂ)) g : ℂˣ) : ℂ) := by
  simp only [detChar, absPow, MonoidHom.coe_comp, Function.comp_apply, MonoidHom.coe_toHomUnits,
    MonoidHom.coe_mk, OneHom.coe_mk]
  rw [← Complex.ofReal_cpow (GlobalTheory.SmGL.nabs_pos' k _).le, Complex.conj_ofReal]

end ConjDual

open ConjDual in
theorem conjDual (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    ConjDual k := by
  intro n V _ _ ρ hs hi hu s
  obtain ⟨B, -, hBpos, hBinv⟩ := hu
  have hinv : ∀ (g : GL (Fin n) k) (w : V), ρ g (ρ g⁻¹ w) = w := by
    intro g w
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  let L : V → Module.Dual ℂ V := fun v =>
    { toFun := fun w => B w v
      map_add' := by intro a b; simp
      map_smul' := by intro c a; simp }
  have hL : ∀ v w, L v w = B w v := fun v w => rfl
  have hmem : ∀ v, L v ∈ smoothPart ρ.dual := by
    intro v
    apply GlobalTheory.SmGL.mem_smoothPart_of_nhds
    apply Filter.mem_of_superset ((hs v).mem_nhds (by simp))
    intro g hg
    simp only [Set.mem_setOf_eq] at hg ⊢
    have hv' : ρ g⁻¹ v = v := by
      conv_lhs => rw [← hg]
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    ext w
    rw [Representation.dual_apply, Module.Dual.transpose_apply, LinearMap.comp_apply, hL, hL]
    rw [← hBinv g⁻¹ w v, hv']
  let φ : V →ₗ⋆[ℂ] smoothPart ρ.dual :=
    { toFun := fun v => ⟨L v, hmem v⟩
      map_add' := by
        intro a b
        ext w
        simp [hL]
      map_smul' := by
        intro c a
        ext w
        simp [hL] }
  have hφ : ∀ v w, (φ v : Module.Dual ℂ V) w = B w v := fun v w => rfl
  have hint : ∀ (g : GL (Fin n) k) (v : V), φ (ρ g v) = contra ρ g (φ v) := by
    intro g v
    ext w
    rw [contra_apply, hφ, hφ, ← hBinv g (ρ g⁻¹ w) v, hinv]
  refine ⟨φ, ⟨?_, ?_⟩, fun g v => ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro v hv
    by_contra hne
    have h0 := hBpos v hne
    have : B v v = 0 := by
      rw [← hφ, hv]
      rfl
    rw [this] at h0
    simp at h0
  · have hadm := irrAdm' k n V ρ hs hi
    have hbasis : ∀ U ∈ nhds (1 : GL (Fin n) k), ∃ K : Subgroup (GL (Fin n) k),
        IsOpen (K : Set (GL (Fin n) k)) ∧ IsCompact (K : Set (GL (Fin n) k)) ∧ (K : Set (GL (Fin n) k)) ⊆ U := by
      intro U hU
      obtain ⟨J, hJo, hJU, hJK, -⟩ := GlobalTheory.SmGL.exists_open_normalised_subgroup_subset k (Fin n) U hU
      exact ⟨J, hJo, GlobalTheory.SplitFlip.isCompact_KO.of_isClosed_subset (J.isClosed_of_isOpen hJo)
        (fun x hx => hJK hx), hJU⟩
    have hci := GlobalTheory.ContraRefl.contra_isIrreducible hbasis hadm hi
    let S : Subrepresentation (contra ρ) :=
      ⟨LinearMap.range φ, by
        rintro g x ⟨v, rfl⟩
        exact ⟨ρ g v, hint g v⟩⟩
    haveI := GlobalTheory.SmGL.nontrivial_of_irreducible hi
    rcases eq_bot_or_eq_top S with h | h
    · exfalso
      obtain ⟨v, hv⟩ := exists_ne (0 : V)
      have hm : φ v ∈ S.toSubmodule := LinearMap.mem_range_self φ v
      rw [h] at hm
      have hz : φ v = 0 := (Submodule.mem_bot ℂ).1 hm
      have h0 := hBpos v hv
      have : B v v = 0 := by
        rw [← hφ, hz]
        rfl
      rw [this] at h0
      simp at h0
    · have hr : LinearMap.range φ = ⊤ := congrArg Subrepresentation.toSubmodule h
      exact LinearMap.range_eq_top.1 hr
  · rw [twist_apply, twist_apply, map_smulₛₗ, conj_chi, hint]

end PositivityTheory.RgGu.NR

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.ConjProd
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil
open scoped TensorProduct

namespace PositivityTheory.RgGu.NR.ConjProd

def Cj (Y : Type) : Type := Y

instance (Y : Type) [AddCommGroup Y] : AddCommGroup (Cj Y) := inferInstanceAs (AddCommGroup Y)

instance (Y : Type) [AddCommGroup Y] [Module ℂ Y] : Module ℂ (Cj Y) := Module.compHom Y (starRingEnd ℂ)

def semiInv {X Y : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (φ : X →ₛₗ[starRingEnd ℂ] Y) (hφ : Function.Bijective φ) : Y →ₛₗ[starRingEnd ℂ] X where
  toFun := Function.surjInv hφ.2
  map_add' a b := hφ.1 (by rw [map_add (f := _), Function.surjInv_eq hφ.2, Function.surjInv_eq hφ.2,
    Function.surjInv_eq hφ.2])
  map_smul' c y := hφ.1 (by
    rw [Function.surjInv_eq hφ.2, map_smulₛₗ, Function.surjInv_eq hφ.2]
    simp)

theorem semiInv_apply {X Y : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (φ : X →ₛₗ[starRingEnd ℂ] Y) (hφ : Function.Bijective φ) (y : Y) : φ (semiInv φ hφ y) = y :=
  Function.surjInv_eq hφ.2 y

theorem semiInv_apply' {X Y : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (φ : X →ₛₗ[starRingEnd ℂ] Y) (hφ : Function.Bijective φ) (x : X) : semiInv φ hφ (φ x) = x :=
  hφ.1 (semiInv_apply φ hφ (φ x))

section Tensor

variable {α : Type} [Fintype α] {X Y : α → Type} [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]
  [∀ a, AddCommGroup (Y a)] [∀ a, Module ℂ (Y a)]

omit [Fintype α] in
theorem update_comp (φ : ∀ a, X a →ₛₗ[starRingEnd ℂ] Y a) [DecidableEq α] (x : ∀ a, X a) (i : α) (w : X i) :
    (fun a => φ a (Function.update x i w a)) = Function.update (fun a => φ a (x a)) i (φ i w) := by
  funext a
  exact Function.apply_update (fun a => φ a) x i w a

def mlin (φ : ∀ a, X a →ₛₗ[starRingEnd ℂ] Y a) : MultilinearMap (RingHom.id ℂ) X (Cj (⨂[ℂ] a, Y a)) where
  toFun x := (PiTensorProduct.tprod ℂ (fun a => φ a (x a)) : ⨂[ℂ] a, Y a)
  map_update_add' x i u v := by
    show (PiTensorProduct.tprod ℂ (fun a => φ a (Function.update x i (u + v) a)) : ⨂[ℂ] a, Y a) =
      PiTensorProduct.tprod ℂ (fun a => φ a (Function.update x i u a)) +
        PiTensorProduct.tprod ℂ (fun a => φ a (Function.update x i v a))
    rw [update_comp, update_comp, update_comp, map_add (f := _), MultilinearMap.map_update_add]
  map_update_smul' x i c u := by
    show (PiTensorProduct.tprod ℂ (fun a => φ a (Function.update x i (c • u) a)) : ⨂[ℂ] a, Y a) =
      starRingEnd ℂ c • PiTensorProduct.tprod ℂ (fun a => φ a (Function.update x i u a))
    rw [update_comp, update_comp, map_smulₛₗ, MultilinearMap.map_update_smul, RingHom.id_apply]

def tmap (φ : ∀ a, X a →ₛₗ[starRingEnd ℂ] Y a) : (⨂[ℂ] a, X a) →ₛₗ[starRingEnd ℂ] (⨂[ℂ] a, Y a) where
  toFun t := (PiTensorProduct.lift (mlin φ) t : Cj (⨂[ℂ] a, Y a))
  map_add' s t := by
    show (PiTensorProduct.lift (mlin φ) (s + t) : Cj (⨂[ℂ] a, Y a)) = _
    rw [map_add (f := _)]
    rfl
  map_smul' c t := by
    show (PiTensorProduct.lift (mlin φ) (c • t) : Cj (⨂[ℂ] a, Y a)) = _
    rw [map_smul]
    rfl

theorem tmap_tprod (φ : ∀ a, X a →ₛₗ[starRingEnd ℂ] Y a) (x : ∀ a, X a) :
    tmap φ (PiTensorProduct.tprod ℂ x) = PiTensorProduct.tprod ℂ (fun a => φ a (x a)) := by
  show (PiTensorProduct.lift (mlin φ) (PiTensorProduct.tprod ℂ x) : Cj (⨂[ℂ] a, Y a)) = _
  rw [PiTensorProduct.lift.tprod]
  rfl

theorem tmap_comp (φ : ∀ a, X a →ₛₗ[starRingEnd ℂ] Y a) (ψ : ∀ a, Y a →ₛₗ[starRingEnd ℂ] X a)
    (h : ∀ a (x : X a), ψ a (φ a x) = x) (t : ⨂[ℂ] a, X a) : tmap ψ (tmap φ t) = t := by
  induction t using PiTensorProduct.induction_on with
  | smul_tprod r x =>
    rw [map_smulₛₗ, map_smulₛₗ, tmap_tprod, tmap_tprod]
    simp [h]
  | add s t hs ht => rw [map_add (f := _), map_add (f := _), hs, ht]

end Tensor

theorem conjEquiv_piTensor {α : Type} [Fintype α] {Γ X Y : α → Type} [∀ a, Group (Γ a)]
    [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] [∀ a, AddCommGroup (Y a)] [∀ a, Module ℂ (Y a)]
    (π : ∀ a, Representation ℂ (Γ a) (X a)) (σ : ∀ a, Representation ℂ (Γ a) (Y a))
    (h : ∀ a, ConjEquiv (π a) (σ a)) : ConjEquiv (piTensor π) (piTensor σ) := by
  choose φ hφ heq using h
  refine ⟨tmap φ, ⟨fun s t hst => ?_, fun t => ⟨tmap (fun a => semiInv (φ a) (hφ a)) t, ?_⟩⟩, fun g t => ?_⟩
  · have := congrArg (tmap (fun a => semiInv (φ a) (hφ a))) hst
    rwa [tmap_comp _ _ (fun a x => semiInv_apply' (φ a) (hφ a) x),
      tmap_comp _ _ (fun a x => semiInv_apply' (φ a) (hφ a) x)] at this
  · exact tmap_comp (fun a => semiInv (φ a) (hφ a)) φ (fun a y => semiInv_apply (φ a) (hφ a) y) t
  · induction t using PiTensorProduct.induction_on with
    | smul_tprod r x =>
      rw [map_smul, map_smulₛₗ, map_smulₛₗ, map_smul, piTensor_tprod, tmap_tprod, tmap_tprod, piTensor_tprod]
      congr 2
      funext a
      exact heq a (g a) (x a)
    | add s t hs ht => rw [map_add (f := _), map_add (f := _), hs, ht, map_add (f := _), map_add (f := _)]

section Ind

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {α : Type} [Fintype α] [LinearOrder α] {m : α → Type} [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]
  {n : Type} [Fintype n] [DecidableEq n]

theorem star_deltaHalf (g : Levi k m) : starRingEnd ℂ (deltaHalf k m g : ℂ) = deltaHalf k m g := by
  rw [deltaHalf_apply, Units.coe_prod, map_prod]
  refine Finset.prod_congr rfl fun a _ => ?_
  have e : ((modExp m a : ℂ) / 2) = (((modExp m a : ℝ) / 2 : ℝ) : ℂ) := by push_cast; ring
  show starRingEnd ℂ (((nabs k (Matrix.GeneralLinearGroup.det (g a)) : ℝ) : ℂ) ^ ((modExp m a : ℂ) / 2)) =
    ((nabs k (Matrix.GeneralLinearGroup.det (g a)) : ℝ) : ℂ) ^ ((modExp m a : ℂ) / 2)
  rw [e, ← Complex.ofReal_cpow (nabs_pos' k _).le, Complex.conj_ofReal]

variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

def indMap (e : (Σ a, m a) ≃ n) {ρ : Representation ℂ (Levi k m) V} {τ : Representation ℂ (Levi k m) W}
    (φ : V →ₛₗ[starRingEnd ℂ] W) (hφ : ∀ g v, φ (ρ g v) = τ g (φ v)) :
    IndSp e ρ →ₛₗ[starRingEnd ℂ] IndSp e τ where
  toFun f := ⟨⟨fun g => φ (f.1.1 g), fun p g => by
      show φ (f.1.1 (p * g)) = (deltaHalf k m (leviProj k e p) : ℂ) • τ (leviProj k e p) (φ (f.1.1 g))
      rw [parInd_law e ρ f p g, map_smulₛₗ, star_deltaHalf, hφ]⟩,
    mem_smoothPart_of_nhds (Filter.mem_of_superset (IsOpen.mem_nhds f.2 (by simp)) fun g hg => by
      have hg' : ind (parab k e) ((twist ρ (deltaHalf k m)).comp (leviProj k e)) g f.1 = f.1 := hg
      apply Subtype.ext
      funext x
      exact congrArg φ (congrFun (congrArg Subtype.val hg') x))⟩
  map_add' f f' := by
    apply Subtype.ext; apply Subtype.ext; funext g
    exact map_add φ (f.1.1 g) (f'.1.1 g)
  map_smul' c f := by
    apply Subtype.ext; apply Subtype.ext; funext g
    exact map_smulₛₗ φ c (f.1.1 g)

theorem indMap_apply (e : (Σ a, m a) ≃ n) {ρ : Representation ℂ (Levi k m) V} {τ : Representation ℂ (Levi k m) W}
    (φ : V →ₛₗ[starRingEnd ℂ] W) (hφ : ∀ g v, φ (ρ g v) = τ g (φ v)) (f : IndSp e ρ) (g : GL n k) :
    (indMap e φ hφ f).1.1 g = φ (f.1.1 g) := rfl

theorem conjEquiv_parInd (e : (Σ a, m a) ≃ n) (ρ : Representation ℂ (Levi k m) V)
    (τ : Representation ℂ (Levi k m) W) (h : ConjEquiv ρ τ) : ConjEquiv (parInd e ρ) (parInd e τ) := by
  obtain ⟨φ, hφ, heq⟩ := h
  have hinv : ∀ g w, semiInv φ hφ (τ g w) = ρ g (semiInv φ hφ w) := fun g w => by
    apply hφ.1
    rw [semiInv_apply, heq, semiInv_apply]
  refine ⟨indMap e φ heq, ⟨fun f f' hff => ?_, fun f => ⟨indMap e (semiInv φ hφ) hinv f, ?_⟩⟩, fun g f => ?_⟩
  · apply Subtype.ext; apply Subtype.ext; funext x
    apply hφ.1
    have := congrArg (fun F : IndSp e τ => F.1.1 x) hff
    simpa only [indMap_apply] using this
  · apply Subtype.ext; apply Subtype.ext; funext x
    show φ (semiInv φ hφ (f.1.1 x)) = f.1.1 x
    exact semiInv_apply φ hφ _
  · apply Subtype.ext; apply Subtype.ext; funext x
    rfl

end Ind

end PositivityTheory.RgGu.NR.ConjProd

namespace PositivityTheory.RgGu.NR

open ConjProd in
theorem conjProd (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    ConjProd k := by
  intro h N d hd X Y _ _ _ _ π σ hc
  exact conjEquiv_parInd _ _ _ (conjEquiv_piTensor π σ hc)

end PositivityTheory.RgGu.NR

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.PiTensorTwist
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil
  GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.RgGu.NR

namespace Model

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem prodIrr_congr {h N : ℕ} {y z : Fin h → IrrGL (k := k)} (e : y = z) (hy : ∑ a, (y a).1 = N) (hz : ∑ a, (z a).1 = N) :
    Nonempty ((prodIrr y hy).Equiv (prodIrr z hz)) := by
  subst e
  exact ⟨Representation.Equiv.refl _⟩

theorem piTensor_twist (x : IrrGL (k := k)) (s : ℝ) :
    piTensor (fun a : Fin 2 => twist x.rep (detChar (Fin x.1) (absPow k (![-(s : ℂ), (s : ℂ)] a)))) =
      twist (piTensor fun _ : Fin 2 => x.rep) (chi k x.1 s) := by
  ext g : 1
  refine PiTensorProduct.ext (MultilinearMap.ext fun v => ?_)
  have ht : ∀ {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) k) V)
      (χ : GL (Fin n) k →* ℂˣ) (g : GL (Fin n) k), twist ρ χ g = ((χ g : ℂ) • ρ g) := fun _ _ _ => rfl
  have ht2 : ∀ (g : Levi k fun _ : Fin 2 => Fin x.1), twist (piTensor fun _ : Fin 2 => x.rep) (chi k x.1 s) g =
      ((chi k x.1 s g : ℂ) • (piTensor fun _ : Fin 2 => x.rep) g) := fun _ => rfl
  simp only [LinearMap.compMultilinearMap_apply, piTensor_tprod, ht, ht2, LinearMap.smul_apply]
  rw [MultilinearMap.map_smul_univ]
  congr 1
  simp [chi, Fin.prod_univ_two, Units.val_mul]

end Model

open Model in
theorem prodModel (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    ProdModel k := by
  intro x s hd
  let π : ∀ a : Fin 2, Representation ℂ (GL (Fin x.1) k) x.2.rep.V :=
    fun a => twist x.rep (detChar (Fin x.1) (absPow k (![-(s : ℂ), (s : ℂ)] a)))
  have hs : ∀ a, IsSmooth (π a) := fun a => isSmooth_twist x.2.rep.smooth (isSmoothChar_absPow _).detChar
  have hi : ∀ a, (π a).IsIrreducible := fun a => isIrreducible_twist x.2.rep.irr _
  have e1 := prodIrrEquiv (d := fun _ : Fin 2 => x.1) (sum_two x.1) π hs hi
  have hy : (fun a => IrrGL.of (π a) (hs a) (hi a)) = ![x.nu (-(s : ℂ)), x.nu (s : ℂ)] := by
    funext a
    have key : ∀ c : ℂ, IrrGL.of (twist x.rep (detChar (Fin x.1) (absPow k c))) (isSmooth_twist x.2.rep.smooth
        (isSmoothChar_absPow c).detChar) (isIrreducible_twist x.2.rep.irr _) = x.nu c := fun c =>
      (IrrGL.tw_of x.rep x.2.rep.smooth x.2.rep.irr (absPow k c) (isSmoothChar_absPow c)).symm.trans
        (congrArg (fun y => IrrGL.tw y (absPow k c) (isSmoothChar_absPow c)) (IrrGL.of_rep x))
    fin_cases a
    · exact key _
    · exact key _
  obtain ⟨e2⟩ := prodIrr_congr hy (sum_two x.1) hd
  have e3 : (multiProd (stdBlocks (fun _ : Fin 2 => x.1) (sum_two x.1)) π).Equiv
      (parInd (blk2 x.1) (twist (piTensor fun _ : Fin 2 => x.rep) (chi k x.1 s))) :=
    parIndEquiv (blk2 x.1) ((piTensor_twist x s) ▸ Representation.Equiv.refl _)
  exact ⟨(e2.symm.trans e1.symm).trans e3⟩

theorem cuspUnit (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    CuspUnit k := by
  intro y hy
  obtain ⟨ω, hωs, hω⟩ := exists_smooth_hasCentralChar y.2.rep.smooth y.2.rep.irr
  obtain ⟨s, hs⟩ := GlobalTheory.SmoothCharNorm.norm_eq_nabs_rpow k ω hωs
  have hN : (y.1 : ℝ) ≠ 0 := by exact_mod_cast hy.1.ne'
  refine ⟨y.nu ((-(s / y.1) : ℝ) : ℂ), s / y.1, hy.nu _, ?_, ?_⟩
  · have hρc : (y.nu ((-(s / y.1) : ℝ) : ℂ)).IsCusp := hy.nu _
    have hcc := UnitaryOrder.hasCentralChar_nu y hω ((-(s / y.1) : ℝ) : ℂ)
    have hi := (y.nu ((-(s / y.1) : ℝ) : ℂ)).2.rep.irr
    have hsm := (y.nu ((-(s / y.1) : ℝ) : ℂ)).2.rep.smooth
    haveI := GlobalTheory.SmGL.Model.nontrivial_of_isIrreducible hi
    obtain ⟨v₀, hv₀⟩ := exists_ne (0 : (y.nu ((-(s / y.1) : ℝ) : ℂ)).2.rep.V)
    obtain ⟨l, hl⟩ := GlobalTheory.ContraRefl.exists_smooth_form_ne hsm (GlobalTheory.SqIntUnit.compactOpen_basis k _) hv₀
    refine GlobalTheory.isUnitarisable_of_isSupercuspidal _ _ _ (l : Module.Dual ℂ _) l.2
      (fun e => hl (by rw [e]; rfl)) hi (GlobalTheory.CuspCoef.isSupercuspidal_of_isCuspidal k _ _ _ hρc.2) ?_
    intro g hg
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hg
    obtain ⟨a, rfl⟩ := hg
    refine ⟨_, ?_, hcc a⟩
    have h1 := UnitaryOrder.log_norm_mul_absPow ω (-(s / y.1)) y.1 a
    have hpos := nabs_pos' k a
    rw [hs a, Real.log_rpow hpos] at h1
    have h2 : Real.log ‖(((ω * absPow k ((-(s / y.1) : ℝ) : ℂ) ^ y.1) a : ℂˣ) : ℂ)‖ = 0 := by
      rw [h1]; field_simp; ring
    exact Real.eq_one_of_pos_of_log_eq_zero (norm_pos_iff.2 (Units.ne_zero _)) h2
  · rw [IrrGL.nu_nu, show ((-(s / y.1) : ℝ) : ℂ) + ((s / y.1 : ℝ) : ℂ) = 0 by push_cast; ring, IrrGL.nu_zero]

end PositivityTheory.RgGu.NR

end
end
