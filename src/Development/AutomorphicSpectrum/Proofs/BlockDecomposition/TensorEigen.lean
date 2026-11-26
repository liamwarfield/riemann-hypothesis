module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.CosetCount
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenFns
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ActEqSumOfKernel

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensorEigen
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensorEigen
open TensorProduct

namespace GlobalTheory.CompanionTheory.TensContr

variable {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

noncomputable def contr (v : V ⊗[ℂ] W) : Module.Dual ℂ W →ₗ[ℂ] V where
  toFun l := TensorProduct.rid ℂ V (LinearMap.lTensor V l v)
  map_add' l m := by
    induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [add_smul]
    | add s t hs ht =>
      simp only [map_add (f := _)] at hs ht ⊢
      rw [hs, ht]; abel
  map_smul' c l := by
    induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [mul_smul]
    | add s t hs ht =>
      simp only [map_add (f := _), RingHom.id_apply, smul_add] at hs ht ⊢
      rw [hs, ht]

@[simp] theorem contr_tmul (a : V) (b : W) (l : Module.Dual ℂ W) :
    contr (a ⊗ₜ[ℂ] b) l = l b • a := by
  show TensorProduct.rid ℂ V (LinearMap.lTensor V l (a ⊗ₜ[ℂ] b)) = l b • a
  rw [LinearMap.lTensor_tmul, TensorProduct.rid_tmul]

theorem contr_apply (v : V ⊗[ℂ] W) (l : Module.Dual ℂ W) :
    contr v l = TensorProduct.rid ℂ V (LinearMap.lTensor V l v) := rfl

theorem contr_add (s t : V ⊗[ℂ] W) (l : Module.Dual ℂ W) :
    contr (s + t) l = contr s l + contr t l := by
  simp only [GlobalTheory.CompanionTheory.TensContr.contr_apply, map_add (f := _)]

theorem contr_smul (c : ℂ) (t : V ⊗[ℂ] W) (l : Module.Dual ℂ W) :
    contr (c • t) l = c • contr t l := by
  simp only [GlobalTheory.CompanionTheory.TensContr.contr_apply, map_smul]

theorem contr_map (f : V →ₗ[ℂ] V) (g : W →ₗ[ℂ] W) (t : V ⊗[ℂ] W) (l : Module.Dual ℂ W) :
    contr (TensorProduct.map f g t) l = f (contr t (l ∘ₗ g)) := by
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero, GlobalTheory.CompanionTheory.TensContr.contr_apply]
  | tmul a b =>
    rw [TensorProduct.map_tmul, GlobalTheory.CompanionTheory.TensContr.contr_tmul, GlobalTheory.CompanionTheory.TensContr.contr_tmul,
      LinearMap.comp_apply, map_smul]
  | add s t hs ht =>
    rw [map_add (f := _), GlobalTheory.CompanionTheory.TensContr.contr_add, GlobalTheory.CompanionTheory.TensContr.contr_add, hs, ht, map_add (f := _)]

theorem exists_finset_contr (v : V ⊗[ℂ] W) :
    ∃ s : Finset V, ∀ l, contr v l ∈ Submodule.span ℂ (s : Set V) := by
  classical
  induction v using TensorProduct.induction_on with
  | zero =>
    refine ⟨∅, fun l => ?_⟩
    simp only [GlobalTheory.CompanionTheory.TensContr.contr_apply, map_zero]
    exact Submodule.zero_mem _
  | tmul a b =>
    refine ⟨{a}, fun l => ?_⟩
    rw [GlobalTheory.CompanionTheory.TensContr.contr_tmul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  | add s t hs ht =>
    obtain ⟨S, hS⟩ := hs
    obtain ⟨T, hT⟩ := ht
    refine ⟨S ∪ T, fun l => ?_⟩
    rw [GlobalTheory.CompanionTheory.TensContr.contr_add]
    refine Submodule.add_mem _ (Submodule.span_mono ?_ (hS l)) (Submodule.span_mono ?_ (hT l))
    · exact_mod_cast Finset.subset_union_left
    · exact_mod_cast Finset.subset_union_right

theorem finiteDimensional_range_contr (v : V ⊗[ℂ] W) :
    FiniteDimensional ℂ (LinearMap.range (contr v)) := by
  obtain ⟨s, hs⟩ := GlobalTheory.CompanionTheory.TensContr.exists_finset_contr v
  haveI := FiniteDimensional.span_finset ℂ s
  have hle : LinearMap.range (GlobalTheory.CompanionTheory.TensContr.contr v) ≤ Submodule.span ℂ (s : Set V) := by
    rintro _ ⟨l, rfl⟩
    exact hs l
  exact Submodule.finiteDimensional_of_le hle

theorem eq_zero_of_contr (v : V ⊗[ℂ] W) (h : ∀ l, contr v l = 0) : v = 0 := by
  classical
  let b := Module.Basis.ofVectorSpace ℂ W
  let e := TensorProduct.equivFinsuppOfBasisRight (M := V) b
  have key : ∀ (t : V ⊗[ℂ] W) i, e t i = GlobalTheory.CompanionTheory.TensContr.contr t (b.coord i) := by
    intro t i
    induction t using TensorProduct.induction_on with
    | zero =>
      simp only [map_zero, Finsupp.coe_zero, Pi.zero_apply, GlobalTheory.CompanionTheory.TensContr.contr_apply]
    | tmul a w =>
      rw [TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply, GlobalTheory.CompanionTheory.TensContr.contr_tmul,
        Module.Basis.coord_apply]
    | add s t hs ht =>
      rw [map_add (f := _), Finsupp.add_apply, hs, ht, GlobalTheory.CompanionTheory.TensContr.contr_add]
  have he : e v = 0 := by
    ext i
    rw [key, h, Finsupp.coe_zero, Pi.zero_apply]
  exact (LinearEquiv.map_eq_zero_iff e).mp he

end GlobalTheory.CompanionTheory.TensContr

namespace GlobalTheory.CompanionTheory.TensContr

variable {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
variable {X Y : Type*}

theorem exists_contr_eigen [Nonempty Y]
    (A : X → V →ₗ[ℂ] V) (B : Y → W →ₗ[ℂ] W) (lam : X → ℂ) (mu : Y → ℂ)
    (hlam : ∀ x, lam x ≠ 0) (hmu : ∀ y, mu y ≠ 0)
    (v : V ⊗[ℂ] W) (hv : v ≠ 0)
    (heig : ∀ x y, TensorProduct.map (A x) (B y) v = (lam x * mu y) • v) :
    ∃ (l : Module.Dual ℂ W) (c : ℂ), c ≠ 0 ∧
      TensorProduct.rid ℂ V (LinearMap.lTensor V l v) ≠ 0 ∧
      ∀ x, A x (TensorProduct.rid ℂ V (LinearMap.lTensor V l v)) =
        (c * lam x) • TensorProduct.rid ℂ V (LinearMap.lTensor V l v) := by
  simp only [← GlobalTheory.CompanionTheory.TensContr.contr_apply]
  set φ := GlobalTheory.CompanionTheory.TensContr.contr v with hφ
  have hne : ∃ l, φ l ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hv (GlobalTheory.CompanionTheory.TensContr.eq_zero_of_contr v hcon)
  obtain ⟨l₀, hl₀⟩ := hne
  by_cases hX : IsEmpty X
  · exact ⟨l₀, 1, one_ne_zero, hl₀, fun x => (hX.false x).elim⟩
  obtain ⟨x₀⟩ := not_isEmpty_iff.mp hX
  obtain ⟨y₀⟩ := ‹Nonempty Y›
  have rel : ∀ x l, A x (φ (l ∘ₗ B y₀)) = (lam x * mu y₀) • φ l := by
    intro x l
    rw [hφ, ← GlobalTheory.CompanionTheory.TensContr.contr_map, heig, GlobalTheory.CompanionTheory.TensContr.contr_smul]
  let U := LinearMap.range φ
  haveI : FiniteDimensional ℂ U := GlobalTheory.CompanionTheory.TensContr.finiteDimensional_range_contr v
  let U' := LinearMap.range (φ ∘ₗ (B y₀).dualMap)
  have hU'U : U' ≤ U := LinearMap.range_comp_le_range _ _
  have hmapU' : U ≤ Submodule.map (A x₀) U' := by
    rintro _ ⟨l, rfl⟩
    have hk : lam x₀ * mu y₀ ≠ 0 := mul_ne_zero (hlam x₀) (hmu y₀)
    refine ⟨φ (((lam x₀ * mu y₀)⁻¹ • l) ∘ₗ B y₀), ⟨(lam x₀ * mu y₀)⁻¹ • l, ?_⟩, ?_⟩
    · rw [LinearMap.comp_apply, LinearMap.dualMap_apply']
    · rw [rel, map_smul, smul_smul, mul_inv_cancel₀ hk, one_smul]
  haveI : FiniteDimensional ℂ U' := Submodule.finiteDimensional_of_le hU'U
  have hUU' : U' = U := by
    refine Submodule.eq_of_le_of_finrank_le hU'U ?_
    calc Module.finrank ℂ U ≤ Module.finrank ℂ (Submodule.map (A x₀) U') :=
          Submodule.finrank_mono hmapU'
      _ ≤ Module.finrank ℂ U' := Submodule.finrank_map_le _ _
  have hrepr : ∀ u ∈ U, ∃ l, u = φ (l ∘ₗ B y₀) := by
    intro u hu
    rw [← hUU'] at hu
    obtain ⟨l, rfl⟩ := hu
    exact ⟨l, by rw [LinearMap.comp_apply, LinearMap.dualMap_apply']⟩
  have hmaps : ∀ x, ∀ u ∈ U, A x u ∈ U := by
    intro x u hu
    obtain ⟨l, rfl⟩ := hrepr u hu
    rw [rel]
    exact Submodule.smul_mem _ _ ⟨l, rfl⟩
  have hprop : ∀ x, ∀ u ∈ U, A x u = (lam x * (lam x₀)⁻¹) • A x₀ u := by
    intro x u hu
    obtain ⟨l, rfl⟩ := hrepr u hu
    rw [rel, rel, smul_smul]
    congr 1
    field_simp [hlam x₀, hmu y₀]
  let T : Module.End ℂ U := (A x₀).restrict (hmaps x₀)
  have hsurj : Function.Surjective T := by
    rintro ⟨u, hu⟩
    obtain ⟨w, hw, hwu⟩ := hmapU' hu
    exact ⟨⟨w, hU'U hw⟩, Subtype.ext (by simpa [T, LinearMap.restrict_apply] using hwu)⟩
  have hinj : Function.Injective T := LinearMap.injective_iff_surjective.mpr hsurj
  haveI : Nontrivial U := nontrivial_of_ne (⟨φ l₀, ⟨l₀, rfl⟩⟩ : U) 0
    (fun h => hl₀ (congrArg Subtype.val h))
  obtain ⟨t, ht⟩ := Module.End.exists_eigenvalue T
  obtain ⟨u, hu⟩ := ht.exists_hasEigenvector
  have hTu := hu.apply_eq_smul
  have hu0 : u ≠ 0 := hu.2
  have ht0 : t ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hTu
    exact hu0 (hinj (by rw [hTu, map_zero]))
  have hAu : A x₀ u = t • (u : V) := by
    have := congrArg Subtype.val hTu
    simpa [T, LinearMap.restrict_apply] using this
  obtain ⟨l, hl⟩ := u.2
  refine ⟨l, t * (lam x₀)⁻¹, mul_ne_zero ht0 (inv_ne_zero (hlam x₀)), ?_, fun x => ?_⟩
  · rw [hl]
    exact fun h => hu0 (Subtype.ext h)
  · rw [hl, hprop x _ u.2, hAu, smul_smul]
    congr 1
    ring

end GlobalTheory.CompanionTheory.TensContr

namespace GlobalTheory.CompanionTheory.TensContr

theorem tensEig : PositivityTheory.Rg.BcB.F.Tail.PExp.TensEig := by
  intro V W X Y _ _ _ _ A B lam mu v hv hY hlam hmu heig
  exact GlobalTheory.CompanionTheory.TensContr.exists_contr_eigen A B lam mu hlam hmu v hv heig

end GlobalTheory.CompanionTheory.TensContr
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensorEigenStatement
namespace PositivityTheory.Rg.BcB.F.Tail.PExp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensor_eigen : PositivityTheory.Rg.BcB.F.Tail.PExp.TensEig := by
  first | exact @GlobalTheory.CompanionTheory.TensContr.tensEig | exact GlobalTheory.CompanionTheory.TensContr.tensEig | (intros; apply GlobalTheory.CompanionTheory.TensContr.tensEig <;> assumption)
end PositivityTheory.Rg.BcB.F.Tail.PExp
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedJacquetTensorProductEquiv
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedJacquetTensorProductEquiv
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib GlobalTheory.CompanionTheory.Rodier
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.Rodier.PiCoinv

section Modules

variable {α : Type} {X : α → Type} [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]

def pureSpan (K : ∀ a, Submodule ℂ (X a)) : Submodule ℂ (⨂[ℂ] a, X a) :=
  Submodule.span ℂ {t | ∃ (x : ∀ a, X a) (a : α), x a ∈ K a ∧ t = PiTensorProduct.tprod ℂ x}

theorem tprod_sub_mem [Fintype α] (K : ∀ a, Submodule ℂ (X a)) {x y : ∀ a, X a}
    (h : ∀ a, x a - y a ∈ K a) :
    PiTensorProduct.tprod ℂ x - PiTensorProduct.tprod ℂ y ∈ pureSpan K := by
  classical
  have key : ∀ s : Finset α, PiTensorProduct.tprod ℂ x -
      PiTensorProduct.tprod ℂ (fun a => if a ∈ s then y a else x a) ∈ pureSpan K := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · simp
    · intro b s hb ih
      have hx : Function.update (fun a => if a ∈ s then y a else x a) b (x b) =
          (fun a => if a ∈ s then y a else x a) := by
        rw [Function.update_eq_self_iff]
        simp [hb]
      have hupd : (fun a => if a ∈ insert b s then y a else x a) =
          Function.update (fun a => if a ∈ s then y a else x a) b (y b) := by
        funext a
        by_cases hab : a = b
        · subst hab
          simp
        · simp [Function.update_of_ne hab, Finset.mem_insert, hab]
      have e : PiTensorProduct.tprod ℂ
            (Function.update (fun a => if a ∈ s then y a else x a) b (x b - y b)) =
          PiTensorProduct.tprod ℂ (fun a => if a ∈ s then y a else x a) -
            PiTensorProduct.tprod ℂ (fun a => if a ∈ insert b s then y a else x a) := by
        rw [MultilinearMap.map_update_sub, hx, hupd]
      have hmem : PiTensorProduct.tprod ℂ (fun a => if a ∈ s then y a else x a) -
          PiTensorProduct.tprod ℂ (fun a => if a ∈ insert b s then y a else x a) ∈ pureSpan K := by
        rw [← e]
        exact Submodule.subset_span ⟨_, b, by simpa using h b, rfl⟩
      have := Submodule.add_mem _ ih hmem
      rwa [sub_add_sub_cancel] at this
  simpa using key Finset.univ

def rep (K : ∀ a, Submodule ℂ (X a)) (q : ∀ a, X a ⧸ K a) (a : α) : X a :=
  Function.surjInv (Submodule.mkQ_surjective (K a)) (q a)

theorem mkQ_rep (K : ∀ a, Submodule ℂ (X a)) (q : ∀ a, X a ⧸ K a) (a : α) :
    (K a).mkQ (rep K q a) = q a := by
  unfold rep
  exact Function.surjInv_eq (Submodule.mkQ_surjective (K a)) (q a)

def descendFun (K : ∀ a, Submodule ℂ (X a)) (q : ∀ a, X a ⧸ K a) : (⨂[ℂ] a, X a) ⧸ pureSpan K :=
  (pureSpan K).mkQ (PiTensorProduct.tprod ℂ (rep K q))

theorem descendFun_eq [Fintype α] (K : ∀ a, Submodule ℂ (X a)) (q : ∀ a, X a ⧸ K a) (y : ∀ a, X a)
    (hy : ∀ a, (K a).mkQ (y a) = q a) :
    descendFun K q = (pureSpan K).mkQ (PiTensorProduct.tprod ℂ y) := by
  unfold descendFun
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
  exact tprod_sub_mem K fun a => (Submodule.Quotient.eq _).1 ((mkQ_rep K q a).trans (hy a).symm)

theorem mkQ_update [DecidableEq α] (K : ∀ a, Submodule ℂ (X a)) {q : ∀ a, X a ⧸ K a} {y : ∀ a, X a}
    (hy : ∀ a, (K a).mkQ (y a) = q a) (a : α) {w : X a} {r : X a ⧸ K a} (hw : (K a).mkQ w = r) (b : α) :
    (K b).mkQ (Function.update y a w b) = Function.update q a r b := by
  by_cases hb : b = a
  · subst hb
    simp [hw]
  · simp [Function.update_of_ne hb, hy]

def descend [Fintype α] (K : ∀ a, Submodule ℂ (X a)) :
    (Π a, X a ⧸ K a) →ₘₗ[ℂ] ((⨂[ℂ] a, X a) ⧸ pureSpan K) where
  toFun := descendFun K
  map_update_add' := by
    intro _ q a u v
    obtain ⟨su, hu⟩ := Submodule.mkQ_surjective (K a) u
    obtain ⟨sv, hv⟩ := Submodule.mkQ_surjective (K a) v
    have hy := mkQ_rep K q
    rw [descendFun_eq K _ _ (mkQ_update K hy a (w := su + sv) (by rw [map_add (f := _), hu, hv])),
      descendFun_eq K _ _ (mkQ_update K hy a hu), descendFun_eq K _ _ (mkQ_update K hy a hv),
      MultilinearMap.map_update_add, map_add]
  map_update_smul' := by
    intro _ q a c u
    obtain ⟨su, hu⟩ := Submodule.mkQ_surjective (K a) u
    have hy := mkQ_rep K q
    rw [descendFun_eq K _ _ (mkQ_update K hy a (w := c • su) (by rw [map_smul, hu])),
      descendFun_eq K _ _ (mkQ_update K hy a hu), MultilinearMap.map_update_smul, map_smul]

def quotMap (K : ∀ a, Submodule ℂ (X a)) :
    ((⨂[ℂ] a, X a) ⧸ pureSpan K) →ₗ[ℂ] ⨂[ℂ] a, X a ⧸ K a :=
  (pureSpan K).liftQ (PiTensorProduct.map fun a => (K a).mkQ) (Submodule.span_le.2 (by
    rintro _ ⟨x, a, hx, rfl⟩
    show PiTensorProduct.map (fun a => (K a).mkQ) (PiTensorProduct.tprod ℂ x) = 0
    rw [PiTensorProduct.map_tprod]
    exact MultilinearMap.map_coord_zero _ a ((Submodule.Quotient.mk_eq_zero _).2 hx)))

def quotEquiv [Fintype α] (K : ∀ a, Submodule ℂ (X a)) :
    ((⨂[ℂ] a, X a) ⧸ pureSpan K) ≃ₗ[ℂ] ⨂[ℂ] a, X a ⧸ K a :=
  LinearEquiv.ofLinear (quotMap K) (PiTensorProduct.lift (descend K))
    (by
      refine PiTensorProduct.ext (MultilinearMap.ext fun q => ?_)
      show quotMap K (PiTensorProduct.lift (descend K) (PiTensorProduct.tprod ℂ q)) =
        PiTensorProduct.tprod ℂ q
      rw [PiTensorProduct.lift.tprod]
      show PiTensorProduct.map (fun a => (K a).mkQ) (PiTensorProduct.tprod ℂ (rep K q)) = _
      rw [PiTensorProduct.map_tprod]
      exact congrArg _ (funext (mkQ_rep K q)))
    (by
      refine Submodule.linearMap_qext _ (PiTensorProduct.ext (MultilinearMap.ext fun x => ?_))
      show PiTensorProduct.lift (descend K) (PiTensorProduct.map (fun a => (K a).mkQ)
        (PiTensorProduct.tprod ℂ x)) = (pureSpan K).mkQ (PiTensorProduct.tprod ℂ x)
      rw [PiTensorProduct.map_tprod, PiTensorProduct.lift.tprod]
      exact descendFun_eq K _ x fun _ => rfl)

end Modules

section Reps

variable {α : Type} [Fintype α] {Γ X : α → Type} [∀ a, Group (Γ a)] [∀ a, AddCommGroup (X a)]
  [∀ a, Module ℂ (X a)]

theorem twKer_piTensor_le (π : ∀ a, Representation ℂ (Γ a) (X a)) (H : ∀ a, Subgroup (Γ a))
    (χ : ∀ a, H a →* ℂˣ) :
    twKer (piTensor π) (piSub H) (piChar χ) ≤ pureSpan fun a => twKer (π a) (H a) (χ a) := by
  unfold twKer
  apply Submodule.span_le.2
  rintro _ ⟨n, v, rfl⟩
  induction v using PiTensorProduct.induction_on with
  | smul_tprod r x =>
    have e1 : (piTensor π) (n : ∀ a, Γ a) (PiTensorProduct.tprod ℂ x) =
        PiTensorProduct.tprod ℂ (fun a => π a ((n : ∀ a, Γ a) a) (x a)) := by
      show PiTensorProduct.map (fun a => π a ((n : ∀ a, Γ a) a)) (PiTensorProduct.tprod ℂ x) = _
      rw [PiTensorProduct.map_tprod]
    have e2 : ((piChar χ n : ℂˣ) : ℂ) =
        ∏ a, ((χ a ⟨(n : ∀ a, Γ a) a, n.2 a (Set.mem_univ a)⟩ : ℂˣ) : ℂ) := by
      rw [← Units.coe_prod]
      rfl
    have e3 := (MultilinearMap.map_smul_univ (PiTensorProduct.tprod ℂ)
      (fun a => ((χ a ⟨(n : ∀ a, Γ a) a, n.2 a (Set.mem_univ a)⟩ : ℂˣ) : ℂ)) x).symm
    simp only [RingHom.id_apply] at e3
    rw [map_smul, smul_comm, ← smul_sub]
    apply Submodule.smul_mem
    rw [e1, e2, e3]
    apply tprod_sub_mem
    intro a
    apply Submodule.subset_span
    exact ⟨⟨(n : ∀ a, Γ a) a, n.2 a (Set.mem_univ a)⟩, x a, rfl⟩
  | add v₁ v₂ h₁ h₂ =>
    rw [map_add (f := _), smul_add, add_sub_add_comm]
    exact Submodule.add_mem _ h₁ h₂

theorem pureSpan_le_twKer (π : ∀ a, Representation ℂ (Γ a) (X a)) (H : ∀ a, Subgroup (Γ a))
    (χ : ∀ a, H a →* ℂˣ) :
    (pureSpan fun a => twKer (π a) (H a) (χ a)) ≤ twKer (piTensor π) (piSub H) (piChar χ) := by
  classical
  apply Submodule.span_le.2
  rintro _ ⟨x, a, hx, rfl⟩
  have key : ∀ u ∈ twKer (π a) (H a) (χ a),
      PiTensorProduct.tprod ℂ (Function.update x a u) ∈ twKer (piTensor π) (piSub H) (piChar χ) := by
    intro u hu
    unfold twKer at hu
    induction hu using Submodule.span_induction with
    | mem u hu =>
      obtain ⟨g, v, rfl⟩ := hu
      have hn : Pi.mulSingle a (g : Γ a) ∈ piSub H := by
        refine (Subgroup.mem_pi _).2 fun b _ => ?_
        by_cases hb : b = a
        · subst hb
          simp
        · rw [Pi.mulSingle_eq_of_ne hb]
          exact one_mem _
      let n : piSub H := ⟨Pi.mulSingle a (g : Γ a), hn⟩
      have e1 : (piTensor π) (n : ∀ a, Γ a) (PiTensorProduct.tprod ℂ (Function.update x a v)) =
          PiTensorProduct.tprod ℂ (Function.update x a (π a (g : Γ a) v)) := by
        show PiTensorProduct.map (fun b => π b ((n : ∀ a, Γ a) b))
          (PiTensorProduct.tprod ℂ (Function.update x a v)) = _
        rw [PiTensorProduct.map_tprod]
        congr 1
        funext b
        by_cases hb : b = a
        · subst hb
          simp [n]
        · simp [n, Function.update_of_ne hb, Pi.mulSingle_eq_of_ne hb]
      have e2 : ((piChar χ n : ℂˣ) : ℂ) = ((χ a g : ℂˣ) : ℂ) := by
        have hu : (piChar χ n : ℂˣ) = ∏ b, χ b ⟨(n : ∀ a, Γ a) b, n.2 b (Set.mem_univ b)⟩ := rfl
        rw [hu, Finset.prod_eq_single a]
        · have : (⟨(n : ∀ a, Γ a) a, n.2 a (Set.mem_univ a)⟩ : H a) = g := Subtype.ext (by simp [n])
          rw [this]
        · intro b _ hb
          have : (⟨(n : ∀ a, Γ a) b, n.2 b (Set.mem_univ b)⟩ : H b) = 1 :=
            Subtype.ext (by simp [n, Pi.mulSingle_eq_of_ne hb])
          rw [this, map_one]
        · intro h
          exact absurd (Finset.mem_univ a) h
      have hw : PiTensorProduct.tprod ℂ (Function.update x a ((π a) (g : Γ a) v - ((χ a g : ℂˣ) : ℂ) • v)) =
          (piTensor π) (n : ∀ a, Γ a) (PiTensorProduct.tprod ℂ (Function.update x a v)) -
            ((piChar χ n : ℂˣ) : ℂ) • PiTensorProduct.tprod ℂ (Function.update x a v) := by
        rw [MultilinearMap.map_update_sub, MultilinearMap.map_update_smul, RingHom.id_apply, e1, e2]
      rw [hw]
      exact Submodule.subset_span ⟨n, _, rfl⟩
    | zero =>
      rw [MultilinearMap.map_update_zero]
      exact Submodule.zero_mem _
    | add u₁ u₂ _ _ h₁ h₂ =>
      rw [MultilinearMap.map_update_add]
      exact Submodule.add_mem _ h₁ h₂
    | smul c u _ h =>
      rw [MultilinearMap.map_update_smul]
      exact Submodule.smul_mem _ c h
  have := key (x a) hx
  rwa [Function.update_eq_self] at this

theorem twKer_piTensor_eq (π : ∀ a, Representation ℂ (Γ a) (X a)) (H : ∀ a, Subgroup (Γ a))
    (χ : ∀ a, H a →* ℂˣ) :
    twKer (piTensor π) (piSub H) (piChar χ) = pureSpan fun a => twKer (π a) (H a) (χ a) := by
  exact le_antisymm (twKer_piTensor_le π H χ) (pureSpan_le_twKer π H χ)

end Reps

theorem twJacquet_piTensor_equiv : ∀ {α : Type} [Fintype α] {Γ X : α → Type} [∀ a, Group (Γ a)] [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (π : ∀ a, Representation ℂ (Γ a) (X a)) (H : ∀ a, Subgroup (Γ a)) (χ : ∀ a, H a →* ℂˣ), Nonempty (TwJacquet (piTensor π) (piSub H) (piChar χ) ≃ₗ[ℂ] ⨂[ℂ] a, TwJacquet (π a) (H a) (χ a)) := by
  intro α _ Γ X _ _ _ π H χ
  exact ⟨(Submodule.quotEquivOfEq _ _ (twKer_piTensor_eq π H χ)).trans
    (quotEquiv fun a => twKer (π a) (H a) (χ a))⟩

end GlobalTheory.CompanionTheory.Rodier.PiCoinv
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedJacquetTensorProductEquivStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib GlobalTheory.CompanionTheory.Rodier
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_jacquet_tensor_product_equiv : ∀ {α : Type} [Fintype α] {Γ X : α → Type} [∀ a, Group (Γ a)] [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (π : ∀ a, Representation ℂ (Γ a) (X a)) (H : ∀ a, Subgroup (Γ a)) (χ : ∀ a, H a →* ℂˣ), Nonempty (TwJacquet (piTensor π) (piSub H) (piChar χ) ≃ₗ[ℂ] ⨂[ℂ] a, TwJacquet (π a) (H a) (χ a)) := by
  first | exact @GlobalTheory.CompanionTheory.Rodier.PiCoinv.twJacquet_piTensor_equiv | exact GlobalTheory.CompanionTheory.Rodier.PiCoinv.twJacquet_piTensor_equiv | (intros; apply GlobalTheory.CompanionTheory.Rodier.PiCoinv.twJacquet_piTensor_equiv <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeMeasureLocallyFinite
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeMeasureLocallyFinite
noncomputable section

open MeasureTheory Matrix Topology Filter
open scoped ContDiff ENNReal ComplexOrder Pointwise

open PositivityTheory.RgTw (Mat G hb)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.ConeHaar

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.ConeHaar.Fin

variable {n : ℕ}

theorem continuous_hOf : Continuous (hOf (n := n)) := by
  unfold hOf
  refine continuous_finsetSum _ fun p _ => ?_
  exact (Complex.continuous_ofReal.comp (continuous_apply p)).smul continuous_const

theorem continuous_detRe : Continuous fun v : Fin n × Fin n → ℝ => (hOf v).det.re :=
  Complex.continuous_re.comp (continuous_hOf.matrix_det)

theorem detRe_pos {v : Fin n × Fin n → ℝ} (hv : v ∈ cone n) : 0 < (hOf v).det.re := by
  have h : 0 < (hOf v).det := Matrix.PosDef.det_pos hv
  exact (Complex.pos_iff.1 h).1

theorem measurable_coneW : Measurable (coneW n) := by
  unfold coneW
  exact ENNReal.measurable_ofReal.comp ((continuous_detRe.measurable.pow_const n).inv)

theorem exists_hOf_eq_one : ∃ v : Fin n × Fin n → ℝ, hOf v = 1 := by
  refine ⟨fun p => ((1 * hb p : Mat n).trace).re, ?_⟩
  have hre : ∀ p : Fin n × Fin n, ((((1 * hb p : Mat n).trace).re : ℝ) : ℂ) = (1 * hb p : Mat n).trace := by
    intro p
    apply Complex.conj_eq_iff_re.1
    have h1 : star (hb p : Mat n).trace = (hb p : Mat n).trace := by
      rw [← Matrix.trace_conjTranspose, GlobalTheory.CompanionTheory.TwistHomotopy.hb_conjTranspose]
    simpa using h1
  have h := (GlobalTheory.CompanionTheory.TopClass.hbB n).sum_repr (1 : Mat n)
  simp only [GlobalTheory.CompanionTheory.TopClass.hbB_repr, GlobalTheory.CompanionTheory.TopClass.hbB_apply] at h
  conv_rhs => rw [← h]
  simp only [hOf, hre]

theorem cone_nonempty : (cone n).Nonempty := by
  obtain ⟨v, hv⟩ := exists_hOf_eq_one (n := n)
  refine ⟨v, ?_⟩
  show (hOf v).PosDef
  rw [hv]
  exact Matrix.PosDef.one

theorem coneW_pos {v : Fin n × Fin n → ℝ} (hv : v ∈ cone n) : coneW n v ≠ 0 := by
  unfold coneW
  have : 0 < ((hOf v).det.re ^ n)⁻¹ := inv_pos.2 (pow_pos (detRe_pos hv) n)
  exact (ENNReal.ofReal_pos.2 this).ne'

theorem coneMeas_ne_zero : coneMeas n ≠ 0 := by
  intro h0
  have hz := (withDensity_eq_zero measurable_coneW.aemeasurable h0)
  have hopen : IsOpen (cone n) := GlobalTheory.T.positive_cone_isOpen n
  have hvol : 0 < volume (cone n) := hopen.measure_pos volume cone_nonempty
  rw [Filter.EventuallyEq, ae_restrict_iff' hopen.measurableSet] at hz
  have hnull : volume (cone n) = 0 := by
    refine measure_mono_null (t := {v | ¬ (v ∈ cone n → coneW n v = (0 : (Fin n × Fin n → ℝ) → ℝ≥0∞) v)}) ?_ hz
    intro v hv
    simpa using ⟨hv, coneW_pos hv⟩
  exact hvol.ne' hnull

theorem coneMeas_lt_top (C : Set (Fin n × Fin n → ℝ)) (hC : IsCompact C) (hCc : C ⊆ cone n) :
    coneMeas n C < ⊤ := by
  have hcont : ContinuousOn (fun v : Fin n × Fin n → ℝ => ((hOf v).det.re ^ n)⁻¹) C :=
    ContinuousOn.inv₀ (continuous_detRe.pow n).continuousOn
      fun v hv => (pow_pos (detRe_pos (hCc hv)) n).ne'
  obtain ⟨M, hM⟩ := hC.exists_bound_of_continuousOn hcont
  have hle : ∀ v ∈ C, coneW n v ≤ ENNReal.ofReal M := fun v hv =>
    ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (hM v hv))
  unfold coneMeas
  rw [withDensity_apply _ hC.measurableSet]
  calc ∫⁻ v in C, coneW n v ∂(volume.restrict (cone n))
      ≤ ∫⁻ _ in C, ENNReal.ofReal M ∂(volume.restrict (cone n)) :=
        setLIntegral_mono' hC.measurableSet hle
    _ = ENNReal.ofReal M * (volume.restrict (cone n)) C := by simp
    _ ≤ ENNReal.ofReal M * volume C := by
        gcongr
        exact Measure.restrict_le_self
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hC.measure_lt_top

theorem coneMeas_ne_zero_and_lt_top : ∀ n : ℕ, coneMeas n ≠ 0 ∧ ∀ C : Set (Fin n × Fin n → ℝ), IsCompact C →
    C ⊆ PositivityTheory.RgBcC.cone n → coneMeas n C < ⊤ :=
  fun _ => ⟨coneMeas_ne_zero, coneMeas_lt_top⟩

end GlobalTheory.CompanionTheory.ConeHaar.Fin
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeMeasureLocallyFiniteStatement
open MeasureTheory Matrix Topology Filter
open scoped ContDiff ENNReal ComplexOrder Pointwise
open PositivityTheory.RgTw (Mat G hb)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.ConeHaar
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cone_measure_locally_finite : ∀ n : ℕ, coneMeas n ≠ 0 ∧ ∀ C : Set (Fin n × Fin n → ℝ), IsCompact C → C ⊆ PositivityTheory.RgBcC.cone n → coneMeas n C < ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.ConeHaar.Fin.coneMeas_ne_zero_and_lt_top | exact GlobalTheory.CompanionTheory.ConeHaar.Fin.coneMeas_ne_zero_and_lt_top | (intros; apply GlobalTheory.CompanionTheory.ConeHaar.Fin.coneMeas_ne_zero_and_lt_top <;> assumption)
end
end
