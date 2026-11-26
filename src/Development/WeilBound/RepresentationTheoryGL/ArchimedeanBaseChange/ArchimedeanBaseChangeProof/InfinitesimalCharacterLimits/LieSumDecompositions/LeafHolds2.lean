module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.GrowPHolds
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PProjA
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.SqIntCritHolds
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.TopNeg
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PrHolds

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.CptRepMemTypePart
noncomputable section

open NumberField MeasureTheory ComplexConjugate
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CapOrth GlobalTheory.LevelTypeProj GlobalTheory.PRep
  GlobalTheory.CuspRep.LocEx PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.PrAdm

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.Leaf2Aux.Alg

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {N : ℕ}

section Hilb

variable {W : Submodule ℂ (Sm E N)} (h : ∀ φ ∈ W, MemL2Quotient (latticeGL E N) (Measure.haar : Measure (GA E N)) φ.1)

theorem inner_cls_eq_pr {x y : Sm E N} (hx : x ∈ W) (hy : y ∈ W) :
    inner ℂ (cls h x) (cls h y) = pr y.1 x.1 := by
  rw [cls_mk h hx, cls_mk h hy]
  exact MemL2Quotient.inner_toL2_eq_theta_pairing (h y hy) (h x hx)

theorem rep_unique (hinj : ∀ x ∈ W, cls h x = 0 → x = 0) {S : Submodule ℂ (Sm E N)} (hS : S ≤ W) {a b : Sm E N}
    (ha : a ∈ S) (hb : b ∈ S) (e : ∀ u ∈ S, inner ℂ (cls h u) (cls h a) = inner ℂ (cls h u) (cls h b)) : a = b := by
  have hm : a - b ∈ S := S.sub_mem ha hb
  have h0 : inner ℂ (cls h (a - b)) (cls h (a - b)) = 0 := by
    rw [cls_sub h (hS ha) (hS hb), inner_sub_right, ← cls_sub h (hS ha) (hS hb), e _ hm, sub_self]
  exact sub_eq_zero.1 (hinj _ (hS hm) (inner_self_eq_zero.1 h0))

theorem exists_rep (hinj : ∀ x ∈ W, cls h x = 0 → x = 0) (S : Submodule ℂ (Sm E N)) [FiniteDimensional ℂ S]
    (hS : S ≤ W) (f : Sm E N → ℂ) (hadd : ∀ x ∈ S, ∀ y ∈ S, f (x + y) = f x + f y)
    (hsmul : ∀ (c : ℂ), ∀ x ∈ S, f (c • x) = conj c * f x) :
    ∃ a ∈ S, ∀ u ∈ S, f u = inner ℂ (cls h u) (cls h a) := by
  let T : S →ₗ[ℂ] L2 (latticeGL E N) (Measure.haar : Measure (GA E N)) :=
    (toL2ₗ _ W h).comp (Submodule.inclusion hS)
  have hT : Function.Injective T := (injective_iff_map_eq_zero _).2 fun x e => by
    have e' : cls h x.1 = 0 := by rw [cls_mk h (hS x.2)]; exact e
    exact Subtype.ext (hinj _ (hS x.2) e')
  have hTc : ∀ x : S, T x = cls h x.1 := fun x => (cls_mk h (hS x.2)).symm
  let e := LinearEquiv.ofInjective T hT
  have : FiniteDimensional ℂ (LinearMap.range T) := LinearEquiv.finiteDimensional e
  have : CompleteSpace (LinearMap.range T) := FiniteDimensional.complete ℂ _
  let g : LinearMap.range T →ₗ[ℂ] ℂ :=
    { toFun := fun m => conj (f (e.symm m).1)
      map_add' := fun m m' => by
        rw [map_add (f := _), Submodule.coe_add, hadd _ (e.symm m).2 _ (e.symm m').2, map_add (f := _)]
      map_smul' := fun c m => by
        rw [map_smul, Submodule.coe_smul, hsmul c _ (e.symm m).2, map_mul, Complex.conj_conj]
        rfl }
  set t := (InnerProductSpace.toDual ℂ (LinearMap.range T)).symm (LinearMap.toContinuousLinearMap g) with ht
  refine ⟨(e.symm t).1, (e.symm t).2, fun u hu => ?_⟩
  have h1 : cls h (e.symm t).1 = (t : L2 (latticeGL E N) (Measure.haar : Measure (GA E N))) := by
    rw [← hTc]
    exact congrArg Subtype.val (e.apply_symm_apply t)
  have h2 : e.symm ⟨cls h u, ⟨u, hu⟩, hTc ⟨u, hu⟩⟩ = ⟨u, hu⟩ := by
    rw [LinearEquiv.symm_apply_eq]
    exact Subtype.ext (hTc ⟨u, hu⟩).symm
  have h3 := InnerProductSpace.toDual_symm_apply (𝕜 := ℂ) (E := LinearMap.range T)
    (x := (⟨cls h u, ⟨u, hu⟩, hTc ⟨u, hu⟩⟩ : LinearMap.range T)) (y := LinearMap.toContinuousLinearMap g)
  rw [← ht] at h3
  change inner ℂ (t : L2 (latticeGL E N) (Measure.haar : Measure (GA E N))) (cls h u) = conj (f (e.symm _).1) at h3
  rw [h2] at h3
  rw [h1, ← inner_conj_symm, h3, Complex.conj_conj]

end Hilb

theorem coeffSpan_rt {K Y : Type} [Group K] [AddCommGroup Y] [Module ℂ Y] (ρ : Representation ℂ K Y)
    {f : K → ℂ} (hf : f ∈ GlobalTheory.Published.AutFin.coeffSpan ρ) (k₀ : K) :
    (fun k => f (k * k₀)) ∈ GlobalTheory.Published.AutFin.coeffSpan ρ := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨ℓ, w, rfl⟩ := hf
    refine Submodule.subset_span ⟨ℓ, ρ k₀ w, ?_⟩
    funext k
    show ℓ (ρ (k * k₀) w) = _
    rw [map_mul, Module.End.mul_apply]
  | zero => exact zero_mem _
  | add f g _ _ hf hg => exact add_mem hf hg
  | smul c f _ hf => exact Submodule.smul_mem _ c hf

theorem cptRep_mem_typePart {L : Subgroup (GL (Fin N) (Af E))} {Y : Type} [AddCommGroup Y] [Module ℂ Y]
    {ρ : Representation ℂ (Kinf E N) Y} {f : Sm E N} (hf : f ∈ typePart L ρ) (k : Kinf E N) :
    cptRep E N k f ∈ typePart L ρ := by
  refine ⟨fun l hl => by rw [finRep_cptRep, hf.1 l hl], fun g => ?_⟩
  have e : (fun k' : Kinf E N => (cptRep E N k' (cptRep E N k f)).1 g) =
      fun k' => (fun k'' : Kinf E N => (cptRep E N k'' f).1 g) (k' * k) := by
    funext k'
    rw [← Module.End.mul_apply, ← map_mul]
  rw [e]
  exact coeffSpan_rt ρ (hf.2 g) k

section Rep

variable [(Measure.haar : Measure (GA E N)).IsMulRightInvariant] {W : Submodule ℂ (Sm E N)}
  (h : ∀ φ ∈ W, MemL2Quotient (latticeGL E N) (Measure.haar : Measure (GA E N)) φ.1)

theorem rep_rt (h2 : PairRt) {g : GA E N} (hg : ∀ φ ∈ W, GlobalTheory.CuspRep.rt E N g φ ∈ W) (hg' : ∀ φ ∈ W, GlobalTheory.CuspRep.rt E N g⁻¹ φ ∈ W)
    {S : Submodule ℂ (Sm E N)} (hSW : S ≤ W) (hS' : ∀ s ∈ S, GlobalTheory.CuspRep.rt E N g⁻¹ s ∈ S) {χ : Sm E N}
    (hχ : ∀ γ ∈ latticeGL E N, ∀ y, χ.1 (γ * y) = χ.1 y)
    (hSl : ∀ s ∈ S, ∀ γ ∈ latticeGL E N, ∀ y, s.1 (γ * y) = s.1 y) {p : Sm E N} (hp : p ∈ W)
    (hrep : ∀ s ∈ S, pr χ.1 s.1 = inner ℂ (cls h s) (cls h p)) :
    ∀ s ∈ S, pr (GlobalTheory.CuspRep.rt E N g χ).1 s.1 = inner ℂ (cls h s) (cls h (GlobalTheory.CuspRep.rt E N g p)) := by
  intro s hs
  have e1 : pr (GlobalTheory.CuspRep.rt E N g χ).1 s.1 = pr χ.1 (GlobalTheory.CuspRep.rt E N g⁻¹ s).1 := h2 E N g χ.1 s.1 hχ (hSl s hs)
  rw [e1, hrep _ (hS' s hs)]
  have e2 := PrSt.inner_rt h hg hg' hp (hSW hs)
  calc inner ℂ (cls h (GlobalTheory.CuspRep.rt E N g⁻¹ s)) (cls h p) = conj (inner ℂ (cls h p) (cls h (GlobalTheory.CuspRep.rt E N g⁻¹ s))) :=
        (inner_conj_symm _ _).symm
    _ = conj (inner ℂ (cls h (GlobalTheory.CuspRep.rt E N g p)) (cls h s)) := by rw [e2]
    _ = inner ℂ (cls h s) (cls h (GlobalTheory.CuspRep.rt E N g p)) := inner_conj_symm _ _

theorem rep_mem_typePart (h1 : PairLin) (h2 : PairRt) (hinj : ∀ x ∈ W, cls h x = 0 → x = 0) (hW : _root_.GlobalTheory.CuspRep.IsStable W)
    (hWQ : ∀ s ∈ W, GrowQ s.1) {U : Submodule ℂ (Sm E N)} (hU : _root_.GlobalTheory.CuspRep.IsStable U) (hUP : ∀ χ ∈ U, GrowP χ.1)
    {χ : Sm E N} (hχ : χ ∈ U) [FiniteDimensional ℂ (orbSpan χ)] {L : Subgroup (GL (Fin N) (Af E))} {Y : Type}
    [AddCommGroup Y] [Module ℂ Y] {ρ : Representation ℂ (Kinf E N) Y} (hχT : χ ∈ typePart L ρ)
    (S : Submodule ℂ (Sm E N)) [FiniteDimensional ℂ S] (hSW : S ≤ W)
    (hSL : ∀ l ∈ L, ∀ s ∈ S, finRep E N l s ∈ S) (hSK : ∀ k, ∀ s ∈ S, cptRep E N k s ∈ S) {p : Sm E N}
    (hp : p ∈ S) (hrep : ∀ s ∈ S, pr χ.1 s.1 = inner ℂ (cls h s) (cls h p)) : p ∈ typePart L ρ := by
  have hSl : ∀ s ∈ S, ∀ γ ∈ latticeGL E N, ∀ y, s.1 (γ * y) = s.1 y := fun s hs => (hWQ s (hSW hs)).2.1
  have hex : ∀ χ' ∈ U, ∃ a ∈ S, ∀ s ∈ S, pr χ'.1 s.1 = inner ℂ (cls h s) (cls h a) := fun χ' hχ' =>
    exists_rep h hinj S hSW (fun s => pr χ'.1 s.1)
      (fun x hx y hy => ((h1 E N).2 χ'.1 x.1 y.1 1 (hUP χ' hχ') (hWQ x (hSW hx)) (hWQ y (hSW hy))).1)
      (fun c x hx => ((h1 E N).2 χ'.1 x.1 x.1 c (hUP χ' hχ') (hWQ x (hSW hx)) (hWQ x (hSW hx))).2)
  refine ⟨fun l hl => ?_, fun x => ?_⟩
  · have hg : ∀ φ ∈ W, GlobalTheory.CuspRep.rt E N (finGL E N l) φ ∈ W := fun φ hφ => hW (.fin l) φ hφ
    have hg' : ∀ φ ∈ W, GlobalTheory.CuspRep.rt E N (finGL E N l)⁻¹ φ ∈ W := fun φ hφ => by
      rw [← map_inv]; exact hW (.fin l⁻¹) φ hφ
    have hS' : ∀ s ∈ S, GlobalTheory.CuspRep.rt E N (finGL E N l)⁻¹ s ∈ S := fun s hs => by
      rw [← map_inv]; exact hSL l⁻¹ (L.inv_mem hl) s hs
    have ht := rep_rt h h2 hg hg' hSW hS' (hUP χ hχ).2.1 hSl (hSW hp) hrep
    refine rep_unique h hinj hSW (hSL l hl p hp) hp fun s hs => ?_
    have e : GlobalTheory.CuspRep.rt E N (finGL E N l) χ = χ := hχT.1 l hl
    have e2 := ht s hs
    rw [e] at e2
    rw [← hrep s hs, e2]
    rfl
  · let O := orbSpan χ
    have hOU : O ≤ U := Submodule.span_le.2 (by rintro _ ⟨k, rfl⟩; exact hU (.cpt k) χ hχ)
    choose! Q hQS hQ using hex
    let Φ : O →ₗ[ℂ] Sm E N :=
      { toFun := fun χ' => Q χ'.1
        map_add' := fun a b => by
          refine rep_unique h hinj hSW (hQS _ (hOU (a + b).2))
            (S.add_mem (hQS _ (hOU a.2)) (hQS _ (hOU b.2))) fun s hs => ?_
          rw [← hQ (a + b : O).1 (hOU (a + b).2) s hs, cls_add h (hSW (hQS _ (hOU a.2))) (hSW (hQS _ (hOU b.2))),
            inner_add_right, ← hQ _ (hOU a.2) s hs, ← hQ _ (hOU b.2) s hs]
          exact ((h1 E N).1 a.1.1 b.1.1 s.1 1 (hUP _ (hOU a.2)) (hUP _ (hOU b.2)) (hWQ s (hSW hs))).1
        map_smul' := fun c a => by
          refine rep_unique h hinj hSW (hQS _ (hOU (c • a).2)) (S.smul_mem c (hQS _ (hOU a.2)))
            fun s hs => ?_
          rw [← hQ (c • a : O).1 (hOU (c • a).2) s hs, RingHom.id_apply, cls_smul h c (hSW (hQS _ (hOU a.2))),
            inner_smul_right, ← hQ _ (hOU a.2) s hs]
          exact ((h1 E N).1 a.1.1 a.1.1 s.1 c (hUP _ (hOU a.2)) (hUP _ (hOU a.2)) (hWQ s (hSW hs))).2 }
    have hΦ : ∀ k, cptRep E N k p = Φ ⟨cptRep E N k χ, Submodule.subset_span ⟨k, rfl⟩⟩ := fun k => by
      have hg : ∀ φ ∈ W, GlobalTheory.CuspRep.rt E N (infGL E N (Unitary.toUnits k)) φ ∈ W := fun φ hφ => hW (.cpt k) φ hφ
      have hg' : ∀ φ ∈ W, GlobalTheory.CuspRep.rt E N (infGL E N (Unitary.toUnits k))⁻¹ φ ∈ W := fun φ hφ => by
        rw [← map_inv, ← map_inv]; exact hW (.cpt k⁻¹) φ hφ
      have hS' : ∀ s ∈ S, GlobalTheory.CuspRep.rt E N (infGL E N (Unitary.toUnits k))⁻¹ s ∈ S := fun s hs => by
        rw [← map_inv, ← map_inv]; exact hSK k⁻¹ s hs
      have ht := rep_rt h h2 hg hg' hSW hS' (hUP χ hχ).2.1 hSl (hSW hp) hrep
      have hkU : cptRep E N k χ ∈ U := hU (.cpt k) χ hχ
      refine rep_unique h hinj hSW (hSK k p hp) (hQS _ hkU) fun s hs => ?_
      show _ = inner ℂ (cls h s) (cls h (Q (cptRep E N k χ)))
      rw [← hQ _ hkU s hs]
      exact (ht s hs).symm
    let Λ : Module.Dual ℂ O →ₗ[ℂ] (Kinf E N → ℂ) :=
      { toFun := fun ℓ k => ℓ ⟨cptRep E N k χ, Submodule.subset_span ⟨k, rfl⟩⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    let ev : GA E N → Module.Dual ℂ O := fun y => (LinearMap.proj y).comp ((Sm E N).subtype.comp O.subtype)
    have htop := span_eval_eq_top ev fun w hw => Subtype.ext (Subtype.ext (funext hw))
    have hle : Submodule.span ℂ (Set.range ev) ≤ (GlobalTheory.Published.AutFin.coeffSpan ρ).comap Λ :=
      Submodule.span_le.2 (by rintro _ ⟨y, rfl⟩; exact hχT.2 y)
    let ℓ : Module.Dual ℂ O := (LinearMap.proj x).comp ((Sm E N).subtype.comp Φ)
    have hℓ : Λ ℓ ∈ GlobalTheory.Published.AutFin.coeffSpan ρ := hle (htop ▸ Submodule.mem_top)
    convert hℓ using 1
    funext k
    rw [hΦ k]
    rfl

theorem exists_repV (h1 : PairLin) (h2 : PairRt) (hinj : ∀ x ∈ W, cls h x = 0 → x = 0) (hW : _root_.GlobalTheory.CuspRep.IsStable W)
    (hWA : ∀ x ∈ W, IsAutForm x) (hWQ : ∀ s ∈ W, GrowQ s.1) {V : Submodule ℂ (Sm E N)} (hV : _root_.GlobalTheory.CuspRep.IsStable V)
    (hVW : V ≤ W)
    (hVfd : ∀ (L : Subgroup (GL (Fin N) (Af E))), IsOpen (L : Set (GL (Fin N) (Af E))) → ∀ (Y : Type)
      [AddCommGroup Y] [Module ℂ Y] [FiniteDimensional ℂ Y] (ρ : Representation ℂ (Kinf E N) Y),
        GlobalTheory.Published.AutFin.IsContRep ρ → FiniteDimensional ℂ (V ⊓ typePart L ρ : Submodule ℂ (Sm E N)))
    {U : Submodule ℂ (Sm E N)} (hU : _root_.GlobalTheory.CuspRep.IsStable U) (hUA : ∀ χ ∈ U, IsAutForm χ) (hUP : ∀ χ ∈ U, GrowP χ.1)
    {χ : Sm E N} (hχ : χ ∈ U) : ∃ a ∈ V, ∀ u ∈ V, pr χ.1 u.1 = inner ℂ (cls h u) (cls h a) := by
  obtain ⟨L, hLo, hLc, hχT⟩ := exists_type (hUA χ hχ)
  have : FiniteDimensional ℂ (orbSpan χ) := (hUA χ hχ).kfin
  have hρ := isContRep_sub (orbSpan χ) (orbSpan_stable χ)
  set ρ := sub (cptRep E N) (orbSpan χ) (orbSpan_stable χ)
  set F : Submodule ℂ (Sm E N) := V ⊓ typePart L ρ with hFdef
  have : FiniteDimensional ℂ F := hVfd L hLo _ ρ hρ
  have hFW : F ≤ W := inf_le_left.trans hVW
  have hadd : ∀ (S : Submodule ℂ (Sm E N)), S ≤ W → ∀ x ∈ S, ∀ y ∈ S,
      pr χ.1 (x + y).1 = pr χ.1 x.1 + pr χ.1 y.1 :=
    fun S hS x hx y hy => ((h1 E N).2 χ.1 x.1 y.1 1 (hUP χ hχ) (hWQ x (hS hx)) (hWQ y (hS hy))).1
  have hsm : ∀ (S : Submodule ℂ (Sm E N)), S ≤ W → ∀ (c : ℂ), ∀ x ∈ S, pr χ.1 (c • x).1 = conj c * pr χ.1 x.1 :=
    fun S hS c x hx => ((h1 E N).2 χ.1 x.1 x.1 c (hUP χ hχ) (hWQ x (hS hx)) (hWQ x (hS hx))).2
  obtain ⟨a, haF, ha⟩ := exists_rep h hinj F hFW (fun s => pr χ.1 s.1) (hadd F hFW) (hsm F hFW)
  refine ⟨a, haF.1, fun u hu => ?_⟩
  have : FiniteDimensional ℂ (orbitSpan L u) := orbitSpan_finiteDimensional L hLc u (hWA u (hVW hu))
  set S' : Submodule ℂ (Sm E N) := orbitSpan L u ⊔ F with hS'def
  have hS'V : S' ≤ V := sup_le (orbitSpan_le hV L hu) inf_le_left
  have hS'W : S' ≤ W := hS'V.trans hVW
  have hSL : ∀ l ∈ L, ∀ s ∈ S', finRep E N l s ∈ S' := fun l hl s hs => by
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hs
    rw [map_add (f := _)]
    refine add_mem (Submodule.mem_sup_left (finRep_mem_orbitSpan hl hy)) (Submodule.mem_sup_right ?_)
    rw [hz.2.1 l hl]
    exact hz
  have hSK : ∀ k, ∀ s ∈ S', cptRep E N k s ∈ S' := fun k s hs => by
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hs
    rw [map_add (f := _)]
    exact add_mem (Submodule.mem_sup_left (cptRep_mem_orbitSpan k hy))
      (Submodule.mem_sup_right ⟨hV (.cpt k) z hz.1, cptRep_mem_typePart hz.2 k⟩)
  obtain ⟨p, hpS, hp⟩ := exists_rep h hinj S' hS'W (fun s => pr χ.1 s.1) (hadd S' hS'W) (hsm S' hS'W)
  have hpT := rep_mem_typePart h h1 h2 hinj hW hWQ hU hUP hχ hχT S' hS'W hSL hSK hpS hp
  have hpF : p ∈ F := ⟨hS'V hpS, hpT⟩
  have hpa : p = a := rep_unique h hinj hFW hpF haF fun s hs => by
    rw [← hp s (Submodule.mem_sup_right hs), ← ha s hs]
  rw [hp u (Submodule.mem_sup_left (mem_orbitSpan_self L u)), hpa]

end Rep

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.Leaf2Aux.Alg

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.Leaf2Aux


open Alg in
theorem core_of (h1 : PairLin) (h2 : PairRt) (h3 : PairLie) (h4 : GrowQHolds) : Core := by
  intro E _ _ _ N U hU hUA hUP φ hφU hφA hφ0
  have : (Measure.haar : Measure (GA E N)).IsMulRightInvariant := GlobalTheory.CovolGL.isMulRightInvariant E N _
  have hF := PositivityTheory.Rg.HF.GL.automorphicFormsFiniteGL
  have hW : _root_.GlobalTheory.CuspRep.IsStable (A2 E N) := PrSt.isStable_square_integrable_forms hF
  have hA : ∀ x ∈ A2 E N, IsAutForm x := fun x hx => (PrSt.mem_square_integrable_forms hx).1
  have h : ∀ x ∈ A2 E N, MemL2Quotient (latticeGL E N) (Measure.haar : Measure (GA E N)) x.1 := fun x hx =>
    memL2_of_isAutForm (PrSt.mem_square_integrable_forms hx).1 (PrSt.mem_square_integrable_forms hx).2
  have hF2 := toL2ₗ_injective h fun x hx => ContAut.continuous_of_isOpen_stab E N x (hA x hx).level
  have hinj : ∀ x ∈ A2 E N, cls h x = 0 → x = 0 := fun x hx e => by
    rw [cls_mk h hx] at e
    exact congrArg Subtype.val (hF2 (e.trans (map_zero _).symm))
  have hadj := fun o => PrSt.exists_adj h hW hA o
  obtain ⟨V, hVst, hVA, hV0, hirr, v, hvV, hvφ⟩ := PrIrr.exists_irr h hW hA hinj hadj hφA hφ0
  have hVW : V ≤ A2 E N := hVA.trans (admissible_span_le _ φ)
  have hWQ : ∀ s ∈ A2 E N, GrowQ s.1 := fun s hs => h4 E N s (PrSt.mem_square_integrable_forms hs).1 (PrSt.mem_square_integrable_forms hs).2
  have hVfd : ∀ (L : Subgroup (GL (Fin N) (Af E))), IsOpen (L : Set (GL (Fin N) (Af E))) → ∀ (Y : Type)
      [AddCommGroup Y] [Module ℂ Y] [FiniteDimensional ℂ Y] (ρ : Representation ℂ (Kinf E N) Y),
        GlobalTheory.Published.AutFin.IsContRep ρ → FiniteDimensional ℂ (V ⊓ typePart L ρ : Submodule ℂ (Sm E N)) := by
    intro L hLo Y _ _ _ ρ hρ
    have := finiteDimensional_admissible_isotypic hA (hA φ hφA) hLo ρ hρ
    exact Submodule.finiteDimensional_of_le (inf_le_inf_right _ hVA)
  have hrep : ∀ χ ∈ U, ∃ a ∈ V, ∀ u ∈ V, pr χ.1 u.1 = inner ℂ (cls h u) (cls h a) := fun χ hχ =>
    exists_repV h h1 h2 hinj hW hA hWQ hVst hVW hVfd hU hUA hUP hχ
  choose! P hPV hP using hrep
  let pU : U →ₗ[ℂ] Sm E N :=
    { toFun := fun χ => P χ.1
      map_add' := fun x y => by
        refine rep_unique h hinj hVW (hPV _ (x + y).2) (V.add_mem (hPV _ x.2) (hPV _ y.2)) fun u hu => ?_
        rw [← hP (x + y : U).1 (x + y).2 u hu, cls_add h (hVW (hPV _ x.2)) (hVW (hPV _ y.2)), inner_add_right,
          ← hP _ x.2 u hu, ← hP _ y.2 u hu]
        exact ((h1 E N).1 x.1.1 y.1.1 u.1 1 (hUP _ x.2) (hUP _ y.2) (hWQ u (hVW hu))).1
      map_smul' := fun c x => by
        refine rep_unique h hinj hVW (hPV _ (c • x).2) (V.smul_mem c (hPV _ x.2)) fun u hu => ?_
        rw [← hP (c • x : U).1 (c • x).2 u hu, RingHom.id_apply, cls_smul h c (hVW (hPV _ x.2)),
          inner_smul_right, ← hP _ x.2 u hu]
        exact ((h1 E N).1 x.1.1 x.1.1 u.1 c (hUP _ x.2) (hUP _ x.2) (hWQ u (hVW hu))).2 }
  obtain ⟨p, hp⟩ := LinearMap.exists_extend pU
  have hpU : ∀ χ ∈ U, p χ = P χ := fun χ hχ => LinearMap.congr_fun hp ⟨χ, hχ⟩
  refine ⟨V, p, ⟨fun x hx => hA x (hVW hx), fun x hx => (PrSt.mem_square_integrable_forms (hVW hx)).2, hVst, hV0, hirr⟩,
    fun χ hχ => by rw [hpU χ hχ]; exact hPV χ hχ, fun o χ hχ => ?_, ?_⟩
  · rw [hpU _ (hU o χ hχ), hpU χ hχ]
    refine rep_unique h hinj hVW (hPV _ (hU o χ hχ)) (hVst o _ (hPV χ hχ)) fun u hu => ?_
    rw [← hP _ (hU o χ hχ) u hu]
    have hχl := (hUP χ hχ).2.1
    have hVl : ∀ s ∈ V, ∀ γ ∈ latticeGL E N, ∀ y, s.1 (γ * y) = s.1 y := fun s hs => (hWQ s (hVW hs)).2.1
    cases o with
    | fin k =>
      have hg : ∀ x ∈ A2 E N, GlobalTheory.CuspRep.rt E N (finGL E N k) x ∈ A2 E N := fun x hx => hW (.fin k) x hx
      have hg' : ∀ x ∈ A2 E N, GlobalTheory.CuspRep.rt E N (finGL E N k)⁻¹ x ∈ A2 E N := fun x hx => by
        rw [← map_inv]; exact hW (.fin k⁻¹) x hx
      have hS' : ∀ s ∈ V, GlobalTheory.CuspRep.rt E N (finGL E N k)⁻¹ s ∈ V := fun s hs => by
        rw [← map_inv]; exact hVst (.fin k⁻¹) s hs
      exact rep_rt h h2 hg hg' hVW hS' hχl hVl (hVW (hPV χ hχ)) (hP χ hχ) u hu
    | cpt k =>
      have hg : ∀ x ∈ A2 E N, GlobalTheory.CuspRep.rt E N (infGL E N (Unitary.toUnits k)) x ∈ A2 E N := fun x hx => hW (.cpt k) x hx
      have hg' : ∀ x ∈ A2 E N, GlobalTheory.CuspRep.rt E N (infGL E N (Unitary.toUnits k))⁻¹ x ∈ A2 E N := fun x hx => by
        rw [← map_inv, ← map_inv]; exact hW (.cpt k⁻¹) x hx
      have hS' : ∀ s ∈ V, GlobalTheory.CuspRep.rt E N (infGL E N (Unitary.toUnits k))⁻¹ s ∈ V := fun s hs => by
        rw [← map_inv, ← map_inv]; exact hVst (.cpt k⁻¹) s hs
      exact rep_rt h h2 hg hg' hVW hS' hχl hVl (hVW (hPV χ hχ)) (hP χ hχ) u hu
    | lie X =>
      have e1 := h3 E N X χ u (hUP χ hχ) (hUP _ (hU (.lie X) χ hχ)) (hWQ u (hVW hu))
        (hWQ _ (hW (.lie X) u (hVW hu)))
      rw [e1, hP χ hχ _ (hVst (.lie X) u hu)]
      have e2 := GlobalTheory.LieSkew.lie_skew E N (Measure.haar : Measure (GA E N)) (A2 E N) h hW hA X ⟨u, hVW hu⟩
        ⟨P χ, hVW (hPV χ hχ)⟩
      rw [cls_mk h (hW (.lie X) u (hVW hu)), cls_mk h (hVW (hPV χ hχ)), cls_mk h (hVW hu),
        cls_mk h (hW (.lie X) (P χ) (hVW (hPV χ hχ)))]
      rw [e2, neg_neg]
  · rw [hpU φ hφU]
    intro e
    have h0 := hP φ hφU v hvV
    rw [e, show (0 : Sm E N) = (0 : ℂ) • (0 : Sm E N) by simp, cls_smul h 0 (A2 E N).zero_mem, zero_smul,
      inner_zero_right] at h0
    have h5 := inner_cls_eq_pr h (hVW hvV) hφA
    apply hvφ
    rw [← inner_conj_symm, h5, h0, map_zero]

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.Leaf2Aux

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.UntwExp
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.Leaf2Aux.Tw

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}

omit [IsCMField E] in
theorem re_tw {z : ℂ} (hz : z.re = 0) : (z / (N * (Module.finrank ℚ E : ℂ))).re = 0 := by
  rw [Complex.div_re]
  simp [hz]

theorem untw_cen (hN : 0 < N) {z : ℂ} {φ : Sm E N}
    (hc : ∀ (t : ℝ) g, φ.1 (splitCentre E N t * g) = Complex.exp (z * t) * φ.1 g) (t : ℝ) (g : GA E N) :
    (mulChi N (Model.absC E (-(z / (N * (Module.finrank ℚ E : ℂ))))) φ).1 (splitCentre E N t * g) =
      (mulChi N (Model.absC E (-(z / (N * (Module.finrank ℚ E : ℂ))))) φ).1 g := by
  have hd : (Module.finrank ℚ E : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  have hNc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  set w := z / (N * (Module.finrank ℚ E : ℂ)) with hw
  have hcd : ∀ t : ℝ, ((chiDet N (Model.absC E (-w)) (splitCentre E N t) : ℂˣ) : ℂ) = Complex.exp (-(z * t)) := by
    intro t
    rw [ExponentTwist.splitCentre_eq, ExponentTwist.chiDet_aT le_rfl]
    congr 1
    rw [hw]
    field_simp
  rw [mulChi_apply, mulChi_apply, hc t g, map_mul, Units.val_mul, hcd t]
  have e : Complex.exp (z * t) * Complex.exp (-(z * t)) = 1 := by
    rw [← Complex.exp_add]; simp
  linear_combination (φ.1 g * ((chiDet N (Model.absC E (-w)) g : ℂˣ) : ℂ)) * e

theorem untw_exp {z : ℂ} (hz : z.re = 0) {φ : Sm E N} (hA : IsAutForm φ) (r : ℕ) (hr : 0 < r) (hrN : r < N) (c : ℂ)
    (hc : c ∈ Exp r (mulChi N (Model.absC E (-(z / (N * (Module.finrank ℚ E : ℂ))))) φ).1) :
    ∃ c' ∈ Exp r φ.1, pE E N r c = pE E N r c' := by
  have hd : (Module.finrank ℚ E : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  have hNc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  set w := z / (N * (Module.finrank ℚ E : ℂ)) with hw
  have h1 := expTw_holds E N φ (-w) hA r hr hrN c hc
  refine ⟨_, h1, ?_⟩
  have e : -w * (r : ℂ) * (Module.finrank ℚ E : ℂ) = (((-(r : ℝ) / N) : ℝ) : ℂ) * z := by
    rw [hw]; push_cast; field_simp
  have hre : (c - -w * (r : ℂ) * (Module.finrank ℚ E : ℂ)).re = c.re := by
    rw [e, Complex.sub_re, Complex.re_ofReal_mul, hz, mul_zero, sub_zero]
  unfold pE
  rw [hre]

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.Leaf2Aux.Tw

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.Leaf2Aux

open Tw ParabolicProjection in
theorem leaf_of (hC : Core) (hP : GrowPHolds) : Leaf := by
  intro E _ _ _ N τ hN U hU φ hφU hneg hφ0
  obtain ⟨⟨hst, hA⟩, -, hNP, ⟨z, hz, hcent⟩, -⟩ := hU
  have aut_tw {a : ℕ} {ψ : Sm E a} (h : IsAutForm ψ) (χ : HChar E) :
      IsAutForm (mulChi a χ ψ) := by
    exact {
      left γ g := by simp [h.left, chiDet_ratGL]
      level := isOpen_stab_of_mem_nhds _ _ <| Filter.mem_of_superset
        ((h.level.inter (isOpen_ker_chiDet χ)).mem_nhds ⟨by simp, by simp⟩) fun k hk => by
          have h1 : GlobalTheory.CuspRep.rt E a (finGL E a k) ψ = ψ := hk.1
          have h2 : chiDet a χ (finGL E a k) = 1 := hk.2
          change GlobalTheory.CuspRep.rt E a (finGL E a k) _ = _
          rw [rt_mulChi, h1, h2, Units.val_one, one_smul]
      kfin := by
        have := h.kfin
        refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ (Set.range fun k => cptRep E a k ψ)).map
          (GlobalTheory.CuspRep.mulChi a χ).toLinearMap) (Submodule.span_le.2 ?_)
        rintro _ ⟨k, rfl⟩
        exact ⟨_, Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩), (rt_mulChi χ _ ψ).symm⟩
      zfin := by
        have := h.zfin
        refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z ψ) ''
          Zalg E a)).map (GlobalTheory.CuspRep.mulChi a χ).toLinearMap) (Submodule.span_le.2 ?_)
        rintro _ ⟨z, hz, rfl⟩
        obtain ⟨z', h1, h2⟩ := Zalg_mulChi χ hz
        exact ⟨_, Submodule.subset_span ⟨z', h1, rfl⟩, (h2 ψ).symm⟩
      growth g := by
        obtain ⟨C, N, h1⟩ := h.growth g
        obtain ⟨C', N', h2⟩ := chiDet_growth (a := a) χ
        refine ⟨C * (‖((chiDet a χ g : ℂˣ) : ℂ)‖ * C'), N + N', fun y => ?_⟩
        rw [mulChi_apply, map_mul, Units.val_mul, norm_mul, norm_mul]
        refine (mul_le_mul (h1 y) (mul_le_mul_of_nonneg_left (h2 y) (norm_nonneg _)) (by positivity)
          ((norm_nonneg _).trans (h1 y))).trans_eq ?_
        ring }
  set w := z / (N * (Module.finrank ℚ E : ℂ)) with hw
  have hU'st : _root_.GlobalTheory.CuspRep.IsStable (tw U (-w)) := isStable_tw hst (-w)
  have hU'A : ∀ χ ∈ tw U (-w), IsAutForm χ := by
    rintro _ ⟨ψ, hψ, rfl⟩
    exact aut_tw (hA ψ hψ) _
  have hU'P : ∀ χ ∈ tw U (-w), GrowP χ.1 := by
    rintro _ ⟨ψ, hψ, rfl⟩
    refine hP E N _ (aut_tw (hA ψ hψ) _) (untw_cen hN (hcent ψ hψ)) fun r hr hrN c hc => ?_
    obtain ⟨c', hc', e⟩ := untw_exp hz (hA ψ hψ) r hr hrN c hc
    rw [e]
    exact hNP ψ hψ r hr hrN c' hc'
  have hφ'A2 : mulChi N (Model.absC E (-w)) φ ∈ A2 E N := by
    refine Submodule.subset_span ⟨aut_tw (hA φ hφU) _, sqIntCrit_holds E N _ (aut_tw (hA φ hφU) _)
      (untw_cen hN (hcent φ hφU)) fun r hr hrN c hc => ?_⟩
    obtain ⟨c', hc', e⟩ := untw_exp hz (hA φ hφU) r hr hrN c hc
    rw [e]
    exact hneg r hr hrN c' hc'
  have hφ'0 : mulChi N (Model.absC E (-w)) φ ≠ 0 := by
    rw [Ne, LinearEquiv.map_eq_zero_iff]; exact hφ0
  obtain ⟨V, p, hV, hpV, hpe, hp0⟩ :=
    hC E N (tw U (-w)) hU'st hU'A hU'P _ ⟨φ, hφU, rfl⟩ hφ'A2 hφ'0
  have hUle : ∀ ψ ∈ U, ψ ∈ tw (tw U (-w)) w := fun ψ hψ => ⟨_, ⟨ψ, hψ, rfl⟩, mulChi_absC_neg' N w ψ⟩
  refine ⟨.leaf V w, twMap N w p, Or.inr ⟨hN, hV, re_tw hz⟩, hN,
    fun o ψ hψ => twMap_equiv hU'st hpe o ψ (hUle ψ hψ), fun ψ hψ => twMap_mem hpV ψ (hUle ψ hψ), ?_⟩
  rw [twMap_apply, Ne, LinearEquiv.map_eq_zero_iff]
  exact hp0

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.Leaf2Aux

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.ReLtRho
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.AutomorphicL2Unitary PositivityTheory.Rg.Rs
open scoped Pointwise ENNReal

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.Leaf2Aux

namespace Grow

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {N : ℕ}

theorem leftInv {φ : Sm E N} (hφ : IsAutForm φ) (hcen : ∀ (t : ℝ) g, φ.1 (splitCentre E N t * g) = φ.1 g) :
    ∀ γ ∈ latticeGL E N, ∀ g, φ.1 (γ * g) = φ.1 g := by
  let S : Subgroup (GA E N) :=
    { carrier := {γ | ∀ g, φ.1 (γ * g) = φ.1 g}
      one_mem' := fun g => by rw [one_mul]
      mul_mem' := fun {x y} hx hy g => by rw [mul_assoc, hx, hy]
      inv_mem' := fun {x} hx g => by rw [← hx, mul_inv_cancel_left] }
  have : latticeGL E N ≤ S := sup_le (by rintro _ ⟨γ, rfl⟩; exact hφ.left γ) (Subgroup.zpowers_le.2 (hcen 1))
  exact this

theorem exists_kill {φ : Sm E N} (hφ : IsAutForm φ) (hcen : ∀ (t : ℝ) g, φ.1 (splitCentre E N t * g) = φ.1 g)
    {r : ℕ} (hr0 : 0 < r) (hrN : r < N) :
    ∃ p : ℂ[X], p.Monic ∧ An.Kill r φ.1 p ∧ ∀ z, p.IsRoot z → ∃ c ∈ Exp r φ.1, z = Complex.exp c := by
  obtain ⟨hA, hS, _, hCT⟩ := dict_holds E N
  have hcen' : ∀ (t : ℝ) g, φ.1 (An.tor E (fun _ => t) * g) = φ.1 g := fun t g => by
    rw [← hS]; exact hcen t g
  have hnice := niceAut_holds E N φ hφ hcen'
  have hct := (hCT φ hφ r hr0 hrN).1
  have hfin := finTr_holds E N φ hφ r hr0 hrN _ hct
  have hadd : ∀ s t, aT E N r (s + t) = aT E N r s * aT E N r t := fun s t => by
    rw [hA, hA, hA]; exact JSqIntGlue.aR_add r s t
  have hcont : ∀ g, Continuous fun t => An.ctn r φ.1 (aT E N r t * g) := by
    intro g
    have e : (fun t => An.ctn r φ.1 (aT E N r t * g)) = fun t => An.ctn r φ.1 (An.aR E N r t * g) :=
      funext fun t => by rw [hA]
    rw [e]
    exact JSqIntGlue.continuous_ctn_comp hnice.cont r ((JSqIntGlue.continuous_aR r).mul continuous_const)
  obtain ⟨p, hp, hpk, hroots⟩ := killPoly_holds (GA E N) (aT E N r) (An.ctn r φ.1) hadd hcont hfin
  refine ⟨p, hp, fun g => ?_, fun z hz => ?_⟩
  · have := hpk g
    simpa only [hA] using this
  · obtain ⟨c, rfl, F, hF, hF0, hFe⟩ := hroots z hz
    exact ⟨c, ⟨_, hct, F, hF, hF0, hFe⟩, rfl⟩

theorem bnd_of' {φ : Sm E N} (hφ : IsAutForm φ) (hcen : ∀ (t : ℝ) g, φ.1 (splitCentre E N t * g) = φ.1 g)
    (κ : ℕ → ℝ) (hκ : ∀ r, 0 < r → r < N → ∃ p : ℂ[X], p.Monic ∧ An.Kill r φ.1 p ∧
      ∀ z, p.IsRoot z → ‖z‖ < Real.exp (κ r)) : An.Bnd φ.1 κ := by
  obtain ⟨_, hS, _, _⟩ := dict_holds E N
  have hcen' : ∀ (t : ℝ) g, φ.1 (An.tor E (fun _ => t) * g) = φ.1 g := fun t g => by
    rw [← hS]; exact hcen t g
  have hnice := niceAut_holds E N φ hφ hcen'
  obtain ⟨M, hM⟩ := initBnd_holds E N φ hφ hcen'
  exact GlobalTheory.CompanionTheory.AnBoot.bootGlue diffstep_holds (ctstepglue_holds GlobalTheory.CompanionTheory.LinRec.recBound) E N φ.1 M κ hnice hM hκ

theorem bnd_of {φ : Sm E N} (hφ : IsAutForm φ) (hcen : ∀ (t : ℝ) g, φ.1 (splitCentre E N t * g) = φ.1 g)
    (κ : ℕ → ℝ) (hκ : ∀ r, 0 < r → r < N → ∀ c ∈ Exp r φ.1, c.re < κ r) : An.Bnd φ.1 κ := by
  refine bnd_of' hφ hcen κ fun r hr0 hrN => ?_
  obtain ⟨p, hp, hk, hroots⟩ := exists_kill hφ hcen hr0 hrN
  refine ⟨p, hp, hk, fun z hz => ?_⟩
  obtain ⟨c, hc, rfl⟩ := hroots z hz
  rw [Complex.norm_exp]
  exact Real.exp_lt_exp.2 (hκ r hr0 hrN c hc)

omit [_root_.NumberField.IsTotallyComplex E] in
theorem re_le_rho {r : ℕ} {c : ℂ} (h : pE E N r c ≤ 0) : c.re ≤ An.rho E N r := by
  have hd : (0 : ℝ) < Module.finrank ℚ E := by exact_mod_cast Module.finrank_pos
  unfold pE at h
  have h2 : c.re / (Module.finrank ℚ E : ℝ) ≤ (r : ℝ) * ((N : ℝ) - r) / 2 := by linarith
  have h3 := (div_le_iff₀ hd).1 h2
  unfold An.rho
  calc c.re ≤ (r : ℝ) * ((N : ℝ) - r) / 2 * (Module.finrank ℚ E : ℝ) := h3
    _ = _ := by ring

omit [_root_.NumberField.IsTotallyComplex E] in
theorem re_lt_rho {r : ℕ} {c : ℂ} (h : pE E N r c < 0) : c.re < An.rho E N r := by
  have hd : (0 : ℝ) < Module.finrank ℚ E := by exact_mod_cast Module.finrank_pos
  unfold pE at h
  have h2 : c.re / (Module.finrank ℚ E : ℝ) < (r : ℝ) * ((N : ℝ) - r) / 2 := by linarith
  have h3 := (div_lt_iff₀ hd).1 h2
  unfold An.rho
  calc c.re < (r : ℝ) * ((N : ℝ) - r) / 2 * (Module.finrank ℚ E : ℝ) := h3
    _ = _ := by ring

end Grow

open Grow in
theorem growPHolds : GrowPHolds := by
  intro E _ _ _ N χ hχ hcen hnp
  refine ⟨ContAut.continuous_of_isOpen_stab E N χ hχ.level, leftInv hχ hcen, fun ε hε => ?_⟩
  exact bnd_of hχ hcen _ fun r hr0 hrN c hc => by
    have := re_le_rho (hnp r hr0 hrN c hc)
    linarith

open Grow in
theorem growQHolds : GrowQHolds := by
  intro E _ _ _ N u hu hsq
  have hcen := hsq.1
  have hk : ∀ r, ∃ κ : ℝ, 0 < r → r < N → κ < An.rho E N r ∧ ∃ p : ℂ[X], p.Monic ∧ An.Kill r u.1 p ∧
      ∀ z, p.IsRoot z → ‖z‖ < Real.exp κ := by
    intro r
    by_cases hr : 0 < r ∧ r < N
    swap
    · exact ⟨0, fun h1 h2 => (hr ⟨h1, h2⟩).elim⟩
    obtain ⟨hr0, hrN⟩ := hr
    obtain ⟨p, hp, hpk, hroots⟩ := exists_kill hu hcen hr0 hrN
    have hroot' : ∀ z ∈ p.roots.toFinset, ‖z‖ < Real.exp (An.rho E N r) := by
      intro z hz
      rw [Multiset.mem_toFinset, mem_roots hp.ne_zero] at hz
      obtain ⟨c, hc, rfl⟩ := hroots z hz
      rw [Complex.norm_exp]
      exact Real.exp_lt_exp.2 (re_lt_rho (expNeg_holds E N u hu hsq r hr0 hrN c hc))
    obtain ⟨κ, hκ, hκz⟩ := JSqIntGlue.exists_lt_of_finset _ _ hroot'
    refine ⟨κ, fun _ _ => ⟨hκ, p, hp, hpk, fun z hz => hκz z ?_⟩⟩
    rw [Multiset.mem_toFinset, mem_roots hp.ne_zero]
    exact hz
  choose κ hκ using hk
  exact ⟨ContAut.continuous_of_isOpen_stab E N u hu.level, leftInv hu hcen, κ, fun r h1 h2 => (hκ r h1 h2).1,
    bnd_of' hu hcen κ fun r h1 h2 => (hκ r h1 h2).2⟩

theorem intBnd : IntBnd := by
  intro E _ _ _ N H hc h0 hl m hm hB
  obtain ⟨_, hS, hL, _⟩ := dict_holds E N
  set φ : GA E N → ℂ := fun g => ((Real.sqrt (H g) : ℝ) : ℂ) with hφ
  have hφc : Continuous φ := Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp hc)
  have hφB : An.Bnd φ (fun r => m r / 2) := by
    intro ω hω hωB t₀ Q hQ
    obtain ⟨C, hC⟩ := hB ω hω hωB t₀ Q hQ
    refine ⟨Real.sqrt (max C 0), fun b hb x hx q hq => ?_⟩
    have h1 := hC b hb x hx q hq
    rw [Complex.norm_real, Real.norm_of_nonneg (h0 _)] at h1
    set S := ∑ r ∈ Finset.range N, m r * An.sr x r with hSdef
    have e2 : ∑ r ∈ Finset.range N, m r / 2 * An.sr x r = S / 2 := by
      rw [hSdef, Finset.sum_div]
      exact Finset.sum_congr rfl fun r _ => by ring
    have e : Real.exp (∑ r ∈ Finset.range N, m r / 2 * An.sr x r) = Real.sqrt (Real.exp S) := by
      rw [e2]
      conv_rhs => rw [show S = S / 2 + S / 2 by ring]
      rw [Real.exp_add, Real.sqrt_mul_self (Real.exp_pos _).le]
    have h2 : H (b * An.tor E x * q) ≤ max C 0 * Real.exp S :=
      h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
    calc ‖φ (b * An.tor E x * q)‖ = Real.sqrt (H (b * An.tor E x * q)) := by
          rw [hφ, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
      _ ≤ Real.sqrt (max C 0 * Real.exp S) := Real.sqrt_le_sqrt h2
      _ = Real.sqrt (max C 0) * Real.sqrt (Real.exp S) := Real.sqrt_mul (le_max_right _ _) _
      _ = _ := by rw [e]
  have hκ : ∀ r, 0 < r → r < N → m r / 2 < An.rho E N r := fun r h1 h2 => by
    have := hm r h1 h2
    linarith
  have hslab := GlobalTheory.CompanionTheory.SlabGlue.slabGlue boxvol_holds E N Measure.haar φ (fun r => m r / 2) hφc hφB hκ
  have hfd := isFundamentalDomain_stdDom (latticeGL E N) (Measure.haar : Measure (GA E N))
  obtain ⟨ω, hω, hωB, t, ht, hsieg⟩ := GroundTheory.Automorphic.Reduction.exists_siegelSet (K := E) N
  have : MeasurableConstSMul (latticeGL E N) (GA E N) := ⟨fun γ => measurable_const_mul (γ : GA E N)⟩
  have : SMulInvariantMeasure (latticeGL E N) (GA E N) (Measure.haar : Measure (GA E N)) :=
    ⟨fun γ s _ => measure_preimage_mul _ γ.1 s⟩
  have hle := JSqIntGlue.setLIntegral_le_of_cover hfd (S := An.slab ω (max 0 (-Real.log t)))
    (fun g => by
      obtain ⟨γ, hγ, h⟩ := JSqIntGlue.exists_mem_slab hS hL ht hsieg g
      exact ⟨⟨γ, hγ⟩, h⟩) (fun g => ENNReal.ofReal (H g)) (fun γ g => by
      show ENNReal.ofReal (H (γ.1 * g)) = ENNReal.ofReal (H g)
      rw [hl γ.1 γ.2 g])
  have e : ∀ g, ‖φ g‖ₑ ^ 2 = ENNReal.ofReal (H g) := fun g => by
    show ‖((Real.sqrt (H g) : ℝ) : ℂ)‖ₑ ^ 2 = _
    rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
      ← ENNReal.ofReal_pow (Real.sqrt_nonneg _),
      Real.sq_sqrt (h0 g)]
  simp only [e] at hslab
  exact hle.trans_lt (hslab ω hω hωB _)

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.Leaf2Aux

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.IntegrableDescendSupP
noncomputable section

open NumberField MeasureTheory ComplexConjugate Filter Topology
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.CuspRep.CuspidalL2GL PositivityTheory.Rg.Rs

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.Leaf2Aux

namespace Pair

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {N : ℕ}

def rmulEquiv (x : GA E N) : Quot (latticeGL E N) ≃ᵐ Quot (latticeGL E N) where
  toFun := rmul (latticeGL E N) x
  invFun := rmul (latticeGL E N) x⁻¹
  left_inv q := by rw [← rmul_mul, mul_inv_cancel, rmul_one]
  right_inv q := by rw [← rmul_mul, inv_mul_cancel, rmul_one]
  measurable_toFun := measurable_rmul x
  measurable_invFun := measurable_rmul x⁻¹

theorem descend_rmul {f : GA E N → ℂ} (hf : LeftInv (latticeGL E N) f) (x : GA E N) (q : Quot (latticeGL E N)) :
    descend (latticeGL E N) f (rmul (latticeGL E N) x q) = f (q.out * x) := by
  have hq : rmul (latticeGL E N) x q = mk (latticeGL E N) (q.out * x) := by
    conv_lhs => rw [← Quotient.out_eq q]
    rfl
  rw [hq, hf.descend_mk]

theorem exists_eps (a : ℕ → ℝ) (N : ℕ) (h : ∀ r, 0 < r → r < N → 0 < a r) :
    ∃ ε > 0, ∀ r, 0 < r → r < N → ε < a r := by
  induction N with
  | zero => exact ⟨1, one_pos, fun r _ h => absurd h (Nat.not_lt_zero r)⟩
  | succ n ih =>
    obtain ⟨ε, hε, hε'⟩ := ih fun r h1 h2 => h r h1 (Nat.lt_succ_of_lt h2)
    by_cases hn : 0 < n
    · refine ⟨min ε (a n / 2), lt_min hε (half_pos (h n hn (Nat.lt_succ_self n))), fun r h1 h2 => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 h2 with h3 | rfl
      · exact (min_le_left _ _).trans_lt (hε' r h1 h3)
      · exact (min_le_right _ _).trans_lt (half_lt_self (h r h1 (Nat.lt_succ_self r)))
    · refine ⟨ε, hε, fun r h1 h2 => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 h2 with h3 | rfl
      · exact hε' r h1 h3
      · exact absurd h1 hn

def supP (K : Set (GA E N)) (f g : GA E N → ℂ) (y : GA E N) : ℝ :=
  sSup ((fun k => ‖f (y * k)‖ * ‖g (y * k)‖) '' K)

omit [_root_.NumberField.IsTotallyComplex E] in
theorem continuous_supP {K : Set (GA E N)} (hK : IsCompact K) {f g : GA E N → ℂ} (hf : Continuous f)
    (hg : Continuous g) : Continuous (supP K f g) :=
  hK.continuous_sSup (f := fun y k => ‖f (y * k)‖ * ‖g (y * k)‖)
    ((hf.comp continuous_mul).norm.mul (hg.comp continuous_mul).norm)

omit [_root_.NumberField.IsTotallyComplex E] in
theorem le_supP {K : Set (GA E N)} (hK : IsCompact K) {f g : GA E N → ℂ} (hf : Continuous f) (hg : Continuous g)
    (y : GA E N) {k : GA E N} (hk : k ∈ K) : ‖f (y * k)‖ * ‖g (y * k)‖ ≤ supP K f g y :=
  le_csSup (hK.image ((hf.comp (continuous_const.mul continuous_id)).norm.mul
    (hg.comp (continuous_const.mul continuous_id)).norm)).bddAbove ⟨k, hk, rfl⟩

omit [_root_.NumberField.IsTotallyComplex E] in
theorem supP_nonneg (K : Set (GA E N)) (f g : GA E N → ℂ) (y : GA E N) : 0 ≤ supP K f g y :=
  Real.sSup_nonneg (by rintro _ ⟨k, -, rfl⟩; positivity)

theorem supP_left {K : Set (GA E N)} {f g : GA E N → ℂ} (hf : LeftInv (latticeGL E N) f)
    (hg : LeftInv (latticeGL E N) g) : ∀ γ ∈ latticeGL E N, ∀ y, supP K f g (γ * y) = supP K f g y := by
  intro γ hγ y
  unfold supP
  simp only [mul_assoc, hf γ hγ, hg γ hγ]

omit [_root_.NumberField.IsTotallyComplex E] in
theorem bnd_supP {K : Set (GA E N)} (hK : IsCompact K) (hK0 : K.Nonempty) {f g : GA E N → ℂ}
    {m₁ m₂ : ℕ → ℝ} (hf : An.Bnd f m₁) (hg : An.Bnd g m₂) :
    An.Bnd (fun y => (supP K f g y : ℂ)) (m₁ + m₂) := by
  intro ω hω hωB t₀ Q hQ
  have hQ' : IsCompact ((fun p : GA E N × GA E N => p.1 * p.2) '' (Q ×ˢ K)) :=
    (hQ.prod hK).image continuous_mul
  obtain ⟨C₁, hC₁⟩ := hf ω hω hωB t₀ _ hQ'
  obtain ⟨C₂, hC₂⟩ := hg ω hω hωB t₀ _ hQ'
  refine ⟨C₁ * C₂, fun b hb x hx q hq => ?_⟩
  rw [Complex.norm_real, Real.norm_of_nonneg (supP_nonneg _ _ _ _)]
  refine csSup_le (hK0.image _) ?_
  rintro _ ⟨k, hk, rfl⟩
  have hqk : q * k ∈ (fun p : GA E N × GA E N => p.1 * p.2) '' (Q ×ˢ K) := ⟨(q, k), ⟨hq, hk⟩, rfl⟩
  have h1 := hC₁ b hb x hx _ hqk
  have h2 := hC₂ b hb x hx _ hqk
  have e : b * An.tor E x * q * k = b * An.tor E x * (q * k) := mul_assoc _ _ _
  simp only [e]
  have h3 := mul_le_mul h1 h2 (norm_nonneg _) ((norm_nonneg _).trans h1)
  refine h3.trans (le_of_eq ?_)
  have e2 : ∑ r ∈ Finset.range N, (m₁ + m₂) r * An.sr x r =
      ∑ r ∈ Finset.range N, m₁ r * An.sr x r + ∑ r ∈ Finset.range N, m₂ r * An.sr x r := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Pi.add_apply, add_mul]
  rw [e2, Real.exp_add]
  ring

theorem lintegral_supP_lt_top (hI : IntBnd) {K : Set (GA E N)} (hK : IsCompact K) (hK0 : K.Nonempty)
    {f g : GA E N → ℂ} (hf : GrowP f) (hg : GrowQ g) :
    ∫⁻ y in stdDom (latticeGL E N), ENNReal.ofReal (supP K f g y) ∂(Measure.haar : Measure (GA E N)) < ⊤ := by
  obtain ⟨hfc, hfl, hfb⟩ := hf
  obtain ⟨hgc, hgl, κ, hκ, hgb⟩ := hg
  obtain ⟨ε, hε, hε'⟩ := exists_eps (fun r => An.rho E N r - κ r) N (fun r h1 h2 => sub_pos.2 (hκ r h1 h2))
  refine hI E N _ (continuous_supP hK hfc hgc) (supP_nonneg K f g) (supP_left hfl hgl) _ ?_
    (bnd_supP hK hK0 (hfb ε hε) hgb)
  intro r h1 h2
  have := hε' r h1 h2
  simp only [Pi.add_apply]
  linarith

theorem integrable_pet (hI : IntBnd) {f g : GA E N → ℂ} (hf : GrowP f) (hg : GrowQ g) :
    Integrable (fun q => descend (latticeGL E N) f q * conj (descend (latticeGL E N) g q))
      (quotMeasure (latticeGL E N) (Measure.haar : Measure (GA E N))) := by
  have hfl : LeftInv (latticeGL E N) f := hf.2.1
  have hgl : LeftInv (latticeGL E N) g := hg.2.1
  have hl : LeftInv (latticeGL E N) (fun y => f y * conj (g y)) := fun γ hγ y => by
    simp only [hfl γ hγ, hgl γ hγ]
  have e : (fun q => descend (latticeGL E N) f q * conj (descend (latticeGL E N) g q)) =
      descend (latticeGL E N) (fun y => f y * conj (g y)) := rfl
  rw [e]
  refine ⟨?_, ?_⟩
  · rw [aestronglyMeasurable_quotMeasure_iff_lift, hl.lift_descend]
    exact (hf.1.mul (Complex.continuous_conj.comp hg.1)).aestronglyMeasurable
  · rw [hasFiniteIntegral_iff_enorm, lintegral_quotMeasure (isFundamentalDomain_stdDom _ _)]
    refine lt_of_le_of_lt (lintegral_mono fun y => ?_)
      (lintegral_supP_lt_top hI isCompact_singleton (Set.singleton_nonempty 1) hf hg)
    rw [hl.descend_mk, ← ofReal_norm]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [norm_mul, Complex.norm_conj]
    simpa using le_supP isCompact_singleton hf.1 hg.1 y (Set.mem_singleton 1)

def cX (X : Lie E N) (t : ℝ) : GA E N := infGL E N (GlobalTheory.ExpDeriv.expGL X t)

theorem continuous_cX (X : Lie E N) : Continuous (cX X) := by
  have hv : Continuous fun t : ℝ => NormedSpace.exp (t • Matrix.of X) := by
    open scoped Matrix.Norms.Operator in
    exact NormedSpace.exp_continuous.comp (continuous_id.smul continuous_const)
  have hinv : ∀ t, (GlobalTheory.ExpDeriv.expGL X t)⁻¹ = GlobalTheory.ExpDeriv.expGL X (-t) := fun t =>
    (eq_inv_of_mul_eq_one_right (by rw [← GlobalTheory.ExpDeriv.expGL_add, add_neg_cancel, GlobalTheory.ExpDeriv.expGL_zero])).symm
  have he : Continuous (GlobalTheory.ExpDeriv.expGL X) := Units.continuous_iff.2 ⟨hv, by
    simp only [hinv, GlobalTheory.ExpDeriv.expGL_val]
    exact hv.comp continuous_neg⟩
  exact GlobalTheory.CuspQuot.continuous_infGL.comp he

theorem cX_zero (X : Lie E N) : cX X 0 = 1 := by
  simp only [cX, GlobalTheory.ExpDeriv.expGL_zero, map_one]

theorem descend_eq_sec {X : Type*} {φ : GA E N → X} (hl : LeftInv (latticeGL E N) φ) :
    descend (latticeGL E N) φ = φ ∘ sec (latticeGL E N) := by
  funext q
  conv_lhs => rw [← mk_sec q]
  exact hl.descend_mk _

theorem aesm_descend {X : Type*} [NormedAddCommGroup X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X] {φ : GA E N → X} (hc : Continuous φ) (hl : LeftInv (latticeGL E N) φ) :
    AEStronglyMeasurable (descend (latticeGL E N) φ)
      (quotMeasure (latticeGL E N) (Measure.haar : Measure (GA E N))) := by
  rw [descend_eq_sec hl]
  exact (hc.measurable.comp measurableEmbedding_sec.measurable).aestronglyMeasurable

theorem integrable_descend_supP (hI : IntBnd) {K : Set (GA E N)} (hK : IsCompact K) (hK0 : K.Nonempty)
    {f g : GA E N → ℂ} (hf : GrowP f) (hg : GrowQ g) :
    Integrable (descend (latticeGL E N) (supP K f g))
      (quotMeasure (latticeGL E N) (Measure.haar : Measure (GA E N))) := by
  have hl : LeftInv (latticeGL E N) (supP K f g) := supP_left hf.2.1 hg.2.1
  refine ⟨?_, ?_⟩
  · exact aesm_descend (continuous_supP hK hf.1 hg.1) hl
  rw [hasFiniteIntegral_iff_enorm, lintegral_quotMeasure (isFundamentalDomain_stdDom _ _)]
  refine lt_of_le_of_lt (le_of_eq (lintegral_congr fun y => ?_)) (lintegral_supP_lt_top hI hK hK0 hf hg)
  rw [hl.descend_mk, ← ofReal_norm, Real.norm_of_nonneg (supP_nonneg _ _ _ _)]

end Pair

open Pair in
theorem pairRt : PairRt := by
  intro E _ _ _ N x f g hf hg
  have : (Measure.haar : Measure (GA E N)).IsMulRightInvariant := GlobalTheory.CovolGL.isMulRightInvariant E N _
  have hmp : MeasurePreserving (rmulEquiv x) (quotMeasure (latticeGL E N) (Measure.haar : Measure (GA E N)))
      (quotMeasure (latticeGL E N) (Measure.haar : Measure (GA E N))) := measurePreserving_rmul x
  have hg' : LeftInv (latticeGL E N) fun y => g (y * x⁻¹) := LeftInv.mul_right (Γ := latticeGL E N) hg x⁻¹
  unfold pr pet
  refine (integral_congr_ae (Eventually.of_forall fun q => ?_)).trans (hmp.integral_comp'
    (fun q => descend (latticeGL E N) f q * conj (descend (latticeGL E N) (fun y => g (y * x⁻¹)) q)))
  change f (q.out * x) * conj (g q.out) = descend (latticeGL E N) f (rmul (latticeGL E N) x q) *
    conj (descend (latticeGL E N) (fun y => g (y * x⁻¹)) (rmul (latticeGL E N) x q))
  rw [descend_rmul hf, descend_rmul hg', mul_inv_cancel_right]

open Pair in
theorem pairLin_of (hI : IntBnd) : PairLin := by
  intro E _ _ _ N
  refine ⟨fun f₁ f₂ g c h₁ h₂ hg => ⟨?_, ?_⟩, fun f g₁ g₂ c hf h₁ h₂ => ⟨?_, ?_⟩⟩
  · unfold pr pet
    rw [← integral_add (integrable_pet hI h₁ hg) (integrable_pet hI h₂ hg)]
    refine integral_congr_ae (Eventually.of_forall fun q => ?_)
    simp only [descend, Pi.add_apply, add_mul]
  · unfold pr pet
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun q => ?_)
    simp only [descend, Pi.smul_apply, smul_eq_mul, mul_assoc]
  · unfold pr pet
    rw [← integral_add (integrable_pet hI hf h₁) (integrable_pet hI hf h₂)]
    refine integral_congr_ae (Eventually.of_forall fun q => ?_)
    simp only [descend, Pi.add_apply, map_add (f := _), mul_add]
  · unfold pr pet
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun q => ?_)
    simp only [descend, Pi.smul_apply, smul_eq_mul, map_mul]
    ring

open Pair in
theorem pairLie_of (hI : IntBnd) : PairLie := by
  intro E _ _ _ N X χ u hχ hXχ hu hXu
  have hc : Continuous (cX (E := E) (N := N) X) := continuous_cX X
  have hc0 : cX (E := E) (N := N) X 0 = 1 := cX_zero X
  set c := cX (E := E) (N := N) X with hcdef
  set K : Set (GA E N) := c '' Set.Icc (-1) 1 with hKdef
  have hK : IsCompact K := isCompact_Icc.image hc
  have hK0 : K.Nonempty := ⟨c 0, 0, ⟨by norm_num, by norm_num⟩, rfl⟩
  set Γ := latticeGL E N with hΓ
  set μq := quotMeasure Γ (Measure.haar : Measure (GA E N)) with hμq
  set Xχ := act (.lie X) χ with hXχdef
  set Xu := act (.lie X) u with hXudef
  let F : ℝ → Quot Γ → ℂ := fun t q => χ.1 (q.out * c t) * conj (u.1 (q.out * c t))
  let F' : ℝ → Quot Γ → ℂ := fun t q => Xχ.1 (q.out * c t) * conj (u.1 (q.out * c t)) +
    χ.1 (q.out * c t) * conj (Xu.1 (q.out * c t))
  let bound : Quot Γ → ℝ := fun q => supP K Xχ.1 u.1 q.out + supP K χ.1 Xu.1 q.out
  have hJ : ∀ t, ∫ q, F t q ∂μq = pr χ.1 u.1 := by
    intro t
    have h := pairRt E N (c t) χ.1 (fun y => u.1 (y * c t)) hχ.2.1
      (LeftInv.mul_right (Γ := latticeGL E N) hu.2.1 _)
    simp only [inv_mul_cancel_right] at h
    exact h
  have hF_meas : ∀ᶠ t in 𝓝 (0 : ℝ), AEStronglyMeasurable (F t) μq := Eventually.of_forall fun t =>
    aesm_descend (φ := fun y => χ.1 (y * c t) * conj (u.1 (y * c t)))
      ((hχ.1.comp (continuous_id.mul continuous_const)).mul
        (Complex.continuous_conj.comp (hu.1.comp (continuous_id.mul continuous_const))))
      (fun γ hγ y => by simp only [mul_assoc, hχ.2.1 γ hγ, hu.2.1 γ hγ])
  have e0 : F 0 = fun q => descend Γ χ.1 q * conj (descend Γ u.1 q) := by
    funext q; simp only [F, hc0, mul_one, descend]
  have hF_int : Integrable (F 0) μq := by rw [e0]; exact integrable_pet hI hχ hu
  have e0' : F' 0 = fun q => (descend Γ Xχ.1 q * conj (descend Γ u.1 q) +
      descend Γ χ.1 q * conj (descend Γ Xu.1 q)) := by
    funext q; simp only [F', hc0, mul_one, descend]
  have hF'_meas : AEStronglyMeasurable (F' 0) μq := by
    rw [e0']
    exact ((integrable_pet hI hXχ hu).add (integrable_pet hI hχ hXu)).aestronglyMeasurable
  have h_bound : ∀ᵐ q ∂μq, ∀ t ∈ Set.Ioo (-1 : ℝ) 1, ‖F' t q‖ ≤ bound q := by
    refine Eventually.of_forall fun q t ht => ?_
    have hk : c t ∈ K := ⟨t, ⟨ht.1.le, ht.2.le⟩, rfl⟩
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_mul, Complex.norm_conj]
      exact le_supP hK hXχ.1 hu.1 q.out hk
    · rw [norm_mul, Complex.norm_conj]
      exact le_supP hK hχ.1 hXu.1 q.out hk
  have bound_int : Integrable bound μq :=
    (integrable_descend_supP hI hK hK0 hXχ hu).add (integrable_descend_supP hI hK hK0 hχ hXu)
  have h_diff : ∀ᵐ q ∂μq, ∀ t ∈ Set.Ioo (-1 : ℝ) 1, HasDerivAt (F · q) (F' t q) t := by
    refine Eventually.of_forall fun q t _ => ?_
    have h1 := GlobalTheory.ExpDeriv.hasDerivAt_along X χ q.out t
    have h2 := (GlobalTheory.ExpDeriv.hasDerivAt_along X u q.out t).star
    exact h1.mul h2
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μq) (F := F) (x₀ := 0)
    (Ioo_mem_nhds (by norm_num : (-1 : ℝ) < 0) (by norm_num : (0 : ℝ) < 1)) hF_meas hF_int hF'_meas h_bound
    bound_int h_diff
  have hconst : (fun t => ∫ q, F t q ∂μq) = fun _ => pr χ.1 u.1 := funext hJ
  have hd := hmain.2
  rw [hconst] at hd
  have hz : ∫ q, F' 0 q ∂μq = 0 := hd.unique (hasDerivAt_const 0 _)
  rw [e0', integral_add (integrable_pet hI hXχ hu) (integrable_pet hI hχ hXu)] at hz
  exact eq_neg_of_add_eq_zero_left hz

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.Leaf2Aux

end
end

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz

open Leaf2Aux in
theorem leaf_holds2 : Leaf :=
  leaf_of (Leaf2Aux.core_of (pairLin_of intBnd) pairRt (pairLie_of intBnd) growQHolds) growPHolds

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz
