module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumATools

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumACR
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumAGP
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocalCountOfGlue
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumAFG
noncomputable section

open ValuativeRel

namespace Formalism.L2.SG.LsDatumA

open Formalism.MainNotions.S.Loc

section FG

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

private theorem isNoetherianRing_locE_O' (L : LocE F E) [IsNonarchimedeanLocalField F] [CharZero F] :
    IsNoetherianRing L.O := by
  classical
  haveI : IsReduced E := L.reduced
  haveI : Module.Free F E := L.free
  haveI : Module.Finite F E := Module.finite_of_finrank_eq_succ L.rank
  haveI : Nontrivial E := Module.nontrivial_of_finrank_eq_succ L.rank
  have hA : ∀ a : 𝒪[F], algebraMap 𝒪[F] E a = algebraMap F E (a : F) := fun a =>
    IsScalarTower.algebraMap_apply 𝒪[F] F E a
  have hcjA : ∀ (a : F) (w : E), L.cj (algebraMap F E a * w) = algebraMap F E a * L.cj w := by
    intro a w
    rw [map_mul, L.cj.commutes]
  have hcjO : ∀ x ∈ L.O, L.cj x ∈ L.O := by
    intro x hx
    rw [L.O_def] at hx ⊢
    exact hx.map ((L.cj : E →ₐ[F] E).restrictScalars 𝒪[F])
  have htr : ∀ z ∈ L.O, ∃ a : 𝒪[F], algebraMap 𝒪[F] E a = z + L.cj z := by
    intro z hz
    have hmem : z + L.cj z ∈ L.O := L.O.add_mem hz (hcjO z hz)
    obtain ⟨a, ha⟩ := (L.cj_fix (z + L.cj z)).1 (by rw [map_add (f := _), L.cj_cj, add_comm])
    have hint : IsIntegral 𝒪[F] (algebraMap F E a) := ha ▸ (L.O_def _).1 hmem
    have hint' : IsIntegral 𝒪[F] a :=
      (isIntegral_algHom_iff (IsScalarTower.toAlgHom 𝒪[F] F E) (algebraMap F E).injective).1 hint
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint'
    exact ⟨y, by rw [hA, ← ha, ← hy]; rfl⟩
  have hnd : ∀ x : E, (∀ y : E, x * y + L.cj (x * y) = 0) → x = 0 := by
    intro x hx
    have h1 : L.cj x = -x := by
      have h := hx 1
      rw [mul_one] at h
      exact eq_neg_of_add_eq_zero_right h
    have h2 := hx x
    rw [map_mul, h1, neg_mul_neg, ← two_mul] at h2
    have hu : IsUnit (2 : E) := by
      have h3 : (2 : E) = algebraMap F E 2 := (map_ofNat (algebraMap F E) 2).symm
      rw [h3]
      exact (IsUnit.mk0 (2 : F) two_ne_zero).map _
    have hxx : x * x = 0 := hu.mul_right_eq_zero.1 h2
    exact IsReduced.eq_zero x ⟨2, by rw [pow_two, hxx]⟩
  let b := Module.finBasisOfFinrankEq F E L.rank
  have hsc : ∀ i, ∃ c : F, c ≠ 0 ∧ algebraMap F E c * b i ∈ L.O := by
    intro i
    haveI : Algebra.IsAlgebraic 𝒪[F] F := IsLocalization.isAlgebraic F (nonZeroDivisors 𝒪[F])
    haveI : Algebra.IsAlgebraic 𝒪[F] E := Algebra.IsAlgebraic.trans 𝒪[F] F E
    obtain ⟨c, hc, hci⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := 𝒪[F]) (b i)).exists_integral_multiple
    refine ⟨(c : F), by exact_mod_cast hc, (L.O_def _).2 ?_⟩
    rwa [Algebra.smul_def, hA] at hci
  choose c hc0 hcO using hsc
  let φ : 𝒪[F] →+* L.O :=
    (algebraMap 𝒪[F] E).codRestrict L.O (fun a => (L.O_def _).2 isIntegral_algebraMap)
  letI : Algebra 𝒪[F] L.O := φ.toAlgebra
  have hsm : ∀ (a : 𝒪[F]) (x : L.O), ((a • x : L.O) : E) = algebraMap F E (a : F) * x := by
    intro a x
    rw [Algebra.smul_def, Subring.coe_mul, ← hA]
    rfl
  let B : Fin 2 → E := fun i => algebraMap F E (c i) * b i
  let g : L.O →ₗ[𝒪[F]] (Fin 2 → E) :=
    { toFun := fun x i => (x : E) * B i + L.cj ((x : E) * B i)
      map_add' := by
        intro x y
        funext i
        simp only [Subring.coe_add, add_mul, map_add (f := _), Pi.add_apply]
        ring
      map_smul' := by
        intro a x
        funext i
        simp only [RingHom.id_apply, Pi.smul_apply]
        rw [hsm, Algebra.smul_def, hA]
        simp only [mul_assoc, hcjA, mul_add] }
  let N : Submodule 𝒪[F] (Fin 2 → E) :=
    Submodule.span 𝒪[F] (Set.range fun i : Fin 2 => Pi.single i (1 : E))
  haveI : IsNoetherian 𝒪[F] N := isNoetherian_span_of_finite 𝒪[F] (Set.finite_range _)
  have hgN : ∀ x, g x ∈ N := by
    intro x
    have hx : ∀ i, ∃ a : 𝒪[F], algebraMap 𝒪[F] E a = (x : E) * B i + L.cj ((x : E) * B i) :=
      fun i => htr _ (L.O.mul_mem x.2 (hcO i))
    choose a ha using hx
    rw [Submodule.mem_span_range_iff_exists_fun]
    refine ⟨a, ?_⟩
    show _ = fun j => (x : E) * B j + L.cj ((x : E) * B j)
    funext j
    simp [Finset.sum_apply, Pi.single_apply, Algebra.smul_def, ha]
  have hinj : Function.Injective (g.codRestrict N hgN) := by
    intro x y hxy
    have h0 : g x = g y := congrArg Subtype.val hxy
    have hd : ∀ i, ((x : E) - y) * B i + L.cj (((x : E) - y) * B i) = 0 := by
      intro i
      have h := congrFun h0 i
      simp only [g, LinearMap.coe_mk, AddHom.coe_mk] at h
      rw [sub_mul, map_sub]
      linear_combination h
    have hb : ∀ i, ((x : E) - y) * b i + L.cj (((x : E) - y) * b i) = 0 := by
      intro i
      have h := hd i
      simp only [B] at h
      rw [mul_left_comm, hcjA, ← mul_add] at h
      exact ((IsUnit.mk0 _ (hc0 i)).map (algebraMap F E)).mul_right_eq_zero.1 h
    have hall : ∀ w, ((x : E) - y) * w + L.cj (((x : E) - y) * w) = 0 := by
      intro w
      let τ : E →ₗ[F] E := LinearMap.mulLeft F ((x : E) - y) +
        (L.cj.toLinearMap).comp (LinearMap.mulLeft F ((x : E) - y))
      have hτ : τ = 0 := b.ext (fun i => by simpa [τ] using hb i)
      simpa [τ] using LinearMap.congr_fun hτ w
    exact Subtype.ext (sub_eq_zero.1 (hnd _ hall))
  haveI : IsNoetherian 𝒪[F] L.O := isNoetherian_of_injective (g.codRestrict N hgN) hinj
  exact isNoetherianRing_iff.2 (isNoetherian_of_tower 𝒪[F] this)

theorem thFG_at (M : Model F E) (r : ℕ) (hM : M.OK) : ThFG M r := by
  intro V _ _ H t ht
  haveI := hM.loc
  haveI := hM.char0
  haveI : IsNoetherianRing M.L.O := isNoetherianRing_locE_O' M.L
  have hfg : t.abelian₂.FG := ht.1.1.1
  haveI : IsNoetherian M.L.O t.abelian₂ := isNoetherian_of_fg_of_noetherian _ hfg
  have hle : ThL H t ≤ t.abelian₂ := inf_le_left
  haveI := isNoetherian_of_le hle
  exact Module.Finite.iff_fg.1 inferInstance

end FG

end Formalism.L2.SG.LsDatumA
end
end

noncomputable section

open ValuativeRel

namespace Formalism.L2.SG.LsDatumA

open Formalism.MainNotions.S.Loc

section Top2

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

theorem latSide_at' (M : Model F E) (r n : ℕ) (hM : M.OK) (hE : GlueEta M r) (hV : GlueConv M r)
    (hP : GenOfPrim M r n) (hR : ClaimR M r n) : LatSide M r n :=
  latSide_at M r n hM hE hV hP (gramMM_holds M r n) (thFG_at M r hM) (thSpan_at M r hM) hR

theorem localCount_of_glue (M : Model F E) (r n : ℕ) (hM : M.OK) (hE : GlueEta M r) (hV : GlueConv M r)
    (hP : GenOfPrim M r n) (hR : ClaimR M r n) (h0 : ModSide0 M r n M.split.isSome)
    (hU : ModSideU M r n M.split.isSome) : Formalism.MainNotions.ThinScalesBound.FamilyLocalModel M r n := by
  intro V _ _ H hn t₁ hg f₂ f₂' φ φ' hF hF' hI hs hs'
  have hT : LocalCountHypotheses H t₁ f₂ f₂' φ φ' := ⟨hg, hF, hF', hI, hs, hs'⟩
  have hL := latSide_at' M r n hM hE hV hP hR V H hn t₁ f₂ f₂' φ φ' hT
  dsimp only
  refine ⟨fun hz Z₁ Z₂ h₁ h₂ => ?_, fun hu Y₁ Y₂ be₁ be₂ al₁ al₂ hY hb => ?_⟩
  · rw [hL]
    exact h0 rfl V H hn t₁ f₂ f₂' φ φ' hT hz Z₁ Z₂ h₁ h₂
  · rw [hL]
    exact hU rfl V H hn t₁ f₂ f₂' φ φ' hT hu Y₁ Y₂ be₁ be₂ al₁ al₂ hY hb

end Top2

end Formalism.L2.SG.LsDatumA
end
end

noncomputable section

open ValuativeRel

namespace Formalism.L2.SG.LsDatumA

open Formalism.MainNotions.S.Loc

section GP

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

theorem prim_comp {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V)
    {Λ : Submodule M.L.O V} {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] {v : ι → V} (hv : H.Prim Λ v)
    (e : κ → ι) (he : Function.Injective e) : H.Prim Λ (v ∘ e) := by
  refine ⟨fun a => hv.1 (e a), hv.2.1.comp e he, fun x hx hxs => ?_⟩
  have hxv : x ∈ Submodule.span E (Set.range v) := Submodule.span_mono (Set.range_comp_subset_range e v) hxs
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun M.L.O).1 (hv.2.2 x hx hxv)
  obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hxs
  have ha' : ∑ i, ((a i : M.L.O) : E) • v i = x := ha
  let d' : ι → E := fun i => ∑ j, if e j = i then d j else 0
  have hd' : ∑ i, d' i • v i = ∑ j, d j • v (e j) := by
    simp only [d', Finset.sum_smul, ite_smul, zero_smul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.sum_ite_eq]
    simp
  have hcoef : ∀ i, ((a i : M.L.O) : E) = d' i := by
    have h0 : ∑ i, (((a i : M.L.O) : E) - d' i) • v i = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib]
      rw [hd', ha']
      simpa using hd.symm ▸ sub_self x
    intro i
    exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hv.2.1 _ h0 i)
  have hzero : ∀ i, i ∉ Set.range e → a i = 0 := by
    intro i hi
    apply Subtype.ext
    rw [hcoef i]
    apply Finset.sum_eq_zero
    intro j _
    rw [if_neg (fun h => hi ⟨j, h⟩)]
  rw [Submodule.mem_span_range_iff_exists_fun]
  refine ⟨fun j => a (e j), ?_⟩
  rw [← ha]
  exact (Fintype.sum_of_injective e he (fun j => a (e j) • (v ∘ e) j) (fun i => a i • v i)
    (fun i hi => by rw [hzero i hi, zero_smul]) (fun j => rfl))

theorem genOfPrim_holds (M : Model F E) (r n : ℕ) : GenOfPrim M r n := by
  intro _ V _ _ H hn t₁ f₂ f₂' φ φ' hyp hD₂ Λ₂ hsd hprim
  obtain ⟨hg₁, hF₂, hF₂', hI, -, -⟩ := hyp
  have hT1 := hg₁.1
  have hD₁ : IsUnit (H.Dl t₁.f t₁.f' (r + 1)) := hT1.2.2.2.1
  have hG₁ : IsUnit (H.Gdet t₁.f t₁.f' t₁.T t₁.T') := isUnit_Gdet H _ _ _ _ hT1.2.2.2.2.1
  have hG₂ : IsUnit (H.Gdet f₂ f₂' t₁.T t₁.T') := by
    have e := Gdet_rel H t₁.f t₁.f' f₂ f₂' t₁.T t₁.T' hI.2.2.2.2.2
    have hN₂ : IsUnit (H.normE (H.Dl f₂ f₂' (r + 1))) := hD₂.mul (hD₂.map M.L.cj)
    have h3 : IsUnit (H.Gdet f₂ f₂' t₁.T t₁.T' * H.normE (H.Dl t₁.f t₁.f' (r + 1))) := by
      rw [e]
      exact hN₂.mul hG₁
    exact isUnit_of_mul_isUnit_left h3
  have hnt : Nontrivial E := by
    by_contra hc
    rw [not_nontrivial_iff_subsingleton] at hc
    have h0 := Module.finrank_zero_of_subsingleton (R := F) (M := E)
    rw [M.L.rank] at h0
    exact absurd h0 (by norm_num)
  have hfam_inl : (H.MMfam (⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ : Term V M r)) ∘ Sum.inl = f₂ := by
    funext a
    unfold HermSp.MMfam
    rcases M.split with _ | g <;> rfl
  have hPf : H.Prim Λ₂ f₂ := by
    have := prim_comp H hprim Sum.inl Sum.inl_injective
    rwa [hfam_inl] at this
  have hPf' : H.Prim Λ₂ f₂' := by
    rcases hs : M.split with _ | g
    · have hfam_inr : (H.MMfam (⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ : Term V M r)) ∘ Sum.inr = f₂' := by
        funext a
        unfold HermSp.MMfam
        rw [hs]
        rfl
      have := prim_comp H hprim Sum.inr Sum.inr_injective
      rwa [hfam_inr] at this
    · set Q : E := algebraMap F E (g.q : F)
      set qi : E := algebraMap F E ((g.q : F)⁻¹)
      have hq0 : (g.q : F) ≠ 0 := fun h0 => g.q_irr.ne_zero (Subtype.ext h0)
      have hQqi : Q * qi = 1 := by
        simp only [Q, qi]
        rw [← map_mul, mul_inv_cancel₀ hq0, map_one]
      have hQO : Q ∈ M.L.O := Formalism.MainNotions.LocalModelPeriodLattices.algebraMap_mem_O M.L g.q
      have hMM : H.MMfam (⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ : Term V M r) = Sum.elim f₂ (fun a => qi • (f₂' a - f₂ a)) := by
        unfold HermSp.MMfam
        rw [hs]
      rw [hMM] at hprim
      obtain ⟨hmem, hli, hsat⟩ := hprim
      set y : Fin (r + 1) → V := fun a => qi • (f₂' a - f₂ a)
      have hf' : ∀ a, f₂' a = f₂ a + Q • y a := by
        intro a
        simp only [y]
        rw [smul_smul, hQqi, one_smul]
        abel
      refine ⟨fun a => ?_, ?_, fun x hx hxs => ?_⟩
      · rw [hf' a]
        refine Submodule.add_mem _ (hmem (Sum.inl a)) ?_
        have := Λ₂.smul_mem (⟨Q, hQO⟩ : M.L.O) (hmem (Sum.inr a))
        rwa [Subring.smul_def] at this
      · rw [Fintype.linearIndependent_iff]
        intro d hd a
        have h0 : ∑ i, (Sum.elim d (fun b => d b * Q) i) • Sum.elim f₂ y i = 0 := by
          rw [Fintype.sum_sum_type]
          simp only [Sum.elim_inl, Sum.elim_inr]
          rw [← hd, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [hf' b, smul_add, mul_smul]
        exact (Fintype.linearIndependent_iff.1 hli) _ h0 (Sum.inl a)
      · obtain ⟨d, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hxs
        have hx2 : ∑ a, d a • f₂' a ∈ Submodule.span E (Set.range (Sum.elim f₂ y)) := by
          refine Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ ?_
          rw [hf' a]
          exact Submodule.add_mem _ (Submodule.subset_span ⟨Sum.inl a, rfl⟩)
            (Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inr a, rfl⟩))
        obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun M.L.O).1 (hsat _ hx hx2)
        have hcoef := (Fintype.linearIndependent_iff.1 hli)
          (fun i => (c i : E) - Sum.elim d (fun b => d b * Q) i) (by
            simp only [sub_smul, Finset.sum_sub_distrib]
            have e1 : ∑ i, (c i : E) • Sum.elim f₂ y i = ∑ a, d a • f₂' a := by
              rw [← hc]
              exact Finset.sum_congr rfl fun i _ => (Subring.smul_def _ _).symm
            rw [e1, Fintype.sum_sum_type]
            simp only [Sum.elim_inl, Sum.elim_inr]
            rw [← Finset.sum_add_distrib, sub_eq_zero]
            refine Finset.sum_congr rfl fun b _ => ?_
            rw [hf' b, smul_add, mul_smul])
        have hdO : ∀ a, d a ∈ M.L.O := by
          intro a
          have := hcoef (Sum.inl a)
          simp only [Sum.elim_inl] at this
          rw [← sub_eq_zero.1 this]
          exact (c _).2
        refine Submodule.sum_mem _ fun a _ => ?_
        have := Submodule.smul_mem (Submodule.span M.L.O (Set.range f₂')) (⟨d a, hdO a⟩ : M.L.O)
          (Submodule.subset_span ⟨a, rfl⟩)
        rwa [Subring.smul_def] at this
  refine ⟨⟨hsd, ⟨hPf, hF₂.1, hF₂.2, hT1.2.1.2.2.2⟩, ⟨hPf', hF₂'.1, hF₂'.2, hT1.2.2.1.2.2.2⟩, hD₂, hG₂.ne_zero,
    fun g hs => ⟨(hT1.2.2.2.2.2 g hs).1, (hT1.2.2.2.2.2 g hs).2.1, fun b => ?_⟩⟩, hprim⟩
  have hq0 : (g.q : F) ≠ 0 := fun h0 => g.q_irr.ne_zero (Subtype.ext h0)
  have hMM : H.MMfam (⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ : Term V M r) =
      Sum.elim f₂ (fun a => algebraMap F E ((g.q : F)⁻¹) • (f₂' a - f₂ a)) := by
    unfold HermSp.MMfam
    rw [hs]
  have hy : algebraMap F E ((g.q : F)⁻¹) • (f₂' b - f₂ b) ∈ Λ₂ := by
    have := hprim.1 (Sum.inr b)
    rw [hMM] at this
    exact this
  have e : f₂' b - f₂ b = algebraMap F E (g.q : F) • (algebraMap F E ((g.q : F)⁻¹) • (f₂' b - f₂ b)) := by
    rw [smul_smul, ← map_mul, mul_inv_cancel₀ hq0, map_one, one_smul]
  show f₂' b - f₂ b ∈ H.smulLat (algebraMap F E (g.q : F)) Λ₂
  rw [e]
  exact Submodule.subset_span ⟨_, hy, rfl⟩

end GP

end Formalism.L2.SG.LsDatumA
end
end

noncomputable section

open ValuativeRel

namespace Formalism.L2.SG.LsDatumA

open Formalism.MainNotions.S.Loc

section CR

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {r : ℕ}

def GamG (t : Term V M r) (g : Fin (r + 1) → V) : Set (DDt H t × H.Wb g) :=
  {p | ∃ (u : ↥(MMsharp H t)) (hu : (u : V) ∈ H.perp (H.X g)), p = (ddMk H t u, H.mkW g ⟨u, hu⟩)}

theorem mkW_add {g : Fin (r + 1) → V} (a b : V) (ha : a ∈ H.perp (H.X g)) (hb : b ∈ H.perp (H.X g)) :
    H.mkW g ⟨a + b, Submodule.add_mem _ ha hb⟩ = H.mkW g ⟨a, ha⟩ + H.mkW g ⟨b, hb⟩ := by
  rw [← map_add (f := _)]
  rfl

theorem mkW_sub {g : Fin (r + 1) → V} (a b : V) (ha : a ∈ H.perp (H.X g)) (hb : b ∈ H.perp (H.X g)) :
    H.mkW g ⟨a - b, Submodule.sub_mem _ ha hb⟩ = H.mkW g ⟨a, ha⟩ - H.mkW g ⟨b, hb⟩ := by
  rw [← map_sub]
  rfl

theorem mkW_congr {g : Fin (r + 1) → V} {a b : V} (ha : a ∈ H.perp (H.X g)) (hb : b ∈ H.perp (H.X g))
    (h : a = b) : H.mkW g ⟨a, ha⟩ = H.mkW g ⟨b, hb⟩ := by
  subst h
  rfl

theorem spanMM_le_U (t : Term V M r) :
    Submodule.span E (Set.range (H.MMfam t)) ≤ Submodule.span E (Set.range (Sum.elim t.f t.f')) := by
  have hsup : Submodule.span E (Set.range (Sum.elim t.f t.f')) = H.Xp t.f ⊔ H.Xp t.f' := by
    rw [Set.Sum.elim_range, Submodule.span_union]
    rfl
  rw [hsup]
  exact Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact MMfam_mem_sup H t i)

theorem claimR_side (t₁ t₂ : Term V M r) (Λ₂ : Submodule M.L.O V)
    (ψ : ↥(H.W0 t₁.f t₁.f') ≃ₗ[E] ↥(H.W0 t₂.f t₂.f'))
    (hU₂ : IsCompl (Submodule.span E (Set.range (Sum.elim t₂.f t₂.f'))) (H.W0 t₂.f t₂.f'))
    (hU₁ : IsCompl (Submodule.span E (Set.range (Sum.elim t₁.f t₁.f'))) (H.W0 t₁.f t₁.f'))
    (hsd₁ : H.IsSelfDual t₁.abelian₂) (hsd₂ : H.IsSelfDual Λ₂)
    (hMM₁ : MMo H t₁ ≤ t₁.abelian₂) (hMM₂ : MMo H t₂ ≤ Λ₂)
    (hth : ∀ w : ↥(H.W0 t₁.f t₁.f'), (w : V) ∈ t₁.abelian₂ ↔ (ψ w : V) ∈ Λ₂)
    (θ : DDt H t₁ ≃ₗ[M.L.O] DDt H t₂)
    (hθ : ∀ m₁ m₂, θ (ddMk H t₁ m₁) = ddMk H t₂ m₂ ↔
      ∃ w : ↥(H.W0 t₁.f t₁.f'), (m₁ : V) + w ∈ t₁.abelian₂ ∧ (m₂ : V) + ψ w ∈ Λ₂)
    (hsurj₁ : ∀ m₁ : ↥(MMsharp H t₁), ∃ w : ↥(H.W0 t₁.f t₁.f'), (m₁ : V) + w ∈ t₁.abelian₂)
    (g₁ g₂ : Fin (r + 1) → V)
    (hY₂ : H.X g₂ ≤ Submodule.span E (Set.range (Sum.elim t₂.f t₂.f')))
    (hW₁ : H.W0 t₁.f t₁.f' ≤ H.perp (H.X g₁)) (hW₂ : H.W0 t₂.f t₂.f' ≤ H.perp (H.X g₂))
    (χ : H.Wb g₁ ≃ₗ[E] H.Wb g₂)
    (hC1 : ∀ w : ↥(H.W0 t₁.f t₁.f'), χ (H.mkW g₁ ⟨w, hW₁ w.2⟩) = H.mkW g₂ ⟨ψ w, hW₂ (ψ w).2⟩)
    (hC2 : ∀ u ∈ Submodule.span E (Set.range (Sum.elim t₁.f t₁.f')), ∀ hu : u ∈ H.perp (H.X g₁),
      ∃ u' ∈ Submodule.span E (Set.range (Sum.elim t₂.f t₂.f')), ∃ hu' : u' ∈ H.perp (H.X g₂),
        χ (H.mkW g₁ ⟨u, hu⟩) = H.mkW g₂ ⟨u', hu'⟩) :
    χ '' H.Lset t₁.abelian₂ g₁ = H.Lset Λ₂ g₂ ↔
      (fun p => (θ p.1, χ p.2)) '' GamG H t₁ g₁ = GamG H t₂ g₂ := by

  have hsep₂ : ∀ (a b : V) (ha : a ∈ Submodule.span E (Set.range (Sum.elim t₂.f t₂.f')))
      (hb : b ∈ H.W0 t₂.f t₂.f') (ha' : a ∈ H.perp (H.X g₂)),
      H.mkW g₂ ⟨a, ha'⟩ = H.mkW g₂ ⟨b, hW₂ hb⟩ → b = 0 := by
    intro a b ha hb ha' hab
    have h1 := sub_mem_X_of_mkW_eq H hab
    have h2 : b = a - (a - b) := by abel
    have h3 : b ∈ Submodule.span E (Set.range (Sum.elim t₂.f t₂.f')) := by
      rw [h2]; exact Submodule.sub_mem _ ha (hY₂ h1)
    exact (Submodule.disjoint_def.1 hU₂.disjoint) b h3 hb
  have hpart : ∀ (t : Term V M r) (Λ : Submodule M.L.O V), H.IsSelfDual Λ → MMo H t ≤ Λ →
      ∀ a b : V, a ∈ Submodule.span E (Set.range (Sum.elim t.f t.f')) → b ∈ H.W0 t.f t.f' → a + b ∈ Λ →
        a ∈ MMsharp H t := by
    intro t Λ hsd hMM a b ha hb hab
    refine ⟨span_frames_le_MM H t ha, fun μ hμ => ?_⟩
    have hμU : μ ∈ Submodule.span E (Set.range (H.MMfam t)) := Submodule.span_le_restrictScalars M.L.O E _ hμ
    have h1 : H.h (a + b) μ ∈ M.L.O := (hsd.2.2 _).1 hab μ (hMM hμ)
    rw [H.h_add_left, hermitian_W0_span_zero H t hb hμU, add_zero] at h1
    exact h1
  have hdec : ∀ (U W : Submodule E V), IsCompl U W → ∀ x : V, ∃ a ∈ U, ∃ b ∈ W, a + b = x := by
    intro U W hUW x
    have hx : x ∈ U ⊔ W := by rw [hUW.sup_eq_top]; exact Submodule.mem_top
    exact Submodule.mem_sup.1 hx
  have hperp_a : ∀ {g : Fin (r + 1) → V} (a b : V), b ∈ H.perp (H.X g) → a + b ∈ H.perp (H.X g) →
      a ∈ H.perp (H.X g) := by
    intro g a b hb hab
    have : a = (a + b) - b := by abel
    rw [this]
    exact Submodule.sub_mem _ hab hb

  have hθs : ∀ m₂ : ↥(MMsharp H t₂), ∃ m₁ : ↥(MMsharp H t₁), θ (ddMk H t₁ m₁) = ddMk H t₂ m₂ := by
    intro m₂
    obtain ⟨m₁, hm₁⟩ := Submodule.Quotient.mk_surjective _ (θ.symm (ddMk H t₂ m₂))
    refine ⟨m₁, ?_⟩
    rw [show ddMk H t₁ m₁ = θ.symm (ddMk H t₂ m₂) from hm₁, LinearEquiv.apply_symm_apply]
  constructor
  · intro hL
    apply Set.Subset.antisymm
    · rintro _ ⟨q, ⟨u₁, hu₁, rfl⟩, rfl⟩
      obtain ⟨n₁, hn₁⟩ := hsurj₁ u₁
      have hx₁p : (u₁ : V) + n₁ ∈ H.perp (H.X g₁) := Submodule.add_mem _ hu₁ (hW₁ n₁.2)
      have hmem : χ (H.mkW g₁ ⟨(u₁ : V) + n₁, hx₁p⟩) ∈ H.Lset Λ₂ g₂ := by
        rw [← hL]
        exact ⟨_, ⟨⟨_, hx₁p⟩, hn₁, rfl⟩, rfl⟩
      obtain ⟨x₂, hx₂Λ, hx₂e⟩ := hmem
      obtain ⟨a, ha, b, hb, hab⟩ := hdec _ _ hU₂ (x₂ : V)
      have hap : a ∈ H.perp (H.X g₂) := hperp_a a b (hW₂ hb) (by rw [hab]; exact x₂.2)
      have haMM : a ∈ MMsharp H t₂ := hpart t₂ Λ₂ hsd₂ hMM₂ a b ha hb (by rw [hab]; exact hx₂Λ)
      obtain ⟨u', hu'U, hu'p, hχu⟩ := hC2 u₁ (spanMM_le_U H t₁ u₁.2.1) hu₁
      have e1 : χ (H.mkW g₁ ⟨(u₁ : V) + n₁, hx₁p⟩) = H.mkW g₂ ⟨u', hu'p⟩ + H.mkW g₂ ⟨ψ n₁, hW₂ (ψ n₁).2⟩ := by
        rw [mkW_add H _ _ hu₁ (hW₁ n₁.2), map_add (f := _), hχu, hC1]
      have e2 : H.mkW g₂ x₂ = H.mkW g₂ ⟨a, hap⟩ + H.mkW g₂ ⟨b, hW₂ hb⟩ := by
        rw [← mkW_add H _ _ hap (hW₂ hb)]
        exact mkW_congr H _ _ hab.symm
      have e3 : H.mkW g₂ ⟨a - u', Submodule.sub_mem _ hap hu'p⟩ =
          H.mkW g₂ ⟨(ψ n₁ : V) - b, Submodule.sub_mem _ (hW₂ (ψ n₁).2) (hW₂ hb)⟩ := by
        rw [mkW_sub H a u' hap hu'p, mkW_sub H (ψ n₁ : V) b (hW₂ (ψ n₁).2) (hW₂ hb), sub_eq_sub_iff_add_eq_add,
          ← e2, hx₂e, e1, add_comm]
      have hb0 := hsep₂ (a - u') ((ψ n₁ : V) - b) (Submodule.sub_mem _ ha hu'U)
        (Submodule.sub_mem _ (ψ n₁).2 hb) (Submodule.sub_mem _ hap hu'p) e3
      have hbψ : b = (ψ n₁ : V) := (sub_eq_zero.1 hb0).symm
      have e4 : H.mkW g₂ ⟨a, hap⟩ = H.mkW g₂ ⟨u', hu'p⟩ := by
        have := e3
        rw [mkW_sub H a u' hap hu'p, mkW_sub H (ψ n₁ : V) b (hW₂ (ψ n₁).2) (hW₂ hb)] at this
        rw [mkW_congr H (hW₂ (ψ n₁).2) (hW₂ hb) hbψ.symm, sub_self, sub_eq_zero] at this
        exact this
      have hθu : θ (ddMk H t₁ u₁) = ddMk H t₂ ⟨a, haMM⟩ :=
        (hθ u₁ ⟨a, haMM⟩).2 ⟨n₁, hn₁, by rw [← hbψ, hab]; exact hx₂Λ⟩
      refine ⟨⟨a, haMM⟩, hap, ?_⟩
      simp only [Prod.mk.injEq]
      exact ⟨hθu, hχu.trans e4.symm⟩
    · rintro _ ⟨u₂, hu₂, rfl⟩
      obtain ⟨m₁, hm₁⟩ := hθs u₂
      obtain ⟨n₁, hn₁, hx₂Λ⟩ := (hθ m₁ u₂).1 hm₁
      have hx₂p : (u₂ : V) + ψ n₁ ∈ H.perp (H.X g₂) := Submodule.add_mem _ hu₂ (hW₂ (ψ n₁).2)
      have hmem : H.mkW g₂ ⟨(u₂ : V) + ψ n₁, hx₂p⟩ ∈ χ '' H.Lset t₁.abelian₂ g₁ := by
        rw [hL]
        exact ⟨⟨_, hx₂p⟩, hx₂Λ, rfl⟩
      obtain ⟨_, ⟨x₁, hx₁Λ, rfl⟩, hx₁e⟩ := hmem
      obtain ⟨a₁, ha₁, b₁, hb₁, hab₁⟩ := hdec _ _ hU₁ (x₁ : V)
      have ha₁p : a₁ ∈ H.perp (H.X g₁) := hperp_a a₁ b₁ (hW₁ hb₁) (by rw [hab₁]; exact x₁.2)
      have ha₁MM : a₁ ∈ MMsharp H t₁ := hpart t₁ t₁.abelian₂ hsd₁ hMM₁ a₁ b₁ ha₁ hb₁ (by rw [hab₁]; exact hx₁Λ)
      obtain ⟨u', hu'U, hu'p, hχu⟩ := hC2 a₁ ha₁ ha₁p
      have e1 : χ (H.mkW g₁ x₁) = H.mkW g₂ ⟨u', hu'p⟩ + H.mkW g₂ ⟨ψ ⟨b₁, hb₁⟩, hW₂ (ψ ⟨b₁, hb₁⟩).2⟩ := by
        rw [mkW_congr H x₁.2 (Submodule.add_mem _ ha₁p (hW₁ hb₁)) hab₁.symm, mkW_add H _ _ ha₁p (hW₁ hb₁),
          map_add, hχu]
        rw [← hC1 ⟨b₁, hb₁⟩]
      have e3 : H.mkW g₂ ⟨(u₂ : V) - u', Submodule.sub_mem _ hu₂ hu'p⟩ =
          H.mkW g₂ ⟨(ψ ⟨b₁, hb₁⟩ : V) - ψ n₁, Submodule.sub_mem _ (hW₂ (ψ ⟨b₁, hb₁⟩).2) (hW₂ (ψ n₁).2)⟩ := by
        rw [mkW_sub H (u₂ : V) u' hu₂ hu'p,
          mkW_sub H (ψ ⟨b₁, hb₁⟩ : V) (ψ n₁ : V) (hW₂ (ψ ⟨b₁, hb₁⟩).2) (hW₂ (ψ n₁).2),
          sub_eq_sub_iff_add_eq_add, ← mkW_add H _ _ hu₂ (hW₂ (ψ n₁).2), ← hx₁e, e1, add_comm]
      have hb0 := hsep₂ ((u₂ : V) - u') ((ψ ⟨b₁, hb₁⟩ : V) - ψ n₁)
        (Submodule.sub_mem _ (spanMM_le_U H t₂ u₂.2.1) hu'U)
        (Submodule.sub_mem _ (ψ ⟨b₁, hb₁⟩).2 (ψ n₁).2) (Submodule.sub_mem _ hu₂ hu'p) e3
      have hψeq : ψ ⟨b₁, hb₁⟩ = ψ n₁ := Subtype.ext (sub_eq_zero.1 hb0)
      have hbn : (⟨b₁, hb₁⟩ : ↥(H.W0 t₁.f t₁.f')) = n₁ := ψ.injective hψeq
      have e4 : H.mkW g₂ ⟨u₂, hu₂⟩ = H.mkW g₂ ⟨u', hu'p⟩ := by
        have := e3
        rw [mkW_sub H (u₂ : V) u' hu₂ hu'p,
          mkW_sub H (ψ ⟨b₁, hb₁⟩ : V) (ψ n₁ : V) (hW₂ (ψ ⟨b₁, hb₁⟩).2) (hW₂ (ψ n₁).2)] at this
        rw [mkW_congr H (hW₂ (ψ ⟨b₁, hb₁⟩).2) (hW₂ (ψ n₁).2) (congrArg Subtype.val hψeq), sub_self,
          sub_eq_zero] at this
        exact this
      have hθa : θ (ddMk H t₁ ⟨a₁, ha₁MM⟩) = ddMk H t₂ u₂ :=
        (hθ ⟨a₁, ha₁MM⟩ u₂).2 ⟨⟨b₁, hb₁⟩, by rw [hab₁]; exact hx₁Λ, by rw [hψeq]; exact hx₂Λ⟩
      refine ⟨(ddMk H t₁ ⟨a₁, ha₁MM⟩, H.mkW g₁ ⟨a₁, ha₁p⟩), ⟨⟨a₁, ha₁MM⟩, ha₁p, rfl⟩, ?_⟩
      simp only [Prod.mk.injEq]
      exact ⟨hθa, hχu.trans e4.symm⟩
  · intro hG
    apply Set.Subset.antisymm
    · rintro _ ⟨_, ⟨x₁, hx₁Λ, rfl⟩, rfl⟩
      obtain ⟨a₁, ha₁, b₁, hb₁, hab₁⟩ := hdec _ _ hU₁ (x₁ : V)
      have ha₁p : a₁ ∈ H.perp (H.X g₁) := hperp_a a₁ b₁ (hW₁ hb₁) (by rw [hab₁]; exact x₁.2)
      have ha₁MM : a₁ ∈ MMsharp H t₁ := hpart t₁ t₁.abelian₂ hsd₁ hMM₁ a₁ b₁ ha₁ hb₁ (by rw [hab₁]; exact hx₁Λ)
      have hin : (θ (ddMk H t₁ ⟨a₁, ha₁MM⟩), χ (H.mkW g₁ ⟨a₁, ha₁p⟩)) ∈ GamG H t₂ g₂ := by
        rw [← hG]
        exact ⟨_, ⟨⟨a₁, ha₁MM⟩, ha₁p, rfl⟩, rfl⟩
      obtain ⟨u₂, hu₂, hue⟩ := hin
      simp only [Prod.mk.injEq] at hue
      obtain ⟨n₁, hn₁, hx₂'⟩ := (hθ ⟨a₁, ha₁MM⟩ u₂).1 hue.1
      have hd : (⟨b₁, hb₁⟩ : ↥(H.W0 t₁.f t₁.f')) - n₁ ∈ {w : ↥(H.W0 t₁.f t₁.f') | (w : V) ∈ t₁.abelian₂} := by
        show b₁ - (n₁ : V) ∈ t₁.abelian₂
        have := t₁.abelian₂.sub_mem hx₁Λ hn₁
        rwa [← hab₁, show a₁ + b₁ - (a₁ + (n₁ : V)) = b₁ - n₁ by abel] at this
      have hdψ := (hth _).1 hd
      rw [map_sub, Submodule.coe_sub] at hdψ
      have hx₂Λ : (u₂ : V) + ψ ⟨b₁, hb₁⟩ ∈ Λ₂ := by
        have := Λ₂.add_mem hx₂' hdψ
        rwa [show (u₂ : V) + ψ n₁ + ((ψ ⟨b₁, hb₁⟩ : V) - ψ n₁) = u₂ + ψ ⟨b₁, hb₁⟩ by abel] at this
      have hx₂p : (u₂ : V) + ψ ⟨b₁, hb₁⟩ ∈ H.perp (H.X g₂) := Submodule.add_mem _ hu₂ (hW₂ (ψ ⟨b₁, hb₁⟩).2)
      refine ⟨⟨_, hx₂p⟩, hx₂Λ, ?_⟩
      rw [mkW_add H _ _ hu₂ (hW₂ (ψ ⟨b₁, hb₁⟩).2), ← hC1 ⟨b₁, hb₁⟩, ← hue.2, ← map_add (f := _),
        ← mkW_add H _ _ ha₁p (hW₁ hb₁)]
      exact congrArg χ (mkW_congr H _ _ hab₁)
    · rintro _ ⟨x₂, hx₂Λ, rfl⟩
      obtain ⟨a, ha, b, hb, hab⟩ := hdec _ _ hU₂ (x₂ : V)
      have hap : a ∈ H.perp (H.X g₂) := hperp_a a b (hW₂ hb) (by rw [hab]; exact x₂.2)
      have haMM : a ∈ MMsharp H t₂ := hpart t₂ Λ₂ hsd₂ hMM₂ a b ha hb (by rw [hab]; exact hx₂Λ)
      have hin : (ddMk H t₂ ⟨a, haMM⟩, H.mkW g₂ ⟨a, hap⟩) ∈
          (fun p => (θ p.1, χ p.2)) '' GamG H t₁ g₁ := by
        rw [hG]
        exact ⟨⟨a, haMM⟩, hap, rfl⟩
      obtain ⟨_, ⟨u₁, hu₁, rfl⟩, hue⟩ := hin
      simp only [Prod.mk.injEq] at hue
      obtain ⟨n₁, hn₁, hx₂'⟩ := (hθ u₁ ⟨a, haMM⟩).1 hue.1
      set bb : ↥(H.W0 t₁.f t₁.f') := ψ.symm ⟨b, hb⟩
      have hψbb : (ψ bb : V) = b := by simp [bb]
      have hd2 : (ψ (bb - n₁) : V) ∈ Λ₂ := by
        rw [map_sub, Submodule.coe_sub, hψbb]
        have := Λ₂.sub_mem hx₂Λ hx₂'
        rwa [← hab, show a + b - (a + (ψ n₁ : V)) = b - ψ n₁ by abel] at this
      have hd1 : ((bb - n₁ : ↥(H.W0 t₁.f t₁.f')) : V) ∈ t₁.abelian₂ := (hth _).2 hd2
      have hx₁Λ : (u₁ : V) + bb ∈ t₁.abelian₂ := by
        have := t₁.abelian₂.add_mem hn₁ hd1
        rwa [Submodule.coe_sub, show (u₁ : V) + n₁ + ((bb : V) - n₁) = u₁ + bb by abel] at this
      have hx₁p : (u₁ : V) + bb ∈ H.perp (H.X g₁) := Submodule.add_mem _ hu₁ (hW₁ bb.2)
      refine ⟨_, ⟨⟨_, hx₁p⟩, hx₁Λ, rfl⟩, ?_⟩
      rw [mkW_add H _ _ hu₁ (hW₁ bb.2), map_add (f := _), hue.2, hC1]
      rw [← mkW_add H _ _ hap (hW₂ (ψ bb).2)]
      exact mkW_congr H _ _ (by rw [hψbb, hab])

end CR

end Formalism.L2.SG.LsDatumA
end
end

noncomputable section

open ValuativeRel Matrix

namespace Formalism.L2.SG.LsDatumA

open Formalism.MainNotions.S.Loc

section CR2

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {r : ℕ}

theorem U_swap (f f' : Fin (r + 1) → V) :
    Submodule.span E (Set.range (Sum.elim f' f)) = Submodule.span E (Set.range (Sum.elim f f')) := by
  rw [Set.Sum.elim_range, Set.Sum.elim_range, Set.union_comm]

theorem Zhat_swap (f f' : Fin (r + 1) → V) :
    H.Zhat f' f = ((M.L.cj.toRingEquiv.toRingHom).mapMatrix (H.Zhat f f'))ᵀ := by
  ext a b
  simp only [HermSp.Zhat, Matrix.transpose_apply, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]
  exact H.h_herm _ _

theorem om'_swap (f f' : Fin (r + 1) → V) : H.om' f' f = H.om f f' := by
  unfold HermSp.om' HermSp.om
  rw [Zhat_swap, ← Matrix.adjugate_transpose, ← RingHom.map_adjugate]
  simp only [Matrix.transpose_apply, RingHom.mapMatrix_apply, Matrix.map_apply]
  rfl

theorem det_Zhat_swap_unit (f f' : Fin (r + 1) → V) (h : IsUnit (H.Zhat f f').det) :
    IsUnit (H.Zhat f' f).det := by
  rw [Zhat_swap, Matrix.det_transpose, ← RingHom.map_det]
  exact h.map _

theorem cond_second_of_iso (g₁ g₁' g₂ g₂' : Fin (r + 1) → V) (T₁ T₂ : F) (hF₁ : Formalism.MainNotions.ThinScalesBound.FrameK H g₁ T₁)
    (hF₂ : Formalism.MainNotions.ThinScalesBound.FrameK H g₂ T₂) (hZ₁ : IsUnit (H.Zhat g₁ g₁').det) (χ : H.Wb g₁ ≃ₗ[E] H.Wb g₂) (κ : E)
    (hz : χ (H.mkW g₁ ⟨g₁ (Fin.last r), z_mem_perpX H hF₁⟩) = H.mkW g₂ ⟨g₂ (Fin.last r), z_mem_perpX H hF₂⟩)
    (ho : χ (H.mkW g₁ ⟨H.om' g₁ g₁', om'_mem_perpX H _ _⟩) = κ • H.mkW g₂ ⟨H.om' g₂ g₂', om'_mem_perpX H _ _⟩) :
    ∀ u ∈ Submodule.span E (Set.range (Sum.elim g₁ g₁')), ∀ hu : u ∈ H.perp (H.X g₁),
      ∃ u' ∈ Submodule.span E (Set.range (Sum.elim g₂ g₂')), ∃ hu' : u' ∈ H.perp (H.X g₂),
        χ (H.mkW g₁ ⟨u, hu⟩) = H.mkW g₂ ⟨u', hu'⟩ := by
  intro u hu hup
  obtain ⟨x, hx, β, γ, hxe⟩ := decomp_U_perpX H hF₁ hZ₁ hu hup
  let zP₁ : ↥(H.perp (H.X g₁)) := ⟨g₁ (Fin.last r), z_mem_perpX H hF₁⟩
  let oP₁ : ↥(H.perp (H.X g₁)) := ⟨H.om' g₁ g₁', om'_mem_perpX H _ _⟩
  let zP₂ : ↥(H.perp (H.X g₂)) := ⟨g₂ (Fin.last r), z_mem_perpX H hF₂⟩
  let oP₂ : ↥(H.perp (H.X g₂)) := ⟨H.om' g₂ g₂', om'_mem_perpX H _ _⟩
  have h1 : H.mkW g₁ ⟨u, hup⟩ = H.mkW g₁ (β • zP₁ + γ • oP₁) := by
    apply mkW_eq_of_sub_mem
    show u - (β • g₁ (Fin.last r) + γ • H.om' g₁ g₁') ∈ H.X g₁
    rw [hxe]
    convert hx using 1
    abel
  refine ⟨((β • zP₂ + (γ * κ) • oP₂ : ↥(H.perp (H.X g₂))) : V), ?_, (β • zP₂ + (γ * κ) • oP₂).2, ?_⟩
  · exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inl (Fin.last r), rfl⟩))
      (Submodule.smul_mem _ _ (om'_mem_U H g₂ g₂'))
  · rw [h1]
    simp only [map_add (f := _), map_smul]
    rw [show χ (H.mkW g₁ zP₁) = H.mkW g₂ zP₂ from hz, show χ (H.mkW g₁ oP₁) = κ • H.mkW g₂ oP₂ from ho, smul_smul]

end CR2

end Formalism.L2.SG.LsDatumA
