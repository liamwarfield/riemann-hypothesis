module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.LocInt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CobordismLinearRelations.ClozelConjCOfSteps
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.FormsFiniteGL

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.HarmFin
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

private theorem cmp_rT {W : Type} [AddCommGroup W] [Module ℂ W] {d : ℕ} (T : W →ₗ[ℂ] W) (i : Fin d)
    (x : W ⊗[ℂ] (Fin d → ℂ)) : cmp i (T.rTensor _ x) = T (cmp i x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul φ v => simp

private noncomputable def coords {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ} (Ξ : AlgRep E a) (q : ℕ)
    {n : ℕ} (e : Fin n → Herm E a) : Co Ξ q →ₗ[ℂ] ((Fin q → Fin n) × Fin Ξ.d → Sm E a) where
  toFun ω p := cmp p.2 (ω fun j => e (p.1 j))
  map_add' α β := funext fun p => map_add (Bor.cmp p.2) _ _
  map_smul' c α := funext fun p => map_smul (Bor.cmp p.2) c _

private theorem coords_inj {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ} (Ξ : AlgRep E a) (q : ℕ)
    {n : ℕ} {e : Fin n → Herm E a} (he : IsFrame e) : Function.Injective (coords Ξ q e) := by
  intro α β h
  have hs : Submodule.span ℝ (Set.range e) = ⊤ := by
    refine eq_top_iff.2 fun X _ => ?_
    rw [he X]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  apply AlternatingMap.coe_multilinearMap_injective
  refine MultilinearMap.ext_of_span_eq_top (g := fun _ => e) (fun _ => hs) fun I => ?_
  change α (fun j => e (I j)) = β (fun j => e (I j))
  rw [← sum_cmp (α _), ← sum_cmp (β _)]
  refine Finset.sum_congr rfl fun i _ => ?_
  have := congrFun h (I, i)
  exact congrArg (· ⊗ₜ[ℂ] _) this

theorem UpperTheory.V.Cj.H.harmFin :
    UpperTheory.V.Cj.H.HarmFin := by
  intro E _ _ _ a Ξ r m q U hU
  obtain ⟨n, e, he⟩ := frameEx E a
  obtain ⟨W, _, _, _, ρ, hρ, hk⟩ := kType E a Ξ q
  have hF := formsFiniteGL E a U hU W ρ hρ fun t u => ((m t).map (u + ·)).prod
  set F := Submodule.span ℂ (GlobalTheory.Published.AutFinGL.forms U ρ fun t u => ((m t).map (u + ·)).prod) with hFd
  have hle : ∀ ω ∈ Submodule.span ℂ {ω : Co Ξ q | IsH r m ω ∧ ∀ u ∈ U, trans u ω = ω}, ∀ p, coords Ξ q e ω p ∈ F := by
    intro ω hω p
    induction hω using Submodule.span_induction with
    | zero => rw [map_zero]; exact F.zero_mem
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact F.add_mem hx hy
    | smul c x _ hx => rw [map_smul]; exact F.smul_mem c hx
    | mem ω hω =>
      obtain ⟨h, hu⟩ := hω
      obtain ⟨U', -, -, hl⟩ := h.lev
      refine Submodule.subset_span ⟨(h.aut _ _).1, fun k hk' => ?_, fun g => ?_, (h.aut _ _).2⟩
      · have h1 := congrArg (fun η : Co Ξ q => cmp p.2 (η fun j => e (p.1 j))) (hu k hk')
        exact (cmp_rT _ _ _).symm.trans h1
      · obtain ⟨T, w, hT, hw⟩ := hk ω hl.equiv (fun j => e (p.1 j)) p.2
        have := GlobalTheory.Published.AutFinGL.type_of_map ρ T hT w g
        rw [hw] at this
        exact this
  refine FiniteDimensional.of_injective (V₂ := (Fin q → Fin n) × Fin Ξ.d → F)
    (LinearMap.pi fun p => ((LinearMap.proj p ∘ₗ coords Ξ q e) ∘ₗ Submodule.subtype _).codRestrict F fun ω => hle ω.1 ω.2 p)
    fun α β h => Subtype.ext (coords_inj Ξ q he (funext fun p => ?_))
  exact congrArg Subtype.val (congrFun h p)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CoForm
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL ComplexOrder
open UpperTheory.V.Cj UpperTheory.V.Cj.H

private noncomputable def ipL {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ} {Ξ : AlgRep E a} {q n : ℕ}
    (e : Fin n → Herm E a)
    (H : Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ) →ₗ⋆[ℂ] Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ) →ₗ[ℂ] ℂ) : Co Ξ q →ₗ⋆[ℂ] Co Ξ q →ₗ[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (fun ω η => ip e H ω η)
    (fun ω ω' η => by
      simp only [ip, AlternatingMap.add_apply, map_add (f := _), LinearMap.add_apply, Finset.sum_add_distrib])
    (fun c ω η => by
      simp only [ip, AlternatingMap.smul_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, Finset.smul_sum])
    (fun ω η η' => by
      simp only [ip, AlternatingMap.add_apply, map_add (f := _), Finset.sum_add_distrib])
    (fun c ω η => by
      simp only [ip, AlternatingMap.smul_apply, map_smul, Finset.smul_sum, RingHom.id_apply])

private theorem ipL_apply {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ} {Ξ : AlgRep E a} {q n : ℕ}
    (e : Fin n → Herm E a)
    (H : Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ) →ₗ⋆[ℂ] Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ) →ₗ[ℂ] ℂ) (ω η : Co Ξ q) :
    ipL e H ω η = ip e H ω η := rfl

theorem UpperTheory.V.Cj.H.coForm :
    UpperTheory.V.Cj.H.CoForm := by
  intro E _ _ _ a ha Ξ r q
  obtain ⟨-, H, hH, hx⟩ := petInv E a ha r
  obtain ⟨n, e, he⟩ := frameEx E a
  have hT := tformPos (Sm E a) Ξ.d H (sqSub E a r) 1 hH Matrix.PosDef.one
  obtain ⟨h1, h2⟩ := ipDef E a n e he _ (tform H 1) _ hT q
  refine ⟨transRep Ξ q, ipL e (tform H 1), fun _ _ => rfl, fun M hM => ⟨fun ω η => h1 ω η, fun ω hω => ?_, fun ω hω => ?_⟩,
    fun x => ?_⟩
  · exact (h2 ω fun X => mem_tens.2 (hM ω hω X)).1
  · exact (h2 ω fun X => mem_tens.2 (hM ω hω X)).2
  · obtain ⟨c, hc⟩ := hx x
    refine ⟨c, fun ω η hω hη => ?_⟩
    rw [ipL_apply, ipL_apply]
    simp only [ip, tform_apply, cmp_trans, Finset.mul_sum]
    refine Finset.sum_congr rfl fun I _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have := hc _ (hω (fun k => e (I k)) i) _ (hη (fun k => e (I k)) j)
    rw [mul_left_comm, ← this]
    rfl
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.AbsSSProj
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

private theorem exists_orthogonal_decomposition_of_isPos {W : Type} [AddCommGroup W] [Module ℂ W] (B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ)
    (M : Submodule ℂ W) (hB : IsPos B M) (F K : Submodule ℂ W) (hF : F ≤ M) (hK : K ≤ F)
    [FiniteDimensional ℂ F] (v : W) (hv : v ∈ F) :
    ∃ a ∈ K, ∃ b ∈ F, v = a + b ∧ ∀ x ∈ K, B x b = 0 := by
  letI core : InnerProductSpace.Core ℂ F :=
    { inner := fun x y => B x y
      conj_inner_symm := fun x y => by
        show (starRingEnd ℂ) (B y x) = B x y
        rw [hB.herm]; simp
      re_inner_nonneg := fun x => hB.nonneg x (hF x.2)
      add_left := fun x y z => by
        show B (x + y : F) z = B x z + B y z
        simp
      smul_left := fun x y r => by
        show B (r • x : F) y = (starRingEnd ℂ) r * B x y
        simp
      definite := fun x hx => Subtype.ext (hB.definite x (hF x.2) hx) }
  letI : NormedAddCommGroup F := InnerProductSpace.Core.toNormedAddCommGroup (cd := core)
  letI : InnerProductSpace ℂ F := InnerProductSpace.ofCore (𝕜 := ℂ) (F := F) inferInstance
  let K' : Submodule ℂ F := K.comap F.subtype
  haveI : CompleteSpace K' := FiniteDimensional.complete ℂ K'
  obtain ⟨y, hy, z, hz, hyz⟩ := K'.exists_add_mem_mem_orthogonal ⟨v, hv⟩
  refine ⟨y, hy, z, z.2, congrArg Subtype.val hyz, fun x hx => ?_⟩
  have := (Submodule.mem_orthogonal K' z).1 hz ⟨x, hK hx⟩ hx
  exact this

private theorem orbit_of_compact_finite_of_open_stabilizer {G W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G W) (n : W) (U V : Subgroup G)
    (hUc : IsCompact (U : Set G)) (hVo : IsOpen (V : Set G)) (hVn : ∀ u ∈ V, ρ u n = n) :
    ((fun u => ρ u n) '' (U : Set G)).Finite := by
  obtain ⟨t, ht⟩ := hUc.elim_finite_subcover (fun u : U => (fun g => (u : G)⁻¹ * g) ⁻¹' (V : Set G))
    (fun u => hVo.preimage (continuous_const.mul continuous_id))
    (fun g hg => Set.mem_iUnion.2 ⟨⟨g, hg⟩, by simp [V.one_mem]⟩)
  apply ((t : Set U).toFinite.image (fun u : U => ρ (u : G) n)).subset
  rintro _ ⟨g, hg, rfl⟩
  obtain ⟨u, hu, hgu⟩ := Set.mem_iUnion₂.1 (ht hg)
  refine ⟨u, hu, ?_⟩
  have hg' : g = (u : G) * ((u : G)⁻¹ * g) := by group
  show ρ (u : G) n = ρ g n
  rw [hg', map_mul, Module.End.mul_apply, hVn _ hgu]

theorem UpperTheory.V.Cj.H.absSS :
    UpperTheory.V.Cj.H.AbsSS := by
  intro G W _ _ _ _ _ ρ M B hB hM hc hsm hfd N hNM hN
  have hρ : ∀ (g h : G) (x : W), ρ g (ρ h x) = ρ (g * h) x := by
    intro g h x
    rw [map_mul, Module.End.mul_apply]
  let N' : Submodule ℂ W :=
    { carrier := {w | w ∈ M ∧ ∀ n ∈ N, B n w = 0}
      add_mem' := fun {a b} ha hb => ⟨M.add_mem ha.1 hb.1, fun n hn => by simp [ha.2 n hn, hb.2 n hn]⟩
      zero_mem' := ⟨M.zero_mem, fun n _ => by simp⟩
      smul_mem' := fun r w hw => ⟨M.smul_mem r hw.1, fun n hn => by simp [hw.2 n hn]⟩ }
  have memN' : ∀ w, w ∈ N' ↔ w ∈ M ∧ ∀ n ∈ N, B n w = 0 := fun w => Iff.rfl
  refine ⟨N', fun w hw => ((memN' w).1 hw).1, ?_, ?_, ?_⟩
  · intro g w hw
    rw [memN'] at hw ⊢
    refine ⟨hM g w hw.1, fun n hn => ?_⟩
    obtain ⟨c, hcg⟩ := hc g
    have hn' : ρ g⁻¹ n ∈ N := hN _ _ hn
    have h1 : ρ g (ρ g⁻¹ n) = n := by rw [hρ, mul_inv_cancel, map_one, Module.End.one_apply]
    rw [← h1, hcg _ (hNM hn') _ hw.1, hw.2 _ hn', mul_zero]
  · rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxN, hxN'⟩ := Submodule.mem_inf.1 hx
    rw [memN'] at hxN'
    exact (Submodule.mem_bot ℂ).2 (hB.definite x (hNM hxN) (hxN'.2 x hxN))
  · refine le_antisymm (sup_le hNM fun w hw => ((memN' w).1 hw).1) ?_
    intro v hv
    obtain ⟨U, hUo, hUc, hUv⟩ := hsm v hv
    haveI := hfd U hUo
    have hFM : Submodule.span ℂ {x | x ∈ M ∧ ∀ u ∈ U, ρ u x = x} ≤ M :=
      Submodule.span_le.2 fun x hx => hx.1
    have hFfix : ∀ x ∈ Submodule.span ℂ {x | x ∈ M ∧ ∀ u ∈ U, ρ u x = x}, ∀ u ∈ U, ρ u x = x := by
      intro x hx u hu
      induction hx using Submodule.span_induction with
      | mem y hy => exact hy.2 u hu
      | zero => simp
      | add y z _ _ hy hz => simp [hy, hz]
      | smul r y _ hy => simp [hy]
    have hvF : v ∈ Submodule.span ℂ {x | x ∈ M ∧ ∀ u ∈ U, ρ u x = x} :=
      Submodule.subset_span ⟨hv, hUv⟩
    obtain ⟨a, haK, b, hbF, hvab, hb⟩ :=
      exists_orthogonal_decomposition_of_isPos B M hB _ (N ⊓ Submodule.span ℂ {x | x ∈ M ∧ ∀ u ∈ U, ρ u x = x}) hFM inf_le_right v hvF
    rw [hvab]
    refine Submodule.add_mem_sup (Submodule.mem_inf.1 haK).1 ((memN' b).2 ⟨hFM hbF, fun n hn => ?_⟩)
    have hinv : ∀ u ∈ U, ∀ x ∈ M, B (ρ u x) b = B x b := by
      intro u hu x hx
      obtain ⟨c, hcu⟩ := hc u
      have h1 := hcu x hx b (hFM hbF)
      rw [hFfix b hbF u hu] at h1
      by_cases hb0 : b = 0
      · simp [hb0]
      have h2 := hcu b (hFM hbF) b (hFM hbF)
      rw [hFfix b hbF u hu] at h2
      have hbb : B b b ≠ 0 := fun h => hb0 (hB.definite b (hFM hbF) h)
      have hc1 : c = 1 := by
        have h3 : (c - 1) * B b b = 0 := by rw [sub_mul, ← h2]; ring
        rcases mul_eq_zero.1 h3 with h | h
        · exact sub_eq_zero.1 h
        · exact absurd h hbb
      rw [h1, hc1, one_mul]
    obtain ⟨V, hVo, -, hVn⟩ := hsm n (hNM hn)
    have hfin := orbit_of_compact_finite_of_open_stabilizer ρ n U V hUc hVo hVn
    have hmemS : ∀ x, x ∈ hfin.toFinset ↔ ∃ g ∈ U, ρ g n = x := by
      intro x
      rw [Set.Finite.mem_toFinset]
      rfl
    have hSN : ∀ x ∈ hfin.toFinset, x ∈ N ∧ B x b = B n b := by
      intro x hx
      obtain ⟨g, hg, rfl⟩ := (hmemS x).1 hx
      exact ⟨hN g n hn, hinv g hg n (hNM hn)⟩
    have hsN : (∑ x ∈ hfin.toFinset, x) ∈ N := Submodule.sum_mem _ fun x hx => (hSN x hx).1
    have hsfix : ∀ u ∈ U, ρ u (∑ x ∈ hfin.toFinset, x) = ∑ x ∈ hfin.toFinset, x := by
      intro u hu
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Finset.sum_nbij' (fun x => ρ u x) (fun x => ρ u⁻¹ x) ?_ ?_ ?_ ?_ (fun _ _ => rfl)
      · intro x hx
        obtain ⟨g, hg, rfl⟩ := (hmemS x).1 hx
        exact (hmemS _).2 ⟨u * g, U.mul_mem hu hg, (hρ u g n).symm⟩
      · intro x hx
        obtain ⟨g, hg, rfl⟩ := (hmemS x).1 hx
        exact (hmemS _).2 ⟨u⁻¹ * g, U.mul_mem (U.inv_mem hu) hg, (hρ u⁻¹ g n).symm⟩
      · intro x _
        rw [hρ, inv_mul_cancel, map_one, Module.End.one_apply]
      · intro x _
        rw [hρ, mul_inv_cancel, map_one, Module.End.one_apply]
    have hsF : (∑ x ∈ hfin.toFinset, x) ∈ Submodule.span ℂ {x | x ∈ M ∧ ∀ u ∈ U, ρ u x = x} :=
      Submodule.subset_span ⟨hNM hsN, hsfix⟩
    have hzero := hb _ (Submodule.mem_inf.2 ⟨hsN, hsF⟩)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, LinearMap.sum_apply, Finset.sum_congr rfl fun x hx => (hSN x hx).2,
      Finset.sum_const, nsmul_eq_mul] at hzero
    have hcard : (hfin.toFinset.card : ℂ) ≠ 0 := by
      have : n ∈ hfin.toFinset := (hmemS n).2 ⟨1, U.one_mem, by simp⟩
      exact_mod_cast (Finset.card_pos.2 ⟨n, this⟩).ne'
    exact (mul_eq_zero.1 hzero).resolve_left hcard
end

open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

private theorem harmSS_fix {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ} {Ξ : AlgRep E a} {q : ℕ}
    {U : Subgroup (GL (Fin a) (Af E))} {ω : Co Ξ q} (h : IsLev U Ξ ω) {u : GL (Fin a) (Af E)} (hu : u ∈ U) :
    trans u ω = ω := by
  ext X
  have hle : Submodule.span ℂ {x : Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ) | ∃ φ v, IsLevelFn U Ξ φ ∧ x = φ ⊗ₜ[ℂ] v} ≤
      LinearMap.eqLocus ((act (.fin u) : Module.End ℂ (Sm E a)).rTensor (Fin Ξ.d → ℂ)) LinearMap.id := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨φ, v, hφ, rfl⟩
    show LinearMap.rTensor _ _ (φ ⊗ₜ[ℂ] v) = φ ⊗ₜ[ℂ] v
    rw [LinearMap.rTensor_tmul, hφ.2.1 u hu]
  exact hle (h.val X)

theorem UpperTheory.V.Cj.H.harmSS :
    UpperTheory.V.Cj.H.HarmSS := by
  intro E _ _ _ a ha Ξ r m q M hM hT N hNM hN
  obtain ⟨ρ, B, hρ, hpos, hc⟩ := UpperTheory.V.Cj.H.coForm E a ha Ξ r q
  have hsq : ∀ ω ∈ M, Val (sqSub E a r) ω := fun ω h => ((hM ω).1 h).sq
  obtain ⟨N', h1, h2, h3, h4⟩ := UpperTheory.V.Cj.H.absSS (GL (Fin a) (Af E)) (Co Ξ q) ρ M B (hpos M hsq)
    (fun g v hv => by rw [hρ]; exact hT g v hv)
    (fun g => by
      obtain ⟨c, h⟩ := hc g
      exact ⟨c, fun v hv w hw => by rw [hρ, hρ]; exact h v w (hsq v hv) (hsq w hw)⟩)
    (fun v hv => by
      obtain ⟨U, hUo, hUc, hU⟩ := ((hM v).1 hv).lev
      exact ⟨U, hUo, hUc, fun u hu => by rw [hρ]; exact harmSS_fix hU hu⟩)
    (fun U hU => by
      have h := UpperTheory.V.Cj.H.harmFin E a Ξ r m q U hU
      have e : {v : Co Ξ q | v ∈ M ∧ ∀ u ∈ U, ρ u v = v} = {ω : Co Ξ q | IsH r m ω ∧ ∀ u ∈ U, trans u ω = ω} := by
        ext v
        simp only [Set.mem_setOf_eq, hM, hρ]
      rw [e]
      exact h)
    N hNM (fun g v hv => by rw [hρ]; exact hN g v hv)
  exact ⟨N', h1, fun x ω h => by rw [← hρ]; exact h2 x ω h, h3, h4⟩
