module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ProBurnside
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.AmFin
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.QuotProf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.LimOut

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.LimElt
open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

theorem UpperTheory.V.AlgebraTools.exists_lim_elt :
    ∀ (G ι : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] (U : Ultrafilter ι) (K : ι → Subgroup G) [∀ i, (K i).Normal],
      (∀ a : ι → G, ∃ b : G, ∀ O : OpenNormalSubgroup G, ∀ᶠ i in (U : Filter ι), b⁻¹ * a i ∈ O.toSubgroup) ∧
      (∀ (a : ι → G) (b b' : G), (∀ O : OpenNormalSubgroup G, ∀ᶠ i in (U : Filter ι), b⁻¹ * a i ∈ K i ⊔ O.toSubgroup) →
        (∀ O : OpenNormalSubgroup G, ∀ᶠ i in (U : Filter ι), b'⁻¹ * a i ∈ K i ⊔ O.toSubgroup) → b⁻¹ * b' ∈ limKer (U : Filter ι) K) := by
  intro G ι _ _ _ _ _ U K _
  refine ⟨fun a => ?_, fun a b b' hb hb' => ?_⟩
  · obtain ⟨b, hl⟩ : ∃ b : G, Tendsto a (U : Filter ι) (nhds b) := by
      refine ⟨(U.map a).lim, ?_⟩
      have h' := (U.map a).le_nhds_lim
      rw [Ultrafilter.coe_map] at h'
      exact h'
    refine ⟨b, fun O => ?_⟩
    have hopen : IsOpen {y : G | b⁻¹ * y ∈ O.toSubgroup} :=
      O.toOpenSubgroup.isOpen.preimage (continuous_const_mul _)
    exact hl.eventually (hopen.mem_nhds (by simp))
  · rw [mem_limKer]
    intro O
    filter_upwards [hb O, hb' O] with i h1 h2
    have heq : b⁻¹ * b' = (b⁻¹ * a i) * (b'⁻¹ * a i)⁻¹ := by group
    rw [heq]
    exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ h2)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.LimKer
open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

private theorem limKer_key {G ι : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] (U : Ultrafilter ι) (K : ι → Subgroup G) (O : OpenNormalSubgroup G) (x : G) :
    (∀ᶠ i in (U : Filter ι), x ∈ K i ⊔ O.toSubgroup) ↔
      x ∈ limKer (U : Filter ι) K ⊔ O.toSubgroup := by
  haveI := O.isNormal'
  constructor
  · intro h
    have hex : ∀ᶠ i in (U : Filter ι), ∃ k ∈ K i, k⁻¹ * x ∈ O.toSubgroup := by
      refine h.mono fun i hi => ?_
      obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup_of_normal_right.1 hi
      refine ⟨y, hy, ?_⟩
      rw [← hyz]
      simpa using hz
    classical
    obtain ⟨k, hk⟩ : ∃ k : ι → G, ∀ᶠ i in (U : Filter ι), k i ∈ K i ∧ (k i)⁻¹ * x ∈ O.toSubgroup := by
      refine ⟨fun i => if hi : ∃ k ∈ K i, k⁻¹ * x ∈ O.toSubgroup then hi.choose else 1, ?_⟩
      refine hex.mono fun i hi => ?_
      simp only [dif_pos hi]
      exact hi.choose_spec
    obtain ⟨l, hl⟩ : ∃ l : G, Tendsto k (U : Filter ι) (nhds l) := by
      refine ⟨(U.map k).lim, ?_⟩
      have h' := (U.map k).le_nhds_lim
      rw [Ultrafilter.coe_map] at h'
      exact h'
    have hlL : l ∈ limKer (U : Filter ι) K := by
      rw [mem_limKer]
      intro O'
      have hopen : IsOpen {y : G | l⁻¹ * y ∈ O'.toSubgroup} :=
        O'.toOpenSubgroup.isOpen.preimage (continuous_const_mul _)
      filter_upwards [hl.eventually (hopen.mem_nhds (by simp)), hk] with i h1 h2
      have heq : l = k i * (l⁻¹ * k i)⁻¹ := by group
      rw [heq]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left h2.1) (Subgroup.mem_sup_right (Subgroup.inv_mem _ h1))
    have hC : IsClosed {y : G | y⁻¹ * x ∈ O.toSubgroup} :=
      O.toOpenSubgroup.isClosed.preimage (continuous_inv.mul continuous_const)
    have hlx : l⁻¹ * x ∈ O.toSubgroup := hC.mem_of_tendsto hl (hk.mono fun i h => h.2)
    have heq : x = l * (l⁻¹ * x) := by group
    rw [heq]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hlL) (Subgroup.mem_sup_right hlx)
  · intro h
    let S : Subgroup G :=
      { carrier := {g | ∀ᶠ i in (U : Filter ι), g ∈ K i ⊔ O.toSubgroup}
        mul_mem' := fun ha hb =>
          Filter.Eventually.mono (Filter.Eventually.and ha hb) fun i hi => Subgroup.mul_mem _ hi.1 hi.2
        one_mem' := Filter.Eventually.of_forall fun i => Subgroup.one_mem _
        inv_mem' := fun ha => Filter.Eventually.mono ha fun i hi => Subgroup.inv_mem _ hi }
    have hle : limKer (U : Filter ι) K ⊔ O.toSubgroup ≤ S :=
      sup_le (fun g hg => (mem_limKer.1 hg) O)
        (fun g hg => Filter.Eventually.of_forall fun i => Subgroup.mem_sup_right hg)
    exact hle h

theorem UpperTheory.V.AlgebraTools.limKer_sup :
    ∀ (G ι : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] (U : Ultrafilter ι) (K : ι → Subgroup G) [∀ i, (K i).Normal],
      IsClosed (limKer (U : Filter ι) K : Set G) ∧
      (∀ O : OpenNormalSubgroup G, ∀ᶠ i in (U : Filter ι), K i ⊔ O.toSubgroup = limKer (U : Filter ι) K ⊔ O.toSubgroup) ∧
      (∀ O : OpenNormalSubgroup G, limKer (U : Filter ι) K ≤ O.toSubgroup ↔ ∀ᶠ i in (U : Filter ι), K i ≤ O.toSubgroup) := by
  intro G ι _ _ _ _ _ U K _
  have h2 : ∀ O : OpenNormalSubgroup G, ∀ᶠ i in (U : Filter ι),
      K i ⊔ O.toSubgroup = limKer (U : Filter ι) K ⊔ O.toSubgroup := by
    intro O
    obtain ⟨T, hT⟩ := isCompact_univ.elim_finite_subcover
      (fun g : G => {y : G | g⁻¹ * y ∈ O.toSubgroup})
      (fun g => O.toOpenSubgroup.isOpen.preimage (continuous_const_mul _))
      (fun y _ => Set.mem_iUnion.2 ⟨y, by simp⟩)
    have hev : ∀ᶠ i in (U : Filter ι), ∀ t ∈ T,
        (t ∈ K i ⊔ O.toSubgroup ↔ t ∈ limKer (U : Filter ι) K ⊔ O.toSubgroup) := by
      refine (Filter.eventually_all_finset T).2 (fun t _ => ?_)
      by_cases ht : t ∈ limKer (U : Filter ι) K ⊔ O.toSubgroup
      · exact ((limKer_key U K O t).2 ht).mono fun i hi => iff_of_true hi ht
      · have hn : ¬ ∀ᶠ i in (U : Filter ι), t ∈ K i ⊔ O.toSubgroup :=
          fun h => ht ((limKer_key U K O t).1 h)
        exact (Ultrafilter.eventually_not.2 hn).mono fun i hi => iff_of_false hi ht
    filter_upwards [hev] with i hi
    ext g
    obtain ⟨t, htT, hgt⟩ : ∃ t ∈ T, t⁻¹ * g ∈ O.toSubgroup := by
      have := hT (Set.mem_univ g)
      simp only [Set.mem_iUnion] at this
      obtain ⟨t, htT, hgt⟩ := this
      exact ⟨t, htT, hgt⟩
    have mem_iff : ∀ M : Subgroup G, O.toSubgroup ≤ M → (g ∈ M ↔ t ∈ M) := by
      intro M hM
      have hg : g = t * (t⁻¹ * g) := by group
      rw [hg]
      exact mul_mem_cancel_right (hM hgt)
    rw [mem_iff _ le_sup_right, mem_iff _ le_sup_right]
    exact hi t htT
  have hclosed : IsClosed (limKer (U : Filter ι) K : Set G) := by
    have hset : (limKer (U : Filter ι) K : Set G) =
        ⋂ O : OpenNormalSubgroup G, ((limKer (U : Filter ι) K ⊔ O.toSubgroup : Subgroup G) : Set G) := by
      ext x
      simp only [SetLike.mem_coe, Set.mem_iInter]
      constructor
      · intro hx O
        exact Subgroup.mem_sup_left hx
      · intro hx
        rw [mem_limKer]
        intro O
        exact (limKer_key U K O x).2 (hx O)
    rw [hset]
    exact isClosed_iInter fun O =>
      Subgroup.isClosed_of_isOpen _ (Subgroup.isOpen_mono le_sup_right O.toOpenSubgroup.isOpen)
  refine ⟨hclosed, h2, fun O => ⟨fun h => ?_, fun h => ?_⟩⟩
  · filter_upwards [h2 O] with i hi
    rw [sup_eq_right.2 h] at hi
    exact sup_eq_right.1 hi
  · intro x hx
    obtain ⟨i, hi1, hi2⟩ := ((mem_limKer.1 hx O).and h).exists
    exact (sup_le hi2 le_rfl) hi1
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.PlGen
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

theorem UpperTheory.V.Pa.pl_gen :
    ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ] (H : Subgroup Γ) [H.Normal], IsOpen (H : Set Γ) → PL l H = ⊥ → Finite (HomL l H) → TopFG Γ ∧ ∀ b : ℕ, Nat.card (HomL l H) ≤ b → ∃ z : Fin b → H, TopGen (Set.range z) := by
  intro l _ Γ _ _ _ _ _ H _ hH hPL hfin
  have hpro : IsProL l H := ((pl_props l Γ H hH).2.2.2.2.1).1 hPL
  have hcl : IsClosed (H : Set Γ) := Subgroup.isClosed_of_isOpen H hH
  haveI : CompactSpace H := isCompact_iff_compactSpace.1 hcl.isCompact
  obtain ⟨-, hgen⟩ := topGen_of_hom l H hpro
  have key : ∀ b : ℕ, Nat.card (HomL l H) ≤ b → ∃ z : Fin b → H, TopGen (Set.range z) := by
    intro b hb
    have hf : {f : H →* Multiplicative (ZMod l) | IsOpen (f.ker : Set H)}.Finite := Set.finite_coe_iff.1 hfin
    have hn : {f : H →* Multiplicative (ZMod l) | IsOpen (f.ker : Set H)}.ncard ≤ l ^ b := by
      rw [← Nat.card_coe_set_eq]
      exact hb.trans (Nat.lt_pow_self (Fact.out : l.Prime).one_lt).le
    exact hgen b hf hn
  refine ⟨?_, key⟩
  obtain ⟨z, hz⟩ := key _ le_rfl
  haveI : Finite (Γ ⧸ H) := Subgroup.quotient_finite_of_isOpen H hH
  refine ⟨Subtype.val '' Set.range z ∪ Set.range (Quotient.out : Γ ⧸ H → Γ),
    ((Set.finite_range z).image _).union (Set.finite_range _), ?_⟩
  rw [topGen_iff]
  set K := (Subgroup.closure (Subtype.val '' Set.range z ∪ Set.range (Quotient.out : Γ ⧸ H → Γ))).topologicalClosure
  have hsub : Subtype.val '' ((Subgroup.closure (Set.range z) : Subgroup H) : Set H) ⊆ (K : Set Γ) := by
    intro y hy
    have hmap : y ∈ (Subgroup.closure (Set.range z)).map H.subtype := hy
    rw [MonoidHom.map_closure] at hmap
    exact Subgroup.le_topologicalClosure _ (Subgroup.closure_mono Set.subset_union_left hmap)
  have hHK : H ≤ K := by
    intro h hh
    have h1 : (⟨h, hh⟩ : H) ∈ closure ((Subgroup.closure (Set.range z) : Subgroup H) : Set H) := hz ⟨h, hh⟩
    have h2 := mem_closure_image continuous_subtype_val.continuousAt h1
    exact closure_minimal hsub (Subgroup.isClosed_topologicalClosure _) h2
  refine eq_top_iff.2 fun g _ => ?_
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul H g
  have hg : g = (QuotientGroup.mk g : Γ ⧸ H).out * (h : Γ)⁻¹ := by
    rw [hh]
    group
  rw [hg]
  refine K.mul_mem ?_ (hHK (H.inv_mem h.2))
  exact Subgroup.le_topologicalClosure _ (Subgroup.subset_closure (Or.inr ⟨_, rfl⟩))
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.Loc_fin
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

theorem UpperTheory.V.Pa.loc_fin :
    ∀ (l : ℕ) [Fact l.Prime] (Y : Type) [Group Y] [TopologicalSpace Y] [IsTopologicalGroup Y] [CompactSpace Y] [TotallyDisconnectedSpace Y] (H : Subgroup Y) [H.Normal], IsOpen (H : Set Y) → PhiCond Y l → ∃ (P : Subgroup Y) (_ : P.Normal), TopFG (Y ⧸ P) ∧ ∀ (Z : Type) [Group Z] [TopologicalSpace Z] [IsTopologicalGroup Z] [CompactSpace Z] [TotallyDisconnectedSpace Z] (f : Y →* Z) (H' : Subgroup Z), Continuous f → PL l H' = ⊥ → H ≤ H'.comap f → P ≤ f.ker := by
  intro l _ Y _ _ _ _ _ H _ hH hphi
  obtain ⟨hPn, hPc, hPH, -, -, -⟩ := pl_props l Y H hH
  refine ⟨PL l H, hPn, ?_, ?_⟩
  · let P := PL l H
    let m : Y →* Y ⧸ P := QuotientGroup.mk' P
    have hmc : Continuous m := continuous_quot_mk
    have hms : Function.Surjective m := QuotientGroup.mk'_surjective P
    haveI : TotallyDisconnectedSpace (Y ⧸ P) := (totallyDisconnected_quot Y P hPc).1
    let H' : Subgroup (Y ⧸ P) := H.map m
    haveI : H'.Normal := Subgroup.Normal.map inferInstance m hms
    have hcm : H'.comap m = H := by
      rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']
      exact sup_eq_left.mpr hPH
    have hH'open : IsOpen (H' : Set (Y ⧸ P)) := by
      have : (H' : Set (Y ⧸ P)) = m '' (H : Set Y) := by simp [H']
      rw [this]
      exact QuotientGroup.isOpenMap_coe _ hH
    have hPL' : PL l H' = ⊥ := by
      rw [← pl_map l Y (Y ⧸ P) m H' hH'open hmc hms, hcm]
      rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    have hfin : Finite (HomL l (H'.comap m)) := by
      rw [hcm]
      exact hphi H hH
    exact (pl_gen l (Y ⧸ P) H' hH'open hPL' (homl_desc l Y (Y ⧸ P) m H' hmc hms hfin).1).1
  · intro Z _ _ _ _ _ f H' hf hPL hle g hg
    rw [MonoidHom.mem_ker]
    have hmem : f g ∈ PL l H' := by
      simp only [PL, Subgroup.mem_iInf] at hg ⊢
      intro U hU
      let V : OpenNormalSubgroup Y :=
        { toOpenSubgroup := U.toOpenSubgroup.comap f hf
          isNormal' := Subgroup.Normal.comap U.isNormal' f }
      have hV : ∀ y : Y, y ∈ V ↔ f y ∈ U := fun y => Iff.rfl
      have := hg V (by
        intro h hh
        obtain ⟨e, he⟩ := hU (f h) (hle hh)
        exact ⟨e, (hV _).mpr (by simpa using he)⟩)
      exact (hV g).mp this
    rw [hPL] at hmem
    exact (Subgroup.mem_bot).mp hmem
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.SysCover
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

theorem UpperTheory.V.Pa.sys_cover :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0), T.ProL → ∃ (Ph : Type) (_ : Group Ph) (_ : TopologicalSpace Ph) (_ : IsTopologicalGroup Ph) (_ : CompactSpace Ph) (_ : TotallyDisconnectedSpace Ph) (π : ∀ N, Ph →* (T.GN N).Γ) (ct : Ph), TopFG Ph ∧ (∀ N, Continuous (π N) ∧ Function.Surjective (π N) ∧ π N ct = (T.GN N).c) ∧ ∀ N N' g, (T.h N).p (π N g) * ((T.h N').p (π N' g))⁻¹ ∈ T.H := by
  intro l _ L G0 T hT
  classical
  let H0 : Subgroup G0.Γ := (T.H : Subgroup G0.Γ)
  have hH0open : IsOpen (H0 : Set G0.Γ) := T.H.isOpen
  obtain ⟨n, e, he⟩ : ∃ n : ℕ, ∃ e : Fin n → G0.Γ ⧸ H0, Function.Surjective e := by
    obtain ⟨n, ⟨eq⟩⟩ := Finite.exists_equiv_fin (G0.Γ ⧸ H0)
    exact ⟨n, eq.symm, eq.symm.surjective⟩
  let lift : G0.Γ ⧸ H0 → G0.Γ := Function.surjInv QuotientGroup.mk_surjective
  have hlift : ∀ y, (QuotientGroup.mk (lift y) : G0.Γ ⧸ H0) = y :=
    Function.surjInv_eq QuotientGroup.mk_surjective
  let yc : Fin (n + 1) → G0.Γ := Fin.cons G0.c (fun i => lift (e i))
  let γ : Fin (n + 1) → G0.Γ ⧸ H0 := fun i => QuotientGroup.mk (yc i)
  have hγ : Function.Surjective γ := by
    intro y
    obtain ⟨i, rfl⟩ := he y
    exact ⟨i.succ, by simp [γ, yc, hlift]⟩
  obtain ⟨P, iG, iT, iTG, iC, iTD, x, hx, hfree⟩ := exists_free_profinite (n + 1 + T.hb)
  obtain ⟨f0, hf0c, hf0x⟩ := hfree G0.Γ (Fin.append yc (fun _ => 1))
  let π0 : P →* G0.Γ ⧸ H0 := (QuotientGroup.mk' H0).comp f0
  have hπ0ker : IsOpen (π0.ker : Set P) := by
    have : (π0.ker : Set P) = f0 ⁻¹' (H0 : Set G0.Γ) := by
      ext g
      simp [π0, MonoidHom.mem_ker, QuotientGroup.eq_one_iff]
    rw [this]
    exact hH0open.preimage hf0c
  have hcast : ∀ i : Fin (n + 1), π0 (x (Fin.castAdd T.hb i)) = γ i := by
    intro i
    simp [π0, γ, hf0x, Fin.append_left]
  have hnat : ∀ i : Fin T.hb, π0 (x (Fin.natAdd (n + 1) i)) = 1 := by
    intro i
    simp [π0, hf0x, Fin.append_right]
  have key : ∀ N : ℕ, ∃ f : P →* (T.GN N).Γ, Continuous f ∧ Function.Surjective f ∧
      ((QuotientGroup.mk' H0).comp (T.h N).p).comp f = π0 ∧
      f (x (Fin.castAdd T.hb 0)) = (T.GN N).c := by
    intro N
    let p := (T.h N).p
    let q : (T.GN N).Γ →* G0.Γ ⧸ H0 := (QuotientGroup.mk' H0).comp p
    let HN : Subgroup (T.GN N).Γ := H0.comap p
    haveI : HN.Normal := Subgroup.Normal.comap inferInstance p
    have hqker : q.ker = HN := by
      ext g
      simp [q, HN, p, MonoidHom.mem_ker, QuotientGroup.eq_one_iff]
    have hHNopen : IsOpen (HN : Set (T.GN N).Γ) := hH0open.preimage (T.h N).cont
    have hqopen : IsOpen (q.ker : Set (T.GN N).Γ) := by rw [hqker]; exact hHNopen
    let g : Fin (n + 1) → (T.GN N).Γ :=
      Fin.cons (T.GN N).c (fun i => Function.surjInv (T.h N).surj (yc i.succ))
    have hg : ∀ i, q (g i) = γ i := by
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [q, g, γ, yc, p, (T.h N).c]
      · simp [q, g, γ, p, Function.surjInv_eq (T.h N).surj]
    have hz : ∃ z : Fin T.hb → ↥q.ker, TopGen (Set.range z) := by
      rw [hqker]
      have hPL := hT.2 N
      have hfin := T.finN N
      exact (pl_gen l (T.GN N).Γ HN hHNopen hPL hfin.1).2 T.hb hfin.2
    obtain ⟨f, hfc, hfs, hfq, hfx⟩ :=
      exists_surj_over_finite P (G0.Γ ⧸ H0) (n + 1) T.hb x γ π0 hx hfree hγ hπ0ker hcast hnat
        (T.GN N).Γ q hqopen g hg hz
    exact ⟨f, hfc, hfs, hfq, by rw [hfx 0]; simp [g]⟩
  choose F hFc hFs hFq hFx using key
  refine ⟨P, iG, iT, iTG, iC, iTD, F, x (Fin.castAdd T.hb 0), ⟨Set.range x, Set.finite_range x, hx⟩,
    fun N => ⟨hFc N, hFs N, hFx N⟩, ?_⟩
  intro N N' g
  have h1 := congrArg (fun φ => φ g) (hFq N)
  have h2 := congrArg (fun φ => φ g) (hFq N')
  simp only [MonoidHom.comp_apply, QuotientGroup.mk'_apply] at h1 h2
  have h3 : (QuotientGroup.mk ((T.h N).p (F N g)) : G0.Γ ⧸ H0) = QuotientGroup.mk ((T.h N').p (F N' g)) := by
    rw [h1, h2]
  rw [QuotientGroup.eq_iff_div_mem, div_eq_mul_inv] at h3
  exact h3
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.InLim
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem exists_tendsto_ultrafilter_of_compact {X : Type} [TopologicalSpace X] [CompactSpace X] (U : Ultrafilter ℕ) (a : ℕ → X) :
    ∃ x, Tendsto a (U : Filter ℕ) (nhds x) := by
  obtain ⟨x, -, hx⟩ := isCompact_univ.ultrafilter_le_nhds (U.map a) (by simp)
  exact ⟨x, by rwa [Ultrafilter.coe_map] at hx⟩

private theorem inv_mul_mem_limKer_of_tendsto_of_eventually_eq {Ph : Type} [Group Ph] [TopologicalSpace Ph] [IsTopologicalGroup Ph]
    {Γ : ℕ → Type} [∀ N, Group (Γ N)] (π : ∀ N, Ph →* Γ N) (U : Ultrafilter ℕ)
    (a b : ℕ → Ph) (x y : Ph) (ha : Tendsto a (U : Filter ℕ) (nhds x))
    (hb : Tendsto b (U : Filter ℕ) (nhds y))
    (hab : ∀ᶠ N in (U : Filter ℕ), π N (a N) = π N (b N)) :
    x⁻¹ * y ∈ limKer (U : Filter ℕ) (fun N => (π N).ker) := by
  rw [mem_limKer]
  intro O
  have hO : ((O.toOpenSubgroup : Subgroup Ph) : Set Ph) ∈ nhds (1 : Ph) :=
    O.toOpenSubgroup.isOpen.mem_nhds O.toOpenSubgroup.one_mem
  have h1 : Tendsto (fun N => x⁻¹ * a N) (U : Filter ℕ) (nhds 1) := by
    simpa using (tendsto_const_nhds (x := x⁻¹)).mul ha
  have h2 : Tendsto (fun N => (b N)⁻¹ * y) (U : Filter ℕ) (nhds 1) := by
    simpa using hb.inv.mul (tendsto_const_nhds (x := y))
  filter_upwards [h1 hO, h2 hO, hab] with N h1N h2N hN
  have e : x⁻¹ * y = (x⁻¹ * a N) * ((a N)⁻¹ * b N) * ((b N)⁻¹ * y) := by group
  rw [e]
  refine Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_right h1N)
    (Subgroup.mem_sup_left ?_)) (Subgroup.mem_sup_right h2N)
  rw [MonoidHom.mem_ker, map_mul, map_inv, hN, inv_mul_cancel]

private theorem exists_eventually_eq_of_eventually_mem_finite {β : Type} (U : Ultrafilter ℕ) (g : ℕ → β) (A : Set β) (hA : A.Finite)
    (hg : ∀ᶠ N in (U : Filter ℕ), g N ∈ A) : ∃ c ∈ A, ∀ᶠ N in (U : Filter ℕ), g N = c := by
  have h : (⋃ c ∈ A, {N | g N = c}) ∈ (U : Filter ℕ) := by
    filter_upwards [hg] with N hN
    exact Set.mem_biUnion hN rfl
  exact (Ultrafilter.finite_biUnion_mem_iff hA).1 h

private theorem continuous_section_quotient_of_ker_le_open {Ph G : Type} [Group Ph] [TopologicalSpace Ph] [IsTopologicalGroup Ph]
    [CompactSpace Ph] [Group G] [TopologicalSpace G] [T2Space G] (π : Ph →* G) (hπ : Continuous π)
    (σ : G → Ph) (hσ : ∀ γ, π (σ γ) = γ) (S : Subgroup Ph) (hS : IsOpen (S : Set Ph))
    (hk : π.ker ≤ S) : Continuous (fun γ => (σ γ : Ph ⧸ S)) := by
  haveI : DiscreteTopology (Ph ⧸ S) := QuotientGroup.discreteTopology hS
  have hmk : Continuous (QuotientGroup.mk : Ph → Ph ⧸ S) := continuous_quot_mk
  have key : ∀ s : Set (Ph ⧸ S), (fun γ => (σ γ : Ph ⧸ S)) ⁻¹' s =
      π '' ((QuotientGroup.mk : Ph → Ph ⧸ S) ⁻¹' s) := by
    intro s
    ext γ
    constructor
    · intro h
      exact ⟨σ γ, h, hσ γ⟩
    · rintro ⟨a, ha, rfl⟩
      have e : (σ (π a) : Ph ⧸ S) = (a : Ph ⧸ S) := by
        rw [QuotientGroup.eq]
        apply hk
        rw [MonoidHom.mem_ker, map_mul, map_inv, hσ, inv_mul_cancel]
      simp only [Set.mem_preimage, e]
      exact ha
  rw [continuous_discrete_rng]
  intro z
  have hc : IsClosed (π '' ((QuotientGroup.mk : Ph → Ph ⧸ S) ⁻¹' {z}ᶜ)) :=
    hπ.isClosedMap _ ((isClosed_discrete ({z}ᶜ : Set (Ph ⧸ S))).preimage hmk)
  rw [← key, Set.preimage_compl] at hc
  exact isClosed_compl_iff.1 hc

private theorem mul_one_sub_add_psi_eq_of_conj {Ph Y : Type} [Group Ph] [TopologicalSpace Ph] [IsTopologicalGroup Ph]
    [CompactSpace Ph] [Group Y] [TopologicalSpace Y] [IsTopologicalGroup Y]
    {Γ : ℕ → Type} [∀ N, Group (Γ N)] [∀ N, TopologicalSpace (Γ N)] [∀ N, T2Space (Γ N)]
    (π : ∀ N, Ph →* Γ N) (hπ : ∀ N, Continuous (π N))
    (σ : ∀ N, Γ N → Ph) (hσ : ∀ N γ, π N (σ N γ) = γ)
    (U : Ultrafilter ℕ) (P : Subgroup Y) [P.Normal] (f : ∀ N, Y →* Γ N)
    (hP : TopFG (Y ⧸ P)) (hf : ∀ N, Continuous (f N) ∧ P ≤ (f N).ker)
    (V : OpenNormalSubgroup Ph) :
    ∃ S : Subgroup Ph, IsOpen (S : Set Ph) ∧ ∃ c : Y → Ph ⧸ S, Continuous c ∧
      ∀ᶠ N in (U : Filter ℕ), (π N).ker ⊔ (V.toOpenSubgroup : Subgroup Ph) = S ∧
        ∀ y, ((σ N (f N y) : Ph) : Ph ⧸ S) = c y := by
  set W : Subgroup Ph := (V.toOpenSubgroup : Subgroup Ph) with hW
  have hWo : IsOpen (W : Set Ph) := V.toOpenSubgroup.isOpen
  haveI : Finite (Ph ⧸ W) := Subgroup.quotient_finite_of_isOpen W hWo
  have hmem : ∀ S : Subgroup Ph, W ≤ S → ∀ x : Ph,
      x ∈ S ↔ (x : Ph ⧸ W) ∈ (QuotientGroup.mk : Ph → Ph ⧸ W) '' (S : Set Ph) := by
    intro S hS x
    constructor
    · intro hx
      exact ⟨x, hx, rfl⟩
    · rintro ⟨s, hs, he⟩
      rw [QuotientGroup.eq] at he
      have e : x = s * (s⁻¹ * x) := by group
      rw [e]
      exact S.mul_mem hs (hS he)
  have hA1 : {S : Subgroup Ph | W ≤ S}.Finite := by
    apply Set.Finite.of_finite_image (f := fun S : Subgroup Ph =>
      (QuotientGroup.mk : Ph → Ph ⧸ W) '' (S : Set Ph)) (Set.toFinite _)
    intro S1 h1 S2 h2 he
    ext x
    rw [hmem S1 h1, hmem S2 h2]
    simp only at he
    rw [he]
  obtain ⟨S, hWS, hS⟩ := exists_eventually_eq_of_eventually_mem_finite U (fun N => (π N).ker ⊔ W) _ hA1
    (Filter.Eventually.of_forall fun N => show W ≤ (π N).ker ⊔ W from le_sup_right)
  have hSo : IsOpen (S : Set Ph) := Subgroup.isOpen_mono hWS hWo
  obtain ⟨N0, hN0⟩ := hS.exists
  haveI hSn : S.Normal := by
    rw [← hN0]
    infer_instance
  haveI : DiscreteTopology (Ph ⧸ S) := QuotientGroup.discreteTopology hSo
  haveI : Finite (Ph ⧸ S) := Subgroup.quotient_finite_of_isOpen S hSo
  have hΦ := (finite_hom_of_topFG (Y ⧸ P) hP).1 (Ph ⧸ S)
  set A2 : Set (Y → Ph ⧸ S) := {φ | Continuous φ ∧
    ∃ θ ∈ {θ : Y ⧸ P →* Ph ⧸ S | IsOpen (θ.ker : Set (Y ⧸ P))},
      φ = fun y : Y => θ (y : Y ⧸ P)} with hA2
  have hA2f : A2.Finite := by
    apply (hΦ.image (fun θ : Y ⧸ P →* Ph ⧸ S => fun y : Y => θ (y : Y ⧸ P))).subset
    rintro φ ⟨-, θ, hθ, rfl⟩
    exact ⟨θ, hθ, rfl⟩
  have hg2 : ∀ᶠ N in (U : Filter ℕ), (fun y => ((σ N (f N y) : Ph) : Ph ⧸ S)) ∈ A2 := by
    filter_upwards [hS] with N hN
    have kle : (π N).ker ≤ S := hN ▸ le_sup_left
    have hcont : Continuous (fun y => ((σ N (f N y) : Ph) : Ph ⧸ S)) :=
      (continuous_section_quotient_of_ker_le_open (π N) (hπ N) (σ N) (hσ N) S hSo kle).comp (hf N).1
    refine ⟨hcont, ?_⟩
    let φY : Y →* Ph ⧸ S := MonoidHom.mk' (fun y => ((σ N (f N y) : Ph) : Ph ⧸ S)) (by
      intro a b
      rw [← QuotientGroup.mk_mul, QuotientGroup.eq]
      apply kle
      simp [MonoidHom.mem_ker, hσ])
    have hPle : P ≤ φY.ker := by
      intro p hp
      rw [MonoidHom.mem_ker]
      show ((σ N (f N p) : Ph) : Ph ⧸ S) = 1
      rw [(hf N).2 hp, QuotientGroup.eq_one_iff]
      apply kle
      simp [MonoidHom.mem_ker, hσ]
    refine ⟨QuotientGroup.lift P φY hPle, ?_, rfl⟩
    have hpre : (QuotientGroup.mk : Y → Y ⧸ P) ⁻¹' ((QuotientGroup.lift P φY hPle).ker : Set (Y ⧸ P))
        = (fun y => ((σ N (f N y) : Ph) : Ph ⧸ S)) ⁻¹' {1} := by
      ext y
      simp [MonoidHom.mem_ker, φY]
    have ho := hcont.isOpen_preimage _ (isOpen_discrete ({1} : Set (Ph ⧸ S)))
    rw [← hpre] at ho
    have ho2 := (QuotientGroup.isOpenMap_coe (N := P)) _ ho
    rwa [Set.image_preimage_eq _ QuotientGroup.mk_surjective] at ho2
  obtain ⟨c, hcA, hc⟩ := exists_eventually_eq_of_eventually_mem_finite U _ A2 hA2f hg2
  refine ⟨S, hSo, c, hcA.1, ?_⟩
  filter_upwards [hS, hc] with N h1 h2
  exact ⟨h1, fun y => congrFun h2 y⟩

theorem UpperTheory.V.Pa.in_lim :
    ∀ (Ph Y : Type) [Group Ph] [TopologicalSpace Ph] [IsTopologicalGroup Ph] [CompactSpace Ph] [TotallyDisconnectedSpace Ph] [Group Y] [TopologicalSpace Y] [IsTopologicalGroup Y] [CompactSpace Y] [TotallyDisconnectedSpace Y] (Γ : ℕ → Type) [∀ N, Group (Γ N)] [∀ N, TopologicalSpace (Γ N)] [∀ N, IsTopologicalGroup (Γ N)] [∀ N, CompactSpace (Γ N)] [∀ N, TotallyDisconnectedSpace (Γ N)] (π : ∀ N, Ph →* Γ N) (U : Ultrafilter ℕ) (P : Subgroup Y) [P.Normal] (f : ∀ N, Y →* Γ N), (∀ N, Continuous (π N) ∧ Function.Surjective (π N)) → TopFG (Y ⧸ P) → (∀ N, Continuous (f N) ∧ P ≤ (f N).ker) → ∃ F : Y →* Ph ⧸ limKer (U : Filter ℕ) (fun N => (π N).ker), Continuous F ∧ ∀ V : OpenNormalSubgroup Ph, ∀ᶠ N in (U : Filter ℕ), ∀ y, Close (π N) (QuotientGroup.mk' (limKer (U : Filter ℕ) fun N => (π N).ker)) V.toSubgroup (f N y) (F y) := by
  intro Ph Y _ _ _ _ _ _ _ _ _ _ Γ _ _ _ _ _ π U P _ f hπ hP hf
  haveI : ∀ N, T2Space (Γ N) := fun N => inferInstance
  choose σ hσ using fun N (γ : Γ N) => (hπ N).2 γ
  choose h hh using fun y => exists_tendsto_ultrafilter_of_compact U (fun N => σ N (f N y))
  have hmul : ∀ a b, ((h (a * b) : Ph) : Ph ⧸ limKer (U : Filter ℕ) fun N => (π N).ker) =
      (h a : Ph ⧸ limKer (U : Filter ℕ) fun N => (π N).ker) * (h b) := by
    intro a b
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq]
    refine inv_mul_mem_limKer_of_tendsto_of_eventually_eq π U _ _ _ _ (hh (a * b)) ((hh a).mul (hh b)) ?_
    filter_upwards with N
    simp [hσ, map_mul]
  refine ⟨MonoidHom.mk' (fun y => (h y : Ph ⧸ limKer (U : Filter ℕ) fun N => (π N).ker)) hmul, ?_, ?_⟩
  · apply continuous_of_continuousAt_one
    rw [ContinuousAt, map_one, Filter.tendsto_def]
    intro W hW
    have hmkc : Continuous (QuotientGroup.mk : Ph → Ph ⧸ limKer (U : Filter ℕ) fun N => (π N).ker) :=
      continuous_quot_mk
    have h1 : (QuotientGroup.mk : Ph → Ph ⧸ limKer (U : Filter ℕ) fun N => (π N).ker) ⁻¹' W ∈ nhds (1 : Ph) :=
      hmkc.continuousAt.preimage_mem_nhds (by rw [QuotientGroup.mk_one]; exact hW)
    obtain ⟨t, ht, hto, ht1⟩ := mem_nhds_iff.1 h1
    obtain ⟨V, hV⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hto ht1
    obtain ⟨S, hSo, c, hc, hev⟩ := mul_one_sub_add_psi_eq_of_conj π (fun N => (hπ N).1) σ hσ U P f hP hf V
    haveI : DiscreteTopology (Ph ⧸ S) := QuotientGroup.discreteTopology hSo
    rw [mem_nhds_iff]
    refine ⟨c ⁻¹' {c 1}, ?_, hc.isOpen_preimage _ (isOpen_discrete _), rfl⟩
    intro y hy
    have hin : ∀ᶠ N in (U : Filter ℕ),
        σ N (f N y) ∈ (π N).ker ⊔ (V.toOpenSubgroup : Subgroup Ph) := by
      filter_upwards [hev] with N hN
      obtain ⟨hN, hcN⟩ := hN
      have e1 : ((σ N (f N y) : Ph) : Ph ⧸ S) = ((σ N (f N 1) : Ph) : Ph ⧸ S) := by
        rw [hcN y, hcN 1]
        exact hy
      rw [QuotientGroup.eq] at e1
      have hk1 : σ N (f N 1) ∈ (π N).ker := by simp [MonoidHom.mem_ker, hσ]
      have e2 : σ N (f N y) = σ N (f N 1) * ((σ N (f N 1))⁻¹ * σ N (f N y)) := by group
      rw [e2]
      refine Subgroup.mul_mem _ (Subgroup.mem_sup_left hk1) ?_
      rw [hN]
      simpa using S.inv_mem e1
    have hdec : ∀ N, ∃ v ∈ (V.toOpenSubgroup : Subgroup Ph),
        σ N (f N y) ∈ (π N).ker ⊔ (V.toOpenSubgroup : Subgroup Ph) →
          σ N (f N y) * v⁻¹ ∈ (π N).ker := by
      intro N
      by_cases hm : σ N (f N y) ∈ (π N).ker ⊔ (V.toOpenSubgroup : Subgroup Ph)
      · rw [← SetLike.mem_coe, Subgroup.mul_normal] at hm
        obtain ⟨k, hk, v, hv, hkv⟩ := hm
        refine ⟨v, hv, fun _ => ?_⟩
        rw [← hkv, mul_inv_cancel_right]
        exact hk
      · exact ⟨1, one_mem _, fun h' => absurd h' hm⟩
    choose v hvV hv using hdec
    obtain ⟨w, hw⟩ := exists_tendsto_ultrafilter_of_compact U v
    have hwV : w ∈ (V.toOpenSubgroup : Subgroup Ph) :=
      V.toOpenSubgroup.isClosed.mem_of_tendsto hw (Filter.Eventually.of_forall hvV)
    have hlim := inv_mul_mem_limKer_of_tendsto_of_eventually_eq π U (fun N => σ N (f N y) * (v N)⁻¹) (fun _ => 1) (h y * w⁻¹) 1
      ((hh y).mul hw.inv) tendsto_const_nhds (by
        filter_upwards [hin] with N hN
        rw [map_one]
        exact (MonoidHom.mem_ker).1 (hv N hN))
    have hm' : h y * w⁻¹ ∈ limKer (U : Filter ℕ) (fun N => (π N).ker) := by
      simpa using inv_mem hlim
    have hconj := (limKer_normal (U : Filter ℕ) (fun N => (π N).ker)).conj_mem _ hm' w⁻¹
    have e3 : w⁻¹ * (h y * w⁻¹) * w⁻¹⁻¹ = w⁻¹ * h y := by group
    rw [e3] at hconj
    show ((h y : Ph) : Ph ⧸ limKer (U : Filter ℕ) fun N => (π N).ker) ∈ W
    have e4 : ((h y : Ph) : Ph ⧸ limKer (U : Filter ℕ) fun N => (π N).ker) =
        ((w : Ph) : Ph ⧸ limKer (U : Filter ℕ) fun N => (π N).ker) := by
      rw [QuotientGroup.eq]
      simpa using inv_mem hconj
    rw [e4]
    exact ht (hV hwV)
  · intro V
    obtain ⟨S, hSo, c, hc, hev⟩ := mul_one_sub_add_psi_eq_of_conj π (fun N => (hπ N).1) σ hσ U P f hP hf V
    have hVS : ∀ᶠ N in (U : Filter ℕ), (V.toOpenSubgroup : Subgroup Ph) ≤ S := by
      filter_upwards [hev] with N hN
      rw [← hN.1]
      exact le_sup_right
    have hcy : ∀ y, c y = ((h y : Ph) : Ph ⧸ S) := by
      intro y
      have hO : ((V.toOpenSubgroup : Subgroup Ph) : Set Ph) ∈ nhds (1 : Ph) :=
        V.toOpenSubgroup.isOpen.mem_nhds V.toOpenSubgroup.one_mem
      have ht : Tendsto (fun N => (σ N (f N y))⁻¹ * h y) (U : Filter ℕ) (nhds 1) := by
        simpa using (hh y).inv.mul (tendsto_const_nhds (x := h y))
      obtain ⟨N, ⟨-, hN⟩, hle, hmemN⟩ := (hev.and (hVS.and (ht hO))).exists
      rw [← hN y, QuotientGroup.eq]
      exact hle hmemN
    filter_upwards [hev] with N hN
    obtain ⟨hN, hcN⟩ := hN
    intro y
    have e1 : ((σ N (f N y) : Ph) : Ph ⧸ S) = ((h y : Ph) : Ph ⧸ S) := by rw [hcN y, hcy y]
    rw [QuotientGroup.eq, ← hN, ← SetLike.mem_coe, Subgroup.mul_normal] at e1
    obtain ⟨k, hk, v, hv, hkv⟩ := e1
    refine ⟨σ N (f N y) * k, h y, ?_, rfl, ?_⟩
    · rw [map_mul, hσ, (MonoidHom.mem_ker).1 hk, mul_one]
    · have e : (σ N (f N y) * k)⁻¹ * h y = k⁻¹ * ((σ N (f N y))⁻¹ * h y) := by group
      rw [e, ← hkv, inv_mul_cancel_left]
      exact hv
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.CloseMap
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

theorem UpperTheory.V.Pa.close_map :
    ∀ (Ph B Z : Type) [Group Ph] [TopologicalSpace Ph] [IsTopologicalGroup Ph] [CompactSpace Ph] [TotallyDisconnectedSpace Ph] [Group B] [Group Z] [TopologicalSpace Z] [IsTopologicalGroup Z] [CompactSpace Z] [TotallyDisconnectedSpace Z] (Γ : ℕ → Type) [∀ N, Group (Γ N)] (π : ∀ N, Ph →* Γ N) (πo : Ph →* B) (p : ∀ N, Γ N →* Z) (po : B →* Z) (U : Ultrafilter ℕ) (a : ∀ N, Γ N) (b : B) (z : Z), Continuous (po.comp πo) → (∀ W : OpenNormalSubgroup Z, ∀ᶠ N in (U : Filter ℕ), ∀ g, p N (π N g) * (po (πo g))⁻¹ ∈ W) → (∀ V : OpenNormalSubgroup Ph, ∀ᶠ N in (U : Filter ℕ), Close (π N) πo V.toSubgroup (a N) b) → (∀ W : OpenNormalSubgroup Z, ∀ᶠ N in (U : Filter ℕ), p N (a N) * z⁻¹ ∈ W) → po b = z := by
  intro Ph B Z _ _ _ _ _ _ _ _ _ _ _ Γ _ π πo p po U a b z hf hp hclose ha
  set f : Ph →* Z := po.comp πo with hfdef
  have key : ∀ W : OpenNormalSubgroup Z, po b * z⁻¹ ∈ W := by
    intro W
    let V : OpenNormalSubgroup Ph :=
      { toOpenSubgroup := ⟨W.toSubgroup.comap f, W.isOpen.preimage hf⟩
        isNormal' := Subgroup.Normal.comap W.isNormal' f }
    obtain ⟨N, h1, h2, h3⟩ := ((hp W).and ((hclose V).and (ha W))).exists
    obtain ⟨g, g', hg, hg', hV⟩ := h2
    have hV' : f (g⁻¹ * g') ∈ W := hV
    have e1 := h1 g
    rw [hg] at e1
    have hb : po b = f g' := by simp [hfdef, hg']
    have hn : f g' * (f g)⁻¹ ∈ W := by
      have hc := W.isNormal'.conj_mem _ hV' (f g)
      have he : f g * f (g⁻¹ * g') * (f g)⁻¹ = f g' * (f g)⁻¹ := by
        simp [map_mul, map_inv, mul_assoc]
      rw [he] at hc
      exact hc
    have hx : po b * z⁻¹ = (f g' * (f g)⁻¹) * (p N (a N) * (f g)⁻¹)⁻¹ * (p N (a N) * z⁻¹) := by
      rw [hb]; group
    rw [hx]
    exact W.mul_mem (W.mul_mem hn (W.inv_mem e1)) h3
  by_contra hne
  have hx1 : po b * z⁻¹ ≠ 1 := fun h => hne (mul_inv_eq_one.mp h)
  obtain ⟨H, hH⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
    (isOpen_compl_singleton (x := po b * z⁻¹)) (by simpa [eq_comm] using hx1)
  exact hH (key H) rfl
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.EltLim
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

theorem UpperTheory.V.Pa.elt_lim :
    ∀ (Ph B : Type) [Group Ph] [TopologicalSpace Ph] [IsTopologicalGroup Ph] [CompactSpace Ph] [TotallyDisconnectedSpace Ph] [Group B] (Γ : ℕ → Type) [∀ N, Group (Γ N)] (π : ∀ N, Ph →* Γ N) (πo : Ph →* B) (U : Ultrafilter ℕ) (a : ∀ N, Γ N), (∀ N, Function.Surjective (π N)) → ∃ b : B, ∀ V : OpenNormalSubgroup Ph, ∀ᶠ N in (U : Filter ℕ), Close (π N) πo V.toSubgroup (a N) b := by
  intro Ph B _ _ _ _ _ _ Γ _ π πo U a hπ
  choose g hg using fun N => hπ N (a N)
  obtain ⟨b, hb⟩ := (exists_lim_elt Ph ℕ U fun N => (π N).ker).1 g
  refine ⟨πo b, fun V => (hb V).mono fun N h => ⟨g N, b, hg N, rfl, ?_⟩⟩
  simpa using V.toSubgroup.inv_mem h
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.CommLim
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem eventually_le_of_le_atTop {U : Filter ℕ} (h : U ≤ atTop) (n : ℕ) : ∀ᶠ N in U, n ≤ N :=
  h (eventually_ge_atTop n)

theorem UpperTheory.V.Pa.comm_lim :
    ∀ (l : ℕ) [Fact l.Prime] (Ph B : Type) [Group Ph] [TopologicalSpace Ph] [IsTopologicalGroup Ph] [CompactSpace Ph] [TotallyDisconnectedSpace Ph] [Group B] [TopologicalSpace B] [IsTopologicalGroup B] [CompactSpace B] [TotallyDisconnectedSpace B] (Γ : ℕ → Type) [∀ N, Group (Γ N)] [∀ N, TopologicalSpace (Γ N)] [∀ N, IsTopologicalGroup (Γ N)] [∀ N, CompactSpace (Γ N)] [∀ N, TotallyDisconnectedSpace (Γ N)] (π : ∀ N, Ph →* Γ N) (πo : Ph →* B) (U : Ultrafilter ℕ) (ph ta : ∀ N, Γ N) (q : ℕ → ℕ) (a b : B), (U : Filter ℕ) ≤ atTop → (∀ N, Continuous (π N) ∧ Function.Surjective (π N)) → Continuous πo → (∀ V : OpenNormalSubgroup Ph, ∀ᶠ N in (U : Filter ℕ), (π N).ker ⊔ V.toSubgroup = πo.ker ⊔ V.toSubgroup) → (∀ V : OpenNormalSubgroup Ph, ∀ᶠ N in (U : Filter ℕ), Close (π N) πo V.toSubgroup (ph N) a) → (∀ V : OpenNormalSubgroup Ph, ∀ᶠ N in (U : Filter ℕ), Close (π N) πo V.toSubgroup (ta N) b) → (∀ N, q N ≡ 1 [MOD l ^ N]) → (∀ N, (ph N)⁻¹ * ta N * ph N = ta N ^ q N) → (∀ N (W : OpenNormalSubgroup (Γ N)), ∃ e : ℕ, ta N ^ l ^ e ∈ W) → a * b = b * a := by
  intro l _ Ph B _ _ _ _ _ _ _ _ _ _ Γ _ _ _ _ _ π πo U ph ta q a b hUa hπ hπo hker hph hta hq hrel hlw
  have hl : l.Prime := Fact.out
  have key : ∀ W : OpenNormalSubgroup B, (a * b)⁻¹ * (b * a) ∈ W.toSubgroup := by
    intro W
    haveI : W.toSubgroup.Normal := W.isNormal'
    haveI : Finite (B ⧸ W.toSubgroup) :=
      W.toSubgroup.quotient_finite_of_isOpen W.toOpenSubgroup.isOpen
    haveI : W.toSubgroup.FiniteIndex := W.toSubgroup.finiteIndex_of_finite_quotient
    have hn0 : W.toSubgroup.index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
    let V : OpenNormalSubgroup Ph :=
      { toOpenSubgroup := ⟨W.toSubgroup.comap πo, W.toOpenSubgroup.isOpen.preimage hπo⟩
        isNormal' := Subgroup.Normal.comap W.isNormal' πo }
    have hVmem : ∀ x, x ∈ V.toSubgroup ↔ πo x ∈ W.toSubgroup := fun x => Iff.rfl
    obtain ⟨N, hNn, hk, h1, h2⟩ := ((eventually_le_of_le_atTop hUa W.toSubgroup.index).and
      ((hker V).and ((hph V).and (hta V)))).exists
    obtain ⟨g1, g1', e1, e1', hg1⟩ := h1
    obtain ⟨g2, g2', e2, e2', hg2⟩ := h2
    have hkV : (π N).ker ≤ V.toSubgroup := by
      have : (π N).ker ≤ πo.ker ⊔ V.toSubgroup := hk ▸ le_sup_left
      refine this.trans (sup_le ?_ le_rfl)
      intro x hx
      rw [hVmem, MonoidHom.mem_ker.mp hx]
      exact W.toSubgroup.one_mem
    set mk : B →* B ⧸ W.toSubgroup := QuotientGroup.mk' W.toSubgroup with hmk
    have eqmk : ∀ x y : Ph, x⁻¹ * y ∈ V.toSubgroup → mk (πo x) = mk (πo y) := by
      intro x y h
      rw [hmk, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
      have := (hVmem _).mp h
      simpa [map_mul, map_inv] using this
    have hA : mk (πo g1) = mk a := by rw [← e1']; exact eqmk _ _ hg1
    have hB : mk (πo g2) = mk b := by rw [← e2']; exact eqmk _ _ hg2
    have hrelq : (mk a)⁻¹ * mk b * mk a = mk b ^ q N := by
      have hk1 : (g1⁻¹ * g2 * g1) ⁻¹ * g2 ^ q N ∈ V.toSubgroup := by
        apply hkV
        rw [MonoidHom.mem_ker]
        simp only [map_mul, map_inv, map_pow, e1, e2, hrel N]
        group
      have := eqmk _ _ hk1
      simp only [map_mul, map_inv, map_pow, hA, hB] at this
      exact this
    have hW'ex : ∃ W' : OpenNormalSubgroup (Γ N), ∀ x, π N x ∈ W'.toSubgroup → x ∈ V.toSubgroup := by
      have hVc : IsClosed ((V.toSubgroup : Set Ph)ᶜ) := V.toOpenSubgroup.isOpen.isClosed_compl
      have hcm : IsClosedMap (π N) := (hπ N).1.isClosedMap
      have hS : IsOpen ((π N '' (V.toSubgroup : Set Ph)ᶜ)ᶜ) := (hcm _ hVc).isOpen_compl
      have h1S : (1 : Γ N) ∈ (π N '' (V.toSubgroup : Set Ph)ᶜ)ᶜ := by
        rintro ⟨x, hx, hx1⟩
        exact hx (hkV (MonoidHom.mem_ker.mpr hx1))
      obtain ⟨W', hW'⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hS h1S
      refine ⟨W', fun x hx => ?_⟩
      by_contra hxV
      exact hW' hx ⟨x, hxV, rfl⟩
    obtain ⟨W', hW'⟩ := hW'ex
    obtain ⟨e, he⟩ := hlw N W'
    have hbe : mk b ^ l ^ e = 1 := by
      have h3 : g2 ^ l ^ e ∈ V.toSubgroup := hW' _ (by rw [map_pow, e2]; exact he)
      have h' := eqmk 1 (g2 ^ l ^ e) (by simpa using h3)
      simp only [map_one, map_pow, hB] at h'
      exact h'.symm
    have hbn : mk b ^ W.toSubgroup.index = 1 := by
      rw [← map_pow, hmk, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact W.toSubgroup.pow_index_mem b
    obtain ⟨c, -, hc⟩ := (Nat.dvd_prime_pow hl).mp (orderOf_dvd_of_pow_eq_one hbe)
    have hc1 : l ^ c ≤ W.toSubgroup.index := by
      rw [← hc]
      exact Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) (orderOf_dvd_of_pow_eq_one hbn)
    have hc2 : c < l ^ c := Nat.lt_pow_self hl.one_lt
    have hdiv : orderOf (mk b) ∣ l ^ N := by
      rw [hc]
      exact pow_dvd_pow l (by omega)
    have hbq : mk b ^ q N = mk b := by
      have h4 : q N ≡ 1 [MOD orderOf (mk b)] := Nat.ModEq.of_dvd hdiv (hq N)
      simpa using pow_eq_pow_iff_modEq.mpr h4
    have hcomm : mk a * mk b = mk b * mk a := by
      rw [hbq] at hrelq
      calc mk a * mk b = mk a * ((mk a)⁻¹ * mk b * mk a) := by rw [hrelq]
        _ = mk b * mk a := by group
    have h5 : mk (a * b) = mk (b * a) := by simp only [map_mul, hcomm]
    rw [hmk, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at h5
    exact h5
  by_contra hne
  have hx1 : (a * b)⁻¹ * (b * a) ≠ 1 := fun h => hne (inv_mul_eq_one.mp h)
  obtain ⟨H, hH⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
    (isOpen_compl_singleton (x := (a * b)⁻¹ * (b * a))) (by simpa [eq_comm] using hx1)
  exact hH (key H) rfl
end

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

theorem UpperTheory.V.Pa.selmer_cocycles_limit_and_descent_properties :
    S4 := by
  intro l _ L G0 T hT
  obtain ⟨Ph, i1, i2, i3, i4, i5, π, ct, hfg, hπ, hcomp⟩ := sys_cover l L G0 T hT
  let U : Ultrafilter ℕ := Filter.hyperfilter ℕ
  have hU : (U : Filter ℕ) ≤ atTop := by
    rw [← Nat.cofinite_eq_atTop]
    exact Filter.hyperfilter_le_cofinite
  set K : Subgroup Ph := limKer (U : Filter ℕ) (fun N => (π N).ker) with hK
  have hKs := limKer_sup Ph ℕ U (fun N => (π N).ker)
  haveI : TotallyDisconnectedSpace (Ph ⧸ K) := (totallyDisconnected_quot Ph K hKs.1).1
  have sep : ∀ z : G0.Γ, (∀ W : OpenNormalSubgroup G0.Γ, z ∈ (W : Subgroup G0.Γ)) → z = 1 := by
    intro z hz
    have h1 := (totallyDisconnected_quot G0.Γ ⊥ (by simpa using isClosed_singleton)).2 z
      (fun O => by simpa using hz O)
    simpa using h1
  have swapW : ∀ (W : OpenNormalSubgroup G0.Γ) (a b : G0.Γ),
      b⁻¹ * a ∈ (W : Subgroup G0.Γ) → a * b⁻¹ ∈ (W : Subgroup G0.Γ) := by
    intro W a b h
    exact (Subgroup.Normal.mem_comm_iff inferInstance).1 h
  obtain ⟨F0, hF0c, hF0k, hF0u, hF0s⟩ := exists_lim_hom_out Ph G0.Γ ℕ hfg U (fun N => (π N).ker)
    (fun N => (T.h N).p.comp (π N)) (fun N => (T.h N).cont.comp (hπ N).1)
    (fun N x hx => by simp_all [MonoidHom.mem_ker])
  let hp : Ph ⧸ K →* G0.Γ := QuotientGroup.lift K F0 hF0k
  have hp_mk : ∀ g, hp (QuotientGroup.mk g) = F0 g := fun g => rfl
  have hp_cont : Continuous hp := by
    refine (QuotientGroup.isQuotientMap_mk K).continuous_iff.2 ?_
    exact hF0c
  have hp_surj : Function.Surjective hp := by
    intro z
    obtain ⟨g, rfl⟩ := hF0s (fun N => ((T.h N).surj.comp (hπ N).2.1)) z
    exact ⟨_, hp_mk g⟩
  have unif : ∀ W : OpenNormalSubgroup G0.Γ, ∀ᶠ N in (U : Filter ℕ),
      ∀ g : Ph, (T.h N).p (π N g) * (hp (QuotientGroup.mk' K g))⁻¹ ∈ (W : Subgroup G0.Γ) := by
    intro W
    filter_upwards [hF0u W] with N hN g
    exact swapW W _ _ (hN g)
  have hct : hp (QuotientGroup.mk' K ct) = G0.c := by
    have h1 : ∀ W : OpenNormalSubgroup G0.Γ, (F0 ct)⁻¹ * G0.c ∈ (W : Subgroup G0.Γ) := by
      intro W
      obtain ⟨N, hN⟩ := (hF0u W).exists
      have h2 := hN ct
      simpa [(hπ N).2.2, (T.h N).c] using h2
    have h3 := sep _ h1
    exact (inv_mul_eq_one.1 h3)
  have modH : ∀ N (g : Ph), (T.h N).p (π N g) * (hp (QuotientGroup.mk' K g))⁻¹ ∈ (T.H : Subgroup G0.Γ) := by
    intro N g
    obtain ⟨M, hM⟩ := (unif T.H).exists
    have h1 := Subgroup.mul_mem _ (hcomp N M g) (hM g)
    simpa [mul_assoc] using h1
  have lift : ∀ (Y : Type) [Group Y] [TopologicalSpace Y] [IsTopologicalGroup Y] [CompactSpace Y]
      [TotallyDisconnectedSpace Y], PhiCond Y l → ∀ (f : ∀ N, Y →* (T.GN N).Γ) (f0 : Y →* G0.Γ),
      (∀ N, Continuous (f N)) → Continuous f0 → (∀ N y, (T.h N).p (f N y) = f0 y) →
      ∃ F : Y →* Ph ⧸ K, Continuous F ∧
        (∀ V : OpenNormalSubgroup Ph, ∀ᶠ N in (U : Filter ℕ), ∀ y,
          Close (π N) (QuotientGroup.mk' K) (V : Subgroup Ph) (f N y) (F y)) ∧
        ∀ y, hp (F y) = f0 y := by
    intro Y _ _ _ _ _ hphi f f0 hfc hf0c hf
    obtain ⟨P, hPn, hPfg, hPker⟩ := loc_fin l Y (Subgroup.comap f0 (T.H : Subgroup G0.Γ))
      (T.H.toOpenSubgroup.isOpen.preimage hf0c) hphi
    obtain ⟨F, hFc, hFconv⟩ := in_lim Ph Y (fun N => (T.GN N).Γ) π U P f
      (fun N => ⟨(hπ N).1, (hπ N).2.1⟩) hPfg
      (fun N => ⟨hfc N, hPker _ (f N) (Subgroup.comap (T.h N).p (T.H : Subgroup G0.Γ)) (hfc N) (hT.2 N)
        (fun y hy => by simpa [Subgroup.mem_comap, hf] using hy)⟩)
    refine ⟨F, hFc, hFconv, fun y => ?_⟩
    refine close_map Ph (Ph ⧸ K) G0.Γ (fun N => (T.GN N).Γ) π (QuotientGroup.mk' K) (fun N => (T.h N).p) hp U
      (fun N => f N y) (F y) (f0 y) (hp_cont.comp continuous_quot_mk) unif
      (fun V => (hFconv V).mono fun N h => h y) (fun W => Filter.Eventually.of_forall fun N => ?_)
    simp [hf]
  have hv := fun v => lift (L.Gv v) (T.phiV v) (fun N => (T.GN N).η.ker.subtype.comp ((T.GN N).φ v))
    (G0.η.ker.subtype.comp (G0.φ v)) (fun N => continuous_subtype_val.comp ((T.GN N).φ_cont v))
    (continuous_subtype_val.comp (G0.φ_cont v)) (fun N y => (T.h N).φ v y)
  choose Fv hFvc hFvconv hFvp using hv
  have hu := fun u => lift (L.Gu u) (T.phiU u) (fun N => (T.GN N).η.ker.subtype.comp ((T.GN N).φu u))
    (G0.η.ker.subtype.comp (G0.φu u)) (fun N => continuous_subtype_val.comp ((T.GN N).φu_cont u))
    (continuous_subtype_val.comp (G0.φu_cont u)) (fun N y => (T.h N).φu u y)
  choose Fu hFuc hFuconv hFup using hu
  have memv : ∀ v y, Fv v y ∈ (G0.η.comp hp).ker := by
    intro v y
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, hFvp v y]
    exact (G0.φ v y).2
  have memu : ∀ u y, Fu u y ∈ (G0.η.comp hp).ker := by
    intro u y
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, hFup u y]
    exact (G0.φu u y).2
  let G : Glob l L :=
    { Γ := Ph ⧸ K
      η := G0.η.comp hp
      η_open := by
        rw [← MonoidHom.comap_ker]
        exact G0.η_open.preimage hp_cont
      c := QuotientGroup.mk' K ct
      c_sq := by
        rw [← map_mul, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        intro O
        refine Filter.Eventually.of_forall fun N => Subgroup.mem_sup_left ?_
        simp [MonoidHom.mem_ker, (hπ N).2.2, (T.GN N).c_sq]
      η_c := by
        rw [MonoidHom.comp_apply, hct, G0.η_c]
      ε := G0.ε.comp hp
      ε_cont := G0.ε_cont.comp hp_cont
      φ := fun v => (Fv v).codRestrict _ (memv v)
      φ_cont := fun v => (hFvc v).subtype_mk _
      φu := fun u => (Fu u).codRestrict _ (memu u)
      φu_cont := fun u => (hFuc u).subtype_mk _ }
  let h : G.Hom G0 :=
    { p := hp
      cont := hp_cont
      surj := hp_surj
      η := fun g => rfl
      c := hct
      ε := fun g => rfl
      φ := fun v g => hFvp v g
      φu := fun u g => hFup u g }
  have hPL : ∀ (W : OpenNormalSubgroup G0.Γ), PL l (T.H : Subgroup G0.Γ) ≤ (W : Subgroup G0.Γ) := by
    intro W
    rw [hT.1]
    exact bot_le
  have eph : ∀ j : Fin T.q, ∃ b : Ph ⧸ K, (∀ V : OpenNormalSubgroup Ph, ∀ᶠ N in (U : Filter ℕ),
      Close (π N) (QuotientGroup.mk' K) (V : Subgroup Ph) ((T.ph N j : (T.GN N).Γ)) b) ∧
      hp b = (T.sg j : G0.Γ) := by
    intro j
    obtain ⟨b, hb⟩ := elt_lim Ph (Ph ⧸ K) (fun N => (T.GN N).Γ) π (QuotientGroup.mk' K) U
      (fun N => (T.ph N j : (T.GN N).Γ)) (fun N => (hπ N).2.1)
    refine ⟨b, hb, ?_⟩
    exact close_map Ph (Ph ⧸ K) G0.Γ (fun N => (T.GN N).Γ) π (QuotientGroup.mk' K) (fun N => (T.h N).p) hp U
      (fun N => (T.ph N j : (T.GN N).Γ)) b _ (hp_cont.comp continuous_quot_mk) unif hb
      (fun W => hU (T.ph_lim W j (hPL W)))
  have eta : ∀ j : Fin T.q, ∃ b : Ph ⧸ K, (∀ V : OpenNormalSubgroup Ph, ∀ᶠ N in (U : Filter ℕ),
      Close (π N) (QuotientGroup.mk' K) (V : Subgroup Ph) ((T.ta N j : (T.GN N).Γ)) b) ∧
      hp b = 1 := by
    intro j
    obtain ⟨b, hb⟩ := elt_lim Ph (Ph ⧸ K) (fun N => (T.GN N).Γ) π (QuotientGroup.mk' K) U
      (fun N => (T.ta N j : (T.GN N).Γ)) (fun N => (hπ N).2.1)
    refine ⟨b, hb, ?_⟩
    refine close_map Ph (Ph ⧸ K) G0.Γ (fun N => (T.GN N).Γ) π (QuotientGroup.mk' K) (fun N => (T.h N).p) hp U
      (fun N => (T.ta N j : (T.GN N).Γ)) b _ (hp_cont.comp continuous_quot_mk) unif hb
      (fun W => Filter.Eventually.of_forall fun N => ?_)
    simp [T.ta_ker N j]
  choose bph hbph hbphp using eph
  choose bta hbta hbtap using eta
  have memph : ∀ j, bph j ∈ G.η.ker := by
    intro j
    show G0.η (hp (bph j)) = 1
    rw [hbphp j]
    exact (T.sg j).2
  have memta : ∀ j, bta j ∈ G.η.ker := by
    intro j
    show G0.η (hp (bta j)) = 1
    rw [hbtap j, map_one]
  have hcomm : ∀ j, bph j * bta j = bta j * bph j := by
    intro j
    refine comm_lim l Ph (Ph ⧸ K) (fun N => (T.GN N).Γ) π (QuotientGroup.mk' K) U
      (fun N => (T.ph N j : (T.GN N).Γ)) (fun N => (T.ta N j : (T.GN N).Γ)) (fun N => T.Nq N j)
      (bph j) (bta j) hU (fun N => ⟨(hπ N).1, (hπ N).2.1⟩) continuous_quot_mk
      (fun V => by simpa [QuotientGroup.ker_mk'] using hKs.2.1 V) (hbph j) (hbta j)
      (fun N => T.Nq_mod N j) (fun N => ?_) (fun N W => ?_)
    · have e := T.tame N j
      rw [hT.2 N, Subgroup.mem_bot, OneMemClass.coe_eq_one, inv_mul_eq_one] at e
      have e2 := congrArg Subtype.val e
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, SubmonoidClass.coe_pow] at e2
      exact e2.symm
    · have hpl := (pl_props l (T.GN N).Γ (Subgroup.comap (T.h N).p (T.H : Subgroup G0.Γ))
        (T.H.toOpenSubgroup.isOpen.preimage (T.h N).cont)).2.2.2.1 W
      refine hpl.1 (by rw [hT.2 N]; exact bot_le) _ ?_
      simp [Subgroup.mem_comap, T.ta_ker N j]
  obtain ⟨s, hs, hsg⟩ := hfg
  exact ⟨
    { Ph := Ph
      fg := ⟨hs.toFinset, by simpa [topGen_iff] using hsg⟩
      U := U
      U_le := hU
      π := π
      π_cont := fun N => (hπ N).1
      π_surj := fun N => (hπ N).2.1
      G := G
      h := h
      πo := QuotientGroup.mk' K
      πo_cont := continuous_quot_mk
      πo_surj := QuotientGroup.mk'_surjective K
      modH := modH
      ct := ct
      ct_N := fun N => (hπ N).2.2
      ct_o := rfl
      ker_lim := fun V => by
        rw [QuotientGroup.ker_mk']
        exact hKs.2.1 V
      p_lim := unif
      φ_lim := fun V => Filter.eventually_all.2 fun v => hFvconv v V
      φu_lim := fun V => Filter.eventually_all.2 fun u => hFuconv u V
      ph := fun j => ⟨bph j, memph j⟩
      ta := fun j => ⟨bta j, memta j⟩
      ph_lim := fun V => Filter.eventually_all.2 fun j => hbph j V
      ta_lim := fun V => Filter.eventually_all.2 fun j => hbta j V
      comm := fun j => Subtype.ext (hcomm j)
      p_ph := fun j => Subtype.ext (hbphp j)
      p_ta := fun j => Subtype.ext (hbtap j) }⟩
