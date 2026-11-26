module

public import GroundTheory.AutomorphicForms.GeometricLemmaCellSurjective

@[expose] public section

section -- merged from GroundTheory.AutomorphicForms.GeometricLemmaGraded
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Automorphic

namespace Parabolic

open Matrix Iwasawa GLnLocal ValuativeRel Topology Set DoubleCoset Filter

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {β γ : Fin n → ℕ} {w : Equiv.Perm (Fin n)}
  {W : Type*} [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (levi F n β) W)

section Average

theorem avgOver_mem_supportedIn {Y : Set (GL (Fin n) F)}
    (hYQ : ∀ g ∈ Y, ∀ q ∈ blockUpper F n γ, g * q ∈ Y) {K : Subgroup (GL (Fin n) F)}
    (hK : IsCompact (K : Set (GL (Fin n) F))) (hKQ : K ≤ blockUpper F n γ)
    {f : parabolicIndSpace F n β σ} (hf : f ∈ supportedIn σ Y) :
    ∃ g : parabolicIndSpace F n β σ, (g : GL (Fin n) F → W) = avgOver K f ∧ g ∈ supportedIn σ Y := by
  obtain ⟨U, hU, hUf⟩ := exists_rightStab_parabolicInd σ f
  have hfin : AvgFinite K (f : GL (Fin n) F → W) :=
    avgFinite_of_isOpen hK hU fun k hk => (mem_rightStab).2 fun x => hUf k hk x
  have hmem : avgOver K (f : GL (Fin n) F → W) ∈ parabolicIndSpace F n β σ :=
    avgOver_mem hfin fun k _ => (parabolicInd F n β σ k f).2
  refine ⟨⟨_, hmem⟩, rfl, fun g hg => ?_⟩
  show avgOver K (f : GL (Fin n) F → W) g = 0
  refine avgOver_eq_zero_of_forall fun k hk => hf _ fun hgk => hg ?_
  simpa using hYQ _ hgk _ ((blockUpper F n γ).inv_mem (hKQ hk))

theorem cellJacquet_avgOver {Y : Set (GL (Fin n) F)} (hYo : IsOpen Y)
    (hCY : closure (doubleCoset (permGL F w) (blockUpper F n β : Set (GL (Fin n) F))
      (blockUpper F n γ)) ∩ Y = doubleCoset (permGL F w) (blockUpper F n β : Set (GL (Fin n) F))
      (blockUpper F n γ))
    {K : Subgroup (GL (Fin n) F)} (hK : IsCompact (K : Set (GL (Fin n) F)))
    (hKN : K ≤ unipotentRadical F n γ)
    {f g : parabolicIndSpace F n β σ} (hf : f ∈ supportedIn σ Y) (hg : g ∈ supportedIn σ Y)
    (hgf : (g : GL (Fin n) F → W) = avgOver K f) {m : GL (Fin n) F} (hm : m ∈ levi F n γ) :
    cellJacquet γ w σ g m = cellJacquet γ w σ f m := by
  obtain ⟨e, hfe, hge⟩ := exists_cellSupp_pair σ hYo hCY hf hg hm
  have hmK : IsCompact ((K.map (MulAut.conj m).toMonoidHom : Subgroup (GL (Fin n) F)) :
      Set (GL (Fin n) F)) := by
    rw [Subgroup.coe_map]
    exact hK.image (conjHomeomorph m).continuous
  obtain ⟨e₂, he₂⟩ := exists_unipotentCompactG_of_isCompact (γ := γ) hmK (by
    rintro _ ⟨k, hk, rfl⟩
    exact conj_mem_unipotentRadical (levi_le_blockUpper hm) (hKN hk))
  set E := max e e₂
  have hE := isCellCompact_unipotentCompactG (F := F) (γ := γ) E
  rw [cellJacquet_eq_cellEv σ hYo hCY hg hm hE (hge.mono (unipotentCompactG_mono (le_max_left _ _))),
    cellJacquet_eq_cellEv σ hYo hCY hf hm hE (hfe.mono (unipotentCompactG_mono (le_max_left _ _)))]
  unfold cellEv
  obtain ⟨U, hU, hUf⟩ := exists_rightStab_parabolicInd σ f
  have hfinF : AvgFinite K (fun z => (f : GL (Fin n) F → W) (permGL F w * m * z)) := by
    refine avgFinite_of_isOpen hK hU fun k hk => (mem_rightStab).2 fun x => ?_
    rw [← mul_assoc, hUf k hk]
  have hcf : cellFun w σ g m = avgOver (K.map (MulAut.conj m).toMonoidHom) (cellFun w σ f m) := by
    funext y
    have h1 : cellFun w σ f m = fun y =>
        (fun z => (f : GL (Fin n) F → W) (permGL F w * m * z)) ((MulAut.conj m).symm y) := by
      funext y
      unfold cellFun
      rw [MulAut.conj_symm_apply]
      group
    rw [h1, avgOver_map_mulEquiv (MulAut.conj m) hfinF, avgOver_comp_mul_left]
    unfold cellFun
    rw [hgf, MulAut.conj_symm_apply]
    congr 1
    group
  have hfinC : AvgFinite (K.map (MulAut.conj m).toMonoidHom) (cellFun w σ f m) :=
    avgFinite_cellFun σ f m hmK
  rw [hcf, avgOver_avgOver (he₂.trans fun x hx => unipotentCompactG_mono (le_max_right _ _) hx)
    (avgFinite_cellFun σ f m hE.2.1)]

end Average

section Graded

variable {Y : Set (GL (Fin n) F)} (hYo : IsOpen Y)
  (hCY : closure (doubleCoset (permGL F w) (blockUpper F n β : Set (GL (Fin n) F))
    (blockUpper F n γ)) ∩ Y = doubleCoset (permGL F w) (blockUpper F n β : Set (GL (Fin n) F))
    (blockUpper F n γ))
  (hYQ : ∀ g ∈ Y, ∀ q ∈ blockUpper F n γ, g * q ∈ Y)


include hYo hCY hYQ in
theorem cellJacquet_eq_zero_of_mk_eq_zero {f : parabolicIndSpace F n β σ}
    (hf : f ∈ supportedIn σ Y)
    (h0 : Representation.Coinvariants.mk ((parabolicInd F n β σ).comp
      (unipotentRadical F n γ).subtype) f = 0) {m : GL (Fin n) F} (hm : m ∈ levi F n γ) :
    cellJacquet γ w σ f m = 0 := by
  have hx := (Representation.Coinvariants.mk_eq_zero _).1 h0
  obtain ⟨K', hK'c, -, hK'⟩ := exists_mem_coinvariantsKer _ exists_compactOpen_unipotentRadical hx
  set K : Subgroup (GL (Fin n) F) := K'.map (unipotentRadical F n γ).subtype
  have hKc : IsCompact (K : Set (GL (Fin n) F)) := by
    rw [Subgroup.coe_map]
    exact hK'c.image continuous_subtype_val
  have hKN : K ≤ unipotentRadical F n γ := by
    rintro _ ⟨k, -, rfl⟩
    exact k.2

  have hfinI : ∀ v : parabolicIndSpace F n β σ, AvgFinite K (v : GL (Fin n) F → W) := by
    intro v
    obtain ⟨U, hU, hUv⟩ := exists_rightStab_parabolicInd σ v
    exact avgFinite_of_isOpen hKc hU fun k hk => (mem_rightStab).2 fun x => hUv k hk x
  let L : parabolicIndSpace F n β σ →ₗ[ℂ] (GL (Fin n) F → W) :=
    { toFun := fun v => avgOver K (v : GL (Fin n) F → W)
      map_add' := fun v v' => by
        rw [Submodule.coe_add, avgOver_add (hfinI v) (hfinI v')]
      map_smul' := fun c v => by
        rw [Submodule.coe_smul, avgOver_smul c (hfinI v)]
        rfl }
  have hL : L f = 0 := by
    have : coinvariantsKer ((parabolicInd F n β σ).comp (unipotentRadical F n γ).subtype) K' ≤
        LinearMap.ker L := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨⟨k, v⟩, rfl⟩
      simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, sub_eq_zero]
      show avgOver K (((parabolicInd F n β σ ((k : unipotentRadical F n γ) : GL (Fin n) F) v :
        parabolicIndSpace F n β σ)) : GL (Fin n) F → W) = avgOver K (v : GL (Fin n) F → W)
      have : ((parabolicInd F n β σ ((k : unipotentRadical F n γ) : GL (Fin n) F) v :
          parabolicIndSpace F n β σ) : GL (Fin n) F → W) =
          fun y => (v : GL (Fin n) F → W) (y * ((k : unipotentRadical F n γ) : GL (Fin n) F)) := by
        funext y
        rw [coe_indRep_apply]
      rw [this]
      exact avgOver_comp_mul_right (hfinI v) (Subgroup.mem_map_of_mem _ k.2)
    exact this hK'
  obtain ⟨g, hg, hgY⟩ := avgOver_mem_supportedIn σ hYQ hKc
    (hKN.trans unipotentRadical_le_blockUpper) hf
  rw [← cellJacquet_avgOver σ hYo hCY hKc hKN hf hgY hg hm]
  have hg0 : (g : GL (Fin n) F → W) = 0 := hg.trans hL
  obtain ⟨e, he⟩ := exists_cellSupp σ hYo hCY hgY hm
  rw [cellJacquet_eq_cellEv σ hYo hCY hgY hm (isCellCompact_unipotentCompactG e) he]
  unfold cellEv
  rw [avgOver_eq_zero_of_forall (fun k _ => by unfold cellFun; rw [hg0]; rfl), map_zero, smul_zero]


variable (γ w) in
def jacquetSupported (Y : Set (GL (Fin n) F)) :
    supportedIn σ Y →ₗ[ℂ] jacquetFiltration γ (σ := σ) Y :=
  ((Representation.Coinvariants.mk _).comp (supportedIn σ Y).subtype).codRestrict _
    fun f => ⟨f, f.2, rfl⟩

theorem jacquetSupported_surjective (Y : Set (GL (Fin n) F)) :
    Function.Surjective (jacquetSupported γ σ Y) := by
  rintro ⟨_, f, hf, rfl⟩
  exact ⟨⟨f, hf⟩, rfl⟩

include hYo hCY hYQ in
theorem ker_jacquetSupported_le :
    LinearMap.ker (jacquetSupported γ σ Y) ≤ LinearMap.ker (cellJacquetMap γ w σ hYo hCY) := by
  intro f hf
  rw [LinearMap.mem_ker] at hf ⊢
  have h0 : Representation.Coinvariants.mk ((parabolicInd F n β σ).comp
      (unipotentRadical F n γ).subtype) (f : parabolicIndSpace F n β σ) = 0 :=
    congrArg Subtype.val hf
  apply Subtype.ext
  funext m
  exact cellJacquet_eq_zero_of_mk_eq_zero σ hYo hCY hYQ f.2 h0 m.2

include hYo hCY hYQ in
theorem cellJacquetMap_eq_of_jacquetSupported_eq {f f' : supportedIn σ Y}
    (h : jacquetSupported γ σ Y f = jacquetSupported γ σ Y f') :
    cellJacquetMap γ w σ hYo hCY f = cellJacquetMap γ w σ hYo hCY f' := by
  rw [← sub_eq_zero, ← map_sub]
  apply ker_jacquetSupported_le σ hYo hCY hYQ
  rw [LinearMap.mem_ker, map_sub, h, sub_self]


variable (γ w) in
def gradedJacquetMap :
    jacquetFiltration γ (σ := σ) Y →ₗ[ℂ] indSpace (cellLeviSub F β γ w) (cellInducing β γ w σ) where
  toFun x := cellJacquetMap γ w σ hYo hCY
    (Function.surjInv (jacquetSupported_surjective σ Y) x)
  map_add' x y := by
    rw [← map_add (f := _)]
    apply cellJacquetMap_eq_of_jacquetSupported_eq σ hYo hCY hYQ
    have hs := jacquetSupported_surjective (γ := γ) σ Y
    rw [map_add (f := _), Function.surjInv_eq hs x, Function.surjInv_eq hs y, Function.surjInv_eq hs (x + y)]
  map_smul' c x := by
    rw [RingHom.id_apply, ← map_smul]
    apply cellJacquetMap_eq_of_jacquetSupported_eq σ hYo hCY hYQ
    have hs := jacquetSupported_surjective (γ := γ) σ Y
    rw [map_smul, Function.surjInv_eq hs x, Function.surjInv_eq hs (c • x)]

theorem gradedJacquetMap_apply (f : supportedIn σ Y) :
    gradedJacquetMap γ w σ hYo hCY hYQ (jacquetSupported γ σ Y f) =
      cellJacquetMap γ w σ hYo hCY f :=
  cellJacquetMap_eq_of_jacquetSupported_eq σ hYo hCY hYQ
    (Function.surjInv_eq (jacquetSupported_surjective σ Y) _)

end Graded

section GradedProps

variable {Y : Set (GL (Fin n) F)} (hYo : IsOpen Y)
  (hCY : closure (doubleCoset (permGL F w) (blockUpper F n β : Set (GL (Fin n) F))
    (blockUpper F n γ)) ∩ Y = doubleCoset (permGL F w) (blockUpper F n β : Set (GL (Fin n) F))
    (blockUpper F n γ))
  (hYQ : ∀ g ∈ Y, ∀ q ∈ blockUpper F n γ, g * q ∈ Y)

theorem gradedJacquetMap_jacquetRep (m : levi F n γ) (x : jacquetFiltration γ (σ := σ) Y) :
    gradedJacquetMap γ w σ hYo hCY hYQ
        ⟨jacquetRep F n γ (parabolicInd F n β σ) m x, jacquetFiltration_le_comap γ hYQ m x.2⟩ =
      invSqrtModular F n γ (leviIncl m) •
        indRep (cellLeviSub F β γ w) (cellInducing β γ w σ) m (gradedJacquetMap γ w σ hYo hCY hYQ x) := by
  obtain ⟨f, rfl⟩ := jacquetSupported_surjective (γ := γ) σ Y x
  have hmf : parabolicInd F n β σ (m : GL (Fin n) F) (f : parabolicIndSpace F n β σ) ∈
      supportedIn σ Y := supportedIn_le_comap γ hYQ (levi_le_blockUpper m.2) f.2
  have hx : (⟨jacquetRep F n γ (parabolicInd F n β σ) m (jacquetSupported γ σ Y f),
      jacquetFiltration_le_comap γ hYQ m (jacquetSupported γ σ Y f).2⟩ :
        jacquetFiltration γ (σ := σ) Y) =
      invSqrtModular F n γ (leviIncl m) • jacquetSupported γ σ Y ⟨_, hmf⟩ := by
    apply Subtype.ext
    exact jacquetRep_mk _ m _
  rw [hx, map_smul, gradedJacquetMap_apply, gradedJacquetMap_apply]
  congr 1
  apply Subtype.ext
  funext m'
  rw [coe_cellJacquetMap_apply, coe_indRep_apply, coe_cellJacquetMap_apply]
  exact cellJacquet_parabolicInd σ _ _ _

theorem gradedJacquetMap_eq_zero_of_mem (x : jacquetFiltration γ (σ := σ) Y)
    (hx : (x : JacquetModule F n γ (parabolicInd F n β σ)) ∈ jacquetFiltration γ (σ := σ)
      (Y \ doubleCoset (permGL F w) (blockUpper F n β : Set (GL (Fin n) F)) (blockUpper F n γ))) :
    gradedJacquetMap γ w σ hYo hCY hYQ x = 0 := by
  obtain ⟨g, hg, hgx⟩ := hx
  have hgY : g ∈ supportedIn σ Y := supportedIn_mono sdiff_subset hg
  have : x = jacquetSupported γ σ Y ⟨g, hgY⟩ := Subtype.ext hgx.symm
  rw [this, gradedJacquetMap_apply]
  apply Subtype.ext
  funext m
  rw [coe_cellJacquetMap_apply]
  exact cellJacquet_eq_zero σ hYo hCY hgY (fun c hc => hg c fun h => h.2 hc) m.2

theorem gradedJacquetMap_eq_zero_iff
    (hker : ∀ f : parabolicIndSpace F n β σ, f ∈ supportedIn σ Y →
      (∀ m ∈ levi F n γ, cellJacquet γ w σ f m = 0) →
      ∃ g : parabolicIndSpace F n β σ, g ∈ supportedIn σ (Y \ doubleCoset (permGL F w)
        (blockUpper F n β : Set (GL (Fin n) F)) (blockUpper F n γ)) ∧
        f - g ∈ Representation.Coinvariants.ker
          ((parabolicInd F n β σ).comp (unipotentRadical F n γ).subtype))
    (x : jacquetFiltration γ (σ := σ) Y) :
    gradedJacquetMap γ w σ hYo hCY hYQ x = 0 ↔
      (x : JacquetModule F n γ (parabolicInd F n β σ)) ∈ jacquetFiltration γ (σ := σ)
        (Y \ doubleCoset (permGL F w) (blockUpper F n β : Set (GL (Fin n) F)) (blockUpper F n γ)) := by
  refine ⟨fun h0 => ?_, gradedJacquetMap_eq_zero_of_mem σ hYo hCY hYQ x⟩
  obtain ⟨f, rfl⟩ := jacquetSupported_surjective (γ := γ) σ Y x
  rw [gradedJacquetMap_apply] at h0
  have hz : ∀ m ∈ levi F n γ, cellJacquet γ w σ (f : parabolicIndSpace F n β σ) m = 0 := by
    intro m hm
    have := congrArg (fun φ : indSpace (cellLeviSub F β γ w) (cellInducing β γ w σ) =>
      φ.1 ⟨m, hm⟩) h0
    simpa only [coe_cellJacquetMap_apply, ZeroMemClass.coe_zero, Pi.zero_apply] using this
  obtain ⟨g, hg, hfg⟩ := hker f f.2 hz
  refine ⟨g, hg, ?_⟩
  show Representation.Coinvariants.mk _ g = Representation.Coinvariants.mk _ (f : parabolicIndSpace F n β σ)
  rw [eq_comm, ← sub_eq_zero, ← map_sub]
  exact (Representation.Coinvariants.mk_eq_zero _).2 hfg

theorem gradedJacquetMap_surjective (hsurj : Function.Surjective (cellJacquetMap γ w σ hYo hCY)) :
    Function.Surjective (gradedJacquetMap γ w σ hYo hCY hYQ) := by
  intro φ
  obtain ⟨f, rfl⟩ := hsurj φ
  exact ⟨jacquetSupported γ σ Y f, gradedJacquetMap_apply σ hYo hCY hYQ f⟩

end GradedProps

end Parabolic

end GroundTheory.Automorphic
end
end

section -- merged from GroundTheory.AutomorphicForms.GeometricLemmaCellKernel
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.Automorphic

namespace Parabolic

open Matrix Iwasawa GLnLocal ValuativeRel Topology Set DoubleCoset Filter

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {β γ : Fin n → ℕ} {w : Equiv.Perm (Fin n)}

theorem isCompact_subgroupOf_cellUnipotent (e : ℕ) :
    IsCompact (((unipotentCompactG (F := F) γ e).subgroupOf (cellUnipotent F β γ w) :
      Subgroup (cellUnipotent F β γ w)) : Set (cellUnipotent F β γ w)) := by
  rw [Subgroup.coe_subgroupOf]
  exact isClosed_cellUnipotent.isClosedEmbedding_subtypeVal.isCompact_preimage
    (isCompact_unipotentCompactG e)

theorem isOpen_subgroupOf_cellUnipotent (e : ℕ) :
    IsOpen (((unipotentCompactG (F := F) γ e).subgroupOf (cellUnipotent F β γ w) :
      Subgroup (cellUnipotent F β γ w)) : Set (cellUnipotent F β γ w)) := by
  have : (unipotentCompactG (F := F) γ e).subgroupOf (cellUnipotent F β γ w) =
      ((integralGL F n).comap (MulAut.conj (rankTorus F n γ e)).toMonoidHom).subgroupOf
        (cellUnipotent F β γ w) := by
    ext x
    simp only [Subgroup.mem_subgroupOf, unipotentCompactG_eq, Subgroup.mem_inf]
    exact ⟨fun h => h.2, fun h => ⟨cellUnipotent_le_unipotentRadical x.2, h⟩⟩
  rw [this, Subgroup.coe_subgroupOf]
  exact (isOpen_conj_integralGL _).preimage continuous_subtype_val

theorem coinvariantsKer_mono {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ G V} {H H' : Subgroup G} (h : H ≤ H') :
    coinvariantsKer ρ H ≤ coinvariantsKer ρ H' := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨⟨x, v⟩, rfl⟩
  exact sub_mem_coinvariantsKer (h x.2) v

section Vanishing

variable {W : Type*} [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (levi F n β) W)

theorem exists_avgOver_cellFun_eq_zero (hσ : IsSmooth σ) {Y : Set (GL (Fin n) F)}
    (hYo : IsOpen Y)
    (hCY : closure (doubleCoset (permGL F w) (blockUpper F n β : Set (GL (Fin n) F))
      (blockUpper F n γ)) ∩ Y = doubleCoset (permGL F w) (blockUpper F n β : Set (GL (Fin n) F))
      (blockUpper F n γ))
    {f : parabolicIndSpace F n β σ} (hf : f ∈ supportedIn σ Y) {t : GL (Fin n) F}
    (ht : t ∈ levi F n γ) (h0 : cellJacquet γ w σ f t = 0) :
    ∃ e : ℕ, CellSupp γ w σ f t (unipotentCompactG γ e) ∧
      avgOver (unipotentCompactG γ e) (cellFun w σ f t) 1 = 0 := by
  set A := cellUnipotent F β γ w
  set θ := cellRepA β γ w σ
  set h := cellFun w σ f t
  obtain ⟨e, he⟩ := exists_cellSupp σ hYo hCY hf ht
  have hK := isCellCompact_unipotentCompactG (F := F) (γ := γ) e
  set v := avgOver (unipotentCompactG γ e) h 1

  have hv : v ∈ Representation.Coinvariants.ker θ := by
    have h1 := cellJacquet_eq_cellEv σ hYo hCY hf ht hK he
    rw [h0] at h1
    unfold cellEv at h1
    have hc : ((cellNorm F β γ w (unipotentCompactG γ e) : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (cellNorm_pos (w := w) (β := β) hK).ne'
    have h2 : Representation.Coinvariants.mk θ v = 0 :=
      (smul_eq_zero.1 h1.symm).resolve_left hc
    exact (Representation.Coinvariants.mk_eq_zero _).1 h2
  obtain ⟨A', hA'c, hA'o, hvA'⟩ := exists_mem_coinvariantsKer θ
    (fun s => exists_compactOpen_subgroupOf isClosed_cellUnipotent
      cellUnipotent_le_unipotentRadical s) hv

  obtain ⟨e₁, he₁⟩ := exists_unipotentCompactG_of_isCompact (γ := γ)
    (hA'c.image continuous_subtype_val)
    (by rintro _ ⟨x, -, rfl⟩; exact cellUnipotent_le_unipotentRadical x.2)
  set e' := max e e₁
  have hK' := isCellCompact_unipotentCompactG (F := F) (γ := γ) e'
  have hKK' : unipotentCompactG (F := F) γ e ≤ unipotentCompactG γ e' :=
    unipotentCompactG_mono (le_max_left _ _)
  have hf' : AvgFinite (unipotentCompactG γ e) h := avgFinite_cellFun σ f t hK.2.1
  have hhA : ∀ a : A, ∀ y, h ((a : GL (Fin n) F) * y) = θ a (h y) := cellFun_mul_left σ f t
  refine ⟨e', he.mono hKK', ?_⟩
  rw [avgOver_eq_smul_avgOver_inf (A := A) hKK' hf' (hK.relIndex_ne_zero hK')
    (fun y hy hy0 => he y (hK'.1 hy) hy0)]

  set B : Subgroup A := (unipotentCompactG (F := F) γ e').subgroupOf A
  have hBc : IsCompact (B : Set A) := isCompact_subgroupOf_cellUnipotent e'
  have hBo : IsOpen (B : Set A) := isOpen_subgroupOf_cellUnipotent e'
  set h' := avgOver (unipotentCompactG γ e) h
  have hh' : ∀ a : A, ∀ y, h' ((a : GL (Fin n) F) * y) = θ a (h' y) :=
    fun a y => avgOver_mul_left_eq (fun a => θ a) hhA hf' a y
  have hfin' : AvgFinite (unipotentCompactG γ e' ⊓ A) h' := by
    have h2 : (unipotentCompactG (F := F) γ e ⊓ A).relIndex (unipotentCompactG γ e' ⊓ A) ≠ 0 :=
      relIndex_inf_ne_zero (hK.relIndex_ne_zero hK')
    intro h0
    exact h2 (Nat.eq_zero_of_zero_dvd (h0 ▸ Subgroup.relIndex_dvd_of_le_left _
      (le_trans inf_le_left (le_rightStab_avgOver hf'))))
  have : LocallyCompactSpace A := isClosed_cellUnipotent.isClosedEmbedding_subtypeVal.locallyCompactSpace
  set u := avgOver (unipotentCompactG γ e' ⊓ A) h' 1
  have hu : u ∈ fixedVectors θ B := by
    intro b hb
    have hbK : (b : GL (Fin n) F) ∈ unipotentCompactG γ e' ⊓ A :=
      ⟨Subgroup.mem_subgroupOf.1 hb, b.2⟩
    show θ b (avgOver (unipotentCompactG γ e' ⊓ A) h' 1) = avgOver (unipotentCompactG γ e' ⊓ A) h' 1
    rw [← avgOver_comp_linearMap hfin']
    have : (fun y => θ b (h' y)) = fun y => h' ((b : GL (Fin n) F) * y) := by
      funext y
      rw [hh']
    rw [this, avgOver_comp_mul_left, show (b : GL (Fin n) F) * 1 = 1 * (b : GL (Fin n) F) by group,
      avgOver_mul_right hfin' hbK]
  have hsub : v - u ∈ coinvariantsKer θ B := by
    have hspan := sub_avgOver_mem_span hfin'
    have hev := Submodule.mem_map_of_mem (f := LinearMap.proj (R := ℂ) (φ := fun _ : GL (Fin n) F => W) 1) hspan
    rw [Submodule.map_span] at hev
    refine Submodule.span_le.2 ?_ hev
    rintro _ ⟨g, ⟨k, hk, rfl⟩, rfl⟩
    have hkA : (k : GL (Fin n) F) ∈ A := (Subgroup.mem_inf.1 hk).2
    have hkB : (⟨k, hkA⟩ : A) ∈ B := Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.1 hk).1
    simp only [LinearMap.proj_apply, Pi.sub_apply, one_mul]
    have : h' k = θ ⟨k, hkA⟩ (h' 1) := by
      have := hh' ⟨k, hkA⟩ 1
      rwa [mul_one] at this
    rw [this]
    exact sub_mem_coinvariantsKer hkB _
  have hproj : (fixedProj θ (isSmooth_cellRepA hσ) hBc hBo v : W) = u := by
    have := (fixedProj_eq_iff (isSmooth_cellRepA hσ) hBc hBo (w := ⟨u, hu⟩)).2 hsub
    rw [this]
  have hA'B : A' ≤ B := fun x hx => Subgroup.mem_subgroupOf.2
    (unipotentCompactG_mono (le_max_right _ _) (he₁ ⟨x, hx, rfl⟩))
  have hzero := fixedProj_apply_of_mem_coinvariantsKer (isSmooth_cellRepA hσ) hBc hBo
    (coinvariantsKer_mono hA'B hvA')
  rw [← hproj, hzero]
  simp

end Vanishing

section AvgConj

variable {G : Type*} [Group G] {W : Type*} [AddCommGroup W] [Module ℂ W]

theorem avgOver_mul_right_of_normalizes {K : Subgroup G} {f : G → W} (hf : AvgFinite K f) {k : G}
    (hk : K.map (MulAut.conj k).toMonoidHom = K) (hkf : ∀ y, f (y * k) = f y) (y : G) :
    avgOver K f (y * k) = avgOver K f y := by
  have h1 := avgOver_map_conj k hf (k * y)
  rw [hk] at h1
  have h2 : (fun z => f (k⁻¹ * z * k)) = fun z => f (k⁻¹ * z) := by
    funext z
    exact hkf _
  rw [h2, avgOver_comp_mul_left] at h1
  rw [show k⁻¹ * (k * y) * k = y * k by group] at h1
  rw [← h1]
  congr 1
  group

theorem avgFinite_comp_mul_left {K : Subgroup G} {f : G → W} (hf : AvgFinite K f) (h : G) :
    AvgFinite K (fun y => f (h * y)) := by
  intro h0
  have hle : rightStab f ≤ rightStab (fun y => f (h * y)) := fun g hg => by
    rw [mem_rightStab] at hg ⊢
    intro x
    rw [← mul_assoc, hg]
  exact hf (Nat.eq_zero_of_zero_dvd (h0 ▸ Subgroup.relIndex_dvd_of_le_left _ hle))

end AvgConj

section Kernel

variable {W : Type*} [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (levi F n β) W)

theorem avgOver_permGL_mul_mul (f : parabolicIndSpace F n β σ) {K : Subgroup (GL (Fin n) F)}
    (hf : AvgFinite K (f : GL (Fin n) F → W)) {t : GL (Fin n) F}
    (ht : K.map (MulAut.conj t).toMonoidHom = K) (u : GL (Fin n) F) :
    avgOver K (f : GL (Fin n) F → W) (permGL F w * u * t) = avgOver K (cellFun w σ f t) u := by
  have h0 := avgFinite_comp_mul_left hf (permGL F w * t)
  have h1 := avgOver_map_conj t h0 u
  rw [ht] at h1
  have h2 : (fun y => (fun z => (f : GL (Fin n) F → W) (permGL F w * t * z)) (t⁻¹ * y * t)) =
      cellFun w σ f t := by
    funext y
    unfold cellFun
    group
  rw [h2] at h1
  rw [h1, avgOver_comp_mul_left]
  congr 1
  group

theorem exists_sub_mem_ker_of_cellJacquet_eq_zero (hσ : IsSmooth σ) {Y : Set (GL (Fin n) F)}
    (hYo : IsOpen Y)
    (hCY : closure (doubleCoset (permGL F w) (blockUpper F n β : Set (GL (Fin n) F))
      (blockUpper F n γ)) ∩ Y = doubleCoset (permGL F w) (blockUpper F n β : Set (GL (Fin n) F))
      (blockUpper F n γ))
    (hYQ : ∀ g ∈ Y, ∀ q ∈ blockUpper F n γ, g * q ∈ Y)
    {f : parabolicIndSpace F n β σ} (hf : f ∈ supportedIn σ Y)
    (h0 : ∀ m ∈ levi F n γ, cellJacquet γ w σ f m = 0) :
    ∃ g : parabolicIndSpace F n β σ,
      g ∈ supportedIn σ (Y \ doubleCoset (permGL F w) (blockUpper F n β : Set (GL (Fin n) F))
        (blockUpper F n γ)) ∧
      f - g ∈ Representation.Coinvariants.ker
        ((parabolicInd F n β σ).comp (unipotentRadical F n γ).subtype) := by
  classical
  obtain ⟨U, hU, hUf⟩ := exists_rightStab_parabolicInd σ f
  obtain ⟨j, -, hj⟩ := (hasBasis_nhds_one F n).mem_iff.1 (hU.mem_nhds U.one_mem)
  obtain ⟨T, hT, hTcov⟩ := exists_finset_levi_eq_mul (F := F) (β := β) (γ := γ) (w := w) j
  have hTe : ∀ t ∈ T, ∃ e, CellSupp γ w σ f t (unipotentCompactG (F := F) γ e) ∧
      avgOver (unipotentCompactG (F := F) γ e) (cellFun w σ f t) 1 = 0 := fun t ht =>
    exists_avgOver_cellFun_eq_zero σ hσ hYo hCY hf (hT t ht).1 (h0 t (hT t ht).1)
  choose! et het using hTe
  set E := T.sup et
  set NE := unipotentCompactG (F := F) γ E
  have hNEc : IsCompact (NE : Set (GL (Fin n) F)) := isCompact_unipotentCompactG E
  have hffin : AvgFinite NE (f : GL (Fin n) F → W) :=
    avgFinite_of_isOpen hNEc hU (fun k hk => mem_rightStab.2 fun y => hUf k hk y)
  have hconj : ∀ k, k ∈ levi F n γ → k ∈ integralGL F n →
      NE.map (MulAut.conj k).toMonoidHom = NE := by
    intro k hk hk'
    apply le_antisymm
    · rintro _ ⟨u, hu, rfl⟩
      exact conj_mem_unipotentCompactG hk hk' hu
    · intro u hu
      refine ⟨k⁻¹ * u * k, ?_, by show k * (k⁻¹ * u * k) * k⁻¹ = u; group⟩
      have := conj_mem_unipotentCompactG ((levi F n γ).inv_mem hk) ((integralGL F n).inv_mem hk') hu
      simpa using this
  set gfun := avgOver NE (f : GL (Fin n) F → W)
  have hgmem : gfun ∈ parabolicIndSpace F n β σ := avgOver_mem hffin (fun k hk => by
    have : (fun y => (f : GL (Fin n) F → W) (y * k)) =
        ((parabolicInd F n β σ k f : parabolicIndSpace F n β σ) : GL (Fin n) F → W) := by
      funext y
      rw [coe_indRep_apply]
    rw [this]
    exact (parabolicInd F n β σ k f).2)
  set g : parabolicIndSpace F n β σ := ⟨gfun, hgmem⟩
  have hgP := ((mem_parabolicIndSpace σ).1 hgmem).1

  have hvanT : ∀ t ∈ T, ∀ u ∈ unipotentRadical F n γ, gfun (permGL F w * u * t) = 0 := by
    intro t ht u hu
    have htM := (hT t ht).1
    have htK := (hT t ht).2
    show avgOver NE (f : GL (Fin n) F → W) (permGL F w * u * t) = 0
    rw [avgOver_permGL_mul_mul σ f hffin (hconj t htM htK) u]
    obtain ⟨hsupp, hzero⟩ := het t ht
    have hle : unipotentCompactG (F := F) γ (et t) ≤ NE := unipotentCompactG_mono (Finset.le_sup ht)
    have hK1 := isCellCompact_unipotentCompactG (F := F) (γ := γ) (et t)
    have hKE := isCellCompact_unipotentCompactG (F := F) (γ := γ) E
    have hfin1 : AvgFinite (unipotentCompactG γ (et t)) (cellFun w σ f t) :=
      avgFinite_cellFun σ f t hK1.2.1
    have hz : avgOver NE (cellFun w σ f t) 1 = 0 :=
      avgOver_eq_zero_of_le (fun a => cellRepA β γ w σ a) (cellFun_mul_left σ f t) hle hfin1
        (hK1.relIndex_ne_zero hKE) (fun y hy hy0 => hsupp y (hKE.1 hy) hy0) hzero
    have hfinE : AvgFinite NE (cellFun w σ f t) := avgFinite_cellFun σ f t hKE.2.1
    by_cases hAN : ∃ a ∈ cellUnipotent F β γ w, ∃ k ∈ NE, u = a * k
    · obtain ⟨a, ha, k, hk, rfl⟩ := hAN
      rw [avgOver_mul_right hfinE hk, show a = a * 1 by group,
        avgOver_mul_left_eq (fun a => cellRepA β γ w σ a) (cellFun_mul_left σ f t) hfinE ⟨a, ha⟩ 1,
        hz, map_zero]
    · apply avgOver_eq_zero_of_forall
      intro k hk
      by_contra hne
      obtain ⟨a, ha, k₁, hk₁, he⟩ := hsupp (u * k)
        ((unipotentRadical F n γ).mul_mem hu (unipotentCompactG_le E hk)) hne
      exact hAN ⟨a, ha, k₁ * k⁻¹, NE.mul_mem (hle hk₁) (NE.inv_mem hk), by
        rw [← mul_assoc, ← he]; group⟩

  have hvanC : ∀ x ∈ doubleCoset (permGL F w) (blockUpper F n β : Set (GL (Fin n) F))
      (blockUpper F n γ), gfun x = 0 := by
    intro x hx
    obtain ⟨p, hp, q, hq, rfl⟩ := mem_doubleCoset.1 hx
    set m₀ := leviProj F n γ ⟨q, hq⟩
    have hn₀ : q * ((m₀ : levi F n γ) : GL (Fin n) F)⁻¹ ∈ unipotentRadical F n γ := by
      rw [show q * ((m₀ : levi F n γ) : GL (Fin n) F)⁻¹ =
        ((⟨q, hq⟩ * (leviIncl m₀)⁻¹ : blockUpper F n γ) : GL (Fin n) F) from rfl,
        mem_unipotentRadical_iff_leviProj, map_mul, map_inv, leviProj_leviIncl, mul_inv_cancel]
    obtain ⟨b, hb, t, htT, k, hk, hm₀⟩ := hTcov _ m₀.2
    set n₀ := q * ((m₀ : levi F n γ) : GL (Fin n) F)⁻¹
    have hq' : q = n₀ * (b * t * k) := by
      rw [← hm₀]
      simp only [n₀]
      group
    have hbM : b ∈ levi F n γ := cellLeviParabolic_le_levi hb
    set n₁ := b⁻¹ * n₀ * b
    have hn₁ : n₁ ∈ unipotentRadical F n γ := by
      have := conj_mem_unipotentRadical ((blockUpper F n γ).inv_mem (levi_le_blockUpper hbM)) hn₀
      simpa [n₁] using this
    have hkM : k ∈ levi F n γ := (Subgroup.mem_inf.1 hk).1
    have hkK : k ∈ congruenceSubgroup F n j := (Subgroup.mem_inf.1 hk).2
    have hxeq : p * permGL F w * q =
        (p * (permGL F w * b * (permGL F w)⁻¹)) * (permGL F w * n₁ * t) * k := by
      rw [hq']
      simp only [n₁]
      group
    have hpb : p * (permGL F w * b * (permGL F w)⁻¹) ∈ blockUpper F n β :=
      (blockUpper F n β).mul_mem hp ((conj_permGL_mem_blockUpper_iff w).2
        (cellLeviParabolic_le_blockUpper hb))
    rw [hxeq]
    show avgOver NE (f : GL (Fin n) F → W) _ = 0
    rw [avgOver_mul_right_of_normalizes hffin
      (hconj k hkM (congruenceSubgroup_le F n j hkK)) (fun y => hUf k (hj hkK) y)]
    show gfun (((⟨_, hpb⟩ : blockUpper F n β) : GL (Fin n) F) * (permGL F w * n₁ * t)) = 0
    rw [hgP ⟨_, hpb⟩, hvanT t htT n₁ hn₁, map_zero, smul_zero]
  refine ⟨g, ?_, ?_⟩
  · intro x hx
    show gfun x = 0
    by_cases hxY : x ∈ Y
    · exact hvanC x (by by_contra hxC; exact hx ⟨hxY, hxC⟩)
    · apply avgOver_eq_zero_of_forall
      intro k hk
      apply hf
      intro hxk
      apply hxY
      have := hYQ _ hxk k⁻¹ ((blockUpper F n γ).inv_mem
        (unipotentRadical_le_blockUpper (unipotentCompactG_le E hk)))
      simpa using this
  ·
    have : ((rightStab (f : GL (Fin n) F → W)).subgroupOf NE).FiniteIndex := ⟨hffin⟩
    let _ := Fintype.ofFinite (NE ⧸ (rightStab (f : GL (Fin n) F → W)).subgroupOf NE)
    have hI : (((rightStab (f : GL (Fin n) F → W)).relIndex NE : ℕ) : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.2 hffin
    have hcard : Fintype.card (NE ⧸ (rightStab (f : GL (Fin n) F → W)).subgroupOf NE) =
        (rightStab (f : GL (Fin n) F → W)).relIndex NE := by
      rw [Subgroup.relIndex, Subgroup.index, Nat.card_eq_fintype_card]
    have hkN : ∀ q : NE ⧸ (rightStab (f : GL (Fin n) F → W)).subgroupOf NE,
        ((Quotient.out q : NE) : GL (Fin n) F) ∈ unipotentRadical F n γ :=
      fun q => unipotentCompactG_le E (Quotient.out q).2
    have key : f - g = (((rightStab (f : GL (Fin n) F → W)).relIndex NE : ℂ)⁻¹) •
        ∑ q : NE ⧸ (rightStab (f : GL (Fin n) F → W)).subgroupOf NE,
          -(((parabolicInd F n β σ).comp (unipotentRadical F n γ).subtype) ⟨_, hkN q⟩ f - f) := by
      apply Subtype.ext
      simp only [Submodule.coe_sub, Submodule.coe_smul, Submodule.coe_sum, neg_sub]
      show (f : GL (Fin n) F → W) - gfun = _
      simp only [gfun]
      rw [avgOver_eq_sum_translates]
      have e1 : ∀ q : NE ⧸ (rightStab (f : GL (Fin n) F → W)).subgroupOf NE,
          ((((parabolicInd F n β σ).comp (unipotentRadical F n γ).subtype) ⟨_, hkN q⟩ f :
            parabolicIndSpace F n β σ) : GL (Fin n) F → W) =
          fun y => (f : GL (Fin n) F → W) (y * ((Quotient.out q : NE) : GL (Fin n) F)) := by
        intro q
        funext y
        exact coe_indRep_apply _ _ _ _ _
      simp only [e1]
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, hcard,
        ← Nat.cast_smul_eq_nsmul ℂ, smul_sub, smul_smul, inv_mul_cancel₀ hI, one_smul]
    rw [key]
    exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun q _ =>
      Submodule.neg_mem _ (Representation.Coinvariants.sub_mem_ker
        (ρ := (parabolicInd F n β σ).comp (unipotentRadical F n γ).subtype) ⟨_, hkN q⟩ f))

end Kernel

end Parabolic

end GroundTheory.Automorphic
end
end

set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.Automorphic

namespace Parabolic

open Matrix Iwasawa GLnLocal ValuativeRel Topology Set DoubleCoset Filter

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {β γ : Fin n → ℕ} {W : Type*} [AddCommGroup W] [Module ℂ W]
  (σ : Representation ℂ (levi F n β) W)

theorem cellUnion_mul_mem {k : ℕ} (w : Fin k → Equiv.Perm (Fin n)) (j : ℕ) :
    (∀ g ∈ cellUnion (fun l => doubleCoset (permGL F (w l)) (blockUpper F n β : Set (GL (Fin n) F))
        (blockUpper F n γ)) j, ∀ q ∈ blockUpper F n γ, g * q ∈ cellUnion (fun l => doubleCoset
          (permGL F (w l)) (blockUpper F n β : Set (GL (Fin n) F)) (blockUpper F n γ)) j) ∧
      (∀ p ∈ blockUpper F n β, ∀ g ∈ cellUnion (fun l => doubleCoset (permGL F (w l))
        (blockUpper F n β : Set (GL (Fin n) F)) (blockUpper F n γ)) j, p * g ∈ cellUnion
          (fun l => doubleCoset (permGL F (w l)) (blockUpper F n β : Set (GL (Fin n) F))
            (blockUpper F n γ)) j) := by
  constructor
  · intro g hg q hq
    obtain ⟨l, hl, hgl⟩ := (mem_cellUnion _).1 hg
    obtain ⟨p', hp', q', hq', rfl⟩ := mem_doubleCoset.1 hgl
    exact (mem_cellUnion _).2 ⟨l, hl, mem_doubleCoset.2 ⟨p', hp', q' * q,
      (blockUpper F n γ).mul_mem hq' hq, by group⟩⟩
  · intro p hp g hg
    obtain ⟨l, hl, hgl⟩ := (mem_cellUnion _).1 hg
    obtain ⟨p', hp', q', hq', rfl⟩ := mem_doubleCoset.1 hgl
    exact (mem_cellUnion _).2 ⟨l, hl, mem_doubleCoset.2 ⟨p * p',
      (blockUpper F n β).mul_mem hp hp', q', hq', by group⟩⟩

theorem exists_filtration_jacquetModule_parabolicInd (hσ : IsSmooth σ) :
    ∃ (k : ℕ) (w : Fin k → Equiv.Perm (Fin n)),
      (∀ g : GL (Fin n) F, ∃! j, g ∈ doubleCoset (permGL F (w j))
        (blockUpper F n β : Set (GL (Fin n) F)) (blockUpper F n γ)) ∧
      ∃ V : ℕ → Submodule ℂ (JacquetModule F n γ (parabolicInd F n β σ)),
        V 0 = ⊥ ∧ V k = ⊤ ∧ Monotone V ∧
        ∃ hV : ∀ i (m : levi F n γ), V i ≤ (V i).comap (jacquetRep F n γ (parabolicInd F n β σ) m),
          ∀ j : Fin k, ∃ Ψ : Representation.IntertwiningMap
              ((jacquetRep F n γ (parabolicInd F n β σ)).subrepresentation (V (j + 1)) (hV (j + 1)))
              (twist ((invSqrtModular F n γ).comp leviIncl)
                (indRep (cellLeviSub F β γ (w j)) (cellInducing β γ (w j) σ))),
            Function.Surjective Ψ ∧
              ∀ x, Ψ x = 0 ↔ (x : JacquetModule F n γ (parabolicInd F n β σ)) ∈ V j := by
  obtain ⟨k, w, hcov, hanti⟩ := exists_cellEnumeration (F := F) β γ
  set C : Fin k → Set (GL (Fin n) F) := fun l =>
    doubleCoset (permGL F (w l)) (blockUpper F n β : Set (GL (Fin n) F)) (blockUpper F n γ)
  have hdisj : Pairwise fun i j => Disjoint (C i) (C j) := by
    intro i j hij
    rw [Set.disjoint_left]
    intro g hgi hgj
    obtain ⟨l, -, hl⟩ := hcov g
    exact hij ((hl i hgi).trans (hl j hgj).symm)
  have hcov' : ∀ g, ∃ l, g ∈ C l := fun g => (hcov g).exists
  have hcl := closure_doubleCoset_subset_of_antitone hcov hanti
  refine ⟨k, w, hcov, fun i => jacquetFiltration γ (σ := σ) (cellUnion C i), ?_, ?_, ?_, ?_⟩
  · show jacquetFiltration γ (cellUnion C 0) = ⊥
    rw [cellUnion_zero, jacquetFiltration_empty]
  · show jacquetFiltration γ (cellUnion C k) = ⊤
    rw [cellUnion_of_cover hcov', jacquetFiltration_univ]
  · exact fun i i' h => jacquetFiltration_mono γ (cellUnion_mono h)
  refine ⟨fun i m => jacquetFiltration_le_comap γ (cellUnion_mul_mem w i).1 m, fun j => ?_⟩
  have hYo : IsOpen (cellUnion C ((j : ℕ) + 1)) := isOpen_cellUnion hdisj hcov' hcl _
  have hCY : closure (C j) ∩ cellUnion C ((j : ℕ) + 1) = C j :=
    closure_inter_cellUnion_succ hdisj hcl j
  have hYQ := (cellUnion_mul_mem (F := F) (β := β) (γ := γ) w ((j : ℕ) + 1)).1
  have hYP := (cellUnion_mul_mem (F := F) (β := β) (γ := γ) w ((j : ℕ) + 1)).2
  have hdiff : cellUnion C ((j : ℕ) + 1) \ C j = cellUnion C j := by
    rw [cellUnion_succ j, union_sdiff_right, (disjoint_cellUnion hdisj j).symm.sdiff_eq_left]
  refine ⟨⟨gradedJacquetMap γ (w j) σ hYo hCY hYQ, fun m => ?_⟩, ?_, fun x => ?_⟩
  · refine LinearMap.ext fun x => ?_
    exact gradedJacquetMap_jacquetRep σ hYo hCY hYQ m x
  · exact gradedJacquetMap_surjective σ hYo hCY hYQ (cellJacquetMap_surjective hYo hCY hYP hYQ hσ)
  · have := gradedJacquetMap_eq_zero_iff σ hYo hCY hYQ
      (fun f hf h0 => exists_sub_mem_ker_of_cellJacquet_eq_zero σ hσ hYo hCY hYQ hf h0) x
    rw [hdiff] at this
    exact this

end Parabolic

end GroundTheory.Automorphic
