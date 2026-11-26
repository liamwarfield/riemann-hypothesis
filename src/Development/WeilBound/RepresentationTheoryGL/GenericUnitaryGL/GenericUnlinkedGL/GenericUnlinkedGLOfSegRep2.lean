module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.GeometricSplitting.Imports
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalSwapProductGeneric
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.UnlinkedIrreducibility.LUnlinkedIrrOfHeredity
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.NuPairInjectivity.NuPair
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentJacquetAll

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.WhittakerHeredity.Replay
open GlobalTheory.BZMir.Leib

namespace PositivityTheory.rg.gu.hered2

theorem whitHeredity_all :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
      WhitHeredity k :=
  fun k _ _ _ _ => GlobalTheory.CompanionTheory.Rodier.whitHeredity k

end PositivityTheory.rg.gu.hered2
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.CuspidalGenericity.Bridge
section -- merged from Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.CuspidalGenericity.Direct
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir

theorem GlobalTheory.BZSeg.Cusp.isGenericFor_of_isCuspidal_direct :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
      (π : Representation ℂ (GL (Fin (N + 1)) k) V), IsCuspidal π → Nontrivial V → IsGenericFor ψ π :=
  GlobalTheory.CompanionTheory.BZDeriv.isGenericFor_of_isCuspidal_of GlobalTheory.CompanionTheory.BZMirDer.NonZero.exists_derivative_nontrivial
    (fun k _ _ _ _ ψ m n V _ _ π => GlobalTheory.CompanionTheory.BZMirDer.twKer_resM_derUnipM (k := k) ψ m n V π) GlobalTheory.T.cuspidal_twisted_kernel_top
    (fun k _ _ _ _ ψ N V _ _ π => GlobalTheory.CompanionTheory.DerWhit.twKer_derUnip_zero (k := k) ψ N V π)
end

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir

namespace GlobalTheory.BZSeg.Cusp

theorem nontrivial_of_isIrreducible {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (h : ρ.IsIrreducible) : Nontrivial V := by
  by_contra hV
  rw [not_nontrivial_iff_subsingleton] at hV
  exact bot_ne_top (α := Subrepresentation ρ) (Subrepresentation.ext (Subsingleton.elim _ _))

theorem cuspGeneric (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    GlobalTheory.BZSeg.CuspGeneric k := by
  intro N V _ _ π hN _ hirr hc
  obtain ⟨ψ, hψc, hψ1⟩ := exists_continuous_addChar_ne_one (k := k)
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  exact ⟨ψ, hψc, hψ1, GlobalTheory.BZSeg.Cusp.isGenericFor_of_isCuspidal_direct k ψ hψc hψ1 M V π hc (nontrivial_of_isIrreducible π hirr)⟩

end GlobalTheory.BZSeg.Cusp

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GelfandKazhdanLocal
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GelfandKazhdanLocal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.GenGK

theorem gkLocal_gen : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    GlobalTheory.Published.IrreducibleAdmissibleGL → Zc.Cos.GKLocal k :=
  fun hA => GlobalTheory.CompanionTheory.GKLocalProof.gkLocal hA

end GlobalTheory.CompanionTheory.GenGK
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GelfandKazhdanLocalStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gelfand_kazhdan_local : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → Zc.Cos.GKLocal k := by
  first | exact @GlobalTheory.CompanionTheory.GenGK.gkLocal_gen | exact GlobalTheory.CompanionTheory.GenGK.gkLocal_gen | (intros; apply GlobalTheory.CompanionTheory.GenGK.gkLocal_gen <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnlinkedLayersHold
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnlinkedLayersHold
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu

namespace GlobalTheory.CompanionTheory.SegLayers

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem term_injective (Δ : Segment k) : Function.Injective Δ.term := fun a b h =>
  Fin.ext ((IrrGL.nu_natCast_inj (x := Δ.first) Δ.d_pos).1 h)

theorem ms_nodup (Δ : Segment k) : Δ.ms.Nodup :=
  Multiset.Nodup.map (term_injective Δ) Finset.univ.nodup

theorem ncard_carrier (Δ : Segment k) : Δ.carrier.ncard = Δ.len := by
  rw [Segment.carrier, ← Set.image_univ, Set.ncard_image_of_injective _ (term_injective Δ)]
  simp

theorem ms_le {Δ : Segment k} {s : Multiset (IrrGL (k := k))} (h : ∀ x ∈ Δ.carrier, x ∈ s) : Δ.ms ≤ s :=
  (Multiset.le_iff_subset (ms_nodup Δ)).2 fun _ hx => h _ (Segment.mem_ms.1 hx)

theorem exists_longest {s : Multiset (IrrGL (k := k))} {y : IrrGL (k := k)} (hy : y ∈ s) (hc : y.IsCusp) :
    ∃ Γ : Segment k, (∀ x ∈ Γ.carrier, x ∈ s) ∧
      ∀ D : Segment k, (∀ x ∈ D.carrier, x ∈ s) → D.len ≤ Γ.len := by
  classical
  let P : ℕ → Prop := fun l => ∃ D : Segment k, (∀ x ∈ D.carrier, x ∈ s) ∧ D.len = l
  have hb : ∀ D : Segment k, (∀ x ∈ D.carrier, x ∈ s) → D.len ≤ Multiset.card s := fun D hD => by
    rw [← Segment.card_ms]
    exact Multiset.card_le_card (ms_le hD)
  have h1 : P 1 := ⟨Segment.single y hc, fun x hx => by
    rw [Segment.carrier_single] at hx
    exact hx ▸ hy, rfl⟩
  have h1' : 1 ≤ Multiset.card s := by
    obtain ⟨D, hD, e⟩ := h1
    exact e ▸ hb D hD
  obtain ⟨Γ, hΓ, e⟩ := Nat.findGreatest_spec h1' h1
  exact ⟨Γ, hΓ, fun D hD => e ▸ Nat.le_findGreatest (hb D hD) ⟨D, hD, rfl⟩⟩

theorem not_linked_of_longest {s : Multiset (IrrGL (k := k))} {Γ D : Segment k} (hΓ : ∀ x ∈ Γ.carrier, x ∈ s)
    (hm : ∀ D : Segment k, (∀ x ∈ D.carrier, x ∈ s) → D.len ≤ Γ.len) (hD : ∀ x ∈ D.carrier, x ∈ s) :
    ¬ Γ.Linked D := by
  rintro ⟨⟨U, hU⟩, -, h2⟩
  have h3 : U.len ≤ Γ.len := hm U fun x hx => by
    rw [hU] at hx
    exact hx.elim (hΓ x) (hD x)
  have h4 : Γ.carrier ⊂ U.carrier := by
    rw [hU]
    exact ⟨Set.subset_union_left, fun h => h2 (Set.subset_union_right.trans h)⟩
  have h5 := Set.ncard_lt_ncard h4 (Set.finite_range U.term)
  rw [ncard_carrier, ncard_carrier] at h5
  omega

theorem exists_unlinked (n : ℕ) : ∀ s : Multiset (IrrGL (k := k)), Multiset.card s = n → (∀ y ∈ s, y.IsCusp) →
    ∃ m : Multiset (Segment k), (∀ D ∈ m, ∀ D' ∈ m, ¬ D.Linked D') ∧ m.bind Segment.ms = s := by
  classical
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro s hn hs
    rcases Multiset.empty_or_exists_mem s with rfl | ⟨y, hy⟩
    · exact ⟨0, by simp, by simp⟩
    obtain ⟨Γ, hΓ, hm⟩ := exists_longest hy (hs y hy)
    have hle := ms_le hΓ
    have hsub : ∀ x ∈ s - Γ.ms, x ∈ s := fun x hx => Multiset.mem_of_le (Multiset.sub_le_self _ _) hx
    have hcard : Multiset.card (s - Γ.ms) < n := by
      have h1 := Multiset.card_sub hle
      have h2 := Multiset.card_le_card hle
      have h3 := Γ.len_pos
      rw [Segment.card_ms] at h1 h2
      omega
    obtain ⟨m, hu, hb⟩ := ih _ hcard _ rfl fun x hx => hs x (hsub x hx)
    have hin : ∀ D ∈ m, ∀ x ∈ D.carrier, x ∈ s := fun D hD x hx =>
      hsub x (hb ▸ Multiset.mem_bind.2 ⟨D, hD, Segment.mem_ms.2 hx⟩)
    have hΓD : ∀ D ∈ m, ¬ Γ.Linked D := fun D hD => not_linked_of_longest hΓ hm (hin D hD)
    refine ⟨Γ ::ₘ m, fun D hD D' hD' => ?_, ?_⟩
    · rcases Multiset.mem_cons.1 hD with e | e₁ <;> rcases Multiset.mem_cons.1 hD' with e' | e₂
      · rw [e, e']
        exact Segment.not_linked_self _
      · rw [e]
        exact hΓD _ e₂
      · rw [e']
        exact fun h => hΓD _ e₁ h.symm
      · exact hu _ e₁ _ e₂
    · rw [Multiset.cons_bind, hb]
      exact add_tsub_cancel_of_le hle

theorem unlinkedLayers (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    UnlinkedLayers k := by
  intro s hs
  obtain ⟨m, hu, hb⟩ := exists_unlinked _ s rfl hs
  have hmem : ∀ i : Fin m.toList.length, m.toList.get i ∈ m := fun i =>
    Multiset.mem_toList.1 (List.get_mem _ _)
  refine ⟨m.toList.length, m.toList.get, fun i j _ => hu _ (hmem i) _ (hmem j), ?_⟩
  have h1 : (Finset.univ.val.map m.toList.get : Multiset (Segment k)) = m := by
    rw [Fin.univ_val_map, List.ofFn_get, Multiset.coe_toList]
  conv_rhs => rw [← hb, ← h1]
  simp [Multiset.bind, Multiset.map_map, Function.comp_def]

end GlobalTheory.CompanionTheory.SegLayers

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnlinkedLayersHoldStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unlinked_layers_hold : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], UnlinkedLayers k := by
  first | exact @GlobalTheory.CompanionTheory.SegLayers.unlinkedLayers | exact GlobalTheory.CompanionTheory.SegLayers.unlinkedLayers | (intros; apply GlobalTheory.CompanionTheory.SegLayers.unlinkedLayers <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalSupportRealisedByProduct
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultiProdEquivStandardBlocks
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultiProdEquivStandardBlocks
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.GenMultiProd

theorem multiProd_equiv_stdBlocks : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) (e : (Σ a, Fin (d a)) ≃ Fin N) (X : Fin h → Type) [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (π : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a)), Nonempty ((multiProd e π).Equiv (multiProd (stdBlocks d hd) π)) := by
  intro k _ _ _ _ h N d hd e X _ _ π
  exact (GlobalTheory.SmGL.Placing.parInd_jac_placing k (Fin h) (Fin N) (fun a => Fin (d a)) e (stdBlocks d hd) _).1 _

end GlobalTheory.CompanionTheory.GenMultiProd
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultiProdEquivStandardBlocksStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multiProd_equiv_standard_blocks : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) (e : (Σ a, Fin (d a)) ≃ Fin N) (X : Fin h → Type) [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (π : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a)), Nonempty ((multiProd e π).Equiv (multiProd (stdBlocks d hd) π)) := by
  first | exact @GlobalTheory.CompanionTheory.GenMultiProd.multiProd_equiv_stdBlocks | exact GlobalTheory.CompanionTheory.GenMultiProd.multiProd_equiv_stdBlocks | (intros; apply GlobalTheory.CompanionTheory.GenMultiProd.multiProd_equiv_stdBlocks <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalSupportRealisedByProduct
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.GenSupp

theorem hasSupport_std : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) (s : Multiset (IrrGL (k := k))), HasSupport π s → ∃ (h : ℕ) (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N), Finset.univ.val.map x = s ∧ (∀ a, (x a).IsCusp) ∧ IsSubquotient π (prodIrr x hd) := by
  intro k _ _ _ _ N V _ _ π s hπ
  obtain ⟨h, x, hs, -, hc, e, hsq⟩ := hπ
  have hd : ∑ a, (x a).1 = N := by
    have := Fintype.card_congr e
    simpa [Fintype.card_sigma] using this
  obtain ⟨φ⟩ := GlobalTheory.T.multiProd_equiv_standard_blocks k (fun a => (x a).1) hd e _ (fun a => (x a).rep)
  exact ⟨h, x, hd, hs, fun a => ⟨(hc a).1, (hc a).2.2⟩, hsq.trans (GlobalTheory.JacStages.isSubquotient_of_equiv φ)⟩

end GlobalTheory.CompanionTheory.GenSupp
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalSupportRealisedByProductStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspidal_support_realised_by_product : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) (s : Multiset (IrrGL (k := k))), HasSupport π s → ∃ (h : ℕ) (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N), Finset.univ.val.map x = s ∧ (∀ a, (x a).IsCusp) ∧ IsSubquotient π (prodIrr x hd) := by
  first | exact @GlobalTheory.CompanionTheory.GenSupp.hasSupport_std | exact GlobalTheory.CompanionTheory.GenSupp.hasSupport_std | (intros; apply GlobalTheory.CompanionTheory.GenSupp.hasSupport_std <;> assumption)
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.Realize
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL

namespace GlobalTheory.RgGu

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem sum_map_fst_ms (Δ : Segment k) : (Δ.ms.map Sigma.fst).sum = Δ.deg := by
  rw [Segment.ms, Multiset.map_map, ← Δ.sum_term_fst]
  rfl

theorem unlinkedRealize_of (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hL : GlobalTheory.BZSeg.LUnlinkedIrr k)
    (hG : GlobalTheory.BZSeg.LSegGeneric k) (hP : GlobalTheory.BZMir.Leib.GenericProdIff k) : UnlinkedRealize k := by
  intro N s hs hN
  obtain ⟨h, Δ, hun, hbind⟩ := GlobalTheory.T.unlinked_layers_hold k s hs
  choose π hπ using fun i => GlobalTheory.T.exists_segment_representation hA (Δ i)
  let x : Fin h → IrrGL (k := k) := fun i => IrrGL.of (π i).ρ (π i).smooth (π i).irr
  have hx : ∀ i, IsLSeg (Δ i) (x i).rep := fun i => (hπ i).of_equiv (IrrGL.equivOf _ _ _)
  have hd : ∑ a, (x a).1 = N := by
    rw [← hN, ← hbind, Multiset.map_bind, Multiset.sum_bind]
    change ∑ a, (Δ a).deg = _
    rw [Finset.sum_eq_multiset_sum]
    congr 1
    exact Multiset.map_congr rfl fun i _ => (sum_map_fst_ms (Δ i)).symm
  have hirr : (prodIrr x hd).IsIrreducible :=
    hL h N Δ x hd (fun i j => if e : i = j then e ▸ Segment.not_linked_self _ else hun i j e) hx
  refine ⟨h, Δ, x, hd, hun, hx, ?_, ?_⟩
  · have := GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_of_isSubquotient_prodIrr (t := fun i => (Δ i).ms)
      (fun i => (hx i).hasSupport) hirr (IsSubquotient.refl _)
    rwa [show (∑ i, (Δ i).ms) = s from hbind] at this
  · exact (hP h N (fun a => (x a).1) hd (fun a => (x a).2.rep.V) (fun a => (x a).rep)
      (fun a => (x a).2.rep.smooth)).2 fun i => hG (Δ i) _ _ _ (hx i)

theorem unlinkedRealize (hJ : Zc.LSegJacquet k) (hN : GlobalTheory.BZSeg.NuPair k) : UnlinkedRealize k :=
  unlinkedRealize_of PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top
    (GlobalTheory.RgGu.Unl.lUnlinkedIrr_nu k hJ PositivityTheory.Geo.geometricLemmaFiltration hN)
    (GlobalTheory.T.segment_generic_of_jacquet_nu_pair k PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top hJ hN)
    (GlobalTheory.T.whittaker_heredity_generic_product k (PositivityTheory.rg.gu.hered2.whitHeredity_all k))

end GlobalTheory.RgGu

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.TopAll
section -- merged from Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.ExistsEquivOfMapUnivEq
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL

namespace GlobalTheory.RgGu

theorem exists_equiv_of_map_univ_eq {α : Type*} {h h' : ℕ} (x : Fin h → α) (y : Fin h' → α)
    (H : Finset.univ.val.map x = Finset.univ.val.map y) : ∃ e : Fin h ≃ Fin h', ∀ a, y (e a) = x a := by
  classical
  have hc : ∀ v, Fintype.card {a // x a = v} = Fintype.card {b // y b = v} := fun v => by
    have := congrArg (Multiset.count v) H
    simp only [Multiset.count_map] at this
    simp only [Fintype.card_subtype, Finset.card_def, Finset.filter_val, eq_comm (b := v)]
    exact this
  exact ⟨Equiv.ofFiberEquiv fun v => Fintype.equivOfCardEq (hc v), fun a => Equiv.ofFiberEquiv_map _ a⟩

theorem genericUnique_of_perm {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hH : GlobalTheory.BZMir.Leib.WhitHeredity k) (hW : GlobalTheory.BZSeg.WhitRankIrr k)
    (hC : GlobalTheory.BZSeg.CuspGeneric k)
    (hP : GlobalTheory.Published.IrreducibleAdmissibleGL → Zc.Cos.GKLocal k → GlobalTheory.BZMir.Leib.WhitHeredity k → GlobalTheory.BZSeg.WhitRankIrr k → GlobalTheory.BZSeg.CuspGeneric k → ∀ (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ {h N : ℕ} (x : Fin h → IrrGL (k := k)), (∀ a, (x a).IsCusp) → ∀ (hd : ∑ a, (x a).1 = N) (τ : Equiv.Perm (Fin h)) (hd' : ∑ a, (x (τ a)).1 = N) {W : Type} [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GL (Fin N) k) W), IsSmooth σ → σ.IsIrreducible → IsGenericFor ψ σ → IsSubquotient σ (prodIrr x hd) → IsSubquotient σ (prodIrr (fun a => x (τ a)) hd')) :
    GenericUnique k := by
  intro N s V W _ _ _ _ π σ hπ hσ gπ gσ
  obtain ⟨ψ, hψc, hψ1, gπψ⟩ := gπ
  have gσψ : IsGenericFor ψ σ := (isGeneric_iff_isGenericFor hψc hψ1 σ).1 gσ
  obtain ⟨h, x, hd, hxs, hxc, hπx⟩ := GlobalTheory.T.cuspidal_support_realised_by_product k π s hπ
  obtain ⟨h', y, hd', hys, hyc, hσy⟩ := GlobalTheory.T.cuspidal_support_realised_by_product k σ s hσ
  obtain ⟨e, he⟩ := exists_equiv_of_map_univ_eq x y (hxs.trans hys.symm)
  have hh : h = h' := by simpa using Fintype.card_congr e
  subst hh
  have hfun : (fun a => y (e a)) = x := funext he
  subst hfun
  have hσx : IsSubquotient σ (prodIrr (fun a => y (e a)) hd) :=
    hP hA (GlobalTheory.T.gelfand_kazhdan_local hA) hH hW hC ψ hψc hψ1 y hyc hd' e hd σ hσ.isSmooth hσ.isIrreducible gσψ hσy
  exact GlobalTheory.T.whittaker_rank_extension_bound k ψ hψc N (prodIrr (fun a => y (e a)) hd) π σ (isSmooth_prodIrr _ hd)
    (GlobalTheory.T.whittaker_rank_product_le_one k hH hW ψ hψc hψ1 h N _ hd) hπ.isIrreducible hσ.isIrreducible hπx hσx gπψ gσψ

theorem perm_abs {α : Type 1} {h : ℕ} (P : (Fin h → α) → Prop)
    (hP : ∀ (y : Fin h → α) (j : ℕ) (hj : j + 1 < h), P y → P fun a => y (Equiv.swap ⟨j, by omega⟩ ⟨j + 1, hj⟩ a))
    (x : Fin h → α) (hx : P x) (τ : Equiv.Perm (Fin h)) : P fun a => x (τ a) := by
  rcases h with _ | n
  · obtain rfl : τ = 1 := Subsingleton.elim _ _
    exact hx
  have hτ : τ ∈ Submonoid.closure (Set.range fun i : Fin n => Equiv.swap i.castSucc i.succ) := by
    rw [Equiv.Perm.mclosure_swap_castSucc_succ]; trivial
  induction hτ using Submonoid.closure_induction_right with
  | one => exact hx
  | mul_right t ht s hs' ih =>
    obtain ⟨i, rfl⟩ := hs'
    exact hP (fun a => x (t a)) i.1 (by omega) ih

theorem perm_of_swap : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → Zc.Cos.GKLocal k → GlobalTheory.BZMir.Leib.WhitHeredity k → GlobalTheory.BZSeg.WhitRankIrr k → GlobalTheory.BZSeg.CuspGeneric k → ∀ (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ {h N : ℕ} (x : Fin h → IrrGL (k := k)), (∀ a, (x a).IsCusp) → ∀ (hd : ∑ a, (x a).1 = N) (τ : Equiv.Perm (Fin h)) (hd' : ∑ a, (x (τ a)).1 = N) {W : Type} [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GL (Fin N) k) W), IsSmooth σ → σ.IsIrreducible → IsGenericFor ψ σ → IsSubquotient σ (prodIrr x hd) → IsSubquotient σ (prodIrr (fun a => x (τ a)) hd') := by
  intro k _ _ _ _ hA hG hH hW hC ψ hc h1 h N x hx hd τ hd' W _ _ σ hs hi hg hσ
  let P : (Fin h → IrrGL (k := k)) → Prop := fun y =>
    (∀ a, (y a).IsCusp) ∧ ∃ e : ∑ a, (y a).1 = N, IsSubquotient σ (prodIrr y e)
  have step : ∀ (y : Fin h → IrrGL (k := k)) (j : ℕ) (hj : j + 1 < h), P y →
      P fun a => y (Equiv.swap ⟨j, by omega⟩ ⟨j + 1, hj⟩ a) := by
    rintro y j hj ⟨c, e, H⟩
    have e' : ∑ a, (y (Equiv.swap ⟨j, by omega⟩ ⟨j + 1, hj⟩ a)).1 = N :=
      (Equiv.sum_comp (Equiv.swap ⟨j, by omega⟩ ⟨j + 1, hj⟩) fun a => (y a).1).trans e
    exact ⟨fun a => c _, e', @GlobalTheory.T.cuspidal_swap_product_generic k _ _ _ _ hA hG hH hW hC ψ hc h1 h N y c e j hj e' W _ _ σ hs hi hg H⟩
  obtain ⟨-, e, H⟩ := perm_abs P step x ⟨hx, hd, hσ⟩ τ
  exact H

theorem genericUnique_of {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hH : GlobalTheory.BZMir.Leib.WhitHeredity k) (hW : GlobalTheory.BZSeg.WhitRankIrr k)
    (hC : GlobalTheory.BZSeg.CuspGeneric k) : GenericUnique k :=
  genericUnique_of_perm hA hH hW hC (@perm_of_swap k _ _ _ _)

end GlobalTheory.RgGu

end
end

namespace GlobalTheory.RgGu

theorem genericUnique (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    GenericUnique k :=
  genericUnique_of PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top (PositivityTheory.rg.gu.hered2.whitHeredity_all k)
    (PositivityTheory.rg.gu.whit.whitRankIrr k) (GlobalTheory.BZSeg.Cusp.cuspGeneric k)

end GlobalTheory.RgGu
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.GenericUnlinkedGLOf
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL

namespace GlobalTheory.RgGu

theorem suppExists (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    SuppExists k := by
  intro N V _ _ π hs hi
  have hG : GlobalTheory.Published.GeometricLemma := GlobalTheory.T.geometricLemma_of_bzFiniteness_of_filtration GlobalTheory.T.bernstein_zelevinsky_finiteness PositivityTheory.Geo.geometricLemmaFiltration
  obtain ⟨s, h⟩ := GlobalTheory.CompanionTheory.Hypotheses₂.TD.exists_hasSupport GlobalTheory.T.bernstein_zelevinsky_finiteness hG (IrrGL.of π hs hi)
  exact ⟨s, h.of_equiv (IrrGL.equivOf π hs hi).symm⟩

theorem genericUnlinkedGL_of
    (hS : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k],
      SuppExists k)
    (hU : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k],
      GenericUnique k)
    (hR : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k],
      UnlinkedRealize k) :
    GlobalTheory.Published.GenericUnlinkedGL := by
  intro k _ _ _ _ _ N V _ _ π hs hi hg
  obtain ⟨s, hsupp⟩ := hS k N V π hs hi
  have hsum : (s.map Sigma.fst).sum = N := by simpa using hsupp.sum_fst
  obtain ⟨h, Δ, x, hd, hΔ, hL, hx, hxg⟩ := hR k N s (fun y hy => hsupp.isCusp hy) hsum
  exact ⟨h, Δ, x, hd, hΔ, hL, hU k N s V _ π (prodIrr x hd) hsupp hx hg hxg⟩

end GlobalTheory.RgGu

end
end

namespace GlobalTheory.RgGu

theorem genericUnlinkedGL_of_segRep2 (hZ : GlobalTheory.Published.SegmentRepresentation) : GlobalTheory.Published.GenericUnlinkedGL :=
  genericUnlinkedGL_of (fun k _ _ _ _ _ => suppExists k) (fun k _ _ _ _ _ => genericUnique k)
    (fun k _ _ _ _ _ => unlinkedRealize (k := k)
      (GlobalTheory.CompanionTheory.SegCoarse.lSegJacquet PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top hZ) (GlobalTheory.RgGu.Nup2.nuPair k))

end GlobalTheory.RgGu
