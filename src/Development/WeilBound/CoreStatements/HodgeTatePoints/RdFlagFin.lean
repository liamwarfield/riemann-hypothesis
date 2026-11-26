module

public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.TeichmullerCharacterExists
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ChartBundleBaseExtension

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.StableHopfOrderSubgroupCharacters
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.StableHopfOrderSubgroupCharacters
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open PositivityTheory.HtPt.Rc ReciprocityTheory.PGsh.L2.SecondCohomologyLattice
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.stable_hopf_order_subgroup_characters : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable (F := F) AA.carrier → ∀ (K : Submodule F N) (χ : MulChar F R) (a b c : NNReal), HasLen v R (OmType (AA.carrier.map (LinearMap.funLeft R C (Subtype.val : K → N))) χ) a → HasLen v R (OmType (AA.carrier.comap (LinearMap.funLeft R C (K.mkQ : N → N ⧸ K))) χ) b → HasLen v R (OmType AA.carrier χ) c → a * b ≤ c := by
  intro p _ C _ _ _ v R _ _ hv hvp F _ _ _ _ f _ N _ _ _ _ AA hAA K χ a b c ha hb hc
  have hu := exists_inv_card (F := F) hv p hvp
  have hQ : FStable (F := F) (AA.carrier.comap (LinearMap.funLeft R C K.mkQ)) := by
    intro a g hg
    have hg' := hAA a _ hg
    show LinearMap.funLeft R C K.mkQ _ ∈ AA.carrier
    convert hg' using 1
    funext x
    show g (a • K.mkQ x) = g (K.mkQ (a • x))
    rw [map_smul]
  have hsq : FStable (F := F) (sqIdeal (augIdeal AA.carrier)) :=
    fun a _ hg => sq_pull (LinearMap.lsmul F N a).toAddMonoidHom _ _ (hAA a) hg
  have proj_mem {X : Type} [AddCommGroup X] [Module F X] (χ : MulChar F R)
      (S : Submodule R (X → C)) (hS : FStable (F := F) S) {g : X → C} (hg : g ∈ S) :
      projL χ g ∈ S := by
    obtain ⟨u, hu⟩ := hu
    have hproj : projL χ g = u • ∑ a : Fˣ, χ⁻¹ (a : F) • (fun x => g ((a : F) • x)) := by
      funext x
      rw [projL_apply, Pi.smul_apply, Finset.sum_apply, Algebra.smul_def, hu]
      exact congrArg _ (Finset.sum_congr rfl fun a _ => (Algebra.smul_def _ _).symm)
    rw [hproj]
    exact S.smul_mem _ (S.sum_mem fun a _ => S.smul_mem _ (hS _ g hg))
  have proj_eig {X : Type} [AddCommGroup X] [Module F X] (χ : MulChar F R)
      {M : Submodule R (X → C)} (hM : FStable (F := F) M) {g : X → C} (hg : g ∈ augIdeal M) :
      projL χ g ∈ eig M χ := by
    rw [mem_aug] at hg
    refine ⟨proj_mem χ M hM hg.1, fun a x => ?_⟩
    by_cases ha : a = 0
    · rw [ha, zero_smul, MulChar.map_zero, map_zero, zero_mul, projL_apply]
      simp only [smul_zero, hg.2, mul_zero, Finset.sum_const_zero]
    · obtain ⟨a, rfl⟩ := isUnit_iff_ne_zero.2 ha
      rw [projL_apply, projL_apply, mul_left_comm, Finset.mul_sum Finset.univ _ (algebraMap R C _),
        ← Equiv.sum_comp (Equiv.mulRight a) (fun b : Fˣ => algebraMap R C (χ (a : F)) *
          (algebraMap R C (χ⁻¹ (b : F)) * g ((b : F) • x)))]
      congr 1
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [Equiv.coe_mulRight, Units.val_mul, mul_smul, ← mul_assoc, ← map_mul, map_mul χ⁻¹,
        mul_left_comm, mul_inv_unit, mul_one]
  rw [mul_comm]
  refine len_mul_le hv (omMap χ K.mkQ (AA.carrier.comap (LinearMap.funLeft R C K.mkQ)) AA.carrier
      (fun _ hg => hg))
    (omMap χ K.subtype AA.carrier (AA.carrier.map (LinearMap.funLeft R C K.subtype))
      (fun _ hg => Submodule.mem_map_of_mem hg)) ?_ ?_ hb hc ha
  · intro y
    obtain ⟨⟨h, hh⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨g, hg, hgh⟩ := hh.1
    have hga : g ∈ augIdeal AA.carrier := by
      rw [mem_aug]
      refine ⟨hg, ?_⟩
      have := ((mem_aug _ _).1 (eig_le_aug _ χ hh)).2
      rw [← hgh] at this
      exact this
    refine ⟨Submodule.Quotient.mk ⟨projL χ g, proj_eig χ hAA hga⟩, ?_⟩
    refine congrArg Submodule.Quotient.mk (Subtype.ext ?_)
    show LinearMap.funLeft R C K.subtype (projL χ g) = h
    rw [← projL_funLeft, ← projL_self χ hh, ← hgh]
  · intro x hx
    obtain ⟨⟨g, hg⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have hx' := (Submodule.Quotient.mk_eq_zero _).1 hx
    obtain ⟨q, hq, hgq⟩ := om_exact hv AA K.subtype.toAddMonoidHom K.mkQ.toAddMonoidHom
      K.mkQ_surjective Subtype.val_injective (range_subtype_eq K) g (eig_le_aug _ χ hg) hx'
    refine ⟨Submodule.Quotient.mk ⟨projL χ q, proj_eig χ hQ hq⟩, ?_⟩
    symm
    refine (Submodule.Quotient.eq _).2 ?_
    show g - LinearMap.funLeft R C K.mkQ (projL χ q) ∈ sqIdeal (augIdeal AA.carrier)
    have := proj_mem χ _ hsq hgq
    rw [map_sub, projL_self χ hg] at this
    rw [← projL_funLeft]
    exact this
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.StableHopfOrderSubgroupCharactersStatement
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stable_hopf_order_subgroup_characters : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable F AA.carrier → ∀ (K : Submodule F N) (χ : MulChar F R) (a b c : NNReal), HasLen v R (OmType (AA.carrier.map (LinearMap.funLeft R C (Subtype.val : K → N))) χ) a → HasLen v R (OmType (AA.carrier.comap (LinearMap.funLeft R C (K.mkQ : N → N ⧸ K))) χ) b → HasLen v R (OmType AA.carrier χ) c → a * b ≤ c := by
  first | exact @GlobalTheory.CompanionTheory.Relay.stable_hopf_order_subgroup_characters | exact GlobalTheory.CompanionTheory.Relay.stable_hopf_order_subgroup_characters | (intros; apply GlobalTheory.CompanionTheory.Relay.stable_hopf_order_subgroup_characters <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.StableHopfOrderSubgroupRestriction
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.StableHopfOrderSubgroupRestriction
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace GlobalTheory.CompanionTheory.Ar.GR

theorem subquoHopfOrder : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable (F := F) AA.carrier → ∀ (K : Submodule F N) [Fintype K] [DecidableEq K] [Fintype (N ⧸ K)] [DecidableEq (N ⧸ K)], (∃ AK : HopfOrder (C := C) R K, AK.carrier = (AA.carrier.map (LinearMap.funLeft R C (Subtype.val : K → N))) ∧ FStable (F := F) AK.carrier) ∧ (∃ AQ : HopfOrder (C := C) R (N ⧸ K), AQ.carrier = (AA.carrier.comap (LinearMap.funLeft R C (K.mkQ : N → N ⧸ K))) ∧ FStable (F := F) AQ.carrier) ∧ invFun AA.carrier K.toAddSubgroup = (AA.carrier.comap (LinearMap.funLeft R C (K.mkQ : N → N ⧸ K))).map (LinearMap.funLeft R C (K.mkQ : N → N ⧸ K)) ∧ ∀ c cQ cK, HasColen R v AA.carrier c → HasColen R v (AA.carrier.comap (LinearMap.funLeft R C (K.mkQ : N → N ⧸ K))) cQ → HasColen R v (AA.carrier.map (LinearMap.funLeft R C (Subtype.val : K → N))) cK → c = cQ ^ Fintype.card K * cK ^ Fintype.card (N ⧸ K) :=
  by
    intro p _ C _ _ _ v R _ _ hv _ F _ _ _ _ f _ N _ _ _ _ AA hAA K _ _ _ _
    have hres : FStable (F := F)
        (AA.carrier.map (LinearMap.funLeft R C (Subtype.val : K → N))) := by
      rintro a _ ⟨g, hg, rfl⟩
      exact ⟨_, hAA a g hg, rfl⟩
    have hquo : FStable (F := F)
        (AA.carrier.comap (LinearMap.funLeft R C (K.mkQ : N → N ⧸ K))) := by
      intro a g hg
      have h := hAA a _ hg
      show LinearMap.funLeft R C (K.mkQ : N → N ⧸ K) _ ∈ AA.carrier
      convert h using 1
      funext x
      show g (K.mkQ (a • x)) = g (a • K.mkQ x)
      rw [map_smul]
    have hrange : K.subtype.toAddMonoidHom.range = K.mkQ.toAddMonoidHom.ker := by
      ext x
      simp [AddMonoidHom.mem_range, AddMonoidHom.mem_ker]
    refine ⟨?_, ?_, ?_, ?_⟩
    · obtain ⟨AK, hAK⟩ := PositivityTheory.HtPt.Rc.exists_res hv AA
        K.subtype.toAddMonoidHom Subtype.val_injective
      exact ⟨AK, hAK, hAK ▸ hres⟩
    · obtain ⟨AQ, hAQ⟩ := PositivityTheory.HtPt.Rc.exists_quo hv AA
        K.mkQ.toAddMonoidHom K.mkQ_surjective
      exact ⟨AQ, hAQ, hAQ ▸ hquo⟩
    · exact PositivityTheory.HtPt.Rc.invFun_eq _ K.mkQ.toAddMonoidHom
        K.mkQ_surjective _ (fun x => by simp)
    · intro c cQ cK hc hQ hK
      exact PositivityTheory.HtPt.Rc.colen_ses hv AA K.subtype.toAddMonoidHom
        Subtype.val_injective K.mkQ.toAddMonoidHom K.mkQ_surjective hrange c cQ cK hc hQ hK

end GlobalTheory.CompanionTheory.Ar.GR
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.StableHopfOrderSubgroupRestrictionStatement
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stable_hopf_order_subgroup_restriction : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable F AA.carrier → ∀ (K : Submodule F N) [Fintype K] [DecidableEq K] [Fintype (N ⧸ K)] [DecidableEq (N ⧸ K)], (∃ AK : HopfOrder (C := C) R K, AK.carrier = (AA.carrier.map (LinearMap.funLeft R C (Subtype.val : K → N))) ∧ FStable F AK.carrier) ∧ (∃ AQ : HopfOrder (C := C) R (N ⧸ K), AQ.carrier = (AA.carrier.comap (LinearMap.funLeft R C (K.mkQ : N → N ⧸ K))) ∧ FStable F AQ.carrier) ∧ invFun AA.carrier K.toAddSubgroup = (AA.carrier.comap (LinearMap.funLeft R C (K.mkQ : N → N ⧸ K))).map (LinearMap.funLeft R C (K.mkQ : N → N ⧸ K)) ∧ ∀ c cQ cK, HasColen R v AA.carrier c → HasColen R v (AA.carrier.comap (LinearMap.funLeft R C (K.mkQ : N → N ⧸ K))) cQ → HasColen R v (AA.carrier.map (LinearMap.funLeft R C (Subtype.val : K → N))) cK → c = cQ ^ Fintype.card K * cK ^ Fintype.card (N ⧸ K) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GR.subquoHopfOrder | exact GlobalTheory.CompanionTheory.Ar.GR.subquoHopfOrder | (intros; apply GlobalTheory.CompanionTheory.Ar.GR.subquoHopfOrder <;> assumption)
end
end

section -- merged from Development.WeilBound.CoreStatements.HodgeTatePoints.RdFlag
section -- merged from Development.WeilBound.CoreStatements.HodgeTatePoints.RdChain
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace PositivityTheory.HtPt.Rd

section

variable {F : Type} [Field F] {N : Type} [AddCommGroup N] [Module F N]

structure IsChain (n : ℕ) (K : ℕ → Submodule F N) (t : ℕ → N) : Prop where
  mono : Monotone K
  zero : K 0 = ⊥
  top : K n = ⊤
  succ : ∀ i < n, K (i + 1) = K i ⊔ Submodule.span F {t i}
  notMem : ∀ i < n, t i ∉ K i

theorem IsChain.quot {n : ℕ} {K : ℕ → Submodule F N} {t : ℕ → N} (h : IsChain n K t) (j : ℕ) :
    IsChain (n - j) (fun i => (K (j + i)).map (K j).mkQ) (fun i => (K j).mkQ (t (j + i))) := by
  exact {
    mono := fun a b hab => Submodule.map_mono (h.mono (by omega))
    zero := by simp
    top := by
      have : K (j + (n - j)) = ⊤ := top_le_iff.1 (h.top ▸ h.mono (by omega))
      simp only [this, Submodule.map_top, Submodule.range_mkQ]
    succ := fun i hi => by
      simp only [← add_assoc]
      rw [h.succ (j + i) (by omega), Submodule.map_sup, Submodule.map_span, Set.image_singleton]
    notMem := fun i hi hm => by
      apply h.notMem (j + i) (by omega)
      have : t (j + i) ∈ ((K (j + i)).map (K j).mkQ).comap (K j).mkQ := hm
      rwa [Submodule.comap_map_eq, Submodule.ker_mkQ, sup_eq_left.2 (h.mono (by omega))] at this
  }

theorem IsChain.mem {n : ℕ} {K : ℕ → Submodule F N} {t : ℕ → N} (h : IsChain n K t) {i j : ℕ}
    (hi : i < min j n) : t i ∈ K j := by
  apply h.mono (show i + 1 ≤ j by omega)
  rw [h.succ i (by omega)]
  exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)

open Classical in
theorem IsChain.sub {n : ℕ} {K : ℕ → Submodule F N} {t : ℕ → N} (h : IsChain n K t) (j : ℕ) :
    IsChain (min j n) (fun i => (K i).comap (K j).subtype)
      (fun i => if hi : t i ∈ K j then ⟨t i, hi⟩ else 0) := by
  exact {
    mono := fun a b hab => Submodule.comap_mono (h.mono hab)
    zero := by simp [h.zero]
    top := by
      rw [Submodule.comap_subtype_eq_top]
      rcases le_total j n with h1 | h1
      · rw [min_eq_left h1]
      · rw [min_eq_right h1, h.top]; exact le_top
    succ := fun i hi => by
      apply Submodule.map_injective_of_injective (K j).injective_subtype
      simp only [dite_eq_left (h.mem hi)]
      rw [Submodule.map_sup, Submodule.map_span, Set.image_singleton, Submodule.map_comap_subtype,
        Submodule.map_comap_subtype, inf_eq_right.2 (h.mono (by omega)),
        inf_eq_right.2 (h.mono (by omega)), h.succ i (by omega)]
      rfl
    notMem := fun i hi hm => by
      apply h.notMem i (by omega)
      simp only [dite_eq_left (h.mem hi)] at hm
      exact hm
  }

theorem isChain_flag {n : ℕ} (b : Module.Basis (Fin n) F N) :
    IsChain n (flagSub b) (fun i => if h : i < n then b ⟨i, h⟩ else 0) := by
  exact {
    mono := fun a c hac => Submodule.span_mono (Set.image_mono fun j hj => lt_of_lt_of_le hj hac)
    zero := by simp [flagSub]
    top := by
      have : {j : Fin n | (j : ℕ) < n} = Set.univ := Set.eq_univ_of_forall fun j => j.2
      rw [flagSub, this, Set.image_univ, b.span_eq]
    succ := fun i hi => by
      have : {j : Fin n | (j : ℕ) < i + 1} = {j : Fin n | (j : ℕ) < i} ∪ {⟨i, hi⟩} := by
        ext j
        simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_singleton_iff, Fin.ext_iff]
        omega
      simp only [dite_eq_left hi]
      rw [flagSub, this, Set.image_union, Submodule.span_union, Set.image_singleton]
      rfl
    notMem := fun i hi => by
      simp only [dite_eq_left hi]
      exact b.linearIndependent.notMem_span_image (by simp)
  }

end

section

variable (hex : type_of% @GlobalTheory.T.teichmuller_character_exists) (hsq : type_of% @GlobalTheory.T.stable_hopf_order_subgroup_restriction)
  (hsplit : type_of% @GlobalTheory.T.stable_hopf_order_fundamental_ideal) (hos : type_of% @GlobalTheory.T.stable_hopf_order_subgroup_characters)
  (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
  (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C] (hv : v.Integers R)
  (hp : v (p : C) < 1) (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ)
  (hF : Fintype.card F = p ^ f)

include hex hsq hsplit hos hv hp hF

theorem chain_le (χ : MulChar F R) (n : ℕ) : ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N]
    [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable F AA.carrier →
    ∀ (K : ℕ → Submodule F N) (t : ℕ → N), IsChain n K t → ∀ (s : ℕ → NNReal) (r : NNReal),
    (∀ i < n, HasLen v R (OmType (stepOrder AA.carrier (K i) (t i)) χ) (s i)) →
    HasLen v R (OmType AA.carrier χ) r → ∏ i ∈ Finset.range n, s i ≤ r := by
  classical
  induction n with
  | zero =>
    intro N _ _ _ _ AA hst K t h s r hs hr
    have : Subsingleton N := (Submodule.subsingleton_iff F).1
      (subsingleton_of_bot_eq_top (h.zero.symm.trans h.top))
    rw [hasLen_trivial hv hr]
    simp
  | succ n ih =>
    intro N _ _ _ _ AA hst K t h s r hs hr
    obtain ⟨σ, hσ⟩ := hex p C v R hv hp F f hF
    have : Finite (N ⧸ K 1) := Finite.of_surjective _ (K 1).mkQ_surjective
    let _ : Fintype (N ⧸ K 1) := Fintype.ofFinite _
    let _ : Fintype (K 1) := Fintype.ofFinite _
    obtain ⟨-, ⟨AQ, hQ, hQs⟩, -⟩ := hsq p C v R hv hp F f hF N AA hst (K 1)
    obtain ⟨b, -, hb⟩ := (hsplit p C v R hv hp F f hF _ AQ hQs σ hσ).1 χ
    have h1 := ih _ AQ hQs _ _ (h.quot 1) (fun i => s (1 + i)) b (fun i hi => by
      rw [hQ, quot_step _ (h.mono (by omega))]
      exact hs _ (by omega)) hb
    have ht : t 0 ≠ 0 := fun h0 => h.notMem 0 (by omega) (h0 ▸ Submodule.zero_mem _)
    have h2 := hs 0 (by omega)
    rw [h.zero] at h2
    have h3 := hasLen_line _ ht h2
    have hK : Submodule.span F {t 0} = K 1 := by
      rw [h.succ 0 (by omega), h.zero, bot_sup_eq]
    rw [hK] at h3
    rw [hQ] at hb
    have h4 := hos p C v R hv hp F f hF N AA hst (K 1) χ _ _ _ h3 hb hr
    rw [add_comm n 1, Finset.prod_range_add]
    refine le_trans ?_ h4
    rw [Finset.prod_range_one]
    exact mul_le_mul_right h1 _

theorem chain_partial (hstep : type_of% @GlobalTheory.T.stable_hopf_order_subgroup_translation) (χ : MulChar F R) (n : ℕ) (N : Type)
    [AddCommGroup N] [Module F N] [Fintype N]
    [DecidableEq N] (AA : HopfOrder (C := C) R N) (hst : FStable F AA.carrier)
    (K : ℕ → Submodule F N) (t : ℕ → N) (h : IsChain n K t) (s : ℕ → NNReal)
    (hs : ∀ i < n, HasLen v R (OmType (stepOrder AA.carrier (K i) (t i)) χ) (s i))
    (hr : HasLen v R (OmType AA.carrier χ) (∏ i ∈ Finset.range n, s i)) (j : ℕ) :
    HasLen v R (OmType (AA.carrier.map (LinearMap.funLeft R C (Subtype.val : K j → N))) χ)
      (∏ i ∈ Finset.range (min j n), s i) := by
  classical
  obtain ⟨σ, hσ⟩ := hex p C v R hv hp F f hF
  have : Finite (N ⧸ K j) := Finite.of_surjective _ (K j).mkQ_surjective
  let _ : Fintype (N ⧸ K j) := Fintype.ofFinite _
  let _ : Fintype (K j) := Fintype.ofFinite _
  obtain ⟨⟨AK, hK, hKs⟩, ⟨AQ, hQ, hQs⟩, -⟩ := hsq p C v R hv hp F f hF N AA hst (K j)
  obtain ⟨a, -, ha⟩ := (hsplit p C v R hv hp F f hF _ AK hKs σ hσ).1 χ
  obtain ⟨b, hb0, hb⟩ := (hsplit p C v R hv hp F f hF _ AQ hQs σ hσ).1 χ
  have h1 := chain_le hex hsq hsplit hos p C v R hv hp F f hF χ _ _ AQ hQs _ _ (h.quot j)
    (fun i => s (j + i)) b (fun i hi => by
      rw [hQ, quot_step _ (h.mono (by omega))]
      exact hs _ (by omega)) hb
  have h2 := chain_le hex hsq hsplit hos p C v R hv hp F f hF χ _ _ AK hKs _ _ (h.sub j)
    s a (fun i hi => by
      rw [(hstep p C v R hv hp F f hF _ AK hKs _ _ ((h.sub j).notMem i hi)).2, hK,
        sub_stepRes _ (h.mono (by omega)), dite_eq_left (h.mem hi),
        ← (hstep p C v R hv hp F f hF _ AA hst _ _ (h.notMem i (by omega))).2]
      exact hs _ (by omega)) ha
  rw [hK] at ha
  rw [hQ] at hb
  have h4 := hos p C v R hv hp F f hF N AA hst (K j) χ _ _ _ ha hb hr
  have h5 : ∏ i ∈ Finset.range n, s i =
      (∏ i ∈ Finset.range (min j n), s i) * ∏ i ∈ Finset.range (n - j), s (j + i) := by
    rcases le_total j n with h6 | h6
    · rw [min_eq_left h6, ← Finset.prod_range_add, Nat.add_sub_cancel' h6]
    · rw [min_eq_right h6, Nat.sub_eq_zero_of_le h6, Finset.prod_range_zero, mul_one]
  rw [h5] at h4
  have h7 : a ≤ ∏ i ∈ Finset.range (min j n), s i :=
    le_of_mul_le_mul_right (h4.trans (mul_le_mul_right h1 _)) (pos_iff_ne_zero.2 hb0)
  rw [← le_antisymm h7 h2]
  exact ha

end

end PositivityTheory.HtPt.Rd
end

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace PositivityTheory.HtPt.Rd

theorem prod_ext {n : ℕ} (s : Fin n → NNReal) :
    ∏ i ∈ Finset.range n, (fun i => if h : i < n then s ⟨i, h⟩ else 1) i = ∏ i, s i := by
  rw [Finset.prod_range]
  simp

theorem prod_ext_min {n : ℕ} (s : Fin n → NNReal) (j : ℕ) :
    ∏ i ∈ Finset.range (min j n), (fun i => if h : i < n then s ⟨i, h⟩ else 1) i =
      ∏ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < j), s i := by
  have key : Finset.range (min j n) = (Finset.range n).filter (fun i => i < j) := by
    ext i
    simp only [Finset.mem_range, Finset.mem_filter, lt_min_iff]
    tauto
  rw [key, Finset.prod_filter, Finset.prod_filter,
    ← Fin.prod_univ_eq_prod_range (fun i => if i < j then (if h : i < n then s ⟨i, h⟩ else 1) else 1) n]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  simp

theorem flag_om_of (hex : type_of% @GlobalTheory.T.teichmuller_character_exists) (hsq : type_of% @GlobalTheory.T.stable_hopf_order_subgroup_restriction)
    (hsplit : type_of% @GlobalTheory.T.stable_hopf_order_fundamental_ideal) (hos : type_of% @GlobalTheory.T.stable_hopf_order_subgroup_characters) : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable F AA.carrier → ∀ (n : ℕ) (b : Module.Basis (Fin n) F N), ∀ (χ : MulChar F R) (s : Fin n → NNReal) (r : NNReal), (∀ i : Fin n, HasLen v R (OmType (stepOrder AA.carrier (flagSub b i) (b i)) χ) (s i)) → HasLen v R (OmType AA.carrier χ) r → ∏ i, s i ≤ r := by
  intro p _ C _ _ _ v R _ _ hR hp F _ _ _ _ f hcard N _ _ _ _ AA hst n b χ s r hs hr
  have key := chain_le hex hsq hsplit hos p C v R hR hp F f hcard χ n N AA hst (flagSub b)
    (fun i => if h : i < n then b ⟨i, h⟩ else 0) (isChain_flag b)
    (fun i => if h : i < n then s ⟨i, h⟩ else 1) r
    (by
      intro i hi
      have e1 : (if h : i < n then b ⟨i, h⟩ else 0) = b ⟨i, hi⟩ := dif_pos hi
      have e2 : (if h : i < n then s ⟨i, h⟩ else 1) = s ⟨i, hi⟩ := dif_pos hi
      show HasLen v R (OmType (stepOrder AA.carrier (flagSub b i)
        (if h : i < n then b ⟨i, h⟩ else 0)) χ) (if h : i < n then s ⟨i, h⟩ else 1)
      rw [e1, e2]
      exact hs ⟨i, hi⟩) hr
  rwa [prod_ext] at key

theorem gr_partial_of (hex : type_of% @GlobalTheory.T.teichmuller_character_exists) (hsq : type_of% @GlobalTheory.T.stable_hopf_order_subgroup_restriction)
    (hstep : type_of% @GlobalTheory.T.stable_hopf_order_subgroup_translation) (hsplit : type_of% @GlobalTheory.T.stable_hopf_order_fundamental_ideal)
    (hos : type_of% @GlobalTheory.T.stable_hopf_order_subgroup_characters) : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable F AA.carrier → ∀ (n : ℕ) (b : Module.Basis (Fin n) F N), ∀ (χ : MulChar F R) (s : Fin n → NNReal), (∀ i : Fin n, HasLen v R (OmType (stepOrder AA.carrier (flagSub b i) (b i)) χ) (s i)) → HasLen v R (OmType AA.carrier χ) (∏ i, s i) → ∀ j : ℕ, HasLen v R (OmType (AA.carrier.map (LinearMap.funLeft R C (Subtype.val : flagSub b j → N))) χ) (∏ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < j), s i) := by
  intro p _ C _ _ _ v R _ _ hR hp F _ _ _ _ f hcard N _ _ _ _ AA hst n b χ s hs hr j
  have key := chain_partial hex hsq hsplit hos p C v R hR hp F f hcard hstep χ n N AA hst (flagSub b)
    (fun i => if h : i < n then b ⟨i, h⟩ else 0) (isChain_flag b)
    (fun i => if h : i < n then s ⟨i, h⟩ else 1)
    (by
      intro i hi
      have e1 : (if h : i < n then b ⟨i, h⟩ else 0) = b ⟨i, hi⟩ := dif_pos hi
      have e2 : (if h : i < n then s ⟨i, h⟩ else 1) = s ⟨i, hi⟩ := dif_pos hi
      show HasLen v R (OmType (stepOrder AA.carrier (flagSub b i)
        (if h : i < n then b ⟨i, h⟩ else 0)) χ) (if h : i < n then s ⟨i, h⟩ else 1)
      rw [e1, e2]
      exact hs ⟨i, hi⟩)
    (by rwa [prod_ext]) j
  rwa [prod_ext_min] at key

end PositivityTheory.HtPt.Rd
end

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace PositivityTheory.HtPt.Rd

theorem flag_om : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable F AA.carrier → ∀ (n : ℕ) (b : Module.Basis (Fin n) F N), ∀ (χ : MulChar F R) (s : Fin n → NNReal) (r : NNReal), (∀ i : Fin n, HasLen v R (OmType (stepOrder AA.carrier (flagSub b i) (b i)) χ) (s i)) → HasLen v R (OmType AA.carrier χ) r → ∏ i, s i ≤ r :=
  flag_om_of @PositivityTheory.HtPt.Rb.fund_ex @PositivityTheory.HtPt.Rc.subquo @PositivityTheory.HtPt.Rc.om_split
    @PositivityTheory.HtPt.Rc.om_step

theorem gr_partial : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable F AA.carrier → ∀ (n : ℕ) (b : Module.Basis (Fin n) F N), ∀ (χ : MulChar F R) (s : Fin n → NNReal), (∀ i : Fin n, HasLen v R (OmType (stepOrder AA.carrier (flagSub b i) (b i)) χ) (s i)) → HasLen v R (OmType AA.carrier χ) (∏ i, s i) → ∀ j : ℕ, HasLen v R (OmType (AA.carrier.map (LinearMap.funLeft R C (Subtype.val : flagSub b j → N))) χ) (∏ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < j), s i) :=
  gr_partial_of @PositivityTheory.HtPt.Rb.fund_ex @PositivityTheory.HtPt.Rc.subquo @PositivityTheory.HtPt.Rc.step
    @PositivityTheory.HtPt.Rc.om_split @PositivityTheory.HtPt.Rc.om_step

end PositivityTheory.HtPt.Rd
