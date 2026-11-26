module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StabilizerEquivLocPart
namespace GlobalTheory.FinTrace

theorem stabilizer_equiv_locPart : ∀ (G : Type) [Group G] (H K : Subgroup G) (x : G),
    Nonempty (MulAction.stabilizer H (QuotientGroup.mk x : G ⧸ K) ≃ GlobalTheory.LKLoc.locPart H K x) := by
  intro G _ H K x
  have hmem : ∀ h : H, h ∈ MulAction.stabilizer H (QuotientGroup.mk x : G ⧸ K) ↔
      (h : G) ∈ GlobalTheory.LKLoc.locPart H K x := by
    intro h
    rw [MulAction.mem_stabilizer_iff]
    show ((h : G) • (QuotientGroup.mk x : G ⧸ K)) = _ ↔ _
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq]
    simp only [GlobalTheory.LKLoc.locPart, Subgroup.mem_inf, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      SetLike.coe_mem, true_and]
    constructor
    · intro hk
      refine ⟨_, K.inv_mem hk, ?_⟩
      group
    · rintro ⟨k, hk, e⟩
      rw [← e]
      convert K.inv_mem hk using 1
      group
  exact ⟨{ toFun := fun h => ⟨h.1, (hmem h.1).1 h.2⟩
           invFun := fun g => ⟨⟨g.1, g.2.1⟩, (hmem _).2 g.2⟩
           left_inv := fun h => rfl
           right_inv := fun g => rfl }⟩

theorem finite_support_conj : ∀ (G : Type) [Group G] (Γ K : Subgroup G) (f : G → ℂ), (∀ k ∈ K, ∀ g, f (g * k) = f g) →
    (Function.support fun q : G ⧸ K => f (Quotient.out q)).Finite → ∀ x : G, Finite (GlobalTheory.LKLoc.locPart Γ K x) →
    (Function.support fun γ : Γ => f (x⁻¹ * γ * x)).Finite := by
  intro G _ Γ K f hR hs x hx
  let π : Γ → G ⧸ K := fun γ => QuotientGroup.mk (x⁻¹ * γ * x)
  have hmaps : Set.MapsTo π (Function.support fun γ : Γ => f (x⁻¹ * γ * x)) (Function.support fun q : G ⧸ K => f q.out) := by
    intro γ hγ
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K (x⁻¹ * γ * x)
    simp only [Function.mem_support, π, hk, hR _ k.2] at hγ ⊢
    exact hγ
  refine Set.Finite.of_finite_fibers π (hs.subset (Set.image_subset_iff.2 hmaps)) ?_
  haveI := hx
  intro q _
  by_cases hne : (π ⁻¹' {q}).Nonempty
  · obtain ⟨γ₀, hγ₀⟩ := hne
    have hsub : π ⁻¹' {q} ⊆ (fun l : GlobalTheory.LKLoc.locPart Γ K x => γ₀ * ⟨l.1, l.2.1⟩) '' Set.univ := by
      intro γ hγ
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at hγ hγ₀
      have h := hγ₀.trans hγ.symm
      rw [QuotientGroup.eq] at h
      refine ⟨⟨(γ₀⁻¹ * γ : Γ), (γ₀⁻¹ * γ : Γ).2, ?_⟩, trivial, Subtype.ext (by simp)⟩
      refine ⟨_, h, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv]
      group
    exact ((Set.finite_univ.image _).subset hsub).subset Set.inter_subset_right
  · rw [Set.not_nonempty_iff_eq_empty.1 hne, Set.inter_empty]
    exact Set.finite_empty

end GlobalTheory.FinTrace
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemStabilizerIff
namespace GlobalTheory.MassConj

@[ext]
structure ConjPair (H X : Type) where

  elt : H

  pt : X

variable {H X : Type} [Group H] [MulAction H X]

instance : MulAction H (ConjPair H X) where
  smul δ p := ⟨δ * p.elt * δ⁻¹, δ • p.pt⟩
  one_smul p := by
    show ConjPair.mk _ _ = p
    ext <;> simp
  mul_smul δ ε p := by
    show ConjPair.mk (δ * ε * p.elt * (δ * ε)⁻¹) ((δ * ε) • p.pt) =
      ConjPair.mk (δ * (ε * p.elt * ε⁻¹) * δ⁻¹) (δ • ε • p.pt)
    ext
    · simp only; group
    · exact mul_smul δ ε p.pt

@[simp] theorem smul_elt (δ : H) (p : ConjPair H X) : (δ • p).elt = δ * p.elt * δ⁻¹ := rfl

@[simp] theorem smul_pt (δ : H) (p : ConjPair H X) : (δ • p).pt = δ • p.pt := rfl

theorem mem_stabilizer_iff (δ : H) (p : ConjPair H X) :
    δ ∈ MulAction.stabilizer H p ↔ δ * p.elt = p.elt * δ ∧ δ • p.pt = p.pt := by
  rw [MulAction.mem_stabilizer_iff, ConjPair.ext_iff, smul_elt, smul_pt]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    calc δ * p.elt = δ * p.elt * δ⁻¹ * δ := by group
      _ = p.elt * δ := by rw [h1]
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    rw [h1]; group

end GlobalTheory.MassConj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitSumLocalParts
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantsMonomialApproximation
open scoped Classical

namespace GlobalTheory.FinTrace

noncomputable def dcToOrbit (G : Type) [Group G] (H K : Subgroup G) :
    DoubleCoset.Quotient (H : Set G) (K : Set G) → MulAction.orbitRel.Quotient H (G ⧸ K) :=
  Quotient.lift (fun g : G => (Quotient.mk _ (QuotientGroup.mk g : G ⧸ K) : MulAction.orbitRel.Quotient H (G ⧸ K)))
    (by
      intro a b hab
      obtain ⟨h, hh, k, hk, rfl⟩ := DoubleCoset.rel_iff.1 hab
      apply Quotient.sound
      show _ ∈ MulAction.orbit H _
      refine ⟨⟨h⁻¹, H.inv_mem hh⟩, ?_⟩
      show ((h⁻¹ : G) • (QuotientGroup.mk (h * a * k) : G ⧸ K)) = _
      rw [MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq]
      simpa [mul_assoc] using hk)

theorem dcToOrbit_mk (G : Type) [Group G] (H K : Subgroup G) (g : G) :
    dcToOrbit G H K (Quotient.mk _ g) = Quotient.mk _ (QuotientGroup.mk g : G ⧸ K) := rfl

theorem dcToOrbit_bijective (G : Type) [Group G] (H K : Subgroup G) :
    Function.Bijective (dcToOrbit G H K) := by
  constructor
  · intro q₁ q₂ he
    induction q₁ using Quotient.inductionOn with | h a => ?_
    induction q₂ using Quotient.inductionOn with | h b => ?_
    rw [dcToOrbit_mk, dcToOrbit_mk] at he
    obtain ⟨h, hh⟩ := Quotient.exact he
    change ((h : G) • (QuotientGroup.mk b : G ⧸ K)) = _ at hh
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq] at hh
    apply Quotient.sound
    apply DoubleCoset.rel_iff.2
    refine ⟨(h : G)⁻¹, H.inv_mem h.2, ((h * b)⁻¹ * a)⁻¹, K.inv_mem hh, ?_⟩
    group
  · intro o
    induction o using Quotient.inductionOn with | h x => ?_
    induction x using QuotientGroup.induction_on with | H g => ?_
    exact ⟨Quotient.mk _ g, rfl⟩

theorem sum_doubleCoset_eq_sum_orbit : ∀ (G : Type) [Group G] (H K : Subgroup G) (F : G ⧸ K → ℂ), (∀ h : H, ∀ x : G ⧸ K, F (h • x) = F x) →
    ∑ᶠ q : DoubleCoset.Quotient (H : Set G) (K : Set G),
        (1 / (Nat.card (GlobalTheory.LKLoc.locPart H K (Quotient.out q)) : ℂ)) * F (QuotientGroup.mk (Quotient.out q)) =
      ∑ᶠ a : MulAction.orbitRel.Quotient H (G ⧸ K),
        (1 / (Nat.card (MulAction.stabilizer H (Quotient.out a)) : ℂ)) * F (Quotient.out a) := by
  intro G _ H K F hF
  let e := Equiv.ofBijective _ (dcToOrbit_bijective G H K)
  rw [← finsum_comp_equiv e]
  refine finsum_congr fun q => ?_
  have heq : e q = Quotient.mk _ (QuotientGroup.mk (Quotient.out q) : G ⧸ K) := by
    show dcToOrbit G H K q = _
    conv_lhs => rw [← Quotient.out_eq q]
    rfl
  have hrel : MulAction.orbitRel H (G ⧸ K) (Quotient.out (e q)) (QuotientGroup.mk (Quotient.out q)) := by
    apply Quotient.exact
    rw [Quotient.out_eq, heq]
  obtain ⟨h, hh⟩ := hrel
  rw [← hh, hF]
  congr 2
  have h1 := Nat.card_congr (Classical.choice (stabilizer_equiv_locPart G H K (Quotient.out q)))
  rw [← h1]
  exact_mod_cast (Nat.card_congr (MulAction.stabilizerEquivStabilizerOfOrbitRel (G := H) (a := h • (QuotientGroup.mk (Quotient.out q) : G ⧸ K))
    (b := (QuotientGroup.mk (Quotient.out q) : G ⧸ K)) (MulAction.orbitRel_apply.2 ⟨h, rfl⟩)).toEquiv).symm
end GlobalTheory.FinTrace
end

open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orbit_sum_local_parts : ∀ (G : Type) [Group G] (H K : Subgroup G) (F : G ⧸ K → ℂ), (∀ h : H, ∀ x : G ⧸ K, F (h • x) = F x) →
    ∑ᶠ q : DoubleCoset.Quotient (H : Set G) (K : Set G),
        (1 / (Nat.card (GlobalTheory.LKLoc.locPart H K (Quotient.out q)) : ℂ)) * F (QuotientGroup.mk (Quotient.out q)) =
      ∑ᶠ a : MulAction.orbitRel.Quotient H (G ⧸ K),
        (1 / (Nat.card (MulAction.stabilizer H (Quotient.out a)) : ℂ)) * F (Quotient.out a) := by
  first | exact @GlobalTheory.FinTrace.sum_doubleCoset_eq_sum_orbit | exact GlobalTheory.FinTrace.sum_doubleCoset_eq_sum_orbit | (intros; apply GlobalTheory.FinTrace.sum_doubleCoset_eq_sum_orbit <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MassFormulaConjugationAction
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumOverConjPairsEqOrbitSum
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeLieBundleIntersection
open scoped Classical

namespace GlobalTheory.PtFib

open MulAction GlobalTheory.MassConj

def ConjTgt (H : Type) [Group H] (_K : Subgroup H) : Type := H

variable {H X : Type} [Group H] [MulAction H X]

def ConjTgt.val {K : Subgroup H} (γ : ConjTgt H K) : H := γ

instance (K : Subgroup H) : MulAction K (ConjTgt H K) where
  smul k γ := ((k : H) * (show H from γ) * (k : H)⁻¹ : H)
  one_smul := by
    show ∀ γ : H, (1 : H) * γ * (1 : H)⁻¹ = γ
    intro γ; group
  mul_smul k l := by
    show ∀ γ : H, ((k : H) * l) * γ * ((k : H) * l)⁻¹ = (k : H) * ((l : H) * γ * (l : H)⁻¹) * (k : H)⁻¹
    intro γ; group

theorem mk_smul' {T α : Type} [Group T] [MulAction T α] (t : T) (x : α) :
    (Quotient.mk'' (t • x) : orbitRel.Quotient T α) = Quotient.mk'' x :=
  Quotient.sound' (mem_orbit x t)

theorem exists_smul_eq_out' {T α : Type} [Group T] [MulAction T α] (q : orbitRel.Quotient T α) (x : α)
    (h : (Quotient.mk'' x : orbitRel.Quotient T α) = q) : ∃ t : T, t • x = Quotient.out q := by
  have h2 : (Quotient.mk'' (Quotient.out q) : orbitRel.Quotient T α) = Quotient.mk'' x := by
    rw [h]; exact Quotient.out_eq' q
  exact orbitRel_apply.1 (Quotient.eq''.1 h2)

end GlobalTheory.PtFib

namespace GlobalTheory.PtFib

open MulAction GlobalTheory.MassConj

variable {H X : Type} [Group H] [MulAction H X]

theorem card_stab_pair (x : X) (γ : H) :
    Nat.card (stabilizer (stabilizer H x) (show ConjTgt H (stabilizer H x) from γ)) =
      Nat.card (stabilizer H (ConjPair.mk γ x : ConjPair H X)) := by
  apply Nat.card_congr
  refine
   { toFun := fun k => ⟨((k : stabilizer H x) : H), ?_⟩
     invFun := fun d => ⟨⟨(d : H), ?_⟩, ?_⟩
     left_inv := fun k => rfl
     right_inv := fun d => rfl }
  · have hk : ((k : stabilizer H x) : H) * γ * ((k : stabilizer H x) : H)⁻¹ = γ := k.2
    rw [GlobalTheory.MassConj.mem_stabilizer_iff]
    refine ⟨?_, (k : stabilizer H x).2⟩
    calc ((k : stabilizer H x) : H) * γ
        = ((k : stabilizer H x) : H) * γ * ((k : stabilizer H x) : H)⁻¹ * ((k : stabilizer H x) : H) := by group
      _ = γ * ((k : stabilizer H x) : H) := by rw [hk]
  · exact ((GlobalTheory.MassConj.mem_stabilizer_iff _ _).1 d.2).2
  · have hd := ((GlobalTheory.MassConj.mem_stabilizer_iff _ _).1 d.2).1
    rw [MulAction.mem_stabilizer_iff]
    show (d : H) * γ * (d : H)⁻¹ = γ
    rw [hd]; group

theorem card_stab_smul (t : H) (p : ConjPair H X) :
    Nat.card (stabilizer H (t • p)) = Nat.card (stabilizer H p) :=
  (Nat.card_congr (stabilizerEquivStabilizer (rfl : t • p = t • p)).toEquiv).symm

theorem mk_out_pt (p : ConjPair H X) :
    (Quotient.mk'' (Quotient.out (Quotient.mk'' p : orbitRel.Quotient H (ConjPair H X))).pt :
      orbitRel.Quotient H X) = Quotient.mk'' p.pt := by
  obtain ⟨t, ht⟩ := exists_smul_eq_out' (Quotient.mk'' p : orbitRel.Quotient H (ConjPair H X)) p rfl
  rw [← ht, smul_pt, mk_smul']

theorem ptFib_mass (H : Type) [Group H] (X : Type) [MulAction H X] (f : H → X → ℂ)
    (hf : ∀ δ γ : H, ∀ x : X, f (δ * γ * δ⁻¹) (δ • x) = f γ x)
    (hfin : ∀ x : X, Finite (MulAction.stabilizer H x))
    (hsupp : ∀ x : X, (Function.support fun γ : H => f γ x).Finite) (x : X) :
    ∑ᶠ O : {O : MulAction.orbitRel.Quotient H (GlobalTheory.MassConj.ConjPair H X) //
        (Quotient.mk'' (Quotient.out O).pt : MulAction.orbitRel.Quotient H X) = Quotient.mk'' x},
        (1 / (Nat.card (MulAction.stabilizer H (Quotient.out O.1)) : ℂ)) *
          f (Quotient.out O.1).elt (Quotient.out O.1).pt =
      (1 / (Nat.card (MulAction.stabilizer H x) : ℂ)) * ∑ᶠ γ : H, f γ x := by
  haveI := hfin x
  let K := stabilizer H x
  let F : ConjTgt H K → ℂ := fun γ => f γ x
  have hF : ∀ (k : K) (γ : ConjTgt H K), F (k • γ) = F γ := by
    intro k γ
    change H at γ
    show f ((k : H) * γ * (k : H)⁻¹) x = f γ x
    have h := hf k γ x
    rwa [show (k : H) • x = x from k.2] at h
  have key := GlobalTheory.finsum_orbits_stabilizer_mass F hF (hsupp x)
  let g : ConjTgt H K → {O : orbitRel.Quotient H (ConjPair H X) //
      (Quotient.mk'' (Quotient.out O).pt : orbitRel.Quotient H X) = Quotient.mk'' x} :=
    fun γ => ⟨Quotient.mk'' (ConjPair.mk (H := H) γ x), by rw [mk_out_pt]⟩
  have hg : ∀ a b : ConjTgt H K, a ∈ orbit K b → g a = g b := by
    rintro a b ⟨k, hk⟩
    apply Subtype.ext
    show (Quotient.mk'' (ConjPair.mk (H := H) a x) : orbitRel.Quotient H (ConjPair H X)) = Quotient.mk'' (ConjPair.mk (H := H) b x)
    have : (ConjPair.mk (H := H) a x : ConjPair H X) = (k : H) • ConjPair.mk (H := H) b x := by
      ext
      · rw [smul_elt, ← hk]; rfl
      · rw [smul_pt]; exact k.2.symm
    rw [this, mk_smul']
  let φ : orbitRel.Quotient K (ConjTgt H K) → {O : orbitRel.Quotient H (ConjPair H X) //
      (Quotient.mk'' (Quotient.out O).pt : orbitRel.Quotient H X) = Quotient.mk'' x} :=
    Quotient.lift g (fun a b hab => hg a b (orbitRel_apply.1 hab))
  have hφ : ∀ γ : ConjTgt H K, φ (Quotient.mk'' γ) = g γ := fun γ => rfl
  have hinj : Function.Injective φ := by
    intro o1 o2 h
    induction o1 using Quotient.inductionOn' with | h a => ?_
    induction o2 using Quotient.inductionOn' with | h b => ?_
    rw [hφ, hφ] at h
    have h1 : (Quotient.mk'' (ConjPair.mk (H := H) a x) : orbitRel.Quotient H (ConjPair H X)) =
        Quotient.mk'' (ConjPair.mk (H := H) b x) := congrArg Subtype.val h
    obtain ⟨δ, hδ⟩ := orbitRel_apply.1 (Quotient.eq''.1 h1)
    have he : δ * ConjTgt.val b * δ⁻¹ = ConjTgt.val a := congrArg ConjPair.elt hδ
    have hp : δ • x = x := congrArg ConjPair.pt hδ
    apply Quotient.sound'
    exact orbitRel_apply.2 ⟨⟨δ, hp⟩, he⟩
  have hsurj : Function.Surjective φ := by
    rintro ⟨O, hO⟩
    obtain ⟨t, ht⟩ := orbitRel_apply.1 (Quotient.eq''.1 hO)

    refine ⟨Quotient.mk'' (show ConjTgt H K from (t⁻¹ * (Quotient.out O).elt * t : H)), ?_⟩
    rw [hφ]
    apply Subtype.ext
    show (Quotient.mk'' (ConjPair.mk (t⁻¹ * (Quotient.out O).elt * t) x) :
      orbitRel.Quotient H (ConjPair H X)) = O
    have : (ConjPair.mk (t⁻¹ * (Quotient.out O).elt * t) x : ConjPair H X) = t⁻¹ • Quotient.out O := by
      ext
      · rw [smul_elt]; group
      · rw [smul_pt, ← ht, inv_smul_smul]
    rw [this, mk_smul']
    exact Quotient.out_eq' O
  let e := Equiv.ofBijective φ ⟨hinj, hsurj⟩
  rw [← finsum_comp_equiv e]
  have hterm : ∀ o : orbitRel.Quotient K (ConjTgt H K),
      (1 / (Nat.card (stabilizer H (Quotient.out (e o).1)) : ℂ)) *
          f (Quotient.out (e o).1).elt (Quotient.out (e o).1).pt =
        ((Nat.card (stabilizer K (Quotient.out o)) : ℕ) : ℂ)⁻¹ * F (Quotient.out o) := by
    intro o
    have h1 : (e o).1 = Quotient.mk'' (ConjPair.mk (H := H) (Quotient.out o) x) := by
      show (φ o).1 = _
      conv_lhs => rw [← Quotient.out_eq' o]
      rfl
    rw [h1]
    obtain ⟨t, ht⟩ := exists_smul_eq_out'
      (Quotient.mk'' (ConjPair.mk (H := H) (Quotient.out o) x) : orbitRel.Quotient H (ConjPair H X)) _ rfl
    rw [← ht, card_stab_smul, smul_elt, smul_pt, hf, ← card_stab_pair, one_div]
    rfl
  rw [finsum_congr hterm, key, one_div]
  rfl

end GlobalTheory.PtFib
end

open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finsum_over_conj_pairs_eq_orbit_sum : ∀ (H : Type) [Group H] (X : Type) [MulAction H X] (f : H → X → ℂ),
    (∀ δ γ : H, ∀ x : X, f (δ * γ * δ⁻¹) (δ • x) = f γ x) →
    (∀ x : X, Finite (MulAction.stabilizer H x)) →
    (∀ x : X, (Function.support fun γ : H => f γ x).Finite) →
    ∀ x : X, ∑ᶠ O : {O : MulAction.orbitRel.Quotient H (GlobalTheory.MassConj.ConjPair H X) //
        (Quotient.mk'' (Quotient.out O).pt : MulAction.orbitRel.Quotient H X) = Quotient.mk'' x},
        (1 / (Nat.card (MulAction.stabilizer H (Quotient.out O.1)) : ℂ)) *
          f (Quotient.out O.1).elt (Quotient.out O.1).pt =
      (1 / (Nat.card (MulAction.stabilizer H x) : ℂ)) * ∑ᶠ γ : H, f γ x := by
  first | exact @GlobalTheory.PtFib.ptFib_mass | exact GlobalTheory.PtFib.ptFib_mass | (intros; apply GlobalTheory.PtFib.ptFib_mass <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumStabilizerWeightedPairOrbitsConjClass
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumStabilizerWeightedPairOrbitsConjClass
open scoped Classical

namespace GlobalTheory.MassConj

theorem exists_out_mk_eq_smul {H α : Type} [Group H] [MulAction H α] (a : α) :
    ∃ g : H, Quotient.out (Quotient.mk (MulAction.orbitRel H α) a :
      MulAction.orbitRel.Quotient H α) = g • a := by
  have h := Quotient.mk_out (s := MulAction.orbitRel H α) a
  change MulAction.orbitRel H α _ _ at h
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at h
  obtain ⟨g, hg⟩ := h
  exact ⟨g, hg.symm⟩

theorem finsum_pairOrbit_fibre (G : Type) [Group G] (X : Type) [MulAction G X] (Γ : Subgroup G)
    (Φ : Γ → X → ℂ)
    (hΦ : ∀ δ γ : Γ, ∀ x : X, Φ (δ * γ * δ⁻¹) ((δ : G) • x) = Φ γ x) (γ₀ : Γ) :
    ∑ᶠ O : {O : MulAction.orbitRel.Quotient Γ (ConjPair Γ X) //
        ConjClasses.mk (Quotient.out O).elt = ConjClasses.mk γ₀},
        (1 / (Nat.card (MulAction.stabilizer Γ (Quotient.out O.1)) : ℂ)) *
          Φ (Quotient.out O.1).elt (Quotient.out O.1).pt =
      ∑ᶠ b : MulAction.orbitRel.Quotient (Γ ⊓ Subgroup.centralizer {(γ₀ : G)} : Subgroup G) X,
        (1 / (Nat.card (MulAction.stabilizer (Γ ⊓ Subgroup.centralizer {(γ₀ : G)} : Subgroup G)
          (Quotient.out b)) : ℂ)) * Φ γ₀ (Quotient.out b) := by
  set C : Subgroup G := Γ ⊓ Subgroup.centralizer {(γ₀ : G)} with hC
  have memC : ∀ δ : Γ, δ * γ₀ = γ₀ * δ → (δ : G) ∈ C := by
    intro δ h
    rw [hC, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
    refine ⟨δ.2, ?_⟩
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    subst hg
    have := congrArg (fun z : Γ => (z : G)) h
    simpa using this.symm
  have commC : ∀ c : C, (⟨c, c.2.1⟩ : Γ) * γ₀ = γ₀ * ⟨c, c.2.1⟩ := by
    intro c
    have h2 := (Subgroup.mem_inf.mp c.2).2
    rw [Subgroup.mem_centralizer_iff] at h2
    have h := h2 γ₀ (Set.mem_singleton _)
    ext
    simp [h]
  let f : MulAction.orbitRel.Quotient C X →
      {O : MulAction.orbitRel.Quotient Γ (ConjPair Γ X) //
        ConjClasses.mk (Quotient.out O).elt = ConjClasses.mk γ₀} :=
    fun b => ⟨Quotient.mk _ ⟨γ₀, Quotient.out b⟩, by
      obtain ⟨δ, hδ⟩ := exists_out_mk_eq_smul (H := Γ) (ConjPair.mk γ₀ (Quotient.out b))
      rw [hδ, smul_elt, ConjClasses.mk_eq_mk_iff_isConj, isConj_iff]
      exact ⟨δ⁻¹, by group⟩⟩
  have inj : Function.Injective f := by
    intro b b' hbb
    have h1 := congrArg Subtype.val hbb
    simp only [f] at h1
    have h2 := Quotient.exact h1
    change MulAction.orbitRel Γ _ _ _ at h2
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at h2
    obtain ⟨δ, hδ⟩ := h2
    have he := congrArg ConjPair.elt hδ
    have hp := congrArg ConjPair.pt hδ
    simp only [smul_elt, smul_pt] at he hp
    have hcomm : δ * γ₀ = γ₀ * δ := by
      calc δ * γ₀ = δ * γ₀ * δ⁻¹ * δ := by group
        _ = γ₀ * δ := by rw [he]
    rw [← Quotient.out_eq b, ← Quotient.out_eq b']
    apply Quotient.sound
    change MulAction.orbitRel C X _ _
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
    exact ⟨⟨δ, memC δ hcomm⟩, hp⟩
  have surj : Function.Surjective f := by
    rintro ⟨O, hO⟩
    rw [ConjClasses.mk_eq_mk_iff_isConj, isConj_iff] at hO
    obtain ⟨δ, hδ⟩ := hO
    obtain ⟨c, hc⟩ := exists_out_mk_eq_smul (H := C) (δ • (Quotient.out O).pt)
    refine ⟨Quotient.mk _ (δ • (Quotient.out O).pt), ?_⟩
    apply Subtype.ext
    simp only [f]
    conv_rhs => rw [← Quotient.out_eq O]
    apply Quotient.sound
    change MulAction.orbitRel Γ _ _ _
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
    refine ⟨(⟨c, c.2.1⟩ : Γ) * δ, ?_⟩
    rw [hc, mul_smul]
    ext
    · simp only [smul_elt]
      rw [hδ, commC c]
      group
    · simp only [smul_pt]
      rfl
  have term : ∀ b : MulAction.orbitRel.Quotient C X,
      (1 / (Nat.card (MulAction.stabilizer Γ (Quotient.out (f b).1)) : ℂ)) *
          Φ (Quotient.out (f b).1).elt (Quotient.out (f b).1).pt =
        (1 / (Nat.card (MulAction.stabilizer C (Quotient.out b)) : ℂ)) * Φ γ₀ (Quotient.out b) := by
    intro b
    obtain ⟨δ, hδ⟩ := exists_out_mk_eq_smul (H := Γ) (ConjPair.mk γ₀ (Quotient.out b))
    have hfb : (f b).1 = Quotient.mk _ (ConjPair.mk γ₀ (Quotient.out b)) := rfl
    rw [hfb, hδ, smul_elt, smul_pt]
    have hcard1 : Nat.card (MulAction.stabilizer Γ (δ • ConjPair.mk γ₀ (Quotient.out b))) =
        Nat.card (MulAction.stabilizer Γ (ConjPair.mk γ₀ (Quotient.out b))) :=
      Nat.card_congr (MulAction.stabilizerEquivStabilizer rfl).toEquiv.symm
    have h_to : ∀ s : MulAction.stabilizer Γ (ConjPair.mk γ₀ (Quotient.out b) : ConjPair Γ X),
        ((s : Γ) : G) ∈ C := fun s =>
      memC s.1 ((GlobalTheory.MassConj.mem_stabilizer_iff _ _).mp s.2).1
    have h_to' : ∀ s : MulAction.stabilizer Γ (ConjPair.mk γ₀ (Quotient.out b) : ConjPair Γ X),
        (⟨((s : Γ) : G), h_to s⟩ : C) ∈ MulAction.stabilizer C (Quotient.out b) := by
      intro s
      rw [MulAction.mem_stabilizer_iff]
      exact ((GlobalTheory.MassConj.mem_stabilizer_iff _ _).mp s.2).2
    have h_inv : ∀ t : MulAction.stabilizer C (Quotient.out b),
        (⟨((t : C) : G), (t : C).2.1⟩ : Γ) ∈
          MulAction.stabilizer Γ (ConjPair.mk γ₀ (Quotient.out b) : ConjPair Γ X) := by
      intro t
      rw [GlobalTheory.MassConj.mem_stabilizer_iff]
      exact ⟨commC t.1, MulAction.mem_stabilizer_iff.mp t.2⟩
    have hcard2 : Nat.card (MulAction.stabilizer Γ (ConjPair.mk γ₀ (Quotient.out b) : ConjPair Γ X)) =
        Nat.card (MulAction.stabilizer C (Quotient.out b)) :=
      Nat.card_congr
        { toFun := fun s => ⟨⟨((s : Γ) : G), h_to s⟩, h_to' s⟩
          invFun := fun t => ⟨⟨((t : C) : G), (t : C).2.1⟩, h_inv t⟩
          left_inv := fun s => rfl
          right_inv := fun t => rfl }
    have hphi : Φ (δ * γ₀ * δ⁻¹) (δ • Quotient.out b) = Φ γ₀ (Quotient.out b) :=
      hΦ δ γ₀ (Quotient.out b)
    rw [hcard1, hcard2, hphi]
  refine (finsum_comp_equiv (Equiv.ofBijective f ⟨inj, surj⟩)).symm.trans ?_
  exact finsum_congr term

end GlobalTheory.MassConj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumStabilizerWeightedPairOrbitsConjClassStatement
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finsum_stabilizer_weighted_pair_orbits_conjClass : ∀ (G : Type) [Group G] (X : Type) [MulAction G X] (Γ : Subgroup G) (Φ : Γ → X → ℂ),
    (∀ δ γ : Γ, ∀ x : X, Φ (δ * γ * δ⁻¹) ((δ : G) • x) = Φ γ x) →
    ∀ γ₀ : Γ, ∑ᶠ O : {O : MulAction.orbitRel.Quotient Γ (GlobalTheory.MassConj.ConjPair Γ X) //
        ConjClasses.mk (Quotient.out O).elt = ConjClasses.mk γ₀},
        (1 / (Nat.card (MulAction.stabilizer Γ (Quotient.out O.1)) : ℂ)) *
          Φ (Quotient.out O.1).elt (Quotient.out O.1).pt =
      ∑ᶠ b : MulAction.orbitRel.Quotient (Γ ⊓ Subgroup.centralizer {(γ₀ : G)} : Subgroup G) X,
        (1 / (Nat.card (MulAction.stabilizer (Γ ⊓ Subgroup.centralizer {(γ₀ : G)} : Subgroup G)
          (Quotient.out b)) : ℂ)) * Φ γ₀ (Quotient.out b) := by
  first | (exact @GlobalTheory.MassConj.finsum_pairOrbit_fibre) | (exact GlobalTheory.MassConj.finsum_pairOrbit_fibre) | (intros; apply GlobalTheory.MassConj.finsum_pairOrbit_fibre  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MassFormulaConjugationAction
open scoped Classical

namespace GlobalTheory.MassConj

theorem exists_smul_eq_out' {T α : Type} [Group T] [MulAction T α] (p : α) :
    ∃ t : T, t • p = Quotient.out (Quotient.mk'' p : MulAction.orbitRel.Quotient T α) := by
  have h : (Quotient.mk'' (Quotient.out (Quotient.mk'' p : MulAction.orbitRel.Quotient T α)) :
      MulAction.orbitRel.Quotient T α) = Quotient.mk'' p := Quotient.out_eq' _
  exact MulAction.orbitRel_apply.1 (Quotient.eq''.1 h)

theorem finite_support_pairs : ∀ (H : Type) [Group H] (X : Type) [MulAction H X] (f : H → X → ℂ),
    (∀ δ γ : H, ∀ x : X, f (δ * γ * δ⁻¹) (δ • x) = f γ x) →
    Finite (MulAction.orbitRel.Quotient H X) →
    (∀ x : X, (Function.support fun γ : H => f γ x).Finite) →
    {O : MulAction.orbitRel.Quotient H (GlobalTheory.MassConj.ConjPair H X) |
      f (Quotient.out O).elt (Quotient.out O).pt ≠ 0}.Finite := by
  intro H _ X _ f hinv hfo hsupp
  refine (Set.finite_iUnion fun a : MulAction.orbitRel.Quotient H X =>
    (hsupp (Quotient.out a)).image fun γ => (Quotient.mk'' (ConjPair.mk γ (Quotient.out a)) :
      MulAction.orbitRel.Quotient H (ConjPair H X))).subset ?_
  intro O hO
  have hO' : f (Quotient.out O).elt (Quotient.out O).pt ≠ 0 := hO
  obtain ⟨δ, hδ⟩ := exists_smul_eq_out' (T := H) (Quotient.out O).pt
  refine Set.mem_iUnion.2 ⟨Quotient.mk'' (Quotient.out O).pt, δ * (Quotient.out O).elt * δ⁻¹, ?_, ?_⟩
  · show f _ _ ≠ 0
    rw [← hδ, hinv]; exact hO'
  · have e : ConjPair.mk (δ * (Quotient.out O).elt * δ⁻¹)
        (Quotient.out (Quotient.mk'' (Quotient.out O).pt : MulAction.orbitRel.Quotient H X)) =
        δ • Quotient.out O := by
      rw [← hδ]; rfl
    show (Quotient.mk'' (ConjPair.mk _ _) : MulAction.orbitRel.Quotient H (ConjPair H X)) = O
    rw [e]
    exact (Quotient.sound' (MulAction.mem_orbit _ δ)).trans (Quotient.out_eq' O)

theorem finite_support_weighted {H X : Type} [Group H] [MulAction H X] (f : H → X → ℂ)
    (hfin : {O : MulAction.orbitRel.Quotient H (ConjPair H X) |
      f (Quotient.out O).elt (Quotient.out O).pt ≠ 0}.Finite) :
    (Function.support fun O : MulAction.orbitRel.Quotient H (ConjPair H X) =>
      (1 / (Nat.card (MulAction.stabilizer H (Quotient.out O)) : ℂ)) *
        f (Quotient.out O).elt (Quotient.out O).pt).Finite := by
  refine hfin.subset fun O hO => ?_
  exact right_ne_zero_of_mul hO

theorem mass_pt_side : ∀ (H : Type) [Group H] (X : Type) [MulAction H X] (f : H → X → ℂ),
    (∀ δ γ : H, ∀ x : X, f (δ * γ * δ⁻¹) (δ • x) = f γ x) →
    Finite (MulAction.orbitRel.Quotient H X) → (∀ x : X, Finite (MulAction.stabilizer H x)) →
    (∀ x : X, (Function.support fun γ : H => f γ x).Finite) →
    {O : MulAction.orbitRel.Quotient H (GlobalTheory.MassConj.ConjPair H X) |
      f (Quotient.out O).elt (Quotient.out O).pt ≠ 0}.Finite →
    ∑ᶠ a : MulAction.orbitRel.Quotient H X,
        (1 / (Nat.card (MulAction.stabilizer H (Quotient.out a)) : ℂ)) * ∑ᶠ γ : H, f γ (Quotient.out a) =
      ∑ᶠ O : MulAction.orbitRel.Quotient H (GlobalTheory.MassConj.ConjPair H X),
        (1 / (Nat.card (MulAction.stabilizer H (Quotient.out O)) : ℂ)) *
          f (Quotient.out O).elt (Quotient.out O).pt := by
  intro H _ X _ f hinv hfo hstab hsupp hfin
  rw [GlobalTheory.finsum_fiberwise_of_finite_support
    (fun O : MulAction.orbitRel.Quotient H (ConjPair H X) =>
      (Quotient.mk'' (Quotient.out O).pt : MulAction.orbitRel.Quotient H X)) _
    (finite_support_weighted f hfin)]
  refine finsum_congr fun a => ?_
  have h := GlobalTheory.T.finsum_over_conj_pairs_eq_orbit_sum H X f hinv hstab hsupp (Quotient.out a)
  rw [Quotient.out_eq'] at h
  exact h.symm

theorem mass_class_side : ∀ (G : Type) [Group G] (X : Type) [MulAction G X] (Γ : Subgroup G) (Φ : Γ → X → ℂ),
    (∀ δ γ : Γ, ∀ x : X, Φ (δ * γ * δ⁻¹) ((δ : G) • x) = Φ γ x) →
    (∀ x : X, Finite (MulAction.stabilizer Γ x)) →
    {O : MulAction.orbitRel.Quotient Γ (GlobalTheory.MassConj.ConjPair Γ X) |
      Φ (Quotient.out O).elt (Quotient.out O).pt ≠ 0}.Finite →
    ∑ᶠ O : MulAction.orbitRel.Quotient Γ (GlobalTheory.MassConj.ConjPair Γ X),
        (1 / (Nat.card (MulAction.stabilizer Γ (Quotient.out O)) : ℂ)) *
          Φ (Quotient.out O).elt (Quotient.out O).pt =
      ∑ᶠ c : ConjClasses Γ, ∑ᶠ b : MulAction.orbitRel.Quotient
          (Γ ⊓ Subgroup.centralizer {((Quotient.out c : Γ) : G)} : Subgroup G) X,
        (1 / (Nat.card (MulAction.stabilizer (Γ ⊓ Subgroup.centralizer {((Quotient.out c : Γ) : G)} : Subgroup G)
          (Quotient.out b)) : ℂ)) * Φ (Quotient.out c) (Quotient.out b) := by
  intro G _ X _ Γ Φ hinv hstab hfin
  rw [GlobalTheory.finsum_fiberwise_of_finite_support
    (fun O : MulAction.orbitRel.Quotient Γ (ConjPair Γ X) => ConjClasses.mk (Quotient.out O).elt) _
    (finite_support_weighted Φ hfin)]
  refine finsum_congr fun c => ?_
  have h := GlobalTheory.T.finsum_stabilizer_weighted_pair_orbits_conjClass G X Γ Φ hinv (Quotient.out c)
  have e : ConjClasses.mk (Quotient.out c) = c := Quotient.out_eq c
  rw [e] at h
  exact h

theorem mass_formula_conj : ∀ (G : Type) [Group G] (X : Type) [MulAction G X] (Γ : Subgroup G) (Φ : Γ → X → ℂ),
    (∀ δ γ : Γ, ∀ x : X, Φ (δ * γ * δ⁻¹) ((δ : G) • x) = Φ γ x) →
    Finite (MulAction.orbitRel.Quotient Γ X) → (∀ x : X, Finite (MulAction.stabilizer Γ x)) →
    (∀ x : X, (Function.support fun γ : Γ => Φ γ x).Finite) →
    {c : ConjClasses Γ | ∃ x : X, Φ (Quotient.out c) x ≠ 0}.Finite ∧
    ∑ᶠ a : MulAction.orbitRel.Quotient Γ X,
        (1 / (Nat.card (MulAction.stabilizer Γ (Quotient.out a)) : ℂ)) * ∑ᶠ γ : Γ, Φ γ (Quotient.out a) =
      ∑ᶠ c : ConjClasses Γ, ∑ᶠ b : MulAction.orbitRel.Quotient
          (Γ ⊓ Subgroup.centralizer {((Quotient.out c : Γ) : G)} : Subgroup G) X,
        (1 / (Nat.card (MulAction.stabilizer (Γ ⊓ Subgroup.centralizer {((Quotient.out c : Γ) : G)} : Subgroup G)
          (Quotient.out b)) : ℂ)) * Φ (Quotient.out c) (Quotient.out b) := by
  intro G _ X _ Γ Φ hinv hfo hstab hsupp
  have hinv' : ∀ δ γ : Γ, ∀ x : X, Φ (δ * γ * δ⁻¹) (δ • x) = Φ γ x := fun δ γ x => hinv δ γ x
  have hfin := finite_support_pairs Γ X Φ hinv' hfo hsupp
  refine ⟨?_, mass_pt_side Γ X Φ hinv' hfo hstab hsupp hfin |>.trans (mass_class_side G X Γ Φ hinv hstab hfin)⟩
  refine (hfin.image (fun O => ConjClasses.mk (Quotient.out O).elt)).subset ?_
  rintro c ⟨x, hx⟩
  obtain ⟨δ, hδ⟩ := exists_smul_eq_out' (T := Γ) (ConjPair.mk (Quotient.out c) x)
  refine ⟨Quotient.mk'' (ConjPair.mk (Quotient.out c) x), ?_, ?_⟩
  · show Φ _ _ ≠ 0
    rw [← hδ, smul_elt, smul_pt, hinv']
    exact hx
  · show ConjClasses.mk _ = c
    rw [← hδ, smul_elt]
    calc ConjClasses.mk (δ * Quotient.out c * δ⁻¹) = ConjClasses.mk (Quotient.out c) :=
          ConjClasses.mk_eq_mk_iff_isConj.2 (isConj_iff.2 ⟨δ, rfl⟩).symm
      _ = c := Quotient.out_eq c

end GlobalTheory.MassConj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MassFormulaConjugationActionStatement
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.massFormula_conjugation_action : ∀ (G : Type) [Group G] (X : Type) [MulAction G X] (Γ : Subgroup G) (Φ : Γ → X → ℂ),
    (∀ δ γ : Γ, ∀ x : X, Φ (δ * γ * δ⁻¹) ((δ : G) • x) = Φ γ x) →
    Finite (MulAction.orbitRel.Quotient Γ X) → (∀ x : X, Finite (MulAction.stabilizer Γ x)) →
    (∀ x : X, (Function.support fun γ : Γ => Φ γ x).Finite) →
    {c : ConjClasses Γ | ∃ x : X, Φ (Quotient.out c) x ≠ 0}.Finite ∧
    ∑ᶠ a : MulAction.orbitRel.Quotient Γ X,
        (1 / (Nat.card (MulAction.stabilizer Γ (Quotient.out a)) : ℂ)) * ∑ᶠ γ : Γ, Φ γ (Quotient.out a) =
      ∑ᶠ c : ConjClasses Γ, ∑ᶠ b : MulAction.orbitRel.Quotient
          (Γ ⊓ Subgroup.centralizer {((Quotient.out c : Γ) : G)} : Subgroup G) X,
        (1 / (Nat.card (MulAction.stabilizer (Γ ⊓ Subgroup.centralizer {((Quotient.out c : Γ) : G)} : Subgroup G)
          (Quotient.out b)) : ℂ)) * Φ (Quotient.out c) (Quotient.out b) := by
  first | exact @GlobalTheory.MassConj.mass_formula_conj | exact GlobalTheory.MassConj.mass_formula_conj | (intros; apply GlobalTheory.MassConj.mass_formula_conj <;> assumption)
end
end

open scoped Classical

namespace GlobalTheory.FinTrace

theorem unfolded_eq_orbital : ∀ (G : Type) [Group G] (Γ K : Subgroup G) (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
  (ξ : Representation ℂ Γ W),
  Finite (DoubleCoset.Quotient (Γ : Set G) (K : Set G)) → (∀ x : G, Finite (GlobalTheory.LKLoc.locPart Γ K x)) →
  ∀ f : G → ℂ, (∀ k ∈ K, ∀ k' ∈ K, ∀ g, f (k * g * k') = f g) → (Function.support (fun q : G ⧸ K => f q.out)).Finite →
  {c : ConjClasses Γ | ∃ g : G, f (g⁻¹ * (Quotient.out c : Γ) * g) ≠ 0}.Finite ∧
  ∑ᶠ q : DoubleCoset.Quotient (Γ : Set G) (K : Set G),
    (1 / (Nat.card (GlobalTheory.LKLoc.locPart Γ K q.out) : ℂ)) * ∑ᶠ γ : Γ, f (q.out⁻¹ * γ * q.out) * LinearMap.trace ℂ W (ξ γ) =
  ∑ᶠ c : ConjClasses Γ, LinearMap.trace ℂ W (ξ (Quotient.out c)) *
    ∑ᶠ y : DoubleCoset.Quotient ((Γ ⊓ Subgroup.centralizer {((Quotient.out c : Γ) : G)} : Subgroup G) : Set G) (K : Set G),
      (1 / (Nat.card (GlobalTheory.LKLoc.locPart (Γ ⊓ Subgroup.centralizer {((Quotient.out c : Γ) : G)}) K y.out) : ℂ)) *
        f (y.out⁻¹ * (Quotient.out c : Γ) * y.out) := by
  intro G _ Γ K W _ _ _ ξ hfin hloc f hf hsupp
  have hR : ∀ k ∈ K, ∀ g, f (g * k) = f g := fun k hk g => by simpa using hf 1 K.one_mem k hk g
  have hmk : ∀ (g : G) (y : G), f (((QuotientGroup.mk g : G ⧸ K).out)⁻¹ * y * (QuotientGroup.mk g : G ⧸ K).out)
      = f (g⁻¹ * y * g) := by
    intro g y
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K g
    rw [hk, mul_inv_rev, show (k : G)⁻¹ * g⁻¹ * y * (g * k) = (k : G)⁻¹ * (g⁻¹ * y * g) * k by group]
    exact hf _ (K.inv_mem k.2) _ k.2 _
  let Φ : (Γ → ℂ) → Γ → G ⧸ K → ℂ := fun χ γ x => f (x.out⁻¹ * γ * x.out) * χ γ
  have hΦmk : ∀ χ γ (g : G), Φ χ γ (QuotientGroup.mk g) = f (g⁻¹ * γ * g) * χ γ := fun χ γ g => by
    simp only [Φ, hmk]
  have hinv : ∀ (χ : Γ → ℂ), (∀ δ γ : Γ, χ (δ * γ * δ⁻¹) = χ γ) → ∀ δ γ : Γ, ∀ x : G ⧸ K,
      Φ χ (δ * γ * δ⁻¹) ((δ : G) • x) = Φ χ γ x := by
    intro χ hχ δ γ x
    induction x using QuotientGroup.induction_on with
    | H g =>
      rw [MulAction.Quotient.smul_mk, hΦmk, hΦmk, hχ]
      congr 2
      simp only [smul_eq_mul, Subgroup.coe_mul, Subgroup.coe_inv]
      group
  have htr : ∀ δ γ : Γ, LinearMap.trace ℂ W (ξ (δ * γ * δ⁻¹)) = LinearMap.trace ℂ W (ξ γ) := by
    intro δ γ
    rw [map_mul ξ, map_mul ξ, LinearMap.trace_mul_comm ℂ, ← mul_assoc, ← map_mul ξ, inv_mul_cancel, map_one, one_mul]
  have hstab : ∀ (H : Subgroup G) (x : G ⧸ K), H ≤ Γ → Finite (MulAction.stabilizer H x) := by
    intro H x hH
    obtain ⟨e⟩ := GlobalTheory.FinTrace.stabilizer_equiv_locPart G H K x.out
    rw [QuotientGroup.out_eq'] at e
    have hle : GlobalTheory.LKLoc.locPart H K x.out ≤ GlobalTheory.LKLoc.locPart Γ K x.out := inf_le_inf_right _ hH
    haveI : Finite (GlobalTheory.LKLoc.locPart H K x.out) :=
      Finite.of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)
    exact Finite.of_equiv _ e.symm
  have hsuppΦ : ∀ χ (x : G ⧸ K), (Function.support fun γ : Γ => Φ χ γ x).Finite := by
    intro χ x
    induction x using QuotientGroup.induction_on with
    | H g =>
      refine (GlobalTheory.FinTrace.finite_support_conj G Γ K f hR hsupp g (hloc g)).subset fun γ hγ => ?_
      simp only [Function.mem_support, hΦmk] at hγ ⊢
      exact left_ne_zero_of_mul hγ
  have hOrb : Finite (MulAction.orbitRel.Quotient Γ (G ⧸ K)) := by
    refine Finite.of_surjective (fun q : DoubleCoset.Quotient (Γ : Set G) (K : Set G) =>
      (Quotient.mk _ (QuotientGroup.mk (Quotient.out q) : G ⧸ K) : MulAction.orbitRel.Quotient Γ (G ⧸ K))) ?_
    intro a
    induction a using Quotient.inductionOn with
    | h x =>
    induction x using QuotientGroup.induction_on with
    | H g =>
    obtain ⟨h, hh, k, hk, e⟩ := DoubleCoset.mk_out_eq_mul Γ K g
    refine ⟨DoubleCoset.mk Γ K g, Quotient.sound ⟨⟨h, hh⟩, ?_⟩⟩
    show (h : G) • (QuotientGroup.mk g : G ⧸ K) = QuotientGroup.mk (Quotient.out (DoubleCoset.mk Γ K g))
    rw [MulAction.Quotient.smul_mk, e, QuotientGroup.eq]
    simpa [smul_eq_mul, mul_assoc] using hk
  obtain ⟨-, hcE⟩ := GlobalTheory.T.massFormula_conjugation_action G (G ⧸ K) Γ (Φ fun γ => LinearMap.trace ℂ W (ξ γ))
    (hinv (fun γ => LinearMap.trace ℂ W (ξ γ)) htr) hOrb (fun x => hstab Γ x le_rfl) (hsuppΦ _)
  obtain ⟨hcF, -⟩ := GlobalTheory.T.massFormula_conjugation_action G (G ⧸ K) Γ (Φ fun _ => 1)
    (hinv (fun _ => 1) fun _ _ => rfl) hOrb (fun x => hstab Γ x le_rfl) (hsuppΦ _)
  refine ⟨hcF.subset fun c hc => ?_, ?_⟩
  · obtain ⟨g, hg⟩ := hc
    exact ⟨QuotientGroup.mk g, by rw [hΦmk (fun _ => 1) (Quotient.out c) g, mul_one]; exact hg⟩
  let F : G ⧸ K → ℂ := fun x => ∑ᶠ γ : Γ, Φ (fun γ => LinearMap.trace ℂ W (ξ γ)) γ x
  have hFinv : ∀ h : Γ, ∀ x : G ⧸ K, F (h • x) = F x := by
    intro h x
    calc F (h • x) = ∑ᶠ γ : Γ, Φ (fun γ => LinearMap.trace ℂ W (ξ γ)) (MulAut.conj h γ) ((h : G) • x) :=
          (finsum_comp_equiv (MulAut.conj h).toEquiv).symm
      _ = F x := finsum_congr fun γ => hinv (fun γ => LinearMap.trace ℂ W (ξ γ)) htr h γ x
  have hL : ∀ q : DoubleCoset.Quotient (Γ : Set G) (K : Set G),
      ∑ᶠ γ : Γ, f ((Quotient.out q)⁻¹ * γ * Quotient.out q) * LinearMap.trace ℂ W (ξ γ) =
        F (QuotientGroup.mk (Quotient.out q)) := fun q => finsum_congr fun γ => (hΦmk (fun γ => LinearMap.trace ℂ W (ξ γ)) γ (Quotient.out q)).symm
  simp_rw [hL]
  rw [GlobalTheory.T.orbit_sum_local_parts G Γ K F hFinv]
  refine Eq.trans hcE ?_
  refine finsum_congr fun c => ?_
  set Hc : Subgroup G := Γ ⊓ Subgroup.centralizer {((Quotient.out c : Γ) : G)} with hHc
  have hcinv : ∀ h : Hc, ∀ x : G ⧸ K, Φ (fun γ => LinearMap.trace ℂ W (ξ γ)) (Quotient.out c) (h • x) =
      Φ (fun γ => LinearMap.trace ℂ W (ξ γ)) (Quotient.out c) x := by
    intro h x
    let δ : Γ := ⟨h, h.2.1⟩
    have hδ : δ * Quotient.out c * δ⁻¹ = Quotient.out c := by
      have hm := Subgroup.mem_centralizer_iff.mp h.2.2 _ (Set.mem_singleton _)
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, δ]
      rw [← hm]; group
    have := hinv (fun γ => LinearMap.trace ℂ W (ξ γ)) htr δ (Quotient.out c) x
    rw [hδ] at this
    exact this
  rw [mul_finsum]
  refine (GlobalTheory.T.orbit_sum_local_parts G Hc K _ hcinv).symm.trans (finsum_congr fun y => ?_)
  rw [hΦmk (fun γ => LinearMap.trace ℂ W (ξ γ)) (Quotient.out c) (Quotient.out y)]; ring

theorem card_locPart_conj {G : Type} [Group G] (A B K : Subgroup G) (a g : G) {k : G} (hk : k ∈ K)
    (hAB : ∀ y, y ∈ A ↔ a⁻¹ * y * a ∈ B) :
    Nat.card (GlobalTheory.LKLoc.locPart A K (a * g * k)) = Nat.card (GlobalTheory.LKLoc.locPart B K g) := by
  have hEq : GlobalTheory.LKLoc.locPart A K (a * g * k) = (GlobalTheory.LKLoc.locPart B K g).map (MulAut.conj a).toMonoidHom := by
    ext y
    simp only [GlobalTheory.LKLoc.locPart, Subgroup.mem_inf, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    constructor
    · rintro ⟨hyA, k', hk', e⟩
      refine ⟨a⁻¹ * y * a, ⟨(hAB y).1 hyA, k * k' * k⁻¹, K.mul_mem (K.mul_mem hk hk') (K.inv_mem hk), ?_⟩, by group⟩
      rw [← e]; group
    · rintro ⟨z, ⟨hzB, k', hk', e⟩, rfl⟩
      refine ⟨(hAB _).2 (by convert hzB using 1; group), k⁻¹ * k' * k, K.mul_mem (K.mul_mem (K.inv_mem hk) hk') hk, ?_⟩
      rw [← e]; group
  rw [hEq]
  exact Nat.card_congr (Subgroup.equivMapOfInjective _ _ (fun x y h => (MulAut.conj a).injective h)).toEquiv.symm

theorem finsum_doubleCoset_conj {G : Type} [Group G] (A B K : Subgroup G) (f : G → ℂ)
    (hf : ∀ k ∈ K, ∀ k' ∈ K, ∀ g, f (k * g * k') = f g) (a ρA ρB : G)
    (hAB : ∀ y, y ∈ A ↔ a⁻¹ * y * a ∈ B) (hA : ∀ y ∈ A, y * ρA = ρA * y) (hρ : a⁻¹ * ρA * a = ρB) :
    ∑ᶠ q : DoubleCoset.Quotient (A : Set G) (K : Set G),
        (1 / (Nat.card (GlobalTheory.LKLoc.locPart A K (Quotient.out q)) : ℂ)) * f ((Quotient.out q)⁻¹ * ρA * Quotient.out q) =
      ∑ᶠ q : DoubleCoset.Quotient (B : Set G) (K : Set G),
        (1 / (Nat.card (GlobalTheory.LKLoc.locPart B K (Quotient.out q)) : ℂ)) * f ((Quotient.out q)⁻¹ * ρB * Quotient.out q) := by
  let F : DoubleCoset.Quotient (B : Set G) (K : Set G) → DoubleCoset.Quotient (A : Set G) (K : Set G) :=
    fun q => DoubleCoset.mk A K (a * Quotient.out q)
  have hB : ∀ y, y ∈ B → a * y * a⁻¹ ∈ A := fun y hy => (hAB _).2 (by convert hy using 1; group)
  have hbij : Function.Bijective F := by
    constructor
    · intro q1 q2 h
      rw [DoubleCoset.eq] at h
      obtain ⟨h', hh', k, hk, e⟩ := h
      rw [← DoubleCoset.out_eq' q1, ← DoubleCoset.out_eq' q2, DoubleCoset.eq]
      refine ⟨a⁻¹ * h' * a, (hAB h').1 hh', k, hk, ?_⟩
      calc Quotient.out q2 = a⁻¹ * (a * Quotient.out q2) := by group
        _ = _ := by rw [e]; group
    · intro p
      refine ⟨DoubleCoset.mk B K (a⁻¹ * Quotient.out p), ?_⟩
      obtain ⟨b, hb, k, hk, e⟩ := DoubleCoset.mk_out_eq_mul B K (a⁻¹ * Quotient.out p)
      show DoubleCoset.mk A K (a * Quotient.out (DoubleCoset.mk B K (a⁻¹ * Quotient.out p))) = p
      conv_rhs => rw [← DoubleCoset.out_eq' p]
      rw [e, DoubleCoset.eq]
      refine ⟨(a * b * a⁻¹)⁻¹, A.inv_mem (hB b hb), k⁻¹, K.inv_mem hk, by group⟩
  rw [← finsum_comp_equiv (Equiv.ofBijective F hbij)]
  refine finsum_congr fun q => ?_
  simp only [Equiv.ofBijective_apply, F]
  obtain ⟨h, hh, k, hk, e⟩ := DoubleCoset.mk_out_eq_mul A K (a * Quotient.out q)
  rw [e, show h * (a * Quotient.out q) * k = (h * a) * Quotient.out q * k by group]
  have hAB' : ∀ y, y ∈ A ↔ (h * a)⁻¹ * y * (h * a) ∈ B := by
    intro y
    rw [show (h * a)⁻¹ * y * (h * a) = a⁻¹ * (h⁻¹ * y * h) * a by group, ← hAB]
    constructor
    · intro hy; exact A.mul_mem (A.mul_mem (A.inv_mem hh) hy) hh
    · intro hy
      have := A.mul_mem (A.mul_mem hh hy) (A.inv_mem hh)
      convert this using 1; group
  rw [card_locPart_conj A B K (h * a) (Quotient.out q) hk hAB']
  have hc : (h * a)⁻¹ * ρA * (h * a) = ρB := by
    rw [show (h * a)⁻¹ * ρA * (h * a) = a⁻¹ * (h⁻¹ * (h * ρA)) * a by rw [hA h hh]; group]
    rw [show a⁻¹ * (h⁻¹ * (h * ρA)) * a = a⁻¹ * ρA * a by group, hρ]
  rw [show ((h * a) * Quotient.out q * k)⁻¹ * ρA * ((h * a) * Quotient.out q * k) =
      k⁻¹ * ((Quotient.out q)⁻¹ * ((h * a)⁻¹ * ρA * (h * a)) * Quotient.out q) * k by group, hc,
    hf _ (K.inv_mem hk) _ hk]

theorem orbital_conj : ∀ (G : Type) [Group G] (Γ K : Subgroup G) (f : G → ℂ), (∀ k ∈ K, ∀ k' ∈ K, ∀ g, f (k * g * k') = f g) →
    ∀ ρ δ : Γ,
    ∑ᶠ q : DoubleCoset.Quotient ((Subgroup.centralizer {((δ * ρ * δ⁻¹ : Γ) : G)} ⊓ Γ : Subgroup G) : Set G) (K : Set G),
        (1 / (Nat.card (GlobalTheory.LKLoc.locPart (Subgroup.centralizer {((δ * ρ * δ⁻¹ : Γ) : G)} ⊓ Γ) K (Quotient.out q)) : ℂ)) *
          f ((Quotient.out q)⁻¹ * ((δ * ρ * δ⁻¹ : Γ) : G) * Quotient.out q) =
      ∑ᶠ q : DoubleCoset.Quotient ((Subgroup.centralizer {(ρ : G)} ⊓ Γ : Subgroup G) : Set G) (K : Set G),
        (1 / (Nat.card (GlobalTheory.LKLoc.locPart (Subgroup.centralizer {(ρ : G)} ⊓ Γ) K (Quotient.out q)) : ℂ)) *
          f ((Quotient.out q)⁻¹ * (ρ : G) * Quotient.out q) := by
  intro G _ Γ K f hf ρ δ
  refine finsum_doubleCoset_conj _ _ K f hf (δ : G) _ _ ?_ ?_ ?_
  · intro y
    simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff, Subgroup.coe_mul, Subgroup.coe_inv]
    constructor
    · rintro ⟨hc, hy⟩
      refine ⟨?_, Γ.mul_mem (Γ.mul_mem (Γ.inv_mem δ.2) hy) δ.2⟩
      calc (δ : G)⁻¹ * y * δ * ρ = (δ : G)⁻¹ * (y * (δ * ρ * (δ : G)⁻¹)) * δ := by group
        _ = (δ : G)⁻¹ * ((δ * ρ * (δ : G)⁻¹) * y) * δ := by rw [hc]
        _ = ρ * ((δ : G)⁻¹ * y * δ) := by group
    · rintro ⟨hc, hy⟩
      refine ⟨?_, ?_⟩
      · calc y * (δ * ρ * (δ : G)⁻¹) = δ * (((δ : G)⁻¹ * y * δ) * ρ) * (δ : G)⁻¹ := by group
          _ = δ * (ρ * ((δ : G)⁻¹ * y * δ)) * (δ : G)⁻¹ := by rw [hc]
          _ = (δ * ρ * (δ : G)⁻¹) * y := by group
      · have := Γ.mul_mem (Γ.mul_mem δ.2 hy) (Γ.inv_mem δ.2)
        convert this using 1; group
  · intro y hy
    exact (Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hy).1)
  · simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group

theorem unfolded_eq_orbital_reps : ∀ (G : Type) [Group G] (Γ K : Subgroup G) (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
  (ξ : Representation ℂ Γ W),
  Finite (DoubleCoset.Quotient (Γ : Set G) (K : Set G)) → (∀ x : G, Finite (GlobalTheory.LKLoc.locPart Γ K x)) →
  ∀ f : G → ℂ, (∀ k ∈ K, ∀ k' ∈ K, ∀ g, f (k * g * k') = f g) → (Function.support (fun q : G ⧸ K => f q.out)).Finite →
  ∀ R : Set Γ, (∀ γ : Γ, ∃! ρ, ρ ∈ R ∧ IsConj γ ρ) →
  ∑ᶠ q : DoubleCoset.Quotient (Γ : Set G) (K : Set G),
    (1 / (Nat.card (GlobalTheory.LKLoc.locPart Γ K q.out) : ℂ)) * ∑ᶠ γ : Γ, f (q.out⁻¹ * γ * q.out) * LinearMap.trace ℂ W (ξ γ)
  = ∑ᶠ ρ ∈ R, LinearMap.trace ℂ W (ξ ρ) *
      ∑ᶠ q : DoubleCoset.Quotient ((Subgroup.centralizer {(ρ : G)} ⊓ Γ : Subgroup G) : Set G) (K : Set G),
        (1 / (Nat.card (GlobalTheory.LKLoc.locPart (Subgroup.centralizer {(ρ : G)} ⊓ Γ) K q.out) : ℂ)) * f (q.out⁻¹ * ρ * q.out) := by
  intro G _ Γ K W _ _ _ ξ hfin hloc f hf hsupp R hR
  rw [(unfolded_eq_orbital G Γ K W ξ hfin hloc f hf hsupp).2]
  let T : Γ → ℂ := fun ρ => LinearMap.trace ℂ W (ξ ρ) *
      ∑ᶠ q : DoubleCoset.Quotient ((Subgroup.centralizer {(ρ : G)} ⊓ Γ : Subgroup G) : Set G) (K : Set G),
        (1 / (Nat.card (GlobalTheory.LKLoc.locPart (Subgroup.centralizer {(ρ : G)} ⊓ Γ) K (Quotient.out q)) : ℂ)) *
          f ((Quotient.out q)⁻¹ * (ρ : G) * Quotient.out q)
  have htr : ∀ δ γ : Γ, LinearMap.trace ℂ W (ξ (δ * γ * δ⁻¹)) = LinearMap.trace ℂ W (ξ γ) := by
    intro δ γ
    rw [map_mul ξ, map_mul ξ, LinearMap.trace_mul_comm ℂ, ← mul_assoc, ← map_mul ξ, inv_mul_cancel, map_one, one_mul]
  have hT : ∀ a b : Γ, IsConj a b → T a = T b := by
    intro a b hab
    obtain ⟨δ, hδ⟩ := isConj_iff.1 hab
    subst hδ
    simp only [T]
    rw [htr, orbital_conj G Γ K f hf a δ]
  have hL : ∀ c : ConjClasses Γ, LinearMap.trace ℂ W (ξ (Quotient.out c)) *
      ∑ᶠ y : DoubleCoset.Quotient ((Γ ⊓ Subgroup.centralizer {((Quotient.out c : Γ) : G)} : Subgroup G) : Set G) (K : Set G),
        (1 / (Nat.card (GlobalTheory.LKLoc.locPart (Γ ⊓ Subgroup.centralizer {((Quotient.out c : Γ) : G)}) K y.out) : ℂ)) *
          f (y.out⁻¹ * (Quotient.out c : Γ) * y.out) = T (Quotient.out c) := by
    intro c
    rw [show (Γ ⊓ Subgroup.centralizer {((Quotient.out c : Γ) : G)}) =
      Subgroup.centralizer {((Quotient.out c : Γ) : G)} ⊓ Γ from inf_comm _ _]
  simp_rw [hL]
  let e : R → ConjClasses Γ := fun ρ => ConjClasses.mk ρ.1
  have he : Function.Bijective e := by
    refine ⟨fun a b hab => ?_, fun c => ?_⟩
    · have h1 : IsConj a.1 b.1 := ConjClasses.mk_eq_mk_iff_isConj.1 hab
      obtain ⟨ρ, -, hu⟩ := hR a.1
      exact Subtype.ext ((hu a.1 ⟨a.2, IsConj.refl _⟩).trans (hu b.1 ⟨b.2, h1⟩).symm)
    · obtain ⟨γ, rfl⟩ := ConjClasses.mk_surjective c
      obtain ⟨ρ, ⟨hρ, hc⟩, -⟩ := hR γ
      exact ⟨⟨ρ, hρ⟩, ConjClasses.mk_eq_mk_iff_isConj.2 hc.symm⟩
  rw [← finsum_set_coe_eq_finsum_mem, ← finsum_comp_equiv (Equiv.ofBijective e he)]
  refine finsum_congr fun ρ => ?_
  apply hT
  show IsConj (Quotient.out (ConjClasses.mk ρ.1)) ρ.1
  rw [← ConjClasses.mk_eq_mk_iff_isConj]
  exact Quotient.out_eq _

end GlobalTheory.FinTrace
