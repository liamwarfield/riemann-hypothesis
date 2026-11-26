module

public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.ConvGrOf
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HenselPolynomialRefinement
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeLogBound

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicLawOfBlockDet
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicLawOfBlockDet
noncomputable section

open PositivityTheory.RgEis

namespace GlobalTheory.CompanionTheory.RgEisPar

variable {E R : Type} [Field E] [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R]
  [LocallyCompactSpace R] [SecondCountableTopology R]

theorem continuous_circle_coe : Continuous (fun z : Circle => (z : ℂ)) := by
  first | fun_prop | exact continuous_subtype_val | exact continuous_induced_dom

theorem stab_univ_eq_top {κ : Type} [Fintype κ] [DecidableEq κ] : stab R (Set.univ : Set κ) = ⊤ := by
  refine eq_top_iff.2 fun g _ r hr => ?_
  exact absurd (Set.mem_univ r) hr

theorem isCh_of_top {G : Type} [Group G] [TopologicalSpace G] {Γ P : Subgroup G} {c : G → ℂ} (h : IsCh Γ ⊤ c) : IsCh Γ P c := by
  exact ⟨fun p _ q _ => h.mul p (Subgroup.mem_top p) q (Subgroup.mem_top q),
    fun p _ => h.norm p (Subgroup.mem_top p),
    fun γ hγ _ => h.rat γ hγ (Subgroup.mem_top γ),
    h.cont.mono fun x _ => Subgroup.mem_top x⟩

theorem isCh_cGL (hB : BdetLaw) (A : Ad E R) (hA : A.GoodL) (κ : Type) [Fintype κ] [DecidableEq κ] :
    IsCh (A.ratGL κ) ⊤ (A.cGL κ) := by
  obtain ⟨-, hm, hcont, hr, -, hd⟩ := hB E R A hA κ Set.univ
  have htop : ∀ g : GL κ R, g ∈ stab R (Set.univ : Set κ) := fun g => by
    rw [stab_univ_eq_top]; trivial
  have hc : ∀ g : GL κ R, A.cGL κ g = A.χ (bdet Set.univ g) := fun g => by
    rw [hd]; rfl
  refine ⟨fun p _ q _ => ?_, fun p _ => ?_, fun γ hγ _ => ?_, ?_⟩
  · rw [hc, hc, hc, hm p (htop p) q (htop q), map_mul, Circle.coe_mul]
  · rw [hc]; exact Circle.norm_coe _
  · obtain ⟨x, hx⟩ := hr γ (htop γ) hγ
    rw [hc, hx, hA.χi, Circle.coe_one]
  · have hcon : Continuous (bdet (R := R) (Set.univ : Set κ)) := by
      rw [← continuousOn_univ]
      refine hcont.mono fun g _ => htop g
    have : A.cGL κ = fun g => ((A.χ (bdet Set.univ g) : Circle) : ℂ) := funext hc
    rw [this]
    exact (continuous_circle_coe.comp (hA.χcont.comp hcon)).continuousOn

theorem ext_gl (hB : BdetLaw) (hE : ExtLaw) (hT : GrpTop) (A : Ad E R) (hA : A.Good) (κ : Type) [Fintype κ] [DecidableEq κ]
    (t : Set κ) : IsHt (A.ratGL κ) (A.kGL κ) (stab R t) (A.htGL t) ∧
      ∀ p ∈ stab R t, ∀ k ∈ A.kGL κ, A.htGL t (p * k) = A.lg (bdet t p) := by
  obtain ⟨hc, hm, hcont, hr, hk, -⟩ := hB E R A hA.toGoodL κ t
  haveI : T2Space (GL κ R) := (hT E R A hA κ 1).1
  refine hE (GL κ R) (A.ratGL κ) (A.kGL κ) (stab R t) (fun p => A.lg (bdet t p)) (hA.kcpt κ) hc (hA.iwa κ t) ?_ ?_ hk ?_
  · intro p hp q hq
    simp only [hm p hp q hq, hA.lgmul]
  · exact hA.lgcont.comp_continuousOn hcont
  · intro p hp hg
    obtain ⟨x, hx⟩ := hr p hp hg
    simp only [hx, hA.lgi x]

theorem closed_uQ (hB : BdetLaw) (A : Ad E R) (hA : A.GoodL) (ε : ℤˣ) {κ : Type} [Fintype κ] [DecidableEq κ] (t : Set κ) :
    IsClosed (A.uQ ε t : Set (A.U ε κ)) :=
  (hB E R A hA (κ ⊕ κ) (Sum.inl '' t)).1.preimage continuous_subtype_val

theorem ext_u (hB : BdetLaw) (hE : ExtLaw) (hT : GrpTop) (A : Ad E R) (hA : A.Good) (ε : ℤˣ) {κ : Type} [Fintype κ]
    [DecidableEq κ] (t : Set κ) (hI : Iwa (A.uQ ε t) (A.uK ε κ)) :
    IsHt (A.uΓ ε κ) (A.uK ε κ) (A.uQ ε t) (A.uH ε t) ∧
      ∀ p ∈ A.uQ ε t, ∀ k ∈ A.uK ε κ, A.uH ε t (p * k) = A.lg (bdet (Sum.inl '' t) p.1) := by
  obtain ⟨-, hm, hcont, hr, hk, -⟩ := hB E R A hA.toGoodL (κ ⊕ κ) (Sum.inl '' t)
  obtain ⟨-, -, -, h2, -, -, hK⟩ := hT E R A hA κ ε
  haveI := h2
  refine hE (A.U ε κ) (A.uΓ ε κ) (A.uK ε κ) (A.uQ ε t) (fun p => A.lg (bdet (Sum.inl '' t) p.1)) hK
    (closed_uQ hB A hA.toGoodL ε t) hI ?_ ?_ ?_ ?_
  · intro p hp q hq
    simp only [Subgroup.coe_mul, hm p.1 hp q.1 hq, hA.lgmul]
  · exact hA.lgcont.comp_continuousOn (hcont.comp continuous_subtype_val.continuousOn fun x hx => hx)
  · exact fun p hp hpk => hk p.1 hp hpk
  · intro p hp hg
    obtain ⟨x, hx⟩ := hr p.1 hp hg
    simp only [hx, hA.lgi x]

theorem isCh_uC (hB : BdetLaw) (A : Ad E R) (hA : A.GoodL) (ε : ℤˣ) {κ : Type} [Fintype κ] [DecidableEq κ] :
    IsCh (A.uΓ ε κ) (A.uQ ε (Set.univ : Set κ)) (A.uC ε κ) := by
  obtain ⟨-, hm, hcont, hr, -, -⟩ := hB E R A hA (κ ⊕ κ) (Sum.inl '' (Set.univ : Set κ))
  refine ⟨fun p hp q hq => ?_, fun p _ => Circle.norm_coe _, fun γ hγ hp => ?_, ?_⟩
  · simp only [Ad.uC, Subgroup.coe_mul, hm p.1 hp q.1 hq, map_mul, Circle.coe_mul]
  · obtain ⟨x, hx⟩ := hr γ.1 hp hγ
    simp only [Ad.uC, hx, hA.χi, Circle.coe_one]
  · exact continuous_circle_coe.comp_continuousOn
      (hA.χcont.comp_continuousOn (hcont.comp continuous_subtype_val.continuousOn fun x hx => hx))

theorem parLaw : BdetLaw → ExtLaw → GrpTop → ParLaw := by
  intro hB hE hT E R _ _ _ _ _ _ _ A hA ι _ _ ε s
  obtain ⟨hc, -⟩ := hB E R A hA.toGoodL ι s
  have hch := isCh_cGL hB A hA.toGoodL ι
  refine ⟨⟨⟨hc, hA.iwa ι s, ?_⟩, ⟨hc, hA.iwa ι s, isCh_of_top hch⟩, hch, (ext_gl hB hE hT A hA ι s).1, stab_univ_eq_top⟩, ?_⟩
  · refine ⟨fun _ _ _ _ => by simp, fun _ _ => by simp, fun _ _ _ => rfl, continuousOn_const⟩
  intro hI
  have hI' : Iwa (A.uQ ε s) (A.uK ε ι) := fun g => by
    obtain ⟨p, hp, k, hk, e⟩ := hI g
    exact ⟨p, hp.1, k, hk, e⟩
  have hu := ext_u hB hE hT A hA ε s hI'
  have hC := isCh_uC hB A hA.toGoodL (ε := ε) (κ := ι)
  refine ⟨⟨(closed_uQ hB A hA.toGoodL ε s).inter (closed_uQ hB A hA.toGoodL ε Set.univ), hI, ?_⟩, hu.1, fun g => ?_⟩
  · exact ⟨fun p hp q hq => hC.mul p hp.2 q hq.2, fun p hp => hC.norm p hp.2, fun γ hγ hp => hC.rat γ hγ hp.2,
      hC.cont.mono fun _ h => h.2⟩
  · obtain ⟨p, hp, k, hk, rfl⟩ := hI' g
    rw [hu.2 p hp k hk]
    exact ((ext_gl hB hE hT A hA (ι ⊕ ι) (Sum.inl '' s)).2 p.1 hp k.1 hk).symm

end GlobalTheory.CompanionTheory.RgEisPar
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicLawOfBlockDetStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parabolic_law_of_block_det : PositivityTheory.RgEis.BdetLaw → PositivityTheory.RgEis.ExtLaw → PositivityTheory.RgEis.GrpTop → PositivityTheory.RgEis.ParLaw := by
  first | exact @GlobalTheory.CompanionTheory.RgEisPar.parLaw | exact GlobalTheory.CompanionTheory.RgEisPar.parLaw | (intros; apply GlobalTheory.CompanionTheory.RgEisPar.parLaw <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentConvergenceOfParabolic
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentConvergenceOfParabolic
noncomputable section

namespace GlobalTheory.CompanionTheory.RgEis.UnitaryConv

open PositivityTheory.RgEis

variable {G : Type} [Group G]

theorem cos_mk_eq_iff {P Γ : Subgroup G} (a b : Γ) :
    (Quotient.mk (QuotientGroup.rightRel (P.subgroupOf Γ)) a : Cos P Γ) = Quotient.mk _ b ↔
      (b : G) * (a : G)⁻¹ ∈ P := by
  constructor
  · intro h
    have h1 : b * a⁻¹ ∈ P.subgroupOf Γ := QuotientGroup.rightRel_apply.mp (Quotient.exact h)
    simpa using Subgroup.mem_subgroupOf.mp h1
  · intro h
    apply Quotient.sound
    apply QuotientGroup.rightRel_apply.mpr
    apply Subgroup.mem_subgroupOf.mpr
    simpa using h

theorem cos_eq_of_rep {P Γ : Subgroup G} {q q' : Cos P Γ} (h : rep q' * (rep q)⁻¹ ∈ P) : q = q' := by
  have h' := (cos_mk_eq_iff (P := P) (Γ := Γ) (Quotient.out q) (Quotient.out q')).mpr h
  rw [Quotient.out_eq, Quotient.out_eq] at h'
  exact h'

theorem rep_mk {P Γ : Subgroup G} (a : Γ) :
    ∃ p ∈ Γ, p ∈ P ∧ rep (Quotient.mk (QuotientGroup.rightRel (P.subgroupOf Γ)) a : Cos P Γ) = p * a := by
  refine ⟨rep (Quotient.mk _ a : Cos P Γ) * (a : G)⁻¹, ?_, ?_, ?_⟩
  · exact Γ.mul_mem (Quotient.out (Quotient.mk _ a : Cos P Γ)).2 (Γ.inv_mem a.2)
  · exact (cos_mk_eq_iff (P := P) (Γ := Γ) a (Quotient.out (Quotient.mk _ a : Cos P Γ))).mp
      (Quotient.out_eq _).symm
  · exact (inv_mul_cancel_right _ _).symm

theorem conv_comap {G' : Type} [Group G'] (φ : G' →* G) {Γ P : Subgroup G} {Γ' P' : Subgroup G'} {l : G → ℝ}
    (hΓ : ∀ γ ∈ Γ', φ γ ∈ Γ) (hP : ∀ γ ∈ Γ', φ γ ∈ P → γ ∈ P')
    (hl : ∀ γ ∈ Γ, γ ∈ P → ∀ g, l (γ * g) = l g) (hc : Conv Γ P l) :
    Conv Γ' P' fun g => l (φ g) := by
  intro g'
  have hinj : Function.Injective (fun q' : Cos P' Γ' =>
      (Quotient.mk _ ⟨φ (rep q'), hΓ (rep q') (Quotient.out q').2⟩ : Cos P Γ)) := by
    intro q₁ q₂ h
    have h' := (cos_mk_eq_iff (P := P) (Γ := Γ) _ _).mp h
    apply cos_eq_of_rep
    have hmem : rep q₂ * (rep q₁)⁻¹ ∈ Γ' :=
      Γ'.mul_mem (Quotient.out q₂).2 (Γ'.inv_mem (Quotient.out q₁).2)
    refine hP _ hmem ?_
    rw [map_mul, map_inv]
    exact h'
  refine ((hc (φ g')).comp_injective hinj).congr fun q' => ?_
  obtain ⟨p, hpΓ, hpP, hp⟩ := rep_mk (P := P) (Γ := Γ) ⟨φ (rep q'), hΓ (rep q') (Quotient.out q').2⟩
  show Real.exp (l (rep (Quotient.mk _ ⟨φ (rep q'), hΓ (rep q') (Quotient.out q').2⟩ : Cos P Γ) * φ g')) =
    Real.exp (l (φ (rep q' * g')))
  rw [hp, map_mul, mul_assoc, hl p hpΓ hpP]

theorem conv_inf {Γ P₁ P₂ : Subgroup G} {l₁ l₂ : G → ℝ}
    (h₁ : ∀ γ ∈ Γ, γ ∈ P₁ → ∀ g, l₁ (γ * g) = l₁ g) (h₂ : ∀ γ ∈ Γ, γ ∈ P₂ → ∀ g, l₂ (γ * g) = l₂ g)
    (c₁ : Conv Γ P₁ l₁) (c₂ : Conv Γ P₂ l₂) : Conv Γ (P₁ ⊓ P₂) fun g => l₁ g + l₂ g := by
  intro g
  have hinj : Function.Injective (fun q : Cos (P₁ ⊓ P₂) Γ =>
      ((Quotient.mk _ (Quotient.out q) : Cos P₁ Γ), (Quotient.mk _ (Quotient.out q) : Cos P₂ Γ))) := by
    intro q q' h
    have e1 := (cos_mk_eq_iff (P := P₁) (Γ := Γ) _ _).mp (congrArg Prod.fst h)
    have e2 := (cos_mk_eq_iff (P := P₂) (Γ := Γ) _ _).mp (congrArg Prod.snd h)
    exact cos_eq_of_rep (Subgroup.mem_inf.mpr ⟨e1, e2⟩)
  have hprod : Summable fun x : Cos P₁ Γ × Cos P₂ Γ =>
      Real.exp (l₁ (rep x.1 * g)) * Real.exp (l₂ (rep x.2 * g)) := by
    exact Summable.mul_of_nonneg (c₁ g) (c₂ g) (fun _ => (Real.exp_pos _).le)
      (fun _ => (Real.exp_pos _).le)
  refine (hprod.comp_injective hinj).congr fun q => ?_
  obtain ⟨p₁, hp₁Γ, hp₁P, hp₁⟩ := rep_mk (P := P₁) (Γ := Γ) (Quotient.out q)
  obtain ⟨p₂, hp₂Γ, hp₂P, hp₂⟩ := rep_mk (P := P₂) (Γ := Γ) (Quotient.out q)
  show Real.exp (l₁ (rep (Quotient.mk _ (Quotient.out q) : Cos P₁ Γ) * g)) *
      Real.exp (l₂ (rep (Quotient.mk _ (Quotient.out q) : Cos P₂ Γ) * g)) =
    Real.exp (l₁ (rep q * g) + l₂ (rep q * g))
  rw [hp₁, hp₂, mul_assoc, mul_assoc, h₁ p₁ hp₁Γ hp₁P, h₂ p₂ hp₂Γ hp₂P, Real.exp_add]
  rfl

theorem convU_of_parLaw : ParLaw → ConvU := by
  intro hPar E R _ _ _ _ _ _ _ A hA hGr ι _ _ ε s hIwa
  have inv : ∀ {H : Type} [Group H] [TopologicalSpace H] {Γ K P : Subgroup H} {η : H → ℝ} (c : ℝ),
      IsHt Γ K P η → ∀ γ ∈ Γ, γ ∈ P → ∀ g, c * η (γ * g) = c * η g := by
    intro H _ _ Γ K P η c h γ hγ hγP g
    rw [h.left γ hγP g, h.rat γ hγ hγP, zero_add]
  have hconv : ∀ (t : Set ι) (x : ℝ), (∀ g : A.U ε ι, A.uH ε t g = A.htGL (Sum.inl '' t) g.1) →
      IsHt (A.ratGL (ι ⊕ ι)) (A.kGL (ι ⊕ ι)) (stab R (Sum.inl '' t)) (A.htGL (Sum.inl '' t)) →
      Conv (A.ratGL (ι ⊕ ι)) (stab R (Sum.inl '' t)) (fun g => x * A.htGL (Sum.inl '' t) g) →
      Conv (A.uΓ ε ι) (A.uQ ε t) fun g => x * A.uH ε t g := by
    intro t x heq hHt hc
    have h := conv_comap (A.uSub ε ι).subtype (Γ := A.ratGL (ι ⊕ ι)) (P := stab R (Sum.inl '' t))
      (Γ' := A.uΓ ε ι) (P' := A.uQ ε t) (l := fun g => x * A.htGL (Sum.inl '' t) g)
      (fun γ hγ => Subgroup.mem_subgroupOf.mp hγ) (fun γ _ hγ => Subgroup.mem_subgroupOf.mpr hγ)
      (inv x hHt) hc
    have hfun : (fun g : A.U ε ι => x * A.uH ε t g) =
        fun g => x * A.htGL (Sum.inl '' t) ((A.uSub ε ι).subtype g) := by
      funext g
      exact congrArg (fun r => x * r) (heq g)
    rw [hfun]
    exact h
  have hIwaU : Iwa (A.uQ ε (Set.univ : Set ι) ⊓ A.uQ ε Set.univ) (A.uK ε ι) := by
    intro g
    obtain ⟨p, hp, k, hk, hg⟩ := hIwa g
    exact ⟨p, Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hp).2, (Subgroup.mem_inf.mp hp).2⟩, k, hk, hg⟩
  obtain ⟨Rs, hRs⟩ := hGr (ι ⊕ ι) (Sum.inl '' s)
  obtain ⟨Ru, hRu⟩ := hGr (ι ⊕ ι) (Sum.inl '' (Set.univ : Set ι))
  have hs := (hPar E R A hA ι ε s).2 hIwa
  have hu := (hPar E R A hA ι ε Set.univ).2 hIwaU
  have hGs := (hPar E R A hA (ι ⊕ ι) ε (Sum.inl '' s)).1.2.2.2.1
  have hGu := (hPar E R A hA (ι ⊕ ι) ε (Sum.inl '' (Set.univ : Set ι))).1.2.2.2.1
  refine ⟨max Rs Ru, fun y hy => ?_, fun x y hx hy => ?_⟩
  · exact hconv Set.univ y hu.2.2 hGu (hRu y (lt_of_le_of_lt (le_max_right _ _) hy))
  · exact conv_inf (l₁ := fun g => x * A.uH ε s g) (l₂ := fun g => y * A.uH ε Set.univ g)
      (inv x hs.2.1) (inv y hu.2.1)
      (hconv s x hs.2.2 hGs (hRs x (lt_of_le_of_lt (le_max_left _ _) hx)))
      (hconv Set.univ y hu.2.2 hGu (hRu y (lt_of_le_of_lt (le_max_right _ _) hy)))

end GlobalTheory.CompanionTheory.RgEis.UnitaryConv
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentConvergenceOfParabolicStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotent_convergence_of_parabolic : PositivityTheory.RgEis.ParLaw → PositivityTheory.RgEis.ConvU := by
  first | exact @GlobalTheory.CompanionTheory.RgEis.UnitaryConv.convU_of_parLaw | exact GlobalTheory.CompanionTheory.RgEis.UnitaryConv.convU_of_parLaw | (intros; apply GlobalTheory.CompanionTheory.RgEis.UnitaryConv.convU_of_parLaw <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelInductionFromGallery
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelInductionFromGallery
noncomputable section

open PositivityTheory.RgEis

namespace GlobalTheory.CompanionTheory.RgEis

section Heights

variable {G : Type} [Group G] [TopologicalSpace G]

theorem isHt_mono {Γ K P P' : Subgroup G} {η : G → ℝ} (h : IsHt Γ K P η) (hP : P' ≤ P) : IsHt Γ K P' η :=
  ⟨fun p hp g => h.left p (hP hp) g, h.right, fun γ hγ hp => h.rat γ hγ (hP hp), h.cont⟩

theorem isHt_lin {Γ K P : Subgroup G} {η θ : G → ℝ} (x y : ℝ) (h₁ : IsHt Γ K P η) (h₂ : IsHt Γ K P θ) :
    IsHt Γ K P fun g => x * η g + y * θ g := by
  refine ⟨?_, ?_, ?_, (continuous_const.mul h₁.cont).add (continuous_const.mul h₂.cont)⟩
  · intro p hp g
    simp only [h₁.left p hp g, h₂.left p hp g]
    ring
  · intro g k hk
    simp only [h₁.right g k hk, h₂.right g k hk]
  · intro γ hγ hp
    simp only [h₁.rat γ hγ hp, h₂.rat γ hγ hp, mul_zero, add_zero]

theorem isHt_congr {Γ K P : Subgroup G} {η θ : G → ℝ} (h : IsHt Γ K P η) (e : ∀ g, θ g = η g) : IsHt Γ K P θ := by
  rwa [show θ = η from funext e]

theorem conv_congr {Γ P : Subgroup G} {l l' : G → ℝ} (h : Conv Γ P l) (e : ∀ g, l' g = l g) : Conv Γ P l' := by
  rwa [show l' = l from funext e]

end Heights

variable {E R : Type} [Field E] [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R]
  [LocallyCompactSpace R] [SecondCountableTopology R]


open scoped Classical in
theorem wallQ (hTr : Transfer) (hTop : GrpTop) (hPar : ParLaw) (hLQ : LeviQ) (A : Ad E R) (hA : A.Good) (ε : ℤˣ)
    {ι : Type} [Fintype ι] [DecidableEq ι] (s : Set ι) (hI : Iwa (A.uQ ε s ⊓ A.uQ ε Set.univ) (A.uK ε ι))
    (hSg : A.Sg ε (sᶜ : Set ι)) {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
    (ρ : A.uK ε ι →* (W →L[ℂ] W)) (hρ : Continuous ρ) :
    HasWall (A.uΓ ε ι ⊓ A.uQ ε s) (A.uK ε ι) (A.uQ ε s ⊓ A.uQ ε Set.univ) (A.uQ ε s ⊓ A.uQ ε Set.univ) (A.uC ε ι)
      (fun g => A.uH ε Set.univ g - A.uH ε s g) (fun g => A.uH ε Set.univ g - A.uH ε s g)
      (fun g => (Fintype.card (sᶜ : Set ι) : ℝ) * (A.uH ε Set.univ g - A.uH ε s g)) ρ := by
  obtain ⟨π, j, c₀, hL, hP, hIw, hPH⟩ := hLQ E R A hA ι ε s hI
  obtain ⟨-, -, -, t₄, t₅, -, t₇⟩ := hTop E R A hA ι ε
  obtain ⟨-, -, -, u₄, u₅, -, u₇⟩ := hTop E R A hA (sᶜ : Set ι) ε
  have hP' := (hPar E R A hA (sᶜ : Set ι) ε Set.univ).2 (by rwa [inf_idem])
  rw [inf_idem] at hP'
  obtain ⟨hp, hh, -⟩ := hP'
  have hβ' : IsHt (A.uΓ ε (sᶜ : Set ι)) (A.uK ε (sᶜ : Set ι)) (A.uQ ε Set.univ)
      (fun g => (Fintype.card (sᶜ : Set ι) : ℝ) * A.uH ε Set.univ g) :=
    isHt_congr (isHt_lin (Fintype.card (sᶜ : Set ι) : ℝ) 0 hh hh) fun g => by ring
  have hPβ : PullHt (A.uK ε ι) (A.uQ ε s) π
      (fun g => (Fintype.card (sᶜ : Set ι) : ℝ) * (A.uH ε Set.univ g - A.uH ε s g))
      (fun g => (Fintype.card (sᶜ : Set ι) : ℝ) * A.uH ε Set.univ g) := by
    intro q k hk
    have := hPH q k hk
    simp only at this ⊢
    rw [this]
  exact (hTr _ W _ ρ t₇ hρ _ _ _ _ _ _ _ _ _ _ _ π j c₀ _ _ _ _ _ _ _ _ _ _ 0 u₇ hL hP hP hP hp hp hp hh hh hβ'
    hPH hPH hPβ hPH).1 (hSg hIw)

theorem wallsS (hTr : Transfer) (hTw : Twist) (hTop : GrpTop) (hPar : ParLaw) (hLS : LeviS) (A : Ad E R) (hA : A.Good)
    (hMir : A.MirGL) (ε : ℤˣ) {ι : Type} [Fintype ι] [DecidableEq ι] (i₀ i₁ : ι) (hN : 2 ≤ Fintype.card ι)
    (hS : Iwa (A.uQ ε (Set.univ : Set ι)) (A.uK ε ι)) {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]
    [FiniteDimensional ℂ W] (ρ : A.uK ε ι →* (W →L[ℂ] W)) (hρ : Continuous ρ) :
    HasFirst (A.uΓ ε ι ⊓ A.uQ ε Set.univ) (A.uK ε ι) (A.uQ ε Set.univ) (A.uQ ε {i₀} ⊓ A.uQ ε Set.univ)
      (A.uQ ε {i₁}ᶜ ⊓ A.uQ ε Set.univ) (A.uC ε ι) (A.uH ε {i₀}) (fun g => A.uH ε {i₁}ᶜ g - A.uH ε Set.univ g)
      (fun g => A.uH ε Set.univ g + (Fintype.card ι : ℝ) * (A.uH ε {i₁}ᶜ g - A.uH ε Set.univ g)) ρ ∧
    HasWall (A.uΓ ε ι ⊓ A.uQ ε Set.univ) (A.uK ε ι) (A.uQ ε {i₁}ᶜ ⊓ A.uQ ε Set.univ) (A.uQ ε {i₀} ⊓ A.uQ ε Set.univ)
      (A.uC ε ι) (fun g => A.uH ε {i₁}ᶜ g - A.uH ε Set.univ g) (A.uH ε {i₀})
      (fun g => (Fintype.card ι : ℝ) * A.uH ε {i₀} g - A.uH ε Set.univ g) ρ ∧
    HasLast (A.uΓ ε ι ⊓ A.uQ ε Set.univ) (A.uK ε ι) (A.uQ ε Set.univ) (A.uQ ε {i₀} ⊓ A.uQ ε Set.univ)
      (A.uQ ε {i₁}ᶜ ⊓ A.uQ ε Set.univ) (A.uC ε ι) (A.uH ε {i₀}) (fun g => A.uH ε {i₁}ᶜ g - A.uH ε Set.univ g)
      (fun g => A.uH ε Set.univ g + (Fintype.card ι : ℝ) * (A.uH ε {i₁}ᶜ g - A.uH ε Set.univ g))
      (A.uH ε Set.univ) (Fintype.card ι) ρ := by
  obtain ⟨π, j, hL, hP, -, hH⟩ := hLS E R A hA ι ε hS
  obtain ⟨g₁, g₂, -, t₄, t₅, -, t₇⟩ := hTop E R A hA ι ε
  have hk := hA.kcpt ι
  obtain ⟨a₁, a₂, ch, h₀, -⟩ := (hPar E R A hA ι ε {i₀}).1
  obtain ⟨b₁, b₂, -, h₁, -⟩ := (hPar E R A hA ι ε {i₁}ᶜ).1
  obtain ⟨u₁, u₂, -, hu, hst⟩ := (hPar E R A hA ι ε Set.univ).1
  rw [hst] at u₁ u₂ hu
  have hPS : IsPull (A.uQ ε Set.univ) (A.uQ ε Set.univ) ⊤ π 1 (A.uC ε ι) (A.cGL ι) := by
    have := hP Set.univ
    rwa [inf_idem, hst] at this
  have e : (1 : GL ι R → ℂ) * A.cGL ι = A.cGL ι := one_mul _
  obtain ⟨m₁, m₂, m₃⟩ := hMir ι i₀ i₁ hN
  have d₁ : IsHt (A.ratGL ι) (A.kGL ι) (stab R {i₁}ᶜ) (fun g => A.htGL {i₁}ᶜ g - A.htGL Set.univ g) :=
    isHt_congr (isHt_lin 1 (-1) h₁ (isHt_mono hu le_top)) fun g => by ring
  have d₂ : IsHt (A.ratGL ι) (A.kGL ι) (stab R {i₁}ᶜ)
      (fun g => A.htGL Set.univ g + (Fintype.card ι : ℝ) * (A.htGL {i₁}ᶜ g - A.htGL Set.univ g)) :=
    isHt_congr (isHt_lin (Fintype.card ι : ℝ) (1 - (Fintype.card ι : ℝ)) h₁ (isHt_mono hu le_top)) fun g => by ring
  have d₃ : IsHt (A.ratGL ι) (A.kGL ι) (stab R {i₀})
      (fun g => (Fintype.card ι : ℝ) * A.htGL {i₀} g - A.htGL Set.univ g) :=
    isHt_congr (isHt_lin (Fintype.card ι : ℝ) (-1) h₀ (isHt_mono hu le_top)) fun g => by ring
  have p₁ : PullHt (A.uK ε ι) (A.uQ ε Set.univ) π (fun g => A.uH ε {i₁}ᶜ g - A.uH ε Set.univ g)
      (fun g => A.htGL {i₁}ᶜ g - A.htGL Set.univ g) := by
    intro q k hk'
    simp only [hH {i₁}ᶜ q k hk', hH Set.univ q k hk']
  have p₂ : PullHt (A.uK ε ι) (A.uQ ε Set.univ) π
      (fun g => A.uH ε Set.univ g + (Fintype.card ι : ℝ) * (A.uH ε {i₁}ᶜ g - A.uH ε Set.univ g))
      (fun g => A.htGL Set.univ g + (Fintype.card ι : ℝ) * (A.htGL {i₁}ᶜ g - A.htGL Set.univ g)) := by
    intro q k hk'
    simp only [hH {i₁}ᶜ q k hk', hH Set.univ q k hk']
  have p₃ : PullHt (A.uK ε ι) (A.uQ ε Set.univ) π
      (fun g => (Fintype.card ι : ℝ) * A.uH ε {i₀} g - A.uH ε Set.univ g)
      (fun g => (Fintype.card ι : ℝ) * A.htGL {i₀} g - A.htGL Set.univ g) := by
    intro q k hk'
    simp only [hH {i₀} q k hk', hH Set.univ q k hk']
  have T₁ := hTw (GL ι R) (A.ratGL ι) (A.kGL ι) ⊤ (stab R {i₀}) (stab R {i₁}ᶜ) 1 (A.cGL ι) (A.htGL {i₀})
    (fun g => A.htGL {i₁}ᶜ g - A.htGL Set.univ g)
    (fun g => A.htGL Set.univ g + (Fintype.card ι : ℝ) * (A.htGL {i₁}ᶜ g - A.htGL Set.univ g)) (A.htGL Set.univ)
    (Fintype.card ι) hk ch u₁ a₁ b₁
  have T₂ := hTw (GL ι R) (A.ratGL ι) (A.kGL ι) ⊤ (stab R {i₁}ᶜ) (stab R {i₀}) 1 (A.cGL ι)
    (fun g => A.htGL {i₁}ᶜ g - A.htGL Set.univ g) (A.htGL {i₀})
    (fun g => (Fintype.card ι : ℝ) * A.htGL {i₀} g - A.htGL Set.univ g) (A.htGL Set.univ)
    (Fintype.card ι) hk ch u₁ b₁ a₁
  rw [e] at T₁ T₂
  have X₁ := hTr _ W _ ρ t₇ hρ _ _ _ _ _ _ _ _ _ _ _ π j 1 _ _ _ _ _ _ _ _ _ _ (Fintype.card ι) hk hL hPS
    (hP {i₀}) (hP {i₁}ᶜ) u₂ a₂ b₂ h₀ d₁ d₂ (hH {i₀}) p₁ p₂ (hH Set.univ)
  have X₂ := hTr _ W _ ρ t₇ hρ _ _ _ _ _ _ _ _ _ _ _ π j 1 _ _ _ _ _ _ _ _ _ _ (Fintype.card ι) hk hL hPS
    (hP {i₁}ᶜ) (hP {i₀}) u₂ b₂ a₂ d₁ h₀ d₃ p₁ (hH {i₀}) p₃ (hH Set.univ)
  exact ⟨X₁.2.1 (T₁.2.1 m₁), X₂.1 (T₂.1 m₂), X₁.2.2 (T₁.2.2 m₃)⟩


open Classical in
theorem sgStep : Gallery → Transfer → Twist → GrpTop → ParLaw → LeviS → LeviQ → ConvGrOf → ConvU → SgStep := by
  classical
  intro hGal hTr hTw hTop hPar hLS hLQ hCG hCU E R _ _ _ _ _ _ _ A hA hMir ε ι _ _ hN hIH hS W _ _ _ ρ hρ
  obtain ⟨i₀⟩ : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
  obtain ⟨π, j, -, -, hIw, -⟩ := hLS E R A hA ι ε hS
  obtain ⟨-, -, -, t₄, t₅, t₆, t₇⟩ := hTop E R A hA ι ε
  obtain ⟨Ra, ca₁, ca₂⟩ := hCU E R A hA (hCG E R A hA hMir) ι ε {i₀} (hIw _)
  obtain ⟨Rb, -, cb₂⟩ := hCU E R A hA (hCG E R A hA hMir) ι ε {i₀}ᶜ (hIw _)
  have pS := (hPar E R A hA ι ε Set.univ).2 (hIw _)
  rw [inf_idem] at pS
  have pA := (hPar E R A hA ι ε {i₀}).2 (hIw _)
  have pB := (hPar E R A hA ι ε {i₀}ᶜ).2 (hIw _)
  have hc₀ : ∀ f : Fintype ({i₀}ᶜ : Set ι), @Fintype.card _ f = Fintype.card ι - 1 := fun f => by
    rw [Fintype.card_compl_set]; simp
  have hc₁ : ∀ f : Fintype (({i₀}ᶜ : Set ι)ᶜ : Set ι), @Fintype.card _ f = 1 := fun f => by
    rw [Fintype.card_compl_set, hc₀]; omega
  have hc₀' : ∀ f : Fintype ({i₀}ᶜ : Set ι), ((@Fintype.card _ f : ℕ) : ℝ) = (Fintype.card ι : ℝ) - 1 := fun f => by
    rw [hc₀, Nat.cast_sub (by omega)]; simp
  have hq := fun (s : Set ι) (f : Fintype (sᶜ : Set ι)) (d : DecidableEq (sᶜ : Set ι)) => @hIH (sᶜ : Set ι) f d
  have w₁ := wallQ hTr hTop hPar hLQ A hA ε {i₀} (hIw _)
    (hq _ _ _ (by rw [hc₀]; omega) (by rw [hc₀]; omega)) ρ hρ
  have w₂ := wallQ hTr hTop hPar hLQ A hA ε {i₀}ᶜ (hIw _)
    (hq _ _ _ (hc₁ _).ge (by rw [hc₁]; omega)) ρ hρ
  rw [hc₀'] at w₁
  rw [hc₁] at w₂
  simp only [Nat.cast_one, one_mul] at w₂
  rw [show (fun g => A.uH ε Set.univ g - A.uH ε {i₀}ᶜ g) = fun g => -(A.uH ε {i₀}ᶜ g - A.uH ε Set.univ g) from
    funext fun g => by ring] at w₂
  obtain ⟨s₁, s₂, s₃⟩ := wallsS hTr hTw hTop hPar hLS A hA hMir ε i₀ i₀ hN hS ρ hρ
  refine hGal (A.U ε ι) W (A.uK ε ι) ρ t₇ hρ inferInstance (A.uΓ ε ι) (A.uQ ε Set.univ)
    (A.uQ ε {i₀} ⊓ A.uQ ε Set.univ) (A.uQ ε {i₀}ᶜ ⊓ A.uQ ε Set.univ) (A.uQ ε {i₀}) (A.uQ ε {i₀}ᶜ) (A.uC ε ι)
    (A.uH ε Set.univ) (A.uH ε {i₀}) (fun g => A.uH ε {i₀}ᶜ g - A.uH ε Set.univ g) (Fintype.card ι)
    inf_le_right inf_le_right inf_le_left inf_le_left pS.1 pA.1 pB.1 pS.2.1 pA.2.1
    (isHt_congr pB.2.1 fun g => by ring) ⟨max Ra Rb, fun y hy => ca₁ y (lt_of_le_of_lt (le_max_left _ _) hy),
      fun z y hz hy => ca₂ z y (lt_of_le_of_lt (le_max_left _ _) hz) (lt_of_le_of_lt (le_max_left _ _) hy),
      fun r y hr hy => conv_congr (cb₂ r y (lt_of_le_of_lt (le_max_right _ _) hr)
        (lt_of_le_of_lt (le_max_right _ _) hy)) fun g => by ring⟩ s₁ w₂ s₂ w₁ s₃

end GlobalTheory.CompanionTheory.RgEis
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelInductionFromGalleryStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_induction_from_gallery : PositivityTheory.RgEis.Gallery → PositivityTheory.RgEis.Transfer → PositivityTheory.RgEis.Twist → PositivityTheory.RgEis.GrpTop → PositivityTheory.RgEis.ParLaw → PositivityTheory.RgEis.LeviS → PositivityTheory.RgEis.LeviQ → PositivityTheory.RgEis.ConvGrOf → PositivityTheory.RgEis.ConvU → PositivityTheory.RgEis.SgStep := by
  first | exact @GlobalTheory.CompanionTheory.RgEis.sgStep | exact GlobalTheory.CompanionTheory.RgEis.sgStep | (intros; apply GlobalTheory.CompanionTheory.RgEis.sgStep <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewtonApproximationOfDichotomy
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

namespace GlobalTheory.CompanionTheory.NewtonStep

theorem isUnit_or_of_add_quot {S : Type} [CommRing S] (ϖ : S)
    (hj : ϖ ∈ (⊥ : Ideal S).jacobson) (hD : Dich ϖ) (a b : S ⧸ Ideal.span {ϖ ^ 2})
    (h : IsUnit (a + b)) : IsUnit a ∨ IsUnit b := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  obtain ⟨w', hw'⟩ := h.exists_right_inv
  obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective w'
  have h1 : (a + b) * w - 1 ∈ Ideal.span {ϖ ^ 2} := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    simp only [map_sub, map_mul, map_add (f := _), map_one]
    rw [hw', sub_self]
  obtain ⟨v, hv⟩ := Ideal.mem_span_singleton.mp h1
  have hu : IsUnit ((a + b) * w) := by
    have hj' : ϖ ∈ Ring.jacobson S := by simpa only [Ideal.jacobson_bot] using hj
    have h2 := Ring.mem_jacobson_iff.mp hj' (ϖ * v)
    have e : (a + b) * w = ϖ * (ϖ * v) + 1 := by linear_combination hv
    rw [e]; exact h2
  have hab : IsUnit (a + b) := isUnit_of_mul_isUnit_left hu
  have hspan : ϖ ^ 0 ∈ Ideal.span {a, b} := by
    obtain ⟨t, ht⟩ := hab.exists_right_inv
    have h3 : (a + b) * t ∈ Ideal.span {a, b} :=
      Ideal.mul_mem_right _ _ (Ideal.add_mem _ (Ideal.subset_span (by simp))
        (Ideal.subset_span (by simp)))
    rw [ht] at h3
    simpa using h3
  rcases hD a b ⟨0, hspan⟩ with h4 | h4
  · right
    exact (isUnit_of_dvd_unit (dvd_add h4 dvd_rfl) hab).map _
  · left
    exact (isUnit_of_dvd_unit (dvd_add dvd_rfl h4) hab).map _

open Polynomial in
theorem step_comp : ∀ {S : Type} [CommRing S] (ϖ : S), ϖ ∈ (⊥ : Ideal S).jacobson →
    ϖ ∈ nonZeroDivisors S → Dich ϖ → Aic (S := S ⧸ Ideal.span {ϖ ^ 2}) → Step ϖ := by
  intro S _ ϖ hj hnz hD hA Q n hQ hd hn
  have hRoots : Roots ϖ := GlobalTheory.T.polynomial_roots_of_closed_quotient ϖ hj hnz hD hA
  have hq0 : Q.coeff 0 = Q.eval 0 := Polynomial.coeff_zero_eq_eval_zero Q
  have hspan : ϖ ^ (n + 1) ∈ Ideal.span {Q.coeff 0, ϖ ^ (n + 1)} :=
    Ideal.subset_span (by simp)
  rcases hD (Q.coeff 0) (ϖ ^ (n + 1)) ⟨n + 1, hspan⟩ with hdiv | hdiv
  · refine ⟨0, ?_, ?_⟩
    · rw [← hq0]; exact hdiv
    · rw [zero_pow hd.ne']; exact dvd_zero _
  ·
    have hpow : ϖ ^ (n + 1) ∈ nonZeroDivisors S := pow_mem hnz _
    have hcancel : ∀ x : S, Q.coeff 0 * x = 0 → x = 0 := by
      intro x hx
      obtain ⟨e, he⟩ := hdiv
      have h0 : ϖ ^ (n + 1) * x = 0 := by
        rw [he]; linear_combination e * hx
      exact (mem_nonZeroDivisors_iff_right.mp hpow) x (by rw [mul_comm]; exact h0)
    obtain ⟨c, hc1, i0, hi1, hi2, hi3⟩ := GlobalTheory.T.newton_polygon_slope_existence ϖ hD hRoots (fun i => Q.coeff i)
      Q.natDegree (n + 1) hd hQ.coeff_natDegree hdiv
    have hs : ∀ i, ∃ t, (i = 0 → t = 1) ∧
        (i ≤ Q.natDegree → Q.coeff i * c ^ i = Q.coeff 0 * t) := by
      intro i
      rcases Nat.eq_zero_or_pos i with rfl | hi
      · exact ⟨1, fun _ => rfl, fun _ => by simp⟩
      · by_cases hid : i ≤ Q.natDegree
        · obtain ⟨t, ht⟩ := hc1 i hi hid
          exact ⟨t, fun h => by omega, fun _ => ht⟩
        · exact ⟨0, fun h => by omega, fun h => by omega⟩
    choose s hs0 hsd using hs
    have hunit : IsUnit (s i0) := by
      obtain ⟨t, ht⟩ := hi3
      have h5 : Q.coeff 0 * (s i0 * t - 1) = 0 := by
        have h6 := hsd i0 hi2
        rw [h6] at ht
        linear_combination -ht
      have h7 := hcancel _ h5
      exact IsUnit.of_mul_eq_one t (by linear_combination h7)
    let R : Polynomial S := ∑ i ∈ Finset.range (Q.natDegree + 1),
      Polynomial.C (s i) * Polynomial.X ^ i
    have hRc : ∀ j, j ≤ Q.natDegree → R.coeff j = s j := by
      intro j hj'
      simp only [R, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
      rw [Finset.sum_ite_eq]
      simp [Nat.lt_succ_of_le hj']
    have hRe : ∀ y, R.eval y = ∑ i ∈ Finset.range (Q.natDegree + 1), s i * y ^ i := by
      intro y
      simp [R, Polynomial.eval_finsetSum]
    let P : Polynomial (S ⧸ Ideal.span {ϖ ^ 2}) := R.map (Ideal.Quotient.mk _)
    have hP0 : P.coeff 0 = 1 := by
      simp only [P, Polynomial.coeff_map]
      rw [hRc 0 (Nat.zero_le _), hs0 0 rfl, map_one]
    have hPi : IsUnit (P.coeff i0) := by
      simp only [P, Polynomial.coeff_map]
      rw [hRc i0 hi2]
      exact hunit.map _
    have hroot : ∃ y', P.eval y' = 0 := by
      let T := S ⧸ Ideal.span {ϖ ^ 2}
      rcases subsingleton_or_nontrivial T with hT | hT
      · exact ⟨0, Subsingleton.elim _ _⟩
      have hAdd : ∀ a b : T, IsUnit (a + b) → IsUnit a ∨ IsUnit b :=
        isUnit_or_of_add_quot ϖ hj hD
      have unitRoot : ∀ (d : ℕ) (F : Polynomial T), F.Monic → F.natDegree = d →
          ∀ k < d, IsUnit (F.coeff k) → ∃ u : Tˣ, F.eval (u : T) = 0 := by
        intro d
        induction d with
        | zero =>
          intro F hF hdeg k hk
          omega
        | succ d ih =>
          intro F hF hdeg k hk hcoeff
          obtain ⟨x, hx⟩ := hA F hF (by omega)
          by_cases hxu : IsUnit x
          · obtain ⟨u, rfl⟩ := hxu
            exact ⟨u, hx⟩
          let G := F /ₘ (X - C x)
          have hfactor : (X - C x) * G = F := mul_divByMonic_eq_iff_isRoot.mpr hx
          have hG : G.Monic := (monic_X_sub_C x).of_mul_monic_left (hfactor.symm ▸ hF)
          have hGdeg : G.natDegree = d := by
            have h := (monic_X_sub_C x).natDegree_mul hG
            rw [hfactor, hdeg, natDegree_X_sub_C] at h
            omega
          cases k with
          | zero =>
            rw [← hfactor, sub_mul, coeff_sub, coeff_X_mul_zero, coeff_C_mul, zero_sub] at hcoeff
            have hprod : IsUnit (x * G.coeff 0) := by simpa only [neg_neg] using hcoeff.neg
            exact (hxu (isUnit_of_mul_isUnit_left hprod)).elim
          | succ k =>
            rw [← hfactor, coeff_X_sub_C_mul, sub_eq_add_neg] at hcoeff
            rcases hAdd _ _ hcoeff with hGu | hneg
            · obtain ⟨u, hu⟩ := ih G hG hGdeg k (by omega) hGu
              exact ⟨u, by rw [← hfactor, eval_mul, hu, mul_zero]⟩
            · have hprod : IsUnit (x * G.coeff (k + 1)) := by
                simpa only [neg_neg] using hneg.neg
              exact (hxu (isUnit_of_mul_isUnit_left hprod)).elim
      have htd : P.natTrailingDegree = 0 :=
        Nat.le_zero.mp (natTrailingDegree_le_of_ne_zero (by rw [hP0]; exact one_ne_zero))
      have hmon : P.reverse.Monic := by
        rw [Monic, reverse_leadingCoeff, trailingCoeff, htd, hP0]
      have hdeg : P.reverse.natDegree = P.natDegree := by
        rw [reverse_natDegree, htd, Nat.sub_zero]
      have hle : i0 ≤ P.natDegree := le_natDegree_of_ne_zero hPi.ne_zero
      have hcoeff : P.reverse.coeff (P.natDegree - i0) = P.coeff i0 := by
        rw [coeff_reverse, revAt_le (Nat.sub_le _ _)]
        congr 1
        omega
      obtain ⟨u, hu⟩ := unitRoot P.natDegree P.reverse hmon hdeg (P.natDegree - i0)
        (by omega) (hcoeff.symm ▸ hPi)
      refine ⟨↑(u⁻¹), ?_⟩
      let : Invertible ((u⁻¹ : Tˣ) : T) := (u⁻¹).invertible
      have hre := eval₂_reverse_mul_pow (RingHom.id T) ((u⁻¹ : Tˣ) : T) P
      have hinv : ⅟((u⁻¹ : Tˣ) : T) = (u : T) := by simp
      rw [hinv, eval₂_id, eval₂_id, hu, zero_mul] at hre
      exact hre.symm
    obtain ⟨y', hy'⟩ := hroot
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y'
    have hRy : ϖ ^ 2 ∣ R.eval y := by
      rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem]
      simp only [P, Polynomial.eval_map] at hy'
      rwa [Polynomial.eval₂_at_apply] at hy'
    have hQz : Q.eval (c * y) = Q.coeff 0 * R.eval y := by
      rw [Polynomial.eval_eq_sum_range, hRe, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      have h8 := hsd i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
      rw [mul_pow]
      linear_combination (y ^ i) * h8
    have hn0 : ϖ ^ n ∣ Q.coeff 0 := by rw [hq0]; exact hn
    refine ⟨c * y, ?_, ?_⟩
    · rw [hQz]
      have h9 : ϖ ^ n * ϖ ^ 2 ∣ Q.coeff 0 * R.eval y := mul_dvd_mul hn0 hRy
      refine dvd_trans ?_ h9
      rw [← pow_add]
      exact pow_dvd_pow _ (by omega)
    · have h10 : Q.coeff 0 ∣ c ^ Q.natDegree := by
        have h11 := hc1 Q.natDegree hd le_rfl
        simpa [hQ.coeff_natDegree] using h11
      rw [mul_pow]
      exact dvd_mul_of_dvd_left (dvd_trans hn0 h10) _

end GlobalTheory.CompanionTheory.NewtonStep
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeasurableZeroCount
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeasurableZeroCount
open MeasureTheory ReciprocityTheory.L2DbarEstimates GlobalTheory.CompanionTheory.FSCrofton
open scoped ENNReal ComplexConjugate

namespace GlobalTheory.CompanionTheory.FSCrofton

open TopologicalSpace

variable {X : Type} [TopologicalSpace X] {d : ℕ} {α : Type} [Fintype α]

def zeroSetIn (A : Set X) (b : α → X → ℂ) (C : Fin d → α → ℂ) : Set X :=
  {z ∈ A | ∀ k, ∑ j, C k j * b j z = 0}

theorem isClosed_meets_compact {K : Set X} (hK : IsCompact K) {b : α → X → ℂ}
    (hb : ∀ j, ContinuousOn (b j) K) :
    IsClosed {C : Fin d → α → ℂ | ∃ z ∈ K, ∀ k, ∑ j, C k j * b j z = 0} := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hF : Continuous fun p : (Fin d → α → ℂ) × K => fun k => ∑ j, p.1 k j * b j p.2 := by
    refine continuous_pi fun k => ?_
    refine continuous_finsetSum _ fun j _ => ?_
    have h1 : Continuous fun p : (Fin d → α → ℂ) × K => p.1 k j :=
      (continuous_apply j).comp ((continuous_apply k).comp continuous_fst)
    have h2 : Continuous fun p : (Fin d → α → ℂ) × K => b j (p.2 : X) :=
      (hb j).comp_continuous (continuous_subtype_val.comp continuous_snd) fun p => p.2.2
    exact h1.mul h2
  have hclosed : IsClosed {p : (Fin d → α → ℂ) × K | ∀ k, ∑ j, p.1 k j * b j p.2 = 0} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun k => isClosed_eq ((continuous_apply k).comp hF) continuous_const
  have himage : {C : Fin d → α → ℂ | ∃ z ∈ K, ∀ k, ∑ j, C k j * b j z = 0} =
      Prod.fst '' {p : (Fin d → α → ℂ) × K | ∀ k, ∑ j, p.1 k j * b j p.2 = 0} := by
    ext C
    constructor
    · rintro ⟨z, hz, h⟩
      exact ⟨(C, ⟨z, hz⟩), h, rfl⟩
    · rintro ⟨⟨C', z⟩, h, rfl⟩
      exact ⟨z, z.2, h⟩
  rw [himage]
  exact isClosedMap_fst_of_compactSpace _ hclosed

theorem measurableSet_meets_inter [T2Space X] [SecondCountableTopology X] [LocallyCompactSpace X]
    {A B : Set X} (hA : IsSigmaCompact A) (hB : IsOpen B) {b : α → X → ℂ}
    (hb : ∀ j, ContinuousOn (b j) A) :
    MeasurableSet {C : Fin d → α → ℂ | ∃ z ∈ A ∩ B, ∀ k, ∑ j, C k j * b j z = 0} := by
  obtain ⟨K, hK, hKA⟩ := hA
  have hBσ : IsSigmaCompact B := by
    haveI := hB.locallyCompactSpace
    exact isSigmaCompact_iff_sigmaCompactSpace.mpr inferInstance
  obtain ⟨L, hL, hLB⟩ := hBσ
  have hEq : {C : Fin d → α → ℂ | ∃ z ∈ A ∩ B, ∀ k, ∑ j, C k j * b j z = 0} =
      ⋃ n, ⋃ m, {C : Fin d → α → ℂ | ∃ z ∈ K n ∩ L m, ∀ k, ∑ j, C k j * b j z = 0} := by
    ext C
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · rintro ⟨z, ⟨hzA, hzB⟩, h⟩
      rw [← hKA, Set.mem_iUnion] at hzA
      rw [← hLB, Set.mem_iUnion] at hzB
      obtain ⟨n, hn⟩ := hzA
      obtain ⟨m, hm⟩ := hzB
      exact ⟨n, m, z, ⟨hn, hm⟩, h⟩
    · rintro ⟨n, m, z, ⟨hn, hm⟩, h⟩
      refine ⟨z, ⟨?_, ?_⟩, h⟩
      · rw [← hKA]
        exact Set.mem_iUnion.mpr ⟨n, hn⟩
      · rw [← hLB]
        exact Set.mem_iUnion.mpr ⟨m, hm⟩
  rw [hEq]
  refine MeasurableSet.iUnion fun n => MeasurableSet.iUnion fun m => ?_
  refine (isClosed_meets_compact ((hK n).inter (hL m)) fun j => ?_).measurableSet
  refine (hb j).mono ?_
  intro z hz
  rw [← hKA]
  exact Set.mem_iUnion.mpr ⟨n, hz.1⟩

theorem natCast_le_encard_zeroSetIn_iff [T2Space X] [SecondCountableTopology X] (A : Set X)
    (b : α → X → ℂ) (C : Fin d → α → ℂ) (N : ℕ) :
    (N : ℕ∞) ≤ (zeroSetIn A b C).encard ↔
      ∃ f : Fin N → countableBasis X,
        (∀ i j, i ≠ j → Disjoint (f i : Set X) (f j)) ∧
        ∀ i, ∃ z ∈ A ∩ (f i : Set X), ∀ k, ∑ j, C k j * b j z = 0 := by
  classical
  constructor
  · intro hN
    obtain ⟨t, htZ, htN⟩ := Set.exists_subset_encard_eq hN
    have htfin : t.Finite := Set.finite_of_encard_eq_coe htN
    haveI : Finite t := htfin.to_subtype
    have hcard : Nat.card t = N := by
      rw [Nat.card_coe_set_eq, Set.ncard_def, htN, ENat.toNat_natCast]
    let e : t ≃ Fin N := (Finite.equivFin t).trans (finCongr hcard)
    obtain ⟨U, hU, hdisj⟩ := htfin.t2_separation
    have hex : ∀ i : Fin N, ∃ v ∈ countableBasis X, (e.symm i : X) ∈ v ∧ v ⊆ U (e.symm i) :=
      fun i => (isBasis_countableBasis X).exists_subset_of_mem_open (hU _).1 (hU _).2
    choose v hvB hpv hvU using hex
    refine ⟨fun i => ⟨v i, hvB i⟩, ?_, ?_⟩
    · intro i j hij
      have hne : (e.symm i : X) ≠ e.symm j := by
        intro h
        exact hij (e.symm.injective (Subtype.ext h))
      show Disjoint (v i) (v j)
      exact Disjoint.mono (hvU i) (hvU j) (hdisj (e.symm i).2 (e.symm j).2 hne)
    · intro i
      have hz : (e.symm i : X) ∈ zeroSetIn A b C := htZ (e.symm i).2
      simp only [zeroSetIn, Set.mem_ofPred_eq] at hz
      exact ⟨e.symm i, ⟨hz.1, hpv i⟩, hz.2⟩
  · rintro ⟨f, hdisj, hz⟩
    choose z hzmem hzero using hz
    have hinj : Function.Injective z := by
      intro i j h
      by_contra hij
      have hzj : z i ∈ (f j : Set X) := by
        rw [h]
        exact (hzmem j).2
      exact Set.disjoint_left.mp (hdisj i j hij) (hzmem i).2 hzj
    have hsub : ((Finset.univ.image z : Finset X) : Set X) ⊆ zeroSetIn A b C := by
      intro x hx
      simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at hx
      obtain ⟨i, rfl⟩ := hx
      simp only [zeroSetIn, Set.mem_ofPred_eq]
      exact ⟨(hzmem i).1, hzero i⟩
    calc (N : ℕ∞) = ((Finset.univ.image z : Finset X) : Set X).encard := by
          rw [Set.encard_coe_eq_coe_finsetCard, Finset.card_image_of_injective _ hinj,
            Finset.card_univ, Fintype.card_fin]
      _ ≤ (zeroSetIn A b C).encard := Set.encard_le_encard hsub

theorem measurableSet_natCast_le_encard_zeroSetIn [T2Space X] [SecondCountableTopology X]
    [LocallyCompactSpace X] {A : Set X} (hA : IsSigmaCompact A) {b : α → X → ℂ}
    (hb : ∀ j, ContinuousOn (b j) A) (N : ℕ) :
    MeasurableSet {C : Fin d → α → ℂ | (N : ℕ∞) ≤ (zeroSetIn A b C).encard} := by
  classical
  haveI : Countable (countableBasis X) := (countable_countableBasis X).to_subtype
  have hEq : {C : Fin d → α → ℂ | (N : ℕ∞) ≤ (zeroSetIn A b C).encard} =
      ⋃ f : Fin N → countableBasis X, ⋃ (_ : ∀ i j, i ≠ j → Disjoint (f i : Set X) (f j)),
        ⋂ i, {C : Fin d → α → ℂ | ∃ z ∈ A ∩ (f i : Set X), ∀ k, ∑ j, C k j * b j z = 0} := by
    ext C
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_iInter, exists_prop]
    exact natCast_le_encard_zeroSetIn_iff A b C N
  rw [hEq]
  refine MeasurableSet.iUnion fun f => MeasurableSet.iUnion fun _ => MeasurableSet.iInter fun i => ?_
  exact measurableSet_meets_inter hA ((isBasis_countableBasis X).isOpen (f i).2) hb

private theorem measurable_of_natCast_le_lemma {β : Type} [MeasurableSpace β] (g : β → ℕ∞)
    (hg : ∀ N : ℕ, MeasurableSet {x | (N : ℕ∞) ≤ g x}) : Measurable g := by
  refine measurable_to_countable' fun x => ?_
  induction x using ENat.recTopCoe with
  | top =>
    have h : g ⁻¹' {⊤} = ⋂ N : ℕ, {x | (N : ℕ∞) ≤ g x} := by
      ext y
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iInter, Set.mem_ofPred_eq]
      generalize g y = t
      induction t using ENat.recTopCoe with
      | top => exact ⟨fun _ _ => le_top, fun _ => rfl⟩
      | coe m =>
        constructor
        · intro hy
          exact absurd hy (ENat.natCast_ne_top m)
        · intro hy
          exfalso
          have h1 := hy (m + 1)
          norm_cast at h1
          omega
    rw [h]
    exact MeasurableSet.iInter hg
  | coe n =>
    have h : g ⁻¹' {(n : ℕ∞)} = {x | (n : ℕ∞) ≤ g x} \ {x | ((n + 1 : ℕ) : ℕ∞) ≤ g x} := by
      ext y
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_sdiff, Set.mem_ofPred_eq]
      generalize g y = t
      induction t using ENat.recTopCoe with
      | top => simp
      | coe m =>
        norm_cast
        constructor
        · intro h1
          omega
        · intro h1
          omega
    rw [h]
    exact (hg n).diff (hg (n + 1))

theorem measurable_zeroCnt_of_continuousOn [T2Space X] [SecondCountableTopology X]
    [LocallyCompactSpace X] {A : Set X} (hA : IsSigmaCompact A) {b : α → X → ℂ}
    (hb : ∀ j, ContinuousOn (b j) A) :
    Measurable (zeroCnt d A b : (Fin d → α → ℂ) → ℝ≥0∞) := by
  have hg : Measurable fun C : Fin d → α → ℂ => (zeroSetIn A b C).encard :=
    measurable_of_natCast_le_lemma _ fun N => measurableSet_natCast_le_encard_zeroSetIn hA hb N
  exact (Measurable.of_discrete (f := fun n : ℕ∞ => (n : ℝ≥0∞))).comp hg

theorem measurable_zeroCnt : ∀ (d : ℕ) (α : Type) [Fintype α] (U A : Set (V d)) (b : α → V d → ℂ),
    (∀ j, ContinuousOn (b j) U) → A ⊆ U → IsSigmaCompact A →
      Measurable (zeroCnt d A b : (Fin d → α → ℂ) → ℝ≥0∞) := by
  intro d α _ U A b hb hAU hA
  exact measurable_zeroCnt_of_continuousOn hA fun j => (hb j).mono hAU

end GlobalTheory.CompanionTheory.FSCrofton
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeasurableZeroCountStatement
open MeasureTheory ReciprocityTheory.L2DbarEstimates GlobalTheory.CompanionTheory.FSCrofton
open scoped ENNReal ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.measurable_zero_count : ∀ (d : ℕ) (α : Type) [Fintype α] (U A : Set (V d)) (b : α → V d → ℂ), (∀ j, ContinuousOn (b j) U) → A ⊆ U → IsSigmaCompact A → Measurable (zeroCnt d A b : (Fin d → α → ℂ) → ℝ≥0∞) := by
  first | exact @GlobalTheory.CompanionTheory.FSCrofton.measurable_zeroCnt | exact GlobalTheory.CompanionTheory.FSCrofton.measurable_zeroCnt | (intros; apply GlobalTheory.CompanionTheory.FSCrofton.measurable_zeroCnt <;> assumption)
end
end
