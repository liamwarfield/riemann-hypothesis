module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CongModOfMkEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisAutConjugateFieldPointsCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapInverseNatCast
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSetupDividingLabelPersistsDeeperLevel

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisPermutesWeightPartsUpToRoots
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisPermutesWeightPartsUpToRoots
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.GalPart

open GlobalTheory.UPoinc.USum

section General

open MonObj

variable {o Ω o' Ω' : Type} [CommRing o] [Field Ω] [Algebra o Ω] [CommRing o'] [Field Ω'] [Algebra o' Ω']
  {S : ThetaSys o Ω} {S' : ThetaSys o' Ω'} {ρ : S.Real} {ρ' : S'.Real} {lab : S.Gam → S'.Gam} {φ : Ω →+* Ω'}
  {P₀ : PolAV (Sp Ω')} {a : P₀.A.left ⟶ ρ.P.A.left} {a' : P₀.A.left ⟶ ρ'.P.A.left}

theorem exists_isGenLab_of (h₁ : IsGrpPullback P₀.A ρ.P.A (spMap (φ.comp S.R.val.toRingHom)) a)
    (h₂ : IsGrpPullback P₀.A ρ'.P.A (spMap S'.R.val.toRingHom) a') (l₁ : LBIso P₀.L (ρ.P.L.pull a))
    (l₂ : LBIso P₀.L (ρ'.P.L.pull a'))
    (hpt : ∀ x, ∃ w : Sp Ω' ⟶ P₀.A.left, w ≫ a = spMap (φ.comp S.R.val.toRingHom) ≫ (ρ.pt x).left ∧
      w ≫ a' = spMap S'.R.val.toRingHom ≫ (ρ'.pt (lab x)).left) :
    ∃ x, IsGenLab ρ ρ' lab φ P₀ a a' x ∧ ∀ b b', x (b + b') = x b * x b' := by
  obtain ⟨w, hw, hadd, -⟩ := GalAct.exists_generic_labels ρ' h₂
  obtain ⟨e, he⟩ := GalAct.exists_mulEquiv_points h₁ (𝟙 _) _ (Category.id_comp _)
  have := GalTrans.mono_val S'.R S'.frac
  have : Mono a' := (MorphismProperty.monomorphisms Scheme).of_isPullback h₂.1.flip (.infer_property _)
  refine ⟨fun b => e (w b), ⟨h₁, h₂, l₁, l₂, fun b => ⟨(w b).left, Over.w (w b), (he _).symm, hw b⟩,
    fun k => ?_⟩, fun b b' => by simp only [hadd, map_mul]⟩
  obtain ⟨v, hv, hv'⟩ := hpt k
  obtain rfl : v = (w (lab k)).left := (cancel_mono a').1 (hv'.trans (hw _).symm)
  exact Over.OverMorphism.ext ((he _).trans hv)

variable {x : S'.Gam → (genPt (φ.comp S.R.val.toRingHom) ⟶ ρ.P.A)}

theorem exists_conj_over (hx : IsGenLab ρ ρ' lab φ P₀ a a' x) (σ : Ω' →+* Ω') (hσ : Function.Surjective σ)
    (hφ : σ.comp φ = φ) : ∃ (g : S'.Gam ≃+ S'.Gam)
      (s : genPt (φ.comp S.R.val.toRingHom) ⟶ genPt (φ.comp S.R.val.toRingHom)) (t : P₀.A.left ⟶ P₀.A.left),
      s.left = spMap σ ∧ (∀ b, x (g b) = s ≫ x b) ∧ (∀ k, g (lab k) = lab k) ∧ t ≫ a = a ∧
      IsGrpPullback P₀.A P₀.A (spMap σ) t ∧ LBIso P₀.L (P₀.L.pull t) ∧
      ∀ y (w w' : Sp Ω' ⟶ P₀.A.left), w ≫ a' = spMap S'.R.val.toRingHom ≫ (ρ'.pt y).left →
        w' ≫ t = spMap σ ≫ w → w' ≫ a' = spMap S'.R.val.toRingHom ≫ (ρ'.pt (g y)).left := by
  obtain ⟨h₁, h₂, l₁, l₂, hw, hlab⟩ := hx
  have hs : spMap σ ≫ spMap (φ.comp S.R.val.toRingHom) = spMap (φ.comp S.R.val.toRingHom) :=
    GalTrans.sp_comp (by rw [← RingHom.comp_assoc, hφ])
  obtain ⟨t, ht₁, ht₂⟩ : ∃ t : P₀.A.left ⟶ P₀.A.left, t ≫ a = a ∧ t ≫ P₀.A.hom = P₀.A.hom ≫ spMap σ :=
    ⟨h₁.1.lift a (P₀.A.hom ≫ spMap σ) (by rw [Category.assoc, hs, h₁.1.w]), h₁.1.lift_fst _ _ _, h₁.1.lift_snd _ _ _⟩
  have ht : IsGrpPullback P₀.A P₀.A (spMap σ) t := h₁.cancel (h₁.congr hs.symm ht₁.symm) ht₂
  have lt : LBIso (P₀.L.pull t) (ρ.P.L.pull a) :=
    l₁.chartPull (Geo.Tor.chartPullPull P₀.L t t rfl)
      (chartPullSame ρ.P.L (fun _ => a) (fun _ => a) _ t fun _ => ht₁.symm)
  obtain ⟨g, hg, hg'⟩ := GalAct.exists_label_action ρ' h₂ σ hσ ht
  have := GalTrans.mono_val S'.R S'.frac
  have : Mono a' := (MorphismProperty.monomorphisms Scheme).of_isPullback h₂.1.flip (.infer_property _)
  refine ⟨g, Over.homMk (spMap σ) hs, t, rfl, fun b => Over.OverMorphism.ext ?_, fun k => ?_, ht₁, ht,
    LBIso.trans P₀.isLB (pull_isLB ρ.P.isLB _) (pull_isLB P₀.isLB _) l₁ lt.symm, hg⟩
  · obtain ⟨w, e₀, e₁, e₂⟩ := hw b
    obtain ⟨w', -, e₁', e₂'⟩ := hw (g b)
    have c : (spMap σ ≫ w) ≫ P₀.A.hom = 𝟙 _ ≫ spMap σ := by rw [Category.assoc, e₀]; simp
    have k := ht.1.lift_fst _ _ c
    obtain rfl : w' = ht.1.lift _ _ c := (cancel_mono a').1 (e₂'.trans (hg b w _ e₂ k).symm)
    rw [← e₁', ← ht₁, reassoc_of% k, e₁]
    rfl
  · obtain ⟨w, e₀, e₁, e₂⟩ := hw (lab k)
    refine hg' _ w e₂ (h₁.1.hom_ext ?_ ?_)
    · rw [Category.assoc, Category.assoc, ht₁, e₁, hlab]
      exact ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) hs)).symm
    · rw [Category.assoc, Category.assoc, ht₂, reassoc_of% e₀, e₀, Category.comp_id]


open Classical in
theorem exists_root_conj [ArithBase o Ω] [ArithBase o' Ω'] (hx : IsGenLab ρ ρ' lab φ P₀ a a' x)
    (hadd : ∀ b b', x (b + b') = x b * x b') {m : ℕ} (hm : S'.N = m ^ 2) (H : AddSubgroup S'.Gam) (x₀ : S.Gam)
    (h₀ : S.th x₀ ≠ 0) (h₀' : S'.th (lab x₀) ≠ 0) {κ : S.Gam} {h : S'.Gam} (hh : h ∈ H) (e : m • h = lab κ) :
    ∃ ξ : Ω', (∃ k : ℕ, 0 < k ∧ ξ ^ k = 1) ∧ ∀ (σ : Ω' →+* Ω'), σ.comp φ = φ →
      ∀ (s : genPt (φ.comp S.R.val.toRingHom) ⟶ genPt (φ.comp S.R.val.toRingHom)), s.left = spMap σ →
      ∀ g : S'.Gam ≃+ S'.Gam, (∀ b, x (g b) = s ≫ x b) → (∀ k, g (lab k) = lab k) → (∀ y, g y ∈ H ↔ y ∈ H) →
      ∀ b, σ (ξ * (partV S' H ρ'.i₀ b h / S'.th (lab x₀))) = ξ * (partV S' H ρ'.i₀ (g b) h / S'.th (lab x₀)) := by
  have := Fintype.ofFinite (S'.perp H)
  choose V hV₁ using fun t : S'.perp H => TV.ex hx hadd hm t e
  have hV : ∀ h' ∈ H, m • h' = lab κ → ∀ t : S'.perp H, TV ρ x m t h' κ (V t) := fun h' hh' e' t => by
    have := (hV₁ t).transl hx hadd hm (k := h' - h) (by rw [smul_sub, e, e', sub_self]) (t.2 _ (sub_mem hh' hh))
    rwa [add_sub_cancel] at this
  have hφ₀ : φ (S.th x₀) ≠ 0 := (map_ne_zero φ).2 h₀
  obtain ⟨ξ, hξ, hc⟩ := GlobalTheory.T.twistedThetaValue_eq_root_mul_thetaOperatorValue ρ ρ' lab φ P₀ a a' x hx m hm κ x₀ h e
  have hf : ∀ b, ξ * (partV S' H ρ'.i₀ b h / S'.th (lab x₀)) =
      algebraMap o' Ω' (Ring.inverse (Nat.card (S'.perp H) : o')) *
        (∑ t : S'.perp H, algebraMap o' Ω' (S'.ζN ^ (-(wtChar S' _ b t)).val) * V t) / φ (S.th x₀) := fun b => by
    have hv : ∀ t : S'.perp H, V t =
        (ξ * φ (S.th x₀) / S'.th (lab x₀)) * ∑ j, algebraMap o' Ω' (S'.ρ t j ρ'.i₀) * S'.ev h j := fun t => by
      rw [div_mul_eq_mul_div, eq_div_iff h₀']
      exact hc t _ (hV₁ t)
    simp only [hv, partV_eq, mul_left_comm _ (ξ * φ (S.th x₀) / S'.th (lab x₀)), ← Finset.mul_sum]
    field_simp
  refine ⟨ξ, hξ, fun σ hφ s hs g hg hl hH b => ?_⟩
  have hw := hx.weil_conj σ s hs hg
  have h0 : ∀ y y', eStd S'.g _ y y' = 0 ↔ eStd S'.g _ (g y) (g y') = 0 := fun y y' => by
    rw [← zeta_pow_eq_one_iff, ← zeta_pow_eq_one_iff, ← hw, map_eq_one_iff σ σ.injective]
  have hT : ∀ t, t ∈ S'.perp H ↔ g t ∈ S'.perp H := fun t =>
    ⟨fun ht y hy => by
      obtain ⟨y, rfl⟩ := g.surjective y
      exact (h0 _ _).1 (ht y ((hH y).1 hy)), fun ht y hy => (h0 _ _).2 (ht _ ((hH y).2 hy))⟩
  let e' : S'.perp H ≃ S'.perp H := g.toEquiv.subtypeEquiv hT
  have hζ : ∀ t : S'.perp H, σ (algebraMap o' Ω' (S'.ζN ^ (-(wtChar S' _ b t)).val)) =
      algebraMap o' Ω' (S'.ζN ^ (-(wtChar S' _ (g b) (e' t))).val) := fun t => by
    have e₁ : σ (algebraMap o' Ω' (S'.ζN ^ (wtChar S' _ b t).val)) =
        algebraMap o' Ω' (S'.ζN ^ (wtChar S' _ (g b) (e' t)).val) := by
      refine (congrArg (fun q => σ (algebraMap o' Ω' q)) (zetaN_pow_cast _)).trans
        (Eq.trans ?_ (congrArg (algebraMap o' Ω') (zetaN_pow_cast _)).symm)
      rw [map_pow, map_pow, hw, ← map_pow]
      rfl
    have e₂ := congrArg (fun q => σ (algebraMap o' Ω' q)) (zetaN_neg_mul (wtChar S' _ b t))
    have e₃ := congrArg (algebraMap o' Ω') (zetaN_neg_mul (wtChar S' _ (g b) (e' t)))
    simp only [map_mul, map_one] at e₂ e₃
    rw [e₁] at e₂
    exact (eq_inv_of_mul_eq_one_left e₂).trans (eq_inv_of_mul_eq_one_left e₃).symm
  have hσV : ∀ t : S'.perp H, σ (V t) = V (e' t) := fun t =>
    ((hV₁ t).conj σ s hs g.toAddMonoidHom hg).unique ρ'
      (hV (g h) ((hH h).2 hh) (by rw [← map_nsmul, e, hl]) (e' t))
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hf, hf, map_div₀, map_mul, map_inverse_natCast, map_sum,
    show σ (φ (S.th x₀)) = φ (S.th x₀) from RingHom.congr_fun hφ _,
    ← Equiv.sum_comp e' fun t => algebraMap o' Ω' (S'.ζN ^ (-(wtChar S' _ (g b) t)).val) * V t]
  simp only [map_mul, hζ, hσV]

end General

theorem exists_root_galois : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsDiagEnd F W X₁.ρ.P X₁.u ε₁ → ∀ (D : Deep X₁ ε₁) (z₁ : X₁.M.Z) (z₂ : D.X.M.Z), D.q z₂ = z₁ → ∃ U : X₁.S.HH X₁.M z₁ → D.X.Ω₁, (∀ κ, ∃ k : ℕ, 0 < k ∧ U κ ^ k = 1) ∧ ∀ σ : D.X.Ω₁ ≃ₐ[X₁.Ω₁] D.X.Ω₁, ∃ a : D.X.S.Gam ≃+ D.X.S.Gam, D.GalLab σ a ∧ (∀ x, a (D.lab x) = D.lab x) ∧ ((∀ x, a x ∈ D.X.S.HH D.X.M z₂ ↔ x ∈ D.X.S.HH D.X.M z₂) → ∀ b κ, σ (U κ * GSum.part D z₁ z₂ b κ) = U κ * GSum.part D z₁ z₂ (a b) κ) := by
  intro g n F W Z i X₁ hg hn hodd hi hE hT hP ε₁ hε₁ D z₁ z₂ hq
  obtain ⟨P₀, a₁, a₂, ε₀, h₁, h₂, l₁, l₂, hε, hpt⟩ := D.same
  obtain ⟨x, hx, hadd⟩ := exists_isGenLab_of h₁ h₂ l₁ l₂ hpt
  have hb : GSum.base X₁ z₁ ∈ X₁.S.supI X₁.M z₁ := by
    have hne : (X₁.S.supI X₁.M z₁).Nonempty := X₁.div z₁
    rw [GSum.base, dite_eq_left hne]
    exact hne.some_mem
  have hb' := GlobalTheory.T.thetaSetup_dividingLabel_persists_deeperLevel g n F W Z i X₁ hg hn hodd hi hE hT hP ε₁ hε₁ D z₁ _ hb z₂ hq
  have hl : ∀ κ : X₁.S.Gam, GSum.lift D z₂ κ ∈ D.X.S.HH D.X.M z₂ ∧ ∃ κ', D.m • GSum.lift D z₂ κ = D.lab κ' := fun κ => by
    by_cases h : ∃ h' ∈ D.X.S.HH D.X.M z₂, D.m • h' = D.lab κ
    · rw [GSum.lift, dite_eq_left h]
      exact ⟨h.choose_spec.1, κ, h.choose_spec.2⟩
    · rw [GSum.lift, dite_eq_right h]
      exact ⟨zero_mem _, 0, by rw [smul_zero, map_zero]⟩
  choose U hU hσU using fun κ : X₁.S.HH X₁.M z₁ =>
    exists_root_conj hx hadd D.sq (D.X.S.HH D.X.M z₂) _ hb.1 hb'.1 (hl κ).1 (hl κ).2.choose_spec
  refine ⟨U, hU, fun σ => ?_⟩
  have hφ : (σ : D.X.Ω₁ →+* D.X.Ω₁).comp (algebraMap X₁.Ω₁ D.X.Ω₁) = algebraMap X₁.Ω₁ D.X.Ω₁ :=
    RingHom.ext fun y => σ.commutes y
  obtain ⟨a, s, t, hs, ha, hlab, ht₁, ht, lt, hpt'⟩ := exists_conj_over hx (σ : D.X.Ω₁ →+* D.X.Ω₁) σ.surjective hφ
  refine ⟨a, ⟨P₀, a₂, t, ε₀, h₂, ht, l₂, lt, fun E => ⟨(hε E).2, ?_⟩, hpt'⟩, hlab, fun hH b κ => ?_⟩
  · have ht₂ := ht.1.w
    refine h₁.1.hom_ext ?_ ?_
    · rw [Category.assoc, Category.assoc, ht₁, (hε E).1, ← Category.assoc, ht₁]
    · rw [Category.assoc, Category.assoc, ht₂, Over.w (ε₀ E), ← Category.assoc, Over.w (ε₀ E), ht₂]
  · have key := hσU κ _ hφ s hs a ha hlab hH (D.m • b)
    rw [map_nsmul] at key
    exact key

end GlobalTheory.Poinc.GalPart
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisPermutesWeightPartsUpToRootsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_permutes_weightParts_up_to_roots : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsDiagEnd F W X₁.ρ.P X₁.u ε₁ → ∀ (D : Deep X₁ ε₁) (z₁ : X₁.M.Z) (z₂ : D.X.M.Z), D.q z₂ = z₁ → ∃ U : X₁.S.HH X₁.M z₁ → D.X.Ω₁, (∀ κ, ∃ k : ℕ, 0 < k ∧ U κ ^ k = 1) ∧ ∀ σ : D.X.Ω₁ ≃ₐ[X₁.Ω₁] D.X.Ω₁, ∃ a : D.X.S.Gam ≃+ D.X.S.Gam, D.GalLab σ a ∧ (∀ x, a (D.lab x) = D.lab x) ∧ ((∀ x, a x ∈ D.X.S.HH D.X.M z₂ ↔ x ∈ D.X.S.HH D.X.M z₂) → ∀ b κ, σ (U κ * GSum.part D z₁ z₂ b κ) = U κ * GSum.part D z₁ z₂ (a b) κ) := by
  first | exact @GlobalTheory.Poinc.GalPart.exists_root_galois | exact GlobalTheory.Poinc.GalPart.exists_root_galois | (intros; apply GlobalTheory.Poinc.GalPart.exists_root_galois <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightPartDependsOnLabelMod
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightPartDependsOnLabelMod
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.GSum


set_option maxHeartbeats 1000000 in
theorem part_eq_of_congMod : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsDiagEnd F W X₁.ρ.P X₁.u ε₁ → ∀ (D : Deep X₁ ε₁) (z₁ : X₁.M.Z) (z₂ : D.X.M.Z), D.q z₂ = z₁ → ∀ (p : ℕ) [Fact p.Prime] (c : CTrait X₁ p z₁) (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = c.y), y (cPt p) = z₂ → ∀ yy : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) (Fin 8 → c.T.D.toPre.X), IsLab D.X D.ε (D.lift c y h) yy → ∀ a a' ν ν' κ, yy a = QuotientAddGroup.mk ν → yy a' = QuotientAddGroup.mk ν' → CongMod D.m ν ν' → GSum.part D z₁ z₂ a κ = GSum.part D z₁ z₂ a' κ := by
  intro g n F W Z i X₁ hg hn hodd hi hE hT hP ε₁ hd D z₁ z₂ hq p _ c y h hy yy hl a a' ν ν' κ ha ha' hc
  subst hy
  obtain ⟨hon, hker⟩ := GlobalTheory.Poinc.isLab_onto_and_ker g n F W Z i D.X hg hn hodd hi hE hT D.proj D.ε D.diag p
    (y (cPt p)) (D.lift c y h) yy hl
  obtain ⟨w, hw⟩ := hc
  obtain ⟨b, hb⟩ := hon (QuotientAddGroup.mk w)
  have hk : a - a' - D.m • b ∈ D.X.S.HH D.X.M (y (cPt p)) := by
    rw [← hker, AddMonoidHom.mem_ker]
    have e1 : yy (a - a' - D.m • b) = yy a - yy a' - D.m • yy b := by
      rw [map_sub, map_sub, map_nsmul]
    rw [e1, ha, ha', hb, hw]
    show ((QuotientAddGroup.mk (ν' + D.m • w) - QuotientAddGroup.mk ν' - D.m • QuotientAddGroup.mk w :
      ModN (D.X.S.r * D.X.S.N) (Fin 8 → c.T.D.toPre.X))) = 0
    rw [← QuotientAddGroup.mk_nsmul, ← QuotientAddGroup.mk_sub, ← QuotientAddGroup.mk_sub]
    simp
  have hw' : wtChar D (D.X.S.TT D.X.M (y (cPt p))) a = wtChar D (D.X.S.TT D.X.M (y (cPt p))) a' := by
    ext t
    have ht : eStdBilin D.X.S.g _ (t : D.X.S.Gam) (a - a' - D.m • b) = 0 := t.2 _ hk
    have hsplit : D.m • a = D.m • a' + (D.m * D.m) • b + D.m • (a - a' - D.m • b) := by
      rw [mul_nsmul', ← smul_add, ← smul_add]
      congr 1
      abel
    have key : eStd D.X.S.g _ (t : D.X.S.Gam) (D.m • a) =
        eStd D.X.S.g _ (t : D.X.S.Gam) (D.m • a') + (D.m * D.m) • eStd D.X.S.g _ (t : D.X.S.Gam) b := by
      rw [hsplit]
      simp only [← eStdBilin_apply, map_add (f := _), map_nsmul, ht, smul_zero, add_zero]
    have hN : ZMod.castHom (dvd_mul_left D.X.S.N D.X.S.r) (ZMod D.X.S.N)
        ((D.m * D.m) • eStd D.X.S.g _ (t : D.X.S.Gam) b) = 0 := by
      rw [map_nsmul, ← sq, ← D.sq, nsmul_eq_mul, ZMod.natCast_self, zero_mul]
    show ZMod.castHom (dvd_mul_left D.X.S.N D.X.S.r) (ZMod D.X.S.N) (eStd D.X.S.g _ (t : D.X.S.Gam) (D.m • a)) =
      ZMod.castHom (dvd_mul_left D.X.S.N D.X.S.r) (ZMod D.X.S.N) (eStd D.X.S.g _ (t : D.X.S.Gam) (D.m • a'))
    rw [key, map_add (f := _), hN, add_zero]
  simp only [part, hw']

end GlobalTheory.Poinc.GSum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightPartDependsOnLabelModStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weightPart_depends_on_label_mod : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsDiagEnd F W X₁.ρ.P X₁.u ε₁ → ∀ (D : Deep X₁ ε₁) (z₁ : X₁.M.Z) (z₂ : D.X.M.Z), D.q z₂ = z₁ → ∀ (p : ℕ) [Fact p.Prime] (c : CTrait X₁ p z₁) (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = c.y), y (cPt p) = z₂ → ∀ yy : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) (Fin 8 → c.T.D.toPre.X), IsLab D.X D.ε (D.lift c y h) yy → ∀ a a' ν ν' κ, yy a = QuotientAddGroup.mk ν → yy a' = QuotientAddGroup.mk ν' → CongMod D.m ν ν' → GSum.part D z₁ z₂ a κ = GSum.part D z₁ z₂ a' κ := by
  first | exact @GlobalTheory.Poinc.GSum.part_eq_of_congMod | exact GlobalTheory.Poinc.GSum.part_eq_of_congMod | (intros; apply GlobalTheory.Poinc.GSum.part_eq_of_congMod <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaWeightPartValueDependsTraitLabelsClass
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.GSum

theorem eq_of_gPt_comp_eq {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) {p : ℕ} [Fact p.Prime]
    {y y' : Sp (OO p) ⟶ M.Z} (h : gPt p ≫ y = gPt p ≫ y') : y = y' := by
  haveI := M.sep
  haveI : IsDominant (gPt p) :=
    ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical (OO p).subtype).2 fun x hx => by
      rw [show x = 0 from Subtype.ext hx]
      exact Submodule.zero_mem _⟩
  exact ext_of_isDominant_of_isSeparated M.s
    (ext_of_isDominant (gPt p) (by rw [← Category.assoc, h, Category.assoc])) (gPt p) h

theorem val_part_eq : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsDiagEnd F W X₁.ρ.P X₁.u ε₁ → ∀ (D : Deep X₁ ε₁) (z₁ : X₁.M.Z) (z₂ : D.X.M.Z), D.q z₂ = z₁ → ∃ U : X₁.S.HH X₁.M z₁ → D.X.Ω₁, (∀ κ, ∃ k : ℕ, 0 < k ∧ U κ ^ k = 1) ∧ ∀ (p : ℕ) [Fact p.Prime] (c : CTrait X₁ p z₁) (yy₁ : X₁.S.Gam →+ ModN (X₁.S.r * X₁.S.N) (Fin 8 → c.T.D.toPre.X)), IsLab X₁ ε₁ c yy₁ → ∀ (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = c.y), y (cPt p) = z₂ → ∀ yy : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) (Fin 8 → c.T.D.toPre.X), IsLab D.X D.ε (D.lift c y h) yy → D.Compat yy₁ yy → ∀ (y' : Sp (OO p) ⟶ D.X.M.Z) (h' : y' ≫ D.q = c.y), y' (cPt p) = z₂ → ∀ yy' : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) (Fin 8 → c.T.D.toPre.X), IsLab D.X D.ε (D.lift c y' h') yy' → D.Compat yy₁ yy' → ∀ a a' ν ν' κ, yy a = QuotientAddGroup.mk ν → yy' a' = QuotientAddGroup.mk ν' → CongMod D.m ν ν' → D.X.M.val (gPt p ≫ y) (U κ * GSum.part D z₁ z₂ a κ) = D.X.M.val (gPt p ≫ y') (U κ * GSum.part D z₁ z₂ a' κ) := by
  intro g n F W Z i X₁ hg hn ho hi hE hT hP ε₁ hε D z₁ z₂ hz
  obtain ⟨U, hU, hgal⟩ := GlobalTheory.T.galois_permutes_weightParts_up_to_roots g n F W Z i X₁ hg hn ho hi hE hT hP ε₁ hε D z₁ z₂ hz
  refine ⟨U, hU, ?_⟩
  intro p _ c yy₁ hl₁ y h hy yy hl hc y' h' hy' yy' hl' hc' a a' ν ν' κ ha ha' hcong
  haveI := D.fd
  haveI := D.gal
  obtain ⟨σ, s, hs, hys, hval⟩ := GlobalTheory.T.exists_galois_aut_conjugate_field_points_cover X₁.o₁ X₁.Ω₁ D.X.o₁ D.X.Ω₁ X₁.M D.X.M D.q (@GlobalTheory.IsNormalScheme.pred _ X₁.normal)
    (@GlobalTheory.IsNormalScheme.pred _ D.X.normal) D.fin D.gen
    (PadicAlgCl p) (gPt p ≫ y) (gPt p ≫ y') (by rw [Category.assoc, Category.assoc, h, h'])
  obtain rfl : y ≫ s = y' := eq_of_gPt_comp_eq D.X.M (by rw [← Category.assoc, hys])
  obtain ⟨b, hb, hfix, hperm⟩ := hgal σ
  have hlb := GlobalTheory.T.thetaSetup_labelling_transport_galoisConjugate g n F W Z i X₁ hg hn ho hi hE hT hP ε₁ hε D σ s hs b hb p z₁ c y h h' yy hl
  have hcb : D.Compat yy₁ (yy.comp b.toAddMonoidHom) := fun x μ hx => by
    have := hc x μ hx
    rw [← hfix x] at this
    exact this
  have hyy : ∀ x, yy' x = yy (b x) := fun x =>
    DFunLike.congr_fun (GalLab.rigid D c yy₁ hl₁ (y ≫ s) h' _ yy' hlb hcb hl' hc') x
  have hk := (isLab_onto_and_ker g n F W Z i D.X hg hn ho hi hE hT D.proj D.ε D.diag p _ _ _ hl).2
  have hk' := (isLab_onto_and_ker g n F W Z i D.X hg hn ho hi hE hT D.proj D.ε D.diag p _ _ _ hl').2
  replace hk := hk.trans (congrArg (D.X.S.HH D.X.M) hy)
  replace hk' := hk'.trans (congrArg (D.X.S.HH D.X.M) hy')
  have hHH : ∀ x, b x ∈ D.X.S.HH D.X.M z₂ ↔ x ∈ D.X.S.HH D.X.M z₂ := fun x => by
    have h1 : b x ∈ yy.ker ↔ x ∈ yy'.ker := by
      rw [AddMonoidHom.mem_ker, AddMonoidHom.mem_ker, hyy]
    rwa [hk, hk'] at h1
  rw [hval, hperm hHH,
    GlobalTheory.T.weightPart_depends_on_label_mod g n F W Z i X₁ hg hn ho hi hE hT hP ε₁ hε D z₁ z₂ hz p c y h hy yy hl a (b a') ν ν' κ ha
      ((hyy a').symm.trans ha') hcong]

end GlobalTheory.Poinc.GSum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaWeightPartValueDependsTraitLabelsClassStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaWeightPart_value_depends_trait_labels_class : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsDiagEnd F W X₁.ρ.P X₁.u ε₁ → ∀ (D : Deep X₁ ε₁) (z₁ : X₁.M.Z) (z₂ : D.X.M.Z), D.q z₂ = z₁ → ∃ U : X₁.S.HH X₁.M z₁ → D.X.Ω₁, (∀ κ, ∃ k : ℕ, 0 < k ∧ U κ ^ k = 1) ∧ ∀ (p : ℕ) [Fact p.Prime] (c : CTrait X₁ p z₁) (yy₁ : X₁.S.Gam →+ ModN (X₁.S.r * X₁.S.N) (Fin 8 → c.T.D.toPre.X)), IsLab X₁ ε₁ c yy₁ → ∀ (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = c.y), y (cPt p) = z₂ → ∀ yy : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) (Fin 8 → c.T.D.toPre.X), IsLab D.X D.ε (D.lift c y h) yy → D.Compat yy₁ yy → ∀ (y' : Sp (OO p) ⟶ D.X.M.Z) (h' : y' ≫ D.q = c.y), y' (cPt p) = z₂ → ∀ yy' : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) (Fin 8 → c.T.D.toPre.X), IsLab D.X D.ε (D.lift c y' h') yy' → D.Compat yy₁ yy' → ∀ a a' ν ν' κ, yy a = QuotientAddGroup.mk ν → yy' a' = QuotientAddGroup.mk ν' → CongMod D.m ν ν' → D.X.M.val (gPt p ≫ y) (U κ * GSum.part D z₁ z₂ a κ) = D.X.M.val (gPt p ≫ y') (U κ * GSum.part D z₁ z₂ a' κ) := by
  first | exact @GlobalTheory.Poinc.GSum.val_part_eq | exact GlobalTheory.Poinc.GSum.val_part_eq | (intros; apply GlobalTheory.Poinc.GSum.val_part_eq <;> assumption)
end
