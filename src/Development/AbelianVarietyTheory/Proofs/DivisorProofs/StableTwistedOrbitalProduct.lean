module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralProductGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulHomInjective
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.ChainOfKernelsUnique
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvUAbsU
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsConstAlongSingleton
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StableTwistedOrbitalProduct
noncomputable section

open NumberField IsDedekindDomain Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC
open scoped Classical TensorProduct
open GlobalTheory.BCT

namespace GlobalTheory.BCT.StTwTens

theorem finsum_prod_mul' {α β : Type} (u : α → ℂ) (v : β → ℂ) :
    ∑ᶠ z : α × β, u z.1 * v z.2 = (∑ᶠ a, u a) * ∑ᶠ b, v b := by
  have hsupp : Function.support (fun z : α × β => u z.1 * v z.2) =
      Function.support u ×ˢ Function.support v := by
    ext z
    simp only [Function.mem_support, Set.mem_prod, ne_eq, mul_eq_zero, not_or]
  by_cases hu : (Function.support u).Finite
  · by_cases hv : (Function.support v).Finite
    · exact GlobalTheory.BCT.OrbProd.finsum_prod_mul_of_finite u v hu hv
    · have hv' : (Function.support v).Infinite := hv
      rw [finsum_of_infinite_support hv', mul_zero]
      rcases (Function.support u).eq_empty_or_nonempty with h | h
      · have hu0 : u = 0 := Function.support_eq_empty_iff.mp h
        simp [hu0]
      · apply finsum_of_infinite_support
        rw [hsupp]
        exact Set.Infinite.prod_right hv' h
  · have hu' : (Function.support u).Infinite := hu
    rw [finsum_of_infinite_support hu', zero_mul]
    rcases (Function.support v).eq_empty_or_nonempty with h | h
    · have hv0 : v = 0 := Function.support_eq_empty_iff.mp h
      simp [hv0]
    · apply finsum_of_infinite_support
      rw [hsupp]
      exact Set.Infinite.prod_left hu' h

section Gen

variable {G G' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G'] [T2Space G']

theorem twOrb_prod' (θ : G →* G) (θ' : G' →* G') (K : Subgroup G) (K' : Subgroup G') (δ : G) (δ' : G')
    (f : G → ℂ) (f' : G' → ℂ)
    (hf : ∀ x : G, (rStab fun k : K => f ((x * k)⁻¹ * δ * θ (x * k))).index ≠ 0)
    (hf' : ∀ x : G', (rStab fun k : K' => f' ((x * k)⁻¹ * δ' * θ' (x * k))).index ≠ 0) :
    twOrb (θ.prodMap θ') (K.prod K') (δ, δ') (fun y => f y.1 * f' y.2) = twOrb θ K δ f * twOrb θ' K' δ' f' := by
  rw [GlobalTheory.BCT.OrbProd.twOrb_eq, GlobalTheory.BCT.OrbProd.twOrb_eq θ, GlobalTheory.BCT.OrbProd.twOrb_eq θ',
    GlobalTheory.BCT.OrbProd.twCent_prod θ θ' δ δ', ← finsum_prod_mul',
    ← finsum_comp_equiv (Equiv.ofBijective _ (GlobalTheory.BCT.OrbProd.dcPair_bij (twCent θ δ) K (twCent θ' δ') K'))]
  refine finsum_congr fun z => ?_
  obtain ⟨t, ht, k, hk, hq⟩ := DoubleCoset.mk_out_eq_mul ((twCent θ δ).prod (twCent θ' δ')) (K.prod K')
    (Quotient.out z.1, Quotient.out z.2)
  rw [Subgroup.mem_prod] at ht hk
  have hdc : GlobalTheory.BCT.OrbProd.dcPair (twCent θ δ) K (twCent θ' δ') K' z =
      DoubleCoset.mk ((twCent θ δ).prod (twCent θ' δ')) (K.prod K') (Quotient.out z.1, Quotient.out z.2) := rfl
  have hpt : t * (Quotient.out z.1, Quotient.out z.2) * k =
      (t.1 * Quotient.out z.1 * k.1, t.2 * Quotient.out z.2 * k.2) := rfl
  rw [Equiv.ofBijective_apply, hdc, hq, hpt,
    GlobalTheory.BCT.OrbProd.orbTerm_prod θ θ' K K' δ δ' f f' _ _ (hf _) (hf' _),
    GlobalTheory.BCT.OrbProd.orbTerm_inv θ K δ f hf ht.1 hk.1, GlobalTheory.BCT.OrbProd.orbTerm_inv θ' K' δ' f' hf' ht.2 hk.2]

end Gen

section Cl

variable {G G' : Type} [Group G] [Group G']

theorem twRel_equiv (θ : G →* G) : Equivalence (fun x y : G => ∃ g, y = g⁻¹ * x * θ g) := by
  refine ⟨fun x => ⟨1, by simp⟩, ?_, ?_⟩
  · rintro x y ⟨g, rfl⟩
    exact ⟨g⁻¹, by simp [mul_assoc]⟩
  · rintro x y z ⟨g, rfl⟩ ⟨g', rfl⟩
    exact ⟨g * g', by simp [mul_assoc]⟩

def mkC (θ : G →* G) (x : G) : TwCl θ := Quot.mk _ x

theorem rel_of_mkC_eq (θ : G →* G) {x y : G} (h : mkC θ x = mkC θ y) : ∃ g, y = g⁻¹ * x * θ g :=
  (twRel_equiv θ).eqvGen_iff.mp (Quot.eqvGen_exact h)

theorem mkC_eq (θ : G →* G) {x y : G} (g : G) (h : y = g⁻¹ * x * θ g) : mkC θ x = mkC θ y :=
  Quot.sound (r := fun a b : G => ∃ g, b = g⁻¹ * a * θ g) ⟨g, h⟩

theorem mkC_rep (θ : G →* G) (c : TwCl θ) : mkC θ c.rep = c := by
  exact Quot.out_eq c

def clPair (θ : G →* G) (θ' : G' →* G') (c : TwCl (θ.prodMap θ')) : TwCl θ × TwCl θ' :=
  (mkC θ c.rep.1, mkC θ' c.rep.2)

theorem clPair_bij (θ : G →* G) (θ' : G' →* G') : Function.Bijective (clPair θ θ') := by
  constructor
  · intro c d h
    have h1 : mkC θ c.rep.1 = mkC θ d.rep.1 := congrArg Prod.fst h
    have h2 : mkC θ' c.rep.2 = mkC θ' d.rep.2 := congrArg Prod.snd h
    obtain ⟨g, hg⟩ := rel_of_mkC_eq θ h1
    obtain ⟨g', hg'⟩ := rel_of_mkC_eq θ' h2
    calc c = mkC (θ.prodMap θ') c.rep := (mkC_rep _ c).symm
      _ = mkC (θ.prodMap θ') d.rep :=
        mkC_eq _ (g, g') (Prod.ext (by simpa using hg) (by simpa using hg'))
      _ = d := mkC_rep _ d
  · rintro ⟨a, b⟩
    refine ⟨mkC (θ.prodMap θ') (a.rep, b.rep), ?_⟩
    obtain ⟨g, hg⟩ := rel_of_mkC_eq (θ.prodMap θ')
      (mkC_rep (θ.prodMap θ') (mkC (θ.prodMap θ') (a.rep, b.rep)))
    have h1 : a.rep = g.1⁻¹ * (mkC (θ.prodMap θ') (a.rep, b.rep)).rep.1 * θ g.1 := by
      simpa using congrArg Prod.fst hg
    have h2 : b.rep = g.2⁻¹ * (mkC (θ.prodMap θ') (a.rep, b.rep)).rep.2 * θ' g.2 := by
      simpa using congrArg Prod.snd hg
    refine Prod.ext ?_ ?_
    · exact (mkC_eq θ g.1 h1).trans (mkC_rep θ a)
    · exact (mkC_eq θ' g.2 h2).trans (mkC_rep θ' b)

end Cl

theorem charpoly_conj {R m : Type} [CommRing R] [Fintype m] [DecidableEq m] (g X : GL m R) :
    (g⁻¹ * X * g : GL m R).val.charpoly = X.val.charpoly := by
  rw [Units.val_mul, Units.val_mul, Matrix.coe_units_inv]
  exact Matrix.charpoly_units_conj' g X.val

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem rStab_index_ne_zero {n : ℕ} {w : Pl E} {K' : Subgroup (GLw n w)} {φ : GLw n w → ℂ}
    (hK : IsLevel (thL n w) (GlobalTheory.LFun.KGL w (n := n)) K') (hφ : IsHecke K' φ) (δ x : GLw n w) :
    (rStab fun k : GlobalTheory.LFun.KGL w (n := n) => φ ((x * k)⁻¹ * δ * thL n w (x * k))).index ≠ 0 := by
  obtain ⟨hKo, -, hKθ⟩ := hK
  obtain ⟨-, hinv⟩ := hφ
  have hcpt : CompactSpace (GlobalTheory.LFun.KGL w (n := n)) :=
    isCompact_iff_compactSpace.mp (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w n).2
  have hopen : IsOpen ((K'.subgroupOf (GlobalTheory.LFun.KGL w (n := n)) : Subgroup (GlobalTheory.LFun.KGL w (n := n))) :
      Set (GlobalTheory.LFun.KGL w (n := n))) := Subgroup.subgroupOf_isOpen (GlobalTheory.LFun.KGL w (n := n)) K' hKo
  have hfin : Finite (GlobalTheory.LFun.KGL w (n := n) ⧸ K'.subgroupOf (GlobalTheory.LFun.KGL w (n := n))) :=
    Subgroup.quotient_finite_of_isOpen _ hopen
  have hH : (K'.subgroupOf (GlobalTheory.LFun.KGL w (n := n))).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hle : K'.subgroupOf (GlobalTheory.LFun.KGL w (n := n)) ≤
      rStab fun k : GlobalTheory.LFun.KGL w (n := n) => φ ((x * k)⁻¹ * δ * thL n w (x * k)) := by
    intro k hk
    rw [Subgroup.mem_subgroupOf] at hk
    rw [GlobalTheory.TwOrbConj.mem_rStab]
    intro j
    have hk1 : (k : GLw n w)⁻¹ ∈ K' := K'.inv_mem hk
    have hk2 : thL n w (k : GLw n w) ∈ K' := hKθ _ hk
    calc φ ((x * ↑(j * k))⁻¹ * δ * thL n w (x * ↑(j * k)))
        = φ ((↑k)⁻¹ * ((x * ↑j)⁻¹ * δ * thL n w (x * ↑j)) * thL n w ↑k) := by
          congr 1
          simp only [Subgroup.coe_mul, map_mul, mul_inv_rev, mul_assoc]
      _ = φ ((↑k)⁻¹ * ((x * ↑j)⁻¹ * δ * thL n w (x * ↑j))) := (hinv _ hk2 _).2
      _ = φ ((x * ↑j)⁻¹ * δ * thL n w (x * ↑j)) := (hinv _ hk1 _).1
  intro h0
  apply hH
  have hd := Subgroup.index_dvd_of_le hle
  rw [h0] at hd
  exact Nat.eq_zero_of_zero_dvd hd

theorem nrmL_charpoly_twConj (n : ℕ) (w : Pl E) (g y : GLw n w) :
    (nrmL n w (g⁻¹ * y * thL n w g)).val.charpoly = (nrmL n w y).val.charpoly := by
  have hinv := GlobalTheory.BCT.TwistInvol.thL_involutive E n w g
  unfold nrmL
  unfold thL at hinv ⊢
  split_ifs at hinv ⊢ with hs
  · simp only [MonoidHom.id_apply]
    exact charpoly_conj g y
  · have key : g⁻¹ * y * thetaGL n (cj w) g * thetaGL n (cj w) (g⁻¹ * y * thetaGL n (cj w) g) =
        g⁻¹ * (y * thetaGL n (cj w) y) * g := by
      simp only [map_mul, map_inv, hinv]
      group
    rw [key]
    exact charpoly_conj g _

private theorem charpoly_nrmL_rep_eq_and_twOrb_rep_eq {n : ℕ} {w : Pl E} {K' : Subgroup (GLw n w)} {φ : GLw n w → ℂ}
    (hK : IsLevel (thL n w) (GlobalTheory.LFun.KGL w (n := n)) K') (hφ : IsHecke K' φ) (x : GLw n w) :
    (nrmL n w (mkC (thL n w) x).rep).val.charpoly = (nrmL n w x).val.charpoly ∧
      twOrb (thL n w) (GlobalTheory.LFun.KGL w (n := n)) (mkC (thL n w) x).rep φ =
        twOrb (thL n w) (GlobalTheory.LFun.KGL w (n := n)) x φ := by
  obtain ⟨g, hg⟩ := rel_of_mkC_eq (thL n w) (mkC_rep (thL n w) (mkC (thL n w) x))
  constructor
  · have h := nrmL_charpoly_twConj n w g (mkC (thL n w) x).rep
    rw [← hg] at h
    exact h.symm
  · have h := GlobalTheory.TwOrbConj.twOrb_twConj (GLw n w) (thL n w) (GlobalTheory.LFun.KGL w (n := n)) (mkC (thL n w) x).rep g φ
      (fun y => rStab_index_ne_zero hK hφ _ y)
    rw [← hg] at h
    exact h.symm

theorem stTw2_tens : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (w : Pl E)
    (Q₁ Q₂ : (w.adicCompletion E)[X])
    (K₁ : Subgroup (GLw a w)) (K₂ : Subgroup (GLw b w)) (φ₁ : GLw a w → ℂ) (φ₂ : GLw b w → ℂ),
    IsLevel (thL a w) (GlobalTheory.LFun.KGL w (n := a)) K₁ → IsLevel (thL b w) (GlobalTheory.LFun.KGL w (n := b)) K₂ → IsHecke K₁ φ₁ →
    IsHecke K₂ φ₂ → stTw2 a b w Q₁ Q₂ (tens φ₁ φ₂) = stTw a w Q₁ φ₁ * stTw b w Q₂ φ₂ := by
  intro E _ _ _ a b w Q₁ Q₂ K₁ K₂ φ₁ φ₂ h₁ h₂ h₃ h₄
  unfold stTw2 stTw tens clSum
  rw [← finsum_prod_mul', ← finsum_comp_equiv (Equiv.ofBijective _ (clPair_bij (thL a w) (thL b w)))]
  refine finsum_congr fun c => ?_
  have hcl : clPair (thL a w) (thL b w) c = (mkC (thL a w) c.rep.1, mkC (thL b w) c.rep.2) := rfl
  obtain ⟨hc₁, ho₁⟩ := charpoly_nrmL_rep_eq_and_twOrb_rep_eq h₁ h₃ c.rep.1
  obtain ⟨hc₂, ho₂⟩ := charpoly_nrmL_rep_eq_and_twOrb_rep_eq h₂ h₄ c.rep.2
  have ho : twOrb ((thL a w).prodMap (thL b w)) ((GlobalTheory.LFun.KGL w (n := a)).prod (GlobalTheory.LFun.KGL w (n := b))) c.rep
      (fun y => φ₁ y.1 * φ₂ y.2) =
      twOrb (thL a w) (GlobalTheory.LFun.KGL w (n := a)) c.rep.1 φ₁ * twOrb (thL b w) (GlobalTheory.LFun.KGL w (n := b)) c.rep.2 φ₂ :=
    twOrb_prod' (thL a w) (thL b w) _ _ c.rep.1 c.rep.2 φ₁ φ₂ (fun x => rStab_index_ne_zero h₁ h₃ _ x)
      (fun x => rStab_index_ne_zero h₂ h₄ _ x)
  rw [Equiv.ofBijective_apply, hcl]
  simp only [Set.mem_ofPred_eq, Pi.one_apply, one_mul, hc₁, hc₂, ho₁, ho₂, ho]
  by_cases hA : (nrmL a w c.rep.1).val.charpoly = Q₁ <;>
    by_cases hB : (nrmL b w c.rep.2).val.charpoly = Q₂ <;> simp [hA, hB]

end GlobalTheory.BCT.StTwTens
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramRightMulActionLaws
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.FinEtRank.isIsogDeg_of_card :
  ∀ {S : Scheme.{0}} (A K : Over S) (i : K ⟶ A), Mono i → IsFinite K.hom → Etale K.hom → ∀ (d : ℕ), 1 ≤ d → (∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ S), Nat.card {y : Over.mk t ⟶ A // GlobalTheory.IwLevel.InSub i y} = d) → GlobalTheory.IwLevel.IsIsogDeg (toUnit K) d := by
  intro S A K i hi hfin het d hd hcard
  have h : (toUnit K).left = K.hom := by simpa using Over.w (toUnit K)
  have hrank : ∀ s : S, K.hom.finrank s = d := by
    intro s
    obtain ⟨k, _, _, t, ht⟩ := GlobalTheory.FinEt.exists_algClosed_point S s
    obtain ⟨z, rfl⟩ : s ∈ Set.range t := by rw [ht]; rfl
    obtain ⟨-, hc⟩ := GlobalTheory.FinEt.card_points_eq_finrank K.hom t z
    rw [← hc, ← hcard k t]
    refine Nat.card_congr (Equiv.ofBijective (fun x => ⟨Over.homMk x.1 x.2 ≫ i, ⟨Over.homMk x.1 x.2, rfl⟩⟩) ⟨?_, ?_⟩)
    · rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
      have := (cancel_mono i).1 (congrArg Subtype.val hab)
      exact Subtype.ext (congrArg CommaMorphism.left this)
    · rintro ⟨y, y', hy'⟩
      refine ⟨⟨y'.left, Over.w y'⟩, Subtype.ext ?_⟩
      simp only
      rw [← hy']
      congr 1
  have hflat : Flat K.hom := inferInstance
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [h]; exact hfin
  · rw [h]; exact hflat
  · rw [h]; exact (Scheme.Hom.one_le_finrank_iff_surjective K.hom).1 fun s => (hrank s).symm ▸ hd
  · intro y; rw [h]; exact hrank y
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowEqOneOfPrincipalUnitIdeleNormOne
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowEqOneOfPrincipalUnitIdeleNormOne
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.UnitTorsion

theorem principal_unit_idele_torsion : ∀ (E : Type) [Field E] [NumberField E] (t : Eˣ), Neutral.B1.diagUnits E t ∈ GlobalTheory.Mem.Chr.unitIdl E →
    (∀ φ : E →+* ℂ, ‖φ (t : E)‖ = 1) → ∃ n : ℕ, 0 < n ∧ t ^ n = 1 := by
  intro E _ _ t ht hnorm
  have hv : ∀ v : HeightOneSpectrum (𝓞 E), v.valuation E (t : E) ≤ 1 := by
    intro v
    have h1 := ht v
    have h2 : ((Neutral.B1.diagUnits E t : AdeleRing (𝓞 E) E)).2 v = ((t : E) : v.adicCompletion E) := rfl
    rw [h2, HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at h1
    exact h1.le
  obtain ⟨y, hy⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one E (t : E) hv
  have hint : IsIntegral ℤ (t : E) := by
    rw [← hy]; exact y.isIntegral_coe
  obtain ⟨n, hn, hpow⟩ := NumberField.Embeddings.pow_eq_one_of_norm_eq_one E ℂ hint hnorm
  exact ⟨n, hn, Units.ext (by simpa using hpow)⟩

end GlobalTheory.UnitTorsion
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowEqOneOfPrincipalUnitIdeleNormOneStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pow_eq_one_of_principal_unitIdele_norm_one : ∀ (E : Type) [Field E] [NumberField E] (t : Eˣ), Neutral.B1.diagUnits E t ∈ GlobalTheory.Mem.Chr.unitIdl E →
    (∀ φ : E →+* ℂ, ‖φ (t : E)‖ = 1) → ∃ n : ℕ, 0 < n ∧ t ^ n = 1 := by
  first | exact @GlobalTheory.UnitTorsion.principal_unit_idele_torsion | exact GlobalTheory.UnitTorsion.principal_unit_idele_torsion | (intros; apply GlobalTheory.UnitTorsion.principal_unit_idele_torsion <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CutPMulCutP
noncomputable section

open NumberField Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet

namespace GlobalTheory.CentreFin

variable {n r : ℕ}

variable {J : Matrix (Fin n) (Fin n) ℂ} {X Y : Matrix (Fin n) (Fin r) ℂ}

theorem dual_swap (hJ : Jᴴ = J) (hxy : Xᴴ * J * Y = 1) : Yᴴ * J * X = 1 := by
  have := congrArg conjTranspose hxy
  rwa [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hJ, conjTranspose_one, ← Matrix.mul_assoc] at this

section Global

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem map_cT_emb (h : IsCMExt F E σ) (τ : E →+* ℂ) {a b : ℕ} (C : Matrix (Fin a) (Fin b) E) :
    (Formalism.UG.cT (σ : E →+* E) C).map τ = (C.map τ)ᴴ :=
  Matrix.ext fun i j => h.2.2.2 τ (C j i)

theorem frame_emb (h : IsCMExt F E σ) {J : Matrix (Fin n) (Fin n) E} {X Y : Matrix (Fin n) (Fin r) E}
    (hW : IsWittFrame σ J X Y) (τ : E →+* ℂ) :
    (X.map τ)ᴴ * J.map τ * X.map τ = 0 ∧ (Y.map τ)ᴴ * J.map τ * Y.map τ = 0 ∧ (X.map τ)ᴴ * J.map τ * Y.map τ = 1 := by
  simp only [← map_cT_emb h, ← Matrix.map_mul]
  rw [hW.xx, hW.yy, hW.xy]
  exact ⟨Matrix.map_zero _ (map_zero _), Matrix.map_zero _ (map_zero _), Matrix.map_one _ (map_zero _) (map_one _)⟩

end Global

end GlobalTheory.CentreFin

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KawamataLogTerminalLogCanonicalGenerisation
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KawamataLogTerminalLogCanonicalGenerisation
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory.Discrepancy

theorem kltAt_lcAt_of_specializes (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X]
    (p : X ⟶ Sp ℂ) (n : ℕ) (Γ : X → ℚ) (x z : X) (hzx : z ⤳ x) :
    (KltAt p n Γ x → KltAt p n Γ z) ∧ (LcAt p n Γ x → LcAt p n Γ z) :=
  ⟨fun ⟨η, m, g, h₁, h₂, h₃, h₄⟩ =>
      ⟨η, m, g, h₁, h₂, fun w hw E hE => h₃ w (hw.trans hzx) E hE,
        fun E hE => h₄ E (hE.of_specializes hzx)⟩,
    fun ⟨η, m, g, h₁, h₂, h₃, h₄⟩ =>
      ⟨η, m, g, h₁, h₂, fun w hw E hE => h₃ w (hw.trans hzx) E hE,
        fun E hE => h₄ E (hE.of_specializes hzx)⟩⟩

theorem kltAt_lcAt_generisation :
    ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ) (n : ℕ),
      ∀ (Γ : X → ℚ) (x z : X), z ⤳ x →
        (KltAt p n Γ x → KltAt p n Γ z) ∧ (LcAt p n Γ x → LcAt p n Γ z) :=
  fun X _ _ p n Γ x z h => kltAt_lcAt_of_specializes X p n Γ x z h

end GlobalTheory.Discrepancy
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KawamataLogTerminalLogCanonicalGenerisationStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kawamataLogTerminal_logCanonical_generisation : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ) (n : ℕ), ∀ (Γ : X → ℚ) (x z : X), z ⤳ x → (KltAt p n Γ x → KltAt p n Γ z) ∧ (LcAt p n Γ x → LcAt p n Γ z) := by
  first | exact @GlobalTheory.Discrepancy.kltAt_lcAt_generisation | exact GlobalTheory.Discrepancy.kltAt_lcAt_generisation | (intros; apply GlobalTheory.Discrepancy.kltAt_lcAt_generisation <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianLineBundlePositivityPreservedIsometric
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianLineBundlePositivityPreservedIsometric
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.HSNef

theorem isometric_keeps : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k)
    (D : ℕ), IsArithVar p D → ∀ L M : HermLB p, L.Isometric M → (L.SemiPos D → M.SemiPos D) ∧
      (L.IsNef D → M.IsNef D) ∧ (HtNef L D → HtNef M D) ∧ (∀ a, L.IsSelfInter a → M.IsSelfInter a) ∧
      (IsAmpleLB L.B → IsAmpleLB M.B) := by
  intro hA k _ X _ p D hX L M e
  have hS : L.SemiPos D → M.SemiPos D := HermLB.Isometric.semiPos L M D e
  refine ⟨hS, fun hL => ?_, fun hL => ⟨hS hL.1, fun h H x => hL.2 h (e.symm.isArithHeight hX H) x⟩,
    fun a ha => e.isSelfInter hX ha, fun hL => ?_⟩
  · obtain ⟨h, H⟩ := (hA.arExists k X p D hX).1 L
    have HM := e.isArithHeight hX H
    obtain ⟨h₁, h₂⟩ := (H.isNef_iff hX).1 hL
    exact (HM.isNef_iff hX).2 ⟨hS h₁, h₂⟩
  · obtain ⟨w, hw, -⟩ := e.symm
    exact IsAmpleLB.of_lbIso hL M.isLB ⟨w, hw⟩

end GlobalTheory.HSNef
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianLineBundlePositivityPreservedIsometricStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianLineBundle_positivity_preserved_isometric : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ L M : HermLB p, L.Isometric M → (L.SemiPos D → M.SemiPos D) ∧ (L.IsNef D → M.IsNef D) ∧ (HtNef L D → HtNef M D) ∧ (∀ a, L.IsSelfInter a → M.IsSelfInter a) ∧ (IsAmpleLB L.B → IsAmpleLB M.B) := by
  first | exact @GlobalTheory.HSNef.isometric_keeps | exact GlobalTheory.HSNef.isometric_keeps | (intros; apply GlobalTheory.HSNef.isometric_keeps <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmExtensionIdeleConjMemFiniteUnitIdeles
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmExtensionIdeleConjMemFiniteUnitIdeles
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.ConjUnit

theorem ideleConj_mem_unitIdl : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (y : Neutral.B1.Ideles E), y ∈ GlobalTheory.Mem.Chr.unitIdl E →
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleConj (maximalRealSubfield E) E y ∈ GlobalTheory.Mem.Chr.unitIdl E := by
  intro E _ _ _ y hy
  letI : Algebra E E := (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.conj (maximalRealSubfield E) E).toRingEquiv.toRingHom.toAlgebra
  have key : ∀ z : Neutral.B1.Ideles E, z ∈ GlobalTheory.Mem.Chr.unitIdl E → ∀ w : HeightOneSpectrum (𝓞 E),
      Valued.v (((GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleConj (maximalRealSubfield E) E z : AdeleRing (𝓞 E) E)).2 w) ≤ 1 := by
    intro z hz w
    have hz' : ∀ v : HeightOneSpectrum (𝓞 E), ((z : AdeleRing (𝓞 E) E)).2 v ∈ v.adicCompletionIntegers E :=
      fun v => (HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 E) (K := E) (v := v)).mpr (hz v).le
    exact GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteCompletionMap_mapsTo E E w (hz' _)
  intro w
  have h1 := key y hy w
  have h2 := key y⁻¹ (inv_mem hy) w
  have e : ((GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleConj (maximalRealSubfield E) E y : AdeleRing (𝓞 E) E)).2 w *
      ((GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleConj (maximalRealSubfield E) E y⁻¹ : AdeleRing (𝓞 E) E)).2 w = 1 := by
    rw [map_inv]
    exact congrArg (fun a : AdeleRing (𝓞 E) E => a.2 w) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleConj (maximalRealSubfield E) E y).mul_inv
  have e' := congrArg Valued.v e
  rw [map_mul, map_one] at e'
  exact eq_one_of_one_le_mul_left h1 h2 e'.ge

end GlobalTheory.ConjUnit
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmExtensionIdeleConjMemFiniteUnitIdelesStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmExtensionIdeleConj_mem_finiteUnitIdeles : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (y : Neutral.B1.Ideles E), y ∈ GlobalTheory.Mem.Chr.unitIdl E →
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleConj (maximalRealSubfield E) E y ∈ GlobalTheory.Mem.Chr.unitIdl E := by
  first | exact @GlobalTheory.ConjUnit.ideleConj_mem_unitIdl | exact GlobalTheory.ConjUnit.ideleConj_mem_unitIdl | (intros; apply GlobalTheory.ConjUnit.ideleConj_mem_unitIdl <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFixedFieldPointOfFixedBySubgroup
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFixedFieldPointOfFixedBySubgroup
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Published.AbVarRed

theorem exists_fixedField_point (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] (H : Subgroup (Ω ≃ₐ[K] Ω))
    (A : Over (Sp K)) (_ : LocallyOfFiniteType A.hom) (x : ptOver K Ω ⟶ A)
    (hx : ∀ σ ∈ H, specAut σ ≫ x = x) :
    ∃ y : Sp (IntermediateField.fixedField H) ⟶ A.left,
      spMap (algebraMap (IntermediateField.fixedField H) Ω) ≫ y = x.left := by
  obtain ⟨E, hE1, hE2, -⟩ := GlobalTheory.SS.exists_fieldOfValues A.left Ω x.left
  have hid : spMap (RingHom.id Ω) = 𝟙 (Sp Ω) := by
    rw [← Spec.map_id]
    congr 1
  have hfix : ∀ c ∈ E, ∀ σ ∈ H, σ c = c := by
    intro c hc σ hσ
    have h1 : spMap (σ : Ω →+* Ω) ≫ x.left = spMap (RingHom.id Ω) ≫ x.left := by
      rw [hid, Category.id_comp]
      exact congrArg CommaMorphism.left (hx σ hσ)
    exact (hE1 _ _).1 h1 c hc
  refine (hE2 (IntermediateField.fixedField H) (algebraMap (IntermediateField.fixedField H) Ω)).1 ?_
  intro c hc
  exact ⟨⟨c, fun σ => hfix c hc σ σ.2⟩, rfl⟩

end GlobalTheory.Published.AbVarRed
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFixedFieldPointOfFixedBySubgroupStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fixedField_point_of_fixed_by_subgroup : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] (H : Subgroup (Ω ≃ₐ[K] Ω)) (A : Over (Sp K)), LocallyOfFiniteType A.hom → ∀ x : ptOver K Ω ⟶ A, (∀ σ ∈ H, specAut σ ≫ x = x) → ∃ y : Sp (IntermediateField.fixedField H) ⟶ A.left, spMap (algebraMap (IntermediateField.fixedField H) Ω) ≫ y = x.left := by
  first | exact @GlobalTheory.Published.AbVarRed.exists_fixedField_point | exact GlobalTheory.Published.AbVarRed.exists_fixedField_point | (intros; apply GlobalTheory.Published.AbVarRed.exists_fixedField_point <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenInterEqSingletonOfNoGenerisation
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

theorem GlobalTheory.exists_open_inter_eq_singleton_of_no_generisation :
    ∀ (X : Scheme.{0}) [AlgebraicGeometry.IsNoetherian X] (T : Set X) (x : X), IsClosed T → IsClosed ({x} : Set X) → x ∈ T → (∀ z ∈ T, z ⤳ x → z = x) → ∃ U : X.Opens, x ∈ U ∧ ∀ y ∈ U, y ∈ T ↔ y = x := by
  intro X _ T x hT hx hxT hgen
  obtain ⟨S, hSf, hScl, hSirr, hTS⟩ :=
    TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible hT
  let S' : Set (Set X) := {t | t ∈ S ∧ x ∉ t}
  have hS'f : S'.Finite := hSf.subset (fun t ht => ht.1)
  have hcl : IsClosed (⋃₀ S') := by
    rw [Set.sUnion_eq_biUnion]
    exact hS'f.isClosed_biUnion (fun t ht => hScl t ht.1)
  refine ⟨⟨(⋃₀ S')ᶜ, hcl.isOpen_compl⟩, ?_, ?_⟩
  · show x ∈ (⋃₀ S')ᶜ
    rintro ⟨t, ht, hxt⟩
    exact ht.2 hxt
  · intro y hy
    have hy' : y ∈ (⋃₀ S')ᶜ := hy
    constructor
    · intro hyT
      rw [hTS] at hyT
      obtain ⟨t, htS, hyt⟩ := hyT
      by_cases hxt : x ∈ t
      · have hirr := hSirr t htS
        have hclt := hScl t htS
        obtain ⟨η, hηg⟩ := QuasiSober.sober hirr hclt
        have hgp : closure ({η} : Set X) = t := hηg.def
        have hη : η ∈ t := by
          rw [← hgp]; exact subset_closure rfl
        have hηT : η ∈ T := by
          rw [hTS]; exact ⟨t, htS, hη⟩
        have hsp : η ⤳ x := by
          rw [specializes_iff_mem_closure, hgp]; exact hxt
        have heq := hgen _ hηT hsp
        rw [heq, hx.closure_eq] at hgp
        rw [← hgp] at hyt
        exact hyt
      · exact absurd (Set.mem_sUnion.mpr ⟨t, (⟨htS, hxt⟩ : t ∈ S'), hyt⟩) hy'
    · rintro rfl; exact hxT
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionUnramifiedImpTateModuleAndInfinite
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionUnramifiedImpTateModuleAndInfinite
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Proof

theorem exists_prime_natCast_ne_zero (k : Type) [Field k] :
    ∃ (l : ℕ) (_ : Fact l.Prime), (l : k) ≠ 0 := by
  by_cases h2 : ((2 : ℕ) : k) = 0
  · refine ⟨3, ⟨Nat.prime_three⟩, fun h3 => one_ne_zero (α := k) ?_⟩
    have : ((3 : ℕ) : k) - ((2 : ℕ) : k) = 1 := by push_cast; ring
    rw [← this, h2, h3, sub_zero]
  · exact ⟨2, ⟨Nat.prime_two⟩, h2⟩

theorem torsionUnramified_imp_tate_and_infinite :
    ∀ (R K Ω : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [Field Ω]
      [Algebra K Ω] (V : ValuationSubring Ω) (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A],
      (∀ m : ℕ, (m : ResidueField R) ≠ 0 → TorsionUnramified A V m) →
      (∃ (l : ℕ) (_ : Fact l.Prime), (l : ResidueField R) ≠ 0 ∧ TateUnramified A V l) ∧
        {m : ℕ | (m : ResidueField R) ≠ 0 ∧ TorsionUnramified A V m}.Infinite := by
  intro R K Ω _ _ _ _ _ _ _ V A _ _ hb
  obtain ⟨l, hl, hl0⟩ := exists_prime_natCast_ne_zero (ResidueField R)
  have hpow : ∀ n : ℕ, ((l ^ n : ℕ) : ResidueField R) ≠ 0 := fun n => by
    rw [Nat.cast_pow]; exact pow_ne_zero _ hl0
  refine ⟨⟨l, hl, hl0, tateUnramified_of_torsionUnramified fun n => hb _ (hpow n)⟩, ?_⟩
  exact Set.infinite_of_injective_forall_mem (f := fun n : ℕ => l ^ n)
    (Nat.pow_right_injective hl.out.two_le) fun n => ⟨hpow n, hb _ (hpow n)⟩

end GlobalTheory.Proof
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionUnramifiedImpTateModuleAndInfiniteStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsionUnramified_imp_tateModule_and_infinite : ∀ (R K Ω : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [Field Ω] [Algebra K Ω] (V : ValuationSubring Ω) (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], (∀ m : ℕ, (m : ResidueField R) ≠ 0 → TorsionUnramified A V m) → (∃ (l : ℕ) (_ : Fact l.Prime), (l : ResidueField R) ≠ 0 ∧ TateUnramified A V l) ∧ {m : ℕ | (m : ResidueField R) ≠ 0 ∧ TorsionUnramified A V m}.Infinite := by
  first | exact @GlobalTheory.Proof.torsionUnramified_imp_tate_and_infinite | exact GlobalTheory.Proof.torsionUnramified_imp_tate_and_infinite | (intros; apply GlobalTheory.Proof.torsionUnramified_imp_tate_and_infinite <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenSmoothOfRelativeDimensionOfGeneri
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenSmoothOfRelativeDimensionOfGeneri
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
open TopologicalSpace

namespace GlobalTheory.SmoothRelDim

theorem smoothOfRelativeDimension_of_generic (R : Type) [CommRing R] [IsDomain R] (X : Over (Sp R))
    [Smooth X.hom] (K : Type) [Field K] (e : R →+* K) (he : Function.Injective e) (g : ℕ)
    (hg : SmoothOfRelativeDimension g (pullback.snd X.hom (spMap e))) :
    SmoothOfRelativeDimension g X.hom := by
  have hdom : IsDominant (spMap e) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
      (by change RingHom.ker e ≤ _; rw [(RingHom.injective_iff_ker_eq_bot e).1 he]; exact bot_le)⟩
  choose n W hW hd using ReciprocityTheory.ChartRestriction.G.H1.exists_dim X.hom
  have : UniversallyOpen X.hom := UniversallyOpen.of_flat X.hom
  have key : ∀ x, n x = g := fun x => by
    have ho : IsOpen (X.hom.base '' (W x : Set X.left)) := X.hom.isOpenMap _ (W x).isOpen
    obtain ⟨s, ⟨y, hyW, hy⟩, t, rfl⟩ :=
      hdom.denseRange.inter_open_nonempty _ ho ⟨_, x, hW x, rfl⟩
    obtain ⟨z, hz1, -⟩ := Scheme.Pullback.exists_preimage_pullback y t hy
    exact ReciprocityTheory.ChartRestriction.G.H1.dim_base (IsPullback.of_hasPullback X.hom (spMap e)) (hd x) hg z (hz1 ▸ hyW)
  have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension g) := HasRingHomProperty.instIsZariskiLocalAtSource
  exact IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension g) W
    (top_le_iff.1 fun x _ => Opens.mem_iSup.2 ⟨x, hW x⟩) fun x => key x ▸ hd x

theorem exists_basicOpen : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (X : Over (Sp R)), Smooth X.hom → QuasiCompact X.hom → ∀ (K : Type) [Field K] (e : R →+* K), Function.Injective e → ∀ g : ℕ, SmoothOfRelativeDimension g (pullback.snd X.hom (spMap e)) → ∃ f : R, e f ≠ 0 ∧ ∀ (F : Type) [Field F] (ψ : R →+* F), IsUnit (ψ f) → SmoothOfRelativeDimension g (pullback.snd X.hom (spMap ψ)) := by
  intro R _ _ _ X hX _ K _ e he g hg
  haveI := hX
  refine ⟨1, by simp, fun F _ ψ _ => ?_⟩
  exact (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback (IsPullback.of_hasPullback _ _)
    (smoothOfRelativeDimension_of_generic R X K e he g hg)

end GlobalTheory.SmoothRelDim
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenSmoothOfRelativeDimensionOfGeneriStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_basicOpen_smoothOfRelativeDimension_of_generic : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (X : Over (Sp R)), Smooth X.hom → QuasiCompact X.hom → ∀ (K : Type) [Field K] (e : R →+* K), Function.Injective e → ∀ g : ℕ, SmoothOfRelativeDimension g (pullback.snd X.hom (spMap e)) → ∃ f : R, e f ≠ 0 ∧ ∀ (F : Type) [Field F] (ψ : R →+* F), IsUnit (ψ f) → SmoothOfRelativeDimension g (pullback.snd X.hom (spMap ψ)) := by
  first | exact @GlobalTheory.SmoothRelDim.exists_basicOpen | exact GlobalTheory.SmoothRelDim.exists_basicOpen | (intros; apply GlobalTheory.SmoothRelDim.exists_basicOpen <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinsetFixingPointLocallyFiniteType
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinsetFixingPointLocallyFiniteType
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtFin

theorem exists_finset_fix : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] (A : Over (Sp K)),
    LocallyOfFiniteType A.hom → ∀ x : ptOver K Ω ⟶ A, ∃ s : Finset Ω, ∀ σ : Ω ≃ₐ[K] Ω,
      (∀ a ∈ s, σ a = a) → specAut σ ≫ x = x := by
  classical
  intro K Ω _ _ _ A hA x
  haveI := hA
  obtain ⟨⟨p, φ⟩, hx⟩ := (Scheme.SpecToEquivOfField Ω A.left).symm.surjective x.left
  simp only [Scheme.SpecToEquivOfField_symm_apply] at hx
  have hxs : x.left ≫ A.hom = spMap (algebraMap K Ω) := Over.w x
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (A.left.fromSpecResidueField p ≫ A.hom)
  have hess := GlobalTheory.SS.essFiniteType_residueField_of_locallyOfFiniteType A.hom p ψ hψ
  rw [← hx, Category.assoc, ← hψ, ← Spec.map_comp, Spec.map_inj] at hxs
  letI : Algebra K (A.left.residueField p) := ψ.hom.toAlgebra
  haveI : Algebra.EssFiniteType K (A.left.residueField p) := hess
  let fa : A.left.residueField p →ₐ[K] Ω :=
    { φ.hom with commutes' := fun c => congrArg (fun g => g.hom c) hxs }
  refine ⟨(Algebra.EssFiniteType.finset K (A.left.residueField p)).image fa, fun σ hσ => ?_⟩
  have e : (σ : Ω →ₐ[K] Ω).comp fa = fa :=
    Algebra.EssFiniteType.algHom_ext Ω _ _ fun c hc => hσ _ (Finset.mem_image_of_mem _ hc)
  apply Over.OverMorphism.ext
  change spMap (σ : Ω →+* Ω) ≫ x.left = x.left
  rw [← hx, ← Category.assoc, ← Spec.map_comp]
  congr 2
  ext c
  exact congrArg (fun g => g c) e

end GlobalTheory.PtFin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinsetFixingPointLocallyFiniteTypeStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finset_fixing_point_locallyFiniteType : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] (A : Over (Sp K)), LocallyOfFiniteType A.hom → ∀ x : ptOver K Ω ⟶ A, ∃ s : Finset Ω, ∀ σ : Ω ≃ₐ[K] Ω, (∀ a ∈ s, σ a = a) → specAut σ ≫ x = x := by
  first | exact @GlobalTheory.PtFin.exists_finset_fix | exact GlobalTheory.PtFin.exists_finset_fix | (intros; apply GlobalTheory.PtFin.exists_finset_fix <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmExtensionIdeleConjIdeleMapMaxRealSubfield
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmExtensionIdeleConjIdeleMapMaxRealSubfield
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.ConjIdeleReal

theorem adeleMap_eq_baseChange (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap K L = GroundTheory.Global.AdeleBaseChange.adeleMap K L := by
  ext a : 1
  apply Prod.ext
  · funext w
    open scoped NumberField.LiesOver in
    change AbsoluteValue.Completion.map _ _ _ = algebraMap _ _ _
    rw [AbsoluteValue.Completion.algebraMap_eq_of_liesOver]
  · apply FiniteAdeleRing.ext
    intro w
    change GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteCompletionMap K L w _ =
      GroundTheory.Global.SemiLocal.completionMap _ w _
    rfl

theorem ideleConj_ideleMap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (b : Neutral.B1.Ideles (maximalRealSubfield E)),
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleConj (maximalRealSubfield E) E (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E b) =
      GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E b := by
  intro E _ _ _ b
  let alg : Algebra E E := (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.conj (maximalRealSubfield E) E).toRingEquiv.toRingHom.toAlgebra
  have tw : @IsScalarTower (maximalRealSubfield E) E E _ (@Algebra.toSMul _ _ _ _ alg) _ :=
    @IsScalarTower.of_algebraMap_eq (maximalRealSubfield E) E E _ _ _ _ alg _ fun x =>
      ((GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.conj (maximalRealSubfield E) E).commutes x).symm
  have h := @GroundTheory.Global.AdeleBaseChange.adeleMap_adeleMap (maximalRealSubfield E) E E _ _ _ _ _ _ _ alg _ tw
    (b : AdeleRing _ _)
  rw [← adeleMap_eq_baseChange, ← adeleMap_eq_baseChange] at h
  apply Units.ext
  exact h

end GlobalTheory.ConjIdeleReal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmExtensionIdeleConjIdeleMapMaxRealSubfieldStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmExtensionIdeleConj_ideleMap_maxRealSubfield : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (b : Neutral.B1.Ideles (maximalRealSubfield E)),
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleConj (maximalRealSubfield E) E (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E b) =
      GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E b := by
  first | exact @GlobalTheory.ConjIdeleReal.ideleConj_ideleMap | exact GlobalTheory.ConjIdeleReal.ideleConj_ideleMap | (intros; apply GlobalTheory.ConjIdeleReal.ideleConj_ideleMap <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemFiniteUnitIdelesOfMapMaxRealSubfield
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemFiniteUnitIdelesOfMapMaxRealSubfield
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.UnitDown

theorem exists_above {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) : ∃ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v := by
  haveI := v.isMaximal
  obtain ⟨P, hPm, hP⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 E) v.asIdeal
  have hne : P ≠ ⊥ := by
    intro h
    apply v.ne_bot
    rw [hP.over, h]
    exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 E))
  refine ⟨⟨P, hPm.isPrime, hne⟩, ?_⟩
  ext1
  rw [HeightOneSpectrum.under_asIdeal]
  exact hP.over.symm

theorem unit_down : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (b : Neutral.B1.Ideles (maximalRealSubfield E)),
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E b ∈ GlobalTheory.Mem.Chr.unitIdl E → b ∈ GlobalTheory.Mem.Chr.unitIdl (maximalRealSubfield E) := by
  intro E _ _ _ b hb v
  obtain ⟨w, rfl⟩ := exists_above (E := E) v
  have h := hb w
  have e : ((GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E b : AdeleRing (𝓞 E) E).2 w) =
      GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteCompletionMap (maximalRealSubfield E) E w
        ((b : AdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E)).2 (w.under _)) := rfl
  rw [e, GlobalTheory.UpIdeleMod.valued_finiteCompletionMap] at h
  have he : (w.under (𝓞 (maximalRealSubfield E))).asIdeal.ramificationIdx' w.asIdeal ≠ 0 :=
    Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver w.asIdeal (w.under _).ne_bot
  set x := Valued.v ((b : AdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E)).2 (w.under _))
  set n := (w.under (𝓞 (maximalRealSubfield E))).asIdeal.ramificationIdx' w.asIdeal
  have h' : x ^ n = 1 := h
  rcases lt_trichotomy x 1 with hx | hx | hx
  · exact absurd h' (pow_lt_one₀ zero_le' hx he).ne
  · exact hx
  · exact absurd h' (one_lt_pow₀ hx he).ne'

end GlobalTheory.UnitDown
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemFiniteUnitIdelesOfMapMaxRealSubfieldStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_finiteUnitIdeles_of_map_maxRealSubfield : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (b : Neutral.B1.Ideles (maximalRealSubfield E)),
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E b ∈ GlobalTheory.Mem.Chr.unitIdl E → b ∈ GlobalTheory.Mem.Chr.unitIdl (maximalRealSubfield E) := by
  first | exact @GlobalTheory.UnitDown.unit_down | exact GlobalTheory.UnitDown.unit_down | (intros; apply GlobalTheory.UnitDown.unit_down <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentFixLine
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (RingAct)
open scoped CategoryTheory.Obj NumberField
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.IwLevel

namespace GlobalTheory.HTLieFix

end GlobalTheory.HTLieFix

namespace GlobalTheory.HTLieFix

theorem one_left' {S : Scheme.{0}} {G X : Over S} [GrpObj G] : (1 : X ⟶ G).left = X.hom ≫ η[G].left := rfl
end GlobalTheory.HTLieFix

namespace GlobalTheory.HTLieFix

theorem mat_ext' {n : ℕ} {C : Type} [CommRing C] {A B : Matrix (Fin n) (Fin n) C}
    (h : ∀ v, A.mulVec v = B.mulVec v) : A = B :=
  Matrix.toLin'.injective (LinearMap.ext fun v => by simpa [Matrix.toLin'_apply] using h v)

theorem prod_ofFn_eq' {G : Type} [Monoid G] {V : Type} [AddCommMonoid V] (T : V → G)
    (h0 : T 0 = 1) (hadd : ∀ c c', T (c + c') = T c * T c') :
    ∀ {a : ℕ} (w : Fin a → V), (List.ofFn (fun i => T (w i))).prod = T (∑ i, w i)
  | 0, w => by simp [h0]
  | a + 1, w => by
    rw [List.ofFn_succ, List.prod_cons, Fin.sum_univ_succ, hadd, prod_ofFn_eq' T h0 hadd (fun i => w i.succ)]

end GlobalTheory.HTLieFix
end
end
