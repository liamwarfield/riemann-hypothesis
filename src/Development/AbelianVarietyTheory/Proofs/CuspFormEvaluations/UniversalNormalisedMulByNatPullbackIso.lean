module

public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FramedPointBaseChangeLaws
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NormVal
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ModNSqIffExistsGenLatSum

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.UniversalNormalisedMulByNatPullbackIso
section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.UniversalNormalisedMulByNatPullbackIso
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace NormMulUniv

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left}

theorem rigPow_isGen {ρ : LB.Gen (L.pull (eSec A))} (hρ : ρ.IsGen) (k : ℤ) : (rigPow A L ρ k).IsGen := by
  refine isGen_of_gm _ fun y i j hi hj => ?_
  have e := gen_trans (L := L) (φ := fun _ : PUnit.{1} => eSec A) (ε := fun _ => 1) hρ (𝟙 S) y hi hj
  rw [trF, Fintype.prod_unique, zpow_one] at e
  refine (map_zpow _ _ _).trans (Eq.trans ?_ (congrArg₂ (· * ·) rfl (map_zpow _ _ _)).symm)
  rw [trF, Fintype.prod_unique, ← mul_zpow]
  exact congrArg (· ^ k) e

theorem eSec_hom : eSec A ≫ A.hom = 𝟙 S := Over.w η[A]

theorem eSec_mulA (n : ℕ) : eSec A ≫ (mulA A n).left = eSec A := by
  have h : (η[A] : 𝟙_ (Over S) ⟶ A) = 1 := by simp [Hom.one_def]
  have : (η[A] : 𝟙_ (Over S) ⟶ A) ≫ mulA A n = η[A] := by
    rw [MonObj.comp_pow, Category.comp_id, h, one_pow]
  exact congrArg (fun q => q.left) this

theorem exists_normalised (hL : L.IsLB) {ρ : LB.Gen (L.pull (eSec A))} (hρ : ρ.IsGen) (n : ℕ)
    (β : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 A.left, (mulA A n).left] ![(n : ℤ) ^ 2, -1])) (hβ : β.IsGen) :
    ∃ α : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 A.left, (mulA A n).left] ![(n : ℤ) ^ 2, -1]), α.IsGen ∧
      IsNormMul A L ρ n α := by
  obtain ⟨α, hα, hv⟩ := exists_gen hL (φ' := ![𝟙 A.left, (mulA A n).left]) (ε' := ![(n : ℤ) ^ 2, -1])
    (fun U _ f => by
      simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Fintype.prod_unique, Sum.elim_inl, Sum.elim_inr,
        Matrix.cons_val_zero, Matrix.cons_val_one, eSec_mulA, Category.comp_id]
      rw [← zpow_add, ← zpow_add, ← zpow_add, show -(n : ℤ) ^ 2 + - -1 + ((n : ℤ) ^ 2 + -1) = 0 by ring, zpow_zero,
        _root_.mul_one])
    (LB.mulGen L _ _ _ _ β (LB.pullGen L _ _ (LB.mulGen L _ _ _ _
      (LB.invGen L _ _ (LB.pullGen L _ _ β (eSec A)))
      (LB.mulGen L _ _ _ _ (rigPow A L ρ ((n : ℤ) ^ 2)) (LB.invGen L (fun _ : PUnit => eSec A) (fun _ => 1) ρ))) A.hom))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ hβ (DVR.pullGen_isGen _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _
      (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hβ _))
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (rigPow_isGen hρ _) (DVR.invGen_isGen _ _ _ _ hρ))) _))
  refine ⟨α, hα, corr_of_val hL fun y J hJ => ?_⟩
  rw [val_pull hJ, hv _ _ y J hJ, val_mul hJ, val_pull hJ, Category.assoc, eSec_hom, Category.comp_id,
    val_mul hJ, val_inv, val_pull hJ, mul_inv_cancel_left]

theorem normalised_unique (hL : L.IsLB) (hp : Function.Surjective A.hom.appTop.hom)
    {ρ : LB.Gen (L.pull (eSec A))} {n : ℕ}
    {α β : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 A.left, (mulA A n).left] ![(n : ℤ) ^ 2, -1])}
    (hα : α.IsGen) (hβ : β.IsGen) (nα : IsNormMul A L ρ n α) (nβ : IsNormMul A L ρ n β) :
    LB.Gen.Corr L _ _ _ _ α β :=
  corr_of_val hL fun z J hJ => gen_unique hL A.hom (eSec A) eSec_hom hp hα hβ (fun w I hI => by
    have a := val_corr hI nα (𝟙 _)
    have b := val_corr hI nβ (𝟙 _)
    rw [val_pull hI, Category.id_comp] at a b
    exact a.trans b.symm) _ _ z J hJ

theorem exists_pull (hL : L.IsLB) {n : ℕ}
    (β : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 A.left, (mulA A n).left] ![(n : ℤ) ^ 2, -1])) (hβ : β.IsGen)
    (T : Over S) :
    ∃ α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, (snd T A ^ n).left] ![(n : ℤ) ^ 2, -1]), α.IsGen ∧
      LB.Gen.Corr L _ _ _ _ α (LB.pullGen L _ _ β (snd T A).left) := by
  have e₁ : (snd T A).left ≫ (mulA A n).left = (snd T A ^ n).left := by
    rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id]
  obtain ⟨α, hα, hv⟩ := exists_gen hL (φ' := ![(snd T A).left, (snd T A ^ n).left]) (ε' := ![(n : ℤ) ^ 2, -1])
    (fun U _ f => by
      refine Finset.prod_congr rfl fun i _ => ?_
      fin_cases i
      · exact congrArg (fun q => f q ^ ((n : ℤ) ^ 2)) (Category.comp_id _)
      · exact congrArg (fun q => f q ^ (-1 : ℤ)) e₁)
    (LB.pullGen L ![𝟙 A.left, (mulA A n).left] ![(n : ℤ) ^ 2, -1] β (snd T A).left)
    (DVR.pullGen_isGen _ _ _ _ hβ _)
  exact ⟨α, hα, corr_of_val hL fun y J hJ => hv _ _ y J hJ⟩

end NormMulUniv

theorem moduli_univ_normMul :
    Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (N : ℕ), ∃ α₀ : LB.Gen (LB.LinComb Xo.univ.t.PP.L (K := Fin 2) ![𝟙 Xo.univ.t.G.left, (mulA Xo.univ.t.G N).left] ![(N : ℤ) ^ 2, -1]), α₀.IsGen ∧ IsNormMul Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig N α₀ ∧ (∀ α₁, α₁.IsGen → IsNormMul Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig N α₁ → LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ α₁ α₀) ∧ ∀ T : Over Xo.X, ∃ α : LB.Gen (LB.LinComb Xo.univ.t.PP.L (K := Fin 2) ![(snd T Xo.univ.t.G).left, (snd T Xo.univ.t.G ^ N).left] ![(N : ℤ) ^ 2, -1]), α.IsGen ∧ LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ α (LB.pullGen Xo.univ.t.PP.L _ _ α₀ (snd T Xo.univ.t.G).left) := by
  intro hLaw E _ _ _ H Dw l Xo N
  have := UnivPol.isLocallyNoetherian Xo
  have hL := Xo.univ.t.PP.isLB
  obtain ⟨β, hβ⟩ := hLaw.mulPull _ (UnivPol.pol Xo) N
  obtain ⟨α₀, h₀, n₀⟩ := NormMulUniv.exists_normalised hL Xo.univ.t.PP.rigGen N β hβ
  exact ⟨α₀, h₀, n₀, fun α₁ h₁ n₁ => NormMulUniv.normalised_unique hL
    (hLaw.globalFns _ _ (ObjDim.isAbelianScheme Xo.univ)).2 h₁ h₀ n₁ n₀, NormMulUniv.exists_pull hL α₀ h₀⟩

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.UniversalNormalisedMulByNatPullbackIsoStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.universal_normalised_mulByNat_pullback_iso : Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (N : ℕ), ∃ α₀ : LB.Gen (LB.LinComb Xo.univ.t.PP.L (K := Fin 2) ![𝟙 Xo.univ.t.G.left, (mulA Xo.univ.t.G N).left] ![(N : ℤ) ^ 2, -1]), α₀.IsGen ∧ IsNormMul Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig N α₀ ∧ (∀ α₁, α₁.IsGen → IsNormMul Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig N α₁ → LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ α₁ α₀) ∧ ∀ T : Over Xo.X, ∃ α : LB.Gen (LB.LinComb Xo.univ.t.PP.L (K := Fin 2) ![(snd T Xo.univ.t.G).left, (snd T Xo.univ.t.G ^ N).left] ![(N : ℤ) ^ 2, -1]), α.IsGen ∧ LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ α (LB.pullGen Xo.univ.t.PP.L _ _ α₀ (snd T Xo.univ.t.G).left) := by
  first | exact @GlobalTheory.moduli_univ_normMul | exact GlobalTheory.moduli_univ_normMul | (intros; apply GlobalTheory.moduli_univ_normMul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsThetaGrpPullback
section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsThetaGrpPullback
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ThetaPullback

variable {S : Scheme.{0}} {A : Over S} [GrpObj A]

private theorem gm_res_eq_gm {X Z : Scheme.{0}} (r : Z ⟶ X) (z : Z) {U V : X.Opens} (hle : V ≤ U) (hz : r z ∈ V)
    (a : Γ(X, U)ˣ) : gm r z V (res hle a) = gm r z U a := by
  have key : X.presheaf.map (homOfLE hle).op ≫ r.app V ≫ Z.presheaf.germ (r ⁻¹ᵁ V) z hz =
      r.app U ≫ Z.presheaf.germ (r ⁻¹ᵁ U) z (hle hz) := by
    rw [Scheme.Hom.naturality_assoc]
    congr 1
    exact TopCat.Presheaf.germ_res _ _ _ _
  unfold gm res pullU
  rw [dite_eq_left hz, dite_eq_left (hle hz)]
  ext
  simp only [MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe]
  exact congrArg (fun φ => φ.hom (a : Γ(X, U))) key

private theorem exists_isGen_linComb_val_eq_of_eq {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ φ' : K → (Y ⟶ X)}
    {ε : K → ℤ} (hφ : φ = φ') (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) :
    ∃ t' : LB.Gen (LB.LinComb L φ' ε), t'.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι), val t' r z J = val t r z J := by
  subst hφ
  exact ⟨t, ht, fun _ _ _ _ => rfl⟩

theorem whiskerRight_translPt {T T' : Over S} (h : T' ⟶ T) (x : T ⟶ A) :
    h ▷ A ≫ translPt A x = translPt A (h ≫ x) := by
  unfold translPt
  rw [← Category.assoc, comp_lift]
  simp

theorem translT_whiskerRight {T T' : Over S} (h : T' ⟶ T) (x : T ⟶ A) :
    translT A (h ≫ x) ≫ h ▷ A = h ▷ A ≫ translT A x := by
  ext <;> simp [translT, whiskerRight_translPt]

theorem negT_whiskerRight {T T' : Over S} (h : T' ⟶ T) :
    negT A T' ≫ h ▷ A = h ▷ A ≫ negT A T := by
  ext <;> simp [negT]

theorem val_powGen {L : LB A.left} {k : ℤ} {T : Over S} (θ : ThetaGrp A L k T) (n : ℕ) {Z : Scheme.{0}}
    (r : Z ⟶ (T ⊗ A).left) {z : Z} {J} (hJ : Good L z J) :
    val (powGen A L k θ n) r z J = ∏ j : Fin n,
      val (L := L) (φ := ![(snd T A).left, (translPt A θ.pt).left]) (ε := ![k, -k]) θ.φ
        (r ≫ (translT A (θ.pt ^ (j : ℕ))).left) z J := by
  have e : ∀ j : Fin n, val (L := L) (φ := ![(snd T A).left, (translPt A θ.pt).left]) (ε := ![k, -k]) θ.φ
      (r ≫ (translT A (θ.pt ^ (j : ℕ))).left) z J =
      val (LB.pullGen L _ _ θ.φ (translT A (θ.pt ^ (j : ℕ))).left) r z J := fun j => (val_pull hJ _ _ r).symm
  rw [Finset.prod_congr rfl fun j _ => e j]
  unfold powGen val
  dsimp only
  erw [map_prod]
  refine Finset.prod_congr rfl fun j _ => ?_
  exact gm_res_eq_gm _ _ _ (hJ.mem _ r) _

theorem val_symGen {L : LB A.left} {k : ℤ} {T : Over S} (θ : ThetaGrp A L k T) (ν : LB.Gen (negLB A L k T))
    {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) {z : Z} {J} (hJ : Good L z J) :
    val (symGen A L k θ ν) r z J =
      val (L := L) (φ := ![(snd T A).left, (translPt A θ.pt).left]) (ε := ![k, -k]) θ.φ
          (r ≫ (translT A θ.pt⁻¹).left) z J *
        val (L := L) (φ := ![(snd T A).left, (snd T A ≫ (GrpObj.inv : A ⟶ A)).left]) (ε := ![k, -k]) ν r z J *
        (val (L := L) (φ := ![(snd T A).left, (translPt A θ.pt).left]) (ε := ![k, -k]) θ.φ
          (r ≫ (negT A T).left) z J *
        (val (L := L) (φ := ![(snd T A).left, (snd T A ≫ (GrpObj.inv : A ⟶ A)).left]) (ε := ![k, -k]) ν
          (r ≫ (translT A θ.pt⁻¹).left) z J)⁻¹) := by
  unfold symGen
  rw [val_mul hJ, val_mul hJ, val_inv]
  have e1 := val_mul hJ (LB.pullGen L _ _ θ.φ (translT A θ.pt⁻¹).left) ν r
  have e2 := val_pull hJ θ.φ (translT A θ.pt⁻¹).left r
  have e3 := val_pull hJ θ.φ (negT A T).left r
  have e4 := val_pull hJ ν (translT A θ.pt⁻¹).left r
  rw [e1, e2, e3, e4]

theorem exists_thetaGrp_pullback : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : LB A.left), L.IsLB → ∀ (k : ℤ) (T T' : Over S) (h : T' ⟶ T) (θ : ThetaGrp A L k T), ∃ θ' : ThetaGrp A L k T', θ'.pt = h ≫ θ.pt ∧ LB.Gen.Corr L _ _ _ _ θ'.φ (LB.pullGen L _ _ θ.φ (h ▷ A).left) ∧ (∀ (n : ℕ) (x : T ⟶ A), SymLift A L k n x θ → SymLift A L k n (h ≫ x) θ') ∧ ∀ (s t : LB.Sec (LPow A L k T)) (s' t' : LB.Sec (LPow A L k T')), IsActOf A L k θ s t → IsPullSec A L k (h ▷ A) (whiskerRight_snd _ _) s s' → IsPullSec A L k (h ▷ A) (whiskerRight_snd _ _) t t' → IsActOf A L k θ' s' t' := by
  intro S A _ _ L hL k T T' h θ
  have hφ : (fun b => (h ▷ A).left ≫ (![(snd T A).left, (translPt A θ.pt).left] : Fin 2 → _) b) =
      ![(snd T' A).left, (translPt A (h ≫ θ.pt)).left] := by
    funext b
    fin_cases b
    · simp only [Fin.zero_eta, Matrix.cons_val_zero]
      rw [← Over.comp_left, whiskerRight_snd]
    · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      rw [← Over.comp_left, whiskerRight_translPt]
  obtain ⟨φ', gφ', vφ'⟩ :=
    exists_isGen_linComb_val_eq_of_eq hφ _ (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen L _ _ θ.φ θ.3 (h ▷ A).left)
  have vθ : ∀ (Z : Scheme.{0}) (r : Z ⟶ (T' ⊗ A).left) (z : Z) (J : (Z ⟶ A.left) → L.ι), Good L z J →
      val φ' r z J = val (L := L) (φ := ![(snd T A).left, (translPt A θ.pt).left]) (ε := ![k, -k]) θ.φ
        (r ≫ (h ▷ A).left) z J :=
    fun Z r z J hJ => (vφ' Z r z J).trans (val_pull hJ _ _ r)
  have hcorr : LB.Gen.Corr L _ _ _ _ φ' (LB.pullGen L _ _ θ.φ (h ▷ A).left) :=
    corr_of_val hL fun y J _ => vφ' _ _ y J
  have hpow : ∀ j : ℕ, h ≫ θ.pt ^ j = (h ≫ θ.pt) ^ j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih => rw [pow_succ, pow_succ, comp_mul, ih]
  have hinv : h ≫ θ.pt⁻¹ = (h ≫ θ.pt)⁻¹ := GrpObj.comp_inv h θ.pt
  refine ⟨⟨h ≫ θ.pt, φ', gφ'⟩, rfl, hcorr, ?_, ?_⟩
  · intro n x hs
    obtain ⟨hpt, hpw, nu, gnu, hsym⟩ := hs
    refine ⟨?_, ?_, ?_⟩
    · show h ≫ θ.pt = h ≫ x
      rw [hpt]
    · refine corr_of_val hL fun y J hJ => ?_
      have hθ1 := val_corr hJ hpw (h ▷ A).left
      rw [val_one, val_powGen _ _ _ hJ] at hθ1
      rw [val_one, val_powGen _ _ _ hJ, ← hθ1]
      refine Finset.prod_congr rfl fun j _ => ?_
      dsimp only
      rw [vθ _ _ _ _ hJ]
      have e : (𝟙 _ ≫ (translT A ((h ≫ θ.pt) ^ (j : ℕ))).left) ≫ (h ▷ A).left =
          (h ▷ A).left ≫ (translT A (θ.pt ^ (j : ℕ))).left := by
        rw [Category.id_comp, ← Over.comp_left, ← Over.comp_left, ← hpow, translT_whiskerRight]
      rw [e]
    · have hφn : (fun b => (h ▷ A).left ≫
            (![(snd T A).left, (snd T A ≫ (GrpObj.inv : A ⟶ A)).left] : Fin 2 → _) b) =
          ![(snd T' A).left, (snd T' A ≫ (GrpObj.inv : A ⟶ A)).left] := by
        funext b
        fin_cases b
        · simp only [Fin.zero_eta, Matrix.cons_val_zero]
          rw [← Over.comp_left, whiskerRight_snd]
        · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one]
          rw [← Over.comp_left, whiskerRight_snd_assoc]
      obtain ⟨nu', gnu', vnu'⟩ :=
        exists_isGen_linComb_val_eq_of_eq hφn _ (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen L _ _ nu gnu (h ▷ A).left)
      have vnu : ∀ (Z : Scheme.{0}) (r : Z ⟶ (T' ⊗ A).left) (z : Z) (J : (Z ⟶ A.left) → L.ι), Good L z J →
          val nu' r z J = val (L := L) (φ := ![(snd T A).left, (snd T A ≫ (GrpObj.inv : A ⟶ A)).left])
            (ε := ![k, -k]) nu (r ≫ (h ▷ A).left) z J :=
        fun Z r z J hJ => (vnu' Z r z J).trans (val_pull hJ _ _ r)
      refine ⟨nu', gnu', corr_of_val hL fun y J hJ => ?_⟩
      have hθ2 := val_corr hJ hsym (h ▷ A).left
      rw [val_one, val_symGen _ _ _ hJ] at hθ2
      rw [val_one]
      refine (val_symGen _ _ _ hJ).trans ?_
      rw [← hθ2]
      dsimp only
      rw [vθ _ _ _ _ hJ, vθ _ _ _ _ hJ, vnu _ _ _ _ hJ, vnu _ _ _ _ hJ]
      have e1 : (𝟙 _ ≫ (translT A (h ≫ θ.pt)⁻¹).left) ≫ (h ▷ A).left =
          (h ▷ A).left ≫ (translT A θ.pt⁻¹).left := by
        rw [Category.id_comp, ← Over.comp_left, ← Over.comp_left, ← hinv, translT_whiskerRight]
      have e3 : (𝟙 _ ≫ (negT A T').left) ≫ (h ▷ A).left = (h ▷ A).left ≫ (negT A T).left := by
        rw [Category.id_comp, ← Over.comp_left, ← Over.comp_left, negT_whiskerRight]
      rw [e1, e3, Category.id_comp]
  · intro s t s' t' hact hs ht
    unfold IsActOf at hact ⊢
    exact GlobalTheory.TwistBaseChange.isTwistPull_baseChange S A L hL T T' h _ _ _ _ _ _
      (translT_whiskerRight h θ.pt) k k θ.φ φ' θ.3 gφ' hcorr s t s' t' hact hs ht

end GlobalTheory.ThetaPullback
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsThetaGrpPullbackStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_symLift_pullback_isActOf : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : LB A.left), L.IsLB → ∀ (k : ℤ) (T T' : Over S) (h : T' ⟶ T) (θ : ThetaGrp A L k T), ∃ θ' : ThetaGrp A L k T', θ'.pt = h ≫ θ.pt ∧ LB.Gen.Corr L _ _ _ _ θ'.φ (LB.pullGen L _ _ θ.φ (h ▷ A).left) ∧ (∀ (n : ℕ) (x : T ⟶ A), SymLift A L k n x θ → SymLift A L k n (h ≫ x) θ') ∧ ∀ (s t : LB.Sec (LPow A L k T)) (s' t' : LB.Sec (LPow A L k T')), IsActOf A L k θ s t → IsPullSec A L k (h ▷ A) (whiskerRight_snd _ _) s s' → IsPullSec A L k (h ▷ A) (whiskerRight_snd _ _) t t' → IsActOf A L k θ' s' t' := by
  first | exact @GlobalTheory.ThetaPullback.exists_thetaGrp_pullback | exact GlobalTheory.ThetaPullback.exists_thetaGrp_pullback | (intros; apply GlobalTheory.ThetaPullback.exists_thetaGrp_pullback <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ModuliUnivEtaKilled
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace LevelPoints

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {B : Type} [CommRing B] {b : Base l B} {S : Scheme.{0}} {s : S ⟶ Sp B}

theorem section_ext [IsReduced S] {G : Over S} [IsSeparated G.hom] (f g : 𝟙_ (Over S) ⟶ G)
    (h : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S),
      toUnit (Over.mk x) ≫ f = toUnit (Over.mk x) ≫ g) : f = g := by
  have : IsReduced (𝟙_ (Over S)).left := ‹IsReduced S›
  refine Over.OverMorphism.ext (hom_ext_of_geometricPoints_dense G.hom f.left g.left
    ((Over.w f).trans (Over.w g).symm) Set.univ dense_univ fun k _ _ x _ => ?_)
  have e : (toUnit (Over.mk (Y := Sp k) (X := S) x)).left = x :=
    (Category.comp_id _).symm.trans (Over.w (toUnit (Over.mk (Y := Sp k) (X := S) x)))
  have := congrArg CommaMorphism.left (h k x)
  simp only [Over.comp_left] at this
  rw [e] at this
  exact this

theorem eta_zero (o : Obj D l b s) : o.eta 0 = 1 := o.eta_ker 0 (Submodule.zero_mem _)

theorem eta_nsmul (o : Obj D l b s) (n : ℕ) (a : D.La) : o.eta (n • a) = o.eta a ^ n := by
  induction n with
  | zero => rw [zero_smul, pow_zero, eta_zero]
  | succ n ih => rw [succ_nsmul, o.eta_add, ih, pow_succ]

theorem natCast_mem (l : Level H) : (l.M : 𝓞 E) ∈ l.Mb := by
  have h := Ideal.mem_span_singleton_self (l.M : 𝓞 E)
  rw [← l.prod] at h
  exact Ideal.mul_le_left h

theorem eta_pow (o : Obj D l b s) (a : D.La) : o.eta a ^ l.M = 1 := by
  rw [← eta_nsmul, ← Nat.cast_smul_eq_nsmul (𝓞 E)]
  exact o.eta_ker _ (Submodule.smul_mem_smul (natCast_mem l) Submodule.mem_top)

theorem eta_smul [IsReduced S] (o : Obj D l b s) (c : 𝓞 E) (a : D.La) :
    o.eta (c • a) = o.eta a ≫ o.t.act.act c := by
  have := o.proper
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp (l.coprime ▸ Submodule.mem_top :
    (1 : 𝓞 E) ∈ l.Mb ⊔ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E))
  have key : ∀ a : D.La, o.eta a = o.eta (v • a) := fun a => by
    conv_lhs => rw [← one_smul (𝓞 E) a, ← huv, add_smul, o.eta_add,
      o.eta_ker _ (Submodule.smul_mem_smul hu Submodule.mem_top), _root_.one_mul]
  refine section_ext _ _ fun k _ _ x => ?_
  obtain ⟨-, I, -, -, hI⟩ := o.geom k x (Spec.preimage (x ≫ s)).hom (by
    rw [spMap, CommRingCat.ofHom_hom, Spec.map_preimage])
  rw [key a, key (c • a), ← Category.assoc, hI _ (Submodule.smul_mem_smul hv Submodule.mem_top),
    hI _ (Submodule.smul_mem_smul hv Submodule.mem_top), smul_comm v c a, I.lin]

end LevelPoints

theorem moduli_univ_eta_killed :
    Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (a : Dw.La), (∀ b ∈ l.Mb, Xo.univ.eta a ≫ Xo.univ.t.act.act b = 1) ∧ (∀ b : 𝓞 E, Xo.univ.eta (b • a) = Xo.univ.eta a ≫ Xo.univ.t.act.act b) ∧ Xo.univ.eta a ^ l.M = 1 := by
  intro _ E _ _ _ H Dw l Xo a
  have := UnivPol.isReduced Xo
  refine ⟨fun c hc => ?_, fun c => LevelPoints.eta_smul _ c a, LevelPoints.eta_pow _ a⟩
  rw [← LevelPoints.eta_smul]
  exact Xo.univ.eta_ker _ (Submodule.smul_mem_smul hc Submodule.mem_top)

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.UniversalSymLiftExistsUniqueGlobal
section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.UniversalSymLiftExistsUniqueGlobal
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem symLift_exists_unique_of_cast (hLaw : Laws) (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (k : ℕ)
    (hk : Odd k) (hu : IsUnit (k : Γ(S, ⊤))) (K : ℤ) (hK : K = (k : ℤ)) (T : Over S) (x : T ⟶ P.A)
    (hx : x ^ k = 1) :
    (∃ U : ThetaGrp P.A P.L K T, SymLift P.A P.L K k x U) ∧
      ∀ U U' : ThetaGrp P.A P.L K T, SymLift P.A P.L K k x U → SymLift P.A P.L K k x U' →
        LB.Gen.Corr P.L _ _ _ _ U.φ U'.φ := by
  subst hK
  refine ⟨exists_symLift_global hLaw S P k hk hu T x hx, ?_⟩
  intro U U' hU hU'
  exact SymLiftOdd.symLift_unique hLaw.globalFns P.isAb P.isLB hk U U' hU hU'

theorem moduli_univ_symLift_global :
    Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (N : ℕ), Odd N → ∀ (T : Over Xo.X) (x : T ⟶ Xo.univ.t.G), x ^ (N ^ 2) = 1 → (∃ U : ThetaGrp Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) T, SymLift Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (N ^ 2) x U) ∧ ∀ U U' : ThetaGrp Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) T, SymLift Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (N ^ 2) x U → SymLift Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (N ^ 2) x U' → LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ U.φ U'.φ := by
  intro hLaw E _ _ _ H Dw l Xo N hN
  obtain ⟨hNoeth, -, hUnit, -, hP⟩ := moduli_univ_polAV E H Dw l Xo
  have := hNoeth
  have hN2 : Odd (N ^ 2) := hN.pow
  have hpos : 0 < N ^ 2 := pow_pos hN.pos 2
  refine hP (fun (A : Over Xo.X) [GrpObj A] [IsCommMonObj A] (L : LB A.left) (_ : ℕ) =>
    ∀ (T : Over Xo.X) (x : T ⟶ A), x ^ (N ^ 2) = 1 →
      (∃ U : ThetaGrp A L ((N : ℤ) ^ 2) T, SymLift A L ((N : ℤ) ^ 2) (N ^ 2) x U) ∧
        ∀ U U' : ThetaGrp A L ((N : ℤ) ^ 2) T, SymLift A L ((N : ℤ) ^ 2) (N ^ 2) x U →
          SymLift A L ((N : ℤ) ^ 2) (N ^ 2) x U' → LB.Gen.Corr L _ _ _ _ U.φ U'.φ) ?_
  intro P T x hx
  exact symLift_exists_unique_of_cast hLaw Xo.X P (N ^ 2) hN2 (hUnit _ hpos) ((N : ℤ) ^ 2)
    (by push_cast; rfl) T x hx

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.UniversalSymLiftExistsUniqueGlobalStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.universal_symLift_exists_unique_global : Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (N : ℕ), Odd N → ∀ (T : Over Xo.X) (x : T ⟶ Xo.univ.t.G), x ^ (N ^ 2) = 1 → (∃ U : ThetaGrp Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) T, SymLift Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (N ^ 2) x U) ∧ ∀ U U' : ThetaGrp Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) T, SymLift Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (N ^ 2) x U → SymLift Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (N ^ 2) x U' → LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ U.φ U'.φ := by
  first | exact @GlobalTheory.moduli_univ_symLift_global | exact GlobalTheory.moduli_univ_symLift_global | (intros; apply GlobalTheory.moduli_univ_symLift_global <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsIsotropicGroupLatticeClassRepresentatives
section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsIsotropicGroupLatticeClassRepresentatives
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open scoped TensorProduct

namespace GlobalTheory.ZCount

theorem finrank_fibre (O M k : Type) [CommRing O] [IsDomain O] [AddCommGroup M] [Module O M]
    [Module.Finite O M] [Module.Projective O M] [Field k] [Algebra O k] :
    Module.finrank k (k ⊗[O] M) = Module.finrank O M := by
  have : Module.FinitePresentation O M := Module.finitePresentation_of_projective O M
  have key : ∀ (K : Type) [Field K] [Algebra O K], Module.finrank K (K ⊗[O] M) =
      Module.rankAtStalk M (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum O) := fun K _ _ => by
    have h := Module.rankAtStalk_baseChange (R := O) (M := M) (S := K) ⟨⊥, Ideal.isPrime_bot⟩
    rw [Module.rankAtStalk_eq_finrank_of_free] at h
    exact h.trans ((Module.isLocallyConstant_rankAtStalk (R := O) (M := M)).apply_eq_of_preconnectedSpace _ _)
  rw [key k, ← key (FractionRing O), (TensorProduct.isBaseChange O M (FractionRing O)).finrank_eq]

theorem exists_basis_mod (O M : Type) [CommRing O] [IsDomain O] [AddCommGroup M] [Module O M]
    [Module.Finite O M] [Module.Projective O M] (m : O) [Finite (O ⧸ Ideal.span {m})] (r : ℕ)
    (hr : Module.finrank O M = r) :
    ∃ e : Fin r → M, (∀ x : M, ∃ (c : Fin r → O) (y : M), x = ∑ k, c k • e k + m • y) ∧
      ∀ (c : Fin r → O) (y : M), ∑ k, c k • e k = m • y → ∀ k, m ∣ c k := by
  set I : Ideal O := Ideal.span {m} with hI
  have : Finite (Ideal (O ⧸ I)) := Finite.of_injective _ SetLike.coe_injective
  have : Finite (MaximalSpectrum (O ⧸ I)) :=
    Finite.of_injective (fun P => P.asIdeal) fun _ _ h => MaximalSpectrum.ext h
  obtain ⟨B⟩ := Module.nonempty_basis_of_flat_of_finrank_eq (O ⧸ I) ((O ⧸ I) ⊗[O] M) r fun P => by
    let := P.isMaximal
    let := Ideal.Quotient.field P.asIdeal
    rw [(TensorProduct.AlgebraTensorModule.cancelBaseChange O (O ⧸ I) ((O ⧸ I) ⧸ P.1) ((O ⧸ I) ⧸ P.1) M).finrank_eq,
      finrank_fibre, hr]
  have hs : Function.Surjective (TensorProduct.mk O (O ⧸ I) M 1) :=
    TensorProduct.mk_surjective O M (O ⧸ I) Ideal.Quotient.mk_surjective
  have hk : ∀ x : M, TensorProduct.mk O (O ⧸ I) M 1 x = 0 ↔ ∃ y, x = m • y := fun x => by
    rw [← (TensorProduct.quotTensorEquivQuotSMul M I).map_eq_zero_iff, TensorProduct.mk_apply,
      TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul, Submodule.Quotient.mk_eq_zero, hI,
      Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
    exact ⟨fun ⟨y, _, h⟩ => ⟨y, h.symm⟩, fun ⟨y, h⟩ => ⟨y, trivial, h.symm⟩⟩
  choose e he using fun k => hs (B k)
  have hc : ∀ c : Fin r → O, TensorProduct.mk O (O ⧸ I) M 1 (∑ k, c k • e k) =
      ∑ k, Ideal.Quotient.mk I (c k) • B k := fun c => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, he, ← Ideal.Quotient.algebraMap_eq, algebraMap_smul]
  refine ⟨e, fun x => ?_, fun c y h k => ?_⟩
  · choose c hc' using fun k => Ideal.Quotient.mk_surjective (B.repr (TensorProduct.mk O (O ⧸ I) M 1 x) k)
    obtain ⟨y, hy⟩ := (hk (x - ∑ k, c k • e k)).1 (by
      rw [map_sub, hc]
      simp only [hc']
      rw [B.sum_repr, sub_self])
    exact ⟨c, y, by rw [← hy]; abel⟩
  · have h0 := (hk _).2 ⟨y, h⟩
    rw [hc] at h0
    have := Fintype.linearIndependent_iff.1 B.linearIndependent _ h0 k
    rwa [Ideal.Quotient.eq_zero_iff_mem, hI, Ideal.mem_span_singleton] at this

section

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem mem_stdLat (v : Fin n → E) :
    v ∈ stdLat E n ↔ ∃ u : Fin n → 𝓞 E, ∀ b, v b = (u b : E) := by
  simp only [stdLat, Submodule.mem_pi, Set.mem_univ, true_imp_iff, Submodule.mem_one]
  constructor
  · intro h
    choose u hu using h
    exact ⟨u, fun b => (hu b).symm⟩
  · rintro ⟨u, hu⟩ b
    exact ⟨u b, (hu b).symm⟩

theorem mem_smul_stdLat (N : ℕ) (v : Fin n → E) :
    v ∈ Ideal.span {(N : 𝓞 E)} • stdLat E n ↔ ∃ u : Fin n → 𝓞 E, ∀ b, v b = (N : E) * (u b : E) := by
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨u, hu⟩ := (mem_stdLat w).1 hw
    exact ⟨u, fun b => by simp [hu, Algebra.smul_def]⟩
  · rintro ⟨u, hu⟩
    exact ⟨fun b => u b, (mem_stdLat _).2 ⟨u, fun _ => rfl⟩, funext fun b => by simp [hu, Algebra.smul_def]⟩

theorem mul_integral [IsCMField E] (Λ : GenLat E n) (N : ℕ) (hU : Λ.Unimod)
    (hN : Ideal.span {(N : 𝓞 E)} • stdLat E n ≤ Λ.La) (w : Fin n → E) (hw : w ∈ Λ.La) :
    ∃ v : Fin n → 𝓞 E, ∀ b, (v b : E) = (N : E) * w b := by
  have h : ∀ b, ∃ a : 𝓞 E, (a : E) = (N : E) * w b := fun b => by
    have hb : (Pi.single b (N : E) : Fin n → E) ∈ Λ.La := hN ((mem_smul_stdLat N _).2
      ⟨Pi.single b 1, fun j => by
        by_cases hj : j = b
        · subst hj; simp
        · simp [hj]⟩)
    obtain ⟨a, ha⟩ := (hU _).1 hb w hw
    refine ⟨a, ha.trans ?_⟩
    rw [Finset.sum_eq_single b (fun j _ hj => by simp [hj]) (by simp)]
    simp
  choose v hv using h
  exact ⟨v, hv⟩

end

theorem exists_class_representatives : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (n : ℕ) (Λ : GenLat E n) (N : ℕ), Λ.Unimod → 0 < N → Ideal.span {(N : 𝓞 E)} • stdLat E n ≤ Λ.La → ∃ zz : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → Dw.La, (∀ i₀, (∀ (mu : Matrix (Fin n) (Fin n) E), (∀ v ∈ Λ.La, mu.mulVec v ∈ stdLat E n) → ∀ cm : Fin n → Fin n → 𝓞 E, (∀ i j, (cm i j : E) = (N : E) * mu i j) → ∀ i, Dw.ModN (N ^ 2) (∑ j, cm i j • zz i₀ j))) ∧ (∀ i i', (∀ b, Dw.ModN (N ^ 2) (zz i b - zz i' b)) → i = i') ∧ ∀ a : Fin n → Dw.La, (∀ (mu : Matrix (Fin n) (Fin n) E), (∀ v ∈ Λ.La, mu.mulVec v ∈ stdLat E n) → ∀ cm : Fin n → Fin n → 𝓞 E, (∀ i j, (cm i j : E) = (N : E) * mu i j) → ∀ i, Dw.ModN (N ^ 2) (∑ j, cm i j • a j)) → ∃ i, ∀ b, Dw.ModN (N ^ 2) (a b - zz i b) := by
  intro E _ _ _ H Dw n Λ N hU hN0 hN
  have := Dw.fin
  have := Dw.proj
  have hNE : (N : E) ≠ 0 := Nat.cast_ne_zero.2 hN0.ne'
  have hNO : (N : 𝓞 E) ≠ 0 := Nat.cast_ne_zero.2 hN0.ne'
  have : Finite (𝓞 E ⧸ Ideal.span {(N : 𝓞 E) ^ 2}) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ (by simpa using hN0.ne')
  obtain ⟨e, he1, he2⟩ := exists_basis_mod (𝓞 E) Dw.La ((N : 𝓞 E) ^ 2) (Dw.p + Dw.q) Dw.rank
  set K := (Ideal.span {(N : 𝓞 E)} • stdLat E n).toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup with hK
  choose V hV using fun w : Λ.La.toAddSubgroup => mul_integral Λ N hU hN w.1 w.2
  have hKV : ∀ w w' : Λ.La.toAddSubgroup, (w : Λ.La.toAddSubgroup ⧸ K) = w' ↔
      ∀ b, (N : 𝓞 E) ^ 2 ∣ V w' b - V w b := fun w w' => by
    rw [QuotientAddGroup.eq, hK, AddSubgroup.mem_addSubgroupOf, Submodule.mem_toAddSubgroup,
      mem_smul_stdLat]
    constructor
    · rintro ⟨u, hu⟩ b
      refine ⟨u b, RingOfIntegers.ext ?_⟩
      have := hu b
      simp only [AddSubgroup.coe_add, AddSubgroup.coe_neg, Pi.add_apply, Pi.neg_apply] at this
      have e1 := hV w b
      have e2 := hV w' b
      simp only [RingOfIntegers.coe_eq_algebraMap] at *
      rw [map_sub, map_mul, map_pow, map_natCast, e1, e2]
      linear_combination (N : E) * this
    · intro h
      choose u hu using h
      refine ⟨u, fun b => mul_left_cancel₀ hNE ?_⟩
      have := congrArg (algebraMap (𝓞 E) E) (hu b)
      have e1 := hV w b
      have e2 := hV w' b
      simp only [RingOfIntegers.coe_eq_algebraMap] at *
      rw [map_sub, map_mul, map_pow, map_natCast, e1, e2] at this
      simp only [AddSubgroup.coe_add, AddSubgroup.coe_neg, Pi.add_apply, Pi.neg_apply]
      linear_combination this
  have : Finite (Λ.La.toAddSubgroup ⧸ K) :=
    Finite.of_injective (fun q b => Ideal.Quotient.mk (Ideal.span {(N : 𝓞 E) ^ 2}) (V q.out b))
      fun q q' h => by
        rw [← q.out_eq, ← q'.out_eq]
        refine (hKV _ _).2 fun b => ?_
        rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq]
        exact (congrFun h b).symm
  have hcard : Nat.card (Fin (Dw.p + Dw.q) → Λ.La.toAddSubgroup ⧸ K) = Λ.zCard N (Dw.p + Dw.q) := by
    rw [Nat.card_fun, Nat.card_fin]
    rfl
  let σ := (Finite.equivFinOfCardEq hcard).symm
  have hM : ∀ x : Dw.La, Dw.ModN (N ^ 2) x ↔ ∃ y, x = ((N : 𝓞 E) ^ 2) • y := fun x => by
    simp only [Datum.ModN, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
  refine ⟨fun i b => ∑ k, V (σ i k).out b • e k, fun i => ?_, fun i i' h => ?_, fun a ha => ?_⟩
  · exact (GlobalTheory.T.modN_sq_sum_iff_exists_genLat_decomposition E H Dw n Λ N hU hN0 hN _).2
      ⟨_, e, fun k => V (σ i k).out, fun k => ⟨_, (σ i k).out.2, hV _⟩, fun _ => rfl⟩
  · refine σ.injective (funext fun k => ?_)
    rw [← (σ i k).out_eq, ← (σ i' k).out_eq]
    refine ((hKV _ _).2 fun b => ?_).symm
    obtain ⟨y, hy⟩ := (hM _).1 (h b)
    refine he2 (fun k => V (σ i k).out b - V (σ i' k).out b) y ?_ k
    rw [← hy, ← Finset.sum_sub_distrib]
    simp only [sub_smul]
  · obtain ⟨m, x, v, hv, hav⟩ := (GlobalTheory.T.modN_sq_sum_iff_exists_genLat_decomposition E H Dw n Λ N hU hN0 hN a).1 ha
    choose w hw hvw using hv
    choose c y hcy using fun i => he1 (x i)
    let W : Fin (Dw.p + Dw.q) → Λ.La.toAddSubgroup := fun k =>
      ⟨∑ i, c i k • w i, Λ.La.sum_mem fun i _ => Λ.La.smul_mem _ (hw i)⟩
    have hW : ∀ k b, V (W k) b = ∑ i, v i b * c i k := fun k b => by
      refine RingOfIntegers.ext ?_
      rw [hV]
      simp only [RingOfIntegers.coe_eq_algebraMap] at *
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [W, map_sum, map_mul, hvw, Finset.sum_apply, Pi.smul_apply, Algebra.smul_def,
        Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    refine ⟨σ.symm fun k => (W k : Λ.La.toAddSubgroup ⧸ K), fun b => (hM _).2 ?_⟩
    simp only [Equiv.apply_symm_apply]
    choose t ht using fun k => (hKV _ (W k)).1 (QuotientAddGroup.out_eq' (W k : Λ.La.toAddSubgroup ⧸ K)) b
    refine ⟨∑ k, t k • e k + ∑ i, v i b • y i, ?_⟩
    have h1 : a b = ∑ k, V (W k) b • e k + (N : 𝓞 E) ^ 2 • ∑ i, v i b • y i := by
      rw [hav b]
      simp only [hW, Finset.sum_smul]
      rw [Finset.sum_comm, Finset.smul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hcy i, smul_add, Finset.smul_sum, smul_comm (v i b)]
      simp only [mul_smul]
    rw [h1, smul_add, add_sub_right_comm, ← Finset.sum_sub_distrib, add_left_inj, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← sub_smul, ht, mul_smul]

end GlobalTheory.ZCount
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsIsotropicGroupLatticeClassRepresentativesStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isotropic_group_lattice_class_representatives : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (n : ℕ) (Λ : GenLat E n) (N : ℕ), Λ.Unimod → 0 < N → Ideal.span {(N : 𝓞 E)} • stdLat E n ≤ Λ.La → ∃ zz : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → Dw.La, (∀ i₀, (∀ (mu : Matrix (Fin n) (Fin n) E), (∀ v ∈ Λ.La, mu.mulVec v ∈ stdLat E n) → ∀ cm : Fin n → Fin n → 𝓞 E, (∀ i j, (cm i j : E) = (N : E) * mu i j) → ∀ i, Dw.ModN (N ^ 2) (∑ j, cm i j • zz i₀ j))) ∧ (∀ i i', (∀ b, Dw.ModN (N ^ 2) (zz i b - zz i' b)) → i = i') ∧ ∀ a : Fin n → Dw.La, (∀ (mu : Matrix (Fin n) (Fin n) E), (∀ v ∈ Λ.La, mu.mulVec v ∈ stdLat E n) → ∀ cm : Fin n → Fin n → 𝓞 E, (∀ i j, (cm i j : E) = (N : E) * mu i j) → ∀ i, Dw.ModN (N ^ 2) (∑ j, cm i j • a j)) → ∃ i, ∀ b, Dw.ModN (N ^ 2) (a b - zz i b) := by
  first | exact @GlobalTheory.ZCount.exists_class_representatives | exact GlobalTheory.ZCount.exists_class_representatives | (intros; apply GlobalTheory.ZCount.exists_class_representatives <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.UniversalWeilPairingPullbackExistsUnique
section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.UniversalWeilPairingPullbackExistsUnique
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UnivPairing

theorem weilIs_pow_eq_one (hW : WeilSt) {S : Scheme.{0}} [IsLocallyNoetherian S] (P : PolAV S) (k : ℕ)
    {T : Over S} (x y : T ⟶ P.A) (hx : x ^ k = 1) (hy : y ^ k = 1) (c : Γ(T.left, ⊤)ˣ)
    (hc : WeilIs P.A P.L k x y c) : c ^ k = 1 := by
  obtain ⟨hex, hmul, -, -⟩ := hW S P k T
  obtain ⟨c₁, hc₁, hu⟩ := hex 1 y (one_pow k) hy
  have h₂ := hmul 1 1 y c₁ c₁ hc₁ hc₁
  rw [_root_.mul_one] at h₂
  obtain rfl : c₁ = 1 := mul_eq_left.1 (hu _ h₂)
  have hpow : ∀ j : ℕ, WeilIs P.A P.L k (x ^ j) y (c ^ j) := fun j => by
    induction j with
    | zero => rw [pow_zero, pow_zero]; exact hc₁
    | succ j ih => rw [pow_succ, pow_succ]; exact hmul _ _ _ _ _ ih hc
  have h := hpow k
  rw [hx] at h
  exact hu _ h

theorem isNilpotent_of_geometric {B : Type} [CommRing B] {b : B}
    (h : ∀ (K : Type) [Field K] [IsAlgClosed K] (χ : B →+* K), χ b = 0) : IsNilpotent b := by
  refine nilpotent_iff_mem_prime.2 fun J hJ => ?_
  have e := h (AlgebraicClosure (FractionRing (B ⧸ J)))
    (((algebraMap (FractionRing (B ⧸ J)) _).comp (algebraMap (B ⧸ J) (FractionRing (B ⧸ J)))).comp
      (Ideal.Quotient.mk J))
  rw [RingHom.comp_apply, RingHom.comp_apply, map_eq_zero,
    map_eq_zero_iff _ (IsFractionRing.injective (B ⧸ J) _)] at e
  exact Ideal.Quotient.eq_zero_iff_mem.1 e

theorem eq_one_of_geometric (B : Type) [CommRing B] (u : B) (k : ℕ) (hk : IsUnit (k : B)) (hu : u ^ k = 1)
    (h : ∀ (K : Type) [Field K] [IsAlgClosed K] (χ : B →+* K), χ u = 1) : u = 1 := by
  have hn : IsNilpotent ((∑ i ∈ Finset.range k, u ^ i) - k) := isNilpotent_of_geometric fun K _ _ χ => by
    simp [h K χ]
  have hs : IsUnit (∑ i ∈ Finset.range k, u ^ i) := by
    have := hn.isUnit_add_right_of_commute hk (Commute.all _ _)
    rwa [sub_add_cancel] at this
  have e := geom_sum_mul u k
  rw [hu, sub_self] at e
  exact sub_eq_zero.1 (hs.mul_right_eq_zero.1 e)

theorem weilIs_univ_pull_exists_unique : Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (N : ℕ), 0 < N → (∀ (T T' : Over Xo.X) (h : T' ⟶ T) (x y : T ⟶ Xo.univ.t.G) (e : Γ(T.left, ⊤)ˣ), x ^ (N ^ 2) = 1 → y ^ (N ^ 2) = 1 → WeilIs Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) x y e → WeilIs Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (h ≫ x) (h ≫ y) (Units.map h.left.appTop.hom.toMonoidHom e)) ∧ (∀ (T : Over Xo.X) (x y : T ⟶ Xo.univ.t.G), x ^ (N ^ 2) = 1 → y ^ (N ^ 2) = 1 → ∃ e : Γ(T.left, ⊤)ˣ, WeilIs Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) x y e ∧ e ^ (N ^ 2) = 1 ∧ ∀ e', WeilIs Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) x y e' → e' = e) ∧ ∀ (B : Type) [CommRing B] (u : B) (k : ℕ), IsUnit (k : B) → u ^ k = 1 → (∀ (K : Type) [Field K] [IsAlgClosed K] (χ : B →+* K), χ u = 1) → u = 1 := by
  intro hL E _ _ _ H Dw l Xo N _
  have := UnivPol.isLocallyNoetherian Xo
  refine ⟨fun T T' h x y e _ _ he => ?_, fun T x y hx hy => ?_, eq_one_of_geometric⟩
  · exact CommPairing.weilIs_pull hL.globalFns (UnivPol.pol Xo).isAb (UnivPol.pol Xo).isLB h he
  · rw [← Nat.cast_pow]
    obtain ⟨e, he, hu⟩ := (hL.weil Xo.X (UnivPol.pol Xo) (N ^ 2) T).1 x y hx hy
    exact ⟨e, he, weilIs_pow_eq_one hL.weil (UnivPol.pol Xo) (N ^ 2) x y hx hy e he, hu⟩

end GlobalTheory.UnivPairing
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.UniversalWeilPairingPullbackExistsUniqueStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.universal_weilPairing_pullback_exists_unique : Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (N : ℕ), 0 < N → (∀ (T T' : Over Xo.X) (h : T' ⟶ T) (x y : T ⟶ Xo.univ.t.G) (e : Γ(T.left, ⊤)ˣ), x ^ (N ^ 2) = 1 → y ^ (N ^ 2) = 1 → WeilIs Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) x y e → WeilIs Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (h ≫ x) (h ≫ y) (Units.map h.left.appTop.hom.toMonoidHom e)) ∧ (∀ (T : Over Xo.X) (x y : T ⟶ Xo.univ.t.G), x ^ (N ^ 2) = 1 → y ^ (N ^ 2) = 1 → ∃ e : Γ(T.left, ⊤)ˣ, WeilIs Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) x y e ∧ e ^ (N ^ 2) = 1 ∧ ∀ e', WeilIs Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) x y e' → e' = e) ∧ ∀ (B : Type) [CommRing B] (u : B) (k : ℕ), IsUnit (k : B) → u ^ k = 1 → (∀ (K : Type) [Field K] [IsAlgClosed K] (χ : B →+* K), χ u = 1) → u = 1 := by
  first | exact @GlobalTheory.UnivPairing.weilIs_univ_pull_exists_unique | exact GlobalTheory.UnivPairing.weilIs_univ_pull_exists_unique | (intros; apply GlobalTheory.UnivPairing.weilIs_univ_pull_exists_unique <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFlatUniversalTorsionTuple
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace TorsTuple

theorem exists_power {X : Scheme.{0}} (Q : Over X) [IsAffineHom Q.hom] [Flat Q.hom] (J : Type) [Finite J] :
    ∃ (R : Over X) (p : J → (R ⟶ Q)), IsAffineHom R.hom ∧ Flat R.hom ∧
      ∀ (T : Over X) (u : J → (T ⟶ Q)), ∃ v : T ⟶ R, ∀ i, v ≫ p i = u i := by

  have key : ∀ n : ℕ, ∃ (R : Over X) (p : Fin n → (R ⟶ Q)), IsAffineHom R.hom ∧ Flat R.hom ∧
      ∀ (T : Over X) (u : Fin n → (T ⟶ Q)), ∃ v : T ⟶ R, ∀ i, v ≫ p i = u i := by
    intro n
    induction n with
    | zero =>
      refine ⟨Over.mk (𝟙 X), fun i => i.elim0, ?_, ?_, fun T u => ⟨Over.homMk T.hom (by simp), fun i => i.elim0⟩⟩
      · show IsAffineHom (𝟙 X)
        infer_instance
      · show Flat (𝟙 X)
        infer_instance
    | succ n ih =>
      obtain ⟨R, p, hRa, hRf, hR⟩ := ih
      have ha : IsAffineHom (pullback.fst R.hom Q.hom) :=
        MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsAffineHom)
          (IsPullback.of_hasPullback R.hom Q.hom).flip ‹_›
      let R' : Over X := Over.mk (pullback.fst R.hom Q.hom ≫ R.hom)
      let a : R' ⟶ Q := Over.homMk (pullback.snd R.hom Q.hom) pullback.condition.symm
      let b : R' ⟶ R := Over.homMk (pullback.fst R.hom Q.hom) rfl
      refine ⟨R', Fin.cons (α := fun _ => R' ⟶ Q) a (fun i => b ≫ p i), ?_, ?_, ?_⟩
      · show IsAffineHom (pullback.fst R.hom Q.hom ≫ R.hom)
        infer_instance
      · show Flat (pullback.fst R.hom Q.hom ≫ R.hom)
        infer_instance
      · intro T u
        obtain ⟨v, hv⟩ := hR T (fun i => u i.succ)
        have hc : v.left ≫ R.hom = (u 0).left ≫ Q.hom := by rw [Over.w v, Over.w (u 0)]
        refine ⟨Over.homMk (pullback.lift v.left (u 0).left hc) (by
          change _ ≫ pullback.fst R.hom Q.hom ≫ R.hom = _
          rw [pullback.lift_fst_assoc, Over.w v]), ?_⟩
        refine Fin.cases ?_ (fun i => ?_)
        · apply Over.OverMorphism.ext
          simp only [a, Fin.cons_zero, Over.comp_left, Over.homMk_left]
          exact pullback.lift_snd _ _ _
        · apply Over.OverMorphism.ext
          simp only [b, Fin.cons_succ, Over.comp_left, Over.homMk_left, ← hv i]
          rw [pullback.lift_fst_assoc]
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin J
  obtain ⟨R, p, ha, hf, hu⟩ := key n
  refine ⟨R, fun j => p (e j), ha, hf, fun T u => ?_⟩
  obtain ⟨v, hv⟩ := hu T (fun i => u (e.symm i))
  exact ⟨v, fun j => by simpa using hv (e j)⟩

theorem exists_point {X : Scheme.{0}} (R : Over X) [IsAffineHom R.hom] [Flat R.hom] (S : Type) [CommRing S]
    (x0 : Sp S ⟶ X) :
    ∃ (B : Type) (_ : CommRing B) (φ : S →+* B) (w : Over.mk (spMap φ ≫ x0) ⟶ R), φ.Flat ∧
      ∀ (T : Type) [CommRing T] (ψ : S →+* T) (u : Over.mk (spMap ψ ≫ x0) ⟶ R),
        ∃ χ : B →+* T, χ.comp φ = ψ ∧ u.left = spMap χ ≫ w.left := by

  have : IsAffine (pullback x0 R.hom) := inferInstance
  let e := (pullback x0 R.hom).isoSpec
  obtain ⟨φ, hφ⟩ : ∃ φ : S →+* Γ(pullback x0 R.hom, ⊤), spMap φ = e.inv ≫ pullback.fst x0 R.hom :=
    ⟨_, Spec.map_preimage _⟩
  have hw : (e.inv ≫ pullback.snd x0 R.hom) ≫ R.hom = (Over.mk (spMap φ ≫ x0)).hom := by
    simp [hφ, pullback.condition]
  refine ⟨Γ(pullback x0 R.hom, ⊤), inferInstance, φ, Over.homMk (e.inv ≫ pullback.snd x0 R.hom) hw, ?_, ?_⟩
  · have hfl : Flat (spMap φ) := by
      rw [hφ]
      infer_instance
    exact (HasRingHomProperty.Spec_iff (P := @Flat)).mp hfl
  · intro T _ ψ u
    let g : Sp T ⟶ pullback x0 R.hom := pullback.lift (spMap ψ) u.left (Over.w u).symm
    obtain ⟨χ, hχ⟩ : ∃ χ : Γ(pullback x0 R.hom, ⊤) →+* T, spMap χ = g ≫ e.hom := ⟨_, Spec.map_preimage _⟩
    refine ⟨χ, ?_, ?_⟩
    · have h1 : spMap (χ.comp φ) = spMap ψ := by
        change Spec.map (CommRingCat.ofHom φ ≫ CommRingCat.ofHom χ) = _
        rw [Spec.map_comp]
        change spMap χ ≫ spMap φ = _
        rw [hχ, hφ, Category.assoc, Iso.hom_inv_id_assoc]
        exact pullback.lift_fst _ _ _
      exact congrArg CommRingCat.Hom.hom (Spec.map_injective h1)
    · rw [hχ]
      change u.left = (g ≫ e.hom) ≫ e.inv ≫ pullback.snd x0 R.hom
      rw [Category.assoc, Iso.hom_inv_id_assoc]
      exact (pullback.lift_snd _ _ _).symm

theorem exists_kernel {X : Scheme.{0}} (A : Over X) [GrpObj A] (k : ℕ) [IsFinite (mulA A k).left]
    [Flat (mulA A k).left] :
    ∃ (Q : Over X) (j : Q ⟶ A), IsAffineHom Q.hom ∧ Flat Q.hom ∧ j ^ k = 1 ∧
      ∀ (T : Over X) (u : T ⟶ A), u ^ k = 1 → ∃ v : T ⟶ Q, v ≫ j = u := by

  have hm : ∀ {T : Over X} (u : T ⟶ A), u ^ k = u ≫ mulA A k := by
    intro T u
    rw [show mulA A k = 𝟙 A ^ k from rfl, MonObj.comp_pow, Category.comp_id]

  let Q : Over X := Over.mk (pullback.snd (mulA A k).left (MonObj.one : 𝟙_ (Over X) ⟶ A).left : _ ⟶ X)
  have hjw : pullback.fst (mulA A k).left (MonObj.one : 𝟙_ (Over X) ⟶ A).left ≫ A.hom = Q.hom := by
    rw [← Over.w (mulA A k), pullback.condition_assoc, Over.w]
    exact Category.comp_id _
  let j : Q ⟶ A := Over.homMk (pullback.fst _ _) hjw
  refine ⟨Q, j, ?_, ?_, ?_, ?_⟩
  · show IsAffineHom (pullback.snd (mulA A k).left (MonObj.one : 𝟙_ (Over X) ⟶ A).left)
    infer_instance
  · show Flat (pullback.snd (mulA A k).left (MonObj.one : 𝟙_ (Over X) ⟶ A).left)
    infer_instance
  · rw [hm j]
    apply Over.OverMorphism.ext
    show (j ≫ mulA A k).left = (toUnit Q ≫ MonObj.one).left
    rw [Over.comp_left, Over.comp_left]
    exact pullback.condition
  · intro T u hu
    have h0 : u ≫ mulA A k = toUnit T ≫ MonObj.one := by
      rw [← hm u, hu]
      rfl
    have h1 : u.left ≫ (mulA A k).left = T.hom ≫ (MonObj.one : 𝟙_ (Over X) ⟶ A).left := by
      have h2 := congrArg (fun f => f.left) h0
      simp only [Over.comp_left] at h2
      exact h2
    refine ⟨Over.homMk (pullback.lift u.left T.hom h1) (pullback.lift_snd _ _ _), ?_⟩
    apply Over.OverMorphism.ext
    rw [Over.comp_left]
    exact pullback.lift_fst _ _ _

theorem exists_tuple {X : Scheme.{0}} (A : Over X) [GrpObj A] (k : ℕ) [IsFinite (mulA A k).left]
    [Flat (mulA A k).left] (S : Type) [CommRing S] (x0 : Sp S ⟶ X) (J : Type) [Finite J] :
    ∃ (B : Type) (_ : CommRing B) (φ : S →+* B) (w : J → (Over.mk (spMap φ ≫ x0) ⟶ A)), φ.Flat ∧
      (∀ i, w i ^ k = 1) ∧ ∀ (T : Type) [CommRing T] (ψ : S →+* T) (u : J → (Over.mk (spMap ψ ≫ x0) ⟶ A)),
        (∀ i, u i ^ k = 1) → ∃ χ : B →+* T, χ.comp φ = ψ ∧ ∀ i, (u i).left = spMap χ ≫ (w i).left := by
  obtain ⟨Q, j, hQa, hQf, hj, hQ⟩ := exists_kernel A k
  have := hQa
  have := hQf
  obtain ⟨R, p, hRa, hRf, hR⟩ := exists_power Q J
  have := hRa
  have := hRf
  obtain ⟨B, iB, φ, w, hφ, hw⟩ := exists_point R S x0
  refine ⟨B, iB, φ, fun i => w ≫ p i ≫ j, hφ, fun i => ?_, ?_⟩
  · show (w ≫ p i ≫ j) ^ k = 1
    rw [← Category.assoc, ← MonObj.comp_pow, hj, MonObj.comp_one]
  · intro T _ ψ u hu
    choose v hv using fun i => hQ _ (u i) (hu i)
    obtain ⟨v', hv'⟩ := hR _ v
    obtain ⟨χ, hχ, hχw⟩ := hw T ψ v'
    refine ⟨χ, hχ, fun i => ?_⟩
    rw [← hv i, ← hv' i]
    simp [hχw]

end TorsTuple

theorem exists_flat_universal_torsion_tuple :
    Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S : Type) [CommRing S] (x0 : Sp S ⟶ Xo.X) (k : ℕ), 0 < k → ∀ (J : Type) [Fintype J], ∃ (B : Type) (_ : CommRing B) (φ : S →+* B) (w : J → (ptO Xo (spMap φ ≫ x0) ⟶ Xo.univ.t.G)), φ.Flat ∧ (∀ i, w i ^ k = 1) ∧ ∀ (T : Type) [CommRing T] (ψ : S →+* T) (u : J → (ptO Xo (spMap ψ ≫ x0) ⟶ Xo.univ.t.G)), (∀ i, u i ^ k = 1) → ∃ χ : B →+* T, χ.comp φ = ψ ∧ ∀ i, (u i).left = spMap χ ≫ (w i).left := by
  intro hL E _ _ _ H Dw l Xo S _ x0 k hk J _

  have hN := hL.mulN
  unfold MulNSt at hN
  obtain ⟨hloc, -⟩ := moduli_univ_polAV E H Dw l Xo
  obtain ⟨hfin, hfl, -⟩ := hN Xo.X (UnivPol.pol Xo) k hk
  have hfin' : IsFinite (mulA Xo.univ.t.G k).left := hfin
  have hfl' : Flat (mulA Xo.univ.t.G k).left := hfl
  exact TorsTuple.exists_tuple Xo.univ.t.G k S x0 J

end GlobalTheory
end
end
