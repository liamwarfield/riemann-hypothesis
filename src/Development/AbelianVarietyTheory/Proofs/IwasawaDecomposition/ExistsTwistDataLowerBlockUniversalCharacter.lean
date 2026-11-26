module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.YsOfFi
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PlacesOverRealSubfieldSplit

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDefiniteLevelRecharacterised
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDefiniteLevelRecharacterised
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK HkIdx)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

noncomputable section

namespace GlobalTheory.LevelRechar

open ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.LevGChar

section Loc
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {R : Type} [CommRing R]
  {v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))}


open Classical in
def dU (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (red : v.adicCompletionIntegers (maximalRealSubfield L) →+* R)
    (r : ℕ) (x : Matrix (Fin n) (Fin n) (v.adicCompletion (maximalRealSubfield L))) : Rˣ :=
  if h : IsUnit (red (NX.intLift v (NX.detT r x))) then h.unit else 1

theorem isUnit_red (red : v.adicCompletionIntegers (maximalRealSubfield L) →+* R) (r : ℕ)
    (x : Matrix (Fin n) (Fin n) (v.adicCompletion (maximalRealSubfield L))) (hdx : Valued.v (NX.detT r x) = 1) :
    IsUnit (red (NX.intLift v (NX.detT r x))) := by
  have hix : NX.detT r x ∈ v.adicCompletionIntegers (maximalRealSubfield L) := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, hdx]
  have ex : NX.intLift v (NX.detT r x) = ⟨_, hix⟩ := by rw [NX.intLift, dite_eq_left hix]
  rw [ex]; exact (isUnit_int hdx hix).map red

theorem dU_eq (red : v.adicCompletionIntegers (maximalRealSubfield L) →+* R) (r : ℕ)
    (x : Matrix (Fin n) (Fin n) (v.adicCompletion (maximalRealSubfield L)))
    (h : IsUnit (red (NX.intLift v (NX.detT r x)))) : dU v red r x = h.unit := by
  unfold dU
  rw [dite_eq_left h]

theorem dU_mul (red : v.adicCompletionIntegers (maximalRealSubfield L) →+* R)
    (hred : ∀ z : v.adicCompletionIntegers (maximalRealSubfield L),
      Valued.v (z : v.adicCompletion (maximalRealSubfield L)) < 1 → red z = 0) (r : ℕ)
    (x y : Matrix (Fin n) (Fin n) (v.adicCompletion (maximalRealSubfield L)))
    (hx : NX.InParah v r x) (hy : NX.InParah v r y)
    (hdx : Valued.v (NX.detT r x) = 1) (hdy : Valued.v (NX.detT r y) = 1) :
    dU v red r (x * y) = dU v red r x * dU v red r y := by
  have hix : NX.detT r x ∈ v.adicCompletionIntegers (maximalRealSubfield L) := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, hdx]
  have hiy : NX.detT r y ∈ v.adicCompletionIntegers (maximalRealSubfield L) := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, hdy]
  have ex : NX.intLift v (NX.detT r x) = ⟨_, hix⟩ := by rw [NX.intLift, dite_eq_left hix]
  have ey : NX.intLift v (NX.detT r y) = ⟨_, hiy⟩ := by rw [NX.intLift, dite_eq_left hiy]
  have hxy : red (NX.intLift v (NX.detT r (x * y))) =
      red (NX.intLift v (NX.detT r x)) * red (NX.intLift v (NX.detT r y)) := by
    rw [ex, ey, ← map_mul]
    exact red_intLift red hred _ (by simpa using i_detT_mul v r x y hx hy)
  have hux := isUnit_red red r x hdx
  have huy := isUnit_red red r y hdy
  have huxy : IsUnit (red (NX.intLift v (NX.detT r (x * y)))) := by rw [hxy]; exact hux.mul huy
  rw [dU_eq red r _ hux, dU_eq red r _ huy, dU_eq red r _ huxy]
  exact Units.ext (by simp [hxy])

theorem dU_one (red : v.adicCompletionIntegers (maximalRealSubfield L) →+* R)
    (hred : ∀ z : v.adicCompletionIntegers (maximalRealSubfield L),
      Valued.v (z : v.adicCompletion (maximalRealSubfield L)) < 1 → red z = 0) (r : ℕ)
    (x : Matrix (Fin n) (Fin n) (v.adicCompletion (maximalRealSubfield L)))
    (hx : ∀ a b, Valued.v (x a b - (1 : Matrix (Fin n) (Fin n) (v.adicCompletion (maximalRealSubfield L))) a b) < 1) :
    dU v red r x = 1 := by
  have hd : red (NX.intLift v (NX.detT r x)) = 1 := by
    rw [red_intLift red hred 1 (by simpa using i_detT_cong v r x hx), map_one]
  have hu : IsUnit (red (NX.intLift v (NX.detT r x))) := by rw [hd]; exact isUnit_one
  rw [dU_eq red r x hu]
  exact Units.ext (by rw [IsUnit.unit_spec, hd]; rfl)

theorem exists_cong {ι : Type} [Fintype ι] (s : ι → SplitPlace L) : ∃ N : ℕ, 0 < N ∧ ∀ κ : GAf L n, NG.Cong L n N κ →
    ∀ t a b, Valued.v (NX.locM (s t) κ a b -
      (1 : Matrix (Fin n) (Fin n) ((s t).v.adicCompletion (maximalRealSubfield L))) a b) < 1 := by
  have hpos : ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)), 0 < Ideal.absNorm v.asIdeal := fun v =>
    Nat.pos_of_ne_zero fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.mp h)
  have hmem : ∀ (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (N : ℕ), Ideal.absNorm v.asIdeal ∣ N →
      (N : 𝓞 (maximalRealSubfield L)) ∈ v.asIdeal := fun v N h =>
    Ideal.mem_of_dvd _ (Nat.cast_dvd_cast h) (Ideal.absNorm_mem _)
  refine ⟨∏ t, Ideal.absNorm (s t).v.asIdeal, Finset.prod_pos fun _ _ => hpos _, fun κ hκ t => ?_⟩
  have hd : Ideal.absNorm (s t).v.asIdeal ∣ ∏ t, Ideal.absNorm (s t).v.asIdeal :=
    Finset.dvd_prod_of_mem (fun t => Ideal.absNorm (s t).v.asIdeal) (Finset.mem_univ t)
  exact locM_cong (s t) (hmem _ _ hd) κ hκ

end Loc

theorem mul_ringHom_units_ratio {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (p : B) (a a' : Aˣ) :
    p * f (a' : A) = p * f (a : A) * f ((a' * a⁻¹ : Aˣ) : A) := by
  rw [mul_assoc, ← map_mul, ← Units.val_mul, mul_comm a', mul_inv_cancel_left]

theorem exists_mul_hom {G H : Type} [Group G] [CommGroup H] {J : Subgroup G} (χ : J →* H) (c : G → H)
    (hc : ∀ κ κ' : J, c ((κ * κ' : J) : G) = c κ * c κ') : ∃ χ' : J →* H, ∀ κ : J, χ' κ = χ κ * c κ :=
  ⟨MonoidHom.mk' (fun κ => χ κ * c κ) (fun κ κ' => by rw [hc, map_mul, mul_mul_mul_comm]), fun _ => rfl⟩

theorem gVal_rechar (D : D7) (i : D.ntw.Tw) (k : ℕ) (b : Bool) (kv : Σ k : Fin 2, D.nd.PlG k) (s : SplitPlace D.host.E)
    (red : s.v.adicCompletionIntegers (maximalRealSubfield D.host.E) →+* ZMod (D.host.g kv.1))
    (τ τ' : (ZMod (D.host.g kv.1))ˣ →* (FractionRing (D.ntw.O i))ˣ)
    (x : Matrix (Fin D.R.nV) (Fin D.R.nV) (s.v.adicCompletion (maximalRealSubfield D.host.E)))
    (hu : IsUnit (red (NX.intLift s.v (NX.detT D.R.r x)))) :
    NX.gVal D i k b kv s red τ' x = NX.gVal D i k b kv s red τ x *
      NX.toKk D i k (((τ' (dU s.v red D.R.r x) * (τ (dU s.v red D.R.r x))⁻¹ : (FractionRing (D.ntw.O i))ˣ)) :
        FractionRing (D.ntw.O i)) := by
  unfold NX.gVal
  rw [dite_eq_left hu, dite_eq_left hu, dU_eq red _ x hu]
  exact mul_ringHom_units_ratio _ _ _ _

theorem exists_rechar : ∀ (D : D7) (i : D.ntw.Tw) (j : ℕ) (b : Bool) (k : ℕ) (Q : Finset (PlE D.host)) (ψ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ) (e : ℤ) (W₀ : Type) [AddCommGroup W₀] [Module (FractionRing (D.ntw.O i)) W₀] (ρ₀ : Representation (FractionRing (D.ntw.O i)) (ReciprocityTheory.Aut.GQ D.host.E D.R.nV) W₀) (τ τ' : ∀ kv : (Σ kk : Fin 2, D.nd.PlG kk), (ZMod (D.host.g kv.1))ˣ →* (FractionRing (D.ntw.O i))ˣ) (M : NX.MtVReal D i j b k Q ψ e W₀ ρ₀ τ), ∃ χ' : M.J →* (NX.Kk D i k)ˣ, (∃ N : ℕ, 0 < N ∧ ∀ κ, NG.Cong D.host.E D.R.nV N κ → ∃ h : κ ∈ M.J, χ' ⟨κ, h⟩ = 1) ∧ NX.HypOutsideF M.J χ' (NX.badV D i Q) ∧ ∀ κ (h : κ ∈ M.J), ((χ' ⟨κ, h⟩ : (NX.Kk D i k)ˣ) : NX.Kk D i k) = (∏ kv : (Σ kk : Fin 2, D.nd.PlG kk), NX.gVal D i k b kv (M.sp (NX.pG D kv)) (M.redG kv) (τ' kv) (NX.locM (M.sp (NX.pG D kv)) κ)) * (∏ P ∈ M.QP, NX.ofOk D i k (NX.tameVal ψ P e (NX.resRep (M.sp P) P (NX.detT D.R.r (NX.locM (M.sp P) κ)))).1) * (∏ P ∈ M.DP, NX.ofO0 D i k (NX.tameVal (D.ntw.delta i) P (if b then e else -e) (NX.resRep (M.sp P) P (NX.detT D.R.r (NX.locM (M.sp P) κ)))).1) := by
  intro D i j b k Q ψ e W₀ _ _ ρ₀ τ τ' M
  classical
  have hred : ∀ kv : (Σ kk : Fin 2, D.nd.PlG kk),
      ∀ z : (M.sp (NX.pG D kv)).v.adicCompletionIntegers (maximalRealSubfield D.host.E),
      Valued.v (z : (M.sp (NX.pG D kv)).v.adicCompletion (maximalRealSubfield D.host.E)) < 1 → M.redG kv z = 0 := by
    intro kv z hz
    haveI : Fact (D.host.g kv.1).Prime := ⟨D.host.g_prime kv.1⟩
    exact i_red_zero _ (M.redG kv) z hz
  have hdet : ∀ (s : SplitPlace D.host.E) (κ : GAf D.host.E D.R.nV), κ ∈ Umax D.host.E D.R.nV →
      NX.InParah s.v D.R.r (NX.locM s κ) → Valued.v (NX.detT D.R.r (NX.locM s κ)) = 1 := fun s κ hU hp =>
    i_detT_one _ _ _ (NX.locM s κ⁻¹) (by rw [← locM_mul, mul_inv_cancel, locM_one]) (locM_int s (inv_mem hU)) hp
  obtain ⟨c, hc⟩ : ∃ c : GAf D.host.E D.R.nV → (NX.Kk D i k)ˣ, ∀ κ, c κ =
      ∏ kv : (Σ kk : Fin 2, D.nd.PlG kk), Units.map (NX.toKk D i k).toMonoidHom
        (τ' kv (dU (M.sp (NX.pG D kv)).v (M.redG kv) D.R.r (NX.locM (M.sp (NX.pG D kv)) κ)) *
          (τ kv (dU (M.sp (NX.pG D kv)).v (M.redG kv) D.R.r (NX.locM (M.sp (NX.pG D kv)) κ)))⁻¹) := ⟨_, fun _ => rfl⟩
  have hmul : ∀ κ κ' : M.J, c ((κ * κ' : M.J) : GAf D.host.E D.R.nV) = c κ * c κ' := by
    rintro ⟨κ, hκ⟩ ⟨κ', hκ'⟩
    obtain ⟨h1, h2, -⟩ := (M.J_mem κ).1 hκ
    obtain ⟨h1', h2', -⟩ := (M.J_mem κ').1 hκ'
    show c (κ * κ') = c κ * c κ'
    rw [hc, hc, hc, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun kv _ => ?_
    rw [locM_mul, dU_mul _ (hred kv) _ _ _ (h2 kv).1 (h2' kv).1 (hdet _ _ h1 (h2 kv).1) (hdet _ _ h1' (h2' kv).1),
      ← MonoidHom.map_mul, map_mul (τ kv), map_mul (τ' kv), mul_inv, mul_mul_mul_comm]
  have hone : ∀ κ : GAf D.host.E D.R.nV,
      (∀ kv a b, Valued.v (NX.locM (M.sp (NX.pG D kv)) κ a b - (1 : Matrix (Fin D.R.nV) (Fin D.R.nV)
        ((M.sp (NX.pG D kv)).v.adicCompletion (maximalRealSubfield D.host.E))) a b) < 1) → c κ = 1 := by
    intro κ hg
    rw [hc]
    refine Finset.prod_eq_one fun kv _ => ?_
    rw [dU_one _ (hred kv) _ _ (hg kv), map_one, map_one, inv_one, mul_one, map_one]
  obtain ⟨χ', hχ'⟩ := exists_mul_hom M.χ c hmul
  have hχ : ∀ κ (h : κ ∈ M.J), χ' ⟨κ, h⟩ = M.χ ⟨κ, h⟩ * c κ := fun κ h => hχ' ⟨κ, h⟩
  refine ⟨χ', ?_, ?_, ?_⟩
  · obtain ⟨N, hN, hJ⟩ := M.J_open
    obtain ⟨N', hN', hc'⟩ := exists_cong (n := D.R.nV)
      (fun kv : (Σ kk : Fin 2, D.nd.PlG kk) => M.sp (NX.pG D kv))
    refine ⟨N * N', Nat.mul_pos hN hN', fun κ hκ => ?_⟩
    obtain ⟨h, h1⟩ := hJ κ hκ.of_mul_left
    refine ⟨h, ?_⟩
    have h2 : c κ = 1 := hone κ (hc' κ hκ.of_mul_right)
    rw [hχ, h1, h2, one_mul]
  · intro κ hκ
    refine ⟨(M.hyp κ hκ).1, fun h => ?_⟩
    rw [hχ, (M.hyp κ hκ).2 h, one_mul]
    refine hone κ fun kv a b => ?_
    have hw := (M.sp (NX.pG D kv)).w_under
    rw [M.sp_w _ (Or.inr (Or.inr ⟨kv, rfl⟩))] at hw
    have hb : (M.sp (NX.pG D kv)).v ∈ NX.badV D i Q :=
      ⟨NX.pG D kv, hw, Or.inr (Or.inl ⟨kv.1, D.naut.plGw_over kv.1 kv.2⟩)⟩
    rw [locM_triv _ hκ hb]
    simp
  · intro κ h
    obtain ⟨h1, h2, -⟩ := (M.J_mem κ).1 h
    rw [hχ, Units.val_mul, M.chi_eq κ h, hc, Units.coe_prod,
      Finset.prod_congr rfl fun kv _ => gVal_rechar D i k b kv (M.sp (NX.pG D kv)) (M.redG kv) (τ kv) (τ' kv) _
        (isUnit_red _ _ _ (hdet _ _ h1 (h2 kv).1)), Finset.prod_mul_distrib]
    simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]
    ring

end GlobalTheory.LevelRechar
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDefiniteLevelRecharacterisedStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK HkIdx)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_definiteLevel_recharacterised : ∀ (D : D7) (i : D.ntw.Tw) (j : ℕ) (b : Bool) (k : ℕ) (Q : Finset (PlE D.host)) (ψ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ) (e : ℤ) (W₀ : Type) [AddCommGroup W₀] [Module (FractionRing (D.ntw.O i)) W₀] (ρ₀ : Representation (FractionRing (D.ntw.O i)) (ReciprocityTheory.Aut.GQ D.host.E D.R.nV) W₀) (τ τ' : ∀ kv : (Σ kk : Fin 2, D.nd.PlG kk), (ZMod (D.host.g kv.1))ˣ →* (FractionRing (D.ntw.O i))ˣ) (M : NX.MtVReal D i j b k Q ψ e W₀ ρ₀ τ), ∃ χ' : M.J →* (NX.Kk D i k)ˣ, (∃ N : ℕ, 0 < N ∧ ∀ κ, NG.Cong D.host.E D.R.nV N κ → ∃ h : κ ∈ M.J, χ' ⟨κ, h⟩ = 1) ∧ NX.HypOutsideF M.J χ' (NX.badV D i Q) ∧ ∀ κ (h : κ ∈ M.J), ((χ' ⟨κ, h⟩ : (NX.Kk D i k)ˣ) : NX.Kk D i k) = (∏ kv : (Σ kk : Fin 2, D.nd.PlG kk), NX.gVal D i k b kv (M.sp (NX.pG D kv)) (M.redG kv) (τ' kv) (NX.locM (M.sp (NX.pG D kv)) κ)) * (∏ P ∈ M.QP, NX.ofOk D i k (NX.tameVal ψ P e (NX.resRep (M.sp P) P (NX.detT D.R.r (NX.locM (M.sp P) κ)))).1) * (∏ P ∈ M.DP, NX.ofO0 D i k (NX.tameVal (D.ntw.delta i) P (if b then e else -e) (NX.resRep (M.sp P) P (NX.detT D.R.r (NX.locM (M.sp P) κ)))).1) := by
  first | exact @GlobalTheory.LevelRechar.exists_rechar | exact GlobalTheory.LevelRechar.exists_rechar | (intros; apply GlobalTheory.LevelRechar.exists_rechar <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTwistDataLowerBlockUniversalCharacter
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK HkIdx)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

noncomputable section

namespace GlobalTheory.TrueTau

variable {D : D7} (E : NExpTied D)
  (τ' : ∀ i : D.ntw.Tw, ℕ → Bool → ∀ kv : (Σ k : Fin 2, D.nd.PlG k), (ZMod (D.host.g kv.1))ˣ →* (FractionRing (D.ntw.O i))ˣ)

abbrev Cond (D : D7) (i : D.ntw.Tw) (j k : ℕ) (Q : Finset (PlE D.host))
    (ψ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ) : Type :=
  PLift (1 ≤ j ∧ j ≤ D.R.m ∧ NX.AdmTw D i k Q ψ)

abbrev mtAt (i : D.ntw.Tw) (j : ℕ) (b : Bool) (k : ℕ) (Q : Finset (PlE D.host))
    (ψ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ) (c : Cond D i j k Q ψ) :
    NX.MtVReal D i j b k Q ψ E.sgnT (E.Wt i j b) (E.rhoW i j b) (E.tauG i j b) :=
  E.mtV i j b k Q ψ c.down.1 c.down.2.1 c.down.2.2

def chiAt (i : D.ntw.Tw) (j : ℕ) (b : Bool) (k : ℕ) (Q : Finset (PlE D.host))
    (ψ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ) (c : Cond D i j k Q ψ) :
    (mtAt E i j b k Q ψ c).J →* (NX.Kk D i k)ˣ :=
  (GlobalTheory.T.exists_definiteLevel_recharacterised D i j b k Q ψ E.sgnT (E.Wt i j b) (E.rhoW i j b) (E.tauG i j b) (τ' i j b) (mtAt E i j b k Q ψ c)).choose

abbrev Sp (i : D.ntw.Tw) (j : ℕ) (b : Bool) (k : ℕ) (Q : Finset (PlE D.host))
    (ψ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ) (c : Cond D i j k Q ψ) : Type :=
  ↥(NX.TypeSpF D.host.E D.R.nV (NX.Kk D i k) (mtAt E i j b k Q ψ c).ρ (mtAt E i j b k Q ψ c).J (chiAt E τ' i j b k Q ψ c))

theorem fdSp (i : D.ntw.Tw) (j : ℕ) (b : Bool) (k : ℕ) (Q : Finset (PlE D.host))
    (ψ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ) (c : Cond D i j k Q ψ) :
    FiniteDimensional (NX.Kk D i k) (Sp E τ' i j b k Q ψ c) :=
  GlobalTheory.LevForms.typeSpF_finiteDimensional D.host.E D.R.nV (NX.Kk D i k) _ _ _
    (GlobalTheory.T.exists_definiteLevel_recharacterised D i j b k Q ψ E.sgnT (E.Wt i j b) (E.rhoW i j b) (E.tauG i j b) (τ' i j b)
      (mtAt E i j b k Q ψ c)).choose_spec.1

def MtN (i : D.ntw.Tw) (j : ℕ) (b : Bool) (k : ℕ) (Q : Finset (PlE D.host))
    (ψ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ) : Type :=
  (c : Cond D i j k Q ψ) → Sp E τ' i j b k Q ψ c

section Inst

variable (i : D.ntw.Tw) (j : ℕ) (b : Bool) (k : ℕ) (Q : Finset (PlE D.host))
    (ψ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ)

instance acgMtN : AddCommGroup (MtN E τ' i j b k Q ψ) :=
  inferInstanceAs (AddCommGroup ((c : Cond D i j k Q ψ) → Sp E τ' i j b k Q ψ c))

instance modKMtN : Module (FractionRing (D.ntw.Ok i k)) (MtN E τ' i j b k Q ψ) :=
  inferInstanceAs (Module (NX.Kk D i k) ((c : Cond D i j k Q ψ) → Sp E τ' i j b k Q ψ c))

instance modOMtN : Module (D.ntw.Ok i k) (MtN E τ' i j b k Q ψ) :=
  Module.compHom (MtN E τ' i j b k Q ψ) (algebraMap (D.ntw.Ok i k) (FractionRing (D.ntw.Ok i k)))

instance towMtN : IsScalarTower (D.ntw.Ok i k) (FractionRing (D.ntw.Ok i k)) (MtN E τ' i j b k Q ψ) :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

instance fdMtN : FiniteDimensional (FractionRing (D.ntw.Ok i k)) (MtN E τ' i j b k Q ψ) := by
  haveI := fdSp E τ' i j b k Q ψ
  haveI : Subsingleton (Cond D i j k Q ψ) := ⟨fun ⟨_⟩ ⟨_⟩ => rfl⟩
  haveI : Finite (Cond D i j k Q ψ) := Finite.of_subsingleton
  exact (Module.Finite.pi : Module.Finite (NX.Kk D i k) ((c : Cond D i j k Q ψ) → Sp E τ' i j b k Q ψ c))

def evalN (c : Cond D i j k Q ψ) : MtN E τ' i j b k Q ψ ≃ₗ[NX.Kk D i k] Sp E τ' i j b k Q ψ c where
  toFun f := f c
  invFun x := fun _ => x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv f := funext fun c' => by cases c; cases c'; rfl
  right_inv _ := rfl

end Inst

section AnyExport

variable (ex : NExp D.R D.host D.what₂ D.LL0 D.nd D.ntw)
  (h0 : ∀ g : G0g D.nd, D.what₂.embLL ((ex.eLL0 g : ↥D.LL0) : D.what₂.LL) = D.ntypes.e0.coeff g)
  (nth' : NTh D.R D.host D.what₂ D.LL0 D.nd D.ntw ex)

abbrev twX : TwNew D := ⟨D.ntw, ex, h0, nth', D.ntwbr, D.ntwbr_ind⟩

theorem gVal_twX (hps : ∀ (i : D.ntw.Tw) (b : Bool) (u : G0g D.nd), NX.psiUTot D i b u = NX.psiUTot (twX ex h0 nth').toD7 i b u)
    (i : D.ntw.Tw) (k : ℕ) (b : Bool) (kv : Σ k : Fin 2, D.nd.PlG k) (s : ReciprocityTheory.Aut.SplitPlace D.host.E)
    (red : s.v.adicCompletionIntegers (maximalRealSubfield D.host.E) →+* ZMod (D.host.g kv.1))
    (τ : (ZMod (D.host.g kv.1))ˣ →* (FractionRing (D.ntw.O i))ˣ)
    (x : Matrix (Fin D.R.nV) (Fin D.R.nV) (s.v.adicCompletion (maximalRealSubfield D.host.E))) :
    NX.gVal D i k b kv s red τ x = NX.gVal (twX ex h0 nth').toD7 i k b kv s red τ x := by
  unfold NX.gVal
  rw [hps]
  rfl

def realN (hps : ∀ (i : D.ntw.Tw) (b : Bool) (u : G0g D.nd), NX.psiUTot D i b u = NX.psiUTot (twX ex h0 nth').toD7 i b u)
    (i : D.ntw.Tw) (j : ℕ) (b : Bool) (k : ℕ) (Q : Finset (PlE D.host)) (ψ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ)
    (e : ℤ) (W₀ : Type) [AddCommGroup W₀] [mW : Module (FractionRing (D.ntw.O i)) W₀]
    (ρ₀ : Representation (FractionRing (D.ntw.O i)) (ReciprocityTheory.Aut.GQ D.host.E D.R.nV) W₀)
    (τ τ₁ : ∀ kv : (Σ kk : Fin 2, D.nd.PlG kk), (ZMod (D.host.g kv.1))ˣ →* (FractionRing (D.ntw.O i))ˣ)
    (M : NX.MtVReal D i j b k Q ψ e W₀ ρ₀ τ) (χ' : M.J →* (NX.Kk D i k)ˣ)
    (hχ : (∃ N : ℕ, 0 < N ∧ ∀ κ, NG.Cong D.host.E D.R.nV N κ → ∃ h : κ ∈ M.J, χ' ⟨κ, h⟩ = 1) ∧ NX.HypOutsideF M.J χ' (NX.badV D i Q) ∧ ∀ κ (h : κ ∈ M.J), ((χ' ⟨κ, h⟩ : (NX.Kk D i k)ˣ) : NX.Kk D i k) = (∏ kv : (Σ kk : Fin 2, D.nd.PlG kk), NX.gVal D i k b kv (M.sp (NX.pG D kv)) (M.redG kv) (τ₁ kv) (NX.locM (M.sp (NX.pG D kv)) κ)) * (∏ P ∈ M.QP, NX.ofOk D i k (NX.tameVal ψ P e (NX.resRep (M.sp P) P (NX.detT D.R.r (NX.locM (M.sp P) κ)))).1) * (∏ P ∈ M.DP, NX.ofO0 D i k (NX.tameVal (D.ntw.delta i) P (if b then e else -e) (NX.resRep (M.sp P) P (NX.detT D.R.r (NX.locM (M.sp P) κ)))).1))
    (r : ex.MtV i j b k Q ψ ≃ₗ[NX.Kk D i k] NX.TypeSpF D.host.E D.R.nV (NX.Kk D i k) M.ρ M.J χ') :
    @NX.MtVReal (twX ex h0 nth').toD7 i j b k Q ψ e W₀ _ mW ρ₀ τ₁ :=
  @NX.MtVReal.mk (twX ex h0 nth').toD7 i j b k Q ψ e W₀ _ mW ρ₀ τ₁ M.W M.acg M.mod M.fd M.ρ M.irr M.alg M.bc M.J χ' hχ.1 hχ.2.1
    M.QP M.QP_sub M.QP_cover M.QP_nconj M.DP M.DP_sub M.DP_cover M.DP_nconj M.sp M.sp_w M.redG M.J_mem
    (fun κ h => by
      have h1 := hχ.2.2 κ h
      simp only [gVal_twX ex h0 nth' hps] at h1
      exact h1) r

end AnyExport

section Generic

variable (Mt : ∀ (i : D.ntw.Tw) (_ : ℕ) (_ : Bool) (k : ℕ) (_ : Finset (PlE D.host))
    (_ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ), Type)
  [∀ i j b k Q ψ, AddCommGroup (Mt i j b k Q ψ)] [∀ i j b k Q ψ, Module (FractionRing (D.ntw.Ok i k)) (Mt i j b k Q ψ)]
  [∀ i j b k Q ψ, Module (D.ntw.Ok i k) (Mt i j b k Q ψ)]
  [∀ i j b k Q ψ, IsScalarTower (D.ntw.Ok i k) (FractionRing (D.ntw.Ok i k)) (Mt i j b k Q ψ)]
  [∀ i j b k Q ψ, FiniteDimensional (FractionRing (D.ntw.Ok i k)) (Mt i j b k Q ψ)]

def exN : NExp D.R D.host D.what₂ D.LL0 D.nd D.ntw :=
  { D.nexp with
    delU := fun i Q M => GlobalTheory.GalChar.delU D.host D.ntw.cc (D.ntw.l i) Q M
    delU_unr := fun i => (GlobalTheory.GalChar.universal_anticyclotomic_character_laws D.host D.ntw.cc (D.ntw.l i)).1
    delU_l := fun i => (GlobalTheory.GalChar.universal_anticyclotomic_character_laws D.host D.ntw.cc (D.ntw.l i)).2.1
    delU_anti := fun i => (GlobalTheory.GalChar.universal_anticyclotomic_character_laws D.host D.ntw.cc (D.ntw.l i)).2.2.1
    delU_open := fun i => (GlobalTheory.GalChar.universal_anticyclotomic_character_laws D.host D.ntw.cc (D.ntw.l i)).2.2.2.1
    delU_res := fun i => (GlobalTheory.GalChar.universal_anticyclotomic_character_laws D.host D.ntw.cc (D.ntw.l i)).2.2.2.2.1
    delU_conj := fun i => (GlobalTheory.GalChar.universal_anticyclotomic_character_laws D.host D.ntw.cc (D.ntw.l i)).2.2.2.2.2.1
    MtV := Mt
    acgMt := fun _ _ _ _ _ _ => inferInstance
    modMtK := fun _ _ _ _ _ _ => inferInstance
    modMtO := fun _ _ _ _ _ _ => inferInstance
    towMt := fun _ _ _ _ _ _ => inferInstance
    fdMt := fun _ _ _ _ _ _ => inferInstance
    MtLat := fun i j b k Q ψ =>
      Submodule.span (D.ntw.Ok i k) (Set.range (Module.finBasis (FractionRing (D.ntw.Ok i k)) (Mt i j b k Q ψ)))
    MtLat_fg := fun _ _ _ _ _ _ => Submodule.fg_span (Set.finite_range _)
    MtLat_span := fun i j b k Q ψ => by rw [Submodule.span_span_of_tower, (Module.finBasis _ _).span_eq]
    thP := fun _ _ _ _ _ _ => 0 }

def thN : NTh D.R D.host D.what₂ D.LL0 D.nd D.ntw (exN Mt) := { D.nth with }

variable (nth' : NTh D.R D.host D.what₂ D.LL0 D.nd D.ntw (exN Mt))

abbrev twN : TwNew D := twX (exN Mt) D.nStage_trivialCharacter_coeff_eq nth'

theorem twN_univ : GlobalTheory.UnivChar.IsUnivChar (twN Mt nth').toD7.nexp := fun _ _ _ => rfl

theorem twN_psi : ∀ (i : D.ntw.Tw) (b : Bool) (u : G0g D.nd), NX.psiUTot D i b u = NX.psiUTot (twN Mt nth').toD7 i b u := fun _ _ _ => rfl


set_option maxHeartbeats 4000000 in
def expN (hτ : ∀ i j b kv x, 1 ≤ j → j ≤ D.R.m → NX.pG D kv ∉ placesOver D.host.E (D.ntw.l i) →
      ((E.tauG i j b kv x : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)) =
        ((τ' i j b kv x : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)))
    (r : ∀ i j b k Q ψ (c : Cond D i j k Q ψ), Mt i j b k Q ψ ≃ₗ[NX.Kk D i k] Sp E τ' i j b k Q ψ c) :
    NExpTied (twN Mt nth').toD7 :=
  { E with
    acgWt := E.acgWt
    modWt := E.modWt
    fdWt := E.fdWt
    delU_cont := fun i Q M => (GlobalTheory.GalChar.universal_anticyclotomic_character_laws D.host D.ntw.cc (D.ntw.l i)).2.2.2.1 Q M
    delU_ine := fun i Q M hQ P hP =>
      GlobalTheory.UnivCharIne.delU_ine (twN Mt nth').toD7 (twN_univ Mt nth') i Q M hQ P hP
    tauG := τ'
    tau_galois_first_character := fun i j b kv x u h1 h2 hl hu => (hτ i j b kv x h1 h2 hl).symm.trans (E.tau_galois_first_character i j b kv x u h1 h2 hl hu)
    mtV := fun i j b k Q ψ h1 h2 h =>
      @realN D (exN Mt) D.nStage_trivialCharacter_coeff_eq nth' (twN_psi Mt nth') i j b k Q ψ E.sgnT (E.Wt i j b) (E.acgWt i j b) (E.modWt i j b) (E.rhoW i j b)
        (E.tauG i j b) (τ' i j b) (mtAt E i j b k Q ψ ⟨⟨h1, h2, h⟩⟩) (chiAt E τ' i j b k Q ψ ⟨⟨h1, h2, h⟩⟩)
        (@GlobalTheory.T.exists_definiteLevel_recharacterised D i j b k Q ψ E.sgnT (E.Wt i j b) (E.acgWt i j b) (E.modWt i j b) (E.rhoW i j b) (E.tauG i j b) (τ' i j b)
          (mtAt E i j b k Q ψ ⟨⟨h1, h2, h⟩⟩)).choose_spec
        (r i j b k Q ψ ⟨⟨h1, h2, h⟩⟩) }


set_option maxHeartbeats 4000000 in
def sideN {cf : CharFrame D} {Rw : RowSide D} {low : Finset ℕ}
    {Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host} {S : RatDat D.ntw}
    {hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)} {eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0}
    {θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ} (Bs : SideB D cf Rw low Pq S hL eig θ)
    (hτ : ∀ i j b kv x, 1 ≤ j → j ≤ D.R.m → NX.pG D kv ∉ placesOver D.host.E (D.ntw.l i) →
      ((Bs.exp.tauG i j b kv x : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)) =
        ((τ' i j b kv x : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)))
    (r : ∀ i j b k Q ψ (c : Cond D i j k Q ψ), Mt i j b k Q ψ ≃ₗ[NX.Kk D i k] Sp Bs.exp τ' i j b k Q ψ c) :
    SideB (twN Mt nth').toD7 ((twN Mt nth').cf cf) ((twN Mt nth').row Rw) low Pq ((twN Mt nth').rat S) hL eig θ :=
  { Bs with
    twF := { Bs.twF with }
    tw := { Bs.tw with }
    chiD := { Bs.chiD with }
    chi := { Bs.chi with }
    exp := expN Bs.exp τ' Mt nth' hτ r
    pq := fun i j b k Q ψ hj hj' hA => Bs.pq i j b k Q ψ hj hj' hA }

theorem twN_noOff (h : GlobalTheory.HeightCounting.SerCopy.NoOff D) : GlobalTheory.HeightCounting.SerCopy.NoOff (twN Mt nth').toD7 := fun i j b hn => h i j b hn

end Generic

theorem exists_trueTau : ∀ (D : D7) (cf : CharFrame D) (Rw : RowSide D) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf Rw low Pq S hL eig θ) (τ : ℕ → ∀ kv : (Σ k : Fin 2, D.nd.PlG k), (ZMod (D.host.g kv.1))ˣ →* (↥D.LL0)ˣ), (∀ i j b kv x, 1 ≤ j → j ≤ D.R.m → NX.pG D kv ∉ placesOver D.host.E (D.ntw.l i) → ((Bs.exp.tauG i j b kv x : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)) = sideEmb D.ntw i b ((τ j kv x : (↥D.LL0)ˣ) : ↥D.LL0)) → ∃ N : TwNew D, N.tw = D.ntw ∧ (GlobalTheory.HeightCounting.SerCopy.NoOff D → GlobalTheory.HeightCounting.SerCopy.NoOff N.toD7) ∧ GlobalTheory.UnivChar.IsUnivChar N.toD7.nexp ∧ ∃ Bs' : SideB N.toD7 (N.cf cf) (N.row Rw) low Pq (N.rat S) hL eig θ, TauTrue Bs'.exp := by
  intro D cf Rw low Pq S hL eig θ Bs τ hτ
  let τ' : ∀ i : D.ntw.Tw, ℕ → Bool → ∀ kv : (Σ k : Fin 2, D.nd.PlG k),
      (ZMod (D.host.g kv.1))ˣ →* (FractionRing (D.ntw.O i))ˣ :=
    fun i j b kv => (Units.map (GlobalTheory.SeriesTie.sideEmb D.ntw i b).toMonoidHom).comp (τ j kv)
  exact ⟨twN (MtN Bs.exp τ') (thN _), rfl, twN_noOff _ _, twN_univ _ _, sideN τ' _ _ Bs hτ (evalN Bs.exp τ'), τ,
    fun _ _ _ _ _ _ _ => rfl⟩

end GlobalTheory.TrueTau
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTwistDataLowerBlockUniversalCharacterStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK HkIdx)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_twistData_lowerBlock_universalCharacter : ∀ (D : D7) (cf : CharFrame D) (Rw : RowSide D) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf Rw low Pq S hL eig θ) (τ : ℕ → ∀ kv : (Σ k : Fin 2, D.nd.PlG k), (ZMod (D.host.g kv.1))ˣ →* (↥D.LL0)ˣ), (∀ i j b kv x, 1 ≤ j → j ≤ D.R.m → NX.pG D kv ∉ placesOver D.host.E (D.ntw.l i) → ((Bs.exp.tauG i j b kv x : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)) = sideEmb D.ntw i b ((τ j kv x : (↥D.LL0)ˣ) : ↥D.LL0)) → ∃ N : TwNew D, N.tw = D.ntw ∧ (GlobalTheory.HeightCounting.SerCopy.NoOff D → GlobalTheory.HeightCounting.SerCopy.NoOff N.toD7) ∧ GlobalTheory.UnivChar.IsUnivChar N.toD7.nexp ∧ ∃ Bs' : SideB N.toD7 (N.cf cf) (N.row Rw) low Pq (N.rat S) hL eig θ, TauTrue Bs'.exp := by
  first | exact @GlobalTheory.TrueTau.exists_trueTau | exact GlobalTheory.TrueTau.exists_trueTau | (intros; apply GlobalTheory.TrueTau.exists_trueTau <;> assumption)
end
