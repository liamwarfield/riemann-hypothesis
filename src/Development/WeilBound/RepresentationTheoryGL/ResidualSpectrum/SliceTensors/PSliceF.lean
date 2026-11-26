module

public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PSliceA
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PSliceB
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermFiniteOfSmaller

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PSliceD
noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.CompanionTheory.CTFin
open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm

namespace PositivityTheory.Rg.Rs.SliceClasses

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {N : ℕ}

theorem D_chart_left (F : GA E N → ℂ) (h g : GA E N) : chart (fun x => F (h * x)) g = chart F (h * g) := by
  funext x
  simp only [chart, mul_assoc]

def ltS (h : GA E N) : Sm E N →ₗ[ℂ] Sm E N where
  toFun F := ⟨fun g => F.1 (h * g), fun g => by rw [D_chart_left]; exact F.2 (h * g)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem ltS_apply (h : GA E N) (F : Sm E N) (g : GA E N) : (ltS h F).1 g = F.1 (h * g) := rfl

theorem ltS_act (h : GA E N) (o : Op E N) (F : Sm E N) : ltS h (act o F) = act o (ltS h F) := by
  cases o with
  | fin k =>
    refine Subtype.ext (funext fun g => ?_)
    change F.1 (h * g * finGL E N k) = F.1 (h * (g * finGL E N k))
    rw [mul_assoc]
  | cpt k =>
    refine Subtype.ext (funext fun g => ?_)
    change F.1 (h * g * _) = F.1 (h * (g * _))
    rw [mul_assoc]
  | lie X =>
    refine Subtype.ext (funext fun g => ?_)
    change lieD X F.1 (h * g) = lieD X (fun x => F.1 (h * x)) g
    simp only [lieD, D_chart_left]

theorem D_ct_smooth (r : ℕ) (φ : Sm E N) (hl : ∀ γ g, φ.1 (ratGL E N γ * g) = φ.1 g)
    (hlev : IsOpen {k | finRep E N k φ = φ}) :
    ∃ F : Sm E N, F.1 = An.ctn r φ.1 ∧ ∀ X, (lie E N X F).1 = An.ctn r (lie E N X φ).1 := by
  letI : MeasurableSpace (BlockIx N r → Ad E) := borel _
  have : BorelSpace (BlockIx N r → Ad E) := ⟨rfl⟩
  obtain ⟨μ, hμ, hD, hint⟩ := JDict.exists_normed E N r
  obtain ⟨F, h1, h2⟩ := GlobalTheory.CompanionTheory.CTSmooth.ct_smooth E N r φ hl hlev μ _ hμ hD
  have key : ∀ (f : GA E N → ℂ) g, ∫ x in unipFundamentalDomain E N r, f (unip x * g) ∂μ = An.ctn r f g := by
    intro f g
    rw [hint]
    simp only [An.ctn, constantTerm, GlobalTheory.CompanionTheory.CuspBridge.unipGL_eq_unip]
  exact ⟨F, funext fun g => (h1 g).trans (key _ g), fun X => funext fun g => (h2 X g).trans (key _ g)⟩


open Classical in
def ctSm (r : ℕ) (φ : Sm E N) : Sm E N := if h : An.ctn r φ.1 ∈ Sm E N then ⟨_, h⟩ else 0

theorem ctSm_val (r : ℕ) {φ : Sm E N} (hφ : IsAutForm φ) : (ctSm r φ).1 = An.ctn r φ.1 := by
  obtain ⟨F, hF, -⟩ := D_ct_smooth r φ hφ.left hφ.level
  have h : An.ctn r φ.1 ∈ Sm E N := hF ▸ F.2
  simp only [ctSm, dif_pos h]

theorem ctn_add (r : ℕ) {f g : GA E N → ℂ} (hf : Continuous f) (hg : Continuous g) :
    An.ctn r (f + g) = An.ctn r f + An.ctn r g := by
  funext x
  simp only [An.ctn, Pi.add_apply, constantTerm_add hf hg, mul_add]

theorem ctn_smul (r : ℕ) (c : ℂ) (f : GA E N → ℂ) : An.ctn r (c • f) = c • An.ctn r f := by
  funext x
  simp only [An.ctn, Pi.smul_apply, constantTerm_smul, smul_eq_mul]
  ring

theorem ctSm_act (r : ℕ) {φ : Sm E N} (hφ : IsAutForm φ) (o : Op E N) (hφ' : IsAutForm (act o φ)) :
    ctSm r (act o φ) = act o (ctSm r φ) := by
  obtain ⟨F, hF, hX⟩ := D_ct_smooth r φ hφ.left hφ.level
  have e : ctSm r φ = F := Subtype.ext ((ctSm_val r hφ).trans hF.symm)
  refine Subtype.ext ?_
  rw [ctSm_val r hφ', e]
  cases o with
  | fin k =>
    funext g
    change An.ctn r (fun x => φ.1 (x * finGL E N k)) g = F.1 (g * finGL E N k)
    rw [hF]
    simp only [An.ctn, constantTerm, mul_assoc]
  | cpt k =>
    funext g
    change An.ctn r (fun x => φ.1 (x * _)) g = F.1 (g * _)
    rw [hF]
    simp only [An.ctn, constantTerm, mul_assoc]
  | lie X => exact (hX X).symm

def Aop (N r : ℕ) (τs : Finset ℝ) (a : ℝ → ℂ) : Module.End ℂ (Sm E N) := ∑ t ∈ τs, a t • ltS (aT E N r t)

theorem Aop_apply (r : ℕ) (τs : Finset ℝ) (a : ℝ → ℂ) (F : Sm E N) (g : GA E N) :
    (Aop N r τs a F).1 g = ∑ t ∈ τs, a t * F.1 (aT E N r t * g) := by
  simp only [Aop, LinearMap.sum_apply, LinearMap.smul_apply, Submodule.coe_sum, Submodule.coe_smul,
    Finset.sum_apply, Pi.smul_apply, ltS_apply, smul_eq_mul]

theorem Aop_act (r : ℕ) (τs : Finset ℝ) (a : ℝ → ℂ) (o : Op E N) (F : Sm E N) :
    Aop N r τs a (act o F) = act o (Aop N r τs a F) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Aop, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, ltS_act]

theorem exists_strictHenselian_absolutely_closed_local_ring (V : Submodule ℂ (Sm E N)) (hV : ∀ φ ∈ V, IsAutForm φ) (r : ℕ) (τs : Finset ℝ) (a : ℝ → ℂ) :
    ∃ T : Sm E N →ₗ[ℂ] Sm E N, ∀ φ ∈ V, T φ = Aop N r τs a (ctSm r φ) := by
  let T₁ : V →ₗ[ℂ] Sm E N :=
    { toFun := fun φ => Aop N r τs a (ctSm r φ.1)
      map_add' := fun φ ψ => by
        have e : ctSm r (φ.1 + ψ.1) = ctSm r φ.1 + ctSm r ψ.1 := by
          refine Subtype.ext ?_
          rw [Submodule.coe_add, ctSm_val r (hV _ (V.add_mem φ.2 ψ.2)), ctSm_val r (hV _ φ.2),
            ctSm_val r (hV _ ψ.2)]
          exact ctn_add r (ContAut.continuous_of_isOpen_stab E N _ (hV _ φ.2).level)
            (ContAut.continuous_of_isOpen_stab E N _ (hV _ ψ.2).level)
        simp only [Submodule.coe_add, e, map_add (f := _)]
      map_smul' := fun c φ => by
        have e : ctSm r (c • φ.1) = c • ctSm r φ.1 := by
          refine Subtype.ext ?_
          rw [Submodule.coe_smul, ctSm_val r (hV _ (V.smul_mem c φ.2)), ctSm_val r (hV _ φ.2)]
          exact ctn_smul r c _
        simp only [Submodule.coe_smul, e, map_smul, RingHom.id_apply] }
  obtain ⟨T, hT⟩ := LinearMap.exists_extend T₁
  exact ⟨T, fun φ hφ => LinearMap.congr_fun hT ⟨φ, hφ⟩⟩

end PositivityTheory.Rg.Rs.SliceClasses

end
end

noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.CompanionTheory.CTFin PositivityTheory.Affgl
open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm

namespace PositivityTheory.Rg.Rs.SliceClasses

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {N : ℕ}

theorem ctn_unip {φ : Sm E N} (hφ : IsAutForm φ) (r : ℕ) (x : BlockIx N r → Ad E) (g : GA E N) :
    An.ctn r φ.1 (unip x * g) = An.ctn r φ.1 g := by
  simp only [An.ctn]
  rw [← GlobalTheory.CompanionTheory.CuspBridge.unipGL_eq_unip,
    constantTerm_unipGL_mul (GlobalTheory.CompanionTheory.LeftInv.isLeftInvariant_of_isAutForm E N φ hφ)]

theorem ctn_splitCentre {φ : Sm E N} (hinv : ∀ t g, φ.1 (splitCentre E N t * g) = φ.1 g) (r : ℕ) (t : ℝ) (g : GA E N) :
    An.ctn r φ.1 (splitCentre E N t * g) = An.ctn r φ.1 g := by
  simp only [An.ctn, constantTerm]
  congr 2
  funext X
  rw [← mul_assoc, ← GlobalTheory.CuspRep.CuspidalL2GL.splitCentre_comm, mul_assoc, hinv]

theorem ctn_lev_rat {r s : ℕ} {φ : Sm E (r + s)} (hφ : IsAutForm φ) (γ : GL (Fin r) E × GL (Fin s) E)
    (g : GA E (r + s)) :
    An.ctn r φ.1 (lev (Ad E) r s (ratGL E r γ.1, ratGL E s γ.2) * g) = An.ctn r φ.1 g := by
  letI : MeasurableSpace (BlockIx (r + s) r → Ad E) := borel _
  have : BorelSpace (BlockIx (r + s) r → Ad E) := ⟨rfl⟩
  obtain ⟨μ, hμ, hD, hint⟩ := JDict.exists_normed E (r + s) r
  have key : ∀ (f : GA E (r + s) → ℂ) g,
      ∫ x in unipFundamentalDomain E (r + s) r, f (unip x * g) ∂μ = An.ctn r f g := by
    intro f g
    rw [hint]
    simp only [An.ctn, constantTerm, GlobalTheory.CompanionTheory.CuspBridge.unipGL_eq_unip]
  rw [← key, ← key]
  exact integral_unip_lev_mul E r s φ hφ.left hφ.level μ _ hμ hD γ g

theorem ctn_growth {φ : Sm E N} (hφ : IsAutForm φ) (r : ℕ) (g : GA E N) :
    ∃ (C : ℝ) (n : ℕ), ∀ y, ‖An.ctn r φ.1 (g * infGL E N y)‖ ≤ C * height y ^ n := by
  letI : MeasurableSpace (BlockIx N r → Ad E) := borel _
  have : BorelSpace (BlockIx N r → Ad E) := ⟨rfl⟩
  obtain ⟨μ, hμ, hD, hint⟩ := JDict.exists_normed E N r
  have key : ∀ (f : GA E N → ℂ) g,
      ∫ x in unipFundamentalDomain E N r, f (unip x * g) ∂μ = An.ctn r f g := by
    intro f g
    rw [hint]
    simp only [An.ctn, constantTerm, GlobalTheory.CompanionTheory.CuspBridge.unipGL_eq_unip]
  obtain ⟨C, n, h⟩ := Growth.ct_growth E N r φ hφ μ _ hμ hD g
  exact ⟨C, n, fun y => by rw [← key]; exact h y⟩

theorem aT_mul_unip (N r : ℕ) (t : ℝ) (x : BlockIx N r → Ad E) :
    ∃ y : BlockIx N r → Ad E, aT E N r t * unip x = unip y * aT E N r t := by
  obtain ⟨y, hy⟩ := unip_mul_aT N r (-t) x
  refine ⟨y, ?_⟩
  have h1 : aT E N r t * aT E N r (-t) = 1 := by rw [← aT_add, add_neg_cancel, aT_zero]
  calc aT E N r t * unip x = aT E N r t * (unip x * aT E N r (-t)) * aT E N r t := by
        rw [mul_assoc, mul_assoc, ← aT_add, neg_add_cancel, aT_zero, mul_one]
    _ = unip y * aT E N r t := by rw [hy, ← mul_assoc, h1, one_mul]

variable {r s : ℕ}

theorem F_slices (V : Submodule ℂ (Sm E (r + s))) (hV : IsDiscrete V) (T : Sm E (r + s) →ₗ[ℂ] Sm E (r + s))
    (hequiv : ∀ o, ∀ φ ∈ V, T (act o φ) = act o (T φ)) (τs : Finset ℝ) (a : ℝ → ℂ)
    (hTval : ∀ φ ∈ V, ∀ g, (T φ).1 g = ∑ t ∈ τs, a t * An.ctn r φ.1 (aT E (r + s) r t * g))
    (φ : Sm E (r + s)) (hφ : φ ∈ V) (k : Kinf E (r + s)) (g : GL (Fin (r + s)) (Af E)) :
    (∀ m₂, ∃ ψ : Sm E r, IsAutForm ψ ∧ ∀ m₁, ψ.1 m₁ =
      (T φ).1 (lev (Ad E) r s (m₁, m₂) * (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) g))) ∧
    (∀ m₁, ∃ ψ : Sm E s, IsAutForm ψ ∧ ∀ m₂, ψ.1 m₂ =
      (T φ).1 (lev (Ad E) r s (m₁, m₂) * (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) g))) := by
  have hAφ := hV.aut φ hφ

  have hN : ∀ (x : BlockIx (r + s) r → Ad E) (g : GA E (r + s)), (T φ).1 (unip x * g) = (T φ).1 g := by
    intro x g
    rw [hTval φ hφ, hTval φ hφ]
    refine Finset.sum_congr rfl fun t _ => ?_
    obtain ⟨y, hy⟩ := aT_mul_unip (r + s) r t x
    rw [← mul_assoc, hy, mul_assoc, ctn_unip hAφ]

  have hM : ∀ (γ : GL (Fin r) E × GL (Fin s) E) (g : GA E (r + s)),
      (T φ).1 (lev (Ad E) r s (ratGL E r γ.1, ratGL E s γ.2) * g) = (T φ).1 g := by
    intro γ g
    rw [hTval φ hφ, hTval φ hφ]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [← mul_assoc, aT_comm_lev, mul_assoc, ctn_lev_rat hAφ]

  let L := GlobalTheory.DiscClosure.stabSub φ
  have hLo : IsOpen (L : Set (GL (Fin (r + s)) (Af E))) := hAφ.level
  have hLv : ∀ h ∈ L, finRep E (r + s) h (T φ) = T φ := fun h hh => by
    have e := hequiv (.fin h) φ hφ
    have hh' : finRep E (r + s) h φ = φ := hh
    change T (finRep E (r + s) h φ) = finRep E (r + s) h (T φ) at e
    rw [← e, hh']

  let S := GlobalTheory.CuspRep.LocEx.orbSpan (T φ)
  haveI : FiniteDimensional ℂ S := by
    haveI := hAφ.kfin
    refine Submodule.finiteDimensional_of_le
      (S₂ := (Submodule.span ℂ (Set.range fun κ => cptRep E (r + s) κ φ)).map T) (Submodule.span_le.2 ?_)
    rintro _ ⟨κ, rfl⟩
    exact ⟨_, Submodule.subset_span ⟨κ, rfl⟩, hequiv (.cpt κ) φ hφ⟩
  let ρ := GlobalTheory.PRep.sub (cptRep E (r + s)) S (GlobalTheory.CuspRep.LocEx.orbSpan_stable (T φ))
  have hρ : GlobalTheory.Published.AutFin.IsContRep ρ := GlobalTheory.CuspRep.LocEx.isContRep_sub S _
  have hC : ∀ g : GA E (r + s), (fun κ : Kinf E (r + s) => (cptRep E (r + s) κ (T φ)).1 g) ∈
      GlobalTheory.Published.AutFin.coeffSpan ρ := fun g =>
    GlobalTheory.Published.AutFinGL.type_of_map ρ S.subtype (fun _ _ => rfl) ⟨T φ, Submodule.subset_span ⟨1, by simp⟩⟩ g

  have hG : ∀ g₀ : GA E (r + s), ∃ (C : ℝ) (n : ℕ), ∀ y, ‖(T φ).1 (g₀ * infGL E (r + s) y)‖ ≤ C * height y ^ n := by
    intro g₀
    choose C n hCn using fun t => ctn_growth hAφ r (aT E (r + s) r t * g₀)
    refine ⟨∑ t ∈ τs, ‖a t‖ * |C t|, ∑ t ∈ τs, n t, fun y => ?_⟩
    rw [hTval φ hφ, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun t ht => ?_)
    have hy := one_le_height y
    have e1 : height y ^ n t ≤ height y ^ (∑ t ∈ τs, n t) :=
      pow_le_pow_right₀ hy (Finset.single_le_sum (fun _ _ => Nat.zero_le _) ht)
    have hp : (0 : ℝ) ≤ height y ^ n t := pow_nonneg (by linarith) _
    calc ‖a t * An.ctn r φ.1 (aT E (r + s) r t * (g₀ * infGL E (r + s) y))‖
        = ‖a t‖ * ‖An.ctn r φ.1 (aT E (r + s) r t * g₀ * infGL E (r + s) y)‖ := by rw [norm_mul, mul_assoc]
      _ ≤ ‖a t‖ * (C t * height y ^ n t) := mul_le_mul_of_nonneg_left (hCn t y) (norm_nonneg _)
      _ ≤ ‖a t‖ * (|C t| * height y ^ (∑ t ∈ τs, n t)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul (le_abs_self _) e1 hp (abs_nonneg _)) (norm_nonneg _)
      _ = ‖a t‖ * |C t| * height y ^ (∑ t ∈ τs, n t) := by ring

  have hsc : ∀ (τ : E →+* ℂ) (u : ℂ), ∃ c : ℂ, ∀ ψ ∈ V, cap τ u ψ = c • ψ := fun τ u =>
    GlobalTheory.DiscLocEx.exists_scalarD hV (Algebra.subset_adjoin ⟨τ, u, rfl⟩) (GlobalTheory.SpehInfChar.cap_commute_act τ u)
  choose cc hcc using hsc
  let J : Set (Module.End ℂ (Sm E (r + s))) :=
    {z | ∃ (τ : E →+* ℂ) (u : ℂ), z = Polynomial.aeval (cap (a := r + s) τ u) (Polynomial.X - Polynomial.C (cc τ u))}
  have hJZ : J ⊆ Zalg E (r + s) := by
    rintro _ ⟨τ, u, rfl⟩
    exact aeval_mem_Zalg (cap_mem_Zalg τ u) _
  have hJ : Cofin J := GlobalTheory.CompanionTheory.CTFin.MonicCofin.cofin_of_monic E (r + s) J hJZ fun τ u =>
    ⟨_, Polynomial.monic_X_sub_C _, τ, u, rfl⟩
  have hZ : ∀ z ∈ J, z (T φ) = 0 := by
    rintro _ ⟨τ, u, rfl⟩
    simp only [map_sub, Polynomial.aeval_X, Polynomial.aeval_C, LinearMap.sub_apply, Module.algebraMap_end_apply]
    rw [← GlobalTheory.SpehInfChar.cap_comm_quot (fun X ψ hψ => hV.stable (.lie X) ψ hψ) T hequiv τ u φ hφ,
      hcc τ u φ hφ, map_smul, sub_self]
  have hgood : T φ ∈ goodCT L ρ J := ⟨hN, hM, hLv, hC, hG, hZ⟩
  obtain ⟨J₁, J₂, c₁, c₂, k₁, k₂⟩ := centre J hJ
  have e : ∀ m : GA E r × GA E s, lev (Ad E) r s m * (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) g) =
      lev (Ad E) r s m * finGL E (r + s) g * infGL E (r + s) (Unitary.toUnits k) := by
    intro m
    rw [infGL_comm, mul_assoc]
  refine ⟨fun m₂ => ?_, fun m₁ => ?_⟩
  · obtain ⟨L₁, ρ₁, -, -, h⟩ := Slice1.slice_mem_genSpace E r s L hLo S ρ hρ J hJ J₁ c₁ k₁ g k
    obtain ⟨G, hG, hG'⟩ := h (T φ) hgood m₂
    exact ⟨G, hG.1, fun m₁ => by rw [hG', e]⟩
  · obtain ⟨L₂, ρ₂, -, -, h⟩ := Slice2.slice2 E r s L hLo S ρ hρ J hJ J₂ c₂ k₂ g k
    obtain ⟨G, hG, hG'⟩ := h (T φ) hgood m₁
    exact ⟨G, hG.1, fun m₂ => by rw [hG', e]⟩

end PositivityTheory.Rg.Rs.SliceClasses

end
