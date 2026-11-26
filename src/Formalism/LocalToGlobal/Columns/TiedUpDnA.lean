module

public import Formalism.LocalToGlobal.Columns.TiedUpDnLoc

@[expose] public section

section -- merged from Formalism.LocalToGlobal.Columns.TiedUpDnA
open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.UG

section Lat

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

theorem tud_locP_L {a : 𝓞 E} (ha : SepElt ST a) (d : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)) (P : ST) :
    localization₂ P.1.asIdeal d.1.L = localization₂ P.1.asIdeal (d.1.LshKer P) := by
  rw [d.2.locP_LshKer_self ha P]
  have key : ∀ (L : Submodule (𝓞 E) (Sp E n)) (x : Sp E n),
      x ∈ localization₂ P.1.asIdeal L ↔ ∃ s ∈ P.1.asIdeal.primeCompl, s • x ∈ L := fun _ _ => Iff.rfl
  ext x
  rw [d.2.mem_locP_L P x, key]
  constructor
  · rintro ⟨hx, hf⟩
    obtain ⟨s, hs, hsx⟩ := (key _ x).1 hx
    refine ⟨s, hs, (d.2.mem_kerAt P _).2 ⟨hsx, ?_⟩⟩
    rw [d.2.f_smul P s x hx, hf, mul_zero]
  · rintro ⟨s, hs, hsx⟩
    obtain ⟨hN, hf⟩ := (d.2.mem_kerAt P _).1 hsx
    have hx : x ∈ d.1.at P.1 := (key _ x).2 ⟨s, hs, hN⟩
    refine ⟨hx, ?_⟩
    rw [d.2.f_smul P s x hx] at hf
    rcases mul_eq_zero.1 hf with h0 | h0
    · exact absurd (Ideal.Quotient.eq_zero_iff_mem.1 h0) hs
    · exact h0

end Lat

section Same

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

theorem tud_isOver_conj (hc : Formalism.BasicNotions.CMData F E) {v : HeightOneSpectrum (𝓞 F)} {P : HeightOneSpectrum (𝓞 E)}
    (hov : IsOver v P) : IsOver v (conjPrime₂ P) := by
  unfold IsOver at *
  rw [hov]
  change _ = Ideal.comap _ (Ideal.comap (cO E) P.asIdeal)
  rw [Ideal.comap_comap]
  congr 1
  apply RingHom.ext
  intro x
  symm
  apply RingOfIntegers.ext
  show star ((algebraMap (𝓞 F) (𝓞 E) x : 𝓞 E) : E) = ((algebraMap (𝓞 F) (𝓞 E) x : 𝓞 E) : E)
  rw [hc.fixed]
  refine ⟨(x : F), ?_⟩
  rfl

end Same

end Formalism.L2.Col
end
end

section -- merged from Formalism.LocalToGlobal.Columns.LevPackFrLat
section -- merged from Formalism.LocalToGlobal.Columns.JointLevelFrameZero
open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG

attribute [local instance] Formalism.BasicNotions.Host.cmStar

structure ColLevelXRest {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] {sp : Spaces R F E} {gp : Fin 2 → ℕ}
    {ι : Type} [Fintype ι] {hc : ι → HCParam R} {C : ColumnChain R ι hc} {A : ColumnsAtT R C}
    {clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V} (L : ColLevel R F E sp gp C A clsLat)
    (piU : 𝓞 E)
    (e : A.vT ≃ {v : HeightOneSpectrum (𝓞 F) // ((A.T : ℕ) : 𝓞 F) ∈ v.asIdeal})
    (fz : ∀ (v : A.vT) (c : C.cls 0), Formalism.HermitianLatticesTheory.dual (sp.X 0).hT (clsLat 0 c) → A.Fv v) where

  frG_lat : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)) (h : (gp i : 𝓞 F) ∈ v.asIdeal)
    (t : Fin R.k → v.adicCompletion F),
    (∃ x ∈ Formalism.L2.Herm.locL v L.Lb, ∀ a, (L.splitG i v h (x a)).1 = t a) ↔
      ∀ a, (((L.frG i v h)⁻¹ : GL (Fin R.k) (v.adicCompletion F)) :
        Matrix (Fin R.k) (Fin R.k) (v.adicCompletion F)).mulVec t a ∈ v.adicCompletionIntegers F

  fM_pi : ∀ (v : HeightOneSpectrum (𝓞 F)) (h : ((A.T : ℕ) : 𝓞 F) ∈ v.asIdeal) (a : intV E v),
    (a : E ⊗[F] v.adicCompletion F) = inclE (F := F) (v.adicCompletion F) (piU : E) →
    ∀ m : L.fM v h, a • m = 0

  fMe : ∀ (w : HeightOneSpectrum (𝓞 F)) (h : ((A.T : ℕ) : 𝓞 F) ∈ w.asIdeal), L.fM w h ≃+ A.Fv (e.symm ⟨w, h⟩)

  fv0 : ∀ (w : HeightOneSpectrum (𝓞 F)) (h : ((A.T : ℕ) : 𝓞 F) ∈ w.asIdeal) (c : C.cls 0)
    (z : Formalism.HermitianLatticesTheory.dual (sp.X 0).hT (clsLat 0 c))
    (t : latS (F := F) (w.adicCompletion F) (intV E w)
      (Submodule.span (𝓞 E) (dualSet (sp.cm.sig : E →+* E) sp.gram0 L.Lb))),
    ((bc (prV (E := E) w) (L.y c : GL (Fin R.k) (E ⊗[F] Formalism.L2.Herm.Af F)) : GL (Fin R.k) (E ⊗[F] w.adicCompletion F)) :
      Matrix (Fin R.k) (Fin R.k) (E ⊗[F] w.adicCompletion F)).mulVec t.1 =
      (fun a => inclE (F := F) (w.adicCompletion F) (sp.crd0 z.1 a)) →
    fz (e.symm ⟨w, h⟩) c z = fMe w h (L.fT w h t)

end Formalism.L2.Col
end
end

open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Loc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] {ST : Finset (Pl E)} {π : 𝓞 E} (v : HeightOneSpectrum (𝓞 F))

theorem th_fLoc_pi (h : BasePi ST π) (a : Formalism.BasicNotions.intV E v)
    (ha : (a : E ⊗[F] v.adicCompletion F) = inclE (F := F) (v.adicCompletion F) (algebraMap (𝓞 E) E π)) (m : fMod hc n ST v) :
    a • m = 0 := by
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ m
  show a • fLoc hc n ST v x = 0
  rw [← map_smul, rll_fLoc_eq_zero, rll_baseKer_eq n h, rll_mem_loc_dLat n v _ (div_ne_zero h.star_ne_zero h.coe_ne_zero)]
  have hx : x.1 ∈ Formalism.L2.Herm.locL v (rll_dLat n (star (algebraMap (𝓞 E) E π))) := by
    rw [← rll_dualV_eq hc n v h]; exact x.2
  rw [rll_mem_loc_dLat n v _ h.star_ne_zero] at hx
  refine ⟨fun i hi => mul_mem a.2 (hx.1 i hi), ?_⟩
  show inclE (F := F) (v.adicCompletion F) (star (algebraMap (𝓞 E) E π) / algebraMap (𝓞 E) E π) *
    ((a : E ⊗[F] v.adicCompletion F) * x.1 (lastIdx n)) ∈ Formalism.BasicNotions.intV E v
  rw [ha, rll_cp_mul v h]
  exact hx.2

end Loc

section Gen

variable {X : Fields} {Pr : Primes X} (hc : CMData X.F X.E) (hX : X.Ok) (hPr : Pr.Ok) (σ₀ : X.K →+* ℂ) (u : Pr.Word)
  {n : ℕ} [NeZero n] (Λ : LevFam X.E X.K n Pr.vGs)
  (c₀ : DiaG (E := X.E) (ST := Pr.vT u)) (s : DecoCl n (Pr.vT u) Pr.vGs Λ.grp → DecoSet (E := X.E) (n := n) (ST := Pr.vT u) (SG := Pr.vGs))
  (hS : DecoPtSurj hc n (Pr.vT u) Pr.vGs) (hs : ∀ c, decoCls n (Pr.vT u) Pr.vGs Λ.grp (s c) = c) (hK : LocalLevelIsKOneAtT hc u Λ)

end Gen

end Formalism.L2.Col
end
end

section -- merged from Formalism.LocalToGlobal.Columns.MtHeckeKv
open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.UG Formalism.UG.P
open Formalism.L2.DIV (Pl kP St redAt)

section Kv

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n]

def mhlKv (v : HeightOneSpectrum (𝓞 F)) : Subgroup (UAd hc n) where
  carrier := {η | (∀ w : HeightOneSpectrum (𝓞 F), w ≠ v →
      bc (prV (E := E) w) (η : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = 1) ∧
    bc (prV (E := E) v) (η : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) ∈ stabGL (Formalism.L2.Herm.locL v (stdLat E n))}
  one_mem' := ⟨fun w _ => by rw [OneMemClass.coe_one, map_one], by rw [OneMemClass.coe_one, map_one]; exact one_mem _⟩
  mul_mem' := by
    rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    refine ⟨fun w hw => ?_, ?_⟩
    · rw [Subgroup.coe_mul, map_mul, ha1 w hw, hb1 w hw, mul_one]
    · rw [Subgroup.coe_mul, map_mul]; exact mul_mem ha2 hb2
  inv_mem' := by
    rintro a ⟨ha1, ha2⟩
    refine ⟨fun w hw => ?_, ?_⟩
    · rw [InvMemClass.coe_inv, map_inv, ha1 w hw, inv_one]
    · rw [InvMemClass.coe_inv, map_inv]; exact inv_mem ha2

variable {hc n}

theorem mhl_eq_put {v : HeightOneSpectrum (𝓞 F)} {η : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} (hη : η ∈ UAd hc n)
    (h : ∀ w : HeightOneSpectrum (𝓞 F), w ≠ v → bc (prV (E := E) w) η = 1) :
    η = rll_put n v (bc (prV (E := E) v) η) := by
  have h1 : (afsplitE hc.sig (1 : Matrix (Fin n) (Fin n) E) v ⟨η, hη⟩).2 = 1 :=
    (afsplitE_snd_eq_one hc.sig 1 v ⟨η, hη⟩).2 h
  have h2 : afsplitU v 1 η = 1 := by
    rw [← afsplitE_snd hc.sig (1 : Matrix (Fin n) (Fin n) E) v ⟨η, hη⟩]
    exact congrArg Subtype.val h1
  conv_lhs => rw [← afsplit_left v η, h2]
  rfl

variable (ST SG : Finset (Pl E))

theorem put_mem_kOne_of_not_over {v : HeightOneSpectrum (𝓞 F)} (hST : ∀ P ∈ ST, ¬ IsOver v P) (hSG : ∀ P ∈ SG, ¬ IsOver v P)
    {g : GL (Fin n) (E ⊗[F] v.adicCompletion F)} (hU : rll_put n v g ∈ UAd hc n)
    (hg : g ∈ stabGL (Formalism.L2.Herm.locL v (stdLat E n))) : rll_put n v g ∈ K1 hc n ST SG := by
  have hS := rll_put_mem_St n v hg
  have hJ : rll_put n v g ∈ J0 hc n ST := by
    refine ⟨⟨hU, hS⟩, Subgroup.mem_iInf.2 fun P => Subgroup.mem_iInf.2 fun hP => ?_⟩
    refine ⟨⟨rll_put n v g, hS⟩, ?_, rfl⟩
    show redAt 1 P ⟨rll_put n v g, hS⟩ ∈ mirab (kP P) n
    rw [rll_put_red n v g hS P (hST P hP)]
    exact one_mem _
  refine ⟨⟨_, hJ⟩, MonoidHom.mem_ker.2 ?_, rfl⟩
  funext w
  exact rll_put_red n v g hS w.1 (hSG w.1 w.2)

theorem localLevel_le_kOne {v : HeightOneSpectrum (𝓞 F)} (hST : ∀ P ∈ ST, ¬ IsOver v P) (hSG : ∀ P ∈ SG, ¬ IsOver v P)
    {η : UAd hc n} (hη : η ∈ mhlKv hc n v) : (η : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) ∈ K1 hc n ST SG := by
  have e := mhl_eq_put η.2 hη.1
  rw [e] at ⊢
  exact put_mem_kOne_of_not_over ST SG hST hSG (e ▸ η.2) hη.2

theorem decoOf_mul_mhlKv {v : HeightOneSpectrum (𝓞 F)} (hST : ∀ P ∈ ST, ¬ IsOver v P) (hSG : ∀ P ∈ SG, ¬ IsOver v P)
    (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) {η : UAd hc n} (hη : η ∈ mhlKv hc n v) :
    decoOf ST SG (x * (η : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))) = decoOf ST SG x :=
  decoration_mul_principal hc n ST SG x (localLevel_le_kOne ST SG hST hSG hη)

theorem mem_localLevel_of_mem_kOne {v : HeightOneSpectrum (𝓞 F)} {η : UAd hc n}
    (h1 : ∀ w : HeightOneSpectrum (𝓞 F), w ≠ v → bc (prV (E := E) w) (η : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = 1)
    (hK : (η : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) ∈ K1 hc n ST SG) : η ∈ mhlKv hc n v := by
  refine ⟨h1, ?_⟩
  have hS : (η : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) ∈ St (1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) :=
    congruence_subgroup_le_stabilizer hc n ST (principal_le_congruence_subgroup hc n ST SG hK)
  rw [St_one] at hS
  exact Formalism.L2.DIV.lc_stab_loc v (stdLat E n) _ hS

theorem mhl_inv_mul_mem {v : HeightOneSpectrum (𝓞 F)} (x g g' : UAd hc n)
    (hg : ∀ w : HeightOneSpectrum (𝓞 F), w ≠ v → bc (prV (E := E) w) (g : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = 1)
    (hg' : ∀ w : HeightOneSpectrum (𝓞 F), w ≠ v → bc (prV (E := E) w) (g' : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = 1)
    (h : decoOf ST SG ((x * g : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) =
      decoOf ST SG ((x * g' : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))) :
    g⁻¹ * g' ∈ mhlKv hc n v := by
  have hr : decoRaw ST SG ((x * g : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) =
      decoRaw ST SG ((x * g' : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) := by
    rw [← rlc_decoOf_val hc n ST SG (x * g).2, ← rlc_decoOf_val hc n ST SG (x * g').2, h]
  have hK := mem_principal_of_same_decoration hc n ST SG (x * g).2 (x * g').2 hr
  have e : ((x * g : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))⁻¹ * ((x * g' : UAd hc n) : GL (Fin n) _) =
      ((g⁻¹ * g' : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) := by
    simp only [Subgroup.coe_mul, InvMemClass.coe_inv, _root_.mul_inv_rev]
    group
  rw [e] at hK
  refine mem_localLevel_of_mem_kOne ST SG (fun w hw => ?_) hK
  rw [Subgroup.coe_mul, InvMemClass.coe_inv, map_mul, map_inv, hg w hw, hg' w hw, inv_one, one_mul]

end Kv

end Formalism.L2.Col
end
end
