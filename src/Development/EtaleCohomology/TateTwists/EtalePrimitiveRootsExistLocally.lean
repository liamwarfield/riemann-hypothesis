module

public import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass

@[expose] public section

section -- merged from Development.EtaleCohomology.TateTwists.EtalePrimitiveRootsExistLocally
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

def LateralTheory.EtaleFoundations.EtalePrimitiveRootsExistLocally : Prop :=
  ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}), (IsUnit (q : Γ(U, ⊤)) → Loc U fun V _ => Nonempty (Prim q Γ(V, ⊤))) ∧ (∀ ζ ξ : Prim q Γ(U, ⊤), Loc U fun _ g => ∃ a : (ZMod q)ˣ, g.appTop.hom ξ.1 = g.appTop.hom ζ.1 ^ (a : ZMod q).val) ∧ (∀ (ζ : Prim q Γ(U, ⊤)) (x : Γ(U, ⊤)), x ^ q = 1 → Loc U fun _ g => ∃ a : ℕ, g.appTop.hom x = g.appTop.hom ζ.1 ^ a) ∧ (IsUnit (q : Γ(U, ⊤)) → ∀ u : (Γ(U, ⊤))ˣ, Loc U fun V g => ∃ v : (Γ(V, ⊤))ˣ, v ^ q = Units.map g.appTop.hom.toMonoidHom u)
end

section -- merged from Development.EtaleCohomology.TateTwists.EtaleTateTwistSectionsLocallyGenerated
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

def LateralTheory.EtaleFoundations.EtaleTateTwistSectionsLocallyGenerated : Prop :=
  ∀ (q : ℕ) [NeZero q] (i : ℤ), (∀ (U : Scheme.{0}) (y : Sec (tw q i) U), Loc U fun V g => Sec.res g y = 0 ∨ ∃ (ζ : Prim q Γ(V, ⊤)) (c : ℕ), Sec.res g y = c • twGen i ζ) ∧ (∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) (y : Sec (tw q i) U), Loc U fun V g => ∃ c : ℕ, Sec.res g y = c • twGen i (ζ.map g.appTop.hom)) ∧ (∀ (U : Scheme.{0}) [Nonempty U] (ζ : Prim q Γ(U, ⊤)) (c : ℕ), c • twGen i ζ = 0 → q ∣ c) ∧ (∀ (V U : Scheme.{0}) (g : V ⟶ U) (ζ : Prim q Γ(U, ⊤)), Sec.res g (twGen i ζ) = twGen i (ζ.map g.appTop.hom)) ∧ (∀ (U : Scheme.{0}) (ζ ξ : Prim q Γ(U, ⊤)) (a : (ZMod q)ˣ), ξ.1 = ζ.1 ^ (a : ZMod q).val → twGen i ξ = ((a ^ i : (ZMod q)ˣ) : ZMod q).val • twGen i ζ) ∧ ∀ (M : Shv (ZMod q)) (e : ∀ U : Scheme.{0}, Prim q Γ(U, ⊤) → Sec M U), (∀ (V U : Scheme.{0}) (g : V ⟶ U) ζ, Sec.res g (e U ζ) = e V (ζ.map g.appTop.hom)) → (∀ (U : Scheme.{0}) (ζ ξ : Prim q Γ(U, ⊤)) (a : (ZMod q)ˣ), ξ.1 = ζ.1 ^ (a : ZMod q).val → e U ξ = ((a ^ i : (ZMod q)ˣ) : ZMod q).val • e U ζ) → ∃! φ : tw q i ⟶ M, ∀ U ζ, Sec.map φ (twGen i ζ) = e U ζ
end

section -- merged from Development.EtaleCohomology.TateTwists.EtaleSheafSectionsSeparatedAndGlue
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

def LateralTheory.EtaleFoundations.EtaleSheafSectionsSeparatedAndGlue : Prop :=
  ∀ (R : Type) [CommRing R] (F : Shv R) (U : Scheme.{0}), (∀ a b : Sec F U, (Loc U fun _ g => Sec.res g a = Sec.res g b) → a = b) ∧ ∀ (S : Sieve U), S ∈ Scheme.etaleTopology U → ∀ s : ∀ (V : Scheme.{0}) (g : V ⟶ U), S.arrows g → Sec F V, (∀ (V W : Scheme.{0}) (g : V ⟶ U) (k : W ⟶ V) (hg : S.arrows g), Sec.res k (s V g hg) = s W (k ≫ g) (S.downward_closed hg k)) → ∃ a : Sec F U, ∀ V g hg, Sec.res g a = s V g hg
end

section -- merged from Development.EtaleCohomology.TateTwists.EtaleTateTwistTensorIsoOfGeneratorMapIso
section -- merged from Development.EtaleCohomology.TateTwists.EtaleTateTwistSingletonTensorGenMul
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

def LateralTheory.EtaleFoundations.EtaleTateTwistSingletonTensorGenMul : Prop :=
  ∀ (q : ℕ) [NeZero q] (i j k : ℤ), i + j = k → ∃ μ : Pair (sgl (tw q i)) (sgl (tw q j)) (sgl (tw q k)), μ.IsTensor ∧ ∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)), μ.mul U 0 0 0 (add_zero 0) (Sec.map (sglι _) (twGen i ζ)) (Sec.map (sglι _) (twGen j ζ)) = Sec.map (sglι _) (twGen k ζ)
end

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
namespace LateralTheory.EtaleFoundations.TwMulPf

variable {R : Type} [CommRing R]

theorem sec_res_map {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.res g (Sec.map φ x) = Sec.map φ (Sec.res g x) := by
  have := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (φ.hom.naturality g.op)) x
  simpa using this.symm

theorem sec_map_comp {F G H : Shv R} (φ : F ⟶ G) (ψ : G ⟶ H) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map ψ (Sec.map φ x) = Sec.map (φ ≫ ψ) x := by
  simp [Sec.map]

theorem sec_map_id {F : Shv R} {U : Scheme.{0}} (x : Sec F U) : Sec.map (𝟙 F) x = x := by
  simp [Sec.map]

theorem loc_mono {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : Loc U P)
    (hPQ : ∀ V g, P V g → Q V g) : Loc U Q := by
  obtain ⟨S, hS, hP⟩ := h
  exact ⟨S, hS, fun V g hg => hPQ V g (hP V g hg)⟩

def secL {F G : Shv R} (φ : F ⟶ G) (U : Scheme.{0}) : Sec F U →ₗ[ULift.{1} R] Sec G U :=
  (φ.hom.app (op U)).hom

def transp {I J K K' : Cx R} (μ : Pair I J K) (ψ : K ≅ K') : Pair I J K' where
  mul U s t w h := (μ.mul U s t w h).compr₂ (secL (ψ.hom.f w) U)
  nat g s t w h a b := by
    change Sec.res g (Sec.map (ψ.hom.f w) _) = Sec.map (ψ.hom.f w) _
    rw [sec_res_map, μ.nat]
  leibniz U s t w h a b := by
    change Sec.map (K'.d w (w + 1)) (Sec.map (ψ.hom.f w) _) =
      Sec.map (ψ.hom.f (w + 1)) _ + s.negOnePow • Sec.map (ψ.hom.f (w + 1)) _
    rw [sec_map_comp, ψ.hom.comm w (w + 1), ← sec_map_comp, μ.leibniz]
    simp only [Sec.map, map_add (f := _), map_zsmul_unit]

theorem transp_lift {I J K K' : Cx R} (μ : Pair I J K) (ψ : K ≅ K') (U : Scheme.{0}) (w : ℤ)
    (x : Tens I J U w) : (transp μ ψ).lift U w x = Sec.map (ψ.hom.f w) (μ.lift U w x) := by
  classical
  change _ = secL (ψ.hom.f w) U (μ.lift U w x)
  rw [← LinearMap.comp_apply]
  congr 1
  refine DirectSum.linearMap_ext _ fun p => TensorProduct.ext' fun a b => ?_
  simp [Pair.lift, transp]

theorem transp_isTensor {I J K K' : Cx R} (μ : Pair I J K) (ψ : K ≅ K') (hμ : μ.IsTensor) :
    (transp μ ψ).IsTensor := by
  refine ⟨fun U w y => ?_, fun U w x hx => ?_⟩
  · refine loc_mono (hμ.1 U w (Sec.map (ψ.inv.f w) y)) fun V g ⟨x, hx⟩ => ⟨x, ?_⟩
    rw [transp_lift, hx, ← sec_res_map, sec_map_comp, ← HomologicalComplex.comp_f, ψ.inv_hom_id,
      HomologicalComplex.id_f, sec_map_id]
  · refine hμ.2 U w x ?_
    rw [transp_lift] at hx
    have := congrArg (Sec.map (ψ.inv.f w)) hx
    rw [sec_map_comp, ← HomologicalComplex.comp_f, ψ.hom_inv_id, HomologicalComplex.id_f, sec_map_id] at this
    rw [this]
    exact map_zero _

theorem sgl_map_f_zero {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (((CochainComplex.singleFunctor (Shv R) 0).map φ).f 0) (Sec.map (sglι F) x) =
      Sec.map (sglι G) (Sec.map φ x) := by
  rw [sec_map_comp, sec_map_comp]
  congr 1

end LateralTheory.EtaleFoundations.TwMulPf


open LateralTheory.EtaleFoundations.TwMulPf in
def LateralTheory.EtaleFoundations.EtaleTateTwistTensorPairingExists : Prop :=
  ∀ (q : ℕ) [NeZero q] (i j : ℤ), ∃ (T : Shv (ZMod q)) (μ : Pair (sgl (tw q i)) (sgl (tw q j)) (sgl T)), μ.IsTensor

def LateralTheory.EtaleFoundations.EtaleTateTwistGeneratorCompatibleMapExists : Prop :=
  ∀ (q : ℕ) [NeZero q] (i j k : ℤ) (T : Shv (ZMod q)) (μ : Pair (sgl (tw q i)) (sgl (tw q j)) (sgl T)),
    μ.IsTensor → i + j = k → ∃ φ : tw q k ⟶ T, ∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)),
      Sec.map (sglι T) (Sec.map φ (twGen k ζ)) =
        μ.mul U 0 0 0 (add_zero 0) (Sec.map (sglι _) (twGen i ζ)) (Sec.map (sglι _) (twGen j ζ))

def LateralTheory.EtaleFoundations.EtaleTateTwistGeneratorCompatibleMapIsIso : Prop :=
  ∀ (q : ℕ) [NeZero q] (i j k : ℤ) (T : Shv (ZMod q)) (μ : Pair (sgl (tw q i)) (sgl (tw q j)) (sgl T)),
    μ.IsTensor → i + j = k → ∀ φ : tw q k ⟶ T, (∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)),
      Sec.map (sglι T) (Sec.map φ (twGen k ζ)) =
        μ.mul U 0 0 0 (add_zero 0) (Sec.map (sglι _) (twGen i ζ)) (Sec.map (sglι _) (twGen j ζ))) → IsIso φ

open LateralTheory.EtaleFoundations.TwMulPf in
theorem LateralTheory.EtaleFoundations.etale_tate_twist_tensor_iso_of_generator_map_iso (h1 : LateralTheory.EtaleFoundations.EtaleTateTwistTensorPairingExists)
    (h2 : LateralTheory.EtaleFoundations.EtaleTateTwistGeneratorCompatibleMapExists) (h3 : LateralTheory.EtaleFoundations.EtaleTateTwistGeneratorCompatibleMapIsIso) :
    LateralTheory.EtaleFoundations.EtaleTateTwistSingletonTensorGenMul := by
  intro q _ i j k hk
  obtain ⟨T, μ, hμ⟩ := h1 q i j
  obtain ⟨φ, hφ⟩ := h2 q i j k T μ hμ hk
  have := h3 q i j k T μ hμ hk φ hφ
  let ψ : sgl T ≅ sgl (tw q k) := (CochainComplex.singleFunctor (Shv (ZMod q)) 0).mapIso (asIso φ).symm
  refine ⟨transp μ ψ, transp_isTensor μ ψ hμ, fun U ζ => ?_⟩
  change Sec.map (ψ.hom.f 0) (μ.mul U 0 0 0 (add_zero 0) _ _) = _
  rw [← hφ U ζ]
  change Sec.map (((CochainComplex.singleFunctor (Shv (ZMod q)) 0).map (inv φ)).f 0) _ = _
  rw [sgl_map_f_zero, sec_map_comp, sec_map_comp, IsIso.hom_inv_id_assoc]
end
end

section -- merged from Development.EtaleCohomology.TateTwists.EtaleTensorPairTwistResolutionMul
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

def LateralTheory.EtaleFoundations.EtaleTensorPairTwistResolutionMul : Prop :=
  ∀ (q : ℕ) [NeZero q] (i j k : ℤ), i + j = k → ∀ {I J T : Cx (ZMod q)} (e : ∀ U : Scheme.{0}, Prim q Γ(U, ⊤) → Sec (I.X 0) U) (e' : ∀ U : Scheme.{0}, Prim q Γ(U, ⊤) → Sec (J.X 0) U), IsTwRes q i I e → IsTwRes q j J e' → (∀ t, FlatS (J.X t)) → ∀ τ : Pair I J T, τ.IsTensor → IsTwRes q k T fun U ζ => τ.mul U 0 0 0 (add_zero 0) (e U ζ) (e' U ζ)
end

section -- merged from Development.EtaleCohomology.TateTwists.EtaleSheafMonoEpiSectionCriteria
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

def LateralTheory.EtaleFoundations.EtaleSheafMonoEpiSectionCriteria : Prop :=
  ∀ (R : Type) [CommRing R] {F G : Shv R} (φ : F ⟶ G), (Mono φ ↔ ∀ U, Function.Injective (Sec.map φ (U := U))) ∧ (Mono φ ↔ ∀ U (a : Sec F U), Sec.map φ a = 0 → Loc U fun _ g => Sec.res g a = 0) ∧ (Epi φ ↔ ∀ U (b : Sec G U), Loc U fun V g => ∃ a : Sec F V, Sec.map φ a = Sec.res g b) ∧ (∀ ψ : F ⟶ G, (∀ U (a : Sec F U), Sec.map φ a = Sec.map ψ a) → φ = ψ)
end

section -- merged from Development.EtaleCohomology.TateTwists.EtaleLocalPropertyBasicClosure
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

def LateralTheory.EtaleFoundations.EtaleLocalPropertyBasicClosure : Prop :=
  (∀ (U : Scheme.{0}) (P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop), (∀ V g, P V g) → Loc U P) ∧ (∀ (U : Scheme.{0}) (P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop), Loc U P → (∀ V g, P V g → Q V g) → Loc U Q) ∧ (∀ (U : Scheme.{0}) (P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop), Loc U P → Loc U Q → Loc U fun V g => P V g ∧ Q V g) ∧ (∀ (U W : Scheme.{0}) (k : W ⟶ U) (P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop), Loc U P → Loc W fun V g => P V (g ≫ k)) ∧ (∀ (U : Scheme.{0}) (P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop), Loc U (fun V g => Loc V fun W k => P W (k ≫ g)) → Loc U P) ∧ (∀ (U : Scheme.{0}) (ι : Type) [Finite ι] (P : ι → ∀ V : Scheme.{0}, (V ⟶ U) → Prop), (∀ i, Loc U (P i)) → Loc U fun V g => ∀ i, P i V g) ∧ (∀ (U : Scheme.{0}) [IsEmpty U] (P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop), Loc U P)
end

section -- merged from Development.EtaleCohomology.TateTwists.EtaleKummerTriangleExists
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

def LateralTheory.EtaleFoundations.EtaleKummerTriangleExists : Prop :=
  ∀ (q : ℕ) [NeZero q], IsKum q (kumT q)
end

section -- merged from Development.EtaleCohomology.TateTwists.StrictHenselianAcyclic
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite TensorProduct GlobalTheory.EtC GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec

namespace LateralTheory.EtaleFoundations.CongruenceLocalDecomposition

def TwLoc : Prop := ∀ (q : ℕ) [NeZero q] (i : ℤ),
  (∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) (y : Sec (tw q i) U),
    Loc U fun V g => ∃ c : ℕ, Sec.res g y = c • twGen i (ζ.map g.appTop.hom)) ∧
  (∀ (U : Scheme.{0}) [Nonempty U] (ζ : Prim q Γ(U, ⊤)) (c : ℕ), c • twGen i ζ = 0 → q ∣ c) ∧
  ∀ (V U : Scheme.{0}) (g : V ⟶ U) (ζ : Prim q Γ(U, ⊤)), Sec.res g (twGen i ζ) = twGen i (ζ.map g.appTop.hom)

end LateralTheory.EtaleFoundations.CongruenceLocalDecomposition
end
end

section -- merged from Development.EtaleCohomology.TateTwists.EtaleCochainEvaluationLinear
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

def LateralTheory.EtaleFoundations.EtaleCochainEvaluationLinear : Prop :=
  ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ},
    (∀ (α β : Cochain ((chains R).obj E) I n) p s h U x,
      ev (α + β) p s h U x = ev α p s h U x + ev β p s h U x ∧
      ev (α - β) p s h U x = ev α p s h U x - ev β p s h U x ∧
      ev (0 : Cochain ((chains R).obj E) I n) p s h U x = 0 ∧
      ∀ c : ℤ, ev (c • α) p s h U x = c • ev α p s h U x) ∧
    (∀ (α : Cochain ((chains R).obj E) I n) p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U),
      Sec.res g (ev α p s h U x) = ev α p s h V (x.res g)) ∧
    (∀ α β : Cochain ((chains R).obj E) I n,
      (∀ p s h U x, ev α p s h U x = ev β p s h U x) → α = β) ∧
    (∀ {E' : Spc} (f : E' ⟶ E) (α : Cochain ((chains R).obj E) I n) p s h U (x : Sx E' p U),
      ev ((Cochain.ofHom ((chains R).map f)).comp α (zero_add n)) p s h U x = ev α p s h U (x.map f)) ∧
    ∀ {J : Cx R} (m : I ⟶ J) (α : Cochain ((chains R).obj E) I n) p s h U x,
      ev (α.comp (Cochain.ofHom m) (add_zero n)) p s h U x = Sec.map (m.f s) (ev α p s h U x)
end

section -- merged from Development.EtaleCohomology.TateTwists.EtaleTensorPreservesQuasiIsoOfAcyclicAndCone
section -- merged from Development.EtaleCohomology.TateTwists.EtaleTensorPairQuasiIsoOfFlatQuasiIso
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

def LateralTheory.EtaleFoundations.EtaleTensorPairQuasiIsoOfFlatQuasiIso : Prop :=
  ∀ (R : Type) [CommRing R] {I I' J T T' : Cx R} [I.IsStrictlyGE 0] [I'.IsStrictlyGE 0] [J.IsStrictlyGE 0] (τ : Pair I J T) (τ' : Pair I' J T'), τ.IsTensor → τ'.IsTensor → (∀ t, FlatS (J.X t)) → ∀ (f : I ⟶ I') [QuasiIso f] (u : T ⟶ T'), τ.Compat τ' f (𝟙 J) u → QuasiIso u
end

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.tqis

def acyc : Prop :=
  ∀ (R : Type) [CommRing R] {C J T : Cx R} (a b : ℤ) [C.IsStrictlyGE a] [J.IsStrictlyGE b] (τ : Pair C J T),
    τ.IsTensor → (∀ t, FlatS (J.X t)) → C.Acyclic → T.Acyclic

def cone : Prop :=
  ∀ (R : Type) [CommRing R] {I I' J T T' : Cx R} (τ : Pair I J T) (τ' : Pair I' J T') (f : I ⟶ I') (u : T ⟶ T'),
    τ.IsTensor → τ'.IsTensor → τ.Compat τ' f (𝟙 J) u → ∃ σ : Pair (mappingCone f) J (mappingCone u), σ.IsTensor

end LateralTheory.EtaleFoundations.tqis

theorem qis_iff_cone {R : Type} [CommRing R] {K L : Cx R} (f : K ⟶ L) : QuasiIso f ↔ (mappingCone f).Acyclic := by
  have h : HomotopyCategory.quasiIso (Shv R) (ComplexShape.up ℤ) ((HomotopyCategory.quotient _ _).map f) ↔ (HomotopyCategory.subcategoryAcyclic (Shv R)).trW ((HomotopyCategory.quotient _ _).map f) := by
    rw [HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic]
  rw [HomotopyCategory.quotient_map_mem_quasiIso_iff] at h
  change HomologicalComplex.quasiIso (Shv R) (ComplexShape.up ℤ) f ↔ _
  exact h.trans ((ObjectProperty.trW_iff_of_distinguished (HomotopyCategory.subcategoryAcyclic (Shv R)) _
    (HomotopyCategory.mappingCone_triangleh_distinguished f)).trans
    (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _))

theorem cone_ge {R : Type} [CommRing R] {I I' : Cx R} [I.IsStrictlyGE 0] [I'.IsStrictlyGE 0] (f : I ⟶ I') :
    (mappingCone f).IsStrictlyGE (-1) :=
  CochainComplex.isStrictlyGE_mappingCone f 0 0 (-1)

theorem LateralTheory.EtaleFoundations.etale_tensor_preserves_quasiIso_of_acyclic_and_cone (hA : LateralTheory.EtaleFoundations.tqis.acyc) (hC : LateralTheory.EtaleFoundations.tqis.cone) :
    LateralTheory.EtaleFoundations.EtaleTensorPairQuasiIsoOfFlatQuasiIso := by
  intro R _ I I' J T T' _ _ _ τ τ' hτ hτ' hJ f _ u hc
  obtain ⟨σ, hσ⟩ := hC R τ τ' f u hτ hτ' hc
  have := cone_ge f
  rw [qis_iff_cone]
  exact hA R (-1) 0 σ hσ hJ ((qis_iff_cone f).1 inferInstance)
end

section -- merged from Development.EtaleCohomology.TateTwists.EtaleTwistResolutionUniversalExtension
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

def LateralTheory.EtaleFoundations.EtaleTwistResolutionUniversalExtension : Prop :=
  ∀ (q : ℕ) [NeZero q] (i : ℤ), IsTwRes q i (res _ (tw q i)) (fun _ ζ => resGen i ζ) ∧ (∀ t, FlatS ((res _ (tw q i)).X t)) ∧ ∀ {T : Cx (ZMod q)} (e : ∀ U : Scheme.{0}, Prim q Γ(U, ⊤) → Sec (T.X 0) U), IsTwRes q i T e → (∃ u : T ⟶ res _ (tw q i), ∀ U ζ, Sec.map (u.f 0) (e U ζ) = resGen i ζ) ∧ ∀ u u' : T ⟶ res _ (tw q i), (∀ U ζ, Sec.map (u.f 0) (e U ζ) = Sec.map (u'.f 0) (e U ζ)) → Nonempty (Homotopy u u')
end

section -- merged from Development.EtaleCohomology.TateTwists.EtaleCochainExistsOfNaturalEvaluation
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

def LateralTheory.EtaleFoundations.EtaleCochainExistsOfNaturalEvaluation : Prop :=
  ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ} (a : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + n = s → ∀ U : Scheme.{0}, Sx E p U → Sec (I.X s) U), (∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (a p s h U x) = a p s h V (x.res g)) → ∃ α : Cochain ((chains R).obj E) I n, ∀ p s h U x, ev (R := R) α p s h U x = a p s h U x
end

section -- merged from Development.EtaleCohomology.TateTwists.EtaleCochainSemilinearMapCompCompatible
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

def LateralTheory.EtaleFoundations.EtaleCochainSemilinearMapCompCompatible : Prop :=
  ∀ (S R : Type) [CommRing S] [CommRing R] {I : Cx S} {J J' : Cx R} (ρ : SemiMap I J) (ρ' : SemiMap I J') (u : J ⟶ J'), (∀ (U : Scheme.{0}) (s : ℤ) (a : Sec (I.X s) U), ρ'.app U s a = Sec.map (u.f s) (ρ.app U s a)) → (∀ (E : Spc) (n : ℤ) x, ρ'.op.app E n x = cpush _ u n (ρ.op.app E n x)) ∧ ((∀ (U : Scheme.{0}) (s : ℤ), Function.Bijective (ρ.app U s)) → ∀ (E : Spc) (n : ℤ), Function.Bijective (ρ.op.app E n))
end

section -- merged from Development.EtaleCohomology.TateTwists.EtaleInjectiveResolutionBasicProperties
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

def LateralTheory.EtaleFoundations.EtaleInjectiveResolutionBasicProperties : Prop :=
  ∀ (R : Type) [CommRing R] (F : Shv R), (res R F).IsKInjective ∧ (∀ n, Injective ((res R F).X n)) ∧ (res R F).IsStrictlyGE 0 ∧ QuasiIso (resAug F) ∧ sglι F ≫ (resAug F).f 0 = resι R F ∧ Mono (resι R F) ∧ resι R F ≫ (res R F).d 0 1 = 0 ∧ ∀ (G : Shv R) (φ : F ⟶ G), resAug F ≫ resMap R φ = (CochainComplex.singleFunctor (Shv R) 0).map φ ≫ resAug G ∧ resι R F ≫ (resMap R φ).f 0 = φ ≫ resι R G
end

section -- merged from Development.EtaleCohomology.TateTwists.EtaleSheafShortComplexExactIffLocallyLifts
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

def LateralTheory.EtaleFoundations.EtaleSheafShortComplexExactIffLocallyLifts : Prop :=
  ∀ (R : Type) [CommRing R] (S : ShortComplex (Shv R)), S.Exact ↔ ∀ U (b : Sec S.X₂ U), Sec.map S.g b = 0 → Loc U fun V g => ∃ a : Sec S.X₁ V, Sec.map S.f a = Sec.res g b
end

section -- merged from Development.EtaleCohomology.TateTwists.EtaleTensorPairProductAssociative
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

def LateralTheory.EtaleFoundations.EtaleTensorPairProductAssociative : Prop :=
  ∀ (R : Type) [CommRing R] {I J K T T3 : Cx R} (τ : Pair I J T) (τ' : Pair T K T3), τ.IsTensor → τ'.IsTensor → ∀ {M L : Cx R} (μ' : Pair J K M) (ν' : Pair I M L), ∃ ν : Pair T K L, ∀ (U : Scheme.{0}) (s t u st tu w : ℤ) (h1 : s + t = st) (h2 : st + u = w) (h3 : t + u = tu) (h4 : s + tu = w) a b c, ν.mul U st u w h2 (τ.mul U s t st h1 a b) c = ν'.mul U s tu w h4 a (μ'.mul U t u tu h3 b c)
end

section -- merged from Development.EtaleCohomology.TateTwists.EtaleCochainSemilinearMapOnClasses
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

def LateralTheory.EtaleFoundations.EtaleCochainSemilinearMapOnClasses : Prop :=
  ∀ (S R : Type) [CommRing S] [CommRing R] {I : Cx S} {J : Cx R} (ρ : SemiMap I J), (∀ (E : Spc) (n : ℤ) (α : Cocycle ((chains S).obj E) I n), ∃ β : Cocycle ((chains R).obj E) J n, ρ.IsImage α.1 β.1) ∧ ∀ (E : Spc) (n : ℤ) (α : Cocycle ((chains S).obj E) I n) (β : Cocycle ((chains R).obj E) J n), ρ.IsImage α.1 β.1 → ρ.op.app E n (CohomologyClass.mk α) = CohomologyClass.mk β
end

section -- merged from Development.EtaleCohomology.TateTwists.EtaleCupProductNaturalInCoefficients
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

def LateralTheory.EtaleFoundations.EtaleCupProductNaturalInCoefficients : Prop :=
  ∀ (R : Type) [CommRing R] {I J K I' J' K' : Cx R} (μ : Pair I J K) (ν : Pair I' J' K') (f : I ⟶ I') (g : J ⟶ J') (u : K ⟶ K'), μ.Compat ν f g u → ∀ (E : Spc) {n m k : ℤ} (hk : n + m = k) a b, cpush _ u k (μ.cup E hk a b) = ν.cup E hk (cpush _ f n a) (cpush _ g m b)
end

section -- merged from Development.EtaleCohomology.TateTwists.EtaleSimplexSubfaceComposition
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

def LateralTheory.EtaleFoundations.EtaleSimplexSubfaceComposition : Prop :=
  ∀ {E : Spc} {U : Scheme.{0}} {N : ℕ} (x : Sx E N U), (∀ (j l j' l' : ℕ) (h : j + l ≤ N) (h' : j' + l' ≤ l), (x.sub j l h).sub j' l' h' = x.sub (j + j') l' (by omega)) ∧ x.sub 0 N (by omega) = x ∧ (∀ (j l : ℕ) (h : j + l ≤ N), (∀ {V : Scheme.{0}} (g : V ⟶ U), (x.res g).sub j l h = (x.sub j l h).res g) ∧ (∀ {E' : Spc} (f : E ⟶ E'), (x.map f).sub j l h = (x.sub j l h).map f) ∧ x.sub j l h = x.along (SimplexCategory.subinterval j l h)) ∧ ∀ {p r : ℕ} (a : SimplexCategory.mk p ⟶ SimplexCategory.mk N) (b : SimplexCategory.mk r ⟶ SimplexCategory.mk p), (x.along a).along b = x.along (b ≫ a)
end

section -- merged from Development.EtaleCohomology.TateTwists.EtaleCochainCupAssociativeOfPairing
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

def LateralTheory.EtaleFoundations.EtaleCochainCupAssociativeOfPairing : Prop :=
  ∀ (R : Type) [CommRing R] {I J K M M' L : Cx R} (μ : Pair I J M) (ν : Pair M K L) (μ' : Pair J K M') (ν' : Pair I M' L), (∀ (U : Scheme.{0}) (s t u st tu w : ℤ) (h1 : s + t = st) (h2 : st + u = w) (h3 : t + u = tu) (h4 : s + tu = w) a b c, ν.mul U st u w h2 (μ.mul U s t st h1 a b) c = ν'.mul U s tu w h4 a (μ'.mul U t u tu h3 b c)) → ∀ (E : Spc) {n m k nm mk w : ℤ} (h1 : n + m = nm) (h2 : nm + k = w) (h3 : m + k = mk) (h4 : n + mk = w) a b c, ν.cup E h2 (μ.cup E h1 a b) c = ν'.cup E h4 a (μ'.cup E h3 b c)
end

section -- merged from Development.EtaleCohomology.TateTwists.PrimitiveRootsOfUnityBasicIdentities
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

def LateralTheory.EtaleFoundations.PrimitiveRootsOfUnityBasicIdentities : Prop :=
  ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], (∀ ζ : Prim q A, ζ.1 ^ q = 1) ∧ (∀ (ζ : Prim q A) (a : ℕ), Nat.Coprime a q → ∃ ξ : Prim q A, ξ.1 = ζ.1 ^ a) ∧ (∀ (ζ : Prim q A) (a b : ℕ), ¬ a ≡ b [MOD q] → IsUnit (ζ.1 ^ a - ζ.1 ^ b)) ∧ (∀ (ζ : Prim q A) (x : A), x ^ q = 1 → ∏ a ∈ Finset.range q, (x - ζ.1 ^ a) = 0) ∧ (∀ (ζ ξ : Prim q A), ∏ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), (ξ.1 - ζ.1 ^ a) = 0) ∧ ∀ (r : ℕ), r ∣ q → ∀ ζ : Prim q A, ∃ ξ : Prim r A, ξ.1 = ζ.1 ^ (q / r)
end

section -- merged from Development.EtaleCohomology.TateTwists.EtaleRootsOfUnityReductionMapGenerator
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

def LateralTheory.EtaleFoundations.EtaleRootsOfUnityReductionMapGenerator : Prop :=
  ∀ (Q q : ℕ) [NeZero Q] [NeZero q], q ∣ Q → ∀ (i : ℤ) (U : Scheme.{0}) (ζ : Prim Q Γ(U, ⊤)) (ξ : Prim q Γ(U, ⊤)), ξ.1 = ζ.1 ^ (Q / q) → (redMap Q q i).app U 0 (resGen i ζ) = resGen i ξ
end

section -- merged from Development.EtaleCohomology.TateTwists.EtaleKInjectiveHomExtendsAlongQuasiIso
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

def LateralTheory.EtaleFoundations.EtaleKInjectiveHomExtendsAlongQuasiIso : Prop :=
  ∀ (R : Type) [CommRing R] (F : Shv R) (T I : Cx R) [I.IsKInjective] [I.IsStrictlyGE 0] (ε : sgl F ⟶ T) [QuasiIso ε], (∀ a : sgl F ⟶ I, ∃ m : T ⟶ I, ε ≫ m = a) ∧ ∀ m m' : T ⟶ I, ε ≫ m = ε ≫ m' → Nonempty (Homotopy m m')
end

section -- merged from Development.EtaleCohomology.TateTwists.EtaleRestrictScalarsResolutionCompatible
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

def LateralTheory.EtaleFoundations.EtaleRestrictScalarsResolutionCompatible : Prop :=
  ∀ (R S : Type) [CommRing R] [CommRing S] (φ : R →+* S) (F : Shv S)
    (U : Scheme.{0}) (a : Sec F U),
    (GlobalTheory.EtC.restrMap φ F).app U 0 (Sec.map (resι S F) a) =
      Sec.map (resι R ((restr φ).obj F)) (show Sec ((restr φ).obj F) U from a)
end

section -- merged from Development.EtaleCohomology.TateTwists.EtaleCochainEvaluationCoboundaryFormula
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

def LateralTheory.EtaleFoundations.EtaleCochainEvaluationCoboundaryFormula : Prop :=
  ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n m : ℤ} (hm : n + 1 = m)
    (α : Cochain ((chains R).obj E) I n) (U : Scheme.{0}),
    (∀ x : Sx E 0 U, ev (δ n m α) 0 m (by simp) U x = Sec.map (I.d n m) (ev α 0 n (by simp) U x)) ∧
    ∀ (p : ℕ) (s t : ℤ) (hs : -((p + 1 : ℕ) : ℤ) + n = s) (ht : -((p + 1 : ℕ) : ℤ) + m = t)
      (x : Sx E (p + 1) U),
      ev (δ n m α) (p + 1) t ht U x = Sec.map (I.d s t) (ev α (p + 1) s hs U x) +
        m.negOnePow • ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • ev α p t (by omega) U (x.face i)
end

section -- merged from Development.EtaleCohomology.TateTwists.FirstChernSpecOfRepresentative
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

def IsEtaleFirstChernKummerCocycleRep (q : ℕ) {E : Spc} (L : E ⟶ ofCat (glCat 1)) (γ : Cocycle ((chains (ZMod q)).obj E) (res _ (tw q 1)) 2) : Prop :=
  (∀ (U : Scheme.{0}) (x : Sx E 0 U), ev γ.1 0 2 (by simp) U x = 0) ∧
    (∀ (U : Scheme.{0}) (x : Sx E 1 U) (v : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L x →
      ev γ.1 1 1 (by simp) U x = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q U v)) ∧
    ∀ (U : Scheme.{0}) (x : Sx E 2 U) (v w : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L (x.sub 0 1 (by omega)) →
      w ^ q = lineUnit L (x.sub 1 1 (by omega)) →
      ev γ.1 2 0 (by simp) U x = kumT q U v + kumT q U w - kumT q U (v * w)

def first_chern_class_exists : Prop := ∀ (q : ℕ) [NeZero q] {E : Spc} (L : E ⟶ ofCat (glCat 1)), Inv q E → ∃ γ, IsEtaleFirstChernKummerCocycleRep q L γ

end LateralTheory.EtaleFoundations
end

section -- merged from Development.EtaleCohomology.TateTwists.CupGradedCommOfFlip
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

def cupflip_wd : Prop :=
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) (E : Spc) {n m k : ℤ} (hk : n + m = k),
    ∃ c : CohomologyClass ((chains R).obj E) I n →+ CohomologyClass ((chains R).obj E) J m →+
        CohomologyClass ((chains R).obj E) K k,
      ∀ (α : Cocycle _ I n) (β : Cocycle _ J m) (γ : Cocycle _ K k), μ.IsAW hk α.1 β.1 γ.1 →
        c (CohomologyClass.mk α) (CohomologyClass.mk β) = CohomologyClass.mk γ

def cupflip_aw_exists : Prop :=
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) (E : Spc) {n m k : ℤ} (hk : n + m = k)
    (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m),
    ∃ γ : Cocycle ((chains R).obj E) K k, μ.IsAW hk α.1 β.1 γ.1

def cupflip_aw_flip : Prop :=
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) (ν : Pair J I K), μ.IsFlip ν →
    ∀ (E : Spc) {n m k : ℤ} (h : n + m = k) (h' : m + n = k)
      (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m)
      (γ γ' : Cocycle ((chains R).obj E) K k),
      μ.IsAW h α.1 β.1 γ.1 → ν.IsAW h' β.1 α.1 γ'.1 →
        CohomologyClass.mk γ = (n * m).negOnePow • CohomologyClass.mk γ'

end LateralTheory.EtaleFoundations
end

section -- merged from Development.EtaleCohomology.TateTwists.EtaleShortComplexExactIffLocallySurjectiveOnKern
section -- merged from Development.EtaleCohomology.TateTwists.EtaleTensorAcyclicOfFlatBounded
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

def LateralTheory.EtaleFoundations.EtaleTensorAcyclicOfFlatBounded : Prop :=
  ∀ (R : Type) [CommRing R] {C J T : Cx R} (a b : ℤ) [C.IsStrictlyGE a] [J.IsStrictlyGE b] (τ : Pair C J T), τ.IsTensor → (∀ t, FlatS (J.X t)) → C.Acyclic → T.Acyclic
end

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

def EtaleShortComplexExactIffLocallySurjectiveOnKernel : Prop :=
  ∀ (R : Type) [CommRing R] (S : ShortComplex (Shv R)), S.Exact ↔
    ∀ U (b : Sec S.X₂ U), Sec.map S.g b = 0 → Loc U fun V g => ∃ a : Sec S.X₁ V, Sec.map S.f a = Sec.res g b

def EtaleTensorComplexLocallyExactOfFlatBounded : Prop :=
  ∀ (R : Type) [CommRing R] {C J T : Cx R} (a b : ℤ) [C.IsStrictlyGE a] [J.IsStrictlyGE b] (τ : Pair C J T),
    τ.IsTensor → (∀ t, FlatS (J.X t)) →
    (∀ (s : ℤ) (U : Scheme.{0}) (y : Sec (C.sc s).X₂ U), Sec.map (C.sc s).g y = 0 →
      Loc U fun V g => ∃ x : Sec (C.sc s).X₁ V, Sec.map (C.sc s).f x = Sec.res g y) →
    ∀ (w : ℤ) (U : Scheme.{0}) (y : Sec (T.sc w).X₂ U), Sec.map (T.sc w).g y = 0 →
      Loc U fun V g => ∃ x : Sec (T.sc w).X₁ V, Sec.map (T.sc w).f x = Sec.res g y

theorem etale_tensor_complex_acyclic_of_locally_exact_flat (hE : EtaleShortComplexExactIffLocallySurjectiveOnKernel) (hS : EtaleTensorComplexLocallyExactOfFlatBounded) :
    EtaleTensorAcyclicOfFlatBounded := by
  intro R _ C J T a b _ _ τ hτ hJ hC w
  have hCl := fun s => (hE R (C.sc s)).1 (hC s)
  exact (hE R (T.sc w)).2 (hS R a b τ hτ hJ hCl w)

end LateralTheory.EtaleFoundations
end

section -- merged from Development.EtaleCohomology.TateTwists.EtaleSheafSectionLocallyIffOfPresheafFacts
section -- merged from Development.EtaleCohomology.TateTwists.EtaleLocalIffAffineEtaleCoverPointwise
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

def LateralTheory.EtaleFoundations.EtaleLocalIffAffineEtaleCoverPointwise : Prop :=
  ∀ (U : Scheme.{0}) (P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop), (∀ (V W : Scheme.{0}) (g : V ⟶ U) (k : W ⟶ V), P V g → P W (k ≫ g)) → (Loc U P ↔ ∀ x : U, ∃ (V : Scheme.{0}) (g : V ⟶ U), IsAffine V ∧ Etale g ∧ x ∈ Set.range g ∧ P V g)
end

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

theorem etale_sheaf_section_locally_iff_of_presheaf_facts : EtaleLocalIffAffineEtaleCoverPointwise := by
  intro U P hP
  constructor
  · rintro ⟨S, hS, hSP⟩ x
    obtain ⟨𝒰, hle⟩ := (Scheme.mem_grothendieckTopology_iff (P := (@Etale : MorphismProperty Scheme.{0}))).mp hS
    obtain ⟨i, y, hy⟩ := ((Scheme.presieve₀_mem_precoverage_iff _).mp 𝒰.mem₀).1 x
    let 𝒱 := (𝒰.X i).affineCover
    obtain ⟨z, hz⟩ := 𝒱.covers y
    refine ⟨𝒱.X (𝒱.idx y), 𝒱.f (𝒱.idx y) ≫ 𝒰.f i, inferInstance, ?_, ⟨z, ?_⟩, ?_⟩
    · have : Etale (𝒰.f i) := 𝒰.map_prop i
      infer_instance
    · simp only [Scheme.Hom.comp_apply, hz, hy]
    · exact hSP _ _ (S.downward_closed (hle _ _ (Presieve.ofArrows.mk i)) _)
  · intro h
    choose V g hA hE hx hPg using h
    refine ⟨{ arrows := fun W k => P W k, downward_closed := fun {Y Z f} hf k => hP Y Z f k hf }, ?_, ?_⟩
    · refine (Scheme.mem_grothendieckTopology_iff (P := (@Etale : MorphismProperty Scheme.{0}))).mpr ⟨Scheme.Cover.mkOfCovers (P := (@Etale : MorphismProperty Scheme.{0})) U V g (fun x => ⟨x, hx x⟩) (fun x => hE x), ?_⟩
      rintro W k ⟨x⟩
      exact hPg x
    · intro W k hk
      exact hk

end LateralTheory.EtaleFoundations
end

section -- merged from Development.EtaleCohomology.TateTwists.EtaleTwistedCupGradedCommOfFlipAndUniquePairing
section -- merged from Development.EtaleCohomology.TateTwists.EtaleTwistedCupProductGradedCommutative
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

def LateralTheory.EtaleFoundations.EtaleTwistedCupProductGradedCommutative : Prop :=
  ∀ (q : ℕ) [NeZero q] (E : Spc) {n m i j : ℤ} (a : Ht q E n i) (b : Ht q E m j), cup q a b = (n * m).negOnePow • (cup q b a).cast (by ring) (by ring)
end

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

def LateralTheory.EtaleFoundations.cc_cup_flip : Prop :=
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) (ν : Pair J I K), μ.IsFlip ν → ∀ (E : Spc) {n m k : ℤ}
    (h : n + m = k) (h' : m + n = k) a b, μ.cup E h a b = (n * m).negOnePow • ν.cup E h' b a

def LateralTheory.EtaleFoundations.cc_flip_ex : Prop :=
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K), ∃ ν : Pair J I K, μ.IsFlip ν

def LateralTheory.EtaleFoundations.cc_twpair : Prop :=
  ∀ (q : ℕ) [NeZero q] (i j : ℤ), IsTwPair (twPair q i j) ∧ ∀ (k : ℤ), i + j = k →
    ∀ μ ν : Pair (res _ (tw q i)) (res _ (tw q j)) (res _ (tw q k)), IsTwPair μ → IsTwPair ν →
    ∀ (E : Spc) {n m w : ℤ} (h : n + m = w), μ.cup E h = ν.cup E h

theorem LateralTheory.EtaleFoundations.cc_cup_eq_of_twPair (htw : LateralTheory.EtaleFoundations.cc_twpair) (q : ℕ) [NeZero q] (E : Spc) {n m i j : ℤ}
    (a : Ht q E n i) (b : Ht q E m j) (k : ℤ) (hk : j + i = k)
    (ν : Pair (res _ (tw q j)) (res _ (tw q i)) (res _ (tw q k))) (hν : IsTwPair ν) (w : ℤ) (hw : m + n = w) :
    ν.cup E hw b a = (cup q b a).cast hw hk := by
  subst hk hw
  obtain ⟨h1, h2⟩ := htw q j i
  have := h2 (j + i) rfl ν (twPair q j i) hν h1 E (n := m) (m := n) rfl
  rw [this]
  rfl

theorem LateralTheory.EtaleFoundations.etale_twisted_cup_graded_comm_of_flip_and_unique_pairing (hflip : LateralTheory.EtaleFoundations.cc_cup_flip) (hex : LateralTheory.EtaleFoundations.cc_flip_ex)
    (htw : LateralTheory.EtaleFoundations.cc_twpair) : LateralTheory.EtaleFoundations.EtaleTwistedCupProductGradedCommutative := by
  intro q _ E n m i j a b
  obtain ⟨ν, hν⟩ := hex (ZMod q) (twPair q i j)
  have hνtw : IsTwPair ν := by
    intro U ζ
    have := hν U 0 0 0 (add_zero 0) (resGen i ζ) (resGen j ζ)
    rw [this, (htw q i j).1 U ζ]
    simp
  have e1 : cup q a b = (n * m).negOnePow • ν.cup E (add_comm m n) b a :=
    hflip (ZMod q) (twPair q i j) ν hν E rfl (add_comm m n) a b
  rw [e1, LateralTheory.EtaleFoundations.cc_cup_eq_of_twPair htw q E a b (i + j) (add_comm j i) ν hνtw (n + m) (add_comm m n)]
end

section -- merged from Development.EtaleCohomology.TateTwists.EtaleTwistedCupAssocOfTwistedPairingExistsAssoc
section -- merged from Development.EtaleCohomology.TateTwists.EtaleTwistedCupProductAssociative
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

def LateralTheory.EtaleFoundations.EtaleTwistedCupProductAssociative : Prop :=
  ∀ (q : ℕ) [NeZero q] (E : Spc) {n m k i j l : ℤ} (a : Ht q E n i) (b : Ht q E m j) (c : Ht q E k l), cup q (cup q a b) c = (cup q a (cup q b c)).cast (by ring) (by ring)
end

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

def t_twpair_ex : Prop :=
  ∀ (q : ℕ) [NeZero q] (i j : ℤ), ∃ μ : Pair (res _ (tw q i)) (res _ (tw q j)) (res _ (tw q (i + j))), IsTwPair μ

def t_pair_assoc : Prop :=
  ∀ (q : ℕ) [NeZero q] (E : Spc) {i j l k₁ k₂ k : ℤ} (_ : i + j = k₁) (_ : j + l = k₂) (_ : i + k₂ = k)
    (μ₁ : Pair (res _ (tw q i)) (res _ (tw q j)) (res _ (tw q k₁)))
    (μ₂ : Pair (res _ (tw q k₁)) (res _ (tw q l)) (res _ (tw q k)))
    (ν₁ : Pair (res _ (tw q j)) (res _ (tw q l)) (res _ (tw q k₂)))
    (ν₂ : Pair (res _ (tw q i)) (res _ (tw q k₂)) (res _ (tw q k))),
    IsTwPair μ₁ → IsTwPair μ₂ → IsTwPair ν₁ → IsTwPair ν₂ →
    ∀ {n m p s₁ s₂ s : ℤ} (h₁ : n + m = s₁) (h₂ : s₁ + p = s) (h₃ : m + p = s₂) (h₄ : n + s₂ = s)
      (a : Ht q E n i) (b : Ht q E m j) (c : Ht q E p l),
      μ₂.cup E h₂ (μ₁.cup E h₁ a b) c = ν₂.cup E h₄ a (ν₁.cup E h₃ b c)

theorem cast_pair_cup {q : ℕ} {E : Spc} {i j k k' n m s s' : ℤ}
    (μ : Pair (res _ (tw q i)) (res _ (tw q j)) (res _ (tw q k))) (e : k = k') (hk : n + m = s) (hs : s = s')
    (a : Ht q E n i) (b : Ht q E m j) :
    Ht.cast hs e (μ.cup E hk a b : Ht q E s k) = (e ▸ μ : Pair _ _ (res _ (tw q k'))).cup E (hk.trans hs) a b := by
  subst e; subst hs; rfl

theorem isTwPair_cast {q : ℕ} {i j k k' : ℤ}
    (μ : Pair (res _ (tw q i)) (res _ (tw q j)) (res _ (tw q k))) (e : k = k') (h : IsTwPair μ) :
    IsTwPair (e ▸ μ : Pair _ _ (res _ (tw q k'))) := by
  subst e; exact h

theorem etale_twisted_cup_assoc_of_twisted_pairing_exists_assoc (hex : t_twpair_ex) (has : t_pair_assoc) : EtaleTwistedCupProductAssociative := by
  intro q _ E n m k i j l a b c
  have hp : ∀ i j : ℤ, IsTwPair (twPair q i j) := fun i j => pick_spec (hex q i j)
  have e : i + (j + l) = i + j + l := by ring
  have hs : n + (m + k) = n + m + k := by ring
  show (twPair q (i + j) l).cup E rfl ((twPair q i j).cup E rfl a b) c =
    Ht.cast hs e ((twPair q i (j + l)).cup E rfl a ((twPair q j l).cup E rfl b c))
  rw [cast_pair_cup]
  exact has q E rfl rfl e _ _ _ _ (hp i j) (hp (i + j) l) (hp j l) (isTwPair_cast _ e (hp i (j + l)))
    rfl rfl rfl (rfl.trans hs) a b c

end LateralTheory.EtaleFoundations
end

section -- merged from Development.EtaleCohomology.TateTwists.EtaleKummerClassSpecificationOfExistenceNaturali
section -- merged from Development.EtaleCohomology.TateTwists.EtaleKummerClassExplicitCocycle
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

def LateralTheory.EtaleFoundations.EtaleKummerClassExplicitCocycle : Prop :=
  ∀ (q : ℕ) [NeZero q],
    (∀ (X : Scheme.{0}) (u : (Γ(X, ⊤))ˣ), IsUnit (q : Γ(X, ⊤)) →
      ∃ γ : Cocycle ((chains (ZMod q)).obj (sch.obj X)) (res _ (tw q 1)) 1,
        CohomologyClass.mk γ = kum q u ∧
        (∀ (U : Scheme.{0}) (x : U ⟶ X), ev γ.1 1 0 (by simp) U x = 0) ∧
        ∀ (U : Scheme.{0}) (x : U ⟶ X) (v : (Γ(U, ⊤))ˣ),
          v ^ q = Units.map x.appTop.hom.toMonoidHom u →
          ev γ.1 0 1 (by simp) U x = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q U v)) ∧
    (∀ {Y X : Scheme.{0}} (f : Y ⟶ X) (u : (Γ(X, ⊤))ˣ), IsUnit (q : Γ(X, ⊤)) →
      pull _ (sch.map f) _ _ (kum q u) = kum q (Units.map f.appTop.hom.toMonoidHom u)) ∧
    ∀ {X : Scheme.{0}} (u v : (Γ(X, ⊤))ˣ), IsUnit (q : Γ(X, ⊤)) →
      kum q (u * v) = kum q u + kum q v ∧ kum q (u ^ q) = 0
end

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

def kum_exists : Prop :=
  ∀ (q : ℕ) [NeZero q] (X : Scheme.{0}) (u : (Γ(X, ⊤))ˣ), IsUnit (q : Γ(X, ⊤)) →
    ∃ γ : Cocycle ((chains (ZMod q)).obj (sch.obj X)) (res _ (tw q 1)) 1,
      (∀ (U : Scheme.{0}) (x : U ⟶ X), ev γ.1 1 0 (by simp) U x = 0) ∧
      ∀ (U : Scheme.{0}) (x : U ⟶ X) (v : (Γ(U, ⊤))ˣ), v ^ q = Units.map x.appTop.hom.toMonoidHom u →
        ev γ.1 0 1 (by simp) U x = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q U v)

def kum_nat : Prop :=
  ∀ (q : ℕ) [NeZero q] {Y X : Scheme.{0}} (f : Y ⟶ X) (u : (Γ(X, ⊤))ˣ), IsUnit (q : Γ(X, ⊤)) →
    pull _ (sch.map f) _ _ (kum q u) = kum q (Units.map f.appTop.hom.toMonoidHom u)

def kum_add : Prop :=
  ∀ (q : ℕ) [NeZero q] {X : Scheme.{0}} (u v : (Γ(X, ⊤))ˣ), IsUnit (q : Γ(X, ⊤)) →
    kum q (u * v) = kum q u + kum q v ∧ kum q (u ^ q) = 0

theorem kum_spec_of_exists (he : kum_exists) (q : ℕ) [NeZero q] (X : Scheme.{0}) (u : (Γ(X, ⊤))ˣ)
    (hq : IsUnit (q : Γ(X, ⊤))) :
    ∃ γ : Cocycle ((chains (ZMod q)).obj (sch.obj X)) (res _ (tw q 1)) 1, CohomologyClass.mk γ = kum q u ∧
      (∀ (U : Scheme.{0}) (x : U ⟶ X), ev γ.1 1 0 (by simp) U x = 0) ∧
      ∀ (U : Scheme.{0}) (x : U ⟶ X) (v : (Γ(U, ⊤))ˣ), v ^ q = Units.map x.appTop.hom.toMonoidHom u →
        ev γ.1 0 1 (by simp) U x = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q U v) := by
  obtain ⟨γ, h1, h2⟩ := he q X u hq
  unfold kum
  exact pick_spec (P := fun c => ∃ γ : Cocycle ((chains (ZMod q)).obj (sch.obj X)) (res _ (tw q 1)) 1,
      CohomologyClass.mk γ = c ∧ (∀ (U : Scheme.{0}) (x : U ⟶ X), ev γ.1 1 0 (by simp) U x = 0) ∧
      ∀ (U : Scheme.{0}) (x : U ⟶ X) (v : (Γ(U, ⊤))ˣ), v ^ q = Units.map x.appTop.hom.toMonoidHom u →
        ev γ.1 0 1 (by simp) U x = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q U v))
    ⟨CohomologyClass.mk γ, γ, rfl, h1, h2⟩

theorem etale_kummer_class_specification_of_existence_naturality_additivity (he : kum_exists) (hn : kum_nat) (ha : kum_add) : EtaleKummerClassExplicitCocycle := by
  intro q _
  exact ⟨fun X u hq => kum_spec_of_exists he q X u hq, fun f u hq => hn q f u hq, fun u v hq => ha q u v hq⟩

end LateralTheory.EtaleFoundations
end

section -- merged from Development.EtaleCohomology.TateTwists.EtaleTateTwistCupPairingOfTensorAndResolutionPro
section -- merged from Development.EtaleCohomology.TateTwists.EtaleTwistResolutionPairingCupUnique
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

def LateralTheory.EtaleFoundations.EtaleTwistResolutionPairingCupUnique : Prop :=
  ∀ (q : ℕ) [NeZero q] (i j : ℤ), IsTwPair (twPair q i j) ∧ ∀ (k : ℤ), i + j = k → ∀ μ ν : Pair (res _ (tw q i)) (res _ (tw q j)) (res _ (tw q k)), IsTwPair μ → IsTwPair ν → ∀ (E : Spc) {n m w : ℤ} (h : n + m = w), μ.cup E h = ν.cup E h
end

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

def twpair_tens_ex : Prop :=
  ∀ (R : Type) [CommRing R] (I J : Cx R), ∃ (K : Cx R) (τ : Pair I J K), τ.IsTensor

def twpair_tens_univ : Prop :=
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (τ : Pair I J K), τ.IsTensor → (∀ {I' J' K' : Cx R} (ν : Pair I' J' K') (f : I ⟶ I') (g : J ⟶ J'), ∃! u : K ⟶ K', τ.Compat ν f g u) ∧ (I.IsStrictlyGE 0 → J.IsStrictlyGE 0 → K.IsStrictlyGE 0) ∧ ∀ {K' : Cx R} (u : K ⟶ K'), ∃ ν : Pair I J K', τ.Compat ν (𝟙 I) (𝟙 J) u

def twpair_tens_twres : Prop :=
  ∀ (q : ℕ) [NeZero q] (i j k : ℤ), i + j = k → ∀ {I J T : Cx (ZMod q)} (e : ∀ U : Scheme.{0}, Prim q Γ(U, ⊤) → Sec (I.X 0) U) (e' : ∀ U : Scheme.{0}, Prim q Γ(U, ⊤) → Sec (J.X 0) U), IsTwRes q i I e → IsTwRes q j J e' → (∀ t, FlatS (J.X t)) → ∀ τ : Pair I J T, τ.IsTensor → IsTwRes q k T fun U ζ => τ.mul U 0 0 0 (add_zero 0) (e U ζ) (e' U ζ)

def twpair_twres_ext : Prop :=
  ∀ (q : ℕ) [NeZero q] (i : ℤ), IsTwRes q i (res _ (tw q i)) (fun _ ζ => resGen i ζ) ∧ (∀ t, FlatS ((res _ (tw q i)).X t)) ∧ ∀ {T : Cx (ZMod q)} (e : ∀ U : Scheme.{0}, Prim q Γ(U, ⊤) → Sec (T.X 0) U), IsTwRes q i T e → (∃ u : T ⟶ res _ (tw q i), ∀ U ζ, Sec.map (u.f 0) (e U ζ) = resGen i ζ) ∧ ∀ u u' : T ⟶ res _ (tw q i), (∀ U ζ, Sec.map (u.f 0) (e U ζ) = Sec.map (u'.f 0) (e U ζ)) → Nonempty (Homotopy u u')

def twpair_cup_compat : Prop :=
  ∀ (R : Type) [CommRing R] {I J K I' J' K' : Cx R} (μ : Pair I J K) (ν : Pair I' J' K') (f : I ⟶ I') (g : J ⟶ J') (u : K ⟶ K'), μ.Compat ν f g u → ∀ (E : Spc) {n m k : ℤ} (hk : n + m = k) a b, cpush _ u k (μ.cup E hk a b) = ν.cup E hk (cpush _ f n a) (cpush _ g m b)

def twpair_zc_fun : Prop :=
  ∀ (R : Type) [CommRing R] , (∀ (K I : Cx R) (n : ℤ) x, cpull (𝟙 K) I n x = x ∧ cpush K (𝟙 I) n x = x) ∧ (∀ {K L M : Cx R} (f : K ⟶ L) (g : L ⟶ M) (I : Cx R) (n : ℤ) x, cpull (f ≫ g) I n x = cpull f I n (cpull g I n x)) ∧ (∀ (K : Cx R) {I J M : Cx R} (f : I ⟶ J) (g : J ⟶ M) (n : ℤ) x, cpush K (f ≫ g) n x = cpush K g n (cpush K f n x)) ∧ (∀ {K L I J : Cx R} (f : K ⟶ L) (g : I ⟶ J) (n : ℤ) x, cpull f J n (cpush L g n x) = cpush K g n (cpull f I n x)) ∧ (∀ {K L : Cx R} (f g : K ⟶ L), Nonempty (Homotopy f g) → ∀ (I : Cx R) (n : ℤ), cpull f I n = cpull g I n ∧ cpush I f n = cpush I g n)

theorem etale_tate_twist_cup_pairing_of_tensor_and_resolution_properties (h1 : twpair_tens_ex) (h2 : twpair_tens_univ) (h3 : twpair_tens_twres)
    (h4 : twpair_twres_ext) (h5 : twpair_cup_compat) (h6 : twpair_zc_fun) : LateralTheory.EtaleFoundations.EtaleTwistResolutionPairingCupUnique := by
  intro q _ i j
  obtain ⟨T, τ, hτ⟩ := h1 (ZMod q) (res _ (tw q i)) (res _ (tw q j))
  have hT := h3 q i j (i + j) rfl _ _ (h4 q i).1 (h4 q j).1 (h4 q j).2.1 τ hτ
  obtain ⟨⟨u, hu⟩, hhom⟩ := (h4 q (i + j)).2.2 _ hT
  refine ⟨?_, ?_⟩
  · obtain ⟨ν, hν⟩ := (h2 (ZMod q) τ hτ).2.2 u
    apply pick_spec
    refine ⟨ν, fun U ζ => ?_⟩
    have := hν U 0 0 0 (add_zero 0) (resGen i ζ) (resGen j ζ)
    rw [← hu U ζ, this]
    rfl
  · intro k hk μ ν hμ hν E n m w h
    subst hk
    obtain ⟨uμ, huμ, -⟩ := (h2 (ZMod q) τ hτ).1 μ (𝟙 _) (𝟙 _)
    obtain ⟨uν, huν, -⟩ := (h2 (ZMod q) τ hτ).1 ν (𝟙 _) (𝟙 _)
    have hgen : ∀ U ζ, Sec.map (uμ.f 0) (τ.mul U 0 0 0 (add_zero 0) (resGen i ζ) (resGen j ζ)) =
        Sec.map (uν.f 0) (τ.mul U 0 0 0 (add_zero 0) (resGen i ζ) (resGen j ζ)) := by
      intro U ζ
      rw [huμ U 0 0 0 (add_zero 0), huν U 0 0 0 (add_zero 0)]
      exact (hμ U ζ).trans (hν U ζ).symm
    have hh := hhom uμ uν hgen
    have hp := ((h6 (ZMod q)).2.2.2.2 uμ uν hh ((chains (ZMod q)).obj E) w).2
    have hid := (h6 (ZMod q)).1
    ext a b
    have e1 := h5 (ZMod q) τ μ (𝟙 _) (𝟙 _) uμ huμ E h a b
    have e2 := h5 (ZMod q) τ ν (𝟙 _) (𝟙 _) uν huν E h a b
    rw [(hid _ _ n a).2, (hid _ _ m b).2] at e1 e2
    rw [← e1, ← e2, hp]

end LateralTheory.EtaleFoundations
end

section -- merged from Development.EtaleCohomology.TateTwists.EtaleFreeSheafHomUniversalPropertyHolds
section -- merged from Development.EtaleCohomology.TateTwists.EtaleFreeSheafUniversalProperty
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

def LateralTheory.EtaleFoundations.EtaleFreeSheafUniversalProperty : Prop :=
  ∀ (R : Type) [CommRing R] (P : PSh) (F : Shv R), (∀ a : ∀ U : Scheme.{0}, P.obj (op U) → Sec F U, (∀ (V U : Scheme.{0}) (g : V ⟶ U) x, Sec.res g (a U x) = a V (P.map g.op x)) → ∃ φ : (free R).obj P ⟶ F, ∀ U x, Sec.map φ (freeGen R P U x) = a U x) ∧ (∀ φ ψ : (free R).obj P ⟶ F, (∀ U x, Sec.map φ (freeGen R P U x) = Sec.map ψ (freeGen R P U x)) → φ = ψ) ∧ (∀ (V U : Scheme.{0}) (g : V ⟶ U) x, Sec.res g (freeGen R P U x) = freeGen R P V (P.map g.op x)) ∧ ∀ (Q : PSh) (f : P ⟶ Q) U x, Sec.map ((free R).map f) (freeGen R P U x) = freeGen R Q U (f.app (op U) x)
end

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.FreeHomPf

variable (R : Type) [CommRing R]

noncomputable def desc (P : PSh) (F : Shv R) (a : ∀ U : Scheme.{0}, P.obj (op U) → Sec F U)
    (ha : ∀ (V U : Scheme.{0}) (g : V ⟶ U) x, Sec.res g (a U x) = a V (P.map g.op x)) :
    (freeP R).obj P ⟶ F.obj where
  app U := ModuleCat.freeDesc (↾fun x : uliftFunctor.{1}.obj (P.obj U) => a U.unop x.down)
  naturality U W g := by
    apply ModuleCat.free_hom_ext
    intro x
    have := ha W.unop U.unop g.unop x.down
    simp only [Sec.res] at this
    simp only [freeP] at *
    simp only [Functor.comp_obj, Functor.whiskeringRight_obj_obj, Functor.comp_map, Functor.whiskeringRight_obj_map,
      ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply]
    erw [ModuleCat.free_map_apply, ModuleCat.freeDesc_apply, ModuleCat.freeDesc_apply]
    exact this.symm

lemma freePresheaf_map_generator {P Q : PSh} (f : P ⟶ Q) (U : Scheme.{0}) (x : P.obj (op U)) :
    (((freeP R).map f).app (op U)).hom (ModuleCat.freeMk (ULift.up x) : ((freeP R).obj P).obj (op U)) =
      (ModuleCat.freeMk (ULift.up (f.app (op U) x)) : ((freeP R).obj Q).obj (op U)) :=
  ModuleCat.free_map_apply _ _

lemma freePresheaf_obj_map_generator (P : PSh) {V U : Scheme.{0}} (g : V ⟶ U) (x : P.obj (op U)) :
    (((freeP R).obj P).map g.op).hom (ModuleCat.freeMk (ULift.up x) : ((freeP R).obj P).obj (op U)) =
      (ModuleCat.freeMk (ULift.up (P.map g.op x)) : ((freeP R).obj P).obj (op V)) :=
  ModuleCat.free_map_apply _ _

lemma gen_eq (P : PSh) (F : Shv R) (φ : (free R).obj P ⟶ F) (U : Scheme.{0}) (x : P.obj (op U)) :
    Sec.map φ (freeGen R P U x) =
      ((toSheafify Scheme.etaleTopology ((freeP R).obj P) ≫ φ.hom).app (op U)).hom
        (ModuleCat.freeMk (ULift.up x)) := rfl

end LateralTheory.EtaleFoundations.FreeHomPf

open LateralTheory.EtaleFoundations.FreeHomPf in
theorem LateralTheory.EtaleFoundations.etale_free_sheaf_hom_universal_property_holds : LateralTheory.EtaleFoundations.EtaleFreeSheafUniversalProperty := by
  intro R _ P F
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a ha
    refine ⟨⟨sheafifyLift Scheme.etaleTopology (desc R P F a ha) F.property⟩, fun U x => ?_⟩
    refine (gen_eq R P F _ U x).trans ?_
    rw [toSheafify_sheafifyLift]
    exact ModuleCat.freeDesc_apply _ _
  · intro φ ψ h
    apply Sheaf.hom_ext
    apply sheafify_hom_ext Scheme.etaleTopology _ _ F.property
    ext U : 2
    apply ModuleCat.free_hom_ext
    intro x
    have := h U.unop x.down
    rw [gen_eq, gen_eq] at this
    exact this
  · intro V U g x
    have hn := (toSheafify Scheme.etaleTopology ((freeP R).obj P)).naturality g.op
    calc _ = (((toSheafify Scheme.etaleTopology ((freeP R).obj P)).app (op U) ≫
          (sheafify Scheme.etaleTopology ((freeP R).obj P)).map g.op)).hom
            (ModuleCat.freeMk (ULift.up x) : ((freeP R).obj P).obj (op U)) := rfl
      _ = ((((freeP R).obj P).map g.op ≫
          (toSheafify Scheme.etaleTopology ((freeP R).obj P)).app (op V))).hom
            (ModuleCat.freeMk (ULift.up x) : ((freeP R).obj P).obj (op U)) := by rw [hn]
      _ = ((toSheafify Scheme.etaleTopology ((freeP R).obj P)).app (op V)).hom
            ((((freeP R).obj P).map g.op).hom
              (ModuleCat.freeMk (ULift.up x) : ((freeP R).obj P).obj (op U))) := rfl
      _ = _ := by rw [freePresheaf_obj_map_generator]; rfl
  · intro Q f U x
    have hn := congrArg (fun η => η.app (op U))
      (toSheafify_naturality Scheme.etaleTopology ((freeP R).map f))
    calc _ = (((toSheafify Scheme.etaleTopology ((freeP R).obj P)).app (op U) ≫
          (sheafifyMap Scheme.etaleTopology ((freeP R).map f)).app (op U))).hom
            (ModuleCat.freeMk (ULift.up x) : ((freeP R).obj P).obj (op U)) := rfl
      _ = ((((freeP R).map f).app (op U) ≫
          (toSheafify Scheme.etaleTopology ((freeP R).obj Q)).app (op U))).hom
            (ModuleCat.freeMk (ULift.up x) : ((freeP R).obj P).obj (op U)) := by
              simp only [NatTrans.comp_app] at hn; rw [hn]
      _ = ((toSheafify Scheme.etaleTopology ((freeP R).obj Q)).app (op U)).hom
            ((((freeP R).map f).app (op U)).hom
              (ModuleCat.freeMk (ULift.up x) : ((freeP R).obj P).obj (op U))) := rfl
      _ = _ := by rw [freePresheaf_map_generator]; rfl
end
