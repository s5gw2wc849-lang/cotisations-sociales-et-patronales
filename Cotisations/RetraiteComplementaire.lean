/-
Retraite complémentaire obligatoire Agirc-Arrco (tous salariés, cadres
ou non) et APEC (cadres).

Paramètres 2026 (circulaire Agirc-Arrco 2025-20) :
- T1 : 6,20 % contractuel, taux appelé 7,87 % réparti 3,15 % salarié /
  4,72 % employeur ;
- T2 : 17 % contractuel, taux appelé 21,59 % réparti 8,64 % /
  12,95 % ;
- CEG : 2,15 % (T1) et 2,70 % (T2), répartis 40/60 ;
- CET : 0,35 % sur T1 + T2 pour les salariés dont la rémunération dépasse
  le PASS (0,14 % salarié / 0,21 % employeur) ;
- APEC : 0,06 % sur T1 + T2 limitée à 4 PASS (0,024 % / 0,036 %).

Les cotisations Agirc-Arrco (T1/T2) et les CEG (T1/T2) partagent la même
mécanique « taux salarié / taux employeur × assiette de tranche » via la
primitive `ligneAgircArrco`.
-/
import Cotisations.Assiette
import Cotisations.Organismes

namespace Cotisations

/-- Taux Agirc-Arrco. Valeurs = 2026. -/
structure ParametresAgircArrco where
  t1Salarial : Rat := 0.0315
  t1Patronal : Rat := 0.0472
  t2Salarial : Rat := 0.0864
  t2Patronal : Rat := 0.1295
  cegT1Salarial : Rat := 0.0086
  cegT1Patronal : Rat := 0.0129
  cegT2Salarial : Rat := 0.0108
  cegT2Patronal : Rat := 0.0162
  cetSalarial : Rat := 0.0014
  cetPatronal : Rat := 0.0021
  apecSalarial : Rat := 0.00024
  apecPatronal : Rat := 0.00036
  apecPlafondPass : Rat := 4
  deriving Repr, DecidableEq

/-- Paramètres officiels 2026. -/
def parametresAgircArrco2026 : ParametresAgircArrco := {}

/-- Ligne Agirc-Arrco générique : taux salarié et taux employeur appliqués
    à une assiette de tranche (sert aux cotisations T1/T2 et aux CEG). -/
def ligneAgircArrco (nom : String) (tSalarial tPatronal : Taux)
    (assiette : Eur) (commentaire : String := "") : LigneCotisation :=
  ligneMixte nom .agircArrco .cotisation assiette
    (tSalarial * assiette) (tPatronal * assiette) commentaire

/-- Cotisation Agirc-Arrco tranche 1 (taux appelé, répartition 40/60). -/
def cotisationAgircArrcoT1 (pp : ParametresAgircArrco) (t : Tranches) : LigneCotisation :=
  ligneAgircArrco "Retraite complémentaire Agirc-Arrco — tranche 1"
    pp.t1Salarial pp.t1Patronal t.tranche1
    "Taux appelé 7,87 % (contractuel 6,20 % × 127 %)"

/-- Cotisation Agirc-Arrco tranche 2 (taux appelé, répartition 40/60). -/
def cotisationAgircArrcoT2 (pp : ParametresAgircArrco) (t : Tranches) : LigneCotisation :=
  ligneAgircArrco "Retraite complémentaire Agirc-Arrco — tranche 2"
    pp.t2Salarial pp.t2Patronal t.tranche2
    "Taux appelé 21,59 % (contractuel 17 % × 127 %)"

/-- Contribution d'équilibre général (CEG) — tranche 1. -/
def cegT1 (pp : ParametresAgircArrco) (t : Tranches) : LigneCotisation :=
  ligneAgircArrco "Contribution d'équilibre général (CEG) — tranche 1"
    pp.cegT1Salarial pp.cegT1Patronal t.tranche1

/-- Contribution d'équilibre général (CEG) — tranche 2. -/
def cegT2 (pp : ParametresAgircArrco) (t : Tranches) : LigneCotisation :=
  ligneAgircArrco "Contribution d'équilibre général (CEG) — tranche 2"
    pp.cegT2Salarial pp.cegT2Patronal t.tranche2

/-- Contribution d'équilibre technique (CET) : 0,35 % sur T1 + T2 pour les
    salariés dont la rémunération excède le plafond (tranche 2 > 0). -/
def cotisationCET (pp : ParametresAgircArrco) (t : Tranches) : LigneCotisation :=
  let a := t.tranche1 + t.tranche2
  ligneMixte "Contribution d'équilibre technique (CET)" .agircArrco .cotisation a
    (if t.tranche2 > 0 then pp.cetSalarial * a else 0)
    (if t.tranche2 > 0 then pp.cetPatronal * a else 0)

/-- Cotisation APEC (cadres) : 0,06 % sur T1 + T2 limitée à 4 PASS. -/
def cotisationApec (pp : ParametresAgircArrco) (t : Tranches) (plafond : Eur) : LigneCotisation :=
  let a := min (t.tranche1 + t.tranche2) (pp.apecPlafondPass * plafond)
  ligneMixte "Cotisation APEC" .apec .cotisation a
    (pp.apecSalarial * a) (pp.apecPatronal * a)

/-- Toutes les lignes Agirc-Arrco (+ APEC si cadre) d'un salarié. -/
def lignesRetraiteComplementaire (ps : ParametresSalarie) (pp : ParametresAgircArrco)
    (t : Tranches) (plafond : Eur) : List LigneCotisation :=
  [cotisationAgircArrcoT1 pp t, cotisationAgircArrcoT2 pp t,
   cegT1 pp t, cegT2 pp t, cotisationCET pp t]
  ++ (if ps.cadre then [cotisationApec pp t plafond] else [])

end Cotisations
