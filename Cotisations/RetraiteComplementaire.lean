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

/-- Cotisation Agirc-Arrco tranche 1 (taux appelé, répartition 40/60). -/
def cotisationAgircArrcoT1 (pp : ParametresAgircArrco) (t : Tranches) : LigneCotisation :=
  { nom := "Retraite complémentaire Agirc-Arrco — tranche 1"
    organisme := .agircArrco, nature := .cotisation, cote := .mixte
    assiette := t.tranche1
    partSalariale := pp.t1Salarial * t.tranche1
    partPatronale := pp.t1Patronal * t.tranche1
    commentaire := "Taux appelé 7,87 % (contractuel 6,20 % × 127 %)" }

/-- Cotisation Agirc-Arrco tranche 2 (taux appelé, répartition 40/60). -/
def cotisationAgircArrcoT2 (pp : ParametresAgircArrco) (t : Tranches) : LigneCotisation :=
  { nom := "Retraite complémentaire Agirc-Arrco — tranche 2"
    organisme := .agircArrco, nature := .cotisation, cote := .mixte
    assiette := t.tranche2
    partSalariale := pp.t2Salarial * t.tranche2
    partPatronale := pp.t2Patronal * t.tranche2
    commentaire := "Taux appelé 21,59 % (contractuel 17 % × 127 %)" }

/-- Contribution d'équilibre général (CEG) — tranche 1. -/
def cegT1 (pp : ParametresAgircArrco) (t : Tranches) : LigneCotisation :=
  { nom := "Contribution d'équilibre général (CEG) — tranche 1"
    organisme := .agircArrco, nature := .cotisation, cote := .mixte
    assiette := t.tranche1
    partSalariale := pp.cegT1Salarial * t.tranche1
    partPatronale := pp.cegT1Patronal * t.tranche1 }

/-- Contribution d'équilibre général (CEG) — tranche 2. -/
def cegT2 (pp : ParametresAgircArrco) (t : Tranches) : LigneCotisation :=
  { nom := "Contribution d'équilibre général (CEG) — tranche 2"
    organisme := .agircArrco, nature := .cotisation, cote := .mixte
    assiette := t.tranche2
    partSalariale := pp.cegT2Salarial * t.tranche2
    partPatronale := pp.cegT2Patronal * t.tranche2 }

/-- Contribution d'équilibre technique (CET) : 0,35 % sur T1 + T2 pour les
    salariés dont la rémunération excède le plafond (tranche 2 > 0). -/
def cotisationCET (pp : ParametresAgircArrco) (t : Tranches) : LigneCotisation :=
  { nom := "Contribution d'équilibre technique (CET)"
    organisme := .agircArrco, nature := .cotisation, cote := .mixte
    assiette := t.tranche1 + t.tranche2
    partSalariale := if t.tranche2 > 0 then pp.cetSalarial * (t.tranche1 + t.tranche2) else 0
    partPatronale := if t.tranche2 > 0 then pp.cetPatronal * (t.tranche1 + t.tranche2) else 0 }

/-- Cotisation APEC (cadres) : 0,06 % sur T1 + T2 limitée à 4 PASS. -/
def cotisationApec (pp : ParametresAgircArrco) (t : Tranches) (plafond : Eur) : LigneCotisation :=
  let assiette := min (t.tranche1 + t.tranche2) (pp.apecPlafondPass * plafond)
  { nom := "Cotisation APEC"
    organisme := .apec, nature := .cotisation, cote := .mixte
    assiette := assiette
    partSalariale := pp.apecSalarial * assiette
    partPatronale := pp.apecPatronal * assiette }

/-- Toutes les lignes Agirc-Arrco (+ APEC si cadre) d'un salarié. -/
def lignesRetraiteComplementaire (ps : ParametresSalarie) (pp : ParametresAgircArrco)
    (t : Tranches) (plafond : Eur) : List LigneCotisation :=
  [cotisationAgircArrcoT1 pp t, cotisationAgircArrcoT2 pp t,
   cegT1 pp t, cegT2 pp t, cotisationCET pp t]
  ++ (if ps.cadre then [cotisationApec pp t plafond] else [])

end Cotisations