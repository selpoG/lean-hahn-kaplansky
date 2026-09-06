# 証明アーキテクチャ

[English version](PROOF_ARCHITECTURE.md)

この文書は `lean-hahn-kaplansky` の証明方針と module の役割を説明します。
公開 API と利用方法は [README.md](README.md) にあります。

## 公開されている完了点

full Hahn field に対する標準の公開 theorem は次である。

```lean
hahnKaplansky_realClosed_of_realClosed_divisible
  : IsRealClosed (HahnField k Γ)
```

ここで `k` は実閉順序体、`Γ` は可除な順序加法可換群である。

有理数 Hahn field の bounded-denominator 部分体に対する公開 theorem は次である。

```lean
puiseuxSeries_isRealClosed
  : IsRealClosed (PuiseuxSeries k)
```

具体例で使う係数体 `ℝ` の instance も提供している。

```lean
instIsRealClosedReal : IsRealClosed ℝ
```

root module は具体的な系 `realPuiseuxSeries_isRealClosed` と
`realRationalHahnField_isRealClosed` も公開する。

利用者は proof-internal module ではなく、公開 endpoint をまとめた
`import HahnKaplanskyRealClosedness` を使う。

## Hahn 側の証明本線

Hahn 側では、実閉性の ordered-field criterion に沿って証明する。

```text
Hahn 級数体と辞書式順序
  → 非負元は平方
  → odd-cluster root 問題
  → multiplicity-one positive core
  → fixed-lift root-or-step continuation
  → 全 ordinal prefix の閉包
  → 奇数次数多項式の root
  → IsRealClosed (HahnField k Γ)
```

共有される代数・valuation の contract は `Basic/` にある。odd-cluster の data と局所的な
補正 step は `SimpleCluster/` で定義する。positive core は ordinal-stack recursion により
multiplicity-one root を構成する。

fixed-lift route は same-multiplicity の engine であり、主な層は次の通りである。

- `SimpleCluster.Fixed.Foundation`: fixed-step contract と lower-edge/affine Newton
  resolution（obstruction data と root-or-step bridge を含む）。
- `SimpleCluster.Fixed.Chain`: chain 構成、summability/evaluation algebra、terminal
  obstruction data。
- `SimpleCluster.Fixed.ShiftState`: ordinal recursion が消費する terminal translation と
  fixed-lift state operation。
- `SimpleCluster.Fixed.OrdinalSupport`: ordinal-prefix の support utility。
- `SimpleCluster.Fixed.OrdinalPrefix`: resolver-free ordinal-prefix recursion と strict rank
  invariant。

fixed-step contract と affine Newton resolution は
`SimpleCluster.Fixed.Foundation` に統合し、consumer はこれを直接 import する。

`OmegaLimit` の multiplicity-one ordinal recursion は、次の責務 folder に分けている。

- `OmegaLimit.Foundation`: ordinal、Nat chain、limit extension の data。
- `OmegaLimit.Components`: compatible positive component fields。
- `OmegaLimit.PositiveRecursion`: limit recursion core と、下流で実際に使う
  component assembly 宣言。
- `OmegaTail.Endpoints`: `Main` が消費する generated recursion endpoint。

positive generated core は、次の責務群に分かれている。

- `OmegaTail.Data`: primitive generated limit-step と block-projection-core record。
- `OmegaTail.CoreRoutes`: generated core projection constructor、ordinal case、
  segment system、below-chain projection、limit
  extension、tower、compatibility、final constructor。

`Main` は canonical positive endpoint と
fixed-lift ordinal-prefix consumer だけを利用する。

## Puiseux 側の証明本線

`PuiseuxSeries k` は、`HahnField k ℚ` の bounded-denominator subfield として表現する。主な追加
課題は、奇数次数 root を構成する間、一つの分母上界を保つことである。

```text
bounded-denominator Hahn support
  → 固定分母 valuation level
  → power-series simple-root lift
  → residue/root translation と scaling
  → lower multiplicity induction
  → same-multiplicity fixed-level chain
  → bounded-denominator Hahn root
  → odd-degree Puiseux root
  → IsRealClosed (PuiseuxSeries k)
```

維持されている Puiseux の層は次の通りである。

- `Puiseux.Support`: bounded-denominator support、subfield embedding、finite level、root witness。
- `Puiseux.Valuation`: valuation と cluster predicate。
- `Puiseux.Lift`: fixed-level residue data と power-series/Hensel lift。
- `Puiseux.Newton`: polynomial support、lower-edge、multiplicity induction、
  same-multiplicity continuation。
- `Puiseux.Roots`: scaling、bounded root、square root。
- `Puiseux.lean`: 安定した公開名と実閉性の直接的な assembly。

full-multiplicity branch では denominator control が本質的になる。Newton correction exponent
が元の denominator lattice に残るため、共通の lattice 内で strict に増加する step 値が得られ、
その列の非有界性から bounded-denominator subfield 内の Hahn candidate が root になる。

## 依存境界

公開 root module は、次の三つを並列に直接 import する。

```text
HahnKaplanskyRealClosedness
  ├─→ Main
  ├─→ Puiseux
  └─→ RealClosedReal
```

`Main` は Puiseux proof に依存しない。Puiseux は共有された `Basic/` と `SimpleCluster/` の
foundation を利用するが、実閉性 endpoint は full Hahn real-closedness theorem を呼び出さず、
fixed-level route で直接証明する。これにより、実閉な ambient field の部分体だから実閉、という
循環的な shortcut を避けている。

公開 completion point は `AxiomAudit.lean` で監査し、`Examples.lean`、`Smoke.lean`、
`PuiseuxSmoke.lean` で利用する。

## 数学的な証明ノート

この構成に対応する数学的証明ノートは、英語版
`docs/hahn_kaplansky_proof.tex` と日本語版
`docs/hahn_kaplansky_proof_ja.tex` である。`task proof-pdf` で両方をコンパイルでき、
PDF は `docs/hahn_kaplansky_proof.pdf` と `docs/hahn_kaplansky_proof_ja.pdf` に更新される。
補助的な生成物は ignore される `docs/build/` に置かれる。本文は数学的証明を示し、
付録は各段階に対応する Lean 宣言と module を掲載する。

## 検証 surface

公開 surface の検証入口は `Taskfile.yml` の `task verify` である。library build、公開例、
smoke test、公開 theorem の axiom audit、style と whitespace の確認をまとめて実行する。
`Taskfile.yml` と CI workflow を標準の検証契約とする。
