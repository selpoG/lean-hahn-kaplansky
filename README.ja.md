# Hahn--Kaplansky 実閉性定理

[English version](README.md)

この文書は、日本語で読むための公開入口である。標準の公開説明と定理名は
[英語版 README](README.md) を主とする。

## 公開定理

`k` を実閉順序体、`Γ` を可除順序加法可換群とする。このとき、先頭係数による辞書式順序を
入れた full Hahn field `HahnField k Γ` は実閉である。

```lean
hahnKaplansky_realClosed_of_realClosed_divisible
  : IsRealClosed (HahnField k Γ)
```

有理数 Hahn field の bounded-denominator 部分体である Puiseux 級数体についても、次の公開
theorem がある。

```lean
puiseuxSeries_isRealClosed
  : IsRealClosed (PuiseuxSeries k)
```

具体例で使う実数の instance も提供している。

```lean
instIsRealClosedReal : IsRealClosed ℝ
```

したがって、実数係数の具体的な field に対する名前付きの系も利用できる。

```lean
realPuiseuxSeries_isRealClosed : IsRealClosed (PuiseuxSeries ℝ)
realRationalHahnField_isRealClosed : IsRealClosed (HahnField ℝ ℚ)
```

利用者は proof-internal module ではなく、公開入口をまとめた次の import を使う。

```lean
import HahnKaplanskyRealClosedness
```

## 証明の概要

Hahn 側では、平方根の構成と odd-cluster root の構成を ordered-field criterion に接続する。
Puiseux 側では、Hahn field の中で分母の共通上界を保つ fixed-level Newton--Puiseux route を
使う。安定した数学的・module 上の構成は
[`PROOF_ARCHITECTURE.ja.md`](PROOF_ARCHITECTURE.ja.md) にまとめている。

公開定理はプロジェクト固有の公理を追加しない。`AxiomAudit.lean` は依存公理が
`propext`、`Classical.choice`、`Quot.sound` のみであることを検査し、
`Examples.lean` は公開 API を実際に使う小さな検証例である。

## Build と検証

Lean toolchain は `lean-toolchain` に固定し、Lake から再現可能に build できる。公開 surface
をまとめて確認するには次を実行する。

```text
task verify
```

個別の入口は次の通りである。

```text
lake exe cache get
lake build
lake build HahnKaplanskyRealClosedness.Examples
lake env lean HahnKaplanskyRealClosedness/AxiomAudit.lean
lake env lean HahnKaplanskyRealClosedness/Smoke.lean
lake env lean HahnKaplanskyRealClosedness/PuiseuxSmoke.lean
task lint
```

## 文書の使い分け

文書ごとに対象と役割を分けている。

| 文書 | 役割 |
| --- | --- |
| `README.md` | 英語の公開入口。定理、利用方法、検証入口、各資料へのリンクを示す。 |
| `README.ja.md` | 同じ範囲を扱う日本語の公開入口。 |
| `PROOF_ARCHITECTURE.md` / `.ja.md` | 変動しにくい数学的証明 spine と module の責務を説明する。 |
| `docs/hahn_kaplansky_proof*.tex` と PDF | 数学的証明と Lean 形式化との対応。 |
| `CITATION.cff` | 機械可読な引用 metadata のみを置く。 |

architecture 文書は証明または module 設計が変わったときに更新する。

## 数学的な証明ノート

数学的証明ノートは英語版と日本語版を用意している。

- [英語 TeX](docs/hahn_kaplansky_proof.tex) / [英語 PDF](docs/hahn_kaplansky_proof.pdf)
- [日本語 TeX](docs/hahn_kaplansky_proof_ja.tex) / [日本語 PDF](docs/hahn_kaplansky_proof_ja.pdf)

本文は数学的証明を示し、付録は各段階に対応する Lean 宣言と module を掲載する。

TeX 環境がある場合は `task proof-pdf` で両方の PDF を再生成できる。補助的な組版生成物は
`docs/build/` に置かれ、commit しない。repository の VS Code 設定では TeX を開いただけでは
build せず、保存時だけ同じ directory へ出力する。同一 source の PDF は byte 単位で再現され、
内容が同じなら committed PDF を置換しない。

## 引用とライセンス

引用 metadata は [`CITATION.cff`](CITATION.cff)、ライセンスは Apache-2.0 である。
