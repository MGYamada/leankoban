# leankoban

Lean 4 だけで書いた倉庫番（箱押しパズル）です。収録している**全 100 面がクリア可能であること**を、
公理を 1 つも使わずに Lean のカーネルで証明しています。

- ゲーム本体、盤面生成器、ソルバー、証明ファイル生成器、ビルド設定（`lakefile.lean`）まで、すべて Lean で書いています。
- 外部ライブラリには依存しません（Lean core とツールチェーン同梱の `Std` のみ。Mathlib も使いません）。
- 100 面はすべて自動生成したオリジナルです（既存作品の面は使っていません）。

## 遊び方

必要なのは [elan](https://github.com/leanprover/elan) だけです（`lean-toolchain` に従って Lean 4.35.0 が入ります）。

```sh
lake build                 # ゲーム・証明・テストをまとめてビルド（証明の検査も含む）
lake exe leankoban         # 未クリアの最初の面から始める
lake exe leankoban 42      # 42 面から始める
lake exe leankoban --line  # 行入力モード（Enter で確定）
```

| キー | 操作 |
| --- | --- |
| 矢印 / WASD / hjkl | 移動 |
| `u` / `z` | 1 手戻す |
| `r` | やり直し |
| `n` / `p` | 次の面 / 前の面 |
| `g` | 面番号を指定して移動 |
| `?` | ヘルプ |
| `q` | 終了 |

- 1 キーごとに反応させるため、端末の設定を `stty` で切り替えています（このゲームが使う唯一の外部コマンドです）。
  `--line` を付けるか、標準入力が端末でない場合は、Lean だけで動く行入力モードになります。
  行入力モードでは、`:rrDDlu` のように `:` で始めると LURD 記法の手順として入力できます。
- クリアした面は `~/.leankoban/progress` に記録されます。
- `--plain` を付けると、色を使わず XSB 形式の文字で表示します。

## 何が証明されているか

`Proofs.lean` の主定理は次のとおりです。

```lean
theorem all_levels_solvable :
    ∀ rows ∈ Levels.all, WellFormed (Level.ofRows rows) ∧ Solvable (Level.ofRows rows)
```

`Levels.all` は、ゲームが実際に読み込む盤面データ（`Leankoban/Levels/Data.lean`）そのものです。
各面の証明は `Proofs/Level001.lean` 〜 `Proofs/Level100.lean` の 100 ファイルにあります。

### 前提（信頼する部分）

「クリア可能」の意味は [`Leankoban/Spec.lean`](Leankoban/Spec.lean)（約 110 行）だけで決まります。

- `Level.ofRows`：XSB 形式の盤面を ASCII バイト単位で読みます（未知の文字は壁として扱う、安全側の読み方です）。
- `Step`：1 手の遷移を帰納的関係として定義します。「歩く」と「箱を 1 個押す」の 2 規則だけです。
- `Reachable`：0 手以上の遷移の反射推移閉包です。
- `Solved`：すべての箱がゴールにあり、すべてのゴールに箱がある状態です。
- `WellFormed`：ゴールが 1 個以上あり、箱とゴールが同数で、重複がなく、人が床の上にいることです（箱 0 個の盤面のような退化を除きます）。
- `Solvable L := ∃ s, Reachable L L.init s ∧ Solved L s`

### 証明のしくみ

```
Spec（信頼する仕様）
  ▲  step_sound / step_complete / run_sound / certify（Leankoban/Soundness.lean）
Engine（計算できる実行系。ゲームの移動処理もこの関数）
  ▲  証明書 = 解の手順（LURD 文字列）
Tools（ソルバー・生成器。信頼しない）
```

- `Engine.step` は仕様 `Step` と完全に一致します（健全性 `step_sound` と完全性 `step_complete`）。
  ゲームは移動の判定にこの関数をそのまま使うので、**ゲームのルールは仕様どおり**です。
- `Soundness.certify` は「`Engine.check rows sol = true` ならば `WellFormed ∧ Solvable`」という定理です。
- 各面の証明は、ソルバーが見つけた手順 `sol` を与え、`check rows sol = true` を
  `decide +kernel` でカーネルに計算させるだけです。ソルバーに誤りがあれば、カーネルが証明を拒否します。

### 公理を使っていないこと

- `sorry` / `native_decide` / 独自の `axiom` は使っていません。
- `propext`、`Quot.sound`、`Classical.choice` も使いません。そのために、core の補題の多くが `propext` に
  依存する点を避け、`simp` を使わずに小さな補題を自前で証明しています。文字列は `String.toList`
  （標準公理に依存し、カーネルでの計算も遅い）を使わず、バイト列として読んでいます。
- [`Proofs/Audit.lean`](Proofs/Audit.lean) が `lake build` のたびに、101 個の定理の**主張が期待どおりであること**と、
  それらと健全性・完全性の定理が**公理に 1 つも依存しないこと**を `collectAxioms` で検査し、違反があればビルドを失敗させます。

```sh
lake build Proofs.Audit
# info: 監査 OK: 面ごとの定理 100 個と all_levels_solvable の主張は期待どおりで、
#       これらと 4 個の健全性・完全性の定理はすべて公理に依存しない。
```

## 盤面と証明の再生成

```sh
lake exe genlevels    # 100 面を生成して Leankoban/Levels/Data.lean に書き出す（seed 固定・約 75 秒）
lake exe genproofs    # 各面をソルバーで解き直し、Proofs/LevelNNN.lean と Proofs.lean を書き出す
lake build            # 証明をカーネルで検査し、監査する
```

- **生成**（`Tools/Generator.lean`）：壁の欠片をランダムに置いて部屋を作ります（床がつながったままのときだけ採用し、
  行き止まりを埋め、3×4 以上の空き地がある部屋は捨てます）。次に、箱をすべてゴールに置いた状態から、
  箱を「引く」手で幅優先探索して、最も深い局面を初期配置にします。引く手の逆は押す手なので、
  得られる面はどれも構成上クリア可能です。回転・鏡映で同じになる面は除きます。
- **証明の生成**（`Tools/GenProofs.lean`）：生成器とは独立に、最終的な盤面データだけを入力にしてソルバー
  （押し数で幅優先探索し、死に床への押し手を枝刈り）で解き直し、手順が `Engine.check` を通ることを確かめてから書き出します。

| 段階 | 面 | 箱 | 最小押し数 |
| --- | --- | --- | --- |
| 入門 | 1–5 | 1 | 5–8 |
| 初級 | 6–15 | 2 | 10–17 |
| 初中級 | 16–30 | 2 | 15–36 |
| 中級 | 31–50 | 3 | 20–40 |
| 中上級 | 51–70 | 3 | 26–37 |
| 上級 | 71–85 | 4 | 31–43 |
| 達人 | 86–95 | 4 | 34–46 |
| 最難関 | 96–100 | 5 | 44–52 |

証明書の手数は全 100 面の合計で 9,812 手です。最長は面 100 の 406 手で、その検査もカーネルで約 1 秒です。

## ファイル構成

```
lakefile.lean               ビルド設定（Lean DSL）
Leankoban/Spec.lean         ルール仕様（信頼の核）
Leankoban/Engine.lean       実行系（ゲームと証明の両方が使う）
Leankoban/Soundness.lean    健全性・完全性と certify（公理なし）
Leankoban/Levels/Data.lean  100 面の盤面データ（生成物）
Leankoban/Game/             描画・入力・ゲームループ
Main.lean                   ゲームの実行ファイル
Tools/                      乱数・探索用盤面・ソルバー・生成器・genlevels・genproofs
Proofs/Level001..100.lean   各面の可解性証明（生成物）
Proofs.lean                 全面の可解性（生成物）
Proofs/Audit.lean           主張と公理の監査
Tests/                      実行系・ゲームの単体テスト（#guard）
```
