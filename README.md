## E869120 とオセロで対戦！
モンテカルロ木探索を用いたオセロの AI です。

OpenSiv3D を用いて実装しています。画面の例は以下の通りです。

![ ](https://i.ibb.co/YbTXQ3m/4.jpg)

<br />

## ディレクトリの構造について
構造は次の通りになっています。

* **Main.cpp**：ソースコード（C++）
* **App/Othello-AI-1.exe**：アプリケーション

Main.cpp からコンパイルして実行するには OpenSiv3D のインストールが必要ですが、exe ファイルから開けばインストールしなくても遊べます。

<br />

## ゲームの難易度について
難易度は「レベル 1」から「レベル 6」の六段階に分かれています。

| 難易度 | 目安 |
|:---:|:---:|
| レベル 1 | ほとんどランダムに手を打つ |
| レベル 2 | - |
| レベル 3 |  |
| レベル 4 | 半分程度の人が負ける |
| レベル 5 | 強い人でなければ勝てない |
| レベル 6 | [square1001 氏](https://www.chess.com/member/square1001)でも勝てなかった（2 勝 3 敗） |

なお、レベル 6 のみ実行環境によって AI の強さが変わります。

レベル 1 ～ 5 はループ回数を決めている一方、レベル 6 は 1 手 15 秒ギリギリまで考えているからです。
