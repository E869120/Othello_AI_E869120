#include <Siv3D.hpp> // OpenSiv3D v0.4.3
#include <algorithm>
#include <ctime>
#include <cmath>
#include <string>
#include <omp.h>
using namespace std;
#pragma warning (disable: 4996)

struct State {
	char c[8][8];
	int bit1[8], bit2[8], bit3[15], bit4[15];
};

// 機械学習の変数
double d1[150][150], e1[150], aa1[150], aa0[150];
double d2[150][150], e2[150], aa2[150];
double d3[150][150], e3[150], aa3[150];

// 全体で使う変数
int Situation = 0;
double GetLastClick = 0.0;
double PI = 3.14159265358979;
int RandX[1 << 13][64];
int Moto1[1 << 16][8], Moto2[1 << 16][8];
int pow4[9] = { 1, 4, 16, 64, 256, 1024, 4096, 16384, 65536 };

// その他の変数
int ALPHA = 1000;
int PLAYS = 1000;
int BACKETS = 50;
const double TEISUU_A = 0.3;
const double TEISUU_B = -0.014;
const int MAX_STATES = 4200000;
int col1[4] = { 175, 175, 175, 100 };
int col4[8] = { 40, 40, 40, 40, 40, 40, 40, 40 };
int col2[10][10];

// オセロの盤面など
State CurrentState;
int Next_Move = 1, Sente = 1, Ti = 0, Consecutive = 0;
int Score1 = 0, Score2 = 0, preX, preY;
double Win_Rate = 0;
bool usable[8][8];

// モンテカルロ木探索
int StateCnt = 0;
int TansakuCnt = 0;
int AlphaBeta = 0;
State CandState[MAX_STATES];
short CandTurn[MAX_STATES]; double win[MAX_STATES], searched[MAX_STATES], tesuu[MAX_STATES];
short deg[MAX_STATES], nex_zahyou[MAX_STATES][30]; int nexnum[MAX_STATES][30];

int dx[8] = { 0, 1, 1, 1, 0, -1, -1, -1 };
int dy[8] = { 1, 1, 0, -1, -1, -1, 0, 1 };
vector<double> Data;

double StringToDouble(string str) {
	if (str[0] == '[') str = str.substr(1, str.size() - 1);
	if (str[str.size() - 1] == ']') str = str.substr(0, str.size() - 1);
	return stod(str);
}

double hantei(State& SS, int turn) {
	for (int i = 0; i < 150; i++) aa1[i] = 0;
	for (int i = 0; i < 150; i++) aa2[i] = 0;
	for (int i = 0; i < 150; i++) aa3[i] = 0;

	// 前処理
	for (int i = 0; i <= 7; i++) {
		for (int j = 0; j <= 7; j++) {
			int idx = i * 8 + j;
			if (SS.c[i][j] == 3 - turn) aa0[idx] = 1;
			else aa0[idx] = 0;
			if (SS.c[i][j] == turn) aa0[idx + 64] = 1;
			else aa0[idx + 64] = 0;
		}
	}

	// 1 層目
	for (int i = 0; i < 128; i++) {
		for (int j = 0; j < 75; j++) aa1[j] += aa0[i] * d1[i][j];
	}
	for (int i = 0; i < 75; i++) {
		aa1[i] += e1[i];
		aa1[i] = tanh(aa1[i]);
		if (rand() % 100 < 10) aa1[i] = 0;
	}

	// 2 層目
	for (int i = 0; i < 75; i++) {
		for (int j = 0; j < 30; j++) aa2[j] += aa1[i] * d2[i][j];
	}
	for (int i = 0; i < 30; i++) {
		aa2[i] += e2[i];
		aa2[i] = tanh(aa2[i]);
	}

	// 3 層目
	double S = 0;
	for (int i = 0; i < 30; i++) {
		for (int j = 0; j < 2; j++) aa3[j] += aa2[i] * d3[i][j];
	}
	for (int i = 0; i < 2; i++) {
		aa3[i] += e3[i];
		S += exp(aa3[i]);
	}
	for (int i = 0; i < 2; i++) aa3[i] = exp(aa3[i]) / S;

	// 勝率決定
	return aa3[0];
}

void Update(State& V, int px, int py, int turn) {
	int sa = (turn - V.c[px][py]);
	V.c[px][py] = turn;
	V.bit1[px] += sa * pow4[py];
	V.bit2[py] += sa * pow4[px];
	V.bit3[px + py] += sa * pow4[py];
	V.bit4[px - py + 7] += sa * pow4[py];
}

int check_usable(vector<int> vec, int turn) {
	bool flag1 = false, flag2 = false;
	for (int i = 0; i < vec.size(); i++) {
		if (vec[i] == 0) return 0;
		if (vec[i] != turn) { flag1 = true; }
		if (vec[i] == turn) { flag2 = true; break; }
	}
	if (flag1 == true && flag2 == true) return 1;
	return 0;
}

void Reset() {
	Data.clear();
	Win_Rate = 0.5;
	preX = -1; preY = -1;
	for (int i = 0; i < 8; i++) {
		for (int j = 0; j < 8; j++) CurrentState.c[i][j] = 0;
	}
	if (Sente == 1) {
		Update(CurrentState, 3, 3, 2);
		Update(CurrentState, 3, 4, 1);
		Update(CurrentState, 4, 3, 1);
		Update(CurrentState, 4, 4, 2);
	}
	if (Sente == 2) {
		Update(CurrentState, 3, 3, 1);
		Update(CurrentState, 3, 4, 2);
		Update(CurrentState, 4, 3, 2);
		Update(CurrentState, 4, 4, 1);
	}
	for (int i = 0; i < (1 << 13); i++) {
		for (int j = 0; j < 64; j++) RandX[i][j] = j;
		for (int j = 0; j < 640; j++) swap(RandX[i][rand() % 64], RandX[i][rand() % 64]);
	}

	for (int i = 0; i < pow4[8]; i++) {
		int bit[8]; bool flag1 = false;
		for (int j = 0; j < 8; j++) {
			bit[j] = (i / pow4[j]) % 4;
			if (bit[j] == 3) flag1 = true;
		}
		if (flag1 == true) continue;
		for (int j = 0; j < 8; j++) {
			if (bit[j] != 0) continue;
			vector<int> v1, v2;
			for (int k = j - 1; k >= 0; k--) v1.push_back(bit[k]);
			for (int k = j + 1; k < 8; k++) v2.push_back(bit[k]);
			Moto1[i][j] = 0;
			Moto2[i][j] = 0;
			Moto1[i][j] |= check_usable(v1, 1);
			Moto1[i][j] |= check_usable(v2, 1);
			Moto2[i][j] |= check_usable(v1, 2);
			Moto2[i][j] |= check_usable(v2, 2);
		}
	}
}

bool hantei_easy(State& T, int ty, int px, int py) {
	if (T.c[px][py] != 0) return false;
	if (ty == 1) {
		if (Moto1[T.bit1[px]][py] == 1) return true;
		if (Moto1[T.bit2[py]][px] == 1) return true;
		if (Moto1[T.bit3[px + py]][py] == 1) return true;
		if (Moto1[T.bit4[px - py + 7]][py] == 1) return true;
		return false;
	}
	if (ty == 2) {
		if (Moto2[T.bit1[px]][py] == 1) return true;
		if (Moto2[T.bit2[py]][px] == 1) return true;
		if (Moto2[T.bit3[px + py]][py] == 1) return true;
		if (Moto2[T.bit4[px - py + 7]][py] == 1) return true;
		return false;
	}
	return false;
}

void Moves(State& V, int turn, int px, int py) {
	for (int i = 0; i < 8; i++) {
		int sx = px, sy = py; bool flag1 = false, flag2 = false;
		while (true) {
			sx += dx[i], sy += dy[i];
			if (sx < 0 || sy < 0 || sx >= 8 || sy >= 8 || V.c[sx][sy] == 0) break;
			if (V.c[sx][sy] != turn) { flag1 = true; }
			if (V.c[sx][sy] == turn) { flag2 = true; break; }
		}
		if (flag1 == true && flag2 == true) {
			sx = px; sy = py;
			while (true) {
				sx += dx[i], sy += dy[i];
				if (sx < 0 || sy < 0 || sx >= 8 || sy >= 8 || V.c[sx][sy] == 0) break;
				if (V.c[sx][sy] != turn) Update(V, sx, sy, turn);
				else if (V.c[sx][sy] == turn) break;
			}
		}
	}

	Update(V, px, py, turn);
}

// サボったαβ探索
tuple<int, int, int> dfs2(State V, int turn) {
	// 0 : 分からない／-1: 負け／1: 引き分け／2: 勝ち
	if (AlphaBeta > ALPHA) return make_tuple(0, -1, -1);

	AlphaBeta += 1;
	int seed = (rand() & 8191), cnt_moves = 0;

	pair<int, int> hikiwake = make_pair(-1, -1);
	for (int i = 0; i < 64; i++) {
		int vx = (RandX[seed][i] >> 3), vy = (RandX[seed][i] & 7);
		if (hantei_easy(V, turn, vx, vy) == true) {
			State VV = V;
			Moves(VV, turn, vx, vy);
			int res = get<0>(dfs2(VV, 3 - turn));
			if (res == -1) return make_tuple(2, vx, vy);
			if (res == 0) return make_tuple(0, -1, -1);
			if (res == 1) hikiwake = make_pair(vx, vy);
			cnt_moves += 1;
		}
	}
	if (hikiwake != make_pair(-1, -1)) {
		return make_tuple(1, hikiwake.first, hikiwake.second);
	}

	if (cnt_moves == 0) {
		for (int i = 0; i < 64; i++) {
			int vx = (RandX[seed][i] >> 3), vy = (RandX[seed][i] & 7);
			if (hantei_easy(V, 3 - turn, vx, vy) == true) {
				cnt_moves += 1;
			}
		}
		if (cnt_moves == 0) {
			int count1 = 0, count2 = 0;
			for (int i = 0; i < 8; i++) {
				for (int j = 0; j < 8; j++) {
					if (V.c[i][j] == turn) count1++;
					if (V.c[i][j] == 3 - turn) count2++;
				}
			}
			if (turn == 1) {
				if (count1 < count2) return make_tuple(-1, -1, -1);
				if (count1 == count2) return make_tuple(1, -1, -1);
				return make_tuple(2, -1, -1);
			}
			if (turn == 2) {
				if (count1 > count2) return make_tuple(2, -1, -1);
				if (count1 == count2) return make_tuple(1, -1, -1);
				return make_tuple(-1, -1, -1);
			}
			return make_tuple(-1, -1, -1);
		}
		else {
			tuple<int, int, int> res = dfs2(V, 3 - turn);
			if (get<0>(res) == -1) return make_tuple(2, -1, -1);
			if (get<0>(res) == 1) return make_tuple(1, -1, -1);
			if (get<0>(res) == 0) return make_tuple(0, -1, -1);
			return make_tuple(-1, -1, -1);
		}
	}
	return make_tuple(-1, -1, -1);
}

// 厳密なαβ探索
tuple<int, int, int> dfs3(State V, int OptEval, int turn) {
	// 0 : 分からない／-1: 負け／1: 引き分け／2: 勝ち
	if (AlphaBeta > ALPHA) return make_tuple(-1, -1, -1);

	AlphaBeta += 1;
	int seed = (rand() & 8191), cnt_moves = 0;
	tuple<int, int, int> next_move = make_tuple(-1, -1, -1); if (turn == 2) next_move = make_tuple(65, -1, -1);
	for (int i = 0; i < 64; i++) {
		int vx = (RandX[seed][i] >> 3), vy = (RandX[seed][i] & 7);
		if (hantei_easy(V, turn, vx, vy) == true) {
			State VV = V;
			Moves(VV, turn, vx, vy);
			int res = get<0>(dfs3(VV, get<0>(next_move), 3 - turn));
			if (turn == 1) next_move = max(next_move, make_tuple(res, vx, vy));
			if (turn == 2) next_move = min(next_move, make_tuple(res, vx, vy));
			if (turn == 1 && res > OptEval) return next_move;
			if (turn == 2 && res < OptEval) return next_move;
			cnt_moves += 1;
		}
	}

	if (cnt_moves == 0) {
		for (int i = 0; i < 64; i++) {
			int vx = (RandX[seed][i] >> 3), vy = (RandX[seed][i] & 7);
			if (hantei_easy(V, 3 - turn, vx, vy) == true) {
				cnt_moves += 1;
			}
		}
		if (cnt_moves == 0) {
			int count1 = 0, count2 = 0;
			for (int i = 0; i < 8; i++) {
				for (int j = 0; j < 8; j++) {
					if (V.c[i][j] == 1) count1++;
					if (V.c[i][j] == 2) count2++;
				}
			}
			return make_tuple(64 * count1 / (count1 + count2), -1, -1);
		}
		else {
			int opt = -1; if (turn == 2) opt = 65;
			tuple<int, int, int> res = dfs3(V, opt, 3 - turn);
			return res;
		}
	}
	return next_move;
}

int Random_Playout(State V, int turn) {
	int flagcnt = 0;
	while (flagcnt <= 1) {
		bool flag = false; int seed = (rand() & 8191);
		for (int i = 0; i < 64; i++) {
			int vx = (RandX[seed][i] >> 3), vy = (RandX[seed][i] & 7);
			usable[vx][vy] = hantei_easy(V, turn, vx, vy);
			if (usable[vx][vy] == true) {
				flagcnt = 0;
				Moves(V, turn, vx, vy);
				turn = (3 - turn);
				flag = true; break;
			}
		}
		if (flag == false) { turn = (3 - turn); flagcnt += 1; }
	}

	int V1 = 0, V2 = 0;
	for (int i = 0; i <= 7; i++) {
		for (int j = 0; j <= 7; j++) {
			if (V.c[i][j] == 1) V1 += 1;
			if (V.c[i][j] == 2) V2 += 1;
		}
	}
	return 64 * V1 / (V1 + V2);
}

double eval(int score, int rem) {
	double keisuu = 0.03 * rem;
	return 1.0 / (1.0 + exp((32.0 - 1.0 * score) / keisuu));
}

void Initialize(State& SS, int pos, int turn) {
	if (pos != -1) {
		nexnum[pos][deg[pos]] = StateCnt;
		deg[pos] += 1;
	}

	CandState[StateCnt] = SS;
	CandTurn[StateCnt] = turn;
	deg[StateCnt] = 0;
	win[StateCnt] = 0;
	searched[StateCnt] = 0;

	for (int i = 0; i < 8; i++) CandState[StateCnt].bit1[i] = 0;
	for (int i = 0; i < 15; i++) CandState[StateCnt].bit2[i] = 0;
	for (int i = 0; i < 15; i++) CandState[StateCnt].bit3[i] = 0;
	for (int i = 0; i < 15; i++) CandState[StateCnt].bit4[i] = 0;

	for (int i = 0; i < 8; i++) {
		for (int j = 0; j < 8; j++) {
			CandState[StateCnt].bit1[i] += SS.c[i][j] * pow4[j];
			CandState[StateCnt].bit2[j] += SS.c[i][j] * pow4[i];
			CandState[StateCnt].bit3[i + j] += SS.c[i][j] * pow4[j];
			CandState[StateCnt].bit4[i - j + 7] += SS.c[i][j] * pow4[j];
		}
	}
	StateCnt += 1;
}

pair<double, double> Gen_Random(int pos, int rems) {
	double a1 = 0.0, a2 = 0.0;
	for (int i = 0; i < deg[pos]; i++) {
		int idx = nexnum[pos][i];
		// int FinalPoint = Random_Playout(CandState[idx], CandTurn[idx]);
		double FinalScore = hantei(CandState[idx], CandTurn[idx]);
		if (CandTurn[idx] == 2) FinalScore = 1.0 - FinalScore;
		win[idx] += FinalScore;
		searched[idx] += 1.0;
		a1 += FinalScore;
		a2 += 1.0;
	}
	return make_pair(a1, a2);
}

pair<double, double> dfs(int pos, int rems) {
	if (deg[pos] != 0) {
		int maxid = -1; double maxn = -1e5;
		for (int i = 0; i < deg[pos]; i++) {
			int idx = nexnum[pos][i];
			double TEISUU = TEISUU_A - TEISUU_B * (Score1 + Score2);
			double eval1 = (1.0 * win[idx] / searched[idx]); if (CandTurn[pos] == 2) eval1 = 1.0 - eval1;
			double eval2 = sqrt(1.0 * log(1.0 * searched[pos]) / searched[idx]);
			double evals = eval1 + TEISUU * eval2;
			if (maxn < evals) {
				maxn = evals;
				maxid = i;
			}
		}
		pair<double, double> AA = dfs(nexnum[pos][maxid], rems);
		win[pos] += AA.first;
		searched[pos] += AA.second;
		return AA;
	}
	else {
		vector<pair<int, int>> nex_f; int V1 = 0, V2 = 0;
		for (int i = 0; i <= 7; i++) {
			for (int j = 0; j <= 7; j++) {
				usable[i][j] = hantei_easy(CandState[pos], CandTurn[pos], i, j);
				if (usable[i][j] == true) nex_f.push_back(make_pair(i, j));
				if (CandState[pos].c[i][j] == 1) V1 += 1;
				if (CandState[pos].c[i][j] == 2) V2 += 1;
			}
		}
		if (nex_f.size() != 0) {
			for (int i = 0; i < nex_f.size(); i++) {
				nex_zahyou[pos][i] = nex_f[i].first * 8 + nex_f[i].second;
				Initialize(CandState[pos], pos, 3 - CandTurn[pos]);
				Moves(CandState[StateCnt - 1], CandTurn[pos], (nex_zahyou[pos][i] >> 3), (nex_zahyou[pos][i] & 7));
			}
			pair<double, double> AA = Gen_Random(pos, rems);
			win[pos] += AA.first;
			searched[pos] += AA.second;
			return AA;
		}
		else {
			int cnt2 = 0;
			for (int i = 0; i < 8; i++) {
				for (int j = 0; j < 8; j++) {
					usable[i][j] = hantei_easy(CandState[pos], 3 - CandTurn[pos], i, j);
					if (usable[i][j] == true) cnt2 += 1;
				}
			}
			if (cnt2 != 0) {
				nex_zahyou[pos][0] = -1;
				Initialize(CandState[pos], pos, 3 - CandTurn[pos]);

				pair<double, double> AA = Gen_Random(pos, rems);
				win[pos] += AA.first;
				searched[pos] += AA.second;
				return AA;
			}
			else {
				double FinalScore = eval(64 * V1 / (V1 + V2), rems);
				win[pos] += FinalScore;
				searched[pos] += 1.0;
				return make_pair(FinalScore, 1.0);
			}
		}
	}
}

void Main() {
	// 機械学習データの入力
	FILE* in = freopen("record.txt", "r", stdin);
	if (in == NULL) {
		Situation = -1;
	}
	else {
		for (int i = 0; i < 128; i++) {
			for (int j = 0; j < 75; j++) {
				string str = ""; while (str.size() <= 1) { cin >> str; }
				d1[i][j] = StringToDouble(str);
			}
		}
		for (int i = 0; i < 75; i++) {
			string str = ""; while (str.size() <= 1) { cin >> str; }
			e1[i] = StringToDouble(str);
		}
		for (int i = 0; i < 75; i++) {
			for (int j = 0; j < 30; j++) {
				string str = ""; while (str.size() <= 1) { cin >> str; }
				d2[i][j] = StringToDouble(str);
			}
		}
		for (int i = 0; i < 30; i++) {
			string str = ""; while (str.size() <= 1) { cin >> str; }
			e2[i] = StringToDouble(str);
		}
		for (int i = 0; i < 30; i++) {
			for (int j = 0; j < 2; j++) {
				string str = ""; while (str.size() <= 1) { cin >> str; }
				d3[i][j] = StringToDouble(str);
			}
		}
		for (int i = 0; i < 2; i++) {
			string str = ""; while (str.size() <= 1) { cin >> str; }
			e3[i] = StringToDouble(str);
		}
	}

	// 背景を水色にする
	srand((unsigned)time(NULL));
	Scene::SetBackground(ColorF(0.0, 0.0, 0.1));

	// フォントを用意
	const Font font80(80);
	const Font font60(60);
	const Font font40(40);
	const Font font30(30);
	const Font font20(20);
	const Font font10(10);

	while (System::Update()) {
		double MouseX = Cursor::PosF().x;
		double MouseY = Cursor::PosF().y;

		// [状態 0] 待ち受け画面
		if (Situation == -1) {
			font40(U"record.txt を").draw(280, 130);
			font40(U"ダウンロードしてください").draw(160, 185);
			font20(U"このファイルを .exe ファイルと同じ階層に置かなければ").draw(140, 350);
			font20(U"ゲームで遊ぶことができません").draw(260, 380);
		}
		if (Situation == 0) {
			Rect(200, 250, 400, 80).draw(Color(255, col1[0], col1[0]));
			Rect(200, 360, 400, 80).draw(Color(255, 255, col1[1]));

			font80(U"Othello 869120").draw(100, 45);
			font30(U"～モンテカルロ木探索・深層学習によるオセロ対戦～").draw(45, 150);
			font40(U"先手を選ぶ").draw(300, 262, Palette::Black);
			font40(U"後手を選ぶ").draw(300, 372, Palette::Black);
			font30(U"クリックしてゲームを始める").draw(200, 490, ColorF(Periodic::Sine0_1(1.5s)));

			if (MouseX >= 200.0 && MouseX <= 600.0 && MouseY >= 250.0 && MouseY <= 330.0) col1[0] = max(col1[0] - 9, 31);
			else col1[0] = min(col1[0] + 9, 175);
			if (MouseX >= 200.0 && MouseX <= 600.0 && MouseY >= 360.0 && MouseY <= 440.0) col1[1] = max(col1[1] - 9, 31);
			else col1[1] = min(col1[1] + 9, 175);

			if (Scene::Time() - GetLastClick >= 0.1 && MouseL.down()) {
				GetLastClick = Scene::Time();
				if (MouseX >= 200.0 && MouseX <= 600.0 && MouseY >= 250.0 && MouseY <= 330.0) { Next_Move = 1; Situation = 1; Sente = 1; Reset(); }
				if (MouseX >= 200.0 && MouseX <= 600.0 && MouseY >= 360.0 && MouseY <= 440.0) { Next_Move = 2; Situation = 1; Sente = 2; Reset(); }
			}
		}

		// [状態 1] コンピュータのレベル選択
		if (Situation == 1) {
			font60(U"コンピュータのレベル選択").draw(40, 45);
			Rect(100, 170, 250, 70).draw(Color(255, 0, 0, 255 * col4[0] / 100));
			Rect(100, 260, 250, 70).draw(Color(255, 0, 0, 255 * col4[1] / 100));
			Rect(100, 350, 250, 70).draw(Color(255, 0, 0, 255 * col4[2] / 100));
			Rect(100, 440, 250, 70).draw(Color(255, 0, 0, 255 * col4[3] / 100));
			Rect(450, 170, 250, 70).draw(Color(255, 0, 0, 255 * col4[4] / 100));
			Rect(450, 260, 250, 70).draw(Color(255, 0, 0, 255 * col4[5] / 100));
			Rect(450, 350, 250, 70).draw(Color(0, 127, 255, 255 * col4[6] / 100));
			Rect(450, 440, 250, 70).draw(Color(0, 127, 255, 255 * col4[7] / 100));
			font30(U"レベル 1").draw(165, 187, Palette::Black);
			font30(U"レベル 2").draw(165, 277, Palette::Black);
			font30(U"レベル 3").draw(165, 367, Palette::Black);
			font30(U"レベル 4").draw(165, 457, Palette::Black);
			font30(U"レベル 5").draw(515, 187, Palette::Black);
			font30(U"レベル 6").draw(515, 277, Palette::Black);
			font30(U"レベル 7").draw(515, 367, Palette::Black);
			font30(U"レベル 8").draw(515, 457, Palette::Black);

			if (MouseX >= 100.0 && MouseX <= 350.0 && MouseY >= 170.0 && MouseY <= 240.0) col4[0] = min(col4[0] + 4, 100);
			else col4[0] = max(col4[0] - 4, 40);
			if (MouseX >= 100.0 && MouseX <= 350.0 && MouseY >= 260.0 && MouseY <= 330.0) col4[1] = min(col4[1] + 4, 100);
			else col4[1] = max(col4[1] - 4, 40);
			if (MouseX >= 100.0 && MouseX <= 350.0 && MouseY >= 350.0 && MouseY <= 420.0) col4[2] = min(col4[2] + 4, 100);
			else col4[2] = max(col4[2] - 4, 40);
			if (MouseX >= 100.0 && MouseX <= 350.0 && MouseY >= 440.0 && MouseY <= 510.0) col4[3] = min(col4[3] + 4, 100);
			else col4[3] = max(col4[3] - 4, 40);
			if (MouseX >= 450.0 && MouseX <= 700.0 && MouseY >= 170.0 && MouseY <= 240.0) col4[4] = min(col4[4] + 4, 100);
			else col4[4] = max(col4[4] - 4, 40);
			if (MouseX >= 450.0 && MouseX <= 700.0 && MouseY >= 260.0 && MouseY <= 330.0) col4[5] = min(col4[5] + 4, 100);
			else col4[5] = max(col4[5] - 4, 40);
			if (MouseX >= 450.0 && MouseX <= 700.0 && MouseY >= 350.0 && MouseY <= 420.0) col4[6] = min(col4[6] + 4, 100);
			else col4[6] = max(col4[6] - 4, 40);
			if (MouseX >= 450.0 && MouseX <= 700.0 && MouseY >= 440.0 && MouseY <= 510.0) col4[7] = min(col4[7] + 4, 100);
			else col4[7] = max(col4[7] - 4, 40);

			if (Scene::Time() - GetLastClick >= 0.1 && MouseL.down()) {
				GetLastClick = Scene::Time();
				if (MouseX >= 100.0 && MouseX <= 350.0 && MouseY >= 170.0 && MouseY <= 240.0) { Situation = 2; PLAYS = 1; BACKETS = 1; ALPHA = 10; }
				if (MouseX >= 100.0 && MouseX <= 350.0 && MouseY >= 260.0 && MouseY <= 330.0) { Situation = 2; PLAYS = 7; BACKETS = 7; ALPHA = 70; }
				if (MouseX >= 100.0 && MouseX <= 350.0 && MouseY >= 350.0 && MouseY <= 420.0) { Situation = 2; PLAYS = 30; BACKETS = 15; ALPHA = 300; }
				if (MouseX >= 100.0 && MouseX <= 350.0 && MouseY >= 440.0 && MouseY <= 510.0) { Situation = 2; PLAYS = 100; BACKETS = 20; ALPHA = 1000; }
				if (MouseX >= 450.0 && MouseX <= 700.0 && MouseY >= 170.0 && MouseY <= 240.0) { Situation = 2; PLAYS = 500; BACKETS = 20; ALPHA = 10000; }
				if (MouseX >= 450.0 && MouseX <= 700.0 && MouseY >= 260.0 && MouseY <= 330.0) { Situation = 2; PLAYS = 2000; BACKETS = 25; ALPHA = 100000; }
				if (MouseX >= 450.0 && MouseX <= 700.0 && MouseY >= 350.0 && MouseY <= 420.0) { Situation = 2; PLAYS = 100000; BACKETS = 100; ALPHA = 4000000; }
				if (MouseX >= 450.0 && MouseX <= 700.0 && MouseY >= 440.0 && MouseY <= 510.0) { Situation = 2; PLAYS = 200000; BACKETS = 100; ALPHA = 15000000; }
			}
		}

		// [状態 2] ゲームプレイ画面
		if (Situation == 2) {
			Score1 = 0; Score2 = 0;
			for (int i = 0; i <= 7; i++) {
				for (int j = 0; j <= 7; j++) {
					if (CurrentState.c[i][j] == 1) Score1 += 1;
					if (CurrentState.c[i][j] == 2) Score2 += 1;
				}
			}

			Rect(550, 0, 250, 600).draw(Color(51, 0, 0)); int ex = -1, ey = -1;
			if (MouseX >= 55.0 && MouseX <= 495.0 && MouseY >= 80.0 && MouseY <= 520.0) {
				ex = (MouseX - 55.0) / 55.0;
				ey = (MouseY - 80.0) / 55.0;
			}
			for (int i = 0; i <= 7; i++) {
				for (int j = 0; j <= 7; j++) {
					if (i == preX && j == preY) Rect(55 + i * 55, 80 + j * 55, 55, 55).draw(Color(50 + col2[i][j], 50 + col2[i][j], 255));
					else Rect(55 + i * 55, 80 + j * 55, 55, 55).draw(Color(col2[i][j], 100 + 3 * col2[i][j] / 5, col2[i][j]));
					if (i == ex && j == ey) col2[i][j] = min(col2[i][j] + 7, 100);
					else col2[i][j] = max(col2[i][j] - 7, 0);
				}
			}

			font30(U"Othello E869120｜GamePlay").draw(15, 15);
			for (int i = 0; i <= 8; i++) Line(55 + 55 * i, 80, 55 + 55 * i, 520).draw(Color(255, 255, 255));
			for (int i = 0; i <= 8; i++) Line(55, 80 + 55 * i, 495, 80 + 55 * i).draw(Color(255, 255, 255));

			for (int i = 0; i <= 7; i++) {
				for (int j = 0; j <= 7; j++) {
					if (CurrentState.c[i][j] == 0) continue;
					int I = CurrentState.c[i][j];
					if (Sente == 2) I = (3 - I);
					if (I == 1) Circle(82 + 55 * i, 107 + 55 * j, 18).draw(Color(0, 0, 0));
					if (I == 2) Circle(82 + 55 * i, 107 + 55 * j, 18).draw(Color(255, 255, 255));
				}
			}

			if (Sente == 1) {
				font20(U"黒番（自分）のスコア").draw(575, 15);
				font20(U"白番（相手）のスコア").draw(575, 125);
				if (Score1 <= 9) font40(Score1).draw(755, 45);
				if (Score1 >= 10) font40(Score1).draw(735, 45);
				if (Score2 <= 9) font40(Score2).draw(755, 155);
				if (Score2 >= 10) font40(Score2).draw(735, 155);
			}
			if (Sente == 2) {
				font20(U"黒番（相手）のスコア").draw(565, 15);
				font20(U"白番（自分）のスコア").draw(565, 125);
				if (Score2 <= 9) font40(Score2).draw(755, 45);
				if (Score2 >= 10) font40(Score2).draw(735, 45);
				if (Score1 <= 9) font40(Score1).draw(755, 155);
				if (Score1 >= 10) font40(Score1).draw(735, 155);
			}
			font20(U"あなたの勝利可能性").draw(575, 300);
			if (Win_Rate >= 0.75) {
				Circle(675, 455, 100).draw(Color(0, 255, 0, 40));
				Circle(675, 455, 100).drawPie(0, ToRadians(max(0.01, min(0.99, Win_Rate)) * 360.0), Color(0, 255, 0));
			}
			else if (Win_Rate >= 0.25) {
				Circle(675, 455, 100).draw(Color(255, 255, 0, 40));
				Circle(675, 455, 100).drawPie(0, ToRadians(max(0.01, min(0.99, Win_Rate)) * 360.0), Color(255, 255, 0));
			}
			else {
				Circle(675, 455, 100).draw(Color(255, 0, 0, 40));
				Circle(675, 455, 100).drawPie(0, ToRadians(max(0.01, min(0.99, Win_Rate)) * 360.0), Color(255, 0, 0));
			}
			Circle(675, 455, 70).draw(Color(51, 0, 0));
			int Fixed_Win_Rate = 100.0 * Win_Rate + 0.5;
			Fixed_Win_Rate = max(1, min(99, Fixed_Win_Rate));
			if (Fixed_Win_Rate <= 9) {
				font60(Fixed_Win_Rate).draw(660, 415);
				font30(U"%").draw(700, 447);
			}
			else {
				font60(Fixed_Win_Rate).draw(625, 415);
				font30(U"%").draw(700, 447);
			}

			// 自分の場合
			if (Next_Move == 1) {
				font20(U"クリックで手を打つことができます").draw(100, 550, ColorF(Periodic::Sine0_1(1.5s)));
				for (int i = 0; i < 8; i++) {
					for (int j = 0; j < 8; j++) usable[i][j] = hantei_easy(CurrentState, 1, i, j);
				}

				bool flag = false, flag2 = false, flag3 = false;
				for (int i = 0; i < 8; i++) {
					for (int j = 0; j < 8; j++) {
						if (usable[i][j] == true) { Circle(82 + 55 * i, 107 + 55 * j, 8).draw(Color(255, 127, 127)); flag = true; }
						if (CurrentState.c[i][j] == 0) flag2 = true;
					}
				}
				for (int i = 0; i < 8; i++) {
					for (int j = 0; j < 8; j++) {
						if (hantei_easy(CurrentState, 2, i, j) == true) flag3 = true;
					}
				}

				if (flag2 == false || (flag == false && flag3 == false)) {
					Rect(0, 0, 550, 600).draw(Color(0, 255, 0, 225));
					if (Score1 < Score2) font80(U"敗北！").draw(155, 150);
					else if (Score1 == Score2) font80(U"引き分け！").draw(75, 150);
					else font80(U"勝利！").draw(155, 150);
					font40(U"ゲームは終了しました").draw(75, 250);
					Rect(100, 400, 380, 80).draw(Color(255, 255, 255, col1[3]));
					if (MouseX >= 100.0 && MouseX <= 450.0 && MouseY >= 380.0 && MouseY <= 460.0) col1[3] = max(col1[3] - 13, 100);
					else col1[3] = min(col1[3] + 13, 255);
					font40(U"リザルト画面").draw(150, 412, Color(0, 0, 0));

					if (Scene::Time() - GetLastClick >= 0.1 && MouseL.down()) {
						GetLastClick = Scene::Time();
						if (MouseX >= 100.0 && MouseX <= 450.0 && MouseY >= 380.0 && MouseY <= 460.0) {
							if (Score1 < Score2) Data.push_back(0.0);
							if (Score1 == Score2) Data.push_back(0.5);
							if (Score1 > Score2) Data.push_back(1.0);
							Situation = 3; col1[3] = 100;
						}
					}
				}
				else if (flag == false) {
					Rect(0, 0, 550, 600).draw(Color(255, 0, 0, 225));
					font80(U"残念！").draw(155, 150);
					font40(U"打てる手がありません").draw(75, 250);
					Rect(100, 400, 380, 80).draw(Color(255, 255, 255, col1[3]));
					if (MouseX >= 100.0 && MouseX <= 450.0 && MouseY >= 380.0 && MouseY <= 460.0) col1[3] = max(col1[3] - 13, 100);
					else col1[3] = min(col1[3] + 13, 255);
					font40(U"パスする").draw(190, 412, Color(0, 0, 0));

					if (Scene::Time() - GetLastClick >= 0.1 && MouseL.down()) {
						GetLastClick = Scene::Time();
						if (MouseX >= 100.0 && MouseX <= 450.0 && MouseY >= 380.0 && MouseY <= 460.0) { Next_Move = 2; Ti = 0; col1[3] = 100; }
					}
				}
				else {
					Consecutive = 0;
					if (Scene::Time() - GetLastClick >= 0.1 && MouseL.down()) {
						GetLastClick = Scene::Time();
						if (ex != -1 && ey != -1 && usable[ex][ey] == true) {
							Moves(CurrentState, 1, ex, ey); Data.push_back(Win_Rate);
							Next_Move = 2; Ti = 0;
							preX = ex; preY = ey;
						}
					}
				}
			}

			// 相手の場合
			if (Next_Move == 2) {
				Ti += 1;

				if (Ti == 2) {
					// 画面表示
					Rect(0, 0, 550, 600).draw(Color(168, 156, 46, 225));
					font80(U"考え中…").draw(115, 130);
					font40(U"しばらくお待ちください").draw(75, 230);

					StateCnt = 0;
					TansakuCnt = 0;
					AlphaBeta = 0;
					Initialize(CurrentState, -1, 2);
				}
				if (Ti == 3) {
					// 画面表示
					Rect(0, 0, 550, 600).draw(Color(168, 156, 46, 225));
					font80(U"考え中…").draw(115, 130);
					font40(U"しばらくお待ちください").draw(75, 230);

					// α-β探索
					tuple<int, int, int> res = dfs2(CurrentState, 2);
					if (get<0>(res) >= 1) {
						if (get<1>(res) == -1) {
							Win_Rate = 0.0;
							Next_Move = 1; Ti = 0; Consecutive += 1;
						}
						else {
							int mx = get<1>(res), my = get<2>(res);
							if (get<0>(res) == 2) {
								AlphaBeta = 0;
								tuple<int, int, int> res2 = dfs3(CurrentState, -1, 2);
								if (AlphaBeta < ALPHA) { mx = get<1>(res2); my = get<2>(res2); }
							}
							Moves(CurrentState, 2, mx, my);
							Win_Rate = 0.0;
							Next_Move = 1; Ti = 0;
							preX = mx; preY = my;
						}
					}
					else if (get<0>(res) == -1) {
						AlphaBeta = 0;
						tuple<int, int, int> res2 = dfs3(CurrentState, -1, 2);
						if (AlphaBeta < ALPHA) {
							Moves(CurrentState, 2, get<1>(res2), get<2>(res2));
							Win_Rate = 1.0;
							Next_Move = 1; Ti = 0;
							preX = get<1>(res2); preY = get<2>(res2);
						}
					}
				}
				if (Ti >= 4) {
					vector<pair<int, int>> nex; int rems = 0;
					for (int i = 0; i < 8; i++) {
						for (int j = 0; j < 8; j++) {
							usable[i][j] = hantei_easy(CurrentState, 2, i, j);
							if (usable[i][j] == true) nex.push_back(make_pair(i, j));
							if (CurrentState.c[i][j] == 0) rems++;
						}
					}
					if (nex.size() == 0) {
						Next_Move = 1; Ti = 0; Consecutive += 1;
					}
					else {
						// 画面表示
						Rect(0, 0, 550, 600).draw(Color(168, 156, 46, 225));
						font80(U"考え中…").draw(115, 130);
						font40(U"しばらくお待ちください").draw(75, 230);
						Rect(95, 325, 360, 60).draw(Color(255, 255, 255));
						Rect(100 + 350 * (Ti - 4) / BACKETS, 330, 350 - 350 * (Ti - 4) / BACKETS, 50).draw(Color(168, 156, 46));
						font30(U"現在").draw(180, 410);
						if (100 * (Ti - 4) / BACKETS <= 9) font30(100 * (Ti - 4) / BACKETS).draw(270, 410);
						else font30(100 * (Ti - 4) / BACKETS).draw(255, 410);
						font30(U"% 完了").draw(300, 410);
						font30(U"探索状態数").draw(150, 455);
						if (TansakuCnt < 10) font30(TansakuCnt).draw(412, 455);
						else if (TansakuCnt < 100) font30(TansakuCnt).draw(394, 455);
						else if (TansakuCnt < 1000) font30(TansakuCnt).draw(376, 455);
						else if (TansakuCnt < 10000) font30(TansakuCnt).draw(358, 455);
						else if (TansakuCnt < 100000) font30(TansakuCnt).draw(340, 455);
						else font30(TansakuCnt).draw(322, 455);

						// モンテカルロ木探索
						Consecutive = 0;
						if (PLAYS < 100000) {
							for (int i = 0; i < PLAYS / BACKETS; i++) {
								TansakuCnt += 1;
								dfs(0, rems);
							}
						}
						else {
							int ti = clock(), lim = 3;
							if (PLAYS == 200000) lim = 15;
							while (clock() - ti < lim * CLOCKS_PER_SEC / 100) {
								if (StateCnt >= 4000000 * (Ti - 3) / BACKETS) break;
								TansakuCnt += 1;
								dfs(0, rems);
							}
						}
						if (Ti == 3 + BACKETS) {
							int minid_x = -1, minid_y = -1; double minx = 2.0;
							for (int i = 0; i < deg[0]; i++) {
								int idx = nexnum[0][i];
								double shouritsu = 1.0 * win[idx] / searched[idx];
								if (minx > shouritsu) {
									minx = shouritsu;
									minid_x = (nex_zahyou[0][i] >> 3);
									minid_y = (nex_zahyou[0][i] & 7);
								}
							}
							Moves(CurrentState, 2, minid_x, minid_y);
							Win_Rate = minx;
							Next_Move = 1; Ti = 0;
							preX = minid_x; preY = minid_y;

							// 勝率補正
							if (PLAYS < 1000) {
								for (int i = 0; i < 1000 - PLAYS; i++) {
									TansakuCnt += 1;
									dfs(0, rems);
								}
								double minx2 = 2.0;
								for (int i = 0; i < deg[0]; i++) {
									int idx = nexnum[0][i];
									minx2 = min(minx2, 1.0 * win[idx] / searched[idx]);
								}
								Win_Rate = minx2;
							}
						}
					}
				}
			}
		}

		// [状態 3] リザルト画面
		if (Situation == 3) {
			font80(U"最終結果").draw(240, 0);
			Line(280, 120, 280, 480).draw(4, Color(255, 255, 255));
			Line(760, 120, 760, 480).draw(4, Color(255, 255, 255));
			Line(280, 120, 760, 120).draw(4, Color(255, 255, 255));
			Line(280, 210, 760, 210).draw(LineStyle::SquareDot, 2, Color(255, 255, 255));
			Line(280, 300, 760, 300).draw(LineStyle::SquareDot, 2, Color(255, 255, 255));
			Line(280, 390, 760, 390).draw(LineStyle::SquareDot, 2, Color(255, 255, 255));
			Line(280, 480, 760, 480).draw(4, Color(255, 255, 255));
			Line(328, 480, 328, 488).draw(2, Color(255, 255, 255));
			Line(388, 480, 388, 488).draw(2, Color(255, 255, 255));
			Line(448, 480, 448, 488).draw(2, Color(255, 255, 255));
			Line(508, 480, 508, 488).draw(2, Color(255, 255, 255));
			Line(568, 480, 568, 488).draw(2, Color(255, 255, 255));
			Line(628, 480, 628, 488).draw(2, Color(255, 255, 255));
			Line(688, 480, 688, 488).draw(2, Color(255, 255, 255));
			Line(748, 480, 748, 488).draw(2, Color(255, 255, 255));
			font20(U"75%").draw(230, 195);
			font20(U"50%").draw(230, 285);
			font20(U"25%").draw(230, 375);
			font20(U"5").draw(320, 492);
			font20(U"10").draw(373, 492);
			font20(U"15").draw(433, 492);
			font20(U"20").draw(493, 492);
			font20(U"25").draw(553, 492);
			font20(U"30").draw(613, 492);
			font20(U"35").draw(673, 492);
			font20(U"40").draw(733, 492);
			for (int i = 0; i < (int)Data.size() - 1; i++) {
				Line(280 + i * 12, 480.0 - 360.0 * Data[i], 292 + i * 12, 480.0 - 360.0 * Data[i + 1]).draw(2, Color(175, 175, 255));
			}
			for (int i = 0; i < (int)Data.size(); i++) {
				if (Data[i] >= 0.75) Circle(280 + i * 12, 480.0 - 360.0 * Data[i], 4).draw(Color(0, 255, 0));
				else if (Data[i] >= 0.25) Circle(280 + i * 12, 480.0 - 360.0 * Data[i], 4).draw(Color(255, 255, 0));
				else Circle(280 + i * 12, 480.0 - 360.0 * Data[i], 4).draw(Color(255, 0, 0));
			}

			Rect(275, 535, 250, 50).draw(Color(255, 255, 0, col1[3]));
			if (MouseX >= 275.0 && MouseX <= 525.0 && MouseY >= 535.0 && MouseY <= 585.0) col1[3] = max(col1[3] - 13, 100);
			else col1[3] = min(col1[3] + 13, 255);
			font30(U"おわる").draw(355, 540, Color(0, 0, 0));

			if (Scene::Time() - GetLastClick >= 0.1 && MouseL.down()) {
				GetLastClick = Scene::Time();
				if (MouseX >= 275.0 && MouseX <= 525.0 && MouseY >= 535.0 && MouseY <= 585.0) break;
			}

			if (Sente == 1) {
				font20(U"黒番（自分）").draw(40, 150);
				if (Score1 <= 9) font80(Score1).draw(80, 180);
				if (Score1 >= 10) font80(Score1).draw(55, 180);
				font30(U"｜").draw(85, 300);
				if (Score2 <= 9) font80(Score2).draw(80, 355);
				if (Score2 >= 10) font80(Score2).draw(55, 355);
				font20(U"白番（相手）").draw(40, 460);
			}
			if (Sente == 2) {
				font20(U"黒番（相手）").draw(40, 150);
				if (Score2 <= 9) font80(Score2).draw(80, 180);
				if (Score2 >= 10) font80(Score2).draw(55, 180);
				font30(U"｜").draw(85, 300);
				if (Score1 <= 9) font80(Score1).draw(80, 355);
				if (Score1 >= 10) font80(Score1).draw(55, 355);
				font20(U"白番（自分）").draw(40, 460);
			}
		}
	}
}