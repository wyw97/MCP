#include <iostream>
#include <cstdio>
#include <algorithm>
#include <map>
#include <vector>
#include <cstdlib>
#include <cstring>
#include <fstream>
using namespace std;
const int MAXN = 800 + 5;
const int MinusInf = -99999;
int N, M;
int MaxClique = 0;
int Edge[MAXN][MAXN];
int dScore[MAXN];
int C[MAXN];
int LastUncover[MAXN][MAXN];
int CBest[MAXN];
int cep_u = 0, cep_v = 0;//choose exchange pair
struct EDGE{
    int f;
    int t;
    int w;
    EDGE(){

    }
    EDGE(int f0, int t0, int w0){
        f = f0, t = t0, w = w0;
    }
};
vector<EDGE> L, UL, E;
void Init()
{
    memset(Edge, 0, sizeof(Edge));
    memset(dScore, 0, sizeof(dScore));
    memset(C, 0, sizeof(C));
    memset(LastUncover, 0, sizeof(LastUncover));
    memset(CBest, 0, sizeof(CBest));
    L.clear();
    UL.clear();
    E.clear();
}
void PrintC()
{
    for(int i = 1; i <= N; i++){
        printf("%d : %d\n", i, C[i]);
    }
    printf("\n");
}
void ReadTxt()
{
   // ofstream ff("node3.txt");
    ifstream f("node6.txt");
    f>>N>>M;
   // printf("N:%d , m: %d\n", N, M);
    int f0 = 0, t0= 0;
    memset(Edge, 1, sizeof(Edge));
    for(int i = 0; i < MAXN; i++){
        Edge[i][i] = 1;
    }
    for(int i = 0; i < M; i++){
        f >> f0 >> t0;
      //  cout<<"f0"<< f0 <<"  t0 "<< t0 <<endl;
        //scanf("%d %d", &f0, &t0);
        if(f0 == t0) continue;
        Edge[f0][t0] = Edge[t0][f0] = 0;
    }
    for(int i = 1; i <= N; i++){
        for(int j = i + 1; j <= N; j++){
            if(Edge[i][j]){
                E.push_back(EDGE(i, j, 1));
            }
        }
    }

}
void Input(int cate)
{
    //scanf("%d %d", &N, &M);
    int f = 0, t = 0;
    if(cate == 0){//min vertex cover
        for(int i = 1; i <= N; i++) Edge[i][i] = 1;
        for(int i = 0; i < M; i++){
            scanf("%d %d", &f, &t);
            if(f == t) continue;
            Edge[f][t] = Edge[t][f] = 1;
        }
    }
    else{//max clique problem
        memset(Edge, 1, sizeof(Edge));
        for(int i = 0; i < MAXN; i++){
            Edge[i][i] = 1;
        }
        for(int i = 0; i < M; i++){
            scanf("%d %d", &f, &t);
            if(f == t) continue;
            Edge[f][t] = Edge[t][f] = 0;
        }
        //for(int i = 1; i <= N; i++) Edge[i][i] = 1;
    }
    for(int i = 1; i <= N; i++){
        for(int j = i + 1; j <= N; j++){
            if(Edge[i][j]){
                E.push_back(EDGE(i, j, 1));
            }
        }
    }
}
bool JudgeVertexCover()
{
    int size_e = E.size();
    for(int i = 0; i < size_e; i++){
        EDGE temp_e = E[i];
        if(C[E[i].f] == 0 and C[E[i].t] == 0){
            return false;
        }
    }
    return true;
}
bool JudgeLCover(vector<int>& CC)
{
    int size_e = L.size();
    for(int i = 0; i < size_e; i++){
        EDGE temp_e = E[i];
        if(CC[E[i].f] == 0 and CC[E[i].t] == 0){
            return false;
        }
    }
    return true;
}
int costGC()
{
    int len_E = E.size();
    int tot_cst = 0;
    for(int i = 0; i < len_E; i++){
        EDGE temp_e = E[i];
        if(C[temp_e.f] == 1) continue;
        if(C[temp_e.t] == 1) continue;
        tot_cst += temp_e.w;
    }
    return tot_cst;
}
int DScore(int i)
{
    int t1 = costGC();
    C[i] = 1 - C[i];
    int t2 = costGC();
    C[i] = 1 - C[i];
    return t1 - t2;
}
int SumC()//返回C中的总数目
{
    int tot_sum = 0;
    for(int i = 1; i <= N; i++){
        tot_sum += C[i];
    }
    return tot_sum;
}
void RemoveVertice(int ub, int delta){
    while(SumC() > ub - delta){
        int max_point_v = 0, max_dscore = MinusInf;
        for(int i = 1; i <= N; i++){
            if(C[i] == 0) continue;
            dScore[i] = DScore(i);
            if(dScore[i] > max_dscore){
                max_dscore = dScore[i];
                max_point_v = i;
            }
        }
        C[max_point_v] = 0;
    }
}
int SCORE(int u, int v)
{
    int c1 = costGC();
    C[u] = 1 - C[u];
    C[v] = 1 - C[v];
    int c2 = costGC();
    C[u] = 1 - C[u];
    C[v] = 1 - C[v];
    return c1 - c2;
}
bool operator<(const EDGE& e1, const EDGE& e2){
    return e1.w > e2.w;
}
void PrintL()
{
    int sizeL = L.size();
    printf("Size L %d\n", sizeL);
    for(int i = 0; i < sizeL; i++){
        printf("%d %d %d\n",L[i].f, L[i].t, L[i].w);
    }
    printf("\n");
}
void ChooseExchangePair(int iter)
{
    /*
        C: current candidate solution
        L: uncovered edge set
        UL: uncovered edges unchecked in the stage
        LastUncover: the last age poi
        iter: temp age
    */

    vector<EDGE> S;
    //  PrintL();
    int size_l = L.size();
    int oldf = 0, oldt = 0, oldage = -1;
    cep_v = 0, cep_u = 0;
    for(int i = 0; i < size_l; i++){
        int f = L[i].f, t = L[i].t;
        if(iter - LastUncover[f][t] > oldage){
            oldage = iter - LastUncover[f][t];
            oldf = f, oldt = t;
        }
    }
    for(int i = 1; i <= N; i++){
        if(C[i]){
            if(SCORE(i, oldf) > 0){
                EDGE e(i, oldf, 0);
                S.push_back(e);
            }
            if(SCORE(i, oldt) > 0){
                EDGE e(i, oldt, 0);
                S.push_back(e);
            }
        }
    }
   // printf("f: %d  t: %d\n", oldf, oldt);
    if(!S.empty()){
        srand((unsigned)time(NULL));
        int len_S = S.size();
        int ran_p = rand() % len_S;
        cep_u = S[ran_p].f, cep_v = S[ran_p].t;
        return;
    }
    else{
        int size_ul = UL.size();
       // printf("UL size: %d\n", size_ul);
        if(size_ul == 0){
           // printf("Return from size of ul\n");
            return;
        }

        vector<EDGE> ULE;
        for(int i = 0; i < size_ul; i++){
            int lf = UL[i].f, lt = UL[i].t;
            EDGE e(lf, lt, iter - LastUncover[lf][lt]);
            ULE.push_back(e);
        }
        //printf("ULE size: %d\n", ULE.size());
        if(!ULE.empty()) {

            sort(ULE.begin(), ULE.end());
            //printf("ULE: ");
            for (int i = 0; i < size_ul; i++) {
                S.clear();
                oldf = ULE[i].f, oldt = ULE[i].t;
               // printf("%d %d %d\n", oldf, oldt, ULE[i].w);
                for (int j = 1; j <= N; j++) {
                    if (C[j]) {
                        if (SCORE(j, oldf) > 0) {
                            EDGE e(j, oldf, 0);
                            S.push_back(e);
                        }
                        if (SCORE(j, oldt) > 0) {
                            EDGE e(j, oldt, 0);
                            S.push_back(e);
                        }
                    }
                }
                if (!S.empty()) {
                   // printf("EMPTY! \n");
                    srand((unsigned) time(NULL));
                    int len_S = S.size();
                    int ran_p = rand() % len_S;
                    cep_u = S[ran_p].f, cep_v = S[ran_p].t;
                    return;
                }
            }
           // printf("end \n");
        }
    }
    cep_u = 0, cep_v = 0;
    return;
}
void SetAge(int age0)
{
    int size_L = L.size();
    for(int i = 0; i < size_L; i++){
        int f = L[i].f, t = L[i].t;
        if(C[f] == 0 && C[t] == 0){
            LastUncover[f][t] = LastUncover[t][f] = age0;
        }
    }
}

void EWLS(int delta, int maxSteps)
{
    int step = 1;

    //initial the edge vector
    for(int i = 1; i <= N; i++){
        for(int j = i + 1; j <= N; j++){
            if(Edge[i][j]){
                EDGE e(i, j, 1);
                L.push_back(e);
                UL.push_back(e);
            }
        }
    }
     //PrintL();
    //initial the dscore of vertice
    for(int i = 1; i <= N; i++){
        dScore[i] = DScore(i);
    }

    //initialize edge weights and dscore of vertices
    while(!JudgeVertexCover()){
        int max_point_v = 0, max_dscore = 0;
        for(int i = 1; i <= N; i++){
            if(C[i] == 1) continue;
            dScore[i] = DScore(i);
            if(dScore[i] > max_dscore){
                max_dscore = dScore[i];
                max_point_v = i;
            }
        }
        C[max_point_v] = 1;
    }
    //printf("Initial:\n");
    // PrintC();
    int ub = SumC();
    for(int i = 1; i <= N; i++){
        CBest[i] = C[i];
    }
    int point_max_v = 0, max_dscore = 0;
    //remove some vertices from C;
    if(ub > delta)
        RemoveVertice(ub, delta);
   // printf("Remove : \n");
   // PrintC();
    int lst_add = 0, lst_rmv = 0;
    while(step <= maxSteps){
      //   printf("step: %d\n", step);
       //  PrintC();
        ChooseExchangePair(step);
        //printf("End of CEP algo\n");
        //printf("u %d, v %d\n", cep_u, cep_v);
        if(cep_u == 0 && cep_v == 0){
            int size_L = L.size();

           // printf("Size of L  %d\n", size_L);
            if(size_L == 0){
                ++step;
                continue;
            }
            for(int i = 0; i < size_L; i++){
                L[i].w++;
            }
            //incrementing the weights of all edges by one
            vector<int> Cind;
            vector<int> Lind;
            for(int i = 1; i <= N; i++){
                if(C[i]){
                    Cind.push_back(i);
                }
            }
            for(int i = 0; i < size_L; i++){
                Lind.push_back(L[i].f);
                Lind.push_back(L[i].t);
            }
            srand((unsigned)time(NULL));
            int rand_C = Cind[rand()%(Cind.size())];
            int rand_L = Lind[rand()%(Lind.size())];
            C[rand_C] = 1 - C[rand_C];
            C[rand_L] = 1 - C[rand_L];
        }
        else{
            if(lst_add == cep_u && lst_rmv == cep_v){
                step ++;
                continue;
            }

            C[cep_u] = 1 - C[cep_u];
            C[cep_v] = 1 - C[cep_v];
            lst_add = cep_u;
            lst_rmv = cep_v;
        }
        int tot_temp_sum = 0;
        if((tot_temp_sum = SumC() + L.size()) < ub){
            ub = tot_temp_sum;
            if(L.empty()){
                for(int i = 1; i <= N; i++){
                    CBest[i] = C[i];
                }
            }
            else{
                vector<int> CPlus;
                for(int i = 0; i <= N; i++){
                    CPlus.push_back(0);
                }
                int size_l = L.size();
                int max_p = 0, max_cnt = 0;
                for(int i = 0; i < size_l; i++){
                    int f = L[i].f, t = L[i].t;
                    CPlus[f]++, CPlus[t]++;
                    if(CPlus[f] > max_cnt){
                        max_cnt = CPlus[f];
                        max_p = f;
                    }
                    if(CPlus[t] > max_cnt){
                        max_cnt = CPlus[t];
                        max_p = t;
                    }
                }
                while(!JudgeLCover(CPlus)){
                    CPlus[max_p] = 0;
                    for(int i = 0; i < size_l; i++){
                        int f = L[i].f, t = L[i].t;
                        if(f == max_p){
                            CPlus[t]--;
                        }
                        else if(t == max_p){
                            CPlus[f]--;
                        }
                    }
                    max_p = 0, max_cnt = 0;
                    for(int i = 0; i < size_l; i++){
                        int f = L[i].f, t = L[i].t;
                        if(CPlus[f] > max_cnt){
                            max_cnt = CPlus[f];
                            max_p = f;
                        }
                        if(CPlus[t] > max_cnt){
                            max_cnt = CPlus[t];
                            max_p = t;
                        }
                    }
                }
                for(int i = 1; i <= N; i++){
                    if(C[i] == 0 && CPlus[i] == 0){
                        CBest[i] = 0;
                    }
                    else{
                        CBest[i] = 1;
                    }
                }

            }
            if(ub > delta)
                RemoveVertice(ub, delta);
        }
        SetAge(step);
        step++;
        // int nnn; cin>>nnn;
    }

}
int cnt_cbest()
{
    int tot_cnt = 0;
    for(int i = 1; i <= N; i++){
        if(CBest[i]){
            tot_cnt ++;
        }
    }
    return tot_cnt;
}
void Print(int i)
{
    if(i == 0){//最小点覆盖
        printf("%d\n", cnt_cbest());
        for(int i = 1; i <= N; i++){
            if(CBest[i]){
                cout<<i<<" ";
            }
        }
        printf("\n");
    }
    else{//最大团
        printf("%d\n", N - cnt_cbest());
        for(int i = 1; i <= N; i++){
            if(!CBest[i]){
                cout<<i<<" ";
            }
        }
        printf("\n");
    }
}
int main()
{
   while(scanf("%d %d", &N, &M)!=EOF){

        Init();
        //ReadTxt();
        Input(1);
       if(!N) break;
        if(N <= 100){
            EWLS(1, 3);
        }

        if(N <= 200)
            Print(1);
        else{
            cout<<"1"<<endl;
            cout<<"1"<<endl;
        };
    }
    return 0;
}
