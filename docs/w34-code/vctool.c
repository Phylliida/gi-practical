// vctool.c: exact VC dimension of the conference-graph separation set systems (w34).
// Input (stdin): repeated "G name\n n\n n rows of '0'/'1' (adjacency)\n".
// Usage: vctool vc1 [maxsec]        one-round system E_vw on ground V.
//        vctool vc2 [maxsec]        two-round system F_vw on ground unordered pairs {a,b}.
// Output one line per graph. Time cap per search; "(>=d)" means exact value not established within the cap.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>
#include <math.h>
typedef uint64_t u64;
#define MAXN 200
static int n; static signed char C[MAXN][MAXN]; static char name[256];
static int NW;
static int nsets, ground; static u64 **X; // X[g] bitset over sets
static double t0; static double maxsec=60; static int timed_out=0;
static double now(){struct timespec ts;clock_gettime(CLOCK_MONOTONIC,&ts);return ts.tv_sec+1e-9*ts.tv_nsec;}
static int best=0; static int bestD[64]; static int curD[64];
static u64 *groups[1<<20];
static inline int inter_nonempty(const u64*a,const u64*b){for(int i=0;i<NW;i++)if(a[i]&b[i])return 1;return 0;}
static inline int inter_diff_nonempty(const u64*a,const u64*b){for(int i=0;i<NW;i++)if(a[i]&~b[i])return 1;return 0;}
static u64 *pool; static long poolcap, poolpos;
static u64 *galloc(){ if(poolpos+NW>poolcap){fprintf(stderr,"pool exhausted\n");exit(1);} u64*r=pool+poolpos; poolpos+=NW; return r; }
static int found_target;
// groups at this level: arr[0..2^d-1], each NW words.
static void dfs(u64 **arr,int d,int start,int target){
  if(found_target||timed_out)return;
  if(d==target){found_target=1;memcpy(bestD,curD,sizeof(int)*d);best=target;return;}
  if(now()-t0>maxsec){timed_out=1;return;}
  int m=1<<d;
  for(int x=start;x<ground;x++){
    if(ground-x<target-d)return;
    int ok=1;
    for(int i=0;i<m&&ok;i++){ if(!inter_nonempty(arr[i],X[x])||!inter_diff_nonempty(arr[i],X[x]))ok=0; }
    if(!ok)continue;
    long savedpos=poolpos;
    u64 **next=(u64**)malloc(sizeof(u64*)*(2*m));
    for(int i=0;i<m;i++){u64*a=galloc(),*b=galloc();for(int w=0;w<NW;w++){a[w]=arr[i][w]&X[x][w];b[w]=arr[i][w]&~X[x][w];}next[2*i]=a;next[2*i+1]=b;}
    curD[d]=x;
    dfs(next,d+1,x+1,target);
    free(next);
    poolpos=savedpos;
    if(found_target||timed_out)return;
  }
}
static int compute_vc(int *out_exact){
  // nsets sets over ground given via X; returns max d with shattered set found (iterative deepening).
  poolcap=(long)(NW)*(1L<<22); pool=(u64*)malloc(sizeof(u64)*poolcap);
  if(!pool){fprintf(stderr,"oom\n");exit(1);} poolpos=0; timed_out=0;
  u64 *all=galloc(); memset(all,0,sizeof(u64)*NW); for(int i=0;i<nsets;i++)all[i/64]|=1ULL<<(i%64);
  best=0; t0=now();
  int d=1;
  while(1){ found_target=0; u64*arr[1]; arr[0]=all;
    dfs(arr,0,0,d);
    if(timed_out){*out_exact=0;break;}
    if(!found_target){*out_exact=1;break;}
    d++; if(d>26){*out_exact=0;break;}
  }
  free(pool); return best;
}
static void free_X(){ for(int g=0;g<ground;g++)free(X[g]); free(X); }
static void dedupe_and_build(unsigned char **M,int nset0){ // M[s][g]
  // dedupe identical set rows; construct X
  // use sorting by hash then memcmp
  int keep=0; int *idx=(int*)malloc(sizeof(int)*nset0);
  // simple dedupe via sort on memcmp
  // qsort with global ptr
  for(int i=0;i<nset0;i++)idx[i]=i;
  // insertion of distinct via hash table
  int cap=nset0*2+1; int *tab=(int*)malloc(sizeof(int)*cap); memset(tab,-1,sizeof(int)*cap);
  unsigned char **R=(unsigned char**)malloc(sizeof(char*)*nset0);
  for(int i=0;i<nset0;i++){ u64 h=1469598103934665603ULL; for(int g=0;g<ground;g++){h^=M[i][g];h*=1099511628211ULL;} int p=h%cap; int dup=0; while(tab[p]!=-1){ if(memcmp(R[tab[p]],M[i],ground)==0){dup=1;break;} p=(p+1)%cap; } if(!dup){tab[p]=keep;R[keep]=M[i];keep++;} }
  nsets=keep; NW=(nsets+63)/64;
  X=(u64**)malloc(sizeof(u64*)*ground);
  for(int g=0;g<ground;g++){X[g]=(u64*)calloc(NW,sizeof(u64)); for(int s=0;s<nsets;s++)if(R[s][g])X[g][s/64]|=1ULL<<(s%64);}
  free(R);free(tab);free(idx);
}
static void run_vc1(){
  int nset0=n*(n-1)/2; ground=n;
  unsigned char **M=(unsigned char**)malloc(sizeof(char*)*nset0);
  int s=0;
  for(int v=0;v<n;v++)for(int w=v+1;w<n;w++){M[s]=(unsigned char*)malloc(ground);for(int x=0;x<n;x++)M[s][x]=(C[v][x]!=C[w][x]);s++;}
  dedupe_and_build(M,nset0);
  int ex; int d=compute_vc(&ex);
  printf("%s n=%d vc1=%s%d (log2n=%.2f, 2log2n=%.2f) distinct_sets=%d\n",name,n,ex?"":">=",d,__builtin_log2((double)n),2*__builtin_log2((double)n),nsets);
  for(int i=0;i<nset0;i++)free(M[i]); free(M); free_X();
}
// two-round system
static short *Tarr; 
static inline short T(int ab,int v){return Tarr[ab*n+v];}
static void run_vc2(){
  ground=n*(n-1)/2; int nset0=n*(n-1)/2;
  int *ai=(int*)malloc(sizeof(int)*ground),*bi=(int*)malloc(sizeof(int)*ground);
  int g=0; for(int a=0;a<n;a++)for(int b=a+1;b<n;b++){ai[g]=a;bi[g]=b;g++;}
  Tarr=(short*)malloc(sizeof(short)*ground*n);
  for(int t=0;t<ground;t++){int a=ai[t],b=bi[t];for(int v=0;v<n;v++){int s=0;for(int x=0;x<n;x++)s+=C[a][x]*C[b][x]*C[v][x];Tarr[t*n+v]=s;}}
  unsigned char **M=(unsigned char**)malloc(sizeof(char*)*nset0);
  double *p=(double*)malloc(sizeof(double)*nset0);
  int s=0; double maxp=0,sump=0;
  for(int v=0;v<n;v++)for(int w=v+1;w<n;w++){ unsigned char *row=(unsigned char*)malloc(ground); long cnt=0;
    for(int t=0;t<ground;t++){int a=ai[t],b=bi[t];
      int coll=0; if(a!=v&&a!=w&&b!=v&&b!=w&&C[a][v]==C[a][w]&&C[b][v]==C[b][w]&&Tarr[t*n+v]==Tarr[t*n+w])coll=1;
      row[t]=coll; cnt+=coll; }
    M[s]=row; p[s]=(double)cnt/ground; if(p[s]>maxp)maxp=p[s]; sump+=p[s]; s++; }
  printf("%s n=%d mean_p2=%.4f max_p2=%.4f 1/sqrt(n)=%.4f\n",name,n,sump/nset0,maxp,1.0/__builtin_sqrt(n));
  // restricted VC for thresholds: B_c = {pairs: p2 >= n^{-c}}, thresholds c list.
  double cs[]={2.0,1.0,0.75,0.5,0.4,0.3,0.2,0.1,0.05,-1};
  for(int ci=0;cs[ci]>0;ci++){ double th=pow(n,-cs[ci]); int kept=0; unsigned char **Mk=(unsigned char**)malloc(sizeof(char*)*nset0);
    for(int i=0;i<nset0;i++)if(p[i]>=th)Mk[kept++]=M[i];
    if(kept==0){printf("  c=%.2f th=%.4f |B_c|=0 d_c=0\n",cs[ci],th);free(Mk);continue;}
    dedupe_and_build(Mk,kept);
    int ex; int d=compute_vc(&ex);
    printf("  c=%.2f th=%.4f |B_c|=%d distinct_sets=%d d_c=%s%d\n",cs[ci],th,kept,nsets,ex?"":">=",d);
    free(Mk); free_X();
  }
  for(int i=0;i<nset0;i++)free(M[i]); free(M); free(p); free(Tarr); free(ai); free(bi);
}
int main(int argc,char**argv){
  const char*mode=argv[1]; if(argc>2)maxsec=atof(argv[2]);
  char line[4096];
  while(fgets(line,sizeof line,stdin)){ if(strncmp(line,"G ",2)==0){sscanf(line+2,"%255[^\n]",name); if(!fgets(line,sizeof line,stdin))break; n=atoi(line); for(int i=0;i<n;i++){fgets(line,sizeof line,stdin);for(int j=0;j<n;j++){C[i][j]=(i==j)?0:(line[j]=='1'?-1:1);} }
    if(!strcmp(mode,"vc1"))run_vc1(); else run_vc2(); fflush(stdout); } }
  return 0;
}
