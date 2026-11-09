// exactiso.c -- exact search for S in GL(N,2) with span(P o S) = span(P'), for
// k-dimensional spaces P, P' of quadratic forms on F_2^N.  (Referee tool, w37.)
// Written independently of docs/w35-cubic-check.py.  Pruning uses only quantities
// invariant under ANY span isometry: for v in W: r(v)=rank of w -> B(v,w), z(v)=[ev(v)=0],
// and the multiset over w of (r,z at w), (r,z at v+w), [B(v,w)=0].
//
// stdin:  N k mode maxsol
//         k forms of P, then k forms of P'; each form is N hex rows (row i bit j, i<=j, = coeff of x_i x_j)
// mode bit0: enumerate all solutions (prints up to maxsol); otherwise stop at first.
// mode bit1: tuple version (R = identity: Q_i o S = Q'_i for each i).
// stdout: "ISO"/"NOT"/"TIMEOUT", node count, solution count; each solution as N hex columns (S e_i).
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#define KMAX 10
#define NMAX 16
typedef uint32_t u32; typedef uint64_t u64;
static int N,K,MODE; static long MAXSOL; static u32 NV; static long NODECAP=2000000000L;
typedef struct { u32 *bv[KMAX]; uint16_t *ev; uint8_t *r; uint8_t *z; u64 *inv; } Sp;
static Sp A,B;
static u32 rowsA[KMAX][NMAX], rowsB[KMAX][NMAX];
static long nodes=0, nsol=0; static long timedout=0;

static int rank_masks(u32 *m, int cnt){ u32 t[KMAX]; memcpy(t,m,sizeof(u32)*cnt); int rk=0;
  for(int bit=N-1;bit>=0 && rk<cnt;bit--){ int p=-1; for(int i=rk;i<cnt;i++) if(t[i]>>bit&1){p=i;break;} if(p<0) continue;
    u32 x=t[p];t[p]=t[rk];t[rk]=x; for(int i=0;i<cnt;i++) if(i!=rk && (t[i]>>bit&1)) t[i]^=t[rk]; rk++; }
  return rk; }
static void build(Sp *S, u32 rows[KMAX][NMAX]){
  for(int j=0;j<K;j++) S->bv[j]=calloc(NV,sizeof(u32));
  S->ev=calloc(NV,sizeof(uint16_t)); S->r=calloc(NV,1); S->z=calloc(NV,1); S->inv=calloc(NV,sizeof(u64));
  u32 pol[KMAX][NMAX];
  for(int j=0;j<K;j++){ memset(pol[j],0,sizeof(pol[j]));
    for(int a=0;a<N;a++) for(int b=a+1;b<N;b++) if(rows[j][a]>>b&1){ pol[j][a]|=1u<<b; pol[j][b]|=1u<<a; } }
  for(u32 v=1;v<NV;v++){ int low=__builtin_ctz(v); u32 pv=v&(v-1);
    for(int j=0;j<K;j++) S->bv[j][v]=S->bv[j][pv]^pol[j][low];
    uint16_t e=S->ev[pv];
    for(int j=0;j<K;j++){ int qi=(rows[j][low]>>low)&1; int b=__builtin_parity(S->bv[j][pv]&(1u<<low)); if((qi^b)&1) e^=(1<<j); }
    S->ev[v]=e; }
  for(u32 v=0;v<NV;v++){ u32 m[KMAX]; for(int j=0;j<K;j++) m[j]=S->bv[j][v]; S->r[v]=rank_masks(m,K); S->z[v]=(S->ev[v]==0); }
}
static inline u64 mix(u64 x){ x^=x>>33; x*=0xff51afd7ed558ccdULL; x^=x>>33; x*=0xc4ceb9fe1a85ec53ULL; x^=x>>33; return x; }
static void strong_inv(Sp *S){
  for(u32 v=0;v<NV;v++){ u64 h=0; 
    for(u32 w=0;w<NV;w++){ int bz=1; for(int j=0;j<K;j++) if(__builtin_parity(S->bv[j][v]&w)){bz=0;break;}
      u64 t = (u64)S->r[w] | ((u64)S->z[w]<<8) | ((u64)S->r[v^w]<<16) | ((u64)S->z[v^w]<<24) | ((u64)bz<<32);
      h += mix(t+0x9e3779b97f4a7c15ULL); }
    S->inv[v]=mix(h ^ ((u64)S->r[v]<<40) ^ ((u64)S->z[v]<<50)); }
}
static int cmp64(const void*a,const void*b){ u64 x=*(u64*)a,y=*(u64*)b; return x<y?-1:x>y; }
static u64 *sortA; static u32 *ordA;
typedef struct { u64 k; u32 v; } KV;
static int cmpKV(const void*a,const void*b){ const KV*x=a,*y=b; return x->k<y->k?-1:x->k>y->k?1:0; }
static KV *clsA; static u32 basisB[NMAX];
static inline int beA(int j,u32 v,u32 w){ return __builtin_parity(A.bv[j][v]&w); }
static inline int beB(int j,u32 v,u32 w){ return __builtin_parity(B.bv[j][v]&w); }
static inline u32 BvecA(u32 v,u32 w){ u32 r=0; for(int j=0;j<K;j++) if(beA(j,v,w)) r|=1u<<j; return r; }
static inline u32 BvecB(u32 v,u32 w){ u32 r=0; for(int j=0;j<K;j++) if(beB(j,v,w)) r|=1u<<j; return r; }
typedef struct { uint16_t tp[KMAX], tq[KMAX], sp[KMAX]; } St;  // tgt pivots (by highbit), paired src, src pivots
static inline int hb(u32 x){ return 31-__builtin_clz(x); }
static int addpair(St *st, u32 tgt, u32 src){
  while(tgt){ int b=hb(tgt); if(!st->tp[b]) break; tgt^=st->tp[b]; src^=st->tq[b]; }
  if(!tgt) return src==0;
  u32 s=src; while(s){ int b=hb(s); if(!st->sp[b]) break; s^=st->sp[b]; }
  if(!s) return 0;
  st->sp[hb(s)]=s; st->tp[hb(tgt)]=tgt; st->tq[hb(tgt)]=src; return 1;
}
static u32 chosen[NMAX];
static u32 cols[NMAX];
static void report(void){
  // S e_{basis[i]} = chosen[i]: output S on standard basis via linear solve on basis.
  nsol++;
  if(nsol<=MAXSOL){ // express: images of standard basis
    // Gaussian on (basisB[i] -> chosen[i])
    u32 src[NMAX], dst[NMAX]; memcpy(src,basisB,sizeof(src)); memcpy(dst,chosen,sizeof(dst));
    for(int bit=0;bit<N;bit++){ int p=-1; for(int i=bit;i<N;i++) if(src[i]>>bit&1){p=i;break;}
      u32 t=src[p];src[p]=src[bit];src[bit]=t; t=dst[p];dst[p]=dst[bit];dst[bit]=t;
      for(int i=0;i<N;i++) if(i!=bit && (src[i]>>bit&1)){ src[i]^=src[bit]; dst[i]^=dst[bit]; } }
    printf("S"); for(int i=0;i<N;i++) printf(" %x",dst[i]); printf("\n"); }
}
static int dfs(int t, St *st, u32 *ech){ // ech[i]=pivot of chosen span
  nodes++; if(nodes>NODECAP){ timedout=1; return 1; }
  if(t==N){ report(); return !(MODE&1); }
  u32 b=basisB[t]; u64 key=B.inv[b]; 
  // binary search in clsA
  long lo=0,hi=(long)NV-1; while(lo<hi){ long mid=(lo+hi)/2; if(clsA[mid].k<key) lo=mid+1; else hi=mid; }
  for(long idx=lo; idx<(long)NV && clsA[idx].k==key; idx++){ u32 w=clsA[idx].v;
    // independence
    u32 x=w; for(int i=0;i<t;i++) if(ech[i] && (x>>hb(ech[i])&1)) x^=ech[i]; if(!x) continue;
    St s2=*st; int ok=addpair(&s2, A.ev[w], B.ev[b]); 
    for(int i=0;i<t && ok;i++) ok=addpair(&s2, BvecA(w,chosen[i]), BvecB(b,basisB[i]));
    if(!ok) continue;
    chosen[t]=w; ech[t]=x; 
    if(dfs(t+1,&s2,ech)) return 1;
  }
  return 0;
}
int main(int argc,char**argv){ if(argc>1) NODECAP=atol(argv[1]);
  if(scanf("%d %d %d %ld",&N,&K,&MODE,&MAXSOL)!=4) return 1; NV=1u<<N;
  if(K>KMAX||N>NMAX){ printf("BADINPUT\n"); return 1; }
  for(int j=0;j<K;j++) for(int i=0;i<N;i++) if(scanf("%x",&rowsA[j][i])!=1) return 1;
  for(int j=0;j<K;j++) for(int i=0;i<N;i++) if(scanf("%x",&rowsB[j][i])!=1) return 1;
  build(&A,rowsA); build(&B,rowsB);
  strong_inv(&A); strong_inv(&B);
  // quick invariant multiset comparison
  u64 *a=malloc(NV*sizeof(u64)),*b=malloc(NV*sizeof(u64)); memcpy(a,A.inv,NV*sizeof(u64)); memcpy(b,B.inv,NV*sizeof(u64));
  qsort(a,NV,sizeof(u64),cmp64); qsort(b,NV,sizeof(u64),cmp64); 
  int same=memcmp(a,b,NV*sizeof(u64))==0; free(a); free(b);
  if(!same){ printf("NOT 0 0\n"); return 0; }
  clsA=malloc(NV*sizeof(KV)); for(u32 v=0;v<NV;v++){ clsA[v].k=A.inv[v]; clsA[v].v=v; } qsort(clsA,NV,sizeof(KV),cmpKV);
  // class sizes on B side, choose basis rarest-first
  KV *clsB=malloc(NV*sizeof(KV)); for(u32 v=0;v<NV;v++){ clsB[v].k=B.inv[v]; clsB[v].v=v; } qsort(clsB,NV,sizeof(KV),cmpKV);
  long *cs=malloc(NV*sizeof(long)); for(long i=0;i<(long)NV;){ long j=i; while(j<(long)NV&&clsB[j].k==clsB[i].k) j++; for(long t=i;t<j;t++) cs[t]=j-i; i=j; }
  // order vectors by class size then pick independent
  long *ord=malloc(NV*sizeof(long)); for(long i=0;i<(long)NV;i++) ord[i]=i;
  // simple selection: repeatedly pick smallest class vector independent of chosen
  u32 ech[NMAX]; memset(ech,0,sizeof(ech)); int got=0; 
  // sort indices by cs
  for(long i=1;i<(long)NV;i++){ /* insertion sort by bucket */ }
  // bucket by size
  long maxc=0; for(long i=0;i<(long)NV;i++) if(cs[i]>maxc) maxc=cs[i];
  for(long sz=1; sz<=maxc && got<N; sz++){ for(long i=0;i<(long)NV && got<N;i++) if(cs[i]==sz){ u32 v=clsB[i].v; if(v==0) continue; u32 x=v; for(int t=0;t<got;t++) if(x>>hb(ech[t])&1) x^=ech[t]; if(x){ ech[got]=x; basisB[got]=v; got++; } } }
  if(got<N){ printf("BADBASIS\n"); return 1; }
  St st; memset(&st,0,sizeof(st)); u32 e2[NMAX]; memset(e2,0,sizeof(e2));
  if(MODE&2) for(int j=0;j<K;j++) if(!addpair(&st,1u<<j,1u<<j)){ printf("BADSEED\n"); return 1; }
  int stop=dfs(0,&st,e2);
  if(timedout){ printf("TIMEOUT %ld %ld\n",nodes,nsol); return 0; }
  printf("%s %ld %ld\n", nsol>0?"ISO":"NOT", nodes, nsol);
  (void)stop; return 0;
}
