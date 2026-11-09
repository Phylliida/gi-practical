/* ir_affine.c -- individualization-refinement search on functions f:F_2^k -> colors
   under AGL(k,2).  Refinement = point/direction 1-WL ("PDR"), optionally with a
   dual (Walsh) sort.  Reports first-path depth, target-cell sizes, full search-tree
   size (with node-invariant pruning), and |Aut(f)| read off from equal leaves.
   Build: gcc -O2 -o ir_affine ir_affine.c    Usage: ir_affine k family seed [dual] */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

typedef uint64_t u64; typedef uint32_t u32;
static int k, N, use_dual;
static inline u64 mix(u64 x){ x+=0x9e3779b97f4a7c15ULL; x=(x^(x>>30))*0xbf58476d1ce4e5b9ULL;
  x=(x^(x>>27))*0x94d049bb133111ebULL; return x^(x>>31); }
static inline u64 mix2(u64 a,u64 b){ return mix(a*0x517cc1b727220a95ULL ^ mix(b)); }
static inline int par(u32 x){ return __builtin_popcount(x)&1; }

static u64 rng_s;
static u64 rnd(){ rng_s+=0x9e3779b97f4a7c15ULL; return mix(rng_s); }

typedef struct { u32 *c; int ncol; } Col;
static int cmp64(const void*a,const void*b){u64 x=*(u64*)a,y=*(u64*)b;return x<y?-1:x>y;}

/* one refinement round; returns new number of colours, writes c */
static u64 *sD,*sA,*sN; static u32 *tmp;
static int refine_round(u32 *c){
  memset(sD,0,N*sizeof(u64));
  for(int d=0;d<N;d++){ u64 s=0; for(int x=0;x<N;x++) s+=mix2(c[x],c[x^d]); sD[d]=s; }
  if(use_dual){
    for(int a=0;a<N;a++){ u64 s=0; for(int d=0;d<N;d++) s+=mix2(sD[d], (u64)par(a&d)); sA[a]=s; }
    /* feed back: direction colour includes multiset of (dual colour, a.d) */
    for(int d=0;d<N;d++){ u64 s=0; for(int a=0;a<N;a++) s+=mix2(sA[a],(u64)par(a&d)); sD[d]=mix2(sD[d],s); }
  }
  for(int x=0;x<N;x++){ u64 s=0; for(int d=0;d<N;d++) s+=mix2(sD[d],c[x^d]); sN[x]=mix2(c[x],s); }
  /* canonicalise hashes to ints via sort */
  static u64 *srt; if(!srt) srt=malloc(N*sizeof(u64));
  memcpy(srt,sN,N*sizeof(u64)); qsort(srt,N,sizeof(u64),cmp64);
  int m=0; for(int i=0;i<N;i++) if(i==0||srt[i]!=srt[i-1]) srt[m++]=srt[i];
  for(int x=0;x<N;x++){ int lo=0,hi=m-1; while(lo<hi){int mid=(lo+hi)/2; if(srt[mid]<sN[x])lo=mid+1;else hi=mid;} c[x]=lo; }
  return m;
}
static int refine(u32 *c,int ncol){ for(;;){ int m=refine_round(c); if(m==ncol) return m; ncol=m; if(m==N) return m; } }

/* node invariant: hash of multiset of colour-class sizes in sorted colour order */
static u64 inv_of(const u32 *c,int ncol){ static int *cnt; if(!cnt) cnt=malloc((N+1)*sizeof(int));
  memset(cnt,0,(ncol+1)*sizeof(int)); for(int x=0;x<N;x++) cnt[c[x]]++;
  u64 h=mix(ncol); for(int i=0;i<ncol;i++) h=mix2(h,(u64)cnt[i]); return h; }

/* choose target cell: smallest non-singleton (first in colour order); returns colour or -1 */
static int target(const u32 *c,int ncol,int *size){ static int *cnt; if(!cnt) cnt=malloc((N+1)*sizeof(int));
  memset(cnt,0,(ncol+1)*sizeof(int)); for(int x=0;x<N;x++) cnt[c[x]]++;
  int best=-1,bs=N+1; for(int i=0;i<ncol;i++) if(cnt[i]>1 && cnt[i]<bs){bs=cnt[i];best=i;}
  *size=bs; return best; }

/* function f (colour values) */
static u32 *F;
/* first-path trace */
#define MAXD 64
static u64 trace_inv[MAXD]; static int trace_size[MAXD]; static int trace_depth=-1;
static u32 *leaf_first; /* leaf labelling: position of each point in first leaf */
static u32 *firstf;
static u64 L_total, L_match, N_nodes, node_limit; static int leaf_recorded=0, overflow=0;

static void leaf_action(u32 *c){
  /* c discrete: rank = c[x] is position; build string */
  static u32 *str; if(!str) str=malloc(N*sizeof(u32));
  for(int x=0;x<N;x++) str[c[x]]=F[x];
  if(!leaf_recorded){ memcpy(firstf,str,N*sizeof(u32)); leaf_recorded=1; L_total=1; L_match=1; return; }
  L_total++; if(!memcmp(firstf,str,N*sizeof(u32))) L_match++;
}
static void search(u32 *c,int ncol,int depth,int first){
  if(node_limit && N_nodes>=node_limit){overflow=1;return;}
  N_nodes++;
  if(ncol==N){ if(first) trace_depth=depth; leaf_action(c); return; }
  int size; int t=target(c,ncol,&size);
  if(first){ trace_size[depth]=size; trace_inv[depth]=inv_of(c,ncol); }
  u32 *cc=malloc(N*sizeof(u32));
  int isfirst=first;
  for(int x=0;x<N;x++) if(c[x]==(u32)t){
    /* individualize x: give it colour ncol (new unique), refine */
    memcpy(cc,c,N*sizeof(u32)); cc[x]=ncol; int m=refine(cc,ncol+1);
    u64 inv=inv_of(cc,m);
    if(isfirst){ trace_inv[depth+1]=inv; }
    if(!isfirst && depth+1<=trace_depth && inv!=trace_inv[depth+1]) { continue; } /* prune by invariant vs first path */
    if(!isfirst && depth+1>trace_depth) continue;
    search(cc,m,depth+1,isfirst);
    isfirst=0;
    if(overflow) break;
  }
  free(cc);
}

/* GF(2^k) arithmetic with primitive polynomial, for k<=10 */
static int primpoly[]={0,3,7,11,19,37,67,131,285,529,1033};
static u32 gfmul(u32 a,u32 b){ u32 r=0; while(b){ if(b&1) r^=a; a<<=1; if(a>>k) a^=primpoly[k]; b>>=1; } return r; }
static u32 gfpow(u32 a,u32 e){ u32 r=1; while(e){ if(e&1) r=gfmul(r,a); a=gfmul(a,a); e>>=1; } return r; }
static int gftrace(u32 a){ u32 t=0,x=a; for(int i=0;i<k;i++){ t^=x; x=gfmul(x,x);} return t&1; }

static void build(const char *fam,int seed){
  rng_s=seed*0x12345ULL+77;
  int m=k/2; int xbits=(1<<m)-1;
  if(!strcmp(fam,"rand")){ for(int x=0;x<N;x++) F[x]=rnd()&1; }
  else if(!strcmp(fam,"balanced")){ for(int x=0;x<N;x++) F[x]=x<N/2; for(int i=N-1;i>0;i--){ int j=rnd()%(i+1); u32 t=F[i];F[i]=F[j];F[j]=t; } }
  else if(!strcmp(fam,"ip")){ /* quadratic bent: inner product x.y, k even */
    for(int x=0;x<N;x++){ int a=x&xbits,b=x>>m; F[x]=par(a&b);} }
  else if(!strcmp(fam,"mm")){ /* Maiorana-McFarland: x.pi(y)+h(y), pi random perm */
    int M=1<<m; int *pi=malloc(M*sizeof(int)); for(int i=0;i<M;i++)pi[i]=i; for(int i=M-1;i>0;i--){int j=rnd()%(i+1);int t=pi[i];pi[i]=pi[j];pi[j]=t;}
    u32 *h=malloc(M*sizeof(u32)); for(int i=0;i<M;i++)h[i]=rnd()&1;
    for(int z=0;z<N;z++){ int x=z&xbits,y=z>>m; F[z]=par(x&pi[y])^h[y]; } free(pi);free(h); }
  else if(!strcmp(fam,"mmpow")){ /* MM with pi = y^3-like via GF(2^m) cubing (when gcd allows) and h=0 */
    int sk=k; k=m; for(int z=0;z<(1<<sk);z++){ int x=z&xbits,y=z>>m; u32 p=gfpow(y,3)%(1<<m); F[z]=par(x&p);} k=sk; }
  else if(!strcmp(fam,"cubic")){ /* random homogeneous cubic */
    for(int x=0;x<N;x++) F[x]=0;
    for(int a=0;a<k;a++) for(int b=a+1;b<k;b++) for(int c=b+1;c<k;c++) if(rnd()&1){ for(int x=0;x<N;x++) if((x>>a&1)&&(x>>b&1)&&(x>>c&1)) F[x]^=1; } }
  else if(!strcmp(fam,"cubicsum")){ /* direct sum of x1x2x3 + x4x5x6 + ... */
    for(int x=0;x<N;x++){ int v=0; for(int i=0;i+2<k;i+=3) v^=((x>>i&1)&(x>>(i+1)&1)&(x>>(i+2)&1)); F[x]=v; } }
  else if(!strcmp(fam,"gold")){ /* Tr(x^3) on GF(2^k) */
    for(int x=0;x<N;x++) F[x]=gftrace(gfpow(x,3)); }
  else if(!strcmp(fam,"tr7")){ for(int x=0;x<N;x++) F[x]=gftrace(gfpow(x,7)); }
  else if(!strcmp(fam,"tr11")){ for(int x=0;x<N;x++) F[x]=gftrace(gfpow(x,11)); }
  else if(!strcmp(fam,"inv")){ /* Tr(x^-1) = Kloosterman function, high degree k-1 */
    for(int x=0;x<N;x++) F[x]=x?gftrace(gfpow(x,N-2)):0; }
  else if(!strcmp(fam,"pap")){ /* PS_ap bent on F_{2^m}^2, f(x,y)=g(x/y), g balanced trace */
    int sk=k; k=m; int M=1<<m;
    for(int z=0;z<(1<<sk);z++){ int x=z&xbits,y=z>>m; if(y==0){F[z]=0;continue;} u32 r=gfmul(x,gfpow(y,M-2)); F[z]=gftrace(r); }
    k=sk; }
  else if(!strcmp(fam,"cyclo")){ /* cyclotomic: f random on cosets of subgroup of index r=seed%5+3 in F^* */
    int r=3+(seed%5); u32 g=2; /* primitive? use logarithm by primitive poly generator */
    int *lg=calloc(N,sizeof(int)); u32 p=1; for(int i=0;i<N-1;i++){ lg[p]=i; p=gfmul(p,g); }
    u32 *cv=malloc(r*sizeof(u32)); for(int i=0;i<r;i++) cv[i]=rnd()&1;
    F[0]=rnd()&1; for(int x=1;x<N;x++) F[x]=cv[lg[x]%r]; free(lg); free(cv); }
  else if(!strcmp(fam,"subspace")){ /* union of a few random subspaces: indicator */
    for(int x=0;x<N;x++) F[x]=0;
    for(int t=0;t<3;t++){ u32 b[8]; int d=2+rnd()%(k/2+1); for(int i=0;i<d;i++) b[i]=rnd()%N; for(int mask=0;mask<(1<<d);mask++){ u32 v=0; for(int i=0;i<d;i++) if(mask>>i&1) v^=b[i]; F[v]^=1; } } }
  else if(!strcmp(fam,"tensor4")){ /* 4-tensor gadget (Section on hardness): k=8, 2x2x2x2 random tensor, blocks coloured */
    u32 T[16]; for(int i=0;i<16;i++)T[i]=rnd()&1;
    for(int z=0;z<N;z++){ int a=z&3,b=z>>2&3,c=z>>4&3,d=z>>6&3; int nz=(a!=0)+(b!=0)+(c!=0)+(d!=0);
      if(nz==4){ F[z]=T[(a-1)&1 | ((b-1)&1)<<1 | ((c-1)&1)<<2 | ((d-1)&1)<<3] ; }
      else { F[z]=2+ (a!=0)+2*(b!=0)+4*(c!=0)+8*(d!=0); }
      /* note: a value in 1..3 of each 2-bit block is a nonzero vector of F_2^2 */ if(nz==4){ /* use full multilinear evaluation */ int v=0; for(int i=0;i<16;i++) if(T[i]){ v^= ((a>>(i&1))&1)&((b>>((i>>1)&1))&1)&((c>>((i>>2)&1))&1)&((d>>((i>>3)&1))&1); } F[z]=v; } }
    F[0]=20; }
  else { fprintf(stderr,"unknown family %s\n",fam); exit(1); }
}

/* Knuth tree-size estimation by random probes, pruning by first-path invariants */
static double probe_leaves, probe_auts;
static void probe(u32 *root,int rootcol){
  u32 *c=malloc(N*sizeof(u32)); memcpy(c,root,N*sizeof(u32)); int ncol=rootcol, depth=0;
  double weight=1;
  u32 *cc=malloc(N*sizeof(u32));
  int *cand=malloc(N*sizeof(int));
  u32 *best=malloc(N*sizeof(u32));
  int leafok=0;
  while(ncol<N && depth<trace_depth){
    int size; int t=target(c,ncol,&size);
    if(size!=trace_size[depth]){ weight=0; break; }
    int nsurv=0, chosen=-1; int bestm=0;
    /* reservoir sample among survivors */
    for(int x=0;x<N;x++) if(c[x]==(u32)t){
      memcpy(cc,c,N*sizeof(u32)); cc[x]=ncol; int m=refine(cc,ncol+1);
      if(inv_of(cc,m)==trace_inv[depth+1]){
        nsurv++;
        if(rnd()%nsurv==0){ chosen=x; memcpy(best,cc,N*sizeof(u32)); bestm=m; }
      }
    }
    if(!nsurv){ weight=0; break; }
    weight*=nsurv; memcpy(c,best,N*sizeof(u32)); ncol=bestm; depth++;
  }
  if(weight>0 && ncol==N){
    static u32 *str; if(!str) str=malloc(N*sizeof(u32));
    for(int x=0;x<N;x++) str[c[x]]=F[x];
    probe_leaves+=weight;
    if(!memcmp(firstf,str,N*sizeof(u32))) probe_auts+=weight;
  }
  free(c);free(cc);free(cand);free(best);
}

/* evaluate current F: returns log2(leaves/auts) of tree (0 if rigid), depth in *dep, nodes in *nn */
static double evaluate_F(int *dep, int *ncol0, u64 *nn){
  static u32 *c; if(!c) c=malloc(N*sizeof(u32)); memcpy(c,F,N*sizeof(u32));
  { u32 s[2]={0,0}; (void)s; for(int x=0;x<N;x++) c[x]=c[x]&1; int m=2; int nc=refine(c,m);
    trace_depth=-1; leaf_recorded=0; overflow=0; L_total=0; L_match=0; N_nodes=0; trace_inv[0]=inv_of(c,nc);
    search(c,nc,0,1); *dep=trace_depth; *ncol0=nc; *nn=N_nodes;
    if(overflow||L_match==0) return -1; return __builtin_log2((double)L_total/(double)L_match); }
}
static void climb(int seed,long iters,double startp){
  rng_s=seed*7777ULL+3; double best=-1; int bdep=0,bcol=0; u64 bnn=0;
  for(int x=0;x<N;x++) F[x]=(rnd()%1000)<startp*1000;
  double cur; int d,c0; u64 nn; cur=evaluate_F(&d,&c0,&nn);
  for(long it=0;it<iters;it++){
    int x=rnd()%N; F[x]^=1; int d2,c2; u64 nn2; double e=evaluate_F(&d2,&c2,&nn2);
    if(e>=0 && e>=cur){ if(e>cur||d2>=d) {cur=e;d=d2;c0=c2;nn=nn2;} }
    else F[x]^=1;
    if(cur>best){best=cur;bdep=d;bcol=c0;bnn=nn; printf("it=%ld excess(log2)=%.2f depth=%d ncol0=%d nodes=%llu\n",it,cur,d,c0,(unsigned long long)nn); fflush(stdout);}
  }
  printf("FINAL excess(log2)=%.2f depth=%d ncol0=%d nodes=%llu; truth: ",best,bdep,bcol,(unsigned long long)bnn); for(int x=0;x<N;x++) putchar('0'+F[x]); printf("\n");
}

int main(int argc,char**argv){
  if(argc>1 && !strcmp(argv[1],"climb")){ k=atoi(argv[2]); N=1<<k; int seed=atoi(argv[3]); long iters=atol(argv[4]); use_dual=argc>5?atoi(argv[5]):0; node_limit=atol(argc>6?argv[6]:"20000");
    F=malloc(N*sizeof(u32)); sD=malloc(N*sizeof(u64)); sA=malloc(N*sizeof(u64)); sN=malloc(N*sizeof(u64)); firstf=malloc(N*sizeof(u32));
    climb(seed,iters,argc>7?atof(argv[7]):0.5); return 0; }
  if(argc<4){ fprintf(stderr,"usage: %s k family seed [dual] [nodelimit]\n",argv[0]); return 2; }
  k=atoi(argv[1]); N=1<<k; const char *fam=argv[2]; int seed=atoi(argv[3]);
  use_dual = argc>4 ? atoi(argv[4]) : 0; node_limit = argc>5 ? atoll(argv[5]) : 2000000;
  F=malloc(N*sizeof(u32)); sD=malloc(N*sizeof(u64)); sA=malloc(N*sizeof(u64)); sN=malloc(N*sizeof(u64)); firstf=malloc(N*sizeof(u32));
  build(fam,seed);
  u32 *c=malloc(N*sizeof(u32)); memcpy(c,F,N*sizeof(u32));
  /* initial normalisation */
  int maxc=0; for(int x=0;x<N;x++) if((int)c[x]>maxc) maxc=c[x];
  { /* compress colours by sort */
    u32 *s=malloc(N*sizeof(u32)); memcpy(s,c,N*sizeof(u32));
    for(int i=0;i<N;i++) for(int j=i+1;j<N;j++) if(s[j]<s[i]){u32 t=s[i];s[i]=s[j];s[j]=t;}
    int m=0; for(int i=0;i<N;i++) if(i==0||s[i]!=s[i-1]) s[m++]=s[i];
    for(int x=0;x<N;x++){ int j=0; while(s[j]!=c[x])j++; c[x]=j; }
    maxc=m; free(s);
  }
  int nc=refine(c,maxc);
  trace_inv[0]=inv_of(c,nc);
  L_total=0;L_match=0;N_nodes=0;
  long probes = argc>6 ? atol(argv[6]) : 0;
  search(c,nc,0,1);
  if(probes>0){ probe_leaves=0;probe_auts=0; for(long i=0;i<probes;i++) probe(c,nc); probe_leaves/=probes; probe_auts/=probes; }
  double logprod=0; printf("%-9s k=%-2d seed=%-3d dual=%d: ncol0=%-5d depth=%-2d cells=[",fam,k,seed,use_dual,nc,trace_depth);
  for(int i=0;i<trace_depth;i++){ printf("%d%s",trace_size[i],i+1<trace_depth?",":""); logprod+=__builtin_log2(trace_size[i]); }
  printf("] log2prod=%.1f tree_nodes=%llu leaves=%llu auts=%llu overflow=%d",logprod,(unsigned long long)N_nodes,(unsigned long long)L_total,(unsigned long long)L_match,overflow);
  if(probes>0) printf(" probe_leaves=%.1f probe_auts=%.1f excess=%.2f",probe_leaves,probe_auts,probe_auts>0?probe_leaves/probe_auts:0.0);
  printf("\n");
  return 0;
}
