// wl.c: 1-WL (point/block incidence) and 2-WL (pairs of the Steiner quasigroup) with greedy
// individualization on an STS. Input: binary file: int32 n, then n*n int32 Q[x][y]=third point (Q[x][x]=x).
// Output: lines "1wl depth d trace ..." and "2wl depth d trace ...".
// Hashing is 64-bit (no canonical renaming): a hash collision could only merge classes, i.e. understate
// refinement. Run under `nice`. One process.
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

typedef uint64_t u64;
static inline u64 mix(u64 a, u64 b){ u64 x=a*0x9E3779B97F4A7C15ULL + b; x^=x>>29; x*=0xBF58476D1CE4E5B9ULL; x^=x>>32; x+=b*0x94D049BB133111EBULL; x^=x>>29; return x; }
static inline u64 h1(u64 v){ v^=v>>33; v*=0xff51afd7ed558ccdULL; v^=v>>33; v*=0xc4ceb9fe1a85ec53ULL; v^=v>>33; return v; }

static int n; static int *Q;
#define QQ(x,y) Q[(x)*n+(y)]

static int cmp_u64(const void*a,const void*b){ u64 x=*(const u64*)a,y=*(const u64*)b; return (x>y)-(x<y); }
static int count_classes(u64 *v,int m,u64 *scratch){ memcpy(scratch,v,m*sizeof(u64)); qsort(scratch,m,sizeof(u64),cmp_u64); int c=0; for(int i=0;i<m;i++) if(i==0||scratch[i]!=scratch[i-1]) c++; return c; }

// ---- 1-WL on incidence ----
static int *blocks; static int nb;
static void build_blocks(void){ blocks=malloc(sizeof(int)*n*n); nb=0; for(int x=0;x<n;x++) for(int y=x+1;y<n;y++){ int z=QQ(x,y); if(z>y){ blocks[nb*3]=x; blocks[nb*3+1]=y; blocks[nb*3+2]=z; nb++; } } }
static int *pt_blocks; // pt_blocks[x][r] block index, r=(n-1)/2
static void build_index(void){ int r=(n-1)/2; pt_blocks=malloc(sizeof(int)*n*r); int *cnt=calloc(n,sizeof(int)); for(int b=0;b<nb;b++) for(int j=0;j<3;j++){ int x=blocks[b*3+j]; pt_blocks[x*r+cnt[x]++]=b; } free(cnt); }

static void refine1(u64 *pc, u64 *scratch){
  int r=(n-1)/2; u64 *bc=malloc(sizeof(u64)*nb); u64 *np=malloc(sizeof(u64)*n);
  int last=count_classes(pc,n,scratch);
  for(int iter=0;iter<n+5;iter++){
    for(int b=0;b<nb;b++){ u64 a=pc[blocks[b*3]],bb=pc[blocks[b*3+1]],c=pc[blocks[b*3+2]]; u64 s=h1(a)+h1(bb)+h1(c); bc[b]=mix(s,h1(a)^h1(bb)^h1(c)); }
    for(int x=0;x<n;x++){ u64 s=0; for(int j=0;j<r;j++) s+=h1(bc[pt_blocks[x*r+j]]); np[x]=mix(pc[x],s); }
    memcpy(pc,np,sizeof(u64)*n);
    int c=count_classes(pc,n,scratch);
    if(c==last) break; last=c;
  }
  free(bc); free(np);
}
static int run1(int *trace){
  u64 *pc=malloc(sizeof(u64)*n); u64 *sc=malloc(sizeof(u64)*n);
  for(int x=0;x<n;x++) pc[x]=1;
  refine1(pc,sc);
  int depth=0; int t=0;
  while(1){
    int c=count_classes(pc,n,sc); trace[t++]=c;
    if(c==n) break;
    // choose smallest non-singleton class
    memcpy(sc,pc,sizeof(u64)*n); qsort(sc,n,sizeof(u64),cmp_u64);
    u64 best=0; int bestsz=n+1; for(int i=0;i<n;){ int j=i; while(j<n&&sc[j]==sc[i]) j++; if(j-i>1&&j-i<bestsz){ bestsz=j-i; best=sc[i]; } i=j; }
    int v=-1; for(int x=0;x<n;x++) if(pc[x]==best){ v=x; break; }
    pc[v]=mix(pc[v],0xABCDEF0123ULL+depth);
    refine1(pc,sc); depth++;
    if(depth>64) break;
  }
  free(pc); free(sc); return depth;
}

// ---- 2-WL on the Steiner quasigroup ----
static u64 *C,*C2,*scr;
static void refine2(void){
  int N=n*n;
  int last=count_classes(C,N,scr);
  for(int iter=0;iter<2*n;iter++){
    for(int x=0;x<n;x++){
      for(int y=0;y<n;y++){
        int xy=QQ(x,y);
        u64 s=0;
        for(int z=0;z<n;z++){ s+=h1(mix(C[x*n+z],C[z*n+y])); }
        u64 h=mix(C[x*n+y],s);
        h=mix(h,C[x*n+xy]); h=mix(h,C[xy*n+y]);
        C2[x*n+y]=h;
      }
    }
    u64 *t=C; C=C2; C2=t;
    int c=count_classes(C,N,scr);
    if(c==last) break; last=c;
  }
}
static int point_classes2(u64 *buf){ for(int x=0;x<n;x++) buf[x]=C[x*n+x]; memcpy(scr,buf,sizeof(u64)*n); qsort(scr,n,sizeof(u64),cmp_u64); int c=0; for(int i=0;i<n;i++) if(i==0||scr[i]!=scr[i-1]) c++; return c; }
static int run2(int *trace){
  int N=n*n; C=malloc(sizeof(u64)*N); C2=malloc(sizeof(u64)*N); scr=malloc(sizeof(u64)*N);
  for(int x=0;x<n;x++) for(int y=0;y<n;y++) C[x*n+y]=(x==y)?2:3;
  refine2();
  u64 *pc=malloc(sizeof(u64)*n);
  int depth=0,t=0;
  while(1){
    int c=point_classes2(pc); trace[t++]=c;
    if(c==n) break;
    u64 *sc=malloc(sizeof(u64)*n); memcpy(sc,pc,sizeof(u64)*n); qsort(sc,n,sizeof(u64),cmp_u64);
    u64 best=0; int bestsz=n+1; for(int i=0;i<n;){ int j=i; while(j<n&&sc[j]==sc[i]) j++; if(j-i>1&&j-i<bestsz){ bestsz=j-i; best=sc[i]; } i=j; }
    free(sc);
    int v=-1; for(int x=0;x<n;x++) if(pc[x]==best){ v=x; break; }
    C[v*n+v]=mix(C[v*n+v],0xFEEDFACEULL+depth);
    refine2(); depth++;
    if(depth>64) break;
  }
  free(C); free(C2); free(scr); free(pc); return depth;
}

// Isomorphism-invariant signatures: H0 = hash of the multiset of 2-WL pair colours; H1 = hash of the multiset,
// over points v, of the 2-WL pair colour multiset hash with v individualized.
static u64 multiset_hash(u64 *v,int m){ u64 s=0; for(int i=0;i<m;i++) s+=h1(v[i]); return mix(s,(u64)m); }
static void signatures(u64 *H0,u64 *H1){
  int N=n*n; C=malloc(sizeof(u64)*N); C2=malloc(sizeof(u64)*N); scr=malloc(sizeof(u64)*N);
  u64 *base=malloc(sizeof(u64)*N);
  for(int x=0;x<n;x++) for(int y=0;y<n;y++) C[x*n+y]=(x==y)?2:3;
  refine2();
  memcpy(base,C,sizeof(u64)*N);
  *H0=multiset_hash(C,N);
  u64 acc=0;
  for(int v=0;v<n;v++){
    memcpy(C,base,sizeof(u64)*N);
    C[v*n+v]=mix(C[v*n+v],0xFEEDFACEULL);
    refine2();
    acc+=h1(multiset_hash(C,N));
  }
  *H1=mix(acc,(u64)n);
  free(C); free(C2); free(scr); free(base);
}

// H2: multiset over ordered pairs (v,w), v!=w, of the 2-WL colouring hash with v and w individualized
// (with distinct individualization tags, so the ordered pair is seen). n^2 refinements: small n only.
static u64 signature2(void){
  int N=n*n; C=malloc(sizeof(u64)*N); C2=malloc(sizeof(u64)*N); scr=malloc(sizeof(u64)*N);
  u64 *base=malloc(sizeof(u64)*N);
  for(int x=0;x<n;x++) for(int y=0;y<n;y++) C[x*n+y]=(x==y)?2:3;
  refine2();
  memcpy(base,C,sizeof(u64)*N);
  u64 acc=0;
  for(int v=0;v<n;v++) for(int w=0;w<n;w++){
    if(v==w) continue;
    memcpy(C,base,sizeof(u64)*N);
    C[v*n+v]=mix(C[v*n+v],0xFEEDFACEULL);
    C[w*n+w]=mix(C[w*n+w],0xBEEFCAFEULL);
    refine2();
    acc+=h1(multiset_hash(C,N));
  }
  free(C); free(C2); free(scr); free(base);
  return mix(acc,(u64)n);
}

int main(int argc,char**argv){
  if(argc<2){ fprintf(stderr,"usage: wl file [which=3]\n"); return 1; }
  int which=argc>2?atoi(argv[2]):3;
  FILE *f=fopen(argv[1],"rb"); if(!f) return 2; int nn; if(fread(&nn,4,1,f)!=1) return 3; n=nn; Q=malloc(sizeof(int)*n*n); if(fread(Q,4,n*n,f)!=(size_t)n*n) return 4; fclose(f);
  build_blocks(); build_index();
  int tr[80];
  if(which&4){ u64 H0,H1; signatures(&H0,&H1); u64 H2=0; if(which&8) H2=signature2(); printf("sig %016llx %016llx %016llx\n",(unsigned long long)H0,(unsigned long long)H1,(unsigned long long)H2); }
  if(which&1){ int d=run1(tr); printf("1wl depth %d trace",d); for(int i=0;i<=d&&i<80;i++) printf(" %d",tr[i]); printf("\n"); }
  if(which&2){ int d=run2(tr); printf("2wl depth %d trace",d); for(int i=0;i<=d&&i<80;i++) printf(" %d",tr[i]); printf("\n"); }
  return 0;
}
