/* tiso.c -- exact isomorphism test for 3-tensors over F_2, slice-rank backtracking.
   Input (stdin, repeated): "nX nY nZ" then for two tensors S, S': nZ slices, each nX hex rows.
   Slice convention S(x,y,z)=x^T M(z) y, M(z)=sum z_k M_k.
   Decides whether (Px,Py,Pz) in GL x GL x GL exist with S'(x,y,z)=S(Px x,Py y,Pz z).

   Method (exhaustive up to the invariant checks below, each necessary for isomorphism):
   rank_S(Pz z)=rank_S'(z) for every z in F_2^nZ, enumerated over all of Z. Backtrack over a basis of Z chosen
   by S' low-rank-first, verifying the rank equality on the full span so far.  Each complete Pz is
   then tested exactly: W M'_k = M_{Pz b_k} Q is a linear system in (W,Q) and we enumerate its
   solution space for an invertible pair.  OVERFLOW is reported rather than guessed.
   Output per instance: ISO/NONISO/OVERFLOW leaves nodes dsolmax. Uses gcc -O2. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
typedef uint64_t u64;
#define MAXN 64
#define MAXZ 26
static int nX,nY,nZ;
static u64 A[2][MAXZ][MAXN];
static uint8_t *rk[2];
static int rank_of(u64 *m,int n){ int r=0; for(int b=0;b<nY;b++){ int p=-1; for(int i=r;i<n;i++) if(m[i]>>b&1){p=i;break;} if(p<0) continue; u64 t=m[p];m[p]=m[r];m[r]=t; for(int i=0;i<n;i++) if(i!=r&&(m[i]>>b&1)) m[i]^=m[r]; r++; if(r==n)break;} return r; }
static void rank_table(int s){ u64 cur[MAXN]; memset(cur,0,sizeof cur); uint32_t g=0; uint32_t N=1u<<nZ; rk[s]=malloc(N); rk[s][0]=0;
  for(uint32_t i=1;i<N;i++){ int b=__builtin_ctz(i); g^=1u<<b; for(int r=0;r<nX;r++) cur[r]^=A[s][b][r]; u64 c2[MAXN]; memcpy(c2,cur,sizeof(u64)*nX); rk[s][g]=rank_of(c2,nX); } }
static int cmp_u(const void*a,const void*b){ uint32_t x=*(uint32_t*)a,y=*(uint32_t*)b; return (x>y)-(x<y);}
static uint32_t *cand[MAXN+2]; static int ncand[MAXN+2];
static uint32_t bp[MAXZ], img[MAXZ];
static uint32_t *spanS, *spanP; /* combos of first k basis vectors, index = subset bitmask */
static long long leaves, nodes, leaf_limit=2000000;
static int dsolmax, overflow, found;
static u64 Mk[MAXZ][MAXN]; /* slices of S at img[k] */
static u64 Mpk[MAXZ][MAXN]; /* slices of S' at bp[k] */
static int invertible(u64 *m,int n){ u64 c[MAXN]; memcpy(c,m,sizeof(u64)*n); int save=nY; nY=n; int r=rank_of(c,n); nY=save; return r==n; }
static void slice_at(int s,uint32_t z,u64 *out){ memset(out,0,sizeof(u64)*nX); for(int k=0;k<nZ;k++) if(z>>k&1) for(int r=0;r<nX;r++) out[r]^=A[s][k][r]; }
/* linear solve */
static int Nu, nW, wd;
static u64 **piv; static int *pivc; static int npiv;
static u64 *eq; static u64 *nv[32]; static char *isp; static int ndim;
static void add_eq(u64 *r){ for(int i=0;i<npiv;i++){ int c=pivc[i]; if(r[c>>6]>>(c&63)&1) for(int w=0;w<wd;w++) r[w]^=piv[i][w]; }
  int c=-1; for(int w=0;w<wd&&c<0;w++) if(r[w]) c=w*64+__builtin_ctzll(r[w]); if(c<0) return;
  for(int i=0;i<npiv;i++) if(piv[i][c>>6]>>(c&63)&1) for(int w=0;w<wd;w++) piv[i][w]^=r[w];
  memcpy(piv[npiv],r,sizeof(u64)*wd); pivc[npiv]=c; npiv++; }
static int leaf_solve(void){ /* returns 1 if invertible solution found */
  for(int k=0;k<nZ;k++){ slice_at(0,img[k],Mk[k]); slice_at(1,bp[k],Mpk[k]); }
  npiv=0;
  for(int k=0;k<nZ;k++) for(int r=0;r<nX;r++) for(int c=0;c<nY;c++){
    memset(eq,0,sizeof(u64)*wd);
    for(int s=0;s<nX;s++) if(Mpk[k][s]>>c&1){ int v=r*nX+s; eq[v>>6]^=1ULL<<(v&63); }
    for(int t=0;t<nY;t++) if(Mk[k][r]>>t&1){ int v=nW+t*nY+c; eq[v>>6]^=1ULL<<(v&63); }
    add_eq(eq);
  }
  /* nullspace */
  memset(isp,0,Nu); for(int i=0;i<npiv;i++) isp[pivc[i]]=1;
  ndim=0;
  int freevars[Nu];
  for(int v=0;v<Nu;v++) if(!isp[v]) freevars[ndim++]=v;
  if(ndim>dsolmax) dsolmax=ndim;
  if(ndim>20){ overflow=1; return 0; }
  /* basis null vectors */
  for(int i=0;i<ndim;i++){ memset(nv[i],0,sizeof(u64)*wd); int fv=freevars[i]; nv[i][fv>>6]|=1ULL<<(fv&63);
    for(int p=0;p<npiv;p++){ if(piv[p][fv>>6]>>(fv&63)&1){ int c=pivc[p]; nv[i][c>>6]^=1ULL<<(c&63);} } }
  u64 cur[128]; memset(cur,0,sizeof(u64)*wd);
  u64 W[MAXN],Q[MAXN];
  unsigned long long total=1ULL<<ndim;
  unsigned long long gray=0, i=0;
  while(i<total){
    if(i>0){ int b=__builtin_ctzll(i); for(int w=0;w<wd;w++) cur[w]^=nv[b][w]; gray^=1ULL<<b; }
    /* extract */
    int oknow=1;
    for(int r=0;r<nX;r++){ W[r]=0; for(int s=0;s<nX;s++){ int v=r*nX+s; if(cur[v>>6]>>(v&63)&1) W[r]|=1ULL<<s; } }
    if(invertible(W,nX)){
      for(int t=0;t<nY;t++){ Q[t]=0; for(int c=0;c<nY;c++){ int v=nW+t*nY+c; if(cur[v>>6]>>(v&63)&1) Q[t]|=1ULL<<c; } }
      if(invertible(Q,nY)) { (void)oknow; return 1; }
    }
    i++;
  }
  return 0;
}
static int search(int k){
  nodes++;
  if(found||overflow) return 0;
  if(k==nZ){ leaves++; if(leaves>leaf_limit){overflow=1;return 0;}
    if(leaf_solve()){ found=1; return 1; } return 0; }
  int size=1<<k; int rt=rk[1][bp[k]];
  for(int ci=0;ci<ncand[rt];ci++){ uint32_t z=cand[rt][ci]; int ok=1;
    for(int i=0;i<size;i++){ uint32_t a=spanS[i]^z, b=spanP[i]^bp[k]; if(spanS[i]==z||rk[0][a]!=rk[1][b]){ok=0;break;} }
    if(!ok) continue;
    for(int i=0;i<size;i++){ spanS[size+i]=spanS[i]^z; spanP[size+i]=spanP[i]^bp[k]; }
    img[k]=z;
    if(search(k+1)) return 1;
    if(found||overflow) return 0;
  }
  return 0;
}
static int run(void){ /* assumes nX,nY,nZ,A loaded */
  rank_table(0); rank_table(1);
  long hs[MAXN+2]={0},hp[MAXN+2]={0};
  uint32_t N=1u<<nZ; for(uint32_t z=0;z<N;z++){ hs[rk[0][z]]++; hp[rk[1][z]]++; }
  int same=1; for(int r=0;r<=MAXN;r++) if(hs[r]!=hp[r]) same=0;
  leaves=0;nodes=0;dsolmax=0;overflow=0;found=0;
  if(!same) { printf("NONISO profile leaves=0 nodes=0 dsol=0\n"); free(rk[0]);free(rk[1]); return 0; }
  /* basis of Z for S' low-rank first */
  uint32_t *order=malloc(sizeof(uint32_t)*(N-1)); int oc=0;
  for(int r=0;r<=nX;r++) for(uint32_t z=1;z<N;z++) if(rk[1][z]==r) order[oc++]=z;
  uint32_t lead[32]; memset(lead,0,sizeof lead); int nb=0;
  for(int i=0;i<oc&&nb<nZ;i++){ uint32_t v=order[i],x=v;
    for(int bt=nZ-1;bt>=0;bt--){ if(x>>bt&1){ if(lead[bt]) x^=lead[bt]; else { lead[bt]=x; bp[nb++]=v; break; } } }
  }
  free(order);
  /* candidates by rank class in S */
  for(int r=0;r<=nX;r++){ ncand[r]=0; }
  for(uint32_t z=1;z<N;z++) ncand[rk[0][z]]++;
  for(int r=0;r<=nX;r++){ cand[r]=malloc(sizeof(uint32_t)*(ncand[r]+1)); ncand[r]=0; }
  for(uint32_t z=1;z<N;z++) { cand[rk[0][z]][ncand[rk[0][z]]++]=z; }
  spanS=malloc(sizeof(uint32_t)*(1u<<nZ)); spanP=malloc(sizeof(uint32_t)*(1u<<nZ)); spanS[0]=0; spanP[0]=0;
  /* solver buffers */
  Nu=nX*nX+nY*nY; nW=nX*nX; wd=(Nu>>6)+1; static int inited=0;
  piv=malloc(sizeof(u64*)*(Nu+1)); for(int i=0;i<=Nu;i++) piv[i]=malloc(sizeof(u64)*wd); pivc=malloc(sizeof(int)*(Nu+1)); eq=malloc(sizeof(u64)*wd); isp=malloc(Nu); for(int i=0;i<32;i++) nv[i]=calloc(wd,sizeof(u64));
  search(0);
  const char *res = overflow ? "OVERFLOW" : (found?"ISO":"NONISO");
  printf("%s search leaves=%lld nodes=%lld dsol=%d\n",res,leaves,nodes,dsolmax);
  for(int i=0;i<=Nu;i++) free(piv[i]); free(piv); free(pivc); free(eq); free(isp); for(int i=0;i<32;i++) free(nv[i]);
  for(int r=0;r<=nX;r++) free(cand[r]);
  free(spanS);free(spanP); free(rk[0]);free(rk[1]); (void)inited;
  return found;
}
/* input tokens: "Q nX nY nZ" + two tensors = solve; "H nX nY nZ" + one tensor = print rank histogram */
int main(void){
  char cmd[8];
  while(scanf("%7s",cmd)==1){
    if(scanf("%d %d %d",&nX,&nY,&nZ)!=3) return 1;
    int tens = (cmd[0]=='Q')?2:1;
    for(int s=0;s<tens;s++) for(int k=0;k<nZ;k++) for(int r=0;r<nX;r++){ unsigned long long v; if(scanf("%llx",&v)!=1) return 1; A[s][k][r]=v; }
    if(cmd[0]=='Q'){ run(); }
    else { rank_table(0); long h[MAXN+2]={0}; for(uint32_t z=0;z<(1u<<nZ);z++) h[rk[0][z]]++; free(rk[0]);
      for(int r=0;r<=nX;r++) printf("%ld ",h[r]); printf("\n"); }
    fflush(stdout);
  }
  return 0;
}
