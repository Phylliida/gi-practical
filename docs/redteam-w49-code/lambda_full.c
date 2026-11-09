/* Exact lambda(v)=|S cap (S+v)| for S=R1 u H on F_2^{de} by Walsh-Hadamard transform,
   tabulated by (class,rank), compared with the memo's formula.  Independent of the author's code.
   usage: lambda_full d e        (d*e <= 30)   */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
static int rankm(uint64_t M, int d, int e){ uint64_t r[32]; for(int i=0;i<d;i++) r[i]=(M>>(i*e))&((1ULL<<e)-1);
  int rk=0; for(int b=0;b<e;b++){ int p=-1; for(int i=rk;i<d;i++) if(r[i]>>b&1){p=i;break;} if(p<0) continue;
    uint64_t t=r[rk]; r[rk]=r[p]; r[p]=t; for(int i=0;i<d;i++) if(i!=rk && (r[i]>>b&1)) r[i]^=r[rk]; rk++; }
  return rk; }
static int Qm(uint64_t M,int d,int e){ int q=0; for(int t=0;t<d/2;t++) for(int s=0;s<e/2;s++){
  int a=2*t,a2=2*t+1,b=2*s,b2=2*s+1;
  int m1=(M>>(a*e+b))&1, m2=(M>>(a2*e+b2))&1, m3=(M>>(a*e+b2))&1, m4=(M>>(a2*e+b))&1;
  q^=(m1&m2)^(m3&m4);} return q; }
int main(int c,char**v){ int d=atoi(v[1]),e=atoi(v[2]); int n=d*e; uint64_t N=1ULL<<n;
  long long *f=calloc(N,sizeof(long long)); char *cls=calloc(N,1); unsigned char *rk=malloc(N);
  for(uint64_t a=1;a<(1ULL<<d);a++) for(uint64_t b=1;b<(1ULL<<e);b++){ uint64_t M=0; for(int i=0;i<d;i++) if(a>>i&1) M|=b<<(i*e); cls[M]=1; }
  long long r=0,h=0; for(uint64_t M=1;M<N;M++){ rk[M]=rankm(M,d,e); if(Qm(M,d,e)){ if(cls[M]==1){printf("R1 cap H nonempty\n");return 1;} cls[M]=2; h++; } if(cls[M]==1) r++; if(cls[M]) f[M]=1; }
  rk[0]=0;
  printf("(d,e)=(%d,%d) |R1|=%lld |H|=%lld\n",d,e,r,h);
  for(int b=0;b<n;b++){ uint64_t s=1ULL<<b; for(uint64_t i=0;i<N;i++) if(!(i&s)){ long long a=f[i],q=f[i|s]; f[i]=a+q; f[i|s]=a-q; } }
  for(uint64_t i=0;i<N;i++) f[i]*=f[i];
  for(int b=0;b<n;b++){ uint64_t s=1ULL<<b; for(uint64_t i=0;i<N;i++) if(!(i&s)){ long long a=f[i],q=f[i|s]; f[i]=(a+q)/2; f[i|s]=(a-q)/2; } }
  /* tabulate */
  long long seen[3][33][64]; int cnt[3][33]; memset(cnt,0,sizeof cnt);
  long long nv[3][33]; memset(nv,0,sizeof nv);
  for(uint64_t M=1;M<N;M++){ int k=cls[M]; int p=rk[M]; nv[k][p]++; long long L=f[M]; int fnd=0; for(int i=0;i<cnt[k][p];i++) if(seen[k][p][i]==L) fnd=1; if(!fnd && cnt[k][p]<64) seen[k][p][cnt[k][p]++]=L; }
  long long D=1LL<<(d+e), m=n/2; long long C=(1LL<<(2*m-2))-(1LL<<(m-1)); long long Rr=((1LL<<d)-1)*((1LL<<e)-1);
  #define tau(p) (((1LL<<d)-(1LL<<(d-(p))))*(1LL<<(e-1)))
  long long c1=(1LL<<d)+(1LL<<e)-4, lamR=c1+2*tau(1)+C;
  const char*nm[3]={"non-S (Q=0,rk>=2 or 0)","R1","H"};
  printf("predicted lambda(R1)=%lld\n",lamR);
  for(int k=0;k<3;k++) for(int p=1;p<=e;p++){ if(!nv[k][p]) continue; printf("class %-24s rank %d count %lld lambda values:",nm[k],p,nv[k][p]); for(int i=0;i<cnt[k][p];i++) printf(" %lld",seen[k][p][i]); 
     if(k==2){ long long cp = p==2?6:(p>=3?0:(1LL<<d)+(1LL<<e)-4); long long pr=cp+2*(Rr-tau(p))+C; printf("  [memo predicted %lld]",pr);} 
     if(k==1){ printf("  [memo predicted %lld]",lamR);} printf("\n"); }
  /* decisive separation check: is lambda on R1 distinct from all lambda on H? */
  int sep=1; for(int p=1;p<=e;p++) for(int i=0;i<cnt[2][p];i++) if(seen[2][p][i]==lamR) sep=0;
  printf("R1 edges separated from H edges by lambda: %s\n",sep?"YES":"NO");
  return 0; }
