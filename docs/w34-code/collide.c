// collide.c: collision rate p2(x,y) on iterated Turyn W_L, as function of the number of differing base coordinates.
// usage: collide v L samples_per_r ntests seed < base.matrix (v rows of +-1)
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
static int v, L, m, n;
static signed char *BV; // base
static signed char *W;  // n x n
#define WIDX(i,j) ((size_t)(i)*n+(j))
static uint64_t st=12345;
static inline uint64_t rnd(){ st^=st<<13; st^=st>>7; st^=st<<17; return st; }
static void build(){
  // iterative Turyn from BV
  int cur=v; signed char *C=(signed char*)malloc(cur*cur); memcpy(C,BV,cur*cur);
  for(int l=0;l<L;l++){ int N=cur*cur; signed char *D=(signed char*)malloc((size_t)N*N);
    for(int i=0;i<cur;i++)for(int j=0;j<cur;j++)for(int k=0;k<cur;k++)for(int l2=0;l2<cur;l2++){
      int val=C[i*cur+k]*C[j*cur+l2]+(i==k)-(j==l2);
      D[(size_t)(i*cur+j)*N+(k*cur+l2)]=val; }
    free(C); C=D; cur=N; }
  W=C; n=cur;
}
int main(int argc,char**argv){
  v=atoi(argv[1]); L=atoi(argv[2]); int per=atoi(argv[3]); int ntests=atoi(argv[4]); st+=atoi(argv[5]);
  BV=(signed char*)malloc(v*v); for(int i=0;i<v*v;i++){int x; if(scanf("%d",&x)!=1)return 1; BV[i]=x;}
  build(); m=1<<L;
  printf("# n=%d m=%d\n",n,m);
  int pw[64]; pw[m-1]=1; for(int j=m-2;j>=0;j--)pw[j]=pw[j+1]*v;
  for(int r=1;r<=m;r++){ double sum=0,mx=0; for(int rep=0;rep<per;rep++){
      int x=rnd()%n; int digits[64]; { int t=x; for(int j=m-1;j>=0;j--){digits[j]=t%v;t/=v;} }
      int y=x; int chosen=0; int mask=0;
      // pick r random coordinates
      int perm[64]; for(int i=0;i<m;i++)perm[i]=i; for(int i=0;i<r;i++){int j=i+rnd()%(m-i);int t=perm[i];perm[i]=perm[j];perm[j]=t;}
      for(int i=0;i<r;i++){int c=perm[i]; int nv; do{nv=rnd()%v;}while(nv==digits[c]); y+=(nv-digits[c])*pw[c];}
      long coll=0;
      for(int t=0;t<ntests;t++){ int a=rnd()%n,b=rnd()%n; if(a==b||a==x||a==y||b==x||b==y)continue;
        if(W[WIDX(a,x)]!=W[WIDX(a,y)]||W[WIDX(b,x)]!=W[WIDX(b,y)])continue;
        int tx=0,ty=0; for(int z=0;z<n;z++){int g=W[WIDX(a,z)]*W[WIDX(b,z)]; tx+=g*W[WIDX(x,z)]; ty+=g*W[WIDX(y,z)];}
        if(tx==ty)coll++;
      }
      double p=(double)coll/ntests; sum+=p; if(p>mx)mx=p;
    }
    printf("r=%d mean_p2=%.4f max_p2=%.4f (1/(4 sqrt r)=%.4f)\n",r,sum/per,mx,0.25/sqrt(r));
  }
  return 0;
}
