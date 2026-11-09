// conf.c: individualization depth and triple-correlation statistics for conference graphs.
// Reads graphs from stdin:  "G name" / "n" / "NREP r1 .. rk" (reps of Aut on V; may be all) /
// "NREP2 r1 .. rk" (reps of stabilizer of r1, applies to first rep only, optional, 0 = all) / n rows of 01.
// Modes (argv[1]):
//   ind1 kmax : exact minimum individualization depth to discreteness under 1-WL, up to kmax.
//   ind2 kmax : same with 2-WL; a vertex is singleton if its diagonal colour is unique.
//   triple    : statistics of T(a,b,v)=sum_x C(a,x)C(b,x)C(v,x), p(v,w)=P_{a,b}[T(a,b,v)=T(a,b,w)].
// 1-WL/2-WL use 64-bit hashing; a collision can only merge classes (overstate depth). Run under nice.
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
typedef uint64_t u64;
#define MAXN 7000
static inline u64 mix(u64 a,u64 b){u64 x=a*0x9E3779B97F4A7C15ULL+b;x^=x>>29;x*=0xBF58476D1CE4E5B9ULL;x^=x>>32;x+=b*0x94D049BB133111EBULL;x^=x>>29;return x;}
static inline u64 h1(u64 v){v^=v>>33;v*=0xff51afd7ed558ccdULL;v^=v>>33;v*=0xc4ceb9fe1a85ec53ULL;v^=v>>33;return v;}
static int n; static unsigned char A[MAXN][MAXN]; static short C[MAXN][MAXN];
static int nbr[MAXN][MAXN],deg[MAXN];
static int cmp_u64(const void*a,const void*b){u64 x=*(const u64*)a,y=*(const u64*)b;return (x>y)-(x<y);}
static int classes(u64*col,int m,u64*scr){memcpy(scr,col,m*sizeof(u64));qsort(scr,m,sizeof(u64),cmp_u64);int c=0;for(int i=0;i<m;i++)if(i==0||scr[i]!=scr[i-1])c++;return c;}
static long rounds_acc=0;
static void refine1(u64*col,int rounds_limit){u64 nw[MAXN],scr[MAXN];int last=classes(col,n,scr);
  for(int it=0;it<rounds_limit;it++){rounds_acc++;
    for(int v=0;v<n;v++){u64 s=0;for(int j=0;j<deg[v];j++)s+=h1(col[nbr[v][j]]);nw[v]=mix(col[v],s);}
    memcpy(col,nw,sizeof(u64)*n);int c=classes(col,n,scr);if(c==last)break;last=c;}}
static int nreps; static int reps[MAXN]; static int nreps2; static int reps2[MAXN];
static int kmax; static long nsamp=200; static int best_k; static long leaves, disc_leaves; static long discrete_by_k[20], visited_by_k[20];
static long cells_sum[20];
static int sel[64];
static int dfs1(u64*col,int depth,int k,int start,int firstrep){
  u64 scr[MAXN]; int c=classes(col,n,scr);
  if(depth==k){visited_by_k[k]++; cells_sum[k]+=c; if(c==n){discrete_by_k[k]++; return 1;} return 0;}
  if(c==n){ /* already discrete: count as discrete at this k */ visited_by_k[k]++; cells_sum[k]+=c; discrete_by_k[k]++; return 1; }
  int found=0;
  // choose candidates: first level: reps; second level: reps2 if given; deeper: > previous
  int cand[MAXN],nc=0;
  if(depth==0){for(int i=0;i<nreps;i++)cand[nc++]=reps[i];}
  else if(depth==1&&nreps2>0){for(int i=0;i<nreps2;i++)cand[nc++]=reps2[i];}
  else for(int v=start;v<n;v++)cand[nc++]=v;
  for(int i=0;i<nc;i++){int v=cand[i];
    // skip singleton vertices
    int cnt=0;for(int u=0;u<n;u++)if(col[u]==col[v])cnt++;
    if(cnt<=1)continue;
    u64 sv[MAXN];memcpy(sv,col,sizeof(u64)*n);
    col[v]=mix(col[v],0x1234567ULL+depth*1000003ULL);
    refine1(col,n+2);
    sel[depth]=v;
    int r=dfs1(col,depth+1,k,(depth>=1)?v+1:0,0);
    memcpy(col,sv,sizeof(u64)*n);
    if(r){found=1;}
  }
  return found;
}
static int nthreads_dummy=0;
// 2-WL
static u64 *W,*W2,*WS;
static void refine2(void){int N=n*n;int last=classes(W,N,WS);
  for(int it=0;it<2*n+5;it++){
    for(int x=0;x<n;x++)for(int y=0;y<n;y++){u64 s=0;for(int z=0;z<n;z++)s+=h1(mix(W[x*n+z],W[z*n+y]));W2[x*n+y]=mix(W[x*n+y],s);}
    u64*t=W;W=W2;W2=t;int c=classes(W,N,WS);if(c==last)break;last=c;}}
static int pointcells(void){u64 d[MAXN],scr[MAXN];for(int x=0;x<n;x++)d[x]=W[x*n+x];return classes(d,n,scr);}
static int dfs2(u64*saved,int depth,int k,int start){
  int c=pointcells();
  if(depth==k||c==n){visited_by_k[k]++;cells_sum[k]+=c; if(c==n){discrete_by_k[k]++;return 1;}return 0;}
  int found=0;
  int cand[MAXN],nc=0;
  if(depth==0){for(int i=0;i<nreps;i++)cand[nc++]=reps[i];}
  else if(depth==1&&nreps2>0){for(int i=0;i<nreps2;i++)cand[nc++]=reps2[i];}
  else for(int v=start;v<n;v++)cand[nc++]=v;
  u64 *cur=malloc(sizeof(u64)*n*n); memcpy(cur,W,sizeof(u64)*n*n);
  u64 d[MAXN];for(int x=0;x<n;x++)d[x]=W[x*n+x];
  for(int i=0;i<nc;i++){int v=cand[i];
    int cnt=0;for(int u=0;u<n;u++)if(d[u]==d[v])cnt++;
    if(cnt<=1)continue;
    memcpy(W,cur,sizeof(u64)*n*n);
    W[v*n+v]=mix(W[v*n+v],0x77777ULL+depth*1000003ULL);
    refine2();
    sel[depth]=v;
    int r=dfs2(saved,depth+1,k,(depth>=1)?v+1:0);
    if(r)found=1;
  }
  memcpy(W,cur,sizeof(u64)*n*n);free(cur);
  return found;
}
// triple statistics
static short *T; // T[a*n*n+b*n+v]
static inline int t_idx(int a,int b,int v){return a*n*n+b*n+v;}
static void compute_T(void){T=malloc(sizeof(short)*n*n*n);
  for(int a=0;a<n;a++)for(int b=0;b<n;b++)for(int v=0;v<n;v++){int s=0;for(int x=0;x<n;x++)s+=C[a][x]*C[b][x]*C[v][x];T[t_idx(a,b,v)]=s;}}
static int cmpint(const void*a,const void*b){return *(const int*)a-*(const int*)b;}
static void triple_stats(const char*name){compute_T();
  // over a<b: distinct values of T(a,b,.), max |T|, ||T||^2 check
  long distinct_sum=0;long min_distinct=1e9,max_distinct=0;long maxabs=0;double sumsq=0;long cnt=0;long zero_vals=0;
  for(int a=0;a<n;a++)for(int b=a+1;b<n;b++){int vals[MAXN];int m=0;long s2=0;
    for(int v=0;v<n;v++){if(v==a||v==b)continue;int t=T[t_idx(a,b,v)];vals[m++]=t;if(abs(t)>maxabs)maxabs=abs(t);s2+=(long)t*t;if(t==0)zero_vals++;}
    qsort(vals,m,sizeof(int),cmpint);int d=0;for(int i=0;i<m;i++)if(i==0||vals[i]!=vals[i-1])d++;
    distinct_sum+=d;if(d<min_distinct)min_distinct=d;if(d>max_distinct)max_distinct=d;sumsq+=s2;cnt++;}
  // p(v,w)
  double maxp=0,minp=2,sump=0;long npairs=0;int bv=-1,bw=-1;long hist[12]={0};
  for(int v=0;v<n;v++)for(int w=v+1;w<n;w++){long eq=0,tot=0;
    for(int a=0;a<n;a++){if(a==v||a==w)continue;for(int b=a+1;b<n;b++){if(b==v||b==w)continue;tot++;if(T[t_idx(a,b,v)]==T[t_idx(a,b,w)])eq++;}}
    double p=(double)eq/tot;sump+=p;npairs++;if(p>maxp){maxp=p;bv=v;bw=w;}if(p<minp)minp=p;int bin=(int)(p*10);if(bin>10)bin=10;hist[bin]++;}
  printf("TRIPLE %s n=%d meanDistinct=%.2f minDistinct=%ld maxDistinct=%ld maxAbsT=%ld meanT2=%.2f zeroFrac=%.4f | maxp=%.4f (pair %d,%d) meanp=%.4f minp=%.4f sqrt(1/n)=%.4f hist01:",
    name,n,(double)distinct_sum/cnt,min_distinct,max_distinct,maxabs,sumsq/(cnt*(n-2.0)),(double)zero_vals/(cnt*(n-2.0)),maxp,bv,bw,sump/npairs,minp,1.0/__builtin_sqrt(n));
  for(int i=0;i<=10;i++)printf(" %ld",hist[i]);printf("\n");free(T);
}

// sampled mode: random k-subsets (first vertex uniform from reps)
static unsigned long long rs=0x123456789ULL;
static unsigned long long rnd(void){rs^=rs<<13;rs^=rs>>7;rs^=rs<<17;return rs;}
static void samp1(const char*name){
  printf("SAMP1 %s n=%d (log2 n=%.2f):",name,n,__builtin_log(n)/__builtin_log(2));
  u64 base[MAXN];for(int i=0;i<n;i++)base[i]=1;refine1(base,n+2);
  for(int k=1;k<=kmax;k++){long disc=0;double cells=0;int mincells=n+1,maxcells=0;long rounds=0;
    for(long s=0;s<nsamp;s++){u64 col[MAXN];memcpy(col,base,sizeof(u64)*n);
      int chosen[64];
      chosen[0]=reps[rnd()%nreps];
      for(int d=1;d<k;d++){int v;do{v=rnd()%n;int dup=0;for(int e=0;e<d;e++)if(chosen[e]==v)dup=1;if(!dup){chosen[d]=v;break;}}while(1);}
      for(int d=0;d<k;d++){int v=chosen[d];col[v]=mix(col[v],0x1234567ULL+d*1000003ULL);}
      long r0=rounds_acc;refine1(col,n+2);rounds+=rounds_acc-r0;
      u64 scr[MAXN];int c=classes(col,n,scr);if(c==n)disc++;cells+=c;if(c<mincells)mincells=c;if(c>maxcells)maxcells=c;
    }
    printf(" k=%d[disc=%ld/%ld,meancells=%.1f,min=%d,max=%d,meanrounds=%.1f]",k,disc,nsamp,cells/nsamp,mincells,maxcells,(double)rounds/nsamp);fflush(stdout);
    if(disc==nsamp)break;
  }
  printf("\n");fflush(stdout);
}

// sampled triple statistics: for S random pairs (a,b) compute T(a,b,.), estimate p(v,w) for all v<w.
static void triple_samp(const char*name){
  int S=(int)nsamp; long *eq=calloc((size_t)n*n,sizeof(long)); short *g=malloc(sizeof(short)*n); int *t=malloc(sizeof(int)*n);
  long maxabs=0; double sumT2=0; long cntT=0; long zeros=0;
  for(int s=0;s<S;s++){int a=rnd()%n,b;do{b=rnd()%n;}while(b==a);
    for(int x=0;x<n;x++)g[x]=C[a][x]*C[b][x];
    for(int v=0;v<n;v++){int sum=0;for(int x=0;x<n;x++)sum+=g[x]*C[v][x];t[v]=sum; if(v!=a&&v!=b){if(abs(sum)>maxabs)maxabs=abs(sum);sumT2+=(double)sum*sum;cntT++;if(sum==0)zeros++;}}
    for(int v=0;v<n;v++){if(v==a||v==b)continue;for(int w=v+1;w<n;w++){if(w==a||w==b)continue;if(t[v]==t[w])eq[v*n+w]++;}}
  }
  double maxp=0,sump=0,minp=2;long npairs=0;long high[5]={0,0,0,0,0};double thr[5]={0.05,0.1,0.2,0.3,0.5};
  for(int v=0;v<n;v++)for(int w=v+1;w<n;w++){double p=(double)eq[v*n+w]/S;sump+=p;npairs++;if(p>maxp)maxp=p;if(p<minp)minp=p;for(int i=0;i<5;i++)if(p>=thr[i])high[i]++;}
  printf("TRIPLES %s n=%d S=%d maxAbsT=%ld meanT2=%.2f zeroFrac=%.5f | maxp=%.3f meanp=%.4f minp=%.3f sqrt(1/n)=%.4f pairs>=[.05,.1,.2,.3,.5]: %ld %ld %ld %ld %ld of %ld\n",
   name,n,S,maxabs,sumT2/cntT,(double)zeros/cntT,maxp,sump/npairs,minp,1.0/__builtin_sqrt(n),high[0],high[1],high[2],high[3],high[4],npairs);
  fflush(stdout);free(eq);free(g);free(t);
}

static int cmpi(const void*a,const void*b){return *(int*)a-*(int*)b;}
static void cells_after(const char*name,int k){ // individualize vertices 0..k-1 under 2-WL, print sorted cell sizes
  W=malloc(sizeof(u64)*n*n);W2=malloc(sizeof(u64)*n*n);WS=malloc(sizeof(u64)*n*n);
  for(int x=0;x<n;x++)for(int y=0;y<n;y++){W[x*n+y]=(x==y)?7:(A[x][y]?1:2);}
  refine2();
  for(int i=0;i<k;i++){W[i*n+i]=mix(W[i*n+i],0x777ULL+i);refine2();}
  u64 d[MAXN];for(int x=0;x<n;x++)d[x]=W[x*n+x];
  int ids[MAXN];u64 scr[MAXN];memcpy(scr,d,sizeof(u64)*n);qsort(scr,n,sizeof(u64),cmp_u64);
  int sizes[MAXN];int nc=0;for(int i=0;i<n;){int j=i;while(j<n&&scr[j]==scr[i])j++;sizes[nc++]=j-i;i=j;}
  qsort(sizes,nc,sizeof(int),cmpi);
  printf("CELLS2 %s k=%d: ncells=%d sizes:",name,k,nc);for(int i=0;i<nc;i++)printf(" %d",sizes[i]);printf("\n");fflush(stdout);
  free(W);free(W2);free(WS);
}
int main(int argc,char**argv){
  const char*mode=argv[1]; kmax=argc>2?atoi(argv[2]):6; if(argc>3)nsamp=atol(argv[3]);
  char name[256],line[10000];
  while(fgets(line,sizeof line,stdin)){
    if(strncmp(line,"G ",2)!=0)continue;
    sscanf(line+2,"%255s",name);
    if(!fgets(line,sizeof line,stdin))break; n=atoi(line);
    if(n>=MAXN){fprintf(stderr,"n too large\n");exit(1);}
    if(!fgets(line,sizeof line,stdin))break;
    nreps=0;{char*p=strtok(line," \n");p=strtok(NULL," \n");while(p){reps[nreps++]=atoi(p);p=strtok(NULL," \n");}}
    if(!fgets(line,sizeof line,stdin))break;
    nreps2=0;{char*p=strtok(line," \n");p=strtok(NULL," \n");while(p){reps2[nreps2++]=atoi(p);p=strtok(NULL," \n");}}
    for(int i=0;i<n;i++){if(!fgets(line,sizeof line,stdin))break;for(int j=0;j<n;j++){A[i][j]=line[j]=='1';C[i][j]=(i==j)?0:(A[i][j]?-1:1);}}
    for(int i=0;i<n;i++){deg[i]=0;for(int j=0;j<n;j++)if(A[i][j])nbr[i][deg[i]++]=j;}
    if(!strcmp(mode,"triple")){triple_stats(name);fflush(stdout);continue;}
    if(!strcmp(mode,"samp1")){samp1(name);continue;}
    if(!strcmp(mode,"cells2")){cells_after(name,kmax);continue;}
    if(!strcmp(mode,"triples")){triple_samp(name);continue;}
    if(!strcmp(mode,"ind1")){
      printf("IND1 %s n=%d (log2 n=%.2f):",name,n,__builtin_log(n)/__builtin_log(2));
      int done=0;
      for(int k=1;k<=kmax&&!done;k++){memset(discrete_by_k,0,sizeof discrete_by_k);memset(visited_by_k,0,sizeof visited_by_k);memset(cells_sum,0,sizeof cells_sum);
        u64 col[MAXN];for(int i=0;i<n;i++)col[i]=1;refine1(col,n+2);
        int r=dfs1(col,0,k,0,1);
        printf(" k=%d[visited=%ld,discrete=%ld,meancells=%.1f]",k,visited_by_k[k],discrete_by_k[k],visited_by_k[k]?(double)cells_sum[k]/visited_by_k[k]:0.0);
        fflush(stdout);if(r){printf(" MIN=%d",k);done=1;}}
      if(!done)printf(" MIN>%d",kmax);printf("\n");fflush(stdout);continue;}
    if(!strcmp(mode,"ind2")){
      printf("IND2 %s n=%d:",name,n);int done=0;
      W=malloc(sizeof(u64)*n*n);W2=malloc(sizeof(u64)*n*n);WS=malloc(sizeof(u64)*n*n);
      for(int k=1;k<=kmax&&!done;k++){memset(discrete_by_k,0,sizeof discrete_by_k);memset(visited_by_k,0,sizeof visited_by_k);memset(cells_sum,0,sizeof cells_sum);
        for(int x=0;x<n;x++)for(int y=0;y<n;y++){W[x*n+y]=(x==y)?7:(A[x][y]?1:2);}
        refine2();
        int r=dfs2(NULL,0,k,0);
        printf(" k=%d[visited=%ld,discrete=%ld,meancells=%.1f]",k,visited_by_k[k],discrete_by_k[k],visited_by_k[k]?(double)cells_sum[k]/visited_by_k[k]:0.0);
        fflush(stdout);if(r){printf(" MIN=%d",k);done=1;}}
      if(!done)printf(" MIN>%d",kmax);printf("\n");fflush(stdout);free(W);free(W2);free(WS);continue;}
  }
  return 0;
}
