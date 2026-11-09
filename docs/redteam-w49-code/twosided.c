/* Exact count of the orbits of Sp(d,2) acting on nondegenerate alternating forms on F_2^d, that is
   the number of double cosets Sp\GL/Sp = children left at the w49 node under TWO-SIDED pruning
   by automorphisms of source and target.  Expected: the number of conjugacy classes of GL(d/2,2)
   (pairs of alternating forms: the F[T]-module V = M (+) M with M of dimension d/2).
   usage: twosided < gens file (from sp_gens.g) ; or argv d to run for one d only */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
static inline int par(unsigned x){ return __builtin_popcount(x)&1; }
int main(int argc,char**argv){ char tok[32]; int want= argc>1?atoi(argv[1]):0; int d,ng;
  while(scanf("%31s %d %d",tok,&d,&ng)==3){ unsigned gens[8][8]; for(int g=0;g<ng;g++) for(int i=0;i<d;i++) scanf("%u",&gens[g][i]);
    if(want && d!=want) continue;
    int nbits=d*(d-1)/2; uint64_t total=1ULL<<nbits;
    /* index (i<j) bits */ int idx[8][8]; int c=0; for(int i=0;i<d;i++) for(int j=i+1;j<d;j++) idx[i][j]=idx[j][i]=c++;
    unsigned char *state=calloc(total,1); /* 1 = nondegenerate */
    uint64_t nnd=0;
    for(uint64_t f=0;f<total;f++){ unsigned B[8]={0}; for(int i=0;i<d;i++) for(int j=i+1;j<d;j++) if(f>>idx[i][j]&1){B[i]|=1u<<j;B[j]|=1u<<i;}
      /* rank */ unsigned t[8]; memcpy(t,B,sizeof t); int r=0; for(int b=0;b<d;b++){int p=-1;for(int i=r;i<d;i++)if(t[i]>>b&1){p=i;break;} if(p<0)continue; unsigned tmp=t[p];t[p]=t[r];t[r]=tmp; for(int i=0;i<d;i++) if(i!=r&&(t[i]>>b&1))t[i]^=t[r]; r++;}
      if(r==d){state[f]=1;nnd++;}
    }
    printf("d=%d nondegenerate alternating forms: %llu\n",d,(unsigned long long)nnd);
    uint32_t *stack=malloc(sizeof(uint32_t)*(nnd+1)); uint64_t orbits=0; uint64_t maxo=0, sumo=0;
    for(uint64_t f0=0;f0<total;f0++){ if(state[f0]!=1) continue; state[f0]=2; int top=0; stack[top++]=f0; uint64_t size=0;
      while(top){ uint32_t f=stack[--top]; size++;
        unsigned B[8]={0}; for(int i=0;i<d;i++) for(int j=i+1;j<d;j++) if((f>>idx[i][j])&1){B[i]|=1u<<j;B[j]|=1u<<i;}
        for(int g=0;g<ng;g++){ /* columns h_j of g */ unsigned h[8]; for(int j=0;j<d;j++){h[j]=0; for(int i=0;i<d;i++) if(gens[g][i]>>j&1) h[j]|=1u<<i;}
          /* v_j[k] = (B h_j)_k */ unsigned Bh[8]; for(int j=0;j<d;j++){unsigned w=0; for(int k=0;k<d;k++) if(par(B[k]&h[j])) w|=1u<<k; Bh[j]=w;}
          uint32_t nf=0; for(int i=0;i<d;i++) for(int j=i+1;j<d;j++){ if(par(h[i]&Bh[j])) nf|=1u<<idx[i][j]; }
          if(state[nf]==1){state[nf]=2;stack[top++]=nf;} else if(state[nf]==0){printf("form became degenerate!\n");return 1;}
        }
      }
      orbits++; sumo+=size; if(size>maxo)maxo=size; printf("  orbit size %llu\n",(unsigned long long)size);
    }
    printf("d=%d: orbits of Sp on nondeg forms = double cosets Sp\\GL/Sp = %llu (largest %llu, total %llu)\n",d,(unsigned long long)orbits,(unsigned long long)maxo,(unsigned long long)sumo);
    free(state); free(stack);
  }
  return 0; }
