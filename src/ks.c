/* strings & string interning */

#include "incs.h"

#include "k.h"
#include "ks.h"

Z I ns=0,sdd=0;
// Z S sdup(S s){R strdupn(s,strlen(s));} //using this because "strdup" uses [used] dynamically linked malloc which fails with our static free
Z S sdupI(S s){I k;S d=alloc(NSLOTS*sizeof(I)+(k=strlen(s))+1);if(!d)R 0;ns++;sdd=1;d+=NSLOTS*sizeof(I);d[k]=0;R memcpy(d,s,k);}
S strdupn (S s,I k) {S d=alloc(k+1);if(!d)R 0;d[k]=0;R memcpy(d,s,k);} // mm/o  (note: this can overallocate)
//I SC0N(S a,S b,I n) {I x=memcmp(a,b,n); R x<0?-1:x>0?1:a[n]?1:0; }// non-standard way to compare aaa\0 vs aaa
I strlenn(S s,I k){S t=memchr(s,'\0',k); R t?t-s:k;}

I StoI(S s,I *n){S t; errno=0; *n=strtol(s,&t,10); R !(errno!=0||t==s||*t!=0);}

I SC(S a,S b)
{ O("BEG SC\n");
  I x=strcmp(a,b);
  R x<0?-1:x>0?1:0; }//String Compare: strcmp unfortunately does not draw from {-1,0,1}

S sp(S k)//symbol from phrase: string interning, Ks(sp("aaa")). This should be called before introducing any sym to the instance
{ //We are using this to ensure any two 'character-identical' symbols are in fact represented by the same pointer S
  //See Knuth Algorithm 6.2.2T
  O("BEG sp   %s\n",k); fflush(stdout);
  #define LINK(n,x) (n)->c[((x)+1)/2] // -1 => 0 , 1 => 1
  if(!k)R 0;//used in glue. used in _2m_4. used in parse. Probably a good argument to keep since it's exposed for libraries via 2: dyadic
  N t=SYMBOLS, s=t->c[1],p=s,q=p,r; I a,x;
  if(!s){s=t->c[1]=newN();P(!s,(S)ME);s->k=sdupI(k); if(!s->k){free(s);t->c[1]=0;ME;} R s->k;} // <-- strdup here and below
  while(q)
  { O("~FN SC(k,p->k)      I SC(S a,S b) <- S sp(S k)      ");
    a=SC(k,p->k);
    O("#FN sp :: SC(k,p->k)  a: %lld\n",a);
    if(!a){R p->k;}//In the usual tree put: p->k=k,p->v=v before returning
    O("~FO LINK(p,a)      LINK(n,x) <- S sp(S k)      \n");
    q=LINK(p,a);
    O("#FO sp :: LINK(p,a)  q: %p\n",q);
    if(!q)
    { O("~FP newN()      N newN() <- S sp(S k)      ");
      q=newN();
      O("#FP sp :: newN()\n");
      P(!q,(S)ME);
      q->k=sdupI(k);
      if(!q->k){ free(q); ME; R 0;}
      LINK(p,a)=q;break; }//Usual tree would q->v=v. mmo
    else if(q->b){t=p;s=q;}
    p=q;
  }
  O("~FR SC(k,s->k)      I SC(S a,S b) <- S sp(S k)      ");
  a=0>SC(k,s->k)?-1:1;
  O("#FR sp :: SC(k,s->k)\n");
  r=p=LINK(s,a);
  while(p!=q)
  { O("~FS SC(k,p->k)      I SC(S a,S b) <- S sp(S k)      ");
    x=SC(k,p->k);
    O("#FS sp :: SC(k,p->k)\n");
    p->b=x;p=LINK(p,x);}
  if(!s->b){s->b=a;R p->k;}
  else if(s->b==-a){s->b=0; R p->k;}
  if(r->b==a){p=r; LINK(s,a)=LINK(r,-a); LINK(r,-a)=s; s->b=r->b=0;}
  else if(r->b==-a)
  { p=LINK(r,-a); LINK(r,-a)=LINK(p,a);
    LINK(p,a)=r; LINK(s,a)=LINK(p,-a); LINK(p,-a)=s;
    if     (p->b== a){s->b=-a; r->b=0;}
    else if(p->b== 0){s->b= 0; r->b=0;}
    else if(p->b==-a){s->b= 0; r->b=a;}
    p->b=0; }
  t->c[s==t->c[1]?1:0]=p;
  S z=q->k;
  O("KK2\n");
  R z;
}

//S spkC(K a){S u=strdupn(kC(a),a->n),v=sp(u);free(u);R v;}
S spn(S s,I n){I k=0;while(k<n && s[k])k++; S u=strdupn(s,k); if(!u)R 0; S v=sp(u); free(u); R v;} //safer/memory-efficient strdupn
I wleft(N x,I y,I z)
{
  if(!x)R z;
  z=wleft(x->c[0],y,z);
  if(x->k&&SV(x->k,y)){I o=SV(x->k,y);SV(x->k,y)=z;z+=o;}
  R wleft(x->c[1],y,z);
}
I wright(N x,I y,I z)
{
  if(!x)R z;
  z=wright(x->c[1],y,z);
  if(x->k&&SV(x->k,y)){I o=SV(x->k,y);SV(x->k,y)=z;z+=o;}
  R wright(x->c[0],y,z);
}
Z void ssI(N x,int y,I z){if(x){DO(2,ssI(x->c[i],y,z));if(x->k)SV(x->k,y)=z;}}
void setS(int y,I z){ssI(SYMBOLS,y,z);}
void OS(N x,I y)
{
  if(!x)R;
  OS(x->c[0],y);
  if(x->k&&SV(x->k,y))O("%p: %lld\n",x->k,SV(x->k,y));
  OS(x->c[1],y);
}
