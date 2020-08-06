/* execution */

#include "incs.h"
#include <signal.h>

#include "k.h"
#include "kc.h"
#include "ko.h"
#include "kx.h"
#include "km.h"
#include "v.h"

extern volatile sig_atomic_t interrupted;

Z K bv_ex(V *p,K k);
K dv_ex(K a,V *p,K b);
Z K ex0(V *v,K k,I r);
Z K ex2(V *v,K k);
Z V ex_(V a,I r);
I cirRef(K p,K y);
I cirRef_(K p,K y,I f);
K kdef(V v);

__thread I fer=0;    // Flag Early Return
__thread I fer1=0;
__thread I fwh=0;    // Flag While
__thread I stk=0;    // Stack counter
__thread I stk1=0;   // Additional stack counter
__thread I prj=0;    // Projection flag
__thread I prj2=0;   // 2nd Projection flag
__thread K prnt=0;   // Parent of Subfunction
__thread I fsf=0;    // Flag for Subfunctions
__thread K grnt=0;   // GrandParent of Subfunction
__thread K cls=0;    // Closure: level 2 linkage
__thread K encf=0;   // Enclosing Function
__thread I encp=0;   // Enclosing Function Param
__thread I frg=0;    // Flag reset globals
         S fnc=0;    // Most recent function from Dispatch Table
         V fncp[128];// DT pointers of executed functions
         I fnci=0;   // indicator of next function pointer position
         I fom=0;    // Flag overMonad (curried)
         I fam=1;    // Flag amend: 1=OK to print response
         I fdvx=0;   // restrict printing of void pointers in dv_ex
         I ft3=0;    // Flag if t3<DT_SIZE
         C cdp[]="aaaaaaaaaa";    // Code Pointer
         I cnte=0;

         I calf=-1;  // counter for alf
         C* alf="abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ"; // for recursive member display in sd_()

K sd_(K x,I f)
{ if(x)
  { if(!bk(x))
    { if(xt==4)O("     %p %p %p  %lld-%lld %lld %lld   ",    x,kK(x),*kK(x),x->_c>>8,(x->_c<<56)>>56,xt,xn);
      else     O("     %p %p            %lld-%lld %lld %lld   ",x,kK(x),x->_c>>8,(x->_c<<56)>>56,xt,xn);
      if(f>0 && ((xt==0) || (xt==5))) O("\n");
      if(xt!=6 && f>0)show(x); else O("\n"); }
    else { O(" is ; or \\n\n"); R x; } }
  else { O("     "); show(x); O("\n"); R x; }
  if(f<2) R 0;
  SW(xt)
  { CS( 7, calf++; O("     %c0:    %p     %s\n",alf[calf],&kS(x)[CONTeXT],kS(x)[CONTeXT]);
           O("     %c1:    %p     %p\n",alf[calf],&kV(x)[DEPTH],kV(x)[DEPTH]);
           DO(-2+TYPE_SEVEN_SIZE, O("     %c%lld:   ",alf[calf],2+i); O(" %p",&kV(x)[2+i]); sd_(kV(x)[2+i],3); )
           calf--; )
    CS(-4, if(1)       //(f>-1)
           { V* v=(kV(x));
             #ifdef __APPLE__
             R 0;
             #else
             if((v[0]>(V)0x10) & (v[0]<(V)0x5000000)) R 0; //stop, if have string of interned symbols
             #endif
             I ii; for(ii=0;v[ii];ii++)
                   { O("     .2%c[%lld]: %p",alf[calf],ii,v[ii]);
                     if(v[ii]>(V)DT_SIZE){ if(calf<2)sd_(*(K*)v[ii],2); else sd_(*(K*)v[ii],1); }
                     else O("\n"); } } )
    CSR(5,)
    CS( 0, DO(xn, O(" %p",&kK(x)[xn-i-1]); sd_(kK(x)[i],2);) ) }
  R 0; }

K sd(K x) { R sd_(x,1); }     //Shows the details of a K-structure. Useful in debugging.

Z K cjoin(K x,K y)
{ O("BEG cjoin\n");
  P(3!=xt,TE)
  if(3==ABS(yt))R ci(y);
  P(yt,TE);
  if(!yn)R newK(-3,0);
  I zn=0;K v;
  DO(yn,v=kK(y)[i];
  if(-3!=v->t) R TE;zn+=v->n)
  zn+=yn?(yn-1)*xn:0;
  K z=newK(-3,zn); M(z); S p=kC(z);
  DO(yn-1, v=kK(y)[i]; memcpy(p,kC(v),v->n); p+=v->n;memcpy(p,kC(x),xn); p+=xn)
  v=kK(y)[yn-1]; memcpy(p,kC(v),v->n); R z; }

Z K csplit(K x,K y)       //scan 2x
{ O("BEG csplit\n");
  P(3!=xt,TE);
  P(3!=ABS(yt),TE);
  int delim=*kC(x);S s=kC(y);
  I p0,p1,zn=0,i=0;
  while(i<yn)
  { I j=i,n=0;
    while(i<yn&&delim!=s[i]){ i++; n++; }
    p0=j; p1=n; zn++;
    if(i<yn&&delim==s[i]) i++; }
  if(yn&&delim==s[yn-1]) zn++;
  if(!zn) R newK(0,0);
  else if(1==zn)
  { if(yn==p1)R enlist(y);
    K z=newK(-3,p1); M(z); memcpy(kC(z),s+p0,p1); y=enlist(z);cd(z); R y; }
  I j=0;K z=newK(0,zn); M(z);
  DO(zn, p0=j; p1=0;
         while(j<yn&&delim!=s[j]){ j++; p1++; }
         K d=newK(-3,p1); M(d,z); memcpy(kC(d),s+p0,p1);kK(z)[i]=d;
         if(j<yn&&delim==s[j]) j++; )
  R z; }

K overDyad(K a, V *p, K b)
{ //TODO: for derived verbs like +/ you can add the sub-pieces in parallel
  O("BEG overeDyad\n");
  V *o=p-1; K (*f)(K,K), k=0; I i=0;
  if(a&&*o==offsetJoin&&!b->t&&!b->n) R 0<a->t?enlist(a):ci(a);
  if(b->t==0) while(i<b->n && !kK(b)[i]->t){++i;}
  if( *o!=offsetJoin || (*o==offsetJoin && i==b->n) )   //only a partial fix for join-over (where all elts of b are lists)
  { if(VA(*o) && (f=DT[(L)*o].alt_funcs.verb_over)) k=f(a,b); }   //k==0 just means not handled.
    //Errors are not set to come from alt_funcs
  P(k,k)
  K u=0,v=0;
  K y=a?v=join(u=enlist(a),b):b; //oom u (TODO: need to unroll to 'x f/y' and 'f/y' to optimize?)
  K z=0,g=0;
  if(yt>0){ z=ci(y); GC; }
  if(*o==(V)0x2a && !a && yt==-1 && yn==0){ z=Ki(1); GC; }
  if(yn == 0){ if(VA(*o))z=LE; GC; } //Some verbs will handle this in alt_funcs
  K c=first(y),d;//mm/o
  //TODO: this reuse of g should be implemented in other adverbs
  if(0>yt)  DO(yn-1, d=c;
                     if(!g)g=newK(ABS(yt),1);
                     memcpy(g->k,((V)y->k)+(i+1)*bp(yt),bp(yt)); c=dv_ex(d,p-1,g);
                     if(2==rc(g)){cd(g);g=0;} cd(d);
                     if(!c) GC; )   //TODO: oom err/mmo unwind above - oom-g
  if(0==yt) DO(yn-1, d=c; c=dv_ex(d,p-1,kK(y)[i+1]); cd(d);
                     if(!c) GC; )   //TODO: err/mmo unwind above
  z=c;
  cleanup:
  if(g)cd(g);
  if(u)cd(u);
  if(v)cd(v);
  R z; }

Z K scanDyad(K a, V *p, K b) //k4 has 1 +\ 2 3 yield 3 6 instead of 1 3 6
{ O("BEG scanDyad\n");
  V *o=p-1; K (*f)(K,K), k=0;
  if(VA(*o) && (f=DT[(L)*o].alt_funcs.verb_scan)) k=f(a,b); //k==0 just means not handled.
    // Errors are not set to come from alt_funcs
  P(k,k)
  if(!a  &&  !(*o<(V)DT_SIZE || 7==(*(K*)*o)->t)  &&  3==(*(K*)*o)->t) R csplit(*(K*)*o,b);
    //note:   !(*o<(V)DT_SIZE || 7==(*(K*)*o)->t)   <==>  f is NOT a function
  K u=0; K y=a?join(u=enlist(a),b):ci(b); cd(u); //oom
  if(yt>0 || yn==0) R y;
  K z=newK(0,yn),c,d,g; kK(z)[0]=first(y);
  if(0>yt)  DO(yn-1, d=kK(z)[i]; g=newK(ABS(yt),1); memcpy(g->k,((V)y->k)+(i+1)*bp(yt),bp(yt)); c=dv_ex(d,p-1,g);
                     cd(g); U(c)  kK(z)[i+1]=c )   //TODO: err/mmo  cd(y) - oom-g
  if(0==yt) DO(yn-1, d=kK(z)[i]; c=dv_ex(d,p-1,kK(y)[i+1]); U(c) kK(z)[i+1]=c ) //TODO: err/mmo  cd(y)
  cd(y);
  //Next line was to fix (there may be a better refactoring):  11+\1 -> 12 (1 K) but  11+\1 2 -> 11 12 14 (3 K)
  if(a&&atomI(b)){ y=z; M(z,u=Ki(1)) M(y,u,z=drop(u,z)) cd(y); cd(u); }
  R collapse(z); }

Z K overMonad(K a, V *p, K b)
{ O("BEG overMonad\n"); O("    sd(a):");sd(a); O("    sd(b):");sd(b);
  if(!p || !*p)O("   !p || !*p\n");
  else
  { I ii;
    if(!fdvx) for(ii=0;p[ii];ii++)
    { O("    oMo p[%lld]: %p",ii,p[ii]);
      if(p[ii]>(V)DT_SIZE)sd(*(K*)p[ii]); else O("\n"); }
    else for(ii=0;p[ii] && ii<fdvx;ii++)
    { O("    oMo p[%lld]: %p",ii,p[ii]);
      if(p[ii]>(V)DT_SIZE)sd(*(K*)p[ii]); else O("\n");
      O("    output limited to %lld\n",fdvx); } }
  fdvx=2; fsf=0; K u=b,c=0; I flag=0,useN=0,n=0,useB=0;
  if(a)
  { if(1==a->t){ useN=1; n=*kI(a); }
    else if(7==a->t || 6==a->t) useB=1; }
  P(n<0,IE)
  if(useN) //n f/x
  { I f=0;
    DO(n, c=dv_ex(0,p-1,u);
          if(b!=u) cd(u);
          if(f && b==c)cd(c);
          f=1; U(u=c) )
    c=c?c:ci(b); }
  else if(useB) // b f/x
  { I t;
    do{ K*aa=&a; fdvx=1;
        O("~BB dv_ex(0,(V)&aa,u)      K dv_ex(K a, V *p, K b) <- K overMonad(K a, V *p, K b)      ");
        K g=dv_ex(0,(V)&aa,u);
        O("#BB overMonad :: dv_ex(0,(V)&aa,u)\n");
        U(g)  t=(g->t==1 && *kI(g)); cd(g);
        if(!t) break;
        c=dv_ex(0,p-1,u);
        if(b!=u) cd(u);
        U(u=c) }while(1);
    c=c?c:ci(b); }
  else   // f/x
  { V*o=p-1;
    if(*o==(V)offsetOver) while(1)
    { if(matchI(b,c) || (u!=b && matchI(u,c)))flag=1;
      if(u!=b) cd(u);
      if(flag) break;
      u=c?c:u; U(c=dv_ex(0,p-1,u))
      if(1==ABS(b->t) && 3==ABS(c->t)) flag=1; }
    else if(*o<(V)DT_SIZE || 7==(*(K*)*o)->t)  //f is a function
    { while(1)
      { if(matchI(b,c) || (u!=b && matchI(u,c)))flag=1;
        if(flag) break;
        if(u!=b) cd(u);
        u=c?c:u; U(c=dv_ex(0,o,u))
        if(1==ABS(b->t) && 3==ABS(c->t)) flag=1; }
      cd(c); R u; }
    else  //f is data
    { a=*(K*)*o;
      if(3==a->t)R cjoin(a,b);
      while(1)   // f/x
      { if(matchI(b,c) || (u!=b && matchI(u,c)))flag=1;
        if(u!=b) cd(u);
        if(flag) break;
        u=c?c:u; U(c=dv_ex(0,o,u))
        if(1==ABS(b->t) && 3==ABS(c->t)) flag=1; } } }
  R c; }

Z K scanMonad(K a, V *p, K b)
{ O("BEG scanMonad\n"); K u=enlist(b),v,w,c=0,d;I flag=0;   //TODO: optimize/memory manage enlists,firsts,reverses here
  U(u);
  I useN=0,n=0,useB=0;
  if(a)
  { if(1 == a->t){ useN=1; n=*kI(a); }
    else if(7==a->t) useB=1; }
  P(n < 0,IE) //mmo
  if(useN) DO(n, U(d=last(u))  c=dv_ex(0,p-1,d); cd(d); U(c)  U(v=enlist(c)) cd(c); u=join(w=u,v); cd(w); cd(v); U(u) )
  else if(useB)
  { I t;
    do{ U(d=last(u))
        K*aa=&a;
        fdvx=1;
        O("~BN dv_ex(0,(V)&aa,d)      K dv_ex(K a, V *p, K b) <- K scanMonad(K a, V *p, K b)      ");
        K g=dv_ex(0,(V)&aa,d);
        O("#BN scanMonad :: dv_ex(0,(V)&aa,d)\n");
        U(g)  t=(1==g->t && *kI(g)); cd(g);
        if(!t){ cd(d); break; }
        c=dv_ex(0,p-1,d); cd(d); U(c)  U(v=enlist(c))  cd(c);
        u=join(w=u,v); cd(w); cd(v); U(u) }while(1); }
  else while(1) //mm/o + error checking   eg if(!c) ...
  { U(d=last(u));
    if(matchI(b,c) || matchI(c,d))flag=1;
    if(!flag && c){ u=join(v=u,w=enlist(c)); cd(v); cd(w); cd(d); d=c; }
    if(interrupted){ interrupted=0; R BE; }
    if(flag){ cd(c); cd(d); break; }
    c=dv_ex(0,p-1,d);cd(d);
    if(!c){ cd(u); R c; } }
  R u; }

Z K each2(K a, V *p, K b)
{ O("BEG each2\n"); O("    sd(a):");sd(a); O("    sd(b):");sd(b);
  if(!p || !*p)O("   !p || !*p\n");
  else
  { I ii;
    if(!fdvx) for(ii=0;p[ii];ii++)
    { O("    dvx p[%lld]: %p",ii,p[ii]);
      if(p[ii]>(V)DT_SIZE) sd(*(K*)p[ii]); else O("\n"); }
    else for(ii=0;p[ii] && ii<fdvx;ii++)
    { O("    dvx p[%lld]: %p",ii,p[ii]);
      if(p[ii]>(V)DT_SIZE) sd(*(K*)p[ii]); else O("\n");
      O("output limited to %lld\n",fdvx); } }
  fdvx=0; I bt=b->t,bn=b->n; K d=0,prnt0=0,grnt0=0;
  if(bt>0)
  { if(a && a->n>0)
    { K z = newK(0,a->n); U(z)
      DO(a->n, O("~EL dv_ex(a,p-1,b)      K dv_ex(K a, V *p, K b) <- K each2(K a, V *p, K b)      ");
               d = dv_ex(kK(a)[i],p-1,b);
               O("#EL each2 :: dv_ex(a,p-1,b)\n"); O("   EL:"); sd(d);
               M(d,z) kK(z)[i]=d )
      z=demote(z);
      if(z->t==1) z->t=-1;
      R z; }
    else
    { O("~EK dv_ex(a,p-1,b)      K dv_ex(K a, V *p, K b) <- K each2(K a, V *p, K b)      ");
      d = dv_ex(a,p-1,b);
      O("#EK each2 :: dv_ex(a,p-1,b)\n"); O("   EK:"); sd(d);
      R d; } }
  else
  { K z=newK(0,bn); U(z)  K g;
    I f=*p==(V)offsetEach && (*(p-1)==(V)offsetEach || *(p-1)==(V)offsetOver || *(p-1)==(V)offsetScan) && *(p-2)<(V)DT_SIZE;
    if(0 >bt) DO(bn, g=newK(ABS(bt),1); M(g,z) memcpy(g->k,((V)b->k)+i*bp(bt),bp(bt));
                     if(f)
                     { O("~EN dv_ex(a,p-1,g)      K dv_ex(K a, V *p, K b) <- K each2(K a, V *p, K b)      ");
                       d=dv_ex(a,p-1,g);
                       O("#EN each2 :: dv_ex(a,p-1,g)\n"); O("   EN:"); sd(d); }
                     else{ O("e2cccc\n"); d=dv_ex(0,p-1,g); }
                     cd(g); M(d,z) kK(z)[i]=d )
    if(0==bt)
    { if(prnt) prnt0=ci(prnt);
      if(grnt) grnt0=ci(grnt);
      DO( bn, if(f)
              { if(a && a->n>1)
                { O("~EJ dv_ex(a,p-1,kK(b)[i])      K dv_ex(K a, V *p, K b) <- K each2(K a, V *p, K b)      i: %lld      ",i);
                  d=dv_ex(kK(a)[i],p-1,kK(b)[i]);
                  O("#EJ each2 :: dv_ex(a,p-1,kK(b)[i])\n"); O("   EJ:"); sd(d); }
                else
                { O("~EH dv_ex(a,p-1,kK(b)[i])      K dv_ex(K a, V *p, K b) <- K each2(K a, V *p, K b)      i: %lld      ",i);
                  d=dv_ex(a,p-1,kK(b)[i]);
                  O("#EH each2 :: dv_ex(a,p-1,kK(b)[i])\n"); O("   EH:"); sd(d); } }
              else
              { if(prnt0){ cd(prnt); prnt=ci(prnt0); }
                if(grnt0){ cd(grnt); grnt=ci(grnt0); }
                O("~EF dv_ex(0,p-1,kK(b)[i])      K dv_ex(K a, V *p, K b) <- K each2(K a, V *p, K b)      i: %lld      ",i);
                d=dv_ex(0,p-1,kK(b)[i]);
                O("#EF each2 :: dv_ex(0,p-1,kK(b)[i])\n"); O("   EF:"); sd(d); }
              if(!d || !z)
              { if(prnt0){ cd(prnt0); prnt0=0; }
                if(grnt0){ cd(grnt0); grnt0=0; } }
              if(grnt && !prnt) prnt=ci(grnt);
              M(d,z) kK(z)[i]=d ) }
    z=demote(z);
    if(z->t==1) z->t=-1;
    if(prnt0){ cd(prnt0); prnt0=0; }
    if(grnt0){ cd(grnt0); grnt0=0; }
    R z; } }

Z K eachright2(K a, V *p, K b)
{ O("BEG eachright2\n"); O("    sd(a):");sd(a); O("    sd(b):");sd(b);
  if(ft3 && !a) R VE;
  if(!p || !*p) O("   !p || !*p\n");
  else
  { I ii;
    if(!fdvx) for(ii=0;p[ii];ii++)
    { O("    dvx p[%lld]: %p",ii,p[ii]);
      if(p[ii]>(V)DT_SIZE)sd(*(K*)p[ii]);
      else O("\n"); }
    else for(ii=0;p[ii] && ii<fdvx;ii++)
    { O("    dvx p[%lld]: %p",ii,p[ii]);
      if(p[ii]>(V)DT_SIZE)sd(*(K*)p[ii]);
      else O("\n");
      O("output limited to %lld\n",fdvx); } }
  fdvx=0; I bt=b->t, bn=b->n;
  if(bt > 0){ O("er2aaaa\n"); dv_ex(a,p-1,b); }
  K z=newK(0,bn),d; K g;
  if(0 >bt) DO(bn, g=newK(ABS(bt),1);                            //TODO: err/mmo oom-g
                   memcpy(g->k,((V)b->k)+i*bp(bt),bp(bt));
                   O("~EG dv_ex(a,p-1,g)      K dv_ex(K a, V *p, K b) <- K eachright2(K a, V *p, K b)      i: %lld      ",i);
                   d=dv_ex(a,p-1,g);
                   O("#EG eachright2 :: dv_ex(a,p-1,g)\n"); O("   EG:"); sd(d);
                   cd(g); U(d) kK(z)[i]=d )
  if(0==bt) DO(bn, O("~DZ dv_ex(a,p-1,kK(b)[i])     K dv_ex(K a, V *p, K b) <- K eachright2(K a, V *p, K b)     i: %lld     ",i);
                   d=dv_ex(a,p-1,kK(b)[i]);
                   O("#DZ eachright2 :: dv_ex(a,p-1,kK(b)[i])\n"); O("   DZ:"); sd(d);
                   U(d)
                   kK(z)[i]=d )
  R demote(z); }

Z K eachleft2(K a, V *p, K b)
{ O("BEG eachleft2\n");
  O("    sd(a):");sd(a); O("    sd(b):");sd(b);
  if(!p || !*p) O("   !p || !*p\n");
  else
  { I ii;
    if(!fdvx) for(ii=0;p[ii];ii++)
    { O("    dvx p[%lld]: %p",ii,p[ii]);
      if(p[ii]>(V)DT_SIZE)sd(*(K*)p[ii]); else O("\n"); }
    else for(ii=0;p[ii] && ii<fdvx;ii++)
    { O("    dvx p[%lld]: %p",ii,p[ii]);
      if(p[ii]>(V)DT_SIZE)sd(*(K*)p[ii]); else O("\n");
      O("output limited to %lld\n",fdvx); } }
  fdvx=0;
  if(!a) R VE;
  I at=a->t, an=a->n;
  if(at>0){ O("el2aaaa\n"); R dv_ex(a,p-1,b); }
  K z=newK(0,an),d,g;
  if(0>at)  DO(an, g=newK(ABS(at),1); memcpy(g->k,((V)a->k)+i*bp(at),bp(at));
                   O("~EO dv_ex(g,p-1,b)      K dv_ex(K a, V *p, K b) <- K eachleft2(K a, V *p, K b)      i: %lld      ",i);
                   d=dv_ex(g,p-1,b);
                   O("#EO eachleft2 :: dv_ex(g,p-1,b)\n"); O("   EO:"); sd(d);
                   cd(g); U(d) kK(z)[i]=d )   //TODO: err/mmo oom-g
  if(0==at) DO(an, O("~EL dv_ex(kK(a)[i],p-1,b)      K dv_ex(K a, V *p, K b) <- K eachleft2(K a, V *p, K b)     i: %lld     ",i);
                   d=dv_ex(kK(a)[i],p-1,b);
                   O("#EL eachleft2 :: dv_ex(kK(a)[i],p-1,b)\n"); O("   EL:"); sd(d);
                   U(d) kK(z)[i]=d )   //TODO: err/mmo
  R demote(z); }

Z K eachpair2(K a, V *p, K b)   //2==k necessary?
{ O("BEG eachpair2\n"); O("    sd(a):");sd(a); O("    sd(b):");sd(b);
  if(!p || !*p) O("   !p || !*p\n");
  else
  { I ii;
    if(!fdvx) for(ii=0;p[ii];ii++)
    { O("    dvx p[%lld]: %p",ii,p[ii]);
      if(p[ii]>(V)DT_SIZE)sd(*(K*)p[ii]); else O("\n"); }
    else for(ii=0;p[ii] && ii<fdvx;ii++)
    { O("    dvx p[%lld]: %p",ii,p[ii]);
      if(p[ii]>(V)DT_SIZE)sd(*(K*)p[ii]); else O("\n");
      O("output limited to %lld\n",fdvx); } }
  V *o=p-1; K (*f)(K,K), k=0;
  O("    *o: %p\n",*o);
  if(VA(*o) && (f=DT[(L)*o].alt_funcs.verb_eachpair)) k=f(a,b);   //k==0 just means not handled.
    //Errors are not set to come from alt_funcs
  O("   k:"); if(k)sd(k); else O(" not k\n");
  P(k,k)  I bt=b->t, bn=b->n; O("   bt: %lld\n",bt);
  if(bt>0) { K u,v; u=enlist(a); M(u,b)  v=join(u,b); cd(u); R v; }
  if(bt<=0)
  { if(bn==0 && !a) R LE;
    else if(bn==0 &&  a) R newK(0,0);   //TODO: memory manage/ optimize in join with null ptr ?
    else if(bn<2) R newK(0,0); }   //TODO: this newK and the above.....does empty list type depend on input?
  K z=newK(0,bn-1),d=0,g,h; U(z)
  if(0 >bt) DO(bn-1, h=newK(ABS(bt),1); g=newK(ABS(bt),1); memcpy(h->k,((V)b->k)+(i)*bp(bt),bp(bt));
                     memcpy(g->k,((V)b->k)+(i+1)*bp(bt),bp(bt));
                     O("~EW dv_ex(g,p-1,h)      K dv_ex(K a, V *p, K b) <- Z K eachpair2(K a, V *p, K b)      i: %lld      ",i);
                     d=dv_ex(g,p-1,h);
                     O("#EW eachpair2 :: dv_ex(g,p-1,h)\n"); O("   EW:"); sd(d);
                     cd(g);cd(h);U(d) kK(z)[i]=d )   //TODO: err/mmo - cd(z) - oom-g-h
  if(0==bt) DO(bn-1, O("~EX dv_ex(kK(b)[i+1],p-1,kK(b)[i])      K dv_ex(K a, V *p, K b) <- Z K eachpair2(K a, V *p, K b)      i: %lld      ",i);
                     d=dv_ex(kK(b)[i+1],p-1,kK(b)[i]);
                     O("#EX eachpair2 :: dv_ex(kK(b)[i+1],p-1,kK(b)[i])\n"); O("   EX:"); sd(d);
                     U(d) kK(z)[i]=d )   //TODO: err/mmo - cd(z)
  z=demote(z);
  if(a){ K u,v; u=enlist(a); M(u,z)  v=join(u,z); cd(u); cd(z); R v; }
  R z; }

K dv_ex(K a, V *p, K b)
{ //TODO: Try (?) and grow adverb results as vectors before devolving to 0-type
  //TODO: consider merging dv_ex with vf_ex
  O("BEG dv_ex\n"); O("    sd(a):");sd(a); O("    sd(b):");sd(b);
  if(!p || !*p) O("   !p || !*p\n");
  else
  { I ii;
    if(!fdvx) for(ii=0;p[ii];ii++)
    { O("    dvx p[%lld]: %p",ii,p[ii]);
      if(p[ii]>(V)DT_SIZE)sd(*(K*)p[ii]); else O("\n"); }
    else for(ii=0;p[ii] && ii<fdvx;ii++)
    { O("    dvx p[%lld]: %p",ii,p[ii]);
      if(p[ii]>(V)DT_SIZE)sd(*(K*)p[ii]); else O("\n");
      O("output limited to %lld\n",fdvx); } }
  fdvx=0;
  if(!p || !*p) R 0; //TODO: ???
  U(b)  V *o=p-1;
  //Arity of V?A_1...A_n-1 for X V?A_1...A_n Y; 0 for X Y, X A Y
  I k=0; K w;
  if(*p==(V)offsetScan && *o>(V)DT_SIZE)
  { w=*(K*)*o;
    if(7==w->t && 3==kVC(w)->n && kV(kVC(w))[0]==(V)0x16 && kV(kVC(w))[1]==(V)offsetScan) k=1; }
  if(k==0) k=adverbClass(*p)?adverbClass(*o)?1:valence(*o):valence(*p); //also t7 basic
  V adverb=*p; //TODO: Implement adverb "Error Reports" error checking from manual
  //k>2 --- ??? bound for special verbs ?.@ , etc.  ??? k=2 ??? valence is weird here
  //!(adver...  ---- added to let f/[;;;] through
  //if(k>2 && !(adverbClass(*p) && !VA(*o)))k=2;
  if(k>2)k=2;
  if(*p==(V)offsetEach && k==1 && a && b && ((a->t>0 && a->t<5 && b->t>0 && b->t<5) || (a->t==-1 &&  b->t==-1))) k=2;
  if(2==k || (k==0 && (UI)adverb==offsetScan && (0==(*(K*)p[-1])->t || 3==(*(K*)p[-1])->t)))
  { if ((UI)adverb == offsetOver) R overDyad(a, p, b);
    if ((UI)adverb == offsetScan) R scanDyad(a, p, b);
    if ((UI)adverb == offsetEach)
    { if(!a) adverb = (V)offsetEachright;
      else if(a->t <= 0 && b->t <= 0 && a->n != b->n) R LE;
      else if(a->t > 0 && b->t > 0)
      { O("~EM dv_ex(a,p-1,b)      K dv_ex(K a, V *p, K b) <- K dv_ex(K a, V *p, K b)      ");
        K zz = dv_ex(a,p-1,b);
        O("#EM dv_ex :: dv_ex(a,p-1,b)\n"); O("   EM:");sd(zz);
        R zz; }
      else if (a->t > 0) adverb = (V)offsetEachright;
      else if(b->t > 0) adverb = (V)offsetEachleft;
      else        //a and b both lists/vectors of size an
      { a=promote(a); b=promote(b); M(a,b)
        K z=newK(0,a->n), k; M(z,a,b)
        DO(a->n, O("~EI dv_ex(kK(a)[i],p-1,kK(b)[i])     K dv_ex(K a, V *p, K b) <- K dv_ex(K a, V *p, K b)     i: %lld     ",i);
                 k=dv_ex(kK(a)[i],p-1,kK(b)[i]);
                 O("#EI dv_ex :: dv_ex(kK(a)[i],p-1,kK(b)[i])\n"); O("   EI:");sd(k);
                 M(k,z,a,b)
                 kK(z)[i]=k )
        cd(a); cd(b);
        R demote(z); } } }
  else if(2>k)
  { if((UI)adverb == offsetOver)
    { if(!fom)
      { O("~BA overMonad(a, p, b)      K overMonad(K a, V *p, K b) <- K dv_ex(K a, V *p, K b)      ");
        K zz=overMonad(a, p, b);
        O("#BA dv_ex :: overMonad(a, p, b)\n");
        R zz; }
      else R overMonad(kK(b)[0],p,kK(b)[1]); }
    if ((UI)adverb == offsetScan)
    { O("~BC scanMonad(a, p, b)      K scanMonad(K a, V *p, K b) <- K dv_ex(K a, V *p, K b)      ");
      K zz=scanMonad(a, p, b);
      O("#BC dv_ex :: scanMonad(a, p, b)\n");
      R zz; }
    if ((UI)adverb == offsetEach)
    { O("~EE each2(a, p, b);      K each2(K a, V *p, K b) <- K dv_ex(K a, V *p, K b)      ");
      K zz=each2(a, p, b);
      O("#EE dv_ex :: each2(a, p, b)\n");
      R zz; } }
  if((UI)adverb == offsetEachright)
  { O("~DY eachright2(a, p, b)      K eachright2(K a, V *p, K b) <- K dv_ex(K a, V *p, K b)      ");
    K zz=eachright2(a, p, b);
    O("#DY dv_ex :: eachright2(a, p, b)\n");
    R zz; }
  if((UI)adverb == offsetEachleft)
  { O("~DF eachleft2(a, p, b)      K eachleft2(K a, V *p, K b) <- K dv_ex(K a, V *p, K b)      ");
    K zz=eachleft2(a, p, b);
    O("#DF dv_ex :: eachleft2(a, p, b)\n");
    R zz; }
  if((UI)adverb==offsetEachpair)
  { O("~EV eachpair2(a, p, b)      Z K eachpair2(K a, V *p, K b) <- K dv_ex(K a, V *p, K b)      ");
    K zz=eachpair2(a, p, b);
    O("#EV dv_ex :: eachpair2(a, p, b)\n"); O("   EV:"); if(zz)sd(zz); else O(" not zz\n");
    R zz; }
  I gn=0;
  if(valence(*p)>=2 && a && b) gn=2;
  else if(a)     //issue #296
  { V q[4]; q[0]=&a; q[1]=(V)1; q[2]=&b; q[3]=(V)0; K u=ex0(&q[0],0,2); q[0]=(V)*p; q[1]=(V)0; K v=ex0(&q[0],u,1); cd(u); R v; }
  else if(b) gn=1;
  K g=newK(0,gn); U(g);
  if(gn>1) kK(g)[1]=b;
  if(gn>0) kK(g)[0]=a?a:b;
  K tmp; I flag=0;
  if((UI)*p>DT_SIZE && b->n)
  { V*p1=*p;
    if((UI)*p1>DT_SIZE)
    { K p2=*p1;
      if(7!=p2->t && -1!=p2->t && 5!=p2->t) flag=1; } }
  if(flag)
  { O("~CC vf_ex(*p,b)      K vf_ex(V q, K g) <- K dv_ex(K a, V *p, K b)      ");
    tmp=vf_ex(*p,b);
    O("#CC dv_ex :: vf_ex(*p,b)\n"); }
  else
  { if(stk>2e6) R kerr("stack"); stk++;
    //        **** Next 2 lines removed to fix #432. They may be needed when returning to #244 and #247
    //  if(encp && (encp!=2 || (strchr(kC(kK(encf)[CODE]),"z"[0]))) && encp!=3 && DT_SIZE<(UI)*p)tmp=vf_ex(&encf,g);
    //  else
    O("\nsd_(prnt,2):");sd_(prnt,2);O("\n");
    O("~AM vf_ex(*p,g)      K vf_ex(V q, K g) <- K dv_ex(K a, V *p, K b)      ");
    tmp=vf_ex(*p,g);
    O("#AM dv_ex :: vf_ex(*p,g)\n"); O("   AM: %p",&tmp);sd_(tmp,2);
    stk--; if(grnt && !prnt)prnt=ci(grnt); }
  memset(kK(g),0,g->n*sizeof(K)); cd(g); //Special privileges here...don't ci() members beforehand
  R tmp; }

//1. Use PARAMETER list (or XYZ tuple) to merge CONJ and ARGS-G into LOCAL-DICT-TREE
//2. Execute as normal, except
//   a. The LOCAL-DICT-TREE acts as the "KTREE"
//   b. Double-colon assignment :: adds to the dictionary in CONTeXT

//Note:  a:{c::1}       <--- even without executing c is set (_n) in context
//       a:{{d::1}}     <--- d set in context (_n, if executed then 1)
//       a:{e:1 {e::2}} <--- e not set

//  X1   local vars
//  X2   _f self-reference
//  X3   a::2 global assignment
//  X4   {[a;b;c]} args
//  X5   {x+y} implicit args
//  X6   execution {}[2]
//  X7   assigned variables wholly local: {b} (global/context) vs. {b:2} (local)
//  X8   projection {}[1;;3] --- 7-{1,2,3} types. Verb projections come for free
//   9   proper sub-functions (hint is the non-null f passed to wd_(). Inherit/copy active dict to kV()[LOCAL] )
//       Arthur: "subfunctions are just projections,
//         eg  c:{[f;g]{f g x}} composition d:{[f;g]{[f;g;x]f g x}[f;g]} composition c[-:;%:] 3 ; d[-:;%:] 3
//  X10  {  :x  } early return
//  X11  Reusably compiled

//For -7 (7-0) CONJ is unexecuted brackets. For 7-{1,2,3} it's 0-type with NULLs
//K3.2 Bug - {b:1_,/";a",/:$a:!x; "{[",b,"]a3}[" ,(1_,/";",/:$a ),"]" }
//  67890  --> Sometimes works, sometimes stack error, sometimes crash

K vf_ex(V q, K g)
{ O("BEG vf_ex\n");
  K tc=0;
  if(q>(V)DT_SIZE){ O("   sd_((K)(*(V*)q,2):");sd_((K)(*(V*)q),2); }
  else O("   q:         %p\n",q);
  O("   sd(g):");sd(g);
  if(interrupted){ interrupted=0; R BE; }
  if(!g)R 0;     //??? R w converted to type7...or ?
  K z=0; U(g=promote(g))  I gn=g->n, k=sva(q), n=-1, j=0;
  if(!k&&!(*(V*)q)) { cd(g); R 0; }              // (2="2") 2 err
  n=valence(q); I ee=0;
  if(q>(V)DT_SIZE)
  { K h=*(K*)q;
    if(h->t==7)
    { if(h->n==1)
      { if(kK(h)[CODE] && (UI)kK(kK(h)[CODE])[0]>DT_SIZE)
        { if(kK(h)[CODE]->n==3 && (*(K*)(kS(kK(h)[CODE])[0]))->t==0 ) { z=dot(*(K*)(kS(kK(h)[CODE])[0]),g); GC; }
          if((UI)kK(kK(h)[CODE])[1]==0x3a && g->t==0 ){ z=dot( *(K*)(kS(kK(h)[CODE])[0]), kK(g)[0] ); GC; } }
        if((V)kS(kK(h)[CODE])[0]>(V)DT_SIZE && (*(K*)kS(kK(h)[CODE])[0])->t==7){ n=2; ee=1; } }
      if(-4==(kK(h)[2])->t && 2==(kK(h)[2])->n && kV(kK(h)[2])[0]==(V)0x3a && 0==g->t )
      { if(NULL==kV(g)[0]){ z=ci(*(K*)q); kV(z)[5]=(V)ci(g); GC; }
        if(6==kK(g)[0]->t){ z=ci(*(K*)q); kV(z)[5]=(V)ci(kK(z)[4]); kK(z)[2][0]=kK(z)[2][1]; ci(kK(z)[2]); GC; } } } }
  if(ee && !kV(g)[0] && kV(g)[1]) fom=1;
  if( ((k || (*(K*)q)->t==7) && ( ((UI)q<DT_SIZE || (*(V*)q))  && gn>n && !(!n && 1>=gn))) || (ee && kV(g)[0] && kV(g)[1]) )
  { if(kK(g)[0]==NULL) { O("raise valence-1\n"); VE; GC; }
    if(3!=kK(g)[0]->t || 1==(*(K*)q)->n || kK(g)[1]==NULL)
    { if(g->t==0  &&  gn==2  &&  kK(*(K*)q)[CODE]->t==-4  &&  (V)kS(kK(*(K*)q)[CODE])[0]>(V)DT_SIZE
      &&  (*(K*)kS(kK(*(K*)q)[CODE])[0])->t==7 )
      { V w[2]; w[0]=(V)kS(kK(*(K*)q)[CODE])[0]; w[1]=(V)offsetOver;
        O("~BM overMonad(kK(g)[0], &w[1], kK(g)[1])      K overMonad(K a, V *p, K b) <- K vf_ex(V q, K g)      ");
        fdvx=1; z=overMonad(kK(g)[0], &w[1], kK(g)[1]);
        O("#BM vf_ex :: overMonad(kK(g)[0], &w[1], kK(g)[1])\n");
        GC; }
      else { O("raise valence-2\n"); VE; GC; } }
    else{ g=enlist(collapse(g)); gn=g->n; cd(kK(g)[0]); } }
  I argc=0; DO(gn, if(kK(g)[i]) argc++ )
  K a=0,b=0,c=0,d=0;
  if(gn>0) a=kK(g)[0];
  if(gn>1) b=kK(g)[1];
  if(gn>2) c=kK(g)[2];
  if(gn>3) d=kK(g)[3];
  //valence overloaded verbs
  if(gn>2 && (q==offsetWhat || q==offsetSSR)) { z=(q==offsetWhat?what_triadic:_ssr)(a,b,c); GC; }
  if(gn>2 && (q==offsetAt   || q==offsetDot ))
  { if(q==offsetAt)
    { O("~CG at_tetradic(a,b,c,d)      K at_tetradic(K a, K b, K c, K y) <- K vf_ex(V q, K g)      ");
      z=at_tetradic(a,b,c,d);
      O("#CG vf_ex :: at_tetradic(a,b,c,d)\n"); O("   CG:");sd(z); }
    else
    { O("~CH dot_tetradic(a,b,c,d)      K dot_tetradic(K a, K b, K c, K y) <- K vf_ex(V q, K g)      ");
      z=dot_tetradic(a,b,c,d);
      O("#CH vf_ex :: dot_tetradic(a,b,c,d)\n"); O("   CH:");sd(z); }
    GC; }     //common verbs
  if(2==k && a && b)
  { fnc=DT[(L)q].text;
    if(fnci<127){ fncp[fnci]=q; fnci++; }
    if(cls && a->t==6) z=((K(*)(K,K))DT[(L)q].func)(cls,b);
    else
    { O("   vf_ex  ELSE --- z=((K(*)(K,K))DT[(L)q].func)(a,b);    (L)q:%lld---",(L)q);
      fdvx=1;
      if(22==(L)q) O("plus\n");
      if(24==(L)q) O("minus\n");
      if(42==(L)q) O("equals\n");
      if(52==(L)q) O("join\n");
      if(62==(L)q) O("_0d\n");
      z=((K(*)(K,K))DT[(L)q].func)(a,b); }
    GC; }
  //? (+).1 -> err ; {[a;b]a+b} 1 -> err
  if(2==k && !a){ VE; GC; } //Reachable? Projection?
  //Reachable: try "#'(1;1 2)" (the # is dyadic not monadic #:). We return projection (#[1;],#[1 2;]), K3.2 gives valence error
  if((2==k || q==offsetSSR) && !b)
  { K v = Kv(), kb = newK(-4,2); M(v,kb)
    kK(kb)[0]=q;
    kK(kb)[1]=0;
    kV(v)[CODE]=kb;
    O("~AV vf_ex(&v,g)      vf_ex(V q, K g) <- vf_ex(V q, K g)      ");
    z=vf_ex(&v,g); //Punt and let another call to vf_ex handle projecting. Probably could build the projected-verb here instead.
    O("#AV vf_ex :: vf_ex(&v,g)\n"); O("   AV:");sd(z);
    cd(v); GC; } //old comment: Projection? '(1+)' -> 1+  Build 7-verb? (Refactor with 'c' from []+: ex and maybe another place?)
  //+:[a] ... +:[a;b] handled above (valence err)
  if(1==k && a){ z= ((K(*)(K))DT[(L)q].func)(a); GC; }
  if(1==k && !a) GC; //Reachable? Projection?
  //Functions  7-{1,2,3}
  K f=(K) (*(V*)q); I ft=f->t;
  if(ft != 7)
  { //z=g?dot(f,g):f; GC;}//TODO: check this for !a and for dict. ternary is superfluous since g nonzero?
    if(g)
    { O("~BO dot(f,g)      K dot(K a, K b) <- K vf_ex(V q, K g)      ");
      z=dot(f,g);
      O("#BO vf_ex :: dot(f,g)\n"); O("   BO:");sd(z); }
    else z=f;
    GC; }
  I t=f->n;
  if(-1==n) n=valence(f); //don't compute twice
  //Projecting simple verbs works.
  // The ex 7-type wrapper will catch simple verbs and they will make it back here. (except in above 2==k && a && !b case?)
  K o=kV(f)[CODE]; K p=kV(f)[PARAMS]; K s=kV(f)[LOCALS]; K r=kV(f)[CONJ];
  I special = 1==t && !r && (offsetAt==*kW(f) || offsetDot==*kW(f) || offsetWhat==*kW(f)); //_ssr is not special (not overloaded)
  if(o->t!=-3)
  { I ii=o->n-2; //not the terminating NULL, but the entry before
    V*u=(V*) kK(o)+ii;
    if(2==n && 1==adverbClass(*u) ) n=gn; }   //   / \ '  but maybe should exclude '
  if(kK(*(K*)q)[CODE]->n==3 && offsetWhat==(V)kV(kK(*(K*)q)[CODE])[1]){ z=what(*(K*)kV(kK(*(K*)q)[CODE])[0],*(K*)kV(g)); GC; }
  if(n && (argc<gn || (gn<n && (!special||gn<=1) ))) //Project. Move this ahead of verbs when finished
  { z=kclone(f); //Is this an opportunity to capture an under-referenced function?
                 //Consider if it could be in use as part of assignment, etc.
    if(!z) GC;
    I ae=0; K*m=(K*)kV(z)+CONJ;
    if(special && gn!=4) n=2; // .'"98" cases. allows a:.[+] then a 2 3  (. is forced 2-adic & not .[;;;]) is this a kluge?
    if(3<kK(z)[CODE]->n  && (V*)kK(kK(z)[CODE])[1]==(V)offsetAt && (V*)kK(kK(z)[CODE])[2]==(V)offsetEach){ ae=1; n=1; }
    if(!*m) *m=newK(0,n);
    if(!*m){ cd(z); GC; }
    K *q=kK(*m);
    DO((*m)->n, if(!q[i] && j<gn) q[i]=ci(kK(g)[j++]) )
    if(ae)
    { V w[5]; w[0]=(V)kS(kK(z)[CODE])[0]; w[1]=(V)offsetAt; w[2]=(V)offsetEach; w[3]=(V)kK(kK(z)[CONJ]); w[4]=0;
      O("~CD ex2(&w[0],0)      ex2(V*v, K k) <- vf_ex(V q, K g)      \n");
      K zz=ex2(&w[0],0);
      O("#CD vf_ex :: ex2(&w[0],0)\n");
      cd(g); cd(z); R zz; }
    GC; }   //K3.2 Projection {[a;b;c]}[;1][1;] returns self. Indicates different (7-0 style?) method
  V v;K tree;
  SW(t)
  { CS( 1, //Executing a derived verb such as 1+2* or (+/)
           if(!r) {z=ex2(kW(f),g);GC;} //No CONJ
           K m=newK(0,r->n);           //CONJ
           if(!m)GC;
           K *q=kK(m);
           DO(m->n, q[i]=ci(kK(r)[i]); if(!q[i] && j<gn) q[i]=ci(kK(g)[j++]))
           if(prj) { V*w=&kW(f)[1]; z=bv_ex(w,m); }
           else
           { O("~CE ex2(kW(f),m)      ex2(V*v, K k) <- vf_ex(V q, K g)      ");
             z=ex2(kW(f),m);
             O("#CE vf_ex :: ex2(kW(f),m)\n"); }
           cd(m); )
    CS( 2, //Executing a dynamically loaded library function from 2:
           v=kW(f)[1];
           K a[7]; DO(7,a[i]=0)
           if(r)memcpy(a,kK(r),MIN(r->n,7)*sizeof(V)); //MIN(.,7) is superfluous
           DO(7, if(!a[i] && j<gn) a[i]=kK(g)[j++] )
           SW(n)
           { CS(0,z=((K(*)())v)())
             CS(1,z=((K(*)(K))v)(a[0]))
             CS(2,z=((K(*)(K,K))v)(a[0],a[1]))
             CS(3,z=((K(*)(K,K,K))v)(a[0],a[1],a[2]))
             CS(4,z=((K(*)(K,K,K,K))v)(a[0],a[1],a[2],a[3]))
             CS(5,z=((K(*)(K,K,K,K,K))v)(a[0],a[1],a[2],a[3],a[4]))
             CS(6,z=((K(*)(K,K,K,K,K,K))v)(a[0],a[1],a[2],a[3],a[4],a[5]))
             CS(7,z=((K(*)(K,K,K,K,K,K,K))v)(a[0],a[1],a[2],a[3],a[4],a[5],a[6])) } )
    CS( 3, //Executing a {} character function such as {1+1}, {x+y+z-1}, or {[a;b] a+b}
           if(((L)kV(f)[DEPTH]) > 500){ kerr("stack"); GC; }
           if(stk > 2e6){ kerr("stack"); GC; }
           stk++;
           I j=0; K*e; K fw;
           if(!(tree=kV(f)[CACHE_TREE]))   //could merge this and and CACHE_WD check by duplicating the arg merge DO
           { O("BEG build tree from locals & params\n");
             O("earlier:    K f=(K)(*(V*)q);   K o=kV(f)[CODE]; K p=kV(f)[PARAMS]; K s=kV(f)[LOCALS]; K r=kV(f)[CONJ];\n");
             O("  3=locals  4=params\n");
             O("sd(f):");sd(f);
             tree=newK(5,p->n+s->n); if(!tree) {stk--; GC;}   //note: cleanup is unusual -- could turn into double labels
             O("tree1: %p",&tree);sd_(tree,2);
             DO(tree->n, if(!(kK(tree)[i]=newK(0,3))){ cd(tree); stk--; GC; } )   //shallow dict copy -- dictionary entry pool?
             O("tree2: %p",&tree);sd_(tree,2);
             DO(tree->n, DO2(3,  kK(DI(tree,i))[j] = ci(kK((i<p->n?DI(p,i):DI(s,i-p->n)))[j]) ) )   //shallow copy
             O("tree3: %p",&tree);sd_(tree,2);
             kV(f)[CACHE_TREE]=tree; }
           if(fsf)
           { K j0=dot_monadic(kV(prnt)[LOCALS]); K j1=dot_monadic(kV(prnt)[CACHE_TREE]);
             K j2=join(ci(j0),j1); cd(j0); cd(kV(prnt)[CACHE_TREE]); kV(prnt)[CACHE_TREE]=dot_monadic(j2);
             cd(j0); cd(j1); cd(j2); tree=kV(prnt)[CACHE_TREE];
             O("tree4 (fsf): %p",&tree);sd_(tree,2);
             cd(kV(prnt)[CACHE_WD]); kV(prnt)[CACHE_WD]=0; }
           O("\ntree5a: sd_(tree,2):");sd_(tree,2);O("\n"); O("p->n: %lld\n",p->n);
           DO(p->n, e=EVP(DI(tree,i)); cd(*e); *e=0;
                    if(r && i<r->n) *e=ci(kK(r)[i]);
                    if(!*e && j<g->n) *e=ci(kK(g)[j++]) )   //merge in: CONJ with function args
           O("\ntree5b: sd_(tree,2):");sd_(tree,2);
           O("\n=======================================================================================\n");
           O("RRR-1\n");
           fw=kV(f)[CACHE_WD]; I t=0;
           if(!fw || (t=(UI)kS(kK(fw)[CODE])[0]>DT_SIZE || (UI)kS(kK(fw)[CODE])[1]>DT_SIZE) )
           { if(t) cd(kV(f)[CACHE_WD]);
             K fc = kclone(f); //clone the function to pass for _f
             cd(kV(fc)[CONJ]); kV(fc)[CONJ]=0;
             kV(fc)[DEPTH]++;
             I tt=0; I ttt=0; I i=0; for(i=0;i<(o->n)-3;++i)
             { if(kC(o)[i]=='{')
               { tt=1;
                 if(kC(o)[i+1]==':'){ ttt=1; break; } } }
             if(!ttt && (!grnt || tt || kC(o)[0]=='['))
             { O("&tree6: %p   sd_(tree6,2):",&tree);sd_(tree,2);
               O("~AW wd_(kC(o),o->n,&tree,fc)      K wd_(S s, int n, K *dict, K func) <- K vf_ex(V q, K g)      ");
               fw=wd_(kC(o),o->n,&tree,fc);
               O("#AW vf_ex :: wd_(kC(o),o->n,&tree,fc)     RRR-2\n");
               O("   AW:   dict-aft-AW:");sd(tree);
               O("sd_(fw,2):     %p",&fw);sd_(fw,2); }
             else
             { tc=kclone(tree);
               O("&tc: %p   sd_(tc,2);",&tc);sd_(tc,2);
               O("~EP wd_(kC(o),o->n,&tc,fc)      K wd_(S s, int n, K *dict, K func) <- K vf_ex(V q, K g)      ");
               fw=wd_(kC(o),o->n,&tc,fc);
               O("#EP vf_ex :: wd_(kC(o),o->n,&tc,fc)\n");
               O("   EP:   dict-aft-EP:");sd(tree);
               O("sd_(fw,2):     %p",&fw);sd_(fw,2); }
             kV(f)[CACHE_WD]=fw; cd(fc); }
           if(stk1>1e3) { cd(g); kerr("stack"); R _n(); }
           ci(fw); stk1++;
           O("~AN ex(fw)      K ex(K a) <- K vf_ex(V q, K g)      RRR-3      ");
           z=ex(fw);
           O("#AN vf_ex :: ex(fw)     RRR-4\n"); O("   AN: %p",&z);sd(z);
           O("sd(fw):");sd(fw);
           stk1--;
           DO(p->n, e=EVP(DI(tree,i)); cd(*e); *e=0; )
           stk--; ) }
  if(encp==2)
  { I ff=0;      // Access the parameters of an enclosing function
    if(z && z->t==7 && z->n==3 && kV(z)[CODE] && strchr(kC(kK(z)[CODE]),"z"[0]) && kV(z)[PARAMS] && kK(z)[PARAMS]->n)
    { ff=1; DO(kK(z)[PARAMS]->n, if(!strcmp(*kS(kK(kK(kK(z)[PARAMS])[i])[0]),"z")) { ff=0; break; } ) }
    if(ff)
    { K d=kK(kK(KTREE)[0])[1]; K w=0;
      DO(d->n, if(!strcmp(*kS(kK(kK(d)[i])[0]),"z")) { w=kclone(kK(d)[i]); break; } )
      if(w)
      { K p=kK(g)[0]; cd(kK(w)[1]); kK(w)[1]=kclone(p); K we=enlist(w);
        K j0=dot_monadic(kK(z)[CACHE_TREE]); K j2=join(ci(j0),we); cd(j0);
        cd(kK(z)[CACHE_TREE]); kK(z)[CACHE_TREE]=dot_monadic(j2); cd(w); cd(we); cd(j0); cd(j2); encp=3; } } }
  if(encp==1)
  { I ff=0;
    if(z && z->t==7 && z->n==3 && kV(z)[CODE] && strchr(kC(kK(z)[CODE]),"y"[0]) && kV(z)[PARAMS] && kK(z)[PARAMS]->n)
    { ff=1; DO(kK(z)[PARAMS]->n, if(!strcmp(*kS(kK(kK(kK(z)[PARAMS])[i])[0]),"y")) { ff=0; break; } ) }
    if(ff)
    { K d=kK(kK(KTREE)[0])[1]; K y=0;
      if(6!=d->t && !(5==d->t && 6==kK(kK(d)[0])[1]->t))
         DO(d->n, if(!strcmp(*kS(kK(kK(d)[i])[0]),"y")){ y=kclone(kK(d)[i]); break; } )
      else R NYI;
      if(y)
      { K p=kK(g)[0]; cd(kK(y)[1]); kK(y)[1]=kclone(p); K ye=enlist(y);
        K j0=dot_monadic(kK(z)[CACHE_TREE]); K j2=join(ci(j0),ye); cd(j0);
        cd(kK(z)[CACHE_TREE]); kK(z)[CACHE_TREE]=dot_monadic(j2); cd(y); cd(ye); cd(j0); cd(j2); encp=2; } } }
  if(encp==0)
  { I ff=0;
    if(z && z->t==7 && z->n==3 && kV(z)[CODE] && strchr(kC(kK(z)[CODE]),"x"[0]) && kV(z)[PARAMS] && kK(z)[PARAMS]->n)
    { ff=1; DO(kK(z)[PARAMS]->n, if(!strcmp(*kS(kK(kK(kK(z)[PARAMS])[i])[0]),"x")) { ff=0; break; } ) }
    if(ff)
    { K xx=newK(4,1); *kK(xx)=(V)sp("x");
      K x=newK(0,3); kK(x)[0]=xx; kK(x)[1]=(K)_n(); kK(x)[2]=(K)_n();
      K p=kK(g)[0]; cd(kK(x)[1]); kK(x)[1]=kclone(p); K xe=enlist(x);
      K j0=dot_monadic(kK(z)[CACHE_TREE]); K j2=join(ci(j0),xe); cd(j0);
      cd(kK(z)[CACHE_TREE]); kK(z)[CACHE_TREE]=dot_monadic(j2); cd(x); cd(xe); cd(j0); cd(j2); encp=1; } }
  cleanup:
  cd(g); cd(tc);  //O("   sd(z): ");sd(z);
  R z; }

Z V ex_(V a, I r)//Expand wd()->7-0 types, expand and evaluate brackets.  Could probably fold ex0 into this function
{ O("BEG ex_\n");
  K x,y=0,z,tmp;
  O("   r:%lld",r);
  if(!a || VA(a) || bk(a)){ O("    R a: %p\n",a); R a; }
  O("   sd(x=*(K*)a):  ");sd(*(K*)a);
  if(!(x=*(K*)a) || 7!=xt || (0<xn && xn<4)){ O("    R ci(x)\n"); R ci(x); }   //assert xn>=4 -> conditionals or similar
  r=xn<4?r:xn;   //suggests maybe r should be stored on 7type itself
  if(kV(x)[CONJ])
  { O("kV(x)[CONJ]\n");
    if((tmp=*(K*)(kV(x)+CONJ))) if(offsetColon==*kW(tmp) && (UI)*(kW(tmp)+1)>DT_SIZE)fer=1;
    O("~BG ex_(kV(x)+CONJ,2)      V ex_(V a, I r) <- V ex_(V a, I r)      ");
    y=ex_(kV(x)+CONJ,2);   //Use 0-type with NULLS if passing to function
    O("#BG ex_ :: ex_(kV(x)+CONJ,2)\n");
    U(y);
    if(y->t == 0 && y->n==0){ cd(y); y=_n(); }
    if(fer>0 && !fCheck){ O("   R y\n"); R y; } }
  O("~AB ex0(kW(x),y,r)      K ex0(V*v,K k,I r) <- V ex_(V a, I r)      ");
  z=ex0(kW(x),y,r);   //eval wd()
  O("#AB ex_ :: ex0(kW(x),y,r)  r:%lld   ",r); O("y:"); if(y)sd(y); else O(" was 0\n");
  O("   AB: %p",&z);sd(z);
  cd(y); R z; }

K ex(K a)   //Input is (usually, but not always) 7-0 type from wd()
{  O("BEG ex \n");
  O("sd_(a,2):");sd_(a,2);O("\n");
  O("exA %lld *****************************************************************************\n\n",++cnte);
  U(a); if(a->t==7 && kVC(a)>(K)DT_SIZE && 7==kVC(a)->t && 6==kVC(a)->n)fwh=1;
  if(a->t==7)
  { if(prnt==0)
    { if(kW(a)[1]==offsetColon && kW(a)[2]!=offset3m) fam=0;
      if(kVC(a)->n>3)
      { I i=3;
        while(kW(a)[i]) {if(kW(a)[i++]==(V)0x1)fam=1; if(kW(a)[i-1]==offsetColon && kW(a)[i]!=offset3m)fam=0;}
        if(!fCheck && i>2)
        { I j,k=0;
          for(j=i-1; j>0 && k<10; j--)
            if(kW(a)[j]<(V)DT_SIZE && kW(a)[j]>(V)1)
            { cdp[k]=(C)*DT[(I)kW(a)[j]].text;
              k++; } } } } }
  else fam=1;
  O("~AA ex_(&a,0)      V ex_(V a, I r) <- K ex(K a)    ");
  K z=ex_(&a,0); cd(a);
  O("#AA ex :: ex_(&a,0)\n"); O("   AA: %p",&z);sd_(z,2);
  if(fer==1) fer=fer1=0;
  fwh=stk=stk1=prj=prj2=fsf=0;
  if(prnt) cd(prnt);
  prnt=0;
  O("\nexB %lld  -- &z  sd_(z,2):\n %p",cnte--,&z); sd_(z,2); O("\n");
  R z; }

Z K ex0(V*v,K k,I r) //r: {0,1,2} -> {code, (code), [code]}
{ //Reverse execution/return multiple (paren not function or script) "list notation"  {4,5,6,7} -> {:,if,while,do}
  O("BEG ex0\n"); O("     r: %lld",r); O("     sd(k):");sd(k);
  I ii; for(ii=0;v[ii];ii++)
        { O("     ex0 v[%lld]: %p",ii,v[ii]);
          if(v[ii]>(V)DT_SIZE)sd(*(K*)v[ii]); else O("\n"); }  //Rex0
  I n=0, e=1, i,a,b;
  while(v[n]) if(bk(v[n++])) e++;
  b=e>1; K z=0, x;
  SW(r)
  { CS(0, for(i=-1;i<n;i++)    //c:9;a+b;c:1
            if(-1==i||bk(v[i]))
            { if(z==0)O("     z==0 (no Asd(z))\n"); else {O("Asd(z):");sd(z);}
              cd(z); frg++;
              O("~AC ex1(v+1+i,0,&i,n,1)      K ex1(V*w, K k, I *i, I n, I f) <- K ex0(V*v, K k, I r)      i: %lld     ",i);
              x=ex1(v+1+i,0,&i,n,1);
              O("#AC ex0 :: ex1(v+1+i,0,&i,n,1)\n"); O("   AC: %p",&x);sd(x);
              O("Bsd(z):");sd(z);
              frg--;
              if(!frg)
              { encp=0;
                if(encf){ cd(encf); encf=0; }
                if(grnt){ cd(grnt); grnt=0; } }
              O("Csd(z):");sd(z);
              U(x)  z=bk(x)?_n():x;
              O("Dsd(z):");sd(z);
              if(fer>0 && !fCheck)R z;
              if(grnt && (!prnt || rc(prnt)==2))
              { if(prnt)cd(prnt);
                prnt=ci(grnt); } } )
    CS(4, for(i=-1;i<n;i++)
            if(-1==i||bk(v[i]))
            { O("~AO ex1(v+1+i,0,&i,n,1) <- ex0      ");
              U(x=ex1(v+1+i,0,&i,n,1))
              O("#AO ex0 :: ex1(v+1+i,0,&i,n,1)\n"); O("...O:");sd(x);
              if(fer>0 && !fCheck)R x;
              x=bk(x)?_n():x; while(++i<n&&!bk(v[i])); if(i==n) R x;
              z=delist(x); if(ABS(z->t)!=1 || z->n!=1){cd(z); O("CS-4\n"); R TE;}
              a=*kI(z); cd(z);
              if(a)
              { O("~AU ex1(v+i+1,0,&i,n,1)      ex1(V*w,K k,I*i,I n,I f) <- ex0(V*v,K k,I r)      ");
                x=ex1(v+i+1,0,&i,n,1);
                O("#AU ex0 :: ex1(v+i+1,0,&i,n,1)\n"); O("...U:");sd(x);
                R x=bk(x)?_n():x; }
              else while(i<n&&!bk(v[i])) i++; }
            R _n() )
    CSR(5,)
    CSR(6,)
    CS(7, do{ I i=0;
              O("~AY ex1(v,0,&i,0,1)      K ex1(V*w,K k,I*i,I n,I f) <- K ex0(V*v,K k,I r)      ");
              U(x=ex1(v,0,&i,0,1))
              O("#AY ex0 :: ex1(v,0,&i,0,1)\n"); O("   AY:");sd(x);
              if(fer>0)R x; x=bk(x)?_n():x; z=delist(x);
              if(ABS(z->t)!=1 || z->n!=1){cd(z); O("CS-7\n"); R TE;} a=*kI(z);cd(z); i=0;
              if(b){while(++i<n&&!bk(v[i])); if(i>=n)break;}
              SW(r)
              { CSR(5,)
                CS(6,if(a&&b)
                     { O("~AZ ex0(v+i+1,0,0)      ex0(V*v,K k,I r) <- ex0(V*v,K k,I r)      ");
                       x=ex0(v+i+1,0,0);
                       O("#AZ ex0 :: ex0(v+i+1,0,0)\n"); O("   AZ:");sd(x);
                       if(fer>0)R x;
                       cd(x); } )
                CS(7,DO2(a, x=ex0(v+i+1,0,0);
                            if(fer>0) R x;
                            cd(x); ) ) } }while(6==r && a);
          R _n() )
    CD: O("~DT newK(0,n?e:0)      K newK(I t, I n) <- Z K ex0(V*v,K k,I r)      ");
        z=newK(0,n?e:0);
        O("#DT ex0 :: newK(0,n?e:0)\n");
        if(n)for(i=n-1;i>=-1;i--)if(-1==i||bk(v[i]))
        { if(offsetColon==(v+1+i)[0] && (UI)(v+1+i)[1]>DT_SIZE) fer=1;
          O("~AT ex1(v+1+i,0,&i,n,0)      K ex1(V*w,K k,I*i,I n,I f) <- K ex0(V*v,K k,I r)      ");
          x=ex1(v+1+i,0,&i,n,0);
          O("#AT ex0 :: ex1(v+1+i,0,&i,n,0)\n"); O("   AT:");sd(x);
          if(fer1 || ((fer>0 && (v[0]==(V)offsetColon || v[2]==(V)1)) && !fCheck)){ cd(z); fer1=1; R x; }
          M(x,z)  kK(z)[--e]=bk(x)?2==r?0:_n():x; } }   //(c:9;a+b;c:1) oom
  //Note on brackets: [] is _n, not (). Expression [1;1] (0-type with two atoms) is different from [1 1] (integer vector)
  if(1==r || v[0]==(V)0x7d) z=collapse(z);
  if(k)
  { I j=valence(&z);
    if(!j && 0==k->t) DO(k->n, if(!kK(k)[i]) kK(k)[i]=_n() )   //Fill in 0-type NULLs with _n
    if(z->t!=7 ||z->n!=1||(j<k->n && !(0==j && k->n==1)))   //(0==j untested) project if necessary, reuse vf_ex.
    { if(encf && DT_SIZE<(UI)&z)
      { O("~DS vf_ex(&encf,k)      K vf_ex(V q, K g) <- K ex0(V*v,K k,I r)      ");
        x=vf_ex(&encf,k);
        O("#DS ex0 :: vf_ex(&encf,k)"); O("   DS:");sd(x); }
      else
      { O("~BF vf_ex(&z,k)	   K vf_ex(V q, K g) <- K ex0(V*v,K k,I r)      ");
        x=vf_ex(&z,k);
        O("#BF ex0 :: vf_ex(&z,k)\n"); O("   BF:");sd(x); }
      if(encp!=3)cd(z);
      R z=x; }
    else // checking if looks like f'[] or f/[] or ...
    { K p = kV(z)[CODE];
      I i=p->n-2; //not the terminating NULL, but the entry before
      V*q=(V*) kK(p)+i;
      K t=0;
      if(k->n==1) t=first(k);
      if((k->n>1 || (t && t->n==1)) && !sva(*q) && adverbClass(*q))
      { if(k->n==1 && !prj2) k->n=2;
        prj2=1;
        DO(k->n, if(!kK(k)[i]) prj=1 )
        if(!prj){ x=bv_ex(q,k); cd(z); R x; } }   // could be the _n() <-> ;;; replacement above
      cd(t);
      if(z->t==7 && z->n==1 && kK(kK(z)[CODE])[0]==offsetSSR && k->t==0 && k->n==3 && ABS(kK(k)[2]->t)==-3)
         {kK(k)[2]=enlist(kK(k)[2]); cd(x);}
      O("~DR vf_ex(&z,k)      K vf_ex(V q, K g) <- K ex0(V*v,K k,I r)      ");
      x=vf_ex(&z,k);
      O("#DR ex0 :: vf_ex(&z,k)\n"); O("   DR:");sd_(x,2);
      cd(z); z=x; } }   //copy/paste
  R z; }

Z K bv_ex(V*p,K k)
{ O("BEG bv_ex\n");
  O("    *p:     %p\n",*p);
  O("     k:");sd(k);
  V q=*p; K x; I n=0;   //assert 0!=k->n    assert k==b->n (otherwise, projection/VE, which shouldn't reach here)
  //Next if-stmt may contribute to bv_ex subtriadic problems
  if(!adverbClass(*p) && valence(*p)<3)
  { if(k->n<2) R VE;
    R dv_ex(kK(k)[0],p,kK(k)[1]); }
  if(offsetOver==(L)q)
  { DO(k->n-1, x=kK(k)[i+1];
               if(!x->n) R ci(*kK(k));
               if(!atomI(x))
               { if(n&&n!=x->n)R LE; else n=x->n; } )   //return x_0 if any empty list x_{i>0}
    n=MAX(1,n);   //if nothing was a list set to 1
    K z=ci(*kK(k)); K g=newK(0,k->n); M(z,g);
    DO(n, *kK(g)=z;
          DO2(g->n-1, x=itemAtIndex(kK(k)[j+1],i); M(x,g)  kK(g)[j+1]=x )
          x=bv_ex(p-1,g); M(x,g)
          DO2(g->n, cd(kK(g)[j]); kK(g)[j]=0 ) //set to 0 in case OOM happens
          z=x )
    cd(g); R z; }
  if(offsetScan==(L)q)
  { DO(k->n-1, x=kK(k)[i+1];
               if(!x)continue;
               if(!x->n) R ci(*kK(k));
               if(!atomI(x))
               {if(n&&n!=x->n)R LE; else n=x->n; } )   //return x_0 if any empty list x_{i>0}
    if(!n) R bv_ex(p-1,k);   //{x+y+z}\[1;1;1] yields 1 but {x+y+z}\[1;1;1 1] yields (1 1;3 3;5 5)
    n=MAX(1,n);   //if nothing was a list set to 1
    K z=newK(0,1); K g=newK(0,k->n); M(z,g)  kK(z)[0]=ci(*kK(k));
    DO(n, *kK(g)=ci(kK(z)[z->n-1]);
          DO2(g->n-1, x=itemAtIndex(kK(k)[j+1],i); M(x,z,g)  kK(g)[j+1]=x; )
          x=bv_ex(p-1,g); M(x,z,g)
          DO2(g->n, cd(kK(g)[j]); kK(g)[j]=0 ) //set to 0 in case OOM happens
          kap(&z,&x); cd(x); )
    cd(g); z=collapse(z); //unnecessary?
    R z; }
  if(offsetEach==(L)q)
  { DO(k->n, x=kK(k)[i];
             if(!x) continue;
             if(!x->n) R newK(0,0);
             if(!atomI(x))
             { if(n&&n!=x->n)R LE; else n=x->n; } ) //return () on any empty list
    I c=!n;//collapse needed
    n=MAX(1,n);//if nothing was a list set to 1
    K z=newK(0,n), g=newK(0,k->n); M(g,z)//break [;;...] into subpieces for f, store in g
    DO(n, K x;
          DO2(k->n, x=itemAtIndex(kK(k)[j],i ); M(x,g,z)  kK(g)[j]=x )
          x=bv_ex(p-1,g); M(x,z,g)  kK(z)[i]=x;
          DO2(k->n, cd(kK(g)[j]); kK(g)[j]=0 ) )   //sic =0
    cd(g);
    if(c)z=collapse(z); else z=demote(z);
    R z; }
  if(offsetEachright==(L)q) { P(k->n!=2,VE) K a=kK(k)[0],b=kK(k)[1];
                              O("~EY eachright2(a,p,b)      Z K eachright2(K a, V *p, K b) <- Z K bv_ex(V*p,K k)      ");
                              K zz=eachright2(a,p,b);
                              O("#EY bv_ex :: eachright2(a,p,b)\n"); O("   EY:");sd(zz);
                              R zz; }
  if(offsetEachleft==(L)q) { P(k->n!=2,VE) K a=kK(k)[0],b=kK(k)[1];
                             O("~EZ eachleft2(a,p,b)      Z K eachleft2(K a, V *p, K b) <- Z K bv_ex(V*p,K k)      ");
                             K zz=eachleft2(a,p,b);
                             O("#EZ bv_ex :: eachleft2(a,p,b)\n"); O("   EZ:");sd(zz);
                             R zz; }
  if(offsetEachpair==(L)q) { P(k->n!=2,VE) K a=kK(k)[0],b=kK(k)[1];
                             O("~FA eachpair2(a,p,b)      Z K eachpair2(K a, V *p, K b) <- Z K bv_ex(V*p,K k)      ");
                             K zz=eachpair2(a,p,b);
                             O("#FA bv_ex :: eachpair2(a,p,b)\n"); O("   FA:");sd(zz);
                             R zz; }
  O("~DQ vf_ex(*p,k)      K vf_ex(V q, K g) <- K bv_ex(V*p,K k)      ");
  K zz=vf_ex(*p,k);
  O("#DQ bv_ex :: vf_ex(*p,k)\n"); O("   DQ:");sd(zz);
  R zz; }

K ex1(V *w,K k,I *i,I n,I f)
{ //convert verb pieces (eg 1+/) to seven-types, default to ex2 (full pieces in between semicolons/newlines)
  O("BEG ex1\n"); O("     i: %p       n: %lld      f: %lld",i,n,f); O("     sd(k):");sd(k);
  I ii; for(ii=0;w[ii];ii++)
        { O("     ex1 w[%lld]: %p",ii,w[ii]);
          if(w[ii]>(V)DT_SIZE)sd(*(K*)w[ii]); else O("\n"); }
  if(offsetColon==w[0] && (UI)w[1]>DT_SIZE && (UI)w[2]>DT_SIZE && fwh==0)
  { fer=1;
    if(f)*i=n; else *i=-1;
    K tmp=*(K*)*(w+1); R ci(tmp); }
     //if(in(*w,adverbs)) R NYI;//Adverb at beginning of snippet eg '1 2 3 or ;':1 2 3; or 4;\1+1;4
  if( DT_ADVERB_OFFSET<=(L)*w && (L)*w<DT_VERB_OFFSET && offsetScan!=(L)*(w+1) && NULL!=*(w+1))
  { if(offsetScan==(L)*w)
    { if(0==strcmp(fBreak,"n")) R ex2(w+1,k);
      if(0==strcmp(fBreak,"t")) R ex2(w+1,k);
      if(0==strcmp(fBreak,"s")){ fer=1; R ex2(w+1,k); } }
    else if((V)offsetEach==*w){ if(3==ABS((*(K*)(w)[1])->t)) R ci(*(K*)(w)[1]); else R _n(); }
         else  R NYI; }
  I c=0; while(w[c] && !bk(w[c]))
         { c++;
           if(offsetColon==w[c-1]) break; }   //must break or assignment is n^2  (a:b:c:1)
  if(!c || !VA(w[c-1]) || (c>1 && offsetColon==w[c-1] ) )
  { O("~AD ex2(w,k)      K ex2(V*v, K k) <- K ex1(V*w, K k, I *i, I n, I f)      ");
    K vv=ex2(w,k); //typical list for execution
    O("#AD ex1 :: ex2(w,k)\n"); O("   AD: %p",&vv);sd(vv);
    R vv; }
  if(w[0]==offsetColon && (UI)w[1]>DT_SIZE)
  { I d=0; while(w[d] && !bk(w[d])) d++;
    K a=Kv(); a->n=0; K kb=newK(-4,d); M(a,kb)  V*b=(V*)kK(kb);
    DO(d-1, b[i]=w[i+1]; )
    b[d-1]=0; kV(a)[CODE]=kb; O("first case\n"); V x=ex_(&a,0); cd(a);
    if(w[-1]!=offsetColon) fer=1;
    R x; }
  //K3.2 crash bug: ."1",123456#"+"
  // build a 7type1 from the words if they end in a verb or adverb
  //Note: A returned +7type1 can never have a bk (; or \n) in it
  //? May be able to grab verb list by ignoring colon (: assignment) and whatever immediately precedes it ?
  //  (K3.2  1+|+a:-+ is 1+|+-+ )
  //grab things like 1+/ from the middle of wordlists eg (;1+/;)
  K a=Kv(), kb=newK(-4,1+c); M(a,kb)  V *b=(V*)kK(kb); b[c]=0; //sic (why sic?)
  DO(c, I j=c-i-1; //counting down
        b[j]=w[j];
        if(VA(b[j])) continue; //partially copy pasted from clone().
         // This pattern occurs here, in clone(), at the end of capture(), and in capture's BRACKET handler
        O("~BD ex_(w[j],1)      V ex_(V a, I r) <- K ex1(V*w,K k,I*i,I n,I f)      ");
        K r=ex_(w[j],1);   //oom
        O("#BD ex1 :: ex_(w[j],1)\n");
        V q=newE(LS,r);   //oom
        kap((K*) kV(a)+LOCALS,&q);   //oom
        cd(q);   //kap does ci
        O("~BE EVP(q)      K* EVP(K e) <- K ex1(V*w,K k,I*i,I n,I f)      ");
        q=EVP(q);   //oom free z etc. kap needs checking
        O("#BE ex1 :: EVP(q)\n"); O("...BE: %p\n",q);
        b[j]=q; )
  kV(a)[CODE]=kb;
  if(fll>0 && 2==kb->n && kdefClass((I)kV(kb)[0])){ K z=kdef(kV(kb)[0]); cd(a); R z; }
  R a; }

Z K ex2(V*v, K k)  //execute words --- all returns must be Ks. v: word list, k: conjunction?
{ O("BEG ex2\n"); O("     sd(k):");sd(k); ft3=0;
  I ii; for(ii=0;v[ii];ii++)
        { O("     ex2 v[%lld]: %p",ii,v[ii]);
          if(v[ii]>(V)DT_SIZE)sd(*(K*)v[ii]); else O("\n"); }
  K t0,t2,t3,e,u; I i=0;
  //TODO: is next line messed up ......we can't index like this for (|-+) ?? what about 0-NULL []
  //ci(k) was R 0; ...  put this here for f/[x;y;z]
  if(!v || !*v)R k?(1==k->n)?ci(kK(k)[0]):ci(k):(K)(L)DT_END_OFFSET; //? '1 + _n' -> domain err, '1 +' -> 1+ . but '4: . ""' -> 6
  if(bk(*v)) R *v;  // ; case
  if(!v[1] && !k)
  { O("~AJ ex_(*v,1)      V ex_(V a, I r) <- K ex2(V*v, K k)      ");
    K z=ex_(*v,1);  // n case
    O("#AJ ex2 :: ex_(*v,1)\n"); O("   AJ:");sd(z);
    if(z>(K)DT_SIZE && z->t==7 && z->n==3)
    { if(prnt && kV(z)[PARAMS] && kV(prnt)[CACHE_TREE] && !kV(z)[CACHE_TREE] && !kK(z)[LOCALS]->n)
      { K j0=dot_monadic(kV(z)[PARAMS]); K j1=dot_monadic(kV(prnt)[CACHE_TREE]); K j2=join(ci(j0),j1); cd(j0);
        if(encp==0) kV(z)[CACHE_TREE]=dot_monadic(j2);
        if(encp==1) kV(z)[CACHE_TREE]=dot_monadic(j1);
        cd(j0); cd(j1); cd(j2); cd(kK(prnt)[CACHE_WD]); kV(prnt)[CACHE_WD]=0; }
      if(prnt  &&  kV(prnt)[CODE]  &&  kK(prnt)[CODE]->t==-3  &&  kC(kK(prnt)[CODE])[0]=="{"[0]
         &&  kC(kK(prnt)[CODE])[kK(prnt)[CODE]->n-1]=="}"[0]  &&  strchr(kC(kK(prnt)[CODE]),"y"[0]))
      { if(encf) cd(encf);
        encf=ci(prnt); }
      if(encp!=2 || !prnt)
      { if(prnt){ if(grnt)cd(grnt); grnt=prnt; }
        prnt=ci(z); }
      else{ cd(z); R prnt; } }
    R z; }
  if(!v[1] && sva(*v))
  { O("~CF vf_ex(*v,k)      K vf_ex(V q, K g) <- K ex2(V*v, K k)      ");
    K zz=vf_ex(*v,k);
    O("#CF ex2 :: vf_ex(*v,k)\n"); O("   CF:");sd(zz);
    R zz; }     //TODO: (,/:) and (,\:) both valence 2
    //TODO: brackets may also appear as:     +/\/\[]    {x}/\/\[]    a/\/\[]    (!200)\\[10;20]
  if(bk(v[1]))
  { O("~AF ex_(*v,1)      V ex_(V a, I r) <- K ex2(V*v, K k)      ");
    K z= ex_(*v,1);
    O("#AF ex2 :: ex_(*v,1)\n"); O("   AF:");sd(z);
    if(fer==2 && !fCheck) R (K)0;
    if(prnt && z && z->t==7)
    { if(kV(prnt)[PARAMS] && !kK(prnt)[PARAMS]->n && kV(z)[LOCALS] && !kK(z)[LOCALS]->n
         && kV(prnt)[LOCALS] && kK(prnt)[LOCALS]->n)
      { kV(z)[CACHE_TREE]=kclone(kK(prnt)[CACHE_TREE]);
        if(prnt)cd(prnt);
        prnt=ci(z); }
      else if(kV(prnt)[LOCALS] && kK(prnt)[LOCALS]->n && kV(z)[PARAMS] && kK(z)[PARAMS]->n)
      { if(kV(prnt)[CACHE_TREE])
        { K j0=dot_monadic(kV(z)[PARAMS]); K j1=dot_monadic(kV(prnt)[CACHE_TREE]);
          K j2=join(ci(j0),j1); cd(j0); kV(z)[CACHE_TREE]=dot_monadic(j2); cd(j0); cd(j1); cd(j2); }
        else kV(z)[CACHE_TREE]=kclone(kV(z)[PARAMS]); } }
    R z; }
  if(!VA(*v) && (offsetColon == v[1] || (VA(v[1]) && offsetColon==v[2]) ) ) //Handle assignment
  { if(adverbClass(v[1])) R SYE;   //Could potentially handle instead of erroring
    K a=0,b=0,c=0,d=0,p=0; K*w=*v; U(a=*w);
    if(7==a->t && 0==a->n && (b=kV(a)[CONJ]) && 7==b->t && 0==b->n )
    { O("~CB ex_(kV(a)+CONJ,((L)*kW(b)==1 || (L)*(kW(b)+1)==1)?1:2))      ex_(V a, I r) <- ex2(V*v, K k)      ");
      U(b=ex_(kV(a)+CONJ,((L)*kW(b)==1 || (L)*(kW(b)+1)==1)?1:2))
      O("#CB ex2 :: ex_(kV(a)+CONJ,((L)*kW(b)==1 || (L)*(kW(b)+1)==1)?1:2))\n");
      w=*kW(a);   //K temp=a;  //a=ci(*kW(a)); w=*kW(a); cd(temp);
      if(b->t==0 && b->n==0)
      { if(1e6<(UI)w)
        { K r=*(K*)w;
          if(r->t==5){ p=enumerate(r); cd(b); b=enlist(p); cd(p); } } } }
  if(!b) U(b=newK(0,0))
  c=Kv(); //mmo  Optimization: could use A struct instead, with array[] for CODE
  K kc=newK(-4,2); //assumes NULL terminating entry
  M(b,c,kc); kV(c)[CODE]=kc;
  *kW(c) = v[1]; //it's v[1] regardless of colon position
  if(1!=sva(v[1]))
  { O("~AE ex1(v+(offsetColon==v[1]?2:3),k,0,0,1)      K ex1(V*w,K k,I*i,I n,I f) <- K ex2(V*v, K k)      ");
    d=ex1(v+(offsetColon==v[1]?2:3),k,0,0,1);   // oom -- except it's ok for d to be 0 elsewhere
    O("#AE ex2 :: ex1(v+(offsetColon==v[1]?2:3),k,0,0,1)\n"); O("   AE:");sd(d); }
    d=bk(d)?0:d;
    if(fer>0){ cd(c); cd(d); cd(b); R _n(); }
    if(cirRef(*w,d) || (((*w)->t==6 && d) && (d->t==0 || d->t==5 || ABS(d->t)!=d->t)))
    { K x=d;
      if(rc(x)){ d=kclone(x); cd(x); } }
    else if((*w)->t!=6)
    { K x = *w;
      if(rc(x)>1){ *w=kclone(x); cd(x); } }
    O("~AG dot_tetradic_2(w,b,c,d)      K dot_tetradic_2(K *g, K b, K c, K y) <- K ex2(V*v, K k)      ");
    K h=dot_tetradic_2(w,b,c,d);
    O("#AG ex2 :: dot_tetradic_2(w,b,c,d)\n"); O("   AG:");sd(h); //O("\nsd(prnt):");sd(prnt);O("\n");
    cd(c); cd(d); M(b,h)
    O("~AX of(h,b)      K of(K a, K b) <- K ex2(V*v, K k)      ");
    K j=of(h,b);
    O("#AX ex2 :: of(h,b)\n"); O("   AX:");sd(j);
    cd(b); R j; }
  while(v[1] && adverbClass(v[2+i])) i++;
  //TODO: Catch 0-returned-errors here and below
  if(!sva(v[0]) && (i || 2==sva(v[1])))   //na+. or nv. case  (n noun, a adverb, + means regex one+ and . means regex anything )
  { O("~AP ex2(v+2+i,k)      Z K ex2(V*v, K k) <- Z K ex2(V*v, K k)      i: %lld      ",i);
    t2=ex2(v+2+i,k);
    O("#AP ex2 :: ex2(v+2+i),k)\n"); O("   AP:");sd(t2);
    for(ii=0;v[ii];ii++)
    { O("     ex2 v[%lld]: %p",ii,v[ii]);
      if(v[ii]>(V)DT_SIZE)sd(*(K*)v[ii]); else O("\n"); }
    if(fer>0 && strcmp(errmsg,"(nil)")) R t2;
       //these cannot be placed into single function call b/c order of eval is unspecified
    O("~AQ ex_(v[1],1)      Z V ex_(V a, I r) <- K ex2(V*v, K k)      ");
    t3=ex_(v[1],1);
    O("#AQ ex2 :: ex_(v[1],1)\n"); if(t3<(K)DT_SIZE)O("   AQ: %p\n",t3);
    if(t3>(K)DT_SIZE && t3->t==7 && t3->n==3)
    { O("   AQ:");sd(t3);
      if(prnt && kV(prnt)[CACHE_TREE] && kV(prnt)[CACHE_WD] && !kK(t3)[LOCALS]->n)
      { K j0=dot_monadic(kV(t3)[PARAMS]); K j1=dot_monadic(kV(prnt)[CACHE_TREE]);
        K j2=join(ci(j0),j1); cd(j0); cd(kK(t3)[CACHE_TREE]); kV(t3)[CACHE_TREE]=dot_monadic(j2); cd(j0); cd(j1); cd(j2);
        if(kK(prnt)[CACHE_TREE]->n) fsf=1; }
      if(prnt)cd(prnt);
      prnt=ci(t3); O("RESET: prnt=ci(t3) at adverbClass in ex2\n"); }
    //if(v[1]!=t3) if(!VA(t3)) show(t3);//for use with below
    u=v[1]; //This u thing fixes repeated use of 7-1 subparen like f:|/0(0|+)\;f a;f b;
            //Not thread-safe. Adding ex_ result to LOCALS on 7-1 is probably better. See below
    v[1]=VA(t3)?t3:(V)&t3;
    O("~AR ex_(*v,1)      V ex_(V a, I r) <- K ex2(V*v, K k)      ");
    t0=ex_(*v,1);
    O("#AR ex2 :: ex_(*v,1)\n"); O("   AR:"); if(t0)sd(t0); else O(" not t0\n");
    if(fer>0 && strcmp(errmsg,"(nil)")){cd(t2); R(t0);}
    if(t0>(K)DT_SIZE && t0->t==7 && t0->n==3)
    { if(prnt && kV(prnt)[CACHE_TREE] && kV(prnt)[CACHE_WD] && !kK(t0)[LOCALS]->n)
      { K j0=dot_monadic(kV(t0)[PARAMS]); K j1=dot_monadic(kV(prnt)[CACHE_TREE]);
        K j2=join(ci(j0),j1); cd(j0); cd(kK(t0)[CACHE_TREE]); kV(t0)[CACHE_TREE]=dot_monadic(j2); cd(j0); cd(j1); cd(j2);
        if(kK(prnt)[CACHE_TREE]->n) fsf=1; }
      if(prnt) cd(prnt);
      prnt=ci(t0); }
    if(!prnt && t0->t==7 && t0->n==3) prnt=ci(t0);
    if(*(v+1+i)==offsetDot && t0->t==7 && t0->n==1 && (kK(kK(t0)[CODE])[1]==(V)offsetEach || kK(kK(t0)[CODE])[1]==(V)offsetEachright || kK(kK(t0)[CODE])[1]==(V)offsetEachleft || kK(kK(t0)[CODE])[1]==(V)offsetEachpair) )
    { K p=kV(t0)[CODE]; I i=p->n-2;  V*q=(V*) kK(p)+i;
      O("~EU bv_ex(q,t2)      Z K bv_ex(V*p,K k) <- K ex2(V*v, K k)      ");
      e=bv_ex(q,t2);
      O("#EU ex2 :: bv_ex(q,t2)\n"); O("   EU:"); if(e)sd(e); else O(" not e\n"); }
    else
    { O("~AS dv_ex(t0,v+1+i,t2)      K dv_ex(K a, V *p, K b) <- K ex2(V*v, K k)      i: %lld      ",i);
      e= dv_ex(t0,v+1+i,t2);
      O("#AS ex2 :: dv_ex(t0,v+1+i,t2)\n"); O("   AS:");sd(e);
      v[1]=u; }
    cd(t0); cd(t2); if(!VA(t3)) cd(t3); R e; }
  //vn. case
  O("vn case before RESET, if prnt:");
  if(prnt) sd_(prnt,2); else O("\n");
  i=0; while(adverbClass(v[1+i])) i++; //ALT'Y: i=adverbClass(b)?i+1:0;
  O("~AI ex2(v+1+i,k)      K ex2(V*v, K k) <- K ex2(V*v, K k)      k:");if(k)sd(k);else O(" is 0      ");
  t2=ex2(v+1+i,k); //oom. these cannot be placed into single function call b/c order of eval is unspecified
  O("#AI ex2 :: ex2(v+1+i,k)\n"); O("   AI:");sd_(t2,1);
  O("~AK ex_(*v,1)      V ex_(V a, I r) <- K ex2(V*v, K k)      ");
  t3=ex_(*v,1);
  O("#AK ex2 :: ex_(*v,1)\n"); if(t3<(K)DT_SIZE){ft3=1;O("   AK: %p\n",t3);} else{O("   AK:");sd(t3);}
  if(t3>(K)DT_SIZE && t3->t==7 && t3->n==3)
  { O("   AK:");sd(t3);
    if(kV(t3)==kV(grnt)){ if(cls)cd(cls); cls=ci(kK(kK(kK(prnt)[7])[0])[1]); }
    if(prnt)
    { if(kV(prnt)[CACHE_WD] && !kK(t3)[LOCALS]->n)
      { if(kK(prnt)[LOCALS]->n)
        { if(kV(t3)[CACHE_WD]  &&  !kV(t3)[CACHE_TREE])
          { kK(t3)[CACHE_TREE]=kK(prnt)[CACHE_TREE]; ci(kK(t3)[CACHE_TREE]); }
          else if(kK(t3)[PARAMS]->n || grnt)
               { K j0=dot_monadic(kV(t3)[PARAMS]); K j1=dot_monadic(kV(prnt)[CACHE_TREE]); K j2=join(ci(j0),j1); cd(j0);
                 if(kV(t3)[CACHE_TREE] && kK(t3)[CACHE_TREE]->n) cd(kK(t3)[CACHE_TREE]);
                 kV(t3)[CACHE_TREE]=dot_monadic(j2); cd(j0); cd(j1); cd(j2); } }
        else if(kV(kK(prnt)[CACHE_WD])[LOCALS] && kK(kK(prnt)[CACHE_WD])[LOCALS]->n
                && kV(prnt)[CACHE_TREE] && kK(prnt)[CACHE_TREE]->n
                && (!kV(kK(kK(kK(prnt)[CACHE_WD])[LOCALS])[0])[1] || !kV(kK(kK(kK(kK(prnt)[CACHE_WD])[LOCALS])[0])[1])[CONJ]) )
             { K j0=dot_monadic(kV(t3)[PARAMS]); K j1=dot_monadic(kV(prnt)[CACHE_TREE]);
               K j2=join(ci(j0),j1); cd(j0); kV(t3)[CACHE_TREE]=dot_monadic(j2); cd(j0); cd(j1); cd(j2); } }
      else if(kV(prnt)[CACHE_TREE] && 1==kK(prnt)[CACHE_TREE]->n && !kV(prnt)[CACHE_WD] && !kV(t3)[CACHE_TREE])
           { K j0=dot_monadic(kV(t3)[PARAMS]); K j1=dot_monadic(kV(prnt)[CACHE_TREE]);
             K j2=join(ci(j0),j1); cd(j0); kV(t3)[CACHE_TREE]=dot_monadic(j2); cd(j0); cd(j1); cd(j2); }
           else if( kV(t3)[PARAMS] && kK(t3)[PARAMS]->n && kV(prnt)[CACHE_TREE] && kK(prnt)[CACHE_TREE]->n==1
                    && (!kK(prnt)[CACHE_WD] || (kK(prnt)[CACHE_WD] && kK(prnt)[CACHE_WD]->n)))
                { K j0=dot_monadic(kV(t3)[PARAMS]); K j1=dot_monadic(kV(prnt)[CACHE_TREE]); K j2=join(ci(j0),j1); cd(j0);
                  if(kV(t3)[CACHE_TREE] && kK(t3)[CACHE_TREE]->n) cd(kK(t3)[CACHE_TREE]);
                  kV(t3)[CACHE_TREE]=dot_monadic(j2); cd(j0); cd(j1); cd(j2); }
      if(grnt)cd(prnt); else grnt=prnt; }
    O("RESET: prnt=ci(t3) at vn case in ex2.  prnt just before:"); if(prnt)sd_(prnt,2); else O("\n");
    prnt=ci(t3);
    O("after RESET, prnt:");sd_(prnt,0); }
  u=*v; //Fixes a bug, see above. Not thread-safe. Adding to LOCALS probably better
  *v=VA(t3)?t3:(V)&t3;
  if(*(v+i)==(V)offsetEach && !grnt)grnt=ci(prnt);
  O("~AL dv_ex(0,v+i,t2)      K dv_ex(K a, V *p, K b) <- K ex2(V*v, K k)      ");
  e=dv_ex(0,v+i,t2);
  O("#AL ex2 :: dv_ex(0,v+i,t2)\n"); O("   AL: %p",&e);sd(e);
  *v=u;
  if(*(v+i)==(V)offsetEach && prnt==grnt){ cd(grnt); grnt=0; }
  cd(t2);
  if(!VA(t3) && (encp!=3 || (encp==3 && kV(t3)[CACHE_WD]))) cd(t3);
  //the encp conditions address the 2 variations of issue #247, neither of which work in k2.8 or k3.2
  R e; }

I cirRef(K x,K y)
{ O("BEG cirRef\n");
  if(x&&(x==y))R 1; // XXX
  I f=0;
  if(xt==6 || !y || (yt!=0 && yt!=5) || (UI)x<DT_SIZE) R 0;
  DO(yn, f=cirRef_(x,kK(y)[yn-i-1],f) )
  R f; }

I cirRef_(K x,K y,I f)
{ O("BEG cirREF_\n");
  if(x==y) f=1;
  DO(yn, if(!f && (yt==0 || yt==5)) f=cirRef_(x,kK(y)[yn-i-1],f) )
  R f; }
