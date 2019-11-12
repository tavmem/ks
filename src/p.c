#include "incs.h"
#include "k.h"
#include "km.h"
#include "p.h"
#include "v.h"
#include "vf.h"

//Parser

S formed_dfa =
// n_\/"*  newline,quote,space,\,/,else (formed_group)
  "023451" //0 OK-NEWLINE
  "021151" //1 OK
  "021451" //2 OK-SPACE //TODO: Tab is in the space group (enough to justify migration to table-lookup?)
  "033333" //3 OK-LOCKED //TODO: was 033433 but any "\t x/y" commented. breaks comment in funcs. is why can't \cmd in func?
  "044444" //4 COMMENT //TODO: ^^^ merge COMMENT & OK-LOCKED. diff't DFA for funcs?
  "556515" //5 QUOTE
  "555555"; //6 QUOTE-ESCAPE
S left  = "([{";
S right = ")]}";
S lineA;
S lineB;
I fdc=1;   //Flag denameD create
I fll=0;   //flag line length

#define STATE_OK(x)      ((x->s) <  4)
#define STATE_COMMENT(x) ((x->s) == 4)
#define STATE_QUOTE(x)   ((x->s) >= 5)

Z I formed_group(C c){ S s="\n \\/\""; R charpos(s,c); }   //could be table-lookup instead

Z C flop(C c){ R c=='('?')':c=='['?']':c=='{'?'}':c; }

I parsedepth(PDA p){ R p?p->n+(STATE_QUOTE(p)?1:0):0; }

I complete(S a, I n, PDA *q, I *marks)   //well-formed or incomplete codeblock? all "{[(\"" closed
{ O("BEG complete\n"); O("a: %s\n",a); O("n: %lld    *marks: ",n);
  if(!marks)O("0"); else DO(n+1, O(" %lld",marks[i])); O("\n");
  if(!*q) *q=newPDA();
  PDA p=*q; C t; P(!p,-1)
  I r=formed_group('\0')+1;   //row-length
  O("pda->i, pda->s, pda->c  (parse state: pos in input, state, stacklength, stack)\n");
  for(;p->i < n;p->i++)
  { I before_pn=p->n, before_sq=STATE_QUOTE(p), before_sc=STATE_COMMENT(p); //for 'marks'/parse() stuff
    t=a[p->i];
    if(STATE_OK(p) && t)   //manage }])([{  (&&t b/c !t breaks strchr)
    { if(strchr(left,t)){ P(push(p,flop(t)),-1) P(p->n > 99,3) } //nest error if stack too tall (not entirely necessary...?)
      else if(strchr(right,t))
      { if(peek(p)!=t) R 2;   //unmatched error
        else pop(p); } }
    p->s = formed_dfa[r*p->s + formed_group(a[p->i])] - '0';   //state transition
    O("a[p->i] %c   i %lld   S %lld   n %lld   c %s\n",a[p->i],p->i,p->s,p->n,p->c);
    if(!marks)continue;   //This marks stuff tacked on for the parse() function
    C bot=bottom(p);
    I m = bot==')'?MARK_PAREN:
          bot==']'?MARK_BRACKET:
          bot=='}'?MARK_BRACE:
          STATE_COMMENT(p)?MARK_IGNORE:
          STATE_QUOTE(p)?MARK_QUOTE:
          before_pn||before_sq?ABS(marks[p->i-1]):0;   // ||before_sc? ?
    if((p->n && !before_pn)||(MARK_QUOTE==m && !before_sq)||(MARK_IGNORE==m && !before_sc)) m *= -1;   //starts
    marks[p->i] = m; }
  R (!STATE_QUOTE(p) && !p->n)?0:1; }   //0-complete, 1-incomplete

Z I mark_symbol(S s,I n,I i,I*m)   //this is probably pretty close to the convention for 'names'
{ if(m[i] || '`'!=s[i]) R 0;   //#spaces marked
  I adot=0,j=0,k;
  //case `"ss-sss"
  while(i+2+j < n && -MARK_QUOTE==m[i+1] && MARK_QUOTE==m[i+2+j]) j++;
  if(j) R j+2;
  //case plain syms
  //It is tempting to want to re-mark NAMES to SYMS like we re-marked QUOTES to SYMS but consider the following counterexample:
  // _a is a system variable. ___a is two floors of _a  but `___a is a type 4
  // none of `. `.. `... are symbols (empty symbol ` followed by verbs)
  for(;(k=i+1+j)<n;j++)
  { C c=s[k];
    if(!j && isdigit(c)) break;
    if(adot && (isdigit(c) || '.'==c))break;
    if(!isalnum(c) && '.'!=c && '_'!=c)break;
    adot='.'==c; }
  if(1==j && adot) R 1;  // `. is width one next to a verb, not width two (`.k. is width 4)
  //Guessing this algorithm could be rewritten
  R j+1; }

Z I isalnum_(C c){R isalnum(c) || '_'==c;}

Z I isalnumdot_(C c){R isalnum_(c) || '.'==c;}

Z I mark_name(S s,I n,I i,I*m)
{ I c=0;
  if(m[i]) R 0;
  if(i && isalnum_(s[i-1])) R 0;   //Not tested well. May be missing cases. Was added to allow 0n (not 0nabc)
  //_A case
  if(i<n-1&&s[i]=='_'&&isalpha(s[i+1])&&(i==n-2||m[i+2]||!isalnumdot_(s[i+2]))) R 2;
  // (\.?S\.?)+ case
  while(i+c<n && isalnumdot_(s[i+c]))
  { if(i+c<n-1 && '.'==s[i+c] && isalpha(s[i+c+1])) c+=2;
    else if(isalpha(s[i+c]))c++; else break;
    if(i+c>=n) break;
    while(i+c<n&&isalnum_(s[i+c])) c++;
    if(i+c>=n) break;
    if('.'==s[i+c]) c++; }
  if(1<i&&'.'==s[i-1]&&(0==m[i-2]&&'.'!=s[i-2])) c=0;
  R c; }

#define EAT(x) while(i+c<n&&!m[i+c]&&x(s[i+c]))c++;
#define EAT_DIGITS EAT(isdigit) //doesn't need !m[i+c] check
#define EAT_SPACES EAT(isspace) //does

Z I mark_number(S s,I n,I i,I*m)
{ I c=0;
  if(m[i])R 0;
  if(i && '-'==s[i] && !isspace(s[i-1]))
    switch(ABS(m[i-1])){case MARK_BRACKET:case MARK_PAREN:case MARK_SYMBOL:case MARK_NAME:case MARK_NUMBER:R 0; }
  if('-'==s[i])
  { if(i<n-2 && '.'==s[i+1] && isdigit(s[i+2]))c++;
    else if(i<n-1 && isdigit(s[i+1])) c++;
    else R 0; }
  EAT_DIGITS
  if(i+c<n && '.'==s[i+c])
  { if(c || (i+c<n-1 && isdigit(s[i+c+1]))) c++;
    else R 0; }
  EAT_DIGITS
  if(i+c<n && 'e'==tolower(s[i+c]))   //Technically in K3.2: 4e5 4e-5 4E5 work but 4E-5 doesn't
   { if(!c)R 0;
    else if(i+c<n-2 && '-'==s[i+c+1] && isdigit(s[i+c+2])) c+=2;
    else if(i+c<n-1 && isdigit(s[i+c+1])) c++;
    else R 0; }  //parse error ?? here or in a parent? think this will be caught by something else
  EAT_DIGITS
  //[-]?0[NIni] //This implementation lets you do unusual things like 0n.1.1 -> 0n 0.1 0.1
  if(i+c<n && ((1==c&&'0'==s[i]) || (2==c && '-'==s[i] && '0'==s[i+1])) && stringHasChar("NIni",s[i+c])
     && (i+c ==n-1 || !isalpha(s[i+c+1]))) c++;
  if(c) EAT_SPACES
  R c; }

Z I mark_adverb(S s,I n,I i,I*m)
{ if(m[i]) R 0;
  C c=s[i];
  if(i==0)
  { if( c=='\'' || c=='\\' )
    { if(strlen(s)>3)
      { I j=3;
        while(s[j]!='\0') if(s[j++]==')')
        R 0; }
      R 1;}
    R 0; }
  if(!strcmp(s,";\\\\")) R 1;
  if(c=='\\' && s[i-1]==';') R 0;
  if( s[i-1]!=' ' && (c=='/' || c=='\\' || c=='\'') )
  { if( i<n-1 && s[i+1]==':') R 2;
    R 1; }
  R 0; }

Z I mark_verb(S s,I n,I i,I*m)
{ I c=0;
  //case: numbered verb "0:  "  (NB: monadic-indicator can be used later: (4::)[{x}] -> 7)
  while(i+c<n-1 && -MARK_NUMBER==m[i] && MARK_NUMBER==m[++c+i]);
  if(c&&':'==s[i+c]){ c++; if(0)EAT_SPACES; R c; }
  if(m[i]) R 0;
  c=0;   //case: reserved verb _bin _bd _ssr
  if('_'==s[i]) while(i+c<n && isalpha(s[i+1+c]))c++;
  if(c>1)R 1+c;
  if( s[i]=='\\' && (s[i-1]==' ' || s[i-1]==';' || s[i-1]=='(')) R 1;
  c=0;   //primitive verbs + - includes verb ":"
  if(isCharVerb(s[i])){ c++; if(0)EAT_SPACES }
  R c; }

Z I mark_conditional(S s,I n,I k,I*m) // :[1;`true;`false]
{ S t[]={"if","do","while"};
  if(s[k]==':' && s[k+1]=='[' && s[k+2]!=';' && !m[k]) R 1;   // :[1;`true;`false]
  else if(m[k]==-MARK_NAME) DO(AE(t), I c=strlen(t[i]); if(!strncmp(s+k,t[i],c)&&s[k+c]=='[')R c )
  R 0; }

Z I mark_end(S s,I n,I i,I*m){ C c=s[i]; R m[i]?0:c==';'||c=='\n'?1:0; } // ?windows may need \r,\n to be -MARK_END,MARK_END

Z I mark_ignore(S s,I n,I i,I*m){ C c=s[i]; R m[i]?0:isspace(c)?1:0; }

//// 9 uses of colon: /////////////////
//amend/assignment  a[]+:9
//pathological verb/inert assigner for amend/error trap (:)[0;2]-> 2 or .(a;();:;9) or .[=;0;:]
//global assignment {b::x}
//conditional statement :[1;2;3] -> 2, even :[0;1] (brackets don't allow spaces)
//function return  {if[x;:10]; :20}
//piece of adverb ': /: \:
//piece of number-verb 0:
//indicate monadic "(+:;-)" "1+*:'a" (not if noun to left or right; ok to have space "+ :")
//resume (debug)
///////////////////////////////////////

//this block is understood by the makeheaders program
#if EXPORT_INTERFACE
enum mark_members{MARK_UNMARKED,MARK_IGNORE,MARK_BRACKET,MARK_END,MARK_PAREN,MARK_BRACE,MARK_QUOTE,MARK_SYMBOL,
                  MARK_NAME,MARK_NUMBER,MARK_VERB,MARK_ADVERB,MARK_CONDITIONAL,MARK_COUNT};
#endif

#define WORD_PART(x)      (ABS(x) > MARK_IGNORE)
#define WORD_START(x)     ((x) <= -MARK_END)
#define NOUN_START(x)     ((x) <= -MARK_PAREN  && (x) >  -MARK_VERB)
#define CAPTURE_START(x)  ((x) <  -MARK_IGNORE)
#define GREEDY_START(x)   ((x) == -MARK_SYMBOL || (x) == -MARK_NUMBER) //greedily form vectors for -1,-2,-4

//A mild overcount of the number of words that need to be added to the wordlist. Off by O(1) at most (?)
//Corrected soon after. No sense in duplicating logic here: let the word-converter decide the true count
Z I overcount(I*m,I n)
{ I c=0,p=0;
  DO(n, if( WORD_START(m[i]) && !(m[i]==p && GREEDY_START(p))){ p=m[i]; c++;} )
  R c; }

Z I syntaxChk(S s)               //TODO: refactor the syntax check as a single pass
{ if(s[0]=='\t' || s[0]=='\014') R 5;
  I n=strlen(s);
  if(n==1){ if(s[0]=='\'')R 10; else R 0; }
  I i,j,k=0;
  for(i=0;i<n;++i) if(s[i]!=' ')break;    //1st non-blank (if it exists)
  if(i>=n-1)R 0;
  for(j=i+1;j<n;++j) if(s[j]!=' ')break;  //2nd non-blank (if it exists)
  if(s[i]=='\\' && s[j]=='\\') R 0;
  if((s[i]=='\'' && s[j]!='\"') || j==n) R 20;
  for(i=0;i<n;++i)
  { if(s[i]=='\"') break;
    if(((i>0 &&  (s[i]=='\013' || s[i]=='\014' || (s[i]=='\'' && s[i-1]==';'))) || (i>1 && s[i]=='\'' && s[i-2]=='\\'))) R 30; }
  if(n>1 && s[n-1]=='\'' && s[n-2]==':') R 50;
  if(n>1) for(i=1;i<n;++i)
  { if(s[i]=='\"') break;
    if(s[i]==':' && s[i-1]=='`') R 55;
    if(s[i]==',' && (s[i-1]=='\\' || s[i-1]=='_')) R 60;
    if(s[i]=='?' && (s[i-1]=='-' || s[i-1]=='\\')) R 70; }
  if(n>2) for(i=2;i<n;++i)
  { if(s[i]=='\\' && s[i-1]==':' && (s[i-2]!='/' && s[i-2]!='\\')) R 80;
    if(s[i]=='/' && (s[i-1]=='+' || s[i-1]=='\'' || s[i-1]=='>' || s[i-1]=='%' || s[i-1]=='*' || s[i-1]=='?' || s[i-1]=='&' 
       || s[i-1]=='\\') && s[i-2]=='/') R 90;
    if(s[i]=='/' && s[i-1]=='/' && s[i-2]=='-') R 100;
    if(s[i]=='/' && s[i-1]=='/' && s[i+1]==',') R 999;
    if(s[i]=='_' && s[i-1]==',' && s[i-2]=='~') R 110;
    if(s[i]=='/' && s[i-1]=='#' && s[i-2]=='0') R 120;
    if(s[i]=='\\' && s[i-1]=='\\' && s[i-2]=='<') R 123;
    if(s[i]=='$' && s[i-1]==',' && s[i-2]=='$') R 130;
    if(s[i]==':' && s[i-1]=='0' && s[i-2]=='0') R 136;
    if(s[i]=='/' && s[i-1]=='/' && s[i-2]=='/') R 140; }
  if(n>3) for(i=3;i<n;++i)
  { if(s[i]=='\\' && s[i-1]==' ' && (s[i-2]=='\\' || s[i-2]=='/') && s[i-3]=='\\') R 141;
    if((isalpha(s[i]) || s[i]=='`') && s[i-1]==':' && s[i-2]==':' && s[i-3]==':') R 142; }
  if(n>3) for(i=2;i<n-1;++i){if(s[i]=='/' && s[i-1]==':' && s[i-2]=='/' && s[i+1]!=':') R 150; }
  if(n>5 && s[n-1]==':' && s[n-2]!=':' && s[n-3]==':') R 160;
  R k; }

I mark(I*m,I k,I t){ DO(k, m[i]=i?t:-t) R k; }

#define marker(a,b) DO(n,i+=maX(0,-1+mark(m+i,a(s,n,i,m),b)) )

//Some parse error cases missing...but it seems OK/preferable to ignore them e.g.  _t.a or 'a.....' (floor t.a or a. ...)
//K3.2: whitespace between ANY_TOKEN and adverb fails
//K3.2: if brackets [] not flush with token to left, parse error "0 1 2[0]" ok but "0 1 2 [1]" not ok
//      this rule doesn't apply to function argument lists, eg: f:{  [a] 1} is ok. however f: {\n\n  [a;b;d]  1+1} not ok
//      so the check probably has to do with whether some useful symbol occurred on the line already
//other errors: syntax error

K wd(S s, int n)
{ O("BEG wd \n"); O("  s: %s      n: %d    ",s,n);
  O("  d_:%s   &NIL:%p   sd(NIL):",d_,&NIL);sd(NIL);
  O("  &KTREE: %p      sd(KTREE):",&KTREE);sd(KTREE);
  lineA=s; fdc=0;
  O("~CZ denameD(&KTREE,d_,1)      K* denameD(K *d,S t,I create) <-  K wd(S s, int n)      ");
  K* z=denameD(&KTREE,d_,1);
  O("#CZ wd :: denameD(&KTREE,d_,1)\n");
  O("   CZ:                   "); O("  z: %p                       sd_(*z,0):",z); if(z)sd_(*z,0); else O("\n");
  if(kK(KTREE)[0])
  { O("        &kK(kK(KTREE)[0])[1]: %p      sd(kK(kK(KTREE)[0])[1]):",&kK(KTREE)[0]); sd(kK(kK(KTREE)[0])[1]); O("\n"); }
  O("~BS wd_(s,n, z,0)      K wd_(S s, int n, K *dict, K func) <- K wd(S s, int n)      ");
  K res=wd_(s,n, z,0);
  O("#BS wd :: wd_(s,n, denameD(&KTREE,d_,1),0)      sd(res):\n"); O(" %p",&res); sd(res);
  R res; }

K wd_(S s, int n, K*dict, K func) //parse: s input string, n length ;
{ //assumes: s does not contain a }])([{ mismatch, s is a "complete" expression
  O("BEG wd_\n");
  O("    s: %s\n",s); O("    n: %d\n",n); O("    sd_(func,2):"); if(func)sd_(func,2); else O("\n");
  O("    dict: %p      sd_(*dict,0):",dict); if(dict)sd(*dict); else O("\n");
  if(!s) R 0;
  if(strstr(s,":\\t")) { show(kerr("\\t  syntax")); R 0; }
  I z=syntaxChk(s); if(z==999)R NE; if(z) R SYE;
  if('\\'==s[0] && fbs){fbs=0; R backslash(s,n, dict);}
  PDA p=0;
  O("~DJ newK(-1,1+n)   K newK(I t, I n) -- K wd_(S s, int n, K* dict, K func)   ");
  K km=newK(-1,1+n);
  O("#DJ wd_ :: newK(-1,1+n)  --  marks\n");
  U(km) I *m = kI(km);   //marks
  O("~EA complete(s,n,&p,m)   I complete(S a, I n, PDA *q, I *marks) <- K wd_(S s, int n, K *dict, K func)      ");
  I e=complete(s,n,&p,m);
  O("#EA wd_ :: complete(s,n,&p,m)\n");
  O("   EA:  e: %lld\n",e);
  if(p){ pdafree(p); p=0; }    //Mark all ([{ and comments and quotes
  lineB=s;
  if(e){ cd(km); R PE; }
  O("~DM Kv()   K Kv() -- K wd_(S s, int n, K *dict, K func)      ");
  K v=Kv();
  O("#DM wd_ :: Kv()\n");
  M(v,km)  v->n=0; //7-0 "waiting" to be executed/potentially condensed ... set "isTenseWordfunc" -- wordfunc 'needing' execution
  marker(mark_end,   MARK_END)   // ";\n" - mark_end first so mark_number's space-eater doesn't get any newlines
  //NOTE: `1 is the 'empty' symbol indexed @ 1, `a.1 is `a . 1,  and `., `.., `... are not symbols
  O("   %d-UNMK %d-IGNR %d-BRKT %d-END %d-PREN %d-BRAC %d-QUOT %d-SMBL %d-NAME %d-NMBR %d-VERB %d-ADVB %d-COND %d-CNT\n",
     MARK_UNMARKED,MARK_IGNORE,MARK_BRACKET,MARK_END,MARK_PAREN,MARK_BRACE,MARK_QUOTE,MARK_SYMBOL,MARK_NAME,MARK_NUMBER,
     MARK_VERB,MARK_ADVERB,MARK_CONDITIONAL,MARK_COUNT);
  O("begin:     ");DO(n+1, O(" %lld",m[i]));O("\n");
  marker(mark_end,MARK_END)   // ";\n" - mark_end first so mark_number's space-eater doesn't get any newlines
  //NOTE: `1 is the 'empty' symbol indexed @ 1, `a.1 is `a . 1,  and `., `.., `... are not symbols
  O("mark end:  ");DO(n+1, O(" %lld",m[i]));O("\n");
  marker(mark_symbol,MARK_SYMBOL)// `a`b `A `_a `_aB01283.aaaa__.AB1._ `A.B.C, re-mark sym-quotes `"h-g" 
  O("mark smbl: ");DO(n+1, O(" %lld",m[i]));O("\n");
  marker(mark_name,MARK_NAME)   // ( _A | (\.?S\.?)+ ) where A := [A-Za-z] and S := A(A|[0-9_])* e.g.  _t, f, .k.a.b, a.b_0..c
  O("mark name: ");DO(n+1, O(" %lld",m[i]));O("\n");
  marker(mark_number,MARK_NUMBER)   //unified numeric type, determine +-1/2 at word-building time. mark spaces for strtol,strtod
  O("mark nmbr: ");DO(n+1, O(" %lld",m[i]));O("\n");
  marker(mark_adverb,MARK_ADVERB)   // / \ ' /: \: ': This is rude with the system/debug commands. those can be remarked later
  O("mark advb: ");DO(n+1, O(" %lld",m[i]));O("\n");
  marker(mark_conditional,MARK_CONDITIONAL)// : if do while
  O("mark cond: ");DO(n+1, O(" %lld",m[i]));O("\n");
  marker(mark_verb,MARK_VERB)   // ( D+: | _AA+ | V ) where D := [0-9] , V := ~!@#$%^&*_-+=|<,>.?:
  O("mark verb: ");DO(n+1, O(" %lld",m[i]));O("\n");
  marker(mark_ignore,MARK_IGNORE)   // get leftover spaces, anything else we want to ignore
  O("mark ignr: ");DO(n+1, O(" %lld",m[i]));O("\n");
  DO(n,if(m[i]==MARK_UNMARKED){cd(v);cd(km); R PE;})
  //TODO: check here if any _A+ listed that don't exist ("reserved error") free m etc. reserved error probably from "dename"
  //TODO: technically .k._a  (a valid global name e.g. no sym quotes) throws a value error then parse error here (mark it weird)
  //(one nice thing about being restrictive here (_verb and -0.0: number verbs) is future versions are backwards compatible)
  I y=0; //consolidate - removes non-word spaces/comments/etc
  O("~DK newK(-1,1+n)   K newK(I t, I n) <- K wd_(S s, int n, K *dict, K func)   ");
  K ks2=newK(-3,n);
  O("#DK wd_ :: newK(-1,1+n)  --  consol\n");
  M(v,km,ks2)  S s2=(S)ks2->k;memcpy(s2,s,n);//don't alter original s string
  DO(n, if(WORD_PART(m[i])){m[y]=m[i]; s2[y]=s2[i]; y++;} ) //m and s are compacted
  s2[y]=m[y]=0; I oc=overcount(m,n);
  O("~DL newK(-1,1+n)   K newK(I t, I n) <- K wd_(S s, int n, K *dict, K func)   ");
  K kw=newK(-4,1+oc);
  O("#DL wd_ :: newK(-1,1+n)  --  words\n");
  M(v,km,ks2,kw) V*w=(V*)kK(kw);//words. Assumes terminal extra NULL
  I c=0,j=0;
  if(!fll)fll=strlen(s2); else fll=-1;
  DO(y, O("~BY capture(s2,y,i,m,w,&c,(K*)kV(v)+LOCALS, dict,func)      ");
        O("I capture(S s, I n, I k, I *m, V *w, I *d, K *locals, K *dict, K func) <- K wd_(S s, int n, K *dict, K func)      ");
        j=capture(s2,y,i,m,w,&c,(K*)kV(v)+LOCALS,dict,func);
        O("#BY wd_ :: capture(s2,y,i,m,w,&c,(K*)kV(v)+LOCALS,dict,func)\n");
        O("   BY: j: %lld\n",j);
        i+=-1+j;
        if(!j  ){ M(0,v,km,ks2,kw) } )
  cd(km); cd(ks2);
  //wrong: Suppressed this for now (wastes at most n/2 space) -- 
  //       may need to reenable if padded oc bad (eg imagine 1+1 is not 0=t,4=n VVV0 but 0=t,6=n VVV000)
  //       ^^^ padded overcount bad already (for O(1) valence calc)
  //"reall0c" kw down to size
  if(oc>c && lsz(sz(0,1+oc)) > lsz(sz(0,1+c)))
     //TODO: better if possible: fix overcount() to be exact count: could just be adding != -MARK_BRACKET. dd() differences
     //if(oc-c){test_print=1; dd(oc-c); if(tests>110)exit(0);}
  { K kw2=newK(-4,1+c); //trim because we cut corners using overcount()
    M(v,kw,kw2) memcpy(kK(kw2),kK(kw),sizeof(V)*c); cd(kw); kw=kw2; }   //-4 special trick: don't recursively cd() contents
  kV(v)[CODE]=kw;   // return what we just built
  kW(v)[c]=0;
  R v; }

Z I isodigit(C c){ R isdigit(c) && c<'8'; } // is octal digit

Z I odigitlen3(S s)
{ I i=0;
  while(s[i]&&isodigit(s[i])&&i<3) i++;
  R i; }   // 0-3 consecutive octal digits

Z C unescape(S s, I*k)   //*k - return is composed of how many [escaped] chars
{ *k=1; C c=*s;
  if('\\'!=c) R c;
  I y=odigitlen3(s+1),a=0;
  if(!y) R *k=2,'b'==(c=s[1])?'\b':'n'==c?'\n':'r'==c?'\r':'t'==c?'\t':c;  // \" and \\ for free
  *k+=y;
  DO(y, a=a*8+s[1+i]-'0' )
  R (C) (UC) MIN(a,255); }

Z I unescaped_size(S s,I n)
{ //assumes s[0:n-1] could be the inside, [exclusive] of any complete MARK_QUOTE token ; checks !isodigit(s[n])
  I k=0;
  DO(n, k++;
        if('\\'==s[i])i+=maX(1,odigitlen3(s+i+1)) )
  R k; }

Z I unescaped_fill(S d, S s, I n)
{ I k=0,q;
  DO(n,d[k++]=unescape(s+i,&q);i+=q-1)
  R k; }

S param_dfa =
// a!;w]*  alpha,digit/underscore,semicolon,whitespace,right-bracket,else
  "155045" //Nothing really read yet
  "113245" //Name in process
  "553245" //Name over
  "155355" //Requires name
//"444444" //Accept
//"555555" //Reject
;

Z I param_gp(C c){ R isalpha(c)?0:isdigit(c)||'_'==c?1:';'==c?2:isspace(c)?3:']'==c?4:5; }

Z I param_validate(S s,I n) // Works on ([]) and {[]} but pass inside exclusive eg "{..[.].}" -> "..[.]."
{ //1-no params, 1-params-ok, 2-params-fail. Cannot assume enclosures are matched ( eg "{[}" )
  S u=s+n;
  while(s<u && isspace(*s) && '\n'!=*s)s++;
  P(s==u || '['!=*s++,0)   //Yield 0 when no bracketed parameter clause.
  //  a=[A-Za-z] ; w=whitespace ; s=w* ; n=sa(a|[0-9]|_)*s ;  \[s(n(;n)*)?\]  full parameter regex
  I p=0,r=param_gp('.')+1;   //hopefully row size. 6?
  while(s<u && 4 > p) p=param_dfa[r*p+param_gp(*s++)]-'0';
  R 4==p?1:2; }   //State-4 yield 1 (pass, good parameters), otherwise yield 2 (fail, bad paramters)

Z K* inKtreeR(K *p,S t,I create)
{ O("BEG inKtreeR\n"); O("    t: %s      create:%lld",t,create);  O("    p: %p      sd_(*p,0):",p);sd_(*p,0);
  if(!*t) R p;
  if('.'==*t) t++;
  I c=0,a=(*p)->t;
  while(t[c] && '.'!=t[c]) c++;
  S u=strdupn(t,c);   //oom
  S k=sp(u);   //oom
  free(u); t+=c;
  P('_'==*k,(K*)kerr("reserved"))// ... not positive this goes here. does it fit in LOC? or parser maybe?
  //Probably the below error check (and any others in front of LOC) should be moved into LOC
  //and LOC should have the potential to return 0 (indicating other errors as well, e.g. out of memory)
  P(!(6==a || 5==a),(K*)TE)
  K e=0;
  if(create){ e=lookupEntryOrCreate(p,k); P(!e,(K*)ME) }
  else{ K a=*p; if(5==a->t)e=DE(a,k); P(!e,(K*)0) }
  if('.'==*t && (!t[1] || '.'==t[1])){ t++; p=EAP(e); }   //attribute dict
  else
  { O("~DI EVP(e)      K* inKtreeR(K*p,S t,I create) <- K* EVP(K e)     ");
    p=EVP(e);
    O("#DI inKtreeR :: EVP(e)\n"); }   //value
  O("~DH inKtreeR(p,t,create)      K *z=inKtreeR(p,t,create) <- K *z=inKtreeR(p,t,create)     ");
  K *z=inKtreeR(p,t,create);
  O("#DH inKtreeR :: inKtreeR(p,t,create)\n");
  R z; }

K* inKtree(K *d, S t, I create)
{ O("BEG inKtree \n"); O("    t: %s      create:%lld",t,create);  O("    d: %p      sd_(*d,0):",d);sd_(*d,0);
  if(!simpleString(t)) R 0;   //some kind of error
  O("~DG inKtreeR('.'==*t||!*t?&KTREE:d,t,create)      K* inKtreeR(K*p,S t,I create) <- K* inKtree(K*d, S t, I create)     ");
  K *z=inKtreeR('.'==*t||!*t?&KTREE:d,t,create);
  O("#DG inKtree :: inKtreeR('.'==*t||!*t?&KTREE:d,t,create)\n");
  R z; }

//TODO: capture - oom all
I capture(S s, I n, I k, I *m, V *w, I *d, K *locals, K *dict, K func)
{ //IN string, string length, pos in string, markings;
  //OUT words, current #words; IN locals-storage, names-storage, charfunc/NULL
  O("BEG capture\n"); O("    s: %s\n    n: %lld    k: %lld    *m: %lld    *w: %p    *d: %lld\n",s,n,k,*m,*w,*d);
  O("    *locals:");sd(*locals);
  if(dict){O("    dict: %p      sd_(*dict,1):",dict); sd_(*dict,1);}
  O("    func:"); if(func)sd_(func,2); else O("\n");
  if(fll && fll!=n)fll=-1;
  V z=0,*p=w+*d; *p=0; I r=1,v=0,y=0,a,b=0,c,l,frc=0;S u="",e;K g,h=0,hh=0;
  if(k>=n || !CAPTURE_START(m[k])) R r;
  I M=m[k];
  while(k+r<n&&-M==m[k+r]) r++;      // r token-length
  if(GREEDY_START(M))                //   -1,-2,-4
    while(k+v<n&&-M==ABS(m[k+v]))    // v vector-length
      if(WORD_START(m[k+v++]))y++;   // y #items in vector
  switch(-M)
  { CS(MARK_CONDITIONAL, O("conditional\n"); z=offsetColon)   //dummy value
    CS(MARK_PAREN  ,  O("paren ... fbr set, fdc set\n"); fbr=1; fdc=1;
                      O("~BT wd_(s+k+1,r-2,dict,func)      K wd_(S s, int n, K *dict, K func) <- ");
                      O("I capture(S s, I n, I k, I *m, V *w, I *d, K *locals, K *dict, K func)      ");
                      z=wd_(s+k+1,r-2,dict,func);
                      O("#BT capture :: wd_(s+k+1,r-2,dict,func)\n");
                      if(!z)R (L)PE;)                   //oom. currently z->t==7 z->n==0.
                      //Execution will know this is paren (for rev order) because of its depth
    CS(MARK_BRACKET,  O("bracket ... fbr set\n"); fbr=1;
                      if(!*d || bk(p[-1]))
                      { if(func && !k) R r;              //Ignore function params. k because no {[a;b][c;d]}
                        else R (L)PE; }                  // [1;2] on a line by itself
                      a=0;
                      while(a < -1+*d && adverbClass(p[-1-a])) a++;
                      //could perhaps put [] directly on () or {} 7 instead of making new g provided 0==a.
                      g=Kv(); K ko=newK(-4,a+2); M(g,ko)  g->n=0; kV(g)[CODE]=ko;
                      V *o=kW(g);
                      if((s+k+1)[0]=='x' && (s+k+1)[1]==';')fbr=0; O("fbr cleared\n");
                      O("~BU wd_(s+k+1,r-2,dict,func)      K wd_(S s, int n, K *dict, K func) <- ");
                      O("I capture(S s, I n, I k, I *m, V *w, I *d, K *locals, K *dict, K func)      ");
                      z=wd_(s+k+1,r-2,dict,func);
                      O("#BU capture :: wd_(s+k+1,r-2,dict,func)\n");
                      if(!z){ cd(g); R (L)PE; }
                      //g o z   oom: you can return 0 but catch above?
                      if(MARK_CONDITIONAL==ABS(m[k-1]))
                      { V *zp=kW(z);
                        while(*zp && !bk(*zp)) zp++;
                        SW(s[k-1]){CS(':',b=4) CS('f',b=5) CS('e',b=6) CS('o',b=7)  }  //: if while do
                        ((K)z)->n=b;
                        cd(g);
                        goto grabdone; }
                      DO(a+1, o[i]=p[-1-a+i] )
                      o[a+1]=0; K *f=p[-1-a];
                      if(!sva(f))
                      { if(MARK_ADVERB==ABS(m[k-1-a]) || MARK_ADVERB==ABS(m[k-a]))
                        { }   //do nothing for '[] and ':[]  (and sort of / /: \ \: ... but they don't reach here)
                        else if(MARK_NAME != ABS(m[k-1-a]))
                        { // Has form na*[] and not va*[] so move n from the parent to the LOCAL on this BRACKET.
                          // NAME special storage case
                          K q=newE(LS,ci(*f)); //oom
                          kap((K*) kV(g)+LOCALS,&q);//oom
                          cd(q); //kap does ci
                             //cd(DI(*locals,--(*locals)->n));  // You can't do this.
                             // (the reason is the same as why you can't (currently) realloc-shrink the anonymous mmapped Ks)
                             // the line can be left out without ill effects assuming
                             // it's OK to let the parent free the objects (it may not be)
                             //  probably best to simply implement realloc-shrink for anonymous mmap
                          K temp=DI(*locals,(*locals)->n-1); //This is a replacement for above.
                             // It can be optimized(?) since it leaves an empty dict entry on *locals
                          if(temp){ cd(kK(temp)[1]); kK(temp)[1]=0; }
                          *o=EVP(q); }
                        else if(7==(*f)->t && 3==(*f)->n){} }   // for {} function add args to local dictionary (huh??)
                      kV(g)[CONJ]=z; z=g;
                      grabdone:
                      (*d)-=1+a; p=w+*d; )
    CS(MARK_BRACE  ,  //Functions & subfunctions validated at parse time
                      O("brace\n"); fbr=1; fdc=1; z=Kv(); g=newK(-3,r-2);
                      M(z,g) //M(z,g,kV(z)[PARAMS]=Kd(),kV(z)[LOCALS]=Kd())
                      kV(z)[CODE]=g; ((K)z)->n=3;
                      memcpy(kC(g),s+k+1,r-2);
                      kV(z)[CONTeXT]=func?kV(func)[CONTeXT]:d_;
                      K* zdict=(K*)kV(z)+PARAMS; O("sd(*zdict):    %p",zdict);sd(*zdict);
                      K* ydict=(K*)kV(z)+LOCALS; O("sd(*ydict):    %p",ydict);sd(*ydict);
                      K j;
                      //Validate brackets in {[..]...} : 0-Absent, 1-OK, 2-Fail
                      I state=param_validate(s+k+1,r-2);
                      P(state>1,(L)kerr("parameter"))
                      if(state) //Bracketed parameters exist and are well-formed
                      { S a=strchr(s+k+1,'['); S b=strchr(a,']');
                        O("~BV wd_(a+1,b-a-1,zdict,z)      K wd_(S s, int n, K *dict, K func) <- ");
                        O("I capture(S s, I n, I k, I *m, V *w, I *d, K *locals, K *dict, K func)      ");
                        j=wd_(a+1,b-a-1, zdict,z); //Grab only params. This must create entries in  zdict
                        O("#BV capture :: wd_(a+1,b-a-1, zdict,z)\n");
                        M(z,j) //not g
                        cd(j); }
                      else   //Deal with any implicit Z,Y,X parameters
                      { K t=Kd(); M(z,t)
                        O("~BW wd_(s+k+1,r-2,&t,0)      K wd_(S s, int n, K *dict, K func) <- ");
                        O("I capture(S s, I n, I k, I *m, V *w, I *d, K *locals, K *dict, K func)      ");
                        j=wd_(s+k+1,r-2,&t,0);   //Grab all local names
                        O("#BW capture :: wd_(s+k+1,r-2,&t,0)\n");
                        O("sd(*ydict):    %p",ydict);sd(*ydict);
                        M(z,t,j); I n=0;
                        DO(3, if(DE(t,IFP[2-i])){ n=3-i; break; } )
                        DO(n, denameD(zdict,IFP[i],1) ) //TODO: oom
                        cd(t); cd(j); }
                      O("~BX wd_(s+k+1,r-2, ydict,z)      K wd_(S s, int n, K *dict, K func) <- ");
                      O("I capture(S s, I n, I k, I *m, V *w, I *d, K *locals, K *dict, K func)      ");
                      j=wd_(s+k+1,r-2, ydict,z);
                      O("#BX capture :: wd_(s+k+1,r-2, ydict,z)\n");
                      M(z,j)
                      cd(j); )
                      //For subfunctions: (subfunction arg list overrides)
                      //if(func) *zdict = merge self, parent (in what way?)
    CS(MARK_NUMBER ,  r=v;   //0 1 -2.3e-4 6. .7 -8 9E0
                      a=1; DO(r,if(stringHasChar(".Eein",s[k+i])){a=2;break;})
                      z=newK(1==y?a:-a,y); U(z)
                      DO(r, if(m[k+i]>=0)continue;
                            l=1;
                            while(m[l+k+i]==MARK_NUMBER) l++;
                            if(!(u=strdupn(s+k+i,l))){ cd(z); R (L)ME; }
                            g=1==a?formKiCS(u):formKfCS(u);
                            O("number   u: %s   \n",u);
                            free(u);
                            M(z,g)
                            if(1==a) kI(z)[b++]=*kI(g);
                            else     kF(z)[b++]=*kF(g);
                            cd(g); ) )
    CS(MARK_QUOTE  ,    // "\b\n\r\t\"\o\oo\ooo\\"  ;  we may rely on completeness here (bounds checking)
                      O("quote\n");
                      a=unescaped_size(s+k+1,r-2);
                      z=newK(1==a?3:-3,a); //mm/o  you can return 0 but catch above?
                      unescaped_fill(kC(z),s+k+1,r-2); )
    CS(MARK_SYMBOL ,  //handle `a`"b-\777\n\0"`c ```d.ef
                      r=v;
                      z=newK(1==y?4:-4,y); //oom
                      O("symbol   ");
                      DO(r, if(m[k+i]>=0)continue;
                            for(a=0;m[k+i+1+a]>0;a++);
                            u=alloc(1+a); //oom  you can return 0 but catch above?
                            c='"'==s[k+i+1]?2:0;
                            u[unescaped_fill(u,s+k+i+1+c/2,a-c)]=0;
                            kS(z)[b++]=sp(u); //mm/o  you can return 0 but catch above?
                            O("u: %s   ",u); free(u); i+=a; )
                      O("\n"); )
    CS(MARK_NAME   ,  e=strdupn(s+k,r); O("name   ");
                      u=sp(e); //converting to sp() probably unnecessary
                      free(e); P(!u,(L)ME)                     //you can return 0 but catch above?
                      //k3.2 knows whether NAME is set for assignment or not.  "b.c" value/parse error but "b.c:3" ok
                      K q;
                      //      it uses the non-path-creating form of dename
                      if(2==r && '_'==*u && stringHasChar(n_s,u[1]))
                        if('f'==u[1]){ O("n1a    got _f\n"); z=func?ci(func):_n(); O("z-set\n"); }
                          //TODO: stack error --- but be careful to generalize.
                          // proper soln will handle cycle f:{ g 0} g:{f 0}
                          // see "getrusage" or http://stackoverflow.com/questions/53827/checking-available-stack-size-in-c
                        else{ O("n1b   "); z=((K(*)())vn_[charpos(n_s,u[1])])(); }
                      else if(func)
                      { O("n2      u: %s     in if(func)\n ",u);
                        O("func *********************************************************************************\n");
                        sd((K)kV(func)[CODE]);
                        O("s ------------------------------------------------------------------------------------\n");
                        O("s: %s\n",s);
                        O("u: %s\n",u);
                        h=*denameS(".k",u,0);
                        if(7==h->t){ hh=match( (K)kV(h)[CODE] , (K)kV(func)[CODE] ); O("sd(h[CODE]):");sd_( (K)kV(h)[CODE] ,2); }
                        O("......................................................................................\n");
                        if( dict==(K*)kV(func)+PARAMS){ O("n2a\n"); V q=newEntry(u); U(q)  M(q,kap( dict,&q))  z=EV(q); cd(q); }
                        else if((q=DE(*dict,u)))
                        { O("n2b      sd_(*dict,9):");sd_(*dict,9); O("sd_(q,9):");sd_(q,9);
                          z=EVP(q); }   //If func has its local, use it
                          //else if(':'==s[k+r] && ':'==s[k+r+1] && -MARK_VERB==m[k+r+1])
                          //  {m[k+r]=MARK_NAME; r++; z=denameS(kV(func)[CONTeXT],u);} //m[]=  probably superfluous
                        else if(-MARK_VERB==m[k+r] && ':'==s[k+r+1] && -MARK_VERB==m[k+r+1])
                        { O("n2c\n");
                          O("        &kK(kK(KTREE)[0])[1]: %p      sd(kK(kK(KTREE)[0])[1]):",
                            &kK(KTREE)[0]);sd(kK(kK(KTREE)[0])[1]);O("\n");
                          if(':'==s[k+r])r++;
                          O("~DX denameS(kV(func)[CONTeXT],u,1)      K* denameS(S dir_string, S t, I create) <- ");
                          O("I capture(S s, I n, I k, I *m, V *w, I *d, K *locals, K *dict,K func)      ");
                          z=denameS(kV(func)[CONTeXT],u,1);
                          O("#DX capture :: denameS(kV(func)[CONTeXT],u,1)\n");
                          O("        &kK(kK(KTREE)[0])[1]: %p      sd(kK(kK(KTREE)[0])[1]):",
                            &kK(KTREE)[0]);sd(kK(kK(KTREE)[0])[1]);O("\n"); }
                        else if(dict==  (K*)kV(func)+LOCALS  && ':'==s[k+r] && -MARK_VERB==m[k+r])
                        { O("n2d\n");
                          O("~ED denameD( dict,u,1)      K* denameD(K *d, S t, I create) <- ");
                          O("I capture(S s, I n, I k, I *m, V *w, I *d, K *locals, K *dict, K func)     ");
                          z=denameD( dict,u,1);
                          O("#ED capture :: denameD( dict,u,1)\n");
                          O("   ED: z: %p\n",z); }
                          //K3.2:  a+:1 format applies to context-globals not locals
                        else if(7==h->t && *kI(hh)){ O("got recur\n"); z=ci(func); frc=1; }
                        else
                        { O("n2e\n");
                          z=denameS(kV(func)[CONTeXT],u,1);
                          O("kK(z): %p   ",kK(z)); } }   //Otherwise check the context (refactor with above?)
                      else
                      { O("n3      u: %s\n",u);
                        if(fll>0) fdc=0;
                        I i; for(i=k;i<strlen(s);i++)
                             { if(!fbr && s[i]==';') break;
                               else if(s[i]==':'|| (fbr && (s[i]=='x'||s[i]=='y'||s[i]=='z'))){ fdc=1; break; } }
                        O("~BZ inKtree( dict,u,0)      K *inKtree(K *d, S t, I create) <- ");
                        O("I capture(S s, I n, I k, I *m, V *w, I *d, K *locals, K *dict, K func)     ");
                        z=inKtree( dict,u,0);
                        O("#BZ capture :: inKtree( dict,u,0)\n");
                        O("   BZ: z: %p      sd(*(K*)z):",z); if(z)sd(*(K*)z); else O("\n");
                        O("      fbr: %lld   fdc: %lld\n",fbr,fdc);
                        if( !fdc && !z )
                        { L err=(L)VLE;
                          #ifndef DEBUG
                          oerr(); O("%s\n%c\n",u,'^');
                          #endif
                          R err; }
                        O("~CA denameD( dict,u,fll&&fdc)      K* denameD(K *d, S t, I create) <- ");
                        O("I capture(S s, I n, I k, I *m, V *w, I *d, K *locals, K *dict, K func)     ");
                        z=denameD( dict,u,fll&&fdc);
                        O("#CA capture :: denameD( dict,u,fll&&fdc)\n");
                        O("   CA: z: %p      sd(*(K*)z):",z); if(z)sd(*(K*)z); else O("\n"); } )
    CS(MARK_VERB   ,  // "+" "4:" "_bin"  ;  grab "+:", "4::"
                      O("verb\n");
                      if(s[k]=='\\'){ z=(V)0x7c; break; }   //trace or scan
                      if(s[k]==':' && ((k==0 && strlen(s)>1 && s[k+1]!=':') ||
                         (k>0 && k!=n-1 && s[k-1]==';' && s[k+1]!=';' && s[k+1]!='_' && s[k+1]!='['))){ z=(V)0x7d; break; }
                      if('_'==s[k] && r > 1)
                      { if(k+r<n && ':'==s[k+r] && -MARK_VERB==m[k+r]) R (L)PE;
                        u=strdupn(s+k,r); P(!u,(L)PE)  L i;
                        i=DT_SPECIAL_VERB_OFFSET;
                        while(i<DT_SIZE && (!DT[i].text || SC(u, DT[i].text))) i++;
                        if(i<DT_SIZE) z=(V)i;   //faster is sp()/hash-table (compared to SC())
                        free(u); P(!z,(L)kerr("reserved"))   // _invalidsystemverbname
                        break; }   // _verb does not grab monadic ':' following
                      //The code for verb arity is hard to follow. I suspect this is because I could not find the factorization
                      I grab=0; L i=0;
                      I is_colon=':'==s[k];
                      I name_bracket_assign=0;
                      I modifier_colon = k+r<n && ':'==s[k+r] && -MARK_VERB==m[k+r];
                      if(k-i > 0) if(is_colon && MARK_VERB == ABS(m[k-i-1])) i++;
                      if(k-i > 0) if(MARK_BRACKET ==  ABS(m[k-i-1])) while(m[k-i] != -MARK_BRACKET) i++;
                      if(k-i > 0) if(MARK_NAME == ABS(m[k-i-1])) name_bracket_assign = 1; //(no adverb, assign to non-names, etc)
                      if(!is_colon && !(k+1<n && ':'==s[k+1] && -MARK_VERB==m[k+1] )) name_bracket_assign=0;
                      //  Handles this case at least (0 0)[0]:1  (works but not proven correct/the right thing to do)
                      if(i && is_colon && !modifier_colon && !name_bracket_assign) R (L)PE;
                      I y_present= k+r+1<n && !(s[k+r+1] == ':' && -MARK_VERB==m[k+r+1]) && MARK_END != ABS(m[k+r+1]);
                      //MARK_END may end up being redundant here?
                      a=(!*d || MARK_END==ABS(m[k-1]) || MARK_ADVERB==ABS(m[k-1]) || MARK_VERB==ABS(m[k-1]))
                          && !( k+r >= n || -MARK_END==m[k+r] || -MARK_ADVERB==m[k+r] || -MARK_BRACKET==m[k+r] )?1:2;   //arity
                      if(is_colon && !modifier_colon)
                      { a=2;
                        if(k> 0 && -MARK_END!=m[k-1] && !s[k+1] && !name_bracket_assign) R (L)PE; }
                        // +:: or 4:: :  or a _abs:  (trailing dyadic :C)
                      else if(name_bracket_assign) a=y_present?2:1;
                      else if(modifier_colon){ m[k+r]*=-1; r++; a=1; grab=1; }   //grab monad ':' sign
                      i=0;
                      if(r-grab==1)
                      { z=(V)(DT_VERB_OFFSET+2*charsVerb(s[k])+(1==a?0:1));
                        if(z==(V)0x3d && s[k]!=':')z=(V)0x7c; }
                      else
                      { j=(V)atol(s+k);
                        i=DT_SPECIAL_VERB_OFFSET;
                        while(i < DT_SIZE && (!DT[i].text || (L)j != atol(DT[i].text)))i++;
                        if(i<DT_SIZE)z=(V)(i+(1==a?0:1));  else R (L)PE; } )
                      //no matching 0: 1: style verb. (if exists, we also allow eg 123: and -2: )
                      //Assignment is not supported for nested bracket: a[][][] +: 1  <--- parse error
                      //save ':' if       a    []?        :    y    ;?        ---> colon
                      //                         verb (should be covered except for   0   :  `file  -> 0:`file )
                      //save ':' if       a    []?    +   :         ;?        ---> monadic verb
                      //save ':' if       a    []?    +   :    y    ;?        ---> dyadic  verb
                      //what passes for y?  <--- anything that isn't an end/\0, except colon
                      //                         verb will go on to ex1 to the right and assign _n
    CS(MARK_ADVERB ,  O("adverb\n");
                      z=(V)(DT_ADVERB_OFFSET+charsAdverb(s[k])+(r>1?3:0)) )
    CS(MARK_END    ,  O("end\n");
		      z=(V)(DT_OFFSET(end)) ) }
  if(!z){}   //TODO: handle null z, which can happen
  switch(-M)   //Things that need to be stored locally
  { CSR(MARK_NAME   , if('_'!=*u && !frc)break;)   //Fall-through
    CSR(MARK_PAREN  ,)
    CSR(MARK_BRACKET,)
    CSR(MARK_BRACE  ,)
    CSR(MARK_NUMBER ,)
    CSR(MARK_QUOTE  ,)
    CS (MARK_SYMBOL , z=newE(LS,z); P(!z,(L)ME)  kap(locals,&z); cd(z); z=EVP(z) ) }   //oom
  frc=0; cd(hh); *p=z; ++*d;
  O("      p: %p    z: %p    r: %lld\n",p,z,r);
  O("      &dict: %p      sd_(*dict,2):",&dict);   if(dict)sd_(*dict,2); else O("\n");
  R r; }
