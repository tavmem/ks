L charsAdverb(C c);
extern V adverbs[];
extern I fbr;
extern I feci;
extern K sd(K x);
extern K sd_(K x,I f);
extern K stopDict;
extern I fStop;
V alloc(size_t sz);
L charsVerb(C c);
I SC(S a,S b);
K *denameS(S dir_string,S t,I create);
K EV(K e);
K newEntry(S s);
extern V vn_[];
K _n();
extern S n_s;
S sp(S k);
K formKfCS(S s);
K formKiCS(S s);
S strdupn(S s,I k);
extern S IFP[3];
K DE(K d,S b);
K Kd();
K kerr(cS s);
K *EVP(K e);
K *EAP(K e);
K DI(K d,I i);
K kap(K *a,V v);
K ci(K a);
extern S LS;
K newE(S s,K k);
I sva(V p);
I adverbClass(V p);
I bk(V p);
extern V offsetSSR,offsetWhat,offsetAt,offsetDot,offsetColon;
extern S param_dfa;
I sz(I t,I n);
I lsz(I k);
I capture(S s,I n,I k,I *m,V *w,I *d,K *locals,K *dict,K func);
K Kv();
K cd(K a);
void pdafree(PDA p);
K newK(I t,I n);
K backslash(S s,I n,K*dict);
extern S d_;
extern K KTREE;
K *denameD(K *d,S t,I create);
K wd_(S s,int n,K *dict,K func);
K wd(S s,int n);
I maX(I a,I b);
I mark(I *m,I k,I t);
enum mark_members {MARK_UNMARKED,MARK_IGNORE,MARK_BRACKET,MARK_END,MARK_PAREN,MARK_BRACE,MARK_QUOTE,MARK_SYMBOL,
                  MARK_NAME,MARK_NUMBER,MARK_VERB,MARK_ADVERB,MARK_CONDITIONAL,MARK_COUNT};
typedef enum mark_members mark_members;
#define EXPORT_INTERFACE 0
I isCharVerb(C c);
I stringHasChar(S s,C c);
C bottom(PDA p);
C pop(PDA p);
C peek(PDA p);
I push(PDA p,C c);
PDA newPDA();
I complete(S a,I n,PDA *q,I *marks);
I parsedepth(PDA p);
extern S right;
extern S left;
extern S formed_dfa;
I charpos(S s,C c);
K lookupEntryOrCreate(K *p,S k);
I oerr();
