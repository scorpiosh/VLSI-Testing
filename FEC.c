#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>

/* ---------- Node set (distinct nets) ---------- */
typedef struct {
    unsigned char *bits;  /* bits[id]=1 if net exists; index 0 unused */
    size_t cap;
} NodeSet;

static void die(const char *m){ fprintf(stderr,"Error: %s\n",m); exit(1); }
static void *xrealloc(void *p,size_t n){ void*q=realloc(p,n); if(!q) die("oom"); return q; }

static void ns_init(NodeSet *s,size_t init){
    s->cap = (init<2?2:init);
    s->bits = (unsigned char*)calloc(s->cap,1);
    if(!s->bits) die("oom");
}
static void ns_ensure(NodeSet *s,size_t need){
    if(need < s->cap) return;
    size_t nc=s->cap; while(nc<=need) nc*=2;
    s->bits = (unsigned char*)xrealloc(s->bits,nc);
    memset(s->bits+s->cap,0,nc-s->cap);
    s->cap = nc;
}
static void ns_add(NodeSet *s,long id){
    if(id<=0) return;
    ns_ensure(s,(size_t)id+1);
    s->bits[id]=1;
}

/* ---------- Gate list ---------- */
typedef enum { G_AND, G_OR, G_NAND, G_NOR, G_UNKNOWN } GType;
typedef struct { GType t; long out, in1, in2; } Gate;

static GType gtype(const char *t){
    char u[16]; size_t i=0; if(!t) return G_UNKNOWN;
    for(; t[i]&&i+1<sizeof(u); ++i) u[i]=(char)toupper((unsigned char)t[i]); u[i]='\0';
    if(!strcmp(u,"AND")) return G_AND;
    if(!strcmp(u,"OR")) return G_OR;
    if(!strcmp(u,"NAND")) return G_NAND;
    if(!strcmp(u,"NOR")) return G_NOR;
    return G_UNKNOWN;
}
static int is_kw(const char *t,const char*kw){
    if(!t) return 0; char u[16]; size_t i=0;
    for(; t[i]&&i+1<sizeof(u); ++i) u[i]=(char)toupper((unsigned char)t[i]); u[i]='\0';
    return !strcmp(u,kw);
}
static int parse_int(const char *tok,long *out){
    if(!tok) return 0; char *e=NULL; long v=strtol(tok,&e,10);
    if(e==tok || *e!='\0') return 0; *out=v; return 1;
}

/* ---------- Union-Find over faults ---------- */
/* Map fault (node id, sa bit) -> index: idx = 2*(id-1) + sa (sa: 0 for sa0, 1 for sa1) */
typedef struct {
    int *p,*r;  /* parent, rank */
    size_t n;   /* size */
} DSU;

static void dsu_init(DSU *d, size_t n){ d->n=n; d->p=(int*)malloc(n*sizeof(int)); d->r=(int*)calloc(n,sizeof(int));
    if(!d->p||!d->r) die("oom");
    for(size_t i=0;i<n;++i) d->p[i]=(int)i;
}
static int dsu_find(DSU *d,int x){ return d->p[x]==x?x:(d->p[x]=dsu_find(d,d->p[x])); }
static void dsu_union(DSU *d,int a,int b){
    a=dsu_find(d,a); b=dsu_find(d,b); if(a==b) return;
    if(d->r[a]<d->r[b]) d->p[a]=b;
    else if(d->r[a]>d->r[b]) d->p[b]=a;
    else { d->p[b]=a; d->r[a]++; }
}

/* helper: index for (node, sa) */
static inline int fault_idx(long node, int sa){ return (int)(2*(node-1) + (sa?1:0)); }

/* ---------- Main ---------- */
int main(int argc, char **argv){
    if(argc<2){
        fprintf(stderr,"Usage: %s <netlist.txt> [--list-classes]\n", argv[0]);
        return 1;
    }
    const char *path=argv[1];
    int list_classes = (argc>=3 && strcmp(argv[2],"--list-classes")==0);

    FILE *fp=fopen(path,"r"); if(!fp) die("cannot open netlist");

    NodeSet nodes; ns_init(&nodes,1024);
    Gate *gates=NULL; size_t ng=0, capg=0;

    char buf[1024]; size_t lineno=0;
    while(fgets(buf,sizeof(buf),fp)){
        ++lineno;
        char *p=buf; while(*p && isspace((unsigned char)*p)) ++p;
        if(*p=='\0' || *p=='#') continue;
        char *nl=strchr(p,'\n'); if(nl) *nl='\0';

        char *save=NULL;
        char *tok=strtok_r(p," \t\r",&save);
        if(!tok) continue;

        if(is_kw(tok,"INPUT") || is_kw(tok,"OUTPUT") || is_kw(tok,"FANOUT")){
            long id; char *t=NULL;
            while((t=strtok_r(NULL," \t\r",&save))){
                if(parse_int(t,&id)) ns_add(&nodes,id);
            }
            continue;
        }

        GType gt=gtype(tok);
        if(gt!=G_UNKNOWN){
            long o=0,i1=0,i2=0;
            char *t1=strtok_r(NULL," \t\r",&save);
            char *t2=strtok_r(NULL," \t\r",&save);
            char *t3=strtok_r(NULL," \t\r",&save);
            if(!parse_int(t1,&o)||!parse_int(t2,&i1)||!parse_int(t3,&i2)){
                fprintf(stderr,"Line %zu: malformed gate\n", lineno);
                continue;
            }
            ns_add(&nodes,o); ns_add(&nodes,i1); ns_add(&nodes,i2);
            if(ng>=capg){ capg = capg?capg*2:256; gates = (Gate*)xrealloc(gates,capg*sizeof(Gate)); }
            gates[ng++] = (Gate){gt,o,i1,i2};
            continue;
        }

        /* ignore unknown trailing labels */
    }
    fclose(fp);

    /* Build DSU over existing faults (compact by using max id) */
    long max_id = (long)nodes.cap - 1;
    long line_count=0;
    for(long i=1;i<=max_id;++i) if(nodes.bits[i]) ++line_count;
    long initial_faults = line_count * 2;

    /* We allocate DSU for indices up to max_id even if some ids unused (simple) */
    size_t dsu_size = (size_t) (2 * (max_id>0?max_id:1));
    DSU dsu; dsu_init(&dsu, dsu_size);

    /* ---------- Equivalence rules ---------- */

    for(size_t k=0;k<ng;++k){
        Gate g = gates[k];

        /* 1) Symmetry-based input equivalence */
        if(g.t==G_AND || g.t==G_NAND){
            /* sa0_in1 == sa0_in2 */
            if(g.in1>0 && g.in2>0){
                dsu_union(&dsu, fault_idx(g.in1,0), fault_idx(g.in2,0));
            }
        } else if(g.t==G_OR || g.t==G_NOR){
            /* sa1_in1 == sa1_in2 */
            if(g.in1>0 && g.in2>0){
                dsu_union(&dsu, fault_idx(g.in1,1), fault_idx(g.in2,1));
            }
        }

        /* 2) Inverter detection (NAND a,a -> NOT) */
        if(g.t==G_NAND && g.in1==g.in2 && g.in1>0){
            long a=g.in1, o=g.out;
            /* input sa0 <-> output sa1 ; input sa1 <-> output sa0 */
            dsu_union(&dsu, fault_idx(a,0), fault_idx(o,1));
            dsu_union(&dsu, fault_idx(a,1), fault_idx(o,0));
        }

        /* (Optional) NOR a,a -> NOT: uncomment if present in your netlists
        if(g.t==G_NOR && g.in1==g.in2 && g.in1>0){
            long a=g.in1, o=g.out;
            dsu_union(&dsu, fault_idx(a,0), fault_idx(o,0)); // since NOR(a,a)=~a, check mapping carefully
            dsu_union(&dsu, fault_idx(a,1), fault_idx(o,1));
        }
        */
    }

    /* ---------- Emit representatives ---------- */
    /* We keep exactly one fault per equivalence class among existing nodes. */
    int *mark = (int*)calloc(dsu_size, sizeof(int));
    if(!mark) die("oom");

    long kept=0;
    for(long id=1; id<=max_id; ++id){
        if(!nodes.bits[id]) continue;
        for(int sa=0; sa<=1; ++sa){
            int idx = fault_idx(id, sa);
            int root = dsu_find(&dsu, idx);
            if(!mark[root]) { mark[root]=1; kept++; }
        }
    }

    /* Print summary */
    printf("Initial faults: %ld\n", initial_faults);
    printf("Collapsed (equivalence) faults: %ld\n", kept);
    if(kept>0) printf("Collapse ratio: %.2f\n", (double)initial_faults / (double)kept);
    printf("----\nKept representatives:\n");

    /* Print one representative name per class */
    /* Choose the smallest (id,sa) in the class as representative when we encounter it first */
    memset(mark,0,dsu_size*sizeof(int));
    for(long id=1; id<=max_id; ++id){
        if(!nodes.bits[id]) continue;
        for(int sa=0; sa<=1; ++sa){
            int idx = fault_idx(id, sa);
            int root = dsu_find(&dsu, idx);
            if(!mark[root]){
                mark[root]=1;
                printf("%s_%ld\n", sa? "sa1":"sa0", id);
            }
        }
    }

    /* Optional: list full classes
    if(list_classes){
        printf("----\nClasses:\n");
        for(size_t r=0;r<dsu_size;++r){
            if(dsu_find(&dsu,(int)r)!= (int)r) continue; 
            int printed=0;
            for(long id=1; id<=max_id; ++id){
                if(!nodes.bits[id]) continue;
                for(int sa=0; sa<=1; ++sa){
                    int idx=fault_idx(id,sa);
                    if(dsu_find(&dsu,idx)==(int)r){
                        if(!printed){ printf("{ "); printed=1; }
                        printf("%s_%ld ", sa?"sa1":"sa0", id);
                    }
                }
            }
            if(printed) printf("}\n");
        }
    }
    */

    /* cleanup */
    free(mark);
    free(dsu.p); free(dsu.r);
    free(gates);
    free(nodes.bits);
    return 0;
}
