#include <stdio.h>
#include <stdlib.h>
#include <time.h>

typedef unsigned char uc;
typedef unsigned int ui;

typedef ui *states;
typedef ui **trans;

typedef struct {
   ui n;
   ui m;
   ui s;
   states F;
   trans d;
} DFA;

typedef struct {
   ui n;
   ui m;
   ui S;
   ui F;
   trans D;
} NFA;

NFA readNFA ( char *fname )
{
   FILE *fp;
   NFA N;
   ui n, m;
   int p, q, a;

   fp = (FILE *)fopen(fname, "r");
   if (fp == NULL) {
      fprintf(stderr, "*** Error: Unable to open input file \"%s\"\n", fname);
      exit(1);
   }

   fscanf(fp, "%u", &n);
   N.n = n;

   fscanf(fp, "%u", &m);
   N.m = m;

   N.S = 0;
   while (1) {
      fscanf(fp, "%d", &p);
      if (p == -1) break;
      N.S |= (1U << p);
   }

   N.F = 0;
   while (1) {
      fscanf(fp, "%d", &p);
      if (p == -1) break;
      N.F |= (1U << p);
   }

   N.D = (ui **)malloc(n * sizeof(ui *));
   for (p=0; p<n; ++p) {
      N.D[p] = (ui *)malloc(m * sizeof(ui));
      for (a=0; a<m; ++a) N.D[p][a] = 0;
   }
   while (1) {
      fscanf(fp, "%d", &p);
      if (p == -1) break;
      fscanf(fp, "%d%d", &a, &q);
      N.D[p][a] |= (1U << q);
   }

   fclose(fp);

   return N;
}

void printstates ( states P, ui n )
{
   ui i, j, q, first = 1;

   printf("{");
   i = j = 0;
   for (q=0; q<n; ++q) {
      if (P[i] & (1U << j)) {
         if (!first) printf(",");
         printf("%u", q);
         first = 0;
      }
      ++j;
      if (j == 32) { j = 0; ++i; }
   }
   printf("}");
}

ui countstates ( states P, ui n )
{
   ui i, j, q, cnt;

   i = j = cnt = 0;
   for (q=0; q<n; ++q) {
      if (P[i] & (1U << j)) ++cnt;
       ++j;
      if (j == 32) { j = 0; ++i; }
   }
   return cnt;
}

void printNFA ( NFA N )
{
   int p;
   ui i, n, m, a;

   n = N.n; m = N.m;

   printf("    Number of states: %d\n", n);
   printf("    Input alphabet: {");
   for (i=0; i<m; ++i) printf("%d%s", i, (i < m-1) ? "," : "}\n");
   printf("    Start states: "); printstates(&(N.S),n); printf("\n");
   printf("    Final states: "); printstates(&(N.F),n); printf("\n");
   printf("    Transition function\n");
   for (p=0; p<n; ++p) {
      for (a=0; a<m; ++a) {
         printf("        Delta(%d,%d) = ", p, a);
         printstates(&(N.D[p][a]),n);
         printf("\n");
      }
   }
}

void printDFA ( DFA D )
{
   int p;
   ui i, n, m, a;

   n = D.n; m = D.m;

   printf("    Number of states: %d\n", n);
   printf("    Input alphabet: {");
   for (i=0; i<m; ++i) printf("%d%s", i, (i < m-1) ? "," : "}\n");
   printf("    Start state: %u\n", D.s);
   if (D.n <= 80) {
      printf("    Final states: "); printstates(D.F,n); printf("\n");
      printf("    Transition function\n");
      printf("    a\\p|"); for (p=0; p<n; ++p) printf(" %2d", p); printf("\n");
      printf("    ---+"); for (p=0; p<n; ++p) printf("---"); printf("\n");
      for (a=0; a<m; ++a) {
         printf("     %d |", a);
         for (p=0; p<n; ++p) printf(" %2u", D.d[p][a]);
         printf("\n");
      }
   } else {
      printf("    %u final states\n", countstates(D.F,n));
      printf("    Transition function: Skipped\n");
   }
}

ui Delta ( NFA N, ui p, ui a )
{
   ui q, r;

   r = 0;
   for (q=0; q<N.n; ++q) if (p & (1U << q)) r |= N.D[q][a];
   return r;
}

DFA subsetcons ( NFA N )
{
   DFA D;
   ui i, j, k, p, a, memsize, isfinal;

   D.n = (1U << N.n); memsize = ((D.n + 31) >> 5);

   D.m = N.m;

   D.s = N.S;

   D.F = (states)malloc(memsize * sizeof(ui));
   for (i=0; i<memsize; ++i) D.F[i] = 0;
   for (p=0; p<D.n; ++p) {
      isfinal = 0;
      for (k=0; k<N.n; ++k) {
         if ( (p & N.F) & (1U << k) ) isfinal = 1;
      }
      if (isfinal) {
         i = (p >> 5); j = (p & 31);
         D.F[i] |= (1U << j);
      }
   }

   D.d = (ui **)malloc(D.n * sizeof(ui *));
   for (p=0; p<D.n; ++p) {
      D.d[p] = (ui *)malloc(D.m * sizeof(ui));
      for (a=0; a<N.m; ++a) D.d[p][a] = Delta(N,p,a);
   }

   return D;
}

void DFS ( DFA D, ui p, states visited )
{
   ui i, j, q, a;

   i = (p >> 5); j = (p & 31);
   visited[i] |= (1U << j);
   for (a=0; a<D.m; ++a) {
      q = D.d[p][a];
      if (q == p) continue;
      i = (q >> 5); j = (q & 31);
      if ((visited[i]) & (1U << j)) continue;
      DFS(D,q,visited);
   }
}

states reachable ( DFA D )
{
   states visited;
   ui memsize, i;

   memsize = ((D.n + 31) >> 5);
   visited = (ui *)malloc(memsize * sizeof(ui));
   for (i=0; i<memsize; ++i) visited[i] = 0;
   DFS(D,D.s,visited);
   return visited;
}

DFA rmunreachable ( DFA D, states R )
{
   DFA E;
   int *newno, p, q;
   ui a, r, i, j, memsize;

   newno = (int *)malloc(D.n * sizeof(int));
   for (i=0; i<D.n; ++i) newno[i] = -1;

   E.n = 0;
   for (p=0; p<D.n; ++p) {
      i = (p >> 5); j = (p & 31);
      if (R[i] & (1U << j)) {
         newno[p] = E.n;
         ++(E.n);
      }
   }

   E.m = D.m;

   E.s = newno[D.s];

   memsize = ((E.n + 31) >> 5);
   E.F = (ui *)malloc(memsize * sizeof(ui));
   for (i=0; i<memsize; ++i) E.F[i] = 0;
   for (p=0; p<D.n; ++p) {
      q = newno[p];
      if (q == -1) continue;
      i = (p >> 5); j = (p & 31);
      if (D.F[i] & (1U << j)) {
         i = (q >> 5); j = (q & 31);
         E.F[i] |= (1U << j);
      }
   }

   E.d = (ui **)malloc(E.n * sizeof(ui *));
   for (i=0; i<E.n; ++i) E.d[i] = (ui *)malloc(E.m * sizeof(ui));
   for (p=0; p<D.n; ++p) {
      q = newno[p];
      if (q == -1) continue;
      for (a=0; a<D.m; ++a) {
         r = newno[D.d[p][a]];
         E.d[q][a] = r;
      }
   }

   return E;
}

int notequiv ( DFA D, int **M, int p, int q )
{
   int u, v, t;
   ui a;

   for (a=0; a<D.m; ++a) {
      u = D.d[p][a]; v = D.d[q][a];
      if (u < v) { t = u; u = v; v = t; }
      if (M[u][v]) return 1;
   }
   return 0;
}

/* It is assumed that the matrix M returned is small, so I have been sloppy about its
   data structure. This could anyway have been implemented as an array of bit arrays. */
int **findequiv ( DFA D )
{
   int **M, newmark;
   ui n, p, q, i, j, f1, f2;

   n = D.n;
   M = (int **)malloc(n * sizeof(int *));
   for (p=0; p<n; ++p) {
      M[p] = (int *)malloc((p + 1) * sizeof(int));
      i = (p >> 5); j = (p & 31); f1 = (D.F[i] & (1U << j)); if (f1) f1 = 1;
      for (q=0; q<=p; ++q) {
         i = (q >> 5); j = (q & 31); f2 = (D.F[i] & (1U << j)); if (f2) f2 = 1;
         M[p][q] = (f1 ^ f2);
      }
   }

   newmark = 1;
   while (newmark) {
      newmark = 0;
      for (p=0; p<n; ++p) {
         for (q=0; q<=p; ++q) {
            if (M[p][q] == 0) {
               if (notequiv(D,M,p,q)) {
                  M[p][q] = 1;
                  ++newmark;
               }
            }
         }
      }
   }

   return M;
}

DFA collapse ( DFA D, int **M )
{
   int *newno, p, q, i, j, first;
   ui a, memsize;
   DFA E;

   newno = (int *)malloc(D.n * sizeof(int));
   for (i=0; i<D.n; ++i) newno[i] = -1;
   newno[0] = 0; E.n = 1;
   for (p=1; p<D.n; ++p) {
      for (q=0; q<p; ++q) {
         if (M[p][q] == 0) {
            if (newno[q] >= 0) newno[p] = newno[q];
         }
      }
      if (newno[p] == -1) newno[p] = (E.n)++;
   }

   printf("\n+++ Equivalent states\n");
   for (i=0; i<E.n; ++i) {
      first = 1;
      printf("    Group %2d: {", i);
      for (p=0; p<D.n; ++p) if (newno[p] == i) {
         if (!first) printf(",");
         printf("%d",p);
         first = 0;
      }
      printf("}\n");
   }

   E.m = D.m;

   E.s = newno[D.s];

   memsize = ((E.n + 31) >> 5);
   E.F = (ui *)malloc(memsize * sizeof(ui));
   for (p=0; p<D.n; ++p) {
      i = (p >> 5); j = (p & 31);
      if (D.F[i] & (1U << j)) {
         q = newno[p];
         i = (q >> 5); j = (q & 31);
         E.F[i] |= (1U << j);
      }
   }

   E.d = (ui **)malloc(E.n * sizeof(ui *));
   for (p=0; p<E.n; ++p) E.d[p] = (ui *)malloc(E.m * sizeof(ui));
   for (p=0; p<D.n; ++p) {
      for (a=0; a<E.m; ++a) {
         E.d[newno[p]][a] = newno[D.d[p][a]];
      }
   }

   return E;
}

int main ( int argc, char *argv[] )
{
   NFA N;
   DFA D, D1, D2;
   states R;
   int **M;

   srand((unsigned int)time(NULL));

   if (argc > 1) N = readNFA(argv[1]);
   else {
      fprintf(stderr, "*** Supply a file name in the command line\n");
      exit(2);
   }

   printf("\n+++ Input NFA\n"); printNFA(N);

   D = subsetcons(N);
   printf("\n+++ Converted DFA\n"); printDFA(D);

   R = reachable(D);
   printf("\n+++ Reachable states: "); printstates(R,D.n); printf("\n");

   D1 = rmunreachable(D,R);
   printf("\n+++ Reduced DFA after removing unreachable states\n"); printDFA(D1);

   M = findequiv(D1);
   D2 = collapse(D1,M);
   printf("\n+++ Reduced DFA after collapsing equivalent states\n"); printDFA(D2);

   printf("\n");

   exit(0);
}