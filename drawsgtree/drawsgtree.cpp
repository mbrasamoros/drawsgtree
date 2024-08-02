/*
 *
 * Copyright (c) 2022, 2023, 2024 Maria Bras-Amoros
 *
 * Distributed under the terms of the GNU General Public License
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
 *
 * See the GNU General Public License for more details.
 * The full text is available at http:
 *
 * Last update: August 1, 2024
 *
 */

#include <cstring>
#include <getopt.h>
#include <iostream>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>

#define MAX 100

long int ng[MAX] = {1, 1, 2, 4, 7, 12,
                    23, 39, 67, 118, 204, 343,
                    592, 1001, 1693, 2857, 4806, 8045,
                    13467, 22464, 37396, 62194, 103246, 170963,
                    282828, 467224, 770832, 1270267, 2091030, 3437839,
                    5646773, 9266788, 15195070, 24896206, 40761087, 66687201,
                    109032500, 178158289};

int pattern[MAX] = {1, 1, -1};
int patternlength = 3;
char patpolynomial[300] = "x_{1}+x_{2}-x_{3}";

bool incremental = false;
bool standalone = true;
bool vertical = false;
bool plain = false;
bool blackandwhite = false;
bool rotated = false;
bool framednodes = false;
bool scaled = false;
bool defaultfilename = true;

bool optionemptynodes = true;
bool optionlist = false;
bool optiongenerators = false;
bool optiongapset = false;
bool optiongapseedbitstream = false;
bool optionseedstable = false;
bool optiondyckhook = false;
bool optionaperykunzposet = false;
bool optionpsystemgenerators = false;

bool distinguishededges = false;
bool trimnondistinguishededges = false;

bool ordinarizationtree = false;
bool quasiordinarizationforest = false;

bool optioninfinitechains = false;
bool optionmed = false;
bool optionpattern = false;

int max(int i, int j) {
  if (i > j)
    return i;
  return j;
}

int prepend(char pre[], char str[]) {
  char aux[100];
  strcpy(aux, pre);
  strcat(aux, str);
  strcpy(str, aux);
  return 0;
}

int nongapstoG(int N[], int c, int G[]) {
  int i = 0, jN = 1;
  for (i = 0; i < c; i++) {
    if (N[jN] == i + 1) {
      G[i] = 0;
      jN++;
    } else
      G[i] = 1;
  }
  return 0;
}

int issemigroup(int N[], int indexc) {
  int i, j, c, G[100];
  if (N[0])
    return 0;
  c = N[indexc];
  nongapstoG(N, c, G);
  for (i = 1; i < c; i++)
    if (!G[i - 1]) {
      for (j = 1; j < c - i; j++)
        if (!G[j - 1] && G[i + j - 1]) {
          return 0;
        }
    }
  return 1;
}

int belongstoinfinitechain(int G[], int c, int m, int indexc) {
  int i, divisorcandidate, isdivisor;
  if (indexc < 2)
    return 1;
  for (divisorcandidate = 2; divisorcandidate <= m; divisorcandidate++) {
    isdivisor = 1;
    for (i = 1; isdivisor && i < c; i++) {
      if (!G[i - 1] && i % divisorcandidate)
        isdivisor = 0;
    }
    if (isdivisor)
      return 1;
  }
  return 0;
}

int GtoS(int G[], int c, int S[]) {
  int i, j, k;
  if (c == 0) {
    S[0] = 0;
    S[1] = 1;
  }
  for (i = 0; i < c; i++) {
    j = i;
    while (j > 0 && G[j - 1] == 1)
      j--;
    S[i] = 1;
    for (k = 1; k <= (c + i - 2 * j) / 2 && S[i] == 1; k++) {
      if (G[i - j + c - k - 1] == 0 && G[j + k - 1] == 0)
        S[i] = 0;
    }
  }
  return 0;
}

int GStoAP(int G[], int S[], int c, int m, int g, int A[MAX], int P[][MAX]) {
  unsigned char r, l, e, previouse, i, j, k;

  for (r = 0; r < m; r++) {
    A[r] = 0;
    for (l = 0; l < m; l++) {
      P[r][l] = 0;
    }
  }

  if (c == m) {
    e = m;
    A[0] = m;
    for (r = 1; r < m; r++) {
      P[r][0] = 1;
      A[r] = m + r;
    }
  } else {
    e = 1;
    for (r = 1; r < c - m; r++) {
      if (!G[r + m - 1]) {
        for (l = 0; l < r && (G[l + m - 1] || r - l - m < 0 ||
                              (r - l - m >= 0 && G[r - l - 1]));
             ++l)
          ;
        if (l >= r) {
          e++;
          P[r % m][0] = 1;
          A[r % m] = r + m;
        }
      }
    }
    for (r = c - m; r < c; r++)
      if (S[r + m - c]) {
        e++;
        P[r % m][0] = 1;
        A[r % m] = r + m;
      }
  }
  l = 1;
  previouse = e;
  while (previouse < m) {
    previouse = e;
    l++;
    for (i = 1; i < m; i++)
      if (P[i][0] == l - 1) {
        for (j = 1; j < m; j++)
          if (P[j][0] == 1) {
            if (!A[(i + j) % m] && A[i] + A[j] - m < c &&
                G[A[i] + A[j] - m - 1]) {
              A[(i + j) % m] = A[i] + A[j];
              e++;
              P[(i + j) % m][0] = l;
              P[(i + j) % m][i] = 1;
              if (A[i] - A[j] < c && G[A[i] - A[j] - 1])
                P[(i + j) % m][j] = 1;

              for (k = 1; k < m; k++) {
                if (k != i && P[(i + j) % m][k] && A[i] - A[k] > m) {
                  if (A[i] - A[k] >= c || !S[A[i] - A[k] - c]) {
                    P[(i + j) % m][k] = 0;
                  }
                }
              }

            } else {
              {
                if (A[i] + A[j] == A[(i + j) % m]) {
                  P[(i + j) % m][i] = 1;
                  if (A[i] - A[j] < c && G[A[i] - A[j] - 1])
                    P[(i + j) % m][j] = 1;

                  for (k = 1; k < m; k++) {
                    if (k != i && P[(i + j) % m][k] && A[i] - A[k] > m) {
                      if (A[i] - A[k] >= c || !S[A[i] - A[k] - c]) {
                        P[(i + j) % m][k] = 0;
                      }
                    }
                    if (k != j && P[(i + j) % m][k] && A[k] - A[j] > m) {
                      if (A[k] - A[j] >= c || !S[A[k] - A[j] - c]) {
                        P[(i + j) % m][j] = 0;
                      }
                    }
                  }

                  if (P[(i + j) % m][0] < l) {
                    P[(i + j) % m][0] = l;
                  }
                }
              }
            }
          }
      }
  }
  return e;
}

int ismed(int G[], int S[], int c, int m) {
  int e = 0, i, j, isgenerator;
  if (m < c)
    e = 1;
  for (i = m + 1; i < c; i++) {
    if (!G[i - 1]) {
      isgenerator = 1;
      for (j = m; j <= i - m && isgenerator; j++) {
        if (!G[j - 1] && !G[i - j - 1])
          isgenerator = 0;
      }
      if (isgenerator)
        e++;
    }
  }
  for (i = c; i < c + m; i++) {
    if (S[i - c])
      e++;
  }
  return (e == m);
}

int isadmissible(int p[], int n) {
  int sum, i;
  if (n == 0)
    return 1;
  sum = p[0];
  for (i = 1; sum >= 0 && i < n; i++)
    sum = sum + p[i];
  return (sum >= 0);
}

int isstronglyadmissible(int p[], int n) {
  int i, pp[MAX];
  for (i = 0; i < n; i++)
    pp[i] = p[i];
  if (pp[0] < 1) {
    printf("Pattern error\n");
    return 0;
  }
  if (pp[0] == 1) {
    for (i = 0; i < n - 1; i++)
      pp[i] = pp[i + 1];
    n--;
    return isadmissible(pp, n);
  }
  pp[0] = pp[0] - 1;
  return isadmissible(pp, n);
}

void stepset(int *set, int n) {
  int i, j;
  i = n - 1;
  while (i > 0 && set[i] == set[i - 1])
    i--;
  set[i] = set[i] + 1;
  for (j = i + 1; j < n; j++)
    set[j] = 0;
}

int belongstosemigroup(int N[], int c, int indexc, int i) {
  int j;
  if (i == 0 || i >= c)
    return 1;
  for (j = 1; j < indexc; j++)
    if (N[j] == i)
      return 1;
  return 0;
}

int admits(int N[], int c, int indexc, int p[], int n) {
  int *set, x, i;
  set = (int *)calloc(n, sizeof(int));
  stepset(set, n);
  while (set[0] < indexc) {
    x = 0;
    for (i = 0; i < n; i++)
      x = x + p[i] * N[set[i]];
    if (!belongstosemigroup(N, c, indexc, x)) {
      free(set);
      return 0;
    }
    stepset(set, n);
  }
  free(set);
  return 1;
}

int drawnodelist(int G[], int S[], int c, int m, int g, FILE *fout) {
  int i;
  if (quasiordinarizationforest) {
    int sc = c - 2;
    int check;
    if (!G[sc - 1]) {
      while (!G[sc - 2])
        sc--;
    }

    fprintf(fout, "{$\\nongap{0}");
    for (i = 1; i < sc; i++)
      if (!G[i - 1])
        fprintf(fout, "\\nongap{%d}", i);
      else
        fprintf(fout, "\\gap{%d}", i);
    if (G[sc - 1])
      fprintf(fout, "\\gap{%d}", sc);
    else {
      for (i = sc; i < c - 1; i++) {
        check = 1;
        for (int j = m; j <= i - m && check; j++) {
          if (!G[j - 1] && !G[i - j - 1])
            check = 0;
        }
        if (check)
          fprintf(fout, "\\generator{%d}", i);
        else
          fprintf(fout, "\\nongap{%d}", i);
      }
    }
    fprintf(fout, "\\gap{%d}", c - 1);
    for (i = c; i < 2 * g + 2; i++) {
      fprintf(fout, "\\nongap{%d}", i);
    }
    fprintf(fout, "\\dotscircles");
    fprintf(fout, "$} ");
  } else {
    fprintf(fout, "{$\\nongap{0}");
    for (i = 1; i < c; i++)
      if (!G[i - 1])
        fprintf(fout, "\\nongap{%d}", i);
      else
        fprintf(fout, "\\gap{%d}", i);
    if (g > 0) {
      if (S[0])
        fprintf(fout, "\\generator{%d}", c);
      else
        fprintf(fout, "\\nongap{%d}", c);
      for (i = c + 1; i < c + m && i < 2 * g + 2; i++) {
        if (S[i - c])
          fprintf(fout, "\\generator{%d}", i);
        else
          fprintf(fout, "\\nongap{%d}", i);
      }
      for (i = c + m; i < 2 * g + 2; i++)
        fprintf(fout, "\\nongap{%d}", i);
      fprintf(fout, "\\dotscircles");
    } else {
      fprintf(fout, "\\generator{1}\\nongap{2}");
      fprintf(fout, "\\dotscircles");
    }
    fprintf(fout, "$} ");
  }
  return 0;
}

int drawnodegenerators(int G[], int S[], int c, int m, int g, FILE *fout) {
  int i, j, isgenerator, mid = 1;
  if (g == 0) {
    fprintf(fout, "{\\scalebox{5.}{$\\langle 1\\rangle$}} ");
    return 0;
  }
  if (m < c)
    fprintf(fout, "{\\scalebox{5.}{$\\langle %d", m);
  else
    fprintf(fout, "{\\scalebox{5.}{$\\langle ");
  for (i = m + 1; i < c; i++) {
    if (!G[i - 1]) {
      isgenerator = 1;
      for (j = m; j <= i - m && isgenerator; j++) {
        if (!G[j - 1] && !G[i - j - 1])
          isgenerator = 0;
      }
      if (isgenerator)
        fprintf(fout, ", %d", i);
    }
  }
  for (i = c; i < c + m; i++) {
    if (S[i - c]) {
      if (mid) {
        fprintf(fout, "\\mid %d", i);
        mid = 0;
      } else
        fprintf(fout, ", %d", i);
    }
  }
  if (mid)
    fprintf(fout, "\\mid ");
  fprintf(fout, "\\rangle_{c=%d}$}} ", c);
  return 0;
}

int drawnodegapset(int G[], int c, int m, int g, FILE *fout) {
  int i, j, q;
  char str[300], straux[300], strtemp[300];
  if (g == 0) {
    fprintf(fout, "{$\\bullet$} ");
    return 0;
  }
  fprintf(fout, "{\\begin{tabular}{c}");
  q = (c + m - 1) / m;
  sprintf(str, " ");
  for (i = q - 1; i >= 0; i--) {
    sprintf(strtemp, "(");
    for (j = 1; j < m; j++) {
      if (G[m * i + j - 1] && m * i + j - 1 < c) {
        if (!plain)
          fprintf(fout, "\\gapingapset{%d}", m * i + j);
        sprintf(straux, "%d", j);
        strcat(strtemp, straux);
      } else {
        if (!plain)
          fprintf(fout, "\\nongapingapset{%d}", m * i + j);
      }
    }
    if (!plain)
      fprintf(fout, "\\\\");
    memcpy(straux, str, strlen(str) + 1);
    strcpy(str, strtemp);
    strcat(str, ")");
    strcat(str, straux);
  }
  fprintf(fout, "\\\\");
  fprintf(fout, "\\scalebox{4.}{%s}", str);
  fprintf(fout, "\\end{tabular}} ");
  return 0;
}

int drawnodegapseedbitstream(int G[], int S[], int c, int m, int g,
                             FILE *fout) {
  int i;
  fprintf(fout, "{$\\begin{array}{l}\\phantom{\\nonseed{0}}");
  for (i = 0; i < c; i++) {
    if (!G[i])
      fprintf(fout, "\\nonseed{%d}", i);
    else
      fprintf(fout, "\\seed{%d}", i);
  }
  for (i = c; i < 2 * g + 2; i++)
    fprintf(fout, "\\phantom{\\nonseed{0}}");
  fprintf(fout, "\\\\\\phantom{\\nonseed{0}}");
  for (i = 0; i < c; i++) {
    if (S[i])
      fprintf(fout, "\\seed{%d} ", i);
    else
      fprintf(fout, "\\nonseed{%d} ", i);
  }
  for (i = c; i < 2 * g + 2; i++)
    fprintf(fout, "\\phantom{\\nonseed{0}}");
  fprintf(fout, "\\end{array}$} ");
  return 0;
}

int drawnodeseedstable(int G[], int S[], int c, int m, int g, FILE *fout) {
  int i, j, k, jant, firstrow;
  char row[300], straux[300];

  if (g == 0) {
    fprintf(fout, "{$\\bullet$} ");
    return 0;
  }
  fprintf(fout,
          "{{\\bf \\begin{tabular}{|@{\\rule[-.15cm]{0pt}{.5cm}}*{%d}{M |}}",
          m);
  jant = 0;
  firstrow = 1;
  i = 0;
  if (S[i])
    sprintf(row, " \\coloredseed %d ", S[i]);
  else
    sprintf(row, " \\cellcolor{white} %d ", S[i]);
  j = 1;
  for (i = 1; i < c; i++)
    if (G[i - 1]) {
      sprintf(straux, "%d ", S[i]);
      if (S[i]) {
        strcat(row, " & \\coloredseed ");
        strcat(row, straux);
      } else {
        strcat(row, " & \\cellcolor{white} ");
        strcat(row, straux);
      }
      j++;
    } else {
      if (firstrow)
        firstrow = 0;
      else
        fprintf(fout, "\\\\");
      fprintf(fout, "\\hhline{|");
      for (k = 1; k <= max(j, jant); k++)
        fprintf(fout, "-|");
      fprintf(fout, "}\n");
      fprintf(fout, " %s ", row);
      if (S[i])
        sprintf(row, " \\coloredseed %d ", S[i]);
      else
        sprintf(row, " \\cellcolor{white} %d ", S[i]);
      jant = j;
      j = 1;
    }
  if (!firstrow)
    fprintf(fout, "\\\\");
  fprintf(fout, "\\hhline{|");
  for (k = 1; k <= max(j, jant); k++)
    fprintf(fout, "-|");
  fprintf(fout, "}\n");
  fprintf(fout, " %s \\\\", row);
  fprintf(fout, "\\hhline{|");
  for (k = 1; k <= j; k++)
    fprintf(fout, "-|");
  fprintf(fout, "}\n");

  fprintf(fout, "\\end{tabular}}} ");

  return 0;
}

int drawnodedyckhook(int G[], int c, int g, FILE *fout) {
  int j, a, b;
  if (g == 0) {
    fprintf(fout, "{$\\bullet$} ");
    return 0;
  }
  fprintf(fout,
          "{\\scalebox{1.75}{{\\bf "
          "\\begin{tabular}{|@{\\rule[-.15cm]{0pt}{.5cm}}*{%d}{M |}}",
          c - g);
  fprintf(fout, "\\cline{1-%d}\n", c - g);
  for (b = c - 1; b >= 1; b--) {
    if (G[b - 1]) {
      fprintf(fout, " %d ", b);
      j = 1;
      for (a = 1; a < b; a++) {
        if (!G[a - 1]) {
          fprintf(fout, "& %d ", b - a);
          j++;
        }
      }
      fprintf(fout, "\\\\\\cline{1-%d}\n", j);
    }
  }
  fprintf(fout, "\\end{tabular}}}} ");
  return 0;
}

int drawnodeaperykunzposet(int G[], int S[], int c, int m, int g, FILE *fout) {
  int i, j, l, maxl, P[MAX][MAX], A[MAX];

  GStoAP(G, S, c, m, g, A, P);
  maxl = P[1][0];
  for (i = 2; i < m; i++)
    if (P[i][0] > maxl)
      maxl = P[i][0];

  fprintf(fout, "{\\scalebox{2.}{\\begin{tabular}{c}");
  fprintf(fout, "\\scalebox{1.75}{A: %d", 0);
  for (i = 1; i < m; i++) {
    fprintf(fout, ", %d", A[i]);
  }
  fprintf(fout, "}\\\\");
  if (g > 0) {
    fprintf(fout, "\\scalebox{1.75}{K: %d", A[1] / m);
    for (i = 2; i < m; i++) {
      fprintf(fout, ", %d", A[i] / m);
    }
    fprintf(fout, "}\\\\");
  }

  fprintf(fout, "\\fbox{\\begin{tikzpicture}");
  for (l = 1; l <= maxl; l++) {
    for (i = 1; i < m; i++)
      if (P[i][0] == l)
        fprintf(fout, "\\node[draw,circle] (%d) at (%d,%d) {%d};\n", i, i, l,
                i);
  }
  for (i = 1; i < m; i++) {
    for (j = 1; j < m; j++)
      if (P[i][j])
        fprintf(fout, "\\draw (%d) to (%d);", i, j);
  }
  fprintf(fout, "\\end{tikzpicture}}\\end{tabular}}} ");
  return 0;
}

int admitspunctured(int N[], int c, int indexc, int p[], int n, int lambda) {
  int *set, x, i, setcontainslambda = 0;
  for (i = indexc; i < indexc + lambda - c; i++)
    N[i] = i + c - indexc;
  set = (int *)calloc(n, sizeof(int));
  stepset(set, n);
  while (set[0] < indexc || set[0] < lambda - c + indexc) {
    setcontainslambda = 0;
    x = 0;
    for (i = 0; i < n && !setcontainslambda; i++) {
      if (N[set[i]] == lambda)
        setcontainslambda = 1;
      else {
        x = x + p[i] * N[set[i]];
      }
    }
    if (!setcontainslambda && x == lambda) {
      free(set);
      return 0;
    }
    stepset(set, n);
  }
  free(set);
  return 1;
}

int drawnodepsystemgenerators(int N[], int G[], int S[], int c, int indexc,
                              int m, int p[], int n, FILE *fout) {
  int i, j, isgenerator;

  if (!admits(N, c, indexc, p, n)) {
    fprintf(fout, "{\\scalebox{3.}{does not admit $p$}} ");
    return 0;
  }

  fprintf(fout, "{\\scalebox{5.}{$\\langle %d", m); // Corollary 15
  for (i = m + 1; i < c; i++) {
    if (!G[i - 1]) {
      isgenerator = 1;
      for (j = m; j <= i - m && isgenerator; j++) {
        if (!G[j - 1] && !G[i - j - 1])
          isgenerator = 0;
      }
      if (isgenerator && admitspunctured(N, c, indexc, p, n, i))
        fprintf(fout, ",%d", i);
    }
  }
  if (m < c) {
    if (S[0] && admitspunctured(N, c, indexc, p, n, c))
      fprintf(fout, ",%d", c);
  }
  for (i = c + 1; i < c + m; i++) {
    if (S[i - c] && admitspunctured(N, c, indexc, p, n, i))
      fprintf(fout, ",%d", i);
  }
  fprintf(fout, "\\rangle_{%s", patpolynomial);
  fprintf(fout, "}$}} ");
  return 0;
}

int drawnode(int N[], int G[], int S[], int c, int m, int g, FILE *fout) {
  if (optionemptynodes) {
    fprintf(fout, "{} ");
    return 0;
  }
  if (framednodes)
    fprintf(fout, "{\\fbox");
  fprintf(fout, "{\\begin{tabular}{c}");
  if (optionlist) {
    drawnodelist(G, S, c, m, g, fout);
    fprintf(fout, "\\\\");
  }
  if (optiongenerators) {
    drawnodegenerators(G, S, c, m, g, fout);
    fprintf(fout, "\\\\");
  }
  if (optionpsystemgenerators) {
    drawnodepsystemgenerators(N, G, S, c, c - g, m, pattern, patternlength,
                              fout);
    fprintf(fout, "\\\\");
  }
  if (optiongapset) {
    drawnodegapset(G, c, m, g, fout);
    fprintf(fout, "\\\\");
  }
  if (optiongapseedbitstream) {
    fprintf(fout, "[20pt]");
    drawnodegapseedbitstream(G, S, c, m, g, fout);
    fprintf(fout, "\\\\");
  }
  if (optionseedstable) {
    drawnodeseedstable(G, S, c, m, g, fout);
    fprintf(fout, "\\\\");
  }
  if (optiondyckhook) {
    drawnodedyckhook(G, c, g, fout);
    fprintf(fout, "\\\\");
  }
  if (optionaperykunzposet) {
    drawnodeaperykunzposet(G, S, c, m, g, fout);
  }
  if (framednodes)
    fprintf(fout, "\\end{tabular}}} ");
  else
    fprintf(fout, "\\end{tabular}} ");
  return 0;
}

long int descendants(int N[], int G[], int S[], int c, int indexc, int g,
                     int ming, int maxg, bool m_set, FILE *fout) {
  int i, s;
  int newN[200], newG[200], newS[200];
  int newc, newindexc;
  long int numdescendants = 0;
  if (g <= maxg) {
    if (g) {
      if (distinguishededges) {
        if ((optioninfinitechains &&
             belongstoinfinitechain(G, c, N[1], indexc)) ||
            (optionmed && ismed(G, S, c, N[1])) ||
            (optionpattern && admits(N, c, indexc, pattern, patternlength))) {
          if (g > ming) {
            if (blackandwhite)
              fprintf(fout, " \\edge [black,thick]; ");
            else
              fprintf(fout, " \\edge [red]; ");
          }
        } else {
          if (trimnondistinguishededges)
            return numdescendants;
          fprintf(fout, " \\edge [gray!50]; ");
        }
      }
    }

    fprintf(fout, "[.");
    drawnode(N, G, S, c, N[1], g, fout);
    if (g == maxg)
      numdescendants++;
    else {
      if (g == 0) {
        newc = 2;
        newindexc = 1;
        newN[0] = 0;
        newN[1] = 2;
        nongapstoG(newN, newc, newG);
        GtoS(newG, newc, newS);
        numdescendants += descendants(newN, newG, newS, newc, newindexc, g + 1,
                                      ming, maxg, m_set, fout);
      } else {
        for (s = 0; s < N[1]; s++) {
          if (!m_set || s || c != N[1]) {
            if (S[s]) {
              newc = c + s + 1;
              newindexc = indexc + s;
              for (i = 0; i <= indexc; i++)
                newN[i] = N[i];
              for (i = indexc + 1; i < newindexc; i++)
                newN[i] = newN[i - 1] + 1;
              newN[newindexc] = newc;
              nongapstoG(newN, newc, newG);
              GtoS(newG, newc, newS);
              numdescendants += descendants(newN, newG, newS, newc, newindexc,
                                            g + 1, ming, maxg, m_set, fout);
            }
          }
        }
      }
    }
    fprintf(fout, "]");
  }
  return numdescendants;
}

long int ord_descendants(int N[], int G[], int M[], int F[], int c, int g,
                         int m, FILE *fout) {
  int i, j, k, check;
  long int numdescendants = 0;
  int newN[MAX], newM[MAX], newF[MAX], auxF[MAX], S[MAX];

  if (distinguishededges) {
    if ((optioninfinitechains && belongstoinfinitechain(G, c, N[1], c - g)) ||
        (optionpattern && admits(N, c, c - g, pattern, patternlength))) {
      if (blackandwhite)
        fprintf(fout, " \\edge [black,thick]; ");
      else
        fprintf(fout, " \\edge [red]; ");
    } else {
      if (trimnondistinguishededges)
        return numdescendants;
      fprintf(fout, " \\edge [gray!50]; ");
    }
  }

  fprintf(fout, "[.");

  GtoS(G, c, S);
  drawnode(N, G, S, c, m, g, fout);
  numdescendants = 1;

  for (i = c; i < c + m; i++) {
    if (M[i]) {
      G[i - 1] = 1;
      for (k = 1; k <= i - c; k++)
        auxF[k] = 0;
      for (k = i - c + 1; k < m; k++)
        auxF[k] = F[k];
      auxF[i - m] = 0;
      if (i % 2 == 0)
        auxF[i / 2] = 0;
      if (i % 3 == 0)
        auxF[i / 3] = 0;
      for (k = 1; k < m; k++)
        if (!G[i - k - 1])
          auxF[k] = 0;
      for (j = 1; j < m; j++) {
        if (auxF[j]) {
          G[j - 1] = 0;
          for (k = 0; k < j; k++) {
            if (G[j + k - 1] == 1)
              newF[k] = 0;
            else
              newF[k] = auxF[k];
          }
          newF[i - j] = 0;
          if (j % 2 == 0 && (3 * j / 2 >= (i + 1) || !G[3 * j / 2 - 1]) &&
              G[(i + 1) - 1 - j / 2 - 1] && G[i - j / 2 - 1]) {
            check = 1;
            for (k = j + 1; check && k < i - j / 2; k++)
              if (!G[k - 1] && G[j / 2 + k - 1])
                check = 0;
            if (check)
              newF[j / 2] = 1;
          }
          for (k = 0; k < i + j; k++)
            newM[k] = M[k];
          for (k = i + j; k < MAX; k++)
            newM[k] = 0;
          newM[2 * j] = 0;
          for (k = i + 1; k < i + j; k++) {
            if (!G[k - j - 1])
              newM[k] = 0;
          }
          newM[i + j] = 1;
          for (k = j; k < i; k++)
            if (!G[k - 1] && !G[i + j - k - 1])
              newM[i + j] = 0;
          newN[0] = 0;
          newN[1] = j;
          for (k = 1; k < c - g; k++)
            newN[k + 1] = N[k];
          while (newN[k] < i) {
            newN[k + 1] = newN[k] + 1;
            k++;
          }
          newN[k] = i + 1;
          numdescendants +=
              ord_descendants(newN, G, newM, newF, i + 1, g, j, fout);
          G[j - 1] = 1;
        }
      }
      G[i - 1] = 0;
    }
  }

  fprintf(fout, "]");

  return numdescendants;
}

long int quasiord_descendants(int N[], int G[], int M[], int F[], int c, int sc,
                              int g, int m, FILE *fout) {
  int i, j, k, check, checkf;
  long int numdescendants = 0;
  int newN[MAX], newM[MAX], newF[MAX], auxF[MAX], S[MAX];

  if (distinguishededges) {
    if ((optioninfinitechains && belongstoinfinitechain(G, c, N[1], c - g)) ||
        (optionpattern && admits(N, c, c - g, pattern, patternlength))) {
      if (blackandwhite)
        fprintf(fout, " \\edge [black,thick]; ");
      else
        fprintf(fout, " \\edge [red]; ");
    } else {
      if (trimnondistinguishededges)
        return numdescendants;
      fprintf(fout, " \\edge [gray!50]; ");
    }
  }

  fprintf(fout, "[.");

  GtoS(G, c, S);
  drawnode(N, G, S, c, m, g, fout);
  numdescendants = 1;

  if (!G[c - 2 - 1]) {
    for (i = sc; i < c - 1; i++) {
      if (M[i]) {
        G[i - 1] = 1;
        for (k = 0; k < m; k++)
          auxF[k] = F[k];
        checkf = c - 1 - i;
        if (!G[2 * checkf - 1] && (3 * checkf >= c || !G[3 * checkf - 1]) &&
            (sc - checkf - 2 < 0 || G[sc - checkf - 2])) {
          check = 1;
          for (k = m; check && k < i + sc - c; k++)
            if (!G[k - 1] && G[checkf + k - 1])
              check = 0;
          if (check)
            auxF[checkf] = 1;
        }
        auxF[i - m] = 0;
        for (k = i - sc + 1; k < m; k++)
          if (!G[i - k - 1])
            auxF[k] = 0;
        if (i % 2 == 0)
          auxF[i / 2] = 0;
        if (i % 3 == 0)
          auxF[i / 3] = 0;
        for (j = 1; j < m; j++) {
          if (auxF[j]) {
            G[j - 1] = 0;
            for (k = 0; k < j; k++)
              newF[k] = auxF[k];
            newF[c - 1 - j] = 0;
            newF[i - j] = 0;
            for (k = 1; k < j && k < sc - j; k++)
              if (!G[j + k - 1] == 0)
                newF[k] = 0;
            if (j % 2 == 0 && (3 * j / 2 >= c || !G[3 * j / 2 - 1]) &&
                G[c - 1 - j / 2 - 1] && G[i - j / 2 - 1]) {
              check = 1;
              for (k = j + 1; check && k < i - j / 2; k++)
                if (!G[k - 1] && G[j / 2 + k - 1])
                  check = 0;
              if (check)
                newF[j / 2] = 1;
            }
            for (k = 0; k < c - 1; k++)
              newM[k] = M[k];
            newM[2 * j] = 0;
            for (k = i + 1; k < c - 1; k++)
              if (!G[k - j - 1])
                newM[k] = 0;
            newN[0] = 0;
            newN[1] = j;
            for (k = 1; k < i + 1 - g; k++)
              newN[k + 1] = N[k];
            for (k = i + 1 - g + 1; k <= c - g; k++)
              newN[k] = N[k];
            numdescendants +=
                quasiord_descendants(newN, G, newM, newF, c, i + 1, g, j, fout);
            G[j - 1] = 1;
          }
        }
        G[i - 1] = 0;
      }
    }
  }

  fprintf(fout, "]");

  return numdescendants;
}

void help() {
  std::cout
      << "./sgroup [options]      generate a latex file with the semigroup tree"
      << std::endl;
  std::cout << "  -h                    display this help" << std::endl;
  std::cout << "  -g <int>              [mandatory option] maximum genus"
            << std::endl;
  std::cout << "  -m <int>              multiplicity" << std::endl;
  std::cout << "  -n [option]           node representation" << std::endl;
  std::cout << "     -n list               list of semigroup elements"
            << std::endl;
  std::cout
      << "     -n minimalgenerators  representation by minimal generator set"
      << std::endl;
  std::cout << "     -n gapset             representation by gapsets"
            << std::endl;
  std::cout << "                               (S. Eliahou, J. Fromentin: "
               "Gapsets and numerical semigroups, Journal of Combinatorial "
               "Theory, Series A, 2020)"
            << std::endl;
  std::cout << "     -n gapseedbitstream   representation with the gap "
               "bitstream and the seed bitstream"
            << std::endl;
  std::cout << "                               (M. Bras-Amoros, J. "
               "Fernandez-Gonzalez: Computation of numerical semigroups by "
               "means of seeds, Math of Comput, 2018"
            << std::endl;
  std::cout << "                                M. Bras-Amoros: On the seeds "
               "and the great-grandchildren of a numerical semigroup, Math of "
               "Comput, Accepted, 2023)"
            << std::endl;
  std::cout << "     -n seedstable         representation by seeds tables"
            << std::endl;
  std::cout << "                               (M. Bras-Amoros, J. "
               "Fernandez-Gonzalez: Computation of numerical semigroups by "
               "means of seeds, Math of Comput, 2018"
            << std::endl;
  std::cout << "                                M. Bras-Amoros: On the seeds "
               "and the great-grandchildren of a numerical semigroup, Math of "
               "Comput, Accepted, 2023)"
            << std::endl;
  std::cout << "     -n dyckhook           representation by augmented Dyck "
               "paths and Hook lengths"
            << std::endl;
  std::cout << "                               (M. Bras-Amoros, A. de Mier: "
               "Representation of numerical semigroups by Dyck paths, "
               "Semigroup Forum, 2007)"
            << std::endl;
  std::cout
      << "                                H. Constantin, B. Houston-Edwards, "
         "N. Kaplan: Numerical sets, core partitions, and integer points in "
         "polytopes, Combinatorial and Additive Number Theory, 2017)"
      << std::endl;
  std::cout << "     -n aperykunzposet     representation by Apery sets, Kunz "
               "coordinates, and posets"
            << std::endl;
  std::cout
      << "                               (E. Kunz: Uber die Klassifikation "
         "numerischer Halbgruppen, Regensburger Mathematische Schriften, 1987"
      << std::endl;
  std::cout
      << "                                J.C. Rosales, P.A. Garcia-Sanchez, "
         "J.I. Garcia-Garcia, M.B. Branco: Systems of inequalities and "
         "numerical semigroups, J. Lond. Math. Soc., 2002"
      << std::endl;
  std::cout << "                                N. Kaplan, K. O'Neill: "
               "Numerical semigroups, polyhedra, and posets I: the group cone, "
               "Combinatorial Theory, 2021)"
            << std::endl;
  std::cout << "  -e [option]           edge distinction" << std::endl;
  std::cout << "     -e infinitechains     distinguish the infinite chains in "
               "the semigroup tree"
            << std::endl;
  std::cout
      << "                               (M. Bras-Amoros, S. Bulygin: Towards "
         "a better understanding of the semigroup tree, Semigroup Forum, 2009"
      << std::endl;
  std::cout
      << "                                M. Rosas-Ribeiro, M. Bras-Amoros: "
         "Infinite chains in the tree of numerical semigroups. Submitted, 2023)"
      << std::endl;
  std::cout
      << "     -e med                distinguish the chains of MED semigroups"
      << std::endl;
  std::cout
      << "                               (J.C. Rosales, P.A. Garcia-Sanchez, "
         "J.I. Garcia-Garcia, M.B. Branco: Numerical semigroups with maximal "
         "embedding dimension, Int. J. Commut. Rings, 2003)"
      << std::endl;
  std::cout << "     -e pattern <sign1>a1<sign2>a2..<signn>" << std::endl;
  std::cout
      << "                           distinguish the semigroups admitting the "
         "(strongly admissible) pattern <sign1>a1x1+<sign2>a2x2+...+<signn>anxn"
      << std::endl;
  std::cout
      << "                               (M. Bras-Amoros, P.A. Garcia-Sanchez: "
         "Patterns on numerical semigroups, Linear Algebra App. 2006)"
      << std::endl;
  std::cout << "  -etrim                discard the non-distinguished edges "
               "together with all its descendants"
            << std::endl;
  std::cout << "  -t [option]           alternative tree" << std::endl;
  std::cout << "     -t ordinarization" << std::endl;
  std::cout
      << "                               (M. Bras-Amoros: The ordinarization "
         "transform of a numerical semigroup and semigroups with a large "
         "number of intervals, J. of Pure and App. Algebra, 2012)"
      << std::endl;
  std::cout << "     -t quasiordinarization" << std::endl;
  std::cout << "                               (M. Bras-Amoros, H. "
               "Perez-Roses, J. M. Serradilla-Merinero: Quasi-ordinarization "
               "transform of a numerical semigroup, Symmetry, 2021)"
            << std::endl;
  std::cout << "  -incremental          incremental with genus" << std::endl;
  std::cout << "  -inputfile            input file (not compiling without a "
               "calling file)"
            << std::endl;
  std::cout << "  -vertical             vertical tree growing down"
            << std::endl;
  std::cout << "  -plain                plain representation of objects using "
               "less memory"
            << std::endl;
  std::cout << "  -blackandwhite        graph without colors" << std::endl;
  std::cout << "  -framednodes          frame each tree node" << std::endl;
  std::cout << "  -d <float>            enlarge distance between generations "
               "by the specified factor"
            << std::endl;
  std::cout << "  -s <float>            enlarge distance between siblings by "
               "the specified factor"
            << std::endl;
  std::cout << "  -rotated              rotated 90 degrees" << std::endl;
  std::cout << "  -o <filename>         output file name" << std::endl;
  std::cout << "  0 N[1] N[2] ... N[k]  root at the semigroup "
               "{0,N[1],N[2],N[k],N[k]+1,N[k]+2,...}"
            << std::endl;
  std::cout << "\nexamples:  ./drawsgtree -g5 -n list" << std::endl;
  std::cout << "           ./drawsgtree -g7 -n list -incremental" << std::endl;
  std::cout << "           ./drawsgtree -g7 -n list 0 5 8 -s .37 -d 1.2"
            << std::endl;
  std::cout << "           ./drawsgtree -g4 -n minimalgenerators -vertical"
            << std::endl;
  std::cout << "           ./drawsgtree -g5 -n gapset -vertical" << std::endl;
  std::cout << "           ./drawsgtree -g7 -n gapseedbitstream -n list -plain"
            << std::endl;
  std::cout << "           ./drawsgtree -g25 -n seedstable -vertical 0 8 16 18 "
               "19 24 26 27 30"
            << std::endl;
  std::cout << "           ./drawsgtree -g10 -n aperykunzposet 0 6 7 9"
            << std::endl;
  std::cout << "           ./drawsgtree -g8 -m4 -n dyckhook" << std::endl;
  std::cout << "           ./drawsgtree -g10 -e infinitechains" << std::endl;
  std::cout << "           ./drawsgtree -g10 -e infinitechains -d 3."
            << std::endl;
  std::cout << "           ./drawsgtree -g42 -m6 -e infinitechains -etrim -d .2"
            << std::endl;
  std::cout << "           ./drawsgtree -g6 -e med -n minimalgenerators"
            << std::endl;
  std::cout << "           ./drawsgtree -g5 -e pattern 1+1-1 -n "
               "minimalgenerators -e trim -vertical "
            << std::endl;
  std::cout << "           ./drawsgtree -g10 -m4 -e pattern 1+1+1-1 -n "
               "minimalgenerators -d 2.3 -s 4."
            << std::endl;
  std::cout
      << "           ./drawsgtree -m3 -g8 -n list -n gapset -n "
         "minimalgenerators -n gapseedbitstream -n aperykunzposet -framednodes"
      << std::endl;
  std::cout << "           ./drawsgtree -g15 0 7 9 11 14 16 18 20 21 22 23 25 "
               "27 -n aperykunzposet"
            << std::endl;
  std::cout << "           ./drawsgtree -g33 0 12 19 24 28 31 34 36 38 40 42 "
               "43 45 -n dyckhook"
            << std::endl;
  std::cout << "           ./drawsgtree -g7 -t ordinarization -n list"
            << std::endl;
  std::cout << "           ./drawsgtree -g7 -t quasiordinarization -n list"
            << std::endl;
}

void opt_g_missing() { std::cerr << "option -g is mandatory" << std::endl; }

int main(int argc, char *argv[]) {
  int g, ming = 0, maxg, m, c, indexc = 0, j, initialj;
  int N[50], G[50], S[50], M[50], F[50];
  long int count[50];
  float fac, facopt = 1., facsib = 1., scale = 1.;
  char filename[400] = "", filenameinput[400] = "", patstring[300] = "",
       sgstring[300] = "-root", straux[400];
  //  char filename[400] = "", filenameaux[400] = "", filenameinput[400] = "",
  //  patstring[300] = "", sgstring[300]="-",straux[400];
  FILE *fout;
  time_t seconds, secondsafter;
  bool g_set = false;
  bool m_set = false;

  while ((j = getopt(argc, argv, ":hg:m:i:v:p:d:s:f:b:r:n:e:x:o:t:")) != -1) {
    switch (j) {
    case 'h':
      help();
      return 0;
    case 'g':
      maxg = atoi(optarg);
      if (maxg < 0) {
        std::cerr << "Option -g must be followed by an integer in {0,1,...}"
                  << std::endl;
        return 1;
      }
      g_set = true;
      break;
    case 'm':
      m = atoi(optarg);
      if (m < 1) {
        std::cerr << "Option -m must be followed by an integer in {1,2,...}"
                  << std::endl;
        return 1;
      }
      m_set = true;
      break;
    case 'i':
      if (strcmp(optarg, "ncremental") == 0)
        incremental = true;
      else {
        if (strcmp(optarg, "nputfile") == 0)
          standalone = false;
        else {
          std::cerr << "Unrecognized option -i" << (char)optopt << optarg
                    << std::endl;
          return 1;
        }
      }
      break;
    case 'v':
      if (strcmp(optarg, "ertical") == 0)
        vertical = true;
      else {
        std::cerr << "Unrecognized option -v" << (char)optopt << optarg
                  << std::endl;
        return 1;
      }
      break;
    case 'p':
      if (strcmp(optarg, "lain") == 0)
        plain = true;
      else {
        std::cerr << "Unrecognized option -p" << (char)optopt << optarg
                  << std::endl;
        return 1;
      }
      break;

    case 'd':
      facopt = atof(optarg);
      break;
    case 's':
      facsib = atof(optarg);
      break;
    case 'x':
      scaled = true;
      scale = atof(optarg);
      break;
    case 'f':
      if (strcmp(optarg, "ramednodes") == 0)
        framednodes = true;
      else {
        std::cerr << "Unrecognized option -f" << (char)optopt << optarg
                  << std::endl;
        return 1;
      }
      break;
    case 'b':
      if (strcmp(optarg, "lackandwhite") == 0)
        blackandwhite = true;
      else {
        std::cerr << "Unrecognized option -b" << (char)optopt << optarg
                  << std::endl;
        return 1;
      }
      break;
    case 'r':
      if (strcmp(optarg, "otated") == 0)
        rotated = true;
      else {
        std::cerr << "Unrecognized option -r" << (char)optopt << optarg
                  << std::endl;
        return 1;
      }
      break;
    case 'o':
      defaultfilename = false;
      strcpy(filenameinput, optarg);
      break;
    case 'n':
      if (strcmp(optarg, "list") == 0) {
        optionemptynodes = false;
        optionlist = true;
        break;
      }
      if (strcmp(optarg, "minimalgenerators") == 0) {
        optionemptynodes = false;
        optiongenerators = true;
        break;
      }
      if (strcmp(optarg, "gapset") == 0) {
        optionemptynodes = false;
        optiongapset = true;
        break;
      }
      if (strcmp(optarg, "seedstable") == 0) {
        optionemptynodes = false;
        optionseedstable = true;
        break;
      }
      if (strcmp(optarg, "gapseedbitstream") == 0) {
        optionemptynodes = false;
        optiongapseedbitstream = true;
        break;
      }
      if (strcmp(optarg, "dyckhook") == 0) {
        optionemptynodes = false;
        optiondyckhook = true;
        break;
      }
      if (strcmp(optarg, "aperykunzposet") == 0) {
        optionemptynodes = false;
        optionaperykunzposet = true;
        break;
      }
      std::cerr << "Unrecognized option -n" << optarg << std::endl;
      return 1;
      break;
    case 'e':
      if (strcmp(optarg, "infinitechains") == 0) {
        if (distinguishededges && !optioninfinitechains) {
          std::cerr << "Can not combine different edge distinctions "
                    << (char)optopt << std::endl;
          return 1;
        }
        if (quasiordinarizationforest) {
          std::cerr << "Can not combine infinite chains edge distinction with "
                       "the quasiordinarization forest "
                    << (char)optopt << std::endl;
          return 1;
        }
        distinguishededges = true;
        optioninfinitechains = true;
        break;
      }
      if (strcmp(optarg, "med") == 0) {
        if (distinguishededges && !optionmed) {
          std::cerr << "Can not combine different edge distinctions "
                    << (char)optopt << std::endl;
          return 1;
        }
        if (ordinarizationtree) {
          std::cerr << "Can not combine med edge distinction with the "
                       "ordinarization tree "
                    << (char)optopt << std::endl;
          return 1;
        }
        if (quasiordinarizationforest) {
          std::cerr << "Can not combine med edge distinction with the "
                       "quasiordinarization forest "
                    << (char)optopt << std::endl;
          return 1;
        }
        distinguishededges = true;
        optionmed = true;
        break;
      }
      if (strcmp(optarg, "pattern") == 0) {
        if (distinguishededges && !optionpattern) {
          std::cerr << "Can not combine different edge distinctions "
                    << (char)optopt << std::endl;
          return 1;
        }
        if (quasiordinarizationforest) {
          std::cerr << "Can not combine pattern edge distinction with the "
                       "quasiordinarization forest "
                    << (char)optopt << std::endl;
          return 1;
        }
        distinguishededges = true;
        optionpattern = true;
        optionemptynodes = false;
        optionpsystemgenerators = true;
        break;
      }
      if (strcmp(optarg, "trim") == 0) {
        trimnondistinguishededges = true;
        break;
      }
      std::cerr << "Unrecognized option -e" << optarg << std::endl;
      return 1;
      break;
    case 't':
      if (strcmp(optarg, "ordinarization") == 0 &&
          quasiordinarizationforest == false) {
        if (optionmed) {
          std::cerr << "Can not combine med edge distinction with the "
                       "ordinarization tree "
                    << (char)optopt << std::endl;
          return 1;
        }
        ordinarizationtree = true;
      } else {
        if (strcmp(optarg, "quasiordinarization") == 0 &&
            ordinarizationtree == false) {
          if (optionmed) {
            std::cerr << "Can not combine med edge distinction with the "
                         "quasiordinarization forest "
                      << (char)optopt << std::endl;
            return 1;
          }
          if (optioninfinitechains) {
            std::cerr << "Can not combine infinite chains edge distinction "
                         "with the quasiordinarization forest "
                      << (char)optopt << std::endl;
            return 1;
          }
          if (optioninfinitechains) {
            std::cerr << "Can not combine pattern edge distinction with the "
                         "quasiordinarization forest "
                      << (char)optopt << std::endl;
            return 1;
          }
          quasiordinarizationforest = true;
        } else {
          std::cerr << "Unrecognized option -t " << (char)optopt << optarg
                    << std::endl;
          return 1;
        }
      }
      break;
    case ':':
      std::cerr << "option -" << (char)optopt << " requires an operand"
                << std::endl;
      return 1;
      break;
    case '?':
      if ((char)optopt < 49 || (char)optopt >= 58) {
        std::cerr << "Unrecognized option -" << (char)optopt << std::endl;
        return 1;
      }
      break;
    }
  }
  if (!g_set) {
    opt_g_missing();
    help();
    return 1;
  }
  if (incremental && !standalone) {
    std::cerr << "incompatible options -incremental and -inputfile"
              << std::endl;
    return 1;
  }

  if (incremental) {
    sprintf(filename, "incremental");
    standalone = 1;
  } else {
    if (standalone) {
      sprintf(filename, "standalone");
    } else {
      sprintf(filename, "inputfile");
    }
  }

  if (plain) {
    strcat(filename, "-plain");
  }

  if (distinguishededges) {
    if (optioninfinitechains)
      strcat(filename, "-infinitechains");
    if (optionmed)
      strcat(filename, "-med");
    if (optionpattern) {
      strcat(filename, "-pattern");
      strcat(filename, patstring);
    }
    if (trimnondistinguishededges)
      strcat(filename, "-trim");
  }

  if (optionaperykunzposet) {
    strcat(filename, "-aperykunzposet");
  }
  if (optiondyckhook) {
    strcat(filename, "-dyckhook");
  }
  if (optiongapseedbitstream) {
    strcat(filename, "-gapseedbitstream");
  }
  if (optionseedstable) {
    strcat(filename, "-seedstable");
  }
  if (optiongapset) {
    strcat(filename, "-gapset");
  }
  if (optiongenerators) {
    strcat(filename, "-minimalgenerators");
  }
  if (optionlist) {
    strcat(filename, "-list");
  }

  if (argc > optind) {
    if (optionpattern && atoi(argv[optind])) {
      char termstring[100] = "";
      int sign = 1;
      patternlength = 0;
      strcpy(patstring, argv[optind]);
      if (patstring[0] == '-') {
        std::cerr << "Non admissible pattern" << std::endl;
        return 1;
      } else {
        if (patstring[0] != '+')
          sprintf(termstring, "%c", patstring[0]);
      }
      for (int i = 1; i < (int)strlen(patstring); i++) {
        if (patstring[i] == '+' || patstring[i] == '-') {
          pattern[patternlength] = sign * atoi(termstring);
          patternlength++;
          strcpy(termstring, "");
          if (patstring[i] == '-')
            sign = -1;
          else
            sign = 1;
        } else {
          sprintf(straux, "%d", patstring[i]);
          strcat(termstring, straux);
        }
      }
      pattern[patternlength] = sign * atoi(termstring);
      patternlength++;
      if (!isstronglyadmissible(pattern, patternlength)) {
        std::cerr << "Non strongly admissible pattern" << std::endl;
        return 1;
      }
      strcpy(patpolynomial, "");
      if (pattern[0] > 1) {
        sprintf(straux, "%d", pattern[0]);
        strcat(patpolynomial, straux);
      }
      strcat(patpolynomial, "x_{1}");
      for (j = 1; j < patternlength; j++) {
        if (pattern[j]) {
          if (pattern[j] > 0) {
            strcat(patpolynomial, "+");
          }
          if (pattern[j] == -1) {
            strcat(patpolynomial, "-");
          } else {
            if (pattern[j] != 1) {
              sprintf(straux, "%d", pattern[j]);
              strcat(patpolynomial, straux);
            }
          }
          sprintf(straux, "x_{%d}", j + 1);
          strcat(patpolynomial, straux);
        }
      }
      std::cout << "pattern: " << patpolynomial << std::endl;
      for (indexc = 0; indexc < argc - optind - 1; indexc++) {
        N[indexc] = atoi(argv[optind + 1 + indexc]);
      }
    } else {
      for (indexc = 0; indexc < argc - optind; indexc++) {
        N[indexc] = atoi(argv[optind + indexc]);
        if (indexc && N[indexc] <= N[indexc - 1]) {
          std::cerr << "the given root semigroup is incorrect" << std::endl;
          return 1;
        }
      }
    }
  }

  if (indexc) {
    indexc--;
    while (indexc > 0 && (N[indexc] == (N[indexc - 1] + 1)))
      indexc--;
    for (j = 0; j <= indexc; j++) {
      std::cout << "N[" << j << "]=" << N[j] << std::endl;
      sprintf(straux, "%d", N[j]);
      strcat(sgstring, straux);
    }
    if (m_set and m != N[1]) {
      std::cerr
          << "The given root semigroup does not have the specified multiplicity"
          << std::endl;
      return 1;
    } else {
      if (!issemigroup(N, indexc)) {
        std::cerr << "The given integers do not correspond to a semigroup"
                  << std::endl;
        return 1;
      } else {
        ming = N[indexc] - indexc;
        if (ming > maxg) {
          std::cerr << "The final genus must be larger than the genus of the "
                       "tree root"
                    << std::endl;
          return 1;
        } else {
          if (ordinarizationtree) {
            if (ming != maxg) {
              std::cerr << "The genus of the tree root must equal the genus of "
                           "the tree"
                        << std::endl;
              return 1;
            }
          } else {
            if (quasiordinarizationforest) {
              if (ming != maxg) {
                std::cerr << "The genus of the root semigroup must equal the "
                             "genus of the forest"
                          << std::endl;
                return 1;
              }
            }
          }
        }
      }
    }
  } else {
    if (m_set) {
      if (maxg < m - 1) {
        std::cerr
            << "The final genus must be at least the multiplicity minus one"
            << std::endl;
        return 1;
      }
      if (ordinarizationtree) {
        std::cerr
            << "The multiplicity can not be fixed in the ordinarization tree"
            << std::endl;
        return 1;
      }
      if (quasiordinarizationforest) {
        std::cerr << "The multiplicity can not be fixed in the "
                     "quasiordinarization forest"
                  << std::endl;
        return 1;
      }
      indexc = 1;
      N[0] = 0;
      N[1] = m;
      sprintf(straux, "0%d", m);
      strcat(sgstring, straux);
      ming = m - 1;
    } else {
      N[0] = 0;
      if (ordinarizationtree) {
        indexc = 1;
        N[1] = maxg + 1;
      } else {
        indexc = 0;
        N[1] = 1;
      }
    }
  }

  if (ordinarizationtree)
    strcat(filename, "-ordinarizationtree-");
  else {
    if (quasiordinarizationforest)
      strcat(filename, "-quasiordinarizationforest-");
    else
      strcat(filename, "-semigrouptree-");
  }
  sprintf(straux, "g%d", maxg);
  strcat(filename, straux);
  if (m_set) {
    sprintf(straux, "-m%d", m);
    strcat(filename, straux);
  }
  if (!quasiordinarizationforest &&
      (((!ordinarizationtree) && N[1] > 1) ||
       (ordinarizationtree && (N[1] != maxg + 1))))
    strcat(filename, sgstring);
  strcat(filename, ".tex");

  c = N[indexc];

  if (!defaultfilename)
    strcpy(filename, filenameinput);

  fout = fopen(filename, "w");
  fprintf(fout, "%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%"
                "%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%"
                "%%%%%%%%%%%%%%%%%%%%%%%%%%\n%%\n%%\n");
  fprintf(fout, "%%     Copyright (c) 2022, 2023, 2024 Maria Bras-Amoros\n");
  fprintf(
      fout,
      "%%     File generated with https://github.com/mbrasamoros/drawsgtree");
  fprintf(fout, "\n%%     ");
  for (j = 0; j < argc; j++)
    fprintf(fout, "%s ", argv[j]);
  fprintf(fout, "\n%%\n%%\n%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%"
                "%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%"
                "%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%\n\n");
  fac = facopt * 1.75;
  if (ordinarizationtree || quasiordinarizationforest)
    facsib *= .1;

  if (standalone) {
    if (optionseedstable || optiondyckhook) {
      if (incremental)
        fprintf(fout, "\\documentclass[table]{article}\n\\usepackage{tikz,tikz-"
                      "qtree,tikz-qtree-compat,fullpage,adjustbox,xcolor,array,"
                      "hhline}\n\\pagestyle{empty}\n");
      else
        fprintf(fout, "\\documentclass[table]{standalone}\n\\usepackage{tikz,"
                      "tikz-qtree,tikz-qtree-compat,fullpage,adjustbox,xcolor,"
                      "array,hhline}\n\\pagestyle{empty}\n");
    } else {
      if (incremental)
        fprintf(fout,
                "\\documentclass{article}\n\\usepackage{tikz,tikz-qtree,tikz-"
                "qtree-compat,fullpage,adjustbox}\n\\pagestyle{empty}\n");
      else
        fprintf(fout,
                "\\documentclass{standalone}\n\\usepackage{tikz,tikz-qtree,"
                "tikz-qtree-compat,fullpage,adjustbox}\n\\pagestyle{empty}\n");
    }
    if (!plain)
      fprintf(fout, "\\usepackage{pst-plot}\n\\usepackage{etoolbox}\n");
    fprintf(fout, "\\usetikzlibrary{positioning}\n");
  }
  if (optionseedstable || optiondyckhook)
    fprintf(fout,
            "\\newcolumntype{M}{>{\\centering\\arraybackslash}m{.5cm}}"
            "\\setlength\\tabcolsep{0pt}\\setlength\\arrayrulewidth{1pt}");
  if (plain) {
    if (blackandwhite) {
      fprintf(fout, "\\providecommand\\nongap{}\\renewcommand\\nongap[1]{"
                    "\\scalebox{2.3}{{\\bf#1\\ }}}\n");
      fprintf(fout, "\\providecommand\\gap{}\\renewcommand\\gap[1]{\\scalebox{"
                    "2.3}{{\\color{gray!70}#1\\ }}}\n");
      fprintf(fout, "\\providecommand\\generator{}\\renewcommand\\generator[1]{"
                    "\\scalebox{2.3}{{\\bf\\underline{#1}\\ }}}\n");
      fprintf(fout, "\\providecommand\\dotscircles{}"
                    "\\renewcommand\\dotscircles{\\scalebox{2.3}{\\dots}}\n");
      if (optiongapseedbitstream) {
        fprintf(fout, "\\providecommand\\seed{}\\renewcommand\\seed[1]{"
                      "\\scalebox{2.3}{{\\bf #1\\ }}}\n");
        fprintf(fout, "\\providecommand\\nonseed{}\\renewcommand\\nonseed[1]{"
                      "\\scalebox{2.3}{{\\color{gray!70}#1\\ }}}\n");
      }

    } else {
      fprintf(fout, "\\providecommand\\nongap{}\\renewcommand\\nongap[1]{"
                    "\\scalebox{2.7}{{\\color{blue}#1\\ }}}\n");
      fprintf(fout, "\\providecommand\\gap{}\\renewcommand\\gap[1]{\\scalebox{"
                    "2.7}{{\\color{gray!50}#1\\ }}}\n");
      fprintf(fout, "\\providecommand\\generator{}\\renewcommand\\generator[1]{"
                    "\\scalebox{2.7}{{\\color{orange!80}#1\\ }}}\n");
      fprintf(fout,
              "\\providecommand\\dotscircles{}\\renewcommand\\dotscircles{"
              "\\scalebox{2.7}{{\\color{blue}\\dots}}}\n");
      if (optiongapseedbitstream) {
        fprintf(fout, "\\providecommand\\seed{}\\renewcommand\\seed[1]{"
                      "\\scalebox{2.7}{{\\color{red}#1\\ }}}\n");
        fprintf(fout, "\\providecommand\\nonseed{}\\renewcommand\\nonseed[1]{"
                      "\\scalebox{2.7}{{\\color{red!20}#1\\ }}}\n");
      }
    }
  } else {
    if (ordinarizationtree || quasiordinarizationforest) {
      fprintf(fout,
              "\\providecommand\\circledcolorednumb{}"
              "\\renewcommand\\circledcolorednumb[2]{\\tikz[baseline=(char."
              "center)]{\\node[shape = circle,draw, inner sep = "
              "2pt,fill=#1](char)    {\\phantom{00}};\\node[anchor=center] at "
              "(char.center) {\\makebox(0,0){\\large{{\\sf #2}}}};}}\n");
      fprintf(fout, "\\providecommand\\dotscircles{}"
                    "\\renewcommand\\dotscircles{{\\bf \\dots}}\n");
    } else {
      fprintf(
          fout,
          "\\providecommand\\circledcolorednumb{}"
          "\\renewcommand\\circledcolorednumb[2]{\\resizebox{%f\\textwidth}{!}{"
          "\\tikz[baseline=(char.center)]{\\node[shape = circle,draw, inner "
          "sep = 2pt,fill=#1](char)    {\\phantom{00}};\\node[anchor=center] "
          "at (char.center) {\\makebox(0,0){\\large{{\\sf #2}}}};}}}\n",
          fac / facsib * (0.1 + maxg - c + indexc) / (27. * facopt * maxg));
      fprintf(fout,
              "\\providecommand\\dotscircles{}\\renewcommand\\dotscircles{"
              "\\resizebox{%f\\textwidth}{!}{\\dots}}\n",
              fac / facsib * (0.1 + maxg - c + indexc) / (27. * facopt * maxg));
    }
    fprintf(fout, "\\robustify{\\circledcolorednumb}\n");
    if (blackandwhite) {
      fprintf(fout, "\\providecommand\\nongap{}\\renewcommand\\nongap[1]{"
                    "\\circledcolorednumb{gray!40}{#1}}\n");
      fprintf(fout, "\\providecommand\\gap{}\\renewcommand\\gap[1]{"
                    "\\circledcolorednumb{black!05}{\\phantom{#1}}}\n");
      fprintf(fout, "\\providecommand\\generator{}\\renewcommand\\generator[1]{"
                    "\\circledcolorednumb{gray}{#1}}\n");
      if (optiongapseedbitstream) {
        fprintf(fout, "\\providecommand\\seed{}\\renewcommand\\seed[1]{"
                      "\\circledcolorednumb{black!30}{#1}}\n");
        fprintf(fout, "\\providecommand\\nonseed{}\\renewcommand\\nonseed[1]{"
                      "\\circledcolorednumb{black!05}{#1}}\n");
      }
      if (optiongapset) {
        fprintf(fout,
                "\\providecommand\\gapingapset{}\\renewcommand\\gapingapset[1]{"
                "\\circledcolorednumb{gray!50}{#1}}\n");
        fprintf(
            fout,
            "\\providecommand\\nongapingapset{}\\renewcommand\\nongapingapset["
            "1]{\\phantom{\\gapingapset{#1}}}\n");
      }
    } else {
      fprintf(fout, "\\providecommand\\nongap{}\\renewcommand\\nongap[1]{"
                    "\\circledcolorednumb{yellow}{#1}}\n");
      fprintf(fout, "\\providecommand\\gap{}\\renewcommand\\gap[1]{"
                    "\\circledcolorednumb{black!20}{\\phantom{#1}}}\n");
      fprintf(fout, "\\providecommand\\generator{}\\renewcommand\\generator[1]{"
                    "\\circledcolorednumb{orange!80}{#1}}\n");
      if (optiongapseedbitstream) {
        fprintf(fout, "\\providecommand\\seed{}\\renewcommand\\seed[1]{"
                      "\\circledcolorednumb{blue!30}{#1}}\n");
        fprintf(fout, "\\providecommand\\nonseed{}\\renewcommand\\nonseed[1]{"
                      "\\circledcolorednumb{white}{#1}}\n");
      }
      if (optiongapset) {
        fprintf(fout,
                "\\providecommand\\gapingapset{}\\renewcommand\\gapingapset[1]{"
                "\\circledcolorednumb{green!30}{#1}}\n");
        fprintf(
            fout,
            "\\providecommand\\nongapingapset{}\\renewcommand\\nongapingapset["
            "1]{\\phantom{\\gapingapset{#1}}}\n");
      }
    }
  }
  if (optionseedstable) {
    if (blackandwhite)
      fprintf(fout, "\\providecommand\\coloredseed{}"
                    "\\renewcommand\\coloredseed{\\cellcolor{gray!70}}\n");
    else
      fprintf(fout, "\\providecommand\\coloredseed{}"
                    "\\renewcommand\\coloredseed{\\cellcolor{blue!30}}\n");
  }
  if (standalone)
    fprintf(fout, "\\begin{document}\n");
  seconds = time(NULL);

  if (incremental)
    initialj = ming;
  else
    initialj = maxg;

  for (j = initialj; j <= maxg; j++) {
    if (incremental) {
      fprintf(fout, "\\pagecolor{white}\n");
      if (j == 0)
        fprintf(fout, "\\mbox{}\\vfill\\resizebox{%f\\textwidth}{!}",
                .375 / maxg);
      else
        fprintf(fout, "\\mbox{}\\vfill\\resizebox{%f\\textwidth}{!}",
                1. * j / maxg);
    } else {
      if (scaled)
        fprintf(fout, "\\scalebox{%f}{", scale);
    }
    if (vertical)
      fprintf(fout, "{\\begin{tikzpicture}[grow=down,sibling distance=%fmm]",
              facsib * 10.);
    else
      fprintf(fout, "{\\begin{tikzpicture}[grow'=right, sibling distance=%fmm]",
              facsib * 6.);
    if (optiongapset)
      fprintf(fout, "\\tikzset{every tree node/.style={anchor=south}}");
    if (optionseedstable)
      fprintf(fout, "\\tikzset{every tree node/.style={anchor=north}}");
    if (optiondyckhook)
      fprintf(fout, "\\tikzset{every tree node/.style={anchor=west}}");
    if (optionaperykunzposet)
      fprintf(fout, "\\tikzset{level 1+/.style={level distance=%fcm}}",
              10. * fac);
    else {
      if (ordinarizationtree || quasiordinarizationforest) {
        fprintf(fout, "\\tikzset{level 1+/.style={level distance=12cm}}");
      } else
        fprintf(
            fout,
            "\\tikzset{level 1/.style={level distance=%fcm}}\\tikzset{level "
            "2/.style={level distance=%fcm}}\\tikzset{level 3/.style={level "
            "distance=%fcm}}\\tikzset{level 4/.style={level "
            "distance=%fcm}}\\tikzset{level 5/.style={level "
            "distance=%fcm}}\\tikzset{level 6/.style={level "
            "distance=%fcm}}\\tikzset{level 7+/.style={level distance=%fcm}}",
            4. * fac, 5. * fac, 6.5 * fac, 8. * fac, 10. * fac, 10.2 * fac,
            10.8 * fac);
    }
    fprintf(fout, "\\node (arbre) at (current page.north) {");
    if (rotated)
      fprintf(fout, "\\adjustbox{max width=.9\\textwidth,max "
                    "height=\\textheight,angle=90}");
    else
      fprintf(fout,
              "\\adjustbox{max width=\\textwidth,max height=.9\\textheight}");
    fprintf(fout, " { ");

    count[j] = 0;

    if (quasiordinarizationforest && !c) {
      fprintf(fout, "\\begin{tabular}{l}\n");
      N[0] = 0;
      N[1] = maxg + 1;
      for (int i = 1; i <= maxg; i++)
        G[i - 1] = 1;
      G[maxg + 1] = 0;

      fprintf(fout, "\n\n\\Tree");
      count[j] += quasiord_descendants(N, G, M, F, maxg + 1, c - 2, maxg,
                                       maxg + 1, fout);
      fprintf(fout, "\\\\\\\\\\\\\n");

      for (c = maxg + 2; c <= 2 * maxg; c++) {
        N[0] = 0;
        for (int i = 1; i < maxg; i++) {
          G[i - 1] = 1;
        }
        for (int i = maxg; i < c - 1; i++) {
          N[i - maxg + 1] = i;
          G[i - 1] = 0;
          M[i] = 1;
        }
        G[c - 1 - 1] = 1;
        G[c - 1] = 0;
        N[c - maxg] = c;
        for (int i = 0; i < maxg - maxg / 2; i++)
          F[i] = 0;
        for (int i = maxg - maxg / 2; i < maxg; i++)
          F[i] = 1;
        for (int i = maxg - maxg / 2; i < c - maxg; i++)
          F[i] = 0;
        if ((c - 1) % 2 == 0)
          F[(c - 1) / 2] = 0;
        if ((c - 1) % 3 == 0)
          F[(c - 1) / 3] = 0;
        fprintf(fout, "\n\n\\Tree");
        count[j] += quasiord_descendants(N, G, M, F, c, maxg, maxg, maxg, fout);
        fprintf(fout, "\\\\\\\\\\\\\n");
      }
      fprintf(fout, "\\end{tabular}\n");

    } else {
      fprintf(fout, "\\Tree");
      nongapstoG(N, c, G);
      GtoS(G, c, S);
      if (ordinarizationtree || quasiordinarizationforest) {
        m = N[1];
        F[0] = 0;
        for (int i = 1; i < c; i++) {
          if (!G[i - 1] || (2 * i < c && G[2 * i - 1]) ||
              (3 * i < c && G[3 * i - 1]))
            F[i] = 0;
          else
            F[i] = 1;
          for (int k = 2; k < c - i && F[i]; k++) {
            if (!G[k - 1] && G[i + k - 1])
              F[i] = 0;
          }
        }
        if (ordinarizationtree) {
          for (int i = c; i < c + m; i++) {
            if (S[i - c])
              M[i] = 1;
            else
              M[i] = 0;
          }

          count[j] = ord_descendants(N, G, M, F, c, c - indexc, m, fout);
        } else {
          int sc = c - 2;
          if (!G[sc - 1]) {
            while (!G[sc - 2])
              sc--;
          }
          for (int i = sc; i < c - 1; i++) {
            if (!G[i - 1]) {
              M[i] = 1;
              for (int j = m; j <= i - m && M[i]; j++) {
                if (!G[j - 1] && !G[i - j - 1])
                  M[i] = 0;
              }
            }
          }
          count[j] =
              quasiord_descendants(N, G, M, F, c, sc, c - indexc, m, fout);
        }
      } else
        count[j] =
            descendants(N, G, S, c, indexc, c - indexc, ming, j, m_set, fout);
    }
    fprintf(fout, " } ");
    if (rotated)
      fprintf(fout,
              " }; \\node[align = center, right =.001\\textwidth of arbre, "
              "rotate=90]{\\resizebox{.2\\textwidth}{!}{{\\textcopyright\\, "
              "2022, 2023, 2024 Maria Bras-Amor\\'os}}};\\end{tikzpicture}}");
    else
      fprintf(fout,
              " }; \\node[align = center, below =.001\\textwidth of "
              "arbre]{\\resizebox{.2\\textwidth}{!}{{\\textcopyright\\, 2022, "
              "2023, 2024 Maria Bras-Amor\\'os}}};\\end{tikzpicture}}");
    if (!incremental && scaled)
      fprintf(fout, "}");
    fprintf(fout, "\n\n");
    if (incremental)
      fprintf(fout, "\\newpage");
  }

  if (standalone)
    fprintf(fout, "\\end{document}\n");
  fclose(fout);

  secondsafter = time(NULL);
  for (g = initialj; g <= maxg; g++) {
    if (g < MAX)
      std::cout << "[g=" << g << "] count=" << count[g] << " ng=" << ng[g]
                << " [" << (int)(secondsafter - seconds) << " seconds]"
                << std::endl;
    else
      std::cout << "[g=" << g << "] count=" << count[g] << " ["
                << (int)(secondsafter - seconds) << " seconds]" << std::endl;
  }
  std::cout << "GENERATED FILE: " << filename << std::endl;
  return 0;
}
