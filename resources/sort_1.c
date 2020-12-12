#include <stdio.h>

void swap(int *t, int l, int i,int j){
  int tmp;
  tmp = t[i];
  t[i] = t[j];
  t[j] = tmp;
  return;
}

void sort(int *t, int l) {
  int i;
  int j;
  for (i=0;i<l;i++) {
    for (j=i; j<l; j++) {
      if (t[i] > t[j]) swap(t, l, i, j);
    }
  }
}



void affiche(int *t, int l) {
  int i;
  printf("{ ");
  for(i=0;i<l-1;i++) {
    printf("%d, ",t[i]);
  }
  printf("%d}\n",t[i]);
}


/* tester les fonctions de tri    *
 * avant d'essayer de les prouver */
int main() {
  int t[10] = {4,3,8,8,1,0,7,2,9,1};
  affiche(t,10);
  sort(t,10);
  affiche(t,10);
  return 0;
}
