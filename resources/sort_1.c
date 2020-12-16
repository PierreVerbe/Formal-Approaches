#include <stdio.h>

/*@
  predicate sorted{L}(int* arr, integer length) =
  \forall integer i, j;
    0 <= i <= j < length ==> arr[i] <= arr[j];
*/

/*@
  requires 0 < l;
  requires \valid(t + (0 .. (l-1)));
  requires 0 <= i < l;
  requires 0 <= j < l;
  ensures \old(t[i]) == t[j] && \old(t[j]) == t[i];
*/
void swap(int *t, int l, int i, int j){
  int tmp;
  tmp = t[i];
  t[i] = t[j];
  t[j] = tmp;
  return;
}

/*@
  requires l > 0;
  requires \valid(t + (0 .. (l-1)));

  ensures sorted{Here}(t, l);
*/
void sort(int *t, int l) {
  int i;
  int j;
  
  /*@
    //slide 64
    loop assigns i, j, *t;

    loop invariant 0 <= i <= l;
    loop invariant 0 <= j <= l;
    loop invariant sorted{Here}(t, i);

    loop variant l-i;
  */
  for (i=0; i<l; i++) {

    /*@
      loop assigns i, j, *t;

      // loop assigns t[i], t[j];

      loop invariant 0 <= i <= l;
      loop invariant i <= j <= l;
      loop invariant sorted{Here}(t, i + 1);
      
      // loop invariant \forall integer i, j;
      //  0 <= i <= j < length ==> arr[i] <= arr[j];

      loop variant l-j;
    */
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
