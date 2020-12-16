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
//requires \valid_range(t, 0, l-1);

ensures sorted{Here}(t, l);
*/
void sort(int *t, int l) {
  int i;
  int j;
  
  /*@
  //slide 64
  loop invariant l > 0;
  loop assigns i, l;
  
  loop invariant 0 <= i;
  loop invariant i < l;

  loop invariant sorted{Here}(t,i);
  loop variant l-i;
  */
  for (i=0; i<l; i++) {

	/*@
	loop assigns i, j;
	
	loop invariant 0 <= i <= j < l;
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
