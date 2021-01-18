#include <stdio.h>

/*@
  requires n >= 0;
  requires \valid(a+(0..(n-1)));

  assigns \nothing;

  behavior v_absent:
  assumes \forall integer k; 0 <= k < n ==> a[k] != v;
  ensures \result == n;

  behavior v_present:
  assumes \exists integer k; 0 <= k < n && a[k] == v;
  ensures 0 <= \result < n;
  ensures a[\result] == v;
  ensures \forall integer j; 0 <= j < \result ==> a[j] != v;

  complete behaviors v_absent, v_present;
  disjoint behaviors v_absent, v_present;
 */


int find(int *a, int n, int v){

  int i;
  
  /*@
    loop invariant 0 <= i <= n;
    loop invariant \forall integer j; 0 <= j < i ==> a[j] != v;

    loop assigns i;

    loop variant n-i;
   */
  for(i=0;i<n;i++){
    if (a[i]==v) {
      return i;
    }
  }
  
  // printf("Hello, Jiahao ! i is equal to : %d\n", i);
  // beware ! i is equal to n here !

  return i;
}


int main(char *args[]) {
  int t[] = {1,2,3,4,5};
  find(t,5,0);
}
