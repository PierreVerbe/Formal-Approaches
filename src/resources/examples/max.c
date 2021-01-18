/*@
requires n >= 0;
requires \valid(t+(0..(n-1)));

assigns \nothing;

behavior empty:
assumes n == 0;
ensures \result == 0;

behavior notEmpty:
assumes n > 0;
ensures 0 <= \result < n;
ensures \forall integer k; 0 <= k < n ==>  t[k] <= t[\result];
ensures \forall integer k; 0 <= k < \result ==>  t[k] < t[\result];

complete behaviors empty, notEmpty;
disjoint behaviors empty, notEmpty;
 */

int max(int * t, int n) {
  if (n == 0) {
    return 0;
  } else {

    int maxInd = 0;
    int i =0;
    

    /*@
      loop assigns i, maxInd;

      loop invariant 0 <= i <= n;
      loop invariant 0 <= maxInd < n;
      loop invariant 0 <= maxInd <= i;

      loop invariant \forall integer k; 0 <= k < i ==>  t[k] <= t[maxInd];
      loop invariant \forall integer k; 0 <= k < maxInd ==>  t[k] < t[maxInd];

      loop variant n-i-1;
    */
   
    for (i=0;i<n;i++) {
      if (t[i] > t[maxInd]) {
	maxInd = i;
      }
    }

    
    return maxInd;
  }
}
