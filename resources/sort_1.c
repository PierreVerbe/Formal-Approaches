#include <stdio.h>


//vien du doc acsl.pdf
/*@ axiomatic Permut {
@ // permut{L1,L2}(t1,t2,n) is true whenever t1[0..n-1] in state L1
@ // is a permutation of t2[0..n-1] in state L2
@ predicate permut{L1,L2}(double *t1, double *t2, integer n);
@ axiom permut_refl{L}:
@ \forall double *t, integer n; permut{L,L}(t,t,n);
@ axiom permut_sym{L1,L2} :
@ \forall double *t1, *t2, integer n;
@ permut{L1,L2}(t1,t2,n) ==> permut{L2,L1}(t2,t1,n) ;
@ axiom permut_trans{L1,L2,L3} :
@ \forall double *t1, *t2, *t3, integer n;
@ permut{L1,L2}(t1,t2,n) && permut{L2,L3}(t2,t3,n)
@ ==> permut{L1,L3}(t1,t3,n) ;
@ axiom permut_exchange{L1,L2} :
@ \forall double *t1, *t2, integer i, j, n;
@ \at(t1[i],L1) == \at(t2[j],L2) &&
@ \at(t1[j],L1) == \at(t2[i],L2) &&
@ ( \forall integer k; 0 <= k < n && k != i && k != j ==>
@ \at(t1[k],L1) == \at(t2[k],L2))
@ ==> permut{L1,L2}(t1,t2,n);
@ }
@*/



/*@
	predicate sorted{L}(int* arr, integer length) =
	\forall integer i,j;
		0 <= i <= j < length ==> arr[i] <= arr[j];
*/


/*@
requires 0 < l;
requires \valid(t + (0 .. l - 1));
requires 0 <= i < l;
requires 0 <= j < l;
ensures \old(t[i]) == t[j] && \old(t[j]) == t[i];
*/
void swap(int *t, int l, int i,int j){
  int tmp;
  tmp = t[i];
  t[i] = t[j];
  t[j] = tmp;
  return;
}


/*@
requires l > 0;
requires \valid(t + (0 .. l - 1));

ensures sorted{Here}(t,l);
*/
void sort(int *t, int l) {
  int i;
  int j;
  
  /*@
  //loop invariant 0 <= i;
  //loop invariant i <= l;
  loop invariant 0 <= i <= l;
  
  loop invariant sorted{Here}(t,i-1);//vert-orange!!
  loop invariant sorted{Here}(t,i);//orange

  loop assigns i,j,*t;
  
  loop variant l-i;
  */
  for (i=0;i<l;i++) {
	/*@

	loop invariant 0 <= i < l;
	loop invariant 0 <= j <= l;
	loop invariant i <= j <= l;
		
	loop invariant sorted{Here}(t,i);
	

	loop invariant \forall integer k; (0 <= k < i) ==>  t[k] <= t[j];
	loop invariant \forall integer k; (0 <= k <= i) ==>  t[k] <= t[j];

	loop invariant t[i] <= t[j];

	loop invariant \forall integer k; (i <= k < j) ==>  t[i] <= t[k];//vert-orange!!
	loop invariant \forall integer k; (i <= k <= j) ==>  t[i] <= t[k];//orange

		
	//loop invariant \forall integer k; (i <= k < j) ==>  t[i] <= t[k];
	//loop invariant \forall integer k; (i <= k <= j) ==>  t[i] <= t[k];

	loop invariant t[j-1] < t[j];

	loop assigns j,*t;


	loop variant l-j;
	*/
    for (j=i; j<l; j++) {
		/*@ assert 0<=i<l;*/
		/*@ assert 0<=j<l;*/
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
