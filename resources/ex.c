// #include <stdio.h>
 
/*@ predicate Sorted{L}(int a[], integer l, integer h) =
  @   \forall integer i; l <= i < h ==> a[i] <= a[i+1];
  @
  @ predicate Swap{L1,L2}(int a[], integer i, integer j) =
  @      \at(a[i],L1) == \at(a[j],L2)
  @   && \at(a[j],L1) == \at(a[i],L2)
  @   && \forall integer k; k != i && k != j ==> \at(a[k],L1) == \at(a[k],L2);
  @*/
 
/*@ inductive Permut{L1,L2}(int a[], integer l, integer h) {
  @  case Permut_refl{L}:
  @   \forall int a[], integer l, h; Permut{L,L}(a, l, h) ;
  @  case Permut_sym{L1,L2}:
  @    \forall int a[], integer l, h;
  @      Permut{L1,L2}(a, l, h) ==> Permut{L2,L1}(a, l, h) ;
  @  case Permut_trans{L1,L2,L3}:
  @    \forall int a[], integer l, h;
  @      Permut{L1,L2}(a, l, h) && Permut{L2,L3}(a, l, h) ==>
  @        Permut{L1,L3}(a, l, h) ;
  @  case Permut_swap{L1,L2}:
  @    \forall int a[], integer l, h, i, j;
  @       l <= i <= h && l <= j <= h && Swap{L1,L2}(a, i, j) ==>
  @     Permut{L1,L2}(a, l, h) ;
  @ }
  @*/
 
/*@ requires \valid(i) && \valid(j);
  @ //assigns *i, *j; //BUG 0000080: Assertion failed in jc_interp_misc.ml
  @ ensures \at(*i,Old) == \at(*j,Here) && \at(*j,Old) == \at(*i,Here);
  @*/
void swap(int *i, int *j) {
    int tmp = *i;
    *i = *j;
    *j = tmp;
}
 
/*@ requires tam > 0;
  @ requires \valid_range(vector,0,tam-1);
  @ ensures Sorted{Here}(vector, 0, tam-1);
  @ ensures Permut{Old,Here}(vector,0,tam-1);
  @*/
void bubbleSort(int *vector, int tam) {
    int j, i;
    j = i = 0;
    //@ ghost int g_swap = 0;
 
  /*@ loop invariant 0 <= i < tam;
    @ loop invariant 0 <= g_swap <= 1;
    //last i+1 elements of sequence are sorted
    @ loop invariant Sorted{Here}(vector,tam-i-1,tam-1);
    //and are all greater or equal to the other elements of the sequence.
    @ loop invariant 0 < i < tam ==> \forall int a, b; 0 <= b <= tam-i-1 <= a < tam ==> vector[a] >= vector[b];
    @ loop invariant 0 < i < tam ==> Permut{Pre,Here}(vector,0,tam-1);
    @ loop variant tam-i;
    @*/
    for(i=0; i<tam; i++) {
      //@ ghost g_swap = 0;
      /*@ loop invariant 0 <= j < tam-i;
        @ loop invariant 0 <= g_swap <= 1;
        //The jth+1 element of sequence is greater or equal to the first j+1 elements of sequence.
        @ loop invariant 0 < j < tam-i ==> \forall int a; 0 <= a <= j ==> vector[a] <= vector[j+1];
        @ loop invariant 0 < j < tam-i ==> (g_swap == 1) ==> Permut{Pre,Here}(vector,0,tam-1);
        @ loop variant tam-i-j-1;
        @*/
        for(j=0; j<tam-i-1; j++) {
            g_swap = 0;
            if (vector[j] > vector[j+1]) {
                //@ ghost g_swap = 1;
                swap(&vector[j],&vector[j+1]);
            }
        }
    }
}
 
/*@ requires \true;
  @ ensures \result == 0;
  @*/
int main(int argc, char *argv[]) {
    int i;
    int v[9] = {8,5,2,6,9,3,0,4,1};
 
    bubbleSort(v,9);
 
//     for(i=0; i<9; i++)
//         printf("v[%d]=%d\n",i,v[i]);
 
    return 0;
}
