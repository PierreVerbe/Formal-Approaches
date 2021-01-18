/*@
r e q u i r e s \ v ali d(a+ (0..(n-1)));
r e q u i r e s n >= 0;
a s si g n s \nothing;
beha vio r empty:
assumes n==0;
ensu res \ r e s u l t==0;
beha vio r not_empty:
assumes n > 0;
ensu res 0 <= \ r e s u l t < n;
ensu res \ f o r a l l i n t e g e r k; (0 <= k < n) ==> (a[k] <= a[\ r e s u l t]);
ensu res \ f o r a l l i n t e g e r k; (0 <= k < \ r e s u l t) ==> (a[k] < a[\ r e s u l t]);
complete beh a vio r s empty, not_empty;
d i s j o i n t beh a vio r s empty, not_empty;
*/
i n t max(const i n t* a, i n t n) {
i f (n == 0) re t u r n 0;
i n t max = 0;
f o r (i n t i = 0; i < n; i ++){
i f (a[max] < a[i]) max = i;
}
re t u r n max;
}
