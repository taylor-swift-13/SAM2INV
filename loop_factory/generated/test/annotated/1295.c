int main1(int h){
  int ls, k, f, j, kn, a7y, cu7;
  ls=h;
  k=0;
  f=1;
  j=1;
  kn=0;
  a7y=6;
  cu7=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant j == f + kn;
  loop invariant 0 <= f <= a7y;
  loop invariant 0 <= kn <= cu7;
  loop invariant 1 <= j;
  loop invariant (cu7 == k);
  loop invariant a7y == 6;
  loop invariant 1 <= j <= k + 1;
  loop assigns f, j, kn, cu7, k;
*/
while (k<ls) {
      if (!(!(k%3==0))) {
          if (f>0) {
              f--;
              kn++;
          }
      }
      else {
          if (f<a7y) {
              f = f + 1;
              j++;
          }
      }
      cu7++;
      k += 1;
  }
}