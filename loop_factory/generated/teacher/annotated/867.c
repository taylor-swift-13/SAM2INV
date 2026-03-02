int main1(int b,int m){
  int h, v, n, k;

  h=b;
  v=0;
  n=0;
  k=0;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant n == k * b;
  loop invariant 0 <= k;
  loop invariant b == \at(b, Pre);
  loop invariant h == \at(b, Pre);
  loop invariant h > 0 ==> k <= h;
  loop invariant n == k * b && k >= 0 && h == b;
  loop invariant n == b * k;
  loop invariant h == b;
  loop invariant m == \at(m, Pre);
  loop invariant k >= 0;

  loop invariant n == k*b;
  loop assigns n, k;
*/
while (k<h) {
      n = n+b;
      k = k+1;
  }

}
