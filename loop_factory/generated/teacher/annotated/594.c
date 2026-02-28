int main1(int b,int m){
  int h, v, n, k;

  h=b;
  v=0;
  n=5;
  k=m;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant h == b;
  loop invariant v >= 0;
  loop invariant n >= 5;
  loop invariant n % 5 == 0;
  loop invariant (k - m) % 2 == 0;

  loop invariant (v == 0) ==> k == m;
  loop invariant b == \at(b, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant h == \at(b, Pre);
  loop invariant (v == 0) ==> (n == 5) && (v >= 1 ==> (n % 2 == 0));
  loop assigns n, k, v;
*/
while (1) {
      n = n*2;
      k = k+n;
      k = k%2;
      v = v+1;
  }

}
