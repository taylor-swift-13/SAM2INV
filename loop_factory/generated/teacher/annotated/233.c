int main1(int b,int n){
  int v, k, p;

  v=b+13;
  k=v+6;
  p=5;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v == \at(b, Pre) + 13;
  loop invariant k >= v;
  loop invariant k <= \at(b, Pre) + 19;
  loop invariant b == \at(b, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant v == b + 13;
  loop invariant k <= v + 6;
  loop invariant p >= 5;

  loop invariant p % 5 == 0;
  loop invariant k - v <= 6;
  loop invariant 0 <= k - v <= 6;
  loop assigns p, k;
*/
while (k>v) {
      p = p*2;
      k = k-1;
  }

}
