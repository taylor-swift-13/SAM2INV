int main1(int m,int p){
  int q, v, n;

  q=p+7;
  v=0;
  n=-5;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant q == p + 7;
  loop invariant v == 0;
  loop invariant p == \at(p, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant (n == 0) || (n == -5);
  loop invariant q == \at(p, Pre) + 7;
  loop invariant n <= 0;
  loop invariant -5 <= n <= 0;
  loop assigns n;
*/
while (v+1<=q) {
      n = n+3;
      n = n-n;
  }

}
