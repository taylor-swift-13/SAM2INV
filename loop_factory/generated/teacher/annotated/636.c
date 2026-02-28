int main1(int b,int k){
  int m, j, v, q, a, g;

  m=b+6;
  j=m;
  v=k;
  q=m;
  a=-5;
  g=0;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ((q == m) || (q == a)) && (v >= k) && (m == b + 6) && (a == -5);
  loop invariant v >= k;
  loop invariant m == b + 6;
  loop invariant a == -5;
  loop invariant (q == m) || (q == a);
  loop invariant k == \at(k, Pre);
  loop invariant b == \at(b, Pre);
  loop invariant q == m || q == a;
  loop invariant q <= m;
  loop invariant m == \at(b, Pre) + 6 && ((q == m) || (q == a)) && v >= \at(k, Pre);

  loop assigns q, v;
*/
while (1) {
      if (v>=m) {
          break;
      }
      if (a<=q) {
          q = a;
      }
      v = v+1;
  }

}
