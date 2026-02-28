int main1(int a,int m,int p){
  int t, n, v, g;

  t=58;
  n=t;
  v=t;
  g=p;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v - 58 == 2*(p - g);
  loop invariant v <= t + 1;
  loop invariant a == \at(a, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant v - t == 2*(p - g);
  loop invariant v <= t;
  loop invariant v + 2*g == 58 + 2*\at(p, Pre);
  loop invariant g <= \at(p, Pre);
  loop invariant v >= 58;
  loop invariant 2*g + v == 58 + 2*p;
  loop invariant g <= p;
  loop assigns v, g;
*/
while (v<t) {
      if (v<t) {
          v = v+1;
      }
      v = v+1;
      g = g-1;
  }

}
