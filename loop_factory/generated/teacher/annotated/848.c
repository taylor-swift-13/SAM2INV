int main1(int k,int m,int p){
  int w, b, d, q, e, v;

  w=77;
  b=1;
  d=b;
  q=p;
  e=k;
  v=-5;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant k == \at(k, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant e == k + 6*(v + 5);
  loop invariant q == p + k*(v + 5) + 3*(v + 5)*(v + 5) - 3*(v + 5);
  loop invariant v <= w + 1;
  loop invariant w == 77;
  loop invariant q == p + k*(v + 5) + 3*(v + 5)*(v + 4);

  loop invariant v >= -5;
  loop invariant -5 <= v;
  loop invariant e == \at(k,Pre) + 6*(v + 5) &&
                   q == \at(p,Pre) + (v + 5) * \at(k,Pre) + 3*(v + 5)*(v + 4) &&
                   d == 1 + (v + 5) * \at(p,Pre) + (\at(k,Pre)) * (v + 5)*(v + 4) / 2 + (v + 5)*(v + 4)*(v + 3) + (v + 5);
  loop invariant e == k + 6*v + 30;
  loop invariant q == p + k*(v + 5) + 3*v*v + 27*v + 60;

  loop invariant b == 1;
  loop assigns d, q, e, v;
*/
while (v<=w) {
      d = d+q;
      q = q+e;
      e = e+6;
      v = v+1;
      d = d+b;
  }

}
