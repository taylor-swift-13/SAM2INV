int main1(int b,int k,int m,int q){
  int g, v, t, z, l, p, d;

  g=73;
  v=0;
  t=0;
  z=3;
  l=b;
  p=v;
  d=g;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (t == 0) ==> (z == 3);
  loop invariant (t > 0) ==> (z == g - t + 1);
  loop invariant t >= 0;
  loop invariant g == 73;
  loop invariant (t > 0) ==> (z == g - (t - 1));
  loop invariant z <= g;
  loop invariant b == \at(b, Pre);
  loop invariant k == \at(k, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant q == \at(q, Pre);

  loop assigns t, z;
*/
while (1) {
      z = g-t;
      t = t+1;
  }

}
