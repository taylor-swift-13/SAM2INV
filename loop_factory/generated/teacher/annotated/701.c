int main1(int b,int k,int n,int q){
  int l, c, v, z, t, o, f;

  l=48;
  c=1;
  v=0;
  z=1;
  t=6;
  o=0;
  f=n;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= o <= l+1;
  loop invariant t == 6 + 4*o;
  loop invariant z == 2*o*o + 4*o + 1;
  loop invariant v == (2*o*o*o + 3*o*o - 2*o) / 3;
  loop invariant b == \at(b, Pre);
  loop invariant k == \at(k, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant o >= 0;
  loop invariant o <= l + 1;
  loop invariant 3*v == 2*o*o*o + 3*o*o - 2*o;
  loop invariant v == o*(2*o*o + 3*o - 2) / 3;
  loop invariant l == 48;
  loop assigns o, v, z, t;
*/
while (o<=l) {
      o = o+1;
      v = v+z;
      z = z+t;
      t = t+4;
  }

}
