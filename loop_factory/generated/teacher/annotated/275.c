int main1(int m,int n){
  int o, l, z, v;

  o=n+22;
  l=1;
  z=8;
  v=l;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant l == 1;
  loop invariant o == n + 22;

  loop invariant z >= 8;
  loop invariant v >= 0;
  loop invariant v <= 8;
  loop invariant m == \at(m, Pre);
  loop invariant v >= 1;
  loop invariant (v == 1) ==> (z == 8);
  loop invariant v >= l;
  loop invariant o == \at(n,Pre) + 22;
  loop assigns z, v;
*/
while (l+4<=o) {
      z = z*3;
      v = v/3;
      z = z+v;
      v = v+v;
      v = v+4;
  }

}
