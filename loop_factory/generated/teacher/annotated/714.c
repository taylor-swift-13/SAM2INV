int main1(int a,int b,int k,int n){
  int o, z, v, l, c, s;

  o=(k%36)+18;
  z=0;
  v=4;
  l=o;
  c=o;
  s=o;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant z == 0;
  loop invariant v == 4;
  loop invariant o == (k % 36) + 18;
  loop invariant l >= o;
  loop invariant a == \at(a, Pre);
  loop invariant k == \at(k, Pre);
  loop invariant o == (\at(k, Pre) % 36) + 18;

  loop assigns l, v;
*/
while (1) {
      l = l+v;
      v = v+z;
      l = l*l;
  }

}
