int main1(int a,int k,int m,int n){
  int l, i, z, v, h, c, x;

  l=a+4;
  i=0;
  z=l;
  v=i;
  h=l;
  c=5;
  x=i;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant l == a + 4;
  loop invariant z == l + 4*i;
  loop invariant v == i*l + 2*i*i + 2*i;
  loop invariant i >= 0;
  loop invariant a == \at(a, Pre);
  loop invariant v == i*l + 2*i*(i+1);
  loop invariant z >= l;
  loop assigns z, i, v;
*/
while (1) {
      if (i>=l) {
          break;
      }
      z = z+3;
      i = i+1;
      z = z+1;
      v = v+z;
  }

}
