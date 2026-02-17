int main1(int a,int m,int n){
  int l, i, v, e, z, t;

  l=25;
  i=l;
  v=i;
  e=4;
  z=a;
  t=a;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant v == 100 - 3*i;
    loop invariant z == a + (l - i) * (3 + a);
    loop invariant i >= 0;
    loop invariant i <= l;
    loop invariant t == a;
    loop assigns i, v, z;
  */
  while (i>0) {
      v = v+3;
      z = z+3;
      z = z+t;
      i = i-1;
  }

}