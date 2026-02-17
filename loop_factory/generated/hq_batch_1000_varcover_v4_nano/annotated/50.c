int main1(int a,int k,int m){
  int l, i, v, p, d, u, n, c, z, r;

  l=a;
  i=0;
  v=a;
  p=k;
  d=-3;
  u=-4;
  n=l;
  c=a;
  z=a;
  r=k;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant v == \at(a,Pre);
    loop invariant l == \at(a,Pre);
    loop invariant i >= 0;
    loop invariant (l < 0) || i <= l;
    loop invariant (i == 0) ==> u == -4;
    loop assigns u, i;
    loop variant l - i;
  */
while (i<l) {
      u = u*u+v;
      i = i+1;
  }

}