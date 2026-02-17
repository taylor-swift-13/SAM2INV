int main1(int a,int m,int n){
  int l, i, v, y, z, t, k, w, o;

  l=73;
  i=l;
  v=0;
  y=a;
  z=1;
  t=i;
  k=n;
  w=a;
  o=8;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant v == 0;
    loop invariant y == a;
    loop invariant i >= 0;
    loop invariant i <= l;
    loop invariant a == \at(a, Pre);
    loop invariant m == \at(m, Pre);
    loop invariant n == \at(n, Pre);
    loop assigns v, y, i;
    loop variant i;
  */
  while (i>0) {
      v = v*2;
      y = y+v;
      i = i/2;
  }

}