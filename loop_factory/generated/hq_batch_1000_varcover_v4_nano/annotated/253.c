int main1(int b,int n,int p){
  int l, i, v, a, q, o, z, f;

  l=24;
  i=0;
  v=0;
  a=-1;
  q=n;
  o=2;
  z=p;
  f=1;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant v == 5*i;
    loop invariant a == -1 + (i*(5*i - 3))/2;
    loop invariant i <= l;
    loop invariant 0 <= i;
    loop invariant b == \at(b, Pre);
    loop invariant n == \at(n, Pre);
    loop invariant p == \at(p, Pre);
    loop assigns v, a, i;
    loop variant l - i;
  */
  while (i<l) {
      v = v+1;
      a = a+v;
      v = v+4;
      i = i+1;
  }

}