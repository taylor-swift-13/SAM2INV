int main1(int a,int p,int q){
  int l, i, v, n, k, h, g, u;

  l=25;
  i=0;
  v=-6;
  n=l;
  k=p;
  h=-3;
  g=l;
  u=1;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant i <= l;
    loop invariant i >= 0;
    loop invariant l == 25;
    loop invariant p == \at(p, Pre);
    loop invariant q == \at(q, Pre);
    loop invariant a == \at(a, Pre);
    loop assigns i;
    loop variant l - i;
  */
  while (i<l) {
      i = i+1;
  }

}