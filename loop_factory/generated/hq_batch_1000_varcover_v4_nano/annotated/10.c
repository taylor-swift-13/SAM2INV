int main1(int a,int b,int q){
  int l, i, v, u, j, n, m, g;

  l=25;
  i=l;
  v=-3;
  u=l;
  j=5;
  n=8;
  m=0;
  g=b;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant l == 25;
    loop invariant i >= 0;
    loop invariant i <= l;
    loop invariant a == \at(a, Pre);
    loop invariant q == \at(q, Pre);
    loop assigns i;
    loop variant i;
  */
  while (i>0) {
      i = i/2;
  }

}