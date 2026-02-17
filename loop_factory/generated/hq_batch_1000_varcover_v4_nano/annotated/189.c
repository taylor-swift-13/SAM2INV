int main1(int a,int m,int q){
  int l, i, v, c, d;

  l=62;
  i=0;
  v=a;
  c=q;
  d=m;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant 0 <= i;
    loop invariant i <= l;
    loop invariant c + d - v == q + m - a;
    loop invariant a == \at(a, Pre);
    loop invariant m == \at(m, Pre);
    loop invariant q == \at(q, Pre);
    loop assigns c, d, v, i;
  */
  while (i<l) {
      c = c+d;
      d = d+v;
      v = v+d;
      i = i+1;
  }

}