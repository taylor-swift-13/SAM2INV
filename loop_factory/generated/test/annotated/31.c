int main1(int a,int b,int m,int q){
  int l, i, v, j;

  l=35;
  i=l;
  v=l;
  j=a;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant i >= 0;
    loop invariant i <= 35;
    loop invariant v == 210 - 5*i;
    loop invariant a == \at(a, Pre);
    loop invariant b == \at(b, Pre);
    loop invariant m == \at(m, Pre);
    loop invariant l == 35;
    loop invariant i <= l;
    loop invariant v == l + 5*(l - i);
    loop invariant q == \at(q, Pre);
    loop invariant v + 5*i == 210;
    loop assigns i, v;
    loop variant i;
  */
  while (i>0) {
      v = v+5;
      i = i-1;
  }

}