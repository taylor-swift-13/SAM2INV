int main1(int a,int m,int n,int q){
  int l, i, v, c;

  l=17;
  i=l;
  v=m;
  c=-4;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant i >= 0;
    loop invariant i <= 17;
    loop invariant c == 81 - 5*i;
    loop invariant v == \at(m,Pre) + 5*(17 - i);
    loop invariant a == \at(a,Pre) && m == \at(m,Pre) && n == \at(n,Pre) && q == \at(q,Pre);
    loop invariant v == \at(m, Pre) + 85 - 5*i;
    loop invariant l == 17;
    loop invariant a == \at(a, Pre) && m == \at(m, Pre) && n == \at(n, Pre) && q == \at(q, Pre);
    loop invariant v == m + 5*(17 - i);
    loop invariant a == \at(a,Pre);
    loop invariant m == \at(m,Pre);
    loop invariant n == \at(n,Pre);
    loop invariant q == \at(q,Pre);
    loop invariant v == m + 85 - 5*i;
    loop invariant i <= l;
    loop invariant v - c == m + 4;
    loop assigns v, c, i;
    loop variant i;
  */
  while (i>0) {
      v = v+1;
      c = c-1;
      if (i+6<=l+l) {
          v = v+4;
      }
      c = c+6;
      i = i-1;
  }

}