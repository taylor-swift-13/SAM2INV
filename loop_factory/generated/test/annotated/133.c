int main1(int a,int m,int p,int q){
  int l, i, v, o;

  l=53;
  i=l;
  v=i;
  o=-5;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant i >= 0;
    loop invariant i <= 53;
    loop invariant v == 318 - 5*i;
    loop invariant 2*o == 19918 - 641*i + 5*i*i;
    loop invariant a == \at(a, Pre) && m == \at(m, Pre) && p == \at(p, Pre) && q == \at(q, Pre);
    loop invariant o >= -5;
    loop invariant a == \at(a, Pre);
    loop invariant m == \at(m, Pre);
    loop invariant p == \at(p, Pre);
    loop invariant q == \at(q, Pre);
    loop invariant v + 5*i == 318;
    loop invariant l == 53;
    loop invariant i <= l;
    loop assigns v, o, i;
  */
  while (i>0) {
      v = v+5;
      o = o+v;
      i = i-1;
  }

}