int main1(int a,int k,int m){
  int l, i, v, d, e, u, s, w;

  l=73;
  i=l;
  v=i;
  d=k;
  e=a;
  u=l;
  s=-2;
  w=k;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant i >= 0;
    loop invariant i <= 73;
    loop invariant a == \at(a, Pre);
    loop invariant k == \at(k, Pre);
    loop invariant m == \at(m, Pre);
    loop invariant l == 73;
    loop assigns i;
    loop variant i;
  */
  while (i>0) {
      i = i-1;
  }

}