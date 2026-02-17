int main1(int b,int k,int m){
  int l, i, v, c, d, x;

  l=68;
  i=0;
  v=i;
  c=-5;
  d=-3;
  x=b;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant i <= l;
    loop invariant i >= 0;
    loop invariant l == 68;
    loop invariant v == 0;
    loop invariant c == -5;
    loop invariant d == -3;
    loop invariant b == \at(b, Pre);
    loop invariant k == \at(k, Pre);
    loop invariant m == \at(m, Pre);
    loop assigns v, c, d, i;
    loop variant l - i;
  */
  while (i<l) {
      v = v*2;
      c = c+v;
      d = d%6;
      i = i+1;
  }

}