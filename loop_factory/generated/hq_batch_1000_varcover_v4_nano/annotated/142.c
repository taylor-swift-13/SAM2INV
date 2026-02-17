int main1(int b,int n,int p){
  int l, i, v, u, f, h;

  l=59;
  i=l;
  v=8;
  u=3;
  f=b;
  h=-3;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant v == 8 + (l - i);
    loop invariant f == b + 3 * (l - i);
    loop invariant i >= 0;
    loop invariant i <= l;
    loop invariant b == \at(b, Pre);
    loop invariant n == \at(n, Pre);
    loop invariant p == \at(p, Pre);
    loop assigns i, v, f;
  */
  while (i>0) {
      v = v+1;
      f = f+3;
      i = i-1;
  }

}