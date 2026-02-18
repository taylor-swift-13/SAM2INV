int main1(int a,int k,int n,int p){
  int l, i, v, g;

  l=54;
  i=l;
  v=-2;
  g=n;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant 0 <= i && i <= l;
    loop invariant a == \at(a, Pre);
    loop invariant n == \at(n, Pre);
    loop invariant p == \at(p, Pre);
    loop invariant k == \at(k, Pre);
    loop invariant i >= 0;
    loop invariant v % 2 == 0;
    loop invariant i <= l;
    loop invariant l == 54;
    loop invariant v <= -2;
    loop invariant v < 0;
    loop invariant i <= 54;
    loop assigns v, i;
    loop variant i;
  */
  while (i>0) {
      v = v*2;
      i = i-1;
  }

}