int main1(int a,int b,int n,int p){
  int l, i, v, x;

  l=13;
  i=1;
  v=-3;
  x=b;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant v == -3*i;
    loop invariant x == b - 6*i + 6;
    loop invariant a == \at(a, Pre);
    loop invariant b == \at(b, Pre);
    loop invariant n == \at(n, Pre);
    loop invariant p == \at(p, Pre);

    loop invariant v == -3 * i;
    loop invariant x == b - 6 * i + 6;
    loop invariant a == \at(a, Pre) && b == \at(b, Pre) && n == \at(n, Pre) && p == \at(p, Pre);
    loop invariant l == 13;
    loop invariant i >= 1;
    loop invariant i <= 2*l;
    loop invariant x == \at(b, Pre) - 6 * i + 6;
    loop invariant x == b - 6 * (i - 1);
    loop invariant i > 0;
    loop assigns v, x, i;
    loop variant l - i;
  */
  while (i<l) {
      v = v*2;
      x = x+v;
      i = i*2;
  }

}