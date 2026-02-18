int main1(int a,int b,int n,int p){
  int l, i, v, q;

  l=30;
  i=0;
  v=i;
  q=-4;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant v == 3*i;
    loop invariant q == -4 + 2*i;
    loop invariant i <= l;
    loop invariant i >= 0;
    loop invariant a == \at(a, Pre) && b == \at(b, Pre) && n == \at(n, Pre) && p == \at(p, Pre);
    loop invariant a == \at(a, Pre);
    loop invariant b == \at(b, Pre);
    loop invariant p == \at(p, Pre);
    loop invariant l == 30;
    loop invariant n == \at(n, Pre);
    loop assigns i, v, q;
  */
  while (i<l) {
      v = v+3;
      q = q+2;
      i = i+1;
  }

}