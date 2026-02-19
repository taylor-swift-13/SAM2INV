int main1(int k,int n){
  int l, i, v, b;

  l=50;
  i=l;
  v=3;
  b=2;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant i >= 0;
    loop invariant v == 3 + (l - i) * (b + b);
    loop invariant l == 50;
    loop invariant b == 2;
    loop invariant v + 2*b*i == 203;
    loop invariant i <= l;
    loop invariant v >= 3;
    loop invariant v <= 203;
    loop invariant (4*i + v) == 203;
    loop invariant i <= 50;
    loop invariant k == \at(k, Pre);
    loop invariant n == \at(n, Pre);
    loop invariant v == 3 + 4*(l - i);
    loop invariant v == 3 + (b + b) * (l - i);
    loop assigns v, i;
    loop variant i;
  */
  while (i>0) {
      v = v+b+b;
      i = i-1;
  }

}