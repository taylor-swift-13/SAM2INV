int main1(int b,int k,int p,int q){
  int l, i, v, g, d;

  l=49;
  i=l;
  v=k;
  g=-4;
  d=-2;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant v == k + (l - i);
    loop invariant 0 <= i;
    loop invariant i <= l;
    loop invariant l == 49;
    loop invariant b == \at(b, Pre);
    loop invariant k == \at(k, Pre);
    loop invariant p == \at(p, Pre);
    loop invariant q == \at(q, Pre);
    loop invariant v + i == k + 49;
    loop invariant i >= 0;
    loop invariant i <= 49;
    loop invariant v >= k;
    loop invariant v + i == \at(k, Pre) + 49;
    loop invariant v - k == l - i;
    loop invariant i + v == l + k;
    loop invariant v <= k + l;
    loop assigns i, v;
    loop variant i;
  */
while (i>0) {
      v = v+1;
      i = i-1;
  }

}