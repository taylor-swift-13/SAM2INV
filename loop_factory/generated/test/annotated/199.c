int main1(int b,int k,int n,int q){
  int l, i, v;

  l=27;
  i=l;
  v=i;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant l == 27;
    loop invariant i <= l;
    loop invariant i >= 0;
    loop invariant v == l + (l*(l+1))/2 - (i*(i+1))/2;
    loop invariant b == \at(b, Pre);
    loop invariant k == \at(k, Pre);
    loop invariant n == \at(n, Pre);
    loop invariant q == \at(q, Pre);
    loop invariant v == 405 - i*(i+1)/2;
    loop invariant 0 <= i <= 27;
    loop invariant b == \at(b, Pre) && k == \at(k, Pre) && n == \at(n, Pre) && q == \at(q, Pre);
    loop invariant i <= 27;
    loop invariant v >= 27;
    loop invariant v >= i;
    loop invariant 0 <= i <= l;
    loop assigns i, v;
    loop variant i;
  */
  while (i>0) {
      v = v+i;
      i = i-1;
  }

}