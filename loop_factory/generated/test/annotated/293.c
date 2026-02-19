int main1(int k,int n){
  int l, i, v;

  l=22;
  i=l;
  v=i;

  
  /*@

    loop invariant i >= 0;

    loop invariant i <= 22;

    loop invariant v + 7*i == 176;

    loop invariant l == 22;

    loop invariant k == \at(k, Pre);

    loop invariant n == \at(n, Pre);

    loop invariant l >= 22;

    loop invariant v + 7 * i == 176;

    loop invariant 0 <= i && i <= 22;

    loop invariant v == 22 + 7*(22 - i);

    loop invariant 0 <= i;

    loop invariant i <= l;

    loop assigns v, i;

    loop variant i;

  */
  while (i>0) {
      v = v+6;
      v = v+1;
      i = i-1;
  }

  /*@ 
    loop invariant i >= 0;
    loop invariant v + 7*i == 176;
    loop invariant k == \at(k, Pre);
    loop invariant n == \at(n, Pre);
    loop invariant l >= 22;
    loop assigns l;
    loop variant i - l;
  */
  while (l < i) {
      l = l+1;
  }

}