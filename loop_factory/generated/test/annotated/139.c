int main1(int a,int k,int m,int n){
  int l, i, v;

  l=11;
  i=l;
  v=l;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant v == l + (l - i)*(l + 1) - ((l - i)*(l - i - 1))/2;
    loop invariant 0 <= i <= l;
    loop invariant a == \at(a,Pre);
    loop invariant k == \at(k,Pre);
    loop invariant m == \at(m,Pre);
    loop invariant n == \at(n,Pre);
    loop invariant 2*v + i*i + 3*i == 176;
    loop invariant i >= 0;
    loop invariant i <= 11;
    loop invariant a == \at(a, Pre);
    loop invariant k == \at(k, Pre);
    loop invariant m == \at(m, Pre);
    loop invariant n == \at(n, Pre);
    loop invariant 2*v == 176 - 3*i - i*i;
    loop invariant v >= 11;
    loop invariant v >= i;
    loop assigns v, i;
    loop variant i;
  */
  while (i>0) {
      v = v+1;
      v = v+i;
      i = i-1;
  }

}