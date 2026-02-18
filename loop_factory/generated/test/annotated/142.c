int main1(int b,int k,int m,int n){
  int l, i, v;

  l=16;
  i=l;
  v=4;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant l == 16;
    loop invariant v == 4 + 9*(l - i);
    loop invariant 0 <= i <= l;
    loop invariant v <= 4 + 9*l;
    loop invariant b == \at(b, Pre);
    loop invariant k == \at(k, Pre);
    loop invariant m == \at(m, Pre);
    loop invariant n == \at(n, Pre);
    loop invariant i >= 0;
    loop invariant b == \at(b, Pre) && k == \at(k, Pre) && m == \at(m, Pre) && n == \at(n, Pre);
    loop invariant i <= 16;
    loop invariant v + 9 * i == 4 + 9 * 16;
    loop invariant 0 <= i && i <= 16;
    loop assigns v, i;
  */
  while (i>0) {
      v = v+3;
      v = v+6;
      i = i-1;
  }

}