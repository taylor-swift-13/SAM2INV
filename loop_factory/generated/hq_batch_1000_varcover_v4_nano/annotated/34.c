int main1(int b,int k,int m){
  int l, i, v, x, n, q;

  l=74;
  i=0;
  v=m;
  x=6;
  n=b;
  q=m;

  
  /*@

    loop invariant x == (6 - 2*\at(m,Pre)) + 2*v;

    loop invariant 0 <= i && i <= l;

    loop invariant b == \at(b,Pre) && k == \at(k,Pre) && m == \at(m,Pre);

    loop invariant (i == 0 ==> n == \at(b,Pre)) && (i >= 1 ==> -7 <= n && n <= 7);

    loop assigns v, x, n, i;

    loop variant l - i;

  */
while (i<l) {
      v = v*2;
      x = x+v;
      n = n%8;
      i = i+1;
  }

}