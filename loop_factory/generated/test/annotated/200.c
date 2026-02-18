int main1(int b,int m,int n,int p){
  int l, i, v;

  l=15;
  i=0;
  v=n;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant i >= 0;
    loop invariant i <= l;
    loop invariant i % 5 == 0;
    loop invariant v == n + (i * (i - 5)) / 10;
    loop invariant n < v + 2;
    loop invariant v >= n;
    loop invariant n == \at(n, Pre);
    loop invariant b == \at(b, Pre);
    loop invariant m == \at(m, Pre);
    loop invariant p == \at(p, Pre);
    loop invariant l == 15;
    loop invariant (v - n) % 5 == 0;

    loop invariant v == n + (i*(i-5))/10;
    loop invariant 0 <= i <= l;
    loop assigns i, v;
    loop variant l - i;
  */
while (i<l) {
      if (n<v+2) {
          v = v+i;
      }
      i = i+5;
  }

}