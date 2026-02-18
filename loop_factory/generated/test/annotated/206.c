int main1(int a,int b,int m,int n){
  int l, i, v;

  l=22;
  i=0;
  v=3;

  
  /*@

    loop invariant 8*v == i*i - 2*i + 24;

    loop invariant i % 4 == 0;

    loop invariant 0 <= i;

    loop invariant a == \at(a, Pre);

    loop invariant b == \at(b, Pre);

    loop invariant m == \at(m, Pre);

    loop invariant n == \at(n, Pre);

    loop invariant i <= l + 3;

    loop invariant v == 3 + 2*(i/4)*(i/4) - (i/4);

    loop invariant i <= l + 2;

    loop invariant l == 22;

    loop invariant v == 3 + (i / 4) * (2 * (i / 4) - 1);


    loop invariant v >= 3;

    loop assigns i, v;

    loop variant l - i;

  */
  while (i<l) {
      if (v+5<l) {
          v = v+i;
      }
      else {
          v = v+i;
      }
      v = v+1;
      i = i+4;
  }

}