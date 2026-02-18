int main1(int a,int b,int m,int p){
  int l, i, v, w;

  l=61;
  i=0;
  v=-3;
  w=-4;

  
  /*@

    loop invariant w == i - 4;

    loop invariant v == -3 + (3*i*(i-1))/2 - 9*i;

    loop invariant 0 <= i <= l;

    loop invariant a == \at(a, Pre);

    loop invariant b == \at(b, Pre);

    loop invariant m == \at(m, Pre);

    loop invariant p == \at(p, Pre);

    loop invariant i <= l;

    loop invariant w - i == -4;

    loop invariant i >= 0;

    loop invariant l == 61;

    loop invariant 0 <= i;

    loop invariant w == -4 + i;

    loop assigns v, w, i;

  */
  while (i<l) {
      v = v+w+w;
      v = v+1;
      w = w+1;
      if (i+2<=w+l) {
          v = v+w;
      }
      v = v+1;
      i = i+1;
  }

}