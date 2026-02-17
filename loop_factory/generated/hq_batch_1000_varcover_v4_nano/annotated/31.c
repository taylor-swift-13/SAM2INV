int main1(int b,int k,int m){
  int l, i, v, x, u;

  l=52;
  i=l;
  v=l;
  x=l;
  u=4;

  
  /*@

    loop invariant b == \at(b, Pre);

    loop invariant k == \at(k, Pre);

    loop invariant m == \at(m, Pre);

    loop invariant i >= 0;

    loop invariant i <= l;

    loop invariant u == 4 + (l - i) * v;

    loop invariant x == l + 4 * (l - i) + v * ((l - i) * (l - i - 1) / 2);

    loop assigns x, u, i;

  */
  while (i>0) {
      x = x+u;
      u = u+v;
      if (u+2<l) {
          x = x+2;
      }
      i = i-1;
  }

}