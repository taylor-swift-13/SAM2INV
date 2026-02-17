int main1(int b,int k,int m){
  int l, i, v, n, o, y;

  l=m;
  i=0;
  v=l;
  n=k;
  o=3;
  y=4;

  
  /*@

    loop invariant b == \at(b, Pre) && k == \at(k, Pre) && m == \at(m, Pre);

    loop invariant l == m;

    loop invariant v == l;

    loop invariant (l >= 0) ==> (i <= l);

    loop invariant (i > 0) ==> (y == v + n + o);

    loop assigns y, i;

    loop variant l - i;

  */
  while (i<l) {
      y = v+n+o;
      i = i+1;
  }

}