int main1(int m,int n,int p){
  int l, i, v, y, q, f;

  l=51;
  i=0;
  v=i;
  y=p;
  q=p;
  f=l;

  
  /*@

    loop invariant 0 <= i && i <= l;

    loop invariant l == 51;

    loop invariant v >= 0;

    loop invariant (i == 0 ==> (v == 0 && y == \at(p, Pre) && q == \at(p, Pre)));

    loop invariant (i >= 1 ==> y >= 0);

    loop invariant q >= \at(p, Pre);

    loop assigns v, y, q, i;

    loop variant l - i;

  */
while (i<l) {
      v = v+i;
      y = y*y;
      q = q+v*y;
      v = v*v+y;
      i = i+1;
  }

}