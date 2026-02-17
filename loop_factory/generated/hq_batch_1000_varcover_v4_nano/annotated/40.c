int main1(int a,int k,int m){
  int l, i, v, b, d, e;

  l=44;
  i=0;
  v=2;
  b=8;
  d=-2;
  e=2;

  
  /*@

    loop invariant l == 44;

    loop invariant e == 2;

    loop invariant d == -2;

    loop invariant i >= 0;

    loop invariant i <= l;

    loop invariant (i == 0) ==> (v == 2);

    loop invariant (i > 0) ==> (v == e*e);

    loop invariant (i == 0) ==> (b == 8);

    loop invariant (i > 0) ==> (b >= 12);

    loop assigns v, b, d, i;

    loop variant l - i;

  */
  while (i<l) {
      v = v*2;
      b = b+v;
      d = d%9;
      v = e*e;
      i = i+1;
  }

}