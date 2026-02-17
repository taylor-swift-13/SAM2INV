int main1(int a,int n,int p){
  int l, i, v, b, x, k, e, q, z;

  l=62;
  i=0;
  v=l;
  b=-2;
  x=n;
  k=-6;
  e=n;
  q=5;
  z=n;

  
  /*@

    loop invariant 0 <= i;

    loop invariant i <= l;

    loop invariant v == l + i*(i-1)/2;

    loop invariant (i == 0) ==> (b == -2);

    loop invariant (i > 0) ==> (b >= 0);

    loop assigns v, b, i;

    loop variant l - i;

  */
  while (i<l) {
      v = v+i;
      b = b*b;
      i = i+1;
  }

}