int main1(int b,int k,int n){
  int l, i, v, x, z, q, p, a;

  l=61;
  i=0;
  v=l;
  x=k;
  z=i;
  q=n;
  p=-8;
  a=k;

  
  /*@

    loop invariant l == 61;

    loop invariant 0 <= i && i <= l;

    loop invariant v > 0;

    loop invariant v % 3 == 0 || i == 0;

    loop assigns v, i;

    loop variant l - i;

  */
while (i<l) {
      v = v*3;
      i = i+1;
  }

}