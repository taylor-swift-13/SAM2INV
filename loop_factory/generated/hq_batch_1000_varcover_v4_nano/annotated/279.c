int main1(int a,int m,int n,int q){
  int l, i, v, j, h, d, b;

  l=72;
  i=l;
  v=-4;
  j=-4;
  h=1;
  d=l;
  b=n;

  
  /*@

    loop invariant 0 <= i <= l;

    loop invariant d == l || d == v + j + h;

    loop invariant d <= l;

    loop invariant d >= v + j + h;

    loop assigns i, d;

    loop variant i;

  */
  while (i>0) {
      d = v+j+h;
      i = i-1;
  }

}