int main1(int a,int b,int p){
  int l, i, v, c, r, q, n;

  l=30;
  i=0;
  v=a;
  c=-1;
  r=p;
  q=i;
  n=i;

  
  /*@

    loop invariant i <= l;

    loop invariant 0 <= i;

    loop invariant v == a + i;

    loop invariant c == -1 + i*a + i*(i+1)/2;

    loop invariant q == 0;

    loop invariant l == 30;

    loop assigns v, c, i;

    loop variant l - i;

  */
  while (i<l) {
      v = v+1;
      c = c+v;
      c = c+q;
      i = i+1;
  }

}