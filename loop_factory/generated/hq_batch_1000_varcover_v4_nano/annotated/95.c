int main1(int a,int k,int n){
  int l, i, v, p, b;

  l=29;
  i=l;
  v=a;
  p=i;
  b=n;

  
  /*@

    loop invariant v == a + 2*(l - i);

    loop invariant b == n + (p+1)*(l - i);

    loop invariant i >= 0;

    loop invariant i <= l;

    loop assigns v, b, i;

    loop variant i;

  */
  while (i>0) {
      v = v+2;
      b = b+1;
      b = b+p;
      i = i-1;
  }

}