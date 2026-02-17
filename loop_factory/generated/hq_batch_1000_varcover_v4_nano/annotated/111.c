int main1(int a,int m,int n){
  int l, i, v, x, r, q, k;

  l=22;
  i=0;
  v=l;
  x=l;
  r=n;
  q=m;
  k=m;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant i >= 0;
    loop invariant i <= l;
    loop invariant v == l + 3*i;
    loop invariant x == l*(i+1) + 3*i*(i+1)/2;
    loop assigns v, x, i;
  */
while (i<l) {
      v = v+3;
      x = x+v;
      i = i+1;
  }

}