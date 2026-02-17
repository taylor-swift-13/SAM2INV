int main1(int b,int k,int p){
  int l, i, v, x, t, g;

  l=(k%7)+12;
  i=0;
  v=k;
  x=p;
  t=2;
  g=p;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant i <= l;
    loop invariant i >= 0;
    loop invariant x == p + 2*i;
    loop invariant v == k + i*p + i*(i-1);
    loop assigns v, x, i;
    loop variant l - i;
  */
while (i<l) {
      v = v+x;
      x = x+t;
      i = i+1;
  }

}