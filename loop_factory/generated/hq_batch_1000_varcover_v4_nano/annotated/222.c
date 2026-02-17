int main1(int a,int m,int p){
  int l, i, v, e, c, k;

  l=14;
  i=0;
  v=6;
  e=i;
  c=6;
  k=p;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant i <= l;
    loop invariant i >= 0;
    loop invariant v == i + 6;
    loop invariant e == 6*i + i*(i+1)/2;
    loop invariant k == p + i*(i-1)/2;
    loop assigns v, e, k, i;
    loop variant l - i;
  */
while (i<l) {
      v = v+1;
      e = e+v;
      k = k+i;
      i = i+1;
  }

}