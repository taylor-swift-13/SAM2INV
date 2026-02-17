int main1(int a,int b,int p,int q){
  int l, i, v, r, s;

  l=19;
  i=0;
  v=8;
  r=b;
  s=i;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant v == 8 + i*(r + s + 1);
    loop invariant i <= l;
    loop invariant 0 <= i;
    loop invariant l == 19;
    loop invariant b == \at(b, Pre);
    loop invariant s == 0;
    loop assigns i, v;
    loop variant l - i;
  */
  while (i<l) {
      v = v+r+s;
      v = v+1;
      i = i+1;
  }

}