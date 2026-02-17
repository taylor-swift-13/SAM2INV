int main1(int b,int k,int p){
  int l, i, v, s, d, r;

  l=30;
  i=0;
  v=5;
  s=i;
  d=i;
  r=1;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant i <= l;
    loop invariant i >= 0;
    loop invariant v == 5 + i;
    loop invariant s == 0;
    loop invariant d == 0;
    loop invariant (i == 0) ==> (r == 1);
    loop invariant (i != 0) ==> (r == v - 1);
    loop assigns r, v, i;
    loop variant l - i;
  */
  while (i<l) {
      r = v+s+d;
      v = v+1;
      i = i+1;
  }

}