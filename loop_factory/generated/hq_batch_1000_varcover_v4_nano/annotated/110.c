int main1(int a,int b,int q){
  int l, i, v, r, u, o, t, h, c;

  l=16;
  i=1;
  v=i;
  r=8;
  u=5;
  o=i;
  t=i;
  h=a;
  c=l;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant l == 16;
    loop invariant i >= 1;
    loop invariant i <= l;
    loop invariant l % i == 0;
    loop invariant a == \at(a, Pre);
    loop assigns i;
  */
  while (i<l) {
      i = i*2;
  }

}