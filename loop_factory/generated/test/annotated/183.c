int main1(int a,int b,int m,int q){
  int l, i, v, y;

  l=17;
  i=0;
  v=-8;
  y=4;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant i <= l;
    loop invariant i >= 0;
    loop invariant y == 4 + i*(1 - q);
    loop invariant v == -8 + 9*i + (1 - q)*i*(i-1);
    loop invariant a == \at(a, Pre);
    loop invariant b == \at(b, Pre);
    loop invariant 0 <= i;
    loop invariant v == -8 + 9*i + (1 - q)*i*(i - 1);
    loop invariant l == 17;
    loop invariant q == \at(q, Pre);
    loop invariant y == 4 + i * (1 - q);
    loop invariant v == -8 + 9 * i + (1 - q) * i * (i - 1);
    loop invariant y - (1 - q) * i == 4;
    loop assigns i, v, y;
  */
  while (i<l) {
      v = v+y+y;
      v = v+1;
      y = y+1;
      y = y-q;
      i = i+1;
  }

}