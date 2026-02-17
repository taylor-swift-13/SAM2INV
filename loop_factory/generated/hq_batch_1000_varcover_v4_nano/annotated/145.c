int main1(int k,int m,int p){
  int l, i, v, y, t, c, q, g;

  l=58;
  i=l;
  v=m;
  y=l;
  t=2;
  c=l;
  q=m;
  g=l;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant v + i == m + l;
    loop invariant y == l + (l - i) * m + ((l - i) * (l - i + 1)) / 2;
    loop invariant i >= 0;
    loop invariant i <= l;
    loop invariant (i < l) ==> c == -4;
    loop assigns v, y, c, i;
  */
  while (i>0) {
      v = v+1;
      y = y+v;
      c = -4;
      i = i-1;
  }

}