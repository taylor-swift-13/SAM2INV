int main1(int a,int b,int p){
  int l, i, v, c, x;

  l=p;
  i=0;
  v=l;
  c=3;
  x=l;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant v == l + i*(c + x + 1);
    loop invariant (l >= 0) ==> (0 <= i && i <= l);
    loop invariant x == l;
    loop invariant l == \at(p, Pre);
    loop invariant c == 3;
    loop assigns v, i;
  */
  while (i<l) {
      v = v+c+x;
      v = v+1;
      i = i+1;
  }

}