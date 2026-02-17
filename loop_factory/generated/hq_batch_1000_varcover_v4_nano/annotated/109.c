int main1(int b,int k,int n){
  int l, i, v, c, j, u, r, a;

  l=53;
  i=0;
  v=k;
  c=l;
  j=5;
  u=-2;
  r=l;
  a=b;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant v == k + i;
    loop invariant r == l + i;
    loop invariant i <= l;

    loop invariant (i > 0) ==> (u - v == c + 2*j - 1);
    loop invariant b == \at(b, Pre);
    loop invariant k == \at(k, Pre);
    loop assigns i, v, u, r;
    loop variant l - i;
  */
  while (i<l) {
      u = v+c+j;
      v = v+1;
      u = u+j;
      r = r+1;
      i = i+1;
  }

}