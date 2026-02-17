int main1(int a,int k,int m){
  int l, i, v, p, j;

  l=57;
  i=0;
  v=8;
  p=0;
  j=l;

  
  /*@

    loop invariant i <= l;

    loop invariant l == 57;

    loop invariant j == 57 + 8*i;

    loop invariant p == 4*i*i + 60*i;

    loop invariant v == 8;

    loop invariant 0 <= i;

    loop assigns i, j, p;

    loop variant l - i;

  */
  while (i<l) {
      p = p+j;
      j = j+v;
      p = p+6;
      p = p+1;
      i = i+1;
  }

}