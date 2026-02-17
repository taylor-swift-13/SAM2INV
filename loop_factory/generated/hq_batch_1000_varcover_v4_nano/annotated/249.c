int main1(int b,int k,int q){
  int l, i, v, j, d;

  l=40;
  i=0;
  v=8;
  j=6;
  d=b;

  
  /*@

    loop invariant 0 <= i && i <= l;

    loop invariant v == 8 + 2 * i;

    loop invariant (j - i * (v - i)) == 6;

    loop invariant d == b + (i + 6) / 7;

    loop assigns v, j, d, i;

    loop variant l - i;

  */
while (i<l) {
      v = v+1;
      j = j+v;
      v = v+1;
      if ((i%7)==0) {
          d = d+1;
      }
      i = i+1;
  }

}