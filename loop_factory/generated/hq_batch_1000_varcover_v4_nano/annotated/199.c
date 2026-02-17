int main1(int b,int n,int p){
  int l, i, v, m, a, w;

  l=(b%16)+18;
  i=0;
  v=b;
  m=l;
  a=l;
  w=-2;

  /*>> LOOP INVARIANT TO FILL <<*/
    /*@
    loop invariant i <= l;
    loop invariant i >= 0;
    loop invariant m == l - i;
    loop invariant (i > 0) ==> (v == 6);
    loop invariant l == (b % 16) + 18;
    loop assigns v, m, i;
    loop variant l - i;
  */
while (i<l) {
      v = v+1;
      m = m-1;
      v = v+5;
      v = 6;
      i = i+1;
  }

}