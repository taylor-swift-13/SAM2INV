int main1(int a,int b,int k){
  int l, i, v;

  l=18;
  i=0;
  v=a;

  
  /*@

    loop invariant v == a + 2*i;

    loop invariant 0 <= i;

    loop invariant i <= l;

    loop invariant i % 2 == 0;

    loop invariant l == 18;

    loop assigns v, i;

  */
  while (i<l) {
      v = v+3;
      v = v+1;
      i = i+2;
  }

}