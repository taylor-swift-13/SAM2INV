int main1(int b,int k,int m){
  int l, i, v;

  l=27;
  i=l;
  v=-4;

  
  /*@

    loop invariant i <= l;

    loop invariant i >= 0;

    loop invariant v == -4 || v == 8;

    loop invariant l == 27;

    loop assigns v, i;

  */
  while (i>0) {
      v = 8;
      i = i-1;
  }

}