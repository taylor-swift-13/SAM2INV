int main1(int b,int n,int q){
  int l, i, v;

  l=62;
  i=0;
  v=i;

  
  /*@

    loop invariant v == 0;

    loop invariant 0 <= i;

    loop invariant i <= l;

    loop invariant l == 62;

    loop assigns v, i;

    loop variant l - i;

  */
  while (i<l) {
      v = v+v;
      if (v+4<l) {
          v = v*i;
      }
      i = i+1;
  }

}