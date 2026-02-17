int main1(int b,int k,int m){
  int l, i, v, e, s, f, z;

  l=36;
  i=0;
  v=-4;
  e=b;
  s=k;
  f=k;
  z=k;

  
  /*@

    loop invariant l == 36;

    loop invariant -4 <= v && v <= l;

    loop assigns v;

  */
  while (v<l) {
      if (v<l) {
          v = v+1;
      }
  }

}