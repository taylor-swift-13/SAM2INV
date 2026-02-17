int main1(int a,int b,int k,int m){
  int l, i, v;

  l=b+19;
  i=0;
  v=l;

  
  /*@

    loop invariant l == b + 19;

    loop invariant 0 <= i;

    loop invariant (l >= 0) ==> i <= l;

    loop invariant (l >= 0) ==> v >= 0;

    loop assigns i, v;

    loop variant l - i;

  */
  while (i<l) {
      if ((i%6)==0) {
          v = l-(-4);
      }
      v = v+v;
      if (i+7<=v+l) {
          v = v+1;
      }
      i = i+1;
  }

}