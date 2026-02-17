int main1(int m,int n,int p){
  int l, i, v, z;

  l=64;
  i=0;
  v=-4;
  z=n;

  
  /*@

    loop invariant 0 <= i <= l;

    loop invariant v == -4 + 9*i;

    loop invariant (i == 0) ==> (z == n);

    loop invariant (i > 0) ==> (z % 2 == 0);

    loop assigns i, v, z;

  */
  while (i<l) {
      v = v+3;
      z = z+v;
      z = z+z;
      v = v+6;
      i = i+1;
  }

}