int main1(int a,int n,int q){
  int l, i, v, y, j, z;

  l=55;
  i=0;
  v=l;
  y=-8;
  j=-5;
  z=i;

  
  /*@

    loop invariant v == l + i;

    loop invariant y == -8 - i;

    loop invariant z == i*(i-1)/2;

    loop invariant i <= l;

    loop invariant i >= 0;

    loop assigns v, y, z, i;

    loop variant l - i;

  */
  while (i<l) {
      v = v+1;
      y = y-1;
      z = z+i;
      i = i+1;
  }

}