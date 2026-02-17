int main1(int a,int m,int q){
  int l, i, v, z, j, u, d;

  l=(m%7)+13;
  i=l;
  v=-2;
  z=a;
  j=i;
  u=i;
  d=q;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant v != 0;

    loop invariant (v > z) ==> (v - z > 0);
    loop invariant (z > v) ==> (z - v > 0);
    loop assigns v, z;
  */
while (v!=0&&z!=0) {
      if (v>z) {
          v = v-z;
      }
      else {
          z = z-v;
      }
  }

}