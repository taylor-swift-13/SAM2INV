int main1(int b,int m,int p){
  int l, i, v, g, h, o, z;

  l=23;
  i=0;
  v=l;
  g=p;
  h=-5;
  o=m;
  z=m;

  
  /*@

    loop invariant (p >= 0) ==> v >= 0;

    loop invariant (p >= 0) ==> g >= 0;

    loop assigns v, g;

  */
  while (v!=0&&g!=0) {
      if (v>g) {
          v = v-g;
      }
      else {
          g = g-v;
      }
  }

}