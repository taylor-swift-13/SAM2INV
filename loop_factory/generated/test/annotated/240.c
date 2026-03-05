int main1(int z,int w){
  int sk58, b5k;
  sk58=z+10;
  b5k=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant b5k >= 0;
  loop invariant z == \at(z, Pre) + b5k*(b5k+1)/2;
  loop invariant sk58 == \at(z, Pre) + 10;
  loop invariant w == \at(w, Pre);
  loop assigns b5k, z;
*/
while (b5k<sk58) {
      b5k = b5k + 1;
      if (b5k<=b5k) {
          b5k = b5k;
      }
      z += b5k;
  }
}