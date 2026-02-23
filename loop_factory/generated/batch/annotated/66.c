int main1(int k,int q){
  int z, w, v;

  z=44;
  w=0;
  v=w;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant z == 44;
  loop invariant v == 0;
  loop invariant w % 5 == 0;
  loop invariant k == \at(k, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant w >= 0;
  loop invariant 0 <= w;
  loop invariant w <= z + 4;

  loop assigns v, w;
*/
while (w<z) {
      v = v-v;
      w = w+5;
  }

}
