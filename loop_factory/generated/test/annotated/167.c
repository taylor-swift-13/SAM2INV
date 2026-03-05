int main1(int q,int v){
  int h6, dfu;
  h6=v-5;
  dfu=8;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant q == \at(q, Pre);
  loop invariant v == \at(v, Pre);
  loop invariant dfu >= 8;
  loop invariant dfu % 8 == 0;
  loop invariant h6 == v - 5;
  loop assigns dfu;
*/
while (dfu<=h6) {
      dfu = dfu + dfu;
  }
}