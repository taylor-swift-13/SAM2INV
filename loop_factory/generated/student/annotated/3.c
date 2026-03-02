int main1(int k,int m){
  int l, u, v, y;

  l=47;
  u=0;
  v=-8;
  y=u;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v >= 0 || y >= 0;
  loop invariant v >= 0 || v <= 0;
  loop invariant y >= 0 || y <= 0;
  loop invariant v >= 0 ==> y >= 0;

  loop invariant v != 0 || y != 0;
  loop assigns v, y;
*/
while (v!=0&&y!=0) {
      if (v>y) {
          v = v-y;
      }
      else {
          y = y-v;
      }
  }

}
