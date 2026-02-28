int main1(int a,int q){
  int x, g, v, s;

  x=24;
  g=x;
  v=-2;
  s=5;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant s - 2*v == 9;
  loop invariant v >= -9;
  loop invariant a == \at(a, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant x == 24;
  loop invariant v <= s;
  loop invariant s != 0;
  loop invariant s >= 0;
  loop invariant s >= v;
  loop assigns v, s;
*/
while (v!=0&&s!=0) {
      if (v>s) {
          v = v-s;
      }
      else {
          s = s-v;
      }
      v = v+1;
      s = s+v;
      s = s+1;
  }

}
