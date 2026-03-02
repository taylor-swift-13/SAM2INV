int main1(int b,int n){
  int o, g, v;

  o=9;
  g=0;
  v=-4;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant o == 9;
  loop invariant g >= 0;
  loop invariant v == 0 || v == -4;
  loop invariant b == \at(b, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant v*(v+4) == 0;
  loop invariant (v == 0) || (g == 0 && v == -4);
  loop invariant v == 0 || (g == 0 && v == -4);
  loop invariant v == 0 || (v == -4 && g == 0);
  loop invariant b == \at(b, Pre) && n == \at(n, Pre);
  loop invariant b == \at(b, Pre) && n == \at(n, Pre) && o == 9;
  loop invariant (v == 0 || v == -4) && g >= 0;
  loop assigns v, g;
*/
while (1) {
      if (g+6<=b+o) {
          v = v+1;
      }
      v = v-v;
      g = g+1;
  }

}
