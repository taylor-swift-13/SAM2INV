int main1(int b){
  int o, r, v;

  o=b+20;
  r=o;
  v=4;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant o == b + 20;

  loop invariant r <= o;
  loop invariant v >= 0;
  loop invariant v <= 4;
  loop invariant b == \at(b, Pre);
  loop invariant o == \at(b, Pre) + 20;
  loop invariant (v == 0) || (v == 4);
  loop invariant v == 0 || v == 4;
  loop invariant (r < o) ==> (v == 0);
  loop assigns r, v;
*/
while (r-1>=0) {
      v = v-v;
      r = r-1;
  }

}
