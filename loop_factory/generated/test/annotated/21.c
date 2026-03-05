int main1(int r,int s){
  int on;
  on=-17592;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant s == \at(s, Pre);
  loop invariant r <= \at(r, Pre);
  loop invariant on <= -17592;
  loop invariant (on % 2 != 0) || (on == -17592);
  loop assigns on, r;
*/
while (on<=-8) {
      on = on+on+2;
      on += 1;
      r = r + on;
  }
}