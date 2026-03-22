int main1(int y){
  int o, uzb, sm, ia;
  o=y-2;
  uzb=0;
  sm=0;
  ia=8;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ia == 8 - uzb;
  loop invariant 2*sm == uzb*(17 - uzb);
  loop invariant sm == uzb*(17 - uzb)/2;
  loop invariant o == \at(y, Pre) - 2;
  loop invariant 0 <= uzb <= 8;
  loop invariant y == \at(y, Pre) + uzb * (uzb + 1) * (25 - uzb) / 6;
  loop assigns uzb, sm, y, ia;
*/
while (uzb<o&&ia>0) {
      uzb++;
      sm += ia;
      y += sm;
      ia -= 1;
  }
}