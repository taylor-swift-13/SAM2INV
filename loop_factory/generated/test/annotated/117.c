int main1(int c,int t){
  int gb, oo7, kg2, rn;
  gb=(c%18)+19;
  oo7=3;
  kg2=0;
  rn=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 7*kg2 + rn == 8*(oo7 - 3);
  loop invariant 0 <= rn;
  loop invariant rn < 7;
  loop invariant c == \at(c, Pre);
  loop invariant t == \at(t, Pre);
  loop invariant gb == \at(c, Pre) % 18 + 19;
  loop invariant oo7 >= 3;
  loop assigns kg2, rn, oo7;
*/
while (oo7<gb) {
      kg2 += 1;
      rn += 1;
      if (rn>=7) {
          rn = rn - 7;
          kg2 += 1;
      }
      oo7++;
  }
}