int main1(int s){
  int e1, kap, m, l2, g, qe9;
  e1=s+16;
  kap=0;
  m=0;
  l2=0;
  g=0;
  qe9=5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= g <= 4;
  loop invariant 0 <= l2 <= 4;
  loop invariant -4*kap <= m <= 4*kap;
  loop invariant 5 <= qe9 <= 5 + 4*kap;
  loop invariant e1 == s + 16;
  loop invariant ((kap == 0) ==> (l2 == 0));
  loop invariant 0 <= l2 && l2 < 5;
  loop invariant qe9 == 5 + ((kap / 5) * 10) + (((kap % 5) * ((kap % 5) - 1)) / 2);
  loop invariant 0 <= g && g < 5;
  loop invariant 0 <= kap;
  loop invariant (kap < qe9) ==> (m == qe9 - 5);
  loop invariant 5 <= qe9;
  loop invariant qe9 <= 5 + 4*kap;
  loop invariant (kap == 0) ==> (l2 == 0);
  loop invariant e1 == \at(s, Pre) + 16;
  loop invariant qe9 >= 5;
  loop invariant m >= 0;
  loop invariant g == 0;
  loop assigns kap, l2, m, g, qe9;
*/
while (kap<e1) {
      l2 = kap%5;
      if (kap>=qe9) {
          g = (kap-qe9)%5;
          m = m+l2-g;
      }
      else {
          m += l2;
      }
      kap++;
      qe9 += l2;
  }
}