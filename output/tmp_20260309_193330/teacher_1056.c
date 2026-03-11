int main1(int m,int q){
  int g, i, v;

  g=56;
  i=g;
  v=8;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant g == 56;
  loop invariant i % 3 == g % 3;
  loop invariant i <= g;
  loop invariant v == 0 || v == 8;
  loop invariant m == \at(m, Pre) && q == \at(q, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant 0 <= i && i <= 56;
  loop invariant i % 3 == 56 % 3;
  loop invariant (v == 0 || v == 8) && i % 3 == 2 && 0 <= i && i <= 56;
  loop invariant g == 56 && m == \at(m, Pre) && q == \at(q, Pre);
  loop invariant (i % 3) == 2 && i >= 2 && g == 56;
  loop invariant (g - i) % 3 == 0;
  loop invariant 0 <= i && i <= g;
  loop invariant (g == 56) && (0 <= i) && (i <= g) && (((g - i) % 3) == 0);
  loop invariant ((v == 0) || (v == 8)) && (m == \at(m, Pre)) && (q == \at(q, Pre));
  loop invariant (i % 3) == (g % 3);
  loop invariant 0 <= i;
  loop invariant i % 3 == 56 % 3 && g == 56 && m == \at(m, Pre);
  loop invariant (v == 0 || v == 8) && 0 <= i && i <= 56 && q == \at(q, Pre);
  loop invariant ((g - i) / 3) >= 0;
  loop assigns i, v;
*/
while (i>=3) {
      if ((i%2)==0) {
          v = v-v;
      }
      i = i-3;
  }

}
