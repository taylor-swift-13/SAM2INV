int main1(int m){
  int h9ev, i38, b, yh, q, o, y, s6, aeo, wzv;
  h9ev=m;
  i38=0;
  b=m;
  yh=h9ev;
  q=h9ev;
  o=i38;
  y=i38;
  s6=-8;
  aeo=m;
  wzv=m;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant y == i38;
  loop invariant s6 == -8 + 2*i38;
  loop invariant q == h9ev + ((i38 + 1) / 4);
  loop invariant h9ev == \at(m,Pre);
  loop invariant b + yh + o + q - i38 == 3 * \at(m,Pre);
  loop invariant b == \at(m,Pre) + ((i38 + 3) / 4);
  loop invariant yh == \at(m,Pre) + ((i38 + 2) / 4);
  loop invariant o == (i38 / 4);
  loop invariant aeo == \at(m,Pre) + 3*i38 + i38*(i38+1)/2;
  loop invariant i38 >= 0;
  loop assigns b, yh, o, q, i38, wzv, y, s6, aeo, m;
*/
while (i38 < h9ev) {
      b = b + ((i38 % 4) == 0);
      yh = yh + ((i38 % 4) == 1);
      o = o + ((i38 % 4) == 3);
      q = q + ((i38 % 4) == 2);
      i38 += 1;
      if ((i38%6)==0) {
          wzv = aeo-wzv;
      }
      if (q<o+1) {
          wzv += 1;
      }
      y++;
      s6 += 2;
      aeo = (3)+(aeo);
      m = m + q;
      aeo += i38;
  }
}