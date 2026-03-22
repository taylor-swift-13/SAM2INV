int main1(){
  int vmh, wx, e, j, m7k, ap, qj5, ek6;
  vmh=189;
  wx=0;
  e=vmh;
  j=vmh;
  m7k=vmh;
  ap=-3;
  qj5=wx;
  ek6=vmh;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= wx <= vmh;
  loop invariant vmh == 189;
  loop invariant ap >= -3;
  loop invariant qj5 >= 0;
  loop invariant qj5 % 2 == 0;
  loop invariant (ap % 2) != 0;
  loop invariant e == 189 + (wx + 1) / 2;
  loop invariant ek6 == 189 + (wx + 1) / 2;
  loop invariant j == 189 + wx / 2;
  loop invariant m7k == 189 + wx / 2;
  loop assigns e, ek6, j, m7k, wx, ap, qj5;
*/
while (wx < vmh) {
      if (wx % 2 == 0) {
          e += 1;
          ek6++;
      }
      else {
          j++;
          m7k++;
      }
      wx += 1;
      if (!(!((wx%9)==0))) {
          ap += qj5;
      }
      ap += 2;
      qj5 += j;
      qj5 = qj5 + ap;
      qj5 += qj5;
  }
}