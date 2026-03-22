int main1(int h){
  int nz, m1, fp, tk4, ht;
  nz=h+13;
  m1=1;
  fp=nz;
  tk4=m1;
  ht=m1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ht == 1;
  loop invariant nz == h + 13;
  loop invariant fp == nz + ((tk4 - 1) * tk4) / 2;
  loop invariant h == \at(h, Pre);
  loop invariant m1 >= 1;
  loop invariant tk4 >= 1;
  loop assigns fp, tk4, m1;
*/
while (1) {
      if (!(m1*3<=nz)) {
          break;
      }
      fp = fp + tk4;
      tk4 += ht;
      m1 = m1*3;
  }
}