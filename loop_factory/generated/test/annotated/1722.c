int main1(int v){
  int qz, el5, h80, m5;
  qz=77;
  el5=0;
  h80=el5;
  m5=el5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant h80 == el5;
  loop invariant m5 == el5*(el5+1)/2;
  loop invariant v == \at(v,Pre) + el5*(el5-1)/2;
  loop invariant 0 <= el5 <= qz;
  loop assigns el5, m5, v, h80;
*/
while (1) {
      if (!(el5 < qz)) {
          break;
      }
      el5++;
      m5 += el5;
      v += h80;
      h80++;
  }
}