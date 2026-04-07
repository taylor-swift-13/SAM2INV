int main1(int b){
  int b5, m2k, c74, i5u9, ige;
  b5=b+13;
  m2k=0;
  c74=b;
  i5u9=0;
  ige=b;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant c74 == \at(b,Pre) + m2k + ((m2k + 1) / 2);
  loop invariant i5u9 >= 0;
  loop invariant i5u9 <= m2k;
  loop invariant b5 == \at(b,Pre) + 13;
  loop invariant (m2k < (b5 / 2)) ==> (i5u9 == 0);
  loop invariant b5 == \at(b, Pre) + 13 &&
                   (m2k < b5/2) ==> i5u9 == 0 &&
                   (m2k >= b5/2) ==> i5u9 == m2k - b5/2 + 1 &&
                   c74 == \at(b, Pre) + m2k + ((m2k + 1) / 2) &&
                   ige >= \at(b, Pre);
  loop assigns b, m2k, c74, i5u9, ige;
*/
while (m2k < b5) {
      m2k += 1;
      i5u9 = i5u9 + (m2k >= (b5 / 2));
      c74 = c74 + 1 + (m2k % 2);
      b = b+(i5u9%6);
      ige = ige+c74+i5u9;
  }
}